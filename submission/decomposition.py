#!/usr/bin/env python3
"""Self-contained extra-fold Block-ZXZ synthesis.

Requires Python >= 3.10, NumPy, and SciPy.
Run: python decomposition.py 3 4 5 --seed 0 --samples 1
For a unitary U of dimension 2**n, decompose(U) returns (circuit, diagonal):
U = diagonal @ circuit_matrix(circuit, n), up to numerical precision.

Qubit q is bit q of a basis index. Gate tuples are in execution order:
("u", q, matrix) and ("cx", control, target). The two-qubit leaves use the algebraic
Shende-Markov-Bullock constructions (three CX, or two with a diagonal carry):
https://arxiv.org/abs/quant-ph/0308033 (Props. IV.3, V.1, V.2)
https://arxiv.org/abs/quant-ph/0308045 (Prop. III.3).
Inputs are assumed valid; pivot searches assume a resolved nonsingular path.
"""

from __future__ import annotations

import argparse
import platform

import numpy as np
import scipy
import scipy.linalg as sl
from scipy.linalg import polar, schur
from scipy.optimize import brentq, linear_sum_assignment

H = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
Z = np.diag([1, -1]).astype(complex)
Y = np.array([[0, -1j], [1j, 0]])
YY = np.kron(Y, Y)
MAGIC = np.array([
    [1, 1j, 0, 0], [0, 0, 1j, 1], [0, 0, 1j, -1], [1, -1j, 0, 0],
]) / np.sqrt(2)
TOL = 1e-7
ROOT_TOL = 2e-13
UNIT_TOL = 1e-8
CLUSTER_TOL = 1e-8
RECONSTRUCTION_TOL = 1e-8
GAMMA = (np.sqrt(5) - 1) / 2


# Standard linear algebra helpers


def random_unitary(d: int, rng: np.random.Generator) -> np.ndarray:
    z = (rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


def unitary_polar(M: np.ndarray) -> np.ndarray:
    """Return the unitary polar factor without forming the positive factor."""
    left, _, right = np.linalg.svd(M)
    return left @ right


def block_diag(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Return A when the top qubit is 0 and B when it is 1."""
    d = A.shape[0]
    out = np.zeros((2 * d, 2 * d), dtype=complex)
    out[:d, :d], out[d:, d:] = A, B
    return out


def tensor_factors(U: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Factor a product unitary U = A tensor B by a rank-one reshuffling."""
    reshuffled = U.reshape(2, 2, 2, 2).transpose(0, 2, 1, 3).reshape(4, 4)
    left, values, right = np.linalg.svd(reshuffled)
    A = np.sqrt(values[0]) * left[:, 0].reshape(2, 2)
    B = np.sqrt(values[0]) * right[0].reshape(2, 2)
    assert np.max(np.abs(U - np.kron(A, B))) <= UNIT_TOL
    return A, B


def unitary_phases(C: np.ndarray) -> np.ndarray:
    """Resolve unitary eigenphases using a Hermitian pencil and clustered solves."""
    Ch = C.conj().T
    w, V = sl.eigh((C + Ch) / 2 + GAMMA * (C - Ch) / 2j, driver="evd")
    lam = np.einsum("ij,ij->j", V.conj(), C @ V)
    i, D = 0, len(w)
    while i < D - 1:
        j = i
        while j < D - 1 and w[j + 1] - w[j] < CLUSTER_TOL:
            j += 1
        if j > i:
            block = V[:, i:j + 1]
            lam[i:j + 1] = np.linalg.eigvals(block.conj().T @ C @ block)
        i = j + 1
    assert np.max(np.abs(np.abs(lam) - 1)) <= UNIT_TOL, (
        "Computed eigenvalues of C are not unimodular"
    )
    return np.angle(lam)


# Quantum circuit helpers


def rx(t: float) -> np.ndarray:
    c, s = np.cos(t / 2), -1j * np.sin(t / 2)
    return np.array([[c, s], [s, c]])


def ry(t: float) -> np.ndarray:
    c, s = np.cos(t / 2), np.sin(t / 2)
    return np.array([[c, -s], [s, c]], dtype=complex)


def rz(t: float) -> np.ndarray:
    return np.diag([np.exp(-1j * t / 2), np.exp(1j * t / 2)])


def embed(M: np.ndarray, qs: list[int], n: int) -> np.ndarray:
    """Embed M on qubits qs; qs[0] is its least significant bit."""
    k = len(qs)
    d = 2**n
    out = np.zeros((d, d), dtype=complex)
    rest_mask = ~sum(1 << q for q in qs)
    for j in range(d):
        sub_j = sum(((j >> q) & 1) << b for b, q in enumerate(qs))
        base = j & rest_mask
        for sub_i in range(2**k):
            i = base | sum(((sub_i >> b) & 1) << q for b, q in enumerate(qs))
            out[i, j] = M[sub_i, sub_j]
    return out


def gate_matrix(g: tuple, n: int) -> np.ndarray:
    if g[0] == "u":
        return embed(g[2], [g[1]], n)
    control, target = g[1:]
    indices = np.arange(2**n)
    outputs = indices ^ (((indices >> control) & 1) << target)
    return np.eye(2**n, dtype=complex)[:, outputs]


def circuit_matrix(circ: list[tuple], n: int) -> np.ndarray:
    M = np.eye(2**n, dtype=complex)
    for g in circ:
        M = gate_matrix(g, n) @ M
    return M


def cnot_count(circ: list[tuple]) -> int:
    return sum(g[0] == "cx" for g in circ)


def mux_rot(thetas: np.ndarray, n: int, axis: str = "z") -> list[tuple]:
    """Expand a top-qubit multiplexed rotation in Gray-code order."""
    k = n - 1
    t = n - 1
    R = rz if axis == "z" else ry
    if k == 0:
        return [("u", t, R(thetas[0]))]
    gray = [i ^ (i >> 1) for i in range(2**k)]
    sign = np.array([
        [(-1) ** bin(j & g).count("1") for g in gray] for j in range(2**k)
    ])
    phis = np.linalg.solve(sign, thetas)
    circ = []
    for i in range(2**k):
        circ.append(("u", t, R(phis[i])))
        flip = gray[i] ^ gray[(i + 1) % 2**k]
        circ.append(("cx", flip.bit_length() - 1, t))
    return circ


def demultiplex(
    U1: np.ndarray, U2: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    T, V = schur(U1 @ U2.conj().T, output="complex")
    # Keep phase factors on the unit circle to prevent recursive norm drift.
    d = np.exp(0.5j * np.angle(np.diag(T)))
    W = np.diag(d) @ V.conj().T @ U2
    thetas = -2 * np.angle(d)
    return V, thetas, W


def block_zxz(U: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Return the four unitary factors of the Block-ZXZ decomposition."""
    d = U.shape[0] // 2
    Xb, Yb, U21, U22 = U[:d, :d], U[:d, d:], U[d:, :d], U[d:, d:]
    UX, SX = polar(Xb, side="left")
    UY, SY = polar(Yb, side="left")
    Cd = 1j * UY.conj().T @ UX
    C = Cd.conj().T
    A1 = (SX + 1j * SY) @ UX
    A2 = U21 + U22 @ Cd
    B = 2 * A1.conj().T @ Xb - np.eye(d)
    return A1, A2, B, C


# Canonical two-qubit synthesis (Shende, Markov, and Bullock)


def magic_spectrum(U: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Diagonalize the SMB invariant in a real orthonormal magic-basis frame."""
    M = MAGIC.conj().T @ U @ MAGIC
    S = M @ M.T
    values, basis = sl.eigh(S.real)
    edges = np.r_[0, np.flatnonzero(np.diff(values) > CLUSTER_TOL) + 1, 4]
    for i, j in zip(edges[:-1], edges[1:]):
        block = basis[:, i:j]
        _, rotation = sl.eigh(block.T @ S.imag @ block)
        basis[:, i:j] = block @ rotation
    return np.diag(basis.T @ S @ basis), basis


def leaf(U: np.ndarray, want_diag: bool) -> tuple[list[tuple], np.ndarray]:
    """SMB synthesis: three CX gates, or two with a left diagonal carry."""
    phase = np.exp(0.25j * np.angle(np.linalg.det(U)))
    U = U / phase
    diagonal = np.ones(4, dtype=complex)
    if want_diag:
        # Choose D so tr(gamma(D^dagger U)) is real: the two-CX criterion.
        w = np.diag(U @ YY @ U.T @ YY)
        even, odd = w[0] + w[3], w[1] + w[2]
        g = 0.5 * np.arctan2((even + odd).imag, (even - odd).real)
        diagonal = np.exp(1j * g * np.array([1, -1, -1, 1]))
        U = diagonal.conj()[:, None] * U

    lam, basis = magic_spectrum(U)
    if want_diag:
        # Pick one eigenphase from each conjugate pair.
        partner = 1 + np.argmin(np.abs(lam[1:] - lam[0].conj()))
        other = next(k for k in range(1, 4) if k != partner)
        x, y = np.angle(lam[[0, other]])
        core = [
            ("cx", 0, 1), ("u", 1, rz((x + y) / 2)),
            ("u", 0, rx((x - y) / 2)), ("cx", 0, 1),
        ]
        core_phase = 1.0
    else:
        # SMB Prop. V.1, with exp(i*pi/4) normalizing the three-CX core.
        t = np.angle(-1j * lam)
        a, b, d = -(t[0] + t[1]) / 2, -(t[0] + t[2]) / 2, (t[1] + t[2]) / 2
        core = [
            ("cx", 0, 1), ("u", 1, rz(d)), ("u", 0, ry(b)),
            ("cx", 1, 0), ("u", 0, ry(a)), ("cx", 0, 1),
        ]
        core_phase = np.exp(1j * np.pi / 4)

    # Match invariant eigenframes to recover U = L V R with local L and R.
    V = core_phase * circuit_matrix(core, 2)
    mu, frame = magic_spectrum(V)
    _, order = linear_sum_assignment(np.abs(lam[:, None] - mu[None, :]))
    frame = frame[:, order]
    assert np.max(np.abs(lam - mu[order])) <= UNIT_TOL
    basis[:, 0] *= np.sign(np.linalg.det(basis))
    frame[:, 0] *= np.sign(np.linalg.det(frame))
    L = MAGIC @ (basis @ frame.T) @ MAGIC.conj().T
    R = V.conj().T @ L.conj().T @ U
    l1, l0 = tensor_factors(L)
    r1, r0 = tensor_factors(R)
    circuit = [("u", 1, r1), ("u", 0, r0)] + core + [("u", 1, l1), ("u", 0, l0)]
    return circuit, phase * core_phase * np.diag(diagonal)


# Routines presented in "An improved algorithm for arbitary unitary synthesis"


def wrap(x):
    """Reduce angles to [-pi, pi)."""
    return (x + np.pi) % (2 * np.pi) - np.pi


def cyclic_split(mu: np.ndarray) -> tuple[np.ndarray, float]:
    """Find the best contiguous half of the circular eigenphase order."""
    mu = np.asarray(mu)
    D = len(mu)
    order = np.argsort(mu)
    phases = mu[order]
    half = D // 2
    prefix = np.r_[0.0, np.cumsum(phases)]
    sums = prefix[half:D] - prefix[:half]
    residuals = np.abs(wrap(2 * sums - phases.sum()))
    start = int(np.argmin(residuals))
    return order[start:start + half], float(residuals[start])


def ordered_phases(mu: np.ndarray, phase: float) -> np.ndarray:
    """Lift sorted principal phases to one turn with the specified total phase."""
    phases = np.sort(mu)
    total = phases.sum()
    assert abs(wrap(total - phase)) <= np.pi / 2, (
        "Determinant phase disagrees with the eigenphases"
    )
    turns = round((phase - total) / (2 * np.pi))
    whole, shift = divmod(turns, len(phases))
    return np.r_[phases[shift:], phases[:shift] + 2 * np.pi] + 2 * np.pi * whole


def _choose_alpha(rho: np.ndarray) -> tuple[float, np.ndarray]:
    """Choose the widest interval with equal upper/lower half-plane counts."""
    crossings = np.sort(np.mod(-np.angle(rho), np.pi))
    edges = np.r_[crossings, crossings[0] + np.pi]
    best = None
    for lo, hi in zip(edges[:-1], edges[1:]):
        alpha = (lo + hi) / 2
        tau = np.exp(1j * alpha) * rho
        if hi > lo and np.count_nonzero(tau.imag > 0) == len(rho) // 2:
            if best is None or hi - lo > best[0]:
                best = hi - lo, alpha, tau
    assert best is not None, "No resolved equal-count interval"
    return best[1], best[2]


def find_pivot(U: np.ndarray) -> tuple[float, float]:
    """Balance the middle-half eigenphase sum along a cached pivot path."""
    D = len(U) // 2
    X, Y = U[:D, :D], U[:D, D:]
    # These direct pivots also cover simple singular blocks, such as Y = 0.
    for beta in (0.0, np.pi / 2):
        c, s = np.cos(beta / 2), np.sin(beta / 2)
        C = (-1j * unitary_polar(c * X + s * Y).conj().T
             @ unitary_polar(-s * X + c * Y))
        if cyclic_split(unitary_phases(C))[1] <= ROOT_TOL:
            return 0.0, beta
    alpha, tau = _choose_alpha(np.linalg.eigvals(np.linalg.solve(X, Y)))

    # Cache X_g^dagger Y_g = K + cos(beta) A + sin(beta) B.
    cross = np.exp(1j * alpha) * (X.conj().T @ Y)
    A, K = (cross + cross.conj().T) / 2, (cross - cross.conj().T) / 2
    B = (Y.conj().T @ Y - X.conj().T @ X) / 2
    tau_phases = np.angle(tau)
    quarter = D // 4

    def imbalance(beta: float) -> float:
        C = -1j * unitary_polar(K + np.cos(beta) * A + np.sin(beta) * B)
        c, s = np.cos(beta / 2), np.sin(beta / 2)
        phase = np.sum(
            tau_phases + np.angle(c - s / tau) - np.angle(c + s * tau)
        )
        theta = ordered_phases(unitary_phases(C), phase)
        middle = theta[quarter:3 * quarter]
        outer = np.r_[theta[:quarter], theta[3 * quarter:]]
        return float(np.sum(middle - outer) / 2)

    lo, hi = imbalance(0.0), imbalance(np.pi)
    if 2 * abs(lo) <= ROOT_TOL:
        return alpha, 0.0
    if 2 * abs(hi) <= ROOT_TOL:
        return alpha, np.pi
    assert np.signbit(lo) != np.signbit(hi), "Pivot does not bracket a root"
    beta, result = brentq(
        imbalance, 0.0, np.pi, xtol=1e-15,
        rtol=4 * np.finfo(float).eps, maxiter=200, full_output=True, disp=False,
    )
    assert result.converged and 2 * abs(imbalance(beta)) <= TOL
    return alpha, beta


def demux_double_fold(C: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Recover the contiguous split at a pivot root and zero its Gray angle."""
    D = len(C)
    V, theta, W = demultiplex(np.eye(D, dtype=complex), C)
    S, residual = cyclic_split(theta)
    assert residual <= TOL, f"Unbalanced contiguous split ({residual:.2e})"
    mask = np.ones(D, dtype=bool)
    mask[S] = False
    perm = np.r_[S, np.flatnonzero(mask)]
    V, theta, W = V[:, perm], theta[perm], W[perm, :]

    # The relevant Walsh row is +1 on the first half, -1 on the second half.
    difference = theta[:D // 2].sum() - theta[D // 2:].sum()
    turns = int(round(difference / (2 * np.pi)))
    theta[0] -= 2 * np.pi * turns
    if turns % 2:
        W[0] *= -1
    angle = (theta[:D // 2].sum() - theta[D // 2:].sum()) / D
    assert abs(angle) <= TOL, (
        f"Branch adjustment did not zero the Gray-code angle ({angle:.2e})"
    )
    return V, theta, W


def apply_pivot(U: np.ndarray, u: np.ndarray) -> np.ndarray:
    """Right-multiply by u on the top qubit, without forming a dense embedded gate."""
    D = len(U) // 2
    return np.concatenate(
        (u[0, 0] * U[:, :D] + u[1, 0] * U[:, D:],
         u[0, 1] * U[:, :D] + u[1, 1] * U[:, D:]),
        axis=1,
    )


def synth(
    U: np.ndarray, n: int, want_diag: bool = False,
) -> tuple[list[tuple], np.ndarray]:
    """Return a circuit and diagonal carry representing U."""
    if n == 1:
        return [("u", 0, U)], np.eye(2, dtype=complex)
    if n == 2:
        return leaf(U, want_diag)
    top = n - 1
    alpha, beta = find_pivot(U)
    u = rz(alpha) @ ry(beta)
    A1, A2, B, C = block_zxz(apply_pivot(U, u))

    Va, theta_a, Wa = demultiplex(A1, A2)
    Vc, theta_c, Wc = demux_double_fold(C)
    z_hi = embed(Z, [n - 2], n - 1)
    z_both = z_hi @ embed(Z, [0], n - 1)
    Vb, theta_b, Wb = demultiplex(Wa @ Vc, z_hi @ Wa @ B @ Vc @ z_both)

    mux_c = mux_rot(theta_c, n)[:-3]
    mux_a = mux_rot(theta_a, n)[::-1][1:]
    mux_b = [("u", top, H)] + mux_rot(theta_b, n) + [("u", top, H)]
    circ = [("u", top, u.conj().T)]
    children = [Wc, Wb, Vb, Va]
    muxes = [mux_c, mux_b, mux_a, []]
    carry = np.eye(2 ** (n - 1), dtype=complex)
    for i, (child, mux) in enumerate(zip(children, muxes)):
        sub, carry = synth(
            child @ carry, n - 1, want_diag=want_diag or i < len(children) - 1
        )
        circ += sub + mux
    return circ, block_diag(carry, carry)


def decompose(U: np.ndarray) -> tuple[list[tuple], np.ndarray]:
    """Decompose a unitary of power-of-two dimension, at least two."""
    U = np.asarray(U, dtype=complex)
    return synth(U, len(U).bit_length() - 1)


# Reproducible numerical validation


def cnot_formula(n: int) -> int:
    """Return the improved synthesis CX count for n >= 1."""
    return (21 * 4**n - 72 * 2**n + 96) // 48


def zxz_formula(n: int) -> int:
    """Return the reference Block-ZXZ CX count for n >= 1."""
    return (22 * 4**n - 72 * 2**n + 80) // 48


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "qubits", nargs="*", type=int, default=[3, 4],
        help="qubit counts to validate (default: 3 4)",
    )
    parser.add_argument(
        "--samples", type=int, default=1,
        help="Haar-random targets per qubit count (default: 1)",
    )
    parser.add_argument(
        "--seed", type=int, default=0,
        help="seed for target generation (default: 0)",
    )
    args = parser.parse_args(argv)
    print(
        f"Python {platform.python_version()}, NumPy {np.__version__}, "
        f"SciPy {scipy.__version__}; seed={args.seed}, samples={args.samples}",
        flush=True,
    )
    rng = np.random.default_rng(args.seed)
    for n in args.qubits:
        for sample in range(args.samples):
            target = random_unitary(2**n, rng)
            circuit, diagonal = decompose(target)
            reconstructed = diagonal @ circuit_matrix(circuit, n)
            error = float(np.max(np.abs(target - reconstructed)))
            count = cnot_count(circuit)
            assert count == cnot_formula(n), f"Unexpected CX count: {count}"
            assert error <= RECONSTRUCTION_TOL, f"Reconstruction error: {error:.3e}"
            print(
                f"n={n}, sample={sample + 1}: {count} CX "
                f"(Block-ZXZ: {zxz_formula(n)}), max error={error:.3e}",
                flush=True,
            )


if __name__ == "__main__":
    main()
