"""Block-ZXZ with one extra CNOT fold per node: c(n) = (21·4^n − 72·2^n + 96)/48 CNOTs.

At each node a free top-qubit gate u = Rz(α)·Ry(β*) is applied at the input (U is decomposed as
(U·u)·u†). The parity rule picks α and the intermediate value theorem gives β* (fold_ivt.py),
so that the eigenphases of the block-ZXZ factor C split into two halves with equal sums mod 2π.
Placing one half on the lower-register states with top control bit 0 makes the Gray-code angle
between the input-side multiplexor's last two CNOTs, CX(q0, top) and CX(q_{n-2}, top), vanish.
Both CNOTs then fold into the central factor as I ⊕ Z_{q0} Z_{q_{n-2}}.

Usage: python3 foldzxz.py [n ...]   (default: n = 3 4)
"""
import sys

import numpy as np

from core import H, Z, block_diag, block_zxz, circuit_matrix, cnot_count, demultiplex, embed, \
    mux_rot, random_unitary
from fold_ivt import choose_alpha, top_gate
from pfaff_general import half_splits
from zxz import leaf

N_SCAN = 100        # grid points for the sign-change scan of β on [0, π]
N_BISECT = 50       # bisection steps once a sign change is bracketed
TOL = 1e-7          # tolerance for an exact balanced split / vanishing Gray angle


def wrap(x):
    """Map angles to (−π, π]."""
    return (x + np.pi) % (2 * np.pi) - np.pi


def split_sign(mu, splits):
    """Sign of the test function P = ∏ 2 sin(ψ_S) for eigenphases mu normalized to det 1."""
    return np.prod(np.sign([np.sin((mu[list(S)].sum() - mu[list(Sc)].sum()) / 2)
                            for S, Sc in splits]))


def c_factor(U, n, alpha, beta):
    """Block-ZXZ factor C of U·u(α, β), with u acting on the top qubit."""
    return block_zxz(U @ embed(top_gate(alpha, beta), [n - 1], n))[3]


def normalized_phases(C, ref_mu=None, ref_det_phase=None):
    """Eigenphases of C / det(C)^(1/D). Given a reference point (ref_mu, ref_det_phase), the root
    and the eigenvalue order are tracked from it so that they vary continuously along a path."""
    D = C.shape[0]
    lam = np.linalg.eigvals(C)
    det_phase = np.angle(np.prod(lam))
    if ref_det_phase is not None:
        det_phase = ref_det_phase + wrap(det_phase - ref_det_phase)
    mu = np.angle(lam * np.exp(-1j * det_phase / D))
    if ref_mu is not None:                       # match each reference eigenvalue to its nearest
        order = []
        for pm in ref_mu:
            dist = np.abs(np.exp(1j * mu) - np.exp(1j * pm))
            dist[order] = np.inf
            order.append(int(np.argmin(dist)))
        mu = ref_mu + wrap(mu[order] - ref_mu)
    return mu, det_phase


def find_beta(U, n, alpha):
    """β* ∈ [0, π] at which C(β) has a balanced split: scan for a sign change of the tracked test
    function (guaranteed by the parity rule), then bisect."""
    splits = half_splits(2 ** (n - 1))

    def state(beta, ref_mu=None, ref_det_phase=None):
        mu, det_phase = normalized_phases(c_factor(U, n, alpha, beta), ref_mu, ref_det_phase)
        return split_sign(mu, splits), mu, det_phase

    lo = 0.0
    g_lo, mu_lo, a_lo = state(lo)
    for hi in np.linspace(0, np.pi, N_SCAN + 1)[1:]:
        g_hi, mu_hi, a_hi = state(hi, mu_lo, a_lo)
        if g_hi != g_lo:
            for _ in range(N_BISECT):
                mid = (lo + hi) / 2
                g_mid, mu_mid, a_mid = state(mid, mu_lo, a_lo)
                if g_mid == g_lo:
                    lo, mu_lo, a_lo = mid, mu_mid, a_mid
                else:
                    hi = mid
            return (lo + hi) / 2
        lo, g_lo, mu_lo, a_lo = hi, g_hi, mu_hi, a_hi
    raise RuntimeError("no sign change on [0, π]; parity rule violated?")


def walsh_angles(thetas):
    """Gray-code rotation angles φ_k of the multiplexed rotation with angles θ_j."""
    k = int(np.log2(len(thetas)))
    gray = [i ^ (i >> 1) for i in range(2**k)]
    sign = np.array([[(-1) ** bin(j & g).count("1") for g in gray] for j in range(2**k)])
    return np.linalg.solve(sign, thetas)


def demux_double_fold(C):
    """Demultiplex I ⊕ C = (I ⊗ V) Δ(θ) (I ⊗ W) so that the last Gray-code angle is exactly 0.

    The eigenvalues of a balanced split S go to the states whose top control bit is 0, and 2π
    branch shifts (each flipping the sign of one row of W) remove the remaining multiple of 2π/D."""
    D = C.shape[0]
    V, theta, W = demultiplex(np.eye(D, dtype=complex), C)
    residual, S, Sc = min((abs(wrap(theta[list(S)].sum() - theta[list(Sc)].sum())), S, Sc)
                          for S, Sc in half_splits(D))
    if residual > TOL:
        raise ValueError(f"C has no balanced split (residual {residual:.1e})")

    top_bit = D // 2
    slots0 = [j for j in range(D) if not j & top_bit]
    slots1 = [j for j in range(D) if j & top_bit]
    perm = np.empty(D, dtype=int)
    perm[slots0], perm[slots1] = S, Sc
    V, theta, W = V[:, perm], theta[perm], W[perm, :]

    # φ_last = (Σ_slots0 θ − Σ_slots1 θ)/D, so each 2π shift on a slots0 entry moves it by 2π/D
    steps = int(round(walsh_angles(theta)[-1] / (2 * np.pi / D)))
    flips = np.ones(D)
    for i in range(abs(steps)):
        j = slots0[i % len(slots0)]
        theta[j] -= np.sign(steps) * 2 * np.pi
        flips[j] *= -1                           # R_z(θ + 2π) = −R_z(θ)
    assert abs(walsh_angles(theta)[-1]) < TOL
    return V, theta, np.diag(flips) @ W


def synth(U, n, want_diag=False):
    """Circuit for U (up to a returned diagonal if want_diag), as a gate list and that diagonal."""
    if n == 2:
        return leaf(U, want_diag)
    top = n - 1
    alpha = choose_alpha(U, n)
    u = top_gate(alpha, find_beta(U, n, alpha))
    A1, A2, B, C = block_zxz(U @ embed(u, [top], n))       # U = (U·u)·u†, u† applied first

    Va, theta_a, Wa = demultiplex(A1, A2)
    Vc, theta_c, Wc = demux_double_fold(C)
    z_hi = embed(Z, [n - 2], n - 1)                        # fold from the output-side multiplexor
    z_both = z_hi @ embed(Z, [0], n - 1)                   # double fold from the input side
    Vb, theta_b, Wb = demultiplex(Wa @ Vc, z_hi @ Wa @ B @ Vc @ z_both)

    mux_c = mux_rot(theta_c, n)[:-3]                       # drop the two folded CNOTs and Rz(0)
    mux_a = mux_rot(theta_a, n)[::-1][1:]                  # mirrored; drop the folded CNOT
    mux_b = [("u", top, H)] + mux_rot(theta_b, n) + [("u", top, H)]

    circ = [("u", top, u.conj().T)]
    children = [Wc, Wb, Vb, Va]
    muxes = [mux_c, mux_b, mux_a, []]
    carry = np.eye(2 ** (n - 1), dtype=complex)            # diagonal passed to the next child
    for i, (child, mux) in enumerate(zip(children, muxes)):
        is_last = i == len(children) - 1
        sub, carry = synth(child @ carry, n - 1, want_diag=want_diag or not is_last)
        circ += sub + mux
    return circ, block_diag(carry, carry)


def cnot_formula(n):
    """CNOT count of this construction, c(n) = 4c(n−1) + 3·2^(n−1) − 6 with c(2) = 3."""
    return (21 * 4**n - 72 * 2**n + 96) // 48


def zxz_formula(n):
    """CNOT count of block-ZXZ, (22·4^n − 72·2^n + 80)/48."""
    return (22 * 4**n - 72 * 2**n + 80) // 48


def main(ns, samples=1, seed=0):
    rng = np.random.default_rng(seed)
    for n in ns:
        for _ in range(samples):
            U = random_unitary(2**n, rng)
            circ, diag = synth(U, n)
            M = diag @ circuit_matrix(circ, n)
            phase = np.vdot(M.ravel(), U.ravel())
            phase /= abs(phase)
            print(f"n={n}: {cnot_count(circ)} CNOTs (formula {cnot_formula(n)}, "
                  f"block-ZXZ {zxz_formula(n)}), "
                  f"max |U - e^(iφ)·circuit| = {np.max(np.abs(U - phase * M)):.1e}", flush=True)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]] or [3, 4])
