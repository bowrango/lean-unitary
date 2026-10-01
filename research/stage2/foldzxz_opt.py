"""Extra-fold Block-ZXZ synthesis with a single, predetermined spectral split.

Choose alpha so exactly half the eigenvalues of exp(i alpha) X^-1 Y are in
each half-plane. Ordered eigenphase lifts of C then reverse and negate between
beta = 0 and pi. Their middle half defines a continuous imbalance with opposite
endpoint signs, so scalar bisection finds a balanced split. Each trial uses one
SVD and one eigensolve on D-by-D matrices, plus O(D log D) phase sorting; no
combinatorial subset list is formed.

The numerical search handles generic, nonsingular paths. Simple balanced
inputs and quarter-turns are accepted directly. Other exceptional or unresolved
ill-conditioned inputs raise an error; the existence proof's limiting argument
is not a floating-point algorithm for selecting singular polar factors.

Usage: python3 foldzxz_opt.py [n ...]   (default: n = 3 4)
"""

import sys

import numpy as np

from core import (H, Z, block_diag, block_zxz, circuit_matrix, cnot_count,
                  demultiplex, embed, mux_rot, random_unitary)
from fold_ivt import top_gate
from foldzxz import cnot_formula, zxz_formula
from zxz import leaf


ROOT_TOL = 2e-13       # balanced-split phase residual targeted by bisection
TOL = 1e-7            # maximum accepted balanced-split phase residual
N_BISECT = 60


def wrap(x):
    """Reduce angles to [-pi, pi)."""
    return (x + np.pi) % (2 * np.pi) - np.pi


def cyclic_split(mu):
    """Best contiguous half in circular order of principal eigenphases.

    There are only D/2 distinct candidates. The middle half of any ordered lift
    is one of these, so a root of PivotPath's imbalance must be recovered here.
    This does not attempt a general subset-sum search for an arbitrary spectrum.
    Return the indices in the original order and the absolute phase residual.
    """
    mu = np.asarray(mu)
    D = len(mu)
    if D < 4 or D % 4:
        raise ValueError("The block dimension must be a positive multiple of four")
    order = np.argsort(mu)
    phases = mu[order]
    half = D // 2
    prefix = np.r_[0.0, np.cumsum(phases)]
    sums = prefix[half:D] - prefix[:half]
    residuals = np.abs(wrap(2 * sums - phases.sum()))
    start = int(np.argmin(residuals))
    return order[start:start + half], float(residuals[start])


def ordered_phases(mu, phase):
    """Lift sorted principal eigenphases to a span <= 2*pi and total phase.

    Raising the smallest phase by 2*pi moves it to the end and adds one turn
    to the total. Quotient/remainder implements any number of these cyclic
    shifts at once. The analytic total fixes the lift at each beta independently.
    """
    phases = np.sort(mu)
    total = phases.sum()
    if abs(wrap(total - phase)) > TOL:
        raise RuntimeError("Determinant phase is numerically inconsistent; pivot path "
                           "is too ill-conditioned")
    turns = round((phase - total) / (2 * np.pi))
    whole, shift = divmod(turns, len(phases))
    return np.r_[phases[shift:], phases[:shift] + 2 * np.pi] + 2 * np.pi * whole


def _choose_alpha(rho):
    """Midpoint of the widest interval with equal upper/lower half-plane counts."""
    if not np.all(np.isfinite(rho)) or np.any(np.abs(rho) == 0):
        raise ValueError("The pivot path requires finite, nonzero eigenvalues of X^-1 Y")
    crossings = np.sort(np.mod(-np.angle(rho), np.pi))
    edges = np.r_[crossings, crossings[0] + np.pi]
    best = None
    for lo, hi in zip(edges[:-1], edges[1:]):
        if hi <= lo:
            continue
        alpha = (lo + hi) / 2
        tau = np.exp(1j * alpha) * rho
        # Relative angular separation also rejects unresolved near-coincidences.
        separated = np.min(np.abs(tau.imag) / np.abs(tau)) > 64 * np.finfo(float).eps
        if separated and np.count_nonzero(tau.imag > 0) == len(rho) // 2:
            if best is None or hi - lo > best[0]:
                best = hi - lo, alpha, tau
    if best is None:
        raise ValueError("No resolved equal-count interval; crossing angles are degenerate "
                         "or too close for floating-point arithmetic")
    return best[1], best[2]


class PivotPath:
    """Cached path with a continuous middle-half imbalance and opposite endpoint values."""

    def __init__(self, U, n):
        D = 2 ** (n - 1)
        if n < 3 or U.shape != (2 * D, 2 * D):
            raise ValueError("A pivot requires a 2**n square unitary with n >= 3")
        self.D = D
        X, Y = U[:D, :D], U[:D, D:]
        try:
            rho = np.linalg.eigvals(np.linalg.solve(X, Y))
        except np.linalg.LinAlgError as error:
            raise ValueError("Cannot construct a nonsingular pivot path from these blocks") from error
        self.alpha, self.tau = _choose_alpha(rho)
        self.t = np.angle(self.tau)

        # X_g^dagger Y_g = K + cos(beta) H + sin(beta) B.
        A = np.exp(1j * self.alpha) * (X.conj().T @ Y)
        self.H = (A + A.conj().T) / 2
        self.K = (A - A.conj().T) / 2
        self.B = (Y.conj().T @ Y - X.conj().T @ X) / 2

    def C(self, beta):
        """Compute only C, using the unitary polar factor of X_g^dagger Y_g."""
        M = self.K + np.cos(beta) * self.H + np.sin(beta) * self.B
        left, _, right = np.linalg.svd(M)
        return -1j * (left @ right)

    def determinant_phase(self, beta):
        """Continuous total phase sigma(beta), with sigma(pi) = -sigma(0)."""
        c, s = np.cos(beta / 2), np.sin(beta / 2)
        return np.sum(self.t + np.angle(c - s / self.tau) - np.angle(c + s * self.tau))

    def state(self, beta):
        """Return the middle-half imbalance and its (unwrapped) split residual."""
        mu = np.angle(np.linalg.eigvals(self.C(beta)))
        theta = ordered_phases(mu, self.determinant_phase(beta))
        quarter = self.D // 4
        # Pairwise summation avoids subtracting two large total phase sums.
        middle = theta[quarter:3 * quarter]
        outer = np.r_[theta[:quarter], theta[3 * quarter:]]
        imbalance = float(np.sum(middle - outer) / 2)
        return imbalance, 2 * abs(imbalance)

    def find_beta(self):
        """Bisect the imbalance of one fixed split; no subset enumeration is needed."""
        lo, hi = 0.0, np.pi
        value_lo, residual_lo = self.state(lo)
        if residual_lo <= ROOT_TOL:
            return lo
        value_hi, residual_hi = self.state(hi)
        if residual_hi <= ROOT_TOL:
            return hi
        if np.signbit(value_lo) == np.signbit(value_hi):
            raise RuntimeError("Pivot endpoints do not have opposite imbalances; numerical "
                               "conditioning prevents a reliable bracket")
        best = min((residual_lo, lo), (residual_hi, hi))
        for _ in range(N_BISECT):
            mid = (lo + hi) / 2
            if mid == lo or mid == hi:
                break
            value_mid, residual = self.state(mid)
            best = min(best, (residual, mid))
            if residual <= ROOT_TOL:
                return mid
            if np.signbit(value_mid) == np.signbit(value_lo):
                lo = mid
            else:
                hi = mid
        if best[0] > TOL:
            raise RuntimeError(f"Bisection did not resolve a balanced split ({best[0]:.2e})")
        return best[1]


def _direct_C(X, Y):
    """Use separate polar factors, including at singular trial blocks."""
    ux, _, vx = np.linalg.svd(X)
    uy, _, vy = np.linalg.svd(Y)
    return -1j * (ux @ vx).conj().T @ (uy @ vy)


def find_pivot(U, n):
    """Return (alpha, beta), checking simple balanced pivots before reporting degeneracy."""
    D = 2 ** (n - 1)
    if n < 3 or U.shape != (2 * D, 2 * D):
        raise ValueError("A pivot requires a 2**n square unitary with n >= 3")
    X, Y = U[:D, :D], U[:D, D:]
    C0 = _direct_C(X, Y)
    if cyclic_split(np.angle(np.linalg.eigvals(C0)))[1] <= ROOT_TOL:
        return 0.0, 0.0
    try:
        path = PivotPath(U, n)
    except ValueError:
        # For example, Y = 0 makes X^-1 Y unusable, but a quarter-turn gives C = i I.
        c, s = np.cos(np.pi / 4), np.sin(np.pi / 4)
        Cmid = _direct_C(c * X + s * Y, -s * X + c * Y)
        if cyclic_split(np.angle(np.linalg.eigvals(Cmid)))[1] <= ROOT_TOL:
            return 0.0, np.pi / 2
        raise
    return path.alpha, path.find_beta()


def demux_double_fold(C):
    """Recover a contiguous split from a pivot root and zero its Gray-code angle.

    A PivotPath root guarantees such a split; arbitrary balanced spectra need
    not have a contiguous solution. Only D/2 circular windows are checked.
    """
    D = len(C)
    V, theta, W = demultiplex(np.eye(D, dtype=complex), C)
    S, residual = cyclic_split(theta)
    if residual > TOL:
        raise ValueError(f"C has no balanced contiguous split (residual {residual:.2e})")
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
    if abs(angle) > TOL:
        raise RuntimeError(f"Branch adjustment did not zero the Gray-code angle ({angle:.2e})")
    return V, theta, W


def apply_pivot(U, u):
    """Right-multiply by u on the top qubit, without forming a dense embedded gate."""
    D = len(U) // 2
    return np.concatenate((u[0, 0] * U[:, :D] + u[1, 0] * U[:, D:],
                           u[0, 1] * U[:, :D] + u[1, 1] * U[:, D:]), axis=1)


def synth(U, n, want_diag=False):
    """Return a circuit and diagonal carry with U = carry @ circuit_matrix(circuit)."""
    if n < 1 or U.shape != (2 ** n, 2 ** n):
        raise ValueError("Expected a 2**n square unitary with n >= 1")
    if n == 1:
        return [("u", 0, U)], np.eye(2, dtype=complex)
    if n == 2:
        return leaf(U, want_diag)
    top = n - 1
    print("start")
    alpha, beta = find_pivot(U, n)
    print("stop")
    u = top_gate(alpha, beta)
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
        sub, carry = synth(child @ carry, n - 1,
                           want_diag=want_diag or i < len(children) - 1)
        circ += sub + mux
    return circ, block_diag(carry, carry)


def main(ns, samples=1, seed=0):
    rng = np.random.default_rng(seed)
    for n in ns:
        for _ in range(samples):
            U = random_unitary(2 ** n, rng)
            circ, diag = synth(U, n)
            M = diag @ circuit_matrix(circ, n)
            phase = np.vdot(M.ravel(), U.ravel())
            phase /= abs(phase)
            print(f"n={n}: {cnot_count(circ)} CNOTs (formula {cnot_formula(n)}, "
                  f"block-ZXZ {zxz_formula(n)}), "
                  f"max |U - e^(iφ)·circuit| = {np.max(np.abs(U - phase * M)):.1e}",
                  flush=True)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]] or [3, 4])
