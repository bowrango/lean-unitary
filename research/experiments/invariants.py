"""Two-qubit CNOT-count invariants (Shende, Bullock, Markov, quant-ph/0308045).

For U in U(4) normalized to det U = 1, let  γ(U) = U (Y⊗Y) Uᵀ (Y⊗Y).
  * U needs 0 CNOTs  iff  γ(U) = ±I
  * U needs ≤ 1 CNOT iff  tr γ(U) = 0 and γ(U)² = -I
  * U needs ≤ 2 CNOTs iff  tr γ(U) is real
(each "up to single-qubit gates"). Diagonal gates change the class only through their Z⊗Z part.
"""

from __future__ import annotations

import numpy as np
from scipy.optimize import brentq

YY = np.kron(np.array([[0, -1j], [1j, 0]]), np.array([[0, -1j], [1j, 0]]))
ZZ = np.diag([1, -1, -1, 1]).astype(complex)


def gamma(U: np.ndarray) -> np.ndarray:
    U = U / np.linalg.det(U) ** 0.25
    return U @ YY @ U.T @ YY


def zz(g: float) -> np.ndarray:
    return np.diag(np.exp(1j * g * np.diag(ZZ).real))


def two_cnot_residual(U: np.ndarray) -> float:
    return float(np.imag(np.trace(gamma(U))))


def one_cnot_residual(U: np.ndarray) -> np.ndarray:
    G = gamma(U)
    t = np.trace(G)
    R = G @ G + np.eye(4)
    return np.concatenate([[t.real, t.imag], R.real.ravel(), R.imag.ravel()])


def zz_roots_two_cnot(V: np.ndarray, grid: int = 256) -> list[float]:
    """All g in [0, π) with tr γ(e^{-igZZ} V) real: the Z⊗Z parts of the diagonals δ for which
    δ⁻¹ V needs only 2 CNOTs."""
    f = lambda g: two_cnot_residual(zz(-g) @ V)
    xs = np.linspace(0, np.pi, grid + 1)
    ys = [f(x) for x in xs]
    roots = []
    for a, b, fa, fb in zip(xs, xs[1:], ys, ys[1:]):
        if fa == 0:
            roots.append(a)
        elif fa * fb < 0:
            roots.append(brentq(f, a, b, xtol=1e-15))
    return roots


def zz_roots_two_cnot_exact(V: np.ndarray) -> list[float]:
    """Closed form of `zz_roots_two_cnot`. Z⊗Z commutes with Y⊗Y conjugation, so with
    D = e^{-igZZ} and A = V YY Vᵀ (det V normalized), tr γ(DV) = tr(D² A YY)
    = e^{-2ig}(w0 + w3) + e^{2ig}(w1 + w2), w = diag(A YY): a single sinusoid in 2g.
    Returns its two roots in [0, π), ordered by branch (h0/2, h0/2 + π/2)."""
    V = V / np.linalg.det(V) ** 0.25
    w = np.diag(V @ YY @ V.T @ YY)
    a, b = w[0] + w[3], w[1] + w[2]
    h0 = np.arctan2(a.imag + b.imag, a.real - b.real)
    g0 = (h0 / 2) % (np.pi / 2)
    return [g0, g0 + np.pi / 2]
