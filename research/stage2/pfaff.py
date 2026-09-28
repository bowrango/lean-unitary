"""Fold condition as a sign-changing function.
For C ∈ U(4), C1 = C / det(C)^(1/4) ∈ SU(4), R = Λ²C1 ∈ SO(6) (real in the Hodge basis).
Fold condition (some pair of eigenphases with μa+μb ≡ μc+μd) ⇔ R has eigenvalue ±1
⇔ P = Pf(R - Rᵀ) = Π_j 2 sin ψ_j = 0."""
import itertools
import numpy as np
from core import block_zxz, embed, ry, random_unitary

PAIRS = list(itertools.combinations(range(4), 2))
def wedge2(C):
    M = np.zeros((6, 6), complex)
    for r, (i, j) in enumerate(PAIRS):
        for c, (k, l) in enumerate(PAIRS):
            M[r, c] = C[i, k] * C[j, l] - C[i, l] * C[j, k]
    return M
s = 1 / np.sqrt(2)
idx = {p: n for n, p in enumerate(PAIRS)}
def e(p): v = np.zeros(6, complex); v[idx[p]] = 1; return v
T = np.array([s * (e((0,1)) + e((2,3))), 1j * s * (e((0,1)) - e((2,3))),
              s * (e((0,2)) - e((1,3))), 1j * s * (e((0,2)) + e((1,3))),
              s * (e((0,3)) + e((1,2))), 1j * s * (e((0,3)) - e((1,2)))]).conj()

def pf(A):
    n = A.shape[0]
    if n == 0: return 1.0
    return sum((-1) ** (j + 1) * A[0, j] * pf(np.delete(np.delete(A, [0, j], 0), [0, j], 1))
               for j in range(1, n))

def R_of(C1):
    R = T @ wedge2(C1) @ T.conj().T
    assert np.max(np.abs(R.imag)) < 1e-9, np.max(np.abs(R.imag))
    return R.real

def scan(U, nb=2001):
    """P(β) along u_in = Ry(β) on the top qubit, β ∈ [0, 2π], 4th root of det C tracked continuously."""
    betas = np.linspace(0, 2 * np.pi, nb)
    out, prev = [], None
    for b in betas:
        C = block_zxz(U @ embed(ry(b), [2], 3))[3]
        a = np.angle(np.linalg.det(C))
        if prev is not None:
            a = prev + (a - prev + np.pi) % (2 * np.pi) - np.pi
        prev = a
        out.append(pf(R_of(C * np.exp(-1j * a / 4)) - R_of(C * np.exp(-1j * a / 4)).T))
    return betas, np.array(out)

if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for t in range(12):
        U = random_unitary(8, rng)
        b, P = scan(U)
        k = len(b) // 2
        ch = lambda lo, hi: int(np.sum(np.sign(P[lo:hi][1:]) != np.sign(P[lo:hi][:-1])))
        print(f"U{t:2d}: P(0)={P[0]:+.3f} P(π)={P[k]:+.3f} P(2π)={P[-1]:+.3f}  sign changes on [0,π]: {ch(0,k+1)}, [π,2π]: {ch(k,len(b))}")
