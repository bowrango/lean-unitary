"""Double-fold conditions for 3-qubit block-ZXZ.

U = (A1⊕A2) H (I⊕B) H (I⊕C). The outer multiplexors come from demultiplexing I⊕C (eigenphases
of C) and A1⊕A2 (eigenphases of A1 A2†). An outer multiplexor can fold TWO CNOTs into the middle
iff the Walsh component sitting between its last two CNOTs is ≡ 0, which (using 2π branch shifts
and Pauli-frame absorption) holds iff its eigenphases satisfy μa+μb ≡ μc+μd (mod 2π) for some
pairing. Free parameters: single-qubit gates on the top qubit at the input and output of U."""
import numpy as np
from scipy.optimize import least_squares
from core import block_zxz, random_unitary, embed, ry, rz

def su2(p):
    return rz(p[0]) @ ry(p[1]) @ rz(p[2])

def wrap(x):
    return (x + np.pi) % (2 * np.pi) - np.pi

def pair_residuals(mu):
    """residuals of the 3 pairings (μa+μb-μc-μd mod 2π)"""
    a, b, c, d = mu
    return np.array([wrap(a + b - c - d), wrap(a + c - b - d), wrap(a + d - b - c)])

def phases(U):
    A1, A2, B, C = block_zxz(U)
    return np.angle(np.linalg.eigvals(C)), np.angle(np.linalg.eigvals(A1 @ A2.conj().T))

def conditioned(U, p):
    return embed(su2(p[3:]), [2], 3) @ U @ embed(su2(p[:3]), [2], 3)

def residual(U, p, which="both"):
    mc, ma = phases(conditioned(U, p))
    rc, ra = np.min(np.abs(pair_residuals(mc))), np.min(np.abs(pair_residuals(ma)))
    return {"C": rc, "A": ra, "both": np.hypot(rc, ra)}[which]

def solve(U, rng, which="both", starts=40):
    best = (np.inf, None)
    for _ in range(starts):
        p0 = rng.uniform(-np.pi, np.pi, 6)
        # smooth objective: pick the pairing active at the start, then solve the smooth equations
        def f(p):
            mc, ma = phases(conditioned(U, p))
            out = []
            if which in ("C", "both"):
                r = pair_residuals(mc); out.append(r[np.argmin(np.abs(r))])
            if which in ("A", "both"):
                r = pair_residuals(ma); out.append(r[np.argmin(np.abs(r))])
            return np.array(out)
        sol = least_squares(f, p0, xtol=1e-15, ftol=1e-15, gtol=1e-15)
        e = residual(U, sol.x, which)
        if e < best[0]: best = (e, sol.x)
        if e < 1e-12: break
    return best

if __name__ == "__main__":
    rng = np.random.default_rng(0)
    for t in range(10):
        U = random_unitary(8, rng)
        e0 = residual(U, np.zeros(6))
        e, p = solve(U, rng)
        print(f"target {t}: residual without freedom {e0:.2e}  →  with top-qubit gates {e:.1e}")
