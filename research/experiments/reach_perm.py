"""Closest approach to a 1-CNOT last leaf, also varying the eigenvalue ordering of each
demultiplexing (V -> VΠ, D -> ΠᵀDΠ, W -> ΠᵀW), which changes the downstream leaves."""
import itertools, sys
import numpy as np
from scipy.optimize import minimize
from core import Z, block_diag, block_zxz, demultiplex, embed, random_unitary
from invariants import zz, zz_roots_two_cnot_exact
from reach import one_cnot_distance

PERMS = [np.eye(4)[list(p)].T for p in itertools.permutations(range(4))]

def demux_p(U1, U2, P):
    V, th, W = demultiplex(U1, U2)
    return V @ P, W if P is None else P.T @ W

def leaves(U, phi, Pa, Pb):
    D2 = np.diag(np.exp(1j * phi))
    A1, A2, B, C = block_zxz(block_diag(np.eye(4), D2.conj()) @ U)
    I = np.eye(4, dtype=complex)
    Va, Wa = demux_p(A1, A2, Pa)
    Vc, _, Wc = demultiplex(I, C)
    Zc = embed(Z, [1], 2)
    Vb, Wb = demux_p(Wa @ Vc, Zc @ Wa @ B @ Vc @ Zc, Pb)
    return Wc, Wb, Vb, Va

def last(U, p, branches, Pa, Pb):
    Wc, Wb, Vb, Va = leaves(U, p[:4], Pa, Pb)
    carry = np.eye(4, dtype=complex)
    for L, b in zip((Wc, Wb, Vb), branches):
        carry = zz(zz_roots_two_cnot_exact(L @ carry)[b])
    return zz(-p[4]) @ Va @ carry

def closest(U, Pa, Pb, rng, samples=150, polish=3):
    best = np.inf
    for branches in itertools.product((0, 1), repeat=3):
        pts = rng.uniform([-np.pi] * 4 + [0], [np.pi] * 4 + [np.pi], (samples, 5))
        vals = [one_cnot_distance(last(U, p, branches, Pa, Pb)) for p in pts]
        for i in np.argsort(vals)[:polish]:
            f = lambda p: one_cnot_distance(last(U, p, branches, Pa, Pb))
            r = minimize(f, pts[i], method="Nelder-Mead", options={"xatol": 1e-12, "fatol": 1e-14, "maxiter": 3000})
            best = min(best, r.fun)
    return best

if __name__ == "__main__":
    rng = np.random.default_rng(19)
    U = random_unitary(8, rng)   # U0 from reach.py (closest approach 6.8e-3 with default ordering)
    res = []
    for i, Pa in enumerate(PERMS):
        d = closest(U, Pa, np.eye(4), rng)
        res.append(d)
        print(f"Va ordering {i:2d}: {d:.2e}", flush=True)
    print("best over Va orderings:", f"{min(res):.2e}")
