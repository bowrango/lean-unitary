"""How close can the free parameters bring the last leaf to the 1-CNOT class?
Distance measured on γ's eigenphases, which are ±2(c1 ± c2 ± c3)-type combinations of the
Weyl-chamber coordinates; the 1-CNOT class has eigenphases {π/2, π/2, -π/2, -π/2}."""
import itertools
import numpy as np
from scipy.optimize import minimize
from core import random_unitary
from invariants import gamma, zz, zz_roots_two_cnot_exact
from idea2 import node_leaves

def one_cnot_distance(X):
    ph = np.sort(np.angle(np.linalg.eigvals(gamma(X))))
    target = np.array([-np.pi / 2, -np.pi / 2, np.pi / 2, np.pi / 2])
    d = np.abs(((ph - target) + np.pi) % (2 * np.pi) - np.pi)
    return float(np.max(d))

def last_leaf(U, phi, g_out, branches):
    Wc, Wb, Vb, Va = node_leaves(U, phi)
    carry = np.eye(4, dtype=complex)
    for L, b in zip((Wc, Wb, Vb), branches):
        carry = zz(zz_roots_two_cnot_exact(L @ carry)[b])
    return zz(-g_out) @ Va @ carry

def min_distance(U, rng, samples=400, polish=8):
    best = (np.inf, None)
    for branches in itertools.product((0, 1), repeat=3):
        pts = rng.uniform([-np.pi] * 4 + [0], [np.pi] * 4 + [np.pi], (samples, 5))
        vals = [one_cnot_distance(last_leaf(U, p[:4], p[4], branches)) for p in pts]
        for i in np.argsort(vals)[:polish]:
            f = lambda p: one_cnot_distance(last_leaf(U, p[:4], p[4], branches))
            r = minimize(f, pts[i], method="Nelder-Mead",
                         options={"xatol": 1e-12, "fatol": 1e-14, "maxiter": 4000})
            if r.fun < best[0]:
                best = (r.fun, branches)
    return best

if __name__ == "__main__":
    rng = np.random.default_rng(19)
    for trial in range(6):
        d, br = min_distance(random_unitary(8, rng), rng)
        print(f"U{trial}: closest approach to 1-CNOT class {d:.2e} (branches {br})", flush=True)
