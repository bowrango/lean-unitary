"""Jacobian rank of (top-qubit output diagonal, output ZZ phase) -> CNOT class of the last leaf."""
import numpy as np
from core import random_unitary
from invariants import gamma, zz, zz_roots_two_cnot_exact
from idea2 import node_leaves

def class_vec(X):
    G = gamma(X)
    t1, t2 = np.trace(G), np.trace(G @ G)
    s = t1 * t1  # invariant under the det^(1/4) sign ambiguity
    return np.array([s.real, s.imag, t2.real, t2.imag])

def nearest(roots, ref):
    d = lambda g: abs(((g - ref + np.pi / 2) % np.pi) - np.pi / 2)
    return min(roots, key=d)

def final(U, phi, g_out, refs):
    Wc, Wb, Vb, Va = node_leaves(U, phi)
    carry, used = np.eye(4, dtype=complex), []
    for L, ref in zip((Wc, Wb, Vb), refs):
        g = nearest(zz_roots_two_cnot_exact(L @ carry), ref)
        used.append(g); carry = zz(g)
    return zz(-g_out) @ Va @ carry, used

if __name__ == "__main__":
    rng = np.random.default_rng(8)
    for trial in range(8):
        U = random_unitary(8, rng)
        x = np.concatenate([rng.uniform(-np.pi, np.pi, 4), [rng.uniform(0, np.pi)]])
        br = [zz_roots_two_cnot_exact(np.eye(4))[0]] * 3
        X0, refs = final(U, x[:4], x[4], [rng.uniform(0, np.pi) for _ in range(3)])
        base = class_vec(X0)
        J = []
        for i in range(5):
            for h in (1e-5,):
                dx = np.zeros(5); dx[i] = h
                Xp, _ = final(U, (x + dx)[:4], (x + dx)[4], refs)
                Xm, _ = final(U, (x - dx)[:4], (x - dx)[4], refs)
                J.append((class_vec(Xp) - class_vec(Xm)) / (2 * h))
        s = np.linalg.svd(np.array(J).T, compute_uv=False)
        print(f"trial {trial}: singular values {np.array2string(s, precision=3)} -> rank {int(np.sum(s > 1e-6 * s[0]))}")
