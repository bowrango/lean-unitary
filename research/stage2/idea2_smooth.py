"""Idea 2, smooth formulation: eigendecompositions become unknowns constrained by equations, so
the search never jumps between eigenvector orderings.

Unknowns: Λ (top-qubit output diagonal), Va, Ea (A-demultiplexing: A1 A2'† = Va Ea Va†),
Vb, Eb (B̃-demultiplexing), g_out (Z⊗Z part of the lower output diagonal).
Residuals: the two demultiplexing equations, and the 1-CNOT invariants of the last leaf after
Wc, Wb, Vb each spend their Z⊗Z freedom on reaching 2 CNOTs.
"""

from __future__ import annotations

import itertools

import numpy as np
from scipy.linalg import expm
from scipy.optimize import least_squares

from core import Z, block_zxz, demultiplex, embed, random_unitary
from invariants import one_cnot_residual, zz, zz_roots_two_cnot_exact

HERM_BASIS = []
for i in range(4):
    for j in range(4):
        E = np.zeros((4, 4), dtype=complex)
        if i == j:
            E[i, i] = 1
        elif i < j:
            E[i, j] = E[j, i] = 1
        else:
            E[i, j], E[j, i] = 1j, -1j
        HERM_BASIS.append(E)
HERM_BASIS = np.array(HERM_BASIS)


def unitary(x, base):
    return base @ expm(1j * np.tensordot(x, HERM_BASIS, 1))


class Node:
    def __init__(self, U):
        self.A1, self.A2, self.B, C = block_zxz(U)
        I = np.eye(4, dtype=complex)
        self.Vc, _, self.Wc = demultiplex(I, C)
        self.Zc = embed(Z, [1], 2)

    def pieces(self, x, bases):
        lam, va, ea, vb, eb, g_out = x[:4], x[4:20], x[20:24], x[24:40], x[40:44], x[44]
        A2p = np.diag(np.exp(-1j * lam)) @ self.A2
        Va = unitary(va, bases[0]); Da = np.diag(np.exp(0.5j * ea))
        Wa = Da @ Va.conj().T @ A2p
        B1 = Wa @ self.Vc
        B2 = self.Zc @ Wa @ self.B @ self.Vc @ self.Zc
        Vb = unitary(vb, bases[1]); Db = np.diag(np.exp(0.5j * eb))
        Wb = Db @ Vb.conj().T @ B2
        r_a = self.A1 @ A2p.conj().T - Va @ np.diag(np.exp(1j * ea)) @ Va.conj().T
        r_b = B1 @ B2.conj().T - Vb @ np.diag(np.exp(1j * eb)) @ Vb.conj().T
        return Va, Wb, Vb, g_out, r_a, r_b

    def residual(self, x, bases, branches):
        Va, Wb, Vb, g_out, r_a, r_b = self.pieces(x, bases)
        carry = np.eye(4, dtype=complex)
        for L, b in zip((self.Wc, Wb, Vb), branches):
            carry = zz(zz_roots_two_cnot_exact(L @ carry)[b])
        X = zz(-g_out) @ Va @ carry
        return np.concatenate([r_a.real.ravel(), r_a.imag.ravel(), r_b.real.ravel(),
                               r_b.imag.ravel(), one_cnot_residual(X)])


def initial(node, lam, rng):
    A2p = np.diag(np.exp(-1j * lam)) @ node.A2
    Va, _, Wa = demultiplex(node.A1, A2p)
    ea = np.angle(np.linalg.eigvals(Va.conj().T @ node.A1 @ A2p.conj().T @ Va).real * 0 +
                  np.diag(Va.conj().T @ node.A1 @ A2p.conj().T @ Va))
    B1 = Wa @ node.Vc
    B2 = node.Zc @ Wa @ node.B @ node.Vc @ node.Zc
    Vb, _, _ = demultiplex(B1, B2)
    eb = np.angle(np.diag(Vb.conj().T @ B1 @ B2.conj().T @ Vb))
    x = np.concatenate([lam, np.zeros(16), ea, np.zeros(16), eb, rng.uniform(0, np.pi, 1)])
    return x, (Va, Vb)


def search(U, rng, restarts=12):
    node = Node(U)
    best = (np.inf, None)
    for branches in itertools.product((0, 1), repeat=3):
        for _ in range(restarts):
            x0, bases = initial(node, rng.uniform(-np.pi, np.pi, 4), rng)
            f = lambda x: node.residual(x, bases, branches)
            sol = least_squares(f, x0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
            err = float(np.max(np.abs(f(sol.x))))
            if err < best[0]:
                best = (err, (branches, sol.x, bases))
            if err < 1e-10:
                return best
    return best


if __name__ == "__main__":
    rng = np.random.default_rng(41)
    for i in range(5):
        err, info = search(random_unitary(8, rng), rng)
        print(f"U{i}: best residual {err:.1e}  branches {info[0]}", flush=True)
