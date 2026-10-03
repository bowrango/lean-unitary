"""Idea 2: a 3-qubit node synthesized up to an output diagonal, with a 1-CNOT final leaf.

The parent absorbs any 3-qubit diagonal Δ on the node's output. Block-ZXZ only uses its lower
part (the last leaf's diagonal). Here the top-qubit part, Δ = I ⊕ diag(e^{iφ}), is chosen so
that, after Wc, Wb, Vb each spend their Z⊗Z freedom on reaching 2 CNOTs, the last leaf

    X = e^{-i g ZZ} · Va · (carry from Vb)

needs only 1 CNOT. Unknowns: φ (4, one redundant) and g; conditions: 3.
"""

from __future__ import annotations

import itertools

import numpy as np
from scipy.optimize import least_squares

from core import Z, block_diag, block_zxz, demultiplex, embed
from invariants import one_cnot_residual, zz, zz_roots_two_cnot_exact as zz_roots_two_cnot


def node_leaves(U: np.ndarray, phi: np.ndarray):
    """The four leaves (time order Wc, Wb, Vb, Va) of the optimized block-ZXZ node for
    Δ⁻¹ U, Δ = I ⊕ diag(e^{iφ})."""
    m = 4
    D2 = np.diag(np.exp(1j * phi))
    Up = block_diag(np.eye(m), D2.conj()) @ U
    A1, A2, B, C = block_zxz(Up)
    I = np.eye(m, dtype=complex)
    Va, _, Wa = demultiplex(A1, A2)
    Vc, _, Wc = demultiplex(I, C)
    Zc = embed(Z, [1], 2)
    Vb, _, Wb = demultiplex(Wa @ Vc, Zc @ Wa @ B @ Vc @ Zc)
    return Wc, Wb, Vb, Va


def final_leaf(U, phi, g_out, branches, carry_in=None):
    carry = np.eye(4, dtype=complex) if carry_in is None else carry_in
    Wc, Wb, Vb, Va = node_leaves(U, phi)
    for L, b in zip((Wc, Wb, Vb), branches):
        roots = zz_roots_two_cnot(L @ carry)
        if len(roots) <= b:
            return None
        carry = zz(roots[b])
    return zz(-g_out) @ Va @ carry


def search(U, rng, restarts=30):
    best = (np.inf, None)
    for branches in itertools.product((0, 1), repeat=3):
        for _ in range(restarts):
            x0 = np.concatenate([[0.0], rng.uniform(-np.pi, np.pi, 3), rng.uniform(0, np.pi, 1)])

            def resid(x):
                X = final_leaf(U, np.concatenate([[0.0], x[:3]]), x[3], branches)
                return np.full(34, 10.0) if X is None else one_cnot_residual(X)

            sol = least_squares(resid, x0[1:], xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=400)
            err = float(np.max(np.abs(resid(sol.x))))
            if err < best[0]:
                best = (err, (branches, sol.x))
            if err < 1e-10:
                return best
    return best


if __name__ == "__main__":
    from core import random_unitary

    rng = np.random.default_rng(31)
    for i in range(6):
        U = random_unitary(8, rng)
        err, info = search(U, rng)
        print(f"U{i}: best 1-CNOT residual {err:.1e}  branches {info[0] if info else None}")
