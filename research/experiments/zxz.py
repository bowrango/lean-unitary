"""Recursive block-ZXZ synthesis (Krol & Al-Ars, arXiv:2403.13692) with both optimizations.

Per level, with m = 2^(n-1) and H on the top qubit:

    U = (A1 ⊕ A2) · H · (I ⊕ B) · H · (I ⊕ C)                                (block-ZXZ)
      = (Va⊕Va) Da (Wa⊕Wa) · H (I⊕B) H · (Vc⊕Vc) Dc (Wc⊕Wc)                (demultiplex A, C)
      = (Va⊕Va) Da'' · H · CZ (WaVc ⊕ Wa B Vc) CZ · H · Dc'' (Wc⊕Wc)
        (the CNOT of Dc / Da next to each H becomes a CZ = I ⊕ Z, folded into the middle)
      = (Va⊕Va) Da'' (Vb⊕Vb) · H Db H · (Wb⊕Wb) Dc'' (Wc⊕Wc)             (demultiplex B̃)

Time order: Wc, Dc'' (m-1 CNOTs), Wb, H·Db·H (m), Vb, Da'' (m-1), Va.
Every diagonal on the lower qubits commutes with Dc'', H·Db·H and Da'', so all sub-unitaries
but the last are synthesized up to a diagonal that migrates into the next one.

    c(n) = 4 c(n-1) + 3·2^(n-1) - 2   (plus 1 saved per non-final 2-qubit leaf)
"""

from __future__ import annotations

import numpy as np

from core import (H, Z, block_diag, block_zxz, circuit_matrix, cnot_count, demultiplex, embed,
                  mux_rot)
from fit import fit, layered


def leaf(U: np.ndarray, want_diag: bool, seed: int = 0):
    circ, D, err = fit(U, layered(2 if want_diag else 3), 2, up_to_diag=want_diag, seed=seed)
    assert err < 1e-9, f"leaf fit failed ({err:.1e})"
    return circ, D


def synth(U: np.ndarray, n: int, want_diag: bool = False):
    """Returns (circuit, D) with U == D · circuit_matrix(circuit), D diagonal (identity unless
    want_diag)."""
    if n == 1:
        return [("u", 0, U)], np.eye(2, dtype=complex)
    if n == 2:
        return leaf(U, want_diag)

    m, top, c = 2 ** (n - 1), n - 1, n - 2
    A1, A2, B, C = block_zxz(U)
    I = np.eye(m, dtype=complex)
    Va, ta, Wa = demultiplex(A1, A2)
    Vc, tc, Wc = demultiplex(I, C)
    Zc = embed(Z, [c], n - 1)
    Vb, tb, Wb = demultiplex(Wa @ Vc, Zc @ Wa @ B @ Vc @ Zc)

    dc = mux_rot(tc, n)[:-1]           # drop the closing CNOT(c -> top): it became a CZ
    da = mux_rot(ta, n)[::-1][1:]      # reversed Gray circuit; drop its opening CNOT
    hdh = [("u", top, H)] + mux_rot(tb, n) + [("u", top, H)]

    circ: list[tuple] = []
    carry = np.eye(m, dtype=complex)   # diagonal migrating forward on the lower qubits
    subs = [Wc, Wb, Vb, Va]
    between = [dc, hdh, da, []]
    for i, (S, seg) in enumerate(zip(subs, between)):
        last = i == len(subs) - 1
        sub_circ, D = synth(S @ carry, n - 1, want_diag=(not last) or want_diag)
        circ += sub_circ + seg
        carry = D
    return circ, block_diag(carry, carry)


def expected(n: int) -> int:
    return (22 * 4**n - 72 * 2**n + 80) // 48


if __name__ == "__main__":
    from core import random_unitary

    rng = np.random.default_rng(7)
    for n in (2, 3, 4):
        U = random_unitary(2**n, rng)
        circ, D = synth(U, n)
        err = float(np.max(np.abs(D @ circuit_matrix(circ, n) - U)))
        print(f"n={n}: {cnot_count(circ)} CNOTs (paper: {expected(n)}), error {err:.1e}")
