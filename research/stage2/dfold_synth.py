"""17-CNOT exact 3-qubit synthesis: block-ZXZ with double folds (numerical construction).

1. Choose top-qubit gates u_in, u_out so that U' = u_out·U·u_in satisfies both double-fold
   conditions (dfold.solve).
2. Block-ZXZ U' = (A1⊕A2) H (I⊕B) H (I⊕C); demultiplex A and C, ordering eigenvalues and choosing
   square-root branches so that the Z_1 Walsh component φ3 of each outer multiplexor is exactly 0.
3. Each outer multiplexor then ends in CX(0,2)·CX(1,2) with nothing between: both become CZs,
   I ⊕ Z0Z1, folded into the middle factor.  Outer multiplexors: 2 CNOTs each (block-ZXZ: 3).
Count: leaves 2+2+2+3, multiplexors 2+4+2 = 17."""
import itertools, sys
import numpy as np
from core import (H, Z, block_diag, block_zxz, circuit_matrix, cnot_count, demultiplex, embed,
                  mux_rot, random_unitary)
from dfold import solve, conditioned, su2
from zxz import leaf

def gray_phis(th):
    gray = [0, 1, 3, 2]
    sign = np.array([[(-1) ** bin(j & g).count("1") for g in gray] for j in range(4)])
    return np.linalg.solve(sign, th)

def demux_fold(U1, U2):
    """demultiplex U1⊕U2 = (V⊕V)·mux(θ)·(W⊕W), with eigen-order and branches chosen so φ3 = 0"""
    V, th, W = demultiplex(U1, U2)
    for perm in itertools.permutations(range(4)):
        p = list(perm)
        t = th[p]
        for shifts in itertools.product([0, 1], repeat=4):
            ts = t + 2 * np.pi * np.array(shifts)
            if abs(gray_phis(ts)[3]) < 1e-9:
                # reorder V columns / W rows; a 2π shift flips the sign of that eigen-block
                S = np.diag([(-1) ** s for s in shifts]).astype(complex)
                return V[:, p], ts, S @ W[p, :]
    raise RuntimeError("fold condition not satisfied")

def synth17(U, rng):
    e, p = solve(U, rng)
    assert e < 1e-10, e
    Up = conditioned(U, p)                     # Up = u_out · U · u_in
    A1, A2, B, C = block_zxz(Up)
    I = np.eye(4, dtype=complex)
    Va, ta, Wa = demux_fold(A1, A2)
    Vc, tc, Wc = demux_fold(I, C)
    Zf = np.kron(Z, Z)                         # CZ(0,2)·CZ(1,2) = I ⊕ Z0Z1
    Vb, tb, Wb = demultiplex(Wa @ Vc, Zf @ Wa @ B @ Vc @ Zf)
    dc = mux_rot(tc, 3)[:-3]                   # drop Rz(φ3)=1 and the closing CX(0,2), CX(1,2)
    da = mux_rot(ta, 3)[::-1][3:]
    hdh = [("u", 2, H)] + mux_rot(tb, 3) + [("u", 2, H)]
    circ, carry = [("u", 2, su2(p[:3]).conj().T)], np.eye(4, dtype=complex)
    for i, (S, seg) in enumerate(zip([Wc, Wb, Vb, Va], [dc, hdh, da, []])):
        last = i == 3
        sub, D = leaf(S @ carry, want_diag=not last, seed=i)
        circ += sub + seg
        carry = D
    circ.append(("u", 2, su2(p[3:]).conj().T))
    return circ, carry

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    for t in range(int(sys.argv[2]) if len(sys.argv) > 2 else 5):
        U = random_unitary(8, rng)
        circ, D = synth17(U, rng)
        M = block_diag(D, D) @ circuit_matrix(circ, 3)
        ph = np.vdot(M.ravel(), U.ravel()); ph /= abs(ph)
        print(f"target {t}: {cnot_count(circ)} CNOTs, max |U - e^(iφ)·circuit| = {np.max(np.abs(U - ph * M)):.1e}")
