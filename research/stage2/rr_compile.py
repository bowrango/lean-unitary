"""Compile a fitted round-robin node (k = n - 2, children on the bottom two qubits) into an explicit
CNOT circuit in core.py conventions and check it against the target.
  glue: multiplexed Rz (or H·Rz·H) on a top qubit, Gray code, 2 controls -> 4 CNOTs
  child: 2-qubit gate, 2 CNOTs up to a diagonal on the bottom pair (the diagonal commutes with the
         next glue and is absorbed into the next child); the last child exact, 3 CNOTs."""
import sys, numpy as np
from core import random_unitary, circuit_matrix, cnot_count, H, rz, embed
from fit import fit, layered
from pg_fitk import NodeK
from pg_k_cx import round_robin

def mux_rz(thetas, controls, target):
    k = len(controls)
    gray = [i ^ (i >> 1) for i in range(2**k)]
    sign = np.array([[(-1) ** bin(j & g).count("1") for g in gray] for j in range(2**k)])
    phis = np.linalg.solve(sign, thetas)
    circ = []
    for i in range(2**k):
        circ.append(("u", target, rz(phis[i])))
        flip = gray[i] ^ gray[(i + 1) % 2**k]
        circ.append(("cx", controls[flip.bit_length() - 1], target))
    return circ

n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
k, nL = n - 2, 2
rng = np.random.default_rng(5)
node = NodeK(k, nL, round_robin(k, 4**k - 1, {}))
U = random_unitary(2**n, rng)
print("fit residual", node.fit(U, rng))
C, TH = node.sol
# NodeK: top qubit q (0 = most significant) is bit n-1-q; L = bits 1, 0 (L index bit i <-> qubit i)
glues = [P for kind, P in node.items if kind == "g"]
toks = round_robin(k, 4**k - 1, {})
circ, carry = [], np.eye(4)
for i in range(len(C)):
    child = C[i] @ carry            # carry: diagonal left over from the previous child (acts first)
    last = i == len(C) - 1
    sub, D, err = fit(child, layered(3 if last else 2), 2, up_to_diag=not last, restarts=60, seed=i)
    assert err < 1e-9, (i, err)
    circ += sub                      # child = D · sub  (D on the bottom pair, applied after sub)
    carry = D if not last else np.eye(4)
    if last:
        circ.append(("block", (0, 1), D, 0))  # D is a global phase here
    if i < len(glues):
        q, P = toks[i].split(":"); t = n - 1 - int(q)
        g = mux_rz(TH[i], [0, 1], t)
        circ += ([("u", t, H)] + g + [("u", t, H)]) if P == "X" else g
# the leftover diagonals were moved past glues (they commute), so the circuit is exact:
M = circuit_matrix(circ, n)
ph = np.vdot(M.ravel(), U.ravel()); ph /= abs(ph)
print(f"n={n}: CNOTs = {cnot_count(circ)} (formula 6·4^(n-2)-3 = {6*4**(n-2)-3}), max |U - e^(iφ)·circuit| = {np.max(np.abs(U - ph*M)):.1e}")
