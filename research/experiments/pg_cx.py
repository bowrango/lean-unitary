"""k=2 node with weight-1 glues only, plus m fixed CNOTs between the two top qubits inserted at
chosen glue slots (they commute with the L-children, so each costs exactly 1 CNOT).
seq tokens: IZ IX ZI XI (glue), 'C' = CNOT s->t, 'D' = CNOT t->s (no parameters)."""
import sys, numpy as np, itertools
from core import random_unitary
from pauli_glue import herm_basis
from pauli_glue_k import pmat, glue

CXst = np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]], complex)  # basis |t s>, control s (low bit)... 
# order (t, s): index = 2t + s. CNOT control s, target t: |t s> -> |t^s, s>
CXst = np.zeros((4, 4), complex)
for t in range(2):
    for s in range(2):
        CXst[2 * (t ^ s) + s, 2 * t + s] = 1
CXts = np.zeros((4, 4), complex)
for t in range(2):
    for s in range(2):
        CXts[2 * t + (s ^ t), 2 * t + s] = 1

def exact_rank(nL, seq, rng, k=2):
    dL, dT = 2**nL, 2**k
    HB = herm_basis(dL)
    R = np.eye(dT * dL, dtype=complex); cols = []
    def add_child():
        nonlocal R
        R = np.kron(np.eye(dT), random_unitary(dL, rng)) @ R
        for B in HB:
            T = R.conj().T @ np.kron(np.eye(dT), B) @ R
            cols.append(np.concatenate([T.real.ravel(), T.imag.ravel()]))
    add_child()
    for tok in seq:
        if tok in ("C", "D"):
            R = np.kron(CXst if tok == "C" else CXts, np.eye(dL)) @ R
            continue
        P = pmat(tok)
        R = glue(P, rng.uniform(-np.pi, np.pi, dL), dL) @ R
        for j in range(dL):
            T = R.conj().T @ np.kron(P, np.diag(np.eye(dL)[j])) @ R
            cols.append(np.concatenate([T.real.ravel(), T.imag.ravel()]))
        add_child()
    s = np.linalg.svd(np.array(cols).T, compute_uv=False)
    return int(np.sum(s > 1e-9 * s[0])), (dT * dL) ** 2

if __name__ == "__main__":
    nL, trials, m = map(int, sys.argv[1:4])
    rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    w1 = ["IZ", "IX", "ZI", "XI"]
    hist, full_seqs = {}, []
    for _ in range(trials):
        seq = [str(rng.choice(w1))]
        while len(seq) < 15:
            c = str(rng.choice(w1))
            if c != seq[-1]: seq.append(c)
        for pos in sorted(rng.choice(range(1, 15), m, replace=False), reverse=True):
            seq.insert(int(pos), str(rng.choice(["C", "D"])))
        r, full = exact_rank(nL, seq, rng)
        hist[r] = hist.get(r, 0) + 1
        if r == full: full_seqs.append(" ".join(seq))
    print(f"nL={nL} m={m}:", dict(sorted(hist.items())), "full =", full)
    for s in full_seqs[:3]: print("  FULL", s)
