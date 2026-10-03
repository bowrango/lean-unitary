"""k-level node: 4^k unitaries on the lower register L interleaved with 4^k - 1 glues, each a
multiplexed (over L) rotation exp(-iθ_j P/2) by a k-qubit Pauli P on the top register.
Exact Jacobian rank at a random point (see pauli_glue.exact_rank)."""
import sys, functools, numpy as np
from core import random_unitary
from pauli_glue import PAULI, herm_basis

def pmat(p):
    return functools.reduce(np.kron, [PAULI[c] for c in p]).astype(complex)

def glue(P, th, dL):
    w, V = np.linalg.eigh(P)
    G = 0
    for j in range(dL):
        E = np.zeros((dL, dL)); E[j, j] = 1
        G = G + np.kron(V @ np.diag(np.exp(-0.5j * th[j] * w)) @ V.conj().T, E)
    return G

def exact_rank(k, nL, seq, rng):
    dL, dT = 2**nL, 2**k
    HB = herm_basis(dL)
    R = np.eye(dT * dL, dtype=complex); cols = []
    for i in range(len(seq) + 1):
        R = np.kron(np.eye(dT), random_unitary(dL, rng)) @ R
        for B in HB:
            T = R.conj().T @ np.kron(np.eye(dT), B) @ R
            cols.append(np.concatenate([T.real.ravel(), T.imag.ravel()]))
        if i < len(seq):
            P = pmat(seq[i])
            R = glue(P, rng.uniform(-np.pi, np.pi, dL), dL) @ R
            for j in range(dL):
                T = R.conj().T @ np.kron(P, np.diag(np.eye(dL)[j])) @ R
                cols.append(np.concatenate([T.real.ravel(), T.imag.ravel()]))
    s = np.linalg.svd(np.array(cols).T, compute_uv=False)
    return int(np.sum(s > 1e-9 * s[0])), (dT * dL) ** 2

if __name__ == "__main__":
    k, nL, trials, maxw = map(int, sys.argv[1:5])
    rng = np.random.default_rng(int(sys.argv[5]) if len(sys.argv) > 5 else 0)
    import itertools
    alph = ["".join(p) for p in itertools.product("IXYZ", repeat=k)
            if 0 < sum(c != "I" for c in p) <= maxw]
    hist = {}
    for _ in range(trials):
        seq = [str(rng.choice(alph))]
        while len(seq) < 4**k - 1:
            c = str(rng.choice(alph))
            if c != seq[-1]: seq.append(c)
        r, full = exact_rank(k, nL, seq, rng)
        hist[r] = hist.get(r, 0) + 1
        if r == full: print("FULL", " ".join(seq), flush=True)
    print(f"k={k} nL={nL} maxw={maxw}:", dict(sorted(hist.items())), "full =", full)
