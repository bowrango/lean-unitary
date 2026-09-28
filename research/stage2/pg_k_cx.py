"""General k: weight-1 multiplexed glues on top qubits + fixed CNOTs 'c:a>b' between top qubits.
Glue token 'q:P' = Pauli P on top qubit q (0 = most significant). Exact Jacobian rank."""
import sys, numpy as np, functools
from core import random_unitary
from pauli_glue import herm_basis, PAULI
from pauli_glue_k import glue

def top_pauli(k, q, P):
    return functools.reduce(np.kron, [PAULI[P] if i == q else np.eye(2) for i in range(k)]).astype(complex)

def top_cx(k, a, b):
    d = 2**k; M = np.zeros((d, d), complex)
    for i in range(d):
        bits = [(i >> (k - 1 - q)) & 1 for q in range(k)]
        if bits[a]: bits[b] ^= 1
        M[sum(v << (k - 1 - q) for q, v in enumerate(bits)), i] = 1
    return M

def exact_rank(k, nL, toks, rng):
    dL, dT = 2**nL, 2**k
    HB = herm_basis(dL)
    R = np.eye(dT * dL, dtype=complex); cols = []
    def child():
        nonlocal R
        R = np.kron(np.eye(dT), random_unitary(dL, rng)) @ R
        for B in HB:
            T = R.conj().T @ np.kron(np.eye(dT), B) @ R
            cols.append(np.concatenate([T.real.ravel(), T.imag.ravel()]))
    child()
    for t in toks:
        if t.startswith("c:"):
            a, b = map(int, t[2:].split(">"))
            R = np.kron(top_cx(k, a, b), np.eye(dL)) @ R
            continue
        q, P = t.split(":"); P = top_pauli(k, int(q), P)
        R = glue(P, rng.uniform(-np.pi, np.pi, dL), dL) @ R
        for j in range(dL):
            T = R.conj().T @ np.kron(P, np.diag(np.eye(dL)[j])) @ R
            cols.append(np.concatenate([T.real.ravel(), T.imag.ravel()]))
        child()
    s = np.linalg.svd(np.array(cols).T, compute_uv=False)
    return int(np.sum(s > 1e-9 * s[0])), (dT * dL) ** 2

def round_robin(k, n_glue, cx_at):
    """cycle qubits 0..k-1; each qubit alternates Z, X; cx_at: {glue index: 'c:a>b'}"""
    toks, cnt = [], [0] * k
    for i in range(n_glue):
        if i in cx_at:
            toks += cx_at[i] if isinstance(cx_at[i], list) else [cx_at[i]]
        q = i % k
        toks.append(f"{q}:{'ZX'[cnt[q] % 2]}"); cnt[q] += 1
    return toks

if __name__ == "__main__":
    rng = np.random.default_rng(0)
    # sanity: k=2 reproduces the 1-CNOT sequence
    print("k=2 rr, cx@7:", exact_rank(2, 2, round_robin(2, 15, {7: "c:1>0"}), rng))
    for k in (3,):
        n = 4**k - 1
        tests = {
            "no cx": {},
            "1 cx mid": {n // 2: "c:2>1"},
            "2 cx": {n // 3: "c:2>1", 2 * n // 3: "c:1>0"},
            "3 cx": {n // 4: "c:2>1", n // 2: "c:1>0", 3 * n // 4: "c:2>1"},
            "4 cx": {n // 5: "c:2>1", 2 * n // 5: "c:1>0", 3 * n // 5: "c:2>1", 4 * n // 5: "c:1>0"},
            "6 cx": {n * i // 7: ["c:2>1", "c:1>0"][i % 2] for i in range(1, 7)},
        }
        for name, cx in tests.items():
            toks = round_robin(k, n, cx)
            print(f"k={k} {name:10s}", exact_rank(k, 1, toks, rng), exact_rank(k, 2, toks, rng), flush=True)
