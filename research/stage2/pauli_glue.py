"""Two-level (k = 2) node: a product of 16 unitaries on the lower register L (n-2 qubits)
interleaved with 15 glue gates, each a multiplexed Pauli rotation over L acting on the top two
qubits {s, t}:  G(θ) = Σ_j |j><j|_L ⊗ exp(-i θ_j P / 2),  P ∈ {X,Y,Z,I}^{⊗2} \\ {II}.

Such a glue with weight-1 P costs 2^(n-2) CNOTs (vs 2^(n-1) for block-ZXZ's top-level glue,
which is controlled by s as well). Parameter count 16·4^(n-2) + 15·2^(n-2) minus the
lower-diagonal gauge 15·2^(n-2) is exactly 4^n, so the question is whether some Pauli sequence
avoids hidden gauges. This script measures the Jacobian rank."""
import itertools, sys
import numpy as np
from scipy.linalg import expm

PAULI = {"I": np.eye(2), "X": np.array([[0, 1], [1, 0]]), "Y": np.array([[0, -1j], [1j, 0]]),
         "Z": np.diag([1., -1.])}

def top_op(p):  # p = "Pt Ps" string, e.g. "ZI" = Z on t, I on s; matrix on (t, s), t most significant
    return np.kron(PAULI[p[0]], PAULI[p[1]]).astype(complex)

def herm_basis(d):
    B = []
    for i in range(d):
        E = np.zeros((d, d), complex); E[i, i] = 1; B.append(E)
    for i in range(d):
        for j in range(i + 1, d):
            E = np.zeros((d, d), complex); E[i, j] = E[j, i] = 1; B.append(E)
            E = np.zeros((d, d), complex); E[i, j] = -1j; E[j, i] = 1j; B.append(E)
    return B

class Node:
    """Full register ordering: (t, s, L) with t most significant; matrices are (4·dL)×(4·dL)."""
    def __init__(self, nL, seq):
        self.nL, self.dL, self.seq = nL, 2**nL, seq
        self.HB = herm_basis(self.dL)
        self.nc, self.ng = len(seq) + 1, len(seq)
        self.np = self.nc * self.dL**2 + self.ng * self.dL

    def factors(self, p):
        dL, k = self.dL, 0
        F = []
        for i in range(self.nc):
            Hm = sum(c * B for c, B in zip(p[k:k + dL * dL], self.HB)); k += dL * dL
            F.append(np.kron(np.eye(4), expm(1j * Hm)))
            if i < self.ng:
                th = p[k:k + dL]; k += dL
                P = top_op(self.seq[i])
                w, V = np.linalg.eigh(P)
                # exp(-i θ_j P/2) for each L state j:  Σ_j (V e^{-iθ_j w/2} V†) ⊗ |j><j|
                G = np.zeros((4 * dL, 4 * dL), complex)
                for j in range(dL):
                    Rj = V @ np.diag(np.exp(-0.5j * th[j] * w)) @ V.conj().T
                    E = np.zeros((dL, dL)); E[j, j] = 1
                    G += np.kron(Rj, E)
                F.append(G)
        return F

    def matrix(self, p):
        M = np.eye(4 * self.dL, dtype=complex)
        for f in self.factors(p):
            M = f @ M
        return M

    def rank(self, rng, h=1e-7):
        p = rng.normal(size=self.np)
        M0 = self.matrix(p)
        cols = []
        for i in range(self.np):
            q = p.copy(); q[i] += h
            dM = M0.conj().T @ (self.matrix(q) - M0) / h  # left-trivialized, anti-Hermitian
            cols.append(np.concatenate([dM.real.ravel(), dM.imag.ravel()]))
        s = np.linalg.svd(np.array(cols).T, compute_uv=False)
        return int(np.sum(s > 1e-4 * s[0])), (4 * self.dL) ** 2

if __name__ == "__main__":
    rng = np.random.default_rng(0)
    nL = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    Zs, Xs, Zt, Xt = "IZ", "IX", "ZI", "XI"
    blk = [Zs, Xs, Zs]
    cands = {
        "zxz-like, top glue on t only": blk + [Zt] + blk + [Xt] + blk + [Zt] + blk,
        "top glue ZZ, XX, ZZ": blk + ["ZZ"] + blk + ["XX"] + blk + ["ZZ"] + blk,
        "top glue ZZ, XI, ZZ": blk + ["ZZ"] + blk + [Xt] + blk + ["ZZ"] + blk,
        "alternate s/t": [Zs, Zt, Xs, Xt] * 3 + [Zs, Zt, Xs],
        "all ZZ/XX/YY alternating": ["ZZ", "XX", "YY"] * 5,
        "Zs,Xt,ZZ cycle": [Zs, Xt, "ZZ"] * 5,
    }
    for name, seq in cands.items():
        r, full = Node(nL, seq).rank(rng)
        print(f"{name:32s} rank {r}/{full}", flush=True)
    for trial in range(8):
        seq = [rng.choice([Zs, Xs, Zt, Xt, "ZZ", "XX", "ZX", "XZ"]) for _ in range(15)]
        r, full = Node(nL, seq).rank(rng)
        print(f"random {' '.join(seq)}: rank {r}/{full}", flush=True)


def exact_rank(node, rng, return_sv=False):
    """Exact Jacobian rank at a random point: perturbing factor k on the right by e^{iεB}
    changes M^†dM by R_k^† (iB) R_k, R_k = F_{k-1}···F_1. Tangent generators: all Hermitian B
    on L (children); P ⊗ |j><j| (glue)."""
    p = rng.normal(size=node.np)
    F = node.factors(p)
    dL = node.dL
    gens_child = [np.kron(np.eye(4), B) for B in node.HB]
    cols, R = [], np.eye(4 * dL, dtype=complex)
    for k, f in enumerate(F):
        R = f @ R  # perturb on the left of f instead: M^†dM = R^† B R with R = F_k···F_1
        if k % 2 == 0:
            gens = gens_child
        else:
            P = top_op(node.seq[k // 2])
            gens = [np.kron(P, np.diag(np.eye(dL)[j])) for j in range(dL)]
        for B in gens:
            T = R.conj().T @ B @ R
            cols.append(np.concatenate([T.real.ravel(), T.imag.ravel()]))
    s = np.linalg.svd(np.array(cols).T, compute_uv=False)
    r = int(np.sum(s > 1e-9 * s[0]))
    return (r, s) if return_sv else r
