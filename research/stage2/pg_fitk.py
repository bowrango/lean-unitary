"""Global fit of a k-level multiplexed-Pauli node (children on L, weight-1 glues 'q:P' on the top
k qubits multiplexed over L, optional fixed CNOTs 'c:a>b') to Haar-random targets.
Manifold Levenberg-Marquardt with a vectorized left-trivialized Jacobian."""
import sys, numpy as np
from scipy.linalg import expm, logm
from core import random_unitary
from pg_k_cx import top_pauli, top_cx, round_robin
from pauli_glue_k import pmat

class NodeK:
    def __init__(self, k, nL, toks):
        self.k, self.dL, self.dT = k, 2**nL, 2**k
        self.N = self.dT * self.dL
        self.items = []  # ("g", P) or ("x", M)
        for t in toks:
            if t.startswith("c:"):
                a, b = map(int, t[2:].split(">")); self.items.append(("x", top_cx(k, a, b)))
            elif ":" in t:
                q, P = t.split(":"); self.items.append(("g", top_pauli(k, int(q), P)))
            else:  # a full Pauli string on the top k qubits, e.g. "XX" (qubit 0 first)
                self.items.append(("g", pmat(t)))
        self.ng = sum(1 for it in self.items if it[0] == "g")
        # glue: exp(-iθ_j P/2) on top ⊗ |j><j|; P is ± permutation-like, P^2 = I
        self.eig = {}

    def gmat(self, P, th):
        c, s = np.cos(th / 2), np.sin(th / 2)
        # Σ_j (c_j I - i s_j P) ⊗ E_jj
        return np.kron(np.eye(self.dT), np.diag(c)) - 1j * np.kron(P, np.diag(s))

    def seq(self, C, TH):
        out, gi = [("c", 0, C[0])], 0
        for kind, P in self.items:
            if kind == "x":
                out.append(("x", None, np.kron(P, np.eye(self.dL))))
            else:
                out.append(("g", gi, self.gmat(P, TH[gi]))); gi += 1
                out.append(("c", gi, C[gi]))
        return out

    def product(self, C, TH):
        M = np.eye(self.N, dtype=complex)
        for kind, i, f in self.seq(C, TH):
            M = (np.kron(np.eye(self.dT), f) if kind == "c" else f) @ M
        return M

    def herr(self, C, TH, U):
        X = -1j * logm(self.product(C, TH).conj().T @ U); X = (X + X.conj().T) / 2
        return X - np.trace(X).real / self.N * np.eye(self.N)

    def jac(self, C, TH):
        dT, dL, N = self.dT, self.dL, self.N
        M = np.eye(N, dtype=complex); blocks = []
        gi = 0
        for kind, i, f in self.seq(C, TH):
            M = (np.kron(np.eye(dT), f) if kind == "c" else f) @ M
            Mr = M.reshape(dT, dL, N)
            if kind == "c":
                K = np.einsum("ali,amj->lmij", Mr.conj(), Mr)  # M^† (I⊗E_lm) M
                # Hermitian basis: E_ll ; E_lm+E_ml ; -i E_lm + i E_ml
                cols = [K[l, l] for l in range(dL)]
                for l in range(dL):
                    for m in range(l + 1, dL):
                        cols.append(K[l, m] + K[m, l]); cols.append(-1j * K[l, m] + 1j * K[m, l])
                blocks.append(np.array(cols))
            elif kind == "g":
                P = self.items_g[i]
                T = np.einsum("aji,ab,bjk->jik", Mr.conj(), P, Mr)
                blocks.append(T)
        B = np.concatenate(blocks)            # (p, N, N)
        return np.concatenate([B.real.reshape(len(B), -1), B.imag.reshape(len(B), -1)], axis=1).T

    def update(self, C, TH, d):
        dL, idx = self.dL, 0
        C2, TH2 = [], []
        for kind, i, f in self.seq(C, TH):
            if kind == "c":
                v = d[idx:idx + dL * dL]; idx += dL * dL
                Hm = np.diag(v[:dL]).astype(complex); t = dL
                for l in range(dL):
                    for m in range(l + 1, dL):
                        a, b = v[t], v[t + 1]; t += 2
                        Hm[l, m] += a - 1j * b; Hm[m, l] += a + 1j * b
                C2.append(expm(1j * Hm) @ C[i])
            elif kind == "g":
                TH2.append(TH[i] - 2 * d[idx:idx + dL]); idx += dL
        return C2, TH2

    def fit(self, U, rng, iters=3000, restarts=3, tol=1e-10):
        self.items_g = [P for kind, P in self.items if kind == "g"]
        best = np.inf
        for _ in range(restarts):
            C = [random_unitary(self.dL, rng) for _ in range(self.ng + 1)]
            TH = [rng.uniform(-np.pi, np.pi, self.dL) for _ in range(self.ng)]
            lam = 1e-3; X = self.herr(C, TH, U); err = np.linalg.norm(X)
            for it in range(iters):
                if err < tol: break
                J = self.jac(C, TH); x = np.concatenate([X.real.ravel(), X.imag.ravel()])
                JtJ = J.T @ J; g = J.T @ x; D = np.diag(JtJ).copy() + 1e-9
                ok = False
                while lam < 1e8:
                    d = np.linalg.solve(JtJ + lam * np.diag(D), g)
                    C2, TH2 = self.update(C, TH, d)
                    X2 = self.herr(C2, TH2, U); e2 = np.linalg.norm(X2)
                    if e2 < err:
                        C, TH, X, err = C2, TH2, X2, e2; lam = max(lam / 3, 1e-12); ok = True; break
                    lam *= 4
                if not ok: break
            if err < best:
                best, self.sol = err, (C, TH)
            if best < tol: break
        return best

if __name__ == "__main__":
    k, nL, ntarg = map(int, sys.argv[1:4])
    toks = round_robin(k, 4**k - 1, {}) if len(sys.argv) < 5 or sys.argv[4] == "rr" else sys.argv[4].split()
    rng = np.random.default_rng(int(sys.argv[5]) if len(sys.argv) > 5 else 21)
    node = NodeK(k, nL, toks); sol = 0
    for t in range(ntarg):
        e = node.fit(random_unitary(node.N, rng), rng); sol += e < 1e-8
        print(f"k={k} n={k+nL} target {t}: residual {e:.2e}", flush=True)
    print(f"k={k} n={k+nL}: solved {sol}/{ntarg}")
