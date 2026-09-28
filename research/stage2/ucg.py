"""Uniformly controlled gates (UCGs): target qubit t, controls = the other qubits; when the controls
are in state j, apply an arbitrary u_j ∈ U(2) to t. Cost test: fit a CNOT template to a random UCG
up to diagonals on the *controls* (on both sides), which neighbouring children absorb for free."""
import numpy as np
from scipy.optimize import least_squares
from core import circuit_matrix, embed, random_unitary
from fit import realize, n_slots

def ucg_matrix(us, n):
    """Target = top qubit n-1; controls = qubits 0..n-2 (state j = lower index)."""
    d = 2 ** (n - 1)
    M = np.zeros((2 * d, 2 * d), dtype=complex)
    for j, u in enumerate(us):
        for a in range(2):
            for b in range(2):
                M[a * d + j, b * d + j] = u[a, b]
    return M

def fit_ucg(target, template, n, restarts=10, seed=0):
    rng = np.random.default_rng(seed)
    d = 2 ** (n - 1)
    k = 3 * n_slots(template)
    def ctrl_diag(ph):  # diagonal on controls, identity on the target (top) qubit
        return np.concatenate([np.exp(1j * ph), np.exp(1j * ph)])
    def resid(p):
        L, R = ctrl_diag(p[k:k + d]), ctrl_diag(p[k + d:])
        M = L[:, None] * circuit_matrix(realize(template, p[:k]), n) * R[None, :]
        r = (M - target).ravel()
        return np.concatenate([r.real, r.imag])
    best = np.inf
    for _ in range(restarts):
        sol = least_squares(resid, rng.uniform(-np.pi, np.pi, k + 2 * d), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        best = min(best, float(np.max(np.abs(resid(sol.x)))))
        if best < 1e-10:
            break
    return best

def to_top(cnots, n):
    t = [("u", q) for q in range(n)]
    for c, tg in cnots:
        t += [("cx", c, tg), ("u", c), ("u", tg)]
    return t

if __name__ == "__main__":
    rng = np.random.default_rng(5)
    n = 3
    for kc in (2, 3, 4):
        # CNOTs from the controls onto the target, cycling controls (Gray-code-like)
        cn = [((i % 2), 2) for i in range(kc)]
        errs = [fit_ucg(ucg_matrix([random_unitary(2, rng) for _ in range(4)], n), to_top(cn, n), n, seed=s) for s in range(3)]
        print(f"UCG with 2 controls, {kc} CNOTs: residuals " + " ".join(f"{e:.1e}" for e in errs), flush=True)
