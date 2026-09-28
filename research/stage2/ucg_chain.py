"""Is a chain of N uniformly controlled gates (targets cycling) universal up to a final diagonal?
Each UCG costs 2^(n-1) - 1 CNOTs up to a diagonal, which the next UCG absorbs."""
import numpy as np
from scipy.optimize import least_squares
from core import random_unitary
from fit import euler

def ucg_on(us, t, n):
    """UCG with target t, controls = all other qubits; us indexed by the controls' joint state."""
    d = 2 ** n
    M = np.zeros((d, d), dtype=complex)
    others = [q for q in range(n) if q != t]
    for i in range(d):
        j = sum(((i >> q) & 1) << b for b, q in enumerate(others))
        a = (i >> t) & 1
        i0 = i & ~(1 << t)
        for b in range(2):
            M[i, i0 | (b << t)] = us[j][a, b]
    return M

def chain(p, targets, n):
    d, k = 2 ** n, 2 ** (n - 1)
    M = np.eye(d, dtype=complex)
    idx = 0
    for t in targets:
        us = [euler(*p[idx + 3 * j: idx + 3 * j + 3]) for j in range(k)]
        idx += 3 * k
        M = ucg_on(us, t, n) @ M
    return np.exp(1j * p[idx: idx + d])[:, None] * M   # final diagonal

def fit_chain(U, targets, n, restarts=15, seed=0):
    rng = np.random.default_rng(seed)
    npar = 3 * 2 ** (n - 1) * len(targets) + 2 ** n
    f = lambda p: np.concatenate([(chain(p, targets, n) - U).real.ravel(), (chain(p, targets, n) - U).imag.ravel()])
    best = np.inf
    for _ in range(restarts):
        sol = least_squares(f, rng.uniform(-np.pi, np.pi, npar), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=6000)
        best = min(best, float(np.max(np.abs(f(sol.x)))))
        if best < 1e-10:
            break
    return best

if __name__ == "__main__":
    rng = np.random.default_rng(1)
    for n, Ns in ((2, (2, 3)), (3, (4, 5, 6))):
        for N in Ns:
            targets = [(n - 1 - i) % n for i in range(N)]
            errs = [fit_chain(random_unitary(2 ** n, rng), targets, n, seed=s) for s in range(4)]
            cost = N * (2 ** (n - 1) - 1)
            print(f"n={n}, {N} UCGs (targets {targets}), {cost} CNOTs up to diagonal: "
                  + " ".join(f"{e:.1e}" for e in errs), flush=True)
