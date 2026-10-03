"""Template fitting where the free output diagonal acts only on chosen qubits (the ones whose
diagonal the next element in the chain can absorb)."""
import numpy as np
from scipy.optimize import least_squares
from core import circuit_matrix, embed
from fit import realize, n_slots

def fit_low(target, template, n, diag_qubits, restarts=25, seed=0):
    rng = np.random.default_rng(seed)
    k = 3 * n_slots(template)
    m = 2 ** len(diag_qubits)
    def resid(p):
        D = embed(np.diag(np.exp(1j * p[k:k + m])), list(diag_qubits), n) * np.exp(1j * p[-1])
        M = D @ circuit_matrix(realize(template, p[:k]), n)
        r = (M - target).ravel()
        return np.concatenate([r.real, r.imag])
    best = np.inf
    for _ in range(restarts):
        sol = least_squares(resid, rng.uniform(-np.pi, np.pi, k + m + 1), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        best = min(best, float(np.max(np.abs(resid(sol.x)))))
        if best < 1e-10: break
    return best
