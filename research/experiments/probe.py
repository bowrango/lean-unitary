"""Probe which CNOT skeletons can reach all of U(2^n) (necessary condition: Jacobian rank = 4^n)."""
import numpy as np
from core import circuit_matrix, random_unitary
from fit import realize

def template_from_cnots(cnots, n):
    t = [("u", q) for q in range(n)]
    for (c, tg) in cnots:
        t += [("cx", c, tg), ("u", c), ("u", tg)]
    return t

def jac_rank(template, n, seed=0, eps=1e-6):
    rng = np.random.default_rng(seed)
    k = 3 * sum(1 for g in template if g[0] == "u")
    p = rng.uniform(-np.pi, np.pi, k)
    M0 = circuit_matrix(realize(template, p), n)
    cols = []
    for i in range(k):
        dp = np.zeros(k); dp[i] = eps
        dM = (circuit_matrix(realize(template, p + dp), n) - M0) / eps
        # tangent in the Lie algebra: M0^† dM is anti-Hermitian; add global phase direction
        A = M0.conj().T @ dM
        cols.append(np.concatenate([A.real.ravel(), A.imag.ravel()]))
    cols.append(np.concatenate([np.zeros(4**n), np.eye(2**n).ravel()]))  # global phase
    s = np.linalg.svd(np.array(cols).T, compute_uv=False)
    return int(np.sum(s > 1e-6 * s[0]))
