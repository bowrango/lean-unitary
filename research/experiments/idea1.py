"""Idea 1: spend the top-qubit part of a 3-qubit node's free output diagonal on the last leaf.

Question: does every M in U(4) factor as  M = P · T · E · T^† · Q  with P, Q, E diagonal
unitaries and T a 1-CNOT circuit (a⊗b)·CX·(c⊗d)?  If so, Va (eigenvectors of the modified
A1 A2^†) needs 1 CNOT up to diagonals instead of 2.
"""
import numpy as np
from scipy.optimize import least_squares
from core import circuit_matrix, random_unitary
from fit import realize

T_TEMPLATE = [("u", 0), ("u", 1), ("cx", 0, 1), ("u", 0), ("u", 1)]

def model(p):
    P = np.exp(1j * p[0:4]); Q = np.exp(1j * p[4:8]); E = np.exp(1j * p[8:12])
    T = circuit_matrix(realize(T_TEMPLATE, p[12:]), 2)
    return (P[:, None] * (T @ np.diag(E) @ T.conj().T)) * Q[None, :]

def try_factor(M, restarts=60, seed=0):
    rng = np.random.default_rng(seed)
    best = np.inf
    for _ in range(restarts):
        p0 = rng.uniform(-np.pi, np.pi, 12 + 12)
        r = lambda p: np.concatenate([(model(p) - M).real.ravel(), (model(p) - M).imag.ravel()])
        sol = least_squares(r, p0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
        best = min(best, float(np.max(np.abs(r(sol.x)))))
        if best < 1e-10:
            break
    return best

if __name__ == "__main__":
    rng = np.random.default_rng(11)
    errs = [try_factor(random_unitary(4, rng), seed=i) for i in range(8)]
    print("residuals:", " ".join(f"{e:.1e}" for e in errs))
