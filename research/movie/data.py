"""Data for the explainer video: one Haar-random target run through stage2/foldzxz_opt.py."""
import os
import sys
from functools import lru_cache

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "stage2"))
from core import random_unitary  # noqa: E402
from foldzxz_opt import PivotPath, ordered_phases, unitary_phases  # noqa: E402

N_QUBITS, SEED = 4, 2
D = 2 ** (N_QUBITS - 1)
S = list(range(D // 4, 3 * D // 4))     # middle half of the sorted list
BETAS = np.linspace(0, np.pi, 361)


@lru_cache(maxsize=None)
def pivot():
    U = random_unitary(2 ** N_QUBITS, np.random.default_rng(SEED))
    path = PivotPath(U, N_QUBITS)
    X, Y = U[:D, :D], U[:D, D:]
    rho = np.linalg.eigvals(np.linalg.solve(X, Y))
    return path, rho


def lift(beta):
    path, _ = pivot()
    return ordered_phases(unitary_phases(path.C(beta)), path.determinant_phase(beta))


@lru_cache(maxsize=None)
def table():
    """Lifted eigenphases nu_j(beta) on BETAS, shape (len(BETAS), D)."""
    return np.array([lift(b) for b in BETAS])


def nu_at(beta):
    """Linear interpolation of the lifted list at any beta in [0, pi]."""
    T = table()
    x = np.clip(beta, 0, np.pi) / np.pi * (len(BETAS) - 1)
    i = min(int(x), len(BETAS) - 2)
    f = x - i
    return (1 - f) * T[i] + f * T[i + 1]


def imbalance(nu):
    nu = np.asarray(nu)
    return nu[S].sum() - np.delete(nu, S).sum()


@lru_cache(maxsize=None)
def beta_star():
    return pivot()[0].find_beta()


def alpha_star():
    return pivot()[0].alpha


def rho():
    return pivot()[1]
