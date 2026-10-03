"""Numerically fit fixed-CNOT circuit templates to a target unitary.

A template is a list of ("u", q) slots (a free single-qubit gate) and ("cx", c, t) gates.
`fit` finds single-qubit gates (and optionally a trailing diagonal) so that

    target == diag · template        (up_to_diag=True)
    target == e^{iφ} · template      (up_to_diag=False)

Used for small leaves whose exact constructions are known theorems (3 CNOTs for any 2-qubit
unitary; 2 CNOTs up to a diagonal), and to probe whether a candidate template is universal.
"""

from __future__ import annotations

import numpy as np
from scipy.optimize import least_squares

from core import circuit_matrix, ry, rz


def euler(a: float, b: float, c: float) -> np.ndarray:
    return rz(a) @ ry(b) @ rz(c)


def realize(template: list[tuple], params: np.ndarray) -> list[tuple]:
    circ, k = [], 0
    for g in template:
        if g[0] == "u":
            circ.append(("u", g[1], euler(*params[k : k + 3])))
            k += 3
        else:
            circ.append(g)
    return circ


def n_slots(template: list[tuple]) -> int:
    return sum(1 for g in template if g[0] == "u")


def fit(target: np.ndarray, template: list[tuple], n: int, *, up_to_diag: bool,
        restarts: int = 40, tol: float = 1e-10, seed: int = 0):
    """Returns (circuit, diag, residual). diag is the diagonal D with target ≈ D · circuit."""
    rng = np.random.default_rng(seed)
    d = 2**n
    k = 3 * n_slots(template)
    n_phase = d if up_to_diag else 1

    def split(p):
        phases = p[k:]
        D = np.exp(1j * phases) if up_to_diag else np.full(d, np.exp(1j * phases[0]))
        return p[:k], D

    def resid(p):
        q, D = split(p)
        M = D[:, None] * circuit_matrix(realize(template, q), n)
        r = (M - target).ravel()
        return np.concatenate([r.real, r.imag])

    best = None
    for _ in range(restarts):
        p0 = rng.uniform(-np.pi, np.pi, k + n_phase)
        sol = least_squares(resid, p0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        err = float(np.max(np.abs(resid(sol.x))))
        if best is None or err < best[0]:
            best = (err, sol.x)
        if err < tol:
            break
    err, p = best
    q, D = split(p)
    return realize(template, q), np.diag(D), err


def layered(n_cx: int, pairs=((0, 1),)) -> list[tuple]:
    """Local layer, then n_cx × (CNOT, local layer), CNOTs cycling through `pairs`."""
    t: list[tuple] = [("u", 0), ("u", 1)]
    for i in range(n_cx):
        c, tg = pairs[i % len(pairs)]
        t += [("cx", c, tg), ("u", 0), ("u", 1)]
    return t
