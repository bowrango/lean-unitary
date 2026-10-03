"""Which single-qubit gates inside the 3-CNOT middle are essential?  Middle: CX02 · (locals) ·
CX12 · (locals) · CX02, flanked by 2-CNOT leaves on qubits 0,1. Locals restricted per variant."""
import numpy as np
from scipy.optimize import least_squares
from core import block_diag, circuit_matrix, random_unitary, ry, rz
from fit import euler

KINDS = {"U": 3, "Z": 1, "Y": 1, "X": 1, "-": 0}

def gate(kind, p):
    if kind == "U": return euler(*p)
    if kind == "Z": return rz(p[0])
    if kind == "Y": return ry(p[0])
    if kind == "X": return np.array([[np.cos(p[0]/2), -1j*np.sin(p[0]/2)], [-1j*np.sin(p[0]/2), np.cos(p[0]/2)]])
    return np.eye(2)

def template(inside):
    """inside: kinds for (q0, q1, q2) after the 1st and after the 2nd middle CNOT."""
    t = [("U", q) for q in range(3)]
    t += [("cx", 0, 1), ("U", 0), ("U", 1), ("cx", 0, 1), ("U", 0), ("U", 1), ("U", 2)]
    for i, (c, tg) in enumerate([(0, 2), (1, 2), (0, 2)]):
        t.append(("cx", c, tg))
        if i < 2:
            t += [(inside[q], q) for q in range(3)]
    t += [("U", 0), ("U", 1), ("U", 2)]
    t += [("cx", 0, 1), ("U", 0), ("U", 1), ("cx", 0, 1), ("U", 0), ("U", 1)]
    return t

def realize(t, p):
    circ, k = [], 0
    for g in t:
        if g[0] == "cx":
            circ.append(g)
        else:
            m = KINDS[g[0]]
            circ.append(("u", g[1], gate(g[0], p[k:k + m]))); k += m
    return circ, k

def fit(T, t, restarts=25, seed=0):
    rng = np.random.default_rng(seed)
    _, k = realize(t, np.zeros(10000))
    f = lambda p: (lambda M: np.concatenate([M.real.ravel(), M.imag.ravel()]))(
        np.exp(1j * p[k:])[:, None] * circuit_matrix(realize(t, p)[0], 3) - T)
    best = np.inf
    for _ in range(restarts):
        sol = least_squares(f, rng.uniform(-np.pi, np.pi, k + 8), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        best = min(best, float(np.max(np.abs(f(sol.x)))))
        if best < 1e-10: break
    return best

if __name__ == "__main__":
    rng = np.random.default_rng(21)
    targets = [block_diag(random_unitary(4, rng), random_unitary(4, rng)) for _ in range(3)]
    variants = ["UUU", "-UU", "U-U", "ZZU", "YYU", "YZU", "ZYU", "Y-U", "-YU", "YYZ", "YY-"]
    for v in variants:
        errs = [fit(T, template(v), seed=40 + i) for i, T in enumerate(targets)]
        print(f"inside (q0,q1,q2) = {v}: " + " ".join(f"{e:.1e}" for e in errs), flush=True)
