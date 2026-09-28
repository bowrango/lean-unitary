"""Claim: a 2-control multiplexed Rz (target 2) equals  L1 · a · C3 · b · L2  where
C3 = CX(0→2) · u · CX(1→2) · u' · CX(0→2) (u, u', a, b single-qubit gates on qubit 2) and
L1, L2 are 2-qubit gates on qubits 0,1 — i.e. 3 CNOTs modulo gates the neighbouring leaves absorb."""
import numpy as np
from scipy.linalg import expm
from scipy.optimize import least_squares
from core import circuit_matrix, embed, mux_rot_matrix
from fit import euler

HB = []
for i in range(4):
    for j in range(4):
        E = np.zeros((4, 4), complex)
        if i == j: E[i, i] = 1
        elif i < j: E[i, j] = E[j, i] = 1
        else: E[i, j], E[j, i] = 1j, -1j
        HB.append(E)
HB = np.array(HB)

def u4(x):
    return expm(1j * np.tensordot(x, HB, 1))

def model(p):
    L1, L2 = u4(p[0:16]), u4(p[16:32])
    a, u, up, b = (euler(*p[32 + 3 * i: 35 + 3 * i]) for i in range(4))
    C3 = [("u", 2, b), ("cx", 0, 2), ("u", 2, u), ("cx", 1, 2), ("u", 2, up), ("cx", 0, 2), ("u", 2, a)]
    return embed(L1, [0, 1], 3) @ circuit_matrix(C3, 3) @ embed(L2, [0, 1], 3)

def solve(T, rng, restarts=30):
    f = lambda p: np.concatenate([(model(p) - T).real.ravel(), (model(p) - T).imag.ravel()])
    best = (np.inf, None)
    for _ in range(restarts):
        sol = least_squares(f, rng.uniform(-np.pi, np.pi, 44), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=5000)
        e = float(np.max(np.abs(f(sol.x))))
        if e < best[0]: best = (e, sol.x)
        if e < 1e-10: break
    return best

if __name__ == "__main__":
    rng = np.random.default_rng(3)
    for i in range(6):
        th = rng.uniform(-np.pi, np.pi, 4)
        e, _ = solve(mux_rot_matrix(th, 3, "z"), rng)
        print(f"multiplexed Rz #{i}: residual {e:.1e}", flush=True)
