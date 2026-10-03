"""Find the top-qubit output diagonal (and output ZZ phase) that makes a 3-qubit node's last
leaf a 1-CNOT gate, by damped Gauss-Newton with continuous root-branch tracking."""
import numpy as np
from core import random_unitary
from rank_test import class_vec, final

TARGET = np.array([0.0, 0.0, -4.0, 0.0])   # (tr γ)² = 0, tr γ² = -4  <=>  1-CNOT class

def solve(U, rng, iters=200, tol=1e-12):
    x = np.concatenate([rng.uniform(-np.pi, np.pi, 4), [rng.uniform(0, np.pi)]])
    refs = [rng.uniform(0, np.pi) for _ in range(3)]
    X, refs = final(U, x[:4], x[4], refs)
    r = class_vec(X) - TARGET
    for _ in range(iters):
        if np.max(np.abs(r)) < tol:
            break
        J = []
        for i in range(5):
            dx = np.zeros(5); dx[i] = 1e-7
            J.append((class_vec(final(U, (x + dx)[:4], (x + dx)[4], refs)[0])
                      - class_vec(final(U, (x - dx)[:4], (x - dx)[4], refs)[0])) / 2e-7)
        step = np.linalg.lstsq(np.array(J).T, -r, rcond=None)[0]
        t = 1.0
        while t > 1e-4:
            xn = x + t * step
            Xn, refs_n = final(U, xn[:4], xn[4], refs)
            rn = class_vec(Xn) - TARGET
            if np.linalg.norm(rn) < np.linalg.norm(r):
                x, refs, r = xn, refs_n, rn
                break
            t /= 2
        else:
            return None, np.max(np.abs(r))
    return (x, refs), float(np.max(np.abs(r)))

if __name__ == "__main__":
    rng = np.random.default_rng(12)
    ok = 0
    for trial in range(10):
        U = random_unitary(8, rng)
        best = np.inf
        for attempt in range(20):
            sol, err = solve(U, rng)
            best = min(best, err)
            if err < 1e-12:
                break
        ok += best < 1e-12
        print(f"U{trial}: residual {best:.1e} after {attempt + 1} start(s)", flush=True)
    print(f"{ok}/10 solved")
