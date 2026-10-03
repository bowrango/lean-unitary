"""Minimum CNOT count for a 3-qubit unitary exactly vs up to an output diagonal (numerical)."""
import numpy as np
from core import random_unitary
from fit import fit

def generic(k, n=3, pairs=((0, 1), (1, 2), (0, 2))):
    t = [("u", q) for q in range(n)]
    for i in range(k):
        c, tg = pairs[i % len(pairs)]
        t += [("cx", c, tg), ("u", c), ("u", tg)]
    return t

if __name__ == "__main__":
    rng = np.random.default_rng(9)
    Us = [random_unitary(8, rng) for _ in range(3)]
    for up in (True, False):
        for k in ((11, 12, 13) if up else (13, 14)):
            errs = [fit(U, generic(k), 3, up_to_diag=up, restarts=8, seed=i)[2] for i, U in enumerate(Us)]
            print(f"{'up to diagonal' if up else 'exact':15s} k={k}: " + " ".join(f"{e:.1e}" for e in errs), flush=True)
