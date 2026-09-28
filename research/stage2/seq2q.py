"""Ansatz: a 3-qubit unitary as a product of general 2-qubit gates on a fixed pair sequence.
Each 2-qubit gate is a 3-CNOT template (any 2-qubit unitary), so k gates cost 3k CNOTs."""
import numpy as np
from core import random_unitary
from fit import fit

def gate_template(a, b):
    t = [("u", a), ("u", b)]
    for _ in range(3):
        t += [("cx", a, b), ("u", a), ("u", b)]
    return t

def seq_template(pairs):
    t = []
    for (a, b) in pairs:
        g = gate_template(a, b)
        t += g if not t else g[2:] if False else g  # keep all locals; redundancy is harmless
    return t

if __name__ == "__main__":
    import sys
    rng = np.random.default_rng(3)
    patterns = {
        "6 alt (01)(12)": [(0, 1), (1, 2)] * 3,
        "5 alt (01)(12)": [(0, 1), (1, 2), (0, 1), (1, 2), (0, 1)],
        "6 cyc (01)(12)(02)": [(0, 1), (1, 2), (0, 2)] * 2,
    }
    for name, pairs in patterns.items():
        errs = []
        for trial in range(3):
            U = random_unitary(8, rng)
            _, _, e = fit(U, seq_template(pairs), 3, up_to_diag=False, restarts=6, seed=trial)
            errs.append(e)
        print(f"{name:22s} ({3*len(pairs)} CNOTs): residuals " + " ".join(f"{e:.1e}" for e in errs), flush=True)
