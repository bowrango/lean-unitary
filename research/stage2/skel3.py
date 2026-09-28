"""CNOT skeleton of 3-qubit block-ZXZ (19 CNOTs), and universality of skeletons with one CNOT
deleted (free single-qubit gates on every qubit between consecutive CNOTs)."""
import sys, numpy as np
from core import random_unitary
from zxz import synth
from fit import fit

def skeleton(n=3, want_diag=False, seed=7):
    U = random_unitary(2**n, np.random.default_rng(seed))
    circ, _ = synth(U, n, want_diag)
    return [(g[1], g[2]) for g in circ if g[0] == "cx"]

def template(cxs, n=3):
    t = [("u", q) for q in range(n)]
    for c, tg in cxs:
        t += [("cx", c, tg), ("u", c), ("u", tg)]
    return t

if __name__ == "__main__":
    cxs = skeleton()
    print(len(cxs), "CNOTs:", " ".join(f"{c}{t}" for c, t in cxs))
    ntarg = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    rng = np.random.default_rng(1)
    targets = [random_unitary(8, rng) for _ in range(ntarg)]
    full = [fit(U, template(cxs), 3, up_to_diag=False, restarts=8)[2] for U in targets]
    print("full skeleton residuals:", " ".join(f"{e:.0e}" for e in full), flush=True)
    for i in range(len(cxs)):
        sk = cxs[:i] + cxs[i+1:]
        errs = [fit(U, template(sk), 3, up_to_diag=False, restarts=8, seed=s)[2] for s, U in enumerate(targets)]
        print(f"delete #{i:2d} ({cxs[i][0]}{cxs[i][1]}): " + " ".join(f"{e:.0e}" for e in errs), flush=True)
