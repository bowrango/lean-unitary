import sys, numpy as np
from pauli_glue import Node, exact_rank
nL = int(sys.argv[1]); trials = int(sys.argv[2]); mode = sys.argv[3]
rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
w1 = ["IZ", "IX", "ZI", "XI"]
opts = {"w1": w1, "w2": w1 + ["ZZ", "XX", "ZX", "XZ"], "all": [a + b for a in "IXYZ" for b in "IXYZ"][1:]}[mode]
full = 4 ** (nL + 2); hist = {}
for _ in range(trials):
    seq = [str(rng.choice(opts))]
    while len(seq) < 15:
        c = str(rng.choice(opts))
        if c != seq[-1]: seq.append(c)
    r = exact_rank(Node(nL, seq), rng)
    hist[r] = hist.get(r, 0) + 1
    if r >= full - 1: print(r, full, " ".join(seq), flush=True)
print(mode, "rank histogram:", dict(sorted(hist.items())))
