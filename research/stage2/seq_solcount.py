"""Number of distinct solutions (mod gauge) for one random target, for several k = 2 sequences.
Few solutions (k = 1 has 2^d) suggest a closed-form construction; many suggest none."""
import sys, numpy as np
from core import random_unitary
from pg_fitk import NodeK
from pauli_glue_k import exact_rank
from rr_solutions import signature

SEQS = {
    "round-robin": "0:Z 1:Z 0:X 1:X 0:Z 1:Z 0:X 1:X 0:Z 1:Z 0:X 1:X 0:Z 1:Z 0:X",
    "KAK":         "1:Z 0:Z 1:X 0:X 1:Z 0:Z XX YY ZZ 1:Z 0:Z 1:X 0:X 1:Z 0:Z",
    "KAK-ZZ-mid":  "1:Z 0:Z 1:X 0:X 1:Z 0:Z XX ZZ YY 1:Z 0:Z 1:X 0:X 1:Z 0:Z",
}
nL, starts = int(sys.argv[1]), int(sys.argv[2])
names = sys.argv[3:] or list(SEQS)
for name in names:
    toks = SEQS[name].split()
    node = NodeK(2, nL, toks)
    rng = np.random.default_rng(0)
    U = random_unitary(node.N, rng)
    reps, conv = [], 0
    for s in range(starts):
        if node.fit(U, np.random.default_rng(5000 + s), restarts=1) > 1e-9: continue
        conv += 1
        sig = signature(node.sol[1])
        if not any(np.max(np.minimum(np.abs(sig - r), 2*np.pi - np.abs(sig - r))) < 1e-5 for r in reps):
            reps.append(sig)
    print(f"{name:12s} d={2**nL}: {conv}/{starts} converged, {len(reps)} distinct solutions", flush=True)
