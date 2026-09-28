"""Enumerate solutions (mod gauge) of the round-robin node for one target by many random starts;
report distinct solutions found vs starts (saturation) and the signed count Σ local degree."""
import sys, numpy as np
from core import random_unitary
from pg_fitk import NodeK
from pg_k_cx import round_robin
from rr_solutions import signature, cluster
from rr_degree import local_degree

k, nL, starts = map(int, sys.argv[1:4])
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
rng = np.random.default_rng(seed)
node = NodeK(k, nL, round_robin(k, 4**k - 1, {}))
U = random_unitary(node.N, rng)
reps, signs, conv = [], [], 0
for s in range(starts):
    e = node.fit(U, np.random.default_rng(10**6 * seed + s), restarts=1)
    if e > 1e-9:
        continue
    conv += 1
    sig = signature(node.sol[1])
    for r in reps:
        dd = np.abs(sig - r); dd = np.minimum(dd, 2 * np.pi - dd)
        if dd.max() < 1e-5: break
    else:
        reps.append(sig); signs.append(local_degree(node, *node.sol)[0])
    if (s + 1) % max(1, starts // 10) == 0:
        print(f"after {s+1} starts: {conv} converged, {len(reps)} distinct, +{signs.count(1)} -{signs.count(-1)}, signed sum {sum(signs)}", flush=True)
