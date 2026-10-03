"""Solution structure of the k = 2 round-robin node for a fixed target U.
Gauge-invariant data of a solution: for each glue, the multiset of its angles mod 2π
(children can permute L basis states and absorb signs, nothing else touches the angles).
Collect many solutions from random starts and cluster them."""
import sys, numpy as np
from core import random_unitary
from pg_fitk import NodeK
from pg_k_cx import round_robin

def signature(TH):
    return np.array([np.sort(np.mod(th, 2 * np.pi)) for th in TH])

def cluster(sigs, tol=1e-5):
    reps, counts = [], []
    for s in sigs:
        for i, r in enumerate(reps):
            d = np.abs(s - r); d = np.minimum(d, 2 * np.pi - d)
            if d.max() < tol:
                counts[i] += 1; break
        else:
            reps.append(s); counts.append(1)
    return reps, counts

if __name__ == "__main__":
    nL, starts = int(sys.argv[1]), int(sys.argv[2])
    rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    node = NodeK(2, nL, round_robin(2, 15, {}))
    U = random_unitary(node.N, rng)
    sigs = []
    for s in range(starts):
        e = node.fit(U, np.random.default_rng(1000 + s), restarts=1)
        if e < 1e-9:
            sigs.append(signature(node.sol[1]))
    reps, counts = cluster(sigs)
    print(f"d = {2**nL}: {len(sigs)}/{starts} starts converged, {len(reps)} distinct solutions, multiplicities {sorted(counts, reverse=True)}")
    # which glues have the same angle multiset in every solution?
    for g in range(15):
        spread = max(np.max(np.minimum(np.abs(r[g] - reps[0][g]), 2*np.pi - np.abs(r[g] - reps[0][g]))) for r in reps)
        print(f"  glue {g+1:2d} {node.items and ['t','s'][g%2]}: spread across solutions {spread:.2e}  angles(sol 0) {np.round(reps[0][g], 4)}")
    np.save(f"/private/tmp/claude-501/-Users-mattbowring-Desktop-lean-unitary/efba8fc9-0ad8-4714-8599-ed5dadea058a/scratchpad/rr_sols_d{2**nL}.npy", np.array(reps))
    np.save(f"/private/tmp/claude-501/-Users-mattbowring-Desktop-lean-unitary/efba8fc9-0ad8-4714-8599-ed5dadea058a/scratchpad/rr_U_d{2**nL}.npy", U)
