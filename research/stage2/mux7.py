"""Can a 1-control, 2-target multiplexor be leaf(2 CNOT on 01) · middle(3 CNOTs touching qubit 2) ·
leaf(2 CNOT on 01), so the leaves stay shareable with neighbours in block-ZXZ?"""
import numpy as np
from core import block_diag, random_unitary
from fit import fit

def leaf01():
    return [("cx", 0, 1), ("u", 0), ("u", 1), ("cx", 0, 1), ("u", 0), ("u", 1)]

def build(mid_cnots, mid_locals):
    t = [("u", 0), ("u", 1), ("u", 2)] + leaf01()
    for c, tg in mid_cnots:
        t.append(("cx", c, tg))
        t += [("u", q) for q in mid_locals]
    return t + leaf01()

if __name__ == "__main__":
    rng = np.random.default_rng(21)
    targets = [block_diag(random_unitary(4, rng), random_unitary(4, rng)) for _ in range(4)]
    variants = {
        "mid CX02 CX12 CX02, locals on all":  ([(0, 2), (1, 2), (0, 2)], (0, 1, 2)),
        "mid CX02 CX12 CX02, locals on top":   ([(0, 2), (1, 2), (0, 2)], (2,)),
        "mid CX02 CX12 CX12?, locals on all":  ([(0, 2), (1, 2), (1, 2)], (0, 1, 2)),
        "mid CX20 CX12 CX20, locals on all":   ([(2, 0), (1, 2), (2, 0)], (0, 1, 2)),
    }
    for name, (cn, loc) in variants.items():
        errs = [fit(T, build(cn, loc), 3, up_to_diag=True, restarts=25, seed=30 + i)[2] for i, T in enumerate(targets)]
        print(f"{name:38s}: " + " ".join(f"{e:.1e}" for e in errs), flush=True)
