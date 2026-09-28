"""Minimum CNOT count of a generic 1-control, 2-target quantum multiplexor B0 ⊕ B1 (block diagonal
w.r.t. the top qubit 2), exactly and up to a diagonal on the lower qubits (which neighbours absorb).
Demultiplexing gives 2 + 4 + 2 = 8 CNOTs (leaves up to diagonals)."""
import numpy as np
from core import block_diag, random_unitary
from fit import fit
from updiag import generic

if __name__ == "__main__":
    rng = np.random.default_rng(13)
    targets = [block_diag(random_unitary(4, rng), random_unitary(4, rng)) for _ in range(3)]
    for k in (4, 5, 6, 7):
        errs = [fit(T, generic(k), 3, up_to_diag=True, restarts=8, seed=i)[2] for i, T in enumerate(targets)]
        print(f"multiplexor, {k} CNOTs (up to a 3-qubit diagonal): " + " ".join(f"{e:.1e}" for e in errs), flush=True)
