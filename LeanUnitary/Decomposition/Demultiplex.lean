import LeanUnitary.Circuit
import LeanUnitary.Blocks
import LeanUnitary.LinearAlgebra

/-!
# Demultiplexing

Milestone `LeanUnitary.Spec.Demultiplex`: `A ⊕ B = (V ⊕ V) · (D ⊕ D†) · (W ⊕ W)` where
`D ⊕ D†` is a multiplexed `R_z` on the top qubit.

Outline (Shende–Markov–Bullock, quant-ph/0406176):
* `A B†` is unitary, so `LinearAlgebra.exists_unitary_diagonalize_of_mem_unitaryGroup` gives
  `A B† = V · diag(exp(i φ_k)) · V†`.
* Take `D = diag(exp(-i θ_k / 2))` with `θ_k = -φ_k`, so `D² = diag(exp(i φ_k))`, and set
  `W = D V† B`. Then `V D W = A` and `V D† W = B`.
* Rewrite both sides with `Blocks.blockDiag_eq` and `Blocks.mux_last_eq` (`Rz` entries are the
  diagonal of `D` and `D†`), then finish with `Matrix.fromBlocks_multiply` and `Blocks.ofBlocks_mul`.
-/

namespace LeanUnitary.Decomposition

open LeanUnitary.Spec

theorem demultiplex : Demultiplex := by
  sorry

end LeanUnitary.Decomposition
