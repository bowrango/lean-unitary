import LeanUnitary.Circuit

/-!
# Demultiplexing

Milestone `LeanUnitary.Spec.Demultiplex`: `A ⊕ B = (V ⊕ V) · (D ⊕ D†) · (W ⊕ W)` where
`D ⊕ D†` is a multiplexed `R_z` on the top qubit.

Outline (Shende–Markov–Bullock, quant-ph/0406176):
* `A B†` is unitary, hence normal, so `A B† = V D² V†` with `V` unitary and `D` diagonal
  unitary. Mathlib has the spectral theorem for Hermitian matrices
  (`Matrix.IsHermitian.spectral_theorem`), but not yet for normal/unitary ones: derive it,
  e.g. by simultaneously diagonalizing the commuting Hermitian parts `(M + M†)/2` and
  `(M - M†)/(2i)`, or via a Schur decomposition.
* Choose `D` as a square root of `D²` (a diagonal of phases `exp(-iθ_k/2)`), and set
  `W = D V† B`. Then `V D W = A` and `V D† W = B`.
* `D ⊕ D†` is `mux (Fin.last n) (fun k => Rz (θ k))`.
-/

namespace LeanUnitary.Decomposition

open LeanUnitary.Spec

theorem demultiplex : Demultiplex := by
  sorry

end LeanUnitary.Decomposition
