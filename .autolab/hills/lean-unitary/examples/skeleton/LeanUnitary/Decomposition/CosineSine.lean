import LeanUnitary.Circuit
import LeanUnitary.Blocks
import LeanUnitary.LinearAlgebra

/-!
# Cosine–sine decomposition

Milestone `LeanUnitary.Spec.CosineSine`: any unitary on `n + 1` qubits is
`(A₀ ⊕ A₁) · Y · (B₀ ⊕ B₁)` with `Y` a multiplexed `R_y` on the top qubit, i.e. the block
matrix `[C -S; S C]` with `C = diag(cos(θ_k/2))`, `S = diag(sin(θ_k/2))`.

Outline (Paige–Wei, "History and generality of the CS decomposition", 1994; Shende–Markov–Bullock):
* The block-matrix statement is `LinearAlgebra.exists_cosineSine` (its docstring has the proof
  route from Mathlib's Hermitian spectral theorem).
* Transport it with `Blocks.topSplit`: `Matrix.reindex` the unitary `U` into
  `Fin (2^n) ⊕ Fin (2^n)` blocks, apply `exists_cosineSine`, and rewrite back with
  `Blocks.blockDiag_eq` and `Blocks.mux_last_eq`.
* The spec's `Ry (θ k)` has `cos(θ k / 2)` on its diagonal, so use the angles `2 θ_k`.
-/

namespace LeanUnitary.Decomposition

open LeanUnitary.Spec

theorem cosineSine : CosineSine := by
  sorry

end LeanUnitary.Decomposition
