import LeanUnitary.Circuit

/-!
# Cosine–sine decomposition

Milestone `LeanUnitary.Spec.CosineSine`: any unitary on `n + 1` qubits is
`(A₀ ⊕ A₁) · Y · (B₀ ⊕ B₁)` with `Y` a multiplexed `R_y` on the top qubit, i.e. the block
matrix `[C -S; S C]` with `C = diag(cos(θ_k/2))`, `S = diag(sin(θ_k/2))`.

Outline (Paige–Wei, "History and generality of the CS decomposition", 1994; Shende–Markov–Bullock):
* Write `U = [U₀₀ U₀₁; U₁₀ U₁₁]` in half-size blocks (top qubit = block index).
* Take an SVD `U₀₀ = A₀ C B₀†` (singular values in `[0, 1]` since `U` is unitary). Mathlib has
  singular values (`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`);
  an SVD for square complex matrices may need to be assembled from the Hermitian
  spectral theorem applied to `U₀₀† U₀₀`.
* Unitarity forces `U₁₀ = A₁ S B₀†` for a unitary `A₁` and `S = sqrt(1 - C²)`, and similarly
  for the right column. Degenerate singular values (0 or 1) need care.
-/

namespace LeanUnitary.Decomposition

open LeanUnitary.Spec

theorem cosineSine : CosineSine := by
  sorry

end LeanUnitary.Decomposition
