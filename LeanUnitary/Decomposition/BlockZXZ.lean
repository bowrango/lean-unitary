import LeanUnitary.Decomposition.QSD

/-!
# Block-ZXZ decomposition

Milestone `LeanUnitary.Spec.BlockZXZ`: `(22/48) 4^n - (3/2) 2^n + 5/3` CNOTs for `n ≥ 2`,
improving on optimized QSD.

Outline (arXiv:2403.13692): replace the cosine–sine step of QSD with the paper's block-ZXZ
factorization, which needs fewer multiplexed rotations per recursive step, then apply its CNOT
optimizations. Read the paper for the exact factorization and the count.
-/

namespace LeanUnitary.Decomposition

open LeanUnitary.Spec

theorem blockZXZ : BlockZXZ := by
  sorry

end LeanUnitary.Decomposition
