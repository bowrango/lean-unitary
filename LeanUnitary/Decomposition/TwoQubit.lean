import LeanUnitary.Circuit
import LeanUnitary.LinearAlgebra

/-!
# Optimal two-qubit synthesis

Milestone `LeanUnitary.Spec.TwoQubitOptimal`: every two-qubit unitary uses at most 3 CNOTs,
which meets the lower bound for `n = 2`.

Outline (Vatan–Williams, quant-ph/0308006; Kraus–Cirac, quant-ph/0011050):
* In the magic basis, local gates `SU(2) ⊗ SU(2)` become real orthogonal matrices `SO(4)`.
* For `U` in the magic basis, `Uᵀ U` is symmetric unitary; its real and imaginary parts are
  commuting real symmetric matrices, so they are simultaneously orthogonally diagonalizable:
  `LinearAlgebra.exists_unitary_diagonalize_of_commute` with `𝕜 = ℝ`. This gives the canonical (KAK) form
  `U = (A ⊗ B) · exp(i(a XX + b YY + c ZZ)) · (C ⊗ D)` up to a global phase.
* The canonical gate has an explicit 3-CNOT circuit (Vatan–Williams), and the phase is
  absorbed into a single-qubit gate.
-/

namespace LeanUnitary.Decomposition

open LeanUnitary.Spec

theorem twoQubitOptimal : TwoQubitOptimal := by
  sorry

end LeanUnitary.Decomposition
