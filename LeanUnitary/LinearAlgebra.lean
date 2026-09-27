import Mathlib

/-!
# Linear-algebra primitives

The decompositions need three facts that Mathlib does not state in this form. Each is a short
step from results Mathlib already proves; **derive them from Mathlib, do not re-develop spectral
theory.** They are stated for arbitrary finite index types, as Mathlib is, so that
`Matrix.fromBlocks` and `Matrix.reindex` apply directly (see `LeanUnitary.Blocks`).

Mathlib ingredients (search `.lake/packages/mathlib` and use `exact?`/`apply?` before proving
any lemma yourself):

* `Matrix.IsHermitian.spectral_theorem`, `.eigenvectorUnitary`, `.eigenvalues`: the spectral
  theorem for Hermitian matrices over any `RCLike` field (so also real symmetric matrices).
* `LinearMap.IsSymmetric.directSum_isInternal_of_commute` (`Analysis/InnerProductSpace/
  JointEigenspace.lean`): commuting symmetric operators have a joint eigenspace decomposition.
  `DirectSum.IsInternal.collectedOrthonormalBasis` turns it into an orthonormal basis, as
  `Matrix.IsHermitian.eigenvectorBasis` does for one operator.
* `Matrix.isHermitian_iff_isSymmetric`, `Matrix.toEuclideanLin`: move between matrices and
  symmetric operators on `EuclideanSpace`.
* `isStarNormal_of_mem_unitary`, `Unitary.spectrum_subset_circle`: unitaries are normal, with
  unit-modulus spectrum. `Complex.norm_eq_one_iff`: `‖z‖ = 1 ↔ ∃ θ, exp (θ * I) = z`.
* `Matrix.PosSemidef`, `Matrix.IsHermitian.cfc` (e.g. `Real.sqrt` applied to the eigenvalues):
  square roots of positive semidefinite matrices. `LinearMap.singularValues`: singular values.
* `Orthonormal.exists_orthonormalBasis_extension`, `gramSchmidtNormed`: completing an
  orthonormal family (needed where cosines or sines vanish in the CS decomposition).
* `Matrix.fromBlocks_multiply`, `Matrix.fromBlocks_diagonal`, `Matrix.fromBlocks_conjTranspose`,
  `Matrix.kronecker_mem_unitary`, `Matrix.mem_unitaryGroup_iff`.
-/

namespace LeanUnitary.LinearAlgebra

open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Commuting Hermitian matrices are simultaneously unitarily diagonalizable. Over `ℝ` this is
simultaneous orthogonal diagonalization of commuting symmetric matrices (the key step of the
two-qubit KAK decomposition).

Route: `LinearMap.IsSymmetric.directSum_isInternal_of_commute` on `toEuclideanLin A` and
`toEuclideanLin B`, then an orthonormal basis of joint eigenvectors, as a unitary matrix. -/
theorem exists_unitary_diagonalize_of_commute {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix m m 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B) :
    ∃ V ∈ unitaryGroup m 𝕜, ∃ a b : m → ℝ,
      A = V * diagonal (fun i => (a i : 𝕜)) * star V ∧
      B = V * diagonal (fun i => (b i : 𝕜)) * star V := by
  sorry

/-- Unitary matrices are unitarily diagonalizable, with eigenvalues `exp (i θ)` (demultiplexing).

Route: the Hermitian parts `(U + Uᴴ)/2` and `(U - Uᴴ)/(2i)` commute because `U` is normal;
apply `exists_unitary_diagonalize_of_commute`, then `Complex.norm_eq_one_iff` on the eigenvalues. -/
theorem exists_unitary_diagonalize_of_mem_unitaryGroup {U : Matrix m m ℂ}
    (hU : U ∈ unitaryGroup m ℂ) :
    ∃ V ∈ unitaryGroup m ℂ, ∃ θ : m → ℝ,
      U = V * diagonal (fun i => Complex.exp (θ i * Complex.I)) * star V := by
  sorry

/-- The cosine–sine decomposition of a unitary with equal-size blocks.

Route: diagonalize the positive semidefinite `U₀₀ᴴ U₀₀ = B₀ C² B₀ᴴ` with the Hermitian spectral
theorem (eigenvalues in `[0, 1]` since `U₀₀ᴴ U₀₀ + U₁₀ᴴ U₁₀ = 1`). The columns of `U₀₀ B₀` and
`U₁₀ B₀` are orthogonal with norms `cos θᵢ` and `sin θᵢ`; normalize them into `A₀`, `A₁`,
completing with `Orthonormal.exists_orthonormalBasis_extension` where a norm is zero. `B₁`
then follows from unitarity of the right column. -/
theorem exists_cosineSine {U : Matrix (m ⊕ m) (m ⊕ m) ℂ} (hU : U ∈ unitaryGroup (m ⊕ m) ℂ) :
    ∃ A₀ ∈ unitaryGroup m ℂ, ∃ A₁ ∈ unitaryGroup m ℂ,
    ∃ B₀ ∈ unitaryGroup m ℂ, ∃ B₁ ∈ unitaryGroup m ℂ, ∃ θ : m → ℝ,
      U = fromBlocks A₀ 0 0 A₁ *
        fromBlocks (diagonal fun i => (Real.cos (θ i) : ℂ)) (diagonal fun i => -(Real.sin (θ i) : ℂ))
          (diagonal fun i => (Real.sin (θ i) : ℂ)) (diagonal fun i => (Real.cos (θ i) : ℂ)) *
        fromBlocks B₀ 0 0 B₁ := by
  sorry

end LeanUnitary.LinearAlgebra
