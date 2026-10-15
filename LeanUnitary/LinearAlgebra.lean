import Mathlib

/-!
# Unitary diagonalization

Mathlib proves the spectral theorem for Hermitian matrices only. This module derives it for
unitary matrices (`exists_unitary_diagonalize_of_mem_unitaryGroup`), which demultiplexing needs.
Results are stated for arbitrary finite index types, so that `Matrix.fromBlocks` and
`Matrix.reindex` apply directly (see `LeanUnitary.Blocks`).
-/

namespace LeanUnitary.LinearAlgebra

open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ### The Cayley transform

A unitary `U` with `1 + U` invertible has the Hermitian Cayley transform
`H = i (1 - U) (1 + U)⁻¹`, and `U = (H + i)⁻¹ (i - H)`; diagonalizing `H` diagonalizes `U`. A unit
phase `ω` with `-ω⁻¹` outside the (finite) spectrum makes `1 + ω U` invertible. -/

/-- A unitary `U` with `1 + U` invertible is unitarily diagonalizable. -/
theorem exists_unitary_diagonalize_of_isUnit_one_add {U : Matrix m m ℂ}
    (hU : U ∈ unitaryGroup m ℂ) (hA : IsUnit (1 + U)) :
    ∃ V ∈ unitaryGroup m ℂ, ∃ e : m → ℂ, U = V * diagonal e * star V := by
  set A : Matrix m m ℂ := 1 + U with hAdef
  have hAdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA
  have hUU : Uᴴ * U = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hU
  set H : Matrix m m ℂ := (Complex.I • (1 - U)) * A⁻¹ with hHdef
  have hHA : H * A = Complex.I • (1 - U) := by
    rw [hHdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAdet, Matrix.mul_one]
  -- `Aᴴ H A = i (Uᴴ - U)` is Hermitian, hence so is `H`
  have hkey : Aᴴ * H * A = Complex.I • (Uᴴ - U) := by
    rw [Matrix.mul_assoc, hHA, hAdef, conjTranspose_add, conjTranspose_one, Matrix.mul_smul,
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hUU]
    congr 1; abel
  have hherm : Hᴴ = H := by
    have h1 : Aᴴ * Hᴴ * A = Aᴴ * H * A := by
      have : (Aᴴ * H * A)ᴴ = Aᴴ * Hᴴ * A := by
        rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← this, hkey, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      rw [show star Complex.I = -Complex.I from by simp]
      rw [neg_smul, ← smul_neg, neg_sub]
    have hAs : IsUnit Aᴴ := by rw [← star_eq_conjTranspose]; exact hA.star
    have h2 : Aᴴ * (Hᴴ * A) = Aᴴ * (H * A) := by simpa only [Matrix.mul_assoc] using h1
    exact hA.mul_right_cancel (hAs.mul_left_cancel h2)
  have hHerm : H.IsHermitian := hherm
  set W := hHerm.eigenvectorUnitary with hW
  set d : m → ℂ := fun k => (hHerm.eigenvalues k : ℂ) with hd
  have hspec : H = (W : Matrix m m ℂ) * diagonal d * star (W : Matrix m m ℂ) := by
    conv_lhs => rw [hHerm.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hWW : star (W : Matrix m m ℂ) * (W : Matrix m m ℂ) = 1 :=
    mem_unitaryGroup_iff'.mp W.2
  have hdI : ∀ k, d k + Complex.I ≠ 0 := by
    intro k h
    have := congrArg Complex.im h
    simp [hd] at this
  set e : m → ℂ := fun k => (Complex.I - d k) / (d k + Complex.I) with he
  refine ⟨W, W.2, e, ?_⟩
  -- `(H + i) U = i - H`, and `H + i` is invertible
  have hHU : (H + Complex.I • 1) * U = Complex.I • 1 - H := by
    have : H * A = H + H * U := by rw [hAdef, Matrix.mul_add, Matrix.mul_one]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    have h2 := hHA
    rw [this, smul_sub] at h2
    rw [smul_one_eq_diagonal] at *
    calc H * U + Complex.I • U = (H + H * U) - H + Complex.I • U := by abel
      _ = _ := by rw [h2]; rw [Matrix.smul_eq_diagonal_mul] at *; abel
  have hHI : IsUnit (H + Complex.I • 1) := by
    have h3 : (H + Complex.I • 1) * A = (2 * Complex.I) • 1 := by
      rw [Matrix.add_mul, hHA, Matrix.smul_mul, Matrix.one_mul, hAdef, smul_sub, smul_add,
        two_mul, add_smul]
      abel
    have h4 : (H + Complex.I • 1) * ((2 * Complex.I)⁻¹ • A) = 1 := by
      rw [Matrix.mul_smul, h3, smul_smul, inv_mul_cancel₀ (by simp), one_smul]
    exact (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_right_inverse h4)
  apply hHI.mul_left_cancel
  rw [hHU, hspec]
  symm
  have hdiag : diagonal d + Complex.I • 1 = diagonal fun k => d k + Complex.I := by
    rw [smul_one_eq_diagonal, diagonal_add]
  have hdiag' : Complex.I • 1 - diagonal d = diagonal fun k => Complex.I - d k := by
    rw [smul_one_eq_diagonal, diagonal_sub]
  have hWW' : (W : Matrix m m ℂ) * star (W : Matrix m m ℂ) = 1 := mem_unitaryGroup_iff.mp W.2
  have hde : (fun k => (d k + Complex.I) * e k) = fun k => Complex.I - d k := by
    funext k; rw [he]; field_simp [hdI k]
  calc ((W : Matrix m m ℂ) * diagonal d * star (W : Matrix m m ℂ) + Complex.I • 1) *
        ((W : Matrix m m ℂ) * diagonal e * star (W : Matrix m m ℂ))
      = (W : Matrix m m ℂ) * (diagonal d * diagonal e) * star (W : Matrix m m ℂ) +
          Complex.I • ((W : Matrix m m ℂ) * diagonal e * star (W : Matrix m m ℂ)) := by
        rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (star (W : Matrix m m ℂ)) (W : Matrix m m ℂ), hWW, Matrix.one_mul]
    _ = (W : Matrix m m ℂ) * ((diagonal d + Complex.I • 1) * diagonal e) *
          star (W : Matrix m m ℂ) := by
        rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_smul, Matrix.smul_mul]
    _ = (W : Matrix m m ℂ) * (Complex.I • 1 - diagonal d) * star (W : Matrix m m ℂ) := by
        rw [hdiag, hdiag', diagonal_mul_diagonal, hde]
    _ = Complex.I • 1 - (W : Matrix m m ℂ) * diagonal d * star (W : Matrix m m ℂ) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hWW']

/-- Some unit phase `z` lies outside the finite spectrum of a matrix. -/
theorem exists_unit_not_mem_spectrum (U : Matrix m m ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ z ∉ spectrum ℂ U := by
  have hinf : (((↑) : Circle → ℂ) ∘ Circle.exp) '' Set.Icc 0 1 |>.Infinite :=
    (Set.Icc_infinite zero_lt_one).image
      (Subtype.val_injective.injOn.comp (Circle.exp_injOn_Icc (by linarith [Real.pi_gt_three]))
        (Set.mapsTo_univ _ _))
  obtain ⟨z, ⟨t, -, rfl⟩, hz⟩ := (hinf.diff (Matrix.finite_spectrum U)).nonempty
  exact ⟨_, Circle.norm_coe _, hz⟩

/-- Unitary matrices are unitarily diagonalizable, with eigenvalues `exp (i θ)`.

Route: rotate by a unit phase so that `1 + ω U` is invertible, then apply the Cayley transform
(`exists_unitary_diagonalize_of_isUnit_one_add`); the diagonal of a unitary has unit entries. -/
theorem exists_unitary_diagonalize_of_mem_unitaryGroup {U : Matrix m m ℂ}
    (hU : U ∈ unitaryGroup m ℂ) :
    ∃ V ∈ unitaryGroup m ℂ, ∃ θ : m → ℝ,
      U = V * diagonal (fun i => Complex.exp (θ i * Complex.I)) * star V := by
  obtain ⟨z, hz1, hz⟩ := exists_unit_not_mem_spectrum U
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
  have hzz : star z * z = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz1]
    simp
  set U' : Matrix m m ℂ := (-z⁻¹) • U with hU'def
  have hU' : U' ∈ unitaryGroup m ℂ := by
    rw [mem_unitaryGroup_iff', hU'def, star_smul, smul_mul_smul, mem_unitaryGroup_iff'.mp hU]
    rw [star_neg, neg_mul_neg, star_inv₀, ← mul_inv, hzz, inv_one, one_smul]
  have hA : IsUnit (1 + U') := by
    have h1 : IsUnit (z • (1 : Matrix m m ℂ) - U) := by
      have := spectrum.notMem_iff.mp hz
      rwa [Algebra.algebraMap_eq_smul_one] at this
    have h2 : 1 + U' = z⁻¹ • (z • (1 : Matrix m m ℂ) - U) := by
      rw [hU'def, smul_sub, smul_smul, inv_mul_cancel₀ hz0, one_smul, neg_smul, sub_eq_add_neg]
    rw [h2, isUnit_iff_isUnit_det, det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.mpr (inv_ne_zero hz0))).mul
      ((isUnit_iff_isUnit_det _).mp h1)
  obtain ⟨V, hV, e, hVe⟩ := exists_unitary_diagonalize_of_isUnit_one_add hU' hA
  have hUe : U = V * diagonal (fun k => -z * e k) * star V := by
    have : U = (-z) • U' := by rw [hU'def, smul_smul, neg_mul_neg, mul_inv_cancel₀ hz0, one_smul]
    have hd : diagonal (fun k => -z * e k) = (-z) • diagonal e := by
      ext i j; by_cases h : i = j <;> simp [h]
    rw [this, hVe, hd, Matrix.mul_smul, Matrix.smul_mul]
  -- the diagonal entries have norm one
  have hdiagU : diagonal (fun k => -z * e k) ∈ unitaryGroup m ℂ := by
    have : diagonal (fun k => -z * e k) = star V * U * V := by
      rw [hUe, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff'.mp hV,
        Matrix.one_mul, Matrix.mul_assoc, mem_unitaryGroup_iff'.mp hV, Matrix.mul_one]
    rw [this]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hV) hU) hV
  have hnorm : ∀ k, ‖-z * e k‖ = 1 := by
    intro k
    have h := congrFun (congrFun (mem_unitaryGroup_iff'.mp hdiagU) k) k
    simp only [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      diagonal_apply_eq, one_apply_eq, Pi.star_apply] at h
    have h' : Complex.normSq (-z * e k) = 1 := by
      have : (Complex.normSq (-z * e k) : ℂ) = 1 := by
        rw [Complex.normSq_eq_conj_mul_self]; exact h
      exact_mod_cast this
    rw [Complex.normSq_eq_norm_sq] at h'
    nlinarith [norm_nonneg (-z * e k)]
  choose θ hθ using fun k => (Complex.norm_eq_one_iff _).mp (hnorm k)
  exact ⟨V, hV, θ, by rw [hUe]; congr 3; funext k; exact (hθ k).symm⟩

end LeanUnitary.LinearAlgebra
