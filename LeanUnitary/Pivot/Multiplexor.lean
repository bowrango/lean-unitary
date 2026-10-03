import LeanUnitary.Pivot.Path

/-!
# The pivoted multiplexor `C(β)`

`submission/decomposition.tex`, Eqs. 10–11. The Block-ZXZ factorization (arXiv:2403.13692,
Sec. 4.1) gives the left-side multiplexor matrix of `U (g ⊗ I)` as

    C(β) = -i X_gᴴ (X_g X_gᴴ)^{-1/2} (Y_g Y_gᴴ)^{-1/2} Y_g,

with the inverse square roots taken by the continuous functional calculus. This module defines
`C(β)` and proves:

* `multiplexor_pi`: the endpoint symmetry `C(π) = C(0)ᴴ`, for any blocks `X`, `Y`;
* `multiplexor_mem_unitaryGroup`: `C(β)` is unitary wherever `X_g` and `Y_g` are invertible,
  because `(X Xᴴ)^{-1/2} X` is unitary for invertible `X` (`invSqrt_mul_mem_unitaryGroup`);
* `multiplexor_pi_eq_inv`: Eq. 11, `C(π) = C(0)⁻¹`, for invertible `X` and `Y`.

Unitarity needs no hypothesis on `U` beyond invertible blocks.
-/

namespace LeanUnitary.Pivot

open Matrix Complex
open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `A^{-1/2}` by the continuous functional calculus (positive definite on the inputs used). -/
noncomputable def invSqrt (A : Matrix m m ℂ) : Matrix m m ℂ := cfc (fun x => (Real.sqrt x)⁻¹) A

theorem star_invSqrt (A : Matrix m m ℂ) : star (invSqrt A) = invSqrt A :=
  (IsSelfAdjoint.cfc (f := fun x => (Real.sqrt x)⁻¹) (a := A)).star_eq

theorem conjTranspose_invSqrt (A : Matrix m m ℂ) : (invSqrt A)ᴴ = invSqrt A :=
  star_invSqrt A

/-- The Block-ZXZ multiplexor matrix `-i Xᴴ (X Xᴴ)^{-1/2} (Y Yᴴ)^{-1/2} Y` of a block row. -/
noncomputable def zxzC (X Y : Matrix m m ℂ) : Matrix m m ℂ :=
  (-I) • (Xᴴ * invSqrt (X * Xᴴ) * invSqrt (Y * Yᴴ) * Y)

/-- `C(β)` for the pivot `g = R_z(α) R_y(β)` (Eq. 10). -/
noncomputable def multiplexor (α β : ℝ) (X Y : Matrix m m ℂ) : Matrix m m ℂ :=
  zxzC (Xg α β X Y) (Yg α β X Y)

omit [Fintype m] [DecidableEq m] in
/-- A unit phase drops out of `A Aᴴ`. -/
theorem smul_mul_conjTranspose_smul [Fintype m] {a : ℂ} (ha : a * star a = 1)
    (A : Matrix m m ℂ) : (a • A) * (a • A)ᴴ = A * Aᴴ := by
  rw [conjTranspose_smul, smul_mul_smul, ha, one_smul]

/-- Eq. 11, `C(π) = C(0)ᴴ`: the pivot path runs from `C(0)` to its adjoint. -/
theorem multiplexor_pi (α : ℝ) (X Y : Matrix m m ℂ) :
    multiplexor α Real.pi X Y = (multiplexor α 0 X Y)ᴴ := by
  have hp := ph_mul_star_ph α
  have hp' : star (ph α) * star (star (ph α)) = 1 := by rw [star_star]; exact star_ph_mul_ph α
  rw [multiplexor, multiplexor, Xg_pi, Yg_pi, Xg_zero, Yg_zero, zxzC, zxzC]
  have h1 := smul_mul_conjTranspose_smul hp Y
  have h2 := smul_mul_conjTranspose_smul hp' X
  have h3 : (-(star (ph α) • X)) * (-(star (ph α) • X))ᴴ = X * Xᴴ := by
    rw [conjTranspose_neg, neg_mul_neg, h2]
  rw [h1, h2, h3]
  simp only [conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_invSqrt, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, smul_smul, smul_neg,
    Matrix.mul_assoc]
  match_scalars
  simp only [star_mul', star_neg, Complex.star_def, Complex.conj_I]
  simp only [← Complex.star_def, star_star]
  ring

/-! ## Unitarity -/

/-- `A^{-1/2} A A^{-1/2} = 1` for positive definite `A`. -/
theorem invSqrt_mul_self_mul_invSqrt {A : Matrix m m ℂ} (hA : A.PosDef) :
    invSqrt A * A * invSqrt A = 1 := by
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) :=
    fun f => A.finite_real_spectrum.continuousOn f
  have hpos : ∀ x ∈ spectrum ℝ A, 0 < x := by
    intro x hx
    obtain ⟨i, rfl⟩ := (Set.ext_iff.mp hA.isHermitian.spectrum_real_eq_range_eigenvalues x).mp hx
    exact hA.eigenvalues_pos i
  calc invSqrt A * A * invSqrt A
      = cfc (fun x => (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹) A := by
        rw [cfc_mul _ _ A (hc _) (hc _), cfc_mul _ _ A (hc _) (hc _), cfc_id' ℝ A hsa, invSqrt]
    _ = cfc (fun _ => (1 : ℝ)) A := cfc_congr fun x hx => by
        have hx := hpos x hx
        have hs := Real.sqrt_pos.mpr hx
        field_simp
        rw [Real.sq_sqrt hx.le]
    _ = 1 := cfc_const_one ℝ A

/-- The polar factor `(X Xᴴ)^{-1/2} X` of an invertible `X` is unitary. -/
theorem invSqrt_mul_mem_unitaryGroup {X : Matrix m m ℂ} (hX : IsUnit X.det) :
    invSqrt (X * Xᴴ) * X ∈ unitaryGroup m ℂ := by
  have hpd : (X * Xᴴ).PosDef := PosDef.mul_conjTranspose_self X
    (vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det X).mpr hX))
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_invSqrt]
  simpa only [Matrix.mul_assoc] using invSqrt_mul_self_mul_invSqrt hpd

/-- The Block-ZXZ multiplexor matrix of invertible blocks is unitary: it is `-i` times the
product of the adjoint of one polar factor and another polar factor. -/
theorem zxzC_mem_unitaryGroup {X Y : Matrix m m ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det) :
    zxzC X Y ∈ unitaryGroup m ℂ := by
  have hW : (invSqrt (X * Xᴴ) * X)ᴴ * (invSqrt (Y * Yᴴ) * Y) ∈ unitaryGroup m ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem (invSqrt_mul_mem_unitaryGroup hX))
      (invSqrt_mul_mem_unitaryGroup hY)
  have heq : zxzC X Y = (-I) • ((invSqrt (X * Xᴴ) * X)ᴴ * (invSqrt (Y * Yᴴ) * Y)) := by
    rw [zxzC, conjTranspose_mul, conjTranspose_invSqrt]
    simp only [Matrix.mul_assoc]
  rw [heq, mem_unitaryGroup_iff, star_smul, smul_mul_smul, (mem_unitaryGroup_iff.mp hW)]
  simp [Complex.conj_I]

/-- `C(β)` is unitary wherever the pivoted blocks are invertible. -/
theorem multiplexor_mem_unitaryGroup (α β : ℝ) {X Y : Matrix m m ℂ}
    (hX : IsUnit (Xg α β X Y).det) (hY : IsUnit (Yg α β X Y).det) :
    multiplexor α β X Y ∈ unitaryGroup m ℂ :=
  zxzC_mem_unitaryGroup hX hY

/-- A unit phase does not change invertibility. -/
theorem isUnit_det_smul_ph {a : ℂ} (ha : a * star a = 1) {X : Matrix m m ℂ} (hX : IsUnit X.det) :
    IsUnit (a • X).det := by
  rw [det_smul]
  exact (IsUnit.pow _ (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one ha))).mul hX

/-- Eq. 11, `C(π) = C(0)⁻¹`, for invertible `X` and `Y`. -/
theorem multiplexor_pi_eq_inv (α : ℝ) {X Y : Matrix m m ℂ} (hX : IsUnit X.det)
    (hY : IsUnit Y.det) :
    multiplexor α Real.pi X Y = (multiplexor α 0 X Y)⁻¹ := by
  have hp' : star (ph α) * star (star (ph α)) = 1 := by rw [star_star]; exact star_ph_mul_ph α
  have hU := multiplexor_mem_unitaryGroup α 0 (X := X) (Y := Y)
    (by rw [Xg_zero]; exact isUnit_det_smul_ph hp' hX)
    (by rw [Yg_zero]; exact isUnit_det_smul_ph (ph_mul_star_ph α) hY)
  rw [multiplexor_pi, (inv_eq_left_inv (mem_unitaryGroup_iff'.mp hU)), star_eq_conjTranspose]

end LeanUnitary.Pivot
