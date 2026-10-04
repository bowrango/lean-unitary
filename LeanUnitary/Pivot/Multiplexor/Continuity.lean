import LeanUnitary.Pivot.Multiplexor.Basic
import LeanUnitary.Pivot.Path.Eigenvalues

/-!
# Continuity of `C(β)` along the pivot path

`submission/decomposition.tex`, Sec. II.C: "choosing `α` with no real `τ_k` keeps `X_g`, `Y_g`
invertible and `C(β)` continuous". This module proves:

* `continuousOn_invSqrt`: `A ↦ A^{-1/2}` is continuous along any continuous family of positive
  definite matrices;
* `continuousOn_multiplexor`: `C(β)` is continuous wherever `X_g` and `Y_g` are invertible;
* `isUnit_det_Xg`, `isUnit_det_Yg`: if `X` is invertible and no `τ_k` is real, `X_g` and `Y_g` are
  invertible for every `β`, since `c + s τ_k` and `c τ_k - s` cannot vanish (`det_Xg_eq_prod`,
  `det_Yg_eq_prod`);
* `continuous_multiplexor`: under that condition `β ↦ C(β)` is continuous on all of `ℝ`.

The continuity of the functional calculus comes from Mathlib's
`ContinuousOn.cfc_of_mem_nhdsSet`, which needs the C⋆-algebra structure on matrices given by the
`L²` operator norm. Its topology is the usual one on matrices. It is installed as a local
instance here and does not leak into other modules.
-/

namespace LeanUnitary.Pivot

open Matrix Complex
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Square complex matrices with the `L²` operator norm form a C⋆-algebra. -/
noncomputable local instance instCStarAlgebraMatrix : CStarAlgebra (Matrix m m ℂ) where
  toNormedRing := Matrix.instL2OpNormedRing
  toStarRing := Matrix.instStarRing
  toCompleteSpace := inferInstance
  toCStarRing := Matrix.instCStarRing
  toNormedAlgebra := Matrix.instL2OpNormedAlgebra
  toStarModule := inferInstance

/-- The spectrum of a positive definite matrix is positive. -/
theorem spectrum_subset_Ioi_of_posDef {A : Matrix m m ℂ} (hA : A.PosDef) :
    spectrum ℝ A ⊆ Set.Ioi 0 := fun x hx => by
  obtain ⟨i, rfl⟩ := (Set.ext_iff.mp hA.isHermitian.spectrum_real_eq_range_eigenvalues x).mp hx
  exact hA.eigenvalues_pos i

/-- `A^{-1/2}` depends continuously on `A` along positive definite matrices. -/
theorem continuousOn_invSqrt {X : Type*} [TopologicalSpace X] {A : X → Matrix m m ℂ}
    {t : Set X} (hA : ContinuousOn A t) (hpos : ∀ x ∈ t, (A x).PosDef) :
    ContinuousOn (fun x => invSqrt (A x)) t := by
  refine ContinuousOn.cfc_of_mem_nhdsSet (s := Set.Ioi (0 : ℝ)) _ ?_ hA
    (fun x hx => (hpos x hx).isHermitian) ?_
  · exact isOpen_Ioi.mem_nhdsSet.mpr
      (Set.iUnion₂_subset fun x hx => spectrum_subset_Ioi_of_posDef (hpos x hx))
  · exact Real.continuous_sqrt.continuousOn.inv₀ fun x hx => (Real.sqrt_pos.mpr hx).ne'

/-- `X Xᴴ` is positive definite for invertible `X`. -/
theorem posDef_mul_conjTranspose_self {X : Matrix m m ℂ} (hX : IsUnit X.det) :
    (X * Xᴴ).PosDef :=
  PosDef.mul_conjTranspose_self X
    (vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det X).mpr hX))

omit [Fintype m] [DecidableEq m] in
theorem continuous_Xg (α : ℝ) (X Y : Matrix m m ℂ) : Continuous fun β => Xg α β X Y := by
  unfold Xg; fun_prop

omit [Fintype m] [DecidableEq m] in
theorem continuous_Yg (α : ℝ) (X Y : Matrix m m ℂ) : Continuous fun β => Yg α β X Y := by
  unfold Yg; fun_prop

/-- `C(β)` is continuous wherever the pivoted blocks are invertible. -/
theorem continuousOn_multiplexor (α : ℝ) (X Y : Matrix m m ℂ) {t : Set ℝ}
    (hXg : ∀ β ∈ t, IsUnit (Xg α β X Y).det) (hYg : ∀ β ∈ t, IsUnit (Yg α β X Y).det) :
    ContinuousOn (fun β => multiplexor α β X Y) t := by
  have hx := continuous_Xg α X Y
  have hy := continuous_Yg α X Y
  have hxx : ContinuousOn (fun β => Xg α β X Y * (Xg α β X Y)ᴴ) t :=
    (hx.mul hx.matrix_conjTranspose).continuousOn
  have hyy : ContinuousOn (fun β => Yg α β X Y * (Yg α β X Y)ᴴ) t :=
    (hy.mul hy.matrix_conjTranspose).continuousOn
  have hix := continuousOn_invSqrt hxx fun β hβ => posDef_mul_conjTranspose_self (hXg β hβ)
  have hiy := continuousOn_invSqrt hyy fun β hβ => posDef_mul_conjTranspose_self (hYg β hβ)
  simp only [multiplexor, zxzC]
  exact continuousOn_const.smul
    (((hx.matrix_conjTranspose.continuousOn.mul hix).mul hiy).mul hy.continuousOn)

/-- For real `c`, `s` with `c² + s² = 1` and nonreal `τ`, neither `c + sτ` nor `cτ - s` is zero. -/
theorem add_mul_ne_zero_and_mul_sub_ne_zero {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) {τ : ℂ}
    (hτ : τ.im ≠ 0) : (c : ℂ) + s * τ ≠ 0 ∧ (c : ℂ) * τ - s ≠ 0 := by
  constructor
  · intro h
    have him : s * τ.im = 0 := by simpa using congrArg Complex.im h
    rcases mul_eq_zero.mp him with hs | h'
    · have hre : c = 0 := by simpa [hs] using congrArg Complex.re h
      rw [hs, hre] at hcs; norm_num at hcs
    · exact hτ h'
  · intro h
    have him : c * τ.im = 0 := by simpa using congrArg Complex.im h
    rcases mul_eq_zero.mp him with hc | h'
    · have hre : s = 0 := by simpa [hc] using congrArg Complex.re h
      rw [hc, hre] at hcs; norm_num at hcs
    · exact hτ h'

private theorem prod_ne_zero_of_forall {s : Multiset ℂ} {f : ℂ → ℂ} (h : ∀ τ ∈ s, f τ ≠ 0) :
    (s.map f).prod ≠ 0 :=
  Multiset.prod_ne_zero fun h0 => by
    obtain ⟨τ, hτ, hfτ⟩ := Multiset.mem_map.mp h0
    exact h τ hτ hfτ

/-- With no real `τ_k`, `X_g` is invertible for every `β`. -/
theorem isUnit_det_Xg (α β : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det) (Y : Matrix m m ℂ)
    (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0) : IsUnit (Xg α β X Y).det := by
  have hp : star (ph α) ≠ 0 := left_ne_zero_of_mul_eq_one (star_ph_mul_ph α)
  rw [det_Xg_eq_prod α β hX, isUnit_iff_ne_zero]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hp) hX.ne_zero) (prod_ne_zero_of_forall ?_)
  exact fun τ hτ' => (add_mul_ne_zero_and_mul_sub_ne_zero (Real.cos_sq_add_sin_sq _) (hτ τ hτ')).1

/-- With no real `τ_k`, `Y_g` is invertible for every `β`. -/
theorem isUnit_det_Yg (α β : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det) (Y : Matrix m m ℂ)
    (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0) : IsUnit (Yg α β X Y).det := by
  have hp : star (ph α) ≠ 0 := left_ne_zero_of_mul_eq_one (star_ph_mul_ph α)
  rw [det_Yg_eq_prod α β hX, isUnit_iff_ne_zero]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hp) hX.ne_zero) (prod_ne_zero_of_forall ?_)
  exact fun τ hτ' => (add_mul_ne_zero_and_mul_sub_ne_zero (Real.cos_sq_add_sin_sq _) (hτ τ hτ')).2

/-- `C(β)` is continuous in `β` when `X` is invertible and no `τ_k` is real. -/
theorem continuous_multiplexor (α : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det)
    (Y : Matrix m m ℂ) (hτ : ∀ τ ∈ taus α X Y, τ.im ≠ 0) :
    Continuous fun β => multiplexor α β X Y :=
  continuousOn_univ.mp (continuousOn_multiplexor α X Y
    (fun β _ => isUnit_det_Xg α β hX Y hτ) (fun β _ => isUnit_det_Yg α β hX Y hτ))

end LeanUnitary.Pivot
