import LeanUnitary.Spec

/-!
# The pivot path

Linear-algebra primitives of the pivot-gate decomposition (`submission/decomposition.tex`,
Sec. II.C). The pivot is `g = R_z(α) R_y(β)`. Write `U = [X Y; * *]` in `D × D` blocks, with
`c = cos(β/2)` and `s = sin(β/2)`. Then `U (g ⊗ I)` has the top-row blocks (Eq. 9)

    X_g = e^{-iα/2} c X + e^{iα/2} s Y,      Y_g = -e^{-iα/2} s X + e^{iα/2} c Y.

This module proves, for arbitrary blocks:

* `gate_mem_unitaryGroup`: `g` is unitary;
* `fromBlocks_mul_lift`: Eq. 9 is the top row of `U (g ⊗ I)`;
* `Xg_zero`, `Yg_zero`, `Xg_pi`, `Yg_pi`: at the endpoints the blocks swap with a sign change;
* `rowGram_Xg_Yg`: `X_g X_gᴴ + Y_g Y_gᴴ = X Xᴴ + Y Yᴴ`, so the top block row stays orthonormal;
* `Xg_eq_mul`, `Yg_eq_mul`, `det_Yg_mul_det_eq`: the factorization through `M = e^{iα} X⁻¹ Y`
  behind Eq. 12, `det Y_g / det X_g = det (c M - s) / det (c + s M)`;
* `det_smul_add_smul_one`: `det (a M + b) = ∏ (a τ_k + b)` over the eigenvalues of `M`;
* `det_Yg_div_det_Xg`: Eq. 12, `det Y_g / det X_g = ∏_k τ_k (c - s/τ_k) / (c + s τ_k)`, with
  `det_Xg_eq_prod` showing `X_g` is invertible iff no factor `c + s τ_k` vanishes.

The top qubit is the first summand of `m ⊕ m`, as in `LeanUnitary.Blocks`, so `g ⊗ I` is
`lift g = [g₀₀ I, g₀₁ I; g₁₀ I, g₁₁ I]`.
-/

namespace LeanUnitary.Pivot

open Matrix LeanUnitary.Spec Complex

/-- The phase `e^{iα/2}`. -/
noncomputable def ph (α : ℝ) : ℂ := exp (((α / 2 : ℝ) : ℂ) * I)

theorem star_ph (α : ℝ) : star (ph α) = exp (-((α / 2 : ℝ) : ℂ) * I) := by
  rw [ph, Complex.star_def, ← exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

theorem star_ph_mul_ph (α : ℝ) : star (ph α) * ph α = 1 := by
  rw [star_ph, ph, ← exp_add]
  simp

theorem ph_mul_star_ph (α : ℝ) : ph α * star (ph α) = 1 := by
  rw [mul_comm, star_ph_mul_ph]

/-- The pivot gate `g = R_z(α) R_y(β)`. -/
noncomputable def gate (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := Rz α * Ry β

theorem gate_eq (α β : ℝ) :
    gate α β =
      !![star (ph α) * (Real.cos (β / 2) : ℂ), -(star (ph α) * (Real.sin (β / 2) : ℂ));
         ph α * (Real.sin (β / 2) : ℂ), ph α * (Real.cos (β / 2) : ℂ)] := by
  rw [gate, Rz, Ry, star_ph, ph]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

set_option linter.flexible false in
/-- A rotation `[p c, -p s; q s, q c]` with unit phases `p`, `q` and `c² + s² = 1` is unitary. -/
theorem mem_unitaryGroup_of_phases {p q : ℂ} {c s : ℝ} (hp : p * star p = 1) (hq : q * star q = 1)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    !![p * (c : ℂ), -(p * (s : ℂ)); q * (s : ℂ), q * (c : ℂ)] ∈ unitaryGroup (Fin 2) ℂ := by
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  rw [mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose] <;>
    simp only [← Complex.star_def] <;>
    first
    | ring1
    | linear_combination ((c : ℂ) ^ 2 + (s : ℂ) ^ 2) * hp + hcs'
    | linear_combination ((c : ℂ) ^ 2 + (s : ℂ) ^ 2) * hq + hcs'

theorem gate_mem_unitaryGroup (α β : ℝ) : gate α β ∈ unitaryGroup (Fin 2) ℂ := by
  rw [gate_eq]
  exact mem_unitaryGroup_of_phases (by rw [star_star]; exact star_ph_mul_ph α)
    (ph_mul_star_ph α) (Real.cos_sq_add_sin_sq _)

/-! ## The pivoted blocks -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `g ⊗ I`: a single-qubit gate on the top qubit of a register split as `m ⊕ m`. -/
def lift (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  fromBlocks (g 0 0 • 1) (g 0 1 • 1) (g 1 0 • 1) (g 1 1 • 1)

/-- The pivoted left block `X_g = e^{-iα/2} c X + e^{iα/2} s Y` (Eq. 9). -/
noncomputable def Xg (α β : ℝ) (X Y : Matrix m m ℂ) : Matrix m m ℂ :=
  (star (ph α) * (Real.cos (β / 2) : ℂ)) • X + (ph α * (Real.sin (β / 2) : ℂ)) • Y

/-- The pivoted right block `Y_g = -e^{-iα/2} s X + e^{iα/2} c Y` (Eq. 9). -/
noncomputable def Yg (α β : ℝ) (X Y : Matrix m m ℂ) : Matrix m m ℂ :=
  (-(star (ph α) * (Real.sin (β / 2) : ℂ))) • X + (ph α * (Real.cos (β / 2) : ℂ)) • Y

/-- Eq. 9: right-multiplying by `g ⊗ I` replaces each block row `(X, Y)` by `(X_g, Y_g)`. -/
theorem fromBlocks_mul_lift (α β : ℝ) (X Y Z W : Matrix m m ℂ) :
    fromBlocks X Y Z W * lift (gate α β) =
      fromBlocks (Xg α β X Y) (Yg α β X Y) (Xg α β Z W) (Yg α β Z W) := by
  rw [lift, gate_eq, fromBlocks_multiply]
  simp [Xg, Yg, add_comm]

omit [Fintype m] [DecidableEq m] in
theorem Xg_zero (α : ℝ) (X Y : Matrix m m ℂ) : Xg α 0 X Y = star (ph α) • X := by
  simp [Xg]

omit [Fintype m] [DecidableEq m] in
theorem Yg_zero (α : ℝ) (X Y : Matrix m m ℂ) : Yg α 0 X Y = ph α • Y := by
  simp [Yg]

omit [Fintype m] [DecidableEq m] in
theorem Xg_pi (α : ℝ) (X Y : Matrix m m ℂ) : Xg α Real.pi X Y = ph α • Y := by
  simp [Xg, Real.cos_pi_div_two, Real.sin_pi_div_two]

omit [Fintype m] [DecidableEq m] in
theorem Yg_pi (α : ℝ) (X Y : Matrix m m ℂ) : Yg α Real.pi X Y = -(star (ph α) • X) := by
  simp [Yg, Real.cos_pi_div_two, Real.sin_pi_div_two]

omit [DecidableEq m] in
/-- The pivot preserves the Gram matrix of the top block row. In particular, if `U` is unitary
then `X_g X_gᴴ + Y_g Y_gᴴ = 1` for every `α`, `β`. -/
theorem rowGram_Xg_Yg (α β : ℝ) (X Y : Matrix m m ℂ) :
    Xg α β X Y * (Xg α β X Y)ᴴ + Yg α β X Y * (Yg α β X Y)ᴴ = X * Xᴴ + Y * Yᴴ := by
  have hp := ph_mul_star_ph α
  have hcs := Real.cos_sq_add_sin_sq (β / 2)
  simp only [Xg, Yg]
  generalize Real.cos (β / 2) = c at *
  generalize Real.sin (β / 2) = s at *
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, smul_mul_smul]
  match_scalars <;>
    simp only [star_mul', star_neg, Complex.star_def, Complex.conj_ofReal] <;>
    simp only [← Complex.star_def, star_star] <;>
    first
    | ring1
    | linear_combination ((c : ℂ) ^ 2 + (s : ℂ) ^ 2) * hp + hcs'

/-! ## Factorization through `M = e^{iα} X⁻¹ Y` (Eq. 12) -/

/-- `M = e^{iα} X⁻¹ Y`, whose eigenvalues are the `τ_k` of Eq. 12. -/
noncomputable def pivotM (α : ℝ) (X Y : Matrix m m ℂ) : Matrix m m ℂ := (ph α ^ 2) • (X⁻¹ * Y)

theorem Xg_eq_mul (α β : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det) (Y : Matrix m m ℂ) :
    Xg α β X Y = star (ph α) • (X *
      ((Real.cos (β / 2) : ℂ) • 1 + (Real.sin (β / 2) : ℂ) • pivotM α X Y)) := by
  have hp' := star_ph_mul_ph α
  rw [pivotM, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.one_mul, Matrix.mul_one, Xg]
  rw [smul_add, smul_smul, smul_smul, smul_smul]
  congr 2
  linear_combination (-(ph α * (Real.sin (β / 2) : ℂ))) * hp'

theorem Yg_eq_mul (α β : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det) (Y : Matrix m m ℂ) :
    Yg α β X Y = star (ph α) • (X *
      ((Real.cos (β / 2) : ℂ) • pivotM α X Y - (Real.sin (β / 2) : ℂ) • 1)) := by
  have hp' := star_ph_mul_ph α
  rw [pivotM, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.one_mul, Matrix.mul_one, Yg]
  rw [smul_sub, smul_smul, smul_smul, smul_smul, sub_eq_add_neg, add_comm, ← neg_smul]
  congr 2
  linear_combination (-(ph α * (Real.cos (β / 2) : ℂ))) * hp'

/-- Eq. 12 in matrix form: `det Y_g / det X_g = det (c M - s) / det (c + s M)`, written without
division. -/
theorem det_Yg_mul_det_eq (α β : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det) (Y : Matrix m m ℂ) :
    (Yg α β X Y).det *
        ((Real.cos (β / 2) : ℂ) • (1 : Matrix m m ℂ) + (Real.sin (β / 2) : ℂ) • pivotM α X Y).det =
      (Xg α β X Y).det *
        ((Real.cos (β / 2) : ℂ) • pivotM α X Y -
          (Real.sin (β / 2) : ℂ) • (1 : Matrix m m ℂ)).det := by
  rw [Xg_eq_mul α β hX, Yg_eq_mul α β hX, det_smul, det_smul, det_mul, det_mul]
  ring

/-! ## Eq. 12 in terms of eigenvalues -/

/-- `det (a M + b) = ∏_k (a τ_k + b)` over the eigenvalues `τ_k` of `M`, counted with
multiplicity as roots of the characteristic polynomial. -/
theorem det_smul_add_smul_one (M : Matrix m m ℂ) (a b : ℂ) :
    (a • M + b • (1 : Matrix m m ℂ)).det = (M.charpoly.roots.map fun τ => a * τ + b).prod := by
  have hsplit := IsAlgClosed.splits M.charpoly
  have hcard : M.charpoly.roots.card = Fintype.card m := by
    rw [Polynomial.splits_iff_card_roots.mp hsplit, charpoly_natDegree_eq_dim]
  by_cases ha : a = 0
  · subst ha
    simp [hcard]
  · have hM : a • M + b • (1 : Matrix m m ℂ) = (-a) • (Matrix.scalar m (-b / a) - M) := by
      ext i j
      rcases eq_or_ne i j with rfl | h
      · simp
        field_simp
        ring
      · simp [h]
    have heval := hsplit.eval_eq_prod_roots (-b / a)
    rw [M.charpoly_monic.leadingCoeff, one_mul, eval_charpoly] at heval
    have hconst : (-a) ^ Fintype.card m = (M.charpoly.roots.map fun _ => -a).prod := by
      rw [Multiset.map_const', Multiset.prod_replicate, hcard]
    rw [hM, det_smul, heval, hconst, ← Multiset.prod_map_mul]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun τ _ => ?_)
    field_simp
    ring

/-- The eigenvalues `τ_k` of `M = e^{iα} X⁻¹ Y`, with multiplicity. -/
noncomputable def taus (α : ℝ) (X Y : Matrix m m ℂ) : Multiset ℂ := (pivotM α X Y).charpoly.roots

/-- Eq. 12 without division: `det Y_g ∏ (c + s τ_k) = det X_g ∏ (c τ_k - s)`. -/
theorem det_Yg_mul_prod_eq (α β : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det) (Y : Matrix m m ℂ) :
    (Yg α β X Y).det *
        ((taus α X Y).map fun τ => (Real.cos (β / 2) : ℂ) + (Real.sin (β / 2) : ℂ) * τ).prod =
      (Xg α β X Y).det *
        ((taus α X Y).map fun τ => (Real.cos (β / 2) : ℂ) * τ - (Real.sin (β / 2) : ℂ)).prod := by
  have h := det_Yg_mul_det_eq α β hX Y
  rw [add_comm, det_smul_add_smul_one, sub_eq_add_neg, ← neg_smul, det_smul_add_smul_one] at h
  simpa [taus, add_comm, sub_eq_add_neg, mul_comm] using h

/-- `det X_g = e^{-iα D/2} det X ∏ (c + s τ_k)`, so `X_g` is invertible iff `X` is and no
factor `c + s τ_k` vanishes. -/
theorem det_Xg_eq_prod (α β : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det) (Y : Matrix m m ℂ) :
    (Xg α β X Y).det = star (ph α) ^ Fintype.card m * X.det *
      ((taus α X Y).map fun τ => (Real.cos (β / 2) : ℂ) + (Real.sin (β / 2) : ℂ) * τ).prod := by
  rw [Xg_eq_mul α β hX, det_smul, det_mul, add_comm, det_smul_add_smul_one, taus, mul_assoc]
  simp only [add_comm]

/-- No `τ_k` vanishes when `Y` is invertible. -/
theorem ne_zero_of_mem_taus (α : ℝ) {X Y : Matrix m m ℂ} (hX : IsUnit X.det)
    (hY : IsUnit Y.det) {τ : ℂ} (hτ : τ ∈ taus α X Y) : τ ≠ 0 := by
  rintro rfl
  have hroot := (Polynomial.mem_roots (pivotM α X Y).charpoly_monic.ne_zero).mp hτ
  rw [← mem_spectrum_iff_isRoot_charpoly, spectrum.zero_mem_iff, isUnit_iff_isUnit_det] at hroot
  apply hroot
  have hp : ph α ≠ 0 := right_ne_zero_of_mul_eq_one (star_ph_mul_ph α)
  rw [pivotM, det_smul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', isUnit_iff_ne_zero]
  simp [hp, hX.ne_zero, hY.ne_zero]

/-- Eq. 12: `det Y_g / det X_g = ∏_k τ_k (c - s/τ_k) / (c + s τ_k)`, for invertible `X`, `Y` and
invertible `X_g`. -/
theorem det_Yg_div_det_Xg (α β : ℝ) {X Y : Matrix m m ℂ} (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hXg : (Xg α β X Y).det ≠ 0) :
    (Yg α β X Y).det / (Xg α β X Y).det =
      ((taus α X Y).map fun τ => τ * (((Real.cos (β / 2) : ℂ) - (Real.sin (β / 2) : ℂ) / τ) /
        ((Real.cos (β / 2) : ℂ) + (Real.sin (β / 2) : ℂ) * τ))).prod := by
  set c : ℂ := (Real.cos (β / 2) : ℂ)
  set s : ℂ := (Real.sin (β / 2) : ℂ)
  have hden : ((taus α X Y).map fun τ => c + s * τ).prod ≠ 0 := by
    intro h0
    exact hXg (by rw [det_Xg_eq_prod α β hX]; simp only [c, s] at h0 ⊢; rw [h0, mul_zero])
  have h := det_Yg_mul_prod_eq α β hX Y
  have hq : (Yg α β X Y).det / (Xg α β X Y).det =
      ((taus α X Y).map fun τ => c * τ - s).prod / ((taus α X Y).map fun τ => c + s * τ).prod := by
    rw [div_eq_div_iff hXg hden]
    simpa only [c, s, mul_comm] using h
  rw [hq, ← Multiset.prod_map_div]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun τ hτ => ?_)
  have := ne_zero_of_mem_taus α hX hY hτ
  field_simp

end LeanUnitary.Pivot
