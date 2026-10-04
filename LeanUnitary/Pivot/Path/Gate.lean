import LeanUnitary.Spec

/-!
# The pivot gate and the pivoted blocks

`submission/decomposition.tex`, Sec. II.C. The pivot is `g = R_z(α) R_y(β)`. Write
`U = [X Y; * *]` in `D × D` blocks, with `c = cos(β/2)` and `s = sin(β/2)`. Then `U (g ⊗ I)`
has the top-row blocks (Eq. 9)

    X_g = e^{-iα/2} c X + e^{iα/2} s Y,      Y_g = -e^{-iα/2} s X + e^{iα/2} c Y.

* `gate_mem_unitaryGroup`: `g` is unitary;
* `fromBlocks_mul_lift`: Eq. 9 is the top row of `U (g ⊗ I)`;
* `Xg_zero`, `Yg_zero`, `Xg_pi`, `Yg_pi`: at the endpoints the blocks swap with a sign change;
* `Xg_eq_mul`, `Yg_eq_mul`: the factorization through `M = e^{iα} X⁻¹ Y` behind Eq. 12.

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

/-! ## Factorization through `M = e^{iα} X⁻¹ Y` -/

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

end LeanUnitary.Pivot
