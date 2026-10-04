import LeanUnitary.Pivot.Path.Gate

/-!
# Eigenvalues and the determinants of the pivoted blocks

`submission/decomposition.tex`, Eq. 12. The eigenvalues `τ_k` of `M = e^{iα} X⁻¹ Y`, taken as
roots of the characteristic polynomial with multiplicity, control the determinants of the
pivoted blocks:

* `det_smul_add_smul_one`: `det (a M + b) = ∏_k (a τ_k + b)`;
* `roots_charpoly_inv`, `roots_charpoly_smul`: the eigenvalues of `A⁻¹` and `c • A` are the
  inverses and the `c`-multiples of those of `A`;
* `norm_eq_one_of_mem_roots_charpoly`: the eigenvalues of a unitary have modulus one;
* `taus_eq_map`: the pivot rotates the eigenvalues, `τ_k(α) = e^{iα} τ_k(0)`;
* `det_Xg_eq_prod`, `det_Yg_eq_prod` (Eq. 12): `det X_g = e^{-iαD/2} det X ∏ (c + s τ_k)` and
  `det Y_g = e^{-iαD/2} det X ∏ (c τ_k - s)`;
* `ne_zero_of_mem_taus`: no `τ_k` vanishes when `Y` is invertible.

Listing multisets as tuples: `exists_list_of_card`, `exists_perm_of_map_eq`,
`multiset_eq_of_prod_sub_eq`, `card_roots_charpoly`.
-/

namespace LeanUnitary.Pivot

open Matrix Complex Finset
open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

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

/-- Monic polynomials `∏ (X - a)` agreeing at every point have the same roots. -/
theorem multiset_eq_of_prod_sub_eq {s t : Multiset ℂ}
    (h : ∀ x : ℂ, (s.map fun a => x - a).prod = (t.map fun a => x - a).prod) : s = t := by
  have hp : (s.map fun a => Polynomial.X - Polynomial.C a).prod =
      (t.map fun a => Polynomial.X - Polynomial.C a).prod := by
    apply Polynomial.funext
    intro x
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def] using h x
  rw [← Polynomial.roots_multiset_prod_X_sub_C s, hp, Polynomial.roots_multiset_prod_X_sub_C]

/-- The eigenvalues of `A⁻¹` are the inverses of the eigenvalues of `A`, with multiplicity. -/
theorem roots_charpoly_inv {A : Matrix m m ℂ} (hA : IsUnit A.det) :
    (A⁻¹).charpoly.roots = A.charpoly.roots.map (·⁻¹) := by
  have hdet : A.det = A.charpoly.roots.prod := det_eq_prod_roots_charpoly A
  have hne : ∀ τ ∈ A.charpoly.roots, τ ≠ 0 := fun τ hτ h0 =>
    hA.ne_zero (hdet ▸ Multiset.prod_eq_zero (h0 ▸ hτ))
  apply multiset_eq_of_prod_sub_eq
  intro x
  -- `det (x - A⁻¹) = det A⁻¹ · det (x A - 1)`
  have h1 := det_smul_add_smul_one (A⁻¹) (-1) x
  have h2 := det_smul_add_smul_one A x (-1)
  have hmat : (-1 : ℂ) • A⁻¹ + x • (1 : Matrix m m ℂ) = A⁻¹ * (x • A + (-1 : ℂ) • 1) := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA,
      Matrix.mul_one, add_comm]
  rw [hmat, det_mul, h2, det_nonsing_inv, Ring.inverse_eq_inv'] at h1
  have hprod : (A.charpoly.roots.map fun τ => x * τ + -1).prod =
      A.charpoly.roots.prod * (A.charpoly.roots.map fun τ => x - τ⁻¹).prod := by
    have hid : A.charpoly.roots.prod = (A.charpoly.roots.map fun τ => τ).prod := by
      rw [Multiset.map_id']
    rw [hid, ← Multiset.prod_map_mul]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun τ hτ => ?_)
    field_simp [hne τ hτ]
    ring
  rw [Multiset.map_map]
  simp only [Function.comp_def]
  rw [show (A⁻¹.charpoly.roots.map fun τ => x - τ) =
      A⁻¹.charpoly.roots.map fun τ => -1 * τ + x from Multiset.map_congr rfl fun τ _ => by ring,
    ← h1, hprod, ← hdet, ← mul_assoc, inv_mul_cancel₀ hA.ne_zero, one_mul]

/-- The eigenvalues of `c • A` are `c` times those of `A`, with multiplicity. -/
theorem roots_charpoly_smul (A : Matrix m m ℂ) (c : ℂ) :
    (c • A).charpoly.roots = A.charpoly.roots.map (c * ·) := by
  apply multiset_eq_of_prod_sub_eq
  intro x
  have h1 := det_smul_add_smul_one (c • A) (-1) x
  have h2 := det_smul_add_smul_one A (-c) x
  rw [smul_smul, show (-1 : ℂ) * c = -c by ring, h2] at h1
  rw [Multiset.map_map]
  simp only [Function.comp_def]
  rw [show (((c • A).charpoly.roots.map fun τ => x - τ)) =
      (c • A).charpoly.roots.map fun τ => -1 * τ + x from Multiset.map_congr rfl fun τ _ => by ring,
    ← h1]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun τ _ => by ring)

/-- The roots of the characteristic polynomial, counted with multiplicity, number `card m`. -/
theorem card_roots_charpoly (A : Matrix m m ℂ) : A.charpoly.roots.card = Fintype.card m := by
  rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), charpoly_natDegree_eq_dim]

/-- The eigenvalues of a unitary matrix have modulus one. -/
theorem norm_eq_one_of_mem_roots_charpoly {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ)
    {τ : ℂ} (hτ : τ ∈ U.charpoly.roots) : ‖τ‖ = 1 := by
  have hroot := (Polynomial.mem_roots U.charpoly_monic.ne_zero).mp hτ
  rw [Polynomial.IsRoot, eval_charpoly] at hroot
  obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr hroot
  have hUx : U *ᵥ x = τ • x := by
    rw [sub_mulVec, sub_eq_zero, scalar_apply] at hx
    rw [← hx]; ext i; simp [mulVec_diagonal]
  have hiso : star (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = star x ⬝ᵥ x := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff'.mp hU, one_mulVec]
  rw [hUx, star_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul] at hiso
  have hne : star x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_star_self_eq_zero.mp h)
  have h1 : star τ * τ = 1 := by
    have := mul_right_cancel₀ hne (hiso.trans (one_mul _).symm)
    exact this
  have h2 : (‖τ‖ : ℂ) ^ 2 = 1 := by
    rw [← Complex.mul_conj', mul_comm, ← Complex.star_def, h1]
  have h3 : ‖τ‖ ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg τ]

/-- A multiset of size `D` is listed by some `u : Fin D → α`. -/
theorem exists_list_of_card {α : Type*} {D : ℕ} (s : Multiset α) (hs : s.card = D) :
    ∃ u : Fin D → α, (univ : Finset (Fin D)).val.map u = s := by
  obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, Multiset.coe_toList s⟩
  simp only [Multiset.coe_card] at hs
  subst hs
  exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]⟩

/-- Two lists with the same multiset of values differ by a permutation. -/
theorem exists_perm_of_map_eq {D : ℕ} {β : Type*} {f g : Fin D → β}
    (h : (univ : Finset (Fin D)).val.map f = (univ : Finset (Fin D)).val.map g) :
    ∃ σ : Equiv.Perm (Fin D), ∀ k, g (σ k) = f k := by
  classical
  have hcard : ∀ c, Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := fun c => by
    have := congrArg (Multiset.count c) h
    simp only [Multiset.count_map, Fintype.card_subtype] at this ⊢
    simp_rw [eq_comm (a := c)] at this
    simpa only [Finset.card_def, Finset.filter_val] using this
  let e : ∀ c, {a // f a = c} ≃ {b // g b = c} := fun c => Fintype.equivOfCardEq (hcard c)
  exact ⟨Equiv.ofFiberEquiv e, fun k => Equiv.ofFiberEquiv_map e k⟩

/-! ## The eigenvalues `τ_k` -/

/-- The eigenvalues `τ_k` of `M = e^{iα} X⁻¹ Y`, with multiplicity. -/
noncomputable def taus (α : ℝ) (X Y : Matrix m m ℂ) : Multiset ℂ := (pivotM α X Y).charpoly.roots

/-- The pivot rotates the eigenvalues: `τ_k(α) = e^{iα} τ_k(0)`, where `τ_k(0)` are the
eigenvalues of `X⁻¹ Y`. -/
theorem taus_eq_map (α : ℝ) (X Y : Matrix m m ℂ) :
    taus α X Y = (X⁻¹ * Y).charpoly.roots.map (exp (α * I) * ·) := by
  rw [taus, pivotM, roots_charpoly_smul]
  congr 2
  rw [ph, ← exp_nat_mul]
  push_cast
  ring_nf

/-- `det X_g = e^{-iα D/2} det X ∏ (c + s τ_k)`, so `X_g` is invertible iff `X` is and no
factor `c + s τ_k` vanishes. -/
theorem det_Xg_eq_prod (α β : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det) (Y : Matrix m m ℂ) :
    (Xg α β X Y).det = star (ph α) ^ Fintype.card m * X.det *
      ((taus α X Y).map fun τ => (Real.cos (β / 2) : ℂ) + (Real.sin (β / 2) : ℂ) * τ).prod := by
  rw [Xg_eq_mul α β hX, det_smul, det_mul, add_comm, det_smul_add_smul_one, taus, mul_assoc]
  simp only [add_comm]

/-- `det Y_g = e^{-iα D/2} det X ∏ (c τ_k - s)`. -/
theorem det_Yg_eq_prod (α β : ℝ) {X : Matrix m m ℂ} (hX : IsUnit X.det) (Y : Matrix m m ℂ) :
    (Yg α β X Y).det = star (ph α) ^ Fintype.card m * X.det *
      ((taus α X Y).map fun τ => (Real.cos (β / 2) : ℂ) * τ - (Real.sin (β / 2) : ℂ)).prod := by
  rw [Yg_eq_mul α β hX, det_smul, det_mul, sub_eq_add_neg, ← neg_smul, det_smul_add_smul_one, taus,
    mul_assoc]
  simp only [← sub_eq_add_neg]

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

end LeanUnitary.Pivot
