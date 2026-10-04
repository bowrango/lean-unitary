import LeanUnitary.Pivot.Multiplexor.Basic
import LeanUnitary.Pivot.Path.Eigenvalues
import LeanUnitary.Pivot.Existence.Lift

/-!
# Eigenphase lists

A list `ν : Fin D → ℝ` *lists the eigenphases* of `A` (`IsPhaseList`) when the eigenvalues of `A`,
with multiplicity, are the `e^{iν_k}`.

* `exists_phaseList`: every unitary has a list of eigenphases;
* `IsPhaseList.of_sameResidues`: lifts of the same phases list the same eigenvalues;
* `det_eq_exp_sum`, `exists_int_of_exp_eq`: `det U = e^{i Σ ν}`, so a phase of `det U` differs from
  `Σ ν` by a multiple of `2π`;
* `sameResidues_neg_of_inv`, `multiplexor_phases_neg`: the eigenphases of `C(π) = C(0)⁻¹` are the
  negated eigenphases of `C(0)`, modulo `2π` and up to permutation (after Eq. 11);
* `exists_phase_close`: unit complex numbers close to `e^{iθ}` have phases close to `θ`.
-/

namespace LeanUnitary.Pivot

open Matrix Complex Finset
open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `ν` lists the eigenphases of `A`: its eigenvalues, with multiplicity, are `e^{iν_k}`. -/
def IsPhaseList {n : ℕ} (A : Matrix m m ℂ) (ν : Fin (n + 1) → ℝ) : Prop :=
  A.charpoly.roots = (univ : Finset (Fin (n + 1))).val.map fun k => exp (ν k * I)

/-- A unitary matrix has a list of eigenphases. -/
theorem exists_phaseList {n : ℕ} {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ)
    (hcard : Fintype.card m = n + 1) : ∃ w : Fin (n + 1) → ℝ, IsPhaseList U w := by
  obtain ⟨u, hu⟩ := exists_list_of_card U.charpoly.roots ((card_roots_charpoly U).trans hcard)
  refine ⟨fun k => arg (u k), ?_⟩
  rw [IsPhaseList, ← hu]
  refine Multiset.map_congr rfl fun k _ => ?_
  have h1 : ‖u k‖ = 1 := norm_eq_one_of_mem_roots_charpoly hU
    (hu ▸ Multiset.mem_map_of_mem _ (mem_univ_val k))
  have := norm_mul_exp_arg_mul_I (u k)
  rw [h1, ofReal_one, one_mul] at this
  exact this.symm

/-- Lifts of the same phases list the same eigenvalues. -/
theorem IsPhaseList.of_sameResidues {n : ℕ} {U : Matrix m m ℂ} {w ν : Fin (n + 1) → ℝ}
    (hw : IsPhaseList U w) (h : SameResidues w ν) : IsPhaseList U ν := by
  obtain ⟨σ, hσ⟩ := h
  rw [IsPhaseList, hw]
  have hexp : ∀ k, exp (ν k * I) = exp (w (σ k) * I) := fun k => by
    obtain ⟨j, hj⟩ := hσ k
    rw [hj, show ((w (σ k) + 2 * Real.pi * j : ℝ) : ℂ) * I = w (σ k) * I + j * (2 * Real.pi * I)
      by push_cast; ring, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  rw [Multiset.map_congr rfl fun k _ => hexp k]
  rw [show (fun k => exp (w (σ k) * I)) = (fun k => exp (w k * I)) ∘ σ from rfl,
    ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- `det U = e^{i Σ w}` for a list of eigenphases `w`. -/
theorem det_eq_exp_sum {n : ℕ} {U : Matrix m m ℂ} {w : Fin (n + 1) → ℝ} (hw : IsPhaseList U w) :
    U.det = exp ((∑ k, w k : ℝ) * I) := by
  rw [det_eq_prod_roots_charpoly, hw, ofReal_sum, Finset.sum_mul, exp_sum]
  rfl

/-- A phase `σ` of `det U` differs from the sum of a list of eigenphases by a multiple of `2π`. -/
theorem exists_int_of_exp_eq {n : ℕ} {U : Matrix m m ℂ} {w : Fin (n + 1) → ℝ}
    (hw : IsPhaseList U w) {σ : ℝ} (hσ : exp (σ * I) = U.det) :
    ∃ k : ℤ, σ = ∑ j, w j + 2 * Real.pi * k := by
  rw [det_eq_exp_sum hw] at hσ
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp hσ
  refine ⟨k, ?_⟩
  have := congrArg Complex.im hk
  simp at this
  linarith

/-- The eigenphases of `A⁻¹` are the negated eigenphases of `A`, modulo `2π` and up to
permutation. -/
theorem sameResidues_neg_of_inv {n : ℕ} {A : Matrix m m ℂ} (hA : IsUnit A.det)
    {ν ν' : Fin (n + 1) → ℝ} (hν : IsPhaseList A ν) (hν' : IsPhaseList A⁻¹ ν') :
    SameResidues (fun k => -ν k) ν' := by
  have h : (univ : Finset (Fin (n + 1))).val.map (fun k => exp (ν' k * I)) =
      (univ : Finset (Fin (n + 1))).val.map (fun k => exp (((fun k => -ν k) k : ℝ) * I)) := by
    rw [← hν', roots_charpoly_inv hA, hν, Multiset.map_map]
    refine Multiset.map_congr rfl fun k _ => ?_
    simp only [Function.comp_apply, ofReal_neg, neg_mul, exp_neg]
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq h
  exact sameResidues_of_exp σ fun k => (hσ k).symm

/-- The endpoint phases of the pivot path: the eigenphases of `C(π)` are the negated
eigenphases of `C(0)`, modulo `2π` and up to permutation. -/
theorem multiplexor_phases_neg {n : ℕ} (α : ℝ) {X Y : Matrix m m ℂ} (hX : IsUnit X.det)
    (hY : IsUnit Y.det) {ν ν' : Fin (n + 1) → ℝ} (hν : IsPhaseList (multiplexor α 0 X Y) ν)
    (hν' : IsPhaseList (multiplexor α Real.pi X Y) ν') :
    SameResidues (fun k => -ν k) ν' := by
  have hp' : star (ph α) * star (star (ph α)) = 1 := by rw [star_star]; exact star_ph_mul_ph α
  have hU := multiplexor_mem_unitaryGroup α 0 (X := X) (Y := Y)
    (by rw [Xg_zero]; exact isUnit_det_smul_ph hp' hX)
    (by rw [Yg_zero]; exact isUnit_det_smul_ph (ph_mul_star_ph α) hY)
  have hdet : IsUnit (multiplexor α 0 X Y).det :=
    isUnit_det_of_left_inverse (mem_unitaryGroup_iff'.mp hU)
  rw [multiplexor_pi_eq_inv α hX hY] at hν'
  exact sameResidues_neg_of_inv hdet hν hν'

/-- Unit complex numbers close to `e^{iθ}` have a phase close to `θ`. -/
theorem exists_phase_close {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (θ : ℝ) (z : ℂ), ‖z‖ = 1 → ‖z - exp (θ * I)‖ < η →
      ∃ θ' : ℝ, exp (θ' * I) = z ∧ |θ' - θ| < ε := by
  have hc := continuousAt_arg (x := 1) (by simp [mem_slitPlane_iff])
  obtain ⟨η, hη, h⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨η, hη, fun θ z hz hzθ => ?_⟩
  set w := z * exp (-(θ * I))
  have hθn : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ
  have hw1 : ‖w‖ = 1 := by
    rw [norm_mul, hz, show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, one_mul]
  have hwdist : dist w 1 < η := by
    rw [dist_eq_norm]
    have : w - 1 = (z - exp (θ * I)) * exp (-(θ * I)) := by
      simp only [w]; rw [sub_mul, ← exp_add, add_neg_cancel, exp_zero]
    rw [this, norm_mul, show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]
    exact hzθ
  have harg := h hwdist
  rw [arg_one, Real.dist_eq, sub_zero] at harg
  refine ⟨θ + arg w, ?_, by rw [add_sub_cancel_left]; exact harg⟩
  have hwexp : exp (arg w * I) = w := by
    have := norm_mul_exp_arg_mul_I w; rwa [hw1, ofReal_one, one_mul] at this
  rw [ofReal_add, add_mul, exp_add, hwexp]
  simp only [w]
  rw [mul_left_comm, ← exp_add, add_neg_cancel, exp_zero, mul_one]

end LeanUnitary.Pivot
