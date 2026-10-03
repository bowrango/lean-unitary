import Mathlib

/-!
# Uniqueness of the normalized eigenphase lift

`submission/decomposition.tex`, Eq. 15. A *normalized lift* of `D` eigenphases is a list of real
representatives `ν_0 ≤ ⋯ ≤ ν_{D-1} ≤ ν_0 + 2π`. The paper fixes the lift by its sum: two
normalized lifts of the same eigenphases (as a multiset modulo `2π`) with the same sum are
equal (`normalized_lift_unique`).

The proof uses the invariant `c(x) = Σ_k ⌊(x - ν_k)/2π⌋`. Together with the sum, this is unchanged
by permuting the list or shifting entries by multiples of `2π`. For a normalized lift, `c` is
`-#{k | ν_k > x}` on the window `[ν_0, ν_0 + 2π)` and at most `-D` below it. So `c` determines
`ν_0`, then the counting function `#{k | ν_k ≤ x}`, and hence the sorted list.

`neg_rev_eq_of_lift`: applied to `ν' = ν(π)` and the reversed negation of `ν(0)`, this gives the
endpoint relation `ν(π) = -ν(0) ∘ rev` used by `Pivot.exists_walsh_eq_zero_of_lift`, from
`C(π) = C(0)⁻¹` (negated eigenphases) and `σ(π) = -σ(0)` (negated sum).
-/

namespace LeanUnitary.Pivot

open Finset Real

variable {n : ℕ}

/-- `ν_0 ≤ ⋯ ≤ ν_{D-1} ≤ ν_0 + 2π` (Eq. 15). -/
def Normalized (ν : Fin (n + 1) → ℝ) : Prop :=
  Monotone ν ∧ ν (Fin.last n) ≤ ν 0 + 2 * π

/-- `ν'` lists the same phases as `ν` modulo `2π`, in some order. -/
def SameResidues (ν ν' : Fin (n + 1) → ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin (n + 1)), ∀ k, ∃ m : ℤ, ν' k = ν (σ k) + 2 * π * m

/-- The floor invariant `c(x) = Σ_k ⌊(x - ν_k)/2π⌋`. -/
noncomputable def floorSum (ν : Fin (n + 1) → ℝ) (x : ℝ) : ℤ :=
  ∑ k, ⌊(x - ν k) / (2 * π)⌋

/-- `#{k | ν_k ≤ x}`. -/
noncomputable def countLE (ν : Fin (n + 1) → ℝ) (x : ℝ) : ℕ :=
  (univ.filter fun k => ν k ≤ x).card

/-- `c(x) + Σ ν / 2π` depends only on the phases modulo `2π`. -/
theorem floorSum_add_sum_eq {ν ν' : Fin (n + 1) → ℝ} (h : SameResidues ν ν') (x : ℝ) :
    (floorSum ν' x : ℝ) + (∑ k, ν' k) / (2 * π) = floorSum ν x + (∑ k, ν k) / (2 * π) := by
  obtain ⟨σ, hσ⟩ := h
  choose m hm using hσ
  have hpi : (2 * π) ≠ 0 := by positivity
  have hterm : ∀ k, (⌊(x - ν' k) / (2 * π)⌋ : ℝ) + ν' k / (2 * π) =
      ⌊(x - ν (σ k)) / (2 * π)⌋ + ν (σ k) / (2 * π) := fun k => by
    have : (x - ν' k) / (2 * π) = (x - ν (σ k)) / (2 * π) - m k := by
      rw [hm k]; field_simp; ring
    rw [this, Int.floor_sub_intCast, hm k]
    push_cast
    field_simp
    ring
  simp only [floorSum, Int.cast_sum, sum_div, ← sum_add_distrib]
  rw [← Equiv.sum_comp σ (fun j => (⌊(x - ν j) / (2 * π)⌋ : ℝ) + ν j / (2 * π))]
  exact sum_congr rfl fun k _ => hterm k

theorem Normalized.le_of_le {ν : Fin (n + 1) → ℝ} (hν : Normalized ν) (k : Fin (n + 1)) :
    ν 0 ≤ ν k ∧ ν k ≤ ν 0 + 2 * π :=
  ⟨hν.1 (Fin.zero_le k), (hν.1 (Fin.le_last k)).trans hν.2⟩

/-- On the window `[ν_0, ν_0 + 2π)`, `c(x) = #{k | ν_k ≤ x} - D`. -/
theorem floorSum_eq_on_window {ν : Fin (n + 1) → ℝ} (hν : Normalized ν) {x : ℝ}
    (h1 : ν 0 ≤ x) (h2 : x < ν 0 + 2 * π) :
    floorSum ν x = countLE ν x - (n + 1) := by
  have hpi : 0 < 2 * π := by positivity
  have hterm : ∀ k, ⌊(x - ν k) / (2 * π)⌋ = if ν k ≤ x then 0 else -1 := fun k => by
    obtain ⟨hk1, hk2⟩ := hν.le_of_le k
    split_ifs with hk
    · rw [Int.floor_eq_iff]; push_cast
      constructor
      · exact div_nonneg (by linarith) hpi.le
      · rw [div_lt_iff₀ hpi]; linarith
    · rw [Int.floor_eq_iff]; push_cast
      constructor
      · rw [le_div_iff₀ hpi]; linarith
      · rw [div_lt_iff₀ hpi]; linarith
  have hsplit := card_filter_add_card_filter_not (s := univ) (fun k => ν k ≤ x)
  rw [card_univ, Fintype.card_fin] at hsplit
  simp only [floorSum, hterm, sum_ite, sum_const_zero, sum_const, nsmul_eq_mul, mul_neg, mul_one,
    zero_add, countLE]
  omega

/-- Below the window, `c(x) ≤ -D`. -/
theorem floorSum_le_of_lt {ν : Fin (n + 1) → ℝ} (hν : Normalized ν) {x : ℝ} (hx : x < ν 0) :
    floorSum ν x ≤ -(n + 1) := by
  have hpi : 0 < 2 * π := by positivity
  have : ∀ k ∈ (univ : Finset (Fin (n + 1))), ⌊(x - ν k) / (2 * π)⌋ ≤ -1 := fun k _ => by
    have := (hν.le_of_le k).1
    rw [Int.floor_le_iff]; push_cast
    rw [neg_add_cancel]
    exact div_neg_of_neg_of_pos (by linarith) hpi
  have := sum_le_sum this
  simp only [sum_const, card_univ, Fintype.card_fin] at this
  simpa [floorSum] using this

/-- For a monotone list, `ν_j ≤ x` iff at least `j + 1` entries are `≤ x`. -/
theorem le_iff_countLE {ν : Fin (n + 1) → ℝ} (hν : Monotone ν) (j : Fin (n + 1)) (x : ℝ) :
    ν j ≤ x ↔ j.val + 1 ≤ countLE ν x := by
  constructor
  · intro h
    have : Iic j ⊆ univ.filter fun k => ν k ≤ x := fun k hk =>
      mem_filter.mpr ⟨mem_univ _, (hν (mem_Iic.mp hk)).trans h⟩
    have := card_le_card this
    rwa [Fin.card_Iic] at this
  · intro h
    by_contra hlt
    push Not at hlt
    have : (univ.filter fun k => ν k ≤ x) ⊆ Iio j := fun k hk => by
      rw [mem_Iio]
      by_contra hjk
      push Not at hjk
      exact absurd ((hν hjk).trans (mem_filter.mp hk).2) (not_le.mpr hlt)
    have := card_le_card this
    rw [Fin.card_Iio] at this
    unfold countLE at h
    omega

/-- Eq. 15: two normalized lifts of the same phases with the same sum are equal. -/
theorem normalized_lift_unique {ν ν' : Fin (n + 1) → ℝ} (hν : Normalized ν) (hν' : Normalized ν')
    (hres : SameResidues ν ν') (hsum : ∑ k, ν k = ∑ k, ν' k) : ν = ν' := by
  -- the floor invariants agree
  have hc : ∀ x, floorSum ν x = floorSum ν' x := fun x => by
    have := floorSum_add_sum_eq hres x
    rw [hsum] at this
    exact_mod_cast (add_right_cancel this).symm
  -- the base points agree
  have hbase : ∀ {μ μ' : Fin (n + 1) → ℝ}, Normalized μ → Normalized μ' →
      (∀ x, floorSum μ x = floorSum μ' x) → ¬ μ 0 < μ' 0 := by
    intro μ μ' hμ hμ' hcμ hlt
    have hw := floorSum_eq_on_window hμ le_rfl (by linarith [pi_pos])
    have hb := floorSum_le_of_lt hμ' hlt
    have h0 : 1 ≤ countLE μ (μ 0) :=
      (le_iff_countLE hμ.1 0 (μ 0)).mp le_rfl
    rw [hcμ] at hw
    omega
  have h0 : ν 0 = ν' 0 := le_antisymm (not_lt.mp (hbase hν' hν fun x => (hc x).symm))
    (not_lt.mp (hbase hν hν' hc))
  -- the counting functions agree everywhere
  have hcount : ∀ x, countLE ν x = countLE ν' x := fun x => by
    rcases lt_or_ge x (ν 0) with hx | hx
    · have hz : ∀ μ : Fin (n + 1) → ℝ, Normalized μ → x < μ 0 → countLE μ x = 0 :=
        fun μ hμ hxμ => by
        rw [countLE, card_eq_zero, filter_eq_empty_iff]
        exact fun k _ => not_le.mpr (hxμ.trans_le (hμ.le_of_le k).1)
      rw [hz ν hν hx, hz ν' hν' (h0 ▸ hx)]
    rcases lt_or_ge x (ν 0 + 2 * π) with hx' | hx'
    · have := hc x
      rw [floorSum_eq_on_window hν hx hx', floorSum_eq_on_window hν' (h0 ▸ hx) (h0 ▸ hx')] at this
      omega
    · have hf : ∀ μ : Fin (n + 1) → ℝ, Normalized μ → μ 0 + 2 * π ≤ x → countLE μ x = n + 1 :=
        fun μ hμ hxμ => by
        rw [countLE, filter_true_of_mem fun k _ => (hμ.le_of_le k).2.trans hxμ, card_univ,
          Fintype.card_fin]
      rw [hf ν hν hx', hf ν' hν' (h0 ▸ hx')]
  -- so the sorted lists agree
  funext j
  exact le_antisymm ((le_iff_countLE hν.1 j _).mpr ((hcount _).symm ▸
      (le_iff_countLE hν'.1 j _).mp le_rfl))
    ((le_iff_countLE hν'.1 j _).mpr ((hcount _) ▸ (le_iff_countLE hν.1 j _).mp le_rfl))

/-- The reversed negation `k ↦ -ν_{D-1-k}` of a normalized lift is normalized. -/
theorem Normalized.neg_rev {ν : Fin (n + 1) → ℝ} (hν : Normalized ν) :
    Normalized fun k => -ν k.rev := by
  refine ⟨fun i j hij => neg_le_neg (hν.1 (Fin.rev_le_rev.mpr hij)), ?_⟩
  simp only [Fin.rev_last, Fin.rev_zero]
  linarith [hν.2]

/-- The endpoint relation of Eq. 15: if `ν'` is a normalized lift of the negated phases of `ν`
with the negated sum, then `ν' = -ν ∘ rev`. -/
theorem neg_rev_eq_of_lift {ν ν' : Fin (n + 1) → ℝ} (hν : Normalized ν) (hν' : Normalized ν')
    (hres : SameResidues (fun k => -ν k) ν') (hsum : ∑ k, ν' k = -∑ k, ν k) :
    ν' = fun k => -ν k.rev := by
  refine (normalized_lift_unique hν.neg_rev hν' ?_ ?_).symm
  · obtain ⟨σ, hσ⟩ := hres
    refine ⟨σ.trans Fin.revPerm, fun k => ?_⟩
    obtain ⟨m, hm⟩ := hσ k
    exact ⟨m, by simp [hm]⟩
  · rw [hsum, ← sum_neg_distrib, ← Equiv.sum_comp Fin.revPerm]
    simp

/-- `SameResidues` from equal phase factors `e^{iν}`. -/
theorem sameResidues_of_exp {ν ν' : Fin (n + 1) → ℝ} (σ : Equiv.Perm (Fin (n + 1)))
    (h : ∀ k, Complex.exp (ν' k * Complex.I) = Complex.exp (ν (σ k) * Complex.I)) :
    SameResidues ν ν' := by
  refine ⟨σ, fun k => ?_⟩
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp (h k)
  refine ⟨m, ?_⟩
  have := congrArg Complex.im hm
  simp at this
  linarith

end LeanUnitary.Pivot
