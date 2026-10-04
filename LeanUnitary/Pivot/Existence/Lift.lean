import Mathlib

/-!
# The normalized eigenphase lift

`submission/decomposition.tex`, Eq. 15. A *normalized lift* of `D` eigenphases is a list of real
representatives `ν_0 ≤ ⋯ ≤ ν_{D-1} ≤ ν_0 + 2π`. The paper fixes the lift by its sum.

* `normalized_lift_unique`: two normalized lifts of the same phases (as a multiset modulo `2π`)
  with the same sum are equal;
* `neg_rev_eq_of_lift`: hence the endpoint relation `ν(π) = -ν(0) ∘ rev`, from negated phases
  and a negated sum;
* `exists_normalized_lift`: any phases have a normalized lift with any sum in `Σ w + 2πℤ`
  (sort, then `shift` the smallest phase to the end after adding `2π`);
* `normalized_lift_stable`: if the phases move by at most `ε` and the sums by less than
  `2π - Dε`, every entry moves by at most `ε`.

The proofs use the floor invariant `c(x) = Σ_k ⌊(x - ν_k)/2π⌋`: together with the sum it is
unchanged by permuting or shifting phases by `2π` (`floorSum_add_sum_eq`), and it recovers a
normalized lift (`le_iff_floorSum`: `ν_j ≤ x ↔ j + 1 - D ≤ c(x)`).
-/

namespace LeanUnitary.Pivot

open Finset Real

variable {n : ℕ}

/-! ## The floor invariant and uniqueness -/

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

/-! ## Existence -/

theorem SameResidues.refl (ν : Fin (n + 1) → ℝ) : SameResidues ν ν :=
  ⟨Equiv.refl _, fun k => ⟨0, by simp⟩⟩

theorem SameResidues.trans {a b c : Fin (n + 1) → ℝ} (hab : SameResidues a b)
    (hbc : SameResidues b c) : SameResidues a c := by
  obtain ⟨σ, hσ⟩ := hab
  obtain ⟨τ, hτ⟩ := hbc
  refine ⟨τ.trans σ, fun k => ?_⟩
  obtain ⟨m₁, h₁⟩ := hτ k
  obtain ⟨m₂, h₂⟩ := hσ (τ k)
  exact ⟨m₂ + m₁, by rw [h₁, h₂]; simp; ring⟩

/-- Move the first entry to the end, adding `2π`. -/
noncomputable def shift (ν : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun k => ν (finRotate (n + 1) k) + if k = Fin.last n then 2 * π else 0

theorem shift_val (k : Fin (n + 1)) (hk : k ≠ Fin.last n) :
    ((finRotate (n + 1) k : Fin (n + 1)) : ℕ) = k + 1 := by
  rw [coe_finRotate, if_neg hk]

theorem Normalized.shift {ν : Fin (n + 1) → ℝ} (hν : Normalized ν) : Normalized (shift ν) := by
  have hle := hν.le_of_le
  have hlast : finRotate (n + 1) (Fin.last n) = 0 := by ext; simp
  constructor
  · intro i j hij
    simp only [Pivot.shift]
    by_cases hj : j = Fin.last n
    · by_cases hi : i = Fin.last n
      · subst hi; subst hj; rfl
      · rw [if_pos hj, if_neg hi, hj, hlast, add_zero]
        exact (hle _).2
    · have hi : i ≠ Fin.last n := fun h => hj (le_antisymm (Fin.le_last j) (h ▸ hij))
      rw [if_neg hj, if_neg hi, add_zero, add_zero]
      apply hν.1
      rw [Fin.le_iff_val_le_val, shift_val i hi, shift_val j hj]
      exact Nat.add_le_add_right hij 1
  · have e1 : Pivot.shift ν (Fin.last n) = ν 0 + 2 * π := by simp [Pivot.shift, hlast]
    have e2 : ν 0 ≤ Pivot.shift ν 0 := by
      unfold Pivot.shift
      split_ifs
      · linarith [(hle (finRotate (n + 1) 0)).1, pi_pos]
      · linarith [(hle (finRotate (n + 1) 0)).1]
    rw [e1]; linarith

theorem sameResidues_shift (ν : Fin (n + 1) → ℝ) : SameResidues ν (shift ν) :=
  ⟨finRotate (n + 1), fun k => by
    by_cases hk : k = Fin.last n
    · exact ⟨1, by simp [Pivot.shift, hk]⟩
    · exact ⟨0, by simp [Pivot.shift, hk]⟩⟩

theorem sum_shift (ν : Fin (n + 1) → ℝ) : ∑ k, shift ν k = ∑ k, ν k + 2 * π := by
  simp only [Pivot.shift, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  rw [Equiv.sum_comp]

theorem exists_shift_nat (ν : Fin (n + 1) → ℝ) (hν : Normalized ν) (r : ℕ) :
    ∃ ν', Normalized ν' ∧ SameResidues ν ν' ∧ ∑ k, ν' k = ∑ k, ν k + 2 * π * r := by
  induction r with
  | zero => exact ⟨ν, hν, SameResidues.refl ν, by simp⟩
  | succ r ih =>
    obtain ⟨ν', h1, h2, h3⟩ := ih
    refine ⟨shift ν', h1.shift, h2.trans (sameResidues_shift ν'), ?_⟩
    rw [sum_shift, h3]; push_cast; ring

theorem Normalized.add_const {ν : Fin (n + 1) → ℝ} (hν : Normalized ν) (c : ℝ) :
    Normalized fun k => ν k + c :=
  ⟨fun i j hij => by simp only; linarith [hν.1 hij], by simp only; linarith [hν.2]⟩

/-- Any phases have a normalized lift with any sum in `Σ w + 2πℤ`. -/
theorem exists_normalized_lift (w : Fin (n + 1) → ℝ) (k : ℤ) :
    ∃ ν, Normalized ν ∧ SameResidues w ν ∧ ∑ j, ν j = ∑ j, w j + 2 * π * k := by
  have h2π : 0 < 2 * π := by positivity
  -- reduce to `[0, 2π)` and sort
  set a : Fin (n + 1) → ℝ := fun j => toIcoMod h2π 0 (w j)
  set N : Fin (n + 1) → ℤ := fun j => toIcoDiv h2π 0 (w j)
  have ha : ∀ j, a j = w j - 2 * π * N j := fun j => by
    change toIcoMod h2π 0 (w j) = _
    rw [← self_sub_toIcoDiv_zsmul h2π 0 (w j), zsmul_eq_mul]; simp only [N]; ring
  have hmem : ∀ j, 0 ≤ a j ∧ a j < 2 * π := fun j => by
    have := toIcoMod_mem_Ico h2π 0 (w j); simp only [zero_add] at this; exact this
  set σ := Tuple.sort a
  set b : Fin (n + 1) → ℝ := a ∘ σ
  have hb : Normalized b := ⟨Tuple.monotone_sort a, by
    simp only [b, Function.comp_apply]; linarith [(hmem (σ (Fin.last n))).2, (hmem (σ 0)).1]⟩
  have hwb : SameResidues w b := ⟨σ, fun j => ⟨-N (σ j), by
    simp only [b, Function.comp_apply, ha]; push_cast; ring⟩⟩
  have hsumb : ∑ j, b j = ∑ j, w j - 2 * π * ∑ j, (N j : ℝ) := by
    simp only [b, Function.comp_apply]
    rw [Equiv.sum_comp σ a]
    simp only [ha, sum_sub_distrib, ← mul_sum]
  -- the target sum is `Σ b + 2π (q (n+1) + r)` with `0 ≤ r < n + 1`
  set j : ℤ := k + ∑ i, N i
  set q : ℤ := j / (n + 1)
  set r : ℤ := j % (n + 1)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hj : j = (n + 1) * q + r := (Int.mul_ediv_add_emod j (n + 1)).symm
  obtain ⟨ν', h1, h2, h3⟩ := exists_shift_nat b hb r.toNat
  refine ⟨fun i => ν' i + 2 * π * q, h1.add_const _, hwb.trans (h2.trans ⟨Equiv.refl _,
    fun i => ⟨q, by simp⟩⟩), ?_⟩
  have hrr : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hr0
  rw [sum_add_distrib, h3, hsumb, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hrr]
  have hj' : (j : ℝ) = (n + 1) * q + r := by exact_mod_cast hj
  simp only [j] at hj'
  push_cast at hj' ⊢
  linear_combination (-(2 * π)) * hj'

/-! ## Stability -/

/-- A normalized lift is recovered from its floor invariant: `ν_j ≤ x ↔ j + 1 - D ≤ c(x)`. -/
theorem le_iff_floorSum {ν : Fin (n + 1) → ℝ} (hν : Normalized ν) (j : Fin (n + 1)) (x : ℝ) :
    ν j ≤ x ↔ (j : ℤ) + 1 - (n + 1) ≤ floorSum ν x := by
  have hpi : 0 < 2 * π := by positivity
  rcases lt_or_ge x (ν 0) with hx | hx
  · have hb := floorSum_le_of_lt hν hx
    constructor
    · intro h; linarith [(hν.le_of_le j).1]
    · intro h; omega
  rcases lt_or_ge x (ν 0 + 2 * π) with hx' | hx'
  · rw [floorSum_eq_on_window hν hx hx', le_iff_countLE hν.1]
    omega
  · have hnn : 0 ≤ floorSum ν x := Finset.sum_nonneg fun k _ => Int.floor_nonneg.mpr
      (div_nonneg (by linarith [(hν.le_of_le k).2]) hpi.le)
    exact ⟨fun _ => by omega, fun _ => (hν.le_of_le j).2.trans hx'⟩

/-- Stability of the normalized lift: if the phases of `ν'` are within `ε` of those of `ν` and
the sums differ by less than `2π - Dε`, then `ν'` is within `ε` of `ν` entrywise. Here `μ` is
a lift of the phases of `ν'` that is close to `ν` after the matching `σ`. -/
theorem normalized_lift_stable {ν ν' μ : Fin (n + 1) → ℝ} (hν : Normalized ν)
    (hν' : Normalized ν') (σ : Equiv.Perm (Fin (n + 1))) {ε : ℝ}
    (hclose : ∀ k, |μ k - ν (σ k)| ≤ ε) (hres : SameResidues μ ν')
    (hsum : |∑ k, ν' k - ∑ k, ν k| + (n + 1) * ε < 2 * π) :
    ∀ j, |ν' j - ν j| ≤ ε := by
  have hpi : 0 < 2 * π := by positivity
  -- the floor invariants of `μ` and `ν'` agree
  have hsumt : |∑ k, μ k - ∑ k, ν k| ≤ (n + 1) * ε := by
    rw [← Equiv.sum_comp σ ν, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun k (_ : k ∈ univ) => hclose k
  have hc : ∀ x, floorSum ν' x = floorSum μ x := fun x => by
    have h := floorSum_add_sum_eq hres x
    have hint : ((floorSum ν' x - floorSum μ x : ℤ) : ℝ) * (2 * π) =
        ∑ k, μ k - ∑ k, ν' k := by
      push_cast; field_simp at h ⊢; linarith
    have hlt : |((floorSum ν' x - floorSum μ x : ℤ) : ℝ)| < 1 := by
      rw [← mul_lt_mul_iff_of_pos_right hpi, one_mul, ← abs_of_pos hpi, ← abs_mul, hint,
        abs_of_pos hpi]
      calc |∑ k, μ k - ∑ k, ν' k|
          ≤ |∑ k, μ k - ∑ k, ν k| + |∑ k, ν' k - ∑ k, ν k| := by
            rw [abs_sub_comm (∑ k, ν' k)]; exact abs_sub_le _ _ _
        _ < 2 * π := by linarith
    have : floorSum ν' x - floorSum μ x = 0 := by
      rw [← Int.cast_abs] at hlt
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
    omega
  -- `μ` is sandwiched between the shifts of `ν` by `±ε`
  have hlow : ∀ x, floorSum ν (x - ε) ≤ floorSum μ x := fun x => by
    rw [floorSum, floorSum, ← Equiv.sum_comp σ]
    exact Finset.sum_le_sum fun k _ => Int.floor_mono (div_le_div_of_nonneg_right
      (by linarith [(abs_le.mp (hclose k)).2]) hpi.le)
  have hhigh : ∀ x, floorSum μ x ≤ floorSum ν (x + ε) := fun x => by
    rw [floorSum, floorSum, ← Equiv.sum_comp σ (fun k => ⌊(x + ε - ν k) / (2 * π)⌋)]
    exact Finset.sum_le_sum fun k _ => Int.floor_mono (div_le_div_of_nonneg_right
      (by linarith [(abs_le.mp (hclose k)).1]) hpi.le)
  intro j
  rw [abs_le]
  constructor
  · -- `ν_j ≤ ν'_j + ε`
    have h1 := (le_iff_floorSum hν' j (ν' j)).mp le_rfl
    have h2 : (j : ℤ) + 1 - (n + 1) ≤ floorSum ν (ν' j + ε) :=
      h1.trans ((hc _).le.trans (hhigh _))
    linarith [(le_iff_floorSum hν j _).mpr h2]
  · -- `ν'_j ≤ ν_j + ε`
    have h1 := (le_iff_floorSum hν j (ν j)).mp le_rfl
    have h2 : (j : ℤ) + 1 - (n + 1) ≤ floorSum ν' (ν j + ε) := by
      have := hlow (ν j + ε)
      rw [show ν j + ε - ε = ν j by ring] at this
      rw [hc]; exact h1.trans this
    linarith [(le_iff_floorSum hν' j _).mpr h2]

end LeanUnitary.Pivot
