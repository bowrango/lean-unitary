import LeanUnitary.Pivot.Split
import LeanUnitary.Pivot.Lift

/-!
# Existence of the pivot angle `β*`

The sign-change argument of `submission/decomposition.tex`, Sec. II.C ("Choosing β"). The
multiplexor has `D = 4q` eigenphases, and `ν β : Fin D → ℝ` is the ordered, lifted list of the
eigenphases of `C(β)` (Eq. 15). The paper shows that, for the pivot angle `α*`, the list depends
continuously on `β` and satisfies the endpoint relation `ν_k(π) = -ν_{D-1-k}(0)`.

From these two properties this module proves:

* `imbalance_neg_rev`: the middle half `S = {D/4, …, 3D/4 - 1}` of the ranks is invariant under
  `k ↦ D - 1 - k`, so the imbalance `P` of Eq. 16 flips sign under the endpoint relation
  (Eq. 17);
* `exists_imbalance_eq_zero`: by the intermediate value theorem, `P(β*) = 0` for some
  `β* ∈ [0, π]`;
* `exists_walsh_eq_zero_of_lift`: at `β*` the eigenphases admit a balanced split, so by
  `Pivot.exists_walsh_eq_zero_iff` some assignment to basis states makes the final angle `φ`
  vanish, which lets the extra CX merge;
* `exists_walsh_eq_zero_of_normalized_lift`: the same, with the endpoint relation derived from
  the uniqueness of the normalized lift (`Pivot.neg_rev_eq_of_lift`).
-/

namespace LeanUnitary.Pivot

open Finset

variable {q : ℕ}

/-- The middle half `S = {D/4, …, 3D/4 - 1}` of the ranks, with `D = 4q`. -/
def middleHalf (q : ℕ) : Finset (Fin (4 * q)) := univ.filter fun k => q ≤ k.val ∧ k.val < 3 * q

/-- The basis states with `h_j = +1`: top control qubit `0`, i.e. `j < D/2`. -/
def topPlus (q : ℕ) : Finset (Fin (4 * q)) := univ.filter fun j => j.val < 2 * q

theorem mem_middleHalf_rev (k : Fin (4 * q)) : k.rev ∈ middleHalf q ↔ k ∈ middleHalf q := by
  simp only [middleHalf, mem_filter, mem_univ, true_and, Fin.val_rev]
  omega

theorem card_middleHalf : (middleHalf q).card = 2 * q := by
  have : middleHalf q = (univ.filter fun k : Fin (4 * q) => k.val < 3 * q) \
      (univ.filter fun k : Fin (4 * q) => k.val < q) := by
    ext k; simp only [middleHalf, mem_filter, mem_univ, true_and, mem_sdiff]; omega
  rw [this, card_sdiff_of_subset (fun k => by simp only [mem_filter, mem_univ, true_and]; omega),
    Fin.card_filter_val_lt, Fin.card_filter_val_lt]
  omega

theorem card_topPlus : (topPlus q).card = 2 * q := by
  rw [topPlus, Fin.card_filter_val_lt]
  omega

/-- Eq. 17: the endpoint relation `ν' = -ν ∘ rev` negates the imbalance over the middle half. -/
theorem imbalance_neg_rev (ν : Fin (4 * q) → ℝ) :
    imbalance (middleHalf q) (fun k => -ν k.rev) = -imbalance (middleHalf q) ν := by
  rw [← sum_walshSign_mul, ← sum_walshSign_mul, ← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, walshSign, mem_middleHalf_rev]
  ring

/-- Eq. 17 and the intermediate value theorem: a continuous lifted eigenphase list with
`ν(π) = -ν(0) ∘ rev` has a balanced middle half at some `β* ∈ [0, π]`. -/
theorem exists_imbalance_eq_zero (ν : ℝ → Fin (4 * q) → ℝ)
    (hν : ContinuousOn ν (Set.Icc 0 Real.pi)) (hend : ν Real.pi = fun k => -ν 0 k.rev) :
    ∃ β ∈ Set.Icc 0 Real.pi, imbalance (middleHalf q) (ν β) = 0 := by
  set P : ℝ → ℝ := fun β => imbalance (middleHalf q) (ν β)
  have hP : ContinuousOn P (Set.Icc 0 Real.pi) := by
    have : Continuous fun μ : Fin (4 * q) → ℝ => imbalance (middleHalf q) μ := by
      unfold imbalance; fun_prop
    exact this.comp_continuousOn hν
  have hπ : P Real.pi = -P 0 := by simp only [P, hend, imbalance_neg_rev]
  rcases le_total (P 0) 0 with h | h
  · obtain ⟨β, hβ, hβ0⟩ := intermediate_value_Icc Real.pi_pos.le hP ⟨h, by linarith⟩
    exact ⟨β, hβ, hβ0⟩
  · obtain ⟨β, hβ, hβ0⟩ := intermediate_value_Icc' Real.pi_pos.le hP ⟨by linarith, h⟩
    exact ⟨β, hβ, hβ0⟩

/-- The existence argument of Sec. II.C: a continuous lifted eigenphase list with the endpoint
relation yields a pivot angle `β*`, an assignment of the eigenphases at `β*` to basis states and
branch shifts for which the final angle `φ` vanishes. -/
theorem exists_walsh_eq_zero_of_lift (hq : 0 < q) (ν : ℝ → Fin (4 * q) → ℝ)
    (hν : ContinuousOn ν (Set.Icc 0 Real.pi)) (hend : ν Real.pi = fun k => -ν 0 k.rev) :
    ∃ β ∈ Set.Icc 0 Real.pi, ∃ (e : Equiv.Perm (Fin (4 * q))) (m : Fin (4 * q) → ℤ),
      walsh (topPlus q) (ν β) e m = 0 := by
  obtain ⟨β, hβ, h0⟩ := exists_imbalance_eq_zero ν hν hend
  have hne : (topPlus q).Nonempty :=
    ⟨⟨0, by omega⟩, by simp [topPlus]; omega⟩
  refine ⟨β, hβ, (exists_walsh_eq_zero_iff hne (ν β)).mpr ⟨middleHalf q, ?_, 0, ?_⟩⟩
  · rw [card_middleHalf, card_topPlus]
  · simp [h0]

/-- The existence argument with the endpoint relation derived rather than assumed. `ν β` is
the normalized lift of the eigenphases of `C(β)` (Eq. 15). At `β = π` the phases are negated
(`C(π) = C(0)⁻¹`) and so is the sum (`σ(π) = -σ(0)`, Eq. 14), so by `neg_rev_eq_of_lift`
`ν(π) = -ν(0) ∘ rev`. -/
theorem exists_walsh_eq_zero_of_normalized_lift (q : ℕ) (ν : ℝ → Fin (4 * (q + 1)) → ℝ)
    (hν : ContinuousOn ν (Set.Icc 0 Real.pi))
    (hnorm0 : Normalized (n := 4 * q + 3) (ν 0)) (hnormπ : Normalized (n := 4 * q + 3) (ν Real.pi))
    (hres : SameResidues (n := 4 * q + 3) (fun k => -ν 0 k) (ν Real.pi))
    (hsum : ∑ k, ν Real.pi k = -∑ k, ν 0 k) :
    ∃ β ∈ Set.Icc 0 Real.pi, ∃ (e : Equiv.Perm (Fin (4 * (q + 1)))) (m : Fin (4 * (q + 1)) → ℤ),
      walsh (topPlus (q + 1)) (ν β) e m = 0 :=
  exists_walsh_eq_zero_of_lift (Nat.succ_pos q) ν hν (neg_rev_eq_of_lift hnorm0 hnormπ hres hsum)

end LeanUnitary.Pivot
