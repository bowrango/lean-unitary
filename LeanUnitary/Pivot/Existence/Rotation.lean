import Mathlib

/-!
# Choosing the pivot angle `α*`

`submission/decomposition.tex`, Sec. II.C ("Choosing α"). The pivot rotates the eigenvalues
`τ_k` of `X⁻¹Y` together, `τ_k ↦ e^{iα} τ_k`. Taking `α*` with no rotated `τ_k` real and exactly
half of them in the upper half-plane (`N₊ = N₋ = D/2`) removes the half-turn term of Eq. 13.

Such an `α*` exists when the crossing angles are distinct, i.e. no two `τ_k` lie on a common
line through the origin. This hypothesis is needed: for `D = 2` and `τ₀ = τ₁ = 1`, `N₊` is
always `0` or `2`.

The proof sweeps a threshold through the sorted crossing angles. Each crossing changes `N₊` by
one, and a half turn replaces `N₊` by `D - N₊`, so a discrete intermediate value argument
(`exists_eq_of_step_le_one`) gives `N₊ = D/2`.

* `exists_rotation_half_pos`: the statement for angles `θ_k`, with `sin (θ_k + α)` the sign
  of the imaginary part;
* `exists_rotation_half_upper`: the statement for nonzero complex `τ_k`.
-/

namespace LeanUnitary.Pivot

open Finset Real

/-- A discrete intermediate value theorem: an integer sequence moving by at most one per step
takes every value between its endpoints. -/
theorem exists_eq_of_step_le_one (f : ℕ → ℤ) (n : ℕ) (hstep : ∀ i < n, |f (i + 1) - f i| ≤ 1)
    {c : ℤ} (h0 : f 0 ≤ c) (hn : c ≤ f n) : ∃ i ≤ n, f i = c := by
  classical
  have hex : ∃ i, i ≤ n ∧ c ≤ f i := ⟨n, le_rfl, hn⟩
  set i := Nat.find hex
  have hi : i ≤ n ∧ c ≤ f i := Nat.find_spec hex
  refine ⟨i, hi.1, ?_⟩
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h] at hi ⊢; omega
  · have hlt : ¬(i - 1 ≤ n ∧ c ≤ f (i - 1)) := Nat.find_min hex (by omega)
    have hs := hstep (i - 1) (by omega)
    rw [Nat.sub_add_cancel h] at hs
    have := abs_le.mp hs
    push Not at hlt
    have := hlt (by omega)
    omega

/-- The same, for a sequence whose endpoints sum to `2c`. -/
theorem exists_eq_of_step_le_one' (f : ℕ → ℤ) (n : ℕ) (hstep : ∀ i < n, |f (i + 1) - f i| ≤ 1)
    {c : ℤ} (hsum : f 0 + f n = 2 * c) : ∃ i ≤ n, f i = c := by
  rcases le_total (f 0) c with h | h
  · exact exists_eq_of_step_le_one f n hstep h (by omega)
  · obtain ⟨i, hi, hfi⟩ := exists_eq_of_step_le_one (fun i => -f i) n
      (fun i hi => by rw [← abs_neg]; convert hstep i hi using 2; ring) (c := -c)
      (show -f 0 ≤ -c by omega) (show -c ≤ -f n by omega)
    exact ⟨i, hi, by have : -f i = -c := hfi; omega⟩

/-- `sin (θ - t)` from the reduction `θ = ψ + nπ` with `ψ ∈ (t - π, t + π)`: positive iff
`ψ > t` when `n` is even, and iff `ψ < t` when `n` is odd. -/
theorem sin_sub_pos_iff {θ ψ t : ℝ} {n : ℤ} (hθ : θ = ψ + n * π) (h1 : t - π < ψ) (h2 : ψ < t + π)
    (hne : ψ ≠ t) : 0 < sin (θ - t) ↔ (t < ψ ↔ Even n) := by
  have hs : sin (θ - t) = (-1) ^ n * sin (ψ - t) := by
    rw [hθ, show ψ + n * π - t = (ψ - t) + n * π by ring, sin_add_int_mul_pi]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hneg : sin (ψ - t) < 0 := sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    rcases Int.even_or_odd n with he | ho
    · rw [hs, he.neg_one_zpow]; simp only [one_mul]; constructor <;> intro h
      · linarith
      · exact absurd (h.mpr he) (by linarith)
    · rw [hs, ho.neg_one_zpow]; constructor <;> intro _
      · exact ⟨fun h => absurd h (by linarith), fun h => absurd ho (Int.not_odd_iff_even.mpr h)⟩
      · linarith
  · have hpos : 0 < sin (ψ - t) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rcases Int.even_or_odd n with he | ho
    · rw [hs, he.neg_one_zpow]; simp only [one_mul]; exact ⟨fun _ => ⟨fun _ => he, fun _ => hgt⟩,
        fun _ => hpos⟩
    · rw [hs, ho.neg_one_zpow]; constructor <;> intro h
      · linarith
      · exact absurd (h.mp hgt) (Int.not_even_iff_odd.mpr ho)

theorem sin_sub_ne_zero {θ ψ t : ℝ} {n : ℤ} (hθ : θ = ψ + n * π) (h1 : t - π < ψ) (h2 : ψ < t + π)
    (hne : ψ ≠ t) : sin (θ - t) ≠ 0 := by
  rw [hθ, show ψ + n * π - t = (ψ - t) + n * π by ring, sin_add_int_mul_pi]
  refine mul_ne_zero (zpow_ne_zero _ (by norm_num)) ?_
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)).ne
  · exact (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'

/-- Eq. 13, choice of `α*`, for angles: if no two `θ_k` differ by a multiple of `π`, some
rotation `α` puts no `θ_k + α` on the real axis and exactly half of them in the upper half
plane. -/
theorem exists_rotation_half_pos {r : ℕ} (θ : Fin (2 * r) → ℝ)
    (hθ : ∀ j k, j ≠ k → ∀ z : ℤ, θ j - θ k ≠ z * π) :
    ∃ α : ℝ, (∀ k, sin (θ k + α) ≠ 0) ∧ (univ.filter fun k => 0 < sin (θ k + α)).card = r := by
  classical
  -- a generic base point `a`, congruent to no `θ_k` modulo `π`
  obtain ⟨a, haI, ha⟩ := (Set.Ioo_infinite (show (0 : ℝ) < π from pi_pos)).exists_notMem_finset
    (univ.image fun k => toIcoMod pi_pos 0 (θ k))
  -- reduce `θ_k = ψ_k + n_k π` with `ψ_k ∈ (a, a + π)`
  set ψ : Fin (2 * r) → ℝ := fun k => toIcoMod pi_pos a (θ k)
  set n : Fin (2 * r) → ℤ := fun k => toIcoDiv pi_pos a (θ k)
  have hθψ : ∀ k, θ k = ψ k + n k * π := fun k => by
    have := self_sub_toIcoDiv_zsmul pi_pos a (θ k)
    rw [zsmul_eq_mul] at this
    simp only [ψ, n]; linarith
  have hψa : ∀ k, a < ψ k ∧ ψ k < a + π := fun k => by
    obtain ⟨h1, h2⟩ := toIcoMod_mem_Ico pi_pos a (θ k)
    refine ⟨lt_of_le_of_ne h1 fun h => ha ?_, h2⟩
    refine mem_image.mpr ⟨k, mem_univ _, ?_⟩
    have : θ k = a + n k * π := by rw [hθψ k, ← h]
    rw [this, ← zsmul_eq_mul, toIcoMod_add_zsmul, toIcoMod_eq_self]
    exact ⟨haI.1.le, by simpa using haI.2⟩
  have hψinj : Function.Injective ψ := fun j k hjk => by
    by_contra hne
    apply hθ j k hne (n j - n k)
    rw [hθψ j, hθψ k, hjk]; push_cast; ring
  -- sort the reduced angles: `s 0 < s 1 < ⋯ < s (D - 1)`
  set A : Finset ℝ := univ.image ψ
  have hA : A.card = 2 * r := by rw [card_image_of_injective _ hψinj, card_univ, Fintype.card_fin]
  set e := A.orderIsoOfFin hA
  set s : ℕ → ℝ := fun j => if h : j < 2 * r then (e ⟨j, h⟩ : ℝ) else 0
  have hsmono : ∀ j j', j' < 2 * r → j < j' → s j < s j' := fun j j' hj' hjj' => by
    simp only [s, dif_pos hj', dif_pos (hjj'.trans hj')]
    exact e.strictMono (Fin.mk_lt_mk.mpr hjj')
  have hsmono' : ∀ j j', j' < 2 * r → j ≤ j' → s j ≤ s j' := fun j j' hj' hjj' => by
    rcases hjj'.lt_or_eq with h | h
    · exact (hsmono j j' hj' h).le
    · rw [h]
  have hsrange : ∀ j < 2 * r, a < s j ∧ s j < a + π := fun j hj => by
    have hm := (e ⟨j, hj⟩).2
    obtain ⟨k, -, hk⟩ := mem_image.mp hm
    simp only [s, dif_pos hj, ← hk]
    exact hψa k
  -- the rank of each reduced angle
  set rankF : Fin (2 * r) → Fin (2 * r) := fun k => e.symm ⟨ψ k, mem_image_of_mem _ (mem_univ k)⟩
  have hsrank : ∀ k, s (rankF k) = ψ k := fun k => by
    simp only [s, dif_pos (rankF k).2, Fin.eta, rankF, OrderIso.apply_symm_apply]
  have hrankinj : Function.Injective rankF := fun j k h => by
    apply hψinj
    rw [← hsrank j, ← hsrank k, h]
  have hranksurj : Function.Surjective rankF := Finite.injective_iff_surjective.mp hrankinj
  -- thresholds `t 0 = a < s 0 < t 1 < s 1 < ⋯ < s (D - 1) < t D = a + π`
  set t : ℕ → ℝ := fun i => if i = 0 then a else if i < 2 * r then (s (i - 1) + s i) / 2
    else a + π
  have ht : ∀ i ≤ 2 * r, ∀ j < 2 * r, (s j < t i ↔ j < i) ∧ s j ≠ t i := fun i hi j hj => by
    have hj' := hsrange j hj
    by_cases h0 : i = 0
    · have ht0 : t i = a := by simp [t, h0]
      rw [ht0, h0]
      exact ⟨⟨fun h => absurd h (not_lt.mpr hj'.1.le), fun h => absurd h (Nat.not_lt_zero _)⟩,
        hj'.1.ne'⟩
    by_cases hlt : i < 2 * r
    · simp only [t, if_neg h0, if_pos hlt]
      have h1 := hsmono (i - 1) i hlt (by omega)
      rcases lt_or_ge j i with hji | hji
      · have := hsmono' j (i - 1) (by omega) (by omega)
        exact ⟨⟨fun _ => hji, fun _ => by linarith⟩, by intro h; linarith⟩
      · have := hsmono' i j hj hji
        exact ⟨⟨fun h => by linarith, fun h => by omega⟩, by intro h; linarith⟩
    · simp only [t, if_neg h0, if_neg hlt]
      exact ⟨⟨fun _ => by omega, fun _ => hj'.2⟩, hj'.2.ne⟩
  have htrange : ∀ i ≤ 2 * r, a ≤ t i ∧ t i ≤ a + π := fun i hi => by
    by_cases h0 : i = 0
    · simp only [t, if_pos h0]; constructor <;> linarith [pi_pos]
    by_cases hlt : i < 2 * r
    · simp only [t, if_neg h0, if_pos hlt]
      have := hsrange (i - 1) (by omega); have := hsrange i hlt
      constructor <;> linarith
    · simp only [t, if_neg h0, if_neg hlt]; constructor <;> linarith [pi_pos]
  -- the sign of `sin (θ_k - t_i)` in terms of ranks
  have hpos : ∀ i ≤ 2 * r, ∀ k, 0 < sin (θ k - t i) ↔ (i ≤ rankF k ↔ Even (n k)) :=
    fun i hi k => by
    have hk := ht i hi (rankF k) (rankF k).2
    rw [hsrank] at hk
    have hr := htrange i hi
    rw [sin_sub_pos_iff (hθψ k) (by linarith [(hψa k).1]) (by linarith [(hψa k).2]) hk.2]
    rw [show t i < ψ k ↔ i ≤ rankF k by
      rw [← not_lt, ← hk.1]; exact ⟨fun h h' => absurd h' (not_lt.mpr h.le), fun h =>
        lt_of_le_of_ne (not_lt.mp h) (Ne.symm hk.2)⟩]
  have hne : ∀ i ≤ 2 * r, ∀ k, sin (θ k - t i) ≠ 0 := fun i hi k => by
    have hk := ht i hi (rankF k) (rankF k).2
    rw [hsrank] at hk
    have hr := htrange i hi
    exact sin_sub_ne_zero (hθψ k) (by linarith [(hψa k).1]) (by linarith [(hψa k).2]) hk.2
  -- count in terms of ranks and apply the discrete intermediate value theorem
  set M : ℕ → ℤ := fun i => ∑ k, if (i ≤ rankF k ↔ Even (n k)) then 1 else 0
  have hNM : ∀ i ≤ 2 * r,
      ((univ.filter fun k => 0 < sin (θ k - t i)).card : ℤ) = M i := fun i hi => by
    rw [card_filter]; push_cast
    exact sum_congr rfl fun k _ => by simp only [hpos i hi k]
  have hstep : ∀ i < 2 * r, |M (i + 1) - M i| ≤ 1 := fun i hi => by
    obtain ⟨k₀, hk₀⟩ := hranksurj ⟨i, hi⟩
    simp only [M, ← sum_sub_distrib]
    rw [sum_eq_single k₀]
    · split_ifs <;> norm_num
    · intro k _ hk
      have : (rankF k : ℕ) ≠ i := fun h => hk (hrankinj (Fin.ext (by rw [h, hk₀])))
      have h1 : (i + 1 ≤ rankF k ↔ i ≤ rankF k) := by omega
      simp only [h1, sub_self]
    · simp
  have hsum : M 0 + M (2 * r) = 2 * r := by
    simp only [M, ← sum_add_distrib]
    rw [show (2 * r : ℤ) = ∑ _k : Fin (2 * r), (1 : ℤ) by simp]
    refine sum_congr rfl fun k _ => ?_
    have h2 : ¬ (2 * r ≤ (rankF k : ℕ)) := not_le.mpr (rankF k).2
    by_cases he : Even (n k) <;> simp [he, h2]
  obtain ⟨i, hi, hMi⟩ := exists_eq_of_step_le_one' M (2 * r) hstep (c := r) (by rw [hsum])
  refine ⟨-t i, fun k => by rw [← sub_eq_add_neg]; exact hne i hi k, ?_⟩
  have := hNM i hi
  simp only [← sub_eq_add_neg]
  omega

/-- Rotating `τ` by `α` puts it at angle `arg τ + α`. -/
theorem im_exp_mul (α : ℝ) (τ : ℂ) :
    (Complex.exp (α * Complex.I) * τ).im = ‖τ‖ * sin (Complex.arg τ + α) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I τ]
  rw [mul_left_comm, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add,
    Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, add_comm]

/-- Eq. 13, choice of `α*`: for nonzero `τ_k`, no two on a common line through the origin, some
rotation `e^{iα}` leaves no `τ_k` real and puts exactly half of them in the upper half-plane,
`N₊ = N₋ = D/2`. -/
theorem exists_rotation_half_upper {r : ℕ} (τ : Fin (2 * r) → ℂ) (hτ : ∀ k, τ k ≠ 0)
    (hline : ∀ j k, j ≠ k → ∀ z : ℤ, Complex.arg (τ j) - Complex.arg (τ k) ≠ z * π) :
    ∃ α : ℝ, (∀ k, (Complex.exp (α * Complex.I) * τ k).im ≠ 0) ∧
      (univ.filter fun k => 0 < (Complex.exp (α * Complex.I) * τ k).im).card = r := by
  obtain ⟨α, hne, hcard⟩ := exists_rotation_half_pos (fun k => Complex.arg (τ k)) hline
  have hn : ∀ k, 0 < ‖τ k‖ := fun k => norm_pos_iff.mpr (hτ k)
  refine ⟨α, fun k => ?_, ?_⟩
  · rw [im_exp_mul]; exact mul_ne_zero (hn k).ne' (hne k)
  · refine Eq.trans ?_ hcard
    congr 1
    ext k
    simp only [mem_filter, mem_univ, true_and, im_exp_mul]
    exact ⟨fun h => pos_of_mul_pos_right h (hn k).le, fun h => mul_pos (hn k) h⟩

end LeanUnitary.Pivot
