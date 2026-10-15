import LeanUnitary.Pivot.Node.TopGates

/-!
# The Gray-code multiplexed rotation

A multiplexed `R_z` on the top qubit, `mux(θ) = ⊕_x R_z(θ_x)`, with `2^n` CNOTs (Möttönen et al.;
the paper, Eq. 2 and Fig. 2). Peeling the control bit `m` gives
`mux_{m+1}(θ) = CX_m · mux_m(θ⁻) · CX_m · mux_m(θ⁺)`, with
`θ^± = (θ|_{bit m = 0} ± θ|_{bit m = 1})/2`;
running the second sub-multiplexor in reverse cancels the CNOTs at the junction. The circuit
`core m θ` is `mux_m(θ)` without its final CNOT, as an explicit gate list:

    core 0 θ       = [R_z(θ₀)]
    core (m + 1) θ = core m θ⁺ ++ [CX_m] ++ reverse (core m θ⁻)

This module proves

* `grayMux_denote`, `grayMuxRev_denote`: `core n θ ++ [CX_{n-1}]` and its mirror
  `[CX_{n-1}] ++ reverse (core n θ)` both implement `mux(θ)`, with `2^n` CNOTs;
* `core_split`: for `n ≥ 2` the circuit ends with `CX_0, R_z(φ)` where `φ` is the mean of `θ⁻`
  (`firstAngle_eq`), the final angle of Eq. 3. When `φ = 0` the last three gates are
  `CX_0, I, CX_{n-1}`, the two CNOTs the pivot merges.

All gates are multiplexors on the top qubit, so correctness is a `2 × 2` identity per basis
state `x` of the controls (`TopGates.mux_mul`).
-/

namespace LeanUnitary.Pivot.Node

open LeanUnitary.Spec LeanUnitary.Circuit

variable {n : ℕ}

/-- `θ⁺` when peeling control bit `m`. -/
noncomputable def plus (m : ℕ) (θ : ℕ → ℝ) (y : ℕ) : ℝ :=
  (θ (y % 2 ^ m) + θ (y % 2 ^ m + 2 ^ m)) / 2

/-- `θ⁻` when peeling control bit `m`. -/
noncomputable def minus (m : ℕ) (θ : ℕ → ℝ) (y : ℕ) : ℝ :=
  (θ (y % 2 ^ m) - θ (y % 2 ^ m + 2 ^ m)) / 2

/-- The Gray-code multiplexor on control bits `< m` without its final CNOT. -/
noncomputable def core (n : ℕ) : (m : ℕ) → m ≤ n → (ℕ → ℝ) → Circuit (n + 1)
  | 0, _, θ => [rzTop n (θ 0)]
  | m + 1, hm, θ =>
    core n m (by omega) (plus m θ) ++ [cxTop ⟨m, by omega⟩] ++
      (core n m (by omega) (minus m θ)).reverse

/-- The control bit flipped by the final CNOT of `mux_m`. -/
def topb : ℕ → ℕ → Bool
  | 0, _ => false
  | m + 1, x => x.testBit m

theorem mod_two_pow_succ (x m : ℕ) :
    x % 2 ^ (m + 1) = x % 2 ^ m + if x.testBit m then 2 ^ m else 0 := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_two_eq_zero_or_one (x / 2 ^ m)
  rcases h with h | h <;> simp [h, mul_comm]

/-- The per-basis-state identity behind one recursion step. -/
theorem step_identity (θ : ℕ → ℝ) (m x : ℕ) (b : Bool) :
    (Rz (minus m θ (x % 2 ^ m)) * xpow b) *
        (xpow (x.testBit m) * (xpow b * Rz (plus m θ (x % 2 ^ m))))
      = xpow (x.testBit m) * Rz (θ (x % 2 ^ (m + 1))) ∧
    (Rz (plus m θ (x % 2 ^ m)) * xpow b) *
        (xpow (x.testBit m) * (xpow b * Rz (minus m θ (x % 2 ^ m))))
      = Rz (θ (x % 2 ^ (m + 1))) * xpow (x.testBit m) := by
  have hx : xpow b * (xpow (x.testBit m) * xpow b) = xpow (x.testBit m) := by
    rw [← mul_assoc, xpow_comm b, mul_assoc, xpow_mul_xpow_self, mul_one]
  have e1 : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, (A * xpow b) * (xpow (x.testBit m) * (xpow b * B)) =
      A * xpow (x.testBit m) * B := by
    intro A B
    calc (A * xpow b) * (xpow (x.testBit m) * (xpow b * B))
        = A * (xpow b * (xpow (x.testBit m) * xpow b)) * B := by simp only [mul_assoc]
      _ = A * xpow (x.testBit m) * B := by rw [hx]
  have hθ : ∀ s : ℝ, s = (if x.testBit m then -minus m θ (x % 2 ^ m) else minus m θ (x % 2 ^ m)) →
      s + plus m θ (x % 2 ^ m) = θ (x % 2 ^ (m + 1)) ∧
      plus m θ (x % 2 ^ m) + s = θ (x % 2 ^ (m + 1)) := by
    rintro s rfl
    rw [mod_two_pow_succ]
    simp only [plus, minus, Nat.mod_mod]
    by_cases hb : x.testBit m
    · simp only [hb, if_true]; constructor <;> ring
    · simp only [hb, if_false, Bool.false_eq_true, add_zero]; constructor <;> ring
  obtain ⟨h1, h2⟩ := hθ _ rfl
  constructor
  · rw [e1, Rz_mul_xpow, mul_assoc, Rz_mul_Rz, h1]
  · rw [e1, mul_assoc, xpow_mul_Rz, ← mul_assoc, Rz_mul_Rz, h2]

/-- `core m θ` is `X^{topb} R_z(θ)` per basis state, and its reverse is `R_z(θ) X^{topb}`. -/
theorem core_denote (m : ℕ) (hm : m ≤ n) (θ : ℕ → ℝ) :
    (core n m hm θ).denote = mux (Fin.last n) (fun x => xpow (topb m x) * Rz (θ (x % 2 ^ m))) ∧
    Circuit.denote (core n m hm θ).reverse =
      mux (Fin.last n) (fun x => Rz (θ (x % 2 ^ m)) * xpow (topb m x)) := by
  induction m generalizing θ with
  | zero =>
    simp only [core, denote_singleton, denote_rzTop, topb, xpow,
      pow_zero, Nat.mod_one, Bool.false_eq_true, if_false, one_mul, mul_one]
    refine ⟨?_, ?_⟩ <;> first | trivial | rfl | (rw [List.reverse_singleton, denote_singleton]; rfl)
  | succ m ih =>
    obtain ⟨hp1, -⟩ := ih (by omega) (plus m θ)
    obtain ⟨-, hm2⟩ := ih (by omega) (minus m θ)
    obtain ⟨hp1', -⟩ := ih (by omega) (minus m θ)
    obtain ⟨-, hm2'⟩ := ih (by omega) (plus m θ)
    constructor
    · simp only [core]
      rw [denote_append, denote_append, denote_singleton, hm2, denote_cxTop, hp1, mux_mul, mux_mul]
      congr 1; funext x
      simpa only [mul_assoc, topb] using (step_identity θ m x (topb m x)).1
    · simp only [core, List.reverse_append, List.reverse_reverse, List.reverse_singleton]
      rw [denote_append, denote_append, denote_singleton, hm2', denote_cxTop, hp1', mux_mul,
        mux_mul]
      congr 1; funext x
      simpa only [mul_assoc, topb] using (step_identity θ m x (topb m x)).2

theorem cnotCount_reverse (c : Circuit n) : Circuit.cnotCount c.reverse = c.cnotCount := by
  simp [Circuit.cnotCount]

theorem cnotCount_core (m : ℕ) (hm : m ≤ n) (θ : ℕ → ℝ) :
    (core n m hm θ).cnotCount = 2 ^ m - 1 := by
  induction m generalizing θ with
  | zero => rfl
  | succ m ih =>
    simp only [core]
    rw [cnotCount_append, cnotCount_append, cnotCount_reverse, ih, ih, cnotCount_cxTop]
    have := Nat.one_le_two_pow (n := m)
    rw [pow_succ]; omega

/-! ## The full multiplexor -/

/-- The Gray-code multiplexor `mux(θ)` on all `n` controls. -/
noncomputable def grayMux (n : ℕ) (hn : 0 < n) (θ : ℕ → ℝ) : Circuit (n + 1) :=
  core n n le_rfl θ ++ [cxTop ⟨n - 1, by omega⟩]

/-- The mirrored Gray-code multiplexor, which starts with its CNOT on the top control. -/
noncomputable def grayMuxRev (n : ℕ) (hn : 0 < n) (θ : ℕ → ℝ) : Circuit (n + 1) :=
  [cxTop ⟨n - 1, by omega⟩] ++ (core n n le_rfl θ).reverse

theorem topb_of_pos {m : ℕ} (hm : 0 < m) (x : ℕ) : topb m x = x.testBit (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rfl

theorem grayMux_denote (hn : 0 < n) (θ : ℕ → ℝ) :
    (grayMux n hn θ).denote = mux (Fin.last n) fun x => Rz (θ x) := by
  rw [grayMux, denote_append, denote_singleton, denote_cxTop, (core_denote n le_rfl θ).1, mux_mul]
  apply mux_congr
  intro x hx
  simp only [topb_of_pos hn, ← mul_assoc, xpow_mul_xpow_self, one_mul,
    Nat.mod_eq_of_lt hx]

theorem grayMuxRev_denote (hn : 0 < n) (θ : ℕ → ℝ) :
    (grayMuxRev n hn θ).denote = mux (Fin.last n) fun x => Rz (θ x) := by
  rw [grayMuxRev, denote_append, denote_singleton, denote_cxTop, (core_denote n le_rfl θ).2,
    mux_mul]
  apply mux_congr
  intro x hx
  simp only [topb_of_pos hn, mul_assoc, xpow_mul_xpow_self, mul_one,
    Nat.mod_eq_of_lt hx]

theorem cnotCount_grayMux (hn : 0 < n) (θ : ℕ → ℝ) : (grayMux n hn θ).cnotCount = 2 ^ n := by
  rw [grayMux, cnotCount_append, cnotCount_core, cnotCount_cxTop]
  have := Nat.one_le_two_pow (n := n); omega

/-! ## The final angle -/

/-- The first rotation angle of `core m θ`, the mean of `θ` (`firstAngle_eq`). -/
noncomputable def firstAngle : ℕ → (ℕ → ℝ) → ℝ
  | 0, θ => θ 0
  | m + 1, θ => firstAngle m (plus m θ)

theorem firstAngle_eq (m : ℕ) (θ : ℕ → ℝ) :
    firstAngle m θ = (∑ x ∈ Finset.range (2 ^ m), θ x) / 2 ^ m := by
  induction m generalizing θ with
  | zero => simp [firstAngle]
  | succ m ih =>
    rw [firstAngle, ih, pow_succ, mul_two, Finset.sum_range_add]
    have : ∀ y ∈ Finset.range (2 ^ m), plus m θ y = (θ y + θ (2 ^ m + y)) / 2 := by
      intro y hy
      rw [plus, Nat.mod_eq_of_lt (Finset.mem_range.mp hy), add_comm y]
    rw [Finset.sum_congr rfl this, ← Finset.sum_div, Finset.sum_add_distrib]
    field_simp
    ring

/-- `core m θ` starts with `R_z(firstAngle m θ)`, then (for `m ≥ 1`) `CX_0`. -/
theorem core_head (m : ℕ) (hm : m ≤ n) (θ : ℕ → ℝ) (hm1 : 1 ≤ m) :
    ∃ tl : Circuit (n + 1), core n m hm θ =
      rzTop n (firstAngle m θ) :: cxTop ⟨0, by omega⟩ :: tl := by
  induction m generalizing θ with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact ⟨[rzTop n (minus 0 θ 0)], by simp [core, firstAngle]⟩
    · obtain ⟨tl, htl⟩ := ih (by omega) (plus m θ) hpos
      refine ⟨tl ++ [cxTop ⟨m, by omega⟩] ++ (core n m (by omega) (minus m θ)).reverse, ?_⟩
      simp only [core, htl, firstAngle, List.cons_append, List.append_assoc]

/-- For `n ≥ 2`, the Gray-code multiplexor ends with `CX_0`, `R_z(φ)`, `CX_{n-1}`, where
`φ = firstAngle (n - 1) θ⁻` is the final angle of Eq. 3. -/
theorem core_split (m : ℕ) (θ : ℕ → ℝ) :
    ∃ R : Circuit (m + 2 + 1), core (m + 2) (m + 2) le_rfl θ =
      R ++ [cxTop ⟨0, by omega⟩, rzTop (m + 2) (firstAngle (m + 1) (minus (m + 1) θ))] ∧
      R.cnotCount = 2 ^ (m + 2) - 2 := by
  obtain ⟨tl, htl⟩ := core_head (n := m + 2) (m + 1) (by omega) (minus (m + 1) θ) (by omega)
  refine ⟨core (m + 2) (m + 1) (by omega) (plus (m + 1) θ) ++ [cxTop ⟨m + 1, by omega⟩] ++
    tl.reverse, ?_, ?_⟩
  · rw [core, htl]
    simp [List.reverse_cons, List.append_assoc]
  · have hc := cnotCount_core (n := m + 2) (m + 1) (by omega) (minus (m + 1) θ)
    rw [htl] at hc
    have hc' : tl.cnotCount = 2 ^ (m + 1) - 2 := by
      simp only [Circuit.cnotCount, List.countP_cons] at hc ⊢
      simp [rzTop, cxTop, Gate.isCnot] at hc
      omega
    rw [cnotCount_append, cnotCount_append, cnotCount_reverse, hc', cnotCount_core,
      cnotCount_cxTop]
    have := Nat.one_le_two_pow (n := m + 1)
    have h2 : 2 ≤ 2 ^ (m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ 2 (m + 1)]; omega

end LeanUnitary.Pivot.Node
