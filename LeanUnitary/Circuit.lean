import LeanUnitary.Spec
import LeanUnitary.Blocks

/-!
# Circuit algebra

Composition and embedding lemmas for `LeanUnitary.Spec.Circuit`, used to assemble the
decompositions into circuits and count their CNOTs.
-/

namespace LeanUnitary.Circuit

open LeanUnitary.Spec

variable {n : ℕ}

theorem denote_nil : Circuit.denote ([] : Circuit n) = 1 := rfl

theorem foldl_denote (c : Circuit n) (A : Op n) :
    c.foldl (fun acc g => g.denote * acc) A = c.denote * A := by
  induction c generalizing A with
  | nil => simp [Circuit.denote]
  | cons g c ih =>
    simp only [List.foldl_cons, Circuit.denote] at ih ⊢
    rw [ih, ih (g.denote * 1), mul_one, mul_assoc]

/-- Running `c₁` then `c₂` multiplies their matrices in reverse order. -/
theorem denote_append (c₁ c₂ : Circuit n) :
    Circuit.denote (c₁ ++ c₂) = c₂.denote * c₁.denote := by
  rw [Circuit.denote, List.foldl_append, ← Circuit.denote, foldl_denote]

theorem denote_singleton (g : Gate n) : Circuit.denote [g] = g.denote := by
  simp [Circuit.denote]

theorem denote_cons (g : Gate n) (c : Circuit n) :
    Circuit.denote (g :: c) = c.denote * g.denote := by
  rw [← List.singleton_append, denote_append, denote_singleton]

theorem cnotCount_append (c₁ c₂ : Circuit n) :
    Circuit.cnotCount (c₁ ++ c₂) = c₁.cnotCount + c₂.cnotCount := by
  simp [Circuit.cnotCount, List.countP_append]

/-- A gate on the lower `n` qubits of an `(n + 1)`-qubit register. -/
def Gate.lift : Gate n → Gate (n + 1)
  | .single q u => .single q.castSucc u
  | .cnot c t h => .cnot c.castSucc t.castSucc (by simpa using h)

/-- A circuit on the lower `n` qubits of an `(n + 1)`-qubit register. -/
def lift (c : Circuit n) : Circuit (n + 1) := c.map Gate.lift

/-! ## Lifting acts block-diagonally -/

/-- Two indices below `2^(n+1)` are equal iff they agree on the top bit and modulo `2^n`. -/
theorem eq_iff_top_and_mod {x y : ℕ} (hx : x < 2 ^ (n + 1)) (hy : y < 2 ^ (n + 1)) :
    x = y ↔ x.testBit n = y.testBit n ∧ x % 2 ^ n = y % 2 ^ n := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩
    rw [Blocks.testBit_top hx, Blocks.testBit_top hy] at h₁
    have hp : 0 < 2 ^ n := by positivity
    by_cases hxn : 2 ^ n ≤ x <;> by_cases hyn : 2 ^ n ≤ y <;> simp [hxn, hyn] at h₁
    · rw [Blocks.mod_top_of_le hx hxn, Blocks.mod_top_of_le hy hyn] at h₂; omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h₂; exact h₂

theorem testBit_mod_of_lt {x p : ℕ} (hp : p < n) : (x % 2 ^ n).testBit p = x.testBit p := by
  simp [Nat.testBit_mod_two_pow, hp]

theorem Gate.denote_lift (g : Gate n) :
    (Gate.lift g).denote = blockDiag g.denote g.denote := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  cases g with
  | single q u =>
    simp only [Gate.lift, Gate.denote, blockDiag]
    have hbit : ∀ k : Fin (2 ^ (n + 1)), bit k q.castSucc =
        bit (⟨k % 2 ^ n, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ n)) q := by
      intro k
      simp [bit, testBit_mod_of_lt q.isLt]
    have hcond : (∀ p : Fin (n + 1), p ≠ q.castSucc → (i : ℕ).testBit p = (j : ℕ).testBit p) ↔
        ((i : ℕ).testBit n = (j : ℕ).testBit n ∧ ∀ p : Fin n, p ≠ q →
          ((i : ℕ) % 2 ^ n).testBit p = ((j : ℕ) % 2 ^ n).testBit p) := by
      constructor
      · intro h
        refine ⟨h (Fin.last n) (by simp [Fin.ext_iff]; omega), fun p hp => ?_⟩
        rw [testBit_mod_of_lt p.isLt, testBit_mod_of_lt p.isLt]
        exact h p.castSucc (fun e => hp (Fin.castSucc_injective _ e))
      · rintro ⟨htop, h⟩ p hp
        by_cases hpn : (p : ℕ) < n
        · have := h ⟨p, hpn⟩ (fun e => hp (by rw [← e]; rfl))
          rwa [testBit_mod_of_lt hpn, testBit_mod_of_lt hpn] at this
        · have : (p : ℕ) = n := by have := p.isLt; omega
          rw [this]; exact htop
    simp only [ite_self]
    by_cases hc : ∀ p : Fin (n + 1), p ≠ q.castSucc → (i : ℕ).testBit p = (j : ℕ).testBit p
    · obtain ⟨htop, hlow⟩ := hcond.mp hc
      rw [if_pos hc, if_pos htop]
      rw [if_pos hlow, hbit, hbit]
    · rw [if_neg hc]
      by_cases htop : (i : ℕ).testBit n = (j : ℕ).testBit n
      · have hlow : ¬ ∀ p : Fin n, p ≠ q →
            ((i : ℕ) % 2 ^ n).testBit p = ((j : ℕ) % 2 ^ n).testBit p :=
          fun h => hc (hcond.mpr ⟨htop, h⟩)
        rw [if_pos htop]
        rw [if_neg hlow]
      · rw [if_neg htop]
  | cnot c t h =>
    simp only [Gate.lift, Gate.denote, blockDiag, Fin.val_castSucc, ite_self]
    set j' := if (j : ℕ).testBit c then (j : ℕ) ^^^ 2 ^ (t : ℕ) else (j : ℕ) with hj'
    have hxor_lt : (j : ℕ) ^^^ 2 ^ (t : ℕ) < 2 ^ (n + 1) :=
      Nat.xor_lt_two_pow hj (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hj'lt : j' < 2 ^ (n + 1) := by rw [hj']; split <;> assumption
    have htop' : j'.testBit n = (j : ℕ).testBit n := by
      rw [hj']; split
      · have : (t : ℕ) ≠ n := by omega
        rw [Nat.testBit_xor, Nat.testBit_two_pow]; simp [this]
      · rfl
    have hmod' : j' % 2 ^ n = if ((j : ℕ) % 2 ^ n).testBit c then ((j : ℕ) % 2 ^ n) ^^^ 2 ^ (t : ℕ)
        else (j : ℕ) % 2 ^ n := by
      rw [hj', testBit_mod_of_lt c.isLt]
      split
      · apply Nat.eq_of_testBit_eq; intro p
        simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
        by_cases hp : p < n
        · simp [hp]
        · have : (t : ℕ) ≠ p := by omega
          simp [hp, this]
      · rfl
    by_cases htop : (i : ℕ).testBit n = (j : ℕ).testBit n
    · rw [if_pos htop]
      have key : (i : ℕ) = j' ↔ (i : ℕ) % 2 ^ n = if ((j : ℕ) % 2 ^ n).testBit c then
          ((j : ℕ) % 2 ^ n) ^^^ 2 ^ (t : ℕ) else (j : ℕ) % 2 ^ n := by
        rw [eq_iff_top_and_mod hi hj'lt, htop', hmod']; simp [htop]
      by_cases e : (i : ℕ) = j'
      · rw [if_pos e]; exact (if_pos (key.mp e)).symm
      · rw [if_neg e]; exact (if_neg (mt key.mpr e)).symm
    · rw [if_neg htop, if_neg]
      intro e; apply htop; rw [e, htop']

/-- A circuit on the lower qubits acts the same whatever the top qubit is. -/
theorem denote_lift (c : Circuit n) : (lift c).denote = blockDiag c.denote c.denote := by
  induction c with
  | nil =>
    simp only [lift, List.map_nil, denote_nil, Blocks.blockDiag_eq]
    rw [Matrix.fromBlocks_one]; simp [Blocks.ofBlocks]
  | cons g c ih =>
    rw [lift, List.map_cons, denote_cons, ← lift, ih, Gate.denote_lift, denote_cons,
      Blocks.blockDiag_eq, Blocks.blockDiag_eq, Blocks.blockDiag_eq, Blocks.ofBlocks_mul,
      Matrix.fromBlocks_multiply]
    simp

theorem cnotCount_lift (c : Circuit n) : (lift c).cnotCount = c.cnotCount := by
  simp only [lift, Circuit.cnotCount, List.countP_map]
  congr 1
  funext g
  cases g <;> rfl

end LeanUnitary.Circuit
