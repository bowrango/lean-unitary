import LeanUnitary.Spec

/-!
# Bridge to Mathlib block matrices

The spec indexes `n + 1` qubits by bits of `Fin (2 ^ (n + 1))`, with the top qubit (`n`) as the
most significant bit. Mathlib's block-matrix API (`Matrix.fromBlocks`, `Matrix.fromBlocks_multiply`,
`Matrix.fromBlocks_diagonal`, …) works over `Fin (2 ^ n) ⊕ Fin (2 ^ n)`. `topSplit` identifies
the two: top qubit `0` ↦ `inl`, top qubit `1` ↦ `inr`, lower qubits ↦ the index inside the block.

Prove these bridges once, then do the decompositions' algebra with Mathlib's block lemmas
instead of bit arithmetic.
-/

namespace LeanUnitary.Blocks

open LeanUnitary.Spec Matrix

/-- Split an `(n + 1)`-qubit basis index by its top qubit. -/
def topSplit (n : ℕ) : Fin (2 ^ (n + 1)) ≃ Fin (2 ^ n) ⊕ Fin (2 ^ n) :=
  (finCongr (by rw [pow_succ, mul_two])).trans finSumFinEquiv.symm

/-- Reindex a block matrix to an operator on `n + 1` qubits. -/
abbrev ofBlocks {n : ℕ} (M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℂ) :
    Op (n + 1) :=
  reindex (topSplit n).symm (topSplit n).symm M

/-! ## The top bit of a basis index -/

/-- Below `2^(n+1)`, the top bit is set exactly from `2^n` on. -/
theorem testBit_top {n i : ℕ} (hi : i < 2 ^ (n + 1)) : i.testBit n = decide (2 ^ n ≤ i) := by
  by_cases h : 2 ^ n ≤ i
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
    have hr : r < 2 ^ n := by rw [pow_succ] at hi; omega
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]
    simp
  · rw [Nat.testBit_lt_two_pow (by omega)]
    simp [h]

theorem mod_top_of_le {n i : ℕ} (hi : i < 2 ^ (n + 1)) (h : 2 ^ n ≤ i) :
    i % 2 ^ n = i - 2 ^ n := by
  rw [pow_succ] at hi
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

theorem topSplit_symm_inl {n : ℕ} (k : Fin (2 ^ n)) :
    ((topSplit n).symm (Sum.inl k) : ℕ) = k := by
  simp [topSplit]

theorem topSplit_symm_inr {n : ℕ} (k : Fin (2 ^ n)) :
    ((topSplit n).symm (Sum.inr k) : ℕ) = 2 ^ n + k := by
  simp [topSplit, add_comm]

/-- `topSplit` reads off the top bit and the index modulo `2^n`. -/
theorem topSplit_apply {n : ℕ} (k : Fin (2 ^ (n + 1))) : topSplit n k =
    if (k : ℕ).testBit n then Sum.inr ⟨k % 2 ^ n, Nat.mod_lt _ (by positivity)⟩
      else Sum.inl ⟨k % 2 ^ n, Nat.mod_lt _ (by positivity)⟩ := by
  rw [testBit_top k.isLt]
  by_cases h : 2 ^ n ≤ (k : ℕ)
  · rw [if_pos (by simpa using h), ← Equiv.eq_symm_apply]
    have := mod_top_of_le k.isLt h
    exact Fin.ext (by rw [topSplit_symm_inr]; exact (by omega : (k : ℕ) = 2 ^ n + (k : ℕ) % 2 ^ n))
  · rw [if_neg (by simpa using h), ← Equiv.eq_symm_apply]
    have : (k : ℕ) % 2 ^ n = k := Nat.mod_eq_of_lt (by omega)
    exact Fin.ext (by rw [topSplit_symm_inl]; exact (by omega : (k : ℕ) = (k : ℕ) % 2 ^ n))

theorem ofBlocks_apply {n : ℕ}
    (M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℂ)
    (i j : Fin (2 ^ (n + 1))) : ofBlocks M i j = M (topSplit n i) (topSplit n j) := by
  simp [ofBlocks, reindex_apply]

/-- `Spec.blockDiag A B` is the block matrix `[A 0; 0 B]`. -/
theorem blockDiag_eq {n : ℕ} (A B : Op n) : Spec.blockDiag A B = ofBlocks (fromBlocks A 0 0 B) := by
  ext i j
  rw [ofBlocks_apply, topSplit_apply, topSplit_apply, Spec.blockDiag]
  by_cases hi : (i : ℕ).testBit n <;> by_cases hj : (j : ℕ).testBit n <;> simp [hi, hj]

theorem clearBit_last {n : ℕ} (i : Fin (2 ^ (n + 1))) : clearBit i n = i % 2 ^ n := by
  rw [clearBit, testBit_top i.isLt]
  by_cases h : 2 ^ n ≤ (i : ℕ)
  · rw [if_pos (by simpa using h), mod_top_of_le i.isLt h]
  · rw [if_neg (by simpa using h), Nat.mod_eq_of_lt (by omega)]

/-- Two indices agree on every qubit below the top one iff they agree modulo `2^n`. -/
theorem forall_testBit_eq_iff {n : ℕ} (i j : Fin (2 ^ (n + 1))) :
    (∀ p : Fin (n + 1), p ≠ Fin.last n → (i : ℕ).testBit p = (j : ℕ).testBit p) ↔
      (i : ℕ) % 2 ^ n = (j : ℕ) % 2 ^ n := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hp : p < n
    · simp only [hp, decide_true, Bool.true_and]
      exact h ⟨p, by omega⟩ (by simp [Fin.ext_iff]; omega)
    · simp [hp]
  · intro h p hp
    have hp' : (p : ℕ) < n := by
      have := p.isLt
      have : (p : ℕ) ≠ n := fun e => hp (Fin.ext (by simpa using e))
      omega
    have := congrArg (fun x => x.testBit p) h
    simpa [Nat.testBit_mod_two_pow, hp'] using this

/-- A multiplexor on the top qubit is a 2 × 2 block matrix of diagonals. -/
theorem mux_last_eq {n : ℕ} (u : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    mux (Fin.last n) u =
      ofBlocks (fromBlocks (diagonal fun k => u k 0 0) (diagonal fun k => u k 0 1)
        (diagonal fun k => u k 1 0) (diagonal fun k => u k 1 1)) := by
  ext i j
  rw [ofBlocks_apply, topSplit_apply, topSplit_apply, mux]
  simp only [forall_testBit_eq_iff, Fin.val_last, clearBit_last, bit]
  by_cases hij : (i : ℕ) % 2 ^ n = (j : ℕ) % 2 ^ n
  · by_cases hi : (i : ℕ).testBit n <;> by_cases hj : (j : ℕ).testBit n <;>
      simp [hi, hj, hij, diagonal_apply_eq]
  · by_cases hi : (i : ℕ).testBit n <;> by_cases hj : (j : ℕ).testBit n <;>
      simp [hi, hj, hij]

theorem ofBlocks_mul {n : ℕ}
    (M N : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℂ) :
    ofBlocks M * ofBlocks N = ofBlocks (M * N) := by
  simp [ofBlocks, reindex_apply, submatrix_mul_equiv]

end LeanUnitary.Blocks
