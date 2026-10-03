import Mathlib

/-!
# CX count of the pivot decomposition

Arithmetic of `submission/decomposition.tex`, Sec. II.D. Block-ZXZ satisfies
`c_n = 4 c_{n-1} + 3 · 2^{n-1} - 5` (arXiv:2403.13692, Sec. 5.3). The pivot merges one more CX
at each recursion node (Eq. 18):

    c_n = 4 c_{n-1} + 3 · 2^{n-1} - 6,    c_2 = 3,

so `c_n = (21/48) 4^n - (3/2) 2^n + 2`, against `(22/48) 4^n - (3/2) 2^n + 5/3` for Block-ZXZ, a
saving of `Δ_n = (4^{n-2} - 1) / 3` (Eq. 19).

The closed forms are stated in the shape of `LeanUnitary.Spec.BlockZXZ`'s bound, so that once the
construction is proved, `count_eq` gives a `GeneralBound` with
`f n = (21 * 4 ^ n - 72 * 2 ^ n + 96) / 48`.
-/

namespace LeanUnitary.Pivot

/-- `4 · 2^n ≤ 4^n` for `n ≥ 2`, so the closed forms below involve no truncated subtraction. -/
theorem four_mul_two_pow_le (n : ℕ) (hn : 2 ≤ n) : 4 * 2 ^ n ≤ 4 ^ n := by
  have h : 4 ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have h2 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [h]
  exact Nat.mul_le_mul_right _ h2

/-- The Block-ZXZ count, `c_n = 4 c_{n-1} + 3 · 2^{n-1} - 5` with `c_2 = 3`. -/
def zxzCount : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 3
  | n + 3 => 4 * zxzCount (n + 2) + 3 * 2 ^ (n + 2) - 5

/-- The pivot count, Eq. 18: `c_n = 4 c_{n-1} + 3 · 2^{n-1} - 6` with `c_2 = 3`. -/
def count : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 3
  | n + 3 => 4 * count (n + 2) + 3 * 2 ^ (n + 2) - 6

/-- Closed form of the Block-ZXZ count: `48 c_n = 22 · 4^n - 72 · 2^n + 80`. -/
theorem zxzCount_closed (n : ℕ) (hn : 2 ≤ n) : 48 * zxzCount n + 72 * 2 ^ n = 22 * 4 ^ n + 80 := by
  induction n, hn using Nat.le_induction with
  | base => simp [zxzCount]
  | succ n hn ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [zxzCount]
    have h2 : 2 ^ (k + 2 + 1) = 2 * 2 ^ (k + 2) := by ring
    have h4 : 4 ^ (k + 2 + 1) = 4 * 4 ^ (k + 2) := by ring
    have hpos : 4 ≤ 2 ^ (k + 2) := by
      rw [pow_add]; have := Nat.one_le_two_pow (n := k); omega
    rw [h2, h4]
    omega

/-- Closed form of the pivot count: `48 c_n = 21 · 4^n - 72 · 2^n + 96`. -/
theorem count_closed (n : ℕ) (hn : 2 ≤ n) : 48 * count n + 72 * 2 ^ n = 21 * 4 ^ n + 96 := by
  induction n, hn using Nat.le_induction with
  | base => simp [count]
  | succ n hn ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [count]
    have h2 : 2 ^ (k + 2 + 1) = 2 * 2 ^ (k + 2) := by ring
    have h4 : 4 ^ (k + 2 + 1) = 4 * 4 ^ (k + 2) := by ring
    have hpos : 4 ≤ 2 ^ (k + 2) := by
      rw [pow_add]; have := Nat.one_le_two_pow (n := k); omega
    rw [h2, h4]
    omega

/-- The Block-ZXZ count is the bound of `LeanUnitary.Spec.BlockZXZ`. -/
theorem zxzCount_eq (n : ℕ) (hn : 2 ≤ n) :
    zxzCount n = (22 * 4 ^ n - 72 * 2 ^ n + 80) / 48 := by
  have := zxzCount_closed n hn
  have := four_mul_two_pow_le n hn
  omega

/-- The pivot count as an explicit bound, `(21/48) 4^n - (3/2) 2^n + 2`. -/
theorem count_eq (n : ℕ) (hn : 2 ≤ n) : count n = (21 * 4 ^ n - 72 * 2 ^ n + 96) / 48 := by
  have := count_closed n hn
  have := four_mul_two_pow_le n hn
  omega

/-- Eq. 19: the pivot saves `Δ_n = (4^{n-2} - 1) / 3` CX gates over Block-ZXZ, one per
recursion node. -/
theorem saving (n : ℕ) (hn : 2 ≤ n) :
    count n ≤ zxzCount n ∧ 3 * (zxzCount n - count n) = 4 ^ (n - 2) - 1 := by
  have h1 := count_closed n hn
  have h2 := zxzCount_closed n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h4 : 4 ^ (k + 2) = 16 * 4 ^ k := by ring
  have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.add_sub_cancel]
  omega

/-- The saving recursion `Δ_n = 4 Δ_{n-1} + 1`, `Δ_2 = 0`: one extra merge per node. -/
theorem saving_succ (n : ℕ) (hn : 2 ≤ n) :
    zxzCount (n + 1) - count (n + 1) = 4 * (zxzCount n - count n) + 1 := by
  have h := (saving n hn).2
  have h' := (saving (n + 1) (by omega)).2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h4 : 4 ^ (k + 2 + 1 - 2) = 4 * 4 ^ (k + 2 - 2) := by
    rw [show k + 2 + 1 - 2 = k + 1 by omega, show k + 2 - 2 = k by omega, pow_succ]; ring
  have hpos : 1 ≤ 4 ^ (k + 2 - 2) := Nat.one_le_pow _ _ (by norm_num)
  omega

end LeanUnitary.Pivot
