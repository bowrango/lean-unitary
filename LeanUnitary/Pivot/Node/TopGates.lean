import LeanUnitary.Circuit
import LeanUnitary.Pivot.Path.Gate

/-!
# Gates on the top qubit

The gates of the Block-ZXZ node that act on the top qubit `n` of an `(n + 1)`-qubit register:
`R_z` and Hadamard on the top qubit, and CNOTs from a lower control onto it. Each is a
multiplexor on the top qubit (`Spec.mux (Fin.last n)`), i.e. a `2 × 2` matrix for each basis state
`x` of the lower qubits, and multiplexors multiply pointwise in `x` (`mux_mul`). This turns the
circuit algebra of the node into `2 × 2` matrix identities.
-/

namespace LeanUnitary.Pivot.Node

open LeanUnitary.Spec LeanUnitary.Blocks Matrix

variable {n : ℕ}

/-! ## Single-qubit matrices -/

/-- Pauli `X`. -/
def σX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- `X^b`. -/
def xpow (b : Bool) : Matrix (Fin 2) (Fin 2) ℂ := if b then σX else 1

/-- The Hadamard gate. -/
noncomputable def had : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹; (Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹]

theorem Ry_zero : Ry 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Ry]

theorem Rz_mem (a : ℝ) : Rz a ∈ unitaryGroup (Fin 2) ℂ := by
  have := Pivot.gate_mem_unitaryGroup a 0
  rwa [Pivot.gate, Ry_zero, Matrix.mul_one] at this

theorem had_mem : had ∈ unitaryGroup (Fin 2) ℂ := by
  have hs : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs' : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = 1 / 2 := by rw [inv_pow, hs]; norm_num
  rw [mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [had, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp [hs']

theorem Rz_mul_Rz (a b : ℝ) : Rz a * Rz b = Rz (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
    <;> ring_nf

theorem Rz_zero : Rz 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Rz]

theorem σX_mul_σX : σX * σX = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σX, Matrix.mul_apply, Fin.sum_univ_two]

theorem σX_mul_Rz (a : ℝ) : σX * Rz a = Rz (-a) * σX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σX, Rz, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf

theorem xpow_mul_xpow_self (b : Bool) : xpow b * xpow b = 1 := by
  cases b <;> simp [xpow, σX_mul_σX]

theorem xpow_comm (b c : Bool) : xpow b * xpow c = xpow c * xpow b := by
  cases b <;> cases c <;> simp [xpow]

/-- `X^c R_z(a) = R_z(±a) X^c`. -/
theorem xpow_mul_Rz (c : Bool) (a : ℝ) : xpow c * Rz a = Rz (if c then -a else a) * xpow c := by
  cases c <;> simp [xpow, σX_mul_Rz]

theorem Rz_mul_xpow (c : Bool) (a : ℝ) : Rz a * xpow c = xpow c * Rz (if c then -a else a) := by
  cases c
  · simp [xpow]
  · simp only [xpow, if_true]; rw [σX_mul_Rz, neg_neg]

/-! ## Multiplexors on the top qubit -/

/-- Multiplexors on the top qubit multiply pointwise. -/
theorem mux_mul (f g : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    mux (Fin.last n) f * mux (Fin.last n) g = mux (Fin.last n) fun k => f k * g k := by
  rw [mux_last_eq, mux_last_eq, mux_last_eq, ofBlocks_mul, fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, diagonal_add, Matrix.mul_apply, Fin.sum_univ_two]

theorem mux_const_one : mux (Fin.last n) (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  rw [mux_last_eq]
  simp only [one_apply_eq, one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    one_apply_ne (by decide : (1 : Fin 2) ≠ 0), diagonal_zero, diagonal_one, fromBlocks_one]
  simp [ofBlocks]

theorem mux_congr {f g : ℕ → Matrix (Fin 2) (Fin 2) ℂ} (h : ∀ k < 2 ^ n, f k = g k) :
    mux (Fin.last n) f = mux (Fin.last n) g := by
  have h' : ∀ k : Fin (2 ^ n), f k = g k := fun k => h k k.isLt
  rw [mux_last_eq, mux_last_eq]
  simp only [h']

/-! ## The gates -/

/-- `R_z(a)` on the top qubit. -/
noncomputable def rzTop (n : ℕ) (a : ℝ) : Gate (n + 1) := .single (Fin.last n) ⟨Rz a, Rz_mem a⟩

/-- The Hadamard gate on the top qubit. -/
noncomputable def hTop (n : ℕ) : Gate (n + 1) := .single (Fin.last n) ⟨had, had_mem⟩

/-- CNOT from the lower qubit `c` onto the top qubit. -/
def cxTop {n : ℕ} (c : Fin n) : Gate (n + 1) :=
  .cnot c.castSucc (Fin.last n) (by simp [Fin.ext_iff]; omega)

theorem denote_single_last (u : unitaryGroup (Fin 2) ℂ) :
    (Gate.single (Fin.last n) u).denote =
      mux (Fin.last n) fun _ => (u : Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

theorem denote_rzTop (a : ℝ) : (rzTop n a).denote = mux (Fin.last n) fun _ => Rz a := rfl

theorem denote_hTop : (hTop n).denote = mux (Fin.last n) fun _ => had := rfl

theorem denote_cxTop (c : Fin n) :
    (cxTop c).denote = mux (Fin.last n) fun k => xpow (k.testBit c) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [mux_last_eq, ofBlocks_apply, topSplit_apply, topSplit_apply]
  simp only [cxTop, Gate.denote, Fin.val_castSucc, Fin.val_last]
  have hxor_lt : (j : ℕ) ^^^ 2 ^ n < 2 ^ (n + 1) :=
    Nat.xor_lt_two_pow hj (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hxtop : ((j : ℕ) ^^^ 2 ^ n).testBit n = !(j : ℕ).testBit n := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow_self]; simp
  have hxmod : ((j : ℕ) ^^^ 2 ^ n) % 2 ^ n = (j : ℕ) % 2 ^ n := by
    apply Nat.eq_of_testBit_eq; intro p
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
    by_cases hp : p < n
    · have : n ≠ p := by omega
      simp [hp, this]
    · simp [hp]
  by_cases hb : (j : ℕ).testBit c
  · -- flip the top bit
    rw [if_pos hb]
    have key : (i : ℕ) = (j : ℕ) ^^^ 2 ^ n ↔
        (i : ℕ).testBit n = !(j : ℕ).testBit n ∧ (i : ℕ) % 2 ^ n = (j : ℕ) % 2 ^ n := by
      rw [Circuit.eq_iff_top_and_mod hi hxor_lt, hxtop, hxmod]
    by_cases hm : (i : ℕ) % 2 ^ n = (j : ℕ) % 2 ^ n
    · by_cases ti : (i : ℕ).testBit n <;> by_cases tj : (j : ℕ).testBit n <;>
        simp [ti, tj, hm, key, hb, xpow, σX, diagonal_apply_eq]
    · by_cases ti : (i : ℕ).testBit n <;> by_cases tj : (j : ℕ).testBit n <;>
        simp [ti, tj, hm, key]
  · rw [if_neg hb]
    have key : (i : ℕ) = (j : ℕ) ↔
        (i : ℕ).testBit n = (j : ℕ).testBit n ∧ (i : ℕ) % 2 ^ n = (j : ℕ) % 2 ^ n :=
      Circuit.eq_iff_top_and_mod hi hj
    by_cases hm : (i : ℕ) % 2 ^ n = (j : ℕ) % 2 ^ n
    · by_cases ti : (i : ℕ).testBit n <;> by_cases tj : (j : ℕ).testBit n <;>
        simp [ti, tj, hm, key, hb, xpow, diagonal_apply_eq]
    · by_cases ti : (i : ℕ).testBit n <;> by_cases tj : (j : ℕ).testBit n <;>
        simp [ti, tj, hm, key]

theorem cnotCount_hTop : Circuit.cnotCount [hTop n] = 0 := rfl
theorem cnotCount_cxTop (c : Fin n) : Circuit.cnotCount [cxTop c] = 1 := rfl

end LeanUnitary.Pivot.Node
