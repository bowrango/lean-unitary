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

/-- `Spec.blockDiag A B` is the block matrix `[A 0; 0 B]`. -/
theorem blockDiag_eq {n : ℕ} (A B : Op n) : Spec.blockDiag A B = ofBlocks (fromBlocks A 0 0 B) := by
  sorry

/-- A multiplexor on the top qubit is a 2 × 2 block matrix of diagonals. -/
theorem mux_last_eq {n : ℕ} (u : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    mux (Fin.last n) u =
      ofBlocks (fromBlocks (diagonal fun k => u k 0 0) (diagonal fun k => u k 0 1)
        (diagonal fun k => u k 1 0) (diagonal fun k => u k 1 1)) := by
  sorry

theorem ofBlocks_mul {n : ℕ} (M N : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℂ) :
    ofBlocks M * ofBlocks N = ofBlocks (M * N) := by
  simp [ofBlocks, reindex_apply, submatrix_mul_equiv]

end LeanUnitary.Blocks
