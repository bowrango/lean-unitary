import Mathlib
import Quantumlib
import Quantumlib.Data.Gate.Unitary

/-!
# Basic definitions

Core types for quantum unitary decomposition, built on LeanQuantum (`Quantumlib`).
-/

/-- An `n`-qubit gate: a `2^n × 2^n` complex matrix (LeanQuantum's `CSquare`). -/
abbrev QGate (n : ℕ) := CSquare (2 ^ n)

/-- Sanity check that LeanQuantum is wired up: CNOT is a unitary 2-qubit gate. -/
example : (cnot : QGate 2).IsUnitary := cnot_isUnitary
