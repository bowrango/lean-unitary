import Mathlib

/-!
# Circuit model

This fixes what "synthesize an `n`-qubit unitary with `k` CNOTs" means:

* the gate set is {arbitrary single-qubit unitary on any qubit, CNOT between any two
  distinct qubits}, the model in which the Shende–Markov–Bullock lower bound
  `⌈(4^n - 3n - 1) / 4⌉` holds;
* a circuit is a list of gates, applied first to last;
* `Synthesizable n k` says every `n`-qubit unitary equals, exactly, the matrix of some
  circuit containing at most `k` CNOTs.

Qubit `q` is bit `q` of the basis-state index, i.e. `Nat.testBit i q`; qubit `n` is the most
significant ("top") qubit of an `(n + 1)`-qubit register.
-/

namespace LeanUnitary.Spec

/-! ## Circuit model -/

/-- An operator on `n` qubits: a `2^n × 2^n` complex matrix. -/
abbrev Op (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

/-- A gate on `n` qubits from the gate set {single-qubit unitary, CNOT}. -/
inductive Gate (n : ℕ) where
  /-- The single-qubit unitary `u` applied to qubit `q`. -/
  | single (q : Fin n) (u : Matrix.unitaryGroup (Fin 2) ℂ)
  /-- CNOT with control qubit `c` and target qubit `t`. -/
  | cnot (c t : Fin n) (h : c ≠ t)

/-- The value of qubit `q` in basis state `i`. -/
def bit {n : ℕ} (i : Fin (2 ^ n)) (q : Fin n) : Fin 2 :=
  if (i : ℕ).testBit q then 1 else 0

/-- The matrix of a gate, acting on basis state `j` to give column `j`. -/
noncomputable def Gate.denote {n : ℕ} : Gate n → Op n
  | .single q u => fun i j =>
      if ∀ p : Fin n, p ≠ q → (i : ℕ).testBit p = (j : ℕ).testBit p then
        (u : Matrix (Fin 2) (Fin 2) ℂ) (bit i q) (bit j q)
      else 0
  | .cnot c t _ => fun i j =>
      if (i : ℕ) = (if (j : ℕ).testBit c then (j : ℕ) ^^^ 2 ^ (t : ℕ) else j) then 1 else 0

/-- Whether a gate is a CNOT. -/
def Gate.isCnot {n : ℕ} : Gate n → Bool
  | .single .. => false
  | .cnot .. => true

/-- A circuit: gates listed in the order they are applied. -/
abbrev Circuit (n : ℕ) := List (Gate n)

/-- The matrix of a circuit `[g₁, …, gₘ]` is `gₘ ⋯ g₁`. -/
noncomputable def Circuit.denote {n : ℕ} (c : Circuit n) : Op n :=
  c.foldl (fun acc g => g.denote * acc) 1

/-- The number of CNOT gates in a circuit. -/
def Circuit.cnotCount {n : ℕ} (c : Circuit n) : ℕ :=
  c.countP Gate.isCnot

/-- Every `n`-qubit unitary is exactly implemented by a circuit with at most `k` CNOTs. -/
def Synthesizable (n k : ℕ) : Prop :=
  ∀ U : Op n, U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ →
    ∃ c : Circuit n, c.denote = U ∧ c.cnotCount ≤ k

/-- A synthesis algorithm for every register of at least two qubits, using at most `f n`
CNOTs on `n` qubits. -/
def GeneralBound (f : ℕ → ℕ) : Prop :=
  ∀ n, 2 ≤ n → Synthesizable n (f n)

/-! ## Operators used by the decompositions -/

/-- `R_y(θ) = exp(-i θ Y / 2)`. -/
noncomputable def Ry (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
     (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)]

/-- `R_z(θ) = exp(-i θ Z / 2)`. -/
noncomputable def Rz (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I), 0;
     0, Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)]

/-- Basis index `i` with bit `t` cleared: the joint value of every qubit except `t`. -/
def clearBit (i t : ℕ) : ℕ :=
  if i.testBit t then i - 2 ^ t else i

/-- A multiplexed single-qubit gate (uniformly controlled gate) with target qubit `t`:
when the other qubits are in the state with index `k` (`clearBit i t`), apply `u k` to `t`. -/
noncomputable def mux {n : ℕ} (t : Fin n) (u : ℕ → Matrix (Fin 2) (Fin 2) ℂ) : Op n :=
  fun i j =>
    if ∀ p : Fin n, p ≠ t → (i : ℕ).testBit p = (j : ℕ).testBit p then
      u (clearBit i t) (bit i t) (bit j t)
    else 0

/-- The block-diagonal operator `A ⊕ B` on `n + 1` qubits: `A` on the lower `n` qubits when
the top qubit is `0`, `B` when it is `1` (a quantum multiplexor controlled by the top qubit). -/
noncomputable def blockDiag {n : ℕ} (A B : Op n) : Op (n + 1) := fun i j =>
  if (i : ℕ).testBit n = (j : ℕ).testBit n then
    (if (i : ℕ).testBit n then B else A)
      ⟨i % 2 ^ n, Nat.mod_lt _ (by positivity)⟩ ⟨j % 2 ^ n, Nat.mod_lt _ (by positivity)⟩
  else 0

end LeanUnitary.Spec
