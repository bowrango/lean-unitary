import LeanUnitary.Spec

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

theorem cnotCount_append (c₁ c₂ : Circuit n) :
    Circuit.cnotCount (c₁ ++ c₂) = c₁.cnotCount + c₂.cnotCount := by
  simp [Circuit.cnotCount, List.countP_append]

/-- A gate on the lower `n` qubits of an `(n + 1)`-qubit register. -/
def Gate.lift : Gate n → Gate (n + 1)
  | .single q u => .single q.castSucc u
  | .cnot c t h => .cnot c.castSucc t.castSucc (by simpa using h)

/-- A circuit on the lower `n` qubits of an `(n + 1)`-qubit register. -/
def lift (c : Circuit n) : Circuit (n + 1) := c.map Gate.lift

/-- A circuit on the lower qubits acts the same whatever the top qubit is. -/
theorem denote_lift (c : Circuit n) : (lift c).denote = blockDiag c.denote c.denote := by
  sorry

theorem cnotCount_lift (c : Circuit n) : (lift c).cnotCount = c.cnotCount := by
  simp only [lift, Circuit.cnotCount, List.countP_map]
  congr 1
  funext g
  cases g <;> rfl

end LeanUnitary.Circuit
