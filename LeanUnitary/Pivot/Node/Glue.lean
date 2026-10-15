import LeanUnitary.Pivot.Node.Gray
import LeanUnitary.Pivot.Node.Demux

/-!
# Glue between circuits and block matrices

Operators on `n + 1` qubits are block matrices over the top qubit (`Blocks.ofBlocks`). This
module expresses the node's gates in that form and records how they commute:

* `dup V = V ⊕ V` is a lifted circuit on the lower qubits (`denote_lift_eq`);
* the Hadamard and pivot gates on the top qubit are `H ⊗ I` and `g ⊗ I` (`denote_hTop_eq`,
  `denote_single_last_eq`), and `CX_c = (H ⊗ I)(I ⊕ Z_c)(H ⊗ I)` (`denote_cxTop_eq`), the identity
  that merges a CNOT into the central multiplexor;
* `D(θ)` is the multiplexed `R_z` (`ofBlocks_Dz`);
* `dup` of a diagonal commutes with every circuit of top-qubit gates (`TopGates.comm_dup_diag`),
  which carries the children's diagonals through the multiplexors.
-/

namespace LeanUnitary.Pivot.Node

open Matrix Complex LeanUnitary.Spec LeanUnitary.Blocks LeanUnitary.Circuit

variable {n : ℕ}

/-! ## Block matrices as operators -/

theorem ofBlocks_one : ofBlocks (1 : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) _ ℂ) = 1 := by
  simp [ofBlocks]

theorem star_ofBlocks (M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℂ) :
    star (ofBlocks M) = ofBlocks (star M) := by
  simp [ofBlocks, star_eq_conjTranspose]

theorem ofBlocks_injective :
    Function.Injective (ofBlocks (n := n)) := (reindex _ _).injective

theorem ofBlocks_mem_iff (M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℂ) :
    ofBlocks M ∈ unitaryGroup (Fin (2 ^ (n + 1))) ℂ ↔ M ∈ unitaryGroup _ ℂ := by
  rw [mem_unitaryGroup_iff, mem_unitaryGroup_iff, star_ofBlocks, ofBlocks_mul, ← ofBlocks_one]
  exact ofBlocks_injective.eq_iff

/-- The blocks of an operator on `n + 1` qubits. -/
noncomputable def topBlocks (U : Op (n + 1)) :
    Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) ℂ :=
  reindex (topSplit n) (topSplit n) U

theorem ofBlocks_topBlocks (U : Op (n + 1)) : ofBlocks (topBlocks U) = U := by
  simp [ofBlocks, topBlocks]

/-- `V ⊕ V`: `V` on the lower `n` qubits. -/
noncomputable def dup (V : Op n) : Op (n + 1) := ofBlocks (fromBlocks V 0 0 V)

theorem denote_lift_eq (c : Circuit n) : (Circuit.lift c).denote = dup c.denote := by
  rw [denote_lift, blockDiag_eq]; rfl

theorem dup_mul (A B : Op n) : dup A * dup B = dup (A * B) := by
  rw [dup, dup, dup, ofBlocks_mul, fromBlocks_multiply]; simp

theorem dup_mem {V : Op n} (hV : V ∈ unitaryGroup _ ℂ) : dup V ∈ unitaryGroup _ ℂ :=
  (ofBlocks_mem_iff _).mpr (fromBlocks_diag_mem hV hV)

/-! ## The gates as block matrices -/

theorem diagonal_const (c : ℂ) : (diagonal fun _ : Fin (2 ^ n) => c) = c • 1 := by
  rw [smul_one_eq_diagonal]

theorem denote_single_last_eq (g : unitaryGroup (Fin 2) ℂ) :
    (Gate.single (Fin.last n) g).denote = ofBlocks (Pivot.lift (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [denote_single_last, mux_last_eq, Pivot.lift]
  simp only [diagonal_const]

theorem denote_hTop_eq : (hTop n).denote = ofBlocks hBlk := by
  rw [denote_hTop, mux_last_eq]
  simp only [diagonal_const]
  rfl

/-- `Z_c`: the sign `(-1)^{x_c}` on the lower qubits. -/
noncomputable def zc (c : Fin n) : Op n := diagonal fun k => if (k : ℕ).testBit c then -1 else 1

theorem zc_mem (c : Fin n) : zc c ∈ unitaryGroup _ ℂ := by
  rw [mem_unitaryGroup_iff, zc, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext k; by_cases h : (k : ℕ).testBit c <;> simp [h]

/-- **The merge identity** `CX_c = (H ⊗ I)(I ⊕ Z_c)(H ⊗ I)`. -/
theorem denote_cxTop_eq (c : Fin n) :
    (cxTop c).denote = ofBlocks (hBlk * fromBlocks 1 0 0 (zc c) * hBlk) := by
  rw [denote_cxTop, mux_last_eq, hBlk_mul_mul_hBlk]
  congr 1
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      smul_apply, add_apply, sub_apply, diagonal_apply, one_apply, zc, smul_eq_mul] <;>
    by_cases hij : i = j <;> simp only [hij, if_true, if_false] <;>
    by_cases h : ((j : ℕ)).testBit c <;> simp [h, xpow, σX] <;> norm_num

/-- Extend angles on the lower basis states to `ℕ`. -/
noncomputable def extθ (θ : Fin (2 ^ n) → ℝ) (x : ℕ) : ℝ := if h : x < 2 ^ n then θ ⟨x, h⟩ else 0

theorem ofBlocks_Dz (θ : Fin (2 ^ n) → ℝ) :
    ofBlocks (Dz θ) = mux (Fin.last n) fun x => Rz (extθ θ x) := by
  rw [mux_last_eq, Dz]
  congr 1
  have h : ∀ k : Fin (2 ^ n), extθ θ k = θ k := fun k => by simp [extθ, k.isLt]
  simp [Rz, h]

/-! ## Top-qubit circuits commute with lower diagonals -/

/-- A circuit of gates on the top qubit only (`R_z`, Hadamard, CNOT onto the top qubit). -/
def TopGates (c : Circuit (n + 1)) : Prop :=
  ∀ g ∈ c, ∃ f : ℕ → Matrix (Fin 2) (Fin 2) ℂ, g.denote = mux (Fin.last n) f

theorem TopGates.denote {c : Circuit (n + 1)} (hc : TopGates c) :
    ∃ F : ℕ → Matrix (Fin 2) (Fin 2) ℂ, c.denote = mux (Fin.last n) F := by
  induction c with
  | nil => exact ⟨fun _ => 1, by rw [denote_nil, mux_const_one]⟩
  | cons g c ih =>
    obtain ⟨F, hF⟩ := ih fun g' hg' => hc g' (List.mem_cons_of_mem _ hg')
    obtain ⟨f, hf⟩ := hc g List.mem_cons_self
    exact ⟨fun k => F k * f k, by rw [denote_cons, hF, hf, mux_mul]⟩

theorem dup_diag_comm_mux (d : Fin (2 ^ n) → ℂ) (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    dup (diagonal d) * mux (Fin.last n) f = mux (Fin.last n) f * dup (diagonal d) := by
  rw [dup, mux_last_eq, ofBlocks_mul, ofBlocks_mul, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, diagonal_mul_diagonal,
    mul_comm (d _)]

theorem TopGates.comm_dup_diag {c : Circuit (n + 1)} (hc : TopGates c) (d : Fin (2 ^ n) → ℂ) :
    dup (diagonal d) * c.denote = c.denote * dup (diagonal d) := by
  obtain ⟨F, hF⟩ := hc.denote
  rw [hF, dup_diag_comm_mux]

theorem TopGates.append {c₁ c₂ : Circuit (n + 1)} (h₁ : TopGates c₁) (h₂ : TopGates c₂) :
    TopGates (c₁ ++ c₂) := fun g hg => by
  rcases List.mem_append.mp hg with h | h
  · exact h₁ g h
  · exact h₂ g h

theorem topGates_rzTop (a : ℝ) : TopGates [rzTop n a] := by
  intro g hg; rw [List.mem_singleton.mp hg]; exact ⟨_, denote_rzTop a⟩

theorem topGates_hTop : TopGates [hTop n] := by
  intro g hg; rw [List.mem_singleton.mp hg]; exact ⟨_, denote_hTop⟩

theorem topGates_cxTop (c : Fin n) : TopGates [cxTop c] := by
  intro g hg; rw [List.mem_singleton.mp hg]; exact ⟨_, denote_cxTop c⟩

theorem TopGates.reverse {c : Circuit (n + 1)} (h : TopGates c) : TopGates c.reverse :=
  fun g hg => h g (List.mem_reverse.mp hg)

theorem topGates_core (m : ℕ) (hm : m ≤ n) (θ : ℕ → ℝ) : TopGates (core n m hm θ) := by
  induction m generalizing θ with
  | zero => exact topGates_rzTop _
  | succ m ih =>
    simp only [core]
    exact ((ih _ _).append (topGates_cxTop _)).append (ih _ _).reverse

end LeanUnitary.Pivot.Node
