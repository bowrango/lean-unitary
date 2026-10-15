import LeanUnitary.Pivot.Node.Factorize
import LeanUnitary.Pivot.Count

/-!
# The pivot recursion, end to end

The CX count of Sec. II.D, from circuits. `node_factor` gives the pivoted node; here its four
children are synthesized recursively. As in Block-ZXZ (Krol–Al-Ars, Sec. 5.3; Shende–Bullock–
Markov, quant-ph/0308045), three children are synthesized only up to a diagonal, which commutes
through the multiplexors into the next child, saving one CX each
(`SynthesizableDiag`). With `k` CX per child and `k - 1` up to a diagonal, a node costs
`3(k - 1) + k + (2^n - 2) + 2^n + (2^n - 1) = 4k + 3·2^n - 6` CX (`node_synth`), Eq. 18.

`pivot_generalBound` closes the recursion. It assumes only

* the two-qubit base cases, `Synthesizable 2 3` (Vatan–Williams) and its diagonal form
  `SynthesizableDiag 2 2` (Shende–Bullock–Markov), and
* the node bound for non-generic unitaries (`Generic` fails), which the paper also leaves aside.

Everything else (the pivot angles, the Block-ZXZ factorization, demultiplexing, the Gray-code
multiplexors and the merges) is proved.
-/

namespace LeanUnitary.Pivot.Node

open Matrix Complex LeanUnitary.Spec LeanUnitary.Blocks LeanUnitary.Circuit

/-- Every `n`-qubit unitary is a circuit with at most `k` CNOTs followed by a diagonal unitary. -/
def SynthesizableDiag (n k : ℕ) : Prop :=
  ∀ U : Op n, U ∈ unitaryGroup (Fin (2 ^ n)) ℂ →
    ∃ c : Circuit n, ∃ d : Fin (2 ^ n) → ℂ, diagonal d ∈ unitaryGroup (Fin (2 ^ n)) ℂ ∧
      U = diagonal d * c.denote ∧ c.cnotCount ≤ k

variable {n : ℕ}

theorem dup_diagonal (d : Fin (2 ^ n) → ℂ) :
    dup (diagonal d) = diagonal fun i => Sum.elim d d (topSplit n i) := by
  rw [dup, fromBlocks_diagonal, ofBlocks, reindex_apply, Equiv.symm_symm,
    submatrix_diagonal_equiv]
  rfl

theorem denote_single_mul_star (g : unitaryGroup (Fin 2) ℂ) :
    (Gate.single (Fin.last n) g).denote * (Gate.single (Fin.last n) (star g)).denote = 1 := by
  rw [denote_single_last, denote_single_last, mux_mul, ← mux_const_one]
  congr 1; funext _
  exact mem_unitaryGroup_iff.mp g.2

theorem cnotCount_single (g : unitaryGroup (Fin 2) ℂ) :
    Circuit.cnotCount [Gate.single (Fin.last n) g] = 0 := rfl

/-- **The node step.** For a generic unitary, children of `k` CX (and `k - 1` up to a diagonal)
give `4k + 3·2^n - 6` CX, and one fewer up to a diagonal. -/
theorem node_synth (k cnt : ℕ) (hcnt : 1 ≤ cnt) (hS : Synthesizable (k + 2) cnt)
    (hD : SynthesizableDiag (k + 2) (cnt - 1)) (U : Op (k + 2 + 1))
    (hU : U ∈ unitaryGroup (Fin (2 ^ (k + 2 + 1))) ℂ) (hgen : Generic U) :
    (∃ c : Circuit (k + 2 + 1), c.denote = U ∧ c.cnotCount ≤ 4 * cnt + 3 * 2 ^ (k + 2) - 6) ∧
    (∃ c : Circuit (k + 2 + 1), ∃ d : Fin (2 ^ (k + 2 + 1)) → ℂ,
      diagonal d ∈ unitaryGroup _ ℂ ∧ U = diagonal d * c.denote ∧
        c.cnotCount ≤ 4 * cnt + 3 * 2 ^ (k + 2) - 7) := by
  obtain ⟨g, Va, Vb, Wb, Wc, hVa, hVb, hWb, hWc, Ra, Mid, Rc, tRa, tMid, tRc, cRa, cMid, cRc,
    heq⟩ :=
    node_factor k U hU hgen
  -- synthesize the children, carrying each diagonal into the next child
  obtain ⟨cWc, dc, hdc, hWc', kWc⟩ := hD Wc hWc
  obtain ⟨cWb, db, hdb, hWb', kWb⟩ := hD (Wb * diagonal dc) (Submonoid.mul_mem _ hWb hdc)
  obtain ⟨cVb, dv, hdv, hVb', kVb⟩ := hD (Vb * diagonal db) (Submonoid.mul_mem _ hVb hdb)
  have hVa' := Submonoid.mul_mem _ hVa hdv
  -- the diagonals pass through the multiplexors
  have hcomm : ∀ (c : Circuit (k + 2 + 1)), TopGates c → ∀ (d : Fin (2 ^ (k + 2)) → ℂ)
      (X : Op (k + 2 + 1)), c.denote * (dup (diagonal d) * X) = dup (diagonal d) * (c.denote * X) :=
    fun c h d X => by rw [← Matrix.mul_assoc, ← h.comm_dup_diag, Matrix.mul_assoc]
  have hdup : ∀ (A B : Op (k + 2)) (X : Op (k + 2 + 1)), dup A * (dup B * X) = dup (A * B) * X :=
    fun A B X => by rw [← Matrix.mul_assoc, dup_mul]
  have key : dup Va * Ra.denote * dup Vb * Mid.denote * dup Wb * Rc.denote *
      dup Wc = dup (Va * diagonal dv) * Ra.denote * dup cVb.denote * Mid.denote *
        dup cWb.denote * Rc.denote * dup cWc.denote := by
    rw [hWc', ← dup_mul]
    simp only [Matrix.mul_assoc]
    rw [hcomm Rc tRc, hdup, hWb', ← dup_mul, Matrix.mul_assoc, hcomm Mid tMid, hdup, hVb',
      ← dup_mul, Matrix.mul_assoc, hcomm Ra tRa, hdup]
  have hUeq : U = dup (Va * diagonal dv) * Ra.denote * dup cVb.denote *
      Mid.denote * dup cWb.denote * Rc.denote * dup cWc.denote *
        (Gate.single (Fin.last (k + 2)) (star g)).denote := by
    rw [← key, ← heq, Matrix.mul_assoc, denote_single_mul_star, Matrix.mul_one]
  have h4 : 4 ≤ 2 ^ (k + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the circuit, gates in time order
  set tail : Circuit (k + 2) → Circuit (k + 2 + 1) := fun cA =>
    [Gate.single (Fin.last (k + 2)) (star g)] ++ Circuit.lift cWc ++ Rc ++ Circuit.lift cWb ++
      Mid ++ Circuit.lift cVb ++ Ra ++ Circuit.lift cA with htail
  have hden : ∀ cA : Circuit (k + 2), (tail cA).denote = dup cA.denote * Ra.denote *
      dup cVb.denote * Mid.denote * dup cWb.denote * Rc.denote * dup cWc.denote *
        (Gate.single (Fin.last (k + 2)) (star g)).denote := by
    intro cA
    simp only [htail, denote_append, denote_singleton, denote_lift_eq, Matrix.mul_assoc]
  have hcount : ∀ cA : Circuit (k + 2), (tail cA).cnotCount =
      cWc.cnotCount + (2 ^ (k + 2) - 2) + cWb.cnotCount + 2 ^ (k + 2) + cVb.cnotCount +
        (2 ^ (k + 2) - 1) + cA.cnotCount := by
    intro cA
    simp only [htail, cnotCount_append, cnotCount_lift, cnotCount_single, cRc, cMid, cRa]
    omega
  constructor
  · obtain ⟨cVa, hcVa, kVa⟩ := hS _ hVa'
    refine ⟨tail cVa, ?_, ?_⟩
    · rw [hden, hcVa, hUeq]
    · rw [hcount]; omega
  · obtain ⟨cVa, da, hda, hVa'', kVa⟩ := hD _ hVa'
    refine ⟨tail cVa, _, (dup_diagonal da) ▸ dup_mem hda, ?_, ?_⟩
    · rw [hden, ← dup_diagonal, hUeq, hVa'', ← dup_mul]
      simp only [Matrix.mul_assoc]
    · rw [hcount]; omega

theorem count_ge_three (n : ℕ) (hn : 2 ≤ n) : 3 ≤ count n := by
  induction n, hn using Nat.le_induction with
  | base => simp [count]
  | succ n hn ih =>
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    simp only [count]
    have : 4 ≤ 2 ^ (j + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **The pivot bound, end to end** (Eq. 18–19). From the two-qubit base cases and the node
bound for non-generic unitaries, every `n`-qubit unitary, `n ≥ 2`, is exactly synthesized with at
most `(21/48) 4^n - (3/2) 2^n + 2` CX gates. -/
theorem pivot_generalBound (hbase : Synthesizable 2 3) (hbaseD : SynthesizableDiag 2 2)
    (hnongeneric : ∀ k cnt, 1 ≤ cnt → Synthesizable (k + 2) cnt →
      SynthesizableDiag (k + 2) (cnt - 1) → ∀ U : Op (k + 2 + 1),
        U ∈ unitaryGroup (Fin (2 ^ (k + 2 + 1))) ℂ → ¬ Generic U →
        (∃ c : Circuit (k + 2 + 1), c.denote = U ∧ c.cnotCount ≤ 4 * cnt + 3 * 2 ^ (k + 2) - 6) ∧
        (∃ c : Circuit (k + 2 + 1), ∃ d : Fin (2 ^ (k + 2 + 1)) → ℂ,
          diagonal d ∈ unitaryGroup _ ℂ ∧ U = diagonal d * c.denote ∧
            c.cnotCount ≤ 4 * cnt + 3 * 2 ^ (k + 2) - 7)) :
    GeneralBound fun n => (21 * 4 ^ n - 72 * 2 ^ n + 96) / 48 := by
  have hpair : ∀ n, 2 ≤ n → Synthesizable n (count n) ∧ SynthesizableDiag n (count n - 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨hbase, hbaseD⟩
    | succ n hn ih =>
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
      have hc := count_ge_three (j + 2) (by omega)
      have hstep : ∀ U : Op (j + 2 + 1), U ∈ unitaryGroup (Fin (2 ^ (j + 2 + 1))) ℂ →
          (∃ c : Circuit (j + 2 + 1), c.denote = U ∧
            c.cnotCount ≤ 4 * count (j + 2) + 3 * 2 ^ (j + 2) - 6) ∧
          (∃ c : Circuit (j + 2 + 1), ∃ d : Fin (2 ^ (j + 2 + 1)) → ℂ,
            diagonal d ∈ unitaryGroup _ ℂ ∧ U = diagonal d * c.denote ∧
              c.cnotCount ≤ 4 * count (j + 2) + 3 * 2 ^ (j + 2) - 7) := by
        intro U hU
        by_cases hg : Generic U
        · exact node_synth j _ (by omega) ih.1 ih.2 U hU hg
        · exact hnongeneric j _ (by omega) ih.1 ih.2 U hU hg
      have hcount : count (j + 2 + 1) = 4 * count (j + 2) + 3 * 2 ^ (j + 2) - 6 := rfl
      refine ⟨fun U hU => ?_, fun U hU => ?_⟩
      · obtain ⟨c, hc, hk⟩ := (hstep U hU).1
        exact ⟨c, hc, by rw [hcount]; exact hk⟩
      · obtain ⟨c, d, hd, hc, hk⟩ := (hstep U hU).2
        exact ⟨c, d, hd, hc, by rw [hcount]; omega⟩
  intro n hn
  change Synthesizable n ((21 * 4 ^ n - 72 * 2 ^ n + 96) / 48)
  rw [← count_eq n hn]
  exact (hpair n hn).1

end LeanUnitary.Pivot.Node
