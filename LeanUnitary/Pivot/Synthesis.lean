import LeanUnitary.Pivot.Count
import LeanUnitary.Spec

/-!
# From the recursion to the CX bound

`submission/decomposition.tex`, Sec. II.D. Block-ZXZ synthesizes an `(n + 1)`-qubit unitary from
four `n`-qubit children and three multiplexors of `2^n` CX gates each, less five merged CX gates
(arXiv:2403.13692, Sec. 5.3). The pivot merges a sixth (`Pivot.pivot_merge`). The construction
of a single node from the baseline decompositions is taken as a hypothesis here (`hnode`); this
module proves that the recursion then gives the bound of Eq. 18:

* `generalBound_of_pivot_node`: a 3-CX two-qubit base case and the pivot node step give
  `GeneralBound (n ↦ (21·4^n - 72·2^n + 96)/48)`, i.e. `(21/48) 4^n - (3/2) 2^n + 2`;
* `generalBound_of_zxz_node`: the same argument with five merges per node gives the Block-ZXZ
  bound of `Spec.BlockZXZ`, `(22/48) 4^n - (3/2) 2^n + 5/3`.
-/

namespace LeanUnitary.Pivot

open LeanUnitary.Spec

/-- The pivot recursion bounds every register of at least two qubits by `count n`. -/
theorem synthesizable_count (hbase : Synthesizable 2 3)
    (hnode : ∀ n, 2 ≤ n → ∀ k, Synthesizable n k → Synthesizable (n + 1) (4 * k + 3 * 2 ^ n - 6))
    (n : ℕ) (hn : 2 ≤ n) : Synthesizable n (count n) := by
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    exact hnode (j + 2) hn _ ih

/-- **The pivot bound.** Given the Block-ZXZ node construction with the pivot's extra merge
(`4k + 3·2^n - 6` CX gates from children of `k`) and the 3-CX two-qubit base case, every `n`-qubit
unitary, `n ≥ 2`, needs at most `(21·4^n - 72·2^n + 96)/48` CX gates. -/
theorem generalBound_of_pivot_node (hbase : Synthesizable 2 3)
    (hnode : ∀ n, 2 ≤ n → ∀ k, Synthesizable n k → Synthesizable (n + 1) (4 * k + 3 * 2 ^ n - 6)) :
    GeneralBound fun n => (21 * 4 ^ n - 72 * 2 ^ n + 96) / 48 := fun n hn => by
  change Synthesizable n ((21 * 4 ^ n - 72 * 2 ^ n + 96) / 48)
  rw [← count_eq n hn]
  exact synthesizable_count hbase hnode n hn

/-- The Block-ZXZ recursion bounds every register of at least two qubits by `zxzCount n`. -/
theorem synthesizable_zxzCount (hbase : Synthesizable 2 3)
    (hnode : ∀ n, 2 ≤ n → ∀ k, Synthesizable n k → Synthesizable (n + 1) (4 * k + 3 * 2 ^ n - 5))
    (n : ℕ) (hn : 2 ≤ n) : Synthesizable n (zxzCount n) := by
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    exact hnode (j + 2) hn _ ih

/-- The same argument with five merges per node recovers the Block-ZXZ bound. -/
theorem generalBound_of_zxz_node (hbase : Synthesizable 2 3)
    (hnode : ∀ n, 2 ≤ n → ∀ k, Synthesizable n k → Synthesizable (n + 1) (4 * k + 3 * 2 ^ n - 5)) :
    BlockZXZ := fun n hn => by
  change Synthesizable n ((22 * 4 ^ n - 72 * 2 ^ n + 80) / 48)
  rw [← zxzCount_eq n hn]
  exact synthesizable_zxzCount hbase hnode n hn

end LeanUnitary.Pivot
