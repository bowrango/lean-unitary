import LeanUnitary.Decomposition.BlockZXZ

/-!
# Claims scored by the lean-unitary hills

Each theorem here is scored only when its proof is complete (no `sorry`, no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`). Keep the names and statements exactly as they
are; change only the proofs.

**`lean-unitary-baselines`** scores the milestones: one theorem per statement in
`LeanUnitary.Spec`, named after it (`muxRotations : MuxRotations`, ...).

**`lean-unitary`** scores `synth : GeneralBound f`: every `n ≥ 2` qubit unitary in at most
`f n` CNOTs. Its statement may change, but only by replacing `f` with a smaller bound; the
score is the mean of `f n / LB n` for `n = 3..8`. It starts from the block-ZXZ bound.
-/

namespace LeanUnitary.Claims

open LeanUnitary.Spec LeanUnitary.Decomposition

theorem muxRotations : MuxRotations := Decomposition.muxRotations
theorem demultiplex : Demultiplex := Decomposition.demultiplex
theorem cosineSine : CosineSine := Decomposition.cosineSine
theorem twoQubitOptimal : TwoQubitOptimal := Decomposition.twoQubitOptimal
theorem qsd : QSD := Decomposition.qsd
theorem qsdOptimized : QSDOptimized := Decomposition.qsdOptimized
theorem blockZXZ : BlockZXZ := Decomposition.blockZXZ

/-- The synthesis algorithm scored by `lean-unitary`. -/
theorem synth : GeneralBound fun n => (22 * 4 ^ n - 72 * 2 ^ n + 80) / 48 :=
  Decomposition.blockZXZ

end LeanUnitary.Claims
