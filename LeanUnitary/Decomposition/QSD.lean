import LeanUnitary.Decomposition.Multiplexor
import LeanUnitary.Decomposition.Demultiplex
import LeanUnitary.Decomposition.CosineSine
import LeanUnitary.Decomposition.TwoQubit

/-!
# Quantum Shannon decomposition

Milestones `LeanUnitary.Spec.QSD` and `LeanUnitary.Spec.QSDOptimized`.

Outline (Shende–Markov–Bullock, quant-ph/0406176, including its appendix of optimizations):
* `U = (A₀ ⊕ A₁) · Y · (B₀ ⊕ B₁)` (cosine–sine), then demultiplex both outer factors:
  `U = (V₁ ⊕ V₁) D₁ (W₁ ⊕ W₁) · Y · (V₂ ⊕ V₂) D₂ (W₂ ⊕ W₂)`.
* Four `n`-qubit unitaries (recursively synthesized, embedded with `Circuit.lift`) plus three
  multiplexed rotations with `n` controls (`2^n` CNOTs each):
  `c(n + 1) = 4 c(n) + 3 · 2^n`, `c(1) = 0`, so `c(n) = (3/4) 4^n - (3/2) 2^n` (`QSD`).
* `QSDOptimized` (`(23/48) 4^n - (3/2) 2^n + 4/3`) adds, for `n ≥ 2`:
  - the two-qubit base case `c(2) = 3` (`TwoQubitOptimal`);
  - implement the middle multiplexed `R_y` with a final CZ instead of a CNOT and merge
    the CZ into the neighbouring multiplexor, saving one CNOT per recursive step;
  - synthesize the two-qubit leaves only up to a diagonal (2 CNOTs) and migrate each
    diagonal through the neighbouring multiplexor into the next leaf.
-/

namespace LeanUnitary.Decomposition

open LeanUnitary.Spec

theorem qsd : QSD := by
  sorry

theorem qsdOptimized : QSDOptimized := by
  sorry

end LeanUnitary.Decomposition
