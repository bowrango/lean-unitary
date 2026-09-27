import LeanUnitary.Circuit
import LeanUnitary.Blocks

/-!
# Multiplexed rotations

Milestone `LeanUnitary.Spec.MuxRotations`: a multiplexed `R_y` or `R_z` with `k = n - 1`
controls costs at most `2^k` CNOTs.

Outline (Shende–Markov–Bullock, quant-ph/0406176; Möttönen et al.,
quant-ph/0404089):
* `k = 0`: a single rotation on the target, no CNOTs.
* `k ≥ 1`: pick a control `c`. Then
  `mux(θ) = mux'(φ₀) · CNOT(c, t) · mux'(φ₁) · CNOT(c, t)` with
  `φ₀ = (θ|c=0 + θ|c=1) / 2` and `φ₁ = (θ|c=0 - θ|c=1) / 2`, where `mux'` has `k - 1` controls.
  This uses `X · R_z(φ) · X = R_z(-φ)` and `X · R_y(φ) · X = R_y(-φ)`.
* Naively this gives `2^(k+1) - 2` CNOTs. Mirroring one of the two sub-multiplexors cancels
  adjacent CNOTs pairwise, which brings the count to `2^k` (equivalently: the Gray-code
  circuit, with angles given by a Walsh–Hadamard transform of `θ`).
* This milestone is circuit algebra, not spectral theory: it needs `Circuit.denote_append`, the
  matrices of CNOT and single-qubit gates, and the two conjugation identities above. For the
  top qubit as target, `Blocks.mux_last_eq` turns multiplexors into diagonal blocks.
-/

namespace LeanUnitary.Decomposition

open LeanUnitary.Spec

theorem muxRotations : MuxRotations := by
  sorry

end LeanUnitary.Decomposition
