# lean-unitary

Machine-checked synthesis of arbitrary `n`-qubit unitaries with fewer CX gates than Block-ZXZ.

The method (`submission/decomposition.tex`) inserts a single-qubit **pivot gate**
`g = R_z(α) R_y(β)` on the top qubit at each step of the Block-ZXZ recursion,

$$U=(\ast)\,\big(I\oplus C(g)\big)\,(g^\dagger\otimes I),$$

and chooses `α*`, `β*` so that the eigenphases of `C(g)` admit a *balanced split*. That zeroes
the final angle `φ` of the left multiplexor, so one more CX merges at every recursion node:

| | recurrence | CX count |
| --- | --- | --- |
| Block-ZXZ ([Krol & Al-Ars 2024](https://arxiv.org/abs/2403.13692)) | `c_n = 4c_{n-1} + 3·2^{n-1} − 5` | `(22/48)·4^n − (3/2)·2^n + 5/3` |
| **pivot (this work)** | `c_n = 4c_{n-1} + 3·2^{n-1} − 6` | `(21/48)·4^n − (3/2)·2^n + 2` |

This saves `(4^{n−2} − 1)/3` CX gates, one per recursion node. The lower bound is `⌈(4^n − 3n − 1)/4⌉`
([Shende, Markov & Bullock](https://arxiv.org/abs/quant-ph/0406176)).

![Lean formalization of the pivot decomposition](report/diagram.png)

*Source: [`report/diagram.tex`](report/diagram.tex).*

## Architecture

The project has three layers, each usable on its own:

| Layer | Path | Role |
| --- | --- | --- |
| Paper | `submission/` | The construction, existence argument and gate count (`decomposition.tex`, `benchmark.py`) |
| Numerics | `research/` | Python reference implementation and experiments (`experiments/foldzxz_opt.py`), supplement, video. Plain NumPy/SciPy with no dependency on Lean. |
| Formalization | `LeanUnitary/` | Lean 4 proofs against the frozen circuit model in `LeanUnitary/Spec.lean` |

The Python code and the Lean library share only the mathematics. The Lean side never runs or imports
the experiments, and the experiments need no Lean toolchain. The one point of contact is a
cross-check: the kernel evaluates `Pivot.count 10 = 457218` and `Pivot.zxzCount 10 = 479063`, the
same CX counts `submission/benchmark.py` measures on its synthesized circuits.

### The pivot formalization, `LeanUnitary/Pivot/`

The modules are grouped by the steps of the algorithm, as in the diagram above. All results are
stated for arbitrary finite index types (`m ⊕ m` blocks, as in `LeanUnitary.Blocks`), are fully
proved, and use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

| Module | Paper | Main results |
| --- | --- | --- |
| **Path** | | |
| `Path/Gate.lean` | Eq. (9) | `gate_mem_unitaryGroup` (the pivot `g = R_z(α)R_y(β)` is unitary); `fromBlocks_mul_lift` (Eq. 9 is the top row of `U(g⊗I)`); `Xg_zero`, `Yg_zero`, `Xg_pi`, `Yg_pi` (endpoint swap); `Xg_eq_mul`, `Yg_eq_mul` (factorization through `M = e^{iα}X⁻¹Y`) |
| `Path/Eigenvalues.lean` | Eq. (12) | `det_smul_add_smul_one` (`det(aM + b) = ∏(aτ_k + b)`); `roots_charpoly_inv`, `roots_charpoly_smul`; `norm_eq_one_of_mem_roots_charpoly`; `taus_eq_map` (`τ_k(α) = e^{iα}τ_k(0)`); `det_Xg_eq_prod`, `det_Yg_eq_prod` (Eq. 12); `ne_zero_of_mem_taus` |
| **Multiplexor** | | |
| `Multiplexor/Basic.lean` | Eqs. (10), (11) | `multiplexor` (`C(β)`, via the functional calculus); `multiplexor_pi` (`C(π) = C(0)ᴴ`); `invSqrt_mul_mem_unitaryGroup` (polar factors are unitary); `multiplexor_mem_unitaryGroup`; `multiplexor_pi_eq_inv` (`C(π) = C(0)⁻¹`) |
| `Multiplexor/Continuity.lean` | Sec. II.C | `continuousOn_invSqrt`; `isUnit_det_Xg`, `isUnit_det_Yg` (no real `τ_k` keeps `X_g`, `Y_g` invertible); `continuous_multiplexor` |
| `Multiplexor/Phase.lean` | Eqs. (12)–(14) | `sigma` (an explicit continuous phase of `det C(β)`); `continuousOn_sigma`; `exp_sigma` (`e^{iσ(β)} = det C(β)`); `sigma_zero`, `sigma_pi` (Eq. 13); `sigma_pi_eq_neg` (`σ(π) = −σ(0)` when `N₊ = N₋`) |
| **Split** | | |
| `Split.lean` | Eqs. (3), (6)–(8) | `walsh_eq` (φ depends only on the split and an integer `ℓ`); `exists_walsh_eq_zero_iff` (φ = 0 is attainable iff a balanced split exists); `topPlus`, `finalAngle` (the Walsh row and φ) |
| **Existence** | | |
| `Existence/Rotation.lean` | Eq. (13) | `exists_rotation_half_upper` (with distinct crossing angles, some rotation makes `N₊ = N₋` with no `τ_k` real), via `exists_eq_of_step_le_one` (a discrete intermediate value theorem) |
| `Existence/Lift.lean` | Eq. (15) | `normalized_lift_unique`; `neg_rev_eq_of_lift` (`ν(π) = −ν(0) ∘ rev`); `exists_normalized_lift`; `normalized_lift_stable` |
| `Existence/EigenContinuity.lean` | — | `eventually_exists_perm_close` (eigenvalues of a continuous matrix family move continuously, as matched lists); `norm_le_of_mem_roots_charpoly` |
| `Existence/PhaseList.lean` | Eq. (11) | `exists_phaseList`; `IsPhaseList.of_sameResidues`; `exists_int_of_exp_eq`; `multiplexor_phases_neg` (the phases of `C(π)` are those of `C(0)` negated); `exists_phase_close` |
| `Existence/Imbalance.lean` | Eqs. (16), (17) | `imbalance_neg_rev` (`P(π) = −P(0)`); `exists_imbalance_eq_zero` (a root `β*`); `exists_walsh_eq_zero_of_lift` (φ = 0 at `β*`) |
| `Existence/Pivot.lean` | Eqs. (1)–(3) | `continuousOn_lift` (the normalized lift with sum `σ(β)` is continuous); `exists_pivot_beta`; `exists_pivot` (both pivot angles exist); **`pivot_merge`** (for generic `U`, the pivot gives `U(g⊗I)` a Block-ZXZ multiplexor whose demultiplexing angles have `φ = 0`, so the extra CX merges) |
| **Synthesis and count** | | |
| `Synthesis.lean` | Eq. (18) | `generalBound_of_pivot_node` (the 3-CX base case and the pivot node step give `GeneralBound ((21·4^n − 72·2^n + 96)/48)`); `generalBound_of_zxz_node` (with five merges, the Block-ZXZ bound) |
| `Count.lean` | Eqs. (18), (19) | `count_closed`, `count_eq` (`(21·4^n − 72·2^n + 96)/48`); `zxzCount_eq` (the Spec's Block-ZXZ bound); `saving` (`Δ_n = (4^{n−2} − 1)/3`) |

**What is assumed.** The baseline decompositions (multiplexed rotations, demultiplexing, the
Block-ZXZ factorization with its five CX merges, and the 3-CX two-qubit case) are taken as known.
They enter `generalBound_of_pivot_node` as two hypotheses: the base case `Synthesizable 2 3` and
the node step. Everything specific to the pivot is proved: the pivot angles exist, and the
final rotation vanishes so the sixth CX merges (`pivot_merge`), and the counting (`Count`,
`Synthesis`).

**Genericity.** As in the paper, `pivot_merge` assumes a generic node: `X`, `Y` invertible and
the eigenvalues of `X⁻¹Y` at distinct crossing angles. A bound for every unitary also needs the
non-generic nodes, either handled directly or by a perturbation argument; that case is not
formalized.

### Setup

This is a [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/) project built on [Mathlib](https://github.com/leanprover-community/mathlib4) alone.

```sh
lake exe cache get   # download prebuilt Mathlib files (avoids a multi-hour compile)
lake build           # build this project
```

#### Conventions

- **Dependencies:** `.lake/` is not committed. Run `lake exe cache get` before the first `lake build`; without the cache Lake compiles Mathlib from source, which takes hours.
- **Where code goes:** all definitions and theorems belong in modules under `LeanUnitary/`. `LeanUnitary.lean` holds only `import` lines.
- **Register new modules:** when you create `LeanUnitary/Foo.lean`, add `import LeanUnitary.Foo` to `LeanUnitary.lean`. `lake build` only compiles modules reachable from it.
- **Verify:** `lake build` must succeed after every change. `sorry` is allowed in work in progress; a result counts as proved only when nothing it depends on uses `sorry`.
- **Fixed statements:** `LeanUnitary/Spec.lean` (the circuit model and the target statements) and the statements in `LeanUnitary/Claims.lean` are not edited; only proofs, and the bound in `Claims.synth`, change.
- **Don't change dependency pins:** leave `lean-toolchain`, `lake-manifest.json`, and the `rev`s in `lakefile.toml` alone, and don't run `lake update` (see [Dependencies](#dependencies)).

### Layout

| Path | Purpose |
| --- | --- |
| `LeanUnitary.lean` | Library root; imports every module in `LeanUnitary/` |
| `LeanUnitary/Spec.lean` | Fixed circuit model, `Synthesizable n k`, and the milestone statements; do not edit |
| `LeanUnitary/Circuit.lean` | Circuit algebra: composition, lifting onto more qubits, CNOT counting |
| `LeanUnitary/Blocks.lean` | Bridge from the spec's bit-indexed operators to Mathlib's `Matrix.fromBlocks` |
| `LeanUnitary/LinearAlgebra.lean` | Linear-algebra primitives, derived from Mathlib's spectral theorems |
| `LeanUnitary/Decomposition/` | One module per milestone (multiplexors, demultiplexing, CSD, two-qubit, QSD, block-ZXZ) |
| `LeanUnitary/Pivot/` | The pivot decomposition: `Path/`, `Multiplexor/`, `Split`, `Existence/`, `Synthesis`, `Count` (see [above](#the-pivot-formalization-leanunitarypivot)) |
| `LeanUnitary/Claims.lean` | Top-level claims: the milestones and `synth`, the proved general CX bound |
| `submission/` | The paper and its benchmark script (not part of the Lean build) |
| `research/` | Python experiments, supplement and video (not part of the Lean build) |
| `report/` | Diagram of the pivot formalization (`diagram.tex`, rendered to `diagram.png`) |
| `lakefile.toml` | Package config: dependencies and Lean options |
| `lean-toolchain` | Pinned Lean version |
| `lake-manifest.json` | Exact resolved commits of all dependencies (generated by `lake update`) |
| `.lake/` | Build output and downloaded dependencies (git-ignored) |

### Dependencies

The only dependency is Mathlib; the circuit model in `Spec.lean` is self-contained. The versions are
pinned:

- **Lean:** `v4.30.0-rc2` (`lean-toolchain`)
- **Mathlib:** commit `c1e30e17` (`lakefile.toml`)

To upgrade, set Mathlib's `rev` in `lakefile.toml` and `lean-toolchain` to a matching pair, then run
`lake update && lake build` and fix any breakage.
