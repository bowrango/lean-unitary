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

Each module follows one part of Sec. II of the paper. All results are stated for arbitrary
finite index types (`m ⊕ m` blocks, as in `LeanUnitary.Blocks`) and use only the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

| Module | Paper | Main results | Status |
| --- | --- | --- | --- |
| `Pivot/Path.lean` | Eqs. (9), (12) | `gate_mem_unitaryGroup`; `fromBlocks_mul_lift` (Eq. 9 is the top row of `U(g⊗I)`); endpoint swap `Xg_pi`, `Yg_pi`; `rowGram_Xg_Yg` (top row stays orthonormal); `det_smul_add_smul_one` (`det(aM + b) = ∏(aτ_k + b)`); `det_Yg_div_det_Xg` (Eq. 12, `det Y_g / det X_g = ∏ τ_k (c − s/τ_k)/(c + sτ_k)` over the eigenvalues `τ_k` of `M = e^{iα}X⁻¹Y`); `det_Xg_eq_prod` (`X_g` invertible iff no `c + sτ_k` vanishes) | proved |
| `Pivot/Multiplexor.lean` | Eqs. (10), (11) | `multiplexor` = `C(β)` via the continuous functional calculus; `multiplexor_pi`: `C(π) = C(0)ᴴ`; `multiplexor_mem_unitaryGroup`: `C(β)` is unitary when `X_g`, `Y_g` are invertible (via the polar factor `invSqrt_mul_mem_unitaryGroup`); `multiplexor_pi_eq_inv`: `C(π) = C(0)⁻¹` | proved |
| `Pivot/Split.lean` | Eqs. (3), (6)–(8) | `walsh_eq` (φ depends only on the split and an integer `ℓ`); `exists_walsh_eq_zero_iff` (φ = 0 is attainable iff a balanced split exists) | proved |
| `Pivot/Count.lean` | Eqs. (18), (19) | `count_closed`, `count_eq` (`(21·4^n − 72·2^n + 96)/48`); `zxzCount_eq` (the Spec's Block-ZXZ bound); `saving`, `saving_succ` | proved |
| `Pivot/Existence.lean` | Eqs. (13)–(17) | choice of `α*` with `N₊ = N₋`, the imbalance `P(β)` with `P(π) = −P(0)`, and an intermediate-value root `β*` | planned |
| `Pivot/Synthesis.lean` | Sec. II.D | the circuit: Block-ZXZ with the pivot and the extra merge, giving `Claims.synth` with `f n = (21·4^n − 72·2^n + 96)/48` | planned |

Next steps, in dependency order:

1. **Existence (Eqs. 13–17).** This is the hard analytic step. It needs continuous eigenphase
   branches along `β` and the intermediate value theorem.
2. **Synthesis.** Build on the baseline milestones (`LinearAlgebra`, `Blocks`, `Circuit.denote_lift`
   and `Decomposition/BlockZXZ`), which are still `sorry`. Then replace the `Claims.synth` bound.

### Setup

This is a [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/) project built on [Mathlib](https://github.com/leanprover-community/mathlib4) and [LeanQuantum](https://github.com/inQWIRE/LeanQuantum).

```sh
lake exe cache get   # download prebuilt Mathlib files (avoids a multi-hour compile)
lake build           # build LeanQuantum and this project
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
| `LeanUnitary/Basic.lean` | Core definitions (`QGate n`, an `n`-qubit gate) |
| `LeanUnitary/Spec.lean` | Fixed circuit model, `Synthesizable n k`, and the milestone statements; do not edit |
| `LeanUnitary/Circuit.lean` | Circuit algebra: composition, lifting onto more qubits, CNOT counting |
| `LeanUnitary/Blocks.lean` | Bridge from the spec's bit-indexed operators to Mathlib's `Matrix.fromBlocks` |
| `LeanUnitary/LinearAlgebra.lean` | Linear-algebra primitives, derived from Mathlib's spectral theorems |
| `LeanUnitary/Decomposition/` | One module per milestone (multiplexors, demultiplexing, CSD, two-qubit, QSD, block-ZXZ) |
| `LeanUnitary/Pivot/` | The pivot decomposition: path, multiplexor, balanced split, gate count (see [above](#the-pivot-formalization-leanunitarypivot)) |
| `LeanUnitary/Claims.lean` | Top-level claims: the milestones and `synth`, the proved general CX bound |
| `submission/` | The paper and its benchmark script (not part of the Lean build) |
| `research/` | Python experiments, supplement and video (not part of the Lean build) |
| `report/` | Diagram of the pivot formalization (`diagram.tex`, rendered to `diagram.png`) |
| `lakefile.toml` | Package config: dependencies and Lean options |
| `lean-toolchain` | Pinned Lean version |
| `lake-manifest.json` | Exact resolved commits of all dependencies (generated by `lake update`) |
| `.lake/` | Build output and downloaded dependencies (git-ignored) |

### Dependencies

This project builds on LeanQuantum (`Quantumlib`) which provides the quantum primitives. It does not compile against the latest Mathlib (as of Lean v4.34.1) and is therefore pinned to the versions LeanQuantum is tested with:

- **Lean:** `v4.30.0-rc2` (`lean-toolchain`)
- **Mathlib:** commit `c1e30e17` (LeanQuantum's own pin)
- **LeanQuantum:** commit `44fc4eb`

In `lakefile.toml`, `require mathlib` must stay after `require quantumlib`. Otherwise Lake resolves Mathlib to a version the two packages disagree on. To upgrade, bump the LeanQuantum `rev`, set Mathlib's `rev` and `lean-toolchain` to match LeanQuantum's `lake-manifest.json` and `lean-toolchain`, then run `lake update && lake build`. Moving ahead of LeanQuantum means fixing its build in a fork.
