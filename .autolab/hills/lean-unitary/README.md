# lean-unitary

Prove, in Lean, an n-qubit unitary synthesis algorithm whose CNOT count approaches the theoretical lower bound, improving on the verified QSD and block-ZXZ baselines.

<!-- This README is the contract. The climbing agent reads it through
     `hills describe lean-unitary` and nothing else. -->

## Task

The repository is a Lean 4 library, `LeanUnitary`, built on Mathlib and
[LeanQuantum](https://github.com/inQWIRE/LeanQuantum) (`Quantumlib`). It contains
machine-checked proofs of the quantum Shannon decomposition and the block-ZXZ decomposition
(from the `lean-unitary-baselines` hill), which synthesize any `n`-qubit unitary in

    QSD, optimized:  (23/48)·4^n − (3/2)·2^n + 4/3   CNOTs
    block-ZXZ:       (22/48)·4^n − (3/2)·2^n + 5/3   CNOTs

The Shende–Markov–Bullock lower bound is `⌈(4^n − 3n − 1)/4⌉`, about `(12/48)·4^n`. Your job
is to **prove a synthesis algorithm with a smaller CNOT count**, for all `n ≥ 2`, and move it
as close to the lower bound as you can. To our knowledge no construction is known to meet the
bound for `n ≥ 3`, so this is research. The number stands in for the quality of the
algorithm; a proof that is correct but no better scores the same as the baseline.

Treat it as research: read the decompositions and understand exactly where their CNOTs come
from before changing anything. Productive directions include:

- **Commutation and circuit identities.** CNOTs commute with `R_z` on the control and `R_x`
  on the target; diagonal gates commute with CNOT controls and can be pushed through
  multiplexors; a CNOT next to a multiplexor can sometimes be merged into it (the CZ trick in
  QSD); decompositions that only need to hold up to a diagonal leave that diagonal free to be
  absorbed by a neighbour.
- **Unused freedom in the decompositions.** CSD, demultiplexing and block-ZXZ factors are not
  unique; choosing them well can make adjacent gates cancel or merge.
- **Better base cases and recursion.** Stronger constructions for small `n` (e.g. 3 qubits)
  improve every level above them. Different recursions may beat QSD's four-way split.
- **Parameter counting.** The lower bound comes from each CNOT adding at most four
  parameters. A circuit that wastes parameters cannot be optimal, which shows where to look.

References: Shende–Markov–Bullock quant-ph/0406176 (QSD, optimizations, the lower bound);
arXiv:2403.13692 (block-ZXZ); Vatan–Williams quant-ph/0308006 (optimal two-qubit circuits);
Möttönen et al. quant-ph/0404089 (multiplexed rotations).

## The statement

`LeanUnitary/Spec.lean` is **frozen**: the evaluator replaces it with its own copy. It fixes
the circuit model: gates `Gate.single q u` (a unitary `u` on qubit `q`) and `Gate.cnot c t`;
circuits are gate lists applied first to last; equality is exact. The scored claim is

```lean
theorem LeanUnitary.Claims.synth : LeanUnitary.Spec.GeneralBound f
-- where  GeneralBound f := ∀ n, 2 ≤ n → Synthesizable n (f n)
```

`f : ℕ → ℕ` is yours to choose (any expression the kernel can evaluate at numerals; it may be
piecewise). Improving the algorithm means proving `synth` for a smaller `f`.

## Submission format

A submission is the repository **directory**. The evaluator uses only:

```
LeanUnitary.lean          library root; must import every module
LeanUnitary/**/*.lean     all modules, including LeanUnitary/Claims.lean
```

Everything else is ignored: the evaluator builds with its own frozen `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain` (Lean v4.30.0-rc2 with the pinned Mathlib and
LeanQuantum commits) and `LeanUnitary/Spec.lean`.

### What you may edit

Any `.lean` file under `LeanUnitary/` and `LeanUnitary.lean`, except `LeanUnitary/Spec.lean`.
In `LeanUnitary/Claims.lean`, `synth` must stay a theorem named `LeanUnitary.Claims.synth`
whose statement is `LeanUnitary.Spec.GeneralBound f`; only `f` and the proof may change. Keep
the existing baseline proofs building: they are the reference your improvement is measured
against.

Do not change `lakefile.toml`, `lake-manifest.json` or `lean-toolchain`, and do not run
`lake update`. Add every new module to `LeanUnitary.lean`, because the whole library must
build: **a build error anywhere scores nothing**.

Reuse what exists: the baseline proofs and their lemmas in `LeanUnitary/`, and Mathlib's linear
algebra (`LeanUnitary/LinearAlgebra.lean` lists the relevant results). Quantumlib only provides gate
matrices, and it contains a `sorry` (`Quantumlib/Data/Error/Operator.lean`); a proof that depends
on it is rejected.

### Not allowed in submission sources

Checked textually (comments are ignored) before anything is built:

- `axiom` declarations
- `native_decide`, `Lean.ofReduceBool`, `implemented_by`, `extern`, `csimp`, `unsafe`
- running code at build time: `#eval`, `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `initialize`
- syntax and elaborator extensions: `macro`, `macro_rules`, `syntax`, `elab`, `elab_rules`,
  `declare_syntax_cat`, `@[command_elab]`, `@[term_elab]`, `@[tactic]`
- `set_option debug.skipKernelTC`

Experiment with `#eval` in scratch files outside `LeanUnitary/`.

## Metric

| metric       | direction | meaning |
|--------------|-----------|---------|
| `cnot_ratio` | min       | mean over `n = 3..8` of `f(n) / ⌈(4^n − 3n − 1)/4⌉` |

**1.0 is optimal.** Block-ZXZ scores about 1.657 and optimized QSD about 1.738. The range
weights large `n`, where the leading coefficient dominates, but a saving at any `n` in `3..8`
improves the score.

A submission is scored only when `synth` is fully proved. There is no partial credit: an
unproved or rejected `synth` fails the run, and `details.bounds` shows the bounds it would have
scored. Acceptance requires:

1. `lake build LeanUnitary LeanUnitary.Claims` succeeds, with the frozen spec in place.
2. Every declaration in every `LeanUnitary.*` module is re-checked by the Lean kernel on top of
   a fresh import of the dependencies.
3. `synth` is a theorem whose statement is `LeanUnitary.Spec.GeneralBound f`, and `f n` reduces
   to a numeral in the kernel for `n = 3..8`.
4. It depends on no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

`details.per_n` gives each `n`'s bound, lower bound and ratio.

## Parameters

None.

## Test mode

There is no held-out data: the statement is public and the proof is checked, not sampled.
`--final` scores exactly like validation.

## Timing

The first evaluation on a machine downloads and builds the pinned Mathlib and LeanQuantum
once. After that, an evaluation takes as long as building your modules plus about a minute of
checking.

## What the evaluator will not do

- It will not trust a number the submission states. Bounds are computed by the kernel from the
  checked statement.
- It will not score an algorithm that is not fully proved.
- It will not accept `sorry`, new axioms or compiler-trusting tactics, however the proof is
  built.
- It will not use your copies of the spec, build config or dependencies.
- A proved bound below the lower bound would mean the frozen spec is wrong. The evaluator fails
  the run instead of scoring it; stop and report it to the hill author.
