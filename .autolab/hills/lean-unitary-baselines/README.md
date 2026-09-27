# lean-unitary-baselines

Formally verify, in Lean, the quantum Shannon decomposition and the block-ZXZ decomposition: the baseline unitary synthesis algorithms later work improves on.

<!-- This README is the contract. The climbing agent reads it through
     `hills describe lean-unitary-baselines` and nothing else. -->

## Task

The repository is a Lean 4 library, `LeanUnitary`, built on Mathlib and
[LeanQuantum](https://github.com/inQWIRE/LeanQuantum) (`Quantumlib`). The long-term goal is
an explicit, formally verified synthesis algorithm for `n`-qubit unitaries whose CNOT count
reaches the Shende–Markov–Bullock lower bound `⌈(4^n − 3n − 1)/4⌉`. This hill builds the
foundation: machine-checked proofs of the two best-known general constructions, the
**quantum Shannon decomposition (QSD)** and the **block-ZXZ decomposition**, with their exact
CNOT counts. A follow-up hill (`lean-unitary`) then starts from these proofs and scores how
far below them the agent can push the proved bound.

The score counts **milestones**: fixed statements on the critical path of those algorithms,
frozen in `LeanUnitary/Spec.lean`. It does not reward any other theorems, so a lemma is
worth writing exactly when it moves a milestone forward. Read the papers before writing
proofs; the milestones follow their structure.

- Shende, Markov, Bullock, *Synthesis of quantum logic circuits*, quant-ph/0406176: QSD,
  multiplexors, demultiplexing, the CNOT optimizations, and the lower bound.
- Möttönen et al., quant-ph/0404089: multiplexed rotations via Gray codes.
- Vatan, Williams, quant-ph/0308006: 3-CNOT circuits for two-qubit gates.
- arXiv:2403.13692: the block-ZXZ decomposition.
- Paige, Wei, *History and generality of the CS decomposition* (1994).

## Milestones

| points | statement (`LeanUnitary.Spec`) | theorem (`LeanUnitary.Claims`) | content |
|---:|---|---|---|
| 2 | `MuxRotations` | `muxRotations` | multiplexed `R_y`/`R_z` with `n−1` controls in `2^(n−1)` CNOTs |
| 2 | `Demultiplex` | `demultiplex` | `A ⊕ B = (V ⊕ V)·(multiplexed R_z)·(W ⊕ W)` |
| 3 | `CosineSine` | `cosineSine` | `U = (A₀ ⊕ A₁)·(multiplexed R_y)·(B₀ ⊕ B₁)` |
| 3 | `TwoQubitOptimal` | `twoQubitOptimal` | every two-qubit unitary in 3 CNOTs |
| 2 | `QSD` | `qsd` | all `n ≥ 1`: `(3/4)4^n − (3/2)2^n` CNOTs |
| 3 | `QSDOptimized` | `qsdOptimized` | all `n ≥ 2`: `(23/48)4^n − (3/2)2^n + 4/3` CNOTs |
| 4 | `BlockZXZ` | `blockZXZ` | all `n ≥ 2`: `(22/48)4^n − (3/2)2^n + 5/3` CNOTs |

19 points in total. Read `LeanUnitary/Spec.lean` for the exact statements: the circuit model
(gates `Gate.single q u` for a unitary `u` on qubit `q`, and `Gate.cnot c t`; circuits are gate
lists applied first to last; exact matrix equality), `Synthesizable n k`, and the operators
`Ry`, `Rz`, `mux` (a uniformly controlled single-qubit gate) and `blockDiag` (a multiplexor
controlled by the top qubit). Qubit `q` is bit `q` of the basis index; the top qubit of an
`(n+1)`-qubit register is qubit `n`.

## Starting point

The repository already contains a skeleton, and you should build on it:

- `LeanUnitary/Circuit.lean`: circuit algebra (`denote_append`, `cnotCount_append`, `lift`
  onto the lower qubits, `cnotCount_lift` proved; `denote_lift` still `sorry`).
- `LeanUnitary/Blocks.lean`: the bridge from the spec's bit-indexed operators to Mathlib's
  block matrices. `blockDiag_eq` and `mux_last_eq` (both `sorry`, checked on 2 qubits) turn
  `blockDiag` and top-qubit multiplexors into `Matrix.fromBlocks`; `ofBlocks_mul` is proved.
- `LeanUnitary/LinearAlgebra.lean`: the three linear-algebra facts the decompositions need,
  stated in Mathlib's vocabulary, each with its route from Mathlib: simultaneous
  diagonalization of commuting Hermitian matrices, diagonalization of unitaries, and the
  block cosine–sine decomposition.
- `LeanUnitary/Decomposition/*.lean`: one module per milestone, each stating the milestone
  with `sorry` and a proof outline that uses the modules above.
- `LeanUnitary/Claims.lean`: the scored theorems, each forwarding to its module.

## Use Mathlib; do not rebuild linear algebra

The decompositions are known algorithms, and the linear algebra under them is largely in
Mathlib. The work here is connecting them, not re-deriving spectral theory. **Before proving
any linear-algebra lemma, search for it**: `exact?` and `apply?`, and grep
`.lake/packages/mathlib/Mathlib`. Write your own proof only for glue that Mathlib lacks.

| need | Mathlib |
|---|---|
| Hermitian / real symmetric spectral theorem | `Matrix.IsHermitian.spectral_theorem`, `.eigenvectorUnitary`, `.eigenvalues` |
| commuting symmetric operators, joint eigenspaces | `LinearMap.IsSymmetric.directSum_isInternal_of_commute`, `DirectSum.IsInternal.collectedOrthonormalBasis` |
| matrices ↔ operators | `Matrix.toEuclideanLin`, `Matrix.isHermitian_iff_isSymmetric` |
| unitaries are normal; unit-modulus eigenvalues | `isStarNormal_of_mem_unitary`, `Unitary.spectrum_subset_circle`, `Complex.norm_eq_one_iff` |
| square roots, singular values | `Matrix.IsHermitian.cfc`, `Matrix.PosSemidef`, `LinearMap.singularValues` |
| completing orthonormal families | `Orthonormal.exists_orthonormalBasis_extension`, `gramSchmidtNormed` |
| block matrices | `Matrix.fromBlocks_multiply`, `Matrix.fromBlocks_diagonal`, `Matrix.fromBlocks_conjTranspose` |
| unitary group, tensor products | `Matrix.mem_unitaryGroup_iff`, `Matrix.kronecker_mem_unitary` |

What Mathlib does *not* have, and so is genuinely yours to write: the three statements in
`LeanUnitary/LinearAlgebra.lean` (short derivations from the table above), the bridge in
`LeanUnitary/Blocks.lean`, and the decompositions themselves.

**Quantumlib (LeanQuantum) will not help with any of this.** It is small (about 2,500 lines):
gate matrices (Pauli, Hadamard, CNOT, SWAP, phase shifts, a general single-qubit `rotate`), their
unitarity, Kronecker-product lemmas and Pauli-group algebra. It has no eigenvalues, spectral
theorems, diagonalization or matrix decompositions. Its tensor products are indexed by
`Fin (a * c)`, not by the spec's bits, so even its Kronecker lemmas need translating. It also
contains a `sorry` (`Quantumlib/Data/Error/Operator.lean`); any claim that depends on it is
rejected, so check with `#print axioms` in a scratch file outside `LeanUnitary/`.

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

Any `.lean` file under `LeanUnitary/` and `LeanUnitary.lean`, except:

- `LeanUnitary/Spec.lean`: frozen; your copy is replaced.
- The names and statements of the milestone theorems in `LeanUnitary/Claims.lean`. Change only
  their proofs.

Do not change `lakefile.toml`, `lake-manifest.json` or `lean-toolchain`, and do not run
`lake update`. Add every new module to `LeanUnitary.lean`, because the whole library must
build: **a build error anywhere scores nothing**. `sorry` elsewhere is allowed while you work;
it only disqualifies the milestones that depend on it.

### Not allowed in submission sources

Checked textually (comments are ignored) before anything is built:

- `axiom` declarations
- `native_decide`, `Lean.ofReduceBool`, `implemented_by`, `extern`, `csimp`, `unsafe`
- running code at build time: `#eval`, `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `initialize`
- syntax and elaborator extensions: `macro`, `macro_rules`, `syntax`, `elab`, `elab_rules`,
  `declare_syntax_cat`, `@[command_elab]`, `@[term_elab]`, `@[tactic]`
- `set_option debug.skipKernelTC`

Use `decide`, `norm_num`, `simp` and ordinary Mathlib tactics. Experiment with `#eval` in scratch
files outside `LeanUnitary/`.

## Metric

| metric             | direction | meaning |
|--------------------|-----------|---------|
| `milestone_points` | max       | sum of the points of the accepted milestones (0 to 19) |

A milestone is accepted only if all of the following hold:

1. `lake build LeanUnitary LeanUnitary.Claims` succeeds, with the frozen spec in place.
2. Every declaration in every `LeanUnitary.*` module is re-checked by the Lean kernel on top of
   a fresh import of the dependencies, so the proof terms themselves are verified.
3. Its theorem in `LeanUnitary.Claims` has exactly the frozen statement.
4. It depends on no axioms other than `propext`, `Classical.choice` and `Quot.sound`, so no
   `sorry` anywhere in its dependencies.

`details.milestones` gives each milestone's status (`proved`, `missing`, `rejected`) and the
reason for any rejection. A failed build reports the tail of the build log.

## Parameters

None.

## Test mode

There is no held-out data: the statements are public and the proofs are checked, not sampled.
`--final` scores exactly like validation.

## Timing

The first evaluation on a machine downloads and builds the pinned Mathlib and LeanQuantum
once. After that, an evaluation takes as long as building your modules plus about a minute of
checking.

## What the evaluator will not do

- It will not credit a theorem whose statement differs from the frozen milestone, however
  close.
- It will not accept `sorry`, new axioms or compiler-trusting tactics, however the proof is
  built.
- It will not use your copies of the spec, build config or dependencies.
- It will not reward theorems that are not milestones.
