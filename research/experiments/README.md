# Experiments: beating block-ZXZ

Findings from an exploration of whether the CNOT count of exact n-qubit unitary synthesis can be
pushed below the best known construction, block-ZXZ (Krol & Al-Ars, arXiv:2403.13692), in a form
that could be proved in Lean. Everything here is numerical prototyping in Python; nothing is
formalized. Conventions match `LeanUnitary/Spec.lean` (qubit `q` = bit `q`, top qubit = most
significant bit, circuits applied first to last, the same `Ry`/`Rz`).

Counts are compared by the **lower-bound ratio**: the mean over n = 3..8 of c(n) / ⌈(4^n − 3n − 1)/4⌉,
where 1 means meeting the Shende–Markov–Bullock lower bound. Block-ZXZ scores 1.657.

## Conclusions

1. **Block-ZXZ is reproduced exactly**: 3, 19, 95 CNOTs for n = 2, 3, 4 (`python3 zxz.py`,
   reconstruction error ~1e-15). Its leading coefficient is 22/48; the lower bound's is 12/48.
2. **The whole gap is in the leading coefficient**, and 18/48 of block-ZXZ's 22/48 is *glue*: the
   three multiplexed rotations per recursion node, which carry one parameter per CNOT and are
   parametrically redundant. Glue is concentrated at the bottom of the recursion tree.
3. **Before section 10, no provable improvement had been found.** Each idea below either fails, has
   a small ceiling, or reduces to a known open problem:

| lever | outcome |
|---|---|
| spend unused output-diagonal freedom on the last 2-qubit leaf (17 instead of 18) | fails: the 1-CNOT class is unreachable |
| synthesis up to a diagonal at every node | ceiling ≈ 21.1/48; already saturated at 3 qubits |
| richer glue: uniformly controlled gates (UCGs) | 24/48, worse |
| cheaper 1-control, 2-target multiplexors | none: 8 CNOTs, demultiplexing is optimal |
| six general 2-qubit gates for 3 qubits (18 CNOTs) | works numerically; proof is a recognized open problem |
| provably near-optimal small base cases | the main lever (→ 12/48 as base size grows), but open even at 3 qubits |
| glue multiplexed over fewer qubits: round-robin Pauli nodes (section 8) | **18/48 numerically** (93 CNOTs at n = 4, 381 at n = 5); surjectivity conjectured, unproved |

4. **3-qubit numbers**: block-ZXZ gives 19 exact / 18 up to a diagonal; numerical minima are
   14 exact / 13 up to a diagonal. The numerical optimum has no piece-by-piece structure that
   eigen-, polar- or KAK-type algebra produces, so closing the gap needs a genuinely new
   constructive idea.
5. **For the formalization**, the realistic target is a verified block-ZXZ plus small, provable
   constant-term gains. That turned out to be too pessimistic: section 10 gives a proved
   leading-coefficient improvement (21/48) whose formalization is substantial but routine.
6. **The most promising unproved lever** (section 8) moves the glue, not the leaves. Splitting k
   qubits per node, with each glue multiplexed only over the bottom register, needs 4^k − 1 glues
   instead of block-ZXZ's 3·2^(k−1)(2^k − 1). A "round-robin" Pauli sequence has full Jacobian rank
   at every tested size and fits Haar-random targets exactly. Taken to k = n − 2 it would give
   6·4^(n−2) − 3 CNOTs (18/48; lower-bound ratio 1.483 vs 1.657). It generalizes block-ZXZ (k = 1), but
   global surjectivity for k ≥ 2 is unproved. No construction reaching the lower bound itself is
   provable today: the best numerical one (arXiv:2511.16736, lower-bound counts for n ≤ 5) is
   conjectural too.
7. **Proved improvement (section 10): 21/48.** Top-qubit gates chosen by a parity rule and the
   intermediate value theorem let every block-ZXZ node fold one more CNOT: c(n) = (21·4^n − 72·2^n + 96)/48,
   i.e. 18 / 90 / 402 CNOTs at n = 3 / 4 / 5, verified end to end. Lower-bound ratio 1.576 vs 1.657. The same
   fold on the output side works numerically (17 CNOTs at n = 3, 20/48 overall), but its proof is open.
8. **A proof of the k = 2 case was attempted and not found** (section 9). Every standard provable
   route is rigid at 18 glues, and the 15-glue sequences have hundreds to thousands of isolated
   solutions per target (k = 1 has 2^d). So no CSD-style formula exists, and a proof must be
   existential. Naive degree theory fails even for the proved k = 1 case (signed count 0). At d = 2
   the claim is itself a parameter-tight 3-qubit universality statement.

## Files

| file | contents |
|---|---|
| `core.py` | circuits and their matrices, CNOT counting, Gray-code multiplexed rotations (2^(n−1) CNOTs), demultiplexing, the block-ZXZ factorization |
| `fit.py` | numerical fitting of fixed-CNOT templates (2-qubit leaves: 3 CNOTs exact, 2 up to a diagonal) |
| `fitlow.py` | template fitting with a free diagonal restricted to chosen qubits (fair accounting) |
| `zxz.py` | recursive block-ZXZ synthesis with both optimizations of arXiv:2403.13692 |
| `probe.py` | Jacobian-rank test: can a CNOT skeleton with free single-qubit gates reach all of U(2^n)? |
| `invariants.py` | 2-qubit CNOT-count invariants γ(U) and the closed-form Z⊗Z roots |
| `idea1.py`, `idea2*.py`, `rank_test.py`, `solve17.py`, `reach*.py` | the 17-CNOT experiment (negative) |
| `seq2q.py` | products of general 2-qubit gates on a fixed pair sequence (six-gate experiment) |
| `updiag.py` | minimum CNOT count of a 3-qubit unitary, exact vs up to an output diagonal |
| `ucg.py`, `ucg_chain.py` | uniformly controlled gates: CNOT cost, and universality of UCG chains |
| `muxcost.py`, `mux7*.py` | cost of a 1-control, 2-target multiplexor |
| `pauli_glue.py`, `pg_exact.py`, `pg_cx.py` | k = 2 multiplexed-Pauli nodes: exact Jacobian rank of glue sequences (section 8) |
| `pauli_glue_k.py`, `pg_k_cx.py` | the same for any k; `round_robin` builds the round-robin sequence |
| `pg_fitk.py` | global fit of a k-level node to Haar-random targets (`python3 pg_fitk.py k nL targets`) |
| `rr_compile.py` | compiles a fitted node (k = n − 2) to an explicit CNOT circuit and checks it |
| `rr_count.py` | CNOT recursion choosing the best k at each n; lower-bound ratio if the conjecture were proved |
| `rr_solutions.py`, `rr_count_solutions.py`, `seq_solcount.py` | distinct solutions per target and their signed count (section 9) |
| `rr_degree.py` | local degree of the node map at a solution, modulo the gauge torus (section 9) |
| `foldzxz.py` | **block-ZXZ with the extra C-side fold at every node: 18 / 90 / 402 CNOTs at n = 3 / 4 / 5 (section 10)** |
| `benchmark.py` | Block-ZXZ (`zxz.py`) vs the pivot construction (`foldzxz_opt.py`): CX counts, synthesis time and reconstruction error for n = 3…10 |
| `balanced_figs.py` | writes every figure of `../supplementary.tex` (balanced-split pivot, paper Sec. II.A–II.C) as PDFs in `../figures/`, via `foldzxz_opt.py`; needs matplotlib and LaTeX |
| `fold_ivt.py`, `pfaff.py`, `pfaff_general.py` | parity rule, Pfaffian sign change and IVT root for the fold condition |
| `dfold.py`, `dfold_synth.py` | both folds by numerical root-finding: verified 17-CNOT 3-qubit circuits |
| `skel3.py` | universality of the 3-qubit block-ZXZ skeleton with one CNOT deleted |

## 1. Where the CNOTs go

### Structure of one block-ZXZ node (m = 2^(n−1))

Time order: `Wc, Dc'' (m−1), Wb, H·Db·H (m), Vb, Da'' (m−1), Va` — four (n−1)-qubit
sub-unitaries and three multiplexed Rz rotations on the top qubit. The paper's two optimizations:
the CNOT of each outer multiplexor next to a top-qubit Hadamard becomes a CZ folded into the
middle factor (−2 per node), and every sub-unitary but the last is synthesized up to a diagonal
that migrates into the next one (−1 per non-final 2-qubit leaf).

### Why the formulas look different

Recursive constructions satisfy `c(n) = 4c(n−1) + β·2^(n−1) + γ`, with solution
`A·4^n − (β/2)·2^n + const`. The `−2^n` term is the truncation of a geometric series, not a
saving. The lower bound, `(4^n − 3n − 1)/4`, is a parameter count (each CNOT adds at most 4
parameters); its `−3n/4` is just the free first layer of single-qubit gates. Only the leading
coefficient matters.

### The glue

Block-ZXZ's 22/48 splits as **+18/48 glue**, −2/48 CZ folds, **+6/48 two-qubit leaves**. A node's
four children already carry 4^m parameters; the glue's 3·2^(m−1) parameters are exactly the
demultiplexing gauge, so the glue CNOTs contribute no net parameters. A node at level m costs
~2^m glue CNOTs and there are 4^(n−m) of them, so level m contributes ~4^n·2^(−m): the glue sits
at the bottom of the tree. With an m0-qubit base case,

```
a ≈ c(m0)/4^m0 + (3/2)·2^(−m0)        (glue term = 72·2^(−m0) in 48ths)
```

e.g. 22/48 today (2-qubit base), ≈18.25/48 with an exact 14-CNOT 3-qubit base, ≈15.6/48 with a
~60-CNOT 4-qubit base, → 12/48 as the base grows.

## 2. Tools

- **CNOT-count invariants** (Shende, Bullock, Markov): for U ∈ U(4), det U = 1,
  γ(U) = U(Y⊗Y)Uᵀ(Y⊗Y). U needs ≤ 2 CNOTs iff tr γ is real; ≤ 1 CNOT iff tr γ = 0 and γ² = −I.
  A diagonal changes the class only through its Z⊗Z part. `tr γ(e^{−igZZ}V)` is a single
  sinusoid in 2g, so a leaf's two "2 CNOTs up to a diagonal" choices have a closed form
  (`zz_roots_two_cnot_exact`, checked against a grid search on 200 unitaries).
- **Jacobian rank** of a circuit template (`probe.py`) — necessary, far from sufficient.
- **Accounting rule.** Only allow a free diagonal on qubits whose diagonal the next element
  genuinely absorbs: a diagonal on the lower qubits migrates through multiplexors; a diagonal
  involving the top qubit is itself a multiplexed Rz (~4 CNOTs at 3 qubits). A node's full output
  diagonal is free because the parent absorbs any diagonal on its lower register; a UCG's full
  diagonal is free because the next UCG absorbs it. Violating this rule produced one false lead
  (section 7).

## 3. Experiment: a 17-CNOT 3-qubit node up to a diagonal (negative)

**Idea.** The parent absorbs any 3-qubit diagonal (8 phases) on a node's output, but block-ZXZ
only uses its lower part. The top-qubit part Δ = I ⊕ Λ changes the matrix the last
demultiplexing diagonalizes (`M·Λ`, M = A1·A2†). Could Λ make the last leaf a 1-CNOT gate (17
instead of 18, i.e. 21.25/48 overall)?

- Without the chain constraint, every M ∈ U(4) factors as P·T·E·T†·Q (P, Q, E diagonal, T a
  1-CNOT circuit): exact on 20 random and several structured unitaries; fails with 0 CNOTs.
- In the chain, the previous leaf's diagonal lands on the last leaf, and pushing it through
  (T·δ = δ'·T' with 1 CNOT) fails generically. The demultiplexing gauge cancels out of it.
- The free parameters (Λ: 3 effective, output Z⊗Z: 1) move the last leaf's class with full
  Jacobian rank 3, but a global search reaches only 7e-3 to 9e-2 from the 1-CNOT class, over all
  root branches and all 24 eigenvalue orderings. The 1-CNOT class sits on an edge of the Weyl
  chamber, outside the reachable set.
- Each leaf-to-leaf diagonal carries exactly one useful parameter (its Z⊗Z part), and every
  2-CNOT leaf consumes it; a 1-CNOT leaf needs three, on a boundary of the class space.

## 4. Experiment: six general 2-qubit gates for 3 qubits (open problem)

**Ansatz.** U = G6(12) G5(01) G4(12) G3(01) G2(12) G1(01), each G a general 2-qubit gate
(≤ 3 CNOTs). Parameters 16 + 12 + 4·9 = 64 = dim U(8): six is exactly the two-qubit-gate lower
bound ⌈(4^n − 3n − 1)/9⌉.

- Exact fits (~1e-15) for 8 random unitaries, Toffoli and QFT3 (alternating pattern), and for
  the cyclic (01)(12)(02) pattern; five gates fail (~1e-1). Numerically this is an
  **18-CNOT** 3-qubit decomposition (17 up to a diagonal).
- Six-gate sufficiency is a recognized open problem: reported numerically by DiVincenzo–Smolin
  (1995); Yu–Ying proved six are necessary; arXiv:2609.22176 (Sept 2026) proved full local rank
  for every six-gate architecture and lists global surjectivity as open ("the obstruction must
  be global"). A Lean proof along these lines would require resolving it.
- Related: deleting any single CNOT from the 19-CNOT block-ZXZ skeleton keeps full Jacobian rank
  (64); shapes stay full rank down to ~14 CNOTs. Local rank is not the bottleneck.

## 5. Lever: synthesis up to a diagonal (ceiling ≈ 0.9/48)

Numerically, a 3-qubit unitary needs **14** CNOTs exactly and **13** up to an output diagonal
(12 fails). An m-qubit diagonal is worth only ~(2^m − m − 1)/4 CNOTs — its global phase and m
local Z phases duplicate single-qubit gates: 1 at m = 3 (already collected by block-ZXZ, 19 vs
18), 2.75 at m = 4, 6.5 at m = 5. Perfect use at every level m ≥ 4 lowers the coefficient only
from 22/48 to about **21.1/48**: diagonals have 2^m parameters against the node's 4^m.

## 6. Lever: richer glue — uniformly controlled gates (negative)

A UCG (an arbitrary u_j ∈ U(2) on the target per control state) with k controls costs
**2^k − 1 CNOTs up to a diagonal** (1, 3, 7 for k = 1, 2, 3), ~3 parameters per CNOT versus 1 for
multiplexed rotations. But adjacent UCGs share a full diagonal gauge (UCG × diagonal = UCG), so
each contributes only ~2^n net parameters: a 3-qubit chain needs 8N + 8 ≥ 64, i.e. **7 UCGs
(21 CNOTs)** — 6 fail (~1e-1), 7 are exact, as predicted. Net ≈ 2 parameters per CNOT, a leading
coefficient of 1/2 = 24/48 (consistent with Bergholm et al. 2005), worse than block-ZXZ's 22/48
(≈ 2.18 parameters per CNOT, thanks to its cheap near-optimal 2-qubit leaves).

## 7. Multiplexor cost (negative, and an accounting pitfall)

A 1-control, 2-target multiplexor B0 ⊕ B1 — the building block of block-ZXZ — appeared to fit
with 7 CNOTs, one fewer than demultiplexing (2 + 4 + 2). That was an artifact: the fit allowed a
free diagonal on all three qubits, and the top-qubit part of it is a multiplexed Rz. With only
the lower-qubit diagonal free (`fitlow.py`), the multiplexor needs **8 CNOTs** (7 fails at ~5e-2).
Algebraically, `L1 · (a·C3·b) · L2` with a 3-CNOT uniformly controlled gate C3 is block diagonal
only if every block a·M_x·b is diagonal, which forces θ00 + θ10 = θ01 + θ11 — not generic.
Demultiplexing is optimal for this piece.

## 8. Multiplexed Pauli glue: a conjectured 18/48 recursion (numerically universal, unproved)

**Why block-ZXZ pays 18/48 for glue.** A block-ZXZ node's three multiplexed rotations are
controlled by all n − 1 lower qubits (2^(n−1) CNOTs each). Unrolled over two levels, the node is
16 grandchildren on the bottom n − 2 qubits L plus **18** glue units, each a rotation multiplexed
over L (2^(n−2) CNOTs): 12 on the second qubit s, and 3 × 2 on the top qubit t (a rotation
controlled by s and L is a Z_t and a Z_sZ_t rotation, each multiplexed over L). A parameter count
says 15 would do: 16 children carry 16·4^(n−2) = 4^n parameters, and each glue's 2^(n−2)
parameters are exactly cancelled by the lower-diagonal gauge next to it. In general a k-level
node needs 4^k children on L and **4^k − 1** glues, against block-ZXZ's 3·2^(k−1)(2^k − 1).

**The ansatz.** Children C_i (arbitrary unitaries on L) alternate with glues
G_i = Σ_j |j⟩⟨j|_L ⊗ exp(−iθ_{ij} P_i / 2), where P_i is a Pauli on the top k qubits. For k = 1 this is
exactly block-ZXZ (Z, X, Z). Findings (exact analytic Jacobians, not finite differences, which
were misleading here):

- **Hidden gauges kill most sequences.** Weight-1 glues in block-ZXZ order (`Zs Xs Zs` blocks
  separated by `Zt Xt Zt`) have rank 232/256 at n = 4: a t-rotation multiplexed only over L
  commutes with every s-operation, which the neighbouring blocks absorb. Random weight-1
  sequences almost never reach full rank; sequences with some weight-2 Paulis often do.
- **Round robin works.** Cycling through the top qubits, each alternating Z, X
  (`q0:Z q1:Z q0:X q1:X q0:Z …`), has **full rank for every size tested**: k = 2 (n = 3, 4, 5),
  k = 3 (n = 4, 5, 6), k = 4 (n = 5, 6). Only weight-1 glues, no CNOTs between top qubits. A KAK-shaped
  k = 2 sequence (local Euler rotations, then XX·YY·ZZ, then local Euler rotations) also has full rank.
- **Global fits** (`pg_fitk.py`, manifold Levenberg–Marquardt, Haar-random targets, residual
  < 1e-10 counted as solved): k = 2, n = 3: 6/6; k = 2, n = 4: 3/4, plus 8/8 for a variant with
  one top CNOT; k = 3, n = 4: 6/6; k = 2, n = 5: 3/3; **k = 3, n = 5: 4/4** (the k = n − 2 case, 381 CNOTs); k = 4, n = 5 (1-qubit L): 2/4 at first, plus target 1 on its first fresh restart (residual 1e-4 → 2e-12); the retry of target 3 (4e-4) was still running when this was written. The one failure retried (k = 2, n = 4, residual 3e-3) was a
  local minimum: a fresh start solved it on the fifth attempt (1.7e-11). No sign of an unreachable
  region.
- **Explicit circuit** (`rr_compile.py`): a Haar-random 4-qubit unitary compiled to **93 CNOTs**
  (block-ZXZ: 95), error 4.5e-12. Glues are Gray-code multiplexed Rz (conjugated by H on
  the target for X), children are 2-CNOT-up-to-diagonal 2-qubit gates whose diagonals commute
  through the next glue, and the last child is exact.

**Counts if true.** With k = n − 2 (all children 2-qubit gates on the bottom pair, all glue
multiplexed over that pair) the circuit is 4^(n−2) layers of "2-qubit gate + multiplexed
single-qubit rotation": **c(n) = 6·4^(n−2) − 3**, leading coefficient **18/48**. That is the best
choice of k at every n ≥ 4 (`rr_count.py`):

| n | 3 | 4 | 5 | 6 | 7 | 8 | score (mean ratio, n = 3..8) |
|---|---|---|---|---|---|---|---|
| block-ZXZ | 19 | 95 | 423 | 1783 | 7319 | 29655 | 1.657 |
| proved k ≤ 2 | 19 | 93 | 409 | 1713 | 7009 | 28353 | 1.605 (21/48) |
| proved k ≤ 3 | 19 | 93 | 381 | 1615 | 6561 | 26337 | 1.532 (19.5/48) |
| all k | 19 | 93 | 381 | 1533 | 6141 | 24573 | 1.483 (18/48) |
| lower bound | 14 | 61 | 252 | 1020 | 4091 | 16378 | 1 |

18/48 is the ceiling of this family with 2-qubit leaves: each layer adds 16 net parameters for 6
CNOTs (2.67 per CNOT, against the ideal 4), because a glue still spends one CNOT per parameter.
Larger leaves are worse (3-qubit leaves: 19.5/48).

**Status and what a proof needs.** This is a conjecture: *for every k ≥ 1 and every lower register
L with at least one qubit, the round-robin product C_0 G_1 C_1 … G_{4^k−1} C_{4^k−1} is surjective
onto U(2^k·2^|L|)*. k = 1 is block-ZXZ, proved via polar decompositions; nothing like that is
known for k ≥ 2. Full rank everywhere tested gives full rank almost everywhere (analyticity), but
global surjectivity is exactly the gap that Wierichs–Kottmann–Killoran (arXiv:2511.16736) leave
open for their brick-wall circuits. Their circuits reach the lower bound itself numerically (14,
61, 252 CZ for n = 3, 4, 5), but they found no analytic parameter routine and state surjectivity as
Conjecture 3 ("critical values have codimension ≥ 2"). What the round-robin family offers over
those circuits is structure: it contains a proved case (k = 1), children are unconstrained
unitaries on a fixed register, and the glue is diagonal up to fixed Hadamards. That makes an
inductive, block-matrix proof plausible in a way it is not for brick walls. **k = 2 is the
natural first target**: it already lowers the leading coefficient (22 → 21/48) and improves every
n ≥ 4.

## 9. Attempted proof of the k = 2 case (not achieved; why it is hard)

**Clean statement.** Let the top qubits be t, s and the lower register L have dimension d ≥ 2. Pushing
each child's cumulative product through the glue gives the node as

    U = (I ⊗ W) · ∏_{i=15..1} exp(−i P_i ⊗ H_i / 2),     W ∈ U(d),  H_i ∈ Herm(d) arbitrary,

with P_i the round-robin Paulis (t:Z, s:Z, t:X, s:X, …). The children are gone; the "angles" are
operators on L. The conjecture: this map onto U(4d) is surjective. For k = 1 the same
statement (Z, X, Z) is block-ZXZ, and it is literally the cosine–sine decomposition: a product C·exp(−iZ⊗Θ)·C'
is an arbitrary block-diagonal A ⊕ B (A = C e^{−iΘ} C', B = C e^{iΘ} C'), so C Z C X C Z C = K · e^{−iX⊗Θ} · K'.

**Reformulation used in the attempt.** Grouping each t-glue with its two neighbouring children
gives U = T8 · S7 · T7 · … · S1 · T1. Here T_i is an arbitrary t-multiplexed L-unitary
(|0⟩⟨0|⊗A + |1⟩⟨1|⊗B, in the Z basis of t for odd i and the X basis for even i), and S_i is a bare
s-rotation multiplexed over L in the fixed computational basis. The gauge is a d-dimensional
diagonal torus per S_i, which gives 8·2d² + 7d − 7d = 16d².

**Why the standard tools don't reach 15.** Every provable step available (the k = 1 lemma on any
split, CSD, demultiplexing, the AI/AIII Cartan decompositions in the magic ⊗ computational basis)
produces a diagonal on (other top qubit ⊗ L) with 2d independent angles. As glues multiplexed over L
that is a pair, e.g. `Zs` + `ZsZt`, costing two glues. Assembled, every route gives 18 glue units,
which is block-ZXZ unrolled. Those decompositions are rigid (fibre = gauge), so their freedom cannot
be spent to merge glues. The AI route (U = O·A·O', with A the multiplexed XX/YY/ZZ torus, which is
cheap) fails on dimension: expressing an element of O(4d) needs about 8d² parameters, but 6 local
glues with complex L-children supply only about 7d².

**Solution counting: no CSD-type formula exists for these sequences.** Constructive decompositions
have few solutions per target: k = 1 at d = 2 has exactly **4** (saturated over 400 starts; 2^d
per-state sign choices). For k = 2 at d = 2, every converged start gives a *new* isolated solution
(kernel at each solution = the 30-dimensional gauge, checked): **412 distinct solutions from 412 converged starts**, no repeats (with equally likely basins that would mean ≳ 10^5 solutions; unequal basins make it a weaker lower bound), local degrees +204 / −208. The same holds for the
KAK-shaped sequences (91/91 and 81/81 distinct). So the parameters are roots of a high-degree
system with no reason to have a closed form, the same situation Wierichs et al. report for brick
walls. A proof has to be existential.

**Degree theory, and why the naive version fails.** The gauge torus acts freely, so the node
descends to F̄: M/T → U(4d) between compact, connected, oriented manifolds of equal dimension
16d². deg F̄ ≠ 0 would prove surjectivity. But the local degrees (`rr_degree.py`) have mixed signs,
and for the *proved* k = 1 case the four solutions are +2 −2: oriented degree 0, and an even count, so
the mod-2 degree is 0 too. Degree can only work after quotienting by the solution symmetries
(per-state sign flips for k = 1; for k = 2, the Z_t, X_t, Z_s, X_s insertions that commute with the
L-children and flip the sign of glues between two others give at least 11 involutions). Then all
solutions of one target must be counted exactly. That count needs certified polynomial homotopy
continuation in 64 real dimensions, and the result would still not be expressible in Lean (Mathlib
has no degree theory).

**Hardness in context.** At d = 2 the k = 2 statement *is* a parameter-tight 3-qubit claim: 15
one-parameter couplings exp(−iP ⊗ n·σ) on a line t–L–s. So a proof for all d includes a tight
3-qubit universality result, a class where the literature has no proof (six-gate, 14 CNOT,
brick walls). Block-ZXZ at n = 3 is also tight but provable, and the difference is visible in
the solution count (a handful vs thousands).

**Slack does not help at k = 2, but exists at k ≥ 3.** A k = 2 node has no CZ folds, so 16 glues
already ties block-ZXZ (16 + 6 = 22/48): only the tight count 15 gains. For a k-node with g glues
the glue term is 12g/(2^k(2^k − 1)) (in 48ths), so it beats block-ZXZ iff g < 74.7 for k = 3
(minimum 63; block-ZXZ unrolled is 84) and g < 320 for k = 4 (minimum 255; unrolled 360). A non-tight
k = 3 construction (64–74 glues) has spare parameters, but the natural way to spend them fails
on a count. Saving one glue at a demultiplexing step needs the diagonal's 2d angles to pair up (a doubly
degenerate spectrum). Eigenvalue coincidences of a unitary have codimension 3 each (von
Neumann–Wigner), so forcing d of them costs 3d parameters to save d. Every provable route found
stays at 84. What does work is spending free parameters on conditions of codimension 1, which is
the fold of section 10.

**Status.** No proof. The concrete conjecture, the reformulations, the k = 1 ↔ CSD
correspondence, the rigidity of all standard routes, and the solution-count evidence that any
proof must be non-constructive are recorded here as the starting point for a follow-up to
arXiv:2511.16736.

## 10. Result: one more fold per block-ZXZ node, 21/48 with an existence proof

**Construction.** Each block-ZXZ node folds one CNOT of each outer multiplexor into the middle
factor (as a CZ). It cannot fold two because a rotation R_z(φ) sits between the multiplexor's last two
CNOTs, CX(q0, top)·CX(q_{n−2}, top). φ is a Walsh component of the multiplexor's angles. The
eigenvalue order and the square-root branches are free, so φ can be made exactly 0 iff the
eigenphases μ of the relevant unitary split into two halves with **equal sums mod 2π**. Then both
CNOTs become CZs, I ⊕ Z_{q0}Z_{q_{n−2}}, and fold. For the input-side multiplexor the relevant
unitary is the block-ZXZ factor C. Single-qubit gates on the top qubit before and after the node
are free and change C. With them:

    c(n) = 4 c(n−1) + 3·2^(n−1) − 6,  c(2) = 3   ⇒   c(n) = (21·4^n − 72·2^n + 96)/48

| n | 3 | 4 | 5 | 6 | 7 | 8 | LB ratio |
|---|---|---|---|---|---|---|---|
| block-ZXZ | 19 | 95 | 423 | 1783 | 7319 | 29655 | 1.657 |
| **with the C-side fold (proved below)** | **18** | **90** | **402** | **1698** | **6978** | **28290** | **1.576** |
| with both folds (A side unproved) | 17 | 85 | 381 | 1613 | 6637 | 26925 | 1.495 |

The leading coefficient drops from 22/48 to **21/48**, and 18 CNOTs for a general 3-qubit
unitary beats the best published analytic count (19).

**Theorem (C-side fold).** For every U ∈ U(2^n), n ≥ 3, there is a top-qubit gate u = R_z(α)R_y(β*)
such that the block-ZXZ factor C of U·u has a balanced split with equal eigenphase sums.

*Proof sketch* (D = 2^(n−1); X, Y the top-row blocks of U; everything generic, and the general case
follows by compactness, see below):

1. **The condition is a sign change.** For C1 = C·det(C)^(−1/D) ∈ SU(D), the exterior power
   R = Λ^(D/2) C1 is real orthogonal of size N = C(D, D/2). The Hodge star gives a real structure because
   D/2 is even. "Some half-product of eigenvalues equals ±1" is equivalent to R having eigenvalue ±1,
   which is equivalent to P = Pf(R − Rᵀ) = ∏ 2 sin ψ_j = 0. P is a continuous, sign-changing
   polynomial (`pfaff.py` checks the real structure for D = 4).
2. **Involution.** Along u(β) = R_z(α)R_y(β), β = π swaps the top-row blocks, (X, Y) → (Y, −X).
   Since C = −i U_X† U_Y (unitary polar factors), this gives C(π) = C(0)⁻¹. With a continuous
   D-th root of det C, R(π) = (−1)^m R(0)ᵀ, and since N/2 is odd (Lucas), P(π) = (−1)^(m+1) P(0).
3. **Parity.** Writing det(cX + sY) = det X ∏(c + sτ_k) with τ_k the eigenvalues of X⁻¹Y, the phase
   winding gives m = #{τ_k in the upper half-plane} − D/2. R_z(α) rotates every τ_k by α, and the
   count changes by ±1 at each real-axis crossing, so some α makes m even.
4. With m even, P(π) = −P(0) and the intermediate value theorem gives β* ∈ (0, π) with P(β*) = 0. ∎

**Verification** (`foldzxz.py`, fully constructive: parity rule for α, eigenvalue-tracked scan plus
bisection for β*, 2-qubit leaves by the proved 3-CNOT / 2-CNOT-up-to-diagonal results):
n = 3: **18 CNOTs**, n = 4: **90 CNOTs**, error ~1e-15. n = 5: **402 CNOTs** (block-ZXZ 423), error 1.7e-14; two random targets per n. The sign relation P(π) = −P(0)
held on 20/20 targets at n = 3 and 8/8 at n = 4 after choosing α (`fold_ivt.py`). The root finder
succeeded on 300/300 targets at n = 3, with the fold condition exact at every root.

**Non-generic U.** Fix the CNOT skeleton of the 18-CNOT circuit (n = 3; analogously for every n).
The unitaries it realizes form the continuous image of a compact set of single-qubit gate
parameters, so a closed set. It contains all generic U, a dense set, so it contains every U. This
step is short to formalize.

**The A side (unproved; would give 20/48).** The output-side multiplexor needs the same condition
for A1A2†. Numerically both conditions hold together on 10/10 targets (`dfold.py`, 6 top-qubit
parameters), and `dfold_synth.py` builds verified **17-CNOT** exact 3-qubit circuits (error
~2e-15). The structure is dual: an output-side R_y(π) inverts the spectrum of A1A2† (just as an
input-side one inverts C's). But each involution also moves the other side's function, so the
1-D argument does not extend. A proof needs a 2-parameter topological lemma for the pair (f_C, f_A)
on the (input-angle, output-angle) torus. The obvious Poincaré–Miranda/Borsuk–Ulam forms don't
apply directly.

**For Lean.** The proof uses exterior powers, a Pfaffian, eigenvalue continuity along a path, the
IVT and a compactness closure. That is substantial Mathlib work, but it is a finished mathematical
argument, not an open problem.

## Open directions

- **Prove the round-robin conjecture for k = 2** (section 8): a block-matrix generalization of
  the block-ZXZ derivation with glue multiplexed over n − 2 qubits instead of n − 1. Worth 1/48
  on its own; each larger k proved moves toward 18/48. A proof for all k gives 18/48 and a
  lower-bound ratio of 1.483. A first step: a quick search for an algebraic peeling step (for example, one
  multiplexed rotation chosen by an eigenproblem that makes the remainder block-structured),
  guided by the numerical solutions from `pg_fitk.py`.
- **Provably near-optimal small blocks** (3 or 4 qubits) as recursion base cases: the only lever
  that moves the leading coefficient substantially. Any exact 3-qubit construction below 18 CNOTs
  up to a diagonal improves it by 0.75/48 per CNOT.
- **Six-gate sufficiency** for 3 qubits (section 4): resolving it constructively would give an
  18/17-CNOT base case.
- **A systematic search** over combinations of provable building blocks (2-qubit leaves, UCGs,
  multiplexed rotations, CZ folds) under the fair accounting rule, to close the question for
  block-structured constructions. Not run.

## References

- A. M. Krol, Z. Al-Ars, *Beyond Quantum Shannon: Circuit Construction for General n-Qubit Gates
  Based on Block ZXZ-Decomposition*, arXiv:2403.13692.
- V. V. Shende, S. S. Bullock, I. L. Markov, *Synthesis of quantum logic circuits*,
  quant-ph/0406176; and *Recognizing small-circuit structure in two-qubit operators*,
  quant-ph/0308045.
- P. Rakyta, Z. Zimborás, *Approaching the theoretical limit in quantum gate decomposition*,
  Quantum 6, 710 (2022).
- V. Bergholm, J. J. Vartiainen, M. Möttönen, M. M. Salomaa, *Quantum circuits with uniformly
  controlled one-qubit gates*, quant-ph/0410066.
- *Every architecture of six two-qubit gates is locally universal on three qubits*,
  arXiv:2609.22176.
- D. Wierichs, J. S. Kottmann, N. Killoran, *Unitary synthesis with optimal brick wall circuits*,
  arXiv:2511.16736 (lower-bound CZ counts for n ≤ 5, numerical; surjectivity conjectured).
- Z. Li, G. Zhang, X.-M. Zhang, *Reducing C-NOT counts for state preparation and block encoding
  via diagonal matrix migration*, arXiv:2603.16492.
