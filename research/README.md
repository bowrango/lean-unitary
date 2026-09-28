# Research notes

Exploratory work that informs the Lean formalization but is not part of it. The evaluators read
only `LeanUnitary/`, so nothing here affects scoring.

| directory | contents |
|---|---|
| [`decomposition.tex`](decomposition.tex) | Paper: block-ZXZ with one extra CNOT fold per node, $\tfrac{21}{48}4^n-\tfrac32 2^n+2$ CNOTs (18 for three qubits), with the existence proof and circuit diagrams. |
| [`stage2/`](stage2/README.md) | Numerical exploration of CNOT-count improvements over block-ZXZ: a reference implementation reproducing 3/19/95 CNOTs, where the gap to the lower bound comes from (multiplexor "glue", 18/48 of 22/48), and the levers tested with their outcomes. **Proved improvement: 21/48** (section 10): an extra CNOT fold per block-ZXZ node, justified by a parity rule plus the intermediate value theorem; 18 / 90 / 402 CNOTs at n = 3 / 4 / 5. Also: "round-robin" nodes whose glue is multiplexed over only the bottom qubits, numerically universal at 18/48 (93 CNOTs at n = 4) but unproved (section 8). |

Run the scripts from inside their directory, e.g. `cd stage2 && python3 zxz.py` (needs numpy and
scipy).
