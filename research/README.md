# Research notes

Exploratory work that informs the Lean formalization but is not part of it: plain Python
(numpy, scipy) with no dependency on Lean, and nothing here is part of the Lean build.

| directory | contents |
|---|---|
| [`decomposition.tex`](decomposition.tex) | Paper: block-ZXZ with one extra CNOT fold per node, $\tfrac{21}{48}4^n-\tfrac32 2^n+2$ CNOTs with the existence proof and circuit diagrams. |
| [`experiments/`](experiments/README.md) | Numerical exploration of CNOT-count improvements over block-ZXZ |

Run the scripts from inside their directory, e.g. `cd experiments && python3 zxz.py` (needs numpy and
scipy).
