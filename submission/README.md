# Optimized Block-ZXZ Decomposition

 - `decomposition.py` implements the improved decomposition and validates reconstruction error
 - `benchmark.py` compares the improved decomposition with the baseline
 - `diagram.tex` is the diagram of the Lean formalization (`../LeanUnitary/`), rendered to `diagram.pdf` and `diagram.png`

## Requirements

Python 3.10+, NumPy, and SciPy; the benchmark also requires Matplotlib:

```bash
python -m pip install numpy scipy matplotlib
```

Tested with Python 3.13, NumPy 2.3.2, SciPy 1.18.1, and Matplotlib 3.10.5.

## Usage

To reproduce the table:
```bash
python decomposition.py 3 4 5 6 --seed 0 --samples 1
```

To reproduce the two-panel benchmark figure:
```bash
python benchmark.py --nmin 3 --nmax 10 --samples 1 --seed 0
```
