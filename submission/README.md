# Optimized Block-ZXZ Decomposition

`decomposition.py` implements extra-fold Block-ZXZ synthesis and reconstruction checks
`benchmark.py` imports its helpers to compare baseline and improved synthesis

## Requirements

Python 3.10+, NumPy, and SciPy; the benchmark also requires Matplotlib:

```bash
python -m pip install numpy scipy matplotlib
```

Tested with Python 3.13, NumPy 2.3.2, SciPy 1.18.1, and Matplotlib 3.10.5.

## Usage

From this directory:
```bash
python decomposition.py 3 4 5 --seed 0 --samples 1
```

To reproduce the two-panel benchmark figure:
```bash
python benchmark.py --nmin 3 --nmax 10 --samples 1 --seed 0
```
