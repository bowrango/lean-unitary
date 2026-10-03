# Optimized Block-ZXZ Decomposition

`decomposition.py` implements extra-fold Block-ZXZ synthesis and reconstruction
checks, using algebraic Shende–Markov–Bullock two-qubit synthesis.
`benchmark.py` imports its helpers to compare baseline and improved synthesis;
these two scripts require no other repository files.

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

The positional arguments specify qubit counts (default: `3 4`). Each run
generates seeded Haar-random targets, reports CNOT counts and reconstruction
errors, and asserts the expected counts and a maximum entrywise error of
`1e-8`. Expected counts for 3, 4, and 5 qubits are 18, 90, and 402.

To reproduce the two-panel benchmark figure:

```bash
python benchmark.py --nmin 3 --nmax 10 --samples 1 --seed 0
```

This reports gate counts and runtimes and writes `bal_benchmark.pdf` (normalized
CNOT counts and logarithmic runtime). Use `--output path.pdf` to change the
destination. Both methods receive identical targets and use the same algebraic
two-qubit synthesis (three CNOTs, or two with a diagonal carry). Timings cover
complete synthesis, excluding target generation and plotting. Multiple samples
are plotted using median times; timings depend on hardware and numerical libraries.
Reconstruction checks are provided separately by `decomposition.py`.

## Python API

```python
from decomposition import decompose, circuit_matrix

circuit, diagonal = decompose(U)  # U is a 2**n × 2**n unitary, n >= 1.
reconstructed = diagonal @ circuit_matrix(circuit, n)
```

Gates appear in execution order as `("u", qubit, matrix)` or
`("cx", control, target)`. Qubit 0 is the least significant bit.
Inputs are assumed valid; the numerical pivot search assumes a resolved,
nonsingular path.
