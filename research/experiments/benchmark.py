"""Compare Block-ZXZ (zxz.py) with the pivot-gate construction (foldzxz_opt.py).

For each n, both synthesizers decompose the same Haar-random unitaries. The script reports the
CX count of each against its closed form, the wall-clock synthesis time, and the reconstruction
error, measured by simulating each circuit on random states.

Both methods share the same two-qubit leaves, and there are 4^(n-2) of them, so by default each
leaf is an exact placeholder block counted as 3 CX gates (2 when it may be synthesized up to a
diagonal). This times only the recursive decomposition, where the two methods differ. Use
--fit-leaves to synthesize the leaves numerically instead (slow for n >= 7).

Run with a numpy whose LAPACK is reliable (e.g. Apple Accelerate); see the supplement.

Usage: python3 benchmark.py [--nmin 3] [--nmax 10] [--samples 1] [--seed 0] [--fit-leaves]
"""
import argparse
import time

import numpy as np

import foldzxz_opt
import zxz
from core import cnot_count, random_unitary
from foldzxz import cnot_formula, zxz_formula


def placeholder_leaf(U, want_diag, seed=0):
    """Exact two-qubit leaf, counted as the CX cost of the standard construction."""
    return [("block", (0, 1), U, 2 if want_diag else 3)], np.eye(4, dtype=complex)


def apply(circ, psi, n):
    """Apply a circuit to a batch of states psi (shape 2^n x k), qubit q = bit q of the index."""
    psi = psi.copy()
    k = psi.shape[1]
    for g in circ:
        kind = g[0]
        if kind == "u":
            q, M = g[1], g[2]
            v = psi.reshape(2 ** (n - 1 - q), 2, 2 ** q, k)
            psi = np.einsum("ab,xbyk->xayk", M, v).reshape(-1, k)
        elif kind == "cx":
            c, t = g[1], g[2]
            v = psi.reshape([2] * n + [k])            # axis i is qubit n-1-i
            ac, at = n - 1 - c, n - 1 - t
            idx = [slice(None)] * (n + 1)
            idx[ac] = 1
            sub = v[tuple(idx)]                          # control = 1
            at_sub = at - (1 if at > ac else 0)
            v[tuple(idx)] = np.flip(sub, axis=at_sub)
            psi = v.reshape(-1, k)
        elif kind == "block":
            qs, M = g[1], g[2]
            assert tuple(qs) == (0, 1), "leaf blocks act on the two lowest qubits"
            v = psi.reshape(2 ** (n - 2), 4, k)
            psi = np.einsum("ab,xbk->xak", M, v).reshape(-1, k)
        else:
            raise ValueError(kind)
    return psi


def error(U, circ, diag, n, n_states=4, rng=None):
    """max |U psi - diag (circuit psi)| over random states, up to one global phase."""
    rng = rng or np.random.default_rng(0)
    d = 2 ** n
    psi = rng.normal(size=(d, n_states)) + 1j * rng.normal(size=(d, n_states))
    psi /= np.linalg.norm(psi, axis=0)
    out = np.diag(diag)[:, None] * apply(circ, psi, n)
    ref = U @ psi
    phase = np.vdot(out.ravel(), ref.ravel())
    phase /= abs(phase)
    return float(np.max(np.abs(ref - phase * out)))


def run(synth, U, n):
    t = time.perf_counter()
    circ, diag = synth(U, n)
    return circ, diag, time.perf_counter() - t


def compare(ns, samples=1, seed=0, fit_leaves=False):
    """Yield one result dict per (n, sample): CX counts, synthesis times and errors of both."""
    saved = zxz.leaf, foldzxz_opt.leaf
    if not fit_leaves:
        zxz.leaf = foldzxz_opt.leaf = placeholder_leaf
    try:
        rng = np.random.default_rng(seed)
        for n in ns:
            for _ in range(samples):
                U = random_unitary(2 ** n, rng)
                c0, d0, t0 = run(zxz.synth, U, n)
                c1, d1, t1 = run(foldzxz_opt.synth, U, n)
                yield dict(n=n, zxz_cx=cnot_count(c0), ours_cx=cnot_count(c1),
                           zxz_time=t0, ours_time=t1,
                           zxz_err=error(U, c0, d0, n), ours_err=error(U, c1, d1, n))
    finally:
        zxz.leaf, foldzxz_opt.leaf = saved


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--nmin", type=int, default=3)
    ap.add_argument("--nmax", type=int, default=10)
    ap.add_argument("--samples", type=int, default=1)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--fit-leaves", action="store_true",
                    help="synthesize two-qubit leaves numerically instead of placeholder blocks")
    args = ap.parse_args()

    print(f"{'n':>3} {'ZXZ CX':>10} {'ours CX':>10} {'saved':>7} {'formulas':>8} "
          f"{'ZXZ time':>10} {'ours time':>10} {'ratio':>6} {'ZXZ err':>8} {'ours err':>8}")
    for r in compare(range(args.nmin, args.nmax + 1), args.samples, args.seed, args.fit_leaves):
        n = r['n']
        ok = "ok" if (r['zxz_cx'], r['ours_cx']) == (zxz_formula(n), cnot_formula(n)) else "MISMATCH"
        print(f"{n:>3} {r['zxz_cx']:>10} {r['ours_cx']:>10} {r['zxz_cx'] - r['ours_cx']:>7} {ok:>8} "
              f"{r['zxz_time']:>9.2f}s {r['ours_time']:>9.2f}s {r['ours_time'] / r['zxz_time']:>6.1f} "
              f"{r['zxz_err']:>8.1e} {r['ours_err']:>8.1e}", flush=True)


if __name__ == "__main__":
    main()
