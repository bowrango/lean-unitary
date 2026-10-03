#!/usr/bin/env python3
"""Compare baseline Block-ZXZ with the optimized extra-fold construction.

Requires decomposition.py, NumPy, SciPy, and Matplotlib; no other repository files.
Run: python benchmark.py --nmin 3 --nmax 10 --samples 1 --seed 0
Writes the comparison figure to bal_benchmark.pdf.
"""

from __future__ import annotations

import argparse
import platform
from pathlib import Path
from time import perf_counter

import matplotlib
import numpy as np
import scipy

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from decomposition import (
    H, Z, block_diag, block_zxz, cnot_count, cnot_formula,
    demultiplex, embed, leaf, mux_rot, random_unitary, synth, zxz_formula,
)


# Baseline synthesis


def baseline_synth(
    U: np.ndarray, n: int, want_diag: bool = False,
) -> tuple[list[tuple], np.ndarray]:
    """Block-ZXZ with the standard boundary folds and diagonal propagation."""
    if n == 1:
        return [("u", 0, U)], np.eye(2, dtype=complex)
    if n == 2:
        return leaf(U, want_diag)
    m, top = 2 ** (n - 1), n - 1
    A1, A2, B, C = block_zxz(U)
    Va, theta_a, Wa = demultiplex(A1, A2)
    Vc, theta_c, Wc = demultiplex(np.eye(m, dtype=complex), C)
    z = embed(Z, [n - 2], n - 1)
    Vb, theta_b, Wb = demultiplex(Wa @ Vc, z @ Wa @ B @ Vc @ z)

    mux_c = mux_rot(theta_c, n)[:-1]
    mux_a = mux_rot(theta_a, n)[::-1][1:]
    mux_b = [("u", top, H)] + mux_rot(theta_b, n) + [("u", top, H)]
    circuit = []
    carry = np.eye(m, dtype=complex)
    children = [Wc, Wb, Vb, Va]
    for i, (child, mux) in enumerate(zip(children, [mux_c, mux_b, mux_a, []])):
        sub, carry = baseline_synth(
            child @ carry, n - 1, want_diag=want_diag or i < len(children) - 1
        )
        circuit += sub + mux
    return circuit, block_diag(carry, carry)


def compare(ns, samples: int = 1, seed: int = 0):
    """Yield paired gate counts and synthesis times for each random target."""
    rng = np.random.default_rng(seed)
    for n in ns:
        for sample in range(1, samples + 1):
            U = random_unitary(2**n, rng)
            row = dict(n=n, sample=sample)
            for name, method, formula in (
                ("zxz", baseline_synth, zxz_formula),
                ("ours", synth, cnot_formula),
            ):
                start = perf_counter()
                circuit, _ = method(U, n)
                elapsed = perf_counter() - start
                count = cnot_count(circuit)
                assert count == formula(n), f"{name}: unexpected CX count {count}"
                row.update({f"{name}_cx": count, f"{name}_time": elapsed})
            yield row


# Figure and command-line output


def plot(rows: list[dict], output: Path) -> None:
    """Reproduce the normalized-CX and log-runtime panels; aggregate by median."""
    ns = sorted({row["n"] for row in rows})
    groups = [[row for row in rows if row["n"] == n] for n in ns]
    style = {
        "font.family": "serif", "font.size": 9, "axes.labelsize": 9,
        "xtick.labelsize": 8, "ytick.labelsize": 8,
        "axes.linewidth": 0.6, "lines.linewidth": 1.2,
    }
    with plt.rc_context(style):
        fig, (ax, tx) = plt.subplots(1, 2, figsize=(6.4, 2.6))
        for key, color, limit, label in (
            ("zxz", "0.35", 22 / 48, "Block-ZXZ"),
            ("ours", "#0047cc", 21 / 48, "Improved"),
        ):
            raw = [group[0][f"{key}_cx"] for group in groups]
            counts = [c / 4.0**n for n, c in zip(ns, raw)]
            times = [np.median([row[f"{key}_time"] for row in group])
                     for group in groups]
            ax.plot(ns, counts, "o-", color=color, ms=4, label=label)
            # label each point with its CX count: Block-ZXZ above, ours below
            dy, va = (5, "bottom") if key == "zxz" else (-5, "top")
            for n, c, y in zip(ns, raw, counts):
                ax.annotate(str(c), (n, y), textcoords="offset points", xytext=(0, dy),
                            ha="center", va=va, fontsize=5.5, color=color)
            ax.axhline(limit, color=color, ls=":", lw=0.9, zorder=0)
            tx.plot(ns, times, "s-", color=color, ms=4, label=label)
        bound = [((4**n - 3*n + 2) // 4) / 4.0**n for n in ns]
        ax.plot(ns, bound, "o-", color="k", ms=4, label="lower bound")
        ax.axhline(12 / 48, color="k", ls=":", lw=0.9)
        ax.set_ylabel(r"leading coefficient $c_n/4^n$")
        ax.set_ylim(top=0.49)                       # room for the Block-ZXZ count labels
        ax.set_xlim(ns[0] - 0.4, ns[-1] + 0.5)      # and for the widest labels at the ends
        ax.set_title("(a) CX count", fontsize=9)
        ax.legend(frameon=False, fontsize=8, loc="center right",
                  bbox_to_anchor=(1.0, 0.45))
        tx.set_yscale("log")
        tx.set_ylabel("synthesis time (s)")
        tx.set_title("(b) synthesis runtime", fontsize=9)
        tx.legend(frameon=False, fontsize=8, loc="upper left")
        for panel in (ax, tx):
            panel.set_xlabel(r"qubits $n$")
            panel.set_xticks(ns)
        fig.tight_layout(pad=0.3, w_pad=1.5)
        fig.savefig(output, bbox_inches="tight", pad_inches=0.02)
        plt.close(fig)


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--nmin", type=int, default=3)
    parser.add_argument("--nmax", type=int, default=10)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--output", type=Path, default=Path("bal_benchmark.pdf"),
        help="comparison figure path (default: bal_benchmark.pdf)",
    )
    args = parser.parse_args(argv)
    print(f"Python {platform.python_version()}, NumPy {np.__version__}, "
          f"SciPy {scipy.__version__}, Matplotlib {matplotlib.__version__}")
    print(f"Complete synthesis; seed={args.seed}, samples={args.samples}")
    print(
        f"{'n':>3} {'sample':>6} {'ZXZ CX':>9} {'ours CX':>9} {'saved':>7} "
        f"{'ZXZ time':>10} {'ours time':>10} {'ratio':>7}",
        flush=True,
    )
    rows = []
    args.output.parent.mkdir(parents=True, exist_ok=True)
    for row in compare(range(args.nmin, args.nmax + 1), args.samples, args.seed):
        rows.append(row)
        print(f"{row['n']:>3} {row['sample']:>6} "
              f"{row['zxz_cx']:>9} {row['ours_cx']:>9} "
              f"{row['zxz_cx'] - row['ours_cx']:>7} "
              f"{row['zxz_time']:>9.3f}s {row['ours_time']:>9.3f}s "
              f"{row['ours_time'] / row['zxz_time']:>7.2f}", flush=True)
    plot(rows, args.output)
    print(f"Saved {args.output}")


if __name__ == "__main__":
    main()
