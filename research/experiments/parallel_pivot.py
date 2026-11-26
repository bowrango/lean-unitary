#!/usr/bin/env python3
"""Level-parallel pivot synthesis: independent node searches plus a Moebius scan over leaves.

The sequential reference (submission/decomposition.py, `synth`) walks the recursion tree depth
first. It multiplies each child by the diagonal carry of the previous child before decomposing
it, so every node waits for all nodes before it in time order. This script removes that
dependency in three phases.

1. Nodes (parallel within a level). A carry acts on the bottom two qubits, which are lower qubits
   of every node with at least three qubits. Right-multiplying a node by I (x) Delta conjugates its
   Block-ZXZ factor C (C -> Delta^dagger C Delta), so the eigenphases of C are unchanged and so is
   the pivot. The carry commutes with the pivot gate and every multiplexor, and it ends up in the
   node's first leaf. Every node can therefore be decomposed from its own unitary alone, and all
   nodes at one level are independent.
2. Carries (associative scan). A two-qubit leaf synthesized up to a diagonal maps the Z(x)Z angle
   h of its input carry to the angle g of its output carry. With z = exp(4ih) and w = exp(4ig),
   this map is the Moebius transformation w = (p z + q) / (conj(q) z + conj(p)). Composing leaves
   is therefore a product of 2x2 matrices, and all carries follow from a prefix scan of depth
   log2(#leaves).
3. Leaves (parallel). Each leaf is synthesized independently from its own unitary and its scanned
   input and output carries.

Run: python parallel_pivot.py 3 4 5 6 --samples 2 [--workers 8]
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "submission"))
import decomposition as dc  # noqa: E402
import triple_fold as tf  # noqa: E402

ZZ = np.array([1, -1, -1, 1])


# Phase 1: carry-free node decomposition


def plan_node_triple(U, n, seed):
    """Carry-free node with the three-CX C-side fold (triple_fold.py); nodes of >= 4 qubits."""
    rng = np.random.default_rng(seed)
    t0 = time.perf_counter()
    d = 2 ** (n - 1)
    if d <= 8:
        cond = tf._COND.setdefault(d, tf.Conditions(d))
        e, p = tf.search(U, cond, rng)
    else:
        e, p, cond = tf.search_large(U, rng)
    assert e < 1e-12, f"no triple-fold root at n={n}"
    t_search = time.perf_counter() - t0
    u = tf.su2(p)
    A1, A2, B, C = dc.block_zxz(dc.apply_pivot(U, u))
    Va, theta_a, Wa = dc.demultiplex(A1, A2)
    Vc, theta_c, Wc = tf.demux_triple_fold(C, cond, n)
    z_hi = dc.embed(dc.Z, [n - 2], n - 1)
    z_three = z_hi @ dc.embed(dc.Z, [0], n - 1) @ dc.embed(dc.Z, [1], n - 1)
    Vb, theta_b, Wb = dc.demultiplex(Wa @ Vc, z_hi @ Wa @ B @ Vc @ z_three)
    top = n - 1
    mux_c = dc.mux_rot(theta_c, n)[:-5]
    mux_a = dc.mux_rot(theta_a, n)[::-1][1:]
    mux_b = [("u", top, dc.H)] + dc.mux_rot(theta_b, n) + [("u", top, dc.H)]
    return (u, [Wc, Wb, Vb, Va], [mux_c, mux_b, mux_a, []], tuple(p), t_search,
            time.perf_counter() - t0)


def plan_node_zxz(U, n):
    """Carry-free Block-ZXZ node without a pivot (baseline_synth in submission/benchmark.py)."""
    t0 = time.perf_counter()
    m, top = 2 ** (n - 1), n - 1
    A1, A2, B, C = dc.block_zxz(U)
    Va, theta_a, Wa = dc.demultiplex(A1, A2)
    Vc, theta_c, Wc = dc.demultiplex(np.eye(m, dtype=complex), C)
    z = dc.embed(dc.Z, [n - 2], n - 1)
    Vb, theta_b, Wb = dc.demultiplex(Wa @ Vc, z @ Wa @ B @ Vc @ z)
    mux_c = dc.mux_rot(theta_c, n)[:-1]
    mux_a = dc.mux_rot(theta_a, n)[::-1][1:]
    mux_b = [("u", top, dc.H)] + dc.mux_rot(theta_b, n) + [("u", top, dc.H)]
    return (np.eye(2, dtype=complex), [Wc, Wb, Vb, Va], [mux_c, mux_b, mux_a, []], (), 0.0,
            time.perf_counter() - t0)


def plan_node(args):
    """Decompose one node without any incoming carry. Returns pivot gate, children, muxes."""
    U, n, triple, seed = args
    if triple == "zxz":
        return plan_node_zxz(U, n)
    if triple and n >= 4:
        return plan_node_triple(U, n, seed)
    t0 = time.perf_counter()
    alpha, beta = dc.find_pivot(U)
    t_search = time.perf_counter() - t0
    u = dc.rz(alpha) @ dc.ry(beta)
    A1, A2, B, C = dc.block_zxz(dc.apply_pivot(U, u))
    Va, theta_a, Wa = dc.demultiplex(A1, A2)
    Vc, theta_c, Wc = dc.demux_double_fold(C)
    z_hi = dc.embed(dc.Z, [n - 2], n - 1)
    z_both = z_hi @ dc.embed(dc.Z, [0], n - 1)
    Vb, theta_b, Wb = dc.demultiplex(Wa @ Vc, z_hi @ Wa @ B @ Vc @ z_both)
    top = n - 1
    mux_c = dc.mux_rot(theta_c, n)[:-3]
    mux_a = dc.mux_rot(theta_a, n)[::-1][1:]
    mux_b = [("u", top, dc.H)] + dc.mux_rot(theta_b, n) + [("u", top, dc.H)]
    t_total = time.perf_counter() - t0
    return (u, [Wc, Wb, Vb, Va], [mux_c, mux_b, mux_a, []], (alpha, beta), t_search, t_total)


def build_tree(U, n, pool=None, triple=False, seed=0):
    """Level-synchronous phase 1. Returns per-level node plans and the leaf unitaries."""
    levels, frontier, size = [], [U], n
    timing = []
    while size > 2:
        jobs = [(V, size, triple, (seed, size, i)) for i, V in enumerate(frontier)]
        t0 = time.perf_counter()
        plans = list(pool.map(plan_node, jobs, chunksize=max(1, len(jobs) // 64))) if pool else [
            plan_node(j) for j in jobs
        ]
        wall = time.perf_counter() - t0
        timing.append((size, len(jobs), wall, sum(p[5] for p in plans), max(p[5] for p in plans),
                       sum(p[4] for p in plans)))
        levels.append(plans)
        frontier = [child for p in plans for child in p[1]]
        size -= 1
    return levels, frontier, timing


# Phase 2: Moebius maps of the leaves and their prefix scan


def det_normalize(U):
    return U / np.exp(0.25j * np.angle(np.linalg.det(U)))


def leaf_moebius(U):
    """Return [[p, q], [conj q, conj p]] with w = (p z + q)/(conj(q) z + conj(p)).

    tr gamma(D^dagger U c) = a^{-1}(b T++ + b^{-1} T+-) + a (b T-+ + b^{-1} T--), with
    a = exp(2ig), b = exp(2ih), T_st = tr(P_s U P_t YY U^T YY) and P_+- the Z(x)Z eigenprojectors.
    Requiring a real trace gives a^2 = (b p + conj(b) q)/conj(...).
    """
    U = det_normalize(U)
    P = {+1: np.diag((ZZ == 1).astype(complex)), -1: np.diag((ZZ == -1).astype(complex))}
    R = dc.YY @ U.T @ dc.YY
    T = {(s, t): np.trace(P[s] @ U @ P[t] @ R) for s in (1, -1) for t in (1, -1)}
    p = T[1, 1] - np.conj(T[-1, -1])
    q = T[1, -1] - np.conj(T[-1, 1])
    return np.array([[p, q], [np.conj(q), np.conj(p)]])


def prefix_scan(mats):
    """Inclusive scan P_j = M_j ... M_0 by recursive doubling (log2 N vectorized rounds)."""
    P = np.array(mats)
    P /= np.linalg.norm(P, axis=(1, 2))[:, None, None]   # projective: only the ratio matters
    step, rounds = 1, 0
    while step < len(P):
        P[step:] = P[step:] @ P[:-step]
        P /= np.linalg.norm(P, axis=(1, 2))[:, None, None]
        step *= 2
        rounds += 1
    return P, rounds


def apply_moebius(M, z):
    return (M[0, 0] * z + M[0, 1]) / (M[1, 0] * z + M[1, 1])


def carry_diag(z):
    """Canonical carry with exp(4ih) = z: diag(exp(i h ZZ))."""
    return np.exp(1j * (np.angle(z) / 4) * ZZ)


# Phase 3: independent leaf synthesis


def synth_leaf(args):
    U, z_in, z_out, last = args
    M = U * carry_diag(z_in)[None, :]
    circ, carry = dc.leaf(M, want_diag=not last)
    d = np.diag(carry)
    if last:
        return circ, d[0], 0.0
    z_actual = (d[0] / d[1]) ** 2
    err = abs(z_actual - z_out)
    L = d / carry_diag(z_out)              # scalar * (Z(x)Z)^k, a product of local diagonals
    circ = circ + [("u", 0, np.diag([L[0], L[1]])), ("u", 1, np.diag([1, L[2] / L[0]]))]
    return circ, 1.0, err


def assemble(levels, leaf_circs, n):
    """Rebuild the time-ordered circuit from node plans and leaf circuits."""
    def node(depth, i):
        size = n - depth
        if size == 2:
            return leaf_circs[i]
        u, _, muxes, *_ = levels[depth][i]
        circ = [("u", size - 1, u.conj().T)]
        for c in range(4):
            circ += node(depth + 1, 4 * i + c) + muxes[c]
        return circ
    return node(0, 0)


def decompose_parallel(U, pool=None, triple=False, seed=0):
    n = len(U).bit_length() - 1
    t0 = time.perf_counter()
    levels, leaves, timing = build_tree(U, n, pool, triple, seed)
    t1 = time.perf_counter()
    N = len(leaves)
    mats = [leaf_moebius(L) for L in leaves[:-1]]
    if mats:
        P, rounds = prefix_scan(mats)
        z = [1.0 + 0j] + [apply_moebius(Pj, 1.0 + 0j) for Pj in P]
    else:
        rounds, z = 0, [1.0 + 0j]
    t2 = time.perf_counter()
    jobs = [(leaves[j], z[j], z[j + 1] if j + 1 < len(z) else None, j == N - 1) for j in range(N)]
    out = list(pool.map(synth_leaf, jobs, chunksize=max(1, N // 64))) if pool else [
        synth_leaf(j) for j in jobs
    ]
    t3 = time.perf_counter()
    leaf_circs = [o[0] for o in out]
    scan_err = max((o[2] for o in out), default=0.0)
    circuit = assemble(levels, leaf_circs, n)
    phase = out[-1][1]
    info = dict(timing=timing, rounds=rounds, scan_err=scan_err, leaves=N,
                t_nodes=t1 - t0, t_scan=t2 - t1, t_leaves=t3 - t2,
                pivots=[[p[3] for p in lvl] for lvl in levels])
    return circuit, phase, info


def apply_circuit(circ, n, states):
    """Apply a circuit to a (2**n, k) block of states by state-vector simulation."""
    k = states.shape[1]
    psi = states.copy()
    idx = np.arange(2**n)
    for g in circ:
        if g[0] == "u":
            q = g[1]
            v = psi.reshape(2 ** (n - q - 1), 2, 2**q, k)
            psi = np.einsum("ab,xbyk->xayk", g[2], v).reshape(2**n, k)
        else:
            c, t = g[1], g[2]
            psi = psi[idx ^ (((idx >> c) & 1) << t)]
    return psi


def check(U, circ, phase, n, rng, k=4):
    """Max deviation of phase * circuit from U on k random input states."""
    v = rng.normal(size=(2**n, k)) + 1j * rng.normal(size=(2**n, k))
    v /= np.linalg.norm(v, axis=0)
    return float(np.max(np.abs(U @ v - phase * apply_circuit(circ, n, v))))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("qubits", nargs="*", type=int, default=[3, 4, 5])
    ap.add_argument("--samples", type=int, default=1)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--workers", type=int, default=0, help="process pool size (0: serial)")
    ap.add_argument("--compare", action="store_true", help="also time the sequential reference")
    ap.add_argument("--triple", action="store_true", help="three-CX C-side fold at nodes of >= 4 qubits")
    ap.add_argument("--zxz", action="store_true", help="plain Block-ZXZ nodes (no pivot), for comparison")
    args = ap.parse_args(argv)
    rng = np.random.default_rng(args.seed)
    pool = ProcessPoolExecutor(args.workers) if args.workers else None
    try:
        for n in args.qubits:
            for s in range(args.samples):
                U = dc.random_unitary(2**n, rng)
                t0 = time.perf_counter()
                circ, phase, info = decompose_parallel(U, pool, "zxz" if args.zxz else args.triple, args.seed)
                wall = time.perf_counter() - t0
                err = check(U, circ, phase, n, rng)
                cx = dc.cnot_count(circ)
                target = (dc.zxz_formula(n) if args.zxz else
                          tf.triple_formula(n) if args.triple and n >= 4 else dc.cnot_formula(n))
                print(f"n={n} sample={s}: {cx} CX (formula {target}), err={err:.1e}, "
                      f"scan rounds={info['rounds']} for {info['leaves']} leaves, "
                      f"max |z_scan - z_actual|={info['scan_err']:.1e}, wall={wall:.2f}s "
                      f"(nodes {info['t_nodes']:.2f}, scan {info['t_scan']:.3f}, leaves {info['t_leaves']:.2f})")
                for size, cnt, lw, work, span, search in info["timing"]:
                    print(f"    level {size}q: {cnt:5d} nodes  work={work:7.3f}s  "
                          f"longest node={span:7.4f}s  searches={search / work:5.1%} of work  wall={lw:.3f}s")
                if args.compare:
                    t0 = time.perf_counter()
                    rc, _ = dc.decompose(U)
                    print(f"    sequential reference: {dc.cnot_count(rc)} CX in {time.perf_counter() - t0:.2f}s")
    finally:
        if pool:
            pool.shutdown()


if __name__ == "__main__":
    main()
