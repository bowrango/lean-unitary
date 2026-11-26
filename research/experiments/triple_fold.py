#!/usr/bin/env python3
"""Does the next fold also stay a small, node-local search? A three-CX fold on the C side.

The pivot zeroes the last Gray-code angle phi_{d-1} of the input-side multiplexor, so its last
two CX gates fold into the central multiplexor. Zeroing phi_{d-2} as well would fold a third CX
(CX on bit 1). With gray[d-2] = top bit + bit 0, the two conditions on the assigned eigenphases
theta_j of C are
    sum_j (-1)^{j_top} theta_j = 0   and   sum_j (-1)^{j_top + j_0} theta_j = 0.
After 2*pi branch shifts they become two equal-sum conditions on quarters Q_ab (a = j_top, b = j_0),
each of size d/4:
    Q_00 = Q_10 (mod 2 pi)   and   Q_01 = Q_11 (mod 2 pi).
For d = 4 (3-qubit nodes) the quarters are single eigenphases, so the conditions are eigenvalue
coincidences. Those have codimension 3 and do not occur in a family with few parameters. For
d >= 8 they are two ordinary codimension-1 conditions, and the free top-qubit gate u in SU(2)
(3 parameters) gives a small node-local search.

This script searches for (u) at the root of an n = 4 or 5 qubit target. It then builds the full
circuit with the three-CX fold at the root (children use the reference synthesis) and verifies it.

Run: python triple_fold.py 4 --targets 10
"""

from __future__ import annotations

import argparse
import itertools
import os
import sys

import numpy as np
from scipy.optimize import least_squares

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "submission"))
import decomposition as dc  # noqa: E402


def wrap(x):
    return (x + np.pi) % (2 * np.pi) - np.pi


def su2(p):
    return dc.rz(p[0]) @ dc.ry(p[1]) @ dc.rz(p[2])


def C_of(U, p):
    return dc.block_zxz(dc.apply_pivot(U, su2(p)))[3]


class Conditions:
    """Best quarter assignment for given eigenphases.

    The two conditions decouple once the half A = Q00 u Q10 is fixed, so for every 2q-subset we
    keep its best q|q split and pair it with the best split of its complement.
    """

    def __init__(self, d):
        q = d // 4
        self.d, self.q = d, q
        self.subsets = np.array(list(itertools.combinations(range(d), 2 * q)))
        split = [c for c in itertools.combinations(range(2 * q), q) if 0 in c]
        self.P = np.array(split)
        self.Pc = np.array([[i for i in range(2 * q) if i not in c] for c in split])
        masks = (1 << self.subsets).sum(1)
        where = {m: i for i, m in enumerate(masks)}
        full = (1 << d) - 1
        self.comp = np.array([where[full ^ m] for m in masks])

    def residuals(self, mu):
        X = mu[self.subsets]
        r = wrap(X[:, self.P].sum(-1) - X[:, self.Pc].sum(-1))
        k = np.argmin(np.abs(r), axis=1)
        best = r[np.arange(len(r)), k]
        score = best**2 + best[self.comp] ** 2
        a = int(np.argmin(score))
        b = int(self.comp[a])
        A, Bs = self.subsets[a], self.subsets[b]
        combo = (A[self.P[k[a]]], A[self.Pc[k[a]]], Bs[self.P[k[b]]], Bs[self.Pc[k[b]]])
        return np.array([best[a], best[b]]), combo


def search(U, cond, rng, starts=60):
    best = (np.inf, None)
    for _ in range(starts):
        p0 = rng.uniform(-np.pi, np.pi, 3)
        f = lambda p: cond.residuals(np.angle(np.linalg.eigvals(C_of(U, p))))[0]
        sol = least_squares(f, p0, xtol=1e-15, ftol=1e-15, gtol=1e-15)
        e = float(np.linalg.norm(f(sol.x)))
        if e < best[0]:
            best = (e, sol.x)
        if e < 1e-12:
            break
    return best


class FixedAssignment:
    """A quarter assignment found at a root, transported to any ordering of the same spectrum."""

    def __init__(self, lam, combo):
        self.lam, self.combo = lam, combo

    def residuals(self, mu):
        from scipy.optimize import linear_sum_assignment
        _, col = linear_sum_assignment(np.abs(np.exp(1j * mu)[None, :] - self.lam[:, None]))
        combo = tuple(col[Q] for Q in self.combo)        # eigen index k -> position in mu
        r = [wrap(mu[combo[0]].sum() - mu[combo[1]].sum()), wrap(mu[combo[2]].sum() - mu[combo[3]].sum())]
        return np.array(r), combo


def local_assignment(mu, rng):
    """Random quarters, then greedy swaps that shrink each equal-sum residual."""
    d, q = len(mu), len(mu) // 4
    order = rng.permutation(d)
    Q = [order[i * q:(i + 1) * q].copy() for i in range(4)]
    for a, b in ((0, 1), (2, 3)):
        while True:
            r = wrap(mu[Q[a]].sum() - mu[Q[b]].sum())
            new = np.abs(wrap(r - 2 * (mu[Q[a]][:, None] - mu[Q[b]][None, :])))
            i, j = np.unravel_index(np.argmin(new), new.shape)
            if new[i, j] >= abs(r) - 1e-15:
                break
            Q[a][i], Q[b][j] = Q[b][j], Q[a][i]
    return tuple(Q)


def search_large(U, rng, starts=20):
    """2-D search over the input gate R_z(a) R_y(b) (an input R_z only rotates the whole spectrum).

    Returns (residual, params, assignment). Labels are fixed at the start point and followed by
    matching eigenvalues, so the solve is a smooth 2 x 2 system.
    """
    best = (np.inf, None, None)
    for _ in range(starts):
        p0 = rng.uniform(-np.pi, np.pi, 2)
        lam0 = np.linalg.eigvals(C_of(U, np.r_[p0, 0.0]))
        fixed = FixedAssignment(lam0, local_assignment(np.angle(lam0), rng))

        def f(p):
            mu = np.angle(np.linalg.eigvals(C_of(U, np.r_[p, 0.0])))
            return fixed.residuals(mu)[0]

        sol = least_squares(f, p0, xtol=1e-15, ftol=1e-15, gtol=1e-15)
        e = float(np.linalg.norm(f(sol.x)))
        if e < best[0]:
            lam = np.linalg.eigvals(C_of(U, np.r_[sol.x, 0.0]))
            r, combo = fixed.residuals(np.angle(lam))
            best = (e, np.r_[sol.x, 0.0], FixedAssignment(lam, combo))
        if e < 1e-12:
            break
    return best


def demux_triple_fold(C, cond, n):
    """Demultiplex I (+) C with the two trailing Gray angles exactly zero."""
    D = len(C)
    V, theta, W = dc.demultiplex(np.eye(D, dtype=complex), C)
    _, (Q00, Q10, Q01, Q11) = cond.residuals(theta)
    top, pos = D // 2, np.arange(D)
    cls = {(a, b): pos[((pos >= top) == a) & ((pos & 1) == b)] for a in (0, 1) for b in (0, 1)}
    perm = np.empty(D, dtype=int)
    for (a, b), Q in {(0, 0): Q00, (1, 0): Q10, (0, 1): Q01, (1, 1): Q11}.items():
        perm[cls[a, b]] = Q
    V, theta, W = V[:, perm], theta[perm].copy(), W[perm, :].copy()
    for (a, b), (c, e) in {((0, 0), (1, 0)): (0, 0), ((0, 1), (1, 1)): (0, 1)}.items():
        diff = theta[cls[a]].sum() - theta[cls[b]].sum()
        turns = int(round(diff / (2 * np.pi)))
        j = cls[a][0]
        theta[j] -= 2 * np.pi * turns
        if turns % 2:
            W[j] *= -1
    gray = [i ^ (i >> 1) for i in range(D)]
    sign = np.array([[(-1) ** bin(j & g).count("1") for g in gray] for j in range(D)])
    phis = np.linalg.solve(sign, theta)
    assert abs(phis[-1]) < 1e-9 and abs(phis[-2]) < 1e-9, phis[-2:]
    return V, theta, W


_COND = {}


def synth_triple(U, n, want_diag=False, rng=None, stats=None):
    """Pivot recursion with the three-CX C-side fold at every node of at least 4 qubits."""
    if n <= 3:
        return dc.synth(U, n, want_diag)
    d = 2 ** (n - 1)
    if d <= 8:
        cond = _COND.setdefault(d, Conditions(d))
        e, p = search(U, cond, rng)
    else:
        e, p, cond = search_large(U, rng)
    assert e < 1e-12, f"no triple-fold root found at n={n} ({e:.1e})"
    if stats is not None:
        stats.append(e)
    top = n - 1
    u = su2(p)
    A1, A2, B, C = dc.block_zxz(dc.apply_pivot(U, u))
    Va, theta_a, Wa = dc.demultiplex(A1, A2)
    Vc, theta_c, Wc = demux_triple_fold(C, cond, n)
    z_hi = dc.embed(dc.Z, [n - 2], n - 1)
    z_three = z_hi @ dc.embed(dc.Z, [0], n - 1) @ dc.embed(dc.Z, [1], n - 1)
    Vb, theta_b, Wb = dc.demultiplex(Wa @ Vc, z_hi @ Wa @ B @ Vc @ z_three)
    mux_c = dc.mux_rot(theta_c, n)[:-5]
    mux_a = dc.mux_rot(theta_a, n)[::-1][1:]
    mux_b = [("u", top, dc.H)] + dc.mux_rot(theta_b, n) + [("u", top, dc.H)]
    circ = [("u", top, u.conj().T)]
    carry = np.eye(2 ** (n - 1), dtype=complex)
    children, muxes = [Wc, Wb, Vb, Va], [mux_c, mux_b, mux_a, []]
    for i, (child, mux) in enumerate(zip(children, muxes)):
        sub, carry = synth_triple(child @ carry, n - 1, want_diag or i < 3, rng, stats)
        circ += sub + mux
    return circ, dc.block_diag(carry, carry)


def triple_formula(n):
    """c_3 = 18, c_n = 4 c_{n-1} + 3 * 2^(n-1) - 7 for n >= 4."""
    c = dc.cnot_formula(3)
    for m in range(4, n + 1):
        c = 4 * c + 3 * 2 ** (m - 1) - 7
    return c


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("qubits", nargs="*", type=int, default=[4])
    ap.add_argument("--targets", type=int, default=5)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args(argv)
    rng = np.random.default_rng(args.seed)
    for n in args.qubits:
        d = 2 ** (n - 1)
        cond = Conditions(d) if d <= 8 else None
        print(f"n={n}: d={d}")
        for t in range(args.targets):
            U = dc.random_unitary(2**n, rng)
            if d <= 8:
                res0 = np.linalg.norm(cond.residuals(np.angle(np.linalg.eigvals(C_of(U, np.zeros(3)))))[0])
                e, p = search(U, cond, rng)
            else:
                res0 = float("nan")
                e, p, _ = search_large(U, rng)
            line = f"  target {t}: residual at u=I {res0:.1e} -> searched {e:.1e}"
            if e < 1e-12 and n >= 4:
                circ, diag = synth_triple(U, n, rng=rng)
                err = float(np.max(np.abs(U - diag @ dc.circuit_matrix(circ, n))))
                line += (f"; circuit {dc.cnot_count(circ)} CX (predicted {triple_formula(n)}, "
                         f"pivot {dc.cnot_formula(n)}), err {err:.1e}")
            print(line, flush=True)


if __name__ == "__main__":
    main()
