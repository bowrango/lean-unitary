"""Block-ZXZ with a provable extra fold at every node (C side): 1 CNOT saved per node.

At each node, top-qubit gates Rz(α)·Ry(β*) at the input (free) make the eigenphases of the
block-ZXZ factor C split into two halves with equal sums mod 2π (IVT argument, fold_ivt.py).
Then the C-side multiplexor's last two CNOTs, CX(q0,top)·CX(q_{n-2},top), have no rotation between
them and both fold into the middle factor as I ⊕ Z_{q0} Z_{q_{n-2}}.

    c(n) = 3 cd(n-1) + c(n-1) + 3·2^(n-1) - 3,   cd = c - 1,   c(2) = 3."""
import itertools
import numpy as np
from core import (H, Z, block_diag, block_zxz, circuit_matrix, cnot_count, demultiplex, embed,
                  mux_rot, random_unitary)
from zxz import leaf
from fold_ivt import choose_alpha, top_gate
from pfaff_general import half_splits

def gap(mu, S, Sc):
    x = mu[list(S)].sum() - mu[list(Sc)].sum()
    return (x + np.pi) % (2 * np.pi) - np.pi

def find_beta(U, n, alpha, nb=800):
    """β* ∈ [0,π] with a zero of the tracked fold function (IVT guarantees a sign change), refined by
    bisection with eigenphases matched to the left end of the bracketing interval"""
    D = 2 ** (n - 1); splits = half_splits(D)
    Cof = lambda b: block_zxz(U @ embed(top_gate(alpha, b), [n - 1], n))[3]
    def track(b, ref_mu, ref_a):
        lam = np.linalg.eigvals(Cof(b)); a = np.angle(np.prod(lam))
        a = ref_a + (a - ref_a + np.pi) % (2 * np.pi) - np.pi
        mu = np.angle(lam * np.exp(-1j * a / D)); order = []
        for pm in ref_mu:
            d = np.abs(np.exp(1j * mu) - np.exp(1j * pm)); d[order] = np.inf; order.append(int(np.argmin(d)))
        mu = mu[order]; mu = ref_mu + (mu - ref_mu + np.pi) % (2 * np.pi) - np.pi
        g = np.prod(np.sign([np.sin((mu[list(S)].sum() - mu[list(Sc)].sum()) / 2) for S, Sc in splits]))
        return g, mu, a
    lam = np.linalg.eigvals(Cof(0.0)); a0 = np.angle(np.prod(lam))
    mu0 = np.angle(lam * np.exp(-1j * a0 / D))
    g0 = np.prod(np.sign([np.sin((mu0[list(S)].sum() - mu0[list(Sc)].sum()) / 2) for S, Sc in splits]))
    prev = (0.0, g0, mu0, a0)
    for b in np.linspace(0, np.pi, nb + 1)[1:]:
        g, mu, a = track(b, prev[2], prev[3])
        if np.sign(g) != np.sign(prev[1]):
            lo, glo, mlo, alo = prev; hi = b
            for _ in range(50):
                mid = (lo + hi) / 2
                gm, mm, am = track(mid, mlo, alo)
                if np.sign(gm) == np.sign(glo): lo, glo, mlo, alo = mid, gm, mm, am
                else: hi = mid
            return (lo + hi) / 2, None
        prev = (b, g, mu, a)
    raise RuntimeError("no sign change (parity rule violated?)")

def gray_phis(th):
    k = int(np.log2(len(th)))
    gray = [i ^ (i >> 1) for i in range(2**k)]
    sign = np.array([[(-1) ** bin(j & g).count("1") for g in gray] for j in range(2**k)])
    return np.linalg.solve(sign, th)

def demux_double(C, S, Sc):
    """demultiplex I ⊕ C with eigenvalues of split S on lower states whose top control bit is 0,
    and branch shifts making the last Gray angle exactly 0"""
    D = C.shape[0]
    V, th, W = demultiplex(np.eye(D, dtype=complex), C)
    # identify which demultiplex eigenvalues belong to S: match eigenphases of C
    lamC = np.linalg.eigvals(C)
    # eigenvalues of I·C† are conj(λ_C); θ_j ≡ ±phase — recompute a split on the actual θ
    k = int(np.log2(D)); hi_bit = 1 << (k - 1)
    best = None
    for SS, SSc in half_splits(D):
        g = th[list(SS)].sum() - th[list(SSc)].sum()
        r = abs((g + np.pi) % (2 * np.pi) - np.pi)
        if best is None or r < best[0]: best = (r, SS, SSc)
    r, SS, SSc = best
    assert r < 1e-7, r
    slots0 = [j for j in range(D) if not j & hi_bit]; slots1 = [j for j in range(D) if j & hi_bit]
    perm = np.empty(D, int); perm[slots0] = SS; perm[slots1] = SSc
    V, th, W = V[:, perm], th[perm].copy(), W[perm, :]
    shifts = np.zeros(D, int)
    phi = gray_phis(th)[-1]
    steps = int(round(phi / (2 * np.pi / D)))
    for _ in range(abs(steps)):          # each +2π on a slot0 entry (or -2π... ) moves φ by ±2π/D
        j = slots0[_ % len(slots0)]
        th[j] -= np.sign(steps) * 2 * np.pi; shifts[j] ^= 1
    assert abs(gray_phis(th)[-1]) < 1e-7, gray_phis(th)[-1]
    Sg = np.diag([(-1) ** s for s in shifts]).astype(complex)
    return V, th, Sg @ W

def synth(U, n, want_diag=False):
    if n == 2:
        return leaf(U, want_diag)
    m, top = 2 ** (n - 1), n - 1
    alpha = choose_alpha(U, n)
    beta, _ = find_beta(U, n, alpha)
    G = embed(top_gate(alpha, beta), [top], n)
    Up = U @ G                                         # U = Up · G†  (G† applied first)
    A1, A2, B, C = block_zxz(Up)
    I = np.eye(m, dtype=complex)
    Va, ta, Wa = demultiplex(A1, A2)
    Vc, tc, Wc = demux_double(C, None, None)
    Zc = embed(Z, [n - 2], n - 1)
    Zf = embed(Z, [n - 2], n - 1) @ embed(Z, [0], n - 1)
    Vb, tb, Wb = demultiplex(Wa @ Vc, Zc @ Wa @ B @ Vc @ Zf)
    dc = mux_rot(tc, n)[:-3]                           # drop Rz(0) and the two closing CNOTs
    da = mux_rot(ta, n)[::-1][1:]
    hdh = [("u", top, H)] + mux_rot(tb, n) + [("u", top, H)]
    circ = [("u", top, top_gate(alpha, beta).conj().T)]
    carry = np.eye(m, dtype=complex)
    for i, (S, seg) in enumerate(zip([Wc, Wb, Vb, Va], [dc, hdh, da, []])):
        last = i == 3
        sub, D = synth(S @ carry, n - 1, want_diag=(not last) or want_diag)
        circ += sub + seg
        carry = D
    return circ, block_diag(carry, carry)

def formula(n):
    c = {2: 3}
    for k in range(3, n + 1):
        c[k] = 3 * (c[k - 1] - 1) + c[k - 1] + 3 * 2 ** (k - 1) - 3
    return c[n]

if __name__ == "__main__":
    import sys
    rng = np.random.default_rng(11)
    for n in [int(a) for a in sys.argv[1:]] or [3, 4]:
        for t in range(2):
            U = random_unitary(2**n, rng)
            circ, D = synth(U, n)
            M = D @ circuit_matrix(circ, n)
            ph = np.vdot(M.ravel(), U.ravel()); ph /= abs(ph)
            print(f"n={n}: {cnot_count(circ)} CNOTs (formula {formula(n)}, block-ZXZ {(22*4**n-72*2**n+80)//48}), "
                  f"max |U - e^(iφ)·circuit| = {np.max(np.abs(U - ph*M)):.1e}", flush=True)
