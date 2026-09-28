"""Constructive (IVT) C-side double fold for a block-ZXZ node on n qubits.

Theorem (sketch, see README §10): let X, Y be the top-row blocks of U (top qubit = n-1).
 (i)  choose α so that an even number of eigenvalues of e^{iα}X^{-1}Y lie in the upper half plane;
 (ii) along u(β) = Rz(α)·Ry(β) on the top qubit at the input, β ∈ [0, π], the block-ZXZ factor C(β)
      satisfies C(π) = C(0)^{-1}, and the continuous fold function changes sign, so it has a zero β*.
At β*, the eigenphases of C split into two halves with equal sums mod 2π: the C-side multiplexor
folds TWO CNOTs into the middle factor instead of one.
Here the fold function is g(β) = Π_splits sin((Σ_S μ − Σ_{S^c} μ)/2) with eigenphases of C·det(C)^(-1/D)
tracked continuously; we locate a sign change by scanning and refine by bisection."""
import numpy as np
from core import block_zxz, embed, ry, rz
from pfaff_general import half_splits

def top_gate(alpha, beta):
    return rz(alpha) @ ry(beta)          # applied as U @ embed(top_gate, [n-1])

def choose_alpha(U, n):
    D = 2 ** (n - 1)
    X, Y = U[:D, :D], U[:D, D:]         # rows/cols with top qubit = 0 / 1 (top = most significant)
    tau = np.linalg.eigvals(np.linalg.solve(X, Y))
    for alpha in np.linspace(0, 2 * np.pi, 721)[:-1]:
        # u = Rz(α) at input: X -> e^{-iα/2} X, Y -> e^{iα/2} Y, so τ -> e^{iα} τ
        if np.sum((np.exp(1j * alpha) * tau).imag > 0) % 2 == 0 and np.min(np.abs((np.exp(1j*alpha)*tau).imag)) > 1e-6:
            return alpha
    raise RuntimeError("no alpha")

class FoldFn:
    def __init__(self, U, n, alpha):
        self.U, self.n, self.alpha, self.D = U, n, alpha, 2 ** (n - 1)
        self.splits = half_splits(self.D)

    def C(self, beta):
        return block_zxz(self.U @ embed(top_gate(self.alpha, beta), [self.n - 1], self.n))[3]

    def g(self, beta, ref_mu=None):
        """fold function with eigenphases matched continuously to ref_mu (normalized by det)"""
        C = self.C(beta)
        lam = np.linalg.eigvals(C)
        a = np.angle(np.prod(lam))
        return lam, a

def scan_and_bisect(U, n, nb=400):
    alpha = choose_alpha(U, n)
    F = FoldFn(U, n, alpha)
    D = F.D
    betas = np.linspace(0, np.pi, nb + 1)
    # continuous tracking: det phase unwrapped; eigenphases of C1 = C / det^(1/D) matched by nearest
    prev_a, prev_mu, vals, mus = None, None, [], []
    for b in betas:
        lam, a = F.g(b)
        if prev_a is not None:
            a = prev_a + (a - prev_a + np.pi) % (2 * np.pi) - np.pi
        prev_a = a
        l1 = lam * np.exp(-1j * a / D)
        mu = np.angle(l1)
        if prev_mu is not None:     # match eigenvalues to previous ordering, unwrap phases
            order = []
            for pm in prev_mu:
                d = np.abs(np.exp(1j * mu) - np.exp(1j * pm)); d[order] = np.inf
                order.append(int(np.argmin(d)))
            mu = mu[order]
            mu = prev_mu + (mu - prev_mu + np.pi) % (2 * np.pi) - np.pi
        prev_mu = mu
        mus.append(mu)
        vals.append(np.prod([np.sin((mu[list(S)].sum() - mu[list(Sc)].sum()) / 2) for S, Sc in F.splits]))
    vals = np.array(vals)
    k = np.where(np.sign(vals[1:]) != np.sign(vals[:-1]))[0]
    return alpha, betas, vals, k

if __name__ == "__main__":
    import sys
    from core import random_unitary
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    rng = np.random.default_rng(5)
    for t in range(int(sys.argv[2]) if len(sys.argv) > 2 else 20):
        U = random_unitary(2**n, rng)
        alpha, b, v, k = scan_and_bisect(U, n)
        print(f"n={n} U{t:2d}: α={alpha:.3f}  g(0)={v[0]:+.2e} g(π)={v[-1]:+.2e}  sign changes on [0,π]: {len(k)}")
