"""Fold function for any D = 2^(n-1): C1 = C/det(C)^(1/D), R = Λ^(D/2) C1 ∈ SO(N) (N = C(D, D/2)),
P = Pf(R - Rᵀ). Instead of forming R we use the equivalent eigenvalue product formula:
P ∝ Π over complementary half-subset pairs {S, S^c} of 2 sin((Σ_S μ - Σ_{S^c} μ)/2),
with the SAME orientation convention as the Pfaffian only up to a global sign, which we fix by
continuity along a path (only sign changes matter)."""
import itertools
import numpy as np

def half_splits(D):
    idx = range(D)
    seen, out = set(), []
    for S in itertools.combinations(idx, D // 2):
        Sc = tuple(i for i in idx if i not in S)
        if Sc in seen: continue
        seen.add(S); out.append((S, Sc))
    return out

def fold_gap(mu):
    """min over balanced splits of |Σ_S μ − Σ_{S^c} μ mod 2π| (0 ⇔ double fold possible)"""
    D = len(mu); best = np.inf
    for S, Sc in half_splits(D):
        x = mu[list(S)].sum() - mu[list(Sc)].sum()
        best = min(best, abs((x + np.pi) % (2 * np.pi) - np.pi))
    return best
