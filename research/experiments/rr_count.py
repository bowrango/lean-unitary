"""CNOT count of the recursion that, at each n, picks the best node:
  k = 1: block-ZXZ (3 glues of 2^(n-1), -2 for the CZ folds)
  k >= 2: round-robin multiplexed-Pauli node, 4^k - 1 weight-1 glues of 2^(n-k) CNOTs each
children: all but the last up to a lower-register diagonal (cd = c - 1 for n >= 2; cd(1) = c(1) = 0)."""
c, cd, how = {1: 0, 2: 3}, {1: 0, 2: 2}, {1: "1q", 2: "leaf"}
def node(n, k):
    m = n - k
    g = (4**k - 1) * 2**m - (2 if k == 1 else 0)
    return (4**k - 1) * cd[m] + c[m] + g
for n in range(3, 41):
    best = min((node(n, k), k) for k in range(1, n))
    c[n], how[n] = best[0], f"k={best[1]}"
    cd[n] = c[n] - 1
LB = lambda n: -(-(4**n - 3*n - 1) // 4)
BZ = lambda n: (22 * 4**n - 72 * 2**n + 80) // 48
print(" n        c(n)   block-ZXZ     LB   node   48·c/4^n  ratio")
for n in list(range(3, 13)) + [16, 24, 40]:
    print(f"{n:2d} {c[n]:11d} {BZ(n):11d} {LB(n):8d}  {how[n]:5s}  {48*c[n]/4**n:7.3f}  {c[n]/LB(n):.3f}")
print("score n=3..8:", round(sum(c[n] / LB(n) for n in range(3, 9)) / 6, 4),
      " block-ZXZ:", round(sum(BZ(n) / LB(n) for n in range(3, 9)) / 6, 4))
