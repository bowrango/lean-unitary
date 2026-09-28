"""Local degree (orientation sign) of the k-level round-robin map at solutions.

Domain M = U(d)^(4^k) × T^((4^k - 1) d), global frame: left-invariant generators iB on each child
(B in the fixed Hermitian basis), ∂/∂θ on angles. The gauge torus acts freely (child i-1 -> e^{iεE}·C,
child i -> C·e^{-iεE}, E = E_jj on L, next to glue i), so M/T is a compact oriented manifold of
dimension 16 d² = dim U(4d) (k = 2). At a solution x the local degree is
    sign det[v | g]_M · sign det(dF v)_{U(4d)},
v any basis of a complement to the gauge directions g. deg F̄ = Σ over all preimages of a regular value."""
import numpy as np
from pauli_glue import herm_basis

def herm_coords(Hm, dL):
    """coordinates of Hermitian Hm in herm_basis(dL) order: E_ll ; E_lm+E_ml ; -iE_lm+iE_ml"""
    v = [Hm[l, l].real for l in range(dL)]
    for l in range(dL):
        for m in range(l + 1, dL):
            v += [Hm[l, m].real, -Hm[l, m].imag]
    return np.array(v)

def local_degree(node, C, TH):
    J = node.jac(C, TH)                       # rows: real+imag of N×N, cols: params
    dL, nc = node.dL, len(C)
    p = J.shape[1]
    # frame check: the children columns of jac are left perturbations e^{iεB}·C, angles d/dθ = -2·(coef)
    # gauge vectors
    G = []
    for i in range(1, nc):                    # glue i sits between child i-1 and child i
        for j in range(dL):
            E = np.zeros((dL, dL), complex); E[j, j] = 1
            g = np.zeros(p)
            g[(i - 1) * (dL * dL + dL) if False else 0:0] = 0
            G.append((i, j, E))
    # parameter layout in jac: child 0, glue 1, child 1, glue 2, ... (children d², glue d)
    off_child = lambda i: i * (dL * dL + dL)
    gv = []
    for (i, j, E) in G:
        g = np.zeros(p)
        g[off_child(i - 1):off_child(i - 1) + dL * dL] += herm_coords(E, dL)
        g[off_child(i):off_child(i) + dL * dL] += herm_coords(-C[i] @ E @ C[i].conj().T, dL)
        gv.append(g)
    Gm = np.array(gv).T                       # p × ngauge
    # check gauge vectors are in the kernel
    kern_err = np.linalg.norm(J @ Gm) / np.linalg.norm(J)
    # complement: orthonormal basis of the orthogonal complement of span(G) in R^p
    Q, _ = np.linalg.qr(Gm, mode="complete")
    V = Q[:, Gm.shape[1]:]
    s1 = np.sign(np.linalg.det(np.concatenate([V, Gm], axis=1)))
    # dF v: J's rows are 2N² real coordinates of the anti-Hermitian-generator; restrict to the
    # N² independent ones (Hermitian coords of the generator T): real diag, real+imag upper triangle
    N = node.N
    JV = J @ V
    rows = []
    Re, Im = JV[:N * N].reshape(N, N, -1), JV[N * N:].reshape(N, N, -1)
    for a in range(N):
        rows.append(Re[a, a])
    for a in range(N):
        for b in range(a + 1, N):
            rows.append(Re[a, b]); rows.append(-Im[a, b])
    A = np.array(rows)
    sv = np.linalg.svd(A, compute_uv=False)
    s2 = np.sign(np.linalg.det(A))
    return int(s1 * s2), kern_err, sv[-1] / sv[0]
