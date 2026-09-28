"""Exact numerical reference for unitary synthesis: circuits, multiplexors, block-ZXZ.

Conventions match `LeanUnitary/Spec.lean`:
  * qubit q is bit q of the basis index; the top qubit of an n-qubit register is n - 1;
  * a circuit is a list of gates applied first to last; its matrix is g_m ... g_1;
  * Ry(t) = [[cos t/2, -sin t/2], [sin t/2, cos t/2]], Rz(t) = diag(e^{-it/2}, e^{it/2});
  * blockDiag(A, B): A when the top qubit is 0, B when it is 1.

Gates are tuples:
  ("u", q, M)          single-qubit unitary M (2x2) on qubit q          -- free
  ("cx", c, t)         CNOT, control c, target t                        -- 1 CNOT
  ("block", qs, M, k)  unitary M on qubits qs (lowest first), counted as k CNOTs; a placeholder
                       for a sub-circuit whose cost is known (e.g. an optimal 2-qubit leaf)
"""

from __future__ import annotations

import numpy as np
from scipy.linalg import polar, schur

I2 = np.eye(2, dtype=complex)
H = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.diag([1, -1]).astype(complex)


def ry(t: float) -> np.ndarray:
    c, s = np.cos(t / 2), np.sin(t / 2)
    return np.array([[c, -s], [s, c]], dtype=complex)


def rz(t: float) -> np.ndarray:
    return np.diag([np.exp(-1j * t / 2), np.exp(1j * t / 2)])


def random_unitary(d: int, rng: np.random.Generator) -> np.ndarray:
    z = (rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))


# ── circuits ──────────────────────────────────────────────────────────────────


def embed(M: np.ndarray, qs: list[int], n: int) -> np.ndarray:
    """The n-qubit matrix of M acting on qubits qs (qs[0] is M's least significant bit)."""
    k = len(qs)
    d = 2**n
    out = np.zeros((d, d), dtype=complex)
    rest_mask = ~sum(1 << q for q in qs)
    for j in range(d):
        sub_j = sum(((j >> q) & 1) << b for b, q in enumerate(qs))
        base = j & rest_mask
        for sub_i in range(2**k):
            i = base | sum(((sub_i >> b) & 1) << q for b, q in enumerate(qs))
            out[i, j] = M[sub_i, sub_j]
    return out


def gate_matrix(g: tuple, n: int) -> np.ndarray:
    kind = g[0]
    if kind == "u":
        return embed(g[2], [g[1]], n)
    if kind == "cx":
        c, t = g[1], g[2]
        d = 2**n
        P = np.zeros((d, d), dtype=complex)
        for j in range(d):
            P[j ^ (1 << t) if (j >> c) & 1 else j, j] = 1
        return P
    if kind == "block":
        return embed(g[2], list(g[1]), n)
    raise ValueError(kind)


def circuit_matrix(circ: list[tuple], n: int) -> np.ndarray:
    M = np.eye(2**n, dtype=complex)
    for g in circ:
        M = gate_matrix(g, n) @ M
    return M


def cnot_count(circ: list[tuple]) -> int:
    return sum(1 if g[0] == "cx" else g[3] if g[0] == "block" else 0 for g in circ)


def lift(circ: list[tuple], offset: int = 0) -> list[tuple]:
    """Relabel a circuit's qubits q -> q + offset."""
    out = []
    for g in circ:
        if g[0] == "u":
            out.append(("u", g[1] + offset, g[2]))
        elif g[0] == "cx":
            out.append(("cx", g[1] + offset, g[2] + offset))
        else:
            out.append(("block", tuple(q + offset for q in g[1]), g[2], g[3]))
    return out


def block_diag(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Spec.blockDiag: A when the top qubit is 0, B when it is 1."""
    d = A.shape[0]
    out = np.zeros((2 * d, 2 * d), dtype=complex)
    out[:d, :d], out[d:, d:] = A, B
    return out


def dist(A: np.ndarray, B: np.ndarray) -> float:
    return float(np.max(np.abs(A - B)))


# ── multiplexed rotations (Gray code, 2^k CNOTs for k controls) ────────────────


def mux_rot(thetas: np.ndarray, n: int, axis: str = "z") -> list[tuple]:
    """Multiplexed R_z (or R_y) on the top qubit n-1, controlled by qubits 0..n-2:
    when the lower qubits are in state k, apply R(thetas[k]) to the top qubit."""
    k = n - 1
    t = n - 1
    R = rz if axis == "z" else ry
    if k == 0:
        return [("u", t, R(thetas[0]))]
    gray = [i ^ (i >> 1) for i in range(2**k)]
    sign = np.array([[(-1) ** bin(j & g).count("1") for g in gray] for j in range(2**k)])
    phis = np.linalg.solve(sign, thetas)
    circ = []
    for i in range(2**k):
        circ.append(("u", t, R(phis[i])))
        flip = gray[i] ^ gray[(i + 1) % 2**k]
        circ.append(("cx", flip.bit_length() - 1, t))
    return circ


def mux_rot_matrix(thetas: np.ndarray, n: int, axis: str = "z") -> np.ndarray:
    R = rz if axis == "z" else ry
    d = 2 ** (n - 1)
    blocks = [R(thetas[k]) for k in range(d)]
    out = np.zeros((2 * d, 2 * d), dtype=complex)
    for k in range(d):
        for a in range(2):
            for b in range(2):
                out[a * d + k, b * d + k] = blocks[k][a, b]
    return out


# ── demultiplexing:  U1 ⊕ U2 = (V ⊕ V) · muxRz(θ) · (W ⊕ W) ─────────────────────


def demultiplex(U1: np.ndarray, U2: np.ndarray):
    T, V = schur(U1 @ U2.conj().T, output="complex")
    lam = np.diag(T)
    d = np.sqrt(lam)
    W = np.diag(d) @ V.conj().T @ U2
    thetas = -2 * np.angle(d)
    return V, thetas, W


# ── block-ZXZ factorization (Krol & Al-Ars, arXiv:2403.13692, eqs. 5-6) ──────────


def block_zxz(U: np.ndarray):
    """U = (A1 ⊕ A2) · (H ⊗ I) · (I ⊕ B) · (H ⊗ I) · (I ⊕ C), H on the top qubit."""
    d = U.shape[0] // 2
    Xb, Yb, U21, U22 = U[:d, :d], U[:d, d:], U[d:, :d], U[d:, d:]
    UX, SX = polar(Xb, side="left")
    UY, SY = polar(Yb, side="left")
    Cd = 1j * UY.conj().T @ UX
    C = Cd.conj().T
    A1 = (SX + 1j * SY) @ UX
    A2 = U21 + U22 @ Cd
    B = 2 * A1.conj().T @ Xb - np.eye(d)
    return A1, A2, B, C


def h_top(n: int) -> np.ndarray:
    return embed(H, [n - 1], n)
