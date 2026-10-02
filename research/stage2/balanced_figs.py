r"""Generate every figure of ../supplementary.tex (balanced-split pivot, paper Sec. II.A-II.C).

Runs the construction of foldzxz_opt.py on one Haar-random four-qubit target (D = 8), samples the
quantities each figure shows, and writes one PDF per figure to ../figures/ at its printed size,
plus bal_values.tex with the numbers quoted in the text. Needs numpy, scipy and matplotlib, and a
LaTeX installation for text rendering.

Usage (from this directory): python3 balanced_figs.py, then compile ../supplementary.tex.
"""
import os

import matplotlib
matplotlib.use("pdf")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch

from core import random_unitary
from foldzxz_opt import PivotPath, ordered_phases

FIG_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'figures')
N_QUBITS, SEED = 4, 2                 # D = 2^(n-1) = 8 eigenphases
N_BISECT_SHOWN = 7                    # bisection midpoints marked in the P(beta) plot


def unit(z):
    """Direction of a complex number, as an (x, y) pair."""
    t = np.angle(z)
    return float(np.cos(t)), float(np.sin(t))


def collect(n=N_QUBITS, seed=SEED):
    """Sample every quantity drawn in the figures for one Haar-random target."""
    D = 2 ** (n - 1)
    U = random_unitary(2 ** n, np.random.default_rng(seed))
    path = PivotPath(U, n)
    X, Y = U[:D, :D], U[:D, D:]
    rho = np.linalg.eigvals(np.linalg.solve(X, Y))
    alpha = path.alpha
    S = list(range(D // 4, 3 * D // 4))   # middle half of the sorted list

    def lift(beta):
        """Sorted eigenphase lifts nu_j(beta), pinned to the total phase sigma(beta)."""
        mu = np.angle(np.linalg.eigvals(path.C(beta)))
        return ordered_phases(mu, path.determinant_phase(beta))

    def imbalance(beta):
        nu = lift(beta)
        return nu[S].sum() - np.delete(nu, S).sum()

    d = {'alpha': alpha}
    d['tau'] = [unit(t) for t in np.exp(1j * alpha) * rho]
    d['rho'] = [unit(r) for r in rho]
    A = np.linspace(0, 2 * np.pi, 1441)
    d['N'] = [(float(a), int(np.sum((np.exp(1j * a) * rho).imag > 0))) for a in A]
    crossings = np.mod(-np.angle(rho), np.pi)
    d['cross'] = sorted(np.r_[crossings, crossings + np.pi].tolist())

    B = np.linspace(0, np.pi, 241)
    d['sigma'] = [(float(b), float(path.determinant_phase(b))) for b in B]
    L = np.array([lift(b) for b in B])
    d['nu'] = [[(float(b), float(L[i, j])) for i, b in enumerate(B)] for j in range(D)]
    d['P'] = [(float(b), float(imbalance(b))) for b in B]

    lo, hi, p_lo, mids = 0.0, np.pi, imbalance(0.0), []
    for k in range(N_BISECT_SHOWN):
        mid = (lo + hi) / 2
        p_mid = imbalance(mid)
        mids.append((k + 1, mid, p_mid))
        if np.sign(p_mid) == np.sign(p_lo):
            lo, p_lo = mid, p_mid
        else:
            hi = mid
    d['mids'] = mids

    bstar = path.find_beta()
    d['bstar'] = bstar
    d['nu0'], d['nupi'], d['nustar'] = (lift(b).tolist() for b in (0.0, np.pi, bstar))
    d['C0'] = np.angle(np.linalg.eigvals(path.C(0.0))).tolist()
    d['Cpi'] = np.angle(np.linalg.eigvals(path.C(np.pi))).tolist()
    d['P0'], d['Ppi'] = imbalance(0.0), imbalance(np.pi)
    nu = np.array(d['nustar'])
    d['halfsums'] = (nu[S].sum(), np.delete(nu, S).sum())
    return d



# ---------------------------------------------------------------------------------------------
# Plotting

MID, OUT = "#0047cc", "#d96c00"       # middle half / outer quarters (cmid, cout in the document)
RED, GREY = "#b30000", "0.6"
plt.rcParams.update({
    "text.usetex": True, "font.family": "serif", "font.size": 9, "axes.labelsize": 9,
    "xtick.labelsize": 8, "ytick.labelsize": 8, "axes.linewidth": 0.6, "lines.linewidth": 1.2,
    "text.latex.preamble": r"\usepackage{amsmath,amssymb,bm}",
})
PI_TICKS = ([0, np.pi / 2, np.pi], [r"$0$", r"$\pi/2$", r"$\pi$"])


def unpack(pairs):
    return np.array([x for x, _ in pairs]), np.array([y for _, y in pairs])


def beta_axis(ax, ylabel):
    ax.set_xlim(0, np.pi)
    ax.set_xticks(*PI_TICKS)
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(ylabel)


def unit_circle(ax, r=1.25):
    t = np.linspace(0, 2 * np.pi, 400)
    ax.plot(np.cos(t), np.sin(t), color="0.45", lw=0.7)
    ax.set_xlim(-r, r)
    ax.set_ylim(-r, r)
    ax.set_aspect("equal")
    ax.axis("off")


def fig_pipeline():
    fig, ax = plt.subplots(figsize=(6.5, 1.75))
    ax.set_xlim(0, 13.6)
    ax.set_ylim(0, 3.5)
    ax.axis("off")

    def box(x, y, w, h, text, search=False):
        ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0.02,rounding_size=0.15",
                                    fc=(0.9, 0.93, 1.0) if search else "white",
                                    ec=MID if search else "0.2", lw=0.8))
        ax.text(x, y, text, ha="center", va="center", fontsize=7.5)

    def arrow(p, q, color="0.4"):
        ax.add_patch(FancyArrowPatch(p, q, arrowstyle="-|>", mutation_scale=8, color=color, lw=0.9))

    xs, y, w = [1.3, 4.05, 6.8, 9.55, 12.3], 2.7, 2.45
    labels = [r"pivot\\$g=R_z(\alpha)$\\$\times R_y(\beta)$", r"top-row\\blocks $X_g,Y_g$\\(Eq.~8)",
              r"multiplexor\\matrix $C(\beta)$\\(Eq.~9)", r"angles $\bm\theta$\\$=$\\eigenphases",
              r"$\varphi=\tfrac1D\mathbf h^{\mathsf T}\bm\theta$\\$=0$\,?"]
    for x, text in zip(xs, labels):
        box(x, y, w, 1.3, r"\shortstack{" + text + "}")
    for x0, x1 in zip(xs[:-1], xs[1:]):
        arrow((x0 + w / 2, y), (x1 - w / 2, y))
    box(4.05, 0.75, 3.9, 1.0, r"\shortstack{\textbf{choose $\alpha$}: sort the $D$ crossing\\angles, "
                               r"pick a count-$D/2$ interval}", search=True)
    box(9.55, 0.75, 3.2, 1.0, r"\shortstack{\textbf{choose $\beta$}: bisect the\\imbalance $P(\beta)$}",
        search=True)
    arrow((2.9, 1.25), (1.6, 2.03), MID)
    arrow((8.4, 1.25), (2.0, 2.03), MID)
    return fig


def fig_endpoints(d):
    fig, ax = plt.subplots(figsize=(3.3, 2.3))
    unit_circle(ax)
    ax.axhline(0, color="0.8", lw=0.6, zorder=0)
    ax.axvline(0, color="0.8", lw=0.6, zorder=0)
    c0, cpi = np.exp(1j * np.array(d['C0'])), np.exp(1j * np.array(d['Cpi']))
    ax.plot(c0.real, c0.imag, "o", color="k", ms=4, label=r"eigenvalues of $C(0)$")
    ax.plot(cpi.real, cpi.imag, "o", mfc="none", mec=MID, mew=1.1, ms=7, label=r"eigenvalues of $C(\pi)$")
    ax.legend(loc="upper left", bbox_to_anchor=(0.88, 1.0), frameon=False, fontsize=8)
    return fig


def fig_alpha_tau(d, D):
    fig, ax = plt.subplots(figsize=(2.0, 2.15))
    unit_circle(ax, 1.3)
    ax.set_ylim(-1.5, 1.5)
    ax.axhspan(0, 1.5, color=MID, alpha=0.07, lw=0)
    ax.axhspan(-1.5, 0, color=OUT, alpha=0.07, lw=0)
    ax.axhline(0, color=RED, lw=1.6)
    ax.axvline(0, color="0.8", lw=0.6)
    rx, ry = unpack(d['rho'])
    ax.plot(rx, ry, "o", mfc="none", mec=GREY, ms=4)
    for x, y in d['tau']:
        ax.plot(x, y, "o", color=MID if y > 0 else OUT, ms=4.5)
    ax.text(0, 1.3, rf"$N=D/2={D // 2}$ above", ha="center", va="center", fontsize=7, color=MID)
    ax.text(0, -1.3, rf"${D // 2}$ below", ha="center", va="center", fontsize=7, color=OUT)
    return fig


def fig_alpha_count(d, D):
    fig, ax = plt.subplots(figsize=(2.25, 1.85))
    a, n = unpack(d['N'])
    upper = n == D // 2
    ax.fill_between(a, 0, D, where=upper, color=MID, alpha=0.15, lw=0, step="post")
    ax.step(a, n, where="post", color="k", lw=1.0)
    ax.axhline(D // 2, color=MID, ls="--", lw=0.8)
    for c in d['cross']:
        ax.plot([c, c], [0, 0.35], color="0.45", lw=0.6)
    ax.axvline(d['alpha'], color=RED, lw=1.0)
    ax.text(d['alpha'] + 0.08, D - 1.1, r"$\alpha$", color=RED, fontsize=8)
    ax.set_xlim(0, 2 * np.pi)
    ax.set_ylim(0, D)
    ax.set_xticks([0, np.pi, 2 * np.pi], [r"$0$", r"$\pi$", r"$2\pi$"])
    ax.set_yticks([0, D // 2, D])
    ax.set_xlabel(r"$\alpha$")
    ax.set_ylabel(r"$N(\alpha)$")
    fig.tight_layout(pad=0.2)
    return fig


def fig_alpha_sigma(d):
    fig, ax = plt.subplots(figsize=(2.25, 1.85))
    b, s = unpack(d['sigma'])
    ax.axhline(0, color="0.7", ls=":", lw=0.8)
    ax.plot(b, s, color="k")
    ax.plot([0, np.pi], [s[0], s[-1]], "o", color="k", ms=3)
    beta_axis(ax, r"$\sigma(\beta)$")
    fig.tight_layout(pad=0.2)
    return fig


def fig_beta_lifts(d, S):
    fig, ax = plt.subplots(figsize=(3.15, 2.5))
    for j, curve in enumerate(d['nu']):
        b, v = unpack(curve)
        ax.plot(b, v, color=MID if j in S else OUT)
    ax.axvline(d['bstar'], color="0.4", ls="--", lw=0.8)
    ax.text(d['bstar'], 3.5, r"$\beta^\ast$", ha="center", va="bottom", fontsize=8)
    ax.set_ylim(-3.4, 3.4)
    beta_axis(ax, r"lifted eigenphases $\nu_j(\beta)$")
    fig.tight_layout(pad=0.2)
    return fig


def fig_beta_imbalance(d, shown=6):
    fig, ax = plt.subplots(figsize=(3.15, 2.5))
    b, p = unpack(d['P'])
    ax.axhline(0, color="0.7", ls=":", lw=0.8)
    ax.plot(b, p, color="k")
    for k, m, v in d['mids'][:shown]:
        ax.plot(m, v, "o", color="k", ms=3)
        ax.annotate(str(k), (m, v), textcoords="offset points", xytext=(-4, 4), fontsize=7)
    ax.plot(d['bstar'], 0, "o", color=MID, ms=5)
    ax.annotate(r"$\beta^\ast$", (d['bstar'], 0), textcoords="offset points", xytext=(4, -10),
                color=MID, fontsize=8)
    beta_axis(ax, r"imbalance $P(\beta)$")
    fig.tight_layout(pad=0.2)
    return fig


def fig_beta_lists(d, S):
    fig, ax = plt.subplots(figsize=(5.6, 1.55))
    rows = [(d['nu0'], 2.0, r"$\beta=0$"), (d['nustar'], 1.0, r"$\beta=\beta^\ast$"),
            (d['nupi'], 0.0, r"$\beta=\pi$")]
    for vals, y, label in rows:
        ax.plot([-3.4, 3.4], [y, y], color="0.55", lw=0.7)
        ax.text(-3.55, y, label, ha="right", va="center", fontsize=8.5)
        for j, v in enumerate(vals):
            ax.plot(v, y, "o", color=MID if j in S else OUT, ms=4.5)
            dy = 0.2 if j % 2 == 0 else -0.33
            ax.text(v, y + dy, rf"$\nu_{j}$", ha="center", fontsize=6.5)
    for v, l in zip([-np.pi, -np.pi / 2, 0, np.pi / 2, np.pi],
                    [r"$-\pi$", r"$-\pi/2$", r"$0$", r"$\pi/2$", r"$\pi$"]):
        ax.text(v, -0.6, l, ha="center", fontsize=7, color="0.4")
    ax.set_xlim(-4.6, 3.6)
    ax.set_ylim(-0.75, 2.4)
    ax.axis("off")
    return fig


def fig_split(d, S, D):
    fig, ax = plt.subplots(figsize=(4.6, 2.1))
    nu = np.array(d['nustar'])
    rest = [k for k in range(D) if k not in S]
    half = D // 2
    ax.bar(range(half), nu[S], width=0.45, color=MID, alpha=0.75, ec=MID)
    ax.bar(range(half, D), nu[rest], width=0.45, color=OUT, alpha=0.75, ec=OUT)
    ax.axhline(0, color="0.5", lw=0.6)
    ax.axvline(half - 0.5, color="0.6", lw=0.7)
    s_mid, s_out = d['halfsums']
    ax.text((half - 1) / 2, 2.75, rf"$\sum={s_mid:.4f}$", ha="center", color=MID, fontsize=8.5)
    ax.text(half + (half - 1) / 2, -3.05, rf"$\sum={s_out:.4f}$", ha="center", color=OUT, fontsize=8.5)
    ax.set_xticks(range(D))
    ax.set_ylim(-3.4, 3.4)
    ax.set_xlim(-0.7, D - 0.3)
    ax.set_xlabel(r"basis state $j$ of the lower register", labelpad=14)
    ax.set_ylabel(r"angle $\theta_j$")
    sec = ax.secondary_xaxis(-0.11)
    sec.set_xticks([(half - 1) / 2, half + (half - 1) / 2], [r"$h_j=+1$", r"$h_j=-1$"])
    sec.tick_params(length=0)
    sec.spines["bottom"].set_visible(False)
    fig.tight_layout(pad=0.2)
    return fig


def values(d):
    """Numbers quoted in the text, as macros."""
    return "\n".join([
        rf"\newcommand{{\BalPzero}}{{{d['P0']:.3f}}}",
        rf"\newcommand{{\BalPpi}}{{{d['Ppi']:.3f}}}",
        rf"\newcommand{{\BalBetaStar}}{{{d['bstar']:.4f}}}",
        rf"\newcommand{{\BalSumMid}}{{{d['halfsums'][0]:.5f}}}",
        rf"\newcommand{{\BalSumOut}}{{{d['halfsums'][1]:.5f}}}",
    ])


def main():
    d = collect()
    D = 2 ** (N_QUBITS - 1)
    S = list(range(D // 4, 3 * D // 4))
    figures = {
        'bal_pipeline': fig_pipeline(),
        'bal_endpoints': fig_endpoints(d),
        'bal_alpha_tau': fig_alpha_tau(d, D),
        'bal_alpha_count': fig_alpha_count(d, D),
        'bal_alpha_sigma': fig_alpha_sigma(d),
        'bal_beta_lifts': fig_beta_lifts(d, S),
        'bal_beta_imbalance': fig_beta_imbalance(d),
        'bal_beta_lists': fig_beta_lists(d, S),
        'bal_split': fig_split(d, S, D),
    }
    os.makedirs(FIG_DIR, exist_ok=True)
    for name, fig in figures.items():
        fig.savefig(os.path.join(FIG_DIR, name + '.pdf'), bbox_inches="tight", pad_inches=0.02)
        plt.close(fig)
    with open(os.path.join(FIG_DIR, 'bal_values.tex'), 'w') as f:
        f.write("% generated by stage2/balanced_figs.py -- do not edit\n" + values(d) + "%\n")
    print(f"wrote {len(figures)} figures and bal_values.tex to {os.path.normpath(FIG_DIR)}")


if __name__ == "__main__":
    main()
