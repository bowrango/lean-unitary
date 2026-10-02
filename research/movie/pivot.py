"""A 3Blue1Brown-style explainer of the balanced-split pivot (Manim Community).

Render everything with ./render.sh, or one scene with
    python -m manim -qh pivot.py Path
All data come from data.py, i.e. from stage2/foldzxz_opt.py on one Haar-random four-qubit target.
"""
import numpy as np
from manim import (BLUE, DOWN, GREY, GREY_B, LEFT, ORANGE, ORIGIN, PI, RIGHT, UP, WHITE, YELLOW,
                   Axes, Circle, Create, DashedLine, DecimalNumber, Dot, FadeIn, FadeOut, Line,
                   MathTex, Rectangle, ReplacementTransform, Scene, SurroundingRectangle, Tex,
                   Transform, ValueTracker, VGroup, Write, always_redraw, rate_functions, smooth)

import data

MID, OUT = BLUE, ORANGE          # middle half / outer quarters of the sorted list
D = data.D


# ---------------------------------------------------------------------------------------------
# helpers

class Captioned(Scene):
    """Scene with a single caption line at the bottom that can be swapped."""

    def setup(self):
        self.caption = None

    def say(self, text, wait=0.0, **kw):
        new = Tex(text, font_size=34, **kw).to_edge(DOWN, buff=0.45)
        if self.caption is None:
            self.play(FadeIn(new, shift=0.1 * UP), run_time=0.6)
        else:
            self.play(ReplacementTransform(self.caption, new), run_time=0.6)
        self.caption = new
        if wait:
            self.wait(wait)


WIRE_Y = {"t": 1.0, "q1": 0.0, "q0": -1.0}


def gate_box(label, x, y=WIRE_Y["t"], color=WHITE, width=None):
    tex = MathTex(label, font_size=30, color=color)
    box = Rectangle(width=width or tex.width + 0.3, height=0.6, color=color, stroke_width=2)
    box.set_fill("#000000", 1.0).move_to([x, y, 0])
    tex.move_to(box)
    return VGroup(box, tex)


def cx_gate(x, ctrl):
    target = Circle(radius=0.2, color=WHITE, stroke_width=2).move_to([x, WIRE_Y["t"], 0])
    target.set_fill("#000000", 1.0)
    plus = VGroup(Line(target.get_left(), target.get_right(), stroke_width=2),
                  Line(target.get_top(), target.get_bottom(), stroke_width=2))
    dot = Dot([x, WIRE_Y[ctrl], 0], radius=0.07)
    stem = Line([x, WIRE_Y[ctrl], 0], target.get_bottom(), stroke_width=2)
    return VGroup(stem, target, plus, dot)


def wires(x0, x1):
    lines = VGroup(*[Line([x0, y, 0], [x1, y, 0], stroke_width=2, color=GREY_B)
                     for y in WIRE_Y.values()])
    labels = VGroup(*[MathTex(name, font_size=30).next_to([x0, y, 0], LEFT, buff=0.2)
                      for name, y in zip([r"t", r"q_1", r"q_0"], WIRE_Y.values())])
    return VGroup(lines, labels)


def unit_circle(radius=2.0):
    circle = Circle(radius=radius, color=GREY, stroke_width=2)
    axes = VGroup(Line([-radius - 0.3, 0, 0], [radius + 0.3, 0, 0], stroke_width=1, color=GREY),
                  Line([0, -radius - 0.3, 0], [0, radius + 0.3, 0], stroke_width=1, color=GREY))
    return VGroup(axes, circle)


def on_circle(phase, radius=2.0, center=ORIGIN):
    return np.array(center) + radius * np.array([np.cos(phase), np.sin(phase), 0])


def colour(j):
    return MID if j in data.S else OUT


# ---------------------------------------------------------------------------------------------
# scenes

class Title(Scene):
    def construct(self):
        title = Tex(r"One more fold per node", font_size=64)
        sub = Tex(r"a pivot gate that balances the multiplexor", font_size=36, color=GREY_B)
        sub.next_to(title, DOWN, buff=0.4)
        self.play(Write(title), run_time=1.5)
        self.play(FadeIn(sub, shift=0.2 * UP))
        self.wait(1.5)
        self.play(FadeOut(title), FadeOut(sub))


class Multiplexor(Captioned):
    def construct(self):
        xs = np.linspace(-4.8, 3.6, 9)
        w = wires(-5.4, 5.3)
        rz0 = gate_box(r"R_z(\varphi_0)", xs[0])
        cx0 = cx_gate(xs[1], "q0")
        rz1 = gate_box(r"R_z(\varphi_1)", xs[2])
        cx1 = cx_gate(xs[3], "q1")
        rz2 = gate_box(r"R_z(\varphi_2)", xs[4])
        cx2 = cx_gate(xs[5], "q0")
        rzp = gate_box(r"R_z(\varphi)", xs[6])
        cx3 = cx_gate(xs[7], "q1")
        h = gate_box(r"H", xs[8], color=YELLOW)
        gates = [rz0, cx0, rz1, cx1, rz2, cx2, rzp, cx3, h]
        central = VGroup(
            Rectangle(width=1.3, height=2.8, color=YELLOW, stroke_width=2).set_fill("#000000", 1)
            .move_to([xs[8] + 1.25, 0, 0]))
        central.add(Tex(r"central\\factor", font_size=26, color=YELLOW).move_to(central[0]))
        circuit = VGroup(w, *gates, central).shift(0.6 * UP)

        self.say(r"The left multiplexor of a Block-ZXZ node: rotations and CX gates.")
        self.play(Create(w), run_time=1)
        self.play(*[FadeIn(g) for g in gates], FadeIn(central), lag_ratio=0.1, run_time=2)
        self.wait(0.5)

        self.say(r"Block-ZXZ slides the last CX through the Hadamard and merges it.")
        self.play(cx3.animate.move_to(central.get_center()).set_opacity(0), run_time=1.5)
        self.play(central[0].animate.set_fill(YELLOW, 0.15), run_time=0.4)
        self.play(central[0].animate.set_fill("#000000", 1), run_time=0.4)
        self.wait(0.3)

        frame = SurroundingRectangle(rzp, color=YELLOW, buff=0.1)
        self.say(r"But $R_z(\varphi)$ stands in the way of the next one.")
        self.play(Create(frame))
        self.wait(1)

        self.say(r"If $\varphi=0$, the rotation vanishes \dots")
        self.play(FadeOut(rzp), FadeOut(frame))
        self.say(r"\dots and a second CX merges: one fewer CX in every node.")
        self.play(cx2.animate.move_to(central.get_center()).set_opacity(0), run_time=1.5)
        self.play(central[0].animate.set_fill(YELLOW, 0.15), run_time=0.4)
        self.play(central[0].animate.set_fill("#000000", 1), run_time=0.4)
        self.wait(1)
        goal = MathTex(r"\text{goal: }\ \varphi=0", font_size=48, color=YELLOW).to_edge(UP)
        self.play(Write(goal))
        self.wait(1.5)
        self.play(*[FadeOut(m) for m in [circuit, goal, self.caption]])


class Angle(Captioned):
    def construct(self):
        eq = MathTex(r"\varphi", r"=", r"\tfrac1D\,\mathbf h^{\mathsf T}\boldsymbol\theta",
                     font_size=52).to_edge(UP, buff=0.6)
        self.say(r"The last angle is a signed sum of the multiplexor angles $\theta_j$.")
        self.play(Write(eq))

        nu = data.nu_at(0.0)
        ax = Axes(x_range=[-0.5, D - 0.5, 1], y_range=[-3.2, 3.2, 1], x_length=8, y_length=3.6,
                  tips=False, axis_config={"color": GREY}).shift(0.2 * DOWN)
        signs = VGroup(*[MathTex("+" if j < D // 2 else "-", font_size=34,
                                 color=GREY_B).move_to(ax.c2p(j, -3.7)) for j in range(D)])
        hlab = MathTex(r"\mathbf h:", font_size=34, color=GREY_B).next_to(signs, LEFT, buff=0.3)

        def bars(order):
            out = VGroup()
            for slot, k in enumerate(order):
                top = ax.c2p(slot, nu[k])
                base = ax.c2p(slot, 0)
                rect = Rectangle(width=0.55, height=abs(top[1] - base[1]), stroke_width=0,
                                 fill_opacity=0.85, fill_color=colour(k))
                rect.move_to((top + base) / 2)
                out.add(rect)
            return out

        order = [0, 1, 2, 3, 4, 5, 6, 7]
        bar = bars(order)
        self.play(Create(ax), FadeIn(signs), FadeIn(hlab))
        self.say(r"The $\theta_j$ are the eigenphases of $C$, placed in any order.")
        self.play(FadeIn(bar, lag_ratio=0.1))

        def readout(order):
            plus = sum(nu[k] for k in order[:D // 2])
            minus = sum(nu[k] for k in order[D // 2:])
            P = plus - minus
            return MathTex(r"\sum_{+}-\sum_{-}=", f"{P:+.2f}", font_size=36).to_corner(UP + RIGHT)

        val = readout(order)
        self.play(FadeIn(val))
        self.say(r"$\varphi=0$ needs a split into two equal halves with equal sums.")
        rng = np.random.default_rng(4)
        for _ in range(5):
            order = list(rng.permutation(D))
            self.play(Transform(bar, bars(order)), Transform(val, readout(order)), run_time=0.7)
            self.wait(0.2)

        count = MathTex(r"\tfrac12\binom{D}{D/2}\ \text{splits:}\quad 35\ (D=8),\quad"
                        r"\approx10^{306}\ (D=1024)", font_size=36).next_to(eq, DOWN, buff=0.35)
        self.say(r"An equal-size subset-sum problem, modulo $2\pi$.")
        self.play(Write(count))
        self.wait(1)
        self.say(r"And for a fixed $C$, there is generically no solution at all.")
        self.wait(2)
        self.play(*[FadeOut(m) for m in [eq, ax, signs, hlab, bar, val, count, self.caption]])


class Path(Captioned):
    def construct(self):
        g = MathTex(r"g=R_z(\alpha)\,R_y(\beta)", font_size=46).to_corner(UP + LEFT)
        self.say(r"Add a single-qubit pivot gate $g$ on the top qubit. It changes $C$.")
        self.play(Write(g))
        circ = unit_circle(2.2).shift(0.3 * DOWN)
        center = circ.get_center()
        self.play(Create(circ))

        beta = ValueTracker(0.0)
        dots = always_redraw(lambda: VGroup(*[
            Dot(on_circle(v, 2.2, center), radius=0.09, color=colour(j))
            for j, v in enumerate(data.nu_at(beta.get_value()))]))
        ghosts = VGroup(*[Dot(on_circle(v, 2.2, center), radius=0.13, color=WHITE,
                              fill_opacity=0.0, stroke_width=2) for v in data.nu_at(0.0)])
        blabel = VGroup(MathTex(r"\beta=", font_size=40),
                        DecimalNumber(0, num_decimal_places=2, font_size=40)).arrange(RIGHT)
        blabel.to_corner(UP + RIGHT)
        blabel[1].add_updater(lambda m: m.set_value(beta.get_value()))
        self.play(FadeIn(dots), FadeIn(blabel))
        self.add(ghosts.set_opacity(0.0))
        self.say(r"Eigenvalues of $C(\beta)$ as $\beta$ sweeps from $0$ to $\pi$ \dots")
        self.play(beta.animate.set_value(PI), run_time=7, rate_func=smooth)
        mirrored = VGroup(*[Dot(on_circle(-v, 2.2, center), radius=0.15, color=YELLOW,
                                fill_opacity=0.0, stroke_width=3) for v in data.nu_at(0.0)])
        eq = MathTex(r"C(\pi)=C(0)^{-1}", font_size=46, color=YELLOW).to_edge(RIGHT).shift(0.5 * DOWN)
        self.say(r"\dots end at the mirror image of where they started: every phase flips sign.")
        self.play(Create(mirrored), Write(eq))
        self.wait(2)
        self.play(*[FadeOut(m) for m in [g, circ, dots, blabel, mirrored, eq, self.caption]])


class Alpha(Captioned):
    def construct(self):
        self.say(r"To compare sorted lists at the two ends, their $2\pi$ branches must match.")
        self.wait(1.5)
        tau_eq = MathTex(r"\tau_k=e^{i\alpha}\rho_k,\qquad \rho_k\in\operatorname{spec}(X^{-1}Y)",
                         font_size=40).to_corner(UP + LEFT)
        self.play(Write(tau_eq))
        R = 2.2
        upper = Rectangle(width=6, height=R + 0.4, stroke_width=0, fill_color=MID,
                          fill_opacity=0.12).move_to([0, (R + 0.4) / 2 - 0.4, 0])
        lower = Rectangle(width=6, height=R + 0.4, stroke_width=0, fill_color=OUT,
                          fill_opacity=0.12).move_to([0, -(R + 0.4) / 2 - 0.4, 0])
        circ = unit_circle(R).shift(0.4 * DOWN)
        center = circ.get_center()
        axis = Line(center + (R + 0.4) * LEFT, center + (R + 0.4) * RIGHT, color="#FF4040",
                    stroke_width=4)
        self.play(FadeIn(upper), FadeIn(lower), Create(circ), Create(axis))

        rho = data.rho()
        alpha = ValueTracker(0.0)

        def taus():
            t = np.angle(np.exp(1j * alpha.get_value()) * rho)
            return VGroup(*[Dot(on_circle(a, R, center), radius=0.1,
                                color=MID if np.sin(a) > 0 else OUT) for a in t])

        dots = always_redraw(taus)
        count = always_redraw(lambda: MathTex(
            r"N(\alpha)=", str(int(np.sum((np.exp(1j * alpha.get_value()) * rho).imag > 0))),
            r"\ \text{above}", font_size=40).to_corner(UP + RIGHT))
        self.say(r"Rotating by $\alpha$ moves all $\tau_k$ together; count how many lie above.")
        self.play(FadeIn(dots), FadeIn(count))
        target = data.alpha_star() + 2 * np.pi
        self.play(alpha.animate.set_value(target), run_time=7, rate_func=rate_functions.linear)
        self.say(r"Stop at $\alpha^\ast$ with $D/2$ above and $D/2$ below \dots")
        self.wait(1.5)
        sig = MathTex(r"\Rightarrow\ \sigma(\pi)=-\sigma(0)", font_size=42,
                      color=YELLOW).to_edge(RIGHT).shift(0.4 * DOWN)
        self.say(r"\dots then the total phase $\sigma=\arg\det C$ flips sign too.")
        self.play(Write(sig))
        self.wait(2)
        self.play(*[FadeOut(m) for m in [tau_eq, upper, lower, circ, axis, dots, count, sig,
                                         self.caption]])


class Beta(Captioned):
    def construct(self):
        line = Axes(x_range=[-PI, PI, PI / 2], y_range=[0, 1, 1], x_length=10, y_length=0.01,
                    tips=False, axis_config={"color": GREY}).shift(1.9 * UP)
        ticks = VGroup(*[MathTex(s, font_size=28, color=GREY_B).move_to(line.c2p(v, 0) + 0.35 * DOWN)
                         for v, s in [(-PI, r"-\pi"), (0, "0"), (PI, r"\pi")]])
        beta = ValueTracker(0.0)
        dots = always_redraw(lambda: VGroup(*[
            Dot(line.c2p(v, 0), radius=0.11, color=colour(j))
            for j, v in enumerate(data.nu_at(beta.get_value()))]))
        self.say(r"Sort the eigenphases: middle half in blue, outer quarters in orange.")
        self.play(Create(line), FadeIn(ticks), FadeIn(dots))
        self.wait(1)

        ax = Axes(x_range=[0, PI, PI / 2], y_range=[-1.6, 2.2, 1], x_length=7, y_length=3.3,
                  tips=False, axis_config={"color": GREY}).shift(1.35 * DOWN)
        xl = MathTex(r"\beta", font_size=32).next_to(ax.x_axis.get_right(), DOWN)
        yl = MathTex(r"P(\beta)=\textstyle\sum_{\rm blue}-\sum_{\rm orange}", font_size=32)
        yl.next_to(ax, UP, buff=0.1).align_to(ax, LEFT)
        self.play(Create(ax), FadeIn(xl), FadeIn(yl))
        trace = always_redraw(lambda: ax.plot(
            lambda b: data.imbalance(data.nu_at(b)), x_range=[0, max(beta.get_value(), 1e-3), 0.01],
            color=WHITE))
        head = always_redraw(lambda: Dot(ax.c2p(beta.get_value(),
                                                data.imbalance(data.nu_at(beta.get_value()))),
                                         color=YELLOW, radius=0.07))
        self.add(trace, head)
        self.say(r"Negating a sorted list reverses it, and the middle half stays the middle half.")
        self.play(beta.animate.set_value(PI), run_time=8, rate_func=smooth)
        full = ax.plot(lambda b: data.imbalance(data.nu_at(b)), x_range=[0, PI, 0.01], color=WHITE)
        self.remove(trace)
        self.add(full)
        trace = full
        self.wait(0.5)
        self.say(r"So the imbalance ends at minus where it began: $P(\pi)=-P(0)$.")
        self.wait(2)
        bstar = data.beta_star()
        bar = Line(ax.c2p(bstar, -1.6), ax.c2p(bstar, 1.5), color=WHITE, stroke_width=4)
        blab = MathTex(r"\beta^\ast", font_size=34).next_to(bar, UP, buff=0.08)
        self.say(r"It must cross zero; Brent's method finds the crossing $\beta^\ast$.")
        self.play(Create(bar), Write(blab))
        self.play(beta.animate.set_value(bstar), run_time=2)
        self.wait(2)
        self.play(*[FadeOut(m) for m in [line, ticks, dots, ax, xl, yl, trace, head, bar, blab,
                                         self.caption]])


class Merge(Captioned):
    def construct(self):
        nu = data.nu_at(data.beta_star())
        order = data.S + [k for k in range(D) if k not in data.S]
        ax = Axes(x_range=[-0.5, D - 0.5, 1], y_range=[-3.2, 3.2, 1], x_length=8, y_length=3.6,
                  tips=False, axis_config={"color": GREY}).shift(0.6 * UP)
        bars = VGroup()
        for slot, k in enumerate(order):
            top, base = ax.c2p(slot, nu[k]), ax.c2p(slot, 0)
            rect = Rectangle(width=0.55, height=abs(top[1] - base[1]), stroke_width=0,
                             fill_opacity=0.85, fill_color=colour(k)).move_to((top + base) / 2)
            bars.add(rect)
        plus = MathTex(r"\textstyle\sum_{+}", font_size=36, color=MID).move_to(ax.c2p(1.5, 2.8))
        minus = MathTex(r"\textstyle\sum_{-}", font_size=36, color=OUT).move_to(ax.c2p(5.5, 2.8))
        eq = MathTex(r"=", font_size=40).move_to(ax.c2p(3.5, 2.8))
        self.say(r"At $\beta^\ast$: blue on the $+$ slots, orange on the $-$ slots.")
        self.play(Create(ax), FadeIn(bars, lag_ratio=0.1))
        self.play(Write(plus), Write(eq), Write(minus))
        phi = MathTex(r"\varphi=\tfrac1D\,\mathbf h^{\mathsf T}\boldsymbol\theta=0", font_size=48,
                      color=YELLOW).next_to(ax, DOWN, buff=0.4)
        self.say(r"Equal sums, so $\varphi=0$, and the extra CX merges.")
        self.play(Write(phi))
        self.wait(1.5)
        self.play(*[FadeOut(m) for m in [ax, bars, plus, minus, eq]], phi.animate.to_edge(UP))
        res = VGroup(
            MathTex(r"\text{one fewer CX per node}", font_size=44),
            MathTex(r"\tfrac{22}{48}\,4^n\ \longrightarrow\ \tfrac{21}{48}\,4^n", font_size=56),
            MathTex(r"\text{found by two 1-D searches, not a subset search}", font_size=36,
                    color=GREY_B),
        ).arrange(DOWN, buff=0.45)
        self.say(r"Every node of the recursion saves a CX.")
        self.play(FadeIn(res[0], shift=0.2 * UP))
        self.play(Write(res[1]))
        self.play(FadeIn(res[2]))
        self.wait(3)
        self.play(*[FadeOut(m) for m in [phi, res, self.caption]])


SCENES = [Title, Multiplexor, Angle, Path, Alpha, Beta, Merge]
