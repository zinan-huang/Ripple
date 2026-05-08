# Apéry generating function — holonomic ODE, singularities, Frobenius

**Purpose.** Alternative encoding of $\zeta(3)$ for the Ripple CRN-computable framework. Replace the three-term factorial recurrence by a third-order linear ODE with polynomial coefficients, suitable for PIVP compilation.

**Target series.**
$$f(x) \;=\; \sum_{n=1}^{\infty} \frac{x^{n}}{n^{3}\binom{2n}{n}}, \qquad \text{radius }=4.$$

Markov–Hjortnaes / Apéry identity:
$$\zeta(3) \;=\; \frac{5}{2}\sum_{k=1}^{\infty}\frac{(-1)^{k-1}}{k^{3}\binom{2k}{k}} \;=\; -\,\frac{5}{2}\,f(-1). \tag{A}$$

Equivalently, $F(x) := f(-x) = \sum_{n\ge1}\frac{(-1)^{n-1}x^n}{n^3\binom{2n}{n}}$ satisfies $F(1)=\tfrac{2}{5}\zeta(3)$.

---

## 1. Derivation via Lehmer's identity

**Lehmer (1985), eq. (20):**
$$\sum_{n=1}^{\infty}\frac{x^{2n}}{n^{2}\binom{2n}{n}} \;=\; 2\arcsin^{2}\!\bigl(x/2\bigr), \qquad |x|\le 2. \tag{L}$$

Set $y = x^{2}$ so $g(y):=\sum_{n\ge1}\frac{y^{n}}{n^{2}\binom{2n}{n}} = 2\arcsin^{2}(\sqrt{y}/2)$ for $0\le y\le 4$. Dividing the series termwise by $n$ is the same as integrating $g(u)/u$:
$$f(y) \;=\; \sum_{n\ge1}\frac{y^{n}}{n^{3}\binom{2n}{n}} \;=\; \int_{0}^{y}\frac{g(u)}{u}\,du \;=\; \int_{0}^{y}\frac{2\arcsin^{2}(\sqrt{u}/2)}{u}\,du.$$

Change of variable $\psi=\arcsin(\sqrt{u}/2)$, $u=4\sin^{2}\psi$, $du/u = 2\cot\psi\,d\psi$:
$$\boxed{\;f(y) \;=\; 4\int_{0}^{\arcsin(\sqrt{y}/2)}\!\psi^{2}\cot\psi\,d\psi\;} \tag{K}$$

(Koecher's representation; see also Borwein–Borwein.) Constant of integration: $f(0)=0$ matches the series.

At $y=-1$ the integration path crosses to the imaginary branch: $\arcsin(i/2)=i\sinh^{-1}(1/2)=i\log\varphi$ with $\varphi=(1+\sqrt5)/2$. Substituting $\psi = i\varphi'$ turns $\cot\psi$ into $-i\coth\varphi'$ and gives the real formula
$$-f(-1) \;=\; 4\int_{0}^{\log\varphi}\varphi'^{\,2}\coth\varphi'\,d\varphi' \;=\; \tfrac{2}{5}\zeta(3),$$
which is the Beukers/Koecher integral underlying Apéry.

---

## 2. Third-order ODE

**Recurrence.** $a_n := 1/(n^{3}\binom{2n}{n})$ obeys
$$2(n+1)^{2}(2n+1)\,a_{n+1} \;-\; n^{3}\,a_{n} \;=\; 0, \qquad n\ge 1. \tag{R}$$

**Translate to $\theta=x\partial_x$.** With $\theta x^{n}=nx^{n}$:
- $\sum_{n\ge1} n^{3}a_{n}x^{n} = \theta^{3} f$,
- $\sum_{n\ge1} 2(n{+}1)^{2}(2n{+}1)a_{n+1}x^{n} = \tfrac{1}{x}\bigl[2\theta^{2}(2\theta-1)f - 2a_{1}x\bigr] = \tfrac{1}{x}\bigl[2\theta^{2}(2\theta-1)f - x\bigr]$.

Substituting (R): $\bigl[4\theta^{3}-2\theta^{2}-x\theta^{3}\bigr]f \;=\; x$. Expanding $\theta^{k}$ in terms of $d/dx$:

$$\boxed{\;x^{2}(4-x)\,f'''(x) \;+\; x(10-3x)\,f''(x) \;+\; (2-x)\,f'(x) \;=\; 1.\;} \tag{E}$$

Equivalently for $F(x)=f(-x)$ (evaluation at $+1$):
$$x^{2}(4+x)F''' + x(10+3x)F'' + (2+x)F' \;=\; 1. \tag{E'}$$

Rational initial data at $x=0$ (from (R) and $a_1=1/2$):
$$f(0)=0,\quad f'(0)=a_1=\tfrac{1}{2},\quad f''(0)=2a_2=\tfrac{1}{24},\quad f'''(0)=6a_3=\tfrac{1}{90}.$$

($a_2=1/(2^3\binom{4}{2})=1/48$, $a_3=1/(3^3\binom{6}{3})=1/540$. Numerical check in `experiments/apery_genfun.py` uses $F$, sign-flipped.) Integer-coefficient order-3 ODE with rational ICs — ideal substrate for a PIVP lift.

**Comparison with literature.** This ODE is the standard Apéry-like Picard–Fuchs equation; Zagier's "15 sporadic solutions" classification gives the unified form
$$\bigl(\theta^{3} - z(2\theta{+}1)(a\theta^{2}+a\theta+b) + z^{2}c(\theta{+}1)^{3} + z^{2}d(\theta{+}1)\bigr)y(z)=0.$$
The kernel at $a_n=1/(n^{3}\binom{2n}{n})$ is the $(a,b,c,d)=(0,\tfrac12,0,0)$-type degeneration after normalization; Almkvist–Zudilin, arXiv:math/0402386, treats the higher-order Calabi–Yau cousins. The closed form (E) appears in Borwein–Bradley (*Thirty-two Goldbach Variations* or the related survey) and is implicit in Koecher's 1980 derivation of Apéry's recurrence.

---

## 3. Singular structure

Leading coefficient $x^{2}(4-x)$. Singular points: $\{0,\,4,\,\infty\}$.

| point | type | indicial roots | note |
|---|---|---|---|
| $x=0$  | regular sing. | $\{0,0,\tfrac12\}$ | double root ⇒ possible $\log x$ branch; analytic $f$ picks the $r=0$ solution with no log |
| $x=4$  | regular sing. | $\{0,1,\tfrac32\}$ | branch cut on $(4,\infty)$ |
| $x=\infty$ | regular sing. | (Fuchsian; roots sum to $3$ by Fuchs relation) | not relevant to PIVP lift from origin |

**The evaluation points $x=-1$ (for $f$) and $x=+1$ (for $F$) are ordinary points.** The leading coefficient $x^{2}(4-x)$ evaluates to $-5$ and $3$ respectively — both nonzero. So the holonomic ODE extends $f$ analytically across the evaluation point with no Frobenius gymnastics required *there*. The only regular singular point that matters for the series expansion and for compiling a PIVP from the origin is $x=0$.

**Verification of indicial at $x=0$.** Ansatz $f = x^{r}$ in the homogeneous part of (E) gives leading coefficient
$$4r(r{-}1)(r{-}2) + 10 r(r{-}1) + 2r \;=\; 2r^{2}(2r-1),$$
so indicial polynomial $2r^{2}(2r-1)=0$ with roots $\{0,0,\tfrac12\}$.

---

## 4. Frobenius expansion at $x=0$

Three independent solutions of the homogeneous equation:
$$y_{1}(x) = 1, \qquad y_{2}(x) = \sum_{n\ge 1}a_{n}x^{n}\;\text{ (the series defining }f\text{)}, \qquad y_{3}(x) = x^{1/2}\sum_{n\ge 0}b_{n}x^{n}.$$

The double root at $r=0$ creates a log-solution $y_{2}^{\log}=y_{2}\log x + \sum c_{n}x^{n}$; but this branch does not enter the *particular* solution we want (the one pinned by $f(0)=0$). The relevant Frobenius decomposition for our particular + homogeneous data:

- **Particular solution** (from RHS $=1$): the analytic series $f=\sum a_{n}x^{n}$ satisfies $f'(0)=\tfrac12$, no log. This is forced by $f(0)=0$ and finiteness of $f'(0)$.
- **Homogeneous piece $y_{3}$:** The $r=\tfrac12$ solution has Puiseux branch $\sim \sqrt{x}$, not admissible for a real PIVP on $[0,1]$ without a uniformization $x\to \tau^{2}$. This is the obstruction noted in `experiments/FINDINGS.md` when trying to regularize the origin.

**Coefficients $b_{n}$ for $y_{3}$.** Plugging $y_{3}=x^{1/2}(b_{0}+b_{1}x+\cdots)$ into (E) and matching powers gives the 2-step recurrence
$$b_{n+1} \;=\; \frac{(n+\tfrac12)\bigl[4(n+\tfrac12)(n-\tfrac12) + 10(n+\tfrac12)\cdot ? \bigr]\cdots}{\cdots}\,b_{n}$$
(left schematic; worked out in `experiments/apery_desingularize.py`). The branch only matters if we try to absorb the regular singular point into the PIVP flow, which is precisely the open question below.

---

## 5. PIVP encoding — open questions

The ODE (E) already *is* a rank-3 linear system with polynomial coefficients. Multiplying through by $x^{2}(4-x)$ and rescaling time $d\tau = dt / (x^{2}(4-x))$ gives a degree-$\le 4$ autonomous polynomial system in $(x,f,f',f'')$. The x-evolution $x' = x^{2}(4-x)$ reaches $x=1$ (our evaluation target for $F$) from any $x_{0}\in(0,4)$ in finite rescaled time — but $x=0$ is a fixed point.

**Three obstructions, one of which is likely genuine:**
1. **Origin is a fixed point** of the rescaled flow. Cannot start at $x_{0}=0$ and reach $x_{0}>0$; must inject initial data from the Frobenius series, which gives *rational* ICs for any rational $x_{0}\in(0,1)\cap\mathbb{Q}$. This is fine for a *family* of approximants (one per $r$), not for a single PIVP.
2. **Puiseux branch at $0$.** The $r=\tfrac12$ solution prevents smooth $\mathbb{Q}$-analytic continuation unless we double-cover via $x=\tau^{2}$. Under $x=\tau^{2}$ the ODE becomes order-3 in $\tau$ with rational coefficients and indicial roots $\{0,0,1\}$ — still one log, but no branch. Worth trying explicitly.
3. **Time modulus for first-floor.** Numerics in `apery_genfun.py` show $\alpha\approx 1.0$ under the change $x=1-e^{-t}$. If obstruction (1) can be absorbed into a single zero-IC canonical form (Theorem 3 of RTCRN2 generalised to $\mathbb{Q}$), we obtain $\zeta(3)\in R_{\mathrm{RTCRN}}$ — the open problem flagged in `FINDINGS.md`.

**Next steps for Ripple (Lean).**
- Formalise (R) ⇒ (E) as `AperyGenFunODE`: a `LinearODE` term of order 3 with integer coefficients.
- State (E)+ICs ⇒ $f(1) = \tfrac{2}{5}\zeta(3)$ as an axiom (follows from Apéry; separate proof obligation via (K)).
- Attempt the $x=\tau^{2}$ uniformisation as a Lean-level tactic and re-check indicial roots; if the branch clears, the origin obstruction becomes purely about the zero-IC lift.

---

## References

- D. H. Lehmer, *Interesting series involving the central binomial coefficient*, Amer. Math. Monthly 92 (1985), 449–457. Identity (L) is eq. (20).
- M. Koecher, *Letter to the editor*, Math. Intelligencer 2 (1979/80), 62–64. Derivation of (K) and the Apéry recurrence.
- R. Apéry, *Irrationalité de $\zeta(2)$ et $\zeta(3)$*, Astérisque 61 (1979), 11–13.
- A. van der Poorten, *A proof that Euler missed…*, Math. Intelligencer 1 (1979), 195–203.
- D. Zagier, *Integral solutions of Apéry-like recurrence equations*, https://people.mpim-bonn.mpg.de/zagier/files/tex/AperylikeRecEqs/fulltext.pdf — the 15 sporadic $(a,b,c,d)$ families.
- G. Almkvist, W. Zudilin, *Differential equations, mirror maps and zeta values*, Mirror Symmetry V (2006) 481–515; arXiv:math/0402386. Calabi–Yau generalisations.
- W. Zudilin, bibliography at https://www.math.ru.nl/~zudilin/zw/ (per `reference_zeta_bibliography.md`).
- Internal: `experiments/apery_genfun.py` (numerical verification of (E'), $\alpha\approx 1.0$ under $x=1-e^{-t}$), `experiments/FINDINGS.md` (origin/zero-IC obstruction), `Ripple/Number/AperyCertificate.lean` (current recurrence-based encoding).
