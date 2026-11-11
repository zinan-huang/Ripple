# Kurtz-type limit theorems beyond convergence in probability

Paper-phase document: sections 0–1 diagnose the gap against the papers; sections 2–4 give the proofs,
after two rounds of review; section 5 is the statement list with its implementation status at the start
of the Lean phase; section 6 is the review history.

## 0. Diagnosis

Of the three former "sorry-free versions" of Kurtz, only convergence in probability had
content, and it was conditional. Since FIX1/FIX3, `Kurtz.kurtz_finite_horizon` is unconditional
(model conditions only). Remaining gap against the papers:

| paper result | Lean before this lane | root class |
|---|---|---|
| LLN, `sup_{t≤T} |X̄_N − x| → 0` in probability (Kurtz 1970) | proved | — |
| LLN with exponential tail (Darling–Norris 2008 §4; Kurtz 1978 uses exponential bounds of this type) | absent | (b) proof not in repo |
| CLT, `√N(X̄_N − x)` ⇒ Gaussian (Kurtz 1971; EK 11.2.3) | absent (removed) | (b) |
| strong approximation, KMT coupling (Kurtz 1978) | absent (removed) | out of reach (no KMT, no D[0,T]) |

All objects are already defined in the repository (canonical chain `DensityDepCTMC.mk N hN Γ`,
canonical record law, `frozenDensityProcess`, `MeanFieldSolution`); no class (a) root. Mathlib
supplies Lévy's continuity theorem (`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`)
and `ProbabilityTheory.multivariateGaussian` with `charFun_multivariateGaussian`; it has no
Skorokhod space and no KMT coupling, so the CLT is proved for finite-dimensional distributions and
the strong approximation is replaced by its consequence for the sup error (§3).

## 1. Setting and notation

`S` finite, `q` a Q-matrix (`QMatrix S`): `q(x,y) ≥ 0` for `y ≠ x`, exit rate
`λ(x) = Σ_{y≠x} q(x,y)`. Canonical record law `P_{x₀}` (`QMatrix.canonicalRecordMeasure`) on
record sequences `R_n = (H_n, Y_n)`: `R_0 = (0, x₀)`; given `R_0..R_n`, if `λ(Y_n) > 0` then
`H_{n+1} ~ Exp(λ(Y_n))` independent of `Y_{n+1} ~ q(Y_n, ·)/λ(Y_n)`; if `λ(Y_n) = 0` then
`R_{n+1} = (0, Y_n)`. Jump times `T_0 = 0`, `T_n = H_1 + … + H_n` (`path.times n = T_{n+1}`).
The state at time `t` is `X(t) = Y_n` for `T_n ≤ t < T_{n+1}`; after absorption at `Y_m`,
`X(t) = Y_m` (this is `CTMCPath.frozenStateAt`). Filtration `F_n = σ(R_0,…,R_n)`.

Fact F1 (Ionescu-Tulcea, `QMatrix.canonicalRecordMeasure_history_next`): the joint law of
`(R_0..R_n, R_{n+1})` is the law of `(R_0..R_n)` composed with the kernel `κ(Y_n)` above. Hence
for bounded measurable `Φ`, `E[Φ(R_0..R_n, R_{n+1})] = E[∫ Φ(R_0..R_n, r) κ(Y_n)(dr)]`.

## 2. The exponential martingale of a finite CTMC

Let `S` be finite and let `q` be a `QMatrix S`. Write

\[
  \lambda(x)=\sum_{y\ne x}q(x,y)
\]

for the exit rate. Under the canonical record law started at `x₀`, write
`R_k=(H_k,Y_k)`, put `T_0=0` and `T_k=H_1+\cdots+H_k`, and let
`𝓕_k=σ(R_0,…,R_k)`. In the repository convention,
`path.times k = T_{k+1}`.

### 2.1. Hypotheses and clamped definitions

Fix a finite set `D ⊂ ℝ` and a tilt

\[
  g:\mathbb R\times S\times S\longrightarrow\mathbb C
\]

with the following properties.

1. `g(s,x,x)=0` for every `s,x`.
2. For every `x,y`, the map `s ↦ g(s,x,y)` is Borel measurable.
3. There is a finite number `G` such that `‖g(s,x,y)‖ ≤ G` for every `s,x,y`.
4. For every `x,y`, the map `s ↦ g(s,x,y)` is continuous at every `s ∉ D`.

These are the paper hypotheses corresponding to the repository structure
`IsExpTilt`: the Lean structure records measurability explicitly, rather than asking every later
proof to reconstruct it. When continuity away from a finite `D` is the primitive assumption,
measurability follows because the restriction to `ℝ \ D` is continuous and the values on the finite
set `D` form a measurable finite modification.

Define

\[
  c(s,x)=\sum_{y\ne x}q(x,y)\bigl(e^{g(s,x,y)}-1\bigr).
\]

Since `S` is finite, `c(·,x)` is measurable, bounded, and continuous away from `D`. Choose a finite
constant `C_c` with `‖c(s,x)‖≤C_c` for all `s,x`.

The Lean definition is total on arbitrary record sequences, including sequences with negative
holding-time coordinates. For a current time `u`, state `x`, next record `r=(h,y)`, and observation
horizon `t≥0`, put

\[
\begin{aligned}
  v&=\max(u,0), & \bar h&=\max(h,0),\\
  a_t(u,x;r)
    &=\mathbf 1_{\{v+h\le t\}}g(v+h,x,y)
      -\int_{\min(v,t)}^{\min(v+\bar h,t)}c(s,x)\,ds .
\end{aligned}
\]

For a record trajectory `ω`, define

\[
  A_n(t)=\sum_{k=0}^{n-1}a_t(T_k,Y_k;R_{k+1}),
  \qquad Z_n(t)=e^{A_n(t)}.
\]

On the event on which all holding times are nonnegative, the clamps disappear and this is

\[
 A_n(t)=\sum_{k=1}^{n}\mathbf 1_{\{T_k\le t\}}
     g(T_k,Y_{k-1},Y_k)
 -\sum_{k=0}^{n-1}\int_{T_k\wedge t}^{T_{k+1}\wedge t}c(s,Y_k)\,ds.
\]

For every record sequence, not only almost every one,

\[
  |A_n(t)|\le n(G+C_ct),
  \qquad |Z_n(t)|\le e^{n(G+C_ct)}.                 \tag{2.1}
\]

The second estimate uses `|e^z|=e^{Re z}≤e^{|z|}`. It is the deterministic integrability bound used
below.

### Lemma L7 (measurability, adaptedness, and integrability package)

For fixed `t≥0`:

* `s ↦ c(s,x)` is measurable for every `x`;
* if `a,b` are measurable real-valued functions, then
  `z ↦ ∫_{a(z)}^{b(z)} c(s,x) ds` is measurable;
* `(u,r) ↦ a_t(u,x;r)` and `ρ_t(u,x;r):=exp(a_t(u,x;r))` are measurable;
* `A_n(t)` and `Z_n(t)` are `𝓕_n`-measurable;
* `Z_n(t)` is integrable; and if `ξ` is bounded and `𝓕_n`-measurable, then
  `(R_0,…,R_{n+1}) ↦ ξZ_n(t)ρ_t(T_n,Y_n;R_{n+1})` is measurable and integrable.

#### Proof

The map `c(·,x)` is a finite sum of products and compositions of measurable maps. For its integral,
let

\[
  C_x(r)=\int_0^r c(s,x)\,ds.
\]

A bounded measurable function is locally Bochner integrable, and its indefinite integral is locally
absolutely continuous, hence continuous. Therefore

\[
  \int_{a(z)}^{b(z)}c(s,x)\,ds=C_x(b(z))-C_x(a(z))
\]

is measurable whenever `a` and `b` are measurable. The operations `max`, `min`, addition, coordinate
projection, and the indicator of the closed relation `v+h≤t` are measurable, so `a_t` and `ρ_t`
are measurable.

Each `T_k` is a finite sum of record-coordinate projections. Thus each summand defining `A_n(t)` is
a measurable function of `R_0,…,R_n`; finite summation and the complex exponential give the
measurability of `A_n(t)` and `Z_n(t)`. The bound (2.1) proves integrability. Multiplying by bounded
measurable `ξ` preserves measurability and integrability. ∎

### Lemma 2.1 (one-step identity)

Let `x∈S`, `u≥0`, and `t≥0`. For a next record `r=(r₁,y)`, put

\[
 \rho(r)=\exp\!\left(
   \mathbf 1_{\{u+r_1\le t\}}g(u+r_1,x,y)
   -\int_{u\wedge t}^{(u+r_1)\wedge t}c(s,x)\,ds\right).
\]

Then

\[
  \int \rho(r)\,\kappa(x,dr)=1,                         \tag{2.2}
\]

where `κ(x)` is the canonical jump-hold kernel from state `x`.

#### Proof

If `x` is absorbing, `κ(x)=δ_(0,x)`. The diagonal condition gives `g(u,x,x)=0`, and the integral has
equal endpoints, so `ρ=1`.

Suppose that `x` is not absorbing and set `λ=λ(x)>0`. If `u≥t`, the exponential holding time is
strictly positive almost surely, hence `u+r₁>t`; the jump indicator vanishes and both integral
endpoints are `t`. Thus `ρ=1` almost surely.

It remains to consider `u<t`. Put `w=t-u>0` and

\[
  \phi(s)=\sum_{y\ne x}q(x,y)e^{g(s,x,y)}=c(s,x)+\lambda,
  \qquad
  \Psi(h)=\exp\!\left(-\int_u^{u+h}\phi(s)\,ds\right).
\]

The holding time has density `λe^{-λh}` on `(0,∞)`, and conditionally on a jump the next state has
mass `q(x,y)/λ` for `y≠x`. Splitting at `w` gives

\[
\begin{aligned}
 \int\rho\,d\kappa(x)
 &=\int_0^w \lambda e^{-\lambda h}
     \sum_{y\ne x}\frac{q(x,y)}{\lambda}
       e^{g(u+h,x,y)}
       e^{-\int_u^{u+h}c(s,x)ds}\,dh\\
 &\quad+\Pr(H>w)e^{-\int_u^t c(s,x)ds}\\
 &=\int_0^w\phi(u+h)\Psi(h)\,dh+\Psi(w).             \tag{2.3}
\end{aligned}
\]

The choice of `H≤w` in the first term and `H>w` in the second is immaterial because the exponential
law has no atom at `w`.

For completeness, here is the analytic identity used in the last line. The function

\[
  P(h)=\int_u^{u+h}\phi(s)\,ds
\]

is absolutely continuous on `[0,w]`, and the Lebesgue fundamental theorem gives
`P'(h)=φ(u+h)` for almost every `h`. Viewing `ℂ` as `ℝ²`, the complex exponential is continuously
differentiable. The absolutely-continuous chain rule therefore gives

\[
  \Psi'(h)=-\phi(u+h)\Psi(h)
\]

for almost every `h`. Equivalently, one may split `[0,w]` at the finitely many points
`(D-u)∩[0,w]`, apply the classical fundamental theorem on each open subinterval, and add the
identities; continuity of the primitive and of `Ψ` cancels all intermediate endpoints. Since `Ψ`
is absolutely continuous,

\[
  \int_0^w\phi(u+h)\Psi(h)\,dh
    =-\int_0^w\Psi'(h)\,dh
    =\Psi(0)-\Psi(w)=1-\Psi(w).
\]

Substitution into (2.3) proves (2.2). ∎

### Lemma 2.2 (record-index martingale, with the repository clamping)

Use the clamped one-step exponent from `Ripple/CTMC/ExpMartingale.lean`. For real `t,u`, state `x`, and next record `r=(h,y)`, set `a_t(u,x;r)=Q.expStepExponent g t u x r`, namely `a_t(u,x;r) = (if max u 0 + h ≤ t then g(max u 0 + h,x,y) else 0) - ∫_min(max u 0,t)^min(max u 0 + max h 0,t) c(s,x) ds`. For a record trajectory `ω`, let `T_k=QMatrix.recTime ω k`, let `A_n(t,ω)=Σ_{k<n} a_t(T_k,Y_k;R_{k+1})`, and let `Z_n(t,ω)=exp(A_n(t,ω))`.

For every real `t`, every `n`, and every bounded `𝓕_n`-measurable complex random variable `ξ`, one has `E[ξ Z_{n+1}(t)] = E[ξ Z_n(t)]`. Consequently `(Z_n(t))_n` is an integrable `𝓕_n`-martingale and `E Z_n(t)=1` for every `n`.

#### Proof

Lemma L7 gives measurability and fixed-index integrability. The deterministic identity `A_{n+1}(t)=A_n(t)+a_t(T_n,Y_n;R_{n+1})` gives `Z_{n+1}(t)=Z_n(t) exp(a_t(T_n,Y_n;R_{n+1}))`.

Let `H_n=Preorder.frestrictLe n` be the history map. The theorem `QMatrix.canonicalRecordMeasure_history_next` says that the law of `(H_n,R_{n+1})` is the history marginal composed with `Q.jumpHoldTrajectoryStepKernel n`. For a history `h`, its current state is `x(h)=QMatrix.currentStateFromHistory n h`, and `Q.jumpHoldTrajectoryStepKernel n h = Q.jumpHoldStepKernel x(h)`. The current clock `T_n(h)` is a measurable function of that finite history.

Apply the history/next-record formula to the measurable integrable function `(h,r) ↦ ξ(h) Z_n(t,h) exp(Q.expStepExponent g t T_n(h) x(h) r)`. This gives `E[ξ Z_{n+1}(t)] = E[ξ Z_n(t) ∫ exp(Q.expStepExponent g t T_n x(H_n) r) d(Q.jumpHoldStepKernel x(H_n))(r)]`. The repository theorem `QMatrix.integral_cexp_expStepExponent` applies pointwise for every real `t`, every real `u`, and every state `x`; therefore the inner integral is exactly `1` for every history, including histories with negative ambient record coordinates. Hence `E[ξ Z_{n+1}(t)] = E[ξ Z_n(t)]` with no almost-everywhere restriction on `T_n`. Taking `ξ=1` and using `Z_0(t)=1` gives `E Z_n(t)=1` by induction. ∎

### Lemma 2.3 (Ville maximal inequality)

Assume that `g` is real-valued. Then `Z_n(t)>0`, and for every `a>0`,

\[
  \Pr\{\exists n,\ Z_n(t)\ge a\}\le a^{-1}.             \tag{2.5}
\]

#### Proof

For a fixed terminal index `N`, let

\[
 B_k=\{Z_k(t)\ge a\}\cap\bigcap_{j<k}\{Z_j(t)<a\},
 \qquad 0\le k\le N.
\]

The sets are disjoint and `B_k∈𝓕_k`. Iterating (2.4) from `k` to `N` with `ξ=1_{B_k}` yields

\[
  \mathbb E[1_{B_k}Z_N(t)]=\mathbb E[1_{B_k}Z_k(t)]
     \ge a\Pr(B_k).
\]

Summing over `k≤N` and using positivity gives

\[
  a\Pr\{\max_{k\le N}Z_k(t)\ge a\}
    \le \mathbb E Z_N(t)=1.
\]

The events increase with `N`; continuity from below gives (2.5). If a later application produces
only `sup_n Z_n≥a`, rather than an attained crossing, apply (2.5) to every `a'<a` and let `a'↑a`.
∎

### Lemma 2.4 (jump count and a common non-explosion event)

Let `Λ≥sup_x λ(x)`, and let

\[
  J_n(t)=\#\{1\le k\le n:T_k\le t,\ Y_k\ne Y_{k-1}\}.
\]

Then

\[
  \Pr\{J_n(t)\ge n\}
      \le \exp\bigl(-n+(e-1)\Lambda t\bigr).             \tag{2.6}
\]

For every finite horizon `T`, there is one probability-one event `Ω_T` on which all holding times
are nonnegative, every nonabsorbing holding time is strictly positive, every nonabsorbing step
changes state, absorbing records remain fixed, and only finitely many genuine jumps occur before
`T`.

#### Proof

Use the real tilt `g(s,x,y)=1_{y≠x}`. Its compensator is `(e-1)λ(x)`, so

\[
 A_n(t)=J_n(t)-(e-1)\sum_{k<n}
       \int_{T_k\wedge t}^{T_{k+1}\wedge t}\lambda(Y_k)\,ds.
\]

The second term is at most `(e-1)Λt`. Since `E e^{A_n(t)}=1`,

\[
  \mathbb E e^{J_n(t)}\le e^{(e-1)\Lambda t},
\]

and Markov's inequality gives (2.6).

For the almost-sure statement, intersect the countably many probability-one events asserting, for
each record index, nonnegativity of the holding time; strict positivity and a changed next state
when the current state is nonabsorbing; and the fixed terminal record when the current state is
absorbing. Call this intersection `Ω_rec`.

On `Ω_rec`, set

\[
 E_n=\{T_n\le T\text{ and no state }Y_0,\ldots,Y_{n-1}
                         \text{ is absorbing}\}.
\]

The events `E_n` decrease. On `E_n` every one of the first `n` steps is a genuine jump, hence
`J_n(T)=n`. Therefore (2.6) gives

\[
 \Pr(E_n)\le e^{-n+(e-1)\Lambda T}\longrightarrow0.
\]

Continuity from above yields `P(∩_nE_n)=0`. On `Ω_rec\(∩_nE_n)`, either absorption occurs, or some
`T_n>T`; in either case only finitely many genuine jumps occur before `T`. This is the required
`Ω_T`. ∎

### Corollary 2.5 (total measurable limiting exponent and exponential identity)

Fix `0≤t≤T`. Every `A_r(t)` is a measurable complex random variable. Define the measurable convergence set `C_t` by declaring that `ω∈C_t` exactly when `(A_r(t,ω))_r` is Cauchy. Explicitly, `C_t = ⋂_{q≥1} ⋃_{R≥0} ⋂_{r,s≥R} {ω : ‖A_r(t,ω)-A_s(t,ω)‖ < 1/q}`. This is measurable because it is obtained from countably many measurable inverse images.

Define a total function `A(t,ω)` on the whole record space by `A(t,ω)=lim_r A_r(t,ω)` when `ω∈C_t`, and `A(t,ω)=0` otherwise. This function is measurable. Indeed, for each `r` put `B_r(ω)=1_{C_t}(ω) A_r(t,ω)`. Every `B_r` is measurable; on `C_t` the sequence `B_r` converges to the chosen limit, and off `C_t` it is identically zero. Thus `B_r→A(t)` pointwise, and a pointwise limit of measurable maps into `ℂ` is measurable.

On the probability-one event `Ω_T` of Lemma 2.4, either some jump time exceeds `T` or the record sequence reaches an absorbing state and thereafter stays at the terminal record. In either case `A_r(t)` is eventually constant. Therefore `Ω_T⊆C_t`, and the total function `A(t)` agrees on `Ω_T` with the eventual value used in the pathwise formulas.

Assume that there is a finite deterministic constant `K_t` such that `sup_r |Z_r(t)|≤K_t` almost surely. Since `A_r(t)→A(t)` almost surely and the complex exponential is continuous, `Z_r(t)=exp(A_r(t))→exp(A(t))` almost surely. The assumed bound is an integrable deterministic dominator, so bounded convergence gives `E exp(A(t)) = lim_r E Z_r(t)=1`.

For a purely imaginary tilt, the jump contribution has zero real part and `-Re c(s,x)=Σ_{y≠x}q(x,y)(1-cos(Im g(s,x,y)))≤2λ(x)≤2Λ`. Hence `|Z_r(t)|≤exp(2Λt)` on the common canonical-record event, uniformly in `r`, so one may take `K_t=exp(2Λt)`. ∎

### Lemma 2.6 (pathwise reading on one horizon event)

On `Ω_T`, simultaneously for every `0≤t≤T`, the right-continuous frozen readout `X` satisfies

On `Ω_T`, the sum is taken only over genuine jumps and is finite: `A(t)=Σ_{k≥1 : T_k≤t and Y_k≠Y_{k-1}} g(T_k,Y_{k-1},Y_k) - ∫_0^t c(s,X(s)) ds`. Equivalently, the summand may be written as `g(T_k,X(T_k-),X(T_k))`. A jump exactly at `t` is included. After absorption the later records have `Y_k=Y_{k-1}`, so they contribute no terms even though their clock values may equal the absorption time.

Here `X(T_k-)=Y_{k-1}` and `X(T_k)=Y_k`; a jump exactly at `t` is included. If
`g(s,x,y)=θ·(φ(y)-φ(x))` is independent of time, then

\[
 A(t)=θ\cdot(\phi(X(t))-\phi(X(0)))
       -\int_0^t c(X(s))\,ds.                            \tag{2.10}
\]

Moreover,

\[
  A_n(T)=A(T_n\wedge T).                                 \tag{2.11}
\]

For a time-independent tilt, on a holding interval
`[T_n,T_{n+1})∩[0,T]`, `t↦A(t)` is affine. Its value at `T_n` is `A_n(T)`. If
`T_{n+1}≤T`, its left limit at `T_{n+1}` is

\[
 A_{n+1}(T)-g(T_{n+1},Y_n,Y_{n+1});
\]

if `T_n<T<T_{n+1}`, its value at `T` is `A_{n+1}(T)`.

#### Proof

On `Ω_T` there are finitely many genuine jumps before `T`, so the genuine-jump sum in (2.9) is an ordinary finite sum for every `t≤T` and the
state is constant on the finitely many intervening half-open intervals. Expanding the step
exponents and joining adjacent integrals gives (2.9) for every `t` at once; no uncountable
intersection of fixed-time events is used. Formula (2.10) follows by finite telescoping of the jump
increments. Formula (2.11) follows directly from the clamped definition: the first `n` steps fill
exactly the interval from `0` to `T_n∧T`. The affine statements result by integrating the constant
compensator rate on a holding interval and accounting for the jump increment at its right endpoint.
∎

## 3. Law of large numbers with exponential tail

Let `Γ : RateSpec d`, let `F=Γ.drift`, and for every positive population size `N` let
`M_N=DensityDepCTMC.mk N hN Γ`. We assume:

* the listed jumps are conservative, so the canonical population chain remains in its population
  simplex;
* `M_N.BoundaryCompatibleOnSimplex`, so every lattice-invalid jump has zero rate at a simplex
  state;
* the mean-field solution `x` satisfies `‖x(t)‖≤1` for `t≥0`.

If `d=0`, no state can have total population `N>0`, so every theorem quantified over simplex initial
states is vacuous. We henceforth work under `[NeZero d]`.

Choose the constants

\[
\begin{aligned}
 J&=\max(\Gamma.\mathrm{jumpNormBound},1),\\
 B&>0\quad\text{with }|\beta_\ell(z)|\le B
       \text{ for }\ell\in\Gamma.\mathrm{jumps},\ \|z\|\le1,\\
 \Lambda&=|\Gamma.\mathrm{jumps}|B+1,\\
 L&\ge0\quad\text{with }\|F(z)-F(z')\|\le L\|z-z'\|
       \text{ on the closed unit ball},\\
 K&=2e^{LT}.
\end{aligned}
\]

Thus `J≥1`, `Λ≥1`, every listed jump has sup norm at most `J`, and every lattice state in the cube
has exit rate at most `NΛ`. Fix `T>0`. Write

\[
 \bar X_N(t)=N^{-1}X_N(t),\qquad
 M_N(t)=\bar X_N(t)-\bar X_N(0)-\int_0^tF(\bar X_N(s))\,ds.
\]

For each `N` and simplex initial state, intersect the event `Ω_T` of Lemma 2.4 with the canonical
simplex-invariance event and the event on which absorbing records stay fixed. On this one
probability-one event, for every time in `[0,T]`:

1. `X_N(t)` is a simplex state and all rates used below are nonnegative;
2. `λ(X_N(t))≤NΛ`;
3. boundary compatibility gives
   \[
     \sum_yq_N(z,y)(y-z)=NF(z/N);
   \]
4. the clamped and unclamped exponential functionals agree;
5. only finitely many genuine jumps occur before `T`.

### Theorem 3.1 (martingale tail)

For `N≥1`, every simplex initial state, and every
`0<δ≤2TΛJ`,

\[
 \Pr\!\left\{\sup_{0\le t\le T}\|M_N(t)\|\ge\delta\right\}
 \le 2d\,e\,
       \exp\!\left(-\frac{N\delta^2}{4T\Lambda J^2}\right). \tag{3.1}
\]

#### Proof

Fix a coordinate `i` and a sign `σ∈{−1,1}`. Set

\[
  \theta=\frac{\delta}{2T\Lambda J^2}.
\]

The hypothesis on `δ` gives `θJ≤1`. Apply Section 2 with the real, time-independent tilt

\[
  g(s,z,y)=\sigma\theta(y_i-z_i).
\]

For `r∈ℝ`, put `p(r)=e^r-1-r`. Since `p(r)≥0` and `p(r)≤r²` for `|r|≤1`, the compensator splits as

\[
 c(z)=\sigma\theta NF_i(z/N)+\kappa(z),
\]

where

\[
 0\le\kappa(z)
   =\sum_yq_N(z,y)p\bigl(\sigma\theta(y_i-z_i)\bigr)
   \le N\Lambda\theta^2J^2.                              \tag{3.2}
\]

Lemma 2.6 and the martingale decomposition give, on the common event,

\[
 A(t)=\sigma\theta N M_{N,i}(t)-\int_0^t\kappa(X_N(s))\,ds. \tag{3.3}
\]

The map `M_{N,i}` is right-continuous: the frozen state is right-continuous and the compensator
integral is continuous. Consequently

\[
 \sup_{0\le t\le T}\sigma M_{N,i}(t)
 =\sup\{\sigma M_{N,i}(q):q\in\mathbb Q\cap[0,T)\}\vee
   \sigma M_{N,i}(T).
\]

Indeed, for `t<T` choose rational `q_r↓t` and use right continuity. This identity proves
measurability of the continuous-time supremum; explicitly, its `≥δ` event is

\[
 \bigcap_{r\ge1}\ \bigcup_{q\in(\mathbb Q\cap[0,T))\cup\{T\}}
       \{\sigma M_{N,i}(q)>\delta-r^{-1}\}.
\]

On each holding interval, `A` is real affine. At a jump endpoint, its left limit differs from the
post-jump record value by at most `θJ`. Lemma 2.6 therefore gives

\[
  \sup_{0\le t\le T}A(t)
       \le \sup_n A_n(T)+\theta J.                       \tag{3.4}
\]

On the event `sup_t σM_{N,i}(t)≥δ`, equations (3.2)–(3.3) imply

\[
 \sup_{t\le T}A(t)
    \ge \theta N\delta-TN\Lambda\theta^2J^2.
\]

Combining this with (3.4), and using the `a'<a` limiting form of Lemma 2.3 when the supremum is not
attained, yields

\[
\begin{aligned}
 \Pr\{\sup_t\sigma M_{N,i}(t)\ge\delta\}
 &\le e^{\theta J}
      \exp\bigl(-N(\theta\delta-T\Lambda\theta^2J^2)\bigr)\\
 &\le e\exp\!\left(-\frac{N\delta^2}{4T\Lambda J^2}\right).
\end{aligned}
\]

The passage from the unclamped path calculation to the record-index event is valid on the
probability-one holding-time event; adding or deleting its null complement does not change the
probability. In the repository sup norm, `‖v‖≥δ` implies `v_i≥δ` or `−v_i≥δ` for some coordinate
`i`. A union bound over `d` coordinates and two signs proves (3.1). ∎

### Lemma L8 (explicit pathwise Gronwall bound and event inclusion)

On every path on which the martingale decomposition holds for all `t∈[0,T]`, put

\[
  Y(t)=\bar X_N(t)-x(t),\qquad
  M^*=\sup_{0\le s\le T}\|M_N(s)\|.
\]

Then

\[
  \sup_{0\le t\le T}\|Y(t)\|
  \le e^{LT}\bigl(\|Y(0)\|+M^*\bigr).                  \tag{3.5}
\]

Consequently, with `K=2e^{LT}`, for every `ε>0`,

\[
 \left\{\sup_{t\le T}\|Y(t)\|\ge\varepsilon\right\}
 \subseteq
 \{\|Y(0)\|\ge\varepsilon/K\}
 \cup\{M^*\ge\varepsilon/K\}.                          \tag{3.6}
\]

#### Proof

Subtract the ODE integral equation from the martingale decomposition. Since both paths remain in
the closed unit ball,

\[
 \|Y(t)\|
 \le \|Y(0)\|+M^*+L\int_0^t\|Y(s)\|\,ds.              \tag{3.7}
\]

Let `a=‖Y(0)‖+M*`, `u(t)=‖Y(t)‖`, and

\[
 v(t)=a+L\int_0^t u(s)\,ds.
\]

The bounded right-continuous function `u` is measurable and integrable. Hence `v` is absolutely
continuous, `u≤v`, and `v'(t)=Lu(t)≤Lv(t)` almost everywhere. The function
`w(t)=e^{-Lt}v(t)` is absolutely continuous and

\[
 w'(t)=e^{-Lt}(v'(t)-Lv(t))\le0
\]

almost everywhere. Therefore

\[
 w(t)-w(0)=\int_0^t w'(s)\,ds\le0,
\]

so `u(t)≤v(t)≤ae^{Lt}`. Taking the supremum proves (3.5).

If both alternatives on the right of (3.6) fail, then

\[
 \|Y(0)\|+M^*<2\varepsilon/K=\varepsilon e^{-LT},
\]

and (3.5) gives `sup_t‖Y(t)‖<ε`. This proves (3.6) by contraposition. ∎

### Theorem 3.3 (LLN with exponential tail)

There are constants `K≥1`, `c>0`, and `ε₀>0`, depending only on `Γ` and `T`, such that for every
`N≥1`, every simplex initial state `x₀`, and every `0<ε≤ε₀` satisfying

\[
  \|x_0/N-x(0)\|<\varepsilon/K,
\]

one has

\[
 \Pr_{x_0}\!\left\{
   \sup_{0\le t\le T}\|\bar X_N(t)-x(t)\|>\varepsilon
 \right\}
 \le2d\,e\,e^{-cN\varepsilon^2}.                       \tag{3.8}
\]

The constants are exactly

\[
  K=2e^{LT},\qquad
  \varepsilon_0=2T\Lambda JK,\qquad
  c=\frac1{4T\Lambda J^2K^2}.                           \tag{3.9}
\]

#### Proof

All three constants have the asserted signs. The strict initial inequality removes the first event
in (3.6), so the event in (3.8) is contained, modulo the common null set, in

\[
 \{M^*>\varepsilon/K\}\subseteq\{M^*\ge\varepsilon/K\}.
\]

The bound `ε≤ε₀` is precisely
`ε/K≤2TΛJ`, so Theorem 3.1 applies with `δ=ε/K`. Substitution gives (3.8) and the value of `c` in
(3.9). ∎

### Corollary 3.4 (the `√(log N/N)` high-probability scale)

For every `p>0`, let `C=√(p/c)`. For all sufficiently large `N`, if

\[
 \|x_0/N-x(0)\|<\frac{C}{K}\sqrt{\frac{\log N}{N}},
\]

then

\[
 \Pr\!\left\{\sup_{t\le T}\|\bar X_N(t)-x(t)\|>
        C\sqrt{\frac{\log N}{N}}\right\}
 \le2d\,e\,N^{-p}.                                      \tag{3.10}
\]

#### Proof

The quantity `C√(log N/N)` tends to zero, so it is at most `ε₀` for all sufficiently large `N`.
Apply Theorem 3.3 and use

\[
 cN C^2\frac{\log N}{N}=p\log N.
\]

This is a high-probability bound at the same scale as a consequence of the 1978 strong
approximation. It is not a KMT coupling and does not assert an
`O(log N/N)` coupling error after subtracting Brownian noise. ∎

## 4. Central limit theorem for finite-dimensional distributions

Assume in addition that

\[
  F=\Gamma.\mathrm{drift}\quad\text{satisfies}\quad
  \mathrm{ContDiff}\;\mathbb R\;1\;F.
\]

The individual rates retain the `RateSpec.rate_lipschitz` hypothesis; differentiability is imposed
on the drift, not on each rate.

Let `m,d : ℕ`, let

\[
  t:\operatorname{Fin}m\to\mathbb R,
  \qquad 0\le t_j\quad(j:\operatorname{Fin}m),
\]

and define

\[
 t_* = \max\bigl(\{0\}\cup\{t_j:j:\operatorname{Fin}m\}\bigr),
 \qquad T=\max(1,t_*).                                   \tag{4.1}
\]

Thus the inner finite maximum has default value `0`; (4.1) covers `m=0` and the case in which every
observation time is zero, and always gives `T≥1`.

Index the populations by

\[
  N_n=n+1.
\]

For each `n`, let `x_n : Fin d → Fin (N_n+1)` be a deterministic simplex state and write
`z_n=x_n/N_n`. Assume

\[
  \sqrt{N_n}\,(z_n-x(0))\longrightarrow v_0
       \quad\text{in }\operatorname{Fin}d\to\mathbb R.  \tag{4.2}
\]

As in Section 3, the `d=0` case has no positive-population simplex initial state and is vacuous; the
nonvacuous theorem uses `[NeZero d]`.

### Lemma 4.0 (the ODE path stays in the closed simplex)

Let

\[
 \Delta=\left\{z:\operatorname{Fin}d\to\mathbb R:
       (\forall i,\ 0\le z_i)\ \text{and}\ \sum_i z_i=1\right\}.
\]

Then `x(s)∈Δ` for every `s≥0`.

#### Proof

The set `Δ` is closed: every coordinate half-space is closed, and the coordinate-sum map is
continuous. From (4.2), the sequence `√N_n(z_n-x(0))` is bounded eventually; division by `√N_n→∞`
gives `z_n→x(0)`. Since every `z_n∈Δ`, closedness gives `x(0)∈Δ`.

Fix `s≥0` and use the positive horizon `T_s=max(1,s)`. The Section 3 law of large numbers applies to
the deterministic initial sequence because `z_n→x(0)`. The canonical density process lies in `Δ`
at every time almost surely by conservative-jump simplex invariance. If `x(s)∉Δ`, closedness gives
an `r>0` such that the open sup-norm ball of radius `r` around `x(s)` is disjoint from `Δ`. Hence

\[
  \|\bar X_{N_n}(s)-x(s)\|\ge r
\]

with probability one for every `n`, while the LLN says the probability of this event tends to zero.
This contradiction proves `x(s)∈Δ`. In particular every
`β_ℓ(x(s))` with `ℓ∈Γ.jumps` is nonnegative. ∎

### 4.1. Coordinate linearization, adjoints, and their bounded extensions

Let `E=Fin d→ℝ` with the repository sup norm. For `j:Fin d`, let `e_j` be the coordinate vector.
Define the coordinate matrix of the Fréchet derivative by

\[
  A(s)_{ij}=\bigl(DF(x(s))e_j\bigr)_i.                  \tag{4.3}
\]

Linearity and the identity `v=Σ_jv_je_j` give

\[
  (DF(x(s))v)_i=\sum_jA(s)_{ij}v_j.                     \tag{4.4}
\]

Define the transpose action coordinatewise by

\[
  (A(s)^\mathsf T u)_j=\sum_iA(s)_{ij}u_i.              \tag{4.5}
\]

Equations (4.4)–(4.5) imply the exact duality identity

\[
  (A(s)^\mathsf T u)\cdot v=u\cdot DF(x(s))v.           \tag{4.6}
\]

This avoids using `ContinuousLinearMap.adjoint` on the sup-norm representation. Continuity of
`DF`, continuity of `x`, and finite-dimensional coordinate evaluation make `s↦A(s)` continuous.

### Lemma 4.1 (backward adjoint, forward fundamental matrix, and transpose bridge)

For every `τ≥0` and `a∈E`, there is a unique continuously differentiable map `ψ:[0,τ]→E` satisfying `ψ(τ)=a` and `ψ'(s)=-A(s)^Tψ(s)`. For every `0≤s≤r≤T`, there is a continuous linear map `Φ(r,s):E→E` such that `Φ(s,s)=I`, the map `r↦Φ(r,s)` is continuously differentiable in the finite-dimensional operator space, and `∂_r Φ(r,s)=A(r)Φ(r,s)`. If `ψ_{τ,i}` is the backward solution with terminal value `e_i`, then for `0≤s≤τ` and `ℓ∈E` one has `(Φ(τ,s)ℓ)_i = ψ_{τ,i}(s)·ℓ`; equivalently `ψ_{τ,i}(s)=Φ(τ,s)^T e_i` coordinatewise.

#### Proof: backward equation

Continuity of `A^T` on `[0,τ]` gives `β≥0` with `‖A(r)^T‖≤β`. Define `u_0(s)=a` and `u_{q+1}(s)=∫_s^τ A(r)^T u_q(r) dr`. Induction gives `‖u_q(s)‖≤‖a‖ β^q(τ-s)^q/q!`. The numerical majorant sums to `‖a‖ exp(βτ)`, so `ψ(s)=Σ_{q≥0}u_q(s)` converges absolutely and uniformly on `[0,τ]`.

Let `S_N=Σ_{q<N}u_q`. Uniform convergence and the operator bound give `sup_{s∈[0,τ]} ‖∫_s^τ A(r)^T(S_N(r)-ψ(r)) dr‖ ≤ τβ sup_{r∈[0,τ]}‖S_N(r)-ψ(r)‖→0`. Hence the series may be passed through the integral, and `ψ(s)=a+∫_s^τ A(r)^Tψ(r) dr`. The integrand is continuous, so the fundamental theorem gives `ψ'(s)=-A(s)^Tψ(s)` and `ψ(τ)=a`, with the usual one-sided derivatives at the endpoints.

For uniqueness, if `w` is the difference of two solutions and `M=sup_{[0,τ]}‖w‖`, repeated substitution in `w(s)=∫_s^τ A(r)^T w(r) dr` gives `‖w(s)‖≤M β^q(τ-s)^q/q!` for every `q`. The right side tends to zero, so `w=0`.

#### Proof: forward fundamental matrix

Fix `s∈[0,T]` and `ℓ∈E`. For `r∈[s,T]`, define forward Picard terms by `v_0^{s,ℓ}(r)=ℓ` and `v_{q+1}^{s,ℓ}(r)=∫_s^r A(u)v_q^{s,ℓ}(u) du`. Choose `β_s≥0` with `‖A(u)‖≤β_s` on `[s,T]`. The same induction gives `‖v_q^{s,ℓ}(r)‖≤‖ℓ‖ β_s^q(r-s)^q/q!`, uniformly for `r∈[s,T]`. Thus `z_{s,ℓ}(r)=Σ_{q≥0}v_q^{s,ℓ}(r)` converges absolutely and uniformly.

If `V_N=Σ_{q<N}v_q^{s,ℓ}`, then `sup_{r∈[s,T]} ‖∫_s^r A(u)(V_N(u)-z_{s,ℓ}(u)) du‖ ≤ (T-s)β_s sup_{u∈[s,T]}‖V_N(u)-z_{s,ℓ}(u)‖→0`. Therefore `z_{s,ℓ}(r)=ℓ+∫_s^r A(u)z_{s,ℓ}(u) du`. The integrand is continuous, so `z_{s,ℓ}` is continuously differentiable, `z_{s,ℓ}(s)=ℓ`, and `z'_{s,ℓ}(r)=A(r)z_{s,ℓ}(r)`.

Every Picard term is linear in `ℓ`; uniform convergence preserves addition and scalar multiplication. Hence `ℓ↦z_{s,ℓ}(r)` is linear. The bound `‖z_{s,ℓ}(r)‖≤exp(β_s(r-s))‖ℓ‖` makes it continuous. Define `Φ(r,s)ℓ=z_{s,ℓ}(r)`. Then `Φ(s,s)=I`. For each basis vector `e_j`, the column `r↦Φ(r,s)e_j` is continuously differentiable and has derivative `A(r)Φ(r,s)e_j`. Since there are finitely many columns, `r↦Φ(r,s)` is continuously differentiable as a matrix, and its derivative is the matrix product `A(r)Φ(r,s)`. Uniqueness of the forward equation follows by the same factorial iteration used for the backward equation.

#### Proof: transpose bridge

Fix `0≤s≤τ`, `i:Fin d`, and `ℓ∈E`, and put `z(r)=Φ(r,s)ℓ` for `r∈[s,τ]`. The coordinate duality identity `(A(r)^T u)·v = u·A(r)v` gives `d/dr [ψ_{τ,i}(r)·z(r)] = (-A(r)^Tψ_{τ,i}(r))·z(r) + ψ_{τ,i}(r)·A(r)z(r)=0`. Thus the scalar product is constant. At `r=τ` it equals `e_i·Φ(τ,s)ℓ=(Φ(τ,s)ℓ)_i`; at `r=s` it equals `ψ_{τ,i}(s)·ℓ` because `Φ(s,s)ℓ=ℓ`. This proves the bridge and the coordinate transpose formula. ∎


For `j:Fin m` and `i:Fin d`, write `ψ_{j,i}` for Lemma 4.1 with `τ=t_j` and terminal value `e_i`.
For coefficients `a=(a_{j,i})`, define

\[
  \alpha_j=(a_{j,i})_i,
  \qquad
  \psi_j(s)=\sum_i a_{j,i}\psi_{j,i}(s),\quad 0\le s\le t_j.
\]

Extend this compact-interval solution to all real times by

\[
 \widehat\psi_j(s)=
 \begin{cases}
   \psi_j(0),&s<0,\\
   \psi_j(s),&0\le s\le t_j,\\
   0,&s>t_j,
 \end{cases}
 \qquad
 \widetilde\psi(s)=\sum_j\widehat\psi_j(s).              \tag{4.12}
\]

Each extension `ψ̂_j` is bounded, is continuous at `0` when `t_j>0`, and is continuous away from its cutoff time `t_j`. Therefore a finite exceptional set for Section 2 may be taken to be `D={t_j : j∈Fin m}`. This set need not be the exact discontinuity set, because a zero terminal coefficient or cancellation can make the extension continuous at a listed time. No additional exceptional point at `0` is needed: the extension is constant with value `ψ_j(0)` below `0`, and when `t_j=0`, the point `0` is already a member of `D`.

with no additional zero unless zero is itself one of the `t_j`.

For every fixed positive `N`, the tilt

\[
 g_N(s,z,y)=\frac{i}{\sqrt N}\,
               \widetilde\psi(s)\cdot(y-z)               \tag{4.14}
\]

satisfies all Section 2 hypotheses on the finite lattice state space: it is diagonal-zero,
measurable, continuous off (4.13), and globally bounded in `s,z,y`. This is the bounded-tilt
hypothesis used in the CLT; no adjoint solution on `(-∞,t_j]` is asserted.

### 4.2. The literal Mathlib target

Let

\[
  \iota=\operatorname{Fin}m\times\operatorname{Fin}d,
  \qquad
  E_{m,d}=\operatorname{EuclideanSpace}\ \mathbb R\ \iota
          =\operatorname{WithLp}\ 2\ (\iota\to\mathbb R).
\]

For a canonical path `ω` at population `N_n`, define the raw coordinate function

\[
 v_n(\omega)(j,i)=\sqrt{N_n}\,
   \bigl(\bar X_{N_n}(t_j,\omega)_i-x(t_j)_i\bigr)
\]

and the Euclidean random vector

\[
  V_n(\omega)=\operatorname{WithLp.toLp}\ 2\bigl(v_n(\omega)\bigr)
       \in E_{m,d}.                                      \tag{4.15}
\]

The frozen state at a deterministic time is measurable; finite coordinate assembly and
`WithLp.toLp 2` are measurable. Hence the mapped canonical law can be packaged as

\[
 \mathcal L_n:
   \operatorname{ProbabilityMeasure}(E_{m,d}),
 \qquad
 (\mathcal L_n:\operatorname{Measure}E_{m,d})
   =(P_{x_n}).\operatorname{map}V_n.                     \tag{4.16}
\]

Define the mean coordinate function and then move it to Euclidean space:

\[
 \mu^{\rm raw}_{(j,i)}=\psi_{j,i}(0)\cdot v_0,
 \qquad
 \mu=\operatorname{WithLp.toLp}\ 2\mu^{\rm raw}.        \tag{4.17}
\]

Define `S : Matrix ι ι ℝ` by

\[
 S_{(j,i),(k,r)}=
  \int_0^{\min(t_j,t_k)}
    \sum_{\ell\in\Gamma.\mathrm{jumps}}
       \beta_\ell(x(s))
       (\psi_{j,i}(s)\cdot\ell)
       (\psi_{k,r}(s)\cdot\ell)\,ds.                    \tag{4.18}
\]

The theorem will prove `hS : S.PosSemidef` before invoking the Gaussian characteristic-function
formula. The target is the Mathlib convergence statement

```text
Tendsto (fun n => ℒ_n) atTop
  (𝓝 (⟨ProbabilityTheory.multivariateGaussian μ S, inferInstance⟩ :
      ProbabilityMeasure (EuclideanSpace ℝ (Fin m × Fin d))))
```

where the target measure is packaged with its probability-measure instance. When `m=0`, the index
type is empty, the Euclidean space has one point, all characteristic functions equal one, and the
same statement specializes to convergence to the point mass; the positive auxiliary horizon in
(4.1) avoids any zero-horizon side condition.

### Lemma L1 (uniformly bounded convergence in probability implies `L¹` convergence on dependent probability spaces)

For every `n`, let `Ω_n` be a sample type with a measurable space, let `P_n` be a probability measure on `Ω_n`, and let `Z_n:Ω_n→ℝ` be measurable. Assume that one deterministic `M≥0` satisfies `0≤Z_n≤M` `P_n`-almost surely for every `n`, and assume convergence to zero in probability in the literal dependent sense: for every `η>0`, `P_n{ω : Z_n(ω)>η}→0`. Then `∫ Z_n dP_n→0`.

#### Proof

For every `η>0`, split the integral over `{Z_n≤η}` and `{Z_n>η}`. The first part is at most `η`; the second is at most `M P_n{Z_n>η}`. Hence `∫ Z_n dP_n ≤ η + M P_n{Z_n>η}`. If `M=0`, the conclusion is immediate. Otherwise, given `ε>0`, take `η=ε/2`, then choose `n` so large that `P_n{Z_n>η}<ε/(2M)`. The displayed bound gives `∫ Z_n dP_n<ε`. ∎

### Lemma L2 (tight times `o_P(1)` is `o_P(1)` on dependent probability spaces)

For every `n`, let `Ω_n` be a sample type with measurable space, let `P_n` be a probability measure on `Ω_n`, and let `U_n,V_n:Ω_n→[0,∞)` be measurable. Assume that `(U_n)` is tight in the dependent sense: for every `ε>0` there is `R>0` such that `P_n{U_n>R}<ε` for every `n` after enlarging `R` to absorb any finite initial segment. Assume also that `V_n→0` in probability: for every `η>0`, `P_n{V_n>η}→0`. Then `U_nV_n→0` in probability.

More generally, let `J` be a fixed finite index type and let `W_{n,j}:Ω_n→ℝ` be measurable for `j∈J`. If `W_{n,j}→0` in probability for every `j`, then `Σ_{j∈J}W_{n,j}→0` in probability.

#### Proof

Fix `δ,ε>0`. Tightness gives `R>0` with `P_n{U_n>R}<ε/2`. For large `n`, convergence of `V_n` gives `P_n{V_n>δ/R}<ε/2`. Since `{U_nV_n>δ}⊆{U_n>R}∪{V_n>δ/R}`, the product probability is below `ε`.

For the finite sum, if `J` is empty the sum is zero. Otherwise, if `|J|=m>0`, then `{|Σ_jW_{n,j}|>δ}⊆⋃_j{|W_{n,j}|>δ/m}`. The finite union bound and coordinatewise convergence in probability give the claim. ∎

### Lemma L3 (uniform derivative modulus and the integral Taylor remainder)

Let `K={z∈E:‖z‖≤1}`. There is a finite nondecreasing function
`ω:[0,∞)→[0,∞)` with `ω(r)→0` as `r↓0` such that, for `x,y∈K`,

\[
 \|F(y)-F(x)-DF(x)(y-x)\|
 \le \omega(\|y-x\|)\,\|y-x\|.                         \tag{4.20}
\]

#### Proof

The closed unit ball `K` is compact because `E` is finite-dimensional. The continuous derivative
map `DF` is uniformly continuous and bounded on `K`. Define

\[
 \omega(r)=\sup\{\|DF(z)-DF(x)\|:
      x,z\in K,\ \|z-x\|\le r\}.                        \tag{4.21}
\]

The set in (4.21) is compact and nonempty, so the supremum is finite and attained. It is
nondecreasing. Given `ε>0`, uniform continuity supplies `δ>0` such that
`x,z∈K` and `‖z-x‖<δ` imply `‖DF(z)-DF(x)‖<ε`. Hence
`0≤r<δ` implies `ω(r)≤ε`, proving `ω(r)→0`.

Let `h=y-x`. Convexity of `K` gives `x+uh∈K` for `0≤u≤1`. The curve
`u↦F(x+uh)` is continuously differentiable with derivative `DF(x+uh)h`; integrating its derivative
coordinatewise, or as a finite-dimensional Bochner integral, gives

\[
 F(y)-F(x)=\int_0^1DF(x+uh)h\,du.
\]

Subtract `DF(x)h` and use the norm bound for an integral:

\[
\begin{aligned}
 \|F(y)-F(x)-DF(x)h\|
 &\le\int_0^1\|DF(x+uh)-DF(x)\|\,\|h\|\,du\\
 &\le\omega(\|h\|)\|h\|.
\end{aligned}
\]

This proves (4.20). ∎

### Lemma L4 (explicit quadratic-compensator Lipschitz estimate)

Fix a Euclidean test vector `a` and the resulting function `ψ̃` from (4.12). For each listed jump,
put

\[
 p_\ell(s)=\widetilde\psi(s)\cdot\ell,
 \quad
 P_\ell=\sup_{0\le s\le T}|p_\ell(s)|,
\]

and choose `L_ℓ` so that

\[
 |\beta_\ell(z)-\beta_\ell(z')|\le L_\ell\|z-z'\|
 \quad(z,z'\in K).
\]

Define

\[
\begin{aligned}
 Q_n&=\int_0^T\sum_{\ell\in\Gamma.\mathrm{jumps}}
       \beta_\ell(\bar X_{N_n}(s))p_\ell(s)^2\,ds,\\
 Q&=\int_0^T\sum_{\ell\in\Gamma.\mathrm{jumps}}
       \beta_\ell(x(s))p_\ell(s)^2\,ds,\\
 C_a&=T\sum_{\ell\in\Gamma.\mathrm{jumps}}L_\ell P_\ell^2.
\end{aligned}
\]

On the common simplex event,

\[
 |Q_n-Q|
 \le C_a\sup_{0\le s\le T}
       \|\bar X_{N_n}(s)-x(s)\|.                         \tag{4.22}
\]

Consequently `Q_n→Q` in probability.

#### Proof

The jump set is finite and `ψ̃` is bounded, so every `P_ℓ` and `C_a` is finite. Pointwise in `s`,

\[
\begin{aligned}
 &\left|\sum_\ell
   (\beta_\ell(\bar X_{N_n}(s))-\beta_\ell(x(s)))p_\ell(s)^2\right|\\
 &\qquad\le\sum_\ell L_\ell P_\ell^2
       \|\bar X_{N_n}(s)-x(s)\|.
\end{aligned}
\]

Integrate over an interval of length `T` and bound the last norm by its time supremum. This gives
(4.22). The Section 3 LLN makes the right side converge to zero in probability. ∎

### Lemma L5 (nonlinear compensator rewrite over the listed jumps)

Let `N>0`, let `z` be a lattice simplex state, let `b∈E`, and let
`h:ℝ→ℂ` satisfy `h(0)=0`. Then

\[
\begin{aligned}
 &\sum_{y\ne z}q_N(z,y)
   h\!\left(\frac{b\cdot(y-z)}{\sqrt N}\right)\\
 &\qquad=N\sum_{\ell\in\Gamma.\mathrm{jumps}}
   \beta_\ell(z/N)
   h\!\left(\frac{b\cdot\ell}{\sqrt N}\right).          \tag{4.23}
\end{aligned}
\]

The corresponding linear identity is

\[
 \sum_{y\ne z}q_N(z,y)(y-z)=NF(z/N).                    \tag{4.24}
\]

#### Proof

For `y≠z`, expand the repository definition

\[
 q_N(z,y)=\sum_{\substack{\ell\in\Gamma.\mathrm{jumps}\\y-z=\ell}}
          N\beta_\ell(z/N).
\]

Finite-sum interchange turns the left side of (4.23) into a sum over listed `ℓ`, followed by a sum
over lattice targets satisfying `y-z=ℓ`.

If `ℓ≠0` and the jump is lattice-valid, there is exactly one such target, namely `y=z+ℓ`, and its
contribution is the displayed right-hand summand. If `ℓ≠0` is lattice-invalid, the inner target sum
is empty; boundary compatibility says `β_ℓ(z/N)=0`, so the corresponding right-hand summand is also
zero. If `ℓ=0`, the only possible target is `y=z`, which is excluded by the off-diagonal sum and by
`offDiagRate`'s diagonal convention; the right-hand contribution is
`Nβ_0(z/N)h(0)=0`. These three cases prove (4.23), including the zero-jump and invalid-jump cases.

For (4.24), perform the same expansion coordinatewise with the factor `(y-z)_i`; the zero jump
again contributes zero, and the resulting sum is exactly the definition of `Γ.drift`. ∎

### Lemma L6 (one probability-one event and a total measurable jump functional)

Fix a population index `n`, put `N=N_n`, and let `P_n` be the canonical record law started from `x_n`. For a deterministic `τ∈[0,T]` and a continuously differentiable `ψ:[0,τ]→E`, first extend `ψ` to a bounded Borel map `ψ^ext:ℝ→E`, for example by the constant value `ψ(0)` below `0` and the constant value `ψ(τ)` above `τ`. The values outside `[0,τ]` are used only to make the whole-space definition total.

For `k≥1`, define the scaled record increment `Δ_{n,k}(ω)` coordinatewise by `Δ_{n,k}(ω)_i = ((Y_k(ω)_i:ℝ)-(Y_{k-1}(ω)_i:ℝ))/N`. Define the measurable genuine-jump summand `b_{n,k}(ψ,τ,ω)=1_{T_k(ω)≤τ} 1_{Y_k(ω)≠Y_{k-1}(ω)} ψ^ext(T_k(ω))·Δ_{n,k}(ω)`. Each factor is measurable: `T_k` is a finite sum of record-coordinate projections, the states are measurable finite-valued coordinates, and the dot product is continuous.

Let `S_{n,r}(ψ,τ)=Σ_{1≤k≤r} b_{n,k}(ψ,τ)` be the measurable finite partial sum. Let `C_{n,ψ,τ}` be the measurable set on which `(S_{n,r}(ψ,τ))_r` is Cauchy, written explicitly as `⋂_{q≥1} ⋃_{R≥0} ⋂_{r,s≥R}{|S_{n,r}-S_{n,s}|<1/q}`. Define the total genuine-jump functional `J_n(ψ,τ)` to be `lim_r S_{n,r}(ψ,τ)` on `C_{n,ψ,τ}` and `0` off that set. It is measurable: the measurable functions `1_{C_{n,ψ,τ}}S_{n,r}` converge pointwise to `J_n(ψ,τ)`.

Define the total random variables `I_n(ψ,τ)=J_n(ψ,τ)-∫_{s∈Set.Icc 0 τ} ψ(s)·F(X̄_N(s)) ds` and `R_n(ψ,τ)=∫_{s∈Set.Icc 0 τ} ψ(s)·(F(X̄_N(s))-F(x(s))-DF(x(s))(X̄_N(s)-x(s))) ds`. The map `(s,ω)↦X̄_N(s,ω)` is jointly measurable by the repository measurability theorem for `frozenStateAt`; composition with the continuous maps `F`, `DF`, coordinate pairing, and multiplication by the deterministic `ψ` is jointly measurable. Parameter integration over the fixed measurable set `Set.Icc 0 τ` therefore makes both time-integral terms measurable. This convention matches the definition of `frozenMartingalePart`; interval endpoints have Lebesgue measure zero.

There is one event `Ω_n` of `P_n`-probability one on which all of the following hold simultaneously: every holding time is nonnegative; at every nonabsorbing record the holding time is positive and the next state changes; after an absorbing state the next record is `(0,current state)`; every record state and every frozen state lies in the population simplex; and the disjunction of `canonical_absorption_or_nonExplosive_ae` holds at horizon `T`, namely either some state in the sequence is absorbing or some repository jump time is strictly larger than `T`.

On `Ω_n`, only finitely many summands `b_{n,k}(ψ,τ)` are nonzero. If absorption occurs, all later state-change indicators vanish. If `T<path.times r`, then nonnegativity of the holding times makes all later clock times at least `path.times r`, so no later term can satisfy `T_k≤τ≤T`. Consequently the partial sums are eventually constant, `Ω_n⊆C_{n,ψ,τ}`, and `J_n(ψ,τ)` equals the ordinary finite sum over genuine jumps with `T_k≤τ`.

On the same event, finite-interval integration by parts gives, simultaneously for every `j∈Fin m`, `α_j·Y_n(t_j)=ψ_j(0)·Y_n(0)+I_n(ψ_j,t_j)+R_n(ψ_j,t_j)`. The proof is the deterministic telescoping argument from R1, now with the genuine-jump functional just defined: on each half-open sojourn interval, integrate `ψ'_j·X̄_N`; at each right endpoint add `ψ_j(T_k)·ΔX̄_N(T_k)` only when the state changes; subtract the ODE product rule; then use `ψ'_j·Y_n=-ψ_j·DF(x)Y_n`.

With the inclusive cutoff extension `ψ̂_j`, one also has almost surely `I_n(ψ̃,T)=Σ_j I_n(ψ_j,t_j)`. For a genuine jump at time `r`, `ψ̃(r)=Σ_{j:r≤t_j}ψ_j(r)`, including the terms with `r=t_j`; for the Lebesgue integral, changing finitely many endpoint values has no effect. Since the jump sum is finite on `Ω_n`, the finite interchange is legitimate.

It remains to prove integrability rather than infer it from almost-sure finiteness. Let `J_{n,T}^{(r)}=Σ_{1≤k≤r}1_{T_k≤T}1_{Y_k≠Y_{k-1}}`, and let `J_{n,T}=sup_r J_{n,T}^{(r)}`. These finite counts are measurable and increase in `r`. Let `Λ_n=sup_z λ_n(z)`; in the density-dependent model `Λ_n≤N_nΛ`. The exponential-moment calculation used in Lemma 2.4 gives `E exp(J_{n,T}^{(r)})≤exp((e-1)Λ_nT)` for every `r`. Monotone convergence gives `E exp(J_{n,T})≤exp((e-1)Λ_nT)`, so `J_{n,T}<∞` almost surely. Markov's inequality gives, for every integer `q≥1`, `P_n(J_{n,T}≥q)≤exp(-q+(e-1)Λ_nT)`. The tail-sum identity therefore yields `E J_{n,T}=Σ_{q≥1}P_n(J_{n,T}≥q)≤exp((e-1)Λ_nT)Σ_{q≥1}e^{-q}=exp((e-1)Λ_nT)/(e-1)≤exp((e-1)N_nΛT)/(e-1)<∞`.

Let `C_ψ=sup_{s∈[0,T]}‖ψ(s)‖∞`. Every scaled lattice coordinate lies in `[0,1]`, hence `‖Δ_{n,k}‖∞≤1`, and the coordinate-sum pairing satisfies `|ψ(T_k)·Δ_{n,k}|≤d C_ψ`. Thus `|J_n(ψ,τ)|≤d C_ψ J_{n,T}` almost surely, proving integrability of the jump functional. If `B_F=sup_{‖z‖≤1}‖F(z)‖∞`, then the compensator integral has absolute value at most `T d C_ψ B_F`, so `I_n(ψ,τ)` is integrable. Continuity of `F` and `DF` on the closed unit ball, boundedness of `Y_n`, and boundedness of `ψ` similarly give a deterministic bound for the remainder integral, so `R_n(ψ,τ)` is integrable. ∎

### 4.3. Mean, covariance, and positive semidefiniteness

The matrix in (4.18) is symmetric by swapping `(j,i)` with `(k,r)`. To prove the exact Mathlib
predicate, fix a real coordinate vector `a:ι→ℝ` and form `ψ_j` and `ψ̃` as above. Finite-sum
interchange and the cutoff identity turn the quadratic form into

For `s∈[0,T]`, the compact-interval solution `ψ_j(s)` is used only when `s≤t_j`; equivalently one uses its cutoff extension `ψ̂_j(s)`. The quadratic-form calculation is `a ⬝ᵥ S *ᵥ a = ∫_0^T Σ_{ℓ∈Γ.jumps} β_ℓ(x(s)) (Σ_{j:s≤t_j} ψ_j(s)·ℓ)^2 ds = ∫_0^T Σ_{ℓ∈Γ.jumps} β_ℓ(x(s)) (Σ_j ψ̂_j(s)·ℓ)^2 ds = ∫_0^T Σ_{ℓ∈Γ.jumps} β_ℓ(x(s))(ψ̃(s)·ℓ)^2 ds = Q(a)`. This is the identity used to prove `S.PosSemidef`.

Lemma 4.0 places `x(s)` in the nonnegative simplex, so every rate in the integrand is nonnegative;
every square is nonnegative. Therefore `Q(a)≥0` for every `a`. Symmetry gives `S.IsHermitian` over
`ℝ`, and (4.27) gives the nonnegative quadratic-form field. By the quadratic-form characterization
of `Matrix.PosSemidef`, these two facts produce

\[
  h_S:S.\mathrm{PosSemidef}.                              \tag{4.28}
\]

This proof precedes and is independent of the characteristic-function limit.

Lemma 4.1 also identifies the displayed formulas with the linearized flow. If

\[
 G(x)=\sum_\ell\beta_\ell(x)\,\ell\ell^T,
\]

then

\[
 S_{(j,i),(k,r)}=
 \left[\int_0^{\min(t_j,t_k)}
   \Phi(t_j,s)G(x(s))\Phi(t_k,s)^Tds\right]_{i,r},
\]

and `μ_(j,i)=(Φ(t_j,0)v₀)_i`. There is no initial covariance term because (4.2) has a deterministic
limit.

### Theorem 4.2 (Kurtz finite-dimensional CLT in Mathlib form)

With the hypotheses above, the covariance matrix `S` satisfies `S.PosSemidef`, and the sequence of
probability measures in (4.16) satisfies

\[
 \mathcal L_n\Longrightarrow
   \operatorname{multivariateGaussian}(\mu,S)
 \quad\text{in }
 \operatorname{ProbabilityMeasure}
   (\operatorname{EuclideanSpace}\ \mathbb R\ (\operatorname{Fin}m\times\operatorname{Fin}d)).
                                                                  \tag{4.29}
\]

Equivalently, (4.29) is the `Tendsto` statement displayed in Section 4.2.

#### Proof

By `ProbabilityMeasure.tendsto_iff_tendsto_charFun`, it is enough to prove pointwise convergence of
characteristic functions. Fix `a∈E_{m,d}` and use its coordinate function to define `α_j`, `ψ_j`,
and `ψ̃`. Put

\[
\begin{aligned}
 c_n&=\sum_j\psi_j(0)\cdot\sqrt{N_n}(z_n-x(0)),\\
 \xi_n&=\sqrt{N_n}\,I_n(\widetilde\psi,T),\\
 \rho_n&=\sqrt{N_n}\sum_jR_n(\psi_j,t_j).
\end{aligned}
\]

Summing (4.25), using (4.26), gives on `Ω_n`

\[
  \langle a,V_n\rangle=c_n+\xi_n+\rho_n.                 \tag{4.30}
\]

**Step 1: the exponential martingale and its nonlinear compensator.** Apply Section 2 with the
bounded purely imaginary tilt (4.14). Let

\[
 \zeta(r)=e^{ir}-1-ir.
\]

The linear identity (4.24), followed by (4.26), gives

\[
 A(T)=i\xi_n-D_n,                                        \tag{4.31}
\]

where

\[
 D_n=\int_0^T\sum_yq_{N_n}(X(s),y)
   \zeta\!\left(\frac{\widetilde\psi(s)\cdot(y-X(s))}
                       {\sqrt{N_n}}\right)ds.            \tag{4.32}
\]

Lemma L5 rewrites (4.32), on the simplex event, as a sum over `Γ.jumps`, including the lattice-invalid
and zero-jump cases rather than silently discarding them.

The integral Taylor formulas

\[
 e^{ir}-1-ir=-r^2\int_0^1(1-u)e^{iur}du
\]

and

\[
 e^{ir}-1-ir+\frac{r^2}{2}
 =(ir)^3\int_0^1\frac{(1-u)^2}{2}e^{iur}du
\]

give

\[
 |\zeta(r)|\le r^2/2,
 \qquad |\zeta(r)+r^2/2|\le|r|^3/6.                     \tag{4.33}
\]

Let

\[
 P=dJ\sup_s\|\widetilde\psi(s)\|.
\]

For every listed jump, `|ψ̃(s)·ℓ|≤P`. Since the sum of the listed rates is at most `Λ`, (4.33) and
Lemma L5 yield the deterministic bounds

\[
 |D_n|\le\bar D:=\frac{T\Lambda P^2}{2},                 \tag{4.34}
\]

and

\[
 \left|D_n+\frac12Q_n\right|
 \le\frac{T\Lambda P^3}{6\sqrt{N_n}}.                  \tag{4.35}
\]

Lemma L4 gives `Q_n→Q(a)` in probability, hence

\[
 D_n\longrightarrow-\tfrac12Q(a)
 \quad\text{in probability}.                            \tag{4.36}
\]

For each fixed population index `n`, let `A^{(n)}(T)` be the total measurable limiting exponent supplied by Corollary 2.5 for the tilt (4.14). On the probability-one event `Ω_n` of Lemma L6, the total limit agrees with the eventual record-index value, the clamped and unclamped expressions agree, and the pathwise compensator calculation gives `A^{(n)}(T)=iξ_n-D_n`. Hence this equality holds almost surely on the whole probability space. Corollary 2.5 gives `E exp(A^{(n)}(T))=1`, and therefore `E exp(iξ_n-D_n)=1`. This is equation `(4.37)`.

Using (4.37),

\[
\begin{aligned}
 \left|\mathbb E e^{i\xi_n}-e^{-Q(a)/2}\right|
 &=\left|\mathbb E\left[e^{i\xi_n}
      \left(1-e^{-D_n-Q(a)/2}\right)\right]\right|\\
 &\le\mathbb E\left|1-e^{-D_n-Q(a)/2}\right|.           \tag{4.38}
\end{aligned}
\]

The nonnegative random variables on the last line converge to zero in probability by (4.36) and
continuity of the exponential. By (4.34), they are bounded by the deterministic constant

\[
  1+e^{\bar D+|Q(a)|/2}.
\]

Lemma L1, not an almost-sure dominated-convergence argument, now shows that the right side of
(4.38) tends to zero. Notice that this step does not use `Q(a)≥0`.

**Step 2: the nonlinear Taylor remainder.** Put

\[
 Y_n^*=\sup_{0\le s\le T}\|Y_n(s)\|,
 \qquad U_n=\sqrt{N_n}Y_n^*.
\]

Because `E=Fin d→ℝ` carries the sup norm while `ψ·r` is the coordinate sum, one has `|ψ·r|≤d‖ψ‖∞‖r‖∞`. Lemma L3 therefore gives `√N_n |R_n(ψ_j,t_j)| ≤ d t_j ‖ψ_j‖∞ ω(Y_n*) U_n`. Put `C_j=d t_j ‖ψ_j‖∞`. The constants `C_j` are deterministic. Since `U_n` is tight and `ω(Y_n*)→0` in probability, Lemma L2 gives `C_j ω(Y_n*)U_n→0` in probability for each `j`; the finite-sum clause of Lemma L2 then gives `ρ_n=√N_n Σ_jR_n(ψ_j,t_j)→0` in probability. Every later reference to the right side of `(4.39)` is to this expression with the factor `d` included.

The LLN gives `Y_n^*→0` in probability, hence `ω(Y_n^*)→0` in probability. We next prove that
`U_n` is tight. Lemma L8 gives

\[
 U_n\le e^{LT}\left(
   \sqrt{N_n}\|z_n-x(0)\|
   +\sqrt{N_n}\sup_{s\le T}\|M_{N_n}(s)\|
 \right).                                                \tag{4.40}
\]

The first term converges by (4.2), hence is tight. The repository Doob `L²` estimate supplies a
constant `C_qv` with

\[
 \mathbb E\left[\sup_{s\le T}\|M_{N_n}(s)\|^2\right]
 \le\frac{C_{qv}T}{N_n}.
\]

Therefore Markov's inequality gives, for every `R>0`,

\[
 \Pr\left\{\sqrt{N_n}\sup_{s\le T}\|M_{N_n}(s)\|>R\right\}
 \le\frac{C_{qv}T}{R^2},                                \tag{4.41}
\]

uniformly in `n`. Equations (4.40)–(4.41) prove tightness of `U_n`. Lemma L2 applied to
`U_n` and `ω(Y_n^*)` makes the right side of (4.39) converge to zero in probability. The finite-sum
part of Lemma L2 then gives

\[
  \rho_n\longrightarrow0\quad\text{in probability}.     \tag{4.42}
\]

**Step 3: characteristic-function assembly.** By (4.2),

\[
 c_n\longrightarrow
 c:=\sum_j\psi_j(0)\cdot v_0=\langle a,\mu\rangle.       \tag{4.43}
\]

Use (4.30) and add and subtract the intermediate characteristic functions:

\[
\begin{aligned}
 &\mathbb E e^{i(c_n+\xi_n+\rho_n)}
      -e^{ic}e^{-Q(a)/2}\\
 &=\bigl(e^{ic_n}-e^{ic}\bigr)\mathbb E e^{i(\xi_n+\rho_n)}\\
 &\quad+e^{ic}\left(\mathbb E e^{i(\xi_n+\rho_n)}
                        -\mathbb E e^{i\xi_n}\right)\\
 &\quad+e^{ic}\left(\mathbb E e^{i\xi_n}-e^{-Q(a)/2}\right).
                                                               \tag{4.44}
\end{aligned}
\]

The first term is bounded by `|c_n-c|`. For the second, the elementary inequality

\[
 |e^{iu}-e^{iv}|\le\min(|u-v|,2)
\]

follows once from the integral of the derivative of `r↦e^{ir}` and once from the triangle
inequality. Thus it is bounded by
`E min(|ρ_n|,2)`. This bounded random variable converges to zero in probability by (4.42), so Lemma
L1 makes its expectation tend to zero. The last term tends to zero by Step 1. Hence (4.44) tends to
zero.

Finally, (4.27) says `Q(a)=a ⬝ᵥ S *ᵥ a`, and (4.28) permits the use of
`ProbabilityTheory.charFun_multivariateGaussian`. We have therefore proved, for every
`a∈E_{m,d}`,

For every `a∈E_{m,d}`, `charFun(ℒ_n)(a) → exp(i⟨a,μ⟩ - (a ⬝ᵥ S *ᵥ a)/2) = charFun(multivariateGaussian μ S)(a)`. Mathlib's Lévy equivalence for `ProbabilityMeasure` now yields (4.29).

### Scope and non-vacuity

For deterministic initial fluctuations satisfying (4.2), joint convergence at arbitrary finitely many observation times and all coordinates is the full finite-dimensional-distribution statement; the random-initial version discussed below is a separate strengthening that requires additional hypotheses and may have a non-Gaussian limit.

This theorem is the finite-dimensional-distribution consequence of the Ethier–Kurtz process CLT;
it does not claim convergence in a Skorokhod space. A random-initial extension requires more than
uniformity over a deterministic `N^{-1/2}` window: one must localize a tight initial fluctuation,
prove conditional characteristic-function convergence uniformly on the localization sets, and
identify the driving Gaussian noise jointly and asymptotically independently of the initial limit.
The resulting limit is

\[
  V(t)=\Phi(t,0)V_0+G(t),
\]

which need not be Gaussian. If `V₀` is Gaussian with covariance `Σ₀`, the block covariance gains
`Φ(t_j,0)Σ₀Φ(t_k,0)^T`.

A concrete nondegenerate probe is the two-state switch `A⇌B` with positive constants
`κ_+,κ_-`, jumps `(-1,1)` and `(1,-1)`, and rates `κ_+x_A` and `κ_-x_B`. Start in the interior of
the simplex and observe coordinate `A` at a positive time. The deterministic trajectory remains in
the interior. At terminal time, the adjoint has value `e_A`, whose dot products with the two jumps
are `−1` and `1`. By continuity, these dot products stay nonzero on a short interval before the
terminal time, while both rates are positive there. The corresponding diagonal entry of `S` is
therefore strictly positive.

Implementation status at the start of the Lean phase was as follows. `Ripple/CTMC/ExpMartingale.lean` contains the bounded-measurable calculus identity, the clamped one-step kernel identity `QMatrix.integral_cexp_expStepExponent`, and the finite-index definitions `recTime` and `expSum`; the file is an uncompiled work in progress and does not yet contain the record-index martingale, Ville inequality, jump-count limit, or pathwise package. `Ripple/Kurtz/Adjoint.lean` contains an uncompiled general continuous-linear-ODE existence and uniqueness development, but not the coordinate transpose and forward fundamental-matrix bridge stated in Lemma 4.1. `Ripple/Kurtz/ExponentialTail.lean` and `Ripple/Kurtz/Fluctuation.lean` do not exist at this head. The paper proof after the replacements in this document is complete at the paper level; this paragraph is not a Lean compilation receipt.


## 5. Statement list and implementation status at the start of the Lean phase

| # | node | planned module | paper status after this repair | Lean status at the start of the Lean phase |
|---|---|---|---|---|
| 1 | 2.1–2.2 | `Ripple/CTMC/ExpMartingale.lean` | Complete paper proof of the one-step identity and record-index martingale | Partial, uncompiled WIP: calculus identity, clamped one-step kernel identity, and finite-index `recTime`/`expSum` are present; the martingale/history theorem is not implemented |
| 2 | 2.3 | same | Complete paper proof of Ville's inequality | Not implemented in Lean |
| 3 | 2.4–2.6 | same, with support from `FrozenRandomIndexDoob.lean` | Complete paper proof of the jump tail, total measurable limit, and pathwise reading | The combined package is not implemented; `canonical_absorption_or_nonExplosive_ae` exists as supporting infrastructure |
| 4 | 3.1–3.4 | `Ripple/Kurtz/ExponentialTail.lean` | Complete paper proof of the martingale tail, exponential LLN, and `√(log N/N)` corollary | File absent; not implemented |
| 5 | 4.1 | `Ripple/Kurtz/Adjoint.lean` | Complete paper proof of the backward adjoint, forward fundamental matrix, and transpose bridge | Partial, uncompiled WIP: general linear ODE existence and uniqueness are present; the coordinate matrix and fundamental-matrix bridge are absent |
| 6 | 4.2 | `Ripple/Kurtz/Fluctuation.lean` | Complete paper proof of the Mathlib-form finite-dimensional CLT | File absent; not implemented |

Non-vacuity remains as stated, subject to construction of the promised probes: the LLN has existing model instances, and a two-state switch with positive rates, an interior trajectory, and a positive observation time gives a strictly positive covariance diagonal entry by the argument in the scope paragraph.

Note (2026-11-09): the table above is the status at the start of the Lean phase; `CHANGELOG.md` records
what has been formalized since.
Lean names fixed at the first green commit: `QMatrix.expStepExponent`, `QMatrix.expSum`,
`QMatrix.realExpSum`, `QMatrix.integral_cexp_expStepExponent`, `QMatrix.ville_realExpSum`
(§2); `Kurtz.frozen_martingale_exp_tail`, `Kurtz.kurtz_finite_horizon_exp_tail` (§3).

## 6. Review history

Round 1: 30 findings, 1 ERROR (unbounded adjoint tilt),
repaired in a first revision. Round 2: holds with repairs; 2 ERROR
(factor `d` in (4.39); L6 integrability inferred from an a.s. finite sum), 5 GAP, 6 MINOR, all
repaired here. Independent checks returned HOLDS on the affine-between-jumps step of Theorem 3.1
(including absorption before `T` and `T_n < T < T_{n+1}`) and on its constants.

### Round-2 resolution summary

The round-1 mathematical objections are resolved in the final §§2–4 after applying the blocks above. The round-2 defects are resolved as follows: the factor `d` is present in `(4.39)`; Lemma L6 uses a total measurable genuine-jump limit and the explicit bound `E J_{n,T}≤exp((e-1)N_nΛT)/(e-1)`; Corollary 2.5 uses a total measurable limiting exponent; Lemma 2.2 uses the repository's clamped one-step identity for arbitrary ambient histories; Lemma 4.1 constructs the forward fundamental matrix; the exceptional-set, active-cutoff, characteristic-function, dependent-probability-space, current-head, and scope wording is corrected; and §5 separates paper completeness from Lean implementation. The current code status is exactly the one recorded in §5.

## 7. Independent checks

### (a) Affine-between-jumps argument: HOLDS

For the time-independent real tilt `g(x,y)=σθ(y_i-x_i)`, the compensator `c(Y_n)` is constant during a sojourn. If `T_n≤t<T_{n+1}` and `t≤T`, the first `n` jumps and their compensator intervals end at `T_n`, so `A(t)=A_n(T)-(t-T_n)c(Y_n)`. Since this is a real affine function of `t`, its supremum on the truncated sojourn is controlled by its endpoint values.

At the left endpoint the value is `A_n(T)`. If `T_{n+1}≤T`, the left limit at the right endpoint is `A_{n+1}(T)-g(Y_n,Y_{n+1})≤A_{n+1}(T)+θJ`. If `T_n<T<T_{n+1}`, then the horizon endpoint satisfies `A(T)=A_{n+1}(T)` because the `(n+1)`st clamped step contributes no jump and exactly the compensator from `T_n` to `T`. If the chain is absorbed before `T`, all later records have zero holding time and unchanged state, `g(x,x)=0`, and `c(x)=0` because the state is absorbing; therefore `A` is constant after absorption and the same bound applies. Taking the supremum over all sojourns gives `sup_{0≤t≤T}A(t)≤sup_r A_r(T)+θJ`.

### (b) Constants in Theorem 3.1: HOLDS

With `θ=δ/(2TΛJ²)`, the condition `δ≤2TΛJ` gives `θJ=δ/(2TΛJ)≤1`. Hence every jump coordinate satisfies `|σθ(y_i-z_i)|≤θJ≤1`, and `p(r)=exp(r)-1-r≤r²` gives `κ(z)≤Σ_y q_N(z,y) θ²J² = λ(z)θ²J²≤NΛθ²J²`. The exponent in Ville's bound is `N(θδ-TΛθ²J²)`. Direct substitution gives `θδ=δ²/(2TΛJ²)` and `TΛθ²J²=δ²/(4TΛJ²)`, so their difference is `δ²/(4TΛJ²)`. Finally `exp(θJ)≤e`, yielding exactly `e exp(-Nδ²/(4TΛJ²))` for each signed coordinate and `2d e exp(-Nδ²/(4TΛJ²))` after the union bound.

