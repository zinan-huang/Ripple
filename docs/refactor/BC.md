# Bounded surrogate compilation: paper proofs and repairs ([BAC] Construction 3.1, Prop 3.2, Thms 3.3, 3.4, 4.5, 4.6)

Paper note accompanying Ripple release r2026.11. Section numbers are cited from Lean docstrings.
Paper numbering follows the DNA 32 version of [BAC]; page numbers refer to its 21-page author version. Every
formula below was re-derived, not copied.

Bibliography keys.

- [BAC] H.-L. Chen and X. Huang, *Bounded Analog Complexity* (DNA 32, 2026).
- BGP: O. Bournez, D. S. Graça, A. Pouly, *Polynomial time corresponds to solutions of polynomial
  ordinary differential equations of polynomial length*, J. ACM (arXiv 1609.08059).

Status labels used below. **HOLDS**: the printed argument is correct. **GAP**: a step is missing
or false as printed. **REPAIR**: a corrected argument. **INSTANCE**: a concrete example.

## 0. Summary

- **Numbering.** In the DNA 32 version: Construction 3.1, Prop 3.2 (limit preservation),
  **Thm 3.3** (bounded GPACs compute the same reals), Thm 3.4 (blow-up times are computable),
  **Lemma 4.1** (one-sided bound `L(t) ≤ v_max t`), Remark 4.2, Lemma 4.3 (state bound from arc
  length), Lemma 4.4 (one step keeps poly length), **Thm 4.5** (iterative bounded compilation),
  **Thm 4.6** (BGP poly-length ⇒ bounded poly-time).
- **Route chosen for Lean: one joint time change** `dt/dτ = 1/P(y)` with `P = 1 + Σᵢ yᵢ^N`
  (`N` even, `N ≥ deg F`), over **all** coordinates, with the multi-index surrogates
  `W_a = y^a/P` (`|a| ≤ N`) and a kept copy of the output. The compiled system is a ℚ-polynomial
  system, cubic in the `W`, with rational initial values; its solution is the explicit
  composition `τ ↦ Φ(y(s(τ)))`, defined on all of `[0, ∞)`; every `W_a` lies in `[−1, 1]`; the
  output keeps its limit. One construction, no induction over variables (§1.4). Checked
  symbolically on 5 configurations, 0 mismatches (§1.4.6).
- **Slowdown.** The paper's iteration composes time changes: `dτ_k/dt = Π_{j≤k}(1 + f_j^{n_j})`
  (§1.3.4, HOLDS), so the growth exponents of the eliminated variables **add**. The joint clock
  `dτ/dt = 1 + Σ yᵢ^N` takes their **maximum**. Time-modulus exponent for an input with
  `μ(r), L(μ(r)) ≤ C(r+1)^k`: joint `k(N+1)`; iterated, by the composite formula,
  `k(1 + Σ_j n_j)`; by the bound the paper's own proof of Thm 4.5 carries through,
  `k·Π_j(1 + n_j + D_j)` (§1.6). Dimension: joint `1 + C(d+N, N)`; iterated `d + Σ_j n_j`.
- **Gaps found** (each with an explicit instance or the failing sentence; §1.7):
  E1 odd `n` (`1 + f^n` vanishes; `U ∈ [0,1]` needs `f ≥ 0`); E2 Prop 3.2, `T* = ∞`: "`s(τ) ≤ τ → ∞`"
  does not give `s → ∞`; E3 Prop 3.2, `T* < ∞`: "`f̄ → ∞` forces `τ → ∞`" fails — instance
  `g' = g²`, `f' = fg/4`, where eliminating `f` reaches `T* = 1` at `τ = 3`; E4 the iteration's
  measure, the choice of variables and the output are unspecified; E5 Thm 3.4 uses one factor
  `U_{n,0}` where the iteration gives a product, and assumes global existence in `τ`; E6 Thm 4.5's
  bound compounds per step (still polynomial); E7 "the time at which the output reaches precision
  `r`" is read as the Def 2.3 modulus. **None of them changes a main theorem**: Thm 3.3, 3.4, 4.5
  and 4.6 hold as stated, with the repairs below.
- **Lean statements** (§3): `IsGPACComputable`, `bounded_compilation` (Thm 3.3),
  `isGPACComputable_iff_isCRNComputable`, `PolyPIVP.arcLength`, `PolyPIVP.arcLength_le_of_bounded`
  (Lemma 4.1), `PolyPIVP.abs_sub_init_le_arcLength` (Lemma 4.3), `bounded_compilation_polyTime`
  (Thm 4.5 + 4.6, exponent `k(N+1)`), `bounded_compilation_of_blowup` (Prop 3.2 with
  `T* < ∞`), `isCRNComputable_blowupTime` (Thm 3.4), and the non-vacuity examples
  (`π/2` from `arctan` with an unbounded clock; `π/2` from the pole of `tan`).

## 1. The paper's statements and complete proofs

### 1.1 Definitions used ([BAC] §2, pp. 5–6)

> **Definition 2.1 (PIVP)** (p. 5). y′(t) = p(y(t)), y(0) = y₀ ∈ Q^d, where p : R^d → R^d is a
> vector of polynomials with rational coefficients. We write y(t) for the (unique, maximal)
> solution. A PIVP is bounded if there exists M > 0 such that ∥y(t)∥ ≤ M for all t ≥ 0.
>
> §2.3 (p. 5): "a PIVP computes a real number α if a designated output variable x(t) → α as
> t → ∞" [BGP convergence semantics].
>
> **Definition 2.3** (p. 6). Let x(t) be a designated output variable of a bounded PIVP. The
> system computes α if there exists a time modulus µ : N → [0, ∞) such that |x(t) − α| < e^{−r}
> whenever t > µ(r).

Lean: `PolyPIVP` (`Core/PIVP.lean`, ℚ-polynomial field, ℚ initial value),
`PIVP.Solution` (`HasDerivAt` at every `t ≥ 0`), `PIVP.Computes` (`Core/PIVP.lean`, the §2.3
limit), `CertifiedBoundedTimeComputable` and `IsCRNComputable` (`Core/BoundedTime.lean`,
Def 2.1 + 2.3, S1.md §1.5). "Computable by a (possibly unbounded) GPAC" (Thm 3.3) is therefore
the §2.3 notion for a ℚ-PIVP whose solution exists on `[0, ∞)`; its Lean name is
`IsGPACComputable` (§3.1).

Notation. `F = (F₁, …, F_d)` with `Fᵢ = Σ_β c_{i,β} y^β ∈ ℚ[y]`; `D = maxᵢ deg Fᵢ`
(total degree); `y^a = Πᵢ yᵢ^{aᵢ}`, `|a| = Σᵢ aᵢ`; `‖·‖` is the sup norm (Lean's norm on
`Fin d → ℝ`); `C_F = maxᵢ Σ_β |c_{i,β}|`.

### 1.2 Construction 3.1 as printed (pp. 6–7), checked

> Let Z = (z₁, …, z_{d−1}, f) satisfy Ż = p(Z) with p ∈ Q[Z]^d, where f is the unbounded variable
> to eliminate. Let n be the highest degree of f in any component of p.
> Step 1: Time change. f̄(τ) = f(s(τ)), z̄ⱼ(τ) = zⱼ(s(τ)), s′(τ) = 1/(1 + f̄(τ)^n);
> U_{n,m}(τ) = f̄^m/(1 + f̄^n) ∈ [0, 1], m = 0, …, n, U_{n,0} + U_{n,n} = 1.
> Step 2: pⱼ = Σ_{m=0}^n g_{j,m}(z̄) f̄^m gives dz̄ⱼ/dτ = Σ_m g_{j,m}(z̄) U_{n,m}.
> Step 3: dU_{n,m}/dτ = (m U_{n,m−1} − n U_{n,n−1} U_{n,m}) · df̄/dτ, and with p_d = Σ_m h_m(z̄) f̄^m,
> df̄/dτ = Σ_m h_m U_{n,m}; hence (1) dU_{n,m}/dτ = (m U_{n,m−1} − n U_{n,n−1} U_{n,m}) Σ_k h_k(z̄) U_{n,k}.
> "If any of z̄₁, …, z̄_{d−1} remain unbounded, apply the construction again […] and repeat until
> all variables are bounded."

Check. Write `u = f̄`. `d/du [u^m/(1+u^n)] = m u^{m−1}/(1+u^n) − n u^{m+n−1}/(1+u^n)²
= m U_{n,m−1} − n U_{n,n−1} U_{n,m}` (for `m = 0` the first term is absent), and
`du/dτ = p_d(Z̄) s′ = Σ_k h_k(z̄) u^k/(1+u^n) = Σ_k h_k U_{n,k}` because `deg_f p_d ≤ n`.
Steps 2–3 and (1) **HOLD** (given that `1 + f̄^n` never vanishes, see E1). The worked examples
(2) (p. 7) and (3) (p. 8) also **HOLD**: for (2), `x′ = (1−x)(1+v)²` gives
`dx̄/dτ = (1−x̄)(U₀ + 2U₁ + U₂) = (1−x̄)(1 + 2U₁)`, and `dU₁/dτ = (U₀² − U₁²)(1 + 2U₁)
= (U₀+U₁)²(2U₀ − 1)` using `U₂ = 1 − U₀`, `U₁² = U₀ − U₀²`; for (3), `dx̄/dτ = 1`,
`U₀′ = −2U₀U₁`, `U₁′ = U₀² − U₁² = U₀(2U₀ − 1)`, `t(τ) = arctan τ`.

**Sign (E1).** With odd `n`, `1 + f̄^n = 0` at `f̄ = −1`. INSTANCE: `f′ = f − 2`, `f(0) = 0`
(`n = 1`), `f(t) = 2 − 2eᵗ` reaches `−1` at `t = ln(3/2)`, where `s′ = 1/(1+f)` is undefined. And
`U_{n,m} ∈ [0,1]` needs `f̄ ≥ 0`: for `f̄ < 0` and odd `m`, `U_{n,m} < 0`. REPAIR: take `N` even
with `N ≥ n` (the exponent is a free choice; the closure only needs `deg_f pᵢ ≤ N`). Then
`1 + f^N ≥ 1`, and for `0 ≤ m ≤ N`: `|f|^m ≤ max(1, |f|^N) ≤ 1 + f^N`, so `|U_{N,m}| ≤ 1`; and
`U_{N,m} ∈ [0, 1]` when `m` is even or `f ≥ 0`. Boundedness is all that Def 2.1 and
`IsCRNComputable` need; nonnegativity is the business of the dual-rail stage ([BAC] §7).

### 1.3 Prop 3.2 and the iteration (p. 7), with repairs

> **Proposition 3.2 (Limit preservation).** Let T* ≤ ∞ be the maximal existence time of the
> original system. If lim_{t→T*−} zⱼ(t) = L, then lim_{τ→∞} z̄ⱼ(τ) = L.
> *Proof.* […] If T* = ∞ (no blowup), then s(τ) ≤ τ → ∞. If T* < ∞ (finite-time blowup), then
> f̄(τ) → ∞ as s(τ) → T*−, forcing s′(τ) → 0; thus s(τ) → T* but never reaches it, and the approach
> takes τ → ∞. In both cases, z̄ⱼ(τ) = zⱼ(s(τ)) → L.

#### 1.3.1 The time change, constructed (even `N`)

Let `y` solve the system on `[0, T*)` and let `ρ(t) = 1 + f(t)^N ≥ 1`, continuous on `[0, T*)`.
Define `θ(t) = ∫₀ᵗ ρ(u) du`. Then `θ(0) = 0`, `θ′ = ρ ≥ 1`, so `θ` is a strictly increasing
`C¹` map of `[0, T*)` onto `[0, τ*)`, `τ* := lim_{t→T*} θ(t) ∈ (0, ∞]`. Let `s = θ⁻¹ : [0, τ*) → [0, T*)`;
by the inverse-function rule `s′(τ) = 1/ρ(s(τ)) = 1/(1 + f̄(τ)^N) ∈ (0, 1]`. So the
reparametrised trajectory exists exactly on `[0, τ*)`, and Prop 3.2 needs **`τ* = ∞`**.

#### 1.3.2 `T* = ∞` (E2) — REPAIR

The printed "`s(τ) ≤ τ → ∞`" is an upper bound on `s` and does not show `s(τ) → ∞`
(GAP). Two correct arguments:

1. `θ(t) ≥ t` (since `ρ ≥ 1`), so `τ* = ∞` and `θ : [0,∞) → [0,∞)` is an increasing bijection;
   its inverse `s` is increasing and unbounded (if `s ≤ S` then `τ = θ(s(τ)) ≤ θ(S)` for all `τ`),
   hence `s(τ) → ∞`.
2. `s` is increasing; if `s(τ) → S < ∞`, then `f` is continuous on the
   compact `[0, S]`, so `|f| ≤ K` there and `s′ = 1/(1 + f̄^N) ≥ 1/(1 + K^N) > 0` for all `τ`,
   whence `s(τ) ≥ τ/(1 + K^N) → ∞`, a contradiction.

Then `z̄ⱼ = zⱼ ∘ s → L` by composition of limits. **HOLDS after the repair.**

#### 1.3.3 `T* < ∞` (E3) — GAP, REPAIR

The proof assumes that the eliminated `f` is the variable that blows up and that `f̄ → ∞` forces
`τ* = ∞`. Neither holds in general: `τ* = ∫₀^{T*}(1 + f^N) dt` can be finite although `f → ∞`.
INSTANCE: `g′ = g²`, `f′ = (1/4) f g`, `f(0) = g(0) = 1`. Then `g = 1/(1−t)`,
`f = (1−t)^{−1/4}` (`f′ = (1/4)(1−t)^{−5/4} = (1/4) f g` ✓), `T* = 1`, and both variables blow up.
`deg_f p = 1`; eliminate `f` with `N = 2`:
`τ* = ∫₀¹ (1 + (1−t)^{−1/2}) dt = 1 + 2 = 3`. So `s` reaches `T* = 1` at `τ = 3`, the compiled
system blows up at `τ = 3` (its `ḡ` does), and "`lim_{τ→∞} z̄ⱼ(τ)`" has no meaning. (The same
happens if the eliminated variable stays bounded while another blows up.) Consumers in [BAC]:
Thm 3.3 is unaffected (its inputs have `T* = ∞`); Thm 3.4 is affected through the
iteration (E5); the example of [BAC] §3.1 is unaffected (there `v ~ 1/(1−t)` and `∫(1+v²) = ∞`).

REPAIR: eliminate all variables at once with the joint clock of §1.4. If `y` is
unbounded on `[0, T*)` (equivalently, for a polynomial field, `T* < ∞` is maximal), then
`τ* = ∞`: every monomial with `|β| ≤ N` satisfies `|y^β| ≤ P(y)` (§1.4.2), so
`|Fᵢ(y)| ≤ C_F P(y)`, and
`|yᵢ(t) − yᵢ(0)| ≤ ∫₀ᵗ |Fᵢ(y)| ≤ C_F ∫₀ᵗ P(y) = C_F θ(t)`; an unbounded `y` forces an unbounded
`θ`. (With the iterated route the repair is weaker: the iteration still ends with a bounded
system, but each intermediate Prop 3.2 must be read with its own blow-up time `τ*_i`, and the
global existence of the last system needs the maximal-solution correspondence; the joint route
avoids this.)

#### 1.3.4 The iteration (E4) and the composition formula — HOLDS, with repairs

Composition. Step 1 has `dτ₁/dt = 1 + f₁(t)^{n₁}`. Step 2 reparametrises the step-1
system by `dτ₂/dτ₁ = 1 + f̄₂(τ₁)^{n₂}` where `f̄₂(τ₁) = f₂(s₁(τ₁)) = f₂(t)`. Hence
`dτ₂/dt = (dτ₂/dτ₁)(dτ₁/dt) = (1 + f₂(t)^{n₂})(1 + f₁(t)^{n₁})`, and by induction

    dτ_k/dt = Π_{j≤k} (1 + f_j(t)^{n_j}),   i.e.   dt/dτ_k = Π_{j≤k} U^{(j)}_{n_j,0}.

**HOLDS.** Example: `d` variables growing like `t` with `n_j = 2` give
`τ ~ ∫ t^{2d} ~ t^{2d+1}`.

The iteration needs, and the paper leaves implicit (E4):
(a) *measure*: the range of `z̄ⱼ` on `[0, τ*)` equals the range of `zⱼ` on `[0, T*)` (`s` is a
bijection), so the set of unbounded original variables loses exactly the eliminated one per step,
and surrogates are bounded; the iteration ends after `k` = (number of unbounded variables) steps;
(b) *degrees do not grow*: in the compiled system the `z̄`-degree of every equation is at most
that of `p` (Step 2 keeps `g_{j,m}`; equation (1) has `z̄`-degree `max_k deg h_k`), so each
later `n_i ≤ D` (rounded up to even);
(c) *choice*: which variables are unbounded is not decidable from the syntax. When `T* = ∞`,
eliminating a bounded variable is harmless (a bounded factor in the clock, `θ(t) ≥ t` still
holds), so one may eliminate every non-output variable. When `T* < ∞` it is not harmless:
eliminating a bounded variable gives a finite `τ*` (§1.3.3);
(d) *output*: the output must be kept as a state (it is bounded, since it converges and is
continuous on `[0, ∞)`); if it were eliminated, the limit would have to be read from surrogates.

### 1.4 The joint route (the Lean route): construction and complete proof

Fixed data: `P₀ : PolyPIVP d` with field `F`, output index `o`, `D = maxᵢ deg Fᵢ`; an even
`N ≥ max(D, 2)` (the smallest such is `N = 2⌈max(D,2)/2⌉`).

#### 1.4.1 Objects

- Clock: `P(y) = 1 + Σᵢ yᵢ^N ≥ 1` (all `d` coordinates; `N` even).
- Index set `A = {a ∈ ℕ^d : |a| ≤ N}` (Lean: `SurrogateIndex d N`, the subtype of
  `MIndex d N = Fin d → Fin (N+1)` of multi-indices of degree at most `N`, a `Fintype`);
  `|A| = C(d+N, N)`.
- Surrogates `W_a(y) = y^a / P(y)`, `a ∈ A`; in particular `W₀ = 1/P = dt/dτ`.
- Compiled state `X = (x̄, (W_a)_{a∈A})`, dimension `1 + C(d+N, N)`; `x̄` is the kept output.
- Splitting. For `k ≥ 1` and `|β| ≤ kN` there are `σ¹(β), …, σᵏ(β) ∈ A` with
  `Σⱼ σʲ(β) = β`. Proof: greedy — `σ¹` takes from `β` coordinates in order until `N` units are
  taken or `β` is exhausted; each round removes `min(|rest|, N)` units, so after `k` rounds the
  rest is `0` iff `|β| ≤ kN`. Consequence: `y^β / P^k = Πⱼ W_{σʲ(β)}(y)`. For the
  monomials that actually occur no general split is needed: `γ = (a − eᵢ) + β` and
  `δ = a + (N−1)eᵢ + β` are sums of two, resp. three, elements of `A` (`|a − eᵢ| ≤ N`, `|β| ≤ D ≤ N`,
  `|(N−1)eᵢ| ≤ N`), and the Lean construction uses exactly these splits.
- Lifted field: for `q = Σ_β c_β y^β` with `deg q ≤ N`, write `q^W := Σ_β c_β W_β`, so that
  `q^W(W(y)) = q(y)/P(y)`.
- Compiled field (`a ∈ A`; `eᵢ` the unit vector; the `aᵢ`-term is absent when `aᵢ = 0`):

      x̄′  = F_o^W
      W_a′ = Σᵢ aᵢ · W_{a−eᵢ} · Fᵢ^W  −  N · W_a · Σᵢ W_{(N−1)eᵢ} · Fᵢ^W
           = Σᵢ Σ_β c_{i,β} [ aᵢ · W_{a−eᵢ} W_β  −  N · W_a W_{(N−1)eᵢ} W_β ].

  Well defined when `D ≤ N` (every `β` of every `Fᵢ` lies in `A`). (With a general split, the
  surrogate lines close already for `D ≤ N + 1`; the output line needs `D ≤ N`.)
- Coefficients: `c_{i,β} ∈ ℚ`, `aᵢ ∈ ℕ`, `N ∈ ℕ` — all rational. Degree: at most 3.
- Initial value: `x̄(0) = y₀,o ∈ ℚ`, `W_a(0) = y₀^a / (1 + Σᵢ y₀ᵢ^N) ∈ ℚ` (`y₀ ∈ ℚ^d`, `P(y₀) ≥ 1`).

#### 1.4.2 Boundedness of the surrogates

For `a ∈ A`: let `M = maxᵢ |yᵢ|`. `|y^a| ≤ M^{|a|}`. If `M ≤ 1`, `M^{|a|} ≤ 1 ≤ P`. If `M > 1`,
`M^{|a|} ≤ M^N = maxᵢ yᵢ^N ≤ P` (N even). So `|W_a| ≤ 1`, and `0 < W₀ ≤ 1`. The same argument
gives `|y^β| ≤ P(y)` for every `|β| ≤ N`, hence `‖F(y)‖ ≤ C_F P(y)` (used in §1.3.3, §1.5).

#### 1.4.3 The time change

Let `sol` be a solution of `P₀` on `[0, ∞)`; replace it by the globally continuous solution `y`
equal to it on `[0, ∞)` (`PIVP.Solution.exists_continuous`, linear for `t < 0`). Let
`ρ(t) = P(y(t))`: continuous on `ℝ`, `ρ ≥ 1`. Let `θ(t) = ∫₀ᵗ ρ`. Then `θ` is `C¹` on `ℝ` with
`θ′ = ρ ≥ 1`; `θ(t) ≥ t` for `t ≥ 0` and `θ(t) ≤ t` for `t ≤ 0`; so `θ : ℝ → ℝ` is a strictly
increasing continuous surjection (IVT), an order isomorphism. Let `s = θ⁻¹`. Then:
`s(0) = 0`; `s` is continuous and strictly increasing; `s(τ) ≥ 0` for `τ ≥ 0`;
`s′(τ) = 1/ρ(s(τ)) ∈ (0, 1]` (inverse-function rule, `ρ ≠ 0`); `s(τ) → ∞` as `τ → ∞`
(§1.3.2, either argument: a finite limit `S` would keep `y` bounded on `[0, S]` and `s′`
bounded below). In Lean this is `exists_inverse_timeChange` (`Core/TimeChange.lean`), for any
continuous `ρ ≥ 1`; the case `ρ = 1 + z^N` is `GPAC.timeChange_via_inverse`
(`BoundedUniversality/GPAC/ExplicitCompile.lean`).

#### 1.4.4 The compiled solution and the derivative identity

Define `X(τ) = Φ(y(s(τ)))` for all `τ ∈ ℝ`, with `Φ(y) = (y_o, (W_a(y))_{a∈A})`. `X` is
continuous on `ℝ` (`y`, `s` continuous, `P ≥ 1`), and `X(0) = Φ(y₀)` is the compiled initial
value. Fix `τ ≥ 0`, `t = s(τ) ≥ 0`, `y = y(t)`. Chain rule: `d/dτ y(s(τ)) = s′(τ) F(y) = F(y)/P(y)`.
So `x̄′(τ) = F_o(y)/P = Σ_β c_{o,β} y^β/P = Σ_β c_{o,β} W_β(y)`. For `a ∈ A`,

    d/dτ W_a(y(s(τ))) = (1/P) [ (∇y^a · F)/P − y^a (∇P · F)/P² ]
                      = Σᵢ aᵢ y^{a−eᵢ} Fᵢ / P²  −  Σᵢ N yᵢ^{N−1} y^a Fᵢ / P³
                      = Σᵢ aᵢ W_{a−eᵢ} (Fᵢ/P)  −  N W_a Σᵢ W_{(N−1)eᵢ} (Fᵢ/P)
                      = Σᵢ aᵢ W_{a−eᵢ} Fᵢ^W  −  N W_a Σᵢ W_{(N−1)eᵢ} Fᵢ^W,

using `∂ᵢ y^a = aᵢ y^{a−eᵢ}` (zero when `aᵢ = 0`), `∂ᵢ P = N yᵢ^{N−1} = N y^{(N−1)eᵢ}` and
`Fᵢ/P = Fᵢ^W` (expansion of `Fᵢ`). This is the compiled field evaluated at `X(τ)`. So `X` solves the
compiled ODE at every `τ ≥ 0` with the two-sided derivative (`s` is differentiable on all of
`ℝ`, and `y` is differentiable at every `t ≥ 0`), i.e. `X` is a `PIVP.Solution` of the compiled
`PolyPIVP`, with a continuous trajectory.

#### 1.4.5 Boundedness, limit, modulus

- `|W_a(X(τ))| ≤ 1` (§1.4.2). The output `x̄(τ) = y_o(s(τ))`, and `{y_o(t) : t ≥ 0}` is bounded
  (continuous on `[0, T]`, and within 1 of `α` after some `T`). Hence the compiled trajectory is
  bounded on `[0, ∞)`: Def 2.1's boundedness.
- `x̄(τ) = y_o(s(τ)) → α` (`s → ∞`, `y_o → α`).
- Modulus: `CertifiedBoundedTimeComputable.exists_of_tendsto` (`Core/BoundedTime.lean`)
  reads it off the limit. Hence `IsCRNComputable α`. This proves **Thm 3.3** (§1.3: the iterated
  route also proves it, after E2 and E4).
- The output is kept, not eliminated (§1.3.4 (d)); the original time `t = s(τ)` and the
  unbounded `y` "pass through" (Remark 6.5) and are not states.

#### 1.4.6 Numerical check (a measurement, not a proof)

A symbolic check was run with sympy (greedy split as above, random ℚ fields with 4 monomials per
component) for `(d, N, D) ∈ {(1,2,2), (2,2,2), (2,4,3), (3,2,2), (2,4,4)}`: all
`|A| ∈ {3, 6, 15, 10, 15}` surrogate equations satisfy `(1/P) d/dt W_a = G_a(W)` identically, and
`F_o/P = Σ c W_β` identically; 0 mismatches.

#### 1.4.7 Variant with a known bounded set

If `y = (z_S, z_B)` and `z_B` is known to be bounded, take `P = 1 + Σ_{i∈S} zᵢ^N`, `A_S =
{a ∈ ℕ^S : |a| ≤ N}`, keep `z̄_B` as states. With `Fᵢ = Σ c_{i,β,γ} z_S^β z_B^γ` and
`deg_{z_S} F ≤ N`: `z̄_b′ = Σ c_{b,β,γ} z̄_B^γ W_β`; `W_a′ = Σ_{i∈S} Σ c_{i,β,γ} z̄_B^γ [aᵢ ΠW(σ(γ_S)) −
N ΠW(σ(δ_S))]` with `γ_S = a − eᵢ + β`, `δ_S = a + (N−1)eᵢ + β`. Bounded factors `z̄_B^γ` times
products of `W`; dimension `|B| + C(|S|+N, N)`. The Lean route takes `S = all` (no knowledge of
`B` needed; the output copy plays the role of `B`). A smaller closed set of multi-indices may
suffice for particular systems (monomial-quadratization style); not needed for the theorems.

### 1.5 Thm 3.4 (p. 8): blow-up times, repaired

> **Theorem 3.4.** Let y′ = p(y), y(0) = y₀ ∈ Q^d be a PIVP with finite maximal existence time
> T* < ∞. Then T* is computable by a bounded PIVP. *Proof.* […] s′(τ) = U_{n,0}(τ) […] Adjoin s
> […] s(τ) < T* […] If L < T*, then f̄(τ) → f(L) […] s′(τ) → 1/(1 + f(L)^n) > 0, contradicting […]

E5: after `k` elimination steps, `dt/dτ = Π_j U^{(j)}_{n_j,0}` (§1.3.4), not one
`U_{n,0}`; and the proof assumes the compiled system exists for all `τ`, which E3 shows can fail
step by step. REPAIR (joint route, **without the kept output**): `y`
is unbounded on `[0, T*)` (a bounded solution of a
polynomial ODE on a finite interval extends). Work on `(−∞, T*)` (extend `y` linearly for
`t < 0`): `θ(t) = ∫₀ᵗ P(y)`, `θ′ ≥ 1`, `θ(t) ≤ t` for `t ≤ 0`, and `θ(t) → ∞` as `t → T*`
(§1.3.3), so `θ : (−∞, T*) → ℝ` is an order isomorphism; `s = θ⁻¹` as in §1.4.3, with values in
`[0, T*)` for `τ ≥ 0`. The compiled system for Thm 3.4 has the state `(s, (W_a)_{a∈A})`: the
surrogate lines of §1.4.1, and `s′ = W₀` (a state, so the field stays polynomial), `s(0) = 0 ∈ ℚ`,
output `s`. It does **not** keep `x̄ = y_o∘s`: in Thm 3.4 the output coordinate itself may blow up
(for `x′ = 1 + x²`, `N = 2`: `x̄′ = (1+x²)/(1+x²) = 1`, so `x̄(τ) = τ` is unbounded, as the paper
notes on p. 8). Dimension `1 + C(d+N, N)`. Bounded: `0 ≤ s < T*`. Limit: `s(τ) → T*` (`s` is the inverse of
an increasing bijection onto `ℝ`; equivalently the paper's argument: a limit `L < T*` keeps `y`
bounded on `[0, L]`, so `s′ = W₀` is bounded below and `s` is unbounded). Output `s`; modulus by
`exists_of_tendsto`. **HOLDS after the repair.** The same construction with the kept output
`x̄` gives Prop 3.2 for `T* < ∞`: if `y_o(t) → α` as `t → T*⁻`, the compiled output tends to
`α` (`bounded_compilation_of_blowup`, §3.5; there the output converges, so `x̄` is bounded). π
example ([BAC] §3.2): `x′ = 1 + x²`, `T* = π/2`, `D = 2`, `N = 2`, `d = 1`: states `s, W₀, W₁, W₂`;
Thm 3.4 gives `IsCRNComputable (π/2)`.
(The paper's (3) is the `n = 2` single-variable form of the same; with `x̄ = τ` its three
states `U₀, U₁, t` suffice.)

### 1.6 §4: Lemma 4.1, Lemma 4.3, Lemma 4.4, Thm 4.5, Thm 4.6

> **Lemma 4.1 (One-sided bound)** (p. 9). y′ = p(y) with trajectory in a compact D ⇒
> ∥p(y)∥ ≤ v_max on D, hence L(t) = ∫₀ᵗ ∥y′∥ ≤ v_max t.
> "The converse one-sided inequality L(t) ≥ v_min t […] fails for the very systems described by
> Definition 2.3. We do not assume it."

Proof (HOLDS): `p` is continuous on the compact closed ball of radius `M`; `y′ = p(y)`; integrate.
(In Lean: `‖P.evalField x‖ ≤ v_max` on `‖x‖ ≤ M` by `IsCompact.exists_bound_of_continuousOn`,
then an interval-integral bound for a function bounded by a constant.)

> **Lemma 4.3** (p. 10). If L(t_r) ≤ q(r) then |yᵢ(s)| ≤ |yᵢ(0)| + q(r) for s ∈ [0, t_r].

Proof (HOLDS): `yᵢ(s) − yᵢ(0) = ∫₀ˢ Fᵢ(y)` (FTC; the integrand is continuous on `[0, s]`), so
`|yᵢ(s) − yᵢ(0)| ≤ ∫₀ˢ ‖F(y)‖ = L(s) ≤ L(t_r)` (`L` is nondecreasing).

> **Lemma 4.4** (p. 10). L_pre(t_r), t_r ≤ q(r); eliminate f of maximal degree n ⇒ τ_r ≤ Q_t(r),
> L_post(τ_r) ≤ Q_L(r). *Proof:* τ_r = ∫₀^{t_r}(1 + f^n) ≤ q(r)(1 + M_f(r)^n); ∥p_post∥ ≤ M_p(r)
> via |z̄ⱼ| ≤ |z̄ⱼ(0)| + q(r); L_post(τ_r) ≤ M_p(r) τ_r.
>
> **Theorem 4.5** (p. 10). L(t_r), t_r ≤ q(r) ⇒ iterated compilation gives a fully bounded PIVP
> computing the same number whose trajectory length and physical time at precision r are both
> polynomial in r; dimensional overhead polynomial in the maximal monomial degree of p.
> *Proof:* induction, Q^{(i+1)} := max(Q_t, Q_L); k steps; overhead at most k(n+1).
>
> **Theorem 4.6** (p. 11). BGP poly length and poly time ⇒ bounded PIVP in polynomial physical
> time. *Proof.* Theorem 4.5.

Reading of the hypothesis (E7). "`t_r` is the physical time at which the output reaches
precision `r`" is read as Def 2.3's modulus: `|y_o(t) − α| < e^{−r}` for all `t > μ(r)`, with
`0 ≤ μ(r) ≤ q(r)` and `L(μ(r)) ≤ q(r)`. (BGP's definition is length-indexed: error
`≤ e^{−r}` once `L(t) ≥ Ω(r)`; together with the paper's extra hypothesis on physical time it
gives this form with `t_r = inf{t : L(t) ≥ Ω(r)}`, at precision `r + 1` for the strict `<`.) We
take `q(r) = C(r+1)^k`.

BGP's definition carries `L(t) ≥ t`: Bournez, Graça,
Pouly, J. ACM (arXiv 1609.08059), Definition 2.3 (Poly-Length-Computable Functions), p. 1:7–1:8,
third bullet "len_y(0, t) ⩾ t ◮ technical condition: the length grows at least linearly with
time" (likewise Definition 2.1, p. 1:7, and the variants on pp. 1:15 and 1:39; footnote 3 says it
may be weakened to `‖p(y(t))‖ ≥ 1/poly(t)`). So under BGP's definition `t_r ≤ L(t_r) ≤ Ω(r)`,
and the paper's "and polynomial physical time" is implied by polynomial length. Our hypothesis
does not assume the technical condition, so it keeps `μ(r) ≤ q(r)` as a separate premise; it is
weaker than or equal to BGP's normalisation.

Lemma 4.4 HOLDS for even `n` (with odd `n`, E1: `1 + f^n` can be `≤ 0` and `τ` is not a time
change). Thm 4.5's statement HOLDS; its proof's accounting compounds (E6, not a defect of
the statement): step `i+1` bounds the next variable through `S_i`'s arc length,
`|f̄_{i+1}| ≤ c + Q^{(i)}`, so `deg Q^{(i+1)} ≤ deg Q^{(i)} · (1 + n_{i+1} + D_i)` (`D_i` the
degree of `S_i`'s field, from `Q_L = M_p Q_t`), i.e. exponent `k·Π_j(1 + n_j + D_j)` — exponential
in the number of steps, still polynomial in `r`. Sharper, by §1.3.4: the ranges of the original
variables do not change under reparametrisation, so `|f_j| ≤ c + q(r)` throughout, and
`τ_r = ∫₀^{μ(r)} Π_j(1 + f_j^{n_j}) ≤ q(r) Π_j(1 + (c + q(r))^{n_j})`: exponent `k(1 + Σ_j n_j)`.

**Joint route, Thm 4.5 + 4.6 (the Lean statement of §3.4).** Assume the hypothesis above
and `N` even, `max(D,2) ≤ N`. Let `c₀ = ‖y₀‖`. For `t ∈ [0, μ(r)]`, `‖y(t)‖ ≤ c₀ + L(μ(r)) ≤ c₀ +
C(r+1)^k` (Lemma 4.3). Compiled modulus: `μ′(r) := θ(μ(r))` (for `τ > θ(μ(r))`, `s(τ) > μ(r)`, so
`|x̄(τ) − α| = |y_o(s(τ)) − α| < e^{−r}`). Bound:

    μ′(r) = ∫₀^{μ(r)} (1 + Σᵢ yᵢ^N) ≤ μ(r) (1 + d (c₀ + C(r+1)^k)^N)
          ≤ C (r+1)^k (1 + d (c₀ + C)^N (r+1)^{kN}) ≤ C′ (r+1)^{k(N+1)},

with `C′ = C(1 + d(c₀ + C)^N)` (using `r + 1 ≥ 1` and `C ≥ 0`, which `0 ≤ μ(0) ≤ C` forces).
`IsPolyTimeComputable` needs a positive constant: take `max(C′, 1)`. So
`IsPolyTimeComputable α (k(N+1))`. The compiled trajectory length is then polynomial as well:
by Lemma 4.1, `L′(τ) ≤ v′_max τ` for the bounded compiled system — this is Thm 4.5's second
clause; `IsPolyTimeComputable` does not mention it, so it is a corollary
(`arcLength_le_of_bounded` applied to the compiled certificate).

**Comparison of routes.**

| route | clock `dτ/dt` | dimension of compiled system | modulus exponent (input `q = C(r+1)^k`) |
|---|---|---|---|
| paper, iterated, `k` eliminated variables, even `n_j` | `Π_j (1 + f_j^{n_j})` | `d + Σ_j n_j` (each step adds `n_j + 1`, removes `f_j`) | `k(1 + Σ_j n_j)` (composite); paper's proof: `k Π_j(1 + n_j + D_j)` |
| joint, product clock, per-variable surrogates `yᵢ^m/(1+yᵢ^N)` (= iterated over all `d`) | `Πᵢ (1 + yᵢ^N)` | `1 + d(N+1)` | `k(1 + dN)` |
| **joint, sum clock, multi-index** `W_a` (**Lean route**) | `1 + Σᵢ yᵢ^N` | `1 + C(d+N, N)` | `k(N + 1)` |

The sum clock covers Thm 3.3, 3.4, 4.5 and 4.6 as written: "dimensional overhead polynomial in the
maximal monomial degree of p" holds for fixed `d` (`C(d+N, N) ≤ (N+1)^d`, degree `d` in `N`), and
for fixed `N` it is polynomial in `d` (degree `N`); it is not jointly polynomial
(`C(2N, N) ~ 4^N/√(πN)`), and it does not match the proof's linear count `k(n+1)`. The product
clock matches the linear count but has the additive exponent; it is also simpler to formalise (no
splitting lemma: `y^β/Π(1+yᵢ^N) = Πᵢ U_{i,βᵢ}`). The Lean development takes the **sum clock**; no
flaw was found in it. The product clock is a second instance of the same proof skeleton
(§1.4.3–1.4.5 unchanged; only `Φ`, the field and the identity change).

### 1.7 Errata in the printed proofs

| id | kind | locator | printed text | what fails | instance | repair | consumers |
|---|---|---|---|---|---|---|---|
| E1 | sign (the printed statement fails for odd `n`) | Constr. 3.1 Step 1, p. 6; Lemma 4.4, p. 10 | "n be the highest degree of f"; "U_{n,m} ∈ [0, 1]" | odd `n`: `1 + f^n = 0` possible; `U ≥ 0` needs `f ≥ 0` | `f′ = f − 2`, `f(0) = 0`, `n = 1`: `f = −1` at `t = ln 1.5` | even `N ≥ n`; `|U| ≤ 1` | Constr. 3.1, Prop 3.2, Lemma 4.4 |
| E2 | error in proof | Prop 3.2 proof, p. 7 | "If T* = ∞ […] then s(τ) ≤ τ → ∞" | upper bound, not divergence | — | `θ(t) ≥ t`, `s = θ⁻¹ → ∞` (§1.3.2) | Prop 3.2, Thm 3.3 |
| E3 | error in proof | Prop 3.2 proof, p. 7 | "f̄(τ) → ∞ […] forcing s′ → 0; […] the approach takes τ → ∞" | `∫₀^{T*} f^n` can be finite; `f` need not blow up | `g′ = g², f′ = fg/4`, `f(0) = g(0) = 1`, `N = 2`: `τ* = 3` | joint clock (§1.3.3) | Prop 3.2 (`T* < ∞`), Thm 3.4 |
| E4 | gap | Constr. 3.1 last paragraph, p. 7; Thm 4.5 "Termination", p. 10 | "apply the construction again […] repeat" | measure, choice of variables, output handling implicit | — | §1.3.4 (a)–(d), or joint clock | Thm 3.3, 4.5 |
| E5 | gap | Thm 3.4 proof, p. 8 | "s′(τ) = U_{n,0}(τ)" | after `k` steps `s′ = Π_j U^{(j)}_{n_j,0}`; global existence in `τ` assumed | (E3) | joint clock, `s′ = W₀` (§1.5) | Thm 3.4, [BAC] §3.2 |
| E6 | gap | Lemma 4.4 / Thm 4.5 proof, p. 10 | "Q^{(i+1)} := max(Q_t, Q_L)" | bound compounds per step (exponent `k Π(1+n_j+D_j)`); statement unaffected | — | composite bound `k(1+Σn_j)` or joint `k(N+1)` (§1.6) | Thm 4.5, 4.6 (exponent only) |
| E7 | gap | Lemma 4.3, Thm 4.5, p. 10 | "t_r is the physical time at which the output reaches precision r" | first hitting vs. Def 2.3 modulus | — | read as modulus (§1.6) | Thm 4.5, 4.6 |

The instances of E1 and E3 are closed-form and can be checked by hand (the derivatives and the
integral above); the joint-closure identity was also checked symbolically on 5 configurations
(§1.4.6).

Status: these errata are one reading of the printed proofs; E2, E3 and the derivative identity of
§1.4.4 have not yet been re-derived independently. The Lean proofs of Theorems 3.3, 3.4, 4.5 and
4.6 do not depend on them: they follow the joint route of §1.4.

## 3. Lean statements

The Lean source is authoritative; the statements below are copied from it.

The modules are `Ripple/Core/TimeChange.lean` (generic inverse time change),
`Ripple/Core/ArcLength.lean` (Lemma 4.1, Lemma 4.3), `Ripple/Core/SurrogateCompilation.lean`
(joint construction, Thm 3.3 core, Thm 4.5), `Ripple/Core/SurrogateCompilationBlowup.lean`
(`T* < ∞`, Thm 3.4), `Ripple/Core/Compilation.lean` (the statements `bounded_compilation`,
`bounded_compilation_polyTime`) and `Ripple/Core/SurrogateCompilationExamples.lean`
(non-vacuity examples).

### 3.1 The input notion and Thm 3.3

```lean
/-- [BAC] §2.3 (Bournez–Graça–Pouly convergence semantics): `α` is computed by a possibly
unbounded GPAC, i.e. by a ℚ-polynomial initial value problem (`PolyPIVP`) with a solution on
`[0, ∞)` whose output tends to `α`. No boundedness and no modulus. -/
def IsGPACComputable (α : ℝ) : Prop :=
  ∃ d : ℕ, ∃ P : PolyPIVP d, ∃ sol : PIVP.Solution P.toPIVP, P.toPIVP.Computes sol α

/-- [BAC] Thm 3.3 (bounded GPACs compute the same real numbers): a ℚ-PIVP with a solution on
`[0, ∞)` whose output converges to `α` yields a bounded ℚ-PIVP computing `α` with a time
modulus ([BAC] Def 2.1 + 2.3). The compiled system is `P.jointSurrogateCompile N` with
`N = 2 · max deg` (`bounded_compilation_certified`). -/
theorem bounded_compilation {d : ℕ} {α : ℝ} (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (hlim : Filter.Tendsto (fun t => sol.trajectory t P.output) Filter.atTop (nhds α)) :
    IsCRNComputable α

/-- [BAC] Thm 3.3 as an equality of classes: unboundedness does not enlarge the class of
GPAC-computable reals. -/
theorem isGPACComputable_iff_isCRNComputable (α : ℝ) :
    IsGPACComputable α ↔ IsCRNComputable α
```

### 3.2 The construction (exported, so that the dimension and the identities are inspectable)

```lean
/-- Multi-indices of total degree `≤ N` on `d` variables (BC.md §1.4.1). -/
abbrev SurrogateIndex (d N : ℕ) := {a : MIndex d N // a.degree ≤ N}

/-- Coordinates of the compiled system: `none` is the kept output (or the physical time in
`jointClockCompile`), `some a` the surrogate `W_a`. -/
abbrev CompiledIndex (d N : ℕ) := Option (SurrogateIndex d N)

/-- Dimension of the compiled system: one extra coordinate plus one surrogate per multi-index. -/
abbrev jointDim (d N : ℕ) : ℕ := Fintype.card (CompiledIndex d N)

/-- The joint clock `P(y) = 1 + Σᵢ yᵢ^N`, so that `dt/dτ = 1/P`. -/
noncomputable def jointClock (N : ℕ) (y : Fin d → ℝ) : ℝ := 1 + ∑ i, y i ^ N

/-- The surrogate `W_a(y) = y^a / P(y)`. -/
noncomputable def jointSurrogate (N : ℕ) (a : SurrogateIndex d N) (y : Fin d → ℝ) : ℝ :=
  a.1.eval y / jointClock N y

/-- [BAC] Construction 3.1, joint form (BC.md §1.4.1): the bounded surrogate compilation of `P`
with the kept output. ℚ-polynomial field (cubic in the surrogates), rational initial value
`(y₀,o, (y₀^a / P(y₀))_a)`, output the kept copy of `P`'s output. -/
noncomputable def PolyPIVP.jointSurrogateCompile (P : PolyPIVP d) (N : ℕ) :
    PolyPIVP (jointDim d N)

/-- The coordinate of the surrogate `W_a` in the compiled system. -/
noncomputable def surrogateCoord {N : ℕ} (a : SurrogateIndex d N) : Fin (jointDim d N)

theorem jointSurrogate_abs_le_one {N : ℕ} (hN : Even N) (a : SurrogateIndex d N)
    (y : Fin d → ℝ) : |jointSurrogate N a y| ≤ 1

/-- [BAC] Construction 3.1 + Prop 3.2 (`T* = ∞`), joint form (BC.md §1.4.3–1.4.4): the
compiled system has the solution `τ ↦ (y_o(s τ), (W_a(y(s τ)))_a)` on `[0, ∞)`, where `s`
inverts the clock `θ(t) = ∫₀ᵗ P(y)`; `s(0) = 0`, `s` is strictly increasing and `s → ∞`. -/
theorem PolyPIVP.jointSurrogateCompile_solution (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (sol : PIVP.Solution P.toPIVP) :
    ∃ (sol' : PIVP.Solution (P.jointSurrogateCompile N).toPIVP) (s : ℝ → ℝ),
      Continuous sol'.trajectory ∧ s 0 = 0 ∧ StrictMono s ∧
      Tendsto s atTop atTop ∧
      (∀ t, 0 ≤ t → s (∫ u in (0 : ℝ)..t, jointClock N (sol.trajectory u)) = t) ∧
      (∀ τ, 0 ≤ τ → sol'.trajectory τ (P.jointSurrogateCompile N).output
          = sol.trajectory (s τ) P.output) ∧
      (∀ τ, 0 ≤ τ → ∀ a : SurrogateIndex d N,
          sol'.trajectory τ (surrogateCoord a) = jointSurrogate N a (sol.trajectory (s τ)))

/-- [BAC] Thm 4.5, dimension clause: the compiled dimension is polynomial in `N` for fixed `d`
(the count is `1 + C(d+N, N)`, which is not proved here; the bound is what the theorem
needs). -/
theorem jointDim_le (d N : ℕ) : jointDim d N ≤ 1 + (N + 1) ^ d

/-- [BAC] Thm 3.3 in certified form: the compiled system is `P.jointSurrogateCompile N`. -/
theorem bounded_compilation_certified {α : ℝ} (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (sol : PIVP.Solution P.toPIVP)
    (hlim : Tendsto (fun t => sol.trajectory t P.output) atTop (nhds α)) :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim d N) α,
      btc.pivp = P.jointSurrogateCompile N
```

`|W_a| ≤ 1` follows from `jointSurrogate_abs_le_one`. The clause `s (∫₀ᵗ P) = t` pins `s` to
the paper's clock (so the time bound of §3.4 is about this `s`, not an arbitrary one); `t ≥ 0`
keeps the integral on the part where `sol` is a solution.

### 3.3 Arc length, Lemma 4.1, Lemma 4.3

```lean
/-- Trajectory (arc) length `L(t) = ∫₀ᵗ ‖p(y(u))‖ du` ([BAC] §2.3, Bournez–Graça–Pouly),
with the sup norm of `Fin d → ℝ`. -/
noncomputable def PolyPIVP.arcLength (P : PolyPIVP d) (y : ℝ → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, ‖P.evalField (y u)‖

/-- [BAC] Lemma 4.1 (one-sided bound): on a bounded trajectory, `L(t) ≤ v_max t`. -/
theorem PolyPIVP.arcLength_le_of_bounded (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (hbd : P.toPIVP.IsBounded sol.trajectory) :
    ∃ v : ℝ, 0 ≤ v ∧ ∀ t, 0 ≤ t → P.arcLength sol.trajectory t ≤ v * t

/-- [BAC] Lemma 4.3: every coordinate moves at most the arc length. -/
theorem PolyPIVP.abs_sub_init_le_arcLength (P : PolyPIVP d) (sol : PIVP.Solution P.toPIVP)
    (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    |sol.trajectory t i - (P.init i : ℝ)| ≤ P.arcLength sol.trajectory t
```

### 3.4 Thm 4.5 + Thm 4.6

```lean
/-- [BAC] Thm 4.6 (from BGP poly length to bounded poly time), via Thm 4.5 in its joint form
(`bounded_compilation_polyTime_certified`, BC.md §1.6): if the output is `e^{-r}`-close after
`μ r`, with `μ r` and the trajectory length `L(μ r)` at most `C (r+1)^k`, then `α` is computed
by a bounded ℚ-PIVP with time modulus `O((r+1)^{k(N+1)})`, for any even `N` at least the degree
of the field. -/
theorem bounded_compilation_polyTime {d : ℕ} {α : ℝ} (P : PolyPIVP d)
    (sol : PIVP.Solution P.toPIVP) (μ : TimeModulus) (k : ℕ) (C : ℝ)
    (hconv : ∀ r : ℕ, ∀ t : ℝ, t > μ r →
      |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ)))
    (hμ : ∀ r : ℕ, 0 ≤ μ r ∧ μ r ≤ C * ((r : ℝ) + 1) ^ k)
    (hL : ∀ r : ℕ, P.arcLength sol.trajectory (μ r) ≤ C * ((r : ℝ) + 1) ^ k)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    IsPolyTimeComputable α (k * (N + 1))
```

The certified form carries all three clauses of Thm 4.5 — the compiled system,
its polynomial time modulus, its arc length `≤ v τ` (Lemma 4.1 on the compiled system) — and the
dimension clause is `jointDim_le`; `bounded_compilation_polyTime` is its corollary (Thm 4.6):

```lean
/-- [BAC] Thm 4.5 (iterative bounded compilation), joint form, BC.md §1.6: if the output is
`e^{-r}`-close after `μ r`, with `μ r` and the arc length `L(μ r)` at most `C (r+1)^k`, then the
bounded compiled system `P.jointSurrogateCompile N` computes `α` with a time modulus at most
`C' (r+1)^{k(N+1)}` (the clock `θ(μ r) = ∫₀^{μ r} P(y)`), and its own trajectory length grows at
most linearly ([BAC] Lemma 4.1), hence polynomially at the precision-`r` time. The dimension
clause of Thm 4.5 is `jointDim_le`. -/
theorem bounded_compilation_polyTime_certified {α : ℝ} (P : PolyPIVP d)
    (sol : PIVP.Solution P.toPIVP) (μ : TimeModulus) (k : ℕ) (C : ℝ)
    (hconv : ∀ r : ℕ, ∀ t : ℝ, t > μ r →
      |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ)))
    (hμ : ∀ r : ℕ, 0 ≤ μ r ∧ μ r ≤ C * ((r : ℝ) + 1) ^ k)
    (hL : ∀ r : ℕ, P.arcLength sol.trajectory (μ r) ≤ C * ((r : ℝ) + 1) ^ k)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim d N) α,
      btc.pivp = P.jointSurrogateCompile N ∧
      (∃ C' : ℝ, 0 < C' ∧ ∀ r : ℕ, btc.modulus r ≤ C' * ((r : ℝ) + 1) ^ (k * (N + 1))) ∧
      (∃ v : ℝ, 0 ≤ v ∧ ∀ τ, 0 ≤ τ → btc.pivp.arcLength btc.sol.trajectory τ ≤ v * τ)
```

### 3.5 Finite blow-up: Prop 3.2 (`T* < ∞`) and Thm 3.4

```lean
/-- Compiled system without the kept output: state `(s, (W_a)_a)`, `s' = W₀`, `s(0) = 0`,
output `s`. -/
noncomputable def PolyPIVP.jointClockCompile (P : PolyPIVP d) (N : ℕ) :
    PolyPIVP (jointDim d N)

/-- [BAC] Prop 3.2 for `T* < ∞` (repaired, BC.md §1.3.3, §1.5): a solution on `[0, T)` that is
unbounded there (so `T` is its maximal existence time) and whose output tends to `α` as
`t → T⁻` yields a bounded computation of `α`. -/
theorem bounded_compilation_of_blowup {α T : ℝ} (P : PolyPIVP d)
    (y : ℝ → Fin d → ℝ) (hy0 : y 0 = fun i => (P.init i : ℝ))
    (hy : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t)
    (hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 T))
    (hlim : Tendsto (fun t => y t P.output) (nhdsWithin T (Set.Iio T)) (nhds α)) :
    IsCRNComputable α

/-- [BAC] Thm 3.4 (poles of GPAC-implementable functions are computable; repaired, BC.md
§1.5): the blow-up time of a ℚ-PIVP is computed by a bounded ℚ-PIVP (output `s`, `s' = W₀`). -/
theorem isCRNComputable_blowupTime {T : ℝ} (P : PolyPIVP d)
    (y : ℝ → Fin d → ℝ) (hy0 : y 0 = fun i => (P.init i : ℝ))
    (hy : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t)
    (hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 T)) :
    IsCRNComputable T
```

The certified forms `bounded_compilation_of_blowup_certified` (compiled system
`P.jointSurrogateCompile N`) and `isCRNComputable_blowupTime_certified` (compiled system
`P.jointClockCompile N`) take `{N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N)` in
addition and conclude `∃ btc : CertifiedBoundedTimeComputable (jointDim d N) _, btc.pivp = _`.

`hunb` is the faithful form of "finite maximal existence time" (for a locally Lipschitz field, a
solution on `[0, T)` with `T < ∞` is maximal iff it is unbounded); no maximal-solution theory is
needed.

### 3.6 Non-vacuity examples

`IsCRNComputable (π/2)` and `IsPolyTimeComputable 1 3` already follow from
`pi_is_realtime` and `realtime_rat_const`, so the examples are stated as **instances of the
hypotheses** on a genuinely unbounded input, plus the compiled certificate pinned to the
construction:

```lean
/-- `t' = 1, u' = -2 t u², x' = u`, `(t,u,x)(0) = (0,1,0)`, output `x`. -/
noncomputable def arctanSys : PolyPIVP 3

/-- The hypotheses of `bounded_compilation` hold for `arctanSys` on an unbounded solution. -/
theorem arctanSys_instance :
    (∀ i, (arctanSys.field i).totalDegree ≤ 4) ∧
    ∃ sol : PIVP.Solution arctanSys.toPIVP,
      arctanSys.toPIVP.Computes sol (Real.pi / 2) ∧
      ¬ arctanSys.toPIVP.IsBounded sol.trajectory

/-- The compiled bounded certificate for `π/2`, pinned to the joint construction. -/
theorem arctanSys_compiled :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim 3 4) (Real.pi / 2),
      btc.pivp = arctanSys.jointSurrogateCompile 4

/-- `t' = 1, x' = 2t(1 - x)`, `(t,x)(0) = (0,0)`; solution `(t, 1 - e^{-t²})`. -/
noncomputable def gaussianSys : PolyPIVP 2

/-- The hypotheses of `bounded_compilation_polyTime` (`k = 1`, `C = 1`, `N = 2`) hold for
`gaussianSys` on an unbounded solution. -/
theorem gaussianSys_instance :
    (∀ i, (gaussianSys.field i).totalDegree ≤ 2) ∧
    ∃ (sol : PIVP.Solution gaussianSys.toPIVP) (μ : TimeModulus),
      (∀ r : ℕ, ∀ t : ℝ, t > μ r →
        |sol.trajectory t gaussianSys.output - 1| < Real.exp (-(r : ℝ))) ∧
      (∀ r : ℕ, 0 ≤ μ r ∧ μ r ≤ 1 * ((r : ℝ) + 1) ^ 1) ∧
      (∀ r : ℕ, gaussianSys.arcLength sol.trajectory (μ r) ≤ 1 * ((r : ℝ) + 1) ^ 1) ∧
      ¬ gaussianSys.toPIVP.IsBounded sol.trajectory

theorem gaussianSys_compiled :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim 2 2) 1,
      btc.pivp = gaussianSys.jointSurrogateCompile 2 ∧
      ∃ C' : ℝ, 0 < C' ∧ ∀ r : ℕ, btc.modulus r ≤ C' * ((r : ℝ) + 1) ^ 3

/-- `u' = 1 + u², t' = 1`, `(u,t)(0) = (0,0)`, output `t`; solution `(tan t, t)` on `[0, π/2)`. -/
noncomputable def tanSys : PolyPIVP 2

theorem tanSys_instance :
    (∀ i, (tanSys.field i).totalDegree ≤ 2) ∧
    tanTraj 0 = (fun i => (tanSys.init i : ℝ)) ∧
    (∀ t ∈ Set.Ico 0 (Real.pi / 2), HasDerivAt tanTraj (tanSys.evalField (tanTraj t)) t) ∧
    ¬ BddAbove ((fun t => ‖tanTraj t‖) '' Set.Ico 0 (Real.pi / 2)) ∧
    Tendsto (fun t => tanTraj t tanSys.output)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (Real.pi / 2))

/-- [BAC] Prop 3.2 at a finite blow-up, pinned to `jointSurrogateCompile 2`. -/
theorem tanSys_compiled_limit :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim 2 2) (Real.pi / 2),
      btc.pivp = tanSys.jointSurrogateCompile 2

/-- [BAC] Thm 3.4, pinned to `jointClockCompile 2` (output the clock `s`, no original
coordinate kept). -/
theorem tanSys_compiled_blowupTime :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim 2 2) (Real.pi / 2),
      btc.pivp = tanSys.jointClockCompile 2
```

Here `tanTraj t = ![Real.tan t, t]`. Each example's docstring states which hypothesis is
genuinely exercised (an unbounded coordinate, a finite blow-up). The `arctan` system has
degree 3 (`t u²`), so `N = 4`, `|A| = C(7, 4) = 35`, dimension 36.
