# Repairs to the [BAC] journal draft used by the Lean formalization

Draft: the journal version of [BAC], in preparation (revision `e4f89de5`). Labels are the LaTeX `\label`s.
Status labels: OPEN (written, not reviewed), REVIEWED (independent review recorded below), SIGNED (cleared
for Lean).

The other results formalized together with these (`lem:closure`, the dimension count, `prop:bc-implies-bd`,
`thm:poly-equiv`, `def:bounded-function`, `rmk:shifted-clock`, the function part of
`thm:compilation`) needed no repair.

## §6. Closure under exponentiation (`thm:power`, `con:power`, `thm:power-complexity`)

### 6.0 Findings

**E6.1 (proof of `thm:power`, "Well-definedness"): the claim `1 + x₁(t) > 0` for all `t ≥ 0` is
false for a general upstream system.** With `x₁' = (x − 1) − x₁`, `x₁(0) = 0`,
`w = 1 + x₁` satisfies `w' = x − w`, `w(0) = 1`, so
`w(t) = e^{−t} + ∫₀ᵗ e^{−(t−s)} x(s) ds`. The draft's argument for `t ∈ [0, T₀]` when
`min x < 0` is not a proof. Counterexample: the bounded ℚ-PIVP `x' = 2 − x`, `x(0) = −11`
(solution `x(s) = 2 − 13 e^{−s} ∈ [−11, 2]`, `x → 2 = α > 0`) gives
`w(t) = e^{−t} + 2(1 − e^{−t}) − 13 t e^{−t}`, and `w(0.5) ≈ 0.607 + 0.787 − 3.942 < 0`. When `w`
reaches `0`, `v = 1 − 1/w` and `u = ln w` are undefined; in the polynomial system,
`(1 − v)' = −(1 − v)² x₁'` gives `1/(1 − v) = w`, so `v` blows up at the first zero of `w` and
the compiled system has no global solution. The draft's bound for `t ≥ T₀` fails as
well: it drops `∫₀^{T₀} e^{−(t−s)} x(s) ds`, which is negative when `min x < 0` (independent review,
finding 3). The theorem's statement is unaffected; the construction needs a nonnegative driving
signal.

**E6.2 (`thm:power-complexity`): the modulus `max(μ_α(r + C), μ_β(r + C)) + O(1)` is false.**
Counterexample: `α = 2`, `β = 1/2`, upstream `x' = 0`, `x(0) = 2` and `y' = 0`, `y(0) = 1/2`,
both with modulus `μ ≡ 0` (every `t > 0` is exact). The theorem would give a bounded ℚ-PIVP
computing `√2` with `μ(r) ≤ c` for all `r`, so its output equals `√2` on `(c, ∞)`. Solutions of
polynomial ODEs are real-analytic, so the output is `√2` on `[0, ∞)`, and its initial value
`√2` is not rational. For the construction itself the loss is visible directly: with `x ≡ α`,
`w(t) − α = (1 − α) e^{−t}`, so for `α ≠ 1`, `β ≠ 0` the modulus of the gadget is at least
`r − O(1)`. The low-pass
filter forgets its initial error at rate `1`, which costs an additive `r`, not `O(1)`; the
proof's Step 1 bound `|e₁(t)| ≤ e^{−t}|α − 1| + ∫₀ᵗ e^{−(t−s)} ε_α(s) ds` is right, but
"inherits the decay profile" (via `lem:input-limited`, an asymptotic statement under extra
smoothness hypotheses) does not give `+O(1)`: that lemma assumes `ε ∈ C¹`, `ε' → 0` and decay slower than `e^{−t}`
(`e^{t}|ε(t)| → ∞`), and concludes `δ ∼ ε`, an asymptotic statement, not a modulus bound. The corrected bound (6.4 below) is
`max(μ_α(r + C), μ_β(r + C)) + r + C`. The conclusion "exponentiation preserves the time
complexity class" holds for every class closed under `μ ↦ μ + O(r)`, in particular for
`Θ(r^n)`, `n ≥ 1`, and all classes of §5.

**E6.3 (`thm:power-complexity`): `C` depends on the upstream systems, not only on `α, β`.** The
proof uses `α_min = min_t (1 + x₁(t))` and bounds of `y`; these depend on the upstream
trajectories.

**E6.4 (proof of `thm:power`): boundedness of the constructed system is not argued.** A bounded
GPAC needs all of `x₁, u, v, z` bounded; this needs a uniform lower bound
`inf_{t ≥ 0} (1 + x₁(t)) > 0`, which the draft's positivity argument does not give either.

### 6.1 Repaired construction (`con:power`, squared driving signal)

Let `X' = F(X)` (dimension `d₁`, output `x`) and `Y' = H(Y)` (dimension `d₂`, output `y`) be
bounded ℚ-PIVPs with `x(t) → α > 0`, `y(t) → β`, bounds `|x(t)| ≤ B_x`, `|y(t)| ≤ B_y` on
`[0, ∞)`, and write `y' = H_y(Y)` for the output component of `H` (a polynomial in `Y`). The
repaired system drives the filter with `x² ≥ 0` and halves the exponent:

    x₁' = (x² − 1) − x₁,
    u'  = (1 − v) x₁',
    v'  = (1 − v)² x₁',
    z'  = ½ z (H_y(Y) u + y (1 − v) x₁'),

`x₁(0) = u(0) = v(0) = 0`, `z(0) = 1`; output `z`. All right-hand sides are ℚ-polynomials in
`(X, Y, x₁, u, v, z)` (substitute `x₁'` by its polynomial). Dimension `d₁ + d₂ + 4`.

When the upstream output is nonnegative (`x(t) ≥ 0` for all `t`; for instance a CRN species),
the draft's Construction 6.2 with `x` itself works by the same proof with `x` in place of `x²`,
`α` in place of `α²`, and without the factor `½` (`w_min = min(α/2, e^{−T₀})`, `U → ln α`). Whether the draft's figure
(upstream `π/4`, `e`, `π` systems of [RTCRN2]) falls under this case depends on those upstream
outputs being nonnegative; not checked.

### 6.2 Lemma (explicit solution)

Let `w(t) = 1 + x₁(t)` where `x₁` solves `x₁' = (x² − 1) − x₁`, `x₁(0) = 0` (a linear ODE with
continuous coefficient, global solution). Then
1. `w(t) = e^{−t} + ∫₀ᵗ e^{−(t−s)} x(s)² ds ≥ e^{−t} > 0` (integrating factor; the integrand
   is `≥ 0`).
2. `U = ln w`, `V = 1 − 1/w`, `Z = exp(½ y U)` satisfy the `u, v, z` equations with the stated
   initial values: `U' = w'/w = x₁'(1 − V)`; `V' = w'/w² = (1 − V)² x₁'`;
   `Z' = Z · ½ (y' U + y U') = ½ Z (H_y(Y) U + y (1 − V) x₁')`; `U(0) = ln 1 = 0`,
   `V(0) = 0`, `Z(0) = exp(0) = 1`. Hence `(X, Y, x₁, U, V, Z)` is a solution of the combined
   system on `[0, ∞)` (and the solution, by uniqueness for polynomial fields).

### 6.3 Theorem (`thm:power`, repaired proof)

*Claim.* The combined system is bounded and its output tends to `α^β`.

*Proof.* (a) Upper bound: `w' = x² − w ≤ B_x² − w`, `w(0) = 1`, so `w ≤ max(1, B_x²) =: w_max`.
(b) Convergence of `w`: `w − α² = e^{−t}(1 − α²) + ∫₀ᵗ e^{−(t−s)} (x(s)² − α²) ds`; with
`g = x² − α² → 0` and `|g| ≤ G := B_x² + α²`, for `T ≤ t`:
`|∫₀ᵗ e^{−(t−s)} g| ≤ G e^{−(t−T)} + sup_{s ≥ T} |g(s)|`, so `w → α²`.
(c) Uniform lower bound: choose `T₀` with `w ≥ α²/2` on `[T₀, ∞)` (by (b)); on `[0, T₀]`,
`w ≥ e^{−T₀}` (6.2.1). So `w ≥ w_min := min(α²/2, e^{−T₀}) > 0` on `[0, ∞)`, and
`α² ≥ w_min` (limit of values `≥ w_min`). An effective choice (independent review, finding 6): take
`ρ₀ ∈ ℕ` with `A₁ e^{−ρ₀} ≤ α²/2` (`A₁` of 6.4 does not involve `w_min`) and
`T₀ = max(μ_α(ρ₀), 0) + ρ₀`; then 6.4 step 1 gives `|w − α²| ≤ α²/2` on `(T₀, ∞)`.
(d) Bounds: `|x₁| ≤ w_max + 1`; `|U| ≤ L_U := max(|ln w_min|, |ln w_max|)`;
`|V| ≤ 1 + 1/w_min`; `0 < Z ≤ exp(½ B_y L_U)`. With the bounded upstream states the combined
state is bounded.
(e) Limit: `U → ln α² = 2 ln α` (continuity of `ln` at `α² > 0`), `½ y U → β ln α`, and
`Z = exp(½ y U) → exp(β ln α) = α^β`. ∎

### 6.4 Theorem (`thm:power-complexity`, corrected)

*Claim.* Let `μ_α`, `μ_β` be time moduli of the upstream outputs (`|x(t) − α| < e^{−r}` for
`t > μ_α(r)`, the same for `y`; moduli are real-valued, possibly negative, as in Lean's
`TimeModulus := ℕ → ℝ`). There is a constant `C ∈ ℕ`, depending on `α`, `β` and the upstream
systems (through `B_x`, `B_y`, `w_min`; with the effective `w_min` of 6.3(c), through `B_x`,
`B_y`, `μ_α`), such that the output of 6.1 satisfies `|z(t) − α^β| < e^{−r}` whenever
`t > max(max(μ_α(r + C), 0) + r + C, μ_β(r + C))`. For a modulus with values in `[0, ∞)` (the
draft's definition) this is `max(μ_α(r + C) + r + C, μ_β(r + C)) ≤
max(μ_α(r + C), μ_β(r + C)) + r + C`.

*Proof.* Put `ρ = r + C` with `C` fixed below, `T = max(μ_α(ρ), 0)`, and take `t > T + ρ`,
`t > μ_β(ρ)`.
1. *Filter.* For `s > T`, `|x(s)² − α²| ≤ (|x(s)| + α)|x(s) − α| ≤ (B_x + α) e^{−ρ}`. Splitting
   the integral of 6.3(b) at `T`:
   `|w(t) − α²| ≤ e^{−t}|1 − α²| + G e^{−(t−T)} + (B_x + α) e^{−ρ}`
   `≤ (|1 − α²| + G) e^{−(t−T)} + (B_x + α) e^{−ρ} ≤ A₁ e^{−ρ}`,
   with `A₁ = |1 − α²| + G + B_x + α`, since `t − T > ρ` and `e^{−t} ≤ e^{−(t−T)}`.
2. *Logarithm.* `w(t), α² ≥ w_min`, so by the mean value theorem
   `|U(t) − 2 ln α| ≤ |w(t) − α²| / w_min ≤ (A₁ / w_min) e^{−ρ}`.
3. *Exponent.* `R = ½ y U`, `R* = β ln α`:
   `|R − R*| ≤ ½ |y| |U − 2 ln α| + |ln α| |y − β| ≤ (½ B_y A₁ / w_min + |ln α|) e^{−ρ}`,
   using `|y(t) − β| < e^{−ρ}` for `t > μ_β(ρ)`.
4. *Output.* `|R|, |R*| ≤ L_R := max(½ B_y L_U, |β ln α|)`, so
   `|Z − α^β| = |e^R − e^{R*}| ≤ e^{L_R} |R − R*| ≤ A e^{−ρ}` with
   `A = e^{L_R}(½ B_y A₁ / w_min + |ln α|)`.
   Choose `C = ⌈max(0, ln A)⌉ + 1 ∈ ℕ`: then `A e^{−ρ} = A e^{−C} e^{−r} ≤ e^{−1} e^{−r} <
   e^{−r}`. ∎

*Remark (sharpness of the additive `r`).* By E6.2 the additive term cannot be `O(1)` in
general; for classes `μ(r) ≥ c·r` (real time and above) the bound is `O(max(μ_α, μ_β)(r + C))`.

### 6.5 Corollary (`cor:crn-power`)

Unchanged in substance, applied to 6.1: the right-hand side of `z'` has the factor `z`, so `z`
needs no dual rail; `x₁, u, v` may be negative and are dual-railed. Dual-railing `x₁, u, v` adds
annihilation terms, so neither 6.3 nor 6.4 transfers to the CRN for free: no time modulus is
claimed for the CRN until §7 provides one. The Lean formalization of the CRN implementation
belongs to §7.

### 6.6 Lean prerequisites (independent review, finding 8)

- `y` is a coordinate of `Y`, so `y'(t) = H_y(Y(t))` along the actual trajectory.
- The combined solution is built explicitly from the upstream solutions and the witnesses of 6.2
  (no uniqueness argument is needed for existence; the Lean certificate carries this solution).
- `α^β` is `Real.rpow α β = exp(log α · β)` for `α > 0`.
- `B_x`, `B_y` come from `PIVP.IsBounded` (sup norm bounds coordinates).
- The modulus of 6.4 is real-valued; no nonnegativity is needed in `CertifiedBoundedTimeComputable`.

### 6.7 Review

Independent review (2026-11-08): **ACCEPT WITH FIXES**. Checked: both counterexamples
(E6.1: `w(0.5) = −2.549`, first zero near `t ≈ 0.092`; E6.2 via analyticity), 6.1–6.4 step by
step, edge cases `α = 1`, `β = 0`, negative `β`. Findings 1 (integral `C`), 2 (threshold with
negative moduli), 3 (both halves of the draft's positivity argument fail), 4 (qualifier
`α ≠ 1, β ≠ 0`), 5 (hypotheses of `lem:input-limited`), 6 (effective `w_min`, rename `T₀`),
7 (dependencies), 8 (Lean prerequisites), 9 (no CRN modulus claimed), 10 (nonnegative case) are
applied above. Status of §6: **SIGNED** for Lean (6.1 construction, 6.3 theorem, 6.4 corrected
complexity theorem).

## §7. CRN readout (`lem:input-limited`, `lem:module-limited`, `thm:crn-preserves`, `cor:crn-realizable`)

Status: repair written (7.1-7.7), independent review ACCEPT WITH FIXES, fixes applied (7.8): **SIGNED** for Lean.

### 7.0 Findings (first read, 2026-11-08)

**E7.1 (§7.2, `eq:aj-linear`): the error analysis is for the linearization, not for the module.**
The Anderson–Joshi readout is `Ż = x₁(t) Z − Z²`; with `x₁ = α + ε`, `Z = α + δ` the exact error
equation is `δ' = −α δ + α ε + ε δ − δ²`, not `δ' + α δ = α ε`. Lemmas 7.1 and 7.2 are stated
for the linear equation; Thm 7.3 applies them to the module without bounding the quadratic terms
(and without `Z(0) > 0`, needed so that `Z` stays positive and does not converge to `0`).

**E7.2 (`thm:crn-preserves` (1)): "`μ_Z(r) = μ(r) + O(1)`" does not follow.** A time modulus is an upper bound; Lemma 7.1 needs pointwise hypotheses on `ε`
(`C¹`, `ε' → 0`, `e^{αt}|ε(t)| → ∞`) that a modulus does not give, and `δ ∼ ε` gives
`|δ| ≤ 2|ε|` eventually, i.e. a shift in precision (`μ_Z(r) ≤ μ(r + 1)` for large `r`), not
`+O(1)` in time: for `μ(r) = r^n`, `μ(r + 1) − μ(r) ≍ n r^{n−1}`. So "`+O(1)`" is not proved
(no counterexample generated by a bounded GPAC is claimed here; the repair 7.4 does not depend on
one).

**E7.3 (`thm:crn-preserves` (2), double inversion):** "the same argument applies with `α`
replaced by `min(α, 1/α)`" is not argued (a cascade of two nonlinear modules).

**E7.4 (`lem:input-limited`): the lemma is false as stated, and the proof shows only
`δ − ε → 0`.** The hypotheses (`ε ∈ C¹`, `ε → 0`, `ε' → 0`, `e^{αt}|ε| → ∞`) hold for
`ε(t) = (2 + sin t)/(t + 1)`, but for the linear equation `δ' + αδ = αε` the filter attenuates
and delays the oscillation: with `α = 1`, `δ(0) = 0` (RK4, step `10⁻³`), `δ(t)/ε(t)` oscillates
between about `0.73` and `1.61` for `t ∈ [390, 400]` (asymptotic ratio
`(2 + sin(t − π/4)/√2)/(2 + sin t) ∈ [0.726, 1.608]`; the nonlinear AJ module gives the same range), so `δ ≁ ε`. The proof bounds the remainder
`∫₀ᵗ e^{−α(t−s)} ε'(s) ds` by `o(1)`, while `δ ∼ ε` needs `o(ε(t))`. Repair: assume
`ε(t) ≠ 0` for large `t` and `ε'(t)/ε(t) → 0` (this implies `e^{αt}|ε(t)| → ∞`); see 7.6.

**E7.5 (`thm:crn-preserves` (2)): "`μ_Z(r) = r/α + O(1)`" is false at the boundary and for
`μ(r) = c r` with `c > 1/α`.** For `ε(t) = e^{−αt}` the linear filter gives
`δ(t) = (δ(0) + αt) e^{−αt}` (the proof of Cor 7.4 says so itself), so `μ_Z(r) = r/α + log r/α + O(1)`;
for `ε(t) = e^{−αt/2}` (`μ(r) = 2r/α = O(r/α)`) the output error is `≍ e^{−αt/2}` and
`μ_Z(r) ≈ 2r/α`. The same holds for the AJ module: with `δ = u e^{−αt}`, `u' = α + (ε − δ)u`;
since `δ → 0` exponentially (7.4), `∫|ε − δ| < ∞`, so Grönwall gives `u = O(t)` and then
`u = αt + O(1)` (numerically `(Z − α)e^{αt} − αt ≈ −0.79` for `α = 1`). The corrected statement 7.4
covers both cases with one bound.

### 7.1 Setting

`α > 0`. The input is a continuous `x : [0, ∞) → ℝ` with a modulus `μ : ℕ → ℝ`:
`|x(t) − α| < e^{−r}` for all `t > μ(r)`. Put `X(t) = ∫₀ᵗ x`, fix `r₀ ∈ ℕ` with
`e^{−r₀} ≤ α/2` and `T₀ = max(μ(r₀), 0)`; then `x(t) ≥ α/2` for `t > T₀`.

**Comparison lemma.** If `V` is continuous on `[T, t]`, differentiable on `(T, t)` with
`V' ≤ −aV + b` there (`a > 0`), then `V(t) ≤ b/a + (V(T) − b/a) e^{−a(t−T)}`. Proof: the
derivative of `e^{as}(V(s) − b/a)` is `e^{as}(V' + aV − b) ≤ 0`, so it is antitone on `[T, t]`.

### 7.2 Lemma (linear inversion; the reciprocal module `q' = 1 − x q`)

For `q₀ ∈ ℝ` let `q(t) = e^{−X(t)} (q₀ + ∫₀ᵗ e^{X(s)} ds)`. Then:

(a) `q(0) = q₀` and `q' = 1 − x q` on `[0, ∞)` (product rule and the fundamental theorem of
calculus, `x` continuous).

(b) Let `e = q − 1/α` and `K = e(T₀)² + 1/α²`. Then `e(t)² ≤ K` for `t ≥ T₀`.

(c) Let `k ∈ ℕ` with `e^{2k} ≥ 8/α⁴`, and `C_q = (2/α) max(log(2K), 0)`. For every `r ∈ ℕ`,
`|q(t) − 1/α| < e^{−r}` for all `t > max(μ(r + k), T₀) + (4/α) r + C_q`.

(d) If `q₀ ≥ 0` then `q(t) ≥ 0` on `[0, ∞)`; if `q₀ > 0` then `q > 0`.

*Proof.* (a) is direct. For the rest, `e' = 1 − x(e + 1/α) = −x e − (x − α)/α`, so for `V = e²`
and `s > T₀` with `|x(s) − α| ≤ η`:
`V' = −2x e² − 2e(x − α)/α ≤ −α e² + 2|e| η/α ≤ −(α/2) V + 2η²/α³`,
using `x ≥ α/2` and `2|e|η/α ≤ (α/2)e² + 2η²/α³` (a square). By the comparison lemma with
`a = α/2`, `b = 2η²/α³`, `b/a = 4η²/α⁴`:
(b) with `η = α/2` on `(T₀, ∞)`: `V(t) ≤ 1/α² + V(T₀) = K`.
(c) on `(T₁, ∞)`, `T₁ = max(μ(r + k), T₀)`, `η = e^{−(r+k)}`:
`V(t) ≤ 4e^{−2(r+k)}/α⁴ + V(T₁) e^{−(α/2)(t − T₁)} ≤ e^{−2r}/2 + K e^{−(α/2)(t−T₁)}`,
and `K e^{−(α/2)(t−T₁)} < e^{−2r}/2` as soon as `t − T₁ > (2/α)(2r + log(2K))`, in particular for
`t − T₁ > (4/α) r + C_q`. So `V(t) < e^{−2r}`.
(d) `e^{−X(t)} > 0` and `∫₀ᵗ e^{X} ≥ 0` for `t ≥ 0`. ∎

No bound on `x` is used. The rate `4/α` is not sharp (the linearization suggests `1/α`); it is
enough for every class below.

### 7.3 Lemma (lower bound for the Anderson–Joshi denominator)

If moreover `|x(t)| ≤ B` on `[0, ∞)` with `B > 0` and `q₀ = 1`, then
`q(t) = e^{−X(t)} + ∫₀ᵗ e^{−(X(t) − X(s))} ds ≥ e^{−Bt} + (1 − e^{−Bt})/B ≥ m := min(1, 1/B)`
for `t ≥ 0` (since `|X(t) − X(s)| ≤ B(t − s)`; the middle expression is a convex combination of
`1` and `1/B`).

### 7.4 Theorem (`thm:crn-preserves`, corrected)

Let `x` be as in 7.1 with `|x| ≤ B` on `[0, ∞)`.

**(AJ)** `Z = 1/q` with `q₀ = 1` solves `Ż = xZ − Z²`, `Z(0) = 1`, on `[0, ∞)`, and
`0 < Z ≤ 1/m = max(1, B)`. With `j ∈ ℕ`, `e^{j} ≥ α/m`, and `k, T₀, C_q` from 7.2:
`|Z(t) − α| < e^{−r}` for `t > max(μ(r + j + k), T₀) + (4/α)(r + j) + C_q`.
*Proof.* `Ż = −q'/q² = (xq − 1)/q² = xZ − Z²`. `|Z − α| = α|q − 1/α|/q ≤ (α/m)|q − 1/α|`;
apply 7.2(c) at precision `r + j`. ∎

**(Double inversion)** `Y = q` with `q₀ = 0` solves `Ẏ = 1 − xY`, `Y(0) = 0`, `Y ≥ 0`, and by
7.2(c) `|Y − 1/α| < e^{−r}` for `t > μ_Y(r) := max(μ(r + k), T₀) + (4/α) r + C_q`. `Y` is
bounded on `[0, ∞)` (by `1/α + √K` on `[T₀, ∞)`, by continuity on `[0, T₀]`). Applying 7.2 to the
input `Y` (target `1/α`, modulus `μ_Y`) with `q₀ = 0` gives `Z` with `Ż = 1 − YZ`, `Z(0) = 0`,
`Z ≥ 0`, bounded, and `|Z − α| < e^{−r}` for `t > max(μ_Y(r + k'), T₀') + 4α r + C'`.

In both cases there are `k_Z ∈ ℕ` and `C ∈ ℝ` (depending on `α`, `μ`, `B` and the upstream
solution) with
`μ_Z(r) ≤ max(μ(r + k_Z), 0) + c·r + C` for all `r`, where
AJ: `c = 4/α`, `k_Z = j + k`, `C = T₀ + 4j/α + C_q`;
double inversion: `c = 4/α + 4α`, `k_Z = k + k'`, `C = T₀ + T₀' + 4k'/α + C_q + C'` (primes: the
constants of 7.2 for the second stage). The draft's (1) "`+O(1)`" and (2) "`= r/α + O(1)`" are replaced by this bound
(E7.2, E7.5). The Anderson–Joshi speed sentence (`ρ_Z = min(ρ_in, α)`) is not claimed here.

*Class consequence.* Every class of moduli closed under `μ ↦ max(μ(r + k), 0) + c r + C` is
preserved: `O(r)` (real time), `O(r^n)` for `n ≥ 1`, `O(r log r)`. A modulus is an upper bound,
so what is preserved is the upper-bound class (`O`, not `Θ`).

### 7.5 The mass-action composition (GPAC ⇒ CRN)

Let a bounded ℚ-PIVP `y' = p(y)`, `y(0) = y₀`, compute `α > 0` with modulus `μ` and bound `B`.
(i) Shift to zero initial values: `ỹ = y − y₀`, field `p(ỹ + y₀)` (ℚ-coefficients, [RTCRN2]
Thm 3), same modulus for the target `α − c`, `c = y₀,out ∈ ℚ`.
(ii) Dual rail with state-dependent annihilation (the §7 introduction): nonnegative bounded species
with `X⁺_j − X⁻_j = ỹ_j` exactly.
(iii) Readout by double inversion driven by `x = X⁺_out − X⁻_out + c = y_out`, `c = c⁺ − c⁻`,
`c^± ≥ 0`:
`Ẏ = (1 + X⁻_out Y + c⁻ Y) − (X⁺_out + c⁺) Y`, `Y(0) = 0`;  `Ż = 1 − Y Z`, `Z(0) = 0`.
Every species' field is `prod − degr · (species)` with nonnegative-coefficient `prod`, `degr`
(mass action), **all initial values are 0** (the [RTCRN2] convention; the AJ module cannot be
used here, since from `Z(0) = 0` it stays at `0`), all species are bounded (7.4), and the output
is the single species `Z`. Since `x = y_out` exactly on `[0, ∞)`, 7.4 (double inversion) applies
with the modulus `max(μ, 0)`: the CRN computes `α` with
`μ_Z(r) ≤ max(μ(r + k_Z), 0) + (4/α + 4α) r + C`. In particular a real-time GPAC gives a
real-time CRN and a degree-`n` polynomial-time GPAC gives a degree-`n` polynomial-time CRN
(`n ≥ 1`). The rate constants are rational; rescaling time by a common denominator `L` gives
integer rate constants and replaces `μ_Z` by `μ_Z/L`, so every class above is unchanged (not
formalized). For `α ∈ (0, 1]` the CRN feeds the [LPP] compiler, giving GPAC ⇒ LPP
(computability only; no modulus is claimed for the LPP); `α = 0` is the trivial protocol.

`cor:crn-power` (Cor 6.5) follows: apply 7.5 to the certified computation of `α^β` (`α > 0`
gives `α^β > 0`). This realizes "can be implemented as a CRN" through full dual rail and the
double-inversion readout, not through the selective encoding in which `z` itself is a species; the selective
form is not claimed here.

### 7.6 Lemma 7.1 (`lem:input-limited`, repaired hypothesis) and Lemma 7.2

Both concern the linear equation `δ' + αδ = αε` (they are not used in 7.2-7.5; the only other
use of `lem:input-limited`, Step 1 of the appendix proof of Thm 6.6 `thm:power-complexity`, is
replaced by the §6 repair 6.4, so no remaining proof relies on the false lemma).

**7.1'.** Let `ε ∈ C¹[0, ∞)`, `ε(t) ≠ 0` for `t ≥ T`, `ε'(t)/ε(t) → 0`. Then every solution has
`δ(t)/ε(t) → 1`. *Proof.* `w = δ − ε` has `w' = −αw − ε'`; `u = w/ε` has
`u' = −(α + g)u − g`, `g = ε'/ε`. Given `η ∈ (0, α/2]` take `T_η ≥ T` with `|g| ≤ η` on
`[T_η, ∞)`; there `(u²)' = −2(α + g)u² − 2gu ≤ −αu² + 2η|u| ≤ −(α/2)u² + 2η²/α`, so by the
comparison lemma `limsup u² ≤ 4η²/α²`. Hence `u → 0`. ∎

**7.2 (`lem:module-limited`).** For `ε = C_ε e^{−βt}`, `β ≠ α`, every solution is
`δ(t) = (δ(0) + αC_ε/(β − α)) e^{−αt} − (αC_ε/(β − α)) e^{−βt}` (the difference with this
function, times `e^{αt}`, has derivative `0`); for `β > α` this is the draft's statement.

### 7.7 Cor 7.4 (`cor:crn-realizable`)

By 7.5 with 7.4: for every `n ≥ 1`, a real `α > 0` (in particular `α = 1`) computed by a bounded
ℚ-PIVP with modulus `O(r^n)` is computed by a mass-action CRN with zero initial values,
single-species output and modulus `O(r^n)`; the same for `O(r log r)`. The draft table's `Θ`
becomes `O` on the CRN side: no lower bound is claimed. The draft's proof (via (1) and the `t e^{−t}` boundary
discussion) is replaced by the class consequence of 7.4.

### 7.8 Review

Independent review (2026-11-08): **ACCEPT WITH FIXES**. Checked without error: E7.1,
E7.3, the comparison lemma, 7.2 (a)-(d) with constants and the strict-modulus endpoints, 7.3, both
modules of 7.4 and the class closure (no monotonicity of `μ` needed: `(r + k)^n ≤ 2^n r^n` for
`r ≥ k`), the shift and sign split of 7.5, 7.6. Findings applied: 1 (7.5 used the AJ readout with
`Z(0) = 1`, against the zero-initial-value convention of [RTCRN2] and [LPP]; now double
inversion), 2 (E7.2 "false" weakened to "not proved"), 3 (E7.4 range `[0.73, 1.61]`), 4 (E7.5 for
the AJ module), 5 (7.7 hypotheses, `Θ → O`), 6 (integer rate constants by time rescaling),
7 (LPP: computability only), 8 (appendix use of Lemma 7.1), 9 (constants of 7.4 spelled out).

## §5. Constructible classes (`thm:poly-constructible`, `prop:rlogr`, `con:tower`, `prop:tower`, `thm:arbitrary`)

Status: checked 2026-11-08; the proofs are complete, so no repair and no review (rule: a review
only when a step is missing). Findings on the statements:

- **N5.1 (`thm:poly-constructible`).** "For every `n ∈ ℕ`": the system has the factor `1/n`, so
  `n ≥ 1`. With the strict modulus convention the exact modulus is `μ_n(r) = (r+1)^n − 1`: the
  bound `|x(t) − 1| < e^{−r}` holds for `t > μ_n(r)` and fails for `0 ≤ t ≤ μ_n(r)`; this is the
  `Θ(r^n)` claim, formalized as such.
- **N5.2 (`prop:rlogr`).** "`g(t) ≥ r`" should be `g(t) > r` (strict convention); the modulus is
  `(r+1) log(r+1)`. The proof uses the Lambert function `W` (inverse of `w e^w`) and its
  derivative; Mathlib has no Lambert `W`, so the Lean proof must construct it.
- **N5.3 (table after `thm:arbitrary`).** The column "`Θ(exp^{(k+1)}(r))`" holds for `k ≤ 1`
  only. The exact modulus is `E_{k+1}(r)`, `E₀(s) = s`, `E_{j+1}(s) = E_j(e^s − 1)` (the inverse
  of `L_{k+1}`); for `k = 2`, `E₃(r) = exp(exp(e^r − 1) − 1) − 1` and
  `E₃(r)/exp³(r) → 0`. The theorem's own statement `exp^{(k+1)}(r + O(1))` is correct:
  `exp^{(j)}(r − 1) ≤ E_j(r) ≤ exp^{(j)}(r)` for `r ≥ 2`.
- `prop:tower`'s "in particular `L_k(t) = log^{(k)}(t) + O(1)`" is not used by `thm:arbitrary`
  and is not formalized.
