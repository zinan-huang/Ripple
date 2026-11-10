# The Chudnovsky formula in Ripple: the CM value `s₂(τ₁₆₃)`

Paper notes for `Ripple.Number.Chudnovsky1989.chudnovsky_one_over_pi` (release `r2026.11.2`), cited
from the Lean source by section. The Chudnovsky series identity follows from two facts: Fact A, a
general identity on the upper half-plane (Milla's proof, arXiv:1809.00533, formalized by Xuanji Li
in Lean Pool and ported under `Ripple/Number/Milla/`, see `NOTICE`), and Fact B, the value
`s₂(τ₁₆₃) = 77265280/90856689` at the CM point `τ₁₆₃ = (1 + √−163)/2`, derived here from Ripple's
certified modular equation `Φ₄₁` by a third-order expansion at its node (§2(b), §3).

Labels: **own** marks reasoning written for these notes rather than taken from a source; HOLDS /
GAP are verdicts on a step; R(k) means an accepted proof checked by k readers. The section numbers
are those of the working document these notes are taken from (§0, §3.4–§3.5, §4.5 and §5, on the
planning, are not included). §4 treats Ramanujan's 1914 series (level 58).

Checkers (evidence for planning, not certificates; the certificates are the Lean kernel facts):
`docs/audit/evidence/chud/beta41.py` (exact integer arithmetic on Ripple's `phi41SparseTerms`),
`docs/audit/evidence/chud/lvl2.py` (double-precision q-series), `docs/audit/evidence/chud/cert.py`
(the `linear_combination` certificates of `E2StarCM163.lean`).

---

## 1. The premise in plain mathematics

### 1.1 What the Lean definition says

`GaussPeriods.lean:3520`:

```
chudnovskyCM163GaussDerivativeCombination :=
  13591409 · F(x₀)² + 545140134 · x₀ · (2 F(x₀) F′(x₀)),
F := gauss2F1 (1/12) (5/12) 1   (Mathlib's ordinaryHypergeometric ₂F₁),
x₀ := 1728 / heegnerJ163Target = −1728/640320³.
```

With `G := F²` this is `13591409 G(x₀) + 545140134 x₀ G′(x₀)`. The premise of
`chudnovsky_one_over_pi` (`Chudnovsky1989.lean:850`) is that this equals
`(Real.rpow 640320 (3/2)) / (12π)`.

How it encodes the series (all proved in Ripple): the coefficient bridge
`a_k = (6k)!/((3k)!k!³) = 1728^k (1/6)_k(1/2)_k(5/6)_k/k!³` (`a_eq_3F2_coeff`), Clausen
`₃F₂(1/6,1/2,5/6;1,1;x) = ₂F₁(1/12,5/12;1;x)²` for `|x| < 1` (`chudnovsky_clausen_eq_gaussSq`),
the term-wise derivative (`chudnovsky_clausenSquareDerivSeries_eq_deriv`), and the argument identity
(`chudnovskyX_eq_jTarget_argument`). Hence

```
Σ_k (−1)^k a_k (13591409 + 545140134 k)/640320^{3k}  =  13591409 G(x₀) + 545140134 x₀ G′(x₀).   (1.1)
```

So the premise is exactly the Chudnovsky formula.

Side observations (CLAIMED, single reader):
- `chudnovsky_cm163_periodDerivative_evaluation` and `ramanujan_cm58_periodDerivative_evaluation`
  (`GaussPeriods.lean:3690, 3715`) compute five `have`s (`hpull`, `hperiod`, `hwr`, `hcm`,
  `hclausen`) and use none; the proof is `…_after_chain_rule hnormalization`. Decorative.
- `chowla_selberg_cm163_period` (`GaussPeriods.lean:3361`) is tautological (its hypothesis is the
  algebraicity of the witness it returns), and `Γ(1/3)³` is the Chowla–Selberg shape of
  discriminant −3, not −163. (Reviewer, from recollection, not checked: the hypothesis is moreover
  false by Wüstholz, a −163 period over a −3 period being transcendental; then it is also vacuous.)
- `cm58LegendreLambda = ramanujanLambda58Target = 1/99²` (`SingularModuli.lean:109`) and
  `ramanujanJ58Target = kleinJFromLambda (1/99²)` are constants. `RamanujanLambda58Statement`
  (`SingularModuli.lean:807`, `thetaLambda (i√58/2) = 1/99²`) is **false**: `λ(i√58/2)·99² =
  0.99994898…` (reviewer, 80-digit check; agrees with `λ ≈ 16q^{1/2}(1 − 8q^{1/2})`,
  `q^{1/2} = e^{−π√58/2} ≈ 6.38·10⁻⁶`). Its consumers in `CMEvaluationIsRoot.lean` (`.isRoot`,
  `.pullback_isRoot`, `.sq`) are vacuous as stated, and the docstring of `cm58LegendreLambda`
  (`GaussPeriods.lean:3104`) is wrong. The true statement is `x₂(i√58/2) = 1/99⁴` for the level-2
  Hauptmodul `x₂` of §4. `ramanujanJ58Target ≈ 24588749568.0000080` is not `j(i√58/2) ≈
  24591258496.0000078` (that number lies in `ℚ(√29)`, disc −232 has class number 2). The false
  statement and its consumers were deleted in `r2026.11.2`.

### 1.2 The two facts behind the premise

Notation: `τ ∈ ℍ`, `y = Im τ`, `q = e^{2πiτ}`, `D = (2πi)⁻¹ d/dτ`. `E₂, E₄, E₆` normalized
Eisenstein series (Mathlib's `E2`, `ModularForm.E 4`, `E 6`; Ripple's `Modular.E4`, `Modular.E6`),
`Δ = (E₄³ − E₆²)/1728` (Mathlib's `discriminant`), `j = E₄³/Δ` (Ripple's `kleinJ`),
`E₂* = E₂ − 3/(πy)`, `s₂ = (E₄/E₆) E₂*` (Lean Pool's `s₂`, Milla's `s₂`; Masser's `ψ = (3/2) s₂`).
`x(τ) = 1728/j(τ)`. `τ₀ = (1 + i√163)/2` (`heegnerTau163`), `y₀ = √163/2`, `j₀ = j(τ₀)`.

**Fact A (general identity; no CM).** On a connected region `R ⊂ ℍ` containing `τ₀` and a
neighbourhood of `i∞`, on which `|x(τ)| < 1` and `E₄(τ)E₆(τ) ≠ 0` (Lean Pool: `Im τ > 5/4`, with
`norm_inv_J_lt_one` and `E₆_ne_zero_of_mem_Region`; A2 uses both conditions),

```
F(x(τ))⁴ = E₄(τ)                                                     (A1, Kummer)
(1 − s₂(τ))/6 · G(x(τ)) + x(τ) G′(x(τ)) = G(x(τ))³ / (2π y E₆(τ)).   (A2, Milla thm42 shape)
```

**Fact B (CM value).** `j₀ = −640320³` (proved: `KleinJCM163Statement_proof`) and

```
s₂(τ₀) = 77265280/90856689,   equivalently (1 − s₂(τ₀))/6 = 13591409/545140134.   (B)
```

**Assembly (own, HOLDS given A and B).** At `τ₀`, `13591409 G + 545140134 x₀ G′ =
545140134 [(1 − s₂)/6 · G + x₀G′] = 545140134 · G³/(2π y₀ E₆) = 545140134 · G³/(π√163 E₆)`.
`(G³/E₆)² = E₄³/E₆² = j₀/(j₀ − 1728) = 640320³/(640320³ + 1728)`. `G³/E₆ > 0` at `τ₀`: `x₀` is real
with `|x₀| < 10⁻¹⁴`, so `F(x₀) ∈ (1/2, 2)` is real positive; `q₀ = −e^{−π√163}` is real with
`|q₀| < 4·10⁻¹⁸`, so `E₆(τ₀) = 1 − 504 Σ σ₅(n) q₀ⁿ ∈ (1/2, 2)`. With the integer identity
`163 · (640320³ + 1728) = 6541681608² = (12 · 545140134)²` (checked), the value is
`545140134 · 640320^{3/2} / (π · 12 · 545140134) = 640320^{3/2}/(12π)`. ∎

---

## 2. Candidate routes

Common to every route: Fact A. The routes differ in Fact B.

### 2.0 Fact A on paper (own; follows Lean Pool `Ramanujan.lean`, `Kummer.lean`, `MainTheorem.lean`)

A0. Ramanujan: `DE₂ = (E₂² − E₄)/12`, `DE₄ = (E₂E₄ − E₆)/3`, `DE₆ = (E₂E₆ − E₄²)/2`, `DΔ = E₂Δ`.
Proof: the Serre derivative `∂_k f = Df − (k/12)E₂ f` maps `M_k(SL₂ℤ)` to `M_{k+2}` (from
`E₂(−1/τ) = τ²E₂(τ) + 6τ/(πi)`, Mathlib `E2_slash_action`, and `Df → 0` at `i∞`); `M₄, M₆, M₈` are
one-dimensional (Mathlib `LevelOne.DimensionFormula`); compare constant terms. `DΔ = E₂Δ`
follows from Mathlib's `logDeriv_eta_eq_E2` (Lean Pool `Ramanujan.lean:736`, about 25 lines). Consequences: `Dj/j = 3DE₄/E₄ − E₂ = −E₆/E₄`, so
`j′ = −2πi j E₆/E₄` and `Dx/x = E₆/E₄`.

A1. Kummer. `x(τ) = 1728q + O(q²)` is a local coordinate at `i∞`. Both `F(x)⁴` and `E₄` are
holomorphic near `i∞` with value 1 there; `E₄^{1/4}` as a function of `x` satisfies the
hypergeometric equation of `₂F₁(1/12,5/12;1;x)` (by A0), whose exponents at `x = 0` are `0, 0`, so
its holomorphic solution with value 1 is unique; identity theorem along the connected region.
(Lean Pool proves the branch-free form `E₄ = F(1/J)⁴` on `Im τ > 5/4` by a Wronskian comparison.)
Consequence: `G² = E₄` with `G = F(x)²`.

A2. From `G² = E₄`: `2G·DG = DE₄`, so `DG = (G/6)(E₂ − E₆/E₄)`, and
`x dG/dx = DG/(Dx/x) = (G/6)(E₂E₄/E₆ − 1)`. Hence
`(1 − s₂)/6 · G + x G′ = (G/6)(E₄/E₆)(E₂ − E₂*) = (G/6)(E₄/E₆)(3/(πy)) = G³/(2πyE₆)`.

Ripple status of Fact A: nothing. Ripple has `Modular.E4`, `E6`, `kleinJ`, S/T laws, `E2` via Mathlib
(used only in `ModularPolynomialQExpansion`), Clausen and the `₂F₁` derivative lemmas; it has no
Ramanujan identity, no Kummer identity. Mathlib `v4.30.0` (`c5ea0035`) has
`ModularForms/Derivative.lean` (`normalizedDerivOfComplex`, `serreDerivative`,
`serreDerivative_mdifferentiable`), `LevelOne/DimensionFormula.lean`, `EisensteinSeries/E2/Transform.lean`
(checked through the GitHub API at that rev). So Lean Pool's `Ramanujan.lean` (761 lines) uses only
APIs present at v4.30 by name; signature drift unmeasured.

### 2(a). Milla's route, as formalized by Lean Pool

Steps for Fact B (from Lean Pool docstrings, `Coefficients.lean`, `MasserA1.lean`, `ComplexMult.lean`):
(a1) `j₀ ∈ ℤ` (abstract `Φ_m ∈ ℤ[X,Y]`, Kronecker, rationality by three primes, class number one;
needs j-surjectivity and j-injectivity mod Γ). (a2) Masser's Theorem A1 at `τ₀`: the trace-zero
fixing matrix `Λ = [[1, −82], [2, −1]]` (det 163, `Λ′(τ₀) = −1`); second-order Taylor of
`Φ₁₆₃(j(Λz), j(z)) ≡ 0`, Lemma A1 (`β₁₀ ≠ 0`, by classifying det-163 matrices fixing `τ₀`); gives
`s₂(τ₀) ∈ ℚ`. (a3) Milla Appendix B: `√D·(E₂*/η⁴)·(AC)²` is an algebraic integer (κ, Legendre
relation, `℘` division values; `DivisionValues.lean` 3068 lines), giving `s₂ · 10996566783048 ∈ ℤ`.
(a4) Numerical pin: `|s₂ · 10996566783048 − 9351571368960| < 1` from 30-digit enclosures of
`e^{−π√163}`.

In Ripple: (a1) is replaced by Ripple's own `Φ₄₁` route (done). Nothing of (a2)–(a4).
Size: `LeanPool/Chudnovsky` is 21,265 lines in all (20,912 without `Numerics`); the j-integrality
part Ripple could skip is about 7.4k of it, so porting (a2)–(a4) with their
supports is roughly 13–20k lines (Mathlib v4.35 → v4.30, module-system syntax stripped). Kernel computations: small (`decide +kernel` tables, ZMod 24).
Risks: backport drift over the lattice/℘/Liouville files (largest share), build cost unmeasured,
duplication of Ripple's own j-value. Advantage: the code is CI-checked upstream.

### 2(b). E₂* at the CM point via a modular equation: the `Φ₄₁` node (own; recommended)

Level 163 (Masser's trace-zero setting) needs `Φ₁₆₃`: degree 164 in each variable, coefficients of
thousands of digits; an explicit certificate is out of reach, and Lean Pool avoids it only by the
abstract `Φ_m`. The Fricke involution of level 41 does not fix `τ₀` (its fixed points have CM by
`ℤ[√−41]`). But `τ₀` is fixed by a determinant-41 matrix of nonzero trace, which is enough once one
goes to third order:

- `M = [[1, −41], [1, 0]]`, `Mz = 1 − 41/z = T S (z/41)`, so `j(Mz) = j(z/41)` for all `z`.
- `Mτ₀ = (τ₀ − 41)/τ₀ = τ₀` since `τ₀² = τ₀ − 41`.
- `λ := M′(τ₀) = 41/τ₀²`, `|λ| = 1`, `λ + 1/λ = −81/41` (own: `τ₀⁴ = −81τ₀ + 1640`), so `λ ≠ ±1`.
  `m₂ := M″(τ₀)/2 = −41/τ₀³`.
- Ripple proves `F₄₁ := Δ(τ)⁴²Δ(41τ)⁴²Φ₄₁(j(41τ), j(τ)) = 0` as a modular form
  (`Phi41FrickeSturm.lean:53` `phi41Level41ClearedAsModularForm_eq_zero`, pointwise via
  `phi41Level41ClearedAsModularForm_apply`), and `Φ₄₁` symmetric (`evalSparseBivarCleared_phi41_symm`).
  Substituting `τ = z/41` and using symmetry: `Φ₄₁(j(z/41), j(z)) = 0` for all `z ∈ ℍ`.

The full derivation is §3. Ripple status: the `Φ₄₁` identity, its symmetry, the data
(`ModularPoly41Terms.lean`, 1766 terms, coefficients up to 606 digits), `j₀`, and the T/S laws are
in place; missing are Ramanujan's identities (shared with Fact A), the third-order extraction lemma,
and four kernel evaluations. Size of the finite computations: each `β_ab` is a sum over the 1766
terms of `c · C(x,a) C(y,b) · j₀^{x+y−a−b}`, integers of about 1400–1500 digits (`β₂₀` has 1394
digits). Kernel cost unmeasured: computed directly, each `β_ab` is a 1766-term sum with binomials
and powers `j₀^{≤84}`, about 9 of them (`phi41Diag_root` is an 84-step Horner evaluation of
precomputed diagonal coefficients; measured at 49 s and 2.4 GB for
`evalPhi41DiagIsolatedC_j163Val`). Cheaper template: precomputed univariate polynomials
`t ↦ ∂ᵃ_X∂ᵇ_YΦ(t,t)/(a!b!)` evaluated by Horner at `j₀`, each linked to `phi41SparseTerms` by one
kernel check, as `phi41SparseTerms_diag_coeffs` does for the diagonal. Plain `Int` arithmetic under
`decide +kernel` suffices (GMP-backed `Nat` literals); the Kronecker-packed Sturm machinery is not
needed for this step.
Risks: (i) the third-order chain-rule extraction in Lean is fiddly (Lean Pool's MasserA1 does second
order, about 500 lines); (ii) the step depends on the `Φ₄₁` certificate staying in the build, which
the charter already requires; (iii) kernel memory, not measured.

### 2(c). Borwein-type derivation through the degree-n multiplier

Borwein–Borwein ch. 5 (own recollection, not reopened): the singular value function
`α(r) = E′/K − π/(4K²)` style quantity is algebraic; it is computed from a modular equation of degree
`n` and the derivative of its multiplier at the fixed point, or identified numerically from a
degree bound. At level 1 with `τ₀` this is the same mathematics as (b): the multiplier derivative of a
degree-`n` modular equation at a CM fixed point is the Taylor data of `Φ_n` along the fixed coset.
With `n = 163` it is Masser's route (infeasible explicitly); with `n = 41` it is route (b). The
numerical-identification variant needs an algebraicity/degree/height bound for `s₂(τ₀)` before a
numerical pin can decide it, i.e. route (a)'s (a2)+(a3). No separate route.

### 2(d). Port Lean Pool wholesale and derive the premise from `chudnovskySum_eq_pi_inv`

Since the premise is equivalent to the series (§0.1), porting Lean Pool's `chudnovskySum_eq_pi_inv`
and composing with Ripple's (1.1) proves the premise with no new mathematics. Cost = (a) plus the
glue to Mathlib's `chudnovskySum` (exists at v4.30: `Mathlib/Analysis/Real/Pi/Chudnovsky.lean`).
It also duplicates Ripple's j-value and Clausen layers. Kept as the fallback if (b)'s extraction
lemma resists.

### 2(e). Alternatives considered and set aside

- A Fricke / Atkin–Lehner fixed point: `E₂*(τ) − N E₂*(Nτ) = E₂(τ) − N E₂(Nτ)` is holomorphic on
  `Γ₀(N)`, and at a fixed point of `W_N` this evaluates `E₂*`; for `τ₀` the relevant `N` is 163
  (`X₀(163)` has genus 13), so the value needs a relation of the same size as `Φ₁₆₃`. Set aside.
- First-order (Λ′ = −1) argument at level 41: no trace-zero element of norm 41 exists in `ℤ[τ₀]`
  (trace-zero elements are `k(2τ₀ − 1)`, norm `163k²`). Hence third order.

---

## 3. Recommended route and complete paper proof of Fact B

### 3.1 Statement

Let `Φ = Φ₄₁ ∈ ℤ[X, Y]` (Ripple's `phi41SparseTerms`) and
`Φ(j₀ + X, j₀ + Y) = Σ_{a,b} β_ab X^a Y^b`, i.e.
`β_ab = Σ_terms c · C(x, a) · C(y, b) · j₀^{x−a+y−b}` (finite integer sums).

**Kernel facts (K)** (all checked exactly by `beta41.py` on Ripple's data):
K1 `β₀₀ = 0`; K2 `β₁₀ = β₀₁ = 0`; K3 `β₂₀ = β₀₂`, `β₂₁ = β₁₂`, `β₃₀ = β₀₃`; K4 `41 β₁₁ = 81 β₂₀`;
K5 `β₂₀ ≠ 0`; K6 `(7j₀ − 6912)/(j₀ − 1728) + 6 j₀ (244 β₃₀ − 82 β₂₁)/(163 β₂₀) = 77265280/90856689`
(cross-multiplied, an integer identity).
K1 is already proved (`phi41Diag_root` with the glue `phi41SparseTerms_diag_coeffs`;
`evalPhi41Diag` is private); K3 follows from the symmetry of `Φ₄₁` but is cheaper as a
direct check; K2 and K4 are also forced by the analysis below (orders 1 and 2), so they serve as
consistency checks, but checking them is cheaper than deriving them.

**Theorem B.** `s₂(τ₀) = 77265280/90856689`.

### 3.2 Proof

Step 1 (the analytic identity). For `u` in a disc around 0 put `z = τ₀ + u`,
`X(u) = j(Mz) − j₀`, `Y(u) = j(z) − j₀`. By §2(b), `P(u) := Σ β_ab X(u)^a Y(u)^b = Φ(j(z/41), j(z)) = 0`
identically. `X, Y` are holomorphic with `X(0) = Y(0) = 0` (since `Mτ₀ = τ₀`).

Step 2 (derivatives of X and Y). Write `j₁ = j′(τ₀)`, `j₂ = j″(τ₀)`, `μ(u) = M(τ₀ + u) − τ₀`,
`μ′(0) = λ`, `μ″(0) = 2m₂`. Then `Y′(0) = j₁`, `Y″(0) = j₂`, `X′(0) = j₁λ`,
`X″(0) = j₂λ² + 2j₁m₂` (chain rule; `j′(Mτ₀) = j₁` because `Mτ₀ = τ₀`).

Step 3 (third derivative of P). Since `β₀₀ = β₁₀ = β₀₁ = 0` (K1, K2), every monomial of `P` has
total degree ≥ 2 in `(X, Y)`, and monomials of degree ≥ 4 have vanishing third derivative at 0. The
third derivative of the degree-2 and degree-3 parts gives (Leibniz; only `X′, X″, Y′, Y″` enter)

```
P‴(0)/6 = β₂₀ X′X″ + (β₁₁/2)(X′Y″ + X″Y′) + β₀₂ Y′Y″
          + β₃₀ X′³ + β₂₁ X′²Y′ + β₁₂ X′Y′² + β₀₃ Y′³ = 0.
```

Substituting Step 2:

```
j₁ j₂ · 𝒟 + j₁² m₂ · 𝒦 + j₁³ · 𝒞 = 0,                                            (3.1)
𝒟 = β₂₀λ³ + β₁₁(λ + λ²)/2 + β₀₂,  𝒦 = 2β₂₀λ + β₁₁,  𝒞 = β₃₀λ³ + β₂₁λ² + β₁₂λ + β₀₃.
```

Step 4 (the constants are rational up to one factor). By K3, K4 and `λ + 1/λ = −81/41`:
`𝒟 = (1+λ) λ β₂₀ (−163/82)`, `𝒞 = (1+λ) λ (−(244β₃₀ − 82β₂₁)/82)`, so
`𝒞/𝒟 = (244β₃₀ − 82β₂₁)/(163β₂₀) =: γ ∈ ℚ`; `𝒟 ≠ 0` by K5 and `λ ∉ {0, −1}`. Also
`−m₂𝒦/𝒟 = i/y₀`: by K4, `𝒦 = β₂₀(2λ + 81/41) = β₂₀(λ − 1/λ)`; with `m₂ = −41/τ₀³` and
`τ₀³λ = 41τ₀`, `−m₂𝒦/𝒟 = −(82/163)(1 − 1/λ)/τ₀ = −(2/163)(82 − τ₀)/τ₀`; with
`1/τ₀ = (1 − τ₀)/41` this is `(2/163)(2τ₀ − 1) = 2i√163/163 = i/y₀` (derivation by the reviewer;
numerically both `0.156652…i`).

Step 5 (j-derivatives via Ramanujan). From A0, `Dj = −jE₆/E₄` and
`D²j = j(2E₆²/(3E₄²) − E₂E₆/(6E₄) + E₄/2)`, hence
`j₂/j₁ = 2πi (E₂/6 − E₄²/(2E₆) − 2E₆/(3E₄))` and `j₁ = −2πi j₀ E₆/E₄` (all at `τ₀`).
`j₁ ≠ 0`: `j₀ ≠ 0` and `E₄(τ₀)³ = j₀Δ ≠ 0`, `E₆(τ₀)² = (j₀ − 1728)Δ ≠ 0`.

Step 6 (solve). Divide (3.1) by `j₁²𝒟`: `j₂/j₁ = −m₂𝒦/𝒟 − j₁ γ`. Insert Step 5 and Step 4:

```
2πi (E₂/6 − E₄²/(2E₆) − 2E₆/(3E₄)) = i/y₀ + 2πi j₀ (E₆/E₄) γ,
E₂/6 − 1/(2πy₀) = E₄²/(2E₆) + 2E₆/(3E₄) + j₀ (E₆/E₄) γ.
```

The left side is `E₂*/6`. Multiply by `6E₄/E₆`:
`s₂(τ₀) = 3E₄³/E₆² + 4 + 6 j₀ γ = 3j₀/(j₀ − 1728) + 4 + 6j₀γ = (7j₀ − 6912)/(j₀ − 1728) + 6 j₀ γ`,
using `E₄³/E₆² = j₀/(j₀ − 1728)`. By K6 this is `77265280/90856689`. ∎

Cross-check (not part of the proof): `lvl2.py` computes `s₂(τ₀) = 0.85040827318723…` from q-series;
`77265280/90856689 = 0.85040827318723…`. The formula of Step 6 has Masser's shape
`s₂ = 3j₀γ′ + (7j₀ − 6912)/(j₀ − 1728)` (Lean Pool `MasserA1.lean` docstring), with `γ′ = 2γ`.

### 3.3 What must be checked in Lean beyond the paper

- Step 1 needs `Φ₄₁(j(z/41), j(z)) = 0` for every `z` near `τ₀` (not only at `τ₀`): from
  `phi41Level41ClearedAsModularForm_eq_zero`, `_apply`, `evalSparseBivarClearedC_eq_den_mul_eval`
  (with the degree bound 42), `Δ ≠ 0`; the swap is optional (use `(X, Y) = (j(z), j(Mz))`
  directly; K3 makes the `β` symmetric and Step 3 is unchanged).
- Holomorphy of `kleinJ ∘ ofComplex` near `τ₀` (Ripple has no such lemma; from `E4`, `Δ`
  holomorphic and `Δ ≠ 0`).
- Step 3 is a polynomial identity in `(X, Y)` composed with holomorphic maps; the cleanest Lean form
  is an `iteratedDeriv 3` statement for `u ↦ Q(X(u), Y(u))` with `Q` a bivariate polynomial whose
  constant and linear coefficients vanish, or the divided-difference form `P(u)/u² → …`.
  The degree ≥ 4 part needs only "`X, Y` vanish at 0".
- The Taylor coefficients `β_ab` as computable functions of the sparse list, plus the lemma
  `Φ(j₀ + X, j₀ + Y) = Σ β_ab X^a Y^b` (binomial expansion of each monomial; generic in the list).
  Alternatively use partial derivatives of the sparse polynomial evaluated at `(j₀, j₀)`
  (`∂^a_X ∂^b_Y Φ (j₀, j₀) = a! b! β_ab`), which needs a formal-derivative lemma for
  `evalSparseBivarC` and avoids the full shift.

---

## 4. Ramanujan 1914 (level 58)

### 4.1 The premise

`GaussPeriods.lean:3472`: `ramanujanCM58GaussDerivativeCombination = 1103 F(z₀)² + 26390 z₀ (2F F′)(z₀)`,
`F = ₂F₁(1/8,3/8;1;·)`, `z₀ = 1/99⁴`; premise: `= 9801/(2√2 π)`. Ripple proves the series side
(`(4k)!/k!⁴ = 256^k (1/4)_k(1/2)_k(3/4)_k/k!³`, Clausen `₃F₂(1/4,1/2,3/4;1,1;z) = ₂F₁(1/8,3/8;1;z)²`,
`256/396⁴ = 1/99⁴`), so again the premise is the formula itself.

### 4.2 Plain mathematics (own; each identity checked numerically by `lvl2.py`)

Level 2: `a = η(τ)²⁴`, `b = η(2τ)²⁴`, `x₂ = 256ab/(a + 64b)²` (a Hauptmodul of `Γ₀(2)+`),
`Z = 2E₂(2τ) − E₂(τ) ∈ M₂(Γ₀(2))`, `w = D log x₂`, `G = F(x₂)²`, `τ₅₈ = i√58/2`, `y₅₈ = √58/2`.

- (R-A1) `G(x₂(τ)) = ₃F₂(1/4,1/2,3/4;1,1;x₂(τ)) = Z(τ)` near `i∞` (level-2 Kummer). Numerically equal
  to 16 digits at `τ = 0.1 + 0.9i` and at `τ₅₈`.
- (R-A2) `w² = Z²(1 − x₂)`, pure algebra (reviewer): from `D log Δ = E₂` at `τ` and `2τ`,
  `w = E₂(τ) + 2E₂(2τ) − 2(aE₂(τ) + 128bE₂(2τ))/(a + 64b) = Z(a − 64b)/(a + 64b)`, and
  `1 − x₂ = ((a − 64b)/(a + 64b))²`. (A Sturm argument would have to handle the zero of `a + 64b`
  at `(1+i)/2`; not needed.) Numerically `w²/(Z²(1 − x₂)) = 1 − 7·10⁻¹⁶` at `τ₅₈`.
- (R-A3) general identity: `c·G + x₂G′ = Z(c + E₂*/(6w) + ∂Z/(wZ)) + Z/(2π y w)`, where
  `∂Z = DZ − E₂Z/6` (weight 4, modular). Proof as A2: `x₂G′ = DZ/w`, `E₂ = E₂* + 3/(πy)`.
- (R-B1) singular value `x₂(τ₅₈) = 1/99⁴` (numerically `x₂(τ₅₈)·99⁴ = 1.0000000000000000`).
- (R-B2) CM value `c₅₈ := −E₂*(τ₅₈)/(6w) − ∂Z/(wZ) = 1103/26390` (numerically
  `0.0417961348995832` vs `0.04179613489958318`).
- Assembly: `1103G + 26390x₂G′ = 26390·Z/(2πy₅₈w) = 26390/(2πy₅₈√(1 − 1/99⁴))`; with
  `99⁴ − 1 = 9800·9802`, `√9800 = 70√2`, `√9802 = 13√58`, this is `9801/(2√2π)`. (Sign:
  `Z/w = (a + 64b)/(a − 64b) > 0` at `τ₅₈`, since `q > 0` is tiny and `a > 64b > 0`.)

### 4.3 The degree-29 modular equation `Ψ₂₉` (computed 2026-11-09)

Normalized Hauptmodul of `Γ₀(2)+`: `T = 256/x₂ − 104 = a/b + 24 + 4096 b/a = q⁻¹ + 4372q + …`
(`a = η(τ)²⁴`, `b = η(2τ)²⁴`; McKay–Thompson series 2A). `T` is invariant under `Γ₀(2)` and under
`W₂ : τ ↦ −1/(2τ)`.

`Ψ₂₉(X, Y) := ∏_{γ} (X − T(γτ))` as a polynomial in `X` with coefficients in `ℤ[T(τ)]`, the product
over the 30 matrices `γ ∈ {(τ+k)/29 : 0 ≤ k < 29} ∪ {29τ}`. Computed in PARI/GP from the power
sums `Σ T(γτ)^m` (`m ≤ 30`), each reduced to a polynomial in `T(τ)` by its principal part, then
Newton's identities: `docs/audit/evidence/chud/lvl58/psi29.gp`, output `psi29.txt`. Result and
checks (all exact unless marked):

| | `Ψ₂₉` (this note) | `Φ₄₁` (Ripple `ModularPoly41Terms`) |
|---|---|---|
| degree in each variable | 30 | 42 |
| nonzero coefficients | 900 (of 961) | 1766 |
| largest coefficient | 900 bits (271 digits) | 2012 bits |
| total coefficient size | 510,374 bits (161 KB as text) | 2,326,858 bits (747 KB as Lean) |
| symmetric `Ψ(X, Y) = Ψ(Y, X)` | yes | yes |

Cost: 238 s and 0.4 GB on mini (one GP process). Numerical check (`check.gp`, 600 digits):
`|Ψ₂₉(T(τ), T(29τ))| / max(|T(τ)|, |T(29τ)|)³⁰ = 4·10⁻⁵²⁹` at `τ = 0.13 + 0.31i`. This is a
computation, not yet a certificate; §4.5 L58-3 is the certificate.

Diagonal (`roots.gp`): `Ψ₂₉(X, X)` has degree 58 and factors over `ℚ` as
`(X − T₀) · (X³ + …) · (square factors)`, with `T₀ = 256·99⁴ − 104 = 24591257752`. `T₀` is a
**simple** root (multiplicity 1); the nearest other root is at distance `1.4·10¹⁰`. The square
factors are the nodes of the diagonal; `T₀` is not a node, so the argument is Masser's
second-order one, not the third-order node argument of §3.

### 4.4 Route and paper proof of R5 and R6 (own; R(2) after an independent review)

Fixing map: `μ(z) = −29/(2z)`. Then `μ(τ₅₈) = τ₅₈` (`τ₅₈² = −29/2`), `μ′(τ₅₈) = 29/(2τ₅₈²) = −1`,
`μ″(τ₅₈) = −29/τ₅₈³ = −2i/y₅₈`. Since `μ = (z ↦ 29z) ∘ W₂` and `T ∘ W₂ = T`,

  (E) `Ψ₂₉(T(z), T(μ(z))) = 0` for all `z ∈ ℍ`.

**R5: `T(τ₅₈) = T₀`, i.e. `x₂(τ₅₈) = 1/99⁴`.** By (E) at `z = τ₅₈`, `T(τ₅₈)` is a root of
`Ψ₂₉(X, X)`. Numerically `T(τ₅₈) = q⁻¹ + 4372q + O(q²)` with `q = e^{−π√58} = 4.07·10⁻¹¹`, and
`e^{π√58} = 24591257751.9999998222…`, so `|T(τ₅₈) − T₀| < 1`, far below the root separation
`1.4·10¹⁰`; hence `T(τ₅₈) = T₀`. (Lean needs: an enclosure of `T(τ₅₈)` to within `10⁹`, i.e. crude
bounds on `e^{π√58}` and on the `η`-product tail, and that the cofactor `Ψ₂₉(X, X)/(X − T₀)` has
no root on that real interval; `T(τ₅₈)` is real because `τ₅₈` is on the imaginary axis, so only
real roots must be excluded, by sign or a Taylor bound. The quoted separation is over `ℂ`.) `x₂ = 256/(T + 104) = 1/99⁴`.

**R6: `c₅₈ = 1103/26390`.** Notation: `s = (a − 64b)/(a + 64b)`, `Z = 2E₂(2τ) − E₂(τ)`,
`w = D log x₂`, `g = DT`, `∂F = DF − (k/12) E₂ F` for weight `k`.

Level-2 identities (each also checked as an identity of `q`-series in `masser58.gp`, and to
`O(q³⁰¹)` by the reviewer):

- (I1) `w = Z s`: pure algebra, it is the formula of R-A2 (`D log x₂·(a + 64b) = Z(a − 64b)`); no
  sign has to be fixed. [review suggestion 5]
- (I2) `∂Z = Z² (1/12 − s/4)`. Since `DE₂ = (E₂² − E₄)/12` at `τ` and `2τ`,
  `∂Z = (Z² + E₄(τ) − 4E₄(2τ))/12`, so (I2) is equivalent to `E₄(τ) − 4E₄(2τ) = −3Z²s`.
  `Z²s` is not a priori holomorphic (`a + 64b` has a double zero at the elliptic point `(1+i)/2`,
  cancelled by the simple zero of `Z` there), so the proof is the cleared identity
  `(E₄(τ) − 4E₄(2τ))(a + 64b) = −3Z²(a − 64b)` in `M₁₆(Γ₀(2))`, Sturm bound `16·3/12 = 4`
  (compare `q⁰ … q⁴`), then division by `a + 64b ≠ 0` at `τ₅₈`. (`E₄(τ) + 4E₄(2τ) = 5Z²` is also
  true but not used.) [review fix]
- (I3) `Ds = −x₂ Z/2` (from `s² = 1 − x₂` and `Dx₂ = x₂ w = x₂ Z s`).
- (I4) `g = DT = −256 Dx₂/x₂² = −256 w/x₂`.

From (I1)–(I4): `∂w = (∂Z)s + Z Ds = Z²s(1/12 − s/4) − x₂Z²/2`, and
`∂g = −256(∂w − w²)/x₂`, so

  (G) `∂g/g² = −x₂ (s/12 − (5/4)(1 − x₂) − x₂/2) / (256 (1 − x₂))`,

a function of `x₂` and `s` only.

Second-order expansion of (E) at `τ₅₈`. Put `u = T`, `v = T ∘ μ`, `uₖ = u⁽ᵏ⁾(τ₅₈)`, and let
`Ψ_X, Ψ_XX, Ψ_XY` be the partials at `(T₀, T₀)`; by symmetry `Ψ_Y = Ψ_X`, `Ψ_YY = Ψ_XX`. Then
`v₁ = −u₁`, `v₂ = u₂ + u₁μ″`. The first derivative of (E) is `(Ψ_X − Ψ_Y)u₁ = 0`, empty. The second is

  `2(Ψ_XX − Ψ_XY) u₁² + Ψ_X (2u₂ + u₁ μ″) = 0`.

With `u₁ = 2πi g`, `u₂ = (2πi)² Dg = (2πi)²(∂g + E₂g/6)` and `μ″ = −2i/y₅₈`:
`2u₂/u₁² + μ″/u₁ = 2∂g/g² + E₂/(3g) − 1/(π y₅₈ g) = 2∂g/g² + E₂*/(3g)`, because
`E₂ = E₂* + 3/(π y)`: the non-holomorphic terms cancel. Hence, if `Ψ_X(T₀, T₀) ≠ 0` and `g(τ₅₈) ≠ 0` (`g = −256 Z s/x₂` with `Z, s, x₂ ≠ 0` at `τ₅₈`;
numerically `g = −q⁻¹ + 4372q + … ≈ −2.459·10¹⁰`), [review fix 2]

  (M) `2 ∂g/g² + E₂*/(3g) = −2 (Ψ_XX − Ψ_XY)/Ψ_X`  at `τ₅₈`.

Exact data (`masser58.gp`): `Ψ_X(T₀,T₀) ≠ 0` (1967 bits), `Ψ_XX − Ψ_XY` (1933 bits),
`−2(Ψ_XX − Ψ_XY)/Ψ_X = 66716347/787408797714739200`.

Assembly. At `τ₅₈`, `x₂ = 1/99⁴` (R5) and `s = +√(1 − x₂)` (`q > 0` tiny, so `a > 64b > 0`).
(M) and (G) give `E₂*/g` in `ℚ(s)`. Then with `E₂*/w = (E₂*/g)(−256/x₂)` (I4) and
`∂Z/(wZ) = (1/12 − s/4)/s` (I1, I2),

  `c₅₈ = −E₂*/(6w) − ∂Z/(wZ) = 1103/26390`,

computed exactly in `ℚ(s)`, `s² = 1 − 1/99⁴`. The `s`-parts cancel identically (reviewer):
`c₅₈ = 128 r/x₀ − 1 − x₀/(2(1 − x₀))` with `r = −2(Ψ_XX − Ψ_XY)/Ψ_X`, `x₀ = 1/99⁴`, so the sign of
`s` matters only for the §4.2 assembly (`Z/w = 1/s`), not for R6. Numerical cross-checks at
`τ₅₈` of (I2), of (M) and of `c₅₈` agree to `10⁻³⁷`–`10⁻⁴⁷` (limited by the `suminf` tolerance
in GP, not by the identities).

With R-A1–R-A3 and R5, R6, the assembly of §4.2 gives the premise (R7).


### 4.6 Alternatives considered

- Level-1 node via `Φ₅₉` (`[[1, −29], [2, 1]]` fixes `τ₅₈`, det 59): degree 60, no certificate, and
  `j(τ₅₈) ∈ ℚ(√29)` is not rational. Heavier than `Ψ₂₉` on every count.
- Level-1 trace-zero `Φ₅₈`: degree 90. Heavier.
- Hecke correspondence `T₅₉` on `X₀(2)+` (degree 60): larger than `Ψ₂₉`, no gain.
- Weber class invariant `g₅₈² = (5 + √29)/2` (Ramanujan's own route): needs Weber-function
  transformation theory, not in Ripple or Mathlib; gives R5 but not R6.
- Milla's `hauptformel` at `τ₅₈` (level 1, already in Ripple) gives a Chudnovsky-type series with
  coefficients in `ℚ(√29)`, not Ramanujan's; converting it needs an algebraic transformation
  between `₂F₁(1/12, 5/12; 1; ·)` and `₂F₁(1/8, 3/8; 1; ·)` plus `j(τ₅₈)` and `s₂(τ₅₈)` in
  `ℚ(√29)`; no saving over §4.4.


### 4.7 Status

All of R1–R6 are formalized in release `r2026.11.3`, and `ramanujan_one_over_pi` has no premise:
the CM evaluation is `Modular.ramanujanCM58_evaluation`; R5 is `Modular.hauptT58_tau58` and
`x2_tau58` (with the `Ψ₂₉` certificate `Modular.psi29_modular_equation`), R6 is
`Modular.ramanujan58_cm_relation` (from `masser58`), and the level-2 Kummer identity is
`Modular.Z_sq_eq_gauss` with the hypergeometric transformations of
`Hypergeometric.Transform58`.

