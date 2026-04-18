# Experiment 11 — Rationale for the 10 Systems

Each system was chosen to probe a question *not* already answered by
exps 06–10. The exps established:
- Exp 06: scalar cubic, k* = Θ(C) when C multiplies a non-cancelling monomial.
- Exp 07: k* is O(1) when the large coefficient multiplies a vanishing-on-trajectory quantity.
- Exp 08: k* = Θ(max|c|) for `y' = ε + A y² − A y³` (non-cancelling).
- Exp 09: Conway deg 71, max|c|=14 → k*/M₀ ≈ 200–359.
- Exp 10: n-bonacci `y^n − y − 1`, max|c|=1, n∈{5,10,20,40} → k*/M₀ ≈ 2.7·n^1.23.

## The 10 systems and what each asks

### 1. golden (`y² − y − 1`)
**Question:** Baseline anchor. What does k*/M₀ look like at the smallest
meaningful degree (deg=2, max|c|=1) for a famous algebraic constant?
Gives the intercept of any degree-power-law fit.

### 2. plastic (`y³ − y − 1`)
**Question:** Famous "plastic number" (the smallest Pisot number). Same
sparse-coefficient structure as n-bonacci but at deg=3 — extends exp 10's
power-law below n=5.

### 3. silver (`y² − 2y − 1`)
**Question:** Same degree as golden, but (i) max|c|=2 instead of 1,
(ii) λ=2.414 far from 1. Does root location matter? Does doubling max|c|
double k*/M₀ at fixed degree (exp 08 says yes, but exp 08 was scaling
*all* coefs proportionally — here only one coef differs).

### 4. tribonacci (`y³ − y² − y − 1`)
**Question:** Same degree and same max|c|=1 as plastic, but **dense** (all
monomials present) vs plastic's **sparse** structure. Answers: does the
number of non-zero monomials (at fixed deg, max|c|) affect k*/M₀?

### 5. dense_deg10 (`y¹⁰ − y⁹ − … − y − 1`)
**Question:** Exp 10 used n-bonacci (sparse, only 3 nonzero coefs).
At deg=10, this system has all 11 coefs = ±1. Does filling in the
middle coefficients raise or lower k*/M₀ vs the sparse n=10 case
(k*/M₀ = 46 from exp 10)?

### 6. small_lambda (`y⁵ − 0.1`)
**Question:** λ ≈ 0.63, i.e. *less than 1*. All prior experiments had
λ ≥ 1. Does λ < 1 behave qualitatively differently? In principle the
monomial binomial-expansion amplification is dampened when λ < 1 because
`λ^k → 0` for large k; might make k*/M₀ *smaller* than deg-power-law predicts.

### 7. large_coef_deg5 (`y⁵ − 50y − 50`)
**Question:** Pairs with exp 10's n=5 (`y⁵ − y − 1`) at same degree.
max|c| scales 50×, and by exp 08 we expect M₀ to scale with max|c|
(so k* scales 50× too), but k*/M₀ should stay close to exp 10's n=5
value (16.68). If k*/M₀ is unchanged: confirms β=0 in joint fit.
If it drifts: coefficient structure matters beyond the M₀ normalization.

### 8. near_cancel_deg5 (`100y⁵ − 100y⁴ − y − 1`)
**Question:** Stress test for near-cancellation at the fixed point.
The big monomials `100y⁵` and `-100y⁴` nearly cancel near λ ≈ 1,
creating huge M₀ with tiny physical flow. By the exp 08 logic, M₀ should
dominate and k*/M₀ should stay moderate. But the dual-rail doesn't see
cancellation — it sees each monomial separately. So M₀ correctly
accounts for it. The question: is there any *additional* penalty
beyond M₀ when positive/negative monomials are nearly matched?

### 9. sparse_deg15 (`y¹⁵ − y¹⁰ − y⁵ − 1`)
**Question:** Interpolates between the exp 10 n=10 and n=20 points with
*different* sparse structure. With 4 nonzero coefs spread geometrically,
does the same degree-power-law hold? Tests robustness of the exponent α.

### 10. cheb_like_deg5 (`16y⁵ − 20y³ + 5y − 3`)
**Question:** Chebyshev-like dense polynomial with alternating signs
(a cancelling structure at fixed point). max|c|=20 at deg=5. Designed
as a (deg, max|c|) midpoint filling in between exp 10's n=5 (deg=5,
max|c|=1) and exp 09's Conway (deg=71, max|c|=14). Follow-up Conway
conjecture: if k*/M₀ really depends *only* on deg and is independent of
coefficient structure once M₀ is fixed, this point should match the
exp-10 n=5 value (~17) irrespective of max|c|=20 vs 1.

## Joint fit plan

Fit `log(k*/M₀) = logC + α·log(deg) + β·log(max|c|)` across the 10 new
points plus the 5 anchors (exp 10 n=5,10,20,40 and exp 09 Conway n=71).

- If β ≈ 0: max|c| does not matter once M₀ is fixed (strong statement).
- If β > 0 significantly: coefficient magnitude has residual effect even
  after normalization.
- The α coefficient should replicate exp 10's estimate (1.2–1.5).

## Systems deliberately omitted

- Higher-dimensional / cascaded systems (exp 07 territory): cleanly
  covered and not adding new info here.
- Strict "coef-uniform" scaling like exp 08's `A y² − A y³` (already done).
- Random polynomials: prefer systems with "meaning" so readers can map
  results to concrete algebraic numbers.
