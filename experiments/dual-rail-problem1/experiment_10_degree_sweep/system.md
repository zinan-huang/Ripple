# Experiment 10 — Intermediate-Degree Sweep

**Date:** 2026-04-18
**Motivation:** Exp 09 (Conway, degree 71) gave `k*/M₀ ≈ 200`, vastly
larger than the `~1·M₀` observed in exps 06/08 (degree ≤ 3). This
experiment varies **polynomial degree** at approximately fixed
coefficient magnitude to extract the degree-prefactor `C(deg)` in

    k* ≈ C(deg) · M₀.

## Polynomial family

For each `n ∈ {5, 10, 20, 40}` we use the generalized
**n-bonacci polynomial**

    q_n(y) = y^n − y − 1.

### Properties

- **Integer coefficients, max|c_k| = 1** — significantly *smaller* than
  Conway's 14. This is deliberate: it isolates the degree effect. If
  degree drives the prefactor, we should still see `k*/M₀` grow even
  with unit coefficients.
- **Unique positive real root λ_n ∈ (1, 2).**
  - `λ_5 ≈ 1.1673`  (5-bonacci)
  - `λ_10 ≈ 1.0800`
  - `λ_20 ≈ 1.0385`
  - `λ_40 ≈ 1.0184`
  By Descartes' rule of signs, `q_n` has exactly one sign change
  (coefficient sequence `+1, 0, …, 0, −1, −1`), so exactly one positive
  real root.
- **`q_n(0) = −1 < 0`, `q_n(1) = −1 < 0`, `q_n(2) = 2^n − 3 > 0`.** So
  `λ_n ∈ (1, 2)`.
- **`q_n'(λ_n) = n·λ_n^{n−1} − 1 > 0`.** So with SIGN = −1
  (`y' = −q_n(y)`), `λ_n` is a stable fixed point.
- **Trajectory from y(0) = 0 rises monotonically to λ_n.** We have
  `y'(0) = −q_n(0) = 1 > 0`, and `y' = 0` only at `y = λ_n` in the
  relevant interval.
- **Known family.** `n = 2` gives the golden ratio. `n = 3` gives the
  tribonacci / plastic constant. Root for `n → ∞` tends to 1 from
  above; specifically `λ_n = 1 + (log n)/n + O((log n)^2/n^2)` (root of
  `y^n = y + 1` with `y > 1`).

### Why this family (vs. Conway or random)

1. **Comparable with exp 09.** Same type of system: `y' = −q(y)` with
   monotone approach from 0 to a unique positive root in `(1, 2)`.
2. **Coefficient magnitude held constant at 1** — any `k*/M₀`
   growth is attributable to degree alone, not to coefficient bloat.
3. **Well-documented and canonical** — these polynomials are
   n-bonacci / Fibonacci-type, cited widely in combinatorics.
4. **Sparse (only 3 nonzero coefficients)** — provides a clean
   lower bound on degree effects. If sparse polynomials already show
   `k*/M₀ ≫ 1`, the effect is inherent to degree, not density.

## Dual-rail expansion

The three nonzero terms `y^n, −y, −1` expand as
`(u−v)^n = Σ_j C(n,j) (−1)^j u^{n−j} v^j`, `−(u−v) = −u + v`, and `−1`.
After SIGN = −1 (`y' = −q(y) = −y^n + y + 1`), positive monomials of
`u, v` go into `p̂⁺`, negative into `p̂⁻`.

Number of monomials from the `y^n` term alone is `n + 1`. Total after
the linear and constant terms: `n + 3`. Far fewer than Conway's 2525,
but enough to probe binomial cancellation.

## On-trajectory production `M₀`

At the fixed point `λ = λ_n`:

    M₀ = p̂⁺(λ, 0) = −q_n(λ)⁺ + [positive monomials of −q_n(u) at u=λ, v=0]

Since only positive monomials at `v = 0` contribute (those with even j
after the sign split), and the `−y^n` term contributes `−λ^n` (negative)
while `+y` contributes `+λ` (positive) and `+1` is constant, the precise
value is computed in `run.py`. For leading order:
`M₀ ≈ λ^n ≈ (1 + ε)^n`, which for the four degrees gives:
- n=5: ≈2.17
- n=10: ≈2.16
- n=20: ≈2.14
- n=40: ≈2.12

(Root satisfies `λ_n^n = λ_n + 1 ≈ 2`, so `λ^n ≈ 2` across all n.)

This is a nice property: M₀ stays O(1) across all four degrees, so
`k*/M₀` directly reflects `k*` itself — any growth is degree-driven, not
M₀-driven.

## k-sweep protocol

Same as exp 09:

- LSODA, `rtol=1e-6, atol=1e-8, max_step=0.01`, `T=5.0`, 1000 eval points.
- `k` sweep: 10 values, `k ∈ [0.1·M₀, 1000·M₀]` log-spaced.
- Success = `solver.success == True` and `all_finite == True` with
  `final_t == T`.
- `k*` = smallest swept `k` with success. Resolution: factor
  `(1000/0.1)^(1/9) ≈ 2.15` between adjacent grid points.

## Expected outcomes

- **If `C(deg)` is O(1) (i.e. constant):** all four degrees give
  `k*/M₀ ≤ 10` and the Conway `~200` prefactor is attributed to
  Conway-specific coefficient structure, not degree.
- **If `C(deg) ≈ poly(deg)`:** monotone growth in `k*/M₀` across
  `n = 5, 10, 20, 40`. Fit `k*/M₀ ≈ A · n^α`; with exp 09 as anchor
  (n=71), we can extrapolate and check consistency.
- **If `C(deg) ≈ 2^deg`:** very fast blow-up; `n=40` might already
  exceed `10⁶ · M₀`. Would indicate the binomial `C(n, n/2) ≈ 2^n/√n`
  in the (u−v)^n expansion directly sets the scale.
- **Anomalies to watch for:** degrees where the solver fails at *all*
  swept k (counterexample candidate), or non-monotone behavior.
