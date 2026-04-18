# Experiment 10 — Notes

**Date:** 2026-04-18
**Family:** `q_n(y) = y^n − y − 1`, `n ∈ {5, 10, 20, 40}`.
**Numerics:** LSODA, `rtol=1e-6, atol=1e-8, max_step=0.01`, `T=5.0`,
10-point log sweep `k/M₀ ∈ [0.1, 1000]` (factor ~2.78 between grid
points, so `k*` resolution is within ~3).

## Headline table

| n   | λ          | M₀        | k*         | k*/M₀ | (k*/M₀)·n^(-1) |
|-----|------------|-----------|------------|-------|----------------|
| 5   | 1.16730398 | 2.167e+0  | 3.615e+1   | 16.68 | 3.34           |
| 10  | 1.07576607 | 2.076e+0  | 9.635e+1   | 46.42 | 4.64           |
| 20  | 1.03619372 | 2.036e+0  | 2.630e+2   | 129.15| 6.46           |
| 40  | 1.01770389 | 2.018e+0  | 7.251e+2   | 359.38| 8.98           |
| 71  | 1.30357727 | 3.629e+8  | 1.304e+11  | 359.38| 5.06 (exp 09)  |

Each successive doubling of degree multiplies `k*/M₀` by ~2.78, which
is *exactly the grid spacing*. Since we resolve `k*` only up to a factor
~2.78, the true ratio between consecutive successful `k*` could be
anywhere in `[1, 2.78²] = [1, 7.7]` per doubling. But the monotone
march across all 4 degrees through consecutive sweep points is a
strong signal.

## Scaling: is it polynomial or exponential?

Two fits on the four exp-10 points:

- **Power law:** `k*/M₀ ≈ 1.55 · n^1.48`
- **Exponential:** `k*/M₀ ≈ 16.68 · exp(0.082·n)`

Both fit well on four points. But an exponential `exp(0.082·n)` at
`n = 71` would predict `k*/M₀ ≈ 16.68 · exp(5.8) ≈ 5600`, whereas
Conway actually sits at 359. The power-law extrapolation
`1.55 · 71^1.48 ≈ 852` is closer but overshoots Conway too.

Including the Conway anchor in the fit gives `k*/M₀ ≈ 2.70 · n^1.23`.
Checking back against our four:
- n=5:  predicted 22,  observed 17
- n=10: predicted 47,  observed 46
- n=20: predicted 111, observed 129
- n=40: predicted 262, observed 359
- n=71: predicted 539, observed 359

The joint fit is imperfect but order-of-magnitude consistent.

**Bottom line:** `k*/M₀ = O(poly(n))`, with exponent in the range
`[1.2, 1.5]`. **Exponential scaling `2^n` is clearly ruled out** —
`n=40` gives `k*/M₀ = 359`, not `2^40 ≈ 10^12`.

## Why the discrepancy with Conway

Conway has `n = 71` and `k*/M₀ ≈ 359`, the SAME prefactor as our
`n = 40`. Two possibilities:

1. **Our sweep resolution is coarse.** `k* = 359·M₀` for both n=40
   and n=71 could be an artifact: both happen to cross threshold
   between the same two grid points (`k/M₀ ∈ [129, 359]`). The true
   `k*` could be anywhere in that interval. In exp 09 the preceding
   grid point (`k/M₀ = 129`) also failed; here for n=40 it also fails.
   Given the factor-2.78 grid, the "true" ratio between Conway and
   our n=40 could be anywhere in `[1, 7.7]`.
2. **Conway's coefficient structure compensates.** Conway has
   `max|c_k| = 14`, but net `q(λ) = 0` forces near-exact algebraic
   cancellation of large monomials. The n-bonacci polynomials have
   `max|c_k| = 1`, so their "gross production" M₀ is near-minimal.
   Per-unit-degree, n-bonacci may actually be *harder* because its
   M₀ barely exceeds the raw monomial cancellation threshold.

Under hypothesis (2), k*/M₀ really does grow faster than naive `n^α`
when coefficient magnitude is minimal — we are probing a "pure degree"
regime.

## Trajectory behavior

All four degrees show the same qualitative story as exp 09:

- **Failures:** solver stalls early (`t ≈ 0.7–1.0`) with `u` and `v`
  both finite and small. Not a blow-up, but a stiff region where LSODA
  can't advance. The system is physically bounded; it's a numerical
  stiffness issue, not blow-up.
- **Successes:** both `u, v` converge; `u → λ`, `v → 0` with
  `v_ss ≈ M₀ / (k·λ)` as predicted by the slow-manifold analysis.

Example: n=10, k/M₀=1000, `v_final = 9.37e-4`, prediction
`M₀/(k·λ) = 1/1000/1.076 = 9.29e-4`. Ratio 1.01. Perfect.

For n=40, k/M₀=1000: `v_final = 1.023e-3`, prediction
`1/1000/1.018 = 9.82e-4`. Ratio 1.04. Perfect.

## No anomalies

- All four degrees have a unique positive real root in (1, 2) as
  advertised — confirmed by brentq bracket `[1+1e-9, 2.0]`.
- All four degrees have `q'(λ) > 0`, so SIGN = −1 is chosen for each
  and trajectory rises monotonically from 0 to λ.
- All four degrees show a clear FAIL→PASS transition in the sweep
  (no degrees fail everywhere; no degrees pass everywhere).
- `final_t` at failure is consistent within a degree (~0.7–0.8 for
  n ≥ 10, ~0.8–1.0 for n=5), and `final_t` for successes is always
  exactly `T = 5.0`.
- No solver exceptions thrown; all failures are LSODA
  `'Unexpected istate in LSODA.'` (step-size collapse), matching exp 09.

## Main takeaway

**Degree drives `k*/M₀` polynomially, not exponentially.** Power-law
exponent from our 4 points alone: `α ≈ 1.48`. If we trust the Conway
anchor, `α` drops to ~1.23 but the fit is imperfect at the endpoints.

Combined with exp 09's Conway result, the working hypothesis is

    k*(n, coeffs) ≈ A · n^α · M₀,   α ∈ [1.2, 1.5],

where `A` absorbs small coefficient-structure corrections. This rules
out two extremal possibilities:

- **NOT** `k* = Θ(M₀)` (prefactor-1 universal law). The prefactor grows
  with degree, so any uniform-in-degree constant-k theorem is false
  even for sparse integer polynomials with max|coef|=1.
- **NOT** `k* = 2^n · M₀` or similar exponential blow-up. A degree-71
  Conway only needs `k/M₀ ≈ 359`, not `10¹²`.

## Implications for the Problem 1 framework

1. A rigorous bound on `k*` in terms of polynomial data must include
   a polynomial-in-degree factor. Something of the form
   `k* ≤ C · deg^α · M₀` with `α ≈ 1.5` is plausible from these
   experiments and does not contradict Conway.
2. For the [BAC] / Ripple formalization: the "dual-rail compilation"
   from a bounded GPAC of degree `n` requires an annihilation rate
   `k` that scales like `n^{O(1)}` larger than the on-trajectory
   production. This is a much weaker constant than `2^n` but still
   non-constant.
3. The exp-08 refinement (replace norm-based bounds with M₀) is still
   the right direction. This experiment shows M₀ by itself doesn't
   suffice — we need `M₀ · poly(deg)`.

## Follow-ups

- **Resolution.** Rerun with a finer k-grid (factor ~1.3 spacing)
  around the transition to tighten `k*` estimates, especially to
  distinguish Conway-n71 from our-n40.
- **Mid-coefficient family.** Repeat with a family that has
  `max|c_k| ≈ 10` at intermediate degrees (e.g. Chebyshev-like). This
  would give a three-way scan in `(degree, coef-magnitude, structure)`.
- **Starting near λ.** Seed `y(0) = λ − δ` to remove the transient
  off-trajectory production, and check whether `k*` drops — isolating
  whether the degree factor comes from the transient or from
  steady-state cancellation structure.
