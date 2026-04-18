# Experiment 11 — Batch Survey of 10 Polynomial Systems

**Date:** 2026-04-18
**Harness:** identical to exp 10 (LSODA, rtol=1e-6, atol=1e-8, max_step=0.01,
T=5.0, 10-point log sweep over k/M₀ ∈ [0.1, 1000]).

## Polynomial family

Ten scalar systems `y' = -q(y)` (or `+q(y)` if q'(λ) < 0). In every case
λ ∈ (0, 3) is a stable positive real root, and the trajectory from
y(0) = 0 approaches λ.

| # | name              | q(y)                                     | deg | max\|c\| | λ (approx) |
|---|-------------------|------------------------------------------|-----|---------|------------|
| 1 | golden            | y² − y − 1                               | 2   | 1       | 1.6180     |
| 2 | plastic           | y³ − y − 1                               | 3   | 1       | 1.3247     |
| 3 | silver            | y² − 2y − 1                              | 2   | 2       | 2.4142     |
| 4 | tribonacci        | y³ − y² − y − 1                          | 3   | 1       | 1.8393     |
| 5 | dense_deg10       | y¹⁰ − y⁹ − … − y − 1                      | 10  | 1       | 1.9990     |
| 6 | small_lambda      | y⁵ − 0.1                                 | 5   | 1       | 0.6310     |
| 7 | large_coef_deg5   | y⁵ − 50y − 50                            | 5   | 50      | 2.8658     |
| 8 | near_cancel_deg5  | 100y⁵ − 100y⁴ − y − 1                    | 5   | 100     | 1.0187     |
| 9 | sparse_deg15      | y¹⁵ − y¹⁰ − y⁵ − 1                        | 15  | 1       | 1.1296     |
| 10| cheb_like_deg5    | 16y⁵ − 20y³ + 5y − 3 (Chebyshev shifted) | 5   | 20      | 1.0628     |

See `rationale.md` for why each one was chosen.

## Dual-rail split

Same construction as exp 09/10: for each monomial `c_k · y^k`, expand
`y = u − v` using binomial theorem, route each resulting term to `p̂⁺`
or `p̂⁻` by sign. Dynamics:

    u' = p̂⁺(u, v) − k·u·v
    v' = p̂⁻(u, v) − k·u·v

with y ≈ u − v on the slow manifold.

## Metric extracted

For each system:
- `M₀ = max(p̂⁺(λ, 0), p̂⁻(λ, 0))` — on-trajectory production at fixed point.
- 10-point log sweep k/M₀ ∈ [0.1, 1000].
- `k*` = smallest k in the sweep for which the dual-rail runs cleanly to
  T = 5.0 with finite (u, v) and matches the slow-manifold prediction
  `v_final ≈ M₀ / (k·λ)`.

## Fit target

Joint scaling law:  `k*/M₀ ≈ C · deg^α · (max|c|)^β`.

Exp 08 said β ≈ 0 when max|c| is absorbed into M₀ (M₀ ∝ max|c|).
Exp 10 said α ∈ [1.2, 1.5] for sparse max|c|=1 systems.
This batch should disambiguate.
