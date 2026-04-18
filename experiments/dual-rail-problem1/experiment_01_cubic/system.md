# Experiment 01 — Scalar Cubic `y' = 1 − y³`

## System

Single-variable bounded GPAC:

    y'(t) = 1 − y(t)³,   y(0) = 0.

## Properties

- Monotone, converges to `y = 1` (unique real fixed point of `y³ = 1`).
- Bounded: `y(t) ∈ [0, 1]` on `[0, ∞)`.
- Degree 3 polynomial — higher than the "safe" quadratic degree, so a
  naive scaling argument *might* predict unbounded dual-rail for constant k.

## Dual-rail

Let `y = u − v`. Then

    p(y) = 1 − y³ = 1 − (u − v)³
         = 1 − u³ + 3u²v − 3uv² + v³.

Split into positive / negative monomials:

    p̂⁺(u, v) = 1 + 3u²v + v³,
    p̂⁻(u, v) = u³ + 3uv².

Constant-k ODEs:

    u' = 1 + 3u²v + v³ − k · u · v,
    v' = u³ + 3uv²    − k · u · v,
    u(0) = v(0) = 0.

## Hypothesis

By the `s = u + v` analysis (`s' = 1 + s³ − (k/2)(s² − y²)` with
`y = u − v` bounded by 1), the nullcline `s' = 0` has a stable fixed
point near `s = 1` for all `k > 0` (sufficiently large). So we expect
**bounded u, v** for all reasonable `k`, with the steady state approaching
the minimal representation `(u, v) ≈ (1, 0)` as `k` grows.

## Why this system

Simple, scalar, high-degree (degree 3). If the conjecture fails anywhere,
it would be nice if it failed here, but the nullcline analysis already
predicts success. Good sanity-check baseline.
