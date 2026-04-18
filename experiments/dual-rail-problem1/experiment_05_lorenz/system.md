# Experiment 05 — Lorenz Attractor

## System

Classical Lorenz system (σ = 10, ρ = 28, β = 8/3), with a small bias
`c > 0` on `x` to kick off zero-init dynamics (origin is a saddle):

    x' = σ(y − x) + c,
    y' = x(ρ − z) − y,
    z' = x y − β z.

Bounded for all initial conditions (trajectories stay inside the
attractor or approach it). Famously chaotic — aperiodic orbit on the
butterfly-shaped attractor, `|x|, |y| ≲ ~20`, `z ≲ ~50`.

Zero init plus `c = 0.1`: the small bias moves `x` away from origin,
trajectory enters the attractor region.

## GPAC form (degree 2 — simpler than degree-3 experiments!)

    p₁(x,y,z) = σ y − σ x + c,
    p₂(x,y,z) = ρ x − x z − y,
    p₃(x,y,z) = x y − β z.

All terms are degree ≤ 2. This makes the dual-rail split cleaner and
lets us test whether low degree gives lower k*.

## Dual-rail

`xᵢ = uᵢ − vᵢ`. Each bilinear term `x y = (u₁ − v₁)(u₂ − v₂)` expands
to four monomials, two positive (u₁ u₂, v₁ v₂) and two negative
(u₁ v₂, v₁ u₂). Similarly for `x z`.

    p̂₁⁺ = σ u₂ + σ v₁ + c
    p̂₁⁻ = σ v₂ + σ u₁
    (σ(y-x) = σu₂ - σv₂ - σu₁ + σv₁)

    p̂₂⁺ = ρ u₁ + u₁ v₃ + v₁ u₃ + v₂
         (ρ x positive part from u₁; −x z positive parts from the -(u₁u₃ - u₁v₃ - v₁u₃ + v₁v₃)
          flipped: +u₁v₃ + v₁u₃; −y positive part from +v₂)
    p̂₂⁻ = ρ v₁ + u₁ u₃ + v₁ v₃ + u₂

    p̂₃⁺ = u₁ u₂ + v₁ v₂ + β v₃
    p̂₃⁻ = u₁ v₂ + v₁ u₂ + β u₃

## Properties of interest

- **Degree 2 only.** Lowest degree among experiments so far.
- **Chaotic dynamics.** `x, y` change sign frequently and aperiodically.
- **Fast time scales.** `σ = 10` is a relaxation rate, making some
  transients quick.
- **Larger amplitude.** `|x|` up to ~20, `|y|` up to ~27, `|z|` up to ~50.
  Good stress test for absolute-magnitude vs coefficient-magnitude
  hypothesis.

## Hypothesis

Degree-2 polynomial should be easier for constant-k dual-rail than
degree-3 (fewer high-order products in p̂⁺, p̂⁻). Expect k* possibly
lower than k* ≈ 100 from Hopf/Brusselator. Chaotic sign changes may or
may not matter, based on experiments 02, 03.

## Why this system

- Famous canonical bounded dynamical system.
- Chaotic (aperiodic), stress-tests annihilation without periodicity.
- Degree 2 (vs degree 3 in 01–04), separates degree effect from
  amplitude effect.
