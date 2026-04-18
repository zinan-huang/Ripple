# Experiment 02 — Van der Pol (with constant bias)

## System

Pure Van der Pol has origin as a fixed point, so zero-init GPAC stays
stuck. To get a bounded oscillating GPAC with `y(0) = 0`, add a constant
bias `c > 0` to the `x₂` equation:

    x₁' = x₂,
    x₂' = μ (1 − x₁²) x₂ − x₁ + c,
    x₁(0) = x₂(0) = 0.

Fixed point shifts to `(c, 0)`. Linearization eigenvalues there:
trace = `μ(1 − c²)`, det = 1. For `|c| < 1` and `μ > 0`, FP is unstable
spiral; limit cycle persists (Poincaré–Bendixson).

## GPAC form (degree 3)

    p₁(x₁, x₂) = x₂,
    p₂(x₁, x₂) = μ x₂ − μ x₁² x₂ − x₁ + c.

## Dual-rail split

`x_i = u_i − v_i`. Expand `x₁² x₂ = (u₁−v₁)²(u₂−v₂)` and collect by sign:

    p̂₁⁺ = u₂,                            p̂₁⁻ = v₂.
    p̂₂⁺ = μ u₂ + μ u₁² v₂ + 2μ u₁ v₁ u₂ + μ v₁² v₂ + v₁ + c,
    p̂₂⁻ = μ v₂ + μ u₁² u₂ + 2μ u₁ v₁ v₂ + μ v₁² u₂ + u₁.

(The `+c` goes into `p̂₂⁺` since `c > 0`. The linear `−x₁` is split as
`+v₁ − u₁`.)

Constant-k ODE with `u_i(0) = v_i(0) = 0`:

    u_i' = p̂_i⁺ − k u_i v_i,
    v_i' = p̂_i⁻ − k u_i v_i.

## Properties of interest

- **Oscillation, sign changes.** `x₁` crosses the FP line at `x₁ = c`,
  but its *sign* changes too for large-amplitude cycles. `x₂` oscillates
  around 0 with amplitude scaling like `μ` in the stiff regime. This is
  the first test where `u_i, v_i` need to *swap roles* as the underlying
  `x_i` changes sign.
- **Frequency scaling with μ.** Small μ: near-harmonic, period ≈ 2π.
  Large μ: relaxation oscillation, period ≈ (3 − 2 ln 2) μ, but stiff
  spikes in `x₂` of size `O(μ²)` happening on short timescales.
- **`k → ∞` feedback.** Conjectured tracking of minimal representation
  `u_i → x_i⁺, v_i → x_i⁻`.

## Hypothesis

Bounded for all sufficiently large `k`, with a k-threshold that might
grow with μ (more oscillation frequency → more demand on annihilation).

## Why this system

Oscillation with sign changes is the minimal stress test beyond scalar
monotone convergence (experiment 01). Stiff μ tests whether constant-k
can keep up with fast transients.
