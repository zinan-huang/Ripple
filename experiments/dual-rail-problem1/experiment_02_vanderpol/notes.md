# Experiment 02 Notes — Van der Pol (biased by c = 0.5)

Date: 2026-04-18

## Setup

Original GPAC:  `x₁' = x₂,  x₂' = μ(1 − x₁²)x₂ − x₁ + c`  with `c = 0.5`,
zero init. FP `(c, 0)` unstable spiral for μ > 0, limit cycle persists.

Dual-rail: monomial-wise split of each polynomial term by sign (see
`system.md`). Constant-k annihilation `−k·u_i·v_i` on each species.

Swept μ ∈ {1, 5, 20} (weak → stiff) and k ∈ {0.1, 1, 10, 100, 1000}.
Integrator: LSODA, rtol=1e-9, atol=1e-11.

## Results

| μ | k | max u₂ | max v₂ | |x₂|_max (orig) | status |
|---|---|--------|--------|------------------|--------|
| 1 | 0.1 | **7.2 × 10⁶** | 7.2 × 10⁶ | 3.17 | BLOWUP (LSODA step → machine eps at t ≈ 1.37) |
| 1 | 1.0 | **2.8 × 10⁵** | 2.8 × 10⁵ | 3.17 | BLOWUP-ish (stiff warnings) |
| 1 | 10 | 3.30 | 1.92 | 3.17 | **bounded**, tracks limit cycle |
| 1 | 100 | 3.18 | 1.82 | 3.17 | bounded, tighter |
| 1 | 1000 | 3.17 | 1.82 | 3.17 | bounded, tightest |
| 5 | 0.1 | **2.5 × 10³** | 2.5 × 10³ | 8.08 | huge mass, likely BLOWUP |
| 5 | 1.0 | **3.8 × 10³** | 3.8 × 10³ | 8.08 | huge mass, likely BLOWUP |
| 5 | 10 | 8.83 | 7.79 | 8.08 | bounded, tracks |
| 5 | 100 | 8.13 | 7.13 | 8.08 | bounded, tighter |
| 5 | 1000 | 8.09 | 7.08 | 8.08 | bounded, tightest |
| 20 | 0.1 | **2.7 × 10⁴** | 2.7 × 10⁴ | 27.3 | huge, likely BLOWUP |
| 20 | 1.0 | 80.3 | 68.1 | 27.3 | unclear (peaks ~3× cycle max) |
| 20 | 10 | 50.0 | 50.1 | 27.3 | slightly above cycle — transient overshoot |
| 20 | 100 | 27.5 | 27.1 | 27.3 | bounded, tracks |
| 20 | 1000 | 27.3 | 27.0 | 27.3 | bounded, tightest |

At `μ = 1, k = 0.1` the LSODA solver emitted repeated
"`t + h = t` on next step" warnings starting at `t ≈ 1.375`; the
reported max values (7 × 10⁶) are from the integrator approaching blow-up
with shrinking step size. Same pattern across `k ≤ 1.0`.

## Conclusion

**Not a counterexample.** For every tested μ there is some k* ≈ 10
(maybe k* grows slowly with μ) above which the dual-rail is bounded
and tracks the underlying limit cycle. As `k → ∞`:

    u₁ → x₁⁺ = max(x₁, 0),   v₁ → x₁⁻ = max(−x₁, 0),
    u₂ → x₂⁺,                 v₂ → x₂⁻.

This is the minimal representation, exactly as predicted by the
slow-manifold / Tikhonov picture: the fast variable is `u_i · v_i` and
the slow manifold is `{u_i · v_i = 0, u_i − v_i = x_i}`.

For small k the annihilation is too weak: the positive rail receives
all of the `c = 0.5` forcing plus positive monomial production, and
without enough drain via `k·u₁·v₁`, the rails jointly blow up
before the limit cycle can establish itself. This matches the
nullcline analysis for scalar cubic (experiment 01): at small k, the
`s = u + v` dynamics are dominated by the positive polynomial part
with insufficient quadratic damping.

## k → ∞ feedback behaviour

Plots `dualrail_mu=5_k=1000.png` etc. clearly show:
- `u_i(t)` hugs `x_i⁺(t)` (the positive part of the original)
- `v_i(t)` hugs `x_i⁻(t)` (the negative part)
- Whenever `x_i` crosses zero, one rail rapidly transfers mass to the
  other via the `k·u_i·v_i` annihilation. The transient is `O(1/k)` in
  duration.

In the stiff regime (μ = 20), the `x₂` spike transitions are so fast
(on the order of `1/μ`) that for `k = 10` we see some overshoot
(u₂ peaks ~50 vs cycle max 27). At `k = 100, 1000` this is gone.

## Caveats

- I did not rigorously distinguish "huge but bounded oscillation" from
  "finite-time blow-up" for small k. LSODA warnings + values `≥ 10⁴`
  strongly suggest blow-up, but a proper check would use an event
  detector with a blow-up threshold. For the conjecture (existence of
  *some* k) this doesn't matter.
- The constant-bias Van der Pol is a mild modification; the original
  (unbiased) is a trivial zero-init GPAC because origin is a fixed
  point.

## Files

- `system.md` — system description with dual-rail expansion
- `run.py` — simulation
- `original_mu=*.png` — x₁(t), x₂(t) trajectories and phase portrait
- `dualrail_mu=*_k=*.png` — u, v trajectories compared to x = u − v
- `k_sweep_mu=5.png` — peaks vs k at μ = 5
- `summary.txt` — per-run dict summary

## Next

Experiment 03: Hopf normal form — cleaner limit cycle geometry,
frequency tunable via ω independently of amplitude. Test whether
the k-threshold cares more about *frequency* or *amplitude*.
