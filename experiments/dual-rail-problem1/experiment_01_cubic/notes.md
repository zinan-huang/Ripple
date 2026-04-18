# Experiment 01 Notes — Scalar Cubic `y' = 1 − y³`

Date: 2026-04-18

## Observations

Simulated original + dual-rail at `k ∈ {0.1, 1.0, 10, 100, 1000}` on `t ∈ [0, 30]`.

| k | max u | max v | max(u+v) | status |
|---|-------|-------|----------|--------|
| 0.1 | NaN | NaN | NaN | **finite-time blow-up** |
| 1.0 | NaN | NaN | NaN | **finite-time blow-up** |
| 10 | 1.134 | 0.134 | 1.268 | bounded |
| 100 | 1.010 | 0.010 | 1.020 | bounded |
| 1000 | 1.001 | 0.001 | 1.002 | bounded |

Original `y(t)` monotone, `y(30) ≈ 1` as expected.

## Conclusion

**Not a counterexample.** Consistent with the nullcline analysis:

    s' = 1 + s³ − (k/2)(s² − y²),   s = u + v, y = u − v ∈ [0, 1].

For `k = 0.1, 1.0` the cubic `f_k(s) = 1 + s³ − (k/2)(s² − y²)` is
positive everywhere on `[0, ∞)` (the negative trough vanishes for small k),
so `s` grows without bound, reaching blow-up in finite time.

For `k ≥ k*` (some threshold `k* ∈ (1, 10)`), the nullcline has a stable
fixed point `s* ∈ (1, ∞)`, and from `s(0) = 0` the trajectory climbs to `s*`
and stops. Larger `k` pushes `s* → 1` (the minimal representation limit).

## k → ∞ feedback behaviour

As `k` grows, `(u, v)` tracks the minimal representation `(y⁺, y⁻)` more
tightly: for `y ≥ 0`, `u → y, v → 0`. The annihilation enforces `u · v → 0`
pointwise, which combined with `u − v = y` pins each variable to its
one-sided minimal representation.

**This is a slow-manifold / Tikhonov-type picture.** For `k → ∞`, the fast
variable is `u · v` and the slow manifold is `{u · v = 0, u − v = y}`.
Quasi-steady-state reduces the dual-rail system back to the original GPAC.

## Caveats

- This matches what a singular-perturbation analysis would predict for
  degree-3 scalar. The multi-species / oscillating cases may differ.
- Finite-time blow-up for small k illustrates the *necessity* of "sufficiently
  large" k — the conjecture is not "every positive k works", it is
  "some sufficiently large k works".

## Files

- `system.md` — system description
- `run.py` — simulation
- `original.png` — y(t)
- `dualrail_k={0.1,1,10,100,1000}.png` — u, v trajectories
- `k_sweep.png` — max over k sweep (NaN at small k expected)

## Next

Move to Experiment 02: Van der Pol oscillator. Oscillating bounded trajectory
should stress the constant-k annihilation's ability to keep up with rapid
sign changes in `y`.
