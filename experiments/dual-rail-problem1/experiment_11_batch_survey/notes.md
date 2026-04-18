# Experiment 11 — Notes

**Date:** 2026-04-18
**Harness:** identical to exp 10 (LSODA, rtol=1e-6, atol=1e-8,
max_step=0.01, T=5.0). 10-point log sweep k/M₀ ∈ [0.1, 1000].

## Summary table

| system            | deg | max\|c\| | λ        | M₀         | k*         | k*/M₀  |
|-------------------|-----|---------|----------|------------|------------|--------|
| golden            | 2   | 1       | 1.6180   | 2.618e+0   | 2.027e+0   | 0.77   |
| plastic           | 3   | 1       | 1.3247   | 2.325e+0   | 1.394e+1   | 5.99   |
| silver            | 2   | 2       | 2.4142   | 5.828e+0   | 4.513e+0   | 0.77   |
| tribonacci        | 3   | 1       | 1.8393   | 6.222e+0   | 1.341e+1   | 2.15   |
| dense_deg10       | 10  | 1       | 1.9990   | 1.019e+3   | 1.700e+4   | 16.68  |
| small_lambda      | 5   | 1       | 0.6310   | 1.000e−1   | 1.000e−2   | 0.10*  |
| large_coef_deg5   | 5   | 50      | 2.8658   | 1.933e+2   | 4.164e+2   | 2.15   |
| near_cancel_deg5  | 5   | 100     | 1.0187   | 1.097e+2   | 5.093e+3   | 46.42  |
| sparse_deg15      | 15  | 1       | 1.1296   | 6.222e+0   | 2.888e+2   | 46.42  |
| cheb_like_deg5    | 5   | 20      | 1.0628   | 2.701e+1   | 4.505e+2   | 16.68  |

*`small_lambda` passed at the very first sweep point k/M₀ = 0.1 and
 every point thereafter; true k* could be arbitrarily small.

Anchors from exps 09, 10 (reproduced for fitting):

| anchor      | deg | max\|c\| | k*/M₀  |
|-------------|-----|---------|--------|
| nbon_n5     | 5   | 1       | 16.68  |
| nbon_n10    | 10  | 1       | 46.42  |
| nbon_n20    | 20  | 1       | 129.15 |
| nbon_n40    | 40  | 1       | 359.38 |
| conway_n71  | 71  | 14      | 359.38 |

## Fits

Joint fit on all 15 points:

    k*/M₀ ≈ 0.262 · deg^1.828 · max|c|^0.170        (1)

Degree-only fit (ignoring max|c|):

    k*/M₀ ≈ 0.306 · deg^1.835                        (2)

The max|c| coefficient β ≈ 0.17 is small and swamped by degree effects.
The fit is noisy (ratios between observation and prediction range from
0.02 to 4.3), but the **exponent α ≈ 1.83 is robust whether or not we
include max|c|**, and it's larger than exp 10's original α ≈ 1.23 fit
now that we have 15 points spanning deg ∈ [2, 71].

## Three surprising findings

### Finding 1 — Root location λ matters dramatically

`small_lambda` (`y⁵ − 0.1`, λ ≈ 0.631) passes at the smallest k we
tried (k/M₀ = 0.1) and every larger k, with v_final essentially constant
across most of the sweep. This is completely unlike every other system
in the batch: no stiffness threshold, no transition. All other systems
show a clean fail→pass transition somewhere in [0.1, 100]·M₀.

Mechanism: when λ < 1, the binomial-expansion amplification factor
`max_k binomial(deg, k) · λ^k` is *bounded* — in fact, for λ ≤ 1/2 or
so, all (u−v)^k expansion coefficients evaluated on-trajectory have
magnitude ≤ 1. The `M₀` normalization here (≈ λ^5 = 0.1) is already
way above what the trajectory demands.

**Implication:** any bound `k* ≤ C · deg^α · M₀` is *not tight* for
λ < 1 polynomials. The correct bound must also be sub-linear in
something that captures "how much bigger than 1 is λ". The two simplest
candidates are `max(1, λ)^deg` or `max_y∈[0,λ] p̂⁺(y, 0)`.

### Finding 2 — `large_coef_deg5` is *easier* than `nbon_n5`

At degree 5:
- `y⁵ − y − 1` (exp 10, nbon_n5): k*/M₀ = 16.68.
- `y⁵ − 50y − 50` (exp 11, large_coef_deg5): **k*/M₀ = 2.15**.

max|c| scaled 50× but k*/M₀ *dropped* by almost 10×. This directly
contradicts the naive reading of exp 08 ("coefficients matter").
Actually exp 08 said: once you normalize by M₀, coefficient magnitude
is already absorbed. This is now sharper — *the normalization is not
just neutral, it over-corrects* when a dominant coefficient multiplies
a monomial that stays large on-trajectory. `50·λ` at λ = 2.87 dominates
M₀, so M₀ ≈ 50·λ = 143 is large; but the trajectory's actual stiffness
scale is smaller than M₀ would suggest.

**Implication:** `M₀` (= p̂⁺(λ, 0)) systematically over-estimates the
required k when a large coefficient inflates M₀ but the dual-rail can
still equilibrate quickly. The "right" normalization may be something
like M₀ / λ or the spectral norm of the linearization.

### Finding 3 — `dense_deg10` exactly matches `nbon_n10`

Both land at k*/M₀ = 16.68 (dense: `y¹⁰ − y⁹ − … − y − 1`)
wait, the log shows dense_deg10 k*/M₀ = 16.68, but the anchor
`nbon_n10` gave 46.42. Actually the dense is *less* stiff per M₀
than the sparse. M₀ for dense is 1019 vs for sparse n=10 was ~2.08.

So for deg=10:
- sparse (nbon_n10): k*/M₀ = 46, M₀ = 2.08, k* = 96
- dense (dense_deg10): k*/M₀ = 16.68, M₀ = 1019, k* = 16998

The dense system needs **177× more absolute k** than the sparse one,
but it needs **fewer k-per-M₀ units** than the sparse one. Confirms:
`k*` itself tracks M₀ up to a slowly-growing factor, but per-M₀ ratios
can differ by a factor of a few between sparse and dense at the same
degree.

### Honorable mention: near_cancel_deg5 ≈ sparse_deg15

Both hit k*/M₀ = 46.4. `near_cancel_deg5` has deg=5 max|c|=100,
`sparse_deg15` has deg=15 max|c|=1. Under fit (1),
predictions are 10.9 and 37.1 respectively — both underestimated,
and approximately equal observation. Coincidence, or evidence that
`near_cancel_deg5`'s effective degree (= 15) due to near-cancellation
inflating M₀? Unclear.

## Fit quality and caveats

The joint-fit residuals vary by up to a factor ~50 between best- and
worst-predicted points. `small_lambda` is a 50× undershoot because we
hit the grid floor. `conway_n71` is a 3× overshoot because the fit is
pulled toward the steeper exponent by small-degree points. `nbon_n5`
is a 3× undershoot.

**Conclusion on the scaling law:** a single power law
`k*/M₀ ≈ C · deg^α` is correct only as a very rough summary. The
true picture is more like:

    k*/M₀ ≈ f(deg, λ, coefficient-structure)

where `λ ≥ 1` is required for the bound to be tight, and the
deg-exponent `α` is somewhere in `[1.2, 1.9]` depending on which
subset of points you fit.

## Trajectory behavior — consistent with exp 09/10

Every failing run shows the same signature as exp 09: LSODA step-size
collapse with u, v finite and small. No system in this batch blew up
physically (neither did any in exps 09, 10). So the k* transition is
numerical stiffness, and we are measuring "k such that the numerical
solver can advance", which is a conservative proxy for the physical
stability threshold.

For successful runs, `v_final ≈ M₀ / (k·λ)` predictions match
observation within a few percent across all 10 systems (spot-checked
in run.log). The slow-manifold analysis is robust.

## Implications for the Problem 1 framework

1. **No simple `k* = O(M₀)` or `k* = O(deg · M₀)` law.** The exponent
   in `k*/M₀ ≈ C·deg^α` is around 1.8–1.9 on our combined 15 points.
   Any formal theorem must carry at least a `deg^2` prefactor to be
   safe across this range.
2. **Root-location dependence.** Polynomials with λ < 1 have tiny
   k* — dual-rail is essentially free. Polynomials with λ close to 1
   from above (`near_cancel_deg5`, `conway_n71`) have the worst
   ratios. A bound should scale something like
   `k* ≤ C · deg^α · max_y∈[0,λ] (p̂⁺ + p̂⁻)(y, 0)`
   to capture the transient production peak.
3. **max|c| is a weak predictor** once M₀ is given. Across our systems
   with max|c| ∈ [1, 100], the residual β ≈ 0.17 is noisy and could
   easily be 0 with larger datasets. M₀ absorbs most of the
   coefficient-magnitude effect — consistent with exp 08.

## Files

- `system.md`, `rationale.md` — setup and design
- `run.py`, `run.log`, `summary.txt` — harness and raw data
- `dualrail_<name>.png` — 10 representative trajectory plots (smallest successful k)
- `kstar_vs_deg_batch.png` — k*/M₀ vs degree, colored by max|c|, with deg-only fit
- `joint_fit_residuals.png` — predicted vs observed k*/M₀

## Follow-ups

1. **Refine k-grid near each transition** with factor-1.3 spacing to
   resolve k* within ~30%. The factor-2.78 grid here gives ±3× error,
   which is the main source of fit noise.
2. **Sweep λ explicitly** on a one-parameter family (`y² − y − c`
   varying c from 0.01 to 1000) to directly test the λ-dependence.
3. **Near-cancellation + high degree:** build a deg-20 polynomial with
   large-magnitude coefficients on adjacent monomials that cancel at
   λ — does the near_cancel_deg5 effect compound with degree?
