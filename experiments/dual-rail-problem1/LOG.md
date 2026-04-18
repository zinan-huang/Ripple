# UCNC25 Problem 1 — Constant-k Dual-Rail Boundedness: Experiment Log

**Target problem.** For a bounded GPAC `y' = p(y)` (i.e. `y(t) ∈ (-β, β)^n`
for some `β > 0` on `[0, ∞)`), is there a constant `k > 0` such that the
dual-railed system

    u_i' = p̂_i⁺(u, v) - k · u_i · v_i,
    v_i' = p̂_i⁻(u, v) - k · u_i · v_i,
    u_i(0) = v_i(0) = 0,

keeps `u, v` bounded on `[0, ∞)`?

Known: the `Z = p̂⁺ + p̂⁻` polynomial-scaled version is bounded (DNA25).

## Strategy

- Collect candidate bounded GPACs from the literature, preferring those with
  structure that might stress the constant-k annihilation (high oscillation,
  multi-species coupling, high polynomial degree, near-singular dynamics).
- For each, simulate both the original GPAC and the dual-railed system at a
  sweep of `k` values, log the `max_{t ∈ [0, T]} (u_i + v_i)` trend.
- Plot both the original trajectory and the `u_i, v_i` trajectories at
  selected `k`.
- Record observations: bounded / unbounded, `k*` (if any) where behavior
  flips, shape of instability, `k → ∞` limiting behavior.

## Experiment template (per file)

Each experiment lives in `experiment_NN_slug/`:

    experiment_NN_slug/
    ├── system.md          -- plain-language system description + why we're
    │                         trying this system
    ├── run.py             -- numerical simulation + plotting
    ├── original.png       -- original GPAC trajectory
    ├── dualrail_k=....png -- dual-rail trajectories at selected k values
    ├── k_sweep.png        -- boundedness as function of k
    └── notes.md           -- observations, conclusions, follow-ups

## Running index

| # | System | Source | Features | Status | Conclusion |
|---|--------|--------|----------|--------|------------|
| 01 | `y' = 1 − y³` | degree-3 pedagogical | high degree, monotone → 1 | done | bounded for k ≥ ~10; small k blow up; nullcline analysis matches |
| 02 | biased Van der Pol | oscillator | limit cycle, sign-changing, stiff μ | done | bounded for k ≳ 10 across μ ∈ {1, 5, 20}; Tikhonov to minimal repr; k* independent of μ |

(more to come)

## Candidate systems to try

Prioritized queue:

1. **Van der Pol oscillator** (bounded limit cycle). `y'' − μ(1−y²)y' + y = 0`
   rewritten as first-order. Features: stable limit cycle, oscillation
   frequency tunable via `μ`. Hypothesis: high `μ` (stiff) might stress
   constant-k annihilation.
2. **Brusselator** (bounded periodic). Two-species chemical oscillator
   `x' = A + x²y − Bx − x`, `y' = Bx − x²y`. Original is bounded for
   suitable parameters; positive-only so trivial after shift. Might still
   be useful after offset shift to push into GPAC form with bounded oscillation.
3. **Lotka-Volterra with saturation**. `x' = x(1 − x) − xy/(1+x)`, etc.
   Rational → polynomial after dual-railing a denominator. Features:
   multi-species, possible oscillation.
4. **Hopf normal form**. `y_1' = y_1 − y_1·(y_1²+y_2²) − ω·y_2`,
   `y_2' = y_2 − y_2·(y_1²+y_2²) + ω·y_1`. Stable circular limit cycle of
   radius 1, frequency ω. Clean high-frequency test case.
5. **Bournez-Pouly constructions for exponentially-growing intermediates**
   (from [bournez.pdf] / [lacl19.pdf]). Candidates where internal intermediate
   variables are large even though the output is bounded.
6. **Chua's circuit** (chaotic but bounded).
7. **Lorenz attractor**. Bounded chaos. Probably most stressful for constant-k
   if any.
8. **Any GPAC computing a specific irrational via a polynomial ODE
   with a high-degree intermediate** (from RTCRN1 / Bounded). These
   match the CRN computability context directly.

## Log conventions

- Timestamp each entry in `notes.md`.
- Save all plots as PNG, not PDF, so they render in MD previews.
- If a system starts looking like a counterexample, mark it **⚠ candidate**
  in the running index and spend extra effort on it.
- If an experiment needs a re-run with different parameters, archive the
  old `notes.md` section with a date stamp rather than deleting.
