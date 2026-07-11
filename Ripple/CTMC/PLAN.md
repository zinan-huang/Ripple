# CTMC Module — Porting Plan

## Goal

Build Lean 4 CTMC infrastructure and use it to **constructively instantiate**
`Ripple.Kurtz.DensityProcess`. Currently DensityProcess is a structure whose
fields (martingale decomposition, QV bound) are assumed. With CTMC we can
PROVE these fields from the CTMC definition.

## Scope (what we need for Kurtz, nothing more)

### Phase 1: DTMC (Discrete-Time Markov Chain)

File: `Ripple/CTMC/DTMC.lean`

- `MarkovChain` structure: countable state space S, transition kernel K : S → S → ℝ≥0
  (row-stochastic). Use Mathlib's `PMF` or `MeasureTheory.Kernel`.
- n-step transition: `stepN K n s t` = K^n(s,t)
- Chapman-Kolmogorov: `stepN K (m+n) s t = ∑ u, stepN K m s u * stepN K n u t`
- Irreducibility: `∀ s t, ∃ n, stepN K n s t > 0`

### Phase 2: CTMC (Continuous-Time Markov Chain)

File: `Ripple/CTMC/CTMC.lean`

- Q-matrix (generator): `QMatrix S` = function `q : S → S → ℝ` with `q s s = -∑_{t≠s} q s t`
- Embedded DTMC: jump probabilities `p s t = q s t / (-q s s)` for s ≠ t
- Holding times: exponential with rate `-q s s`
- Jump-and-hold construction: path from Q-matrix
- Forward Kolmogorov equation: `P'(t) = P(t) · Q` (differential equation for transition matrix)

Dependencies: Mathlib exponential distribution, Mathlib measurable functions.

### Phase 3: Density-Dependent CTMC

File: `Ripple/CTMC/DensityDependent.lean`

- `DensityDepCTMC`: CTMC on (1/N)·ℤ^d with rates q^N(x, x+ℓ) = N·β_ℓ(x/N)
- Martingale decomposition: PROVE M^N(t) = X̄^N(t) - X̄^N(0) - ∫₀ᵗ F(X̄^N(s))ds is a martingale
- QV bound: PROVE E[sup ‖M^N‖²] ≤ CT/N from bounded jump sizes and rates

### Phase 4: Bridge

File: `Ripple/CTMC/Bridge.lean`

- Construct `DensityProcess` instance from `DensityDepCTMC`
- Every field of DensityProcess proved, not assumed

## What Mathlib Already Has

- `MeasureTheory.Kernel.Kernel` — Markov kernels between measurable spaces
- `MeasureTheory.Kernel.comp` — kernel composition
- `MeasureTheory.Kernel.IsSFiniteKernel` — s-finite kernel class
- Ionescu-Tulcea: `MeasureTheory.Kernel.ionescuTulcea` — product measures from kernels
- `ProbabilityTheory.Kernel` — probability kernels
- `MeasureTheory.Measure.exponential` — might exist, needs checking
- Filtrations: `MeasureTheory.Filtration`
- Conditional expectation: `MeasureTheory.condexp`
- Martingales: `MeasureTheory.Martingale`

## Architecture Decision: Countable vs General State Space

For Kurtz's theorem we only need **countable** (actually finite) state spaces.
The CTMC state space is (1/N)·ℤ^d ∩ [0,1]^d, which is finite for each N.
Use `Fintype` or `Countable` instances, not general measurable spaces.

This simplifies everything: sums instead of integrals, PMF instead of kernels,
matrices instead of operators.

## Non-Goals

- MDP (Markov Decision Processes)
- pCTL model checking
- General-state Markov processes
- Stationary distributions (not needed for Kurtz)
- Ergodicity (not needed for Kurtz)
