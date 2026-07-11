# Ripple/LPP — Stochastic Double Limits

Snapshot: 2026-06-27 (updated from 2026-05-19).

## Recent: ExamplePP.lean (2026-06-27)

The first concrete instantiation of the Kurtz bridge for a specific system:
`halfExp_exchanged_limit_stochastic` proves the exchanged-order double limit
for the ½e⁻¹ population protocol, with Kurtz convergence as a hypothesis.

Key pieces:
- `halfExpPP : PopProtocol 3` — 4 reactions including E+E self-reaction
- `halfExpPP_meanFieldDrift_eq` — drift = halfExpFieldPP
- `halfExpPP_boundaryCompatibleOnSimplex` — handles non-InputsDistinct reaction
- `halfExpMeanFieldSolution` — bridges ODE solution to PopProtocol.toRateSpec
- `halfExp_exchanged_limit_stochastic` — the exchanged limit theorem

The construction bypasses `PLPPTransitions` and works directly with
`PopProtocol.toRateSpec`, avoiding the need to build a transition table.

Remaining gap: `NoAbsorbing` fails for the ½e⁻¹ system (all-G state is
absorbing). The exchanged-limit theorem sidesteps this by taking Kurtz
convergence as input rather than constructing the DensityProcessFamily.

This note records the intended meaning of the two stochastic limits around
`Ripple/LPP/Stochastic.lean`, and which extra hypotheses are mathematically
reasonable in the LPP setting.

## Current Formal State

`Stochastic.lean` separates two deterministic computation notions.

- `PLPPContinuumComputation`: a concrete ODE trajectory from rational simplex
  initial data whose marked readout tends to the target. This matches the
  extended LPP notion where a computation may converge by trajectory/readout,
  not necessarily by an isolated equilibrium.
- `PLPPIsolatedComputation`: a stronger classical/BFK-style package with an
  isolated simplex equilibrium, a basin, convergence to the equilibrium, and
  exponential decay.

The file already proves the ODE/readout part of the exchanged-order limit:

- `exchanged_limit_readout`: for the continuum notion, readout convergence is
  exactly a field of the structure.
- `exchanged_limit_isolated`: for the isolated notion, full-state convergence
  to the equilibrium implies marked-readout convergence by continuity of the
  finite sum readout.

What is not yet fully formalized is the outer stochastic wrapper saying that,
for each fixed finite time horizon, the finite-population density process
converges in probability to the ODE solution by Kurtz.

## The Two Orders

There are two different mathematical statements.

### Exchanged Order: `lim_t lim_N`

Informally:

```text
lim_{t -> infinity} [lim_{N -> infinity} readout(X^N(t))] = nu.
```

This is the easy order.

For each fixed `t`, Kurtz gives

```text
readout(X^N(t)) -> readout(x(t)) in probability, as N -> infinity.
```

Then the deterministic LPP construction gives

```text
readout(x(t)) -> nu, as t -> infinity.
```

This order only needs finite-horizon mean-field convergence. It does not need
any statement about the finite-`N` chain after very long time.

Expected Lean formulation:

```lean
-- schematic
theorem exchanged_limit_stochastic
    (C : PLPPContinuumComputation tr marked ν)
    (X : (N : ℕ) -> DensityProcess n tr.toRateSpec N μ)
    (h_init : X_N(0) -> C.sol 0 in probability)
    (h_kurtz_inputs : ... finite-horizon Gronwall/QV assumptions ...) :
    -- for every fixed t, readout(X_N(t)) -> readout(C.sol t),
    -- and therefore the outer deterministic t-limit is ν
```

The current `Kurtz.MeanField` infrastructure already has the right type of
finite-horizon convergence theorem. The remaining work is packaging readout as
a continuous map and threading the `PLPPTransitions.toRateSpec` bridge.

### Standard Order: `lim_N lim_t`

Informally:

```text
lim_{N -> infinity} [lim_{t -> infinity} readout(X^N(t))] = nu.
```

This is not a consequence of Kurtz alone.

Kurtz controls

```text
sup_{0 <= s <= T} ||X^N(s) - x(s)||
```

for each fixed finite `T`. The constants normally depend on `T`, often
exponentially through Gronwall. That theorem gives no direct control after
letting `t -> infinity` for a fixed finite `N`.

For fixed `N`, the question is instead about the long-time behavior of a
finite CTMC on a finite lattice. That requires Markov-chain recurrence,
communicating classes, stationary distributions, absorbing classes, or a
uniform-in-time stochastic stability theorem. None of this is contained in
finite-horizon Kurtz.

## Better Replacement for the Standard Iterated Limit

The most useful statement is not the literal pointwise iterated limit. It is a
uniform large-time concentration statement:

```text
for all eps > 0 and eta > 0,
there exist N0 and T0 such that for all N >= N0 and all t >= T0,
  P(|readout(X^N(t)) - nu| > eps) <= eta.
```

This is the right formal target for the BFK/Koegler isolated-equilibrium
setting. It implies the intended "large population, long time" behavior without
having to separately prove that each fixed-`N` process has a pointwise
`t -> infinity` limit.

The existing placeholder

```lean
standard_limit_concentration_skeleton
```

should be replaced by a theorem with approximately this shape, not by a bare
`Filter.Tendsto` over `lim_N lim_t` unless a finite-`N` limiting law has first
been defined.

## Reasonable Extra Assumptions

There are three levels of assumptions, from weakest to strongest.

### Level 1: finite-horizon Kurtz assumptions

Reasonable and already aligned with the code.

Assume:

- a family `X N` of `DensityProcess n tr.toRateSpec N μ`;
- initial density convergence in probability to the ODE initial condition;
- the Gronwall event inclusion / QV hypotheses required by
  `kurtz_mean_field_convergence` or `kurtz_convergence_for_density_dep_ctmc`.

Consequence:

- fixed-horizon convergence in probability;
- exchanged-order stochastic theorem.

This is valid for both `PLPPContinuumComputation` and
`PLPPIsolatedComputation`.

### Level 2: isolated ODE equilibrium plus uniform stochastic stability

Reasonable for the classical BFK/Koegler theorem, but not automatic from
Kurtz.

Assume:

- `PLPPIsolatedComputation tr marked ν`;
- finite-population initial states converge into the basin of the ODE
  equilibrium, or are initialized from a lattice approximation inside the
  basin;
- a uniform large-time concentration theorem, for example Koegler Corollary 2:

```text
for all eps eta > 0,
there exist N0 T0 such that for all N >= N0 and t >= T0,
  P(dist(X^N(t), eq.point) > eps) <= eta.
```

Consequence:

- standard-order concentration for the marked readout follows by continuity
  of the finite readout map.

This is the right assumption to introduce if the goal is to connect BFK-style
isolated stable PLPPs to finite-population stochastic computation.

### Level 3: stationary / finite-`N` long-time limit assumptions

Stronger and more Markov-chain-specific.

Assume for each `N`:

- the finite CTMC has a limiting distribution from the chosen initial law,
  or a unique stationary distribution in the relevant closed communicating
  class;
- the stationary readout concentrates at `ν` as `N -> infinity`.

Consequence:

- a literal `lim_N lim_t` statement can be formulated and proved.

This is mathematically legitimate, but it is not the best first formal target
for Ripple. It would force the development to reason about finite CTMC
ergodicity/closed classes, which is orthogonal to the algebraic LPP
construction.

## Which Assumptions Fit LPP?

For the extended LPP construction used by the Stage pipeline, isolated
equilibrium should not be assumed by default.

The Stage construction proves a trajectory/readout convergence statement. It
does not, as currently formalized, produce:

- a unique isolated equilibrium;
- a basin of attraction;
- exponential stability;
- finite-`N` stationary concentration.

Therefore:

- exchanged-order stochastic convergence is the natural theorem for the full
  general LPP pipeline;
- standard-order concentration should be stated only under an additional
  isolated/stochastic-stability hypothesis.

For BFK/Koegler-style derandomized protocols, isolated stability assumptions
are more natural for the original/marginal readout, but full-state convergence
of the derandomized product system to the independent replicated point is false
in general. The correct derandomization target is readout/marginal convergence,
not convergence of all product-state coordinates.

### Derandomized Full-State Counterexample

The false target was:

```text
every trajectory near replicatedPoint converges in full product state to
replicatedPoint = uniformLift(x*)
```

This is not true, even when the original two-state PLPP has an isolated stable
interior equilibrium.

Concrete counterexample:

- original state set `d = 2`, common denominator `m = 2`;
- derandomization slots

```text
(0,0,0) -> (1,1),  (0,0,1) -> (0,0)
(0,1,0) -> (0,0),  (0,1,1) -> (1,0)
(1,0,0) -> (0,0),  (1,0,1) -> (0,1)
(1,1,0) -> (0,0),  (1,1,1) -> (0,0)
```

The induced original PLPP has stable isolated equilibrium

```text
x* = (2/3, 1/3)
```

with simplex derivative `F0'(2/3) = -3`. The replicated product point over
states `(0,0),(0,1),(1,0),(1,1)` is

```text
y* = (1/3, 1/3, 1/6, 1/6).
```

In the pure correlation direction

```text
z = (1, -1, -1, 1),
```

which has zero original marginal and zero coin marginal to first order, the
product Jacobian satisfies

```text
J z = (1/3) z.
```

Thus `replicatedPoint` is linearly unstable in the full product simplex. This
rules out any general full-state Lyapunov theorem with
`replicatedSqLyapunov -> 0`.

This does not contradict Koegler's p.93 argument: that proof controls the
original marginal plus the cyclic coin marginal defect. It does not claim full
joint-state convergence to the independent product point. This also matches
the LPP paper's Definition 9, where computation is readout convergence.

The file `Derandomization.lean` now follows this split:

- unconditional algebraic/readout theorem:
  `derandomize_preserves_continuum_computation`;
- isolated-to-continuum readout theorem, given a concrete rational-initialized
  basin trajectory:
  `derandomize_preserves_isolated_as_continuum_of_solution`;
- no general theorem claiming full-state convergence to `replicatedPoint`.

## Formalization Recommendation

Do not try to prove the literal standard order from the existing Kurtz theorem.
Instead add two explicit theorem layers.

### 1. Exchanged stochastic theorem

Name suggestion:

```lean
theorem exchanged_limit_stochastic_readout
```

Inputs:

- `C : PLPPContinuumComputation tr marked ν`;
- a density-process family for `tr.toRateSpec`;
- initial convergence in probability;
- the existing Kurtz finite-horizon hypotheses.

Output:

- fixed-time stochastic readout convergence to `C.sol t`;
- composed with `C.readout_tendsto`, the exchanged-order interpretation.

This theorem should be unconditional with respect to isolated equilibria.

### 2. Standard large-time concentration theorem

Name suggestion:

```lean
structure UniformLongTimeConcentration ...
theorem standard_limit_concentration
```

Structure fields:

```lean
concentrates :
  ∀ eps > 0, ∀ eta > 0,
    ∃ N0 : ℕ, ∃ T0 : ℝ, 0 < T0 ∧
      ∀ N ≥ N0, ∀ t ≥ T0,
        μ {ω | ‖X N t ω - hcomp.eq.point‖ > eps} ≤ ENNReal.ofReal eta
```

Then prove the readout version by Lipschitz/continuity of

```lean
fun x => ∑ i ∈ marked, x i
```

This cleanly isolates the hard stochastic stability theorem from the algebraic
PLPP-to-ODE and PLPP-to-RateSpec work.

## Red Line

The following claim should not be stated without extra assumptions:

```text
Kurtz finite-horizon convergence + ODE convergence implies
lim_{N -> infinity} lim_{t -> infinity} readout(X^N(t)) = ν.
```

It is false as a proof principle. The order `t -> infinity` first asks about
finite-population long-time Markov-chain behavior, which finite-horizon Kurtz
does not control.
