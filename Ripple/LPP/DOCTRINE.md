# Kurtz Bridge for ½e⁻¹ System

## Goal
Wire the ½e⁻¹ PP (LPP/Example.lean) end-to-end to Kurtz's mean-field convergence, establishing:
lim_{T→∞} lim_{N→∞} readout(X̄^N(T)) = ½e⁻¹ (exchanged order, weak law / convergence in probability).

## Avenues

(a) **Construct PopProtocol from IsPPImplementable**: Example.lean has `halfExpFieldPP_pp : IsPPImplementable 3 halfExpFieldPP`. Build a concrete `PopProtocol 3` with 2 reactions (F+E→G+E, E→G using x_uno), prove `meanFieldDrift = halfExpField` on the simplex.

(b) **Discharge DensityProcessFamily fields**: For this concrete PP, prove:
  - `martingale_qv_bound_uniform`: uniform martingale QV ≤ C·T/N. Mass-action rates bounded on simplex → predictable QV ≤ C/N·T → Doob maximal.
  - `gronwall_event_inclusion_uniform`: integral Gronwall on ‖X̄-x‖ ≤ ‖init error‖·e^{LT} + sup‖M‖·e^{LT}. Lipschitz constant L from quadratic rate bounds.

(c) **Wire to PLPPContinuumComputation**: The ½e⁻¹ system has a continuum of equilibria (E=0 plane). Use PLPPContinuumComputation (not Isolated), which only needs readout_tendsto (already proved: halfExpSol_F_tendsto).

(d) **Assemble exchanged limit**: Chain fixedTimeKurtzConvergence_of_kurtz_convergence_for_density_dep_ctmc + stochastic_exchanged_limit_to_target.

## Terminal conditions
- Success: `theorem halfExp_stochastic_convergence : ...` compiles sorry-free.
- Failure: mathematical impossibility (e.g. DensityProcessFamily fields genuinely unsatisfiable for this system).

## Key risk (RESOLVED / DOCUMENTED)

**x_uno**: ABANDONED. The unimolecular E→G rate needs the variable simplex sum
S = F+E+G (not a constant catalyst). Solution: direct 3-species PopProtocol with
4 reactions including E+E→G+E self-reaction.

**NoAbsorbing**: DOCUMENTED GAP. The per-N DensityProcess construction requires
NoAbsorbing (every state has positive total rate), but states with E=0 are
absorbing. The exchanged-limit theorem `halfExp_exchanged_limit_stochastic`
already works with Kurtz convergence as a hypothesis, sidestepping this issue.
The NoAbsorbing gap means we cannot currently DISCHARGE that hypothesis from
the existing CTMC infrastructure without modification.

**Design analysis (ChatGPT family3, 2026-06-27):** NoAbsorbing is NOT
mathematically necessary for Kurtz convergence. The correct approach:

1. Split events: P(error > ε) ≤ P(error > ε ∧ τ_abs > T) + P(τ_abs ≤ T)
2. On {τ_abs > T}: existing no-absorption arguments work up to time T
3. P(τ_abs ≤ T) → 0 as N → ∞ (exponentially fast for ½e⁻¹)

For ½e⁻¹: E never increases, total E-decrease rate = N·x_E = E_count.
P(E_count(T) = 0) ≤ (1 - exp(-T))^{N/2} → 0.

Implementation path: avoid conditional measures. Prove the density-process
bound on the good event {τ_abs > T}, add the bad-event probability via
union bound. This requires modifying the CTMC path layer to support frozen
paths (process stays at absorbing state forever) — the record measure is
already defined for absorbing states, but the path/martingale bridge needs
the frozen-path abstraction.

## Current status (2026-06-27, session 2)

**ExamplePP.lean** — 0 sorry, 0 axiom, build green.

Proved:
- `halfExpPP : PopProtocol 3` (4 reactions)
- `halfExpPP_meanFieldDrift_eq` (drift = halfExpFieldPP)
- `halfExpPP_boundaryCompatibleOnSimplex` (handles E+E self-reaction)
- `halfExpMeanFieldSolution` (ODE solution as MeanFieldSolution)
- `halfExp_exchanged_limit_stochastic` (end-to-end exchanged limit to ½e⁻¹)

The exchanged-limit theorem says: given Kurtz convergence (finite-horizon
mean-field convergence for halfExpPP.toRateSpec), the F-component of the
stochastic process converges to ½e⁻¹ in the exchanged order.

## Remaining: Discharge hKurtz (NoAbsorbing relaxation)

### Root cause analysis

The CTMC path infrastructure (`CTMCPath.stateAt`, `IsCompatible`,
`NonExplosive`) does not handle absorbing states correctly:

1. `stateAt t` returns `path.init` when `¬∃ n, t < path.times n`.
   For absorbing paths where times plateau at absorption time, this
   returns the INITIAL state instead of the ABSORBING state. BUG.

2. `IsCompatible` requires `∀ n, times n < times (n+1)` (strict
   monotonicity). After absorption, holding times = 0, so
   times (n+1) = times n. FAILS.

3. `NonExplosive` requires `times → ∞`. After absorption,
   times plateau at a finite value. FAILS.

All downstream lemmas (right-continuity, integrability, QV bound)
depend on IsCompatible/NonExplosive, creating the NoAbsorbing gate.

### Mathematical fact (confirmed by ChatGPT family1, family2)

NoAbsorbing is NOT required for Kurtz convergence when drift = 0 at
absorbing states. The martingale part M(t) = X(t) - X(0) - ∫F(X(s))ds
is constant after absorption (F=0 at absorbing states, X constant).
The QV bound E[sup M²] ≤ C·T/N holds because post-absorption
contributes zero increments.

### Avenue (e): frozenStateAt + absorbing-aware DensityProcess

**New file: `Ripple/CTMC/DensityDependentAbsorbing.lean`**

1. Define `CTMCPath.frozenStateAt` — same as `stateAt` for t < sup(times),
   returns absorbing state (first stateSeq stabilization) for t ≥ sup(times).

2. Define `frozenDensityProcess` — uses frozenStateAt instead of stateAt.

3. Prove frozenDensityProcess is right-continuous a.e.:
   - Before absorption: standard (strictly increasing times, stateAt works)
   - After absorption: constant (frozenStateAt returns absorbing state)
   - At absorption: right-continuous by combining the two

4. Prove realSup = ratSup a.e. from right-continuity.

5. Prove integrability from ratSup integrability + realSup = ratSup.

6. Prove QV bound using `canonical_martingale_qv_bound_of_instantQV_doob`
   (no NoAbsorbing needed — Doob input from bounded rates/jumps).

7. Construct `DensityProcess` via `toDensityProcess`.

**Terminal condition:**
- Success: `halfExp_exchanged_limit_stochastic` instantiated with
  a concrete DensityProcess family, discharging hKurtz.
- Failure: mathematical impossibility in the frozenStateAt approach.

---

# ExampleGamma Compiled System — DOCTRINE (2026-06-30)

## Goal
Replace the raw 8-variable gamma PIVP in ExampleGamma.lean with the compiled (BD + x_uno) conservative system (21 vars, 71 terms), and wire gamma_kurtz_convergence to the existing CTMC framework via ConservativeJumps.

## Avenues

(a) **Python emitter → Lean certificate**: Write a Python script that runs DecompWithBD on gamma, emits a .lean file with the compiled RateSpec (21 vars, 34 jump directions, 71 monomial terms). Verify in Lean: drift = compiled field, conservative, rates ≥ 0. Then wire to toFrozenDensityProcess.
  - Terminal success: ExampleGammaCompiled.lean compiles with ConservativeJumps proved, convergence wired.
  - Terminal failure: emitted Lean file won't typecheck in reasonable heartbeats.

(b) **Abstract pipeline route**: Use `balancingDilation gammaField` abstractly via Stages.lean. Prove ConservativeJumps from `balancingDilation_conservative`. Build generic `IsCRNImplementable.toRateSpec` bridge.
  - Terminal success: gammaRateSpec defined via balancingDilation + toRateSpec, ConservativeJumps proved generically.
  - Terminal failure: raw gammaField not IsCRNImplementable (g' = -pqv has no g factor), blocking balancingDilation_crn.

(c) **Hybrid**: Abstract BD for conservation proof + concrete reactions from Python for the RateSpec.

## Known issues
- Raw gammaField NOT IsCRNImplementable (g' = -pqv lacks g factor). Avenue (b) needs dual-railing first.
- DecompWithBD does dual-rail + v-vars + BD + x_uno internally. Uncleaned output = 21 vars.
- x_1 (mainvar = gam) missing from cleaned bdsys — need uncleaned version.
