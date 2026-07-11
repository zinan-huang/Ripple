# MassActionRaceLaw Construction — Design Document

## Goal

Construct `MassActionRaceLaw N (Omega N)` for any CRN with positive rates,
using Mathlib's Ionescu-Tulcea theorem (`Kernel.trajFun`).  This eliminates
the conditional hypothesis in `MassActionBridge.lean`.

## Architecture

### Sample Space

```
X n := Option N.I   (uniform for all n)
Omega := (n : ℕ) → X n = (n : ℕ) → Option N.I
```

Coordinate 0 is a dummy (fixed to `none`).
CRN firing at time t is read from coordinate t+1.

### Probability Space (Mathlib route)

1. Build `massActionPMF : State S → PMF (Option N.I)` from propensities
2. Build `stepKernel : (n : ℕ) → Kernel (Prefix n) (Option N.I)` via
   `Kernel.ofFunOfCountable (fun p => (massActionPMF (stateFromPrefix z0 p)).toMeasure)`
3. `rawLaw := Kernel.trajFun stepKernel 0 initialPrefix : Measure Omega`
4. `isProbabilityMeasure_trajFun` gives normalization

### ProbSpec Bridge

```lean
ProbSpec.ofMeasure μ := { Pr := fun E => μ E }
ProbAxioms.ofMeasure := { mono := measure_mono, ... }
```

### raceBound Proof

Given `hstate : ∀ ω, state(ω,t) = z`:
1. Rewrite event: `{ω | fired t ≠ i} = {ω | ω(t+1) ≠ some i}` (by fired = choiceAt)
2. `hstate` implies `∀ prefix, stateFromPrefix prefix = z` (by extendPrefix)
3. Use `traj_comp_partialTraj` + `map_traj_succ_self`:
   marginal at t+1 = stepKernel t = massActionPMF(z).toMeasure
4. `massActionPMF(z){≠ some i} = 1 - prop(i,z)/total(z)` (finite arithmetic)

## Module Structure

| File | Purpose | Est LOC |
|------|---------|---------|
| `MeasureBridge.lean` | `ProbAxioms.ofMeasure` | ~80 |
| `MassAction/Weights.lean` | `massActionPMF`, normalization, bad-event bound | ~200 |
| `MassAction/Traj.lean` | Omega, decoder, stepKernel, rawLaw | ~250 |
| `MassAction/RaceLaw.lean` | path, raceBound, final `massActionRaceLaw` | ~200 |
| **Total** | | **~730** |

## Key Mathlib API

- `Kernel.ofFunOfCountable` — kernel from countable domain
- `Kernel.trajFun` — Ionescu-Tulcea trajectory measure
- `isProbabilityMeasure_trajFun` — probability measure
- `map_traj_succ_self` — marginal at next coordinate = step kernel
- `traj_comp_partialTraj` — composition property
- `PMF.toMeasure` — PMF to measure
- `measure_mono`, `measure_union_le` — for ProbAxioms

## ChatGPT Design Rounds

- R1 research1 (Pro): Kernel.traj route, 3-layer bridge
- R1 research2 (xhigh): OuterMeasure route (fallback)
- R2 research1 (Pro): Full Lean skeleton, stepKernel via ofFunOfCountable, raceBound calc
- R2 research2 (xhigh): pending
- Decision: Pro route (Kernel.trajFun) confirmed after API verification

## Status

- [x] API verification: `Kernel.trajFun` compiles against Mathlib v4.30
- [ ] MeasureBridge.lean
- [ ] MassAction/Weights.lean
- [ ] MassAction/Traj.lean
- [ ] MassAction/RaceLaw.lean

## ChatGPT R3 Critical Finding (2026-06-14)

`ClockBoundedLaw.microstepBound` universally quantifies over ALL enabled
reactions as "intended". For combined comp+clock CRN, this is unsatisfiable
with small ε — clock reactions as "intended" require ε ≥ 1.

**Fix**: bypass ClockBoundedLaw for the unconditional theorem. Go directly:
  raceBound (computation reaction only) → union bound → total error ≤ δ

This uses raceBound (already proved in MassAction/RaceLaw.lean) with
a SCHEDULE that specifies which reaction is "intended" at each microstep.
The existing MultiStepRace.lean has union bound infrastructure.

**Impact**: ClockBoundedLaw.ofMassAction and stochastic_error_le_of_massAction
are NOT suitable for the concrete combined CRN. They are correct for
single-component CRNs where all enabled reactions are "computation."
The unconditional theorem needs a different path.
