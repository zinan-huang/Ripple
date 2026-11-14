/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty et al. §10 — the SEAM DISCHARGE (`SeamDischarge`): C10.

`Assembly.ResidualAtomsFull` carries the seam half as five fields
(`seamP seamT εepidemic εovershoot hDrift hNoOvershoot`) plus the three theorem-arg
glue pins (`hPost2Win hSeedEvent hWin2Pre`).  This file discharges the two QUANTITATIVE
seam fields — `hDrift` and `hNoOvershoot` — at the genuine epidemic / counter budgets,
REUSING the landed Phase-D-4 engines, and records the precise residual status of the
three glue pins.

## What is discharged here (0 sorry / 0 axiom / no native_decide)

### 1. `hDrift` — FULLY DISCHARGED.
`AdvanceEpidemics.advance_drift` PROVES the seam epidemic drift bound at abstract `p`
(the parameter-`p` clone of the Phase-4 non-tie epidemic, `geCount (p+1)`-drift, rate
`m(n−m)/(n(n−1))`).  Its `hε` input is BYTE-IDENTICAL to the budget-fit LHS that C9's
`EpidemicConvergence.epidemicBudget_calibrated` certifies `≤ 1/n²`.  So the per-seam
drift budget is the GENUINE per-phase failure budget `εepidemic k = (1/n²).toNNReal`,
supplied EXACTLY as C9 supplied the slot-4 budget.  `advance_hDrift` builds the
whole `∀ k` field; the per-seam rate `s k > 0` and the `Θ(log n)` horizon-fit
`(n/α)·(s(n−1)+2 log n) ≤ seamT k` are the only inputs.

### 2. `hNoOvershoot` — DISCHARGED to its structural carries.
`AdvanceNoOvershoot.advance_noOvershoot_tail` PROVES the per-seam no-overshoot tail
`≤ tseam·e^{−40(L+1)}` from the deterministic single-step overshoot→at-risk bridge
`OvershootForcesZeroClock p` (the FROZEN-protocol structural fact, carried per-seam) plus
the Stage-4 per-`τ` at-risk tails.  `advance_hNoOvershoot` builds the `∀ k` field
from those carries, with budget `εovershoot k`.

**ANTI-TRAP / GENUINE GAP.**  The clock counter is monotone-DECREASING, so the
no-overshoot tail is built from the CUMULATIVE first-exit prefix-union
(`noOvershoot_window_le_prefix_sum`), NOT a one-step closure — consistent with the
anti-trap.  But the V7 field is keyed on the seam `Pre` (`allPhaseGe p n ∧
advTriggered (p+1)`), whereas `advance_noOvershoot_tail` starts from `NoOvershoot p c₀`.
`allPhaseGe p n` bounds phases BELOW (`≥ p`), NOT above, so it does NOT entail
`NoOvershoot p` (`∀ a, phase < p+2`) pointwise.  The bridge between the two start
predicates is therefore a genuine per-seam carry `hPreToNoOvershoot` (the seam-entry
config has not yet overshot — a timing-separation fact, NOT derivable from the
`≥`-window alone).  We expose it as an explicit input rather than smuggling it.

### 3. The glue pins — PRECISELY ISOLATED TRUE RESIDUALS.
`hPost2Win`/`hWin2Pre` are pointwise interface maps between the PRODUCED concrete work
family `workConcrete ra` and the seam `≥`-windows; they depend on the concrete work `Post`/`Pre`
predicates (which are abstract in `ResidualAtomsFull`), so they cannot be discharged
generically — TRUE residuals to be pinned per concrete instantiation.  `hSeedEvent`
(`SeedStepAndSignThreading.SeedStepEvent`) is the genuine one-step seed remainder: per
`SeedStepAndSignThreading.seedStepEvent_needs_drained_state`, the phase-only genuine work `Post` does
NOT supply the drained all-clock un-seeded state the free timed seed requires, so
`SeedStepEvent` survives — a TRUE residual.  We re-export the precise shapes.

## Reuse summary
* C9 (`EpidemicConvergence.epidemicBudget_calibrated`) → the `hDrift` budget `1/n²`,
  exactly the slot-4 reuse pattern.
* D-4 (`AdvanceEpidemics.advance_drift`) → the seam drift bound (the same `geCount`-epidemic).
* §6 (`AdvanceNoOvershoot.advance_noOvershoot_tail`/`hNoOvershoot_one_advance`) → the
  no-overshoot tail.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.SeedStepAndSignThreading
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceNoOvershoot
import Ripple.PopulationProtocol.ExactMajority.Probability.EpidemicConvergence
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceInstancesCore

namespace Ripple.PopulationProtocol.ExactMajority
namespace AdvanceInstances

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — `hDrift`, FULLY DISCHARGED at the calibrated `1/n²` epidemic budget. -/

/-- **The single-seam drift bound at the calibrated `1/n²` budget.**  Chains
`AdvanceEpidemics.advance_drift` (the abstract-`p` epidemic drift) with C9's
`EpidemicConvergence.epidemicBudget_calibrated` (the budget-fit LHS `≤ 1/n²`).  The
horizon fit is the genuine `Θ(log n)` epidemic time
`(n/α)·(s(n−1) + 2 log n) ≤ tseam`, `α = 1 − e^{−s}`. -/
theorem advance_drift_inv_sq (p n tseam : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (hT : ((n : ℝ) / EpidemicConvergence.epiAlpha s)
            * (s * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (tseam : ℝ))
    (c : Config (AgentState L K))
    (hPre : AdvanceEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
      AdvanceEpidemics.advTriggered (L := L) (K := K) (p + 1) c) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c
        {c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
      ≤ ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) :=
  AdvanceEpidemics.advance_drift p n hn s hs tseam (Real.toNNReal (1 / (n : ℝ) ^ 2))
    (EpidemicConvergence.epidemicBudget_calibrated hn hs hT) c hPre

/-- **The full `hDrift` field, DISCHARGED.**  Produces the entire `∀ (k : Fin 10)` drift
field of `Assembly.ResidualAtomsFull` at the per-seam calibrated budget
`εepidemic k := (1/n²).toNNReal`, from a per-seam positive rate `s k` and a per-seam
horizon fit on `seamT k`.  This is the seam-half analogue of how C9 discharged slot 4. -/
theorem advance_hDrift (n : ℕ) (hn : 2 ≤ n)
    (seamP seamT : Fin 10 → ℕ) (s : Fin 10 → ℝ)
    (hs : ∀ k, 0 < s k)
    (hT : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (s k))
            * (s k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ)) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) :=
  fun k c hPre => advance_drift_inv_sq (seamP k) n (seamT k) hn (s k) (hs k) (hT k) c hPre

-- `inv_sq_budget_lt_one` is now provided by `SeamDischargeCore` (imported above)
-- to break the Assembly chain dependency for Capstone.

/-! ## Part 2 — `hNoOvershoot`, DISCHARGED to its structural carries.

The V7 `hNoOvershoot` field is keyed on the seam `Pre`; the landed tail
(`AdvanceNoOvershoot.advance_noOvershoot_tail`) is keyed on a `NoOvershoot p` START.  Since
the `≥`-window does NOT bound phases above, the START bridge `hPreToNoOvershoot` is an
explicit per-seam carry (a timing-separation fact). -/

/-- **The single-seam no-overshoot bound from its structural carries.**  Composes the
`Pre → NoOvershoot p` start carry with `AdvanceNoOvershoot.advance_noOvershoot_tail`
(prefix-union of the Stage-4 at-risk tails, via the deterministic bridge `hdet`).  The
resulting overshoot probability is `≤ tseam · e^{−40(L+1)} ≤ εovershoot` when the budget
fit `hε` holds. -/
theorem advance_noOvershoot_le_of_tail_budget (p tseam : ℕ) (εovershoot : ℝ≥0)
    (hdet : AdvanceNoOvershoot.OvershootForcesZeroClock (L := L) (K := K) p)
    (hε : (tseam : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
            ≤ (εovershoot : ℝ≥0∞))
    (c : Config (AgentState L K))
    (hStart : AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c)
    (hτ : ∀ τ ∈ Finset.range tseam,
      ((NonuniformMajority L K).transitionKernel ^ τ) c
          {c' | AdvanceNoOvershoot.AtRiskClockZero (L := L) (K := K) p c'}
        ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c
        {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) p c'}
      ≤ (εovershoot : ℝ≥0∞) :=
  le_trans
    (AdvanceNoOvershoot.advance_noOvershoot_tail p tseam hdet c hStart hτ) hε

/-- **The full `hNoOvershoot` field, DISCHARGED to its structural carries.**  Produces
the entire `∀ (k : Fin 10)` no-overshoot field of `Assembly.ResidualAtomsFull`,
from the per-seam deterministic bridge `hdet`, the per-seam budget fits `hε`, the
per-seam `Pre → NoOvershoot` start carry `hPreToNoOvershoot`, and the per-seam Stage-4
at-risk tails `hτ`.  All four are genuine carries (the bridge + at-risk tails are the
FROZEN-protocol structural facts; the start carry is the timing-separation fact the
`≥`-window does not supply). -/
theorem advance_hNoOvershoot (n : ℕ)
    (seamP seamT : Fin 10 → ℕ) (εovershoot : Fin 10 → ℝ≥0)
    (hdet : ∀ k, AdvanceNoOvershoot.OvershootForcesZeroClock (L := L) (K := K) (seamP k))
    (hε : ∀ k, (seamT k : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
            ≤ (εovershoot k : ℝ≥0∞))
    (hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c)
    (hτ : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | AdvanceNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞) :=
  fun k c hPre =>
    advance_noOvershoot_le_of_tail_budget (seamP k) (seamT k) (εovershoot k)
      (hdet k) (hε k) c (hPreToNoOvershoot k c hPre) (hτ k c hPre)

/-! ## Part 3 — the glue pins, PRECISELY ISOLATED as TRUE residuals.

These are NOT discharged: they depend on the concrete work family (abstract in
`ResidualAtomsFull`) / on the drained all-clock seed state the phase-only genuine Post
does not supply.  We re-export their precise shapes so an instantiator pins them. -/

/-- **`hSeedEvent` residual shape** (re-export of `SeedStepAndSignThreading.SeedStepEvent`).  Per
`SeedStepAndSignThreading.seedStepEvent_needs_drained_state`, the phase-only genuine work `Post` does
NOT entail the drained all-clock un-seeded state the FREE timed seed requires, so this
`SeedStepEvent` survives as a TRUE one-step residual.  An instantiator supplies it from
the SEAM-entry configuration (which carries the drained all-clock state), NOT from the
work `Post`. -/
def SeedEvent (workPost : Config (AgentState L K) → Prop) (p : ℕ) : Prop :=
  SeedStepAndSignThreading.SeedStepEvent (L := L) (K := K) p workPost

/-- The seed-event residual is EXACTLY the `hSeedEvent` argument shape consumed by
`Assembly.toResidualFull`: `∀ k, SeedStepEvent (seamP k) ((work …).Post)`. -/
theorem seedEvent_eq_field
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ) (k : Fin 10) :
    SeedEvent (L := L) (K := K) (work ⟨k.val, by omega⟩).Post (seamP k)
      = SeedStepAndSignThreading.SeedStepEvent (L := L) (K := K) (seamP k)
          (work ⟨k.val, by omega⟩).Post := rfl

/-! ## Part 4 — the wired V7 residual seam half (drift + no-overshoot), packaged.

A drop-in bundle for the four V7 seam-half fields `(εepidemic, εovershoot, hDrift,
hNoOvershoot)`, with `εepidemic k := (1/n²).toNNReal` and `εovershoot k` carried, ready
to `refine` into `ResidualAtomsFull`.  The glue (`hPost2Win`/`hSeedEvent`/`hWin2Pre`)
remains the explicit theorem-arg residual. -/
structure AdvanceHalf (n : ℕ) where
  seamP : Fin 10 → ℕ
  seamT : Fin 10 → ℕ
  εepidemic : Fin 10 → ℝ≥0
  εovershoot : Fin 10 → ℝ≥0
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)

/-- **The assembled seam half.**  Both quantitative fields discharged: `hDrift` at the
genuine `1/n²` epidemic budget (via `advance_hDrift`), `hNoOvershoot` at the
carried `εovershoot` (via `advance_hNoOvershoot`). -/
noncomputable def buildAdvanceHalf (n : ℕ) (hn : 2 ≤ n)
    (seamP seamT : Fin 10 → ℕ) (s : Fin 10 → ℝ) (εovershoot : Fin 10 → ℝ≥0)
    (hs : ∀ k, 0 < s k)
    (hTdrift : ∀ k, ((n : ℝ) / EpidemicConvergence.epiAlpha (s k))
            * (s k * ((n : ℝ) - 1) + 2 * Real.log n) ≤ (seamT k : ℝ))
    (hdet : ∀ k, AdvanceNoOvershoot.OvershootForcesZeroClock (L := L) (K := K) (seamP k))
    (hεNO : ∀ k, (seamT k : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))
            ≤ (εovershoot k : ℝ≥0∞))
    (hPreToNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      AdvanceNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c)
    (hτ : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (AdvanceEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        AdvanceEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ∀ τ ∈ Finset.range (seamT k),
        ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | AdvanceNoOvershoot.AtRiskClockZero (L := L) (K := K) (seamP k) c'}
          ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))) :
    AdvanceHalf (L := L) (K := K) n where
  seamP := seamP
  seamT := seamT
  εepidemic := fun _ => Real.toNNReal (1 / (n : ℝ) ^ 2)
  εovershoot := εovershoot
  hDrift := advance_hDrift n hn seamP seamT s hs hTdrift
  hNoOvershoot :=
    advance_hNoOvershoot n seamP seamT εovershoot hdet hεNO hPreToNoOvershoot hτ

/-! ## Axiom audit (verified by `#print axioms`). -/

#print axioms advance_drift_inv_sq
#print axioms advance_hDrift
#print axioms inv_sq_budget_lt_one
#print axioms advance_noOvershoot_le_of_tail_budget
#print axioms advance_hNoOvershoot
#print axioms buildAdvanceHalf

end AdvanceInstances
end Ripple.PopulationProtocol.ExactMajority
