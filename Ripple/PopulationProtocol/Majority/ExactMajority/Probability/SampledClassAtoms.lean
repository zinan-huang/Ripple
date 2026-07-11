/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# PkgEAtoms — slot-5 sampled-class concentration surface

Package E targets the `WorkInputsFull` fields

* `εConc` — the concentration budget scalar;
* `hConc` — the sampled-class floor tail at the slot-5 horizon
  `∑ m ∈ Finset.Icc 1 M₀, tWin5 m`.

Landed pieces used here:

* `SamplingAtoms.hrfloor_of_floors` proves ATOM 1, the rate floor, from the reserve and class floors.
* `SampledClassTail.hConcDemand_of_real_window` and
  `SamplingAtoms.hConcDemand_of_atoms` assemble the killed sampled-class tail.
* `ClockCeiling.clocksBelowHour_of_goodWidth` is the deterministic width readout:
  `GoodFrontWidth` plus the bulk-behind condition gives `ClocksBelowHour`.
* `WidthTransport.widthFail_between_checkpoints_concrete` is the closest landed probabilistic width
  export, but its event is a width failure event.  It does not yet export the sampled-potential prefix
  event that `SampledClassTail` consumes.

The remaining width export needed for a full discharge is therefore named explicitly below:
`phase5WidthSurvivalExport`.  It is exactly the uniform prefix bound
`SamplingAtoms.clockSeparationEscape` needs, at the slot-5 horizon.  Once supplied, this file produces
the exact `WorkInputsFull.hConc` field shape.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SamplingAtoms
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCeiling

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SampledClassAtoms

open Phase5Convergence ReserveSampling SampledClassTail SamplingAtoms

variable {L K : ℕ}

/-- The minimal missing Phase-5 width/survival export for Package E.

This is the precise event-level bridge not currently exported by the width files: for every Phase-5
start and every prefix time before the slot-5 horizon, the mass of states whose sampled-class deficit
potential is still at the failure threshold is bounded by `β`.

The landed width chain currently provides the deterministic implication
`ClockCeiling.clocksBelowHour_of_goodWidth` (`ClockCeiling.lean:133`) and a width-failure tail
`WidthTransport.widthFail_between_checkpoints_concrete` (`WidthTransport.lean:421`).  A full Package E
closure needs those to be connected to this sampled-potential prefix event. -/
def phase5WidthSurvivalExport (n : ℕ) (s : ℝ) (i : Fin (L + 1)) (K₀ t : ℕ)
    (β : ℝ≥0∞) : Prop :=
  SamplingAtoms.clockSeparationEscape (L := L) (K := K) n s i K₀ t β

/-- The named width/survival export is exactly the ATOM-2 escape shape consumed by
`SamplingAtoms.hConcDemand_of_atoms`. -/
theorem clockSeparationEscape_of_widthSurvivalExport
    (n : ℕ) (s : ℝ) (i : Fin (L + 1)) (K₀ t : ℕ) (β : ℝ≥0∞)
    (hwidth : phase5WidthSurvivalExport (L := L) (K := K) n s i K₀ t β) :
    SamplingAtoms.clockSeparationEscape (L := L) (K := K) n s i K₀ t β :=
  hwidth

/-- Re-export of the landed deterministic width readout used by the intended width-survival proof.

This theorem does not itself bound `hConc`; it records the strongest currently landed width fact in
the direction needed for ATOM 2.  The missing step is the probabilistic export from this clock-front
confinement surface to `phase5WidthSurvivalExport`. -/
theorem clocksBelowHour_of_phase5_width_good {h W : ℕ} (hK : 0 < K)
    (c : Config (AgentState L K))
    (hgood : ClockFrontProfile.GoodFrontWidth (L := L) (K := K) W c)
    (hbulk : 10 * ClockRealKernel.rBeyond (L := L) (K := K) ((h + 1) * K - W) c < c.card) :
    PositionalCluster.ClocksBelowHour (L := L) (K := K) h c :=
  ClockCeiling.clocksBelowHour_of_goodWidth (L := L) (K := K) hK c hgood hbulk

/-- Package E adapter producing the exact `WorkInputsFull.hConc` field shape.

Field produced: `WorkBuilder.WorkInputsFull.hConc`, namely the slot-5 sampled-class floor tail at
the horizon `∑ m ∈ Finset.Icc 1 M₀, tWin5 m`.

Carried remainder: `phase5WidthSurvivalExport`, plus the one-step exit bridge `hbridge` already
required by `SampledClassTail.hConcDemand_of_real_window`.  The width files currently stop short of
exporting these sampled-potential events; the closest landed anchors are listed in the definition
comment for `phase5WidthSurvivalExport`. -/
theorem hConc_field_of_atoms_and_widthSurvival
    (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (reserveFloor classFloor : ℕ)
    (hbudget : reserveFloor * classFloor ≤ n * (n - 1))
    (hres : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      reserveFloor ≤ (unsampledReserves (L := L) (K := K)).sum c.count)
    (hcls : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      classFloor ≤ (classMainStates (L := L) (K := K) σ i).sum c.count)
    (K₀ M₀ : ℕ) (tWin5 : ℕ → ℕ) (εConc : ℝ≥0)
    (hbridge : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      sampledClassPot (L := L) (K := K) i s c
          < ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ)))) →
      (NonuniformMajority L K).transitionKernel c
        (sampledClassGate (L := L) (K := K) n)ᶜ = 0)
    (β : ℝ≥0∞)
    (hwidth : phase5WidthSurvivalExport (L := L) (K := K) n s i K₀
      (∑ m ∈ Finset.Icc 1 M₀, tWin5 m) β)
    (hε : ∀ c₀, Phase5AllWin (L := L) (K := K) n c₀ →
      (ENNReal.ofReal (1 - SamplingAtoms.rateFloor reserveFloor classFloor n * (1 - Real.exp (-s))) ^
            (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)
          * sampledClassPot (L := L) (K := K) i s c₀ + 0)
        / ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
      + (((∑ m ∈ Finset.Icc 1 M₀, tWin5 m) : ℕ) : ℝ≥0∞) * β ≤ (εConc : ℝ≥0∞)) :
    ∀ c₀, ReserveSampling.Phase5AllWin (L := L) (K := K) n c₀ →
      ReserveSampling.unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
      ((NonuniformMajority L K).transitionKernel ^ (∑ m ∈ Finset.Icc 1 M₀, tWin5 m)) c₀
        {c | ¬ Phase5Convergence.sampledFloor (L := L) (K := K) i K₀ c} ≤
          (εConc : ℝ≥0∞) := by
  classical
  have hesc : SamplingAtoms.clockSeparationEscape (L := L) (K := K) n s i K₀
      (∑ m ∈ Finset.Icc 1 M₀, tWin5 m) β :=
    clockSeparationEscape_of_widthSurvivalExport (L := L) (K := K) n s i K₀
      (∑ m ∈ Finset.Icc 1 M₀, tWin5 m) β hwidth
  have hdemand := SamplingAtoms.hConcDemand_of_atoms (L := L) (K := K) σ i hiL n hn s hs
    reserveFloor classFloor hbudget hres hcls K₀ M₀
    (∑ m ∈ Finset.Icc 1 M₀, tWin5 m) εConc hbridge β hesc hε
  intro c₀ hwin hbud
  exact hdemand c₀ hwin hbud

#print axioms clockSeparationEscape_of_widthSurvivalExport
#print axioms clocksBelowHour_of_phase5_width_good
#print axioms hConc_field_of_atoms_and_widthSurvival

end SampledClassAtoms

end ExactMajority
