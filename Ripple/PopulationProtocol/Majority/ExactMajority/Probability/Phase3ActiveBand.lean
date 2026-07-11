/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-3 active-band ceiling for the MassToCount / Lemma-6.13 consumers

Verdict: the active-band ceiling is NOT a phase-3-local consequence of the
per-agent predicate `index ≤ own hour`.  The frozen split gate uses the OTHER
agent's hour, and `CeilingRoute.biasedMainIndexLeHour_not_step_preserved`
machine-checks the one-step counterexample.  The sound carried quantity is the
GLOBAL clock-front ceiling
`DoublingEdges.AllBiasedMainBelow (h+1) c`.

This file therefore states the consumer theorem first and carries the
clock-front ceiling explicitly.  The deterministic consumer wiring is then
closed: the carried ceiling feeds `MassToCount.biasedMainCount_le_of_mass` and
the Lemma-6.13 `O_h` floors.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MassToCount
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCeiling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CeilingRoute
import Mathlib.Tactic

namespace ExactMajority
namespace Phase3ActiveBand

open scoped BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Stated first: the reachable active-band readout -/

/-- **Active-band readout on a reachable phase-3 hour window.**

Reachability is carried to match the phase-3 trajectory interface, but it is
not the source of the ceiling.  The source is the §6 clock-front/global-ceiling
event `hClockFrontCeiling`.  This is deliberate: the phase-3-local per-agent
route is refuted in `CeilingRoute.biasedMainIndexLeHour_not_step_preserved`;
the sound phase-3 invariant is the global ceiling carried here. -/
theorem allBiasedMainBelow_of_reachable
    {h : ℕ} {entry c : Config (AgentState L K)}
    (_hReach : (NonuniformMajority L K).Reachable entry c)
    (hClockFrontCeiling :
      DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c) :
    DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c :=
  hClockFrontCeiling

/-! ## The clock-front source and the local-route refutation -/

/-- The landed snapshot bridge that can construct the carried global ceiling
when the clock-front machinery supplies the two relevant snapshots.  This is a
re-export of `ClockCeiling.allBiasedMainBelow_of_snapshots`; it is not a
phase-3-local proof. -/
theorem allBiasedMainBelow_of_clockFrontSnapshots
    {top : ℕ} {c : Config (AgentState L K)}
    (hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c)
    (hHour : WindowReconciliation.MainHourBelow (L := L) (K := K) top c) :
    DoublingEdges.AllBiasedMainBelow (L := L) (K := K) top c :=
  ClockCeiling.allBiasedMainBelow_of_snapshots hIdx hHour

/-- Machine-checked witness that the tempting phase-3-local per-agent route is
false: `BiasedMainIndexLeHour` is not preserved by one frozen split step. -/
theorem phase3_local_perAgent_route_false
    (hL : 1 ≤ L) (base : AgentState L K) :
    ∃ s2 t2 : AgentState L K,
      (∀ (s : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic s i → i.val ≤ t2.hour.val) ∧
      s2.bias = Bias.zero ∧
      (∃ (s : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic s i ∧ s2.hour.val > i.val) ∧
      (∃ (s : Sign) (i : Fin (L + 1)),
        (phase3CancelSplit L K s2 t2).2.bias = Bias.dyadic s i ∧
          i.val > (phase3CancelSplit L K s2 t2).2.hour.val) :=
  CeilingRoute.biasedMainIndexLeHour_not_step_preserved (L := L) (K := K) hL base

/-! ## Consumers: MassToCount and Lemma 6.13 -/

/-- The active-band ceiling supplied by the clock-front event feeds the
deterministic mass-to-count conversion. -/
theorem biasedMainCount_le_of_mass_on_reachable
    (h : ℕ) {entry : Config (AgentState L K)} (rho M : ℝ)
    (c : Config (AgentState L K))
    (hReach : (NonuniformMajority L K).Reachable entry c)
    (hClockFrontCeiling :
      DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c)
    (hMass :
      MassToCount.totalDyadicMass (L := L) (K := K) c
        ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) c : ℝ)
      ≤ 2 * rho * M :=
  MassToCount.biasedMainCount_le_of_mass (L := L) (K := K) h rho M c
    (allBiasedMainBelow_of_reachable (L := L) (K := K) hReach hClockFrontCeiling)
    hMass

/-- Lemma-6.13 `O_h` floor with the active-band premise discharged from the
carried clock-front ceiling. -/
theorem ofuel_floor_of_mass_on_reachable
    (l h : ℕ) {entry : Config (AgentState L K)} (rho M : ℝ)
    (c : Config (AgentState L K))
    (hReachTraj : (NonuniformMajority L K).Reachable entry c)
    (hReached :
      (97 / 100 : ℝ) * M
        ≤ (Lemma613OFloor.phase3ReachedMainCount (L := L) (K := K) l c : ℝ))
    (hClockFrontCeiling :
      DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c)
    (hMass :
      MassToCount.totalDyadicMass (L := L) (K := K) c
        ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (97 / 100 - 2 * rho) * M
      ≤ (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ) :=
  Lemma613OFloor.ofuel_floor (L := L) (K := K) l rho M c hReached
    (biasedMainCount_le_of_mass_on_reachable (L := L) (K := K) h rho M c
      hReachTraj hClockFrontCeiling hMass)

/-- Final-hour Lemma-6.13 floor with the active-band premise discharged from
the carried clock-front ceiling. -/
theorem ofuel_floor_final_hour_of_mass_on_reachable
    (l h : ℕ) {entry : Config (AgentState L K)} (M : ℝ)
    (c : Config (AgentState L K))
    (hM : 0 ≤ M)
    (hReachTraj : (NonuniformMajority L K).Reachable entry c)
    (hReached :
      (97 / 100 : ℝ) * M
        ≤ (Lemma613OFloor.phase3ReachedMainCount (L := L) (K := K) l c : ℝ))
    (hClockFrontCeiling :
      DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c)
    (hMass :
      MassToCount.totalDyadicMass (L := L) (K := K) c
        ≤ Lemma616TotalMass.Constants.rho_lm1 * M * (2 : ℝ) ^ (-(h : ℤ))) :
    (15 / 100 : ℝ) * M
      ≤ (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ) :=
  Lemma613OFloor.ofuel_floor_final_hour (L := L) (K := K) l M c hM hReached
    (biasedMainCount_le_of_mass_on_reachable (L := L) (K := K) h
      Lemma616TotalMass.Constants.rho_lm1 M c hReachTraj hClockFrontCeiling hMass)

#print axioms allBiasedMainBelow_of_reachable
#print axioms allBiasedMainBelow_of_clockFrontSnapshots
#print axioms phase3_local_perAgent_route_false
#print axioms biasedMainCount_le_of_mass_on_reachable
#print axioms ofuel_floor_of_mass_on_reachable
#print axioms ofuel_floor_final_hour_of_mass_on_reachable

end Phase3ActiveBand
end ExactMajority
