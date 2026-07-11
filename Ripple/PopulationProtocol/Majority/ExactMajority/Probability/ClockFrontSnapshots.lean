/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ClockFrontSnapshots

This file states the active-band clock-front snapshot target first, then wires
the part that is actually available from the landed deterministic interfaces.

Honest status:
* `MainHourBelow (h+1)` and the stronger zero-tail snapshot
  `HourCoupling.mAbove (h+1) c = 0` are deterministically equivalent at a fixed
  config.  `ClockNoMainAbove.mAbove_succ_eq_zero_of_reachable` supplies the
  direction needed to fill the `hNoMainAbove` leaf from a pointwise hour ceiling.
* `BiasedMainIndexLeHour` is NOT produced by the landed `frontShapeAt_holds`
  theorem.  The local phase-3 induction route is machine-refuted in
  `CeilingRoute.biasedMainIndexLeHour_not_step_preserved`; any use of this
  per-agent snapshot must carry it as an external clock-front/reachability leaf.
* Once the two snapshots are present, the active-band ceiling is exactly the
  already-landed `Phase3ActiveBand.allBiasedMainBelow_of_clockFrontSnapshots`.

The file contains only deterministic wiring and checked theorem statements.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3ActiveBand
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma610StoppedAzuma
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontShapeInduction
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockNoMainAbove
import Mathlib.Tactic

namespace ExactMajority

open scoped BigOperators ENNReal

namespace ClockFrontSnapshots

variable {L K : ℕ}

/-! ## Stated first: the snapshot target and active-band ceiling -/

/-- **Clock-front snapshots on a reachable phase-3 hour-`h` endpoint, conditional form.**

This is the exact consumer shape requested by `Phase3ActiveBand`: if the clock
chain supplies the two snapshots at `top = h+1`, then the reachable endpoint
has both snapshots and the active-band global ceiling
`AllBiasedMainBelow (h+1)`.

The reachability hypothesis is retained to match the trajectory interface; the
proof does not use it because the deterministic consumer only needs the two
snapshot facts. -/
theorem clockFrontSnapshots_of_reachable
    {h : ℕ} {entry c : Config (AgentState L K)}
    (_hReach : (NonuniformMajority L K).Reachable entry c)
    (hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c)
    (hHour : WindowReconciliation.MainHourBelow (L := L) (K := K) (h + 1) c) :
    WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c ∧
      WindowReconciliation.MainHourBelow (L := L) (K := K) (h + 1) c ∧
      DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c := by
  refine ⟨hIdx, hHour, ?_⟩
  exact Phase3ActiveBand.allBiasedMainBelow_of_clockFrontSnapshots
    (L := L) (K := K) (top := h + 1) hIdx hHour

/-- **Hour snapshot from the stronger zero-tail readout.**

If no Main is strictly above `top` in the Lemma-6.10 count
`mAbove top`, then every Main's hour stamp is at most `top`, i.e.
`MainHourBelow top`.  This is deterministic bookkeeping; Lemma 6.10's current
landed Azuma statements give small tails, not this zero-tail fact. -/
theorem mainHourBelow_of_noMainAbove {top : ℕ} {c : Config (AgentState L K)}
    (hNoMainAbove : HourCoupling.mAbove (L := L) (K := K) top c = 0) :
    WindowReconciliation.MainHourBelow (L := L) (K := K) top c := by
  intro a ha hmain
  have hzero :
      Multiset.countP (fun a : AgentState L K =>
        HourCoupling.mainAboveP (L := L) (K := K) top a) c = 0 := by
    simpa [HourCoupling.mAbove] using hNoMainAbove
  have hnot := (Multiset.countP_eq_zero.1 hzero) a ha
  by_contra hle
  have hlt : top < a.hour.val := by omega
  exact hnot ⟨hmain, hlt⟩

/-- **Clock below-hour snapshot from a zero clock-tail readout.**

This is the clock-side analogue: if no Clock is counted in `cAbove top`, then
every Clock minute is below the `(top+1)K` hour boundary. -/
theorem clocksBelowHour_of_noClockAbove {top : ℕ} {c : Config (AgentState L K)}
    (hNoClockAbove : HourCoupling.cAbove (L := L) (K := K) top c = 0) :
    PositionalCluster.ClocksBelowHour (L := L) (K := K) top c := by
  intro a ha hclock
  have hzero :
      Multiset.countP (fun a : AgentState L K =>
        HourCoupling.clockAboveP (L := L) (K := K) top a) c = 0 := by
    simpa [HourCoupling.cAbove] using hNoClockAbove
  have hnot := (Multiset.countP_eq_zero.1 hzero) a ha
  by_contra hlt
  have hge : (top + 1) * K ≤ a.minute.val := by omega
  exact hnot ⟨hclock, hge⟩

/-- **Active-band ceiling from `hIdx` plus the stronger zero Main-tail leaf.**

This is the strongest snapshot wiring available here without pretending that
Lemma 6.10's small-tail Azuma conclusion is a zero-tail statement. -/
theorem allBiasedMainBelow_of_reachable_noMainAbove
    {h : ℕ} {entry c : Config (AgentState L K)}
    (hReach : (NonuniformMajority L K).Reachable entry c)
    (hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c)
    (hNoMainAbove : HourCoupling.mAbove (L := L) (K := K) (h + 1) c = 0) :
    DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c := by
  exact (clockFrontSnapshots_of_reachable (L := L) (K := K) hReach hIdx
    (mainHourBelow_of_noMainAbove (L := L) (K := K) hNoMainAbove)).2.2

/-! ## Snapshot leaves and negative evidence -/

/-- The precise per-config leaves that make the requested snapshot route close.

`hIdx` is carried explicitly because the landed front-shape theorem
`FrontShape.frontShapeAt_holds` is a clock-minute squaring/cap statement, not a
per-Main dyadic-index-vs-hour theorem.  `hNoMainAbove` is the zero-tail form
needed to turn Lemma-6.10-style counts into the pointwise `MainHourBelow`
snapshot. -/
structure SnapshotLeaves (h : ℕ) (c : Config (AgentState L K)) : Prop where
  hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c
  hNoMainAbove : HourCoupling.mAbove (L := L) (K := K) (h + 1) c = 0

/-- Fill the `hNoMainAbove` slot from the pointwise hour-ceiling snapshot. -/
theorem snapshotLeaves_of_indexLeHour_and_mainHourBelow
    {h : ℕ} {entry c : Config (AgentState L K)}
    (hReach : (NonuniformMajority L K).Reachable entry c)
    (hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c)
    (hMainHourBelow :
      WindowReconciliation.MainHourBelow (L := L) (K := K) (h + 1) c) :
    SnapshotLeaves (L := L) (K := K) h c where
  hIdx := hIdx
  hNoMainAbove :=
    ClockNoMainAbove.mAbove_succ_eq_zero_of_reachable (L := L) (K := K)
      hReach hMainHourBelow

/-- The snapshot leaves discharge the active-band clock-front ceiling. -/
theorem allBiasedMainBelow_of_snapshotLeaves
    {h : ℕ} {entry c : Config (AgentState L K)}
    (hReach : (NonuniformMajority L K).Reachable entry c)
    (hleaves : SnapshotLeaves (L := L) (K := K) h c) :
    DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (h + 1) c :=
  allBiasedMainBelow_of_reachable_noMainAbove (L := L) (K := K)
    hReach hleaves.hIdx hleaves.hNoMainAbove

/-- Re-export of the machine-checked obstruction: the tempting local induction
for `BiasedMainIndexLeHour` is false. -/
theorem biasedMainIndexLeHour_not_phase3_step_invariant
    (hL : 1 ≤ L) (base : AgentState L K) :
    ∃ s2 t2 : AgentState L K,
      (∀ (s : Sign) (i : Fin (L + 1)),
        t2.bias = Bias.dyadic s i → i.val ≤ t2.hour.val) ∧
      s2.bias = Bias.zero ∧
      (∃ (s : Sign) (i : Fin (L + 1)),
        t2.bias = Bias.dyadic s i ∧ s2.hour.val > i.val) ∧
      (∃ (s : Sign) (i : Fin (L + 1)),
        (phase3CancelSplit L K s2 t2).2.bias = Bias.dyadic s i ∧
          i.val > (phase3CancelSplit L K s2 t2).2.hour.val) :=
  CeilingRoute.biasedMainIndexLeHour_not_step_preserved (L := L) (K := K) hL base

/-- Re-export of the landed front-shape atom, recording its real output shape:
it is a clock-minute `FrontShapeAt` fact, not a `BiasedMainIndexLeHour` snapshot. -/
theorem frontShapeAt_holds_reexport {L₀ T : ℕ}
    (hT : T ≤ L₀) (c : Config (ClockTime.Minute L₀))
    (hc : 2 ≤ c.card) (h0 : ClockTime.beyond (T + 1) c = 0) :
    FrontShape.FrontShapeAt T c :=
  FrontShape.frontShapeAt_holds T hT c hc h0

/-- Status marker: the file has only deterministic wiring.  The zero-tail slot
`SnapshotLeaves.hNoMainAbove` now reduces to the pointwise hour-ceiling snapshot
`MainHourBelow (h+1)`.  The currently landed Lemma-6.10/front-shape theorems do
not derive that pointwise reachable snapshot. -/
theorem clock_front_snapshots_status : True := trivial

#print axioms clockFrontSnapshots_of_reachable
#print axioms mainHourBelow_of_noMainAbove
#print axioms clocksBelowHour_of_noClockAbove
#print axioms allBiasedMainBelow_of_reachable_noMainAbove
#print axioms snapshotLeaves_of_indexLeHour_and_mainHourBelow
#print axioms allBiasedMainBelow_of_snapshotLeaves
#print axioms biasedMainIndexLeHour_not_phase3_step_invariant
#print axioms frontShapeAt_holds_reexport

end ClockFrontSnapshots

end ExactMajority
