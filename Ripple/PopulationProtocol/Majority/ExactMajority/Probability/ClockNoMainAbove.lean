/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ClockNoMainAbove

This file states first the deterministic zero-tail readout requested by the
clock snapshot chain:

  if the clock/Main hour snapshot says every Main has `hour <= h+1`, then
  `HourCoupling.mAbove (h+1) c = 0`.

The theorem deliberately consumes the already named pointwise snapshot
`WindowReconciliation.MainHourBelow`.  The currently landed Lemma 6.10 files
prove Azuma tail bounds for the coupling potential; they do not by themselves
produce this pointwise zero-tail snapshot.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowReconciliation
import Mathlib.Tactic

namespace ExactMajority

open scoped BigOperators ENNReal

namespace ClockNoMainAbove

variable {L K : ℕ}

/-! ## Statement first -/

/-- **No Main above the next hour from the pointwise hour ceiling.**

On a reachable phase-3 hour-`h` endpoint, once the clock/Main coupling has
supplied the pointwise snapshot `MainHourBelow (h+1)`, the Lemma-6.10 count
`mAbove (h+1)` is zero.  The reachability hypothesis is retained to match the
trajectory interface; the proof itself is deterministic bookkeeping. -/
theorem mAbove_succ_eq_zero_of_reachable
    {h : ℕ} {entry c : Config (AgentState L K)}
    (_hReach : (NonuniformMajority L K).Reachable entry c)
    (hMainHourBelow :
      WindowReconciliation.MainHourBelow (L := L) (K := K) (h + 1) c) :
    HourCoupling.mAbove (L := L) (K := K) (h + 1) c = 0 := by
  unfold HourCoupling.mAbove
  apply Multiset.countP_eq_zero.2
  intro a ha
  rintro ⟨hmain, habove⟩
  exact not_lt_of_ge (hMainHourBelow a ha hmain) habove

/-- The same deterministic readout at an arbitrary top hour. -/
theorem mAbove_eq_zero_of_mainHourBelow
    {top : ℕ} {c : Config (AgentState L K)}
    (hMainHourBelow :
      WindowReconciliation.MainHourBelow (L := L) (K := K) top c) :
    HourCoupling.mAbove (L := L) (K := K) top c = 0 := by
  unfold HourCoupling.mAbove
  apply Multiset.countP_eq_zero.2
  intro a ha
  rintro ⟨hmain, habove⟩
  exact not_lt_of_ge (hMainHourBelow a ha hmain) habove

#print axioms mAbove_succ_eq_zero_of_reachable
#print axioms mAbove_eq_zero_of_mainHourBelow

end ClockNoMainAbove

end ExactMajority
