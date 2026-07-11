import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3StaticInvDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3AdapterBridge

/-!
# Slot-3 strict-cut timing discharge.

This file isolates the remaining deterministic timing fact for the slot-3 leaf:
on a synchronous good-clock trace, Doty's Sections 6.13--6.16 cuts must place the
`afterMass` cut strictly before the hour-end first passage.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly
namespace Slot3StrictCutTimingDischarge

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

open Slot3LeafTailDischarge
open Slot3StaticInvDischarge

/-- First-passage start times are independent of the proof that the start event
is eventually hit. -/
theorem start_h_eq_of_exists
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (hex1 hex2 :
      ∃ τ, Phase3GoodClock.StartHit (L := L) (K := K) θ h (tr τ)) :
    Phase3GoodClock.start_h (L := L) (K := K) θ tr h hex1 =
      Phase3GoodClock.start_h (L := L) (K := K) θ tr h hex2 := by
  simp [Phase3GoodClock.start_h, Phase3GoodClock.firstPassage]

/-- First-passage end times are independent of the proof that the end event is
eventually hit. -/
theorem end_h_eq_of_exists
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (hex1 hex2 :
      ∃ τ, Phase3GoodClock.EndHit (L := L) (K := K) θ h (tr τ)) :
    Phase3GoodClock.end_h (L := L) (K := K) θ tr h hex1 =
      Phase3GoodClock.end_h (L := L) (K := K) θ tr h hex2 := by
  simp [Phase3GoodClock.end_h, Phase3GoodClock.firstPassage]

theorem goodClock_start_eq_goodClockUpTo_start
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
    (U : Phase3GoodClockRegime.GoodClockUpTo
      (L := L) (K := K) D.M θ tr D.lastCoreHour)
    {h : ℕ} (hh : h ≤ D.lastCoreHour) :
    (coreInput (L := L) (K := K) D θ tr G h).start =
      Phase3GoodClockRegime.GoodClockUpTo.start (L := L) (K := K) U hh := by
  exact start_h_eq_of_exists
    (L := L) (K := K) (θ := θ) (tr := tr) (h := h)
    (G.start_exists h) (U.quantile.start_exists h hh)

theorem goodClock_finish_eq_goodClockUpTo_finish
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
    (U : Phase3GoodClockRegime.GoodClockUpTo
      (L := L) (K := K) D.M θ tr D.lastCoreHour)
    {h : ℕ} (hh : h ≤ D.lastCoreHour) :
    (coreInput (L := L) (K := K) D θ tr G h).finish =
      Phase3GoodClockRegime.GoodClockUpTo.finish (L := L) (K := K) U hh := by
  exact end_h_eq_of_exists
    (L := L) (K := K) (θ := θ) (tr := tr) (h := h)
    (G.end_exists h) (U.quantile.end_exists h hh)

/-- The single remaining Doty Sections 6.13--6.16 clock-timing fact needed here:
for every good-clock window up to `D.lastCoreHour`, the `afterMass` cut
`start + 2/c + 47/M` is strictly inside the hour.  The surrounding adapter
lemmas name the non-strict H13/H16 compatibility facts via
`Slot3AdapterBridge.clockCutHourLen`; this residual is precisely the missing
strict version at the leaf surface. -/
structure StrictCutTiming613_616
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop where
  afterMass_lt_finish :
    ∀ (U : Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour)
      (h : ℕ) (hh : h ≤ D.lastCoreHour),
      Phase3Core.ClockCut.afterMass (L := L) (K := K)
          (Phase3GoodClockRegime.Phase3GoodClock.CoreClockInputs.ofGoodClockUpTo
            (L := L) (K := K) hh U) <
        Phase3Core.ClockCut.finish (L := L) (K := K)
          (Phase3GoodClockRegime.Phase3GoodClock.CoreClockInputs.ofGoodClockUpTo
            (L := L) (K := K) hh U)

theorem leafStrictCutInside_of_goodClockUpTo_timing
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (U : Phase3GoodClockRegime.GoodClockUpTo
      (L := L) (K := K) D.M θ tr D.lastCoreHour)
    (R : StrictCutTiming613_616 (L := L) (K := K) D θ tr) :
    LeafStrictCutInside (L := L) (K := K) D θ tr where
  afterMass_lt_finish := by
    intro G h hh
    have hcut := R.afterMass_lt_finish U h hh
    have hstart :=
      goodClock_start_eq_goodClockUpTo_start
        (L := L) (K := K) (D := D) (θ := θ) (tr := tr) G U hh
    have hfinish :=
      goodClock_finish_eq_goodClockUpTo_finish
        (L := L) (K := K) (D := D) (θ := θ) (tr := tr) G U hh
    simpa [coreInput, Phase3Core.ClockCut.afterMass,
      Phase3Core.ClockCut.finish,
      Phase3GoodClockRegime.Phase3GoodClock.CoreClockInputs.ofGoodClockUpTo,
      hstart, hfinish] using hcut

/-- Pointwise deterministic form: a good clock plus the single strict
Doty-timing residual rules out the strict-cut failure event. -/
theorem not_strictCutInsideFailure_of_timing
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (R : StrictCutTiming613_616 (L := L) (K := K) D θ tr) :
    ¬ StrictCutInsideFailure (L := L) (K := K) D θ tr := by
  intro hfail
  exact hfail.2
    (leafStrictCutInside_of_goodClockUpTo_timing
      (L := L) (K := K) hfail.1 R)

/-- The timing residual is deterministic: if it holds on every trace, the
good-clock/strict-cut bad event is empty. -/
theorem strictCutInsideFailure_tail_zero_of_timing
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (R :
      ∀ tr : Phase3GoodClock.Trace L K,
        StrictCutTiming613_616 (L := L) (K := K) D θ tr) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | StrictCutInsideFailure (L := L) (K := K) D θ tr} ≤ 0 := by
  have hempty :
      {tr : Phase3GoodClock.Trace L K |
        StrictCutInsideFailure (L := L) (K := K) D θ tr} = ∅ := by
    ext tr
    constructor
    · intro htr
      exact False.elim
        (not_strictCutInsideFailure_of_timing
          (L := L) (K := K) (D := D) (θ := θ) (tr := tr) (R tr) htr)
    · intro htr
      exact False.elim htr
  rw [hempty]
  simp

/-- Direct form matching the original residual statement:
`μ {GoodClockUpTo ∧ ¬ LeafStrictCutInside} ≤ 0`, modulo the single named
Doty Sections 6.13--6.16 strict timing residual. -/
theorem goodClock_not_leafStrictCutInside_tail_zero_of_timing
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (R :
      ∀ tr : Phase3GoodClock.Trace L K,
        StrictCutTiming613_616 (L := L) (K := K) D θ tr) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ LeafStrictCutInside (L := L) (K := K) D θ tr} ≤ 0 := by
  have hempty :
      {tr : Phase3GoodClock.Trace L K |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ LeafStrictCutInside (L := L) (K := K) D θ tr} = ∅ := by
    ext tr
    constructor
    · intro htr
      exact False.elim
        (htr.2
          (leafStrictCutInside_of_goodClockUpTo_timing
            (L := L) (K := K) htr.1 (R tr)))
    · intro htr
      exact False.elim htr
  rw [hempty]
  simp

/-- Combine the static-invariant discharge with the strict timing residual:
the whole deterministic-cut branch has zero mass. -/
theorem staticInv_strictCut_failure_tail_zero_of_timing
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (hstatic :
      ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
        ∀ t, StaticInv (L := L) (K := K) D C (tr t))
    (R :
      ∀ tr : Phase3GoodClock.Trace L K,
        StrictCutTiming613_616 (L := L) (K := K) D θ tr) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        deterministicCutFailure (L := L) (K := K) D C θ tr} ≤ 0 := by
  exact Slot3StaticInvDischarge.staticInv_strictCut_failure_tail_of_all_times
    (L := L) (K := K) (D := D) (C := C)
    (θ := θ) (entry := entry) (εcut := 0)
    hstatic
    (strictCutInsideFailure_tail_zero_of_timing
      (L := L) (K := K) (D := D) (θ := θ) (entry := entry) R)

#print axioms start_h_eq_of_exists
#print axioms end_h_eq_of_exists
#print axioms goodClock_start_eq_goodClockUpTo_start
#print axioms goodClock_finish_eq_goodClockUpTo_finish
#print axioms leafStrictCutInside_of_goodClockUpTo_timing
#print axioms not_strictCutInsideFailure_of_timing
#print axioms strictCutInsideFailure_tail_zero_of_timing
#print axioms goodClock_not_leafStrictCutInside_tail_zero_of_timing
#print axioms staticInv_strictCut_failure_tail_zero_of_timing

end Slot3StrictCutTimingDischarge
end Phase3Assembly
end ExactMajority
