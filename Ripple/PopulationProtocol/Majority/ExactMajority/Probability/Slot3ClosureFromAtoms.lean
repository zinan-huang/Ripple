import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3FrontFirstPassageTail
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3GoodClockWhp
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3WindowNegPhiTail
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3StrictCutTimingDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3ResidualsDischarge

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

open Slot3LeafTailDischarge

structure HDomTail610
    (entry : Config (AgentState L K))
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (εh : ℝ≥0∞) : Prop where
  tail :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | Phase3GoodClockRegime.HDomFailureUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εh

namespace HDomTail610

theorem of_stoppedTraceTail
    {entry : Config (AgentState L K)}
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {εh : ℝ≥0∞}
    (h :
      Phase3GoodClockRegime.HDomStoppedTraceTail610
        (L := L) (K := K) entry D.M θ D.lastCoreHour εh) :
    HDomTail610 (L := L) (K := K) entry D θ εh where
  tail := h

end HDomTail610

structure Slot3AtomicResiduals
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (entry : Config (AgentState L K)) where
  front_width_first_passage :
    Phase3GoodClockRegime.FrontWidthFirstPassageTailResidual6369
      (L := L) (K := K) entry θ D.lastCoreHour
  εh : ℝ≥0∞
  hdom : HDomTail610 (L := L) (K := K) entry D θ εh
  leakageC : ℝ
  numeric : LeafNumericFacts (L := L) (K := K) D θ leakageC
  strict_timing :
    ∀ tr : Phase3GoodClock.Trace L K,
      Slot3StrictCutTimingDischarge.StrictCutTiming613_616
        (L := L) (K := K) D θ tr

namespace Slot3AtomicResiduals

noncomputable def εq
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Slot3AtomicResiduals
      (L := L) (K := K) D θ entry) :
    ℝ≥0∞ :=
  ∑ i : Fin (D.lastCoreHour + 1),
    A.front_width_first_passage.εFront i

noncomputable def εclock
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Slot3AtomicResiduals
      (L := L) (K := K) D θ entry) :
    ℝ≥0∞ :=
  A.εq + A.εh

noncomputable def εleaf
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (_A : Slot3AtomicResiduals
      (L := L) (K := K) D θ entry) :
    ℝ≥0∞ :=
  0

noncomputable def εcore
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Slot3AtomicResiduals
      (L := L) (K := K) D θ entry) :
    ℝ≥0∞ :=
  A.εclock + A.εleaf

theorem clock_quantile_tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Slot3AtomicResiduals
      (L := L) (K := K) D θ entry) :
    Phase3GoodClockRegime.ClockFrontQuantileTail
      (L := L) (K := K)
      (ProtocolTraceLaw.μ (L := L) (K := K) entry) θ D.lastCoreHour
      A.εq := by
  have hHour :
      Phase3GoodClockRegime.ClockFrontHourTails63_69
        (L := L) (K := K) entry θ D.lastCoreHour
        A.front_width_first_passage.εFront :=
    Phase3GoodClockRegime.clockFrontHourTails63_69_of_frontWidthFirstPassageTail
      (L := L) (K := K) A.front_width_first_passage (fun _ => le_rfl)
  simpa [εq] using
    Phase3GoodClockRegime.clockFrontQuantileTail_of_hourTails
      (L := L) (K := K) hHour le_rfl

theorem hdom_tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Slot3AtomicResiduals
      (L := L) (K := K) D θ entry) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | Phase3GoodClockRegime.HDomFailureUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ A.εh :=
  A.hdom.tail

theorem leaf_tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Slot3AtomicResiduals
      (L := L) (K := K) D θ entry)
    (hstatic_entry : StaticInv (L := L) (K := K) D A.leakageC entry)
    (hstatic_stepClosed :
      Slot3StaticInvDischarge.StaticInvStepClosed
        (L := L) (K := K) D A.leakageC) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Slot3LeafGood (L := L) (K := K) D θ tr} ≤ A.εleaf := by
  have hstatic :
      ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
        ∀ t, StaticInv (L := L) (K := K) D A.leakageC (tr t) :=
    Slot3StaticInvDischarge.staticInv_ae_all_times
      (L := L) (K := K) (D := D) (C := A.leakageC)
      (entry := entry) hstatic_entry hstatic_stepClosed
  have hdet :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          deterministicCutFailure
            (L := L) (K := K) D A.leakageC θ tr} ≤ 0 :=
    Slot3StrictCutTimingDischarge.staticInv_strictCut_failure_tail_zero_of_timing
      (L := L) (K := K) (D := D) (C := A.leakageC)
      (θ := θ) (entry := entry) hstatic A.strict_timing
  simpa [εleaf] using
    Slot3WindowNegPhiTail.leaf_tail_of_det_tail
      (L := L) (K := K) (D := D) (C := A.leakageC)
      (θ := θ) (entry := entry) A.numeric hdet le_rfl

end Slot3AtomicResiduals

noncomputable def slot3ClosureInputs_of_atoms
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (atoms : Slot3AtomicResiduals
      (L := L) (K := K) D θ entry)
    (hstatic_entry : StaticInv (L := L) (K := K) D atoms.leakageC entry)
    (hstatic_stepClosed :
      Slot3StaticInvDischarge.StaticInvStepClosed
        (L := L) (K := K) D atoms.leakageC)
    (post :
      Slot3PostTailShapeInputs
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    Slot3ClosureInputs
      (L := L) (K := K) D θ n ell M g₀ σ entry
      post.entryTail.horizon.T_end_l2 ε where
  εq := atoms.εq
  εh := atoms.εh
  εclock := atoms.εclock
  εleaf := atoms.εleaf
  εcore := atoms.εcore
  εpost := ((post.entryTail).ε : ℝ≥0∞)
  clock_quantile_tail := atoms.clock_quantile_tail
  hdom_tail := atoms.hdom_tail
  clock_budget := le_rfl
  leaf_tail := atoms.leaf_tail hstatic_entry hstatic_stepClosed
  core_budget := le_rfl
  post_tail := post.entryTail
  post_horizon := rfl
  post_budget := le_rfl
  total_budget := htotal

#print axioms HDomTail610.of_stoppedTraceTail
#print axioms Slot3AtomicResiduals.clock_quantile_tail
#print axioms Slot3AtomicResiduals.hdom_tail
#print axioms Slot3AtomicResiduals.leaf_tail
#print axioms slot3ClosureInputs_of_atoms

end Phase3Assembly

end ExactMajority
