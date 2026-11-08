import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3FrontFirstPassageTail
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3GoodClockWhp
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3WindowNegPhiTail
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3StrictCutTiming
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3ClockRegimeTails
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3LeafTailFrontSync

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

open LeafTail

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

structure Phase3ClosureTails
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (entry : Config (AgentState L K)) where
  front_width_first_passage :
    Phase3GoodClockRegime.FrontWidthFirstPassageTail6369
      (L := L) (K := K) entry θ D.lastCoreHour
  εh : ℝ≥0∞
  hdom : HDomTail610 (L := L) (K := K) entry D θ εh
  leakageC : ℝ
  numeric : LeafNumericFacts (L := L) (K := K) D θ leakageC
  strict_timing :
    ∀ tr : Phase3GoodClock.Trace L K,
      StrictCutTiming.StrictCutTiming613_616
        (L := L) (K := K) D θ tr
  /-- Finite horizon on which the FrontSync guard is required. -/
  leafHorizon : ℕ
  εsync : ℝ≥0∞
  εovershoot : ℝ≥0∞
  sync_tail :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | Phase3LeafStaticGoodClock.FrontSyncPrefixBad
        (L := L) (K := K) leafHorizon tr} ≤ εsync
  cut_overshoot_tail :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | ¬ Phase3LeafStaticGoodClock.LeafCutsBoundedBy
        (L := L) (K := K) leafHorizon D θ tr} ≤ εovershoot

namespace Phase3ClosureTails

noncomputable def εq
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Phase3ClosureTails
      (L := L) (K := K) D θ entry) :
    ℝ≥0∞ :=
  ∑ i : Fin (D.lastCoreHour + 1),
    A.front_width_first_passage.εFront i

noncomputable def εclock
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Phase3ClosureTails
      (L := L) (K := K) D θ entry) :
    ℝ≥0∞ :=
  A.εq + A.εh

noncomputable def εleaf
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Phase3ClosureTails
      (L := L) (K := K) D θ entry) :
    ℝ≥0∞ :=
  A.εsync + A.εovershoot

noncomputable def εcore
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Phase3ClosureTails
      (L := L) (K := K) D θ entry) :
    ℝ≥0∞ :=
  A.εclock + A.εleaf

theorem clock_quantile_tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Phase3ClosureTails
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
    (A : Phase3ClosureTails
      (L := L) (K := K) D θ entry) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | Phase3GoodClockRegime.HDomFailureUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ A.εh :=
  A.hdom.tail

theorem leaf_tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (A : Phase3ClosureTails
      (L := L) (K := K) D θ entry)
    (hstatic_entry : StaticInv (L := L) (K := K) D A.leakageC entry) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Phase3LeafGood (L := L) (K := K) D θ tr} ≤ A.εleaf := by
  exact leaf_tail_of_frontSyncPrefix
    (L := L) (K := K) (D := D) (C := A.leakageC)
    (θ := θ) (entry := entry) (T := A.leafHorizon)
    A.numeric hstatic_entry A.strict_timing A.sync_tail A.cut_overshoot_tail le_rfl

end Phase3ClosureTails

noncomputable def phase3ClosureHypotheses_of_tails
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (atoms : Phase3ClosureTails
      (L := L) (K := K) D θ entry)
    (hstatic_entry : StaticInv (L := L) (K := K) D atoms.leakageC entry)
    (post :
      Phase3PostTailShape
        (L := L) (K := K) D Tcore n ell M g₀ σ entry)
    (ε : ℝ≥0)
    (htotal : atoms.εcore + ((post.entryTail).ε : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    Phase3ClosureHypotheses
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
  leaf_tail := atoms.leaf_tail hstatic_entry
  core_budget := le_rfl
  post_tail := post.entryTail
  post_horizon := rfl
  post_budget := le_rfl
  total_budget := htotal

#print axioms HDomTail610.of_stoppedTraceTail
#print axioms Phase3ClosureTails.clock_quantile_tail
#print axioms Phase3ClosureTails.hdom_tail
#print axioms Phase3ClosureTails.leaf_tail
#print axioms phase3ClosureHypotheses_of_tails

end Phase3Assembly

end Ripple.PopulationProtocol.ExactMajority
