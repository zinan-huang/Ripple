import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3ClosureBuild

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

structure Slot3ClockRegimeTails
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (entry : Config (AgentState L K)) where
  εq : ℝ≥0∞
  εh : ℝ≥0∞
  εclock : ℝ≥0∞
  clock_quantile_tail :
    Phase3GoodClockRegime.ClockFrontQuantileTail
      (L := L) (K := K)
      (ProtocolTraceLaw.μ (L := L) (K := K) entry) θ D.lastCoreHour εq
  hdom_tail :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | Phase3GoodClockRegime.HDomFailureUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εh
  budget : εq + εh ≤ εclock

namespace Slot3ClockRegimeTails

theorem quantile
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (C : Slot3ClockRegimeTails (L := L) (K := K) D θ entry) :
    Phase3GoodClockRegime.ClockFrontQuantileTail
      (L := L) (K := K)
      (ProtocolTraceLaw.μ (L := L) (K := K) entry) θ D.lastCoreHour C.εq :=
  C.clock_quantile_tail

theorem hdom
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (C : Slot3ClockRegimeTails (L := L) (K := K) D θ entry) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | Phase3GoodClockRegime.HDomFailureUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ C.εh :=
  C.hdom_tail

theorem goodClock_tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (C : Slot3ClockRegimeTails (L := L) (K := K) D θ entry) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        ¬ Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ C.εclock :=
  Phase3GoodClockRegime.goodClock_regime_whp
    (L := L) (K := K)
    (Phase3GoodClockRegime.clock_front_quantile_regime_whp
      (L := L) (K := K) C.clock_quantile_tail)
    C.hdom_tail C.budget

end Slot3ClockRegimeTails

end Phase3Assembly

namespace Phase3Post3

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

namespace Snapshot617HourChain

noncomputable def toEntryHourChain
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Snapshot617HourChain (L := L) (K := K) n ell M g₀ σ)
    (entry : Config (AgentState L K))
    (hentry : Slot3Entry (L := L) (K := K) n g₀ entry) :
    Snapshot617EntryHourChain (L := L) (K := K) n ell M g₀ σ entry where
  horizon := A.horizon
  gate := A.gate
  H := A.H
  hourLen := A.hourLen
  Good := A.Good
  ηhour := A.ηhour
  good0 := A.good0 entry hentry
  none_bad := A.none_bad
  tail := A.tail
  readout := A.readout
  horizon_eq := A.horizon_eq
  ε := A.ε
  budget := A.budget

end Snapshot617HourChain
end Phase3Post3

namespace Phase3Assembly

noncomputable def snapshot617EntryHourChain_of_dischargedCore
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (P : DischargedCoreEngineProducers (L := L) (K := K) D T)
    (A :
      Phase3Post3.CoreRowsSnapshot617Adapter
        (L := L) (K := K) D T n ell M g₀ σ)
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    Phase3Post3.Snapshot617EntryHourChain
      (L := L) (K := K) n ell M g₀ σ entry :=
  (snapshot617HourChain_of_dischargedCore (L := L) (K := K) P A).toEntryHourChain
    entry hentry

noncomputable def snapshot617EntryTail_of_dischargedCore
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (P : DischargedCoreEngineProducers (L := L) (K := K) D T)
    (A :
      Phase3Post3.CoreRowsSnapshot617Adapter
        (L := L) (K := K) D T n ell M g₀ σ)
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    Phase3Post3.Snapshot617EntryTail
      (L := L) (K := K) n ell M g₀ σ entry :=
  (snapshot617EntryHourChain_of_dischargedCore
    (L := L) (K := K) P A hentry).toSnapshot617EntryTail

structure Slot3PostTailShapeInputs
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (entry : Config (AgentState L K)) where
  entry_slot3 : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry
  producers : DischargedCoreEngineProducers (L := L) (K := K) D T
  adapter :
    Phase3Post3.CoreRowsSnapshot617Adapter
      (L := L) (K := K) D T n ell M g₀ σ

namespace Slot3PostTailShapeInputs

noncomputable def entryTail
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (P : Slot3PostTailShapeInputs
      (L := L) (K := K) D T n ell M g₀ σ entry) :
    Phase3Post3.Snapshot617EntryTail
      (L := L) (K := K) n ell M g₀ σ entry :=
  snapshot617EntryTail_of_dischargedCore
    (L := L) (K := K) P.producers P.adapter P.entry_slot3

end Slot3PostTailShapeInputs

structure Slot3ReadyClosureInputs
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (entry : Config (AgentState L K))
    (ε : ℝ≥0) where
  clock : Slot3ClockRegimeTails (L := L) (K := K) D θ entry
  εleaf : ℝ≥0∞
  εcore : ℝ≥0∞
  εpost : ℝ≥0∞
  leaf_tail :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Slot3LeafGood (L := L) (K := K) D θ tr} ≤ εleaf
  core_budget : clock.εclock + εleaf ≤ εcore
  post :
    Slot3PostTailShapeInputs
      (L := L) (K := K) D Tcore n ell M g₀ σ entry
  post_budget : ((post.entryTail).ε : ℝ≥0∞) ≤ εpost
  total_budget : εcore + εpost ≤ (ε : ℝ≥0∞)

namespace Slot3ReadyClosureInputs

noncomputable def postTail
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {ε : ℝ≥0}
    (I : Slot3ReadyClosureInputs
      (L := L) (K := K) D Tcore n ell M g₀ σ entry ε) :
    Phase3Post3.Snapshot617EntryTail
      (L := L) (K := K) n ell M g₀ σ entry :=
  I.post.entryTail

noncomputable def toSlot3ClosureInputs
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {ε : ℝ≥0}
    (I : Slot3ReadyClosureInputs
      (L := L) (K := K) D Tcore n ell M g₀ σ entry ε) :
    Slot3ClosureInputs
      (L := L) (K := K) D θ n ell M g₀ σ entry
      I.postTail.horizon.T_end_l2 ε where
  εq := I.clock.εq
  εh := I.clock.εh
  εclock := I.clock.εclock
  εleaf := I.εleaf
  εcore := I.εcore
  εpost := I.εpost
  clock_quantile_tail := I.clock.quantile
  hdom_tail := I.clock.hdom
  clock_budget := I.clock.budget
  leaf_tail := I.leaf_tail
  core_budget := I.core_budget
  post_tail := I.postTail
  post_horizon := rfl
  post_budget := I.post_budget
  total_budget := I.total_budget

noncomputable def slot3_of_entry
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {Tcore : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {ε : ℝ≥0}
    (I : Slot3ReadyClosureInputs
      (L := L) (K := K) D Tcore n ell M g₀ σ entry ε) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  I.toSlot3ClosureInputs.slot3_of_entry I.post.entry_slot3

end Slot3ReadyClosureInputs

#print axioms Slot3ClockRegimeTails.goodClock_tail
#print axioms Phase3Post3.Snapshot617HourChain.toEntryHourChain
#print axioms snapshot617EntryHourChain_of_dischargedCore
#print axioms snapshot617EntryTail_of_dischargedCore
#print axioms Slot3PostTailShapeInputs.entryTail
#print axioms Slot3ReadyClosureInputs.toSlot3ClosureInputs
#print axioms Slot3ReadyClosureInputs.slot3_of_entry

end Phase3Assembly

end ExactMajority
