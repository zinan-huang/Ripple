import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ProtocolTraceLaw
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CoreSurfaceSixLeaf
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3PostChain
import Mathlib.Tactic

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

def Slot3LeafGood
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop :=
  ∃ _ : CoreSurfaceSixLeaf (L := L) (K := K) D θ tr, True

theorem badCoreThread_subset_clock_or_leaf
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams} :
    {tr : Phase3GoodClock.Trace L K |
      ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} ⊆
      {tr |
        ¬ Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour} ∪
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Slot3LeafGood (L := L) (K := K) D θ tr} := by
  intro tr hbad
  by_cases hclock :
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour
  · right
    refine ⟨hclock, ?_⟩
    intro hleaf
    rcases hleaf with ⟨S, _⟩
    exact hbad
      (CoreSurfaceSixLeaf.goodCoreThreadTrace_of
        (L := L) (K := K) S hclock)
  · left
    exact hclock

theorem goodCoreThreadTrace_whp_of_clock_and_leaf
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {εq εh εclock εleaf εcore : ℝ≥0∞}
    (hquant :
      Phase3GoodClockRegime.ClockFrontQuantileTail
        (L := L) (K := K) μ θ D.lastCoreHour εq)
    (hhdom :
      μ {tr | Phase3GoodClockRegime.HDomFailureUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εh)
    (hclockBudget : εq + εh ≤ εclock)
    (hleaf :
      μ {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Slot3LeafGood (L := L) (K := K) D θ tr} ≤ εleaf)
    (hcoreBudget : εclock + εleaf ≤ εcore) :
    μ {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} ≤ εcore := by
  have hclock :
      μ {tr |
        ¬ Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εclock :=
    Phase3GoodClockRegime.goodClock_regime_whp
      (L := L) (K := K)
      (Phase3GoodClockRegime.clock_front_quantile_regime_whp
        (L := L) (K := K) hquant)
      hhdom hclockBudget
  calc
    μ {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr}
        ≤ μ ({tr |
            ¬ Phase3GoodClockRegime.GoodClockUpTo
              (L := L) (K := K) D.M θ tr D.lastCoreHour} ∪
          {tr |
            Phase3GoodClockRegime.GoodClockUpTo
              (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
            ¬ Slot3LeafGood (L := L) (K := K) D θ tr}) :=
      measure_mono (badCoreThread_subset_clock_or_leaf (L := L) (K := K))
    _ ≤ μ {tr |
            ¬ Phase3GoodClockRegime.GoodClockUpTo
              (L := L) (K := K) D.M θ tr D.lastCoreHour} +
          μ {tr |
            Phase3GoodClockRegime.GoodClockUpTo
              (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
            ¬ Slot3LeafGood (L := L) (K := K) D θ tr} :=
      measure_union_le _ _
    _ ≤ εclock + εleaf :=
      add_le_add hclock hleaf
    _ ≤ εcore := hcoreBudget

theorem post_trace_tail_of_snapshot_entry
    {entry : Config (AgentState L K)} {T : ℕ}
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {εpost : ℝ≥0∞}
    (Law : TraceLawAt (L := L) (K := K) entry T μ)
    (post_tail :
      Phase3Post3.Snapshot617EntryTail
        (L := L) (K := K) n ell M g₀ σ entry)
    (hT : T = post_tail.horizon.T_end_l2)
    (hpostBudget : (post_tail.ε : ℝ≥0∞) ≤ εpost) :
    μ {tr |
        GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
        ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)}
      ≤ εpost := by
  have hsub :
      {tr : Phase3GoodClock.Trace L K |
        GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
        ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)}
        ⊆
      {tr |
        ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)} := by
    intro tr h
    exact h.2
  have hkernel :
      ((NonuniformMajority L K).transitionKernel ^ T) entry
          {c | ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c}
        ≤ (post_tail.ε : ℝ≥0∞) := by
    subst T
    calc
      ((NonuniformMajority L K).transitionKernel ^ post_tail.horizon.T_end_l2) entry
          {c | ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c}
          ≤
        ((NonuniformMajority L K).transitionKernel ^ post_tail.horizon.T_end_l2) entry
          {c | ¬ Phase3Post3.Snapshot617 (L := L) (K := K) n ell M g₀ σ c} :=
        measure_mono (Phase3Post3.not_post3_subset_not_snapshot (L := L) (K := K))
      _ ≤ (post_tail.ε : ℝ≥0∞) :=
        post_tail.tail
  calc
    μ {tr |
        GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
        ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)}
        ≤
      μ {tr |
        ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)} :=
      measure_mono hsub
    _ =
      ((NonuniformMajority L K).transitionKernel ^ T) entry
        {c | ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c} := by
      rw [← TraceLawAt.kernel_bad_eq_trace_bad
        (L := L) (K := K) Law
        (Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀)
        (DiscreteMeasurableSpace.forall_measurableSet _)]
    _ ≤ (post_tail.ε : ℝ≥0∞) := hkernel
    _ ≤ εpost := hpostBudget

structure Slot3ClosureInputs
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (entry : Config (AgentState L K)) (T : ℕ)
    (ε : ℝ≥0) where
  εq : ℝ≥0∞
  εh : ℝ≥0∞
  εclock : ℝ≥0∞
  εleaf : ℝ≥0∞
  εcore : ℝ≥0∞
  εpost : ℝ≥0∞
  clock_quantile_tail :
    Phase3GoodClockRegime.ClockFrontQuantileTail
      (L := L) (K := K)
      (ProtocolTraceLaw.μ (L := L) (K := K) entry) θ D.lastCoreHour εq
  hdom_tail :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | Phase3GoodClockRegime.HDomFailureUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εh
  clock_budget : εq + εh ≤ εclock
  leaf_tail :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Slot3LeafGood (L := L) (K := K) D θ tr} ≤ εleaf
  core_budget : εclock + εleaf ≤ εcore
  post_tail :
    Phase3Post3.Snapshot617EntryTail
      (L := L) (K := K) n ell M g₀ σ entry
  post_horizon : T = post_tail.horizon.T_end_l2
  post_budget : (post_tail.ε : ℝ≥0∞) ≤ εpost
  total_budget : εcore + εpost ≤ (ε : ℝ≥0∞)

namespace Slot3ClosureInputs

theorem core_tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (I : Slot3ClosureInputs
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr}
      ≤ I.εcore :=
  goodCoreThreadTrace_whp_of_clock_and_leaf
    (L := L) (K := K)
    I.clock_quantile_tail I.hdom_tail I.clock_budget
    I.leaf_tail I.core_budget

theorem post_tail_trace
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (I : Slot3ClosureInputs
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
        ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)}
      ≤ I.εpost :=
  post_trace_tail_of_snapshot_entry
    (L := L) (K := K)
    (ProtocolTraceLaw.traceLawAt (L := L) (K := K) entry T)
    I.post_tail I.post_horizon I.post_budget

theorem bad_trace
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (I : Slot3ClosureInputs
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | ¬ Slot3TraceGood
        (L := L) (K := K) D θ n ell M g₀ σ T tr} ≤
      (ε : ℝ≥0∞) :=
  slot3TraceGood_whp_of_core_and_post
    (L := L) (K := K) I.core_tail I.post_tail_trace I.total_budget

noncomputable def toSlot3TraceResidual
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (I : Slot3ClosureInputs
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε) :
    Slot3TraceResidual
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε where
  μ := ProtocolTraceLaw.μ (L := L) (K := K) entry
  law := ProtocolTraceLaw.traceLawAt (L := L) (K := K) entry T
  bad_trace := I.bad_trace

noncomputable def toSlot3OfEntryResiduals
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (I : Slot3ClosureInputs
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε)
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    Slot3OfEntryResiduals (L := L) (K := K) D θ n ell M g₀ σ where
  entry := entry
  T := T
  ε := ε
  entry_slot3 := hentry
  chain := I.toSlot3TraceResidual

noncomputable def slot3_of_entry
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (I : Slot3ClosureInputs
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε)
    (hentry : Phase3Post3.Slot3Entry (L := L) (K := K) n g₀ entry) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase3Assembly.slot3_of_entry
    (L := L) (K := K) (I.toSlot3OfEntryResiduals hentry)

end Slot3ClosureInputs

#print axioms badCoreThread_subset_clock_or_leaf
#print axioms goodCoreThreadTrace_whp_of_clock_and_leaf
#print axioms post_trace_tail_of_snapshot_entry
#print axioms Slot3ClosureInputs.bad_trace
#print axioms Slot3ClosureInputs.toSlot3TraceResidual
#print axioms Slot3ClosureInputs.toSlot3OfEntryResiduals
#print axioms Slot3ClosureInputs.slot3_of_entry

end Phase3Assembly

end ExactMajority

