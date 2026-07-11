import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3LeafTailDischarge

/-!
# Slot-3 static-invariant discharge.

This file separates the deterministic static-invariant part of the slot-3 leaf
tail from the strict cut-placement timing obligation.
-/

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly
namespace Slot3StaticInvDischarge

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

open Slot3LeafTailDischarge

/-- One-step support closure needed to propagate the slot-3 static invariant
through the protocol kernel.  This is the deterministic hypothesis consumed by
`Protocol.ae_of_stepDistOrSelf_support_preserved`.

The closure is explicit because `Slot3LeafTailDischarge.StaticInv` uses the old
`HourCoupling.HourWindow`, while the existing phase-3 hygiene lemma is for the
front-refined `Phase3HourWindow.HourWindow'`. -/
def StaticInvStepClosed
    (D : Phase3Core.Phase3ModeDomain L) (C : ℝ) : Prop :=
  ∀ c c' : Config (AgentState L K),
    StaticInv (L := L) (K := K) D C c →
    c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
    StaticInv (L := L) (K := K) D C c'

/-- Endpoint form: from a static-invariant entry and one-step support closure,
the invariant holds almost surely at every fixed Markov time. -/
theorem staticInv_kernel_ae_time
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {entry : Config (AgentState L K)}
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hclosed : StaticInvStepClosed (L := L) (K := K) D C)
    (t : ℕ) :
    ∀ᵐ c ∂(((NonuniformMajority L K).transitionKernel ^ t) entry),
      StaticInv (L := L) (K := K) D C c := by
  exact Protocol.ae_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K)
    (fun c => StaticInv (L := L) (K := K) D C c)
    hclosed entry hentry t

/-- Trace form at a fixed time, obtained by pushing `ProtocolTraceLaw.μ` through
the endpoint map and using the kernel endpoint law. -/
theorem staticInv_ae_time
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {entry : Config (AgentState L K)}
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hclosed : StaticInvStepClosed (L := L) (K := K) D C)
    (t : ℕ) :
    ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
      StaticInv (L := L) (K := K) D C (tr t) := by
  have hkernel :=
    staticInv_kernel_ae_time
      (L := L) (K := K) (D := D) (C := C)
      (entry := entry) hentry hclosed t
  have hbad_kernel :
      ((NonuniformMajority L K).transitionKernel ^ t) entry
        {c : Config (AgentState L K) |
          ¬ StaticInv (L := L) (K := K) D C c} = 0 :=
    ae_iff.mp hkernel
  have hmeas :
      MeasurableSet
        {c : Config (AgentState L K) |
          ¬ StaticInv (L := L) (K := K) D C c} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have htrace_eq :=
    TraceLawAt.kernel_bad_eq_trace_bad
      (L := L) (K := K)
      (ProtocolTraceLaw.traceLawAt (L := L) (K := K) entry t)
      (fun c => StaticInv (L := L) (K := K) D C c)
      hmeas
  rw [htrace_eq] at hbad_kernel
  exact ae_iff.mpr hbad_kernel

/-- Countable-intersection trace form: the static invariant holds at all
discrete times, almost surely under the protocol trajectory law. -/
theorem staticInv_ae_all_times
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {entry : Config (AgentState L K)}
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hclosed : StaticInvStepClosed (L := L) (K := K) D C) :
    ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
      ∀ t, StaticInv (L := L) (K := K) D C (tr t) := by
  rw [ae_all_iff]
  intro t
  exact staticInv_ae_time
    (L := L) (K := K) (D := D) (C := C)
    (entry := entry) hentry hclosed t

/-- Pointwise conversion from an all-time static invariant to the leaf static
invariant required by `Slot3LeafTailDischarge`. -/
theorem leafStaticInvGood_of_all_times
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (hstatic :
      ∀ t, StaticInv (L := L) (K := K) D C (tr t)) :
    LeafStaticInvGood (L := L) (K := K) D C θ tr where
  afterO := by
    intro G h _hh
    exact hstatic
      ((coreInput (L := L) (K := K) D θ tr G h).start + θ.twoOverC)
  afterPhi := by
    intro G h _hh
    exact hstatic
      ((coreInput (L := L) (K := K) D θ tr G h).start +
        θ.twoOverC + θ.fortyOneOverM)
  afterMass := by
    intro G h _hh
    exact hstatic
      ((coreInput (L := L) (K := K) D θ tr G h).start +
        θ.twoOverC + θ.fortySevenOverM)

theorem leafStaticInvGood_ae_of_all_times
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (hstatic :
      ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
        ∀ t, StaticInv (L := L) (K := K) D C (tr t)) :
    ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
      LeafStaticInvGood (L := L) (K := K) D C θ tr :=
  hstatic.mono fun _tr htr =>
    leafStaticInvGood_of_all_times (L := L) (K := K) (θ := θ) htr

theorem leafStaticInvGood_ae
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hclosed : StaticInvStepClosed (L := L) (K := K) D C) :
    ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
      LeafStaticInvGood (L := L) (K := K) D C θ tr :=
  leafStaticInvGood_ae_of_all_times
    (L := L) (K := K) (D := D) (C := C) (θ := θ) (entry := entry)
    (staticInv_ae_all_times
      (L := L) (K := K) (D := D) (C := C)
      (entry := entry) hentry hclosed)

theorem leafStaticInvGood_compl_eq_zero
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hclosed : StaticInvStepClosed (L := L) (K := K) D C) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr} = 0 :=
  ae_iff.mp
    (leafStaticInvGood_ae
      (L := L) (K := K) (D := D) (C := C)
      (θ := θ) (entry := entry) hentry hclosed)

/-- The remaining deterministic-cut bad event after static invariance is
discharged.  This is the timing-only obligation: it should be proved from the
strict cut placement (`2/c + 41/M + 47/M` before the hour finish) supplied by the
clock-timing interface. -/
def StrictCutInsideFailure
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop :=
  Phase3GoodClockRegime.GoodClockUpTo
    (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
    ¬ LeafStrictCutInside (L := L) (K := K) D θ tr

theorem deterministicCutFailure_subset_static_or_strict
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams} :
    {tr : Phase3GoodClock.Trace L K |
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
      deterministicCutFailure (L := L) (K := K) D C θ tr} ⊆
    {tr | ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr} ∪
    {tr | StrictCutInsideFailure (L := L) (K := K) D θ tr} := by
  intro tr htr
  rcases htr with ⟨hgood, hdet⟩
  rcases hdet with hstatic | hstrict
  · exact Or.inl hstatic
  · exact Or.inr ⟨hgood, hstrict⟩

/-- Discharge the original `staticInv_strictCut_failure_tail` event down to the
timing-only strict-cut tail, assuming static invariance holds a.e. at all times. -/
theorem staticInv_strictCut_failure_tail_of_all_times
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {εcut : ℝ≥0∞}
    (hstatic :
      ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
        ∀ t, StaticInv (L := L) (K := K) D C (tr t))
    (hcut :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | StrictCutInsideFailure (L := L) (K := K) D θ tr} ≤ εcut) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        deterministicCutFailure (L := L) (K := K) D C θ tr} ≤ εcut := by
  have hstatic_zero :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr} = 0 :=
    ae_iff.mp
      (leafStaticInvGood_ae_of_all_times
        (L := L) (K := K) (D := D) (C := C)
        (θ := θ) (entry := entry) hstatic)
  calc
    ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          deterministicCutFailure (L := L) (K := K) D C θ tr}
        ≤
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        ({tr | ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr} ∪
          {tr | StrictCutInsideFailure (L := L) (K := K) D θ tr}) :=
        measure_mono
          (deterministicCutFailure_subset_static_or_strict
            (L := L) (K := K) (D := D) (C := C) (θ := θ))
    _ ≤
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr} +
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | StrictCutInsideFailure (L := L) (K := K) D θ tr} :=
        measure_union_le _ _
    _ ≤ εcut := by
      rw [hstatic_zero, zero_add]
      exact hcut

/-- Entry/step-closure convenience form of
`staticInv_strictCut_failure_tail_of_all_times`.  The static branch is charged
zero; the only remaining cost is `StrictCutInsideFailure`. -/
theorem staticInv_strictCut_failure_tail
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {εcut : ℝ≥0∞}
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hclosed : StaticInvStepClosed (L := L) (K := K) D C)
    (hcut :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | StrictCutInsideFailure (L := L) (K := K) D θ tr} ≤ εcut) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        deterministicCutFailure (L := L) (K := K) D C θ tr} ≤ εcut :=
  staticInv_strictCut_failure_tail_of_all_times
    (L := L) (K := K) (D := D) (C := C)
    (θ := θ) (entry := entry)
    (staticInv_ae_all_times
      (L := L) (K := K) (D := D) (C := C)
      (entry := entry) hentry hclosed)
    hcut

/-- If the strict cut-placement condition itself holds a.e. on good-clock
traces, then the whole deterministic-cut failure event has zero mass. -/
theorem staticInv_strictCut_failure_tail_zero_of_strictCut_ae
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (hstatic :
      ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
        ∀ t, StaticInv (L := L) (K := K) D C (tr t))
    (hcut :
      ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour →
        LeafStrictCutInside (L := L) (K := K) D θ tr) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        deterministicCutFailure (L := L) (K := K) D C θ tr} ≤ 0 := by
  have hcut_zero :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | StrictCutInsideFailure (L := L) (K := K) D θ tr} = 0 := by
    have hnot :
        ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
          ¬ StrictCutInsideFailure (L := L) (K := K) D θ tr := by
      filter_upwards [hcut] with tr htr hfail
      exact hfail.2 (htr hfail.1)
    simpa using (ae_iff.mp hnot)
  exact staticInv_strictCut_failure_tail_of_all_times
    (L := L) (K := K) (D := D) (C := C)
    (θ := θ) (entry := entry) (εcut := 0) hstatic (by rw [hcut_zero])

/-- Entry/step-closure convenience form of the zero-mass deterministic-cut
discharge. -/
theorem staticInv_strictCut_failure_tail_zero
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)}
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hclosed : StaticInvStepClosed (L := L) (K := K) D C)
    (hcut :
      ∀ᵐ tr ∂(ProtocolTraceLaw.μ (L := L) (K := K) entry),
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour →
        LeafStrictCutInside (L := L) (K := K) D θ tr) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        deterministicCutFailure (L := L) (K := K) D C θ tr} ≤ 0 :=
  staticInv_strictCut_failure_tail_zero_of_strictCut_ae
    (L := L) (K := K) (D := D) (C := C)
    (θ := θ) (entry := entry)
    (staticInv_ae_all_times
      (L := L) (K := K) (D := D) (C := C)
      (entry := entry) hentry hclosed)
    hcut

#print axioms staticInv_kernel_ae_time
#print axioms staticInv_ae_time
#print axioms staticInv_ae_all_times
#print axioms leafStaticInvGood_of_all_times
#print axioms leafStaticInvGood_ae
#print axioms leafStaticInvGood_compl_eq_zero
#print axioms deterministicCutFailure_subset_static_or_strict
#print axioms staticInv_strictCut_failure_tail_of_all_times
#print axioms staticInv_strictCut_failure_tail
#print axioms staticInv_strictCut_failure_tail_zero_of_strictCut_ae
#print axioms staticInv_strictCut_failure_tail_zero

end Slot3StaticInvDischarge
end Phase3Assembly
end ExactMajority
