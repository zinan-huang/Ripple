import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3WindowNegPhiTail
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3LeafFinishHorizon

/-!
# Corrected slot-3 `leaf_tail` — `StaticInvStepClosed` eliminated

The repo's `Slot3AtomicResiduals.leaf_tail` charges the leaf-static event to ZERO by assuming the
FALSE `StaticInvStepClosed` (a clock at the cap advances past phase 3, so the static invariant is
not step-closed unconditionally).  This file replaces that with the genuine discharge: the
leaf-static failure is charged to the **FrontSync-prefix tail** `Σ_{τ<T} εsync(τ)` (the proven §6
front-width whp) plus the **cut-overshoot tail** (the first-passage residual), both REAL inputs.

`leaf_tail_of_frontSyncPrefix` takes exactly two named, satisfiable residuals — `hsync` (the entry-level
FrontSync prefix mass) and `hovershoot` (the mass where the GoodClock cuts exceed the horizon `T`)
— and produces the leaf tail with NO `StaticInvStepClosed`.  Assembles the four committed pieces:
`supportPathUpTo_ae` (IT-law), `leafStaticInvGood_of_prefix` (stopped-prefix induction),
`leafCutsBoundedBy_of_horizon` (cut bound), `leaf_tail_of_det_tail` (det-tail engine).
-/

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory Phase3Assembly Phase3Assembly.LeafTail
  Phase3StaticInvCountClosed Phase3LeafStaticGoodClock
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

/-- **Event-restricted static branch.**  On the event additionally carrying the per-trace cut bound
`LeafCutsBoundedBy T`, the leaf-static failure is forced into a `FrontSync`-prefix failure
(`GoodClockUpTo` is not needed — the cut bound is supplied directly by the event). -/
theorem leafStaticBad_cutsOK_le_frontSyncPrefixBad
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {T : ℕ}
    (hentry : StaticInv (L := L) (K := K) D C entry) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr ∧
          LeafCutsBoundedBy (L := L) (K := K) T D θ tr}
      ≤ ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | FrontSyncPrefixBad (L := L) (K := K) T tr} := by
  refine measure_mono_ae ?_
  filter_upwards [ProtocolTraceLaw.supportPathUpTo_ae (L := L) (K := K) entry T,
    starts_at_ae (L := L) (K := K) entry] with tr hsupp hstart0 htr
  obtain ⟨hbadLeaf, hcuts⟩ := htr
  by_contra hnotBad
  exact hbadLeaf
    (leafStaticInvGood_of_prefix (L := L) (K := K) hentry hstart0 hsupp
      (frontSyncPrefix_of_not_bad (L := L) (K := K) hnotBad) hcuts)

/-- **The corrected leaf tail.**  No `StaticInvStepClosed`.  The leaf-static event is charged to the
FrontSync-prefix tail (`hsync`) plus the cut-overshoot tail (`hovershoot`); the strict-cut branch is
charged zero by the proven timing dissolution. -/
theorem leaf_tail_of_frontSyncPrefix
    {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {θ : Phase3GoodClock.ClockTimingParams}
    {entry : Config (AgentState L K)} {T : ℕ}
    {εsync εovershoot εleaf : ℝ≥0∞}
    (hn : LeafNumericFacts (L := L) (K := K) D θ C)
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (hstrict_timing : ∀ tr : Phase3GoodClock.Trace L K,
      Ripple.PopulationProtocol.ExactMajority.Phase3Assembly.StrictCutTiming.StrictCutTiming613_616 (L := L) (K := K) D θ tr)
    (hsync : ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | FrontSyncPrefixBad (L := L) (K := K) T tr} ≤ εsync)
    (hovershoot : ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | ¬ LeafCutsBoundedBy (L := L) (K := K) T D θ tr} ≤ εovershoot)
    (hbudget : εsync + εovershoot ≤ εleaf) :
    ProtocolTraceLaw.μ (L := L) (K := K) entry
      {tr | Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ Phase3LeafGood (L := L) (K := K) D θ tr} ≤ εleaf := by
  classical
  -- strict-cut branch charged zero (proven timing dissolution, no `hstatic`)
  have hstrict0 :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | Ripple.PopulationProtocol.ExactMajority.Phase3Assembly.StaticInvTail.StrictCutInsideFailure (L := L) (K := K) D θ tr} ≤ 0 :=
    Ripple.PopulationProtocol.ExactMajority.Phase3Assembly.StrictCutTiming.strictCutInsideFailure_tail_zero_of_timing
      (L := L) (K := K) (D := D) (θ := θ) (entry := entry) hstrict_timing
  -- static branch: ¬LeafStaticInvGood ≤ FrontSync-prefix tail + cut-overshoot tail
  have hstaticBad :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr} ≤ εsync + εovershoot := by
    have hsplit :
        {tr : Phase3GoodClock.Trace L K | ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr} ⊆
          {tr | ¬ LeafStaticInvGood (L := L) (K := K) D C θ tr ∧
              LeafCutsBoundedBy (L := L) (K := K) T D θ tr} ∪
            {tr | ¬ LeafCutsBoundedBy (L := L) (K := K) T D θ tr} := by
      intro tr hbad
      by_cases hc : LeafCutsBoundedBy (L := L) (K := K) T D θ tr
      · exact Or.inl ⟨hbad, hc⟩
      · exact Or.inr hc
    refine le_trans (measure_mono hsplit) ?_
    refine le_trans (measure_union_le _ _) ?_
    exact add_le_add
      (le_trans (leafStaticBad_cutsOK_le_frontSyncPrefixBad (L := L) (K := K) hentry) hsync)
      hovershoot
  -- det-cut failure ≤ static branch + strict branch (existing subset, drops GoodClockUpTo)
  have hdet :
      ProtocolTraceLaw.μ (L := L) (K := K) entry
        {tr | Phase3GoodClockRegime.GoodClockUpTo (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          deterministicCutFailure (L := L) (K := K) D C θ tr} ≤ εsync + εovershoot := by
    refine le_trans (measure_mono
      (Ripple.PopulationProtocol.ExactMajority.Phase3Assembly.StaticInvTail.deterministicCutFailure_subset_static_or_strict
        (L := L) (K := K) (D := D) (C := C) (θ := θ))) ?_
    refine le_trans (measure_union_le _ _) ?_
    refine le_trans (add_le_add hstaticBad hstrict0) ?_
    rw [add_zero]
  -- feed the det-tail engine
  exact Ripple.PopulationProtocol.ExactMajority.Phase3Assembly.WindowNegPhiTail.leaf_tail_of_det_tail
    (L := L) (K := K) (D := D) (C := C) (θ := θ) (entry := entry) hn hdet hbudget

end Ripple.PopulationProtocol.ExactMajority
