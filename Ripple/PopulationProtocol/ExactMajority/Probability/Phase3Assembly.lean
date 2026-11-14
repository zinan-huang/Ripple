import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3GoodClockRegime
import Ripple.PopulationProtocol.ExactMajority.Probability.Lemma613MarkedPullDrop
import Ripple.PopulationProtocol.ExactMajority.Probability.Lemma616MarkedCancelMass
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Post3
import Mathlib.Tactic

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-!
Slot-3 assembly layer.

This file is intentionally a wiring layer: it consumes the discharged leaf
producers and turns them into the `Phase3Core.CoreProducers` used by the strong
Core(h) induction.  The remaining endpoint probability input is the finite
killed-kernel hour chain `CoreSnapshot617TailInput.chain`; `Phase3Post3`
composes that chain on `killK_now` and transfers back to the full kernel only at
the endpoint.
-/

/-- Range-local Core input: clock regime through the actual Core domain plus
the stopped Core surface on the same trace. -/
structure RangeLocalCoreThread
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) where
  good :
    Phase3GoodClockRegime.GoodClockUpTo
      (L := L) (K := K) D.M θ tr D.lastCoreHour
  surface : Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr

/-- Legacy all-hours Core input retained for deterministic per-thread testing.
The final protocol-entry slot-3 atom uses the range-local `RangeLocalCoreThread`
above through the trace-law bridge. -/
structure AllHoursCoreThread
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) where
  good :
    Phase3GoodClockRegime.GoodClockAllRegime
      (L := L) (K := K) D.M θ tr
  surface : Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr

namespace AllHoursCoreThread

noncomputable def toCoreThread
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (I : AllHoursCoreThread (L := L) (K := K) D θ tr) :
    Phase3Core.CoreThread (L := L) (K := K) D θ tr where
  good :=
    Phase3GoodClockRegime.goodClock_of_allRegime
      (L := L) (K := K) I.good
  surface := I.surface

theorem clockInput_eq_allRegime
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (I : AllHoursCoreThread (L := L) (K := K) D θ tr)
    (h : ℕ) :
    (I.toCoreThread.clockInput h) =
      Phase3GoodClockRegime.coreClockFacts_of_allRegime
        (L := L) (K := K) I.good h := rfl

end AllHoursCoreThread

/-! ## Predicate checkpoint surface constructor -/

/-- The hour gate used by the predicate-surface constructor: Doty et al.'s stopped
Lemma-6.10 regime, intersected with any extra local gate predicate supplied by
the concrete Regime discharge. -/
def predicateHourGate
    (D : Phase3Core.Phase3ModeDomain L)
    (C : ℝ)
    (gatePred : ℕ → Set (Phase3Core.Omega L K))
    (h : ℕ) : Set (Phase3Core.Omega L K) :=
  {c |
    c ∈ Lemma610StoppedAzuma.regimeSet
      (L := L) (K := K) (D.M : ℝ) C h ∧
    c ∈ gatePred h}

/-- Pointwise invariant attached to a named checkpoint cut.

This is the predicate half of the checkpoint design: a concrete trace cut may
enter the checkpoint through a trace-cut witness, while row conclusions enter
through these invariant predicates. -/
def coreCutInvariant
    (D : Phase3Core.Phase3ModeDomain L)
    (_θ : Phase3GoodClock.ClockTimingParams)
    (C : ℝ)
    (cut : Phase3Core.Cut) (h : ℕ)
    (c : Phase3Core.Omega L K) : Prop :=
  match cut with
  | Phase3Core.Cut.hourStart =>
      HourCouplingAzuma.Phi (L := L) (K := K) (D.M : ℝ) C h c = 0 ∧
        HourCoupling.mAbove (L := L) (K := K) h c ≤
          Phase3Core.mainAboveTinyThreshold D.M
  | Phase3Core.Cut.afterO =>
      Phase3Core.OFuelFloor (L := L) (K := K) D h c
  | Phase3Core.Cut.afterPhi =>
      Phase3Core.OFuelFloor (L := L) (K := K) D h c ∧
        Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c
  | Phase3Core.Cut.afterMass =>
      Phase3Core.OFuelFloor (L := L) (K := K) D h c ∧
        Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c ∧
        Phase3Core.TotalMassBound (L := L) (K := K) D h c
  | Phase3Core.Cut.hourEnd =>
      Phase3Core.TotalMassBound (L := L) (K := K) D h c

/-- Predicate checkpoints for the Core surface.

The non-start cuts are deliberately not singleton trace points: they accept
either the concrete trace cut (`traceCut`) or the corresponding pointwise row
invariant.  This is the shape needed by the later chain adapter: trace membership
and row-floor implication are discharged by different arms of the same set. -/
def predicateCheckpoint
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (C : ℝ)
    (gatePred : ℕ → Set (Phase3Core.Omega L K))
    (traceCut : Phase3Core.Cut → ℕ → Set (Phase3Core.Omega L K))
    (cut : Phase3Core.Cut) (h : ℕ) : Set (Phase3Core.Omega L K) :=
  {c |
    c ∈ predicateHourGate (L := L) (K := K) D C gatePred h ∧
      match cut with
      | Phase3Core.Cut.hourStart =>
          coreCutInvariant (L := L) (K := K) D θ C cut h c
      | Phase3Core.Cut.afterO =>
          c ∈ traceCut cut h ∨
            coreCutInvariant (L := L) (K := K) D θ C cut h c
      | Phase3Core.Cut.afterPhi =>
          c ∈ traceCut cut h ∨
            coreCutInvariant (L := L) (K := K) D θ C cut h c
      | Phase3Core.Cut.afterMass =>
          c ∈ traceCut cut h ∨
            coreCutInvariant (L := L) (K := K) D θ C cut h c
      | Phase3Core.Cut.hourEnd =>
          coreCutInvariant (L := L) (K := K) D θ C cut h c}

/-- Non-timing facts needed to turn a `GoodClockUpTo` trace into the concrete
`CoreRunSurface` fields.  These are intentionally explicit: `GoodClockUpTo`
supplies the clock schedule, while the Regime/leakage proof supplies membership
in the stopped regime, start synchronization, and numeric readouts. -/
structure CoreSurfacePredicateFacts
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) where
  leakageC : ℝ
  leakageC_pos : 0 < leakageC
  leakageK_pos : 0 < K
  gatePred : ℕ → Set (Phase3Core.Omega L K)
  spanGate : ℕ → ℕ → Set (Phase3Core.Omega L K)
  traceCut : Phase3Core.Cut → ℕ → Set (Phase3Core.Omega L K)
  trace_afterO_mem_gate :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Ripple.PopulationProtocol.ExactMajority.Phase3GoodClock.CoreClockFacts.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC) ∈
        predicateHourGate (L := L) (K := K) D leakageC gatePred h
  trace_afterO_mem_traceCut :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Ripple.PopulationProtocol.ExactMajority.Phase3GoodClock.CoreClockFacts.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC) ∈ traceCut .afterO h
  trace_afterPhi_mem_gate :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Ripple.PopulationProtocol.ExactMajority.Phase3GoodClock.CoreClockFacts.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC + θ.fortyOneOverM) ∈
        predicateHourGate (L := L) (K := K) D leakageC gatePred h
  trace_afterPhi_mem_traceCut :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Ripple.PopulationProtocol.ExactMajority.Phase3GoodClock.CoreClockFacts.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC + θ.fortyOneOverM) ∈
        traceCut .afterPhi h
  trace_afterMass_mem_gate :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Ripple.PopulationProtocol.ExactMajority.Phase3GoodClock.CoreClockFacts.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC + θ.fortySevenOverM) ∈
        predicateHourGate (L := L) (K := K) D leakageC gatePred h
  trace_afterMass_mem_traceCut :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Ripple.PopulationProtocol.ExactMajority.Phase3GoodClock.CoreClockFacts.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC + θ.fortySevenOverM) ∈
        traceCut .afterMass h
  hourGate_clock_tiny : ∀ h, h ≤ D.lastCoreHour →
    ∀ c, c ∈ predicateHourGate (L := L) (K := K) D leakageC gatePred h →
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h c
  clockTiny_frac : ∀ h c,
    Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h c →
      (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / leakageC ≤
        (1 / 1000 : ℝ)
  eps13 : ℕ → ℝ≥0∞
  eps14 : ℕ → ℝ≥0∞
  eps15 : ℕ → ℝ≥0∞
  eps16 : ℕ → ℝ≥0∞

namespace CoreSurfacePredicateFacts

noncomputable def mkSurface
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (_G :
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour)
    (F : CoreSurfacePredicateFacts (L := L) (K := K) D θ tr) :
    Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr where
  hourGate := predicateHourGate (L := L) (K := K) D F.leakageC F.gatePred
  spanGate := F.spanGate
  checkpoint :=
    predicateCheckpoint (L := L) (K := K) D θ F.leakageC F.gatePred F.traceCut
  leakageC := F.leakageC
  leakageC_pos := F.leakageC_pos
  leakageK_pos := F.leakageK_pos
  hourGate_le_regime := by
    intro h _hh c hc
    exact hc.1
  hourStart_mem_gate := by
    intro h _hh c hc
    exact hc.1
  checkpoint_mem_gate := by
    intro cut h _hh c hc
    exact hc.1
  trace_afterO_mem_checkpoint := by
    intro G h hh
    dsimp [predicateCheckpoint]
    exact ⟨F.trace_afterO_mem_gate G h hh, Or.inl (F.trace_afterO_mem_traceCut G h hh)⟩
  trace_afterPhi_mem_checkpoint := by
    intro G h hh
    dsimp [predicateCheckpoint]
    exact ⟨F.trace_afterPhi_mem_gate G h hh,
      Or.inl (F.trace_afterPhi_mem_traceCut G h hh)⟩
  trace_afterMass_mem_checkpoint := by
    intro G h hh
    dsimp [predicateCheckpoint]
    exact ⟨F.trace_afterMass_mem_gate G h hh,
      Or.inl (F.trace_afterMass_mem_traceCut G h hh)⟩
  hourStart_phi_zero := by
    intro h _hh c hc
    exact hc.2.1
  hourGate_clock_tiny := F.hourGate_clock_tiny
  hourStart_main_tiny := by
    intro h _hh c hc
    exact hc.2.2
  clockTiny_frac := F.clockTiny_frac
  eps13 := F.eps13
  eps14 := F.eps14
  eps15 := F.eps15
  eps16 := F.eps16

theorem mem_afterO_of_gate_of_oFuel
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {G :
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour}
    (F : CoreSurfacePredicateFacts (L := L) (K := K) D θ tr)
    {h : ℕ} {c : Phase3Core.Omega L K}
    (hgate : c ∈ (mkSurface (L := L) (K := K) G F).hourGate h)
    (hO : Phase3Core.OFuelFloor (L := L) (K := K) D h c) :
    c ∈ (mkSurface (L := L) (K := K) G F).checkpoint .afterO h := by
  exact ⟨hgate, Or.inr hO⟩

theorem mem_afterPhi_of_gate_of_floors
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {G :
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour}
    (F : CoreSurfacePredicateFacts (L := L) (K := K) D θ tr)
    {h : ℕ} {c : Phase3Core.Omega L K}
    (hgate : c ∈ (mkSurface (L := L) (K := K) G F).hourGate h)
    (hO : Phase3Core.OFuelFloor (L := L) (K := K) D h c)
    (hPhi : Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c) :
    c ∈ (mkSurface (L := L) (K := K) G F).checkpoint .afterPhi h := by
  exact ⟨hgate, Or.inr ⟨hO, hPhi⟩⟩

theorem mem_afterMass_of_gate_of_floors
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {G :
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour}
    (F : CoreSurfacePredicateFacts (L := L) (K := K) D θ tr)
    {h : ℕ} {c : Phase3Core.Omega L K}
    (hgate : c ∈ (mkSurface (L := L) (K := K) G F).hourGate h)
    (hO : Phase3Core.OFuelFloor (L := L) (K := K) D h c)
    (hPhi : Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c)
    (hMass : Phase3Core.TotalMassBound (L := L) (K := K) D h c) :
    c ∈ (mkSurface (L := L) (K := K) G F).checkpoint .afterMass h := by
  exact ⟨hgate, Or.inr ⟨hO, hPhi, hMass⟩⟩

end CoreSurfacePredicateFacts

/-! ## Range-local Core trace event and trace-law lift

The probabilistic GoodClock producer is range-indexed: it supplies
`GoodClockUpTo D.lastCoreHour`, not the legacy all-hours `GoodClockAllRegime`.
The event below is therefore the honest trace-level Core witness used by the
whp bridge.  The legacy `AllHoursCoreThread`/`phase3ThreadWork` constructor
remains available as a deterministic per-thread adapter, but the probabilistic
bridge does not fabricate all-hour first-passage data outside the Core range.
-/

/-- Trace event: the sampled trace carries a range-local Core witness. -/
def GoodCoreThreadTrace
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) : Prop :=
  ∃ _ : RangeLocalCoreThread (L := L) (K := K) D θ tr, True

/-- If every good-clock trace deterministically yields the stopped Core surface,
the good-Core-thread failure set is contained in the good-clock failure set. -/
theorem goodCoreThreadTrace_whp_of_goodClock
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {ε : ℝ≥0∞}
    (hgoodClock :
      μ {tr | ¬ Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ ε)
    (mkSurface : ∀ tr,
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour →
        Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr) :
    μ {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} ≤ ε := by
  refine le_trans (measure_mono ?_) hgoodClock
  intro tr hbad hclock
  exact hbad ⟨⟨hclock, mkSurface tr hclock⟩, trivial⟩

/-- Direct bridge from the discharged GoodClock Regime tail to the range-local
Core-thread trace event. -/
theorem goodCoreThreadTrace_whp_of_regime
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {εq εh ε : ℝ≥0∞}
    (hquant :
      μ {tr | ¬ Phase3GoodClockRegime.ClockFrontQuantileRegime
        (L := L) (K := K) θ tr D.lastCoreHour} ≤ εq)
    (hhdom :
      μ {tr | Phase3GoodClockRegime.HDomFailureUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εh)
    (hbudget : εq + εh ≤ ε)
    (mkSurface : ∀ tr,
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour →
        Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr) :
    μ {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} ≤ ε :=
  goodCoreThreadTrace_whp_of_goodClock
    (L := L) (K := K)
    (Phase3GoodClockRegime.goodClock_regime_whp
      (L := L) (K := K) hquant hhdom hbudget)
    mkSurface

/-- Union-bound form when the stopped Core surface has its own trace-level
failure budget after conditioning the event as a subset, not as conditional
probability. -/
theorem goodCoreThreadTrace_whp_of_goodClock_and_surface
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {εclock εsurface ε : ℝ≥0∞}
    (hgoodClock :
      μ {tr | ¬ Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εclock)
    (hsurface :
      μ {tr |
        Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
        ¬ ∃ _S : Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr, True}
        ≤ εsurface)
    (hbudget : εclock + εsurface ≤ ε) :
    μ {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} ≤ ε := by
  classical
  have hsub :
      {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} ⊆
        {tr | ¬ Phase3GoodClockRegime.GoodClockUpTo
          (L := L) (K := K) D.M θ tr D.lastCoreHour} ∪
        {tr |
          Phase3GoodClockRegime.GoodClockUpTo
            (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
          ¬ ∃ _S : Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr, True} := by
    intro tr hbad
    by_cases hg : Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour
    · right
      refine ⟨hg, ?_⟩
      intro hS
      rcases hS with ⟨S, _⟩
      exact hbad ⟨⟨hg, S⟩, trivial⟩
    · left
      exact hg
  calc
    μ {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr}
        ≤ μ ({tr | ¬ Phase3GoodClockRegime.GoodClockUpTo
              (L := L) (K := K) D.M θ tr D.lastCoreHour} ∪
            {tr |
              Phase3GoodClockRegime.GoodClockUpTo
                (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
              ¬ ∃ _S : Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr, True}) :=
      measure_mono hsub
    _ ≤ μ {tr | ¬ Phase3GoodClockRegime.GoodClockUpTo
              (L := L) (K := K) D.M θ tr D.lastCoreHour} +
          μ {tr |
              Phase3GoodClockRegime.GoodClockUpTo
                (L := L) (K := K) D.M θ tr D.lastCoreHour ∧
              ¬ ∃ _S : Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr, True} :=
      measure_union_le _ _
    _ ≤ εclock + εsurface :=
      add_le_add hgoodClock hsurface
    _ ≤ ε := hbudget

/-- Trace law from a protocol entry: the endpoint map has the same law as the
full-kernel endpoint. -/
structure TraceLawAt
    (entry : Config (AgentState L K))
    (T : ℕ)
    (μ : Measure (Phase3GoodClock.Trace L K)) : Prop where
  endpoint_law :
    Measure.map (fun tr : Phase3GoodClock.Trace L K => tr T) μ =
      ((NonuniformMajority L K).transitionKernel ^ T) entry
  starts_at : μ {tr | tr 0 = entry} = 1

namespace TraceLawAt

/-- Endpoint pushforward: kernel endpoint bad mass is the trace-law mass of the
bad endpoint event. -/
theorem kernel_bad_eq_trace_bad
    {entry : Config (AgentState L K)} {T : ℕ}
    {μ : Measure (Phase3GoodClock.Trace L K)}
    (Law : TraceLawAt (L := L) (K := K) entry T μ)
    (Post : Config (AgentState L K) → Prop)
    (hPost_meas : MeasurableSet {c | ¬ Post c}) :
    ((NonuniformMajority L K).transitionKernel ^ T) entry {c | ¬ Post c} =
      μ {tr | ¬ Post (tr T)} := by
  rw [← Law.endpoint_law]
  rw [Measure.map_apply (measurable_pi_apply T) hPost_meas]
  rfl

end TraceLawAt

/-- A trace-level good event pushes to a kernel endpoint tail by measure
monotonicity.  This is the trace-law replacement for conditional probability. -/
theorem trace_good_event_lift_to_kernel
    {entry : Config (AgentState L K)} {T : ℕ}
    {μ : Measure (Phase3GoodClock.Trace L K)}
    (Law : TraceLawAt (L := L) (K := K) entry T μ)
    (Post : Config (AgentState L K) → Prop)
    (GoodTrace : Phase3GoodClock.Trace L K → Prop)
    {ε : ℝ≥0∞}
    (hPost_meas : MeasurableSet {c | ¬ Post c})
    (hbad : μ {tr | ¬ GoodTrace tr} ≤ ε)
    (hGoodPost : ∀ tr, GoodTrace tr → Post (tr T)) :
    ((NonuniformMajority L K).transitionKernel ^ T) entry {c | ¬ Post c} ≤ ε := by
  rw [TraceLawAt.kernel_bad_eq_trace_bad
    (L := L) (K := K) Law Post hPost_meas]
  refine le_trans (measure_mono ?_) hbad
  intro tr hbadPost hgood
  exact hbadPost (hGoodPost tr hgood)

/-- Slot-3 trace good event: the trace carries the range-local Core thread and
its endpoint satisfies the slot-3 postcondition. -/
def Phase3TraceGood
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (T : ℕ)
    (tr : Phase3GoodClock.Trace L K) : Prop :=
  GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
    Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)

/-- Split the slot-3 trace-good tail into the good-Core-thread tail plus the
endpoint failure tail on good Core traces. -/
theorem phase3TraceGood_whp_of_core_and_post
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell T : ℕ} {M g₀ : ℝ} {σ : Sign}
    {εcore εpost ε : ℝ≥0∞}
    (hcore :
      μ {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} ≤ εcore)
    (hpost :
      μ {tr |
        GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
        ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)}
        ≤ εpost)
    (hbudget : εcore + εpost ≤ ε) :
    μ {tr | ¬ Phase3TraceGood (L := L) (K := K) D θ n ell M g₀ σ T tr}
      ≤ ε := by
  classical
  have hsub :
      {tr | ¬ Phase3TraceGood (L := L) (K := K) D θ n ell M g₀ σ T tr} ⊆
        {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} ∪
        {tr |
          GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
          ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)} := by
    intro tr hbad
    by_cases hcoreGood : GoodCoreThreadTrace (L := L) (K := K) D θ tr
    · right
      refine ⟨hcoreGood, ?_⟩
      intro hpostGood
      exact hbad ⟨hcoreGood, hpostGood⟩
    · left
      exact hcoreGood
  calc
    μ {tr | ¬ Phase3TraceGood (L := L) (K := K) D θ n ell M g₀ σ T tr}
        ≤ μ ({tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} ∪
          {tr |
            GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
            ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)}) :=
      measure_mono hsub
    _ ≤ μ {tr | ¬ GoodCoreThreadTrace (L := L) (K := K) D θ tr} +
          μ {tr |
            GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
            ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)} :=
      measure_union_le _ _
    _ ≤ εcore + εpost :=
      add_le_add hcore hpost
    _ ≤ ε := hbudget

/-- Direct slot-3 trace-good tail from the discharged GoodClock Regime tail, a
surface constructor, and the remaining endpoint/post trace tail. -/
theorem phase3TraceGood_whp_of_regime_and_post
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell T : ℕ} {M g₀ : ℝ} {σ : Sign}
    {εq εh εcore εpost ε : ℝ≥0∞}
    (hquant :
      μ {tr | ¬ Phase3GoodClockRegime.ClockFrontQuantileRegime
        (L := L) (K := K) θ tr D.lastCoreHour} ≤ εq)
    (hhdom :
      μ {tr | Phase3GoodClockRegime.HDomFailureUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour} ≤ εh)
    (hcoreBudget : εq + εh ≤ εcore)
    (mkSurface : ∀ tr,
      Phase3GoodClockRegime.GoodClockUpTo
        (L := L) (K := K) D.M θ tr D.lastCoreHour →
        Phase3Core.CoreRunSurface (L := L) (K := K) D θ tr)
    (hpost :
      μ {tr |
        GoodCoreThreadTrace (L := L) (K := K) D θ tr ∧
        ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ (tr T)}
        ≤ εpost)
    (hbudget : εcore + εpost ≤ ε) :
    μ {tr | ¬ Phase3TraceGood (L := L) (K := K) D θ n ell M g₀ σ T tr}
      ≤ ε :=
  phase3TraceGood_whp_of_core_and_post
    (L := L) (K := K)
    (goodCoreThreadTrace_whp_of_regime
      (L := L) (K := K) hquant hhdom hcoreBudget mkSurface)
    hpost hbudget

/-- Specialized trace lift for the slot-3 `Post3` endpoint. -/
theorem phase3_trace_lift
    {entry : Config (AgentState L K)} {T : ℕ}
    {μ : Measure (Phase3GoodClock.Trace L K)}
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign} {ε : ℝ≥0∞}
    (Law : TraceLawAt (L := L) (K := K) entry T μ)
    (hbad :
      μ {tr | ¬ Phase3TraceGood
        (L := L) (K := K) D θ n ell M g₀ σ T tr} ≤ ε) :
    ((NonuniformMajority L K).transitionKernel ^ T) entry
      {c | ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c} ≤ ε :=
  trace_good_event_lift_to_kernel
    (L := L) (K := K) Law
    (Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀)
    (Phase3TraceGood (L := L) (K := K) D θ n ell M g₀ σ T)
    (DiscreteMeasurableSpace.forall_measurableSet _)
    hbad
    (by intro tr h; exact h.2)

/-- Trace-law residual for the protocol-entry slot-3 work item.  The residual is
only the endpoint law plus the trace-level bad-event bound; the Core good event
is range-local. -/
structure Phase3TraceLawBound
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (entry : Config (AgentState L K)) (T : ℕ) (ε : ℝ≥0) where
  μ : Measure (Phase3GoodClock.Trace L K)
  law : TraceLawAt (L := L) (K := K) entry T μ
  bad_trace :
    μ {tr | ¬ Phase3TraceGood
      (L := L) (K := K) D θ n ell M g₀ σ T tr} ≤ (ε : ℝ≥0∞)

namespace Phase3TraceLawBound

theorem tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (R : Phase3TraceLawBound
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε) :
    ((NonuniformMajority L K).transitionKernel ^ T) entry
      {c | ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c}
      ≤ (ε : ℝ≥0∞) :=
  phase3_trace_lift (L := L) (K := K) R.law R.bad_trace

end Phase3TraceLawBound

/-- Protocol-entry slot-3 weak work item backed directly by the trace law. -/
noncomputable def phase3TraceWork
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (R : Phase3TraceLawBound
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => c = entry ∧
    Phase3Post3.Phase3EntryGap (L := L) (K := K) n g₀ c
  Post := fun c => Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c
  t := T
  ε := ε
  convergence := by
    intro c hc
    rcases hc with ⟨rfl, _hentry⟩
    exact R.tail

@[simp] theorem phase3TraceWork_Post
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (R : Phase3TraceLawBound
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε) :
    (phase3TraceWork (L := L) (K := K) R).Post =
      fun c => Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c := rfl

@[simp] theorem phase3TraceWork_Pre
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)} {T : ℕ} {ε : ℝ≥0}
    (R : Phase3TraceLawBound
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε) :
    (phase3TraceWork (L := L) (K := K) R).Pre =
      fun c => c = entry ∧
        Phase3Post3.Phase3EntryGap (L := L) (K := K) n g₀ c := rfl

/-- The discharged row producers, with H13/H16 entering through their marked
engines and H15/H14 through the already-landed bridge/engine surfaces. -/
structure MarkedCoreEngineProducers
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  pre3 : Phase3Core.Pre3Seed (L := L) (K := K) D T
  h13 :
    Lemma613MarkedPullDrop.H13MarkedPullData
      (L := L) (K := K) D T
  h14 : Phase3StoppedTails.PhiZeroTail (L := L) (K := K) D T
  h15 : Phase3Engines.PhiDropStoppedEngine (L := L) (K := K) D T
  h16 :
    Lemma616MarkedCancelMass.H16MarkedCancelData
      (L := L) (K := K) D T

namespace MarkedCoreEngineProducers

noncomputable def toCoreEngineProducers
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : MarkedCoreEngineProducers (L := L) (K := K) D T) :
    Phase3Engines.CoreEngineProducers (L := L) (K := K) D T where
  pre3 := P.pre3
  h13 := Lemma613MarkedPullDrop.H13MarkedPullData.toH13Bridge
    (L := L) (K := K) P.h13
  h14 := P.h14
  h15 := P.h15
  h16 := Lemma616MarkedCancelMass.H16MarkedCancelData.toH16Engine
    (L := L) (K := K) P.h16

noncomputable def toCoreProducers
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : MarkedCoreEngineProducers (L := L) (K := K) D T) :
    Phase3Core.CoreProducers (L := L) (K := K) D T :=
  P.toCoreEngineProducers.toCoreProducers

theorem core_all
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : MarkedCoreEngineProducers (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour →
      Phase3Core.Core (L := L) (K := K) D T h :=
  Phase3Core.core_all (L := L) (K := K) P.toCoreProducers

theorem core_endpoint
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : MarkedCoreEngineProducers (L := L) (K := K) D T) :
    Phase3Core.Core (L := L) (K := K) D T D.lastCoreHour :=
  P.core_all D.lastCoreHour le_rfl

theorem lemma612_all
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (P : MarkedCoreEngineProducers (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour →
      Phase3Core.Lemma612 (L := L) (K := K) D T h :=
  Phase3Core.lemma612_all (L := L) (K := K) P.toCoreProducers

end MarkedCoreEngineProducers

/-- The remaining cross-leaf endpoint chain: after the discharged Core row
producers are assembled and the Core induction is run, the full protocol reaches
the `Snapshot617` endpoint through a finite killed-kernel CK hour chain from the
concrete protocol-entry configuration.

This field is more granular than the old carried `Snapshot617Tail`: it exposes
the killed per-hour gates, tails, final readout, horizon identity, and budget
that `Snapshot617EntryHourChain.toSnapshot617EntryTail` composes. -/
structure CoreSnapshot617TailInput
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (entry : Config (AgentState L K)) where
  producers :
    MarkedCoreEngineProducers (L := L) (K := K) D T
  entry_slot3 :
    Phase3Post3.Phase3EntryGap (L := L) (K := K) n g₀ entry
  chain :
    Phase3Post3.Snapshot617EntryHourChain
      (L := L) (K := K) n ell M g₀ σ entry

namespace CoreSnapshot617TailInput

noncomputable def toPhase3PostEntryTail
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : CoreSnapshot617TailInput
      (L := L) (K := K) D T n ell M g₀ σ entry) :
    Phase3Post3.Phase3PostEntryTail (L := L) (K := K) n ell M g₀ σ entry where
  snap := A.chain.toSnapshot617EntryTail

noncomputable def phase3W
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : CoreSnapshot617TailInput
      (L := L) (K := K) D T n ell M g₀ σ entry) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase3Post3.phase3PostWorkAtEntry
    (L := L) (K := K) A.entry_slot3 A.toPhase3PostEntryTail

@[simp] theorem phase3W_Post
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : CoreSnapshot617TailInput
      (L := L) (K := K) D T n ell M g₀ σ entry) :
    (A.phase3W).Post =
      fun c => Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c := rfl

@[simp] theorem phase3W_Pre
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {entry : Config (AgentState L K)}
    (A : CoreSnapshot617TailInput
      (L := L) (K := K) D T n ell M g₀ σ entry) :
    (A.phase3W).Pre =
      fun c => c = entry ∧
        Phase3Post3.Phase3EntryGap (L := L) (K := K) n g₀ c := rfl

end CoreSnapshot617TailInput

/-!
## Deterministic per-thread slot-3 adapter

This legacy adapter is retained for local Core-row testing.  It consumes an
all-hours GoodClock witness and a concrete stopped Core surface, so it is not the
final protocol-entry atom.  The final atom below uses the trace-law pushforward
and the range-local `RangeLocalCoreThread` event instead.
-/

/-- Legacy per-thread residual bundle for deterministic Core-row tests. -/
structure Phase3ThreadData
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) where
  /-- Legacy all-hours GoodClock witness plus the stopped Core surface. -/
  core : AllHoursCoreThread (L := L) (K := K) D θ tr
  /-- The Core Pre₃ seed at the same thread built from `core`. -/
  pre3 :
    Phase3Core.Pre3Seed (L := L) (K := K) D core.toCoreThread
  /-- The phase-2→3 entry handoff in the final slot-3 `Pre` shape:
  exact phase 3 plus the pinned signed gap `g₀`. -/
  entry_slot3 :
    Phase3Post3.Phase3EntryGap (L := L) (K := K) n g₀ pre3.entry
  /-- Landed H13/mkH13 producer data. -/
  h13 :
    Lemma613MarkedPullDrop.H13MarkedPullData
      (L := L) (K := K) D core.toCoreThread
  /-- Landed H14/mkH14 producer data. -/
  h14 : Phase3StoppedTails.PhiZeroTail (L := L) (K := K) D core.toCoreThread
  /-- Landed H15/mkH15 producer data. -/
  h15 : Phase3Engines.PhiDropStoppedEngine (L := L) (K := K) D core.toCoreThread
  /-- Landed H16/mkH16 producer data. -/
  h16 :
    Lemma616MarkedCancelMass.H16MarkedCancelData
      (L := L) (K := K) D core.toCoreThread
  /-- Entry-specialized killed-kernel hour-chain composition through the
  `Snapshot617` endpoint.  Its `good0` obligation is only at `pre3.entry`. -/
  entryChain :
    Phase3Post3.Snapshot617EntryHourChain
      (L := L) (K := K) n ell M g₀ σ pre3.entry

namespace Phase3ThreadData

/-- The concrete Core thread constructed from the protocol-entry Regime and
ClockCut surface. -/
noncomputable def toCoreThread
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3ThreadData
      (L := L) (K := K) (θ := θ) (tr := tr) D n ell M g₀ σ) :
    Phase3Core.CoreThread (L := L) (K := K) D θ tr :=
  A.core.toCoreThread

/-- The discharged row producers at the constructed Core thread. -/
noncomputable def toProducers
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3ThreadData
      (L := L) (K := K) (θ := θ) (tr := tr) D n ell M g₀ σ) :
    MarkedCoreEngineProducers
      (L := L) (K := K) (θ := θ) (tr := tr) D A.toCoreThread where
  pre3 := A.pre3
  h13 := A.h13
  h14 := A.h14
  h15 := A.h15
  h16 := A.h16

/-- The granular Core/Snapshot617 input assembled from protocol-entry residuals. -/
noncomputable def toCoreSnapshot617TailInput
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3ThreadData
      (L := L) (K := K) (θ := θ) (tr := tr) D n ell M g₀ σ) :
    CoreSnapshot617TailInput
      (L := L) (K := K) (θ := θ) (tr := tr) D A.toCoreThread
      n ell M g₀ σ A.pre3.entry where
  producers := A.toProducers
  entry_slot3 := A.entry_slot3
  chain := A.entryChain

end Phase3ThreadData

/-- Legacy deterministic slot-3 atom instantiated from per-thread residuals. -/
noncomputable def phase3ThreadWork
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3ThreadData
      (L := L) (K := K) (θ := θ) (tr := tr) D n ell M g₀ σ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  A.toCoreSnapshot617TailInput.phase3W

@[simp] theorem phase3ThreadWork_Post
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3ThreadData
      (L := L) (K := K) (θ := θ) (tr := tr) D n ell M g₀ σ) :
    (phase3ThreadWork (L := L) (K := K) A).Post =
      fun c => Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c := rfl

@[simp] theorem phase3ThreadWork_Pre
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3ThreadData
      (L := L) (K := K) (θ := θ) (tr := tr) D n ell M g₀ σ) :
    (phase3ThreadWork (L := L) (K := K) A).Pre =
      fun c => c = A.pre3.entry ∧
        Phase3Post3.Phase3EntryGap (L := L) (K := K) n g₀ c := rfl

/-!
## Protocol-entry slot-3 trace atom

The top-level slot-3 atom is unconditional over the protocol endpoint law.  The
Core good-thread existence is paid inside `chain.bad_trace` through the
range-local trace event; the only named slot-3 residual data at this surface is
the concrete entry seam and the carried endpoint-chain trace residual.
-/

/-- Protocol-entry residual bundle for the final slot-3 atom. -/
structure Phase3EntryTraceData
    (D : Phase3Core.Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) where
  /-- Concrete phase-3 entry configuration. -/
  entry : Config (AgentState L K)
  /-- Endpoint horizon used by the trace law. -/
  T : ℕ
  /-- Slot-3 error budget assigned to the trace residual. -/
  ε : ℝ≥0
  /-- The remaining phase-2→3 seam witness. -/
  entry_slot3 : Phase3Post3.Phase3EntryGap (L := L) (K := K) n g₀ entry
  /-- Carried endpoint-chain trace residual.  Its bad event already includes the
  range-local Core good-thread event. -/
  chain :
    Phase3TraceLawBound
      (L := L) (K := K) D θ n ell M g₀ σ entry T ε

namespace Phase3EntryTraceData

theorem tail
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3EntryTraceData (L := L) (K := K) D θ n ell M g₀ σ) :
    ((NonuniformMajority L K).transitionKernel ^ A.T) A.entry
      {c | ¬ Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c}
      ≤ (A.ε : ℝ≥0∞) :=
  A.chain.tail

end Phase3EntryTraceData

/-- Top-level slot-3 atom instantiated from the protocol entry trace residual. -/
noncomputable def phase3EntryWork
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3EntryTraceData (L := L) (K := K) D θ n ell M g₀ σ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  phase3TraceWork (L := L) (K := K) A.chain

@[simp] theorem phase3EntryWork_Post
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3EntryTraceData (L := L) (K := K) D θ n ell M g₀ σ) :
    (phase3EntryWork (L := L) (K := K) A).Post =
      fun c => Phase3Post3.Post3 (L := L) (K := K) n ell M σ g₀ c := rfl

@[simp] theorem phase3EntryWork_Pre
    {D : Phase3Core.Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (A : Phase3EntryTraceData (L := L) (K := K) D θ n ell M g₀ σ) :
    (phase3EntryWork (L := L) (K := K) A).Pre =
      fun c => c = A.entry ∧
        Phase3Post3.Phase3EntryGap (L := L) (K := K) n g₀ c := rfl

#print axioms AllHoursCoreThread.toCoreThread
#print axioms AllHoursCoreThread.clockInput_eq_allRegime
#print axioms goodCoreThreadTrace_whp_of_goodClock
#print axioms goodCoreThreadTrace_whp_of_regime
#print axioms goodCoreThreadTrace_whp_of_goodClock_and_surface
#print axioms TraceLawAt.kernel_bad_eq_trace_bad
#print axioms trace_good_event_lift_to_kernel
#print axioms phase3TraceGood_whp_of_core_and_post
#print axioms phase3TraceGood_whp_of_regime_and_post
#print axioms phase3_trace_lift
#print axioms Phase3TraceLawBound.tail
#print axioms phase3TraceWork
#print axioms MarkedCoreEngineProducers.toCoreEngineProducers
#print axioms MarkedCoreEngineProducers.toCoreProducers
#print axioms MarkedCoreEngineProducers.core_all
#print axioms MarkedCoreEngineProducers.core_endpoint
#print axioms MarkedCoreEngineProducers.lemma612_all
#print axioms CoreSnapshot617TailInput.toPhase3PostEntryTail
#print axioms CoreSnapshot617TailInput.phase3W
#print axioms Phase3ThreadData.toCoreThread
#print axioms Phase3ThreadData.toProducers
#print axioms Phase3ThreadData.toCoreSnapshot617TailInput
#print axioms phase3ThreadWork
#print axioms Phase3EntryTraceData.tail
#print axioms phase3EntryWork

end Phase3Assembly

end Ripple.PopulationProtocol.ExactMajority
