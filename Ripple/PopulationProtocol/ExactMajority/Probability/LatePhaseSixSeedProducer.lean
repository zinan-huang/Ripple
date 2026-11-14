-- Ripple/PopulationProtocol/ExactMajority/Probability/LatePhaseSixSeedProducer.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFiveSixWindowTailClosed
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongContinuationTimer
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceOvershootSource

/-!
# The genuine Phase-6 seed after sampling completion

This file instantiates `PhaseSixSeedProducer` of `LateMixedFiveSixWindowTailWf`.

The stochastic input is the existing actual-protocol Phase-5 timer theorem
`StrongContinuationTimer.timed_tail_calibrated`.  It is applied on each finite
`completionTime` fibre and summed with `PairLog.genuine_seed_splice`, so the
result remains under `law init`; no successful future event changes the law.

At the genuine first Phase-6 hit, the predecessor is pure Phase 5.  The frozen
Phase-5 dispatcher then gives both deterministic seed facts needed by it:

* every output has phase at most 6, hence `NoOvershoot 5`;
* every Phase-6 Clock output was created by `stdCounterSubroutine` from a
  Phase-5 Clock and therefore has the full reset counter `50 (L+1)`.

The latter is expressed by the Phase-6 timer potential.  Unselected Phase-5 agents have
zero summand, and the selected pair contributes at most two fresh summands.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindowTailWf

open TimeTheorem PairLog
open PhaseOneDrain PhaseOneDrainStopping
open LateSamplingCompletion LateF6OriginalLaw
open StrongContinuationTimer
open AdvanceNoOvershoot

variable {L K n : ℕ}

/-! ## Deterministic first-seed bounds -/

/-- A pure Phase-5 configuration has zero Phase-6 at-risk potential. -/
private theorem phaseFive_potential_zero
    (scale : ℝ) (c : Config (AgentState L K))
    (hfive : ∀ a ∈ c, a.phase.val = 5) :
    advanceClockPotential (L := L) (K := K) 5 scale c = 0 := by
  unfold advanceClockPotential Config.sumOf
  revert hfive
  induction c using Multiset.induction with
  | empty =>
      intro _
      simp
  | cons a c ih =>
      intro hfive
      have ha : a.phase.val = 5 := hfive a (by simp)
      have hc : ∀ b ∈ c, b.phase.val = 5 := by
        intro b hb
        exact hfive b (by simp [hb])
      have hcond : ¬ (a.role = .clock ∧ a.phase.val = 5 + 1) := by
        rintro ⟨_, hphase⟩
        omega
      have hzero :
          advanceClockSummand (L := L) (K := K) 5 scale a = 0 := by
        unfold advanceClockSummand
        rw [if_neg hcond]
      rw [Multiset.map_cons, Multiset.sum_cons, hzero, zero_add]
      exact ih hc

/-- On a pure Phase-5 pair, the two post-step Phase-6 summands are at most
`2 * freshVal`.  A Clock input is routed literally through
`stdCounterSubroutine`; a non-Clock output stays non-Clock. -/
private theorem phaseFive_pair_potential_le
    (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    advanceClockSummand (L := L) (K := K) 5 1
          (Transition L K s t).1 +
        advanceClockSummand (L := L) (K := K) 5 1
          (Transition L K s t).2 ≤
      2 * freshVal (L := L) 1 := by
  rw [ReserveSampling.Transition_eq_Phase5Transition_of_phase5
    (L := L) (K := K) s t hs ht]
  have htimed : CounterTimedPhase 6 := by
    simp [CounterTimedPhase]
  have hleft :
      advanceClockSummand (L := L) (K := K) 5 1
          (Phase5Transition L K s t).1 ≤
        freshVal (L := L) 1 := by
    by_cases hclock : s.role = .clock
    · rw [AdvanceNoOvershoot.Phase5Transition_left_clock
        (L := L) (K := K) s t hclock]
      exact advanceClockSummand_stdCounterSubroutine_advance_le
        (L := L) (K := K) 5 1 s hclock htimed (by omega)
    · have hout : (Phase5Transition L K s t).1.role ≠ .clock := by
        rw [Phase5Convergence.Phase5Transition_fst_role_eq
          (L := L) (K := K) s t hs]
        exact hclock
      have hcond :
          ¬ ((Phase5Transition L K s t).1.role = .clock ∧
            (Phase5Transition L K s t).1.phase.val = 5 + 1) := by
        rintro ⟨hrole, _⟩
        exact hout hrole
      have hzero :
          advanceClockSummand (L := L) (K := K) 5 1
              (Phase5Transition L K s t).1 = 0 := by
        unfold advanceClockSummand
        rw [if_neg hcond]
      rw [hzero]
      exact zero_le'
  have hright :
      advanceClockSummand (L := L) (K := K) 5 1
          (Phase5Transition L K s t).2 ≤
        freshVal (L := L) 1 := by
    by_cases hclock : t.role = .clock
    · rw [AdvanceNoOvershoot.Phase5Transition_right_clock
        (L := L) (K := K) s t hclock]
      exact advanceClockSummand_stdCounterSubroutine_advance_le
        (L := L) (K := K) 5 1 t hclock htimed (by omega)
    · have hout : (Phase5Transition L K s t).2.role ≠ .clock := by
        rw [Phase5Convergence.Phase5Transition_snd_role_eq
          (L := L) (K := K) s t ht]
        exact hclock
      have hcond :
          ¬ ((Phase5Transition L K s t).2.role = .clock ∧
            (Phase5Transition L K s t).2.phase.val = 5 + 1) := by
        rintro ⟨hrole, _⟩
        exact hout hrole
      have hzero :
          advanceClockSummand (L := L) (K := K) 5 1
              (Phase5Transition L K s t).2 = 0 := by
        unfold advanceClockSummand
        rw [if_neg hcond]
      rw [hzero]
      exact zero_le'
  calc
    advanceClockSummand (L := L) (K := K) 5 1
          (Phase5Transition L K s t).1 +
        advanceClockSummand (L := L) (K := K) 5 1
          (Phase5Transition L K s t).2
        ≤ freshVal (L := L) 1 + freshVal (L := L) 1 :=
      add_le_add hleft hright
    _ = 2 * freshVal (L := L) 1 := by ring

/-- One draw from a pure Phase-5 configuration cannot create Phase 7. -/
private theorem phaseFive_applyDraw_noOvershoot
    (c : Config (AgentState L K))
    (hfive : ∀ a ∈ c, a.phase.val = 5)
    (d : Draw L K) :
    NoOvershoot (L := L) (K := K) 5 (applyDraw c d) := by
  cases d with
  | none =>
      change NoOvershoot (L := L) (K := K) 5 c
      intro a ha
      have hp := hfive a ha
      omega
  | some pair =>
      change NoOvershoot (L := L) (K := K) 5
        (Protocol.stepOrSelf (NonuniformMajority L K)
          c pair.1.1 pair.2.1)
      by_cases happ : Protocol.Applicable c pair.1.1 pair.2.1
      · have hsMem : pair.1.1 ∈ c :=
          Multiset.mem_of_le happ (by simp)
        have htMem : pair.2.1 ∈ c :=
          Multiset.mem_of_le happ (by simp)
        have hs : pair.1.1.phase.val = 5 := hfive _ hsMem
        have ht : pair.2.1.phase.val = 5 := hfive _ htMem
        have houtputs := ReserveSampling.Phase5Transition_phase_le_six
          (L := L) (K := K) pair.1.1 pair.2.1 hs ht
        have htransition :=
          ReserveSampling.Transition_eq_Phase5Transition_of_phase5
            (L := L) (K := K) pair.1.1 pair.2.1 hs ht
        intro a ha
        rcases AdvanceNoOvershoot.mem_stepOrSelf_cases
            c pair.1.1 pair.2.1 a happ ha with hold | rfl | rfl
        · have hp := hfive a
            (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
          omega
        · rw [htransition]
          omega
        · rw [htransition]
          omega
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
        intro a ha
        have hp := hfive a ha
        omega

/-- One draw from a pure Phase-5 configuration has fresh Phase-6 potential at
most `n * freshVal`.  Only the selected pair can contribute, and it contributes
at most two fresh summands. -/
private theorem phaseFive_applyDraw_potential_le
    (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hfive : ∀ a ∈ c, a.phase.val = 5)
    (d : Draw L K) :
    advanceClockPotential (L := L) (K := K) 5 1 (applyDraw c d) ≤
      (n : ℝ≥0∞) * freshVal (L := L) 1 := by
  cases d with
  | none =>
      change advanceClockPotential (L := L) (K := K) 5 1 c ≤ _
      rw [phaseFive_potential_zero (L := L) (K := K) 1 c hfive]
      exact zero_le'
  | some pair =>
      change advanceClockPotential (L := L) (K := K) 5 1
          (Protocol.stepOrSelf (NonuniformMajority L K)
            c pair.1.1 pair.2.1) ≤ _
      by_cases happ : Protocol.Applicable c pair.1.1 pair.2.1
      · have hbase :
            Config.sumOf
                (advanceClockSummand (L := L) (K := K) 5 1)
                (c - {pair.1.1, pair.2.1}) = 0 := by
          change advanceClockPotential (L := L) (K := K) 5 1
              (c - {pair.1.1, pair.2.1}) = 0
          apply phaseFive_potential_zero
          intro a ha
          exact hfive a
            (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
        have hsMem : pair.1.1 ∈ c :=
          Multiset.mem_of_le happ (by simp)
        have htMem : pair.2.1 ∈ c :=
          Multiset.mem_of_le happ (by simp)
        have hs : pair.1.1.phase.val = 5 := hfive _ hsMem
        have ht : pair.2.1.phase.val = 5 := hfive _ htMem
        have hpair := phaseFive_pair_potential_le
          (L := L) (K := K) pair.1.1 pair.2.1 hs ht
        have htwo : (2 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
          exact_mod_cast hn
        rw [advanceClockPotential_stepOrSelf_eq_base_add_pair
          (L := L) (K := K) 5 1 c pair.1.1 pair.2.1 happ,
          hbase, zero_add]
        exact hpair.trans (mul_le_mul_right' htwo _)
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ,
          phaseFive_potential_zero (L := L) (K := K) 1 c hfive]
        exact zero_le'

/-! ## The original-law Phase-5 timer failure -/

/-- Failure of the actual Phase-5 upper timer on the genuine completion fibre.
There is no contribution when `completionTime = ⊤`, because the producer is
only required after a supplied finite completion time. -/
def phaseSixSeedFailure (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ u : ℕ,
    completionTime init n ω = (u : WithTop ℕ) ∧
      ¬ HigherSeed 5
        (trace init ω (u + PhaseOneTimer.timerHorizon n))}

@[simp] theorem mem_phaseSixSeedFailure_iff
    (init : InputCfg n) (ω : InputLog n) :
    ω ∈ phaseSixSeedFailure init ↔
      ∃ u : ℕ, completionTime init n ω = (u : WithTop ℕ) ∧
        ¬ HigherSeed 5
          (trace init ω (u + PhaseOneTimer.timerHorizon n)) :=
  Iff.rfl

/-- A finite completion-time equality exposes the completed all-Phase-5 state. -/
theorem samplingComplete_of_completionTime_eq
    (init : InputCfg n) (ω : InputLog n) (u : ℕ)
    (h : completionTime init n ω = (u : WithTop ℕ)) :
    SamplingComplete n (trace init ω u) := by
  have hfirst :=
    (exitTime_eq_iff_firstHit init (SamplingComplete n) ω u).mp
      (by simpa only [completionTime] using h)
  exact hfirst.1

/-- The Phase-5 timer failure is measurable. -/
theorem phaseSixSeedFailure_measurable (init : InputCfg n) :
    MeasurableSet (phaseSixSeedFailure init) := by
  have heq : phaseSixSeedFailure init =
      ⋃ u : ℕ,
        {ω | completionTime init n ω = (u : WithTop ℕ)} ∩
          {ω | ¬ HigherSeed 5
            (trace init ω (u + PhaseOneTimer.timerHorizon n))} := by
    ext ω
    simp only [phaseSixSeedFailure, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
  rw [heq]
  apply MeasurableSet.iUnion
  intro u
  have htime : MeasurableSet
      {ω | completionTime init n ω = (u : WithTop ℕ)} :=
    (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le u _
      ((completionTime_past init n) u)
  have hbad : MeasurableSet
      {ω | ¬ HigherSeed 5
        (trace init ω (u + PhaseOneTimer.timerHorizon n))} :=
    (show MeasurableSet {c : InputCfg n | ¬ HigherSeed 5 c} from
      (Set.to_countable _).measurableSet).preimage
        ((measurable_pi_apply
          (u + PhaseOneTimer.timerHorizon n)).comp
            (measurable_trace init))
  exact htime.inter hbad

/-- The existing actual Phase-5 timer, spliced over the disjoint genuine
completion-time fibres.  The prefix event retains its probability factor, so
there is no union over possible completion times and no conditioning on a
future successful timer run. -/
theorem law_phaseSixSeedFailure_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseSixSeedFailure init) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 5) := by
  have hn : 2 ≤ n := by
    have hnforty := (time_population_bounds hinput.1).2
    omega
  refine genuine_seed_splice (law init) (completionTime init n)
    (phaseSixSeedFailure init)
    (ENNReal.ofReal (1 / (n : ℝ) ^ 5))
    (phaseSixSeedFailure_measurable init)
    (fun u =>
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le u _
        ((completionTime_past init n) u)) ?_ ?_
  · intro ω hω
    rw [mem_phaseSixSeedFailure_iff] at hω
    obtain ⟨u, hu, _⟩ := hω
    rw [hu]
    exact WithTop.coe_ne_top
  · intro u
    have hσu := (completionTime_past init n) u
    rw [pairLogFiltration_eq_comap] at hσu
    obtain ⟨Aσ, _, hAσ⟩ := hσu
    let A : Set ((k : Finset.Iic u) →
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
      {p | p ∈ Aσ ∧ SamplingComplete n (prefixCfg init u p)}
    have hmem (ω : InputLog n) :
        frestrictLe
            (π := fun _ : ℕ =>
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256) u ω ∈ Aσ ↔
          completionTime init n ω = (u : WithTop ℕ) := by
      change ω ∈
          (frestrictLe
            (π := fun _ : ℕ =>
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256) u) ⁻¹' Aσ ↔
        ω ∈ {ω | completionTime init n ω = (u : WithTop ℕ)}
      rw [hAσ]
    have htail := timed_tail_calibrated
      init hinput.2.1 5 (by simp [TimedPhase]) hn u A
      (fun p hp => by
        refine ⟨hp.2.population, ?_⟩
        exact hp.2.phase_five)
    calc
      law init
          (phaseSixSeedFailure init ∩
            {ω | completionTime init n ω = (u : WithTop ℕ)}) ≤
        law init {ω |
          frestrictLe
              (π := fun _ : ℕ =>
                Draw (PhaseThreeModel.Numeric.hourIndex n) 256) u ω ∈ A ∧
            ¬ HigherSeed 5
              (trace init ω (u + PhaseOneTimer.timerHorizon n))} := by
        apply measure_mono
        rintro ω ⟨hbad, hu⟩
        rw [mem_phaseSixSeedFailure_iff] at hbad
        obtain ⟨r, hr, hlate⟩ := hbad
        have hru : r = u :=
          WithTop.coe_injective (hr.symm.trans hu)
        subst r
        have hcomplete := samplingComplete_of_completionTime_eq
          init ω u hu
        refine ⟨?_, hlate⟩
        refine ⟨(hmem ω).2 hu, ?_⟩
        change SamplingComplete n (trace init ω u)
        exact hcomplete
      _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 5) *
          law init {ω |
            frestrictLe
              (π := fun _ : ℕ =>
                Draw (PhaseThreeModel.Numeric.hourIndex n) 256) u ω ∈ A} :=
        htail
      _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 5) *
          law init {ω |
            completionTime init n ω = (u : WithTop ℕ)} :=
        mul_le_mul_left' (measure_mono (by
          intro ω hω
          exact (hmem ω).1 hω.1)) _

/-! ## Reconstructing the genuine first Phase-6 seed -/

/-- If a Phase-6-or-higher state is present by a finite deadline after a pure
Phase-5 state, then the genuine first `someGE 6` time lies in that interval. -/
theorem exists_firstSix_between
    (init : InputCfg n) (ω : InputLog n) (u N : ℕ)
    (hfive : allPhaseFive (trace init ω u))
    (hhit : HigherSeed 5 (trace init ω (u + N))) :
    ∃ s : ℕ, firstSixStart init ω = (s : WithTop ℕ) ∧
      u ≤ s ∧ s ≤ u + N := by
  classical
  have hend : StageEventSpec.someGE (n := n) 6
      (trace init ω (u + N)) := by
    rcases hhit with ⟨a, ha, hp⟩
    exact ⟨a, ha, by omega⟩
  have hex : ∃ s : ℕ,
      StageEventSpec.someGE (n := n) 6 (trace init ω s) :=
    ⟨u + N, hend⟩
  let s : ℕ := Nat.find hex
  have hfirst : StageEventSpec.firstHit
      (StageEventSpec.someGE (n := n) 6) (trace init ω) s :=
    ⟨Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hus : u ≤ s := by
    by_contra horder
    have hupper := phase_upper_reachable 5 _ _
      (trace_reachable init ω (by omega : s ≤ u))
      (fun a ha => (hfive a ha).le)
    obtain ⟨a, ha, hp⟩ := hfirst.1
    have hu := hupper a ha
    omega
  have htime : firstSixStart init ω = (s : WithTop ℕ) := by
    simpa only [firstSixStart] using
      ((exitTime_eq_iff_firstHit init
        (StageEventSpec.someGE (n := n) 6) ω s).2 hfirst)
  exact ⟨s, htime, hus, Nat.find_min' hex hend⟩

/-- At the genuine first Phase-6 hit after completion, the timer seed is
fresh: the state has no Phase 7, and its Phase-6 potential is bounded by
`n * exp(-50(H))`. -/
theorem firstSix_timerSeed
    (init : InputCfg n) (ω : InputLog n) (u s : ℕ)
    (hcomplete : SamplingComplete n (trace init ω u))
    (htime : firstSixStart init ω = (s : WithTop ℕ))
    (hus : u ≤ s) (hn : 2 ≤ n) :
    PhaseSixTimerSeed n (trace init ω s) := by
  have hfirst :=
    (exitTime_eq_iff_firstHit init
      (StageEventSpec.someGE (n := n) 6) ω s).mp
      (by simpa only [firstSixStart] using htime)
  have huslt : u < s := by
    by_contra hnot
    have hsu : s ≤ u := by omega
    have heq : s = u := Nat.le_antisymm hsu hus
    subst s
    obtain ⟨a, ha, hp⟩ := hfirst.1
    have hfive := hcomplete.phase_five a ha
    omega
  let k : ℕ := s - 1
  have hsk : s = k + 1 := by
    dsimp [k]
    omega
  have huk : u ≤ k := by
    dsimp [k]
    omega
  have hks : k < s := by
    dsimp [k]
    omega
  have hlower := phase_lower_reachable 5
    (trace init ω u) (trace init ω k)
    (trace_reachable init ω huk)
    (fun a ha => (hcomplete.phase_five a ha).ge)
  have hpure : ∀ a ∈ trace init ω k, a.phase.val = 5 := by
    intro a ha
    have hlo := hlower a ha
    have hhi : a.phase.val < 6 := by
      by_contra hge
      exact (hfirst.2 k hks) ⟨a, ha, by omega⟩
    omega
  have hstep : trace init ω s =
      applyDraw (trace init ω k) (ω (k + 1)) := by
    rw [hsk, trace_succ]
  have hcard : (trace init ω s).card = n :=
    (Protocol.reachable_card_eq
      (trace_reachable init ω hus)).trans hcomplete.population
  have hno := phaseFive_applyDraw_noOvershoot
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    (trace init ω k) hpure (ω (k + 1))
  have hpotential := phaseFive_applyDraw_potential_le
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    n hn (trace init ω k) hpure (ω (k + 1))
  refine
    { population := hcard
      no_overshoot := ?_
      potential := ?_ }
  · rw [hstep]
    exact hno
  · rw [hstep]
    simpa [freshVal] using hpotential

/-- Outside `phaseSixSeedFailure`, every supplied finite completion time yields
the genuine first-Phase-6 receipt. -/
theorem phaseSixSeedReceipt_of_not_failure
    (hn : 2 ≤ n) (init : InputCfg n) (ω : InputLog n) (u : ℕ)
    (hcompletion : completionTime init n ω = (u : WithTop ℕ))
    (hgood : ω ∉ phaseSixSeedFailure init) :
    ∃ s : ℕ, PhaseSixSeedReceipt init ω u s := by
  have hcomplete := samplingComplete_of_completionTime_eq
    init ω u hcompletion
  have hhit : HigherSeed 5
      (trace init ω (u + PhaseOneTimer.timerHorizon n)) := by
    by_contra hnone
    apply hgood
    rw [mem_phaseSixSeedFailure_iff]
    exact ⟨u, hcompletion, hnone⟩
  obtain ⟨s, htime, hus, _⟩ := exists_firstSix_between
    init ω u (PhaseOneTimer.timerHorizon n)
    hcomplete.phase_five hhit
  have hseed := firstSix_timerSeed
    init ω u s hcomplete htime hus hn
  exact
    ⟨s,
      { time := htime
        order := hus
        timer_seed := hseed }⟩

/-- The concrete producer. -/
theorem phaseSixSeedProducer
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    PhaseSixSeedProducer init (phaseSixSeedFailure init) := by
  have hn : 2 ≤ n := by
    have hnforty := (time_population_bounds hinput.1).2
    omega
  refine
    { tail := law_phaseSixSeedFailure_tail init hinput
      produce := ?_ }
  intro ω u hu hgood
  exact phaseSixSeedReceipt_of_not_failure
    hn init ω u hu hgood

/-- The mixed-window failure has original-law probability at most
`n⁻²` from `GoodInput` alone: the seed producer is discharged by
`phaseSixSeedProducer`, the dispatch by `advanceRegimeDispatch_five`, and the
overshoot bridge is the reachable per-configuration one. -/
theorem law_mixedFailure_inverse_square_of_goodInput
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (LateMixedFiveSixWindow.mixedFailure init) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) :=
  LateMixedFiveSixWindowTailClosed.law_mixedFailure_inverse_square init hinput
    (phaseSixSeedFailure init) (phaseSixSeedProducer init hinput)

/-!
THEOREM LIST
* `mem_phaseSixSeedFailure_iff`
* `samplingComplete_of_completionTime_eq`
* `phaseSixSeedFailure_measurable`
* `law_phaseSixSeedFailure_tail`
* `exists_firstSix_between`
* `firstSix_timerSeed`
* `phaseSixSeedReceipt_of_not_failure`
* `phaseSixSeedProducer`
* `law_mixedFailure_inverse_square_of_goodInput`

CLOSES
* The first explicit input `PhaseSixSeedProducer`.
* The original-law `n⁻⁵` Phase-5 upper-timer failure set at the genuine
  completion stopping time.
* Existence and ordering of the genuine first Phase-6 seed.
* The fresh Phase-6 timer potential at that first seed.
* `NoOvershoot 5` at that first seed.
* No conditioning on future timer success or epidemic success.

EXPLICIT INPUTS
* `ThresholdEpidemic.GoodInput n init`.
* The definitions in `LateMixedFiveSixWindowTailWf.lean`.
* No new stochastic hypothesis.

UNFINISHED
* Nothing about `AdvanceRegimeDispatch 5` or the overshoot bridge: the
  Wf tail (`LateMixedFiveSixWindowTailClosed`) discharges the dispatch with
  `advanceRegimeDispatch_five` and uses the reachable per-configuration bridge,
  not the false global `OvershootForcesZeroClock 5`.
* The repair of the row-2 fuel-entry certificate is independent of this
  seed producer.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindowTailWf

end
