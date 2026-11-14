-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTimerUpperOriginalLaw.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerUpperPrefixScalar
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerRouteProof
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongContinuationTimer
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourStops

/-!
# Original-law upper timer for homogeneous late phases

Main APIs used here, restated for repairability:

* `UniformRecovery.reachable_positive_phase_has_clockPair`:
  reachable + valid initial + positive population + positive pure phase imply a
  Clock pair.
* `UniformRecovery.timed_transition_left_clock` and
  `timed_transition_right_clock`: on a same timed-phase pair, a Clock endpoint
  is exactly `finishPhase10Entry ... (stdCounterSubroutine ... endpoint)`.
* `StrongContinuationTimer.zero_clock_advances`: a zero-counter Clock in a
  timed phase produces a strictly higher phase.
* `StrongContinuationTimer.no_higher_window`: from a homogeneous start and no
  higher endpoint, every intermediate configuration remains homogeneous.
* `LateTimerProtectionOriginalLaw.labelParticipation_*`: the selected-label
  indicator is adapted Bernoulli with conditional mean exactly `2/n` under
  the original pair-log law.
* `PhaseThreeClockProducer.splice_of_local`: disjoint stopping-time-fibre
  summation, with no conditioning on future success.

Counter-freshness counterexample: an early phase-`p` Clock can meet the final
phase-`p-1` laggard.  The epidemic raises the laggard, and the same dispatch
reduces the Clock counter.  Therefore the first homogeneous state need not
have a fresh counter.  The theorem below uses only `clockCounter_le_capacity`.

Theorem list:
* `homogeneousLatePhaseStart_past`
* `homogeneousLatePhaseStart_eq_iff`
* `clockCounter_le_capacity`
* `clockLabelStep_exact`
* `fixedClock_counter_accounting`
* `bernoulliCount_le_capacity_of_noHigher`
* `lateTimerUpperFailure_fibre_tail`
* `law_lateTimerUpperFailure_tail`
* `nextPhaseSeed_finite_and_le`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped BigOperators ENNReal NNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateTimerUpperOriginalLaw

open TimeTheorem PairLog TraceDrain StageEventSpec
open PhaseOneDrain PhaseOneDrainStopping
open LateTimerProtectionOriginalLaw

variable {n : ℕ}

/-- All agents are at phase exactly `p`. -/
def allPhaseExactly (p : ℕ) (c : InputCfg n) : Prop :=
  ∀ a ∈ c, a.phase.val = p

/-- Genuine first homogeneous Phase-`p` time. -/
def homogeneousLatePhaseStart
    (init : InputCfg n) (p : ℕ) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (allPhaseExactly p)

/-- The literal equation-(10) horizon `ceil (54 n log n)`. -/
noncomputable def lateTimerUpperHorizon (n : ℕ) : ℕ :=
  logWindow n 54

/-- One finite homogeneous-start fibre. -/
def homogeneousLatePhaseFibre
    (init : InputCfg n) (p s : ℕ) : Set (InputLog n) :=
  {ω | homogeneousLatePhaseStart init p ω = (s : WithTop ℕ)}

/-- Equation-(10) failure.  An infinite homogeneous start contributes nothing;
downstream consumers supply a finite homogeneous start.  By phase
monotonicity, absence of a higher phase at the endpoint is equivalent to no
next seed anywhere in this interval. -/
def lateTimerUpperFailure
    (init : InputCfg n) (p : ℕ) : Set (InputLog n) :=
  {ω | ∃ s : ℕ,
    homogeneousLatePhaseStart init p ω = (s : WithTop ℕ) ∧
      ¬ StrongContinuationTimer.HigherSeed p
        (trace init ω (s + lateTimerUpperHorizon n))}

/-- The original-law equation-(10) budget. -/
noncomputable def lateTimerUpperBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (n : ℝ) ^ 5)

/-- Every counter value is at most the nominal fresh value.  This is the
correct replacement for the false assertion that a Clock is fresh at the
homogeneous boundary. -/
theorem clockCounter_le_capacity
    {L K : ℕ} (a : AgentState L K) :
    a.counter.val ≤ 50 * (L + 1) := by
  have h := a.counter.isLt
  omega

private theorem timedPhase_of_lateTimedPhase
    {p : ℕ} (hp : LateTimedPhase p) :
    StrongContinuationTimer.TimedPhase p := by
  have h1 := hp.1
  have h2 := hp.2
  have hcases : p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    simp [StrongContinuationTimer.TimedPhase]

/-- The generalized homogeneous start is a genuine pair-log stopping time. -/
theorem homogeneousLatePhaseStart_past
    (init : InputCfg n) (p : ℕ) :
    PairLogPastTime (homogeneousLatePhaseStart init p) :=
  exitTime_pairLogPastTime init (allPhaseExactly p)

/-- Stopping-time form. -/
theorem homogeneousLatePhaseStart_isStoppingTime
    (init : InputCfg n) (p : ℕ) :
    IsStoppingTime
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (homogeneousLatePhaseStart init p) :=
  TraceDrain.exitTime_isStoppingTime init (allPhaseExactly p)

/-- A finite fibre is exactly the first hit of the homogeneous predicate. -/
theorem homogeneousLatePhaseStart_eq_iff
    (init : InputCfg n) (p s : ℕ) (ω : InputLog n) :
    homogeneousLatePhaseStart init p ω = (s : WithTop ℕ) ↔
      firstHit (allPhaseExactly p) (trace init ω) s := by
  simpa only [homogeneousLatePhaseStart] using
    (exitTime_eq_iff_firstHit init (allPhaseExactly p) ω s)

@[simp] theorem mem_homogeneousLatePhaseFibre_iff
    (init : InputCfg n) (p s : ℕ) (ω : InputLog n) :
    ω ∈ homogeneousLatePhaseFibre init p s ↔
      homogeneousLatePhaseStart init p ω = (s : WithTop ℕ) :=
  Iff.rfl

@[simp] theorem mem_lateTimerUpperFailure_iff
    (init : InputCfg n) (p : ℕ) (ω : InputLog n) :
    ω ∈ lateTimerUpperFailure init p ↔
      ∃ s : ℕ,
        homogeneousLatePhaseStart init p ω = (s : WithTop ℕ) ∧
          ¬ StrongContinuationTimer.HigherSeed p
            (trace init ω (s + lateTimerUpperHorizon n)) :=
  Iff.rfl

/-! ## A prefix-measurable least Clock label -/

/-- The least label carrying the Clock role in a labelling. -/
def firstClockLabel
    (init : InputCfg n) (f : Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) (i : Fin init.card) : Prop :=
  (f i).role = .clock ∧
    ∀ j : Fin init.card, (f j).role = .clock → i ≤ j

/-- The least-Clock event at physical time `s`. -/
def firstClockEvent
    (init : InputCfg n) (s : ℕ) (i : Fin init.card) :
    Set (InputLog n) :=
  {ω | firstClockLabel init (labelsAt init ω s) i}

/-- A homogeneous-start fibre split by its least Clock label. -/
def firstClockCell
    (init : InputCfg n) (p s : ℕ) (i : Fin init.card) :
    Set (InputLog n) :=
  homogeneousLatePhaseFibre init p s ∩ firstClockEvent init s i

private theorem firstClockLabel_unique
    (init : InputCfg n) (f : Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) {i j : Fin init.card}
    (hi : firstClockLabel init f i)
    (hj : firstClockLabel init f j) : i = j :=
  le_antisymm (hi.2 j hj.1) (hj.2 i hi.1)

private theorem exists_firstClockLabel
    (init : InputCfg n) (f : Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256)
    (hex : ∃ i : Fin init.card, (f i).role = .clock) :
    ∃ i : Fin init.card, firstClockLabel init f i := by
  classical
  let C : Finset (Fin init.card) :=
    Finset.univ.filter (fun i => (f i).role = .clock)
  have hC : C.Nonempty := by
    rcases hex with ⟨i, hi⟩
    exact ⟨i, by simp [C, hi]⟩
  let i := C.min' hC
  refine ⟨i, ?_, ?_⟩
  · have hi := Finset.min'_mem C hC
    simpa [C, i] using hi
  · intro j hj
    have hjC : j ∈ C := by simp [C, hj]
    dsimp [i]
    exact Finset.min'_le C j hjC

private theorem label_mem_trace
    (init : InputCfg n) (ω : InputLog n) (t : ℕ)
    (i : Fin init.card) :
    labelsAt init ω t i ∈ trace init ω t := by
  rw [← PairLog.labelsAt_config init ω t]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

private theorem exists_label_of_mem
    (init : InputCfg n) (ω : InputLog n) (t : ℕ)
    {a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256}
    (ha : a ∈ trace init ω t) :
    ∃ i : Fin init.card, labelsAt init ω t i = a := by
  rw [← PairLog.labelsAt_config init ω t] at ha
  rcases Multiset.mem_map.mp ha with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

/-- A Clock label exists on every finite homogeneous late-phase fibre. -/
theorem exists_firstClockLabel_of_homogeneousFibre
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p s : ℕ) (hp : LateTimedPhase p)
    {ω : InputLog n}
    (hfibre : ω ∈ homogeneousLatePhaseFibre init p s) :
    ∃ i : Fin init.card,
      firstClockLabel init (labelsAt init ω s) i := by
  have hfirst :=
    (homogeneousLatePhaseStart_eq_iff init p s ω).mp hfibre
  have hpure : UniformRecovery.PurePhase p (trace init ω s) := by
    simpa [allPhaseExactly, UniformRecovery.PurePhase] using hfirst.1
  have hreach :
      ReachableFrom
        (PhaseThreeModel.Numeric.hourIndex n) 256 init (trace init ω s) := by
    simpa only [TimeTheorem.trace_zero] using
      trace_reachable init ω (Nat.zero_le s)
  have hcard : (trace init ω s).card = n :=
    (Protocol.reachable_card_eq hreach).trans hinput.2.2
  have hpositive : 0 < (trace init ω s).card := by
    have hn : 40 ≤ n := (time_population_bounds hinput.1).2
    rw [hcard]
    omega
  obtain ⟨a, b, hab, ha, _hb⟩ :=
    UniformRecovery.reachable_positive_phase_has_clockPair
      init (trace init ω s) hinput.2.1 hreach hpositive p
      (by have := hp.1; omega) hpure
  have hamem : a ∈ trace init ω s :=
    Multiset.mem_of_le hab (by simp)
  obtain ⟨i, hi⟩ := exists_label_of_mem init ω s hamem
  have hiclock : (labelsAt init ω s i).role = .clock := by
    rw [hi]
    exact ha
  exact exists_firstClockLabel init (labelsAt init ω s) ⟨i, hiclock⟩

/-- Least-Clock selection is measurable from the time-`s` labels. -/
theorem firstClockEvent_measurable_at
    (init : InputCfg n) (s : ℕ) (i : Fin init.card) :
    MeasurableSet[
      pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      (firstClockEvent init s i) := by
  classical
  let B : Set (Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) := {f | firstClockLabel init f i}
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  simpa [firstClockEvent, B] using
    hB.preimage (AveragingHourStops.measurable_labelsAt_at init s)

/-- A homogeneous-start fibre is measurable at shifted time zero. -/
theorem homogeneousLatePhaseFibre_measurable_shifted
    (init : InputCfg n) (p s : ℕ) :
    MeasurableSet[
      AveragingRecordedExpectation.shiftedPairLog
        (PhaseThreeModel.Numeric.hourIndex n) 256 s 0]
      (homogeneousLatePhaseFibre init p s) := by
  simpa [homogeneousLatePhaseFibre,
    AveragingRecordedExpectation.shiftedPairLog] using
      ((homogeneousLatePhaseStart_past init p) s)

/-- A least-Clock cell is also measurable at shifted time zero. -/
theorem firstClockCell_measurable_shifted
    (init : InputCfg n) (p s : ℕ) (i : Fin init.card) :
    MeasurableSet[
      AveragingRecordedExpectation.shiftedPairLog
        (PhaseThreeModel.Numeric.hourIndex n) 256 s 0]
      (firstClockCell init p s i) := by
  apply (homogeneousLatePhaseFibre_measurable_shifted init p s).inter
  simpa [AveragingRecordedExpectation.shiftedPairLog] using
    (firstClockEvent_measurable_at init s i)

/-- Full measurable-space form, used to sum the disjoint cells. -/
theorem firstClockCell_measurable
    (init : InputCfg n) (p s : ℕ) (i : Fin init.card) :
    MeasurableSet (firstClockCell init p s i) := by
  exact
    ((pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256).le s) _
      (((homogeneousLatePhaseStart_past init p) s).inter
        (firstClockEvent_measurable_at init s i))

/-! ## Exact counter accounting for one persistent Clock label -/

/-- On a homogeneous timed-phase step, a selected Clock decrements exactly
once unless it advances.  If the output still has phase `p`, advancement is
impossible, so `counter_out + participation = counter_in`. -/
theorem clockLabelStep_exact
    {L K m p : ℕ}
    (hp : StrongContinuationTimer.TimedPhase p)
    (f : Fin m → AgentState L K) (d : Draw L K)
    (hall : ∀ k, (f k).phase.val = p)
    (i : Fin m) (hclock : (f i).role = .clock)
    (hout : (stepLabels f d i).phase.val = p) :
    (stepLabels f d i).role = .clock ∧
      (f i).counter.val =
        (stepLabels f d i).counter.val +
          LateTimerLabelStep.participates f d i := by
  classical
  unfold stepLabels at hout ⊢
  cases hsel : selectLabels f d with
  | none =>
      rw [hsel] at hout
      simp only at hout ⊢
      rw [LateTimerLabelStep.participates_of_none f d hsel i]
      exact ⟨hclock, by omega⟩
  | some pair =>
      obtain ⟨a, b⟩ := pair
      rw [hsel] at hout
      simp only at hout ⊢
      have hab := selectLabels_distinct f d a b hsel
      by_cases hia : i = a
      · subst a
        have hupd : updateLabels f i b i =
            ((NonuniformMajority L K).δ (f i) (f b)).1 := by
          unfold updateLabels
          rw [Function.update_of_ne hab, Function.update_self]
        rw [hupd] at hout ⊢
        change (Transition L K (f i) (f b)).1.phase.val = p at hout
        change (Transition L K (f i) (f b)).1.role = .clock ∧ _ at ⊢
        have htransition := UniformRecovery.timed_transition_left_clock
          (L := L) (K := K) p
          (StrongContinuationTimer.timed_mem hp)
          (f i) (f b) (hall i) (hall b) hclock
        rw [htransition] at hout ⊢
        have hnonzero : (f i).counter.val ≠ 0 := by
          intro hzero
          have hadv := StrongContinuationTimer.zero_clock_advances
            (L := L) (K := K) p hp (f i) (hall i) hzero
          omega
        have hpart :=
          LateTimerLabelStep.participates_of_left f d i b hsel
        refine ⟨?_, ?_⟩
        · simpa only [finishPhase10Entry_role] using
            (stdCounterSubroutine_clock_role
              (L := L) (K := K) (f i) hclock)
        · rw [hpart]
          change (f i).counter.val =
            (Transition L K (f i) (f b)).1.counter.val + 1
          rw [htransition, finishPhase10Entry_counter]
          unfold stdCounterSubroutine
          rw [dif_neg hnonzero]
          simp
          omega
      · by_cases hib : i = b
        · subst b
          have hupd : updateLabels f a i i =
              ((NonuniformMajority L K).δ (f a) (f i)).2 := by
            unfold updateLabels
            rw [Function.update_self]
          rw [hupd] at hout ⊢
          change (Transition L K (f a) (f i)).2.phase.val = p at hout
          change (Transition L K (f a) (f i)).2.role = .clock ∧ _ at ⊢
          have htransition := UniformRecovery.timed_transition_right_clock
            (L := L) (K := K) p
            (StrongContinuationTimer.timed_mem hp)
            (f a) (f i) (hall a) (hall i) hclock
          rw [htransition] at hout ⊢
          have hnonzero : (f i).counter.val ≠ 0 := by
            intro hzero
            have hadv := StrongContinuationTimer.zero_clock_advances
              (L := L) (K := K) p hp (f i) (hall i) hzero
            omega
          have hpart :=
            LateTimerLabelStep.participates_of_right f d a i hsel
          refine ⟨?_, ?_⟩
          · simpa only [finishPhase10Entry_role] using
              (stdCounterSubroutine_clock_role
                (L := L) (K := K) (f i) hclock)
          · rw [hpart]
            change (f i).counter.val =
              (Transition L K (f a) (f i)).2.counter.val + 1
            rw [htransition, finishPhase10Entry_counter]
            unfold stdCounterSubroutine
            rw [dif_neg hnonzero]
            simp
            omega
        · have hupd : updateLabels f a b i = f i := by
            unfold updateLabels
            rw [Function.update_of_ne hib, Function.update_of_ne hia]
          rw [hupd] at hout ⊢
          rw [LateTimerLabelStep.participates_of_other
            f d a b i hsel hia hib]
          exact ⟨hclock, by omega⟩

/-- Exact telescoping identity for a fixed Clock label through a homogeneous
window. -/
theorem fixedClock_counter_accounting
    (init : InputCfg n) (ω : InputLog n)
    (p s N : ℕ) (hp : StrongContinuationTimer.TimedPhase p)
    (i : Fin init.card)
    (hclock : (labelsAt init ω s i).role = .clock)
    (hwindow : ∀ u : ℕ, u ≤ N →
      allPhaseExactly p (trace init ω (s + u))) :
    (labelsAt init ω (s + N) i).role = .clock ∧
      (labelsAt init ω s i).counter.val =
        (labelsAt init ω (s + N) i).counter.val +
          LateTimerRouteProof.partCount init i s N ω := by
  revert hwindow
  induction N with
  | zero =>
      intro _
      simp [LateTimerRouteProof.partCount, hclock]
  | succ N ih =>
      intro hwindow
      have hprev := ih (fun u hu => hwindow u (by omega))
      have hall : ∀ k : Fin init.card,
          (labelsAt init ω (s + N) k).phase.val = p := by
        intro k
        exact hwindow N (by omega) _
          (label_mem_trace init ω (s + N) k)
      have hout :
          (stepLabels (labelsAt init ω (s + N))
            (ω (s + N + 1)) i).phase.val = p := by
        rw [← labelsAt_succ]
        exact hwindow (N + 1) le_rfl _
          (label_mem_trace init ω (s + (N + 1)) i)
      have hstep := clockLabelStep_exact hp
        (labelsAt init ω (s + N)) (ω (s + N + 1))
        hall i hprev.1 hout
      rw [← labelsAt_succ] at hstep
      have hpart :
          LateTimerRouteProof.partCount init i s (N + 1) ω =
            LateTimerRouteProof.partCount init i s N ω +
              LateTimerLabelStep.participates
                (labelsAt init ω (s + N)) (ω (s + N + 1)) i := by
        unfold LateTimerRouteProof.partCount
        rw [Finset.sum_range_succ]
      refine ⟨?_, ?_⟩
      · simpa [Nat.add_assoc] using hstep.1
      · rw [hpart]
        have hstepCounter := hstep.2
        have hprevCounter := hprev.2
        simp only [Nat.add_assoc] at hstepCounter ⊢
        omega

/-- The natural participation sum equals the real Bernoulli count. -/
theorem partCount_cast_eq_bernoulliCount
    (init : InputCfg n) (i : Fin init.card)
    (s N : ℕ) (ω : InputLog n) :
    (LateTimerRouteProof.partCount init i s N ω : ℝ) =
      PhaseThreeScalar.bernoulliCount
        (labelParticipation init i s) N ω := by
  unfold LateTimerRouteProof.partCount
    PhaseThreeScalar.bernoulliCount
  push_cast
  apply Finset.sum_congr rfl
  intro u hu
  exact (LateTimerRouteProof.labelParticipation_eq init i s u ω).symm

/-- Deterministic paper implication: no higher phase by the endpoint forces
the chosen start-Clock's Bernoulli participation count to be at most `50H`.
No fresh-counter premise occurs. -/
theorem bernoulliCount_le_capacity_of_noHigher
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p s N : ℕ) (hp : LateTimedPhase p)
    (i : Fin init.card) {ω : InputLog n}
    (hfibre : ω ∈ homogeneousLatePhaseFibre init p s)
    (hclock : (labelsAt init ω s i).role = .clock)
    (hno : ¬ StrongContinuationTimer.HigherSeed p
      (trace init ω (s + N))) :
    PhaseThreeScalar.bernoulliCount
        (labelParticipation init i s) N ω ≤
      ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) := by
  have hn : 2 ≤ n := by
    have hlarge := (time_population_bounds hinput.1).2
    omega
  have hfirst :=
    (homogeneousLatePhaseStart_eq_iff init p s ω).mp hfibre
  have hpure : UniformRecovery.PurePhase p (trace init ω s) := by
    simpa [allPhaseExactly, UniformRecovery.PurePhase] using hfirst.1
  have hreach :
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
          init (trace init ω s) := by
    simpa only [TimeTheorem.trace_zero] using
      trace_reachable init ω (Nat.zero_le s)
  have hcard : (trace init ω s).card = n :=
    (Protocol.reachable_card_eq hreach).trans hinput.2.2
  have hentry : StrongContinuationTimer.TimedWindow p n
      (trace init ω s) := ⟨hcard, hpure⟩
  have hpTimed := timedPhase_of_lateTimedPhase hp
  have hwork := StrongContinuationTimer.no_higher_window
    init hinput.2.1 p hpTimed ω n hn s N hentry hno
  have hwindow : ∀ u : ℕ, u ≤ N →
      allPhaseExactly p (trace init ω (s + u)) := by
    intro u hu
    have hw := hwork.1 (s + u) (by omega) (by omega)
    simpa [allPhaseExactly, UniformRecovery.PurePhase] using hw.2
  have haccount := fixedClock_counter_accounting
    init ω p s N hpTimed i hclock hwindow
  have hcap :
      (labelsAt init ω s i).counter.val ≤
        50 * PhaseThreeModel.Numeric.clockHours n := by
    have hraw := clockCounter_le_capacity (labelsAt init ω s i)
    simpa [PhaseThreeModel.Numeric.clockHours] using hraw
  have hnat :
      LateTimerRouteProof.partCount init i s N ω ≤
        50 * PhaseThreeModel.Numeric.clockHours n := by
    omega
  rw [← partCount_cast_eq_bernoulliCount init i s N ω]
  exact_mod_cast hnat

/-! ## Prefix tail on one chosen-label cell -/

/-- The scalar lower-tail event for a fixed selected label. -/
def lowParticipationEvent
    (init : InputCfg n) (i : Fin init.card) (s : ℕ) :
    Set (InputLog n) :=
  {ω |
    PhaseThreeScalar.bernoulliCount
        (labelParticipation init i s) (lateTimerUpperHorizon n) ω ≤
      ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)}

private theorem measure_le_of_real_le_mul_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {A E : Set Ω} {c : ℝ} (hc : 0 ≤ c)
    (h : μ.real A ≤ c * μ.real E) :
    μ A ≤ ENNReal.ofReal c * μ E := by
  have hright : ENNReal.ofReal c * μ E ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) (measure_ne_top μ E)
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ A) hright).mp
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using h

/-- One least-Clock cell has the requested conditional-on-the-prefix bound,
still under the original law. -/
theorem firstClockCell_low_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p s : ℕ) (i : Fin init.card) :
    law init
        (firstClockCell init p s i ∩
          lowParticipationEvent init i s) ≤
      lateTimerUpperBudget n * law init (firstClockCell init p s i) := by
  have hc : 2 ≤ init.card := by
    rw [hinput.2.2]
    have hlarge := (time_population_bounds hinput.1).2
    omega
  have hstrong : ∀ t,
      StronglyMeasurable[
        AveragingRecordedExpectation.shiftedPairLog
          (PhaseThreeModel.Numeric.hourIndex n) 256 s (t + 1)]
        (labelParticipation init i s t) :=
    fun t => labelParticipation_stronglyMeasurable init i s t
  have hzeroOne : ∀ t, ∀ᵐ ω ∂law init,
      labelParticipation init i s t ω = 0 ∨
        labelParticipation init i s t ω = 1 :=
    fun t => ae_of_all _ fun ω =>
      labelParticipation_zero_or_one init i s t ω
  have hprob : ∀ t,
      (law init)[labelParticipation init i s t |
        AveragingRecordedExpectation.shiftedPairLog
          (PhaseThreeModel.Numeric.hourIndex n) 256 s t]
        =ᵐ[law init] (fun _ => 2 / (n : ℝ)) := by
    intro t
    simpa [hinput.2.2] using
      (labelParticipation_conditional_probability init hc i s t)
  have hreal :=
    LateTimerUpperPrefixScalar.late_timer_upper_prefix_scalar
      (μ := law init)
      (ℱ := AveragingRecordedExpectation.shiftedPairLog
        (PhaseThreeModel.Numeric.hourIndex n) 256 s)
      hinput.1
      (labelParticipation init i s)
      hstrong hzeroOne hprob
      (firstClockCell init p s i)
      (firstClockCell_measurable_shifted init p s i)
  have hmeasure := measure_le_of_real_le_mul_upper
    (law init) (by positivity : 0 ≤ 1 / (n : ℝ) ^ 5) hreal
  simpa [lateTimerUpperBudget, lowParticipationEvent,
    lateTimerUpperHorizon] using hmeasure

/-! ## One homogeneous-start fibre and the original stopping-time splice -/

/-- On a fixed genuine homogeneous-start fibre, choose the least Clock from
that fibre's past.  The chosen-label cells are disjoint and cover the fibre,
so their probability factors sum back to the fibre probability. -/
theorem lateTimerUpperFailure_fibre_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p s : ℕ) (hp : LateTimedPhase p) :
    law init
        (lateTimerUpperFailure init p ∩
          homogeneousLatePhaseFibre init p s) ≤
      lateTimerUpperBudget n *
        law init (homogeneousLatePhaseFibre init p s) := by
  let Cell : Fin init.card → Set (InputLog n) :=
    fun i => firstClockCell init p s i
  let Low : Fin init.card → Set (InputLog n) :=
    fun i => lowParticipationEvent init i s
  have hcover :
      lateTimerUpperFailure init p ∩
          homogeneousLatePhaseFibre init p s ⊆
        ⋃ i : Fin init.card, Cell i ∩ Low i := by
    rintro ω ⟨hbad, hfibre⟩
    rcases hbad with ⟨r, hr, hno⟩
    have hrs : r = s :=
      WithTop.coe_injective (hr.symm.trans hfibre)
    subst r
    obtain ⟨i, hfirst⟩ :=
      exists_firstClockLabel_of_homogeneousFibre
        init hinput p s hp hfibre
    have hlow := bernoulliCount_le_capacity_of_noHigher
      init hinput p s (lateTimerUpperHorizon n) hp i hfibre hfirst.1 hno
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    exact ⟨⟨hfibre, hfirst⟩, hlow⟩
  have hdisj : Pairwise (fun i j => Disjoint (Cell i) (Cell j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    rcases hi with ⟨_, hi⟩
    rcases hj with ⟨_, hj⟩
    exact hij (firstClockLabel_unique init (labelsAt init ω s) hi hj)
  have hcellMeas : ∀ i, MeasurableSet (Cell i) := by
    intro i
    exact firstClockCell_measurable init p s i
  have hunion :
      (⋃ i : Fin init.card, Cell i) =
        homogeneousLatePhaseFibre init p s := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨i, hi⟩
      exact hi.1
    · intro hfibre
      obtain ⟨i, hi⟩ :=
        exists_firstClockLabel_of_homogeneousFibre
          init hinput p s hp hfibre
      exact Set.mem_iUnion.mpr ⟨i, hfibre, hi⟩
  have hlocal : ∀ i,
      law init (Cell i ∩ Low i) ≤
        lateTimerUpperBudget n * law init (Cell i) := by
    intro i
    exact firstClockCell_low_tail init hinput p s i
  calc
    law init
        (lateTimerUpperFailure init p ∩
          homogeneousLatePhaseFibre init p s) ≤
      law init (⋃ i : Fin init.card, Cell i ∩ Low i) :=
        measure_mono hcover
    _ ≤ ∑' i : Fin init.card, law init (Cell i ∩ Low i) :=
      measure_iUnion_le _
    _ ≤ ∑' i : Fin init.card,
        lateTimerUpperBudget n * law init (Cell i) :=
      ENNReal.tsum_le_tsum hlocal
    _ = lateTimerUpperBudget n *
        law init (⋃ i : Fin init.card, Cell i) := by
      rw [ENNReal.tsum_mul_left,
        ← measure_iUnion hdisj hcellMeas]
    _ = lateTimerUpperBudget n *
        law init (homogeneousLatePhaseFibre init p s) := by
      rw [hunion]

/-- Lemma 3, equation (10), under the original pair-log law.  `GoodInput`
already contains `timePopulationThreshold ≤ n`. -/
theorem law_lateTimerUpperFailure_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p : ℕ) (hp : LateTimedPhase p) :
    law init (lateTimerUpperFailure init p) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 5) := by
  have htail := PhaseThreeClockProducer.splice_of_local
    (law init)
    (homogeneousLatePhaseStart init p)
    (lateTimerUpperFailure init p)
    (lateTimerUpperBudget n)
    (fun s =>
      ((pairLogFiltration
        (PhaseThreeModel.Numeric.hourIndex n) 256).le s) _
        ((homogeneousLatePhaseStart_past init p) s))
    (by
      intro ω hω
      rcases hω with ⟨s, hs, _⟩
      rw [hs]
      exact WithTop.coe_ne_top)
    (fun s => by
      simpa [homogeneousLatePhaseFibre] using
        lateTimerUpperFailure_fibre_tail init hinput p s hp)
  simpa [lateTimerUpperBudget] using htail

/-- Downstream consumer.  Outside the upper-timer failure, a supplied finite
homogeneous start has a finite genuine first Phase-`p+1` seed no later than
`start + ceil (54 n log n)`. -/
theorem nextPhaseSeed_finite_and_le
    (init : InputCfg n) (p s : ℕ)
    {ω : InputLog n}
    (hstart : homogeneousLatePhaseStart init p ω = (s : WithTop ℕ))
    (hgood : ω ∉ lateTimerUpperFailure init p) :
    phaseSeedTime init (p + 1) ω ≠ ⊤ ∧
      phaseSeedTime init (p + 1) ω ≤
        ((s + lateTimerUpperHorizon n : ℕ) : WithTop ℕ) := by
  have hhit : StrongContinuationTimer.HigherSeed p
      (trace init ω (s + lateTimerUpperHorizon n)) := by
    by_contra hno
    apply hgood
    exact ⟨s, hstart, hno⟩
  have hsome : someGE (n := n) (p + 1)
      (trace init ω (s + lateTimerUpperHorizon n)) := by
    rcases hhit with ⟨a, ha, hp⟩
    exact ⟨a, ha, by omega⟩
  have hle : phaseSeedTime init (p + 1) ω ≤
      ((s + lateTimerUpperHorizon n : ℕ) : WithTop ℕ) := by
    simpa only [phaseSeedTime] using
      (TraceDrain.exitTime_le_iff init (someGE (n := n) (p + 1)) ω
        (s + lateTimerUpperHorizon n)).2
        ⟨s + lateTimerUpperHorizon n, le_rfl, hsome⟩
  exact ⟨ne_top_of_le_ne_top WithTop.coe_ne_top hle, hle⟩

/-!
THEOREM LIST
* `allPhaseExactly`
* `homogeneousLatePhaseStart`
* `lateTimerUpperHorizon`
* `lateTimerUpperFailure`
* `clockCounter_le_capacity`
* `homogeneousLatePhaseStart_past`
* `homogeneousLatePhaseStart_isStoppingTime`
* `homogeneousLatePhaseStart_eq_iff`
* `exists_firstClockLabel_of_homogeneousFibre`
* `clockLabelStep_exact`
* `fixedClock_counter_accounting`
* `partCount_cast_eq_bernoulliCount`
* `bernoulliCount_le_capacity_of_noHigher`
* `firstClockCell_low_tail`
* `lateTimerUpperFailure_fibre_tail`
* `law_lateTimerUpperFailure_tail`
* `nextPhaseSeed_finite_and_le`

CLOSES
* Item 1: generalized genuine homogeneous Phase-`p` start and exact equation-(10)
  failure event.
* Item 2: original-law `n^(-5)` theorem for every `LateTimedPhase p`, with
  prefix-measurable Clock selection, exact counter accounting, the landed
  scalar tail, and stopping-time fibre splicing.
* Item 3: finite first-`p+1` seed and deadline consumer.

CARRIED PREMISES AND PRODUCERS
* `timePopulationThreshold ≤ n`, `validInitial init`, and `init.card = n` are
  the three fields of `ThresholdEpidemic.GoodInput` on main.
* Clock existence is produced by
  `UniformRecovery.reachable_positive_phase_has_clockPair` on main.
* Exact selected-Clock dispatch and zero-counter advance are produced by
  `UniformRecovery.timed_transition_left_clock`,
  `UniformRecovery.timed_transition_right_clock`, and
  `StrongContinuationTimer.zero_clock_advances` on main.
* The no-higher homogeneous window is
  `StrongContinuationTimer.no_higher_window` on main.
* The adapted Bernoulli law is the `labelParticipation_*` family in
  `LateTimerProtectionOriginalLaw` on main.
* Scalar equation (10) is `ScalarTails.late_timer_upper_scalar`; the first file
  above proves only the prefix-weighted lift needed for the splice.

UNFINISHED
* No mathematical premise remains open.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateTimerUpperOriginalLaw

end
