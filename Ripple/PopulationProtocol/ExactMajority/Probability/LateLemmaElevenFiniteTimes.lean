-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaElevenFiniteTimes.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaElevenBeforeSeven
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerUpperOriginalLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerRouteProof
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePhaseSixDrainPaperNumerics

/-!
# Lemma 11: finite Phase-7 and Phase-8 times

Corrections recorded by this file:

* `smallGapPhaseSixDrainFailure` does not imply eventual Phase 7.  The finite
  Phase-7 producer also excludes `lateTimerUpperFailure init 6`.
* Threshold-7 spreading gives only phases `>= 7`.  To obtain an exact
  homogeneous Phase-7 configuration before Phase 8, the spread failure is
  unioned with guarded lower-timer failure at `p = 7`.

The upper timer uses `phaseSeedTime`, whose hit predicate is `someGE`.  The
private no-overshoot adapter below proves the stronger exact
`firstPhaseSeed (p+1)` statement needed by the path receipt.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenFiniteTimes

open TimeTheorem PairLog StageEventSpec
open LateF6OriginalLaw
open LateStrengthening
open LateMixedFuel LateMixedFiveSixWindow
open LateSamplingCompletion LateSamplingStrongSeedReceipt
open LateSamplingStrongReceiptProducer
open LatePhaseSixDrainSelectedLevel
open LateBiasedResourceCreditPath
open LateLemmaElevenEntry
open LateTimerProtectionOriginalLaw
open LateTimerProtectionGuarded
open LateTimerUpperOriginalLaw
open LateTimerRouteProof
open LatePhaseSixDrainPaperNumerics
open AdvanceNoOvershoot
open LateMixedFiveSixReachableWf

variable {L K n m : ℕ}

private theorem label_mem_trace
    (init : InputCfg n) (omega : InputLog n) (t : ℕ)
    (i : Fin init.card) :
    labelsAt init omega t i ∈ trace init omega t := by
  rw [← PairLog.labelsAt_config init omega t]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

private theorem exists_label_of_mem
    (init : InputCfg n) (omega : InputLog n) (t : ℕ)
    {a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256}
    (ha : a ∈ trace init omega t) :
    ∃ i : Fin init.card, labelsAt init omega t i = a := by
  rw [← PairLog.labelsAt_config init omega t] at ha
  rcases Multiset.mem_map.mp ha with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

/-- On a well-formed pure late-phase source, one draw raises every label by at
most one phase. -/
private theorem stepLabels_phase_le_succ_of_pure
    (p : ℕ) (hp5 : 5 ≤ p) (hp8 : p ≤ 8)
    (f : Fin m → AgentState L K)
    (hwf : ∀ i, WfAgent (L := L) (K := K) (f i))
    (hpure : ∀ i, (f i).phase.val = p)
    (d : Draw L K) (k : Fin m) :
    (stepLabels f d k).phase.val ≤ p + 1 := by
  classical
  unfold stepLabels
  cases hsel : selectLabels f d with
  | none =>
      simp only
      have hk := hpure k
      omega
  | some pair =>
      obtain ⟨i, j⟩ := pair
      simp only
      have hij := selectLabels_distinct f d i j hsel
      by_cases hki : k = i
      · subst k
        have hupd : updateLabels f i j i =
            ((NonuniformMajority L K).δ (f i) (f j)).1 := by
          unfold updateLabels
          rw [Function.update_of_ne hij, Function.update_self]
        rw [hupd]
        change (Transition L K (f i) (f j)).1.phase.val ≤ p + 1
        have hi := hpure i
        have hj := hpure j
        have hep := phaseEpidemicUpdate_left_phase_eq_max_of_wf
          (f i) (f j) (hwf i) (hwf j) (by omega) (by omega)
        have hle := Transition_left_phase_le_ep_succ_of_wf
          (f i) (f j) (hwf i) (hwf j) (by omega) (by omega)
        have hi := hpure i
        have hj := hpure j
        omega
      · by_cases hkj : k = j
        · subst k
          have hupd : updateLabels f i j j =
              ((NonuniformMajority L K).δ (f i) (f j)).2 := by
            unfold updateLabels
            rw [Function.update_self]
          rw [hupd]
          change (Transition L K (f i) (f j)).2.phase.val ≤ p + 1
          have hi := hpure i
          have hj := hpure j
          have hep := phaseEpidemicUpdate_right_phase_eq_max_of_wf
            (f i) (f j) (hwf i) (hwf j) (by omega) (by omega)
          have hle := Transition_right_phase_le_ep_succ_of_wf
            (f i) (f j) (hwf i) (hwf j) (by omega) (by omega)
          have hi := hpure i
          have hj := hpure j
          omega
        · have hupd : updateLabels f i j k = f k := by
            unfold updateLabels
            rw [Function.update_of_ne hkj, Function.update_of_ne hki]
          rw [hupd]
          have hk := hpure k
          omega

/-- A finite `someGE (p+1)` first hit following a pure Phase-`p` state is the
exact first Phase-`p+1` seed. -/
private theorem firstPhaseSeed_succ_of_pure_before
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n} (p s r : ℕ)
    (hp5 : 5 ≤ p) (hp8 : p ≤ 8)
    (hpure : allPhaseExactly p (trace init omega s))
    (hsr : s < r)
    (hr : phaseSeedTime init (p + 1) omega = (r : WithTop ℕ)) :
    firstPhaseSeed init (p + 1) r omega := by
  have hfirst := (phaseSeedTime_eq_iff init (p + 1) omega r).mp hr
  obtain ⟨u, hu⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
  subst r
  have hsu : s ≤ u := by omega
  have hlower :
      ∀ a ∈ trace init omega u, p ≤ a.phase.val :=
    PhaseOneDrainStopping.phase_lower_reachable
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      p (trace init omega s) (trace init omega u)
      (trace_reachable init omega hsu)
      (fun a ha => (hpure a ha).symm.le)
  have hupper :
      ∀ i : Fin init.card,
        (labelsAt init omega u i).phase.val ≤ p := by
    intro i
    by_contra hbad
    apply hfirst.2 u (Nat.lt_succ_self u)
    exact ⟨labelsAt init omega u i,
      label_mem_trace init omega u i, by omega⟩
  have hpureLabels :
      ∀ i : Fin init.card,
        (labelsAt init omega u i).phase.val = p := by
    intro i
    have hlo := hlower _ (label_mem_trace init omega u i)
    have hhi := hupper i
    omega
  have hwf :
      ∀ i : Fin init.card,
        WfAgent (labelsAt init omega u i) := by
    intro i
    have hreach := trace_reachable init omega (Nat.zero_le u)
    rw [trace_zero] at hreach
    exact wfAgent_of_reachable_phase_range
      hinput.2.1 hreach (label_mem_trace init omega u i)
      (by have := hlower _ (label_mem_trace init omega u i); omega)
      (by have := hupper i; omega)
  obtain ⟨a, ha, haph⟩ := hfirst.1
  obtain ⟨i, hi⟩ := exists_label_of_mem init omega (u + 1) ha
  have hlabels : labelsAt init omega (u + 1) =
      stepLabels (labelsAt init omega u) (omega (u + 1)) :=
    labelsAt_succ init omega u
  have houtLower :
      p + 1 ≤
        (stepLabels (labelsAt init omega u) (omega (u + 1)) i).phase.val := by
    rw [← hlabels, hi]
    exact haph
  have houtUpper := stepLabels_phase_le_succ_of_pure
    p hp5 hp8 (labelsAt init omega u) hwf hpureLabels
    (omega (u + 1)) i
  have houtEq :
      (stepLabels (labelsAt init omega u) (omega (u + 1)) i).phase.val =
        p + 1 := by omega
  have haeq : a.phase.val = p + 1 := by
    have hiEq : (labelsAt init omega (u + 1) i).phase.val = p + 1 := by
      rw [hlabels]
      exact houtEq
    simpa [hi] using hiEq
  refine ⟨⟨a, ha, haeq⟩, ?_⟩
  intro t ht b hb
  by_contra hbad
  exact hfirst.2 t ht ⟨b, hb, by omega⟩

private theorem phaseSeedTime_eq_of_firstPhaseSeed
    (init : InputCfg n) (omega : InputLog n) (p seed : ℕ)
    (hseed : firstPhaseSeed init p seed omega) :
    phaseSeedTime init p omega = (seed : WithTop ℕ) := by
  apply (phaseSeedTime_eq_iff init p omega seed).2
  constructor
  · rcases hseed.1 with ⟨a, ha, hp⟩
    exact ⟨a, ha, hp.ge⟩
  · intro u hu hsome
    rcases hsome with ⟨a, ha, hge⟩
    exact (Nat.not_le_of_gt (hseed.2 u hu a ha)) hge

/-! ## Named failure sets -/

/-- The missing event in the original formulation of item 1. -/
def phaseSixUpperTimerFailure (init : InputCfg n) : Set (InputLog n) :=
  lateTimerUpperFailure init 6

/-- Threshold 7 has not spread within three logarithmic units. -/
def phaseSevenSpreadFailure (init : InputCfg n) : Set (InputLog n) :=
  {omega | ∃ seven : ℕ,
    firstPhaseSeed init 7 seven omega ∧
      ¬ ∀ a ∈ trace init omega (seven + logWindow n 3),
        7 ≤ a.phase.val}

/-- Corrected failure of producing an exact homogeneous Phase-7 state: either
threshold 7 did not spread, or Phase 8 arrived before the protected spread
window ended. -/
def phaseSevenHomogeneousFailure (init : InputCfg n) : Set (InputLog n) :=
  phaseSevenSpreadFailure init ∪
    timerProtectionFailureGuarded init 7

/-- The upper-timer failure after the first exact homogeneous Phase-7 state. -/
def phaseSevenUpperTimerFailure (init : InputCfg n) : Set (InputLog n) :=
  lateTimerUpperFailure init 7

/-- Total Phase-7 horizon measured from the first Phase-7 seed. -/
def phaseSevenHorizon (n : ℕ) : ℕ :=
  logWindow n 3 + lateTimerUpperHorizon n

/-! ## Measurability -/

private theorem pastTime_fibre_measurable
    (sigma : InputLog n → WithTop ℕ)
    (hsigma : PhaseOneDrain.PairLogPastTime sigma) (s : ℕ) :
    MeasurableSet {omega | sigma omega = (s : WithTop ℕ)} :=
  ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le s) _
    (hsigma s)

private theorem pastTime_lt_coe_measurable
    (sigma : InputLog n → WithTop ℕ)
    (hsigma : PhaseOneDrain.PairLogPastTime sigma) (s : ℕ) :
    MeasurableSet {omega | sigma omega < (s : WithTop ℕ)} := by
  rw [show {omega | sigma omega < (s : WithTop ℕ)} =
      ⋃ r : Fin s, {omega | sigma omega = (r.val : WithTop ℕ)} by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hlt
      obtain ⟨r, hr⟩ :=
        WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
      have hrs : r < s := by
        apply WithTop.coe_lt_coe.mp
        rw [hr]
        exact hlt
      exact ⟨⟨r, hrs⟩, hr.symm⟩
    · rintro ⟨r, hr⟩
      rw [hr]
      exact WithTop.coe_lt_coe.mpr r.isLt]
  exact MeasurableSet.iUnion fun r =>
    pastTime_fibre_measurable sigma hsigma r.val

private theorem pastTime_le_coe_measurable
    (sigma : InputLog n → WithTop ℕ)
    (hsigma : PhaseOneDrain.PairLogPastTime sigma) (s : ℕ) :
    MeasurableSet {omega | sigma omega ≤ (s : WithTop ℕ)} := by
  rw [show {omega | sigma omega ≤ (s : WithTop ℕ)} =
      ⋃ r : Fin (s + 1), {omega | sigma omega = (r.val : WithTop ℕ)} by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hle
      have hfinite : sigma omega ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top hle
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfinite
      have hrs : r < s + 1 := by
        apply Nat.lt_succ_iff.mpr
        apply WithTop.coe_le_coe.mp
        rw [hr]
        exact hle
      exact ⟨⟨r, hrs⟩, hr.symm⟩
    · rintro ⟨r, hr⟩
      rw [hr]
      exact WithTop.coe_le_coe.mpr (Nat.lt_succ_iff.mp r.isLt)]
  exact MeasurableSet.iUnion fun r =>
    pastTime_fibre_measurable sigma hsigma r.val

theorem measurableSet_lateTimerUpperFailure
    (init : InputCfg n) (p : ℕ) :
    MeasurableSet (lateTimerUpperFailure init p) := by
  rw [show lateTimerUpperFailure init p =
      ⋃ s : ℕ,
        {omega | homogeneousLatePhaseStart init p omega =
          (s : WithTop ℕ)} ∩
        {omega | ¬ StrongContinuationTimer.HigherSeed p
          (trace init omega (s + lateTimerUpperHorizon n))} by
    ext omega
    simp [lateTimerUpperFailure]]
  apply MeasurableSet.iUnion
  intro s
  apply (pastTime_fibre_measurable
    (homogeneousLatePhaseStart init p)
    (homogeneousLatePhaseStart_past init p) s).inter
  exact (Set.to_countable
    {c : InputCfg n | ¬ StrongContinuationTimer.HigherSeed p c}).measurableSet.preimage
      ((measurable_trace_at init (s + lateTimerUpperHorizon n)).mono
        ((pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256).le
            (s + lateTimerUpperHorizon n)) le_rfl)

theorem measurableSet_phaseSevenSpreadFailure
    (init : InputCfg n) :
    MeasurableSet (phaseSevenSpreadFailure init) := by
  rw [show phaseSevenSpreadFailure init =
      ⋃ seven : ℕ,
        {omega | firstPhaseSeed init 7 seven omega} ∩
        {omega | ¬ ∀ a ∈ trace init omega
          (seven + logWindow n 3), 7 ≤ a.phase.val} by
    ext omega
    simp [phaseSevenSpreadFailure]]
  apply MeasurableSet.iUnion
  intro seven
  apply (((pairLogFiltration
    (PhaseThreeModel.Numeric.hourIndex n) 256).le seven) _
      (firstPhaseSeed_measurableSet init 7 seven)).inter
  exact (Set.to_countable
    {c : InputCfg n | ¬ ∀ a ∈ c, 7 ≤ a.phase.val}).measurableSet.preimage
      ((measurable_trace_at init (seven + logWindow n 3)).mono
        ((pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256).le
            (seven + logWindow n 3)) le_rfl)

theorem measurableSet_timerProtectionFailureGuarded
    (init : InputCfg n) (p : ℕ) :
    MeasurableSet (timerProtectionFailureGuarded init p) := by
  rw [show timerProtectionFailureGuarded init p =
      ⋃ s : ℕ,
        {omega | phaseSeedTime init p omega = (s : WithTop ℕ)} ∩
          ({omega | allThreeStart init omega < (s : WithTop ℕ)} ∩
            {omega | phaseSeedTime init (p + 1) omega ≤
              ((s + LateTimerPrefixScalar.protectionHorizon n : ℕ) : WithTop ℕ)}) by
    ext omega
    simp [timerProtectionFailureGuarded]]
  apply MeasurableSet.iUnion
  intro s
  exact (pastTime_fibre_measurable
      (phaseSeedTime init p) (phaseSeedTime_past init p) s).inter
    ((pastTime_lt_coe_measurable
      (allThreeStart init) (allThreeStart_past init) s).inter
      (pastTime_le_coe_measurable
        (phaseSeedTime init (p + 1))
        (phaseSeedTime_past init (p + 1))
        (s + LateTimerPrefixScalar.protectionHorizon n)))

theorem measurableSet_phaseSixUpperTimerFailure
    (init : InputCfg n) :
    MeasurableSet (phaseSixUpperTimerFailure init) := by
  simpa only [phaseSixUpperTimerFailure] using
    measurableSet_lateTimerUpperFailure init 6

theorem measurableSet_phaseSevenHomogeneousFailure
    (init : InputCfg n) :
    MeasurableSet (phaseSevenHomogeneousFailure init) :=
  (measurableSet_phaseSevenSpreadFailure init).union
    (measurableSet_timerProtectionFailureGuarded init 7)

theorem measurableSet_phaseSevenUpperTimerFailure
    (init : InputCfg n) :
    MeasurableSet (phaseSevenUpperTimerFailure init) := by
  simpa only [phaseSevenUpperTimerFailure] using
    measurableSet_lateTimerUpperFailure init 7

/-! ## Unconditional law bounds -/

theorem law_phaseSixUpperTimerFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseSixUpperTimerFailure init) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 5) := by
  simpa only [phaseSixUpperTimerFailure] using
    law_lateTimerUpperFailure_tail init hinput 6 (by
      unfold LateTimedPhase
      omega)

theorem law_phaseSevenSpreadFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseSevenSpreadFailure init) ≤
      ENNReal.ofReal
        (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) := by
  simpa [phaseSevenSpreadFailure] using
    (ThresholdEpidemic.threshold_spread_sharp_tail
      init hinput (⟨7, by norm_num⟩ : Fin 11) (by norm_num) 3 (by norm_num))

theorem law_phaseSevenHomogeneousFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseSevenHomogeneousFailure init) ≤
      ENNReal.ofReal
          (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) +
        ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) := by
  calc
    law init (phaseSevenHomogeneousFailure init) ≤
        law init (phaseSevenSpreadFailure init) +
          law init (timerProtectionFailureGuarded init 7) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal
          (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) +
        ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) :=
      add_le_add (law_phaseSevenSpreadFailure init hinput)
        (law_timerProtectionFailureGuarded_tail_of_goodInput
          init hinput 7 (by unfold LateTimedPhase; omega))

theorem law_phaseSevenUpperTimerFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseSevenUpperTimerFailure init) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 5) := by
  simpa only [phaseSevenUpperTimerFailure] using
    law_lateTimerUpperFailure_tail init hinput 7 (by
      unfold LateTimedPhase
      omega)

/-! ## Item 1: finite Phase 7 -/

structure SevenFiniteReceipt
    (init : InputCfg n) (omega : InputLog n)
    (completed homogeneous seven : ℕ) : Prop where
  mixed : MixedFiveSixPrefix init omega completed homogeneous
  seven_time : firstPhaseSevenStart init omega = (seven : WithTop ℕ)
  seven_seed : firstPhaseSeed init 7 seven omega
  completed_le : completed ≤ seven
  all_three_lt : allThreeStart init omega < (seven : WithTop ℕ)

/-- Corrected item 1.  The `completed` witness is the same completion used to
construct `LemmaElevenEntry`; no second completion witness is introduced. -/
theorem exists_lemmaElevenEntry_and_finiteSeven
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hselected : omega ∉ smallGapPhaseSixDrainFailure init)
    (hupper : omega ∉ phaseSixUpperTimerFailure init) :
    ∃ seed allThree four : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign,
      ∃ five completed homogeneous seven M R : ℕ,
        sigma = oppositeSign tau ∧
          M = timeMainCount (trace init omega seed) ∧
          R = StageEventSpec.reserveCount (trace init omega seed) ∧
          LemmaElevenEntry (M := M) (R := R) ell hell sigma tau
            (trace init omega completed) ∧
          SevenFiniteReceipt init omega completed homogeneous seven := by
  have hnotSnapshot :
      omega ∉ smallRowTwoSnapshotProductionFailure init := by
    intro hbad
    exact hselected (Or.inl hbad)
  have hnotMixed : omega ∉ mixedFailure init := by
    intro hbad
    exact hselected (Or.inr (Or.inl hbad))
  obtain ⟨seed, allThree, four, ell, hell, tau, five, completed,
      _hhistory, hseed, hstrong, _hledger⟩ :=
    exists_completedFuelLedger_of_smallHistory
      hinput hsmall hnotSnapshot
  have hcondition : MixedWindowCondition init omega completed := by
    by_contra hbad
    exact hnotMixed
      ⟨completed, hstrong.completion.completed_at, hbad⟩
  obtain ⟨homogeneous, hmixed⟩ :=
    mixedFiveSixPrefix_of_condition hcondition
  have hhomogeneousUpper :
      homogeneousLatePhaseStart init 6 omega =
        (homogeneous : WithTop ℕ) := by
    simpa only [homogeneousLatePhaseStart, allPhaseExactly,
      homogeneousSixStart, allPhaseSix] using hmixed.six_start
  have hnext := nextPhaseSeed_finite_and_le
    init 6 homogeneous hhomogeneousUpper hupper
  obtain ⟨seven, hsevenRev⟩ :=
    WithTop.ne_top_iff_exists.mp hnext.1
  have hphaseSeven :
      phaseSeedTime init 7 omega = (seven : WithTop ℕ) :=
    hsevenRev.symm
  have hsevenTime :
      firstPhaseSevenStart init omega = (seven : WithTop ℕ) := by
    simpa only [phaseSeedTime, firstPhaseSevenStart] using hphaseSeven
  have hrace := hcondition.2
  rw [mem_noTimerExitBeforeHomogeneousSix_iff,
    hmixed.six_start, hsevenTime] at hrace
  have hcompletedHomogeneous : completed ≤ homogeneous :=
    WithTop.coe_le_coe.mp hrace.1
  have hhomogeneousSeven : homogeneous < seven :=
    WithTop.coe_lt_coe.mp hrace.2
  have hpureSix :
      allPhaseExactly 6 (trace init omega homogeneous) := by
    intro a ha
    exact hmixed.endpoint_phase_six a ha
  have hsevenSeed : firstPhaseSeed init 7 seven omega :=
    firstPhaseSeed_succ_of_pure_before
      hinput 6 homogeneous seven (by norm_num) (by norm_num)
      hpureSix hhomogeneousSeven hphaseSeven
  have hentry :
      LemmaElevenEntry
        (M := timeMainCount (trace init omega seed))
        (R := StageEventSpec.reserveCount (trace init omega seed))
        ell hell (oppositeSign tau) tau
        (trace init omega completed) :=
    lemmaElevenEntry_of_completed_receipts
      (M := timeMainCount (trace init omega seed))
      (C := StageEventSpec.clockCount (trace init omega seed))
      (R := StageEventSpec.reserveCount (trace init omega seed))
      hinput ell hell tau hseed hstrong hnotSnapshot
  have hallThreeTime :
      allThreeStart init omega = (allThree : WithTop ℕ) := by
    simpa only [allThreeStart] using
      (PhaseOneDrainStopping.exitTime_eq_iff_firstHit init
        (allGE (n := n) 3) omega allThree).2 hstrong.entry.all_first
  have hallThreeCompleted : allThree ≤ completed :=
    hstrong.completion.observed_path.start_order.trans
      hstrong.completion.observed_path.observed
  have hallThreeSeven : allThree < seven :=
    (hallThreeCompleted.trans hcompletedHomogeneous).trans_lt
      hhomogeneousSeven
  have hallThreeLt :
      allThreeStart init omega < (seven : WithTop ℕ) := by
    rw [hallThreeTime]
    exact WithTop.coe_lt_coe.mpr hallThreeSeven
  refine ⟨seed, allThree, four, ell, hell,
    oppositeSign tau, tau, five, completed, homogeneous, seven,
    timeMainCount (trace init omega seed),
    StageEventSpec.reserveCount (trace init omega seed),
    rfl, rfl, rfl, hentry, ?_⟩
  exact
    { mixed := hmixed
      seven_time := hsevenTime
      seven_seed := hsevenSeed
      completed_le := hcompletedHomogeneous.trans hhomogeneousSeven.le
      all_three_lt := hallThreeLt }

/-! ## Item 2: finite exact Phase-8 seed -/

structure EightSeedReceipt
    (init : InputCfg n) (omega : InputLog n)
    (seven homogeneous eight : ℕ) : Prop where
  homogeneous_time : homogeneousLatePhaseStart init 7 omega =
    (homogeneous : WithTop ℕ)
  homogeneous_le_spread : homogeneous ≤ seven + logWindow n 3
  eight_seed : firstPhaseSeed init 8 eight omega
  seven_le_eight : seven ≤ eight
  eight_le_horizon : eight ≤ seven + phaseSevenHorizon n

/-- Corrected item 2.  The result's `eight_seed` field is definitionally the
field required by `LemmaElevenPathReceipt`. -/
theorem exists_eightSeed_of_finiteSeven
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n} {seven : ℕ}
    (hsevenSeed : firstPhaseSeed init 7 seven omega)
    (hallThree : allThreeStart init omega < (seven : WithTop ℕ))
    (hhomogeneousGood : omega ∉ phaseSevenHomogeneousFailure init)
    (hupperGood : omega ∉ phaseSevenUpperTimerFailure init) :
    ∃ homogeneous eight : ℕ,
      EightSeedReceipt init omega seven homogeneous eight := by
  have hnotSpread : omega ∉ phaseSevenSpreadFailure init := by
    intro hbad
    exact hhomogeneousGood (Or.inl hbad)
  have hnotLower :
      omega ∉ timerProtectionFailureGuarded init 7 := by
    intro hbad
    exact hhomogeneousGood (Or.inr hbad)
  have hseedSevenTime :
      phaseSeedTime init 7 omega = (seven : WithTop ℕ) :=
    phaseSeedTime_eq_of_firstPhaseSeed init omega 7 seven hsevenSeed
  have hnextLate :
      ((seven + LateTimerPrefixScalar.protectionHorizon n : ℕ) : WithTop ℕ) <
        phaseSeedTime init 8 omega := by
    by_contra hbad
    apply hnotLower
    exact ⟨seven, hseedSevenTime, hallThree, le_of_not_gt hbad⟩
  have hspreadLe : logWindow n 3 ≤ LateTimerPrefixScalar.protectionHorizon n := by
    have hfit := spread_add_drain_horizon_le_protection hinput.1
    omega
  have hgeSeven :
      ∀ a ∈ trace init omega (seven + logWindow n 3),
        7 ≤ a.phase.val := by
    by_contra hbad
    exact hnotSpread ⟨seven, hsevenSeed, hbad⟩
  have hltEight :
      ∀ a ∈ trace init omega (seven + logWindow n 3),
        a.phase.val < 8 := by
    intro a ha
    by_contra hbad
    have hhit :
        someGE (n := n) 8
          (trace init omega (seven + logWindow n 3)) :=
      ⟨a, ha, by omega⟩
    have hleSpread :
        phaseSeedTime init 8 omega ≤
          ((seven + logWindow n 3 : ℕ) : WithTop ℕ) := by
      simpa only [phaseSeedTime] using
        (TraceDrain.exitTime_le_iff init (someGE (n := n) 8) omega
          (seven + logWindow n 3)).2
          ⟨seven + logWindow n 3, le_rfl, hhit⟩
    have hleProtection :
        phaseSeedTime init 8 omega ≤
          ((seven + LateTimerPrefixScalar.protectionHorizon n : ℕ) : WithTop ℕ) :=
      hleSpread.trans (WithTop.coe_le_coe.mpr
        (show seven + logWindow n 3 ≤ seven + LateTimerPrefixScalar.protectionHorizon n by omega))
    exact (not_lt_of_ge hleProtection) hnextLate
  have hpureSpread :
      allPhaseExactly 7
        (trace init omega (seven + logWindow n 3)) := by
    intro a ha
    have hlo := hgeSeven a ha
    have hhi := hltEight a ha
    omega
  have hhomogeneousTop :
      homogeneousLatePhaseStart init 7 omega ≤
        ((seven + logWindow n 3 : ℕ) : WithTop ℕ) := by
    simpa only [homogeneousLatePhaseStart] using
      (TraceDrain.exitTime_le_iff init (allPhaseExactly 7) omega
        (seven + logWindow n 3)).2
        ⟨seven + logWindow n 3, le_rfl, hpureSpread⟩
  have hhomogeneousFinite :
      homogeneousLatePhaseStart init 7 omega ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hhomogeneousTop
  obtain ⟨homogeneous, hhomogeneousRev⟩ :=
    WithTop.ne_top_iff_exists.mp hhomogeneousFinite
  have hhomogeneousTime :
      homogeneousLatePhaseStart init 7 omega =
        (homogeneous : WithTop ℕ) :=
    hhomogeneousRev.symm
  have hhomogeneousLe : homogeneous ≤ seven + logWindow n 3 := by
    have hh := hhomogeneousTop
    rw [hhomogeneousTime] at hh
    exact WithTop.coe_le_coe.mp hh
  have hnext := nextPhaseSeed_finite_and_le
    init 7 homogeneous hhomogeneousTime hupperGood
  obtain ⟨eight, heightRev⟩ :=
    WithTop.ne_top_iff_exists.mp hnext.1
  have heightTime :
      phaseSeedTime init 8 omega = (eight : WithTop ℕ) :=
    heightRev.symm
  have hdeadlineEightTop :
      ((seven + LateTimerPrefixScalar.protectionHorizon n : ℕ) : WithTop ℕ) <
        (eight : WithTop ℕ) := by
    rw [← heightTime]
    exact hnextLate
  have hdeadlineEight : seven + LateTimerPrefixScalar.protectionHorizon n < eight :=
    WithTop.coe_lt_coe.mp hdeadlineEightTop
  have hhomogeneousEight : homogeneous < eight := by
    have hhomogeneousProtection :
        homogeneous ≤ seven + LateTimerPrefixScalar.protectionHorizon n := by
      exact hhomogeneousLe.trans (by omega)
    exact hhomogeneousProtection.trans_lt hdeadlineEight
  have hpureHomogeneous :
      allPhaseExactly 7 (trace init omega homogeneous) :=
    ((homogeneousLatePhaseStart_eq_iff
      init 7 homogeneous omega).mp hhomogeneousTime).1
  have heightSeed : firstPhaseSeed init 8 eight omega :=
    firstPhaseSeed_succ_of_pure_before
      hinput 7 homogeneous eight (by norm_num) (by norm_num)
      hpureHomogeneous hhomogeneousEight heightTime
  have heightLeHomogeneous :
      eight ≤ homogeneous + lateTimerUpperHorizon n := by
    have hh : phaseSeedTime init (7 + 1) omega ≤
        ((homogeneous + lateTimerUpperHorizon n : ℕ) : WithTop ℕ) := hnext.2
    have heightTime' : phaseSeedTime init (7 + 1) omega = (eight : WithTop ℕ) :=
      heightTime
    rw [heightTime'] at hh
    exact WithTop.coe_le_coe.mp hh
  have heightLe : eight ≤ seven + phaseSevenHorizon n := by
    unfold phaseSevenHorizon
    omega
  refine ⟨homogeneous, eight, ?_⟩
  exact
    { homogeneous_time := hhomogeneousTime
      homogeneous_le_spread := hhomogeneousLe
      eight_seed := heightSeed
      seven_le_eight := by omega
      eight_le_horizon := heightLe }

/-!
THEOREM LIST
* `measurableSet_lateTimerUpperFailure`
* `measurableSet_phaseSevenSpreadFailure`
* `measurableSet_timerProtectionFailureGuarded`
* `measurableSet_phaseSixUpperTimerFailure`
* `measurableSet_phaseSevenHomogeneousFailure`
* `measurableSet_phaseSevenUpperTimerFailure`
* `law_phaseSixUpperTimerFailure`
* `law_phaseSevenSpreadFailure`
* `law_phaseSevenHomogeneousFailure`
* `law_phaseSevenUpperTimerFailure`
* `exists_lemmaElevenEntry_and_finiteSeven`
* `exists_eightSeed_of_finiteSeven`

CLOSES
* Corrected item 1: the completion used by `LemmaElevenEntry` precedes a
  finite exact first Phase-7 seed, outside the existing Phase-6 upper-timer
  failure.
* Corrected item 2: threshold-7 spread plus guarded lower-timer protection
  produces an exact homogeneous Phase-7 start; the Phase-7 upper timer then
  produces a finite exact first Phase-8 seed.
* `EightSeedReceipt.eight_seed` has exact type
  `firstPhaseSeed init 8 eight omega`.
* Every newly exposed failure set is measurable and has an unconditional law
  bound under `GoodInput`.

CARRIED PREMISES AND PRODUCERS
* `hinput : GoodInput n init`: caller input.  It supplies the population
  threshold and valid-initial-state premise.
* `hsmall`: caller's small-gap branch membership.
* `hselected`: complement of the available
  `smallGapPhaseSixDrainFailure`; it produces the completed snapshot,
  `MixedWindowCondition`, and homogeneous Phase-6 endpoint.
* `hupper : omega ∉ phaseSixUpperTimerFailure init`: complement of the available
  `lateTimerUpperFailure init 6`; law producer
  `law_phaseSixUpperTimerFailure`.
* `hhomogeneousGood`: complement of threshold-7 spread failure union guarded
  lower-timer failure at `p = 7`; law producer
  `law_phaseSevenHomogeneousFailure`.
* `hupperGood`: complement of the upper-timer failure at `p = 7`; law
  producer `law_phaseSevenUpperTimerFailure`.
* No premise is quantified over all logs or arbitrary configurations.

UNFINISHED
* `after_seven` and the final `LemmaElevenPathReceipt` constructor are outside
  this file.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenFiniteTimes

end
