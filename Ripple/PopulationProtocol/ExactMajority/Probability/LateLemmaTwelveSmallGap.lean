-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaTwelveSmallGap.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaTwelveBands
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaElevenAssembly
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase8WitnessSupply

/-!
# Lemma 12 on the small-gap branch

Imported from `LateLemmaTwelveSingleBand` through `LateLemmaTwelveBands`:
* `phaseSevenBandHorizon`, `phaseSevenSingleBandBudget`;
* the original-law stopped single-band estimate.

Imported from `LateLemmaTwelveBands`:
* `middleBand`, `upperBand`;
* `phaseSevenBandsFailure`, its measurability and law bound;
* `phaseSevenBandsBudget`;
* `phaseSevenBands_empty_of_receipts`, whose only open premise was
  `homogeneous + 3 * phaseSevenBandHorizon n < eight`.

The Phase-7 synchronization and guarded lower timer are already the two
summands of `phaseSevenHomogeneousFailure`.  This file does not charge either
one again.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaTwelveSmallGap

open TimeTheorem PairLog StageEventSpec
open LateF6OriginalLaw
open LateStrengthening
open LateMixedFuel LateMixedFiveSixWindow
open LateSamplingCompletion LateSamplingSeedReceipt
open LateSamplingStrongSeedReceipt
open LateSamplingStrongReceiptProducer
open LatePhaseSixDrainSelectedLevel
open LatePhaseSixDrainPaperNumerics
open LatePhaseSixDrainPaperTimeline
open LateBiasedResourceCredit
open LateBiasedResourceCreditPhaseSeven
open LateBiasedResourceCreditPath
open LateLemmaElevenEntry
open LateLemmaElevenBeforeSeven
open LateLemmaElevenFiniteTimes
open LateLemmaElevenAfterSeven
open LateLemmaElevenAssembly
open LateTimerProtectionOriginalLaw
open LateTimerProtectionGuarded
open LateTimerPrefixScalar
open Phase7BandDefs Phase7BandTransition
open LateLemmaTwelveSingleBand LateLemmaTwelveBands
open LateTimerUpperOriginalLaw

variable {L K n : ℕ}

/-! ## The retained Lemma-11 data -/

/-- Lemma 11 with the two facts discarded by its public consumer structure. -/
structure LemmaTwelveRouteReceipt {n M R : ℕ}
    (init : InputCfg n) (omega : InputLog n)
    (completed seven homogeneous eight : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma tau : Sign) : Prop where
  path : LemmaElevenPathReceipt (M := M) (R := R)
    init omega completed seven eight ell hell sigma tau
  height : EightSeedReceipt init omega seven homogeneous eight
  main_lower : 12 * n ≤ 25 * M
  main_upper : M ≤ n
  protection_lt : seven + protectionHorizon n < eight

private theorem phaseSeedTime_eq_firstSeed
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

/-- The same synchronized construction as Lemma 11, retaining density, the
homogeneous-seven receipt, and the strict protected Phase-8 deadline. -/
theorem exists_lemmaTwelveRouteReceipt_of_not_producerFailure
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ lemmaElevenProducerFailure init) :
    ∃ completed seven homogeneous eight : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        LemmaTwelveRouteReceipt (M := M) (R := R)
          init omega completed seven homogeneous eight
          ell hell sigma tau := by
  have hselected : omega ∉ smallGapPhaseSixDrainFailure init := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hphaseSixUpper : omega ∉ phaseSixUpperTimerFailure init := by
    intro hbad
    exact hgood (Or.inr (Or.inl hbad))
  have hphaseSevenHomogeneous :
      omega ∉ phaseSevenHomogeneousFailure init := by
    intro hbad
    exact hgood (Or.inr (Or.inr (Or.inl hbad)))
  have hphaseSevenUpper : omega ∉ phaseSevenUpperTimerFailure init := by
    intro hbad
    exact hgood (Or.inr (Or.inr (Or.inr hbad)))
  have hnotLower : omega ∉ timerProtectionFailureGuarded init 7 := by
    intro hbad
    exact hphaseSevenHomogeneous (Or.inr hbad)

  have hnotSnapshot :
      omega ∉ smallRowTwoSnapshotProductionFailure init := by
    intro hbad
    exact hselected (Or.inl hbad)
  have hnotMixed : omega ∉ mixedFailure init := by
    intro hbad
    exact hselected (Or.inr (Or.inl hbad))
  have hnotSeed :
      omega ∉ LateMixedFiveSixWindowTailWf.phaseSixSeedFailure init := by
    intro hbad
    exact hselected (Or.inr (Or.inr (Or.inl hbad)))
  have hnotSelected :
      omega ∉ anySelectedProducedLevelPhaseSixFailure init := by
    intro hbad
    exact hselected (Or.inr (Or.inr (Or.inr hbad)))

  obtain ⟨seed, allThree, four, ell, hell, tau, five, completed,
      _history, hseed, hstrong, _ledger⟩ :=
    exists_completedFuelLedger_of_smallHistory
      hinput hsmall hnotSnapshot
  obtain ⟨sixHomogeneous, hmixed⟩ :=
    mixedFiveSixPrefix_of_not_mixedFailure
      hnotMixed hstrong.completion

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

  obtain ⟨seedOther, allThreeOther, fourOther, ellOther, hellOther,
      sigmaOther, tauOther, fiveOther, completedOther, homogeneousOther,
      seven, mainOther, reserveOther, signOther, mainEqOther,
      reserveEqOther, entryOther, sevenOther⟩ :=
    exists_lemmaElevenEntry_and_finiteSeven
      hinput hsmall hselected hphaseSixUpper

  have hallThreeSeven : allThree < seven := by
    have hh := sevenOther.all_three_lt
    rw [hstrong.completion.observed_path.all_start] at hh
    exact WithTop.coe_lt_coe.mp hh
  have hcompletedSeven : completed ≤ seven := by
    by_contra hbad
    have hsevenCompleted : seven ≤ completed := by omega
    obtain ⟨a, ha, hphase⟩ := sevenOther.seven_seed.1
    have hupper :=
      hstrong.completion.observed_path.before_six
        seven hallThreeSeven.le hsevenCompleted a ha
    omega
  have hseven :
      SevenFiniteReceipt init omega completed sixHomogeneous seven :=
    { mixed := hmixed
      seven_time := sevenOther.seven_time
      seven_seed := sevenOther.seven_seed
      completed_le := hcompletedSeven
      all_three_lt := sevenOther.all_three_lt }
  have hbefore :
      ∀ t, completed ≤ t → t ≤ seven →
        PhaseFiveSixCreditReachable init n
          (trace init omega completed) (trace init omega t) :=
    lemmaElevenBeforeSeven_of_strongReceipt
      hstrong hmixed hseven.seven_time

  have hnlarge : 2 ≤ n := by
    have hlarge := (time_population_bounds hinput.1).2
    omega
  obtain ⟨seedSix, hSix⟩ :=
    LateMixedFiveSixWindowTailWf.phaseSixSeedReceipt_of_not_failure
      hnlarge init omega completed
      hstrong.completion.completed_at hnotSeed
  have hcompatible :=
    correctedCompatibleFuelReceipt_of_strong
      hinput.1 ell hell tau hstrong hseed hmixed
  have hstart := phaseSixPaperStart_of_correctedReceipt hcompatible hSix
  have hlevel : omega ∈ producedN16LevelEvent init ell :=
    producedN16LevelEvent_of_receipts ell tau hstrong hseed
  obtain ⟨hnotSpread, hnotTimer, hnotDrain⟩ :=
    not_downstreamFailures_of_producedLevel
      init ell hell hlevel hnotSelected
  obtain ⟨endpoint, hreceipt⟩ :=
    phaseSixPaperDrainReceipt_of_start
      init hinput ell hell hstart hnotSpread hnotTimer hnotDrain
  have hnoShallow : NoShallowMain ell (trace init omega seven) := by
    simpa only [NoShallowMain] using
      (no_shallow_main_at_firstPhaseSeven_of_receipt
        hreceipt hseven.seven_time)

  obtain ⟨sevenHomogeneous, eight, height, hafter⟩ :=
    exists_eightSeed_and_afterSeven
      hinput hseven hphaseSevenHomogeneous hphaseSevenUpper
  have hseedSevenTime :
      phaseSeedTime init 7 omega = (seven : WithTop ℕ) :=
    phaseSeedTime_eq_firstSeed init omega 7 seven hseven.seven_seed
  have heightTime :
      phaseSeedTime init 8 omega = (eight : WithTop ℕ) :=
    phaseSeedTime_eq_firstSeed init omega 8 eight height.eight_seed
  have hprotectedTop :
      ((seven + protectionHorizon n : ℕ) : WithTop ℕ) <
        phaseSeedTime init 8 omega := by
    by_contra hbad
    apply hnotLower
    exact ⟨seven, hseedSevenTime, hseven.all_three_lt,
      le_of_not_gt hbad⟩
  have hprotected : seven + protectionHorizon n < eight := by
    rw [heightTime] at hprotectedTop
    exact WithTop.coe_lt_coe.mp hprotectedTop

  let pathReceipt :
      LemmaElevenPathReceipt
        (M := timeMainCount (trace init omega seed))
        (R := StageEventSpec.reserveCount (trace init omega seed))
        init omega completed seven eight ell hell
          (oppositeSign tau) tau :=
    { good_input := hinput
      small_history := hsmall
      selected_good := hselected
      order := ⟨hcompletedSeven, height.seven_le_eight⟩
      seven_time := hseven.seven_time
      eight_seed := height.eight_seed
      entry := hentry
      before_seven := hbefore
      no_shallow_seven := hnoShallow
      after_seven := hafter }
  refine ⟨completed, seven, sevenHomogeneous, eight, ell, hell,
    oppositeSign tau, tau,
    timeMainCount (trace init omega seed),
    StageEventSpec.reserveCount (trace init omega seed), ?_⟩
  exact
    { path := pathReceipt
      height := height
      main_lower := hstrong.density.mains_lower
      main_upper := by
        have htotal := hstrong.density.total_eq
        omega
      protection_lt := hprotected }

/-- Public enriched producer under the existing measurable Lemma-11 failure. -/
theorem exists_lemmaTwelveRouteReceipt_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ lemmaElevenFailure init) :
    ∃ completed seven homogeneous eight : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        LemmaTwelveRouteReceipt (M := M) (R := R)
          init omega completed seven homogeneous eight
          ell hell sigma tau := by
  apply exists_lemmaTwelveRouteReceipt_of_not_producerFailure
    hinput hsmall
  intro hbad
  exact hgood (lemmaElevenProducerFailure_subset_failure init hbad)

/-! ## Timer comparison -/

/-- The synchronization allowance plus all three six-unit band blocks fit
strictly inside the 26.5-unit protection window, including all ceilings. -/
theorem phaseSevenWork_lt_protection
    {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    logWindow n 3 + 3 * phaseSevenBandHorizon n <
      protectionHorizon n := by
  obtain ⟨hnpos, hnlog⟩ :=
    ScalarTails.time_population_scalar_bounds hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hnOne : (1 : ℝ) ≤ n := by
    have h := Real.add_one_le_exp (Real.log (n : ℝ))
    rw [Real.exp_log hnpos] at h
    linarith
  let z : ℝ := (n : ℝ) * Real.log (n : ℝ)
  have hz : (100 : ℝ) ≤ z := by
    have hmul : (1 : ℝ) * 100 ≤
        (n : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul hnOne hnlog (by norm_num) (by positivity)
    simpa [z] using hmul
  have hsync : (logWindow n 3 : ℝ) < 3 * z + 1 := by
    unfold logWindow
    convert Nat.ceil_lt_add_one
      (show 0 ≤ (3 : ℝ) * (n : ℝ) * Real.log (n : ℝ) by positivity)
      using 1 <;> dsimp [z] <;> ring
  have hband : (phaseSevenBandHorizon n : ℝ) < 6 * z + 1 := by
    unfold phaseSevenBandHorizon logWindow
    convert Nat.ceil_lt_add_one
      (show 0 ≤ (6 : ℝ) * (n : ℝ) * Real.log (n : ℝ) by positivity)
      using 1 <;> dsimp [z] <;> ring
  have hprotect : (53 / 2 : ℝ) * z ≤
      (protectionHorizon n : ℝ) := by
    unfold protectionHorizon
    convert Nat.le_ceil
      ((53 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ))
      using 1 <;> dsimp [z] <;> ring
  have hreal :
      ((logWindow n 3 + 3 * phaseSevenBandHorizon n : ℕ) : ℝ) <
        (protectionHorizon n : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hreal

/-- The formerly open strict deadline of `LateLemmaTwelveBands`, with no additional failure charge. -/
theorem phaseSevenDeadline_lt_eight
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (h : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneous eight ell hell sigma tau) :
    homogeneous + 3 * phaseSevenBandHorizon n < eight := by
  have hfit := phaseSevenWork_lt_protection h.path.good_input.1
  have hsync := h.height.homogeneous_le_spread
  have hprotect := h.protection_lt
  omega

/-! ## Finite union over the per-log witnesses -/

/-- One admissible witness branch; inadmissible density or boundary choices
contribute the empty event. -/
def phaseSevenWitnessBranch
    (init : InputCfg n) (M : Fin (n + 1)) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    Set (InputLog n) :=
  if hM : 12 * n ≤ 25 * M.val then
    if hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n then
      phaseSevenBandsFailure init M.val sigma ell hell
    else ∅
  else ∅

/-- Union over `M ≤ n`, both signs, and every possible selected level. -/
def phaseSevenWitnessFailure (init : InputCfg n) : Set (InputLog n) :=
  ⋃ M : Fin (n + 1),
    ⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      (phaseSevenWitnessBranch init M .pos ell ∪
        phaseSevenWitnessBranch init M .neg ell)

noncomputable def phaseSevenWitnessCharge (n : ℕ) : ℝ≥0∞ :=
  ((2 * (n + 1) *
      (PhaseThreeModel.Numeric.hourIndex n + 1) : ℕ) : ℝ≥0∞) *
    phaseSevenBandsBudget n

private theorem measurableSet_phaseSevenWitnessBranch
    (init : InputCfg n) (M : Fin (n + 1)) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    MeasurableSet (phaseSevenWitnessBranch init M sigma ell) := by
  unfold phaseSevenWitnessBranch
  by_cases hM : 12 * n ≤ 25 * M.val
  · simp only [hM, dite_true]
    by_cases hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n
    · simpa only [hell, dite_true] using
        measurableSet_phaseSevenBandsFailure init M.val sigma ell hell
    · simp [hell]
  · simp [hM]

private theorem law_phaseSevenWitnessBranch
    (init : InputCfg n) (hn : 2 ≤ n)
    (M : Fin (n + 1)) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init (phaseSevenWitnessBranch init M sigma ell) ≤
      phaseSevenBandsBudget n := by
  unfold phaseSevenWitnessBranch
  by_cases hM : 12 * n ≤ 25 * M.val
  · simp only [hM, dite_true]
    by_cases hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n
    · simpa only [hell, dite_true] using
        law_phaseSevenBandsFailure init hn hM sigma ell hell
    · simp [hell]
  · simp [hM]

theorem measurableSet_phaseSevenWitnessFailure
    (init : InputCfg n) :
    MeasurableSet (phaseSevenWitnessFailure init) := by
  unfold phaseSevenWitnessFailure
  apply MeasurableSet.iUnion
  intro M
  apply MeasurableSet.iUnion
  intro ell
  exact
    (measurableSet_phaseSevenWitnessBranch init M .pos ell).union
      (measurableSet_phaseSevenWitnessBranch init M .neg ell)

/-- Exact finite-union charge for the per-log Lemma-11 witnesses. -/
theorem law_phaseSevenWitnessFailure
    (init : InputCfg n) (hn : 2 ≤ n) :
    law init (phaseSevenWitnessFailure init) ≤
      phaseSevenWitnessCharge n := by
  unfold phaseSevenWitnessFailure
  calc
    law init
        (⋃ M : Fin (n + 1),
          ⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
            (phaseSevenWitnessBranch init M .pos ell ∪
              phaseSevenWitnessBranch init M .neg ell)) ≤
      ∑ M : Fin (n + 1),
        law init
          (⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
            (phaseSevenWitnessBranch init M .pos ell ∪
              phaseSevenWitnessBranch init M .neg ell)) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ M : Fin (n + 1),
        ∑ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
          law init
            (phaseSevenWitnessBranch init M .pos ell ∪
              phaseSevenWitnessBranch init M .neg ell) := by
      refine Finset.sum_le_sum fun M _ => ?_
      exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ M : Fin (n + 1),
        ∑ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
          (phaseSevenBandsBudget n + phaseSevenBandsBudget n) := by
      refine Finset.sum_le_sum fun M _ => ?_
      refine Finset.sum_le_sum fun ell _ => ?_
      exact (measure_union_le _ _).trans
        (add_le_add
          (law_phaseSevenWitnessBranch init hn M .pos ell)
          (law_phaseSevenWitnessBranch init hn M .neg ell))
    _ = phaseSevenWitnessCharge n := by
      unfold phaseSevenWitnessCharge
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

private theorem not_phaseSevenBandsFailure_of_not_witnessFailure
    {init : InputCfg n} {omega : InputLog n}
    {M : ℕ} {sigma : Sign}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hMupper : M ≤ n) (hMlower : 12 * n ≤ 25 * M)
    (hgood : omega ∉ phaseSevenWitnessFailure init) :
    omega ∉ phaseSevenBandsFailure init M sigma ell hell := by
  intro hbad
  apply hgood
  let q : Fin (n + 1) := ⟨M, by omega⟩
  unfold phaseSevenWitnessFailure
  refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨ell, ?_⟩⟩
  cases sigma with
  | pos =>
      left
      simpa [phaseSevenWitnessBranch, q, hMlower, hell] using hbad
  | neg =>
      right
      simpa [phaseSevenWitnessBranch, q, hMlower, hell] using hbad

/-! ## The charged Lemma-12 event -/

noncomputable def lemmaTwelveFailure
    (init : InputCfg n) : Set (InputLog n) :=
  lemmaElevenFailure init ∪ phaseSevenWitnessFailure init

noncomputable def lemmaTwelveFailureCharge (n : ℕ) : ℝ≥0∞ :=
  lemmaElevenFailureCharge n + phaseSevenWitnessCharge n

theorem measurableSet_lemmaTwelveFailure
    (init : InputCfg n) :
    MeasurableSet (lemmaTwelveFailure init) := by
  unfold lemmaTwelveFailure
  exact (measurableSet_lemmaElevenFailure init).union
    (measurableSet_phaseSevenWitnessFailure init)

theorem law_lemmaTwelveFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lemmaTwelveFailure init) ≤
      lemmaTwelveFailureCharge n := by
  unfold lemmaTwelveFailure lemmaTwelveFailureCharge
  calc
    law init
        (lemmaElevenFailure init ∪ phaseSevenWitnessFailure init) ≤
      law init (lemmaElevenFailure init) +
        law init (phaseSevenWitnessFailure init) :=
      measure_union_le _ _
    _ ≤ lemmaElevenFailureCharge n + phaseSevenWitnessCharge n := by
      apply add_le_add
      · exact law_lemmaElevenFailure init hinput
      · have hn : 2 ≤ n := by
          have hlarge := (time_population_bounds hinput.1).2
          omega
        exact law_phaseSevenWitnessFailure init hn

/-! ## Transport of the cleared prefix to the first Phase-8 seed -/

private theorem trace_card_eq_population
    {init : InputCfg n} {omega : InputLog n}
    (hcard : init.card = n) (t : ℕ) :
    (trace init omega t).card = n := by
  have hreach :
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega t) := by
    simpa only [trace_zero] using
      (trace_reachable init omega
        (s := 0) (t := t) (Nat.zero_le t))
  exact (Protocol.reachable_card_eq hreach).trans hcard

private theorem firstSeven_le_homogeneous
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hpath : LemmaElevenPathReceipt (M := M) (R := R)
      init omega completed seven eight ell hell sigma tau)
    (height : EightSeedReceipt init omega seven homogeneous eight) :
    seven ≤ homogeneous := by
  have hpure : allPhaseExactly 7 (trace init omega homogeneous) :=
    ((homogeneousLatePhaseStart_eq_iff
      init 7 homogeneous omega).mp height.homogeneous_time).1
  have hcard : (trace init omega homogeneous).card = n :=
    trace_card_eq_population hpath.good_input.2.2 homogeneous
  have hpositive : 0 < (trace init omega homogeneous).card := by
    rw [hcard]
    have hnlarge := (time_population_bounds hpath.good_input.1).2
    omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hpositive
  have hsome : someGE (n := n) 7
      (trace init omega homogeneous) :=
    ⟨a, ha, by rw [hpure a ha]⟩
  have hle : firstPhaseSevenStart init omega ≤
      (homogeneous : WithTop ℕ) := by
    simpa only [firstPhaseSevenStart] using
      (TraceDrain.exitTime_le_iff init
        (someGE (n := n) 7) omega homogeneous).2
        ⟨homogeneous, le_rfl, hsome⟩
  rw [hpath.seven_time] at hle
  exact WithTop.coe_le_coe.mp hle

private theorem phaseSevenWin_before_firstEight
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hpath : LemmaElevenPathReceipt (M := M) (R := R)
      init omega completed seven eight ell hell sigma tau)
    (height : EightSeedReceipt init omega seven homogeneous eight)
    (hhomogeneous : homogeneous ≤ t) (htEight : t < eight) :
    PhaseOnlyWindows.Phase7Win
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      n (trace init omega t) := by
  have hpure : allPhaseExactly 7 (trace init omega homogeneous) :=
    ((homogeneousLatePhaseStart_eq_iff
      init 7 homogeneous omega).mp height.homogeneous_time).1
  have hreach := trace_reachable init omega hhomogeneous
  have hlower :=
    PhaseOneDrainStopping.phase_lower_reachable
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      7 (trace init omega homogeneous) (trace init omega t)
      hreach (fun a ha => by rw [hpure a ha])
  refine ⟨trace_card_eq_population hpath.good_input.2.2 t, ?_⟩
  intro a ha
  have hlo : 7 ≤ a.phase.val := hlower a ha
  have hhi : a.phase.val < 8 := height.eight_seed.2 t htEight a ha
  omega

private theorem bandClear_of_noShallow
    (sigma : Sign) (ell : Fin (L + 1))
    (c : Config (AgentState L K))
    (h : NoShallowMain ell c) :
    BandClear (L := L) (K := K) sigma ell.val c := by
  classical
  intro j hj
  unfold bandCountN
  apply Finset.sum_eq_zero
  intro a ha
  simp only [Phase7Convergence.minorityAt7,
    Finset.mem_filter] at ha
  obtain ⟨_, hmain, hbias⟩ := ha
  by_contra hcount
  have hacount : 1 ≤ c.count a := Nat.one_le_iff_ne_zero.mpr hcount
  have hac : a ∈ c := Multiset.one_le_count_iff_mem.mp hacount
  have hhigh : Phase6Convergence.highSt (L := L) (K := K)
      ell.val a :=
    Phase6Convergence.highSt_of
      (L := L) (K := K) ell.val a sigma j hmain hbias hj
  exact h a hac hhigh

private theorem bandClear_applyDraw
    (sigma : Sign) (m population : ℕ)
    (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase7Win
      (L := L) (K := K) population c)
    (hclear : BandClear (L := L) (K := K) sigma m c)
    (draw : Draw L K) :
    BandClear (L := L) (K := K) sigma m (applyDraw c draw) := by
  cases draw with
  | none => exact hclear
  | some pair =>
      change BandClear (L := L) (K := K) sigma m
        (Protocol.stepOrSelf (NonuniformMajority L K)
          c pair.1.1 pair.2.1)
      exact bandClear_stepOrSelf sigma m population c
        hwin hclear pair.1.1 pair.2.1

private theorem bandClear_trace
    (init : Cfg L K) (omega : Ω L K)
    (sigma : Sign) (m population s t : ℕ)
    (hst : s ≤ t)
    (hclear : BandClear (L := L) (K := K) sigma m
      (trace init omega s))
    (hwin : ∀ u, s ≤ u → u < t →
      PhaseOnlyWindows.Phase7Win (L := L) (K := K) population
        (trace init omega u)) :
    BandClear (L := L) (K := K) sigma m
      (trace init omega t) := by
  induction t, hst using Nat.le_induction with
  | base => exact hclear
  | succ t hst ih =>
      have hprev := ih fun u hsu hut => hwin u hsu (by omega)
      rw [trace_succ]
      exact bandClear_applyDraw sigma m population
        (trace init omega t)
        (hwin t hst (Nat.lt_succ_self t))
        hprev (omega (t + 1))

/-- Literal agent-level form of “every minority index is above `ell+2`”. -/
def AllMinorityIndicesAbove
    (sigma : Sign) (ell : Fin (L + 1))
    (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.main →
    ∀ j : Fin (L + 1), a.bias = Bias.dyadic sigma j →
      ell.val + 2 < j.val

private theorem allMinorityIndicesAbove_of_bandClear
    (sigma : Sign) (ell : Fin (L + 1))
    (c : Config (AgentState L K))
    (hclear : BandClear (L := L) (K := K)
      sigma (ell.val + 3) c) :
    AllMinorityIndicesAbove sigma ell c := by
  intro a ha hmain j hbias
  by_contra hnot
  have hj : j.val < ell.val + 3 := by omega
  have hz := hclear j hj
  rw [Phase8WitnessSupply.bandCountN_eq_countP,
    Multiset.countP_eq_zero] at hz
  exact (hz a ha) ⟨hmain, hbias⟩

/-- The three cleared bands persist through the transition creating the exact
first Phase-8 seed. -/
theorem phaseSevenBands_clear_at_firstEight
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneous eight ell hell sigma tau)
    (hgood : omega ∉ phaseSevenWitnessFailure init) :
    BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma (ell.val + 3) (trace init omega eight) ∧
      AllMinorityIndicesAbove sigma ell (trace init omega eight) := by
  have hdeadline := phaseSevenDeadline_lt_eight hroute
  have hnotBands :
      omega ∉ phaseSevenBandsFailure init M sigma ell hell :=
    not_phaseSevenBandsFailure_of_not_witnessFailure
      hell hroute.main_upper hroute.main_lower hgood
  obtain ⟨_hfinalWin, hzeroBase, hzeroMiddle, hzeroUpper⟩ :=
    phaseSevenBands_empty_of_receipts
      hroute.path hroute.height hdeadline hnotBands
  let finalTime := homogeneous + 3 * phaseSevenBandHorizon n
  have hsevenHomogeneous :=
    firstSeven_le_homogeneous hroute.path hroute.height
  have hsevenFinal : seven ≤ finalTime := by
    dsimp [finalTime]
    omega
  have hfinalEight : finalTime < eight := by
    simpa [finalTime] using hdeadline
  have hbaseClear :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma ell.val (trace init omega finalTime) := by
    apply bandClear_of_noShallow sigma ell
    exact hroute.path.noShallow_at hsevenFinal hfinalEight.le
  have hclearFirst :=
    bandClear_succ_of_count_zero sigma ell
      (trace init omega finalTime) hbaseClear
      (by simpa [finalTime] using hzeroBase)
  have hclearMiddle :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma (middleBand ell hell).val
        (trace init omega finalTime) := by
    simpa [middleBand] using hclearFirst
  have hclearSecond :=
    bandClear_succ_of_count_zero sigma (middleBand ell hell)
      (trace init omega finalTime) hclearMiddle
      (by simpa [finalTime] using hzeroMiddle)
  have hclearUpper :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma (upperBand ell hell).val
        (trace init omega finalTime) := by
    simpa [middleBand, upperBand] using hclearSecond
  have hclearThird :=
    bandClear_succ_of_count_zero sigma (upperBand ell hell)
      (trace init omega finalTime) hclearUpper
      (by simpa [finalTime] using hzeroUpper)
  have hclearFinal :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma (ell.val + 3) (trace init omega finalTime) := by
    simpa [upperBand] using hclearThird
  have hclearEight :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma (ell.val + 3) (trace init omega eight) :=
    bandClear_trace init omega sigma (ell.val + 3) n
      finalTime eight hfinalEight.le hclearFinal (by
        intro u hfinalU huEight
        apply phaseSevenWin_before_firstEight
          hroute.path hroute.height
        · dsimp [finalTime] at hfinalU ⊢
          omega
        · exact huEight)
  exact ⟨hclearEight,
    allMinorityIndicesAbove_of_bandClear
      sigma ell (trace init omega eight) hclearEight⟩

/-! ## Lemma 12, small-gap branch -/

/-- **Lemma 12 on the small-gap branch.**  Outside the single measurable
charged event, the same witnesses carry a Lemma-11 path receipt and every
`σ`-minority Main at the exact first Phase-8 seed has index greater than
`ell+2`. -/
theorem lemmaTwelve_smallGap
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ lemmaTwelveFailure init) :
    ∃ completed seven homogeneous eight : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        LemmaElevenPathReceipt (M := M) (R := R)
            init omega completed seven eight ell hell sigma tau ∧
          BandClear
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
            sigma (ell.val + 3) (trace init omega eight) ∧
          AllMinorityIndicesAbove sigma ell
            (trace init omega eight) := by
  have hgoodEleven : omega ∉ lemmaElevenFailure init := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hgoodBands : omega ∉ phaseSevenWitnessFailure init := by
    intro hbad
    exact hgood (Or.inr hbad)
  obtain ⟨completed, seven, homogeneous, eight, ell, hell,
      sigma, tau, M, R, hroute⟩ :=
    exists_lemmaTwelveRouteReceipt_of_smallHistory
      hinput hsmall hgoodEleven
  obtain ⟨hclear, habove⟩ :=
    phaseSevenBands_clear_at_firstEight hroute hgoodBands
  exact ⟨completed, seven, homogeneous, eight, ell, hell,
    sigma, tau, M, R, hroute.path, hclear, habove⟩

/-!
THEOREM LIST
* `LemmaTwelveRouteReceipt`
* `exists_lemmaTwelveRouteReceipt_of_not_producerFailure`
* `exists_lemmaTwelveRouteReceipt_of_smallHistory`
* `phaseSevenWork_lt_protection`
* `phaseSevenDeadline_lt_eight`
* `phaseSevenWitnessBranch`, `phaseSevenWitnessFailure`
* `phaseSevenWitnessCharge`
* `measurableSet_phaseSevenWitnessFailure`
* `law_phaseSevenWitnessFailure`
* `lemmaTwelveFailure`, `lemmaTwelveFailureCharge`
* `measurableSet_lemmaTwelveFailure`
* `law_lemmaTwelveFailure`
* `AllMinorityIndicesAbove`
* `phaseSevenBands_clear_at_firstEight`
* `lemmaTwelve_smallGap`

CLOSES ITEM 1
* Retains the strict guarded lower-timer conclusion proved on the complement
  of `timerProtectionFailureGuarded init 7`.
* Proves `logWindow n 3 + 3*ceil(6 n log n) < protectionHorizon n`, paying all
  four ceiling units from the 5.5-unit slack.
* `phaseSevenHomogeneousFailure` already contains both synchronization and the
  guarded lower timer, so no charge is duplicated.

CLOSES ITEM 2
* Takes a finite measurable union over `M ≤ n`, both signs, and every `ell`.
* Gives the exact unconditional charge
  `2*(n+1)*(hourIndex n+1)*3*n^(-3.64256)`.
* The enriched receipt proves its actual `M` is in the union and satisfies the
  density premise required by `LateLemmaTwelveBands`.

CLOSES ITEM 3
* `lemmaTwelveFailure` is measurable and has law at most
  `lemmaElevenFailureCharge n + phaseSevenWitnessCharge n` under `GoodInput`.
* Outside it, `lemmaTwelve_smallGap` returns the original synchronized
  `LemmaElevenPathReceipt` and proves `BandClear sigma (ell+3)` at the exact
  first Phase-8 seed, together with the literal agent-level statement that
  every `sigma`-minority index is greater than `ell+2`.

CARRIED PREMISES AND PRODUCERS
* `GoodInput` and membership in `smallHistory` are the only caller premises.
* All Lemma-11 times, the selected level/sign/counts, the strong density, and
  the exact first Phase-8 seed are rebuilt from the existing Lemma-11 producer
  union; no premise quantifies over all logs or arbitrary configurations.
* `LateLemmaTwelveBands` supplies the stopped three-band estimate and deterministic sequencing.
* Phase-7 clearance is propagated to the first Phase-8 target by the available
  `Phase7BandTransition.bandClear_stepOrSelf` theorem.

UNFINISHED
* No mathematical premise is intentionally left open.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaTwelveSmallGap

end
