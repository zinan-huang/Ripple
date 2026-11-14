import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaThirteenSmallGap
import Ripple.PopulationProtocol.ExactMajority.Probability.LateCompositionBudget

/-!
# Total late time on the strict-small-gap branch

The timed exits and retained synchronization receipts implement the total
late-time table following Lemma 14 of the late-tail argument.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal


namespace Ripple.PopulationProtocol.ExactMajority.LateSmallGapTimeArithmetic

open TimeTheorem

private theorem logWindow_cast_lt {n c : ℕ} :
    (logWindow n c : ℝ) < (c : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) + 1 := by
  have hnonneg : 0 ≤ (c : ℝ) * (n : ℝ) * Real.log (n : ℝ) := by positivity
  simpa only [logWindow, mul_assoc] using Nat.ceil_lt_add_one hnonneg

/-- Lemma 15: the 243-unit late chain, including its twelve ceilings, fits
inside the 300-unit deadline. -/
theorem late_time_windows_le {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    logWindow n 4 + (logWindow n 4 + logWindow n 54) +
      3 * (logWindow n 3 + logWindow n 54) +
      logWindow n 4 + logWindow n 4 + logWindow n 2 ≤ logWindow n 300 := by
  obtain ⟨hforty, _, hlog, _, _, _⟩ := time_hour_calibration hn
  have hnreal : (40 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hforty
  have hscale : (240 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnreal) (sub_nonneg.mpr hlog)]
  have hfour := logWindow_cast_lt (n := n) (c := 4)
  have hfiftyfour := logWindow_cast_lt (n := n) (c := 54)
  have hthree := logWindow_cast_lt (n := n) (c := 3)
  have htwo := logWindow_cast_lt (n := n) (c := 2)
  have hdeadline : (300 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) ≤
      (logWindow n 300 : ℝ) := by
    simpa only [logWindow, mul_assoc] using
      (Nat.le_ceil ((300 : ℝ) * (n : ℝ) * Real.log (n : ℝ)))
  have hreal :
      (logWindow n 4 : ℝ) + ((logWindow n 4 : ℝ) + (logWindow n 54 : ℝ)) +
        3 * ((logWindow n 3 : ℝ) + (logWindow n 54 : ℝ)) +
        (logWindow n 4 : ℝ) + (logWindow n 4 : ℝ) + (logWindow n 2 : ℝ) ≤
          (logWindow n 300 : ℝ) := by
    norm_num at hfour hfiftyfour hthree htwo
    nlinarith only [hfour, hfiftyfour, hthree, htwo, hscale, hdeadline]
  exact_mod_cast hreal

end Ripple.PopulationProtocol.ExactMajority.LateSmallGapTimeArithmetic


namespace Ripple.PopulationProtocol.ExactMajority.LateSmallGapBudgetRefinement

open TimeTheorem

/-- Two timed-phase upper exits together cost at most one inverse-square unit. -/
theorem two_upper_exit_charges_le {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    ENNReal.ofReal (1 / (n : ℝ) ^ 5) + ENNReal.ofReal (1 / (n : ℝ) ^ 5) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  have hforty : (40 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (time_population_bounds hn).2
  have hnpos : 0 < (n : ℝ) := by linarith
  have hcube : (2 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 40) hforty 3
    norm_num at hpower ⊢
    linarith
  have hreal : 2 / (n : ℝ) ^ 5 ≤ 1 / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcube (by positivity)
      _ = 1 * (n : ℝ) ^ 5 := by ring
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    1 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5 = 2 / (n : ℝ) ^ 5 := by ring
    _ ≤ 1 / (n : ℝ) ^ 2 := hreal

/-- A late charge of 83 inverse-square units plus the two additional upper
exits fits inside 84 units. -/
theorem late_charge_le {n : ℕ} (hn : timePopulationThreshold ≤ n)
    {base : ℝ≥0∞} (hbase : base ≤ ENNReal.ofReal (83 / (n : ℝ) ^ 2)) :
    base + (ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
      ENNReal.ofReal (1 / (n : ℝ) ^ 5)) ≤ ENNReal.ofReal (84 / (n : ℝ) ^ 2) := by
  calc
    base + (ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
        ENNReal.ofReal (1 / (n : ℝ) ^ 5)) ≤
        ENNReal.ofReal (83 / (n : ℝ) ^ 2) + ENNReal.ofReal (1 / (n : ℝ) ^ 2) :=
      add_le_add hbase (two_upper_exit_charges_le hn)
    _ = ENNReal.ofReal (84 / (n : ℝ) ^ 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end Ripple.PopulationProtocol.ExactMajority.LateSmallGapBudgetRefinement

namespace Ripple.PopulationProtocol.ExactMajority.LateSmallGapTimeChain

open TimeTheorem PairLog StageEventSpec
open LateStrengthening LateF6OriginalLaw
open LateSamplingCompletion LateSamplingSeedReceipt
open LateSamplingStrongSeedReceipt LateSamplingStrongReceiptProducer
open LateSamplingFixedRowTwoHorizon
open LateMixedFuel LateMixedFiveSixWindow
open LatePhaseSixDrainSelectedLevel
open LatePhaseSixDrainPaperNumerics LatePhaseSixDrainPaperTimeline
open LateTimerPrefixScalar LateTimerProtectionOriginalLaw
open LateTimerProtectionGuarded LateTimerUpperOriginalLaw
open LateLemmaElevenFiniteTimes LateLemmaElevenAssembly
open LateLemmaTwelveSmallGap LateLemmaThirteenRoute
open LateLemmaThirteenSmallGap

variable {n : ℕ}

/-- First seeds of a fixed phase have a unique natural time. -/
theorem firstPhaseSeed_unique_time
    {init : InputCfg n} {omega : InputLog n} {p s t : ℕ}
    (hs : firstPhaseSeed init p s omega)
    (ht : firstPhaseSeed init p t omega) : s = t := by
  rcases lt_trichotomy s t with hlt | heq | hgt
  · obtain ⟨a, ha, hp⟩ := hs.1
    have hbefore := ht.2 s hlt a ha
    omega
  · exact heq
  · obtain ⟨a, ha, hp⟩ := ht.1
    have hbefore := hs.2 t hgt a ha
    omega

/-- The four-time witness in a successful history is unique even when the
other history witnesses were independently produced. -/
theorem successfulHistory_four_unique
    {init : InputCfg n} {omega : InputLog n}
    {S T rho S' T' rho' : ℕ}
    (h : successfulHistory (reviewedStageEvents n init) omega S T rho)
    (h' : successfulHistory (reviewedStageEvents n init) omega S' T' rho') :
    rho = rho' :=
  firstPhaseSeed_unique_time
    ((reviewedStageEvents n init).clock_seed h.2.2.1)
    ((reviewedStageEvents n init).clock_seed h'.2.2.1)

/-- The Phase-4 to Phase-7 part of the late-time estimate.  Every time is a
genuine first threshold or first homogeneous hit, rather than a later seed. -/
structure EarlyTimeReceipt
    (init : InputCfg n) (omega : InputLog n)
    (rho firstFive homogeneousFive firstSix homogeneousSix firstSeven : ℕ) : Prop where
  first_five_time : phaseSeedTime init 5 omega = (firstFive : WithTop ℕ)
  first_five_le : firstFive ≤ rho + logWindow n 4
  homogeneous_five_time : homogeneousLatePhaseStart init 5 omega =
    (homogeneousFive : WithTop ℕ)
  homogeneous_five_le : homogeneousFive ≤ firstFive + logWindow n 4
  first_six_time : phaseSeedTime init 6 omega = (firstSix : WithTop ℕ)
  first_six_le : firstSix ≤ homogeneousFive + lateTimerUpperHorizon n
  homogeneous_six_time : homogeneousLatePhaseStart init 6 omega =
    (homogeneousSix : WithTop ℕ)
  homogeneous_six_le : homogeneousSix ≤ firstSix + logWindow n 3
  first_seven_time : phaseSeedTime init 7 omega = (firstSeven : WithTop ℕ)
  first_seven_seed : firstPhaseSeed init 7 firstSeven omega
  first_seven_le : firstSeven ≤ homogeneousSix + lateTimerUpperHorizon n
  total_le : firstSeven ≤ rho + logWindow n 4 + logWindow n 4 +
    lateTimerUpperHorizon n + logWindow n 3 + lateTimerUpperHorizon n

/-- Doty et al.'s early late-time chain.  The supplied successful history fixes the
actual Phase-4 origin; the row-two producer's origin is identified with it
through first-seed uniqueness. -/
theorem exists_earlyTimeReceipt
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n} {S T rho : ℕ}
    (hhistory : successfulHistory (reviewedStageEvents n init) omega S T rho)
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ lemmaThirteenFailure init)
    (hupperFive : omega ∉ lateTimerUpperFailure init 5) :
    ∃ firstFive homogeneousFive firstSix homogeneousSix firstSeven : ℕ,
      EarlyTimeReceipt init omega rho
        firstFive homogeneousFive firstSix homogeneousSix firstSeven := by
  have hgoodEleven : omega ∉ lemmaElevenFailure init := by
    intro hbad
    exact hgood (Or.inl (Or.inl (Or.inl hbad)))
  have hgoodProducer : omega ∉ lemmaElevenProducerFailure init := by
    intro hbad
    exact hgoodEleven (lemmaElevenProducerFailure_subset_failure init hbad)
  have hselected : omega ∉ smallGapPhaseSixDrainFailure init :=
    fun h => hgoodProducer (Or.inl h)
  have hupperSix : omega ∉ phaseSixUpperTimerFailure init :=
    fun h => hgoodProducer (Or.inr (Or.inl h))
  have hnotSnapshot : omega ∉ smallRowTwoSnapshotProductionFailure init :=
    fun h => hselected (Or.inl h)
  have hnotMixed : omega ∉ mixedFailure init :=
    fun h => hselected (Or.inr (Or.inl h))
  have hnotSeed : omega ∉ LateMixedFiveSixWindowTailWf.phaseSixSeedFailure init :=
    fun h => hselected (Or.inr (Or.inr (Or.inl h)))
  have hnotSelected : omega ∉ anySelectedProducedLevelPhaseSixFailure init :=
    fun h => hselected (Or.inr (Or.inr (Or.inr h)))
  have hnotFixed : omega ∉ fixedRowTwoHorizonProductionFailure init :=
    fun h => hnotSnapshot (Or.inr (Or.inl h))
  have hnotFour : omega ∉ phaseFourSpreadFailure init :=
    fun h => hnotFixed (Or.inl (Or.inr (Or.inl h)))
  have hnotFive : omega ∉ phaseFiveSpreadFailure init :=
    fun h => hnotFixed (Or.inl (Or.inr (Or.inr h)))
  obtain ⟨seed, allThree, four, ell, hell, sigma, five, completed,
      hhistoryProduced, hseed, hstrong, _hledger⟩ :=
    exists_completedFuelLedger_of_smallHistory hinput hsmall hnotSnapshot
  have hfourEq : four = rho :=
    successfulHistory_four_unique hhistoryProduced hhistory
  obtain ⟨firstFive, hfirstFive, hallFirstFive, hfourFirstFive, hfirstFiveLe⟩ :=
    phaseFiveSeed_of_successfulHistory hinput ell hell sigma
      hhistoryProduced hseed hnotFour
  have hfixed := fixedRowTwoHorizon_of_not_productionFailure
    hinput ell hell sigma hstrong hseed hnotFixed
  have hwide := hfixed.path
  have hwork := rowTwoWorkHorizon_le_protection hinput.1
  have hallGEFive : allGE (n := n) 5
      (trace init omega (firstFive + logWindow n 4)) := by
    by_contra hbad
    apply hnotFive
    rw [mem_phaseFiveSpreadFailure_iff]
    refine ⟨firstFive, hfirstFive, ?_, ?_, hbad⟩
    · have hreach := TimeTheorem.trace_reachable init omega
        (s := 0) (t := firstFive) (Nat.zero_le firstFive)
      simpa only [TimeTheorem.trace_zero] using
        (Protocol.reachable_card_eq hreach).trans hstrong.population
    · exact ((phaseSeedTime_eq_iff init 5 omega firstFive).mp hfirstFive).1
  have hallFive : allPhaseFive
      (trace init omega (firstFive + logWindow n 4)) := by
    intro a ha
    exact le_antisymm
      (hwide.before_six (firstFive + logWindow n 4)
        (by omega) (by omega) a ha)
      (hallGEFive a ha)
  have hhomogeneousFiveLe : five ≤ firstFive + logWindow n 4 := by
    have htop : homogeneousFiveStart init omega ≤
        ((firstFive + logWindow n 4 : ℕ) : WithTop ℕ) := by
      simpa only [homogeneousFiveStart] using
        (TraceDrain.exitTime_le_iff init allPhaseFive omega
          (firstFive + logWindow n 4)).2
          ⟨firstFive + logWindow n 4, le_rfl, hallFive⟩
    rw [hstrong.completion.five_start] at htop
    exact WithTop.coe_le_coe.mp htop
  have hhomogeneousFive : homogeneousLatePhaseStart init 5 omega =
      (five : WithTop ℕ) := by
    simpa only [homogeneousLatePhaseStart, allPhaseExactly,
      homogeneousFiveStart, allPhaseFive] using hstrong.completion.five_start
  have hnlarge : 2 ≤ n := by
    have hn := (time_population_bounds hinput.1).2
    omega
  obtain ⟨firstSix, hSix⟩ :=
    LateMixedFiveSixWindowTailWf.phaseSixSeedReceipt_of_not_failure
      hnlarge init omega completed hstrong.completion.completed_at hnotSeed
  have hfirstSix : phaseSeedTime init 6 omega = (firstSix : WithTop ℕ) := by
    simpa only [phaseSeedTime, LateF6OriginalLaw.firstSixStart] using hSix.time
  have hnextSix := nextPhaseSeed_finite_and_le
    init 5 five hhomogeneousFive hupperFive
  have hfirstSixLe : firstSix ≤ five + lateTimerUpperHorizon n := by
    have hh := hnextSix.2
    rw [hfirstSix] at hh
    exact WithTop.coe_le_coe.mp hh
  obtain ⟨homogeneousSix, hmixed⟩ :=
    mixedFiveSixPrefix_of_not_mixedFailure hnotMixed hstrong.completion
  have hlevel : omega ∈ producedN16LevelEvent init ell :=
    producedN16LevelEvent_of_receipts ell sigma hstrong hseed
  obtain ⟨hnotSpread, hnotTimer, _hnotDrain⟩ :=
    not_downstreamFailures_of_producedLevel init ell hell hlevel hnotSelected
  have hcompatible := correctedCompatibleFuelReceipt_of_strong
    hinput.1 ell hell sigma hstrong hseed hmixed
  have hstart := phaseSixPaperStart_of_correctedReceipt hcompatible hSix
  have hguard : allThreeStart init omega < (firstSix : WithTop ℕ) :=
    LatePhaseSixDrainStrictTimer.phaseSixPaperStart_allThreeStart_lt_phaseSeedTime hstart
  have htimerLate :
      ((firstSix + protectionHorizon n : ℕ) : WithTop ℕ) <
        phaseSeedTime init 7 omega := by
    by_contra hnot
    apply hnotTimer
    exact ⟨firstSix, hfirstSix, hguard, not_lt.mp hnot⟩
  have htimerSeven :
      ((firstSix + protectionHorizon n : ℕ) : WithTop ℕ) <
        firstPhaseSevenStart init omega := by
    simpa only [phaseSeedTime, firstPhaseSevenStart] using htimerLate
  have hallSix : ∀ a ∈ trace init omega (firstSix + logWindow n 3),
      6 ≤ a.phase.val := by
    by_contra hbad
    exact hnotSpread ⟨firstSix, hstart.six_seed, hbad⟩
  have hfit := spread_add_drain_horizon_le_protection hinput.1
  have hspreadLe : logWindow n 3 ≤ protectionHorizon n := by omega
  have hspreadBefore :
      ((firstSix + logWindow n 3 : ℕ) : WithTop ℕ) <
        firstPhaseSevenStart init omega :=
    (WithTop.coe_le_coe.mpr
      (Nat.add_le_add_left hspreadLe firstSix)).trans_lt htimerSeven
  have hbelowSeven := phase_lt_seven_before_firstPhaseSevenStart
    init omega (firstSix + logWindow n 3) hspreadBefore
  have hallExactSix : allPhaseSix
      (trace init omega (firstSix + logWindow n 3)) := by
    intro a ha
    have hlo := hallSix a ha
    have hhi := hbelowSeven a ha
    omega
  have hhomogeneousSixLe : homogeneousSix ≤ firstSix + logWindow n 3 := by
    have htop : homogeneousSixStart init omega ≤
        ((firstSix + logWindow n 3 : ℕ) : WithTop ℕ) := by
      simpa only [homogeneousSixStart] using
        (TraceDrain.exitTime_le_iff init allPhaseSix omega
          (firstSix + logWindow n 3)).2
          ⟨firstSix + logWindow n 3, le_rfl, hallExactSix⟩
    rw [hmixed.six_start] at htop
    exact WithTop.coe_le_coe.mp htop
  have hhomogeneousSix : homogeneousLatePhaseStart init 6 omega =
      (homogeneousSix : WithTop ℕ) := by
    simpa only [homogeneousLatePhaseStart, allPhaseExactly,
      homogeneousSixStart, allPhaseSix] using hmixed.six_start
  obtain ⟨_seedOther, _allThreeOther, _fourOther, _ellOther, _hellOther,
      _sigmaOther, _tauOther, _fiveOther, _completedOther, _homogeneousOther,
      firstSeven, _mainOther, _reserveOther, _signOther, _mainEqOther,
      _reserveEqOther, _entryOther, hseven⟩ :=
    exists_lemmaElevenEntry_and_finiteSeven hinput hsmall hselected hupperSix
  have hfirstSeven : phaseSeedTime init 7 omega = (firstSeven : WithTop ℕ) := by
    simpa only [phaseSeedTime, firstPhaseSevenStart] using hseven.seven_time
  have hnextSeven := nextPhaseSeed_finite_and_le
    init 6 homogeneousSix hhomogeneousSix hupperSix
  have hfirstSevenLe : firstSeven ≤ homogeneousSix + lateTimerUpperHorizon n := by
    have hh := hnextSeven.2
    rw [hfirstSeven] at hh
    exact WithTop.coe_le_coe.mp hh
  refine ⟨firstFive, five, firstSix, homogeneousSix, firstSeven,
    { first_five_time := hfirstFive
      first_five_le := ?_
      homogeneous_five_time := hhomogeneousFive
      homogeneous_five_le := hhomogeneousFiveLe
      first_six_time := hfirstSix
      first_six_le := hfirstSixLe
      homogeneous_six_time := hhomogeneousSix
      homogeneous_six_le := hhomogeneousSixLe
      first_seven_time := hfirstSeven
      first_seven_seed := hseven.seven_seed
      first_seven_le := hfirstSevenLe
      total_le := ?_ }⟩
  · simpa only [hfourEq] using hfirstFiveLe
  · omega



open TimeTheorem PairLog StageEventSpec
open LateLemmaThirteenSmallGap LateLemmaThirteenRoute
open LateLemmaElevenFiniteTimes LateTimerUpperOriginalLaw
open LateTimerProtectionOriginalLaw

variable {n : ℕ}

/-- Fixed producer failures for the total late-time table. The Phase-6 and
Phase-7 upper exits are already charged inside the Lemma-13 event. -/
def lateSmallGapTimeFailure (init : InputCfg n) : Set (InputLog n) :=
  lemmaThirteenFailure init ∪
    (lateTimerUpperFailure init 5 ∪ lateTimerUpperFailure init 8)

/-- The Lemma-13 charge and the two additional timed exits. -/
def charge (n : ℕ) : ℝ≥0∞ :=
  lemmaThirteenFailureCharge n +
    (ENNReal.ofReal (1 / (n : ℝ) ^ 5) + ENNReal.ofReal (1 / (n : ℝ) ^ 5))

/-- Measurability of the fixed finite union in the total late-time table. -/
theorem measurableSet_lateSmallGapTimeFailure (init : InputCfg n) :
    MeasurableSet (lateSmallGapTimeFailure init) :=
  (measurableSet_lemmaThirteenFailure init).union
    ((measurableSet_lateTimerUpperFailure init 5).union
      (measurableSet_lateTimerUpperFailure init 8))

/-- Unconditional original-law bound for the total late-time failures. -/
theorem law_lateSmallGapTimeFailure (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lateSmallGapTimeFailure init) ≤ charge n := by
  unfold lateSmallGapTimeFailure charge
  exact (measure_union_le _ _).trans (add_le_add
    (law_lemmaThirteenFailure init hinput)
    ((measure_union_le _ _).trans (add_le_add
      (law_lateTimerUpperFailure_tail init hinput 5 (by unfold LateTimedPhase; omega))
      (law_lateTimerUpperFailure_tail init hinput 8 (by unfold LateTimedPhase; omega)))))

/-- The time-chain charge fits into the Lemma-15 reserve. -/
theorem charge_le (hn : timePopulationThreshold ≤ n) :
    charge n ≤ ENNReal.ofReal (84 / (n : ℝ) ^ 2) :=
  LateSmallGapBudgetRefinement.late_charge_le hn
    (LateCompositionBudget.lemmaThirteenFailureCharge_le hn)

/-- Including the three inverse-square units reserved for Lemma 14, the
whole late failure charge remains strictly below the requested budget. -/
theorem charge_with_cleanup_lt (hn : timePopulationThreshold ≤ n) :
    charge n + LateCompositionBudget.lemmaFourteenCharge n <
      ENNReal.ofReal (100 / (n : ℝ) ^ 2) := by
  have hnpos : 0 < (n : ℝ) := (time_hour_calibration hn).2.1
  have hbound : charge n + LateCompositionBudget.lemmaFourteenCharge n ≤
      ENNReal.ofReal (87 / (n : ℝ) ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (84 / (n : ℝ) ^ 2) +
          ENNReal.ofReal (3 / (n : ℝ) ^ 2) :=
        add_le_add (charge_le hn) (LateCompositionBudget.lemmaFourteenCharge_le hn)
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  apply hbound.trans_lt
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  exact div_lt_div_of_pos_right (by norm_num) (by positivity)

/-- The Phase-8 upper timer makes the first Phase-9 seed finite and retains
the Lemma-13 work receipt before that seed. -/
theorem finite_nine_of_smallHistory
    {init : InputCfg n} (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n} (hsmall : omega ∈ LateStrengthening.smallHistory init)
    (hgood : omega ∉ lateSmallGapTimeFailure init) :
    ∃ completed seven homogeneousSeven eight homogeneousEight t firstNine : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        LemmaThirteenSmallGapReceipt (M := M) (R := R)
          init omega completed seven homogeneousSeven eight homogeneousEight t
          ell hell sigma tau ∧
        phaseSeedTime init 9 omega = (firstNine : WithTop ℕ) ∧
        t < firstNine ∧
        firstNine ≤ seven + (logWindow n 3 + logWindow n 54) +
          (logWindow n 3 + logWindow n 54) := by
  have hthirteen : omega ∉ lemmaThirteenFailure init :=
    fun h => hgood (Or.inl h)
  have hupper : omega ∉ lateTimerUpperFailure init 8 :=
    fun h => hgood (Or.inr (Or.inr h))
  obtain ⟨completed, seven, homogeneousSeven, eight, homogeneousEight, t,
      ell, hell, sigma, tau, M, R, hreceipt⟩ :=
    lemmaThirteen_smallGap hinput hsmall hthirteen
  have hnext := nextPhaseSeed_finite_and_le init 8 homogeneousEight
    hreceipt.route.timing.homogeneous_time hupper
  obtain ⟨firstNine, hfirst⟩ := WithTop.ne_top_iff_exists.mp hnext.1
  have htime : phaseSeedTime init 9 omega = (firstNine : WithTop ℕ) := hfirst.symm
  have hbefore : t < firstNine := by
    have h := hreceipt.before_nine
    rw [htime] at h
    exact WithTop.coe_lt_coe.mp h
  have hnine : firstNine ≤ homogeneousEight + logWindow n 54 := by
    have h := hnext.2
    change phaseSeedTime init 9 omega ≤ _ at h
    rw [htime] at h
    exact WithTop.coe_le_coe.mp h
  have height := hreceipt.route.twelve.height.eight_le_horizon
  have hhom := hreceipt.route.timing.homogeneous_le_spread
  unfold phaseSevenHorizon lateTimerUpperHorizon at height
  exact ⟨completed, seven, homogeneousSeven, eight, homogeneousEight, t, firstNine,
    ell, hell, sigma, tau, M, R, hreceipt, htime, hbefore, by omega⟩

/-- The total late-time table for each successful-history origin on the
strict-small-gap branch. The work receipt is retained for Lemma 14. -/
theorem lateSmallGapTimeChain
    {init : InputCfg n} (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n} {S T rho : ℕ}
    (hhistory : successfulHistory (reviewedStageEvents n init) omega S T rho)
    (hsmall : omega ∈ LateStrengthening.smallHistory init)
    (hgood : omega ∉ lateSmallGapTimeFailure init) :
    ∃ completed seven homogeneousSeven eight homogeneousEight t firstNine : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        LemmaThirteenSmallGapReceipt (M := M) (R := R)
          init omega completed seven homogeneousSeven eight homogeneousEight t
          ell hell sigma tau ∧
        phaseSeedTime init 9 omega = (firstNine : WithTop ℕ) ∧
        t < firstNine ∧
        firstNine + logWindow n 4 + logWindow n 4 + logWindow n 2 ≤
          rho + logWindow n 300 := by
  have hthirteen : omega ∉ lemmaThirteenFailure init :=
    fun h => hgood (Or.inl h)
  have hupperFive : omega ∉ lateTimerUpperFailure init 5 :=
    fun h => hgood (Or.inr (Or.inl h))
  obtain ⟨firstFive, homogeneousFive, firstSix, homogeneousSix, earlySeven, hearly⟩ :=
    exists_earlyTimeReceipt hinput hhistory hsmall hthirteen hupperFive
  obtain ⟨completed, seven, homogeneousSeven, eight, homogeneousEight, t, firstNine,
      ell, hell, sigma, tau, M, R, hreceipt, htime, hbefore, hlate⟩ :=
    finite_nine_of_smallHistory hinput hsmall hgood
  have hseven : phaseSeedTime init 7 omega = (seven : WithTop ℕ) := by
    simpa only [phaseSeedTime, LateMixedFiveSixWindow.firstPhaseSevenStart] using
      hreceipt.route.twelve.path.seven_time
  have heq : earlySeven = seven :=
    WithTop.coe_injective (hearly.first_seven_time.symm.trans hseven)
  have hearlyBound := hearly.total_le
  rw [heq] at hearlyBound
  unfold lateTimerUpperHorizon at hearlyBound
  have hbudget := LateSmallGapTimeArithmetic.late_time_windows_le hinput.1
  exact ⟨completed, seven, homogeneousSeven, eight, homogeneousEight, t, firstNine,
    ell, hell, sigma, tau, M, R, hreceipt, htime, hbefore, by omega⟩

end Ripple.PopulationProtocol.ExactMajority.LateSmallGapTimeChain


