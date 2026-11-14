-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingStrongReceiptProducer.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingReceiptScope

/-!
# Direct strong receipt producer on the strict-small-gap branch

The phase-5 seed, homogeneous-five start, completion gates, completion receipt,
and fixed completed row-two snapshot are produced from one successful history
and one N16 receipt.  The construction never uses `completionBase`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingStrongReceiptProducer

open TimeTheorem PairLog StageEventSpec PhaseOneDrainStopping
open AveragingEventInterface
open LateStrengthening
open LateF6OriginalLaw LateF6Hazards
open LateAcceptedRectangleHazard
open LateTimerPrefixScalar LateTimerProtectionOriginalLaw
open LateTimerProtectionGuarded
open LateSamplingCompletion LateSamplingSeedReceipt
open LateSamplingStrongSeedReceipt
open LateSamplingRowTwoChoices LateSamplingRowTwoThresholdRepair
open LateSamplingCompletedFuelSnapshot
open LateSamplingFixedRowTwoHorizon
open LateSamplingCompletedFuelProtected
open LateSamplingReceiptScope
open LateThresholdAcceptedCounterCoupling

variable {n : ℕ}

/-- Item 1: `successfulHistory` contains the asynchronous entry literally. -/
theorem asyncEntry_of_successfulHistory
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four : ℕ}
    (h : successfulHistory (reviewedStageEvents n init)
      omega seed allThree four) :
    AsyncEntry init omega seed allThree := by
  exact (reviewedStageEvents_entry_iff init omega seed allThree).mp h.2.1

/-- The same history contains the complete canonical clock history. -/
theorem clockHistory_of_successfulHistory
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four : ℕ}
    (h : successfulHistory (reviewedStageEvents n init)
      omega seed allThree four) :
    ∃ w : ClockTimes init,
      ClockHistory init omega seed allThree four w := by
  exact
    (reviewedStageEvents_clockGood_iff
      init omega seed allThree four).mp h.2.2.1

private theorem label_mem_trace
    (init : InputCfg n) (omega : InputLog n) (t : ℕ)
    (i : Fin init.card) :
    labelsAt init omega t i ∈ trace init omega t := by
  rw [← PairLog.labelsAt_config init omega t]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

private theorem trace_card_eq_population
    {init : InputCfg n} {omega : InputLog n}
    (hcard : init.card = n) (t : ℕ) :
    (trace init omega t).card = n := by
  have hreach :
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega t) := by
    simpa only [TimeTheorem.trace_zero] using
      (TimeTheorem.trace_reachable init omega
        (s := 0) (t := t) (Nat.zero_le t))
  exact (Protocol.reachable_card_eq hreach).trans hcard

/-- Every Main in the N16 adjacent stored-index class is a useful Main for the
completion death process. -/
private theorem adjacentClassCount_le_usefulMainCount
    {L K m : ℕ} (ell : Fin (L + 1))
    (hell : ell.val + 2 ≤ L)
    (f : Fin m → AgentState L K) :
    classCount (indexClass (adjacentIndices ell hell)) f ≤
      usefulMainCount (PairLog.labelCfg f) := by
  classical
  have hcount : usefulMainCount (PairLog.labelCfg f) =
      (pool f (fun a => Phase5Convergence.biasedMainLtL a)).card := by
    unfold usefulMainCount
    rw [AveragingLiveProduct.countP_labelCfg]
    unfold pool
    congr
  rw [hcount]
  unfold classCount
  apply pool_mono
  intro a ha
  rcases ha with ⟨hrole, hclass⟩
  change a.role = .main at hrole
  cases hbias : a.bias with
  | zero =>
      have : False := by
        simpa [indexClass, hbias] using hclass
      contradiction
  | dyadic sigma j =>
      have hj :
          j ∈ adjacentIndices ell hell ∧ j.val < L := by
        simpa [indexClass, hbias] using hclass
      exact ⟨hrole, sigma, j, hj.2, hbias⟩

/-- The genuine phase-5 seed is forced directly by the phase-4 spread and the
N16 adjacent-class floor.  The temporary `Prefix` used in the contradiction is
built from `ClockHistory` under the assumption that phase 5 has not yet
occurred; no receipt containing a future completion is used. -/
theorem phaseFiveSeed_of_successfulHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n} {seed allThree four : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hhistory : successfulHistory (reviewedStageEvents n init)
      omega seed allThree four)
    (hseed : LateSamplingSeedReceipt init
      (timeMainCount (trace init omega seed)) ell.val sigma
      (trace init omega four))
    (hnotFour : omega ∉ phaseFourSpreadFailure init) :
    ∃ seedFive : ℕ,
      phaseSeedTime init 5 omega = (seedFive : WithTop ℕ) ∧
      allThree < seedFive ∧ four ≤ seedFive ∧
      seedFive ≤ four + logWindow n 4 := by
  obtain ⟨w, H⟩ := clockHistory_of_successfulHistory hhistory
  have hfourStart :
      firstFourStart init omega = (four : WithTop ℕ) :=
    firstFourStart_eq_of_firstPhaseSeed init omega four H.first_exit
  have hallFour :
      allGE (n := n) 4
        (trace init omega (four + logWindow n 4)) := by
    by_contra hbad
    apply hnotFour
    rw [mem_phaseFourSpreadFailure_iff init omega]
    refine ⟨four, hfourStart,
      trace_card_eq_population hinput.2.2 four, ?_, hbad⟩
    obtain ⟨a, ha, hp⟩ := H.first_exit.1
    exact ⟨a, ha, hp.ge⟩
  have hseedLe :
      phaseSeedTime init 5 omega ≤
        ((four + logWindow n 4 : ℕ) : WithTop ℕ) := by
    by_contra hnot
    have hbefore :
        ((four + logWindow n 4 : ℕ) : WithTop ℕ) <
          phaseSeedTime init 5 omega :=
      lt_of_not_ge hnot
    have hnone :=
      TraceDrain.not_of_lt_exitTime init
        (someGE (n := n) 5) omega (four + logWindow n 4)
        (by simpa only [phaseSeedTime] using hbefore)
    have hupper :
        ∀ u, allThree ≤ u → u ≤ four + logWindow n 4 →
          ∀ a ∈ trace init omega u, a.phase.val ≤ 5 := by
      intro u _ hu a ha
      have hnotFive : ¬ 5 ≤ a.phase.val := by
        intro hfive
        exact hnone u hu ⟨a, ha, hfive⟩
      omega
    have hpath :
        Prefix init omega allThree four
          (four + logWindow n 4) :=
      prefix_of_clockHistory init omega seed allThree four
        (four + logWindow n 4) w H
        (Nat.le_add_right four _) hupper
    have hMpos :
        0 < timeMainCount (trace init omega seed) := by
      have hstrict := hseed.toSmallReadout.strictGap
      omega
    have hclassPos :
        0 < classCount
          (indexClass (adjacentIndices ell hell))
          (labelsAt init omega (four + logWindow n 4)) := by
      rcases hseed.near_credit with hsmall | hcredit
      · have hfloor := first_branch_global_floor_at
          hinput.2.1 hell hpath hseed
          (Nat.le_add_right four _) le_rfl hsmall
        omega
      · have hfloor := credit_branch_global_floor_at
          hell hpath hseed (Nat.le_add_right four _) le_rfl hcredit
        omega
    have hpoolPos :
        0 < (pool
          (labelsAt init omega (four + logWindow n 4))
          (MainClass (indexClass (adjacentIndices ell hell)))).card := by
      simpa only [classCount] using hclassPos
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpoolPos
    have hmainClass :
        MainClass (indexClass (adjacentIndices ell hell))
          (labelsAt init omega (four + logWindow n 4) i) :=
      (mem_pool _ _ _).mp hi
    have heligible :
        LateF6Acceptance.Eligible (labelsAt init omega (four + logWindow n 4) i) :=
      indexClass_eligible (adjacentIndices ell hell)
        (labelsAt init omega (four + logWindow n 4) i) hmainClass
    have hphaseFour :
        4 ≤ (labelsAt init omega
          (four + logWindow n 4) i).phase.val :=
      hallFour _
        (label_mem_trace init omega (four + logWindow n 4) i)
    have hphaseFive :
        (labelsAt init omega
          (four + logWindow n 4) i).phase.val = 5 :=
      hpath.canonical (four + logWindow n 4)
        (hpath.start_order.trans (Nat.le_add_right four _)) le_rfl
        i heligible hphaseFour
    have hsomeFive :
        someGE (n := n) 5
          (trace init omega (four + logWindow n 4)) :=
      ⟨labelsAt init omega (four + logWindow n 4) i,
        label_mem_trace init omega (four + logWindow n 4) i,
        hphaseFive.ge⟩
    exact (hnone (four + logWindow n 4) le_rfl hsomeFive).elim
  have hfinite : phaseSeedTime init 5 omega ≠ ⊤ :=
    ne_top_of_le_ne_top
      (show ((four + logWindow n 4 : ℕ) : WithTop ℕ) ≠ ⊤ from
        WithTop.coe_ne_top) hseedLe
  obtain ⟨seedFive, hseedFive⟩ :=
    WithTop.ne_top_iff_exists.mp hfinite
  have htime :
      phaseSeedTime init 5 omega = (seedFive : WithTop ℕ) :=
    hseedFive.symm
  have hdeadline : seedFive ≤ four + logWindow n 4 := by
    rw [htime] at hseedLe
    exact WithTop.coe_le_coe.mp hseedLe
  have hfirstFive :=
    (phaseSeedTime_eq_iff init 5 omega seedFive).mp htime
  have hfourTop :
      firstFourStart init omega ≤ (seedFive : WithTop ℕ) := by
    simpa only [firstFourStart] using
      (TraceDrain.exitTime_le_iff init
        (someGE (n := n) 4) omega seedFive).2
        ⟨seedFive, le_rfl, by
          obtain ⟨a, ha, hfive⟩ := hfirstFive.1
          exact ⟨a, ha, by omega⟩⟩
  rw [hfourStart] at hfourTop
  have hfourSeed : four ≤ seedFive :=
    WithTop.coe_le_coe.mp hfourTop
  have hallFourOrder :=
    (clockHistory_seed_lt_exit H).2
  exact ⟨seedFive, htime, hallFourOrder.trans_le hfourSeed,
    hfourSeed, hdeadline⟩

/-- Once the genuine phase-5 seed has been produced, the guarded timer gives
one legal prefix through the whole fixed row-two horizon. -/
theorem widePrefix_of_successfulHistory
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four seedFive : ℕ}
    (hhistory : successfulHistory (reviewedStageEvents n init)
      omega seed allThree four)
    (hseedFive :
      phaseSeedTime init 5 omega = (seedFive : WithTop ℕ))
    (hallSeed : allThree < seedFive)
    (hfourSeed : four ≤ seedFive)
    (hnotTimer : omega ∉ timerProtectionFailureGuarded init 5) :
    Prefix init omega allThree four
      (four + protectionHorizon n) := by
  obtain ⟨w, H⟩ := clockHistory_of_successfulHistory hhistory
  have hallStart :
      allThreeStart init omega = (allThree : WithTop ℕ) := by
    simpa only [allThreeStart] using
      ((exitTime_eq_iff_firstHit init
        (allGE (n := n) 3) omega allThree).2 H.entry.all_first)
  have hguard :
      allThreeStart init omega < (seedFive : WithTop ℕ) := by
    rw [hallStart]
    exact_mod_cast hallSeed
  have hnext :
      ((seedFive + protectionHorizon n : ℕ) : WithTop ℕ) <
        phaseSeedTime init 6 omega := by
    by_contra hnotlt
    apply hnotTimer
    rw [mem_timerProtectionFailureGuarded_iff_five]
    exact ⟨seedFive, hseedFive, hguard, not_lt.mp hnotlt⟩
  have hfuture :
      ((four + protectionHorizon n : ℕ) : WithTop ℕ) <
        phaseSeedTime init 6 omega := by
    have hshift :
        four + protectionHorizon n ≤
          seedFive + protectionHorizon n :=
      Nat.add_le_add_right hfourSeed _
    have hshiftTop :
        ((four + protectionHorizon n : ℕ) : WithTop ℕ) ≤
          ((seedFive + protectionHorizon n : ℕ) : WithTop ℕ) := by
      exact_mod_cast hshift
    exact hshiftTop.trans_lt hnext
  have hbarrier :
      ((four + protectionHorizon n : ℕ) : WithTop ℕ) <
        firstSixStart init omega := by
    simpa only [firstSixStart, phaseSeedTime] using hfuture
  exact prefix_of_clockHistory_before_firstSix
    init omega seed allThree four (four + protectionHorizon n)
    w H (Nat.le_add_right four _) hbarrier

/-- The second spread produces the genuine finite homogeneous-five start, and
its complete sixteen-work-unit interval lies inside the guarded timer prefix. -/
theorem homogeneousFiveStart_of_not_spread
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {allThree four seedFive : ℕ}
    (hwide : Prefix init omega allThree four
      (four + protectionHorizon n))
    (hseedFive :
      phaseSeedTime init 5 omega = (seedFive : WithTop ℕ))
    (hfourSeed : four ≤ seedFive)
    (hseedDeadline : seedFive ≤ four + logWindow n 4)
    (hnotFive : omega ∉ phaseFiveSpreadFailure init) :
    ∃ five : ℕ,
      homogeneousFiveStart init omega = (five : WithTop ℕ) ∧
      four ≤ five ∧
      five + completionHorizon n ≤ four + protectionHorizon n := by
  have hfirstFive :=
    (phaseSeedTime_eq_iff init 5 omega seedFive).mp hseedFive
  have hgeFive :
      allGE (n := n) 5
        (trace init omega (seedFive + logWindow n 4)) := by
    by_contra hbad
    apply hnotFive
    rw [mem_phaseFiveSpreadFailure_iff init omega]
    exact ⟨seedFive, hseedFive,
      trace_card_eq_population hinput.2.2 seedFive,
      hfirstFive.1, hbad⟩
  have hwork := rowTwoWorkHorizon_le_protection hinput.1
  have hstartOrder := hwide.start_order
  have hendWide :
      seedFive + logWindow n 4 ≤
        four + protectionHorizon n := by
    omega
  have hallFive :
      allPhaseFive
        (trace init omega (seedFive + logWindow n 4)) := by
    intro a ha
    exact le_antisymm
      (hwide.before_six (seedFive + logWindow n 4)
        (by omega) hendWide a ha)
      (hgeFive a ha)
  have hhomogeneousLe :
      homogeneousFiveStart init omega ≤
        ((seedFive + logWindow n 4 : ℕ) : WithTop ℕ) := by
    simpa only [homogeneousFiveStart] using
      (TraceDrain.exitTime_le_iff init allPhaseFive omega
        (seedFive + logWindow n 4)).2
        ⟨seedFive + logWindow n 4, le_rfl, hallFive⟩
  have hfinite : homogeneousFiveStart init omega ≠ ⊤ :=
    ne_top_of_le_ne_top
      (show ((seedFive + logWindow n 4 : ℕ) : WithTop ℕ) ≠ ⊤ from
        WithTop.coe_ne_top) hhomogeneousLe
  obtain ⟨five, hfive⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hstart :
      homogeneousFiveStart init omega = (five : WithTop ℕ) :=
    hfive.symm
  have hfiveDeadline : five ≤ seedFive + logWindow n 4 := by
    rw [hstart] at hhomogeneousLe
    exact WithTop.coe_le_coe.mp hhomogeneousLe
  have hfirstHomogeneous :=
    (exitTime_eq_iff_firstHit init allPhaseFive omega five).mp
      (by simpa only [homogeneousFiveStart] using hstart)
  have hcardPos : 0 < (trace init omega five).card := by
    rw [trace_card_eq_population hinput.2.2 five]
    have hnlarge := (time_population_bounds hinput.1).2
    omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hcardPos
  have hsomeFive : someGE (n := n) 5 (trace init omega five) :=
    ⟨a, ha, (hfirstHomogeneous.1 a ha).ge⟩
  have hseedTop :
      phaseSeedTime init 5 omega ≤ (five : WithTop ℕ) := by
    simpa only [phaseSeedTime] using
      (TraceDrain.exitTime_le_iff init
        (someGE (n := n) 5) omega five).2
        ⟨five, le_rfl, hsomeFive⟩
  rw [hseedFive] at hseedTop
  have hseedFiveLe : seedFive ≤ five :=
    WithTop.coe_le_coe.mp hseedTop
  exact ⟨five, hstart, hfourSeed.trans hseedFiveLe, by omega⟩

/-- The N16 adjacent-class floor supplies the useful-Main field of every
completion gate.  Phase equality follows from the homogeneous-five start,
phase monotonicity, and the guarded phase-6 barrier. -/
theorem completionGate_of_direct_prefix
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hentry : AsyncEntry init omega seed allThree)
    (hwide : Prefix init omega allThree four
      (four + protectionHorizon n))
    (hseed : LateSamplingSeedReceipt init
      (timeMainCount (trace init omega seed)) ell.val sigma
      (trace init omega four))
    (hstart : homogeneousFiveStart init omega = (five : WithTop ℕ))
    (hfourFive : four ≤ five)
    (hfiveWindow :
      five + completionHorizon n ≤ four + protectionHorizon n)
    (v : ℕ) (hv : v ≤ completionHorizon n) :
    CompletionGate n (trace init omega (five + v)) := by
  have hfiveHit :=
    (exitTime_eq_iff_firstHit init allPhaseFive omega five).mp
      (by simpa only [homogeneousFiveStart] using hstart)
  have htWide : five + v ≤ four + protectionHorizon n := by
    omega
  have hstartOrder := hwide.start_order
  have hphaseLower :=
    phase_lower_reachable 5
      (trace init omega five) (trace init omega (five + v))
      (trace_reachable init omega (Nat.le_add_right five v))
      (fun a ha => (hfiveHit.1 a ha).ge)
  have hphaseFive :
      ∀ a ∈ trace init omega (five + v), a.phase.val = 5 := by
    intro a ha
    exact le_antisymm
      (hwide.before_six (five + v) (by omega) htWide a ha)
      (hphaseLower a ha)
  have hclassUseful :
      classCount (indexClass (adjacentIndices ell hell))
          (labelsAt init omega (five + v)) ≤
        usefulMainCount (trace init omega (five + v)) := by
    have hle := adjacentClassCount_le_usefulMainCount
      ell hell (labelsAt init omega (five + v))
    have hcfg : PairLog.labelCfg (labelsAt init omega (five + v)) =
        trace init omega (five + v) :=
      PairLog.labelsAt_config init omega (five + v)
    rw [hcfg] at hle
    exact hle
  have hdensity := strongSeedDensity_of_asyncEntry hentry
  have hmains := hdensity.mains_lower
  have huseful :
      296 * n ≤
        3125 * usefulMainCount (trace init omega (five + v)) := by
    rcases hseed.near_credit with hsmall | hcredit
    · have hfloor := first_branch_global_floor_at
        hinput.2.1 hell hwide hseed (by omega) htWide hsmall
      omega
    · have hfloor := credit_branch_global_floor_at
        hell hwide hseed (by omega) htWide hcredit
      omega
  exact
    { population := trace_card_eq_population hinput.2.2 (five + v)
      phase_five := hphaseFive
      useful_floor := huseful }

/-- Internal data produced before choosing the consumer-facing snapshot. -/
structure DirectCompletionData
    (init : InputCfg n) (omega : InputLog n)
    (seed allThree four : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (sigma : Sign) (five completed : ℕ) : Prop where
  wide : Prefix init omega allThree four
    (four + protectionHorizon n)
  completion : CompletionReceipt init omega allThree four five completed
    (fun _ : InputCfg n => True)
  fixed : FixedRowTwoHorizon init omega allThree four completed
    (protectionHorizon n)

/-- Items 1 and 2: direct construction of a completion receipt with the trivial
snapshot, on the complement of the four existing original-law failures. -/
theorem directCompletionData_of_not_failure
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n} {seed allThree four : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hhistory : successfulHistory (reviewedStageEvents n init)
      omega seed allThree four)
    (hseed : LateSamplingSeedReceipt init
      (timeMainCount (trace init omega seed)) ell.val sigma
      (trace init omega four))
    (hgood : omega ∉ fixedRowTwoHorizonProductionFailure init) :
    ∃ five completed : ℕ,
      DirectCompletionData init omega seed allThree four ell sigma
        five completed := by
  have hentry := asyncEntry_of_successfulHistory hhistory
  have hfixedGood : omega ∉ fixedRowTwoHorizonFailure init :=
    fun h => hgood (Or.inl h)
  have hnotTimer : omega ∉ timerProtectionFailureGuarded init 5 :=
    fun h => hfixedGood (Or.inl h)
  have hnotFour : omega ∉ phaseFourSpreadFailure init :=
    fun h => hfixedGood (Or.inr (Or.inl h))
  have hnotFive : omega ∉ phaseFiveSpreadFailure init :=
    fun h => hfixedGood (Or.inr (Or.inr h))
  have hnotCompletion : omega ∉ completionFailure init n :=
    fun h => hgood (Or.inr h)
  obtain ⟨seedFive, hseedFive, hallSeed, hfourSeed,
      hseedDeadline⟩ :=
    phaseFiveSeed_of_successfulHistory hinput ell hell sigma
      hhistory hseed hnotFour
  have hwide := widePrefix_of_successfulHistory
    hhistory hseedFive hallSeed hfourSeed hnotTimer
  obtain ⟨five, hstart, hfourFive, hfiveWindow⟩ :=
    homogeneousFiveStart_of_not_spread hinput hwide hseedFive
      hfourSeed hseedDeadline hnotFive
  have hgates :
      ∀ v, v ≤ completionHorizon n →
        CompletionGate n (trace init omega (five + v)) := by
    intro v hv
    exact completionGate_of_direct_prefix hinput ell hell sigma
      hentry hwide hseed hstart hfourFive hfiveWindow v hv
  have hnotFrom : omega ∉ completionFailureFrom init five n := by
    intro hbad
    exact hnotCompletion ⟨five, hstart, hbad⟩
  have hpaths :
      ∀ u, five ≤ u → u ≤ five + completionHorizon n →
        Prefix init omega allThree four u := by
    intro u hfiveU huEnd
    exact prefix_restrict_endpoint hwide
      (by omega) (huEnd.trans hfiveWindow)
  obtain ⟨completed, hcompletion⟩ :=
    completionReceipt_of_no_failure
      init omega allThree four five
      (fun _ : InputCfg n => True)
      hstart hgates hnotFrom hpaths
      (by
        intro u hfiveU huEnd htime
        trivial)
  have hcompletedWide :
      completed ≤ four + protectionHorizon n :=
    hcompletion.within_sixteen.trans hfiveWindow
  have hfixed :
      FixedRowTwoHorizon init omega allThree four completed
        (protectionHorizon n) :=
    { path := hwide
      completed_le := hcompletedWide }
  exact ⟨five, completed,
    { wide := hwide
      completion := hcompletion
      fixed := hfixed }⟩

/-- The four original-law charges needed for the old existential snapshot. -/
noncomputable def strongReceiptCharge (n : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal
      (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
    (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) +
      ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3))) +
  ENNReal.ofReal
    (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ)))

/-- Direct original-law bound for the four-event producer union. -/
theorem law_fixedStrongReceiptFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (fixedRowTwoHorizonProductionFailure init) ≤
      strongReceiptCharge n := by
  simpa only [strongReceiptCharge] using
    (law_fixedRowTwoHorizonProductionFailure_tail init hinput)

/-- The earlier existential predicate is produced with `Snapshot := True`; no row-two
threshold charge is needed for this existential. -/
theorem smallBranchReceiptAt_of_not_failure
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n} {seed allThree four : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hhistory : successfulHistory (reviewedStageEvents n init)
      omega seed allThree four)
    (hseed : LateSamplingSeedReceipt init
      (timeMainCount (trace init omega seed)) ell.val sigma
      (trace init omega four))
    (hgood : omega ∉ fixedRowTwoHorizonProductionFailure init) :
    SmallBranchReceiptAt init omega seed allThree four := by
  have hentry := asyncEntry_of_successfulHistory hhistory
  obtain ⟨five, completed, data⟩ := directCompletionData_of_not_failure
    hinput ell hell sigma hhistory hseed hgood
  have hstrong :
      StrongSeedReceipt init omega seed allThree four
        five completed
        (timeMainCount (trace init omega seed))
        (clockCount (trace init omega seed))
        (StageEventSpec.reserveCount (trace init omega seed))
        (fun _ : InputCfg n => True) :=
    strongSeedReceipt_of_asyncEntry_completion_counts
      hentry data.completion
  exact ⟨ell.val, sigma, five, completed,
    (fun _ : InputCfg n => True), hseed, hstrong⟩

/-- The remaining event is covered by the four concrete original-law
failures. -/
theorem smallStrongReceiptMissing_subset_productionFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    smallStrongReceiptMissing init ⊆
      fixedRowTwoHorizonProductionFailure init := by
  intro omega hbad
  rw [mem_smallStrongReceiptMissing_iff init omega] at hbad
  obtain ⟨seed, allThree, four, hhistory, hnonzero, hgap,
    ⟨ellNat, sigma, hseed⟩, hmissing⟩ := hbad
  by_contra hgood
  let ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1) :=
    ⟨ellNat, by
      have hupper := hseed.toSmallReadout.levelUpper
      omega⟩
  have hell :
      ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n := by
    simpa only [ell] using hseed.toSmallReadout.levelUpper
  have hseedFin :
      LateSamplingSeedReceipt init
        (timeMainCount (trace init omega seed)) ell.val sigma
        (trace init omega four) := by
    simpa only [ell] using hseed
  exact hmissing
    (smallBranchReceiptAt_of_not_failure hinput ell hell sigma
      hhistory hseedFin hgood)

/-- Item 4, first law statement: the formerly open event now has a closed
original-law bound. -/
theorem law_smallStrongReceiptMissing_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (smallStrongReceiptMissing init) ≤
      strongReceiptCharge n := by
  exact
    (measure_mono
      (smallStrongReceiptMissing_subset_productionFailure init hinput)).trans
      (law_fixedStrongReceiptFailure init hinput)

/-! ## Fixed completed row-two snapshot -/

/-- One fixed-level repaired row-two event; inadmissible levels contribute the
empty set. -/
noncomputable def selectedRowTwoThresholdFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    Set (InputLog n) :=
  if hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n then
    rowTwoThresholdFailure init ell hell (protectionHorizon n)
  else ∅

/-- Finite union needed because the N16 level is selected from the observed
successful history. -/
def anyRowTwoThresholdFailure
    (init : InputCfg n) : Set (InputLog n) :=
  ⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
    selectedRowTwoThresholdFailure init ell

/-- Explicit finite-union charge. -/
noncomputable def selectedLevelRowTwoCharge (n : ℕ) : ℝ≥0∞ :=
  ((PhaseThreeModel.Numeric.hourIndex n + 1 : ℕ) : ℝ≥0∞) *
    ENNReal.ofReal (Real.rpow (n : ℝ) (-190))

/-- A chosen admissible repaired row belongs to the finite selected-level
union. -/
theorem rowTwoThresholdFailure_mem_any
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    {omega : InputLog n}
    (h : omega ∈ rowTwoThresholdFailure init ell hell
      (protectionHorizon n)) :
    omega ∈ anyRowTwoThresholdFailure init := by
  apply Set.mem_iUnion.mpr
  refine ⟨ell, ?_⟩
  simpa [selectedRowTwoThresholdFailure, hell] using h

/-- Complement form used by the pathwise producer. -/
theorem not_rowTwoThresholdFailure_of_not_any
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    {omega : InputLog n}
    (hgood : omega ∉ anyRowTwoThresholdFailure init) :
    omega ∉ rowTwoThresholdFailure init ell hell
      (protectionHorizon n) := by
  intro hbad
  exact hgood (rowTwoThresholdFailure_mem_any init ell hell hbad)

/-- Each selected level has the existing unconditional repaired-row charge. -/
theorem law_selectedRowTwoThresholdFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init (selectedRowTwoThresholdFailure init ell) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) := by
  classical
  by_cases hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n
  · rw [selectedRowTwoThresholdFailure, dif_pos hell]
    exact law_rowTwoThresholdFailure_inverse_power
      init hinput.2.2 hinput.1 ell hell (protectionHorizon n)
  · rw [selectedRowTwoThresholdFailure, dif_neg hell, measure_empty]
    exact zero_le

/-- The selected N16 level costs only the explicit finite sum of the fixed-level
original-law charges. -/
theorem law_anyRowTwoThresholdFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (anyRowTwoThresholdFailure init) ≤
      selectedLevelRowTwoCharge n := by
  calc
    law init (anyRowTwoThresholdFailure init) ≤
        ∑' ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
          law init (selectedRowTwoThresholdFailure init ell) :=
      measure_iUnion_le _
    _ ≤ ∑' _ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
        ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) :=
      ENNReal.tsum_le_tsum
        (law_selectedRowTwoThresholdFailure init hinput)
    _ = selectedLevelRowTwoCharge n := by
      unfold selectedLevelRowTwoCharge
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]

/-- The strengthened consumer-facing receipt has the exact row-two snapshot,
not an arbitrary existential predicate. -/
def StrongSmallBranchReceiptAt
    (init : InputCfg n) (omega : InputLog n)
    (seed allThree four : ℕ) : Prop :=
  ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
    ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
    ∃ sigma : Sign, ∃ five completed : ℕ,
      LateSamplingSeedReceipt init
          (timeMainCount (trace init omega seed)) ell.val sigma
          (trace init omega four) ∧
        StrongSeedReceipt init omega seed allThree four five completed
          (timeMainCount (trace init omega seed))
          (clockCount (trace init omega seed))
          (StageEventSpec.reserveCount (trace init omega seed))
          (LateSamplingCorrectedFuelProducer.CompletedRowTwoFuelSnapshot ell sigma
            (timeMainCount (trace init omega seed))
            (StageEventSpec.reserveCount (trace init omega seed)))

/-- Forgetting the fixed snapshot recovers the earlier existential predicate. -/
theorem StrongSmallBranchReceiptAt.toSmallBranchReceiptAt
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four : ℕ}
    (h : StrongSmallBranchReceiptAt init omega seed allThree four) :
    SmallBranchReceiptAt init omega seed allThree four := by
  obtain ⟨ell, hell, sigma, five, completed, hseed, hstrong⟩ := h
  exact ⟨ell.val, sigma, five, completed,
    LateSamplingCorrectedFuelProducer.CompletedRowTwoFuelSnapshot ell sigma
      (timeMainCount (trace init omega seed))
      (StageEventSpec.reserveCount (trace init omega seed)),
    hseed, hstrong⟩

/-- The strengthened producer union adds only the finite selected-level row. -/
def strongSnapshotProductionFailure
    (init : InputCfg n) : Set (InputLog n) :=
  fixedRowTwoHorizonProductionFailure init ∪
    anyRowTwoThresholdFailure init

noncomputable def strongSnapshotCharge (n : ℕ) : ℝ≥0∞ :=
  strongReceiptCharge n + selectedLevelRowTwoCharge n

/-- Exact original-law bound for the strengthened producer. -/
theorem law_strongSnapshotProductionFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (strongSnapshotProductionFailure init) ≤
      strongSnapshotCharge n := by
  unfold strongSnapshotProductionFailure strongSnapshotCharge
  exact (measure_union_le _ _).trans
    (add_le_add
      (law_fixedStrongReceiptFailure init hinput)
      (law_anyRowTwoThresholdFailure init hinput))

/-- Item 3: construct the receipt first with `True`, prove the completed
row-two snapshot from the repaired row complement, then replace the snapshot
field and rebuild the strong receipt. -/
theorem strongSmallBranchReceiptAt_of_not_failure
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n} {seed allThree four : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hhistory : successfulHistory (reviewedStageEvents n init)
      omega seed allThree four)
    (hseed : LateSamplingSeedReceipt init
      (timeMainCount (trace init omega seed)) ell.val sigma
      (trace init omega four))
    (hgood : omega ∉ strongSnapshotProductionFailure init) :
    StrongSmallBranchReceiptAt init omega seed allThree four := by
  have hbase : omega ∉ fixedRowTwoHorizonProductionFailure init :=
    fun h => hgood (Or.inl h)
  have hany : omega ∉ anyRowTwoThresholdFailure init :=
    fun h => hgood (Or.inr h)
  have hnotRow :=
    not_rowTwoThresholdFailure_of_not_any init ell hell hany
  have hentry := asyncEntry_of_successfulHistory hhistory
  obtain ⟨five, completed, data⟩ := directCompletionData_of_not_failure
    hinput ell hell sigma hhistory hseed hbase
  have hstrongTrue :
      StrongSeedReceipt init omega seed allThree four
        five completed
        (timeMainCount (trace init omega seed))
        (clockCount (trace init omega seed))
        (StageEventSpec.reserveCount (trace init omega seed))
        (fun _ : InputCfg n => True) :=
    strongSeedReceipt_of_asyncEntry_completion_counts
      hentry data.completion
  have hsnapshotRaw :=
    completedRowTwoFuelSnapshot_of_good_path
      hinput.2.1 hinput.1 ell hell sigma
      hstrongTrue hseed data.fixed hnotRow
  have hsnapshot :
      LateSamplingCorrectedFuelProducer.CompletedRowTwoFuelSnapshot ell sigma
        (timeMainCount (trace init omega seed))
        (StageEventSpec.reserveCount (trace init omega seed))
        (trace init omega completed) := by
    simpa only [hstrongTrue.completed_main,
      hstrongTrue.completed_reserve] using hsnapshotRaw
  have hcompletionFixed :
      CompletionReceipt init omega allThree four
        five completed
        (LateSamplingCorrectedFuelProducer.CompletedRowTwoFuelSnapshot ell sigma
          (timeMainCount (trace init omega seed))
          (StageEventSpec.reserveCount (trace init omega seed))) :=
    { observed_path := data.completion.observed_path
      five_start := data.completion.five_start
      completed_at := data.completion.completed_at
      start_le := data.completion.start_le
      within_sixteen := data.completion.within_sixteen
      complete := data.completion.complete
      snapshot := hsnapshot }
  have hstrongFixed :
      StrongSeedReceipt init omega seed allThree four
        five completed
        (timeMainCount (trace init omega seed))
        (clockCount (trace init omega seed))
        (StageEventSpec.reserveCount (trace init omega seed))
        (LateSamplingCorrectedFuelProducer.CompletedRowTwoFuelSnapshot ell sigma
          (timeMainCount (trace init omega seed))
          (StageEventSpec.reserveCount (trace init omega seed))) :=
    strongSeedReceipt_of_asyncEntry_completion_counts
      hentry hcompletionFixed
  exact ⟨ell, hell, sigma, five, completed,
    hseed, hstrongFixed⟩

/-! ## Closed small-row producer and consumer -/

/-- All failures needed to produce the strengthened receipt from a small
history: N16, the two spreads/timer/completion package, and the selected-level
row-two family. -/
def smallRowTwoSnapshotProductionFailure
    (init : InputCfg n) : Set (InputLog n) :=
  lateSamplingSeedProducerFailure init ∪
    strongSnapshotProductionFailure init

noncomputable def nSixteenReceiptCharge (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (2 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 4 +
      Real.rpow (n : ℝ) (-(207 / 100 : ℝ)))

noncomputable def smallRowTwoSnapshotCharge (n : ℕ) : ℝ≥0∞ :=
  nSixteenReceiptCharge n + strongSnapshotCharge n

/-- Item 4, pathwise strengthened producer on the strict-small-gap event. -/
theorem exists_strongSmallBranchReceiptAt_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ smallRowTwoSnapshotProductionFailure init) :
    ∃ seed allThree four : ℕ,
      successfulHistory (reviewedStageEvents n init)
          omega seed allThree four ∧
        StrongSmallBranchReceiptAt init omega seed allThree four := by
  obtain ⟨seed, allThree, four, hhistory, hnonzero, hgap⟩ := hsmall
  have hnotSeed : omega ∉ lateSamplingSeedProducerFailure init :=
    fun h => hgood (Or.inl h)
  have hnotSnapshot : omega ∉ strongSnapshotProductionFailure init :=
    fun h => hgood (Or.inr h)
  have hseedExists :
      ∃ ellNat : ℕ, ∃ sigma : Sign,
        LateSamplingSeedReceipt init
          (timeMainCount (trace init omega seed)) ellNat sigma
          (trace init omega four) := by
    by_contra hnone
    apply hnotSeed
    rw [mem_lateSamplingSeedProducerFailure_iff init omega]
    exact ⟨seed, allThree, four, hhistory,
      hnonzero, hgap, hnone⟩
  obtain ⟨ellNat, sigma, hseed⟩ := hseedExists
  let ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1) :=
    ⟨ellNat, by
      have hupper := hseed.toSmallReadout.levelUpper
      omega⟩
  have hell :
      ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n := by
    simpa only [ell] using hseed.toSmallReadout.levelUpper
  have hseedFin :
      LateSamplingSeedReceipt init
        (timeMainCount (trace init omega seed)) ell.val sigma
        (trace init omega four) := by
    simpa only [ell] using hseed
  exact ⟨seed, allThree, four, hhistory,
    strongSmallBranchReceiptAt_of_not_failure
      hinput ell hell sigma hhistory hseedFin hnotSnapshot⟩

/-- Unconditional charge for the strengthened pathwise producer. -/
theorem law_smallRowTwoSnapshotProductionFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (smallRowTwoSnapshotProductionFailure init) ≤
      smallRowTwoSnapshotCharge n := by
  unfold smallRowTwoSnapshotProductionFailure
  exact (measure_union_le _ _).trans
    (add_le_add
      (by
        simpa only [nSixteenReceiptCharge] using
          (law_lateSamplingSeedProducerFailure_closed init hinput))
      (law_strongSnapshotProductionFailure init hinput))

/-- The basic closed failure union for `smallRowTwoReceiptMissing` does
not need the selected-level row-two family. -/
def smallRowTwoReceiptClosedFailure
    (init : InputCfg n) : Set (InputLog n) :=
  lateSamplingSeedProducerFailure init ∪
    fixedRowTwoHorizonProductionFailure init

noncomputable def smallRowTwoReceiptCharge (n : ℕ) : ℝ≥0∞ :=
  nSixteenReceiptCharge n + strongReceiptCharge n

/-- Deterministic cover with no open summand. -/
theorem smallRowTwoReceiptMissing_subset_closedFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    smallRowTwoReceiptMissing init ⊆
      smallRowTwoReceiptClosedFailure init := by
  intro omega hbad
  rcases smallRowTwoReceiptMissing_cover init hbad with hseed | hstrong
  · exact Or.inl hseed
  · exact Or.inr
      (smallStrongReceiptMissing_subset_productionFailure
        init hinput hstrong)

/-- Item 4, the composed theorem: the open probability summand is gone. -/
theorem law_smallRowTwoReceiptMissing_closed
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (smallRowTwoReceiptMissing init) ≤
      smallRowTwoReceiptCharge n := by
  calc
    law init (smallRowTwoReceiptMissing init) ≤
        law init (smallRowTwoReceiptClosedFailure init) :=
      measure_mono
        (smallRowTwoReceiptMissing_subset_closedFailure init hinput)
    _ ≤ law init (lateSamplingSeedProducerFailure init) +
        law init (fixedRowTwoHorizonProductionFailure init) :=
      measure_union_le _ _
    _ ≤ nSixteenReceiptCharge n + strongReceiptCharge n :=
      add_le_add
        (by
          simpa only [nSixteenReceiptCharge] using
            (law_lateSamplingSeedProducerFailure_closed init hinput))
        (law_fixedStrongReceiptFailure init hinput)
    _ = smallRowTwoReceiptCharge n := rfl

/-- The strengthened receipt feeds the completed protected consumer with
no carried receipt premise. -/
theorem exists_completedFuelLedger_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ smallRowTwoSnapshotProductionFailure init) :
    ∃ seed allThree four : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma : Sign, ∃ five completed : ℕ,
        successfulHistory (reviewedStageEvents n init)
            omega seed allThree four ∧
          LateSamplingSeedReceipt init
            (timeMainCount (trace init omega seed)) ell.val sigma
            (trace init omega four) ∧
          StrongSeedReceipt init omega seed allThree four five completed
            (timeMainCount (trace init omega seed))
            (clockCount (trace init omega seed))
            (StageEventSpec.reserveCount (trace init omega seed))
            (LateSamplingCorrectedFuelProducer.CompletedRowTwoFuelSnapshot ell sigma
              (timeMainCount (trace init omega seed))
              (StageEventSpec.reserveCount (trace init omega seed))) ∧
          Phase6FuelLedger.TwoLevelFuelLedger
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
            ell (LatePotential.fuelFloor n)
            (trace init omega completed) := by
  obtain ⟨seed, allThree, four, hhistory, hreceipt⟩ :=
    exists_strongSmallBranchReceiptAt_of_smallHistory
      hinput hsmall hgood
  obtain ⟨ell, hell, sigma, five, completed,
    hseed, hstrong⟩ := hreceipt
  have hnotFixed :
      omega ∉ fixedRowTwoHorizonProductionFailure init :=
    fun h => hgood (Or.inr (Or.inl h))
  have hnotAny : omega ∉ anyRowTwoThresholdFailure init :=
    fun h => hgood (Or.inr (Or.inr h))
  have hnotRow :=
    not_rowTwoThresholdFailure_of_not_any init ell hell hnotAny
  have hprotected :
      omega ∉ completedProtectedFuelFailure init ell hell := by
    rintro (hfixed | hrow)
    · exact hnotFixed hfixed
    · exact hnotRow hrow
  have hledger :=
    twoLevelFuelLedger_of_completed_protected_good_path
      hinput ell hell sigma hstrong hseed hprotected
  exact ⟨seed, allThree, four, ell, hell, sigma, five, completed,
    hhistory, hseed, hstrong, hledger⟩

/-!
THEOREM LIST
* `asyncEntry_of_successfulHistory`
* `clockHistory_of_successfulHistory`
* `phaseFiveSeed_of_successfulHistory`
* `widePrefix_of_successfulHistory`
* `homogeneousFiveStart_of_not_spread`
* `completionGate_of_direct_prefix`
* `DirectCompletionData`
* `directCompletionData_of_not_failure`
* `law_fixedStrongReceiptFailure`
* `smallBranchReceiptAt_of_not_failure`
* `smallStrongReceiptMissing_subset_productionFailure`
* `law_smallStrongReceiptMissing_tail`
* `selectedRowTwoThresholdFailure`
* `anyRowTwoThresholdFailure`
* `law_anyRowTwoThresholdFailure`
* `StrongSmallBranchReceiptAt`
* `StrongSmallBranchReceiptAt.toSmallBranchReceiptAt`
* `strongSmallBranchReceiptAt_of_not_failure`
* `exists_strongSmallBranchReceiptAt_of_smallHistory`
* `law_smallRowTwoSnapshotProductionFailure`
* `smallRowTwoReceiptMissing_subset_closedFailure`
* `law_smallRowTwoReceiptMissing_closed`
* `exists_completedFuelLedger_of_smallHistory`

CLOSES
* Item 1: direct `AsyncEntry` and `ClockHistory` extraction from the successful
  history.
* Item 2: non-circular first-five, guarded prefix, homogeneous-five start,
  all completion gates, local completion-failure complement, completion time,
  actual role counts, and strong density.
* Item 3: a receipt with the exact `LateSamplingCorrectedFuelProducer.CompletedRowTwoFuelSnapshot`, obtained by
  staging through `Snapshot := True` and the repaired row-two complement.
* Item 4: pathwise strengthened production, an explicit original-law charge
  for `smallStrongReceiptMissing`, a closed `smallRowTwoReceiptMissing` bound,
  and the completed protected `TwoLevelFuelLedger` consumer with no receipt
  hypothesis.

UNFINISHED
* No mathematical or probabilistic premise remains open in this item.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingStrongReceiptProducer

end
