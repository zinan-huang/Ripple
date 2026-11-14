-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingFixedRowTwoHorizon.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCompletedFuelSnapshot
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerRouteProof
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoThresholds

/-!
# The fixed row-two horizon from the genuine late stopping times

The only stochastic failures introduced here are the guarded phase-5 timer
failure and the two genuine stopping-time threshold spreads.  The actual
completion time is carried by `StrongSeedReceipt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingFixedRowTwoHorizon

open TimeTheorem PairLog StageEventSpec PhaseOneDrainStopping
open LateF6OriginalLaw LateF6Acceptance LateF6Hazards
open LateAcceptedRectangleHazard
open LateTimerPrefixScalar LateTimerProtectionOriginalLaw
open LateTimerProtectionGuarded
open LateSamplingCompletion LateSamplingSeedReceipt
open LateSamplingStrongSeedReceipt LateSamplingRowTwoChoices
open LateSamplingCompletedFuelSnapshot
open PhaseTwoThresholds

variable {n : ℕ}

/-- Failure of threshold 4 to cover the population in four work units from
its genuine first seed. -/
def phaseFourSpreadFailure (init : InputCfg n) : Set (InputLog n) :=
  thresholdFailureAt init n 4 (logWindow n 4) (firstFourStart init)

/-- Failure of threshold 5 to cover the population in four work units from
its genuine first seed. -/
def phaseFiveSpreadFailure (init : InputCfg n) : Set (InputLog n) :=
  thresholdFailureAt init n 5 (logWindow n 4) (phaseSeedTime init 5)

@[simp] theorem mem_phaseFourSpreadFailure_iff
    (init : InputCfg n) (omega : InputLog n) :
    omega ∈ phaseFourSpreadFailure init ↔
      ∃ four : ℕ,
        firstFourStart init omega = (four : WithTop ℕ) ∧
        (trace init omega four).card = n ∧
        (∃ a ∈ trace init omega four, 4 ≤ a.phase.val) ∧
        ¬ ∀ a ∈ trace init omega (four + logWindow n 4),
          4 ≤ a.phase.val :=
  Iff.rfl

@[simp] theorem mem_phaseFiveSpreadFailure_iff
    (init : InputCfg n) (omega : InputLog n) :
    omega ∈ phaseFiveSpreadFailure init ↔
      ∃ seed : ℕ,
        phaseSeedTime init 5 omega = (seed : WithTop ℕ) ∧
        (trace init omega seed).card = n ∧
        (∃ a ∈ trace init omega seed, 5 ≤ a.phase.val) ∧
        ¬ ∀ a ∈ trace init omega (seed + logWindow n 4),
          5 ≤ a.phase.val :=
  Iff.rfl

@[simp] theorem mem_timerProtectionFailureGuarded_iff_five
    (init : InputCfg n) (omega : InputLog n) :
    omega ∈ timerProtectionFailureGuarded init 5 ↔
      ∃ seed : ℕ,
        phaseSeedTime init 5 omega = (seed : WithTop ℕ) ∧
        allThreeStart init omega < (seed : WithTop ℕ) ∧
        phaseSeedTime init 6 omega ≤
          ((seed + protectionHorizon n : ℕ) : WithTop ℕ) :=
  Iff.rfl

@[simp] theorem mem_earlySeedBeforeAllThree_iff_five
    (init : InputCfg n) (omega : InputLog n) :
    omega ∈ earlySeedBeforeAllThree init 5 ↔
      ∃ seed : ℕ,
        phaseSeedTime init 5 omega = (seed : WithTop ℕ) ∧
        (seed : WithTop ℕ) ≤ allThreeStart init omega :=
  Iff.rfl

/-- The three local failures that can prevent the fixed prefix once the
strong receipt and N16 seed receipt are carried. -/
def fixedRowTwoHorizonFailure (init : InputCfg n) : Set (InputLog n) :=
  timerProtectionFailureGuarded init 5 ∪
    (phaseFourSpreadFailure init ∪ phaseFiveSpreadFailure init)

/-- The probability package also records the already available completion
failure.  The deterministic construction below uses the completion witness
inside `StrongSeedReceipt`; this extra set is for global accounting. -/
def fixedRowTwoHorizonProductionFailure
    (init : InputCfg n) : Set (InputLog n) :=
  fixedRowTwoHorizonFailure init ∪ completionFailure init n

/-- A single name for the upstream seam that would have to produce both the
strong completion receipt and its matching N16 seed receipt.  No numerical
bound is claimed until the current open `completionBase` producer is available. -/
def rowTwoReceiptMissing (init : InputCfg n) : Set (InputLog n) :=
  {omega | ¬ ∃ seed allThree four five completed M C R ell,
    ∃ sigma : Sign,
    ∃ Snapshot : InputCfg n → Prop,
      StrongSeedReceipt init omega seed allThree four five completed
          M C R Snapshot ∧
        LateSamplingSeedReceipt init M ell sigma
          (trace init omega four)}

private theorem label_mem_trace
    (init : InputCfg n) (omega : InputLog n) (u : ℕ)
    (i : Fin init.card) :
    labelsAt init omega u i ∈ trace init omega u := by
  rw [← PairLog.labelsAt_config init omega u]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

private theorem trace_card_eq_population
    {init : InputCfg n} {omega : InputLog n}
    (hcard : init.card = n) (u : ℕ) :
    (trace init omega u).card = n := by
  have hreach :
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega u) := by
    simpa only [TimeTheorem.trace_zero] using
      (TimeTheorem.trace_reachable init omega
        (s := 0) (t := u) (Nat.zero_le u))
  exact (Protocol.reachable_card_eq hreach).trans hcard

private theorem firstFour_hit
    {init : InputCfg n} {omega : InputLog n}
    {allThree four endpoint : ℕ}
    (hpath : Prefix init omega allThree four endpoint) :
    firstHit (someGE (n := n) 4) (trace init omega) four := by
  apply (exitTime_eq_iff_firstHit
    init (someGE (n := n) 4) omega four).mp
  simpa only [firstFourStart] using hpath.four_start

/-- A genuine first-four prefix is strict at its left endpoint: at
`allThree` every phase equals 3, whereas at `four` some phase is at least 4. -/
theorem prefix_allThree_lt_firstFour
    {init : InputCfg n} {omega : InputLog n}
    {allThree four endpoint : ℕ}
    (hpath : Prefix init omega allThree four endpoint) :
    allThree < four := by
  have hne : allThree ≠ four := by
    intro heq
    subst four
    obtain ⟨a, ha, hge⟩ := (firstFour_hit hpath).1
    have hthree := hpath.all_three a ha
    omega
  have hord := hpath.start_order
  omega

/-- Item 1, pathwise and with no additional exceptional event.  A phase-5
seed is already a threshold-4 witness, so it cannot occur at or before the
all-three time of a genuine strong receipt. -/
theorem StrongSeedReceipt.not_earlySeedBeforeAllThree
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    omega ∉ earlySeedBeforeAllThree init 5 := by
  rw [mem_earlySeedBeforeAllThree_iff_five]
  rintro ⟨seedFive, hseedFive, hearly⟩
  have hfirstFive :=
    (phaseSeedTime_eq_iff init 5 omega seedFive).mp hseedFive
  have hfourTop :
      firstFourStart init omega ≤ (seedFive : WithTop ℕ) := by
    simpa only [firstFourStart] using
      (TraceDrain.exitTime_le_iff init
        (someGE (n := n) 4) omega seedFive).2
        ⟨seedFive, le_rfl, by
          rcases hfirstFive.1 with ⟨a, ha, hfive⟩
          exact ⟨a, ha, by omega⟩⟩
  have hpath := hstrong.completion.observed_path
  rw [hpath.four_start] at hfourTop
  have hfourLe : four ≤ seedFive := WithTop.coe_le_coe.mp hfourTop
  rw [hpath.all_start] at hearly
  have hseedLe : seedFive ≤ allThree := WithTop.coe_le_coe.mp hearly
  have hallFour := prefix_allThree_lt_firstFour hpath
  omega

/-- The early event is therefore charged entirely to failure to produce the
upstream receipts, not to the guarded timer estimate. -/
theorem earlySeedBeforeAllThree_subset_rowTwoReceiptMissing
    (init : InputCfg n) :
    earlySeedBeforeAllThree init 5 ⊆ rowTwoReceiptMissing init := by
  intro omega hearly
  change ¬ ∃ seed allThree four five completed M C R ell,
    ∃ sigma : Sign,
    ∃ Snapshot : InputCfg n → Prop,
      StrongSeedReceipt init omega seed allThree four five completed
          M C R Snapshot ∧
        LateSamplingSeedReceipt init M ell sigma
          (trace init omega four)
  rintro ⟨seed, allThree, four, five, completed, M, C, R, ell,
    sigma, Snapshot, hstrong, _hseed⟩
  exact StrongSeedReceipt.not_earlySeedBeforeAllThree hstrong hearly

/-- The exact law bound presently available for the early event.  A numeric
right-hand side is supplied as soon as the named upstream producer is closed. -/
theorem law_earlySeedBeforeAllThree_le_rowTwoReceiptMissing
    (init : InputCfg n) :
    law init (earlySeedBeforeAllThree init 5) ≤
      law init (rowTwoReceiptMissing init) :=
  measure_mono (earlySeedBeforeAllThree_subset_rowTwoReceiptMissing init)

/-- The rounded paper work budget: two four-unit spreads and the sixteen-unit
sampling drain fit strictly inside the 26.5-unit timer protection window. -/
theorem rowTwoWorkHorizon_le_protection
    (hn : timePopulationThreshold ≤ n) :
    logWindow n 4 + logWindow n 4 + completionHorizon n ≤
      protectionHorizon n := by
  obtain ⟨hnpos, hnlog⟩ :=
    ScalarTails.time_population_scalar_bounds hn
  have hnlarge : 40 ≤ n := (time_population_bounds hn).2
  have hnreal : (40 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlarge
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) := by linarith
  have hfour :
      (logWindow n 4 : ℝ) <
        4 * (n : ℝ) * Real.log (n : ℝ) + 1 := by
    unfold logWindow
    exact Nat.ceil_lt_add_one
      (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hlogNonneg)
  have hsixteen :
      (completionHorizon n : ℝ) <
        16 * (n : ℝ) * Real.log (n : ℝ) + 1 := by
    unfold completionHorizon logWindow
    exact Nat.ceil_lt_add_one
      (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hlogNonneg)
  have hprotect :
      (53 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
        (protectionHorizon n : ℝ) := by
    unfold protectionHorizon
    exact Nat.le_ceil _
  have hproduct :
      (4000 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    calc
      (4000 : ℝ) = 40 * 100 := by norm_num
      _ ≤ (n : ℝ) * Real.log (n : ℝ) :=
        mul_le_mul hnreal hnlog (by norm_num) hnpos.le
  have hslack :
      (3 : ℝ) ≤ (5 / 2 : ℝ) *
        ((n : ℝ) * Real.log (n : ℝ)) := by
    nlinarith only [hproduct]
  have hsumUpper :
      ((logWindow n 4 + logWindow n 4 + completionHorizon n : ℕ) : ℝ) <
        24 * (n : ℝ) * Real.log (n : ℝ) + 3 := by
    push_cast
    nlinarith only [hfour, hsixteen]
  have hbudget :
      24 * (n : ℝ) * Real.log (n : ℝ) + 3 ≤
        (53 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ) := by
    nlinarith only [hslack]
  have hcast :
      ((logWindow n 4 + logWindow n 4 + completionHorizon n : ℕ) : ℝ) ≤
        (protectionHorizon n : ℝ) :=
    hsumUpper.le.trans (hbudget.trans hprotect)
  exact_mod_cast hcast

private theorem spread_error_eq_cube (n : ℕ) :
    Real.exp 3 * Real.rpow (n : ℝ) (1 - ((4 : ℕ) : ℝ)) =
      Real.exp 3 / (n : ℝ) ^ 3 := by
  show Real.exp 3 * (n : ℝ) ^ (1 - ((4 : ℕ) : ℝ)) = _
  rw [show (1 : ℝ) - ((4 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast, div_eq_mul_inv]

/-- Original-law threshold-4 spread charge at the genuine first-four time. -/
theorem law_phaseFourSpreadFailure_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseFourSpreadFailure init) ≤
      ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) := by
  have htail :=
    threshold_spread_logWindow_at_past_time
      init hinput 4 (by norm_num) 4
      (firstFourStart init) (firstFourStart_past init)
  simpa only [phaseFourSpreadFailure, spread_error_eq_cube] using htail

/-- Original-law threshold-5 spread charge at its genuine first seed. -/
theorem law_phaseFiveSpreadFailure_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseFiveSpreadFailure init) ≤
      ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) := by
  have htail :=
    threshold_spread_logWindow_at_past_time
      init hinput 5 (by norm_num) 4
      (phaseSeedTime init 5) (phaseSeedTime_past init 5)
  simpa only [phaseFiveSpreadFailure, spread_error_eq_cube] using htail

/-- The complete local original-law charge for constructing the fixed path. -/
theorem law_fixedRowTwoHorizonFailure_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (fixedRowTwoHorizonFailure init) ≤
      ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
        (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) +
          ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3)) := by
  calc
    law init (fixedRowTwoHorizonFailure init) ≤
        law init (timerProtectionFailureGuarded init 5) +
          law init
            (phaseFourSpreadFailure init ∪ phaseFiveSpreadFailure init) :=
      measure_union_le _ _
    _ ≤ law init (timerProtectionFailureGuarded init 5) +
        (law init (phaseFourSpreadFailure init) +
          law init (phaseFiveSpreadFailure init)) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ ≤ ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
        (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) +
          ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3)) :=
      add_le_add
        (LateTimerRouteProof.law_timerProtectionFailureGuarded_tail_of_goodInput
          init hinput 5 ⟨by norm_num, by norm_num⟩)
        (add_le_add
          (law_phaseFourSpreadFailure_tail init hinput)
          (law_phaseFiveSpreadFailure_tail init hinput))

/-- The same package with the completion failure included for the global
row-two union. -/
theorem law_fixedRowTwoHorizonProductionFailure_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (fixedRowTwoHorizonProductionFailure init) ≤
      (ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
        (ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3) +
          ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 3))) +
      ENNReal.ofReal
        (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ))) := by
  exact (measure_union_le _ _).trans
    (add_le_add
      (law_fixedRowTwoHorizonFailure_tail init hinput)
      (law_completion_failure_tail init hinput.1))

/-- The actual first phase-5 seed is finite, occurs after `allThree`, and is
no earlier than the genuine first-four hit. -/
theorem exists_phaseFiveSeed_after_firstFour
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    ∃ seedFive : ℕ,
      phaseSeedTime init 5 omega = (seedFive : WithTop ℕ) ∧
      allThree < seedFive ∧ four ≤ seedFive ∧
      firstHit (someGE (n := n) 5) (trace init omega) seedFive := by
  have hcomplete := hstrong.completion.complete
  have hcardPos : 0 < (trace init omega completed).card := by
    rw [hcomplete.population]
    have hlarge := (time_population_bounds hinput.1).2
    omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hcardPos
  have hsomeFive : someGE (n := n) 5 (trace init omega completed) :=
    ⟨a, ha, (hcomplete.phase_five a ha).ge⟩
  have hseedLe :
      phaseSeedTime init 5 omega ≤ (completed : WithTop ℕ) := by
    simpa only [phaseSeedTime] using
      (TraceDrain.exitTime_le_iff init
        (someGE (n := n) 5) omega completed).2
        ⟨completed, le_rfl, hsomeFive⟩
  have hfinite : phaseSeedTime init 5 omega ≠ ⊤ :=
    ne_top_of_le_ne_top
      (show (completed : WithTop ℕ) ≠ ⊤ from WithTop.coe_ne_top)
      hseedLe
  obtain ⟨seedFive, hseedFive⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have htime :
      phaseSeedTime init 5 omega = (seedFive : WithTop ℕ) :=
    hseedFive.symm
  have hfirstFive := (phaseSeedTime_eq_iff init 5 omega seedFive).mp htime
  have hpath := hstrong.completion.observed_path
  have hfourTop :
      firstFourStart init omega ≤ (seedFive : WithTop ℕ) := by
    simpa only [firstFourStart] using
      (TraceDrain.exitTime_le_iff init
        (someGE (n := n) 4) omega seedFive).2
        ⟨seedFive, le_rfl, by
          rcases hfirstFive.1 with ⟨b, hb, hfive⟩
          exact ⟨b, hb, by omega⟩⟩
  rw [hpath.four_start] at hfourTop
  have hfourLe : four ≤ seedFive := WithTop.coe_le_coe.mp hfourTop
  have hallFour := prefix_allThree_lt_firstFour hpath
  exact ⟨seedFive, htime, hallFour.trans_le hfourLe,
    hfourLe, hfirstFive⟩

/-- Item 2.  Guarded timer protection extends the genuine prefix all the way
to `four + protectionHorizon n`. -/
theorem fixedPrefix_of_not_timerFailure
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hnotTimer : omega ∉ timerProtectionFailureGuarded init 5) :
    Prefix init omega allThree four
      (four + protectionHorizon n) := by
  obtain ⟨seedFive, hseedFive, hallSeed, hfourSeed, _hfirstFive⟩ :=
    exists_phaseFiveSeed_after_firstFour hinput hstrong
  have hpath := hstrong.completion.observed_path
  have hguard :
      allThreeStart init omega < (seedFive : WithTop ℕ) := by
    rw [hpath.all_start]
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
  have hnone :=
    TraceDrain.not_of_lt_exitTime init
      (someGE (n := n) 6) omega
      (four + protectionHorizon n)
      (by simpa only [phaseSeedTime] using hfuture)
  exact
    { all_start := hpath.all_start
      four_start := hpath.four_start
      start_order := hpath.start_order
      observed := Nat.le_add_right four (protectionHorizon n)
      all_three := hpath.all_three
      before_six := by
        intro u hallu huend b hb
        have hnotSome := hnone u huend
        have hnotSix : ¬ 6 ≤ b.phase.val := by
          intro hsix
          exact hnotSome ⟨b, hb, hsix⟩
        omega }

private theorem allFour_at_spread_endpoint
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hnotFour : omega ∉ phaseFourSpreadFailure init) :
    allGE (n := n) 4 (trace init omega (four + logWindow n 4)) := by
  by_contra hbad
  apply hnotFour
  rw [mem_phaseFourSpreadFailure_iff]
  exact ⟨four, hstrong.completion.observed_path.four_start,
    trace_card_eq_population hstrong.population four,
    (firstFour_hit hstrong.completion.observed_path).1, hbad⟩

/-- Item 3, first spread.  The N16 near-credit disjunction gives a positive
adjacent eligible class at the spread endpoint, so threshold 5 has genuinely
seeded by `four + logWindow n 4`. -/
theorem phaseFiveSeed_deadline
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hwide : Prefix init omega allThree four
      (four + protectionHorizon n))
    (hnotFour : omega ∉ phaseFourSpreadFailure init) :
    ∃ seedFive : ℕ,
      phaseSeedTime init 5 omega = (seedFive : WithTop ℕ) ∧
      four ≤ seedFive ∧
      seedFive ≤ four + logWindow n 4 := by
  obtain ⟨seedFive, hseedFive, _hallSeed, hfourSeed, _hfirstFive⟩ :=
    exists_phaseFiveSeed_after_firstFour hinput hstrong
  have hwork := rowTwoWorkHorizon_le_protection hinput.1
  have hend :
      four + logWindow n 4 ≤ four + protectionHorizon n := by
    omega
  have hallFour := allFour_at_spread_endpoint hstrong hnotFour
  have hMpos : 0 < M := by
    have hnlarge := (time_population_bounds hinput.1).2
    have hm := hstrong.density.mains_lower
    omega
  have hclassPos :
      0 < classCount
        (indexClass (adjacentIndices ell hell))
        (labelsAt init omega (four + logWindow n 4)) := by
    rcases hseed.near_credit with hsmall | hcredit
    · have hfloor := first_branch_global_floor_at
        hinput.2.1 hell hwide hseed
        (Nat.le_add_right four _) hend hsmall
      omega
    · have hfloor := credit_branch_global_floor_at
        hell hwide hseed (Nat.le_add_right four _) hend hcredit
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
      Eligible (labelsAt init omega (four + logWindow n 4) i) :=
    indexClass_eligible (adjacentIndices ell hell)
      (labelsAt init omega (four + logWindow n 4) i) hmainClass
  have hphaseFour :
      4 ≤ (labelsAt init omega (four + logWindow n 4) i).phase.val :=
    hallFour _
      (label_mem_trace init omega (four + logWindow n 4) i)
  have hphaseFive :
      (labelsAt init omega (four + logWindow n 4) i).phase.val = 5 :=
    hwide.canonical (four + logWindow n 4)
      (hwide.start_order.trans (Nat.le_add_right four _)) hend
      i heligible hphaseFour
  have hsomeFive :
      someGE (n := n) 5
        (trace init omega (four + logWindow n 4)) :=
    ⟨labelsAt init omega (four + logWindow n 4) i,
      label_mem_trace init omega (four + logWindow n 4) i,
      hphaseFive.ge⟩
  have hseedLe :
      phaseSeedTime init 5 omega ≤
        ((four + logWindow n 4 : ℕ) : WithTop ℕ) := by
    simpa only [phaseSeedTime] using
      (TraceDrain.exitTime_le_iff init
        (someGE (n := n) 5) omega (four + logWindow n 4)).2
        ⟨four + logWindow n 4, le_rfl, hsomeFive⟩
  rw [hseedFive] at hseedLe
  exact ⟨seedFive, hseedFive, hfourSeed,
    WithTop.coe_le_coe.mp hseedLe⟩

/-- Item 3, second spread plus completion. -/
theorem completion_le_fixed_horizon
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hwide : Prefix init omega allThree four
      (four + protectionHorizon n))
    (hnotFour : omega ∉ phaseFourSpreadFailure init)
    (hnotFive : omega ∉ phaseFiveSpreadFailure init) :
    completed ≤ four + protectionHorizon n := by
  obtain ⟨seedFive, hseedFive, hfourSeed, hseedDeadline⟩ :=
    phaseFiveSeed_deadline hinput ell hell sigma
      hstrong hseed hwide hnotFour
  have hwork := rowTwoWorkHorizon_le_protection hinput.1
  have hgeFive :
      allGE (n := n) 5
        (trace init omega (seedFive + logWindow n 4)) := by
    by_contra hbad
    apply hnotFive
    rw [mem_phaseFiveSpreadFailure_iff]
    exact ⟨seedFive, hseedFive,
      trace_card_eq_population hstrong.population seedFive,
      ((phaseSeedTime_eq_iff init 5 omega seedFive).mp hseedFive).1,
      hbad⟩
  have hend :
      seedFive + logWindow n 4 ≤
        four + protectionHorizon n := by
    omega
  have hstartOrder := hwide.start_order
  have hallFive :
      allPhaseFive
        (trace init omega (seedFive + logWindow n 4)) := by
    intro a ha
    exact le_antisymm
      (hwide.before_six (seedFive + logWindow n 4)
        (by omega) hend a ha)
      (hgeFive a ha)
  have hhomogeneousLe :
      homogeneousFiveStart init omega ≤
        ((seedFive + logWindow n 4 : ℕ) : WithTop ℕ) := by
    simpa only [homogeneousFiveStart] using
      (TraceDrain.exitTime_le_iff init allPhaseFive omega
        (seedFive + logWindow n 4)).2
        ⟨seedFive + logWindow n 4, le_rfl, hallFive⟩
  rw [hstrong.completion.five_start] at hhomogeneousLe
  have hfiveLe : five ≤ seedFive + logWindow n 4 :=
    WithTop.coe_le_coe.mp hhomogeneousLe
  have hcompleted := hstrong.completion.within_sixteen
  omega

/-- Items 1--4, deterministic assembly on the complement of the three local
failures.  The horizon is exactly `protectionHorizon n`. -/
theorem fixedRowTwoHorizon_of_not_failure
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hgood : omega ∉ fixedRowTwoHorizonFailure init) :
    FixedRowTwoHorizon init omega allThree four completed
      (protectionHorizon n) := by
  have hnotTimer : omega ∉ timerProtectionFailureGuarded init 5 :=
    fun h => hgood (Or.inl h)
  have hnotFour : omega ∉ phaseFourSpreadFailure init :=
    fun h => hgood (Or.inr (Or.inl h))
  have hnotFive : omega ∉ phaseFiveSpreadFailure init :=
    fun h => hgood (Or.inr (Or.inr h))
  have hwide := fixedPrefix_of_not_timerFailure
    hinput hstrong hnotTimer
  exact
    { path := hwide
      completed_le := completion_le_fixed_horizon
        hinput ell hell sigma hstrong hseed hwide hnotFour hnotFive }

/-- Consumer-friendly version when the completion charge is present in the
named probability union. -/
theorem fixedRowTwoHorizon_of_not_productionFailure
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot)
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hgood : omega ∉ fixedRowTwoHorizonProductionFailure init) :
    FixedRowTwoHorizon init omega allThree four completed
      (protectionHorizon n) :=
  fixedRowTwoHorizon_of_not_failure hinput ell hell sigma hstrong hseed
    (fun h => hgood (Or.inl h))

/-!
THEOREM LIST
* `mem_phaseFourSpreadFailure_iff`
* `mem_phaseFiveSpreadFailure_iff`
* `mem_timerProtectionFailureGuarded_iff_five`
* `mem_earlySeedBeforeAllThree_iff_five`
* `prefix_allThree_lt_firstFour`
* `StrongSeedReceipt.not_earlySeedBeforeAllThree`
* `earlySeedBeforeAllThree_subset_rowTwoReceiptMissing`
* `law_earlySeedBeforeAllThree_le_rowTwoReceiptMissing`
* `rowTwoWorkHorizon_le_protection`
* `law_phaseFourSpreadFailure_tail`
* `law_phaseFiveSpreadFailure_tail`
* `law_fixedRowTwoHorizonFailure_tail`
* `law_fixedRowTwoHorizonProductionFailure_tail`
* `exists_phaseFiveSeed_after_firstFour`
* `fixedPrefix_of_not_timerFailure`
* `phaseFiveSeed_deadline`
* `completion_le_fixed_horizon`
* `fixedRowTwoHorizon_of_not_failure`
* `fixedRowTwoHorizon_of_not_productionFailure`

CLOSES
* Item 1: the p=5 early event is impossible whenever a strong receipt exists;
  it is a subset of the named upstream receipt-missing event.
* Item 2: guarded timer protection supplies phase <= 5 through the complete
  fixed horizon.
* Item 3: both genuine stopping-time spreads, the forced phase-5 seed, the
  homogeneous-five deadline, completion, and the ceiling arithmetic.
* Item 4: `FixedRowTwoHorizon` with `H = protectionHorizon n`, plus the exact
  unconditional local failure charge.

UNFINISHED
* No numeric estimate for `rowTwoReceiptMissing` is asserted.  N16 is available,
  but the global `completionBase`/`StrongSeedReceipt` existence producer is the
  previously recorded open row-3 seam.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingFixedRowTwoHorizon

end
