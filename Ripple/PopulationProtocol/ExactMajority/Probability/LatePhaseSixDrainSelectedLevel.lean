-- Ripple/PopulationProtocol/ExactMajority/Probability/LatePhaseSixDrainSelectedLevel.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingStrongReceiptProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePhaseSixDrainStrictTimer
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePhaseSixSeedProducer

/-!
# Phase-6 drain at the pathwise N16 level

The fixed-level drain theorem is reindexed by the measurable event that the
N16 receipt supports that level.  The old `EntryFuelCertificate` is
bypassed by transporting the corrected two-level ledger directly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal NNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainSelectedLevel

open TimeTheorem PairLog TraceDrain StageEventSpec
open PhaseOneDrainStopping
open LateF6OriginalLaw LateStrengthening
open LateSamplingCompletion LateSamplingSeedReceipt
open LateSamplingStrongSeedReceipt
open LateSamplingCorrectedFuelProducer hiding InputCfg
open LateSamplingStrongReceiptProducer
open LateMixedFuel
open LatePhaseSixDrainPaperNumerics
open LatePhaseSixDrainFirstBarrierPaper
open LatePhaseSixDrainPaperTimeline
open LatePhaseSixDrainStrictTimer
open LateTimerPrefixScalar LateTimerProtectionOriginalLaw

variable {n : ℕ}

/-! ## Corrected snapshot and mixed-window bridge -/

/-- The completed row-two snapshot produces the corrected branch-indexed
certificate.  It does not produce the obsolete
`LateMixedFuel.EntryFuelCertificate`. -/
theorem completedSnapshot_correctedCertificate
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R (CompletedRowTwoFuelSnapshot ell sigma M R)) :
    LateSamplingFuelFeasibilityAudit.CorrectedEntryFuelCertificate
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) (trace init omega completed) := by
  exact corrected_entry_fuel_certificate_of_completed_snapshot
    ell sigma M C R (trace init omega completed)
      hn hstrong.density hstrong.completion.snapshot

/-- Correct replacement for the old `CompatibleFuelReceipt`.  Its endpoint
fields are the same fields consumed by N17 and by `PhaseSixPaperStart`; only
the invalid old snapshot predicate has been replaced. -/
structure CorrectedCompatibleFuelReceipt
    (init : InputCfg n) (omega : InputLog n)
    (seed allThree four five completed homogeneous M C R : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign) : Prop where
  strong : StrongSeedReceipt init omega seed allThree four five completed
    M C R (CompletedRowTwoFuelSnapshot ell sigma M R)
  seed_receipt : LateSamplingSeedReceipt init M ell.val sigma
    (trace init omega four)
  mixed_path : MixedFiveSixPrefix init omega completed homogeneous
  population : (trace init omega homogeneous).card = n
  phase_six : ∀ a ∈ trace init omega homogeneous, a.phase.val = 6
  ledger : Phase6FuelLedger.TwoLevelFuelLedger
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    ell (LatePotential.fuelFloor n) (trace init omega homogeneous)
  sampled : ReserveSampling.ReserveSampled
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    (trace init omega homogeneous)
  natural_floor : LatePotential.fuelFloor n ≤
    Phase6FuelLedger.twoReserveFuel
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (trace init omega homogeneous)
  real_floor : (687 / 10000 : ℝ) * n ≤
    (Phase6FuelLedger.twoReserveFuel
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (trace init omega homogeneous) : ℝ)

/-- Transport the corrected ledger and the completed sample lock through the
mixed 5/6 prefix. -/
theorem correctedCompatibleFuelReceipt_of_strong
    {init : InputCfg n} (hn : timePopulationThreshold ≤ n)
    {omega : InputLog n}
    {seed allThree four five completed homogeneous M C R : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R (CompletedRowTwoFuelSnapshot ell sigma M R))
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four))
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous) :
    CorrectedCompatibleFuelReceipt init omega seed allThree four five
      completed homogeneous M C R ell hell sigma := by
  have hcertificate :=
    completedSnapshot_correctedCertificate hn ell sigma hstrong
  have hledger : Phase6FuelLedger.TwoLevelFuelLedger
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) (trace init omega completed) :=
    LateSamplingFuelFeasibilityAudit.twoLevelFuelLedger_of_corrected_pair
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell (LatePotential.fuelFloor n) (trace init omega completed)
      hcertificate
  have htransport := phaseFiveSix_compatibleFuel_preserved
    init omega completed homogeneous ell hell
    hmixed.completion_le hmixed.source_window hledger
    hstrong.completion.complete.sampled
  have hpopulation : (trace init omega homogeneous).card = n :=
    (Protocol.reachable_card_eq
      (trace_reachable init omega hmixed.completion_le)).trans
        hstrong.completion.complete.population
  have hfloor := Phase6FuelLedger.twoLevelFuelLedger_union_floor
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    ell hell (LatePotential.fuelFloor n)
    (trace init omega homogeneous) htransport.1
  have hfloorReal :
      (687 / 10000 : ℝ) * n ≤
        (Phase6FuelLedger.twoReserveFuel
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          ell (trace init omega homogeneous) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hfloor)
  exact
    { strong := hstrong
      seed_receipt := hseed
      mixed_path := hmixed
      population := hpopulation
      phase_six := hmixed.endpoint_phase_six
      ledger := htransport.1
      sampled := htransport.2
      natural_floor := hfloor
      real_floor := hfloorReal }

/-- The first-six receipt gives the exact-phase first-hit predicate used by
the paper timeline.  `NoOvershoot 5` changes `phase >= 6` into `phase = 6`. -/
theorem firstPhaseSeed_six_of_seedReceipt
    {init : InputCfg n} {omega : InputLog n} {completed seedSix : ℕ}
    (h : LateMixedFiveSixWindowTailWf.PhaseSixSeedReceipt
      init omega completed seedSix) :
    firstPhaseSeed init 6 seedSix omega := by
  have hfirst :=
    (exitTime_eq_iff_firstHit init
      (someGE (n := n) 6) omega seedSix).mp
      (by simpa only [firstSixStart] using h.time)
  constructor
  · rcases hfirst.1 with ⟨a, ha, hge⟩
    have hlt := h.timer_seed.no_overshoot a ha
    exact ⟨a, ha, by omega⟩
  · intro u hu a ha
    have hnone := hfirst.2 u hu
    by_contra hge
    exact hnone ⟨a, ha, by omega⟩

/-- Assemble the paper-timeline start directly from the corrected compatible
receipt and the first-six receipt. -/
theorem phaseSixPaperStart_of_correctedReceipt
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed homogeneous seedSix M C R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma : Sign}
    (h : CorrectedCompatibleFuelReceipt init omega seed allThree four five
      completed homogeneous M C R ell hell sigma)
    (hSix : LateMixedFiveSixWindowTailWf.PhaseSixSeedReceipt
      init omega completed seedSix) :
    PhaseSixPaperStart init omega allThree four completed homogeneous
      seedSix M C R ell sigma := by
  have hguard : allThree ≤ seedSix := by
    have hpath := h.strong.completion.observed_path
    have h1 := hpath.start_order
    have h2 := hpath.observed
    have h3 := hSix.order
    omega
  exact
    { all_three_time := h.strong.completion.observed_path.all_start
      six_seed := firstPhaseSeed_six_of_seedReceipt hSix
      guard := hguard
      path := h.strong.completion.observed_path
      mixed := h.mixed_path
      readout := h.seed_receipt.toLateSeedReadout
      density := h.strong.density
      ready := ⟨⟨h.population, h.phase_six⟩, h.ledger⟩ }

/-! ## Measurable pathwise-level events -/

/-- `ell` is one N16 receipt level at the genuine first-four configuration.
This is a relation, not an arbitrary choice function. -/
def producedN16LevelEvent
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    Set (InputLog n) :=
  {omega | ∃ four M : ℕ,
    firstFourStart init omega = (four : WithTop ℕ) ∧
      ∃ sigma : Sign,
        LateSamplingSeedReceipt init M ell.val sigma
          (trace init omega four)}

@[simp] theorem mem_producedN16LevelEvent_iff
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (omega : InputLog n) :
    omega ∈ producedN16LevelEvent init ell ↔
      ∃ four M : ℕ,
        firstFourStart init omega = (four : WithTop ℕ) ∧
          ∃ sigma : Sign,
            LateSamplingSeedReceipt init M ell.val sigma
              (trace init omega four) :=
  Iff.rfl

/-- The receipt-level event is measurable under the original pair-log law. -/
theorem producedN16LevelEvent_measurable
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    MeasurableSet (producedN16LevelEvent init ell) := by
  have heq : producedN16LevelEvent init ell =
      ⋃ four : ℕ,
        {omega | firstFourStart init omega = (four : WithTop ℕ)} ∩
          (⋃ M : ℕ, ⋃ sigma : Sign,
            {omega | LateSamplingSeedReceipt init M ell.val sigma
              (trace init omega four)}) := by
    ext omega
    simp [producedN16LevelEvent]
  rw [heq]
  apply MeasurableSet.iUnion
  intro four
  have htime : MeasurableSet
      {omega | firstFourStart init omega = (four : WithTop ℕ)} :=
    (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le
      four _ ((firstFourStart_past init) four)
  apply htime.inter
  apply MeasurableSet.iUnion
  intro M
  apply MeasurableSet.iUnion
  intro sigma
  exact
    (show MeasurableSet {c : InputCfg n |
        LateSamplingSeedReceipt init M ell.val sigma c} from
      (Set.to_countable _).measurableSet).preimage
        ((measurable_pi_apply four).comp (measurable_trace init))

/-- Every strengthened receipt identifies a measurable produced-level
event. -/
theorem producedN16LevelEvent_of_receipts
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (sigma : Sign)
    (hstrong : StrongSeedReceipt init omega seed allThree four five completed
      M C R (CompletedRowTwoFuelSnapshot ell sigma M R))
    (hseed : LateSamplingSeedReceipt init M ell.val sigma
      (trace init omega four)) :
    omega ∈ producedN16LevelEvent init ell := by
  exact ⟨four, M, hstrong.completion.observed_path.four_start,
    sigma, hseed⟩

/-! ## Random-level failure union and law -/

/-- Only the drain tail is level-dependent. -/
noncomputable def selectedProducedLevelDrainFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    Set (InputLog n) :=
  if hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n then
    producedN16LevelEvent init ell ∩
      phaseSixDrainFailure init ell hell
  else ∅

/-- Literal selected-level Phase-6 failure: the N16 receipt supports `ell`, and
one of spread, strict timer, or the fixed-`ell` drain fails. -/
noncomputable def selectedProducedLevelPhaseSixFailure
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    Set (InputLog n) :=
  if hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n then
    producedN16LevelEvent init ell ∩
      (LatePhaseSixDrainPaperTimeline.phaseSixSpreadFailure init ∪
        (LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6 ∪
          phaseSixDrainFailure init ell hell))
  else ∅

noncomputable def anySelectedProducedLevelDrainFailure
    (init : InputCfg n) : Set (InputLog n) :=
  ⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
    selectedProducedLevelDrainFailure init ell

noncomputable def anySelectedProducedLevelPhaseSixFailure
    (init : InputCfg n) : Set (InputLog n) :=
  ⋃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
    selectedProducedLevelPhaseSixFailure init ell

noncomputable def selectedLevelPhaseSixDrainCharge (n : ℕ) : ℝ≥0∞ :=
  ((PhaseThreeModel.Numeric.hourIndex n + 1 : ℕ) : ℝ≥0∞) *
    phaseSixDrainBudget n

/-- Intersection with a receipt-level event never costs more than the
unconditional fixed-level drain theorem. -/
theorem law_selectedProducedLevelDrainFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init (selectedProducedLevelDrainFailure init ell) ≤
      phaseSixDrainBudget n := by
  classical
  by_cases hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n
  · rw [selectedProducedLevelDrainFailure, dif_pos hell]
    exact (measure_mono (by
      intro omega h
      exact h.2)).trans
        (law_phaseSixDrainFailure_tail init hinput.1 ell hell)
  · rw [selectedProducedLevelDrainFailure, dif_neg hell, measure_empty]
    exact zero_le

/-- The fixed-level drain tail is summed over the finite level type. -/
theorem law_anySelectedProducedLevelDrainFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (anySelectedProducedLevelDrainFailure init) ≤
      selectedLevelPhaseSixDrainCharge n := by
  calc
    law init (anySelectedProducedLevelDrainFailure init) ≤
        ∑' ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
          law init (selectedProducedLevelDrainFailure init ell) :=
      measure_iUnion_le _
    _ ≤ ∑' _ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
        phaseSixDrainBudget n :=
      ENNReal.tsum_le_tsum fun ell =>
        law_selectedProducedLevelDrainFailure init hinput ell
    _ = selectedLevelPhaseSixDrainCharge n := by
      unfold selectedLevelPhaseSixDrainCharge
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]

/-- Shared spread and timer failures are paid once, not once per level. -/
theorem anySelectedProducedLevelPhaseSixFailure_subset
    (init : InputCfg n) :
    anySelectedProducedLevelPhaseSixFailure init ⊆
      LatePhaseSixDrainPaperTimeline.phaseSixSpreadFailure init ∪
        (LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6 ∪
          anySelectedProducedLevelDrainFailure init) := by
  classical
  intro omega hbad
  rcases Set.mem_iUnion.mp hbad with ⟨ell, hlevel⟩
  by_cases hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n
  · rw [selectedProducedLevelPhaseSixFailure, dif_pos hell] at hlevel
    rcases hlevel with ⟨hproduced, hbad⟩
    rcases hbad with hspread | htimer | hdrain
    · exact Or.inl hspread
    · exact Or.inr (Or.inl htimer)
    · apply Or.inr
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨ell, ?_⟩
      rw [selectedProducedLevelDrainFailure, dif_pos hell]
      exact ⟨hproduced, hdrain⟩
  · rw [selectedProducedLevelPhaseSixFailure, dif_neg hell] at hlevel
    exact hlevel.elim

noncomputable def selectedProducedLevelPhaseSixCharge (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 2) +
    (ENNReal.ofReal
        (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
      selectedLevelPhaseSixDrainCharge n)

/-- Explicit downstream random-level charge. -/
theorem law_anySelectedProducedLevelPhaseSixFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (anySelectedProducedLevelPhaseSixFailure init) ≤
      selectedProducedLevelPhaseSixCharge n := by
  have htimer :
      law init
          (LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6) ≤
        ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) :=
    LateTimerRouteProof.law_timerProtectionFailureGuarded_tail_of_goodInput
      init hinput 6 (by unfold LateTimedPhase; omega)
  calc
    law init (anySelectedProducedLevelPhaseSixFailure init) ≤
        law init
          (LatePhaseSixDrainPaperTimeline.phaseSixSpreadFailure init ∪
            (LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6 ∪
              anySelectedProducedLevelDrainFailure init)) :=
      measure_mono
        (anySelectedProducedLevelPhaseSixFailure_subset init)
    _ ≤ law init
          (LatePhaseSixDrainPaperTimeline.phaseSixSpreadFailure init) +
        law init
          (LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6 ∪
            anySelectedProducedLevelDrainFailure init) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp 3 / (n : ℝ) ^ 2) +
        (ENNReal.ofReal
            (Real.rpow (n : ℝ) (-(103 / 50 : ℝ))) +
          selectedLevelPhaseSixDrainCharge n) := by
      refine add_le_add
        (LatePhaseSixDrainPaperTimeline.law_phaseSixSpreadFailure_tail
          init hinput) ?_
      exact (measure_union_le _ _).trans
        (add_le_add htimer
          (law_anySelectedProducedLevelDrainFailure init hinput))
    _ = selectedProducedLevelPhaseSixCharge n := rfl

/-- Complete named producer union on the strict-small-gap branch. -/
def smallGapPhaseSixDrainFailure
    (init : InputCfg n) : Set (InputLog n) :=
  smallRowTwoSnapshotProductionFailure init ∪
    (LateMixedFiveSixWindow.mixedFailure init ∪
      (LateMixedFiveSixWindowTailWf.phaseSixSeedFailure init ∪
        anySelectedProducedLevelPhaseSixFailure init))

noncomputable def smallGapPhaseSixDrainCharge (n : ℕ) : ℝ≥0∞ :=
  smallRowTwoSnapshotCharge n +
    (ENNReal.ofReal (1 / (n : ℝ) ^ 2) +
      (ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
        selectedProducedLevelPhaseSixCharge n))

/-- GoodInput-only original-law bound for the complete selected-level row. -/
theorem law_smallGapPhaseSixDrainFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (smallGapPhaseSixDrainFailure init) ≤
      smallGapPhaseSixDrainCharge n := by
  unfold smallGapPhaseSixDrainFailure smallGapPhaseSixDrainCharge
  exact (measure_union_le _ _).trans
    (add_le_add
      (law_smallRowTwoSnapshotProductionFailure init hinput)
      ((measure_union_le _ _).trans
        (add_le_add
          (LateMixedFiveSixWindowTailWf.law_mixedFailure_inverse_square_of_goodInput
            init hinput)
          ((measure_union_le _ _).trans
            (add_le_add
              (LateMixedFiveSixWindowTailWf.law_phaseSixSeedFailure_tail
                init hinput)
              (law_anySelectedProducedLevelPhaseSixFailure
                init hinput))))))

/-- On a log carrying the produced level, complement of the selected-level
union gives all three downstream complements for that same level. -/
theorem not_downstreamFailures_of_producedLevel
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    {omega : InputLog n}
    (hlevel : omega ∈ producedN16LevelEvent init ell)
    (hgood : omega ∉ anySelectedProducedLevelPhaseSixFailure init) :
    omega ∉ LatePhaseSixDrainPaperTimeline.phaseSixSpreadFailure init ∧
      omega ∉ LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6 ∧
      omega ∉ phaseSixDrainFailure init ell hell := by
  constructor
  · intro hspread
    apply hgood
    apply Set.mem_iUnion.mpr
    refine ⟨ell, ?_⟩
    rw [selectedProducedLevelPhaseSixFailure, dif_pos hell]
    exact ⟨hlevel, Or.inl hspread⟩
  · constructor
    · intro htimer
      apply hgood
      apply Set.mem_iUnion.mpr
      refine ⟨ell, ?_⟩
      rw [selectedProducedLevelPhaseSixFailure, dif_pos hell]
      exact ⟨hlevel, Or.inr (Or.inl htimer)⟩
    · intro hdrain
      apply hgood
      apply Set.mem_iUnion.mpr
      refine ⟨ell, ?_⟩
      rw [selectedProducedLevelPhaseSixFailure, dif_pos hell]
      exact ⟨hlevel, Or.inr (Or.inr hdrain)⟩

/-! ## Direct pathwise drain, without a fixed-level producer premise -/

private theorem phaseSeedTime_eq_of_firstPhaseSeed_local
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

/-- The direct form of the pathwise drain theorem.  The start is supplied
for this log and level, so no `PhaseSixPaperStartProducer` is required. -/
theorem phaseSixPaperDrainReceipt_of_start
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    {omega : InputLog n}
    {allThree four completed homogeneous seedSix M C R : ℕ}
    {sigma : Sign}
    (start : PhaseSixPaperStart init omega allThree four completed homogeneous
      seedSix M C R ell sigma)
    (hnotSpread : omega ∉
      LatePhaseSixDrainPaperTimeline.phaseSixSpreadFailure init)
    (hnotTimer : omega ∉
      LateTimerProtectionGuarded.timerProtectionFailureGuarded init 6)
    (hnotDrain : omega ∉ phaseSixDrainFailure init ell hell) :
    ∃ endpoint,
      PhaseSixPaperDrainReceipt init omega ell homogeneous seedSix endpoint := by
  have hnlarge : 2 ≤ n := by
    have hlarge := (time_population_bounds hinput.1).2
    omega
  have hseedTime :=
    phaseSeedTime_eq_of_firstPhaseSeed_local
      init omega 6 seedSix start.six_seed
  have hguardTop : LateF6OriginalLaw.allThreeStart init omega <
      (seedSix : WithTop ℕ) :=
    phaseSixPaperStart_allThreeStart_lt_phaseSeedTime start
  have htimerLate :
      ((seedSix + protectionHorizon n : ℕ) : WithTop ℕ) <
        phaseSeedTime init 7 omega := by
    by_contra hnot
    apply hnotTimer
    exact ⟨seedSix, hseedTime, hguardTop, not_lt.mp hnot⟩
  have htimerSeven :
      ((seedSix + protectionHorizon n : ℕ) : WithTop ℕ) <
        LateMixedFiveSixWindow.firstPhaseSevenStart init omega := by
    simpa [LateTimerProtectionOriginalLaw.phaseSeedTime,
      LateMixedFiveSixWindow.firstPhaseSevenStart] using htimerLate
  have hallSix :
      ∀ a ∈ trace init omega (seedSix + logWindow n 3),
        6 ≤ a.phase.val := by
    by_contra hbad
    apply hnotSpread
    exact ⟨seedSix, start.six_seed, hbad⟩
  have hfit := spread_add_drain_horizon_le_protection hinput.1
  have hspreadLe : logWindow n 3 ≤ protectionHorizon n := by omega
  have hspreadBefore :
      ((seedSix + logWindow n 3 : ℕ) : WithTop ℕ) <
        LateMixedFiveSixWindow.firstPhaseSevenStart init omega :=
    (WithTop.coe_le_coe.mpr
      (Nat.add_le_add_left hspreadLe seedSix)).trans_lt htimerSeven
  have hbelowSix :=
    LateMixedFiveSixWindow.phase_lt_seven_before_firstPhaseSevenStart
      init omega (seedSix + logWindow n 3) hspreadBefore
  have hallExact : LateMixedFuel.allPhaseSix
      (trace init omega (seedSix + logWindow n 3)) := by
    intro a ha
    have hlo := hallSix a ha
    have hhi := hbelowSix a ha
    omega
  have hhomoTop : LateMixedFuel.homogeneousSixStart init omega ≤
      ((seedSix + logWindow n 3 : ℕ) : WithTop ℕ) := by
    simpa only [LateMixedFuel.homogeneousSixStart] using
      (TraceDrain.exitTime_le_iff init LateMixedFuel.allPhaseSix omega
        (seedSix + logWindow n 3)).2
        ⟨seedSix + logWindow n 3, le_rfl, hallExact⟩
  rw [start.mixed.six_start] at hhomoTop
  have hhomoLe : homogeneous ≤ seedSix + logWindow n 3 :=
    WithTop.coe_le_coe.mp hhomoTop
  let endpoint := homogeneous + phaseSixDrainHorizon n
  have hendpointLe : endpoint ≤ seedSix + protectionHorizon n := by
    dsimp [endpoint]
    omega
  have hbefore : (endpoint : WithTop ℕ) <
      LateMixedFiveSixWindow.firstPhaseSevenStart init omega :=
    (WithTop.coe_le_coe.mpr hendpointLe).trans_lt htimerSeven
  have hnoSeven : ¬ SomeSeven (trace init omega endpoint) := by
    intro hsome
    rcases hsome with ⟨a, ha, hge⟩
    have hlt :=
      LateMixedFiveSixWindow.phase_lt_seven_before_firstPhaseSevenStart
        init omega endpoint hbefore a ha
    omega
  have hsharp := start.sharpConfig hnlarge
  have hpotential : LatePotential.shallowLargePotential ell.val
      (trace init omega endpoint) = 0 := by
    by_contra hpos
    apply hnotDrain
    refine ⟨homogeneous, start.mixed.six_start, hsharp, ?_, ?_⟩
    · simpa only [endpoint] using hnoSeven
    · simpa only [endpoint] using hpos
  exact
    ⟨endpoint,
      { homogeneous_time := start.mixed.six_start
        ready := start.ready
        seed_time := hseedTime
        endpoint_eq := rfl
        before_seven := hbefore
        potential_zero := hpotential }⟩

/-- Complete pathwise assembly on the small-gap branch. -/
theorem exists_selectedPhaseSixPaperDrainReceipt_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ LateStrengthening.smallHistory init)
    (hgood : omega ∉ smallGapPhaseSixDrainFailure init) :
    ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ homogeneous seedSix endpoint : ℕ,
        omega ∈ producedN16LevelEvent init ell ∧
          PhaseSixPaperDrainReceipt
            init omega ell homogeneous seedSix endpoint := by
  have hnotSnapshot :
      omega ∉ smallRowTwoSnapshotProductionFailure init :=
    fun h => hgood (Or.inl h)
  have hnotMixed : omega ∉ LateMixedFiveSixWindow.mixedFailure init :=
    fun h => hgood (Or.inr (Or.inl h))
  have hnotSeed :
      omega ∉ LateMixedFiveSixWindowTailWf.phaseSixSeedFailure init :=
    fun h => hgood (Or.inr (Or.inr (Or.inl h)))
  have hnotSelected :
      omega ∉ anySelectedProducedLevelPhaseSixFailure init :=
    fun h => hgood (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨seed, allThree, four, ell, hell, sigma, five, completed,
      _hhistory, hseed, hstrong, _hledger⟩ :=
    exists_completedFuelLedger_of_smallHistory
      hinput hsmall hnotSnapshot
  have hlevel : omega ∈ producedN16LevelEvent init ell :=
    producedN16LevelEvent_of_receipts ell sigma hstrong hseed
  obtain ⟨homogeneous, hmixed⟩ :=
    LateMixedFiveSixWindow.mixedFiveSixPrefix_of_not_mixedFailure
      hnotMixed hstrong.completion
  have hnlarge : 2 ≤ n := by
    have hlarge := (time_population_bounds hinput.1).2
    omega
  obtain ⟨seedSix, hSix⟩ :=
    LateMixedFiveSixWindowTailWf.phaseSixSeedReceipt_of_not_failure
      hnlarge init omega completed
        hstrong.completion.completed_at hnotSeed
  have hcompatible := correctedCompatibleFuelReceipt_of_strong
    hinput.1 ell hell sigma hstrong hseed hmixed
  have hstart :=
    phaseSixPaperStart_of_correctedReceipt hcompatible hSix
  obtain ⟨hnotSpread, hnotTimer, hnotDrain⟩ :=
    not_downstreamFailures_of_producedLevel
      init ell hell hlevel hnotSelected
  obtain ⟨endpoint, hreceipt⟩ :=
    phaseSixPaperDrainReceipt_of_start
      init hinput ell hell hstart hnotSpread hnotTimer hnotDrain
  exact ⟨ell, hell, homogeneous, seedSix, endpoint, hlevel, hreceipt⟩

/-- Public Phase-6 drain row: at the genuine first Phase-7 configuration no
biased Main remains below the pathwise N16 level. -/
theorem no_shallow_main_at_firstPhaseSeven_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ LateStrengthening.smallHistory init)
    (hgood : omega ∉ smallGapPhaseSixDrainFailure init)
    (seven : ℕ)
    (hseven : LateMixedFiveSixWindow.firstPhaseSevenStart init omega =
      (seven : WithTop ℕ)) :
    ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
        omega ∈ producedN16LevelEvent init ell ∧
          ∀ a ∈ trace init omega seven,
            ¬ Phase6Convergence.highSt
              (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
              ell.val a := by
  obtain ⟨ell, hell, homogeneous, seedSix, endpoint,
      hlevel, hreceipt⟩ :=
    exists_selectedPhaseSixPaperDrainReceipt_of_smallHistory
      hinput hsmall hgood
  exact
    ⟨ell, hell, hlevel,
      no_shallow_main_at_firstPhaseSeven_of_receipt
        hreceipt hseven⟩

/-!
THEOREM LIST
* `completedSnapshot_correctedCertificate`
* `CorrectedCompatibleFuelReceipt`
* `correctedCompatibleFuelReceipt_of_strong`
* `firstPhaseSeed_six_of_seedReceipt`
* `phaseSixPaperStart_of_correctedReceipt`
* `producedN16LevelEvent`, `producedN16LevelEvent_measurable`
* `producedN16LevelEvent_of_receipts`
* `selectedProducedLevelDrainFailure`
* `selectedProducedLevelPhaseSixFailure`
* `law_anySelectedProducedLevelDrainFailure`
* `law_anySelectedProducedLevelPhaseSixFailure`
* `smallGapPhaseSixDrainFailure`, `law_smallGapPhaseSixDrainFailure`
* `phaseSixPaperDrainReceipt_of_start`
* `exists_selectedPhaseSixPaperDrainReceipt_of_smallHistory`
* `no_shallow_main_at_firstPhaseSeven_of_smallHistory`

CLOSES
* Item 1: a measurable pathwise-level event and the finite selected-level
  union, with spread/timer paid once and only the drain tail summed over levels.
* Item 2, corrected: deterministic conversion from
  `CompletedRowTwoFuelSnapshot` to the corrected certificate and ledger;
  no use of the false old snapshot certificate.
* Item 3: mixed-window transport, genuine first-six receipt, exact first-six
  seed, and the strict all-three timer guard on the same log.
* Item 4: a GoodInput-only law bound and the no-shallow-Main conclusion at the
  genuine first Phase-7 configuration for the produced level.

UNFINISHED
* No mathematical premise remains open after replacing the obsolete
  `EntryFuelCertificate` by its corrected interface.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainSelectedLevel

end
