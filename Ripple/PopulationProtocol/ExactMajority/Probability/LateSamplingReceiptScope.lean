-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingReceiptScope.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCompletedFuelProtected
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReceiptCover

/-!
# Scope of the late row-two receipt

`rowTwoReceiptMissing` is intentionally not a global failure event: its witness
contains the strict-small-gap N16 receipt.  This file proves that the event is
the whole sample space on tie and strong-gap inputs, and isolates the corrected
small-gap-local completion seam without using the vacuous `completionBase`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingReceiptScope

open TimeTheorem StageEventSpec PairLog
open AveragingSparseEntry AveragingEventInterface
open AveragingDominantLevelSplice AveragingGlobalFailureSplice
open AveragingHourEvents AveragingHourPrefix
open AveragingTerminalPackages AveragingHourStops
open AveragingObservedHourTails AveragingSeededDelay
open AveragingFixedSeedHours AveragingIntegerPotential
open LateStrengthening
open LateSamplingSeedReceipt LateSamplingStrongSeedReceipt
open LateSamplingFixedRowTwoHorizon

variable {n : ℕ}

private theorem timeMainCount_le_card
    {L K : ℕ} (c : Cfg L K) :
    timeMainCount c ≤ c.card := by
  unfold timeMainCount
  exact Multiset.countP_le_card _ _

private theorem trace_card_eq_input
    (init : InputCfg n) (omega : InputLog n) (t : ℕ) :
    (trace init omega t).card = init.card := by
  have hreach :
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega t) := by
    simpa only [TimeTheorem.trace_zero] using
      (TimeTheorem.trace_reachable init omega
        (s := 0) (t := t) (Nat.zero_le t))
  exact Protocol.reachable_card_eq hreach

private theorem timeMainCount_trace_le_population
    {init : InputCfg n} {omega : InputLog n} {t : ℕ}
    (hcard : init.card = n) :
    timeMainCount (trace init omega t) ≤ n := by
  calc
    timeMainCount (trace init omega t) ≤
        (trace init omega t).card :=
      timeMainCount_le_card _
    _ = init.card := trace_card_eq_input init omega t
    _ = n := hcard

/-- No row-two witness can exist when the initial gap is in the strong branch.
The contradiction uses the receipt's literal `strictGap` field and the fact
that Main agents are a submultiset of the population. -/
theorem no_rowTwoReceipt_of_not_strictGap
    (init : InputCfg n) (omega : InputLog n)
    (hgap : n ≤ 40 * gapMagnitude init) :
    ¬ ∃ seed allThree four five completed M C R ell,
      ∃ sigma : Sign,
      ∃ Snapshot : InputCfg n → Prop,
        StrongSeedReceipt init omega seed allThree four five completed
            M C R Snapshot ∧
          LateSamplingSeedReceipt init M ell sigma
            (trace init omega four) := by
  rintro ⟨seed, allThree, four, five, completed, M, C, R, ell,
    sigma, Snapshot, hstrong, hseed⟩
  have hMtrace :
      timeMainCount (trace init omega four) ≤ n :=
    timeMainCount_trace_le_population hstrong.population
  have hMle : M ≤ n := by
    rw [← hseed.main_count]
    exact hMtrace
  have hstrict : 40 * gapMagnitude init < M :=
    hseed.toSmallReadout.strictGap
  omega

/-- Tie inputs are an even simpler obstruction: N16 records a positive gap. -/
theorem no_rowTwoReceipt_of_tie
    (init : InputCfg n) (omega : InputLog n)
    (htie : gapMagnitude init = 0) :
    ¬ ∃ seed allThree four five completed M C R ell,
      ∃ sigma : Sign,
      ∃ Snapshot : InputCfg n → Prop,
        StrongSeedReceipt init omega seed allThree four five completed
            M C R Snapshot ∧
          LateSamplingSeedReceipt init M ell sigma
            (trace init omega four) := by
  rintro ⟨seed, allThree, four, five, completed, M, C, R, ell,
    sigma, Snapshot, _hstrong, hseed⟩
  have hnonzero : 0 < gapMagnitude init :=
    hseed.toSmallReadout.nonzero
  rw [htie] at hnonzero
  omega

/-- On a strong-gap input, the global receipt-missing set is `univ`. -/
theorem rowTwoReceiptMissing_eq_univ_of_not_strictGap
    (init : InputCfg n)
    (hgap : n ≤ 40 * gapMagnitude init) :
    rowTwoReceiptMissing init = Set.univ := by
  ext omega
  constructor
  · intro _
    simp
  · intro _
    change ¬ ∃ seed allThree four five completed M C R ell,
      ∃ sigma : Sign,
      ∃ Snapshot : InputCfg n → Prop,
        StrongSeedReceipt init omega seed allThree four five completed
            M C R Snapshot ∧
          LateSamplingSeedReceipt init M ell sigma
            (trace init omega four)
    exact no_rowTwoReceipt_of_not_strictGap init omega hgap

/-- On a tie input, the global receipt-missing set is also `univ`. -/
theorem rowTwoReceiptMissing_eq_univ_of_tie
    (init : InputCfg n)
    (htie : gapMagnitude init = 0) :
    rowTwoReceiptMissing init = Set.univ := by
  ext omega
  constructor
  · intro _
    simp
  · intro _
    change ¬ ∃ seed allThree four five completed M C R ell,
      ∃ sigma : Sign,
      ∃ Snapshot : InputCfg n → Prop,
        StrongSeedReceipt init omega seed allThree four five completed
            M C R Snapshot ∧
          LateSamplingSeedReceipt init M ell sigma
            (trace init omega four)
    exact no_rowTwoReceipt_of_tie init omega htie

/-- Exact law obstruction for the strong branch. -/
theorem law_rowTwoReceiptMissing_eq_one_of_not_strictGap
    (init : InputCfg n)
    (hgap : n ≤ 40 * gapMagnitude init) :
    law init (rowTwoReceiptMissing init) = 1 := by
  rw [rowTwoReceiptMissing_eq_univ_of_not_strictGap init hgap,
    measure_univ]

/-- Exact law obstruction for the tie branch. -/
theorem law_rowTwoReceiptMissing_eq_one_of_tie
    (init : InputCfg n)
    (htie : gapMagnitude init = 0) :
    law init (rowTwoReceiptMissing init) = 1 := by
  rw [rowTwoReceiptMissing_eq_univ_of_tie init htie,
    measure_univ]

/-- Any proposed upper bound strictly below one is impossible on the strong
branch. -/
theorem not_law_rowTwoReceiptMissing_le_of_not_strictGap
    (init : InputCfg n)
    (hgap : n ≤ 40 * gapMagnitude init)
    {q : ℝ≥0∞} (hq : q < 1) :
    ¬ law init (rowTwoReceiptMissing init) ≤ q := by
  intro hle
  rw [law_rowTwoReceiptMissing_eq_one_of_not_strictGap init hgap] at hle
  exact (not_le_of_gt hq) hle

/-- A matching receipt at one genuine successful small-gap history.  The role
counts are definitionally the actual counts at the asynchronous seed. -/
def SmallBranchReceiptAt
    (init : InputCfg n) (omega : InputLog n)
    (seed allThree four : ℕ) : Prop :=
  ∃ ell : ℕ, ∃ sigma : Sign, ∃ five completed : ℕ,
    ∃ Snapshot : InputCfg n → Prop,
      LateSamplingSeedReceipt init
          (timeMainCount (trace init omega seed)) ell sigma
          (trace init omega four) ∧
        StrongSeedReceipt init omega seed allThree four five completed
          (timeMainCount (trace init omega seed))
          (clockCount (trace init omega seed))
          (StageEventSpec.reserveCount (trace init omega seed))
          Snapshot

/-- The only part of the receipt-missing event relevant to row two. -/
def smallRowTwoReceiptMissing (init : InputCfg n) : Set (InputLog n) :=
  rowTwoReceiptMissing init ∩ smallHistory init

/-- Exact remaining seam after the N16 receipt has been produced: a
successful strict-small-gap history and an N16 receipt exist, but no matching
strong completion receipt exists for that genuine history. -/
def smallStrongReceiptMissing (init : InputCfg n) : Set (InputLog n) :=
  {omega | ∃ seed allThree four : ℕ,
    successfulHistory (reviewedStageEvents n init)
        omega seed allThree four ∧
      0 < gapMagnitude init ∧
      40 * gapMagnitude init <
        timeMainCount (trace init omega seed) ∧
      (∃ ell : ℕ, ∃ sigma : Sign,
        LateSamplingSeedReceipt init
          (timeMainCount (trace init omega seed)) ell sigma
          (trace init omega four)) ∧
      ¬ SmallBranchReceiptAt init omega seed allThree four}

@[simp] theorem mem_smallRowTwoReceiptMissing_iff
    (init : InputCfg n) (omega : InputLog n) :
    omega ∈ smallRowTwoReceiptMissing init ↔
      omega ∈ rowTwoReceiptMissing init ∧
        omega ∈ smallHistory init :=
  Iff.rfl

@[simp] theorem mem_smallStrongReceiptMissing_iff
    (init : InputCfg n) (omega : InputLog n) :
    omega ∈ smallStrongReceiptMissing init ↔
      ∃ seed allThree four : ℕ,
        successfulHistory (reviewedStageEvents n init)
            omega seed allThree four ∧
          0 < gapMagnitude init ∧
          40 * gapMagnitude init <
            timeMainCount (trace init omega seed) ∧
          (∃ ell : ℕ, ∃ sigma : Sign,
            LateSamplingSeedReceipt init
              (timeMainCount (trace init omega seed)) ell sigma
              (trace init omega four)) ∧
          ¬ SmallBranchReceiptAt init omega seed allThree four :=
  Iff.rfl

/-- The corrected local receipt failure is covered by the landed N16 failure
and the one genuinely open strong-completion failure. -/
theorem smallRowTwoReceiptMissing_cover
    (init : InputCfg n) :
    smallRowTwoReceiptMissing init ⊆
      lateSamplingSeedProducerFailure init ∪
        smallStrongReceiptMissing init := by
  rintro omega ⟨hmissing, hsmall⟩
  obtain ⟨seed, allThree, four, hhistory, hnonzero, hgap⟩ := hsmall
  by_cases hseed :
      ∃ ell : ℕ, ∃ sigma : Sign,
        LateSamplingSeedReceipt init
          (timeMainCount (trace init omega seed)) ell sigma
          (trace init omega four)
  · apply Or.inr
    rw [mem_smallStrongReceiptMissing_iff init omega]
    refine ⟨seed, allThree, four, hhistory, hnonzero, hgap,
      hseed, ?_⟩
    intro hreceipt
    obtain ⟨ell, sigma, five, completed, Snapshot,
      hseedReceipt, hstrong⟩ := hreceipt
    exact hmissing
      ⟨seed, allThree, four, five, completed,
        timeMainCount (trace init omega seed),
        clockCount (trace init omega seed),
        StageEventSpec.reserveCount (trace init omega seed),
        ell, sigma, Snapshot, hstrong, hseedReceipt⟩
  · apply Or.inl
    rw [mem_lateSamplingSeedProducerFailure_iff init omega]
    exact ⟨seed, allThree, four, hhistory, hnonzero, hgap, hseed⟩

/-- Closed receipt-valued N16 charge, rather than the weaker public readout
corollary. -/
theorem law_lateSamplingSeedProducerFailure_closed
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lateSamplingSeedProducerFailure init) ≤
      ENNReal.ofReal
        (2 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 4 +
          Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
  let selector := receiptOldBlockSelector init
  have hcover :
      lateSamplingSeedProducerSafeFailure init ⊆
        protectedTestFailure init ∪
          (nearTestFailure init ∪ oldIndexFailure selector) := by
    simpa only [selector] using
      late_sampling_seed_receipt_safe_cover init hinput
  have hreceipt :=
    late_sampling_seed_receipt_estimate init hinput
      (protectedTestFailure init) (nearTestFailure init)
      (oldIndexFailure selector) hcover
      (protected_test_failure_estimate init hinput)
      (near_test_failure_estimate init hinput)
      (oldIndexFailure_hold init hinput.1 selector)
  simpa only [lateSamplingSeedProducerFailure] using hreceipt

/-- Numerically closed part of the corrected local event. -/
theorem law_smallRowTwoReceiptMissing_le
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (smallRowTwoReceiptMissing init) ≤
      ENNReal.ofReal
          (2 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 4 +
            Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) +
        law init (smallStrongReceiptMissing init) := by
  calc
    law init (smallRowTwoReceiptMissing init) ≤
        law init
          (lateSamplingSeedProducerFailure init ∪
            smallStrongReceiptMissing init) :=
      measure_mono (smallRowTwoReceiptMissing_cover init)
    _ ≤ law init (lateSamplingSeedProducerFailure init) +
        law init (smallStrongReceiptMissing init) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal
          (2 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 4 +
            Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) +
        law init (smallStrongReceiptMissing init) :=
      add_le_add
        (law_lateSamplingSeedProducerFailure_closed init hinput) le_rfl

/-- Outside the two named small-gap failures, all receipt fields exist with
`M,C,R` equal to the actual asynchronous-seed counts.  This theorem carries no
universal per-log premise.  It does not claim a bound for
`smallStrongReceiptMissing`; that is exactly the open producer. -/
theorem exists_matching_receipts_of_small_history
    {init : InputCfg n} {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉
      lateSamplingSeedProducerFailure init ∪
        smallStrongReceiptMissing init) :
    ∃ seed allThree four ell : ℕ,
      ∃ sigma : Sign, ∃ five completed : ℕ,
      ∃ Snapshot : InputCfg n → Prop,
        successfulHistory (reviewedStageEvents n init)
            omega seed allThree four ∧
          0 < gapMagnitude init ∧
          40 * gapMagnitude init <
            timeMainCount (trace init omega seed) ∧
          LateSamplingSeedReceipt init
            (timeMainCount (trace init omega seed)) ell sigma
            (trace init omega four) ∧
          StrongSeedReceipt init omega seed allThree four five completed
            (timeMainCount (trace init omega seed))
            (clockCount (trace init omega seed))
            (StageEventSpec.reserveCount (trace init omega seed))
            Snapshot := by
  obtain ⟨seed, allThree, four, hhistory, hnonzero, hgap⟩ := hsmall
  have hnotSeed :
      omega ∉ lateSamplingSeedProducerFailure init :=
    fun h => hgood (Or.inl h)
  have hnotStrong :
      omega ∉ smallStrongReceiptMissing init :=
    fun h => hgood (Or.inr h)
  have hseedExists :
      ∃ ell : ℕ, ∃ sigma : Sign,
        LateSamplingSeedReceipt init
          (timeMainCount (trace init omega seed)) ell sigma
          (trace init omega four) := by
    by_contra hnone
    apply hnotSeed
    rw [mem_lateSamplingSeedProducerFailure_iff init omega]
    exact ⟨seed, allThree, four, hhistory, hnonzero, hgap, hnone⟩
  have hreceipt :
      SmallBranchReceiptAt init omega seed allThree four := by
    by_contra hnone
    apply hnotStrong
    rw [mem_smallStrongReceiptMissing_iff init omega]
    exact ⟨seed, allThree, four, hhistory, hnonzero, hgap,
      hseedExists, hnone⟩
  obtain ⟨ell, sigma, five, completed, Snapshot,
    hseedReceipt, hstrong⟩ := hreceipt
  exact ⟨seed, allThree, four, ell, sigma, five, completed,
    Snapshot, hhistory, hnonzero, hgap, hseedReceipt, hstrong⟩

/-- The global event necessarily includes every non-small branch.  This is the
correct branch decomposition and explains why no GoodInput-only inverse-power
bound is possible. -/
theorem rowTwoReceiptMissing_cover_by_branch
    (init : InputCfg n) :
    rowTwoReceiptMissing init ⊆
      smallRowTwoReceiptMissing init ∪ (smallHistory init)ᶜ := by
  intro omega hmissing
  by_cases hsmall : omega ∈ smallHistory init
  · exact Or.inl ⟨hmissing, hsmall⟩
  · exact Or.inr hsmall

/-- Exact law decomposition.  The last term is not a failure probability: it
contains the early-terminal, tie, and strong-gap branches. -/
theorem law_rowTwoReceiptMissing_le_branch_decomposition
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (rowTwoReceiptMissing init) ≤
      (ENNReal.ofReal
          (2 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 4 +
            Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) +
        law init (smallStrongReceiptMissing init)) +
      law init (smallHistory init)ᶜ := by
  calc
    law init (rowTwoReceiptMissing init) ≤
        law init
          (smallRowTwoReceiptMissing init ∪
            (smallHistory init)ᶜ) :=
      measure_mono (rowTwoReceiptMissing_cover_by_branch init)
    _ ≤ law init (smallRowTwoReceiptMissing init) +
        law init (smallHistory init)ᶜ :=
      measure_union_le _ _
    _ ≤ (ENNReal.ofReal
          (2 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 4 +
            Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) +
          law init (smallStrongReceiptMissing init)) +
        law init (smallHistory init)ᶜ :=
      add_le_add
        (law_smallRowTwoReceiptMissing_le init hinput) le_rfl

/-!
THEOREM LIST
* `no_rowTwoReceipt_of_not_strictGap`
* `no_rowTwoReceipt_of_tie`
* `rowTwoReceiptMissing_eq_univ_of_not_strictGap`
* `rowTwoReceiptMissing_eq_univ_of_tie`
* `law_rowTwoReceiptMissing_eq_one_of_not_strictGap`
* `law_rowTwoReceiptMissing_eq_one_of_tie`
* `not_law_rowTwoReceiptMissing_le_of_not_strictGap`
* `SmallBranchReceiptAt`
* `smallRowTwoReceiptMissing`
* `smallStrongReceiptMissing`
* `smallRowTwoReceiptMissing_cover`
* `law_lateSamplingSeedProducerFailure_closed`
* `law_smallRowTwoReceiptMissing_le`
* `exists_matching_receipts_of_small_history`
* `rowTwoReceiptMissing_cover_by_branch`
* `law_rowTwoReceiptMissing_le_branch_decomposition`

CLOSES
* Refutes the unqualified GoodInput-only receipt and ledger route on tie and
  strong-gap inputs.
* Gives the exact corrected strict-small-gap event.
* Closes its N16 receipt-valued charge from existing original-law theorems.
* Produces matching actual-count receipts outside two named events, without
  `completionBase` or any universal per-log premise.
* Isolates the sole remaining strong-completion event rather than hiding it.

UNFINISHED
* `smallStrongReceiptMissing` has no unconditional bound on main.  Closing it
  requires a direct construction of `Prefix` from `AsyncEntry` and the genuine
  first-four facts, a non-circular phase-5/homogeneous-five producer, all
  completion gates, and the completed row-two snapshot.  `completionFailure`
  alone does not provide these data.
* Therefore no `TwoLevelFuelLedger` theorem with only `GoodInput` can be stated
  for all logs.  The correct final theorem must dispatch the terminal,
  tie/strong, and strict-small-gap branches, applying the global receipt only in the last.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingReceiptScope

end
