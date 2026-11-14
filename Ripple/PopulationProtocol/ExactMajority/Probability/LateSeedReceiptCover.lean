-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedReceiptCover.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReceiptCoverData

/-!
# Deterministic N16 receipt cover and final strengthening estimate

The three stochastic families are already fixed:

* `protectedTestFailure init = globalHourFailure init`;
* `nearTestFailure init = globalTerminalFailure init ∪ globalNearLevelFailure init`;
* `oldIndexFailure (receiptOldBlockSelector init)`.

This file proves only the deterministic complement implication and then invokes
the original-law estimates from `LateSeedProtectedTestFailure`, `LateSeedNearTestFailure`, and
`LateSeedOldIndexFailure`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open PhaseThreeClockProducer

open TimeTheorem PairLog PhaseOneDrain StageEventSpec
open AveragingSparseEntry AveragingEventInterface
open AveragingDominantLevelSplice AveragingGlobalFailureSplice
open AveragingHourEvents AveragingHourPrefix
open AveragingTerminalPackages AveragingHourStops
open AveragingObservedHourTails AveragingSeededDelay
open LateSamplingSeedReceipt AveragingFixedSeedHours AveragingIntegerPotential

/-- The requested deterministic `hcover`.  Every use of a future successful
history is outside the adapted selector fibre; it is used only to identify the
actual deterministic path after the three original-law failure events have
already been fixed. -/
theorem late_sampling_seed_receipt_safe_cover
    {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    lateSamplingSeedProducerSafeFailure init ⊆
      protectedTestFailure init ∪
        (nearTestFailure init ∪
          oldIndexFailure (receiptOldBlockSelector init)) := by
  intro ω hfailure
  rw [mem_lateSamplingSeedProducerSafeFailure_iff init ω] at hfailure
  obtain ⟨S, T, ρ, hhistory, hnonzero, hgap, hseed, hnoReceipt⟩ := hfailure
  by_cases hprotected : ω ∈ protectedTestFailure init
  · exact Or.inl hprotected
  by_cases hnear : ω ∈ nearTestFailure init
  · exact Or.inr (Or.inl hnear)
  by_cases hold : ω ∈ oldIndexFailure (receiptOldBlockSelector init)
  · exact Or.inr (Or.inr hold)
  have hvalid : validInitial init := hinput.2.1
  have hn : timePopulationThreshold ≤ n := hinput.1
  obtain ⟨w, H⟩ :=
    (reviewedStageEvents_clockGood_iff init ω S T ρ).1
      hhistory.2.2.1
  have hSearly : S ≤ earlyHorizon n := H.entry.order.trans hhistory.1
  let p := selectedSchedule init (trace init ω S)
  let ell := p.1
  let σ := selectedSign init
  have hs :
      DominantScale init (trace init ω S) p.1 ∧
      p.2 = p.1 ∧
      AdmissibleSchedule (n := n) p ∧
      ω ∈ ClockScope init S p.1 p.2 (selectedSign init) := by
    simpa only [p] using strict_schedule_scope H hnonzero hgap
  have hpEq : p = (ell, ell) := by
    apply Prod.ext
    · rfl
    · simpa only [ell] using hs.2.1
  have hnoHours :
      ω ∉ hourFailure
        (hourSuccess init (seedTime init 3) ell σ) ell := by
    intro hbad
    apply hprotected
    rw [mem_protectedTestFailure_iff init ω]
    refine ⟨S, hSearly, hseed, ?_⟩
    change ω ∈ scheduledHourFailure init S p
    rw [scheduledHourFailure, if_pos hs.2.2.1]
    refine ⟨hs.2.2.2, ?_⟩
    rw [hs.2.1]
    exact hbad
  have hterminal :
      ReceiptTerminalCheckpointData init ω S w ell σ := by
    rcases receipt_terminal_checkpoint_data_or_failure
        (init := init) hvalid hn hseed H
        (selectedSign_winning init hnonzero) hs.1
        hnoHours with hdata | hbad
    · exact hdata
    · exfalso
      apply hnear
      rw [mem_nearTestFailure_iff init ω]
      apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨S, ⟨⟨hSearly, hseed⟩, ?_⟩⟩
      dsimp
      refine ⟨w.start (p.1 + 2), ?_, ?_⟩
      · exact hourStart_phaseThreeSeed_clockHistory H (p.1 + 2)
          (by simpa only [p] using hs.1.2.1)
      · simpa only [p, ell, σ, hs.2.1, seedCounts] using hbad
  have hnearEx :
      ∃ c : ℕ, ReceiptNearCheckpointData init ω S T ρ ell σ c := by
    rcases receipt_near_checkpoint_data_or_failure
        (init := init) hvalid hn hseed H hs.1
        hnoHours with hdata | hbad
    · exact hdata
    · exfalso
      apply hnear
      rw [mem_nearTestFailure_iff init ω]
      apply Or.inr
      refine ⟨S, hSearly, hseed, ?_⟩
      change ω ∈ scheduledNearLevelFailure init S p
      have hadm : nearLevelScheduleAdmissible n p :=
        ⟨hs.1.1, hs.1.2.1⟩
      rw [scheduledNearLevelFailure, dif_pos hadm]
      change ∃ s : ℕ,
        hourStart init (seedTime init 3) (_ + 1) ω =
            (s : WithTop ℕ) ∧
          ω ∈ twoLevelBlockFailure init s (selectedSign init) _ n
            (seedCounts init S ω).1 (seedCounts init S ω).2
      refine ⟨w.start (p.1 + 1), ?_, ?_⟩
      · exact hourStart_phaseThreeSeed_clockHistory H (p.1 + 1)
          (by have := hs.1.2.1; omega)
      · exact hbad
  have holdZero :
      augmentedPhiNat (ell - terminalCutoff n)
        (trace init ω w.cap) = 0 :=
    receipt_old_checkpoint_zero_of_not_failure init hvalid hn
      hseed H hs.1 hpEq
      hnoHours hold
  have hcapρ : w.cap < ρ :=
    lt_of_le_of_lt (Nat.le_add_right _ _) H.protected_settling
  obtain ⟨cNear, hnearData⟩ := hnearEx
  have hreceipt :
      LateSamplingSeedReceipt init
        (timeMainCount (trace init ω S)) ell σ
        (trace init ω ρ) :=
    lateSamplingSeedReceipt_of_checkpoint_data
      (init := init) (ω := ω) (S := S) (T := T) (ρ := ρ)
      (s := cNear) (u := w.cap)
      (M := timeMainCount (trace init ω S))
      (ell := ell) (w := w) (σ := σ)
      hvalid H hseed hn H.all_before_cap hcapρ rfl
      (selectedSign_winning init hnonzero) hnonzero hgap
      hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2
      hterminal.protected_credit hterminal.minority hterminal.potential
      hnearData.seed_le hnearData.before_exit
      hnearData.barrier hnearData.exception_bound hnearData.potential_bound
      holdZero
  exact (hnoReceipt ⟨ell, σ, hreceipt⟩).elim

/-- N16, exact headline. -/
theorem late_seed_strengthening_estimate
    {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init
      {ω | ∃ S T ρ : ℕ,
        successfulHistory (reviewedStageEvents n init) ω S T ρ ∧
        0 < gapMagnitude init ∧
        40 * gapMagnitude init < timeMainCount (trace init ω S) ∧
        ¬ (∃ ell σ,
          LateSeedReadout init
            (timeMainCount (trace init ω S)) ell σ
            (trace init ω ρ))} ≤
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
  have hsub :
      {ω | ∃ S T ρ : ℕ,
        successfulHistory (reviewedStageEvents n init) ω S T ρ ∧
        0 < gapMagnitude init ∧
        40 * gapMagnitude init < timeMainCount (trace init ω S) ∧
        ¬ (∃ ell σ,
          LateSeedReadout init
            (timeMainCount (trace init ω S)) ell σ
            (trace init ω ρ))} ⊆
        lateSamplingSeedProducerFailure init := by
    rintro ω ⟨S, T, ρ, hhistory, hnonzero, hgap, hbad⟩
    rw [mem_lateSamplingSeedProducerFailure_iff init ω]
    refine ⟨S, T, ρ, hhistory, hnonzero, hgap, ?_⟩
    rintro ⟨ell, σ, hseed⟩
    exact hbad ⟨ell, σ, hseed.toLateSeedReadout⟩
  exact (measure_mono hsub).trans (by
    simpa only [lateSamplingSeedProducerFailure] using hreceipt)

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
