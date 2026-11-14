import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoActivationProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroTwoCalibration

/-!
# N11: the actual Phase-0--2 entry estimate

All post-Phase-0 estimates in this file are supplied by concrete original-law
producers. The single named Phase-0 estimate occurs only as a hypothesis of
the final assembly theorem.

The weak and strong Phase-1 starts are charged separately. Their slightly
larger union budget still fits 2/n^2 for n >= 40. The literal ceiling horizons
fit 965 n H, hence the unchanged earlyHorizon = 1150 n H.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseZeroTwoEntry

open TimeTheorem PairLog PhaseZeroEntry PhaseOneDrain PhaseOneDrainStopping
open PhaseTwoEntryProducer PhaseTwoDrainedSafety PhaseTwoActivationProducer
open PhaseTwoThresholds PhaseTwoHeight StrongGapBackup PhaseZeroTwoCalibration

def phaseZeroFailure {n : ℕ} (init : InputCfg n) : Set (InputLog n) :=
  {ω | ¬ ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
    IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s}

def weakOutcomeFailure {n : ℕ} (init : InputCfg n) (hn : 2 ≤ n) : Set (InputLog n) :=
  {ω | ∃ d : ℕ, firstDrained init ω = (d : WithTop ℕ) ∧
    PhaseOneReadyProfile init (trace init ω d) ∧
    ¬ SeedOrStableBy init ω d (outcomeHorizon init hn)}

def strongOutcomeFailure {n : ℕ} (init : InputCfg n) (hn : 2 ≤ n) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, phaseOneStart init ω = (s : WithTop ℕ) ∧
    PhaseOneEntryProfile init ω s ∧
    ¬ ProfiledOutcomeBy init ω s (outcomeHorizon init hn)}

def activationFailure {n : ℕ} (init : InputCfg n) : Set (InputLog n) :=
  thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) (firstCrossing init) ∪
    heightFailureAt init (firstCrossing init)

def strongBackupFailure {n : ℕ} (init : InputCfg n) : Set (InputLog n) :=
  {ω | n ≤ 120 * gapMagnitude init ∧
    ω ∈ backupFailureAt init n (firstBackup init)}

theorem strong_backup_failure_le {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (strongBackupFailure init) ≤ ENNReal.ofReal (5 / (n : ℝ) ^ 3) := by
  classical
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  by_cases hg : n ≤ 120 * gapMagnitude init
  · exact (measure_mono fun ω hω => hω.2).trans
      (backup_seed_tail_at_past_time init hinput.2.1 (by omega) hg
        (firstBackup init) (firstBackup_past init))
  · have heq : strongBackupFailure init = ∅ := by
      ext ω
      simp only [strongBackupFailure, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false]
      exact fun h => hg h.1
    rw [heq, measure_empty]
    exact zero_le

theorem backup_done_before_deadline {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (u : ℕ) (hg : n ≤ 120 * gapMagnitude init)
    (hseed : BackupSeed n (trace init ω u))
    (hgood : ω ∉ strongBackupFailure init) :
    ∃ v ≤ u + backupHorizon n,
      trace init ω v ∈ StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init := by
  classical
  obtain ⟨r, hr, hru⟩ := exists_firstBackup_before init ω u hseed.2
  have hactualSeed := backup_seed_at_firstBackup init hinput ω r hr
  have hdone :
      trace init ω (r + backupHorizon n) ∈
        StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init := by
    by_contra hbad
    exact hgood ⟨hg, r, hr, hactualSeed, hbad⟩
  exact ⟨r + backupHorizon n, Nat.add_le_add_right hru _, hdone⟩

theorem doneOrAsyncBy_mono {n : ℕ} (init : InputCfg n) (ω : InputLog n)
    {s t : ℕ} (hst : s ≤ t) :
    DoneOrAsyncBy init ω s → DoneOrAsyncBy init ω t := by
  rintro (⟨u, hu, hd⟩ | ⟨S, T, hT, he⟩)
  · exact Or.inl ⟨u, hu.trans hst, hd⟩
  · exact Or.inr ⟨S, T, hT.trans hst, he⟩

theorem strong_profiled_outcome_to_async_or_done {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s N : ℕ) (hg : n ≤ 120 * gapMagnitude init)
    (hout : ProfiledOutcomeBy init ω s N)
    (hflood : ω ∉ thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n)
      (firstCrossing init))
    (hheight : ω ∉ heightFailureAt init (firstCrossing init))
    (hbackup : ω ∉ strongBackupFailure init) :
    DoneOrAsyncBy init ω
      (s + N + StageEventSpec.activationHorizon n + backupHorizon n) := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  rcases hout with ⟨u, hsu, hu, hdone⟩ | ⟨S, hsS, hS, hfirst, hb | hp⟩
  · exact Or.inl ⟨u, by omega, hdone⟩
  · obtain ⟨v, hv, hd⟩ := backup_done_before_deadline init hinput ω S hg hb hbackup
    exact Or.inl ⟨v, by omega, hd⟩
  · have hσ : firstCrossing init ω = (S : WithTop ℕ) :=
      (firstCrossing_eq_iff init ω S).2 hfirst
    have hact := seed_activation_of_not_failures init hinput.2.1 (by omega) ω
      (firstCrossing init) S hσ hfirst hp hflood hheight
    rcases hact with ⟨T, he⟩ | ⟨u, hSu, hu, hb⟩
    · exact Or.inr ⟨S, T, by have := he.deadline; omega, he⟩
    · obtain ⟨v, hv, hd⟩ := backup_done_before_deadline init hinput ω u hg hb hbackup
      exact Or.inl ⟨v, by omega, hd⟩

theorem not_entry_failure_of_done_or_async {n : ℕ}
    (init : InputCfg n) (ω : InputLog n)
    (h : DoneOrAsyncBy init ω (earlyHorizon n)) :
    ω ∉ phaseEntryFailure (StageEventSpec.reviewedStageEvents n init) := by
  rintro ⟨hnotdone, hnotentry⟩
  rcases h with ⟨u, hu, hd⟩ | ⟨S, T, hT, he⟩
  · exact hnotdone ⟨u, hu, hd⟩
  · exact hnotentry ⟨S, T, hT, he⟩

/-- Deterministic cover on actual executions. The only unproved input estimate
will be the measure of phaseZeroFailure in the final theorem. -/
theorem phase_entry_failure_cover {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (hn : 2 ≤ n) :
    phaseEntryFailure (StageEventSpec.reviewedStageEvents n init) ⊆
      phaseZeroFailure init ∪
        (firstDrainedWindowFailure init ∪
          (weakOutcomeFailure init hn ∪
            (strongOutcomeFailure init hn ∪
              (activationFailure init ∪ strongBackupFailure init)))) := by
  classical
  intro ω hbad
  by_cases hzero : ω ∈ phaseZeroFailure init
  · exact Or.inl hzero
  by_cases hdrain : ω ∈ firstDrainedWindowFailure init
  · exact Or.inr (Or.inl hdrain)
  by_cases hweak : ω ∈ weakOutcomeFailure init hn
  · exact Or.inr (Or.inr (Or.inl hweak))
  by_cases hstrong : ω ∈ strongOutcomeFailure init hn
  · exact Or.inr (Or.inr (Or.inr (Or.inl hstrong)))
  by_cases hact : ω ∈ activationFailure init
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hact))))
  by_cases hbackup : ω ∈ strongBackupFailure init
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbackup))))
  exfalso
  have hex : ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
      IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s := by
    by_contra hno
    exact hzero hno
  obtain ⟨s, hs, hfirst, hp⟩ := hex
  have hflood : ω ∉ thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n)
      (firstCrossing init) := fun h => hact (Or.inl h)
  have hheight : ω ∉ heightFailureAt init (firstCrossing init) :=
    fun h => hact (Or.inr h)
  have hcal := combinedHorizon_le_earlyHorizon init hinput.1 hn
  have hnforty : 40 ≤ n := (time_population_bounds hinput.1).2
  by_cases hgap : 40 * (initialGap init).natAbs ≤
      RoleSplitConcentration.mainCount (trace init ω s)
  · obtain ⟨d, hd⟩ := exists_drainedPrefix_of_not_failure init hinput ω s
      hfirst hp hgap hdrain
    have hready := hd.ready_profile hinput
    have hout : SeedOrStableBy init ω d (outcomeHorizon init hn) := by
      by_contra hno
      exact hweak ⟨d, hd.drain_eq, hready, hno⟩
    have he := drained_outcome_to_async init (by omega) ω d
      (outcomeHorizon init hn) hready hout hflood hheight
    have htime : d + outcomeHorizon init hn + StageEventSpec.activationHorizon n ≤
        combinedHorizon init hn := by
      have hdeadline := hd.deadline
      unfold outcomeHorizon combinedHorizon
      omega
    exact not_entry_failure_of_done_or_async init ω
      (doneOrAsyncBy_mono init ω (htime.trans hcal) he) hbad
  · have hstrict : RoleSplitConcentration.mainCount (trace init ω s) <
        40 * gapMagnitude init := by
      simpa only [gapMagnitude] using Nat.lt_of_not_ge hgap
    have hg := gap_floor_of_entry_profile init ω s hp hstrict
    have hout : ProfiledOutcomeBy init ω s (outcomeHorizon init hn) := by
      by_contra hno
      exact hstrong ⟨s, (phaseOneStart_eq_iff init ω s).2 hfirst, hp, hno⟩
    have he := strong_profiled_outcome_to_async_or_done init hinput ω s
      (outcomeHorizon init hn) hg hout hflood hheight hbackup
    have htime :
        s + outcomeHorizon init hn + StageEventSpec.activationHorizon n + backupHorizon n ≤
          combinedHorizon init hn := by
      unfold outcomeHorizon combinedHorizon
      omega
    exact not_entry_failure_of_done_or_async init ω
      (doneOrAsyncBy_mono init ω (htime.trans hcal) he) hbad

/-- N11 with exactly one named external estimate: the separately produced
Phase-0 entry theorem. All subsequent producers are proved in this package. -/
theorem phase_zero_two_entry_estimate {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (phase_zero_entry_estimate :
      law init {ω | ¬ ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
        IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s} ≤
          ENNReal.ofReal (8 / (n : ℝ) ^ 3)) :
    law init (phaseEntryFailure (StageEventSpec.reviewedStageEvents n init)) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
  have hnforty : 40 ≤ n := (time_population_bounds hinput.1).2
  have hn : 2 ≤ n := by omega
  have hzero : law init (phaseZeroFailure init) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 3) := phase_zero_entry_estimate
  have hdrain := firstDrainedWindowFailure_le init hinput
  have hweak : law init (weakOutcomeFailure init hn) ≤ outcomeBudget n :=
    drained_seed_or_stable_tail_at_past_time init hinput hn
      (firstDrained init) (firstDrained_past init)
  have hstrong : law init (strongOutcomeFailure init hn) ≤ outcomeBudget n :=
    entry_profile_outcome_tail_at_past_time init hinput hn
      (phaseOneStart init) (phaseOneStart_past init)
  have hact : law init (activationFailure init) ≤ activationBudget n :=
    activation_union_bound init (by omega) (firstCrossing init) (firstCrossing_past init)
  have hbackup := strong_backup_failure_le init hinput
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hheightcast : ENNReal.ofReal (1 / (n : ℝ) ^ 8) = 1 / (n : ℝ≥0∞) ^ 8 := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hnpos 8), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  calc
    law init (phaseEntryFailure (StageEventSpec.reviewedStageEvents n init)) ≤
      law init (phaseZeroFailure init ∪
        (firstDrainedWindowFailure init ∪
          (weakOutcomeFailure init hn ∪
            (strongOutcomeFailure init hn ∪
              (activationFailure init ∪ strongBackupFailure init))))) :=
      measure_mono (phase_entry_failure_cover init hinput hn)
    _ ≤ law init (phaseZeroFailure init) +
        (law init (firstDrainedWindowFailure init) +
          (law init (weakOutcomeFailure init hn) +
            (law init (strongOutcomeFailure init hn) +
              (law init (activationFailure init) + law init (strongBackupFailure init))))) := by
      apply (measure_union_le _ _).trans
      refine add_le_add le_rfl ?_
      apply (measure_union_le _ _).trans
      refine add_le_add le_rfl ?_
      apply (measure_union_le _ _).trans
      refine add_le_add le_rfl ?_
      apply (measure_union_le _ _).trans
      refine add_le_add le_rfl ?_
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 3) +
        (1 / (n : ℝ≥0∞) ^ 2 +
          (outcomeBudget n + (outcomeBudget n +
            (activationBudget n + ENNReal.ofReal (5 / (n : ℝ) ^ 3))))) :=
      add_le_add hzero (add_le_add hdrain
        (add_le_add hweak (add_le_add hstrong (add_le_add hact hbackup))))
    _ = two_start_probabilityBudget n := by
      unfold outcomeBudget activationBudget two_start_probabilityBudget
      rw [hheightcast]
      ring
    _ ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) :=
      two_start_probabilityBudget_le n hnforty

end Ripple.PopulationProtocol.ExactMajority.PhaseZeroTwoEntry

end
