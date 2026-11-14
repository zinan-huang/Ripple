-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedSparseEntry.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingSparseEntry

/-!
# The original-input sparse-entry charge for late strengthening

The event in N16 is a successful strict-small-gap history. Its averaging
readout may already hold, so the N13 exception theorem restricted to
phaseAveragingFailure cannot be applied to it directly.

This file reuses the compiled Phase-0 and weak-drain estimates with the
strict-gap premise of the late event. The resulting exception costs 2/n^2
under law init. The safe seed is the genuine first Phase-3 seed, and its
safety predicate is measurable at that seed. No future clock success is
used as a conditional law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem PairLog StageEventSpec
open PhaseZeroEntry PhaseOneDrainStopping PhaseTwoDrainedSafety
open AveragingEventInterface AveragingSparseEntry

variable {n : ℕ}

/-- Successful histories in the strict-small-gap branch, with their
original seed Main count retained. -/
def smallHistory (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ S T ρ : ℕ,
    successfulHistory (reviewedStageEvents n init) ω S T ρ ∧
      0 < gapMagnitude init ∧
      40 * gapMagnitude init < timeMainCount (trace init ω S)}

/-- The literal failure event in the N16 headline. -/
def lateSeedFailure (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ S T ρ : ℕ,
    successfulHistory (reviewedStageEvents n init) ω S T ρ ∧
      0 < gapMagnitude init ∧
      40 * gapMagnitude init < timeMainCount (trace init ω S) ∧
      ¬ (∃ ell σ,
        LateSeedReadout init (timeMainCount (trace init ω S))
          ell σ (trace init ω ρ))}

theorem lateSeedFailure_subset_smallHistory (init : InputCfg n) :
    lateSeedFailure init ⊆ smallHistory init := by
  rintro ω ⟨S, T, ρ, hh, hn, hg, _⟩
  exact ⟨S, T, ρ, hh, hn, hg⟩

/-- A safe sparse-entry witness belongs to the very same first seed as the
retained successful history; one cannot replace it by a later snapshot. -/
theorem safeSparseSeed_at_successfulHistory
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    (hh : successfulHistory (reviewedStageEvents n init) ω S T ρ)
    (hsafe : ω ∈ safeSparseEntry init) :
    SafeSparseSeed init ω S := by
  have hentry : AsyncEntry init ω S T := hh.2.1
  exact ⟨hentry.first_phase_seed, safeSeedState_at_entry hentry hsafe⟩

/-- The safe predicate used at the first seed is a genuine prefix event. -/
theorem late_safe_seed_past (init : InputCfg n) (S : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 S]
      {ω | SafeSparseSeed init ω S} :=
  safeSparseSeed_past init S

/-- Successful small histories without a safe sparse seed are covered by
the already proved Phase-0 and weak-drain exceptions. -/
theorem smallHistory_sparse_failure_cover
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    smallHistory init \ safeSparseEntry init ⊆
      PhaseZeroTwoEntry.phaseZeroFailure init ∪ firstDrainedWindowFailure init := by
  classical
  intro ω hbad
  by_cases hzero : ω ∈ PhaseZeroTwoEntry.phaseZeroFailure init
  · exact Or.inl hzero
  by_cases hdrain : ω ∈ firstDrainedWindowFailure init
  · exact Or.inr hdrain
  exfalso
  have hphaseZero : ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
      IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s := by
    by_contra hnone
    exact hzero hnone
  obtain ⟨s, _, hfirst, hprofile⟩ := hphaseZero
  obtain ⟨S, T, ρ, hhistory, _, hsmall⟩ := hbad.1
  obtain ⟨w, hclock⟩ := hhistory.2.2.1
  have hmain := mainCount_at_seed init ω s S T hprofile hclock.entry
  have hweak : 40 * (initialGap init).natAbs ≤
      RoleSplitConcentration.mainCount (trace init ω s) := by
    change 40 * gapMagnitude init ≤ _
    rw [← hmain]
    exact hsmall.le
  obtain ⟨d, hd⟩ := exists_drainedPrefix_of_not_failure
    init hinput ω s hfirst hprofile hweak hdrain
  have hready := hd.ready_profile hinput
  have hdS : d ≤ S :=
    (all_one_time_lt_seed init ω d S hready.all_one hclock.entry.seed_first).le
  exact hbad.2 ⟨S,
    safeSparseSeed_of_drained_clockHistory init ω d S T ρ hready hdS hclock⟩

/-- The first term of the N16 budget is an actual original-law estimate.
It uses neither the N12 headline nor the N13 headline. -/
theorem smallHistory_sparse_entry_exception
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (smallHistory init \ safeSparseEntry init) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
  have hnforty : 40 ≤ n := (time_population_bounds hinput.1).2
  have hzero : law init (PhaseZeroTwoEntry.phaseZeroFailure init) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 3) :=
    PhaseZeroEntryProducer.phase_zero_entry_estimate init hinput
  have hdrain := firstDrainedWindowFailure_le init hinput
  calc
    law init (smallHistory init \ safeSparseEntry init) ≤
        law init (PhaseZeroTwoEntry.phaseZeroFailure init ∪
          firstDrainedWindowFailure init) :=
      measure_mono (smallHistory_sparse_failure_cover init hinput)
    _ ≤ law init (PhaseZeroTwoEntry.phaseZeroFailure init) +
        law init (firstDrainedWindowFailure init) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 3) + 1 / (n : ℝ≥0∞) ^ 2 :=
      add_le_add hzero hdrain
    _ ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) :=
      sparse_entry_error_budget (by omega)

/-- The safe sparse-entry charge applies to the literal late-seed failure,
even though that event intersects successful averaging. -/
theorem late_seed_sparse_entry_exception
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lateSeedFailure init \ safeSparseEntry init) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
  have hsub : lateSeedFailure init \ safeSparseEntry init ⊆
      smallHistory init \ safeSparseEntry init := by
    intro ω hω
    exact ⟨lateSeedFailure_subset_smallHistory init hω.1, hω.2⟩
  exact (measure_mono hsub).trans (smallHistory_sparse_entry_exception init hinput)

/-- Exact separation of the paid sparse-entry exception from the still
unproved successful-seed strengthening. This is not the N16 headline. -/
theorem late_seed_failure_after_sparse_entry
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lateSeedFailure init) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
        law init (lateSeedFailure init ∩ safeSparseEntry init) := by
  classical
  have hsub : lateSeedFailure init ⊆
      (lateSeedFailure init \ safeSparseEntry init) ∪
        (lateSeedFailure init ∩ safeSparseEntry init) := by
    intro ω hω
    by_cases hs : ω ∈ safeSparseEntry init
    · exact Or.inr ⟨hω, hs⟩
    · exact Or.inl ⟨hω, hs⟩
  calc
    law init (lateSeedFailure init) ≤
        law init ((lateSeedFailure init \ safeSparseEntry init) ∪
          (lateSeedFailure init ∩ safeSparseEntry init)) :=
      measure_mono hsub
    _ ≤ law init (lateSeedFailure init \ safeSparseEntry init) +
        law init (lateSeedFailure init ∩ safeSparseEntry init) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
        law init (lateSeedFailure init ∩ safeSparseEntry init) :=
      add_le_add (late_seed_sparse_entry_exception init hinput) le_rfl

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
