import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoActivationProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoSparse

/-!
# Sparse asynchronous entry from an actual drained boundary

The absolute-mass extension costs no further probability. The retained drained
boundary and the successful AsyncEntry are events on the original pair-log
sample, and the deterministic sparse readout applies to that same sample.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoSparseProducer

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping
open PhaseTwoThresholds PhaseTwoHeight PhaseTwoEntryProducer PhaseTwoDrainedSafety
open PhaseTwoActivationProducer

def DoneOrSparseBy {n : ℕ} (init : InputCfg n) (ω : InputLog n) (D : ℕ) : Prop :=
  (∃ u ≤ D, trace init ω u ∈ StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init) ∨
    ∃ s t : ℕ, t ≤ D ∧ StageEventSpec.sparseAsyncEntry init ω s t

theorem drained_outcome_to_sparse {n : ℕ}
    (init : InputCfg n) (hn : 0 < n) (ω : InputLog n) (d N : ℕ)
    (hp : PhaseOneReadyProfile init (trace init ω d))
    (hout : SeedOrStableBy init ω d N)
    (hflood : ω ∉ thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n)
      (firstCrossing init))
    (hheight : ω ∉ heightFailureAt init (firstCrossing init)) :
    DoneOrSparseBy init ω (d + N + StageEventSpec.activationHorizon n) := by
  rcases hout with ⟨u, hdu, hu, hdone⟩ | ⟨s, hds, hs, hfirst, hseed⟩
  · exact Or.inl ⟨u, by omega, hdone⟩
  · obtain ⟨t, ht⟩ := drained_activation_of_not_failures init hn ω
      (firstCrossing init) d s hp hds
      ((firstCrossing_eq_iff init ω s).2 hfirst) hfirst hflood hheight
    exact Or.inr ⟨s, t, by have := ht.deadline; omega,
      PhaseTwoSparse.sparse_async_entry_of_drained init ω d s t hp hds ht⟩

/-- The actual-law post-drain tail, strengthened to sparseAsyncEntry without
an additional error term or a condition on a future success event. -/
theorem drained_sparse_phase_two_entry_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ d : ℕ, σ ω = (d : WithTop ℕ) ∧
        PhaseOneReadyProfile init (trace init ω d) ∧
        ¬ DoneOrSparseBy init ω
          (d + outcomeHorizon init hn + StageEventSpec.activationHorizon n)} ≤
      outcomeBudget n + activationBudget n := by
  classical
  let E : Set (InputLog n) :=
    {ω | ∃ d : ℕ, σ ω = (d : WithTop ℕ) ∧
      PhaseOneReadyProfile init (trace init ω d) ∧
      ¬ SeedOrStableBy init ω d (outcomeHorizon init hn)}
  let A : Set (InputLog n) :=
    thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) (firstCrossing init) ∪
      heightFailureAt init (firstCrossing init)
  have hE : law init E ≤ outcomeBudget n :=
    drained_seed_or_stable_tail_at_past_time init hinput hn σ hσ
  have hnforty : 40 ≤ n := (time_population_bounds hinput.1).2
  have hA : law init A ≤ activationBudget n :=
    activation_union_bound init (by omega) (firstCrossing init) (firstCrossing_past init)
  have hcover :
      {ω | ∃ d : ℕ, σ ω = (d : WithTop ℕ) ∧
        PhaseOneReadyProfile init (trace init ω d) ∧
        ¬ DoneOrSparseBy init ω
          (d + outcomeHorizon init hn + StageEventSpec.activationHorizon n)} ⊆ E ∪ A := by
    rintro ω ⟨d, hd, hp, hbad⟩
    by_cases he : ω ∈ E
    · exact Or.inl he
    by_cases ha : ω ∈ A
    · exact Or.inr ha
    have hout : SeedOrStableBy init ω d (outcomeHorizon init hn) := by
      by_contra hno
      exact he ⟨d, hd, hp, hno⟩
    have hfl : ω ∉ thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n)
        (firstCrossing init) := fun h => ha (Or.inl h)
    have hh : ω ∉ heightFailureAt init (firstCrossing init) := fun h => ha (Or.inr h)
    exact (hbad (drained_outcome_to_sparse init (by omega) ω d
      (outcomeHorizon init hn) hp hout hfl hh)).elim
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add hE hA))

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoSparseProducer

end
