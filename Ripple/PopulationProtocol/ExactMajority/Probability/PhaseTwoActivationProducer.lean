import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoHeight
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoDrainedSafety
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongGapBackupProfileTail

/-!
# Genuine first-seed activation on the original law

The threshold epidemic and the height-before-backup event are charged under
the original pair-log law. The general branch reaches AsyncEntry or a backup
seed. From an actual drained boundary, the preserved small-bias range excludes
backup throughout the low-height activation interval, so the same two failure
events give AsyncEntry itself.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoActivationProducer

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping
open PhaseTwoThresholds PhaseTwoSeedProfile PhaseTwoActivation PhaseTwoHeight
open PhaseTwoEntryProducer PhaseTwoDrainedSafety

def activationBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 / (n : ℝ) ^ 5) + ENNReal.ofReal (1 / (n : ℝ) ^ 8)

theorem active_clock_callback_of_not_height_failure {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (σ : InputLog n → WithTop ℕ) (s : ℕ)
    (hs : σ ω = (s : WithTop ℕ))
    (hseed : StageEventSpec.SeedProfile n init (trace init ω s))
    (hgood : ω ∉ heightFailureAt init σ) :
    ∀ u, s ≤ u → u ≤ s + StageEventSpec.activationHorizon n →
      (∀ a ∈ trace init ω u, a.phase.val ≠ 10) →
        ActiveClockBelow (trace init ω u) := by
  intro u hsu hu hno
  apply no_height_active_clock_below
  intro hheight
  exact hgood ⟨s, hs, hseed, u, hsu, hu, hheight,
    (no_backup_iff _).mpr hno⟩

theorem first_all_after_seed_of_not_failure {n : ℕ}
    (init : InputCfg n) (hn : 0 < n) (ω : InputLog n)
    (σ : InputLog n → WithTop ℕ) (s : ℕ) (hs : σ ω = (s : WithTop ℕ))
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) s)
    (hseed : StageEventSpec.SeedProfile n init (trace init ω s))
    (hgood : ω ∉ thresholdFailureAt init n 3
      (StageEventSpec.activationHorizon n) σ) :
    ∃ t : ℕ,
      StageEventSpec.firstHit (StageEventSpec.allGE (n := n) 3) (trace init ω) t ∧
      s ≤ t ∧ t ≤ s + StageEventSpec.activationHorizon n := by
  have hend : ∀ a ∈ trace init ω (s + StageEventSpec.activationHorizon n),
      3 ≤ a.phase.val := by
    by_contra hnot
    exact hgood ⟨s, hs, hseed.card_eq, hfirst.1, hnot⟩
  exact exists_first_all_after_first_seed init ω n 3 s
    (StageEventSpec.activationHorizon n) hn hseed.card_eq
    (first_phase_seed_of_profile init ω s hfirst hseed) hend

def SeedActivationBy {n : ℕ} (init : InputCfg n) (ω : InputLog n) (s : ℕ) : Prop :=
  (∃ t : ℕ, StageEventSpec.AsyncEntry init ω s t) ∨
    ∃ u : ℕ, s ≤ u ∧ u ≤ s + StageEventSpec.activationHorizon n ∧
      StrongGapBackup.BackupSeed n (trace init ω u)

theorem seed_activation_of_not_failures {n : ℕ}
    (init : InputCfg n) (hvalid : validInitial init) (hn : 0 < n)
    (ω : InputLog n) (σ : InputLog n → WithTop ℕ) (s : ℕ)
    (hs : σ ω = (s : WithTop ℕ))
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) s)
    (hseed : StageEventSpec.SeedProfile n init (trace init ω s))
    (hflood : ω ∉ thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) σ)
    (hheight : ω ∉ heightFailureAt init σ) :
    SeedActivationBy init ω s := by
  classical
  have hlow := active_clock_callback_of_not_height_failure init ω σ s hs hseed hheight
  by_cases hb : ∃ u : ℕ, s ≤ u ∧ u ≤ s + StageEventSpec.activationHorizon n ∧
      Backup (trace init ω u)
  · right
    obtain ⟨u, hsu, hu, hbackup⟩ := hb
    exact ⟨u, hsu, hu,
      (Protocol.reachable_card_eq (trace_reachable init ω hsu)).trans hseed.card_eq,
      hbackup⟩
  · left
    obtain ⟨t, htfirst, hst, ht⟩ :=
      first_all_after_seed_of_not_failure init hn ω σ s hs hfirst hseed hflood
    have hno : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u, a.phase.val ≠ 10 := by
      intro u hsu hut
      apply (no_backup_iff _).mp
      intro hbackup
      exact hb ⟨u, hsu, hut.trans ht, hbackup⟩
    exact ⟨t, async_entry_of_low_clock_no_backup init hvalid ω s t
      hfirst htfirst hst ht hseed
      (fun u hsu hut => hlow u hsu (hut.trans ht) (hno u hsu hut)) hno⟩

/-- The weak branch gets AsyncEntry itself: low Clock height plus the
unconditional drained small-bias invariant excludes backup during activation. -/
theorem drained_activation_of_not_failures {n : ℕ}
    (init : InputCfg n) (hn : 0 < n) (ω : InputLog n)
    (σ : InputLog n → WithTop ℕ) (d s : ℕ)
    (hp : PhaseOneReadyProfile init (trace init ω d)) (hds : d ≤ s)
    (hs : σ ω = (s : WithTop ℕ))
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) s)
    (hflood : ω ∉ thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) σ)
    (hheight : ω ∉ heightFailureAt init σ) :
    ∃ t : ℕ, StageEventSpec.AsyncEntry init ω s t := by
  have hseed := ready_first_crossing_seed_profile init ω d s hp hds hfirst
  obtain ⟨t, htfirst, hst, ht⟩ :=
    first_all_after_seed_of_not_failure init hn ω σ s hs hfirst hseed hflood
  have hlow := active_clock_callback_of_not_height_failure init ω σ s hs hseed hheight
  exact ⟨t, drained_async_entry_of_low_clock init ω d s t hp hds
    hfirst htfirst hst ht hseed (fun u hsu hut => hlow u hsu (hut.trans ht))⟩

def seedActivationFailure {n : ℕ} (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
    StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3) (trace init ω) s ∧
    StageEventSpec.SeedProfile n init (trace init ω s) ∧
    ¬ SeedActivationBy init ω s}

theorem seed_activation_failure_cover {n : ℕ}
    (init : InputCfg n) (hvalid : validInitial init) (hn : 0 < n)
    (σ : InputLog n → WithTop ℕ) :
    seedActivationFailure init σ ⊆
      thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) σ ∪
        heightFailureAt init σ := by
  classical
  rintro ω ⟨s, hs, hf, hp, hbad⟩
  by_cases hfl : ω ∈ thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) σ
  · exact Or.inl hfl
  by_cases hh : ω ∈ heightFailureAt init σ
  · exact Or.inr hh
  exact (hbad (seed_activation_of_not_failures init hvalid hn ω σ s hs hf hp hfl hh)).elim

theorem activation_union_bound {n : ℕ}
    (init : InputCfg n) (hn : 4 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init (thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) σ ∪
      heightFailureAt init σ) ≤ activationBudget n := by
  have hf := (threshold_spread_at_past_time init (by omega) 3 (by decide)
    (StageEventSpec.activationHorizon n) σ hσ).trans
      (activation_thresholdBudget_le (by omega))
  have hh := activation_height_tail_at_past_time init hn σ hσ
  exact (measure_union_le _ _).trans (add_le_add hf hh)

theorem seed_activation_tail_at_past_time {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init (seedActivationFailure init σ) ≤ activationBudget n := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  exact (measure_mono (seed_activation_failure_cover init hinput.2.1 (by omega) σ)).trans
    (activation_union_bound init (by omega) σ hσ)

def drainedActivationFailure {n : ℕ} (init : InputCfg n)
    (σ : InputLog n → WithTop ℕ) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
    (∃ d ≤ s, PhaseOneReadyProfile init (trace init ω d)) ∧
    StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3) (trace init ω) s ∧
    ¬ ∃ t : ℕ, StageEventSpec.AsyncEntry init ω s t}

theorem drained_activation_failure_cover {n : ℕ}
    (init : InputCfg n) (hn : 0 < n) (σ : InputLog n → WithTop ℕ) :
    drainedActivationFailure init σ ⊆
      thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) σ ∪
        heightFailureAt init σ := by
  classical
  rintro ω ⟨s, hs, ⟨d, hds, hp⟩, hf, hbad⟩
  by_cases hfl : ω ∈ thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n) σ
  · exact Or.inl hfl
  by_cases hh : ω ∈ heightFailureAt init σ
  · exact Or.inr hh
  exact (hbad (drained_activation_of_not_failures init hn ω σ d s
    hp hds hs hf hfl hh)).elim

theorem drained_activation_tail_at_past_time {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init (drainedActivationFailure init σ) ≤ activationBudget n := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  exact (measure_mono (drained_activation_failure_cover init (by omega) σ)).trans
    (activation_union_bound init (by omega) σ hσ)

def DoneOrAsyncBy {n : ℕ} (init : InputCfg n) (ω : InputLog n) (D : ℕ) : Prop :=
  (∃ u ≤ D, trace init ω u ∈ StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init) ∨
    ∃ s t : ℕ, t ≤ D ∧ StageEventSpec.AsyncEntry init ω s t

theorem drained_outcome_to_async {n : ℕ}
    (init : InputCfg n) (hn : 0 < n) (ω : InputLog n) (d N : ℕ)
    (hp : PhaseOneReadyProfile init (trace init ω d))
    (hout : SeedOrStableBy init ω d N)
    (hflood : ω ∉ thresholdFailureAt init n 3 (StageEventSpec.activationHorizon n)
      (firstCrossing init))
    (hheight : ω ∉ heightFailureAt init (firstCrossing init)) :
    DoneOrAsyncBy init ω (d + N + StageEventSpec.activationHorizon n) := by
  rcases hout with ⟨u, hdu, hu, hdone⟩ | ⟨s, hds, hs, hfirst, hseed⟩
  · exact Or.inl ⟨u, by omega, hdone⟩
  · obtain ⟨t, ht⟩ := drained_activation_of_not_failures init hn ω
      (firstCrossing init) d s hp hds
      ((firstCrossing_eq_iff init ω s).2 hfirst) hfirst hflood hheight
    exact Or.inr ⟨s, t, by have := ht.deadline; omega, ht⟩

/-- Post-drain Phase-2 entry, with the exact asynchronous target. Both the
recorded start and the retained drained profile occur inside the joint event. -/
theorem drained_phase_two_entry_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ d : ℕ, σ ω = (d : WithTop ℕ) ∧
        PhaseOneReadyProfile init (trace init ω d) ∧
        ¬ DoneOrAsyncBy init ω
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
        ¬ DoneOrAsyncBy init ω
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
    exact (hbad (drained_outcome_to_async init (by omega) ω d
      (outcomeHorizon init hn) hp hout hfl hh)).elim
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add hE hA))

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoActivationProducer

end
