import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneTimer
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoDispatchAmplification
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoSeedProfile
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongGapBackupTail

/-!
# Actual first-seed production after Phase 1

A timer seed, a threshold-2 epidemic, and two dispatch blocks are composed
at genuine observed boundaries. Every failure event is measured under
the original pair-log law. No successful future event is conditioned on.

The endpoint alternative is correct stable output, an observed backup
seed, or the genuine first Phase-3 seed with the pinned SeedProfile.
The subsequent AdvancedProfile construction is a separate activation step.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoEntryProducer

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping PhaseOneTimer
open PhaseTwoThresholds PhaseTwoDispatchAmplification PhaseTwoSeedProfile

def firstAllTwo {n : ℕ} (init : InputCfg n) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (StageEventSpec.allGE (n := n) 2)

theorem firstAllTwo_past {n : ℕ} (init : InputCfg n) :
    PairLogPastTime (firstAllTwo init) :=
  exitTime_pairLogPastTime init (StageEventSpec.allGE (n := n) 2)

def firstCrossing {n : ℕ} (init : InputCfg n) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (StageEventSpec.someGE (n := n) 3)

theorem firstCrossing_past {n : ℕ} (init : InputCfg n) :
    PairLogPastTime (firstCrossing init) :=
  exitTime_pairLogPastTime init (StageEventSpec.someGE (n := n) 3)

theorem firstCrossing_eq_iff {n : ℕ} (init : InputCfg n) (ω : InputLog n) (t : ℕ) :
    firstCrossing init ω = (t : WithTop ℕ) ↔
      StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3) (trace init ω) t :=
  exitTime_eq_iff_firstHit init (StageEventSpec.someGE (n := n) 3) ω t

def outcomeHorizon {n : ℕ} (init : InputCfg n) (hn : 2 ≤ n) : ℕ :=
  timerHorizon n + StageEventSpec.activationHorizon n + dispatchHorizon init n hn

def outcomeBudget (n : ℕ) : ℝ≥0∞ :=
  1 / (n : ℝ≥0∞) ^ 4 + 3 / (n : ℝ≥0∞) ^ 5

def noOutcomeFailure {n : ℕ} (init : InputCfg n) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧ TimerEntry n (trace init ω s) ∧
    ∀ k ≤ outcomeHorizon init hn, ¬ ObservedOutcome init (trace init ω (s + k))}

theorem no_outcome_failure_cover {n : ℕ}
    (init : InputCfg n) (hvalid : validInitial init) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) :
    noOutcomeFailure init hn σ ⊆
      timerFailure init σ ∪
        (thresholdFailureAt init n 2 (StageEventSpec.activationHorizon n) (firstLater init) ∪
          doubleDispatchFailure init n hn (firstAllTwo init)) := by
  classical
  rintro ω ⟨s, hs, hentry, hno⟩
  by_cases htimer : ω ∈ timerFailure init σ
  · exact Or.inl htimer
  by_cases hflood : ω ∈ thresholdFailureAt init n 2
      (StageEventSpec.activationHorizon n) (firstLater init)
  · exact Or.inr (Or.inl hflood)
  by_cases hdispatch : ω ∈ doubleDispatchFailure init n hn (firstAllTwo init)
  · exact Or.inr (Or.inr hdispatch)
  exfalso
  obtain ⟨r, hr, hsr, hrbound⟩ :=
    exists_firstLater_of_not_failure init σ ω s hs hentry htimer
  have hrfirst := (firstLater_eq_iff init ω r).1 hr
  have hupper (u : ℕ) (hsu : s ≤ u) (hu : u ≤ s + outcomeHorizon init hn) :
      ∀ a ∈ trace init ω u, a.phase.val ≤ 2 := by
    intro a ha
    have hnone := hno (u - s) (by omega)
    have heq : s + (u - s) = u := by omega
    rw [heq] at hnone
    by_contra h
    exact hnone (Or.inr ⟨a, ha, by omega⟩)
  have hrend : r ≤ s + outcomeHorizon init hn := by
    unfold outcomeHorizon
    omega
  have hrseed : firstPhaseSeed init 2 r ω := by
    constructor
    · obtain ⟨a, ha, hp⟩ := hrfirst.1
      exact ⟨a, ha, Nat.le_antisymm (hupper r hsr hrend a ha) hp⟩
    · intro u hu a ha
      exact Nat.lt_of_not_ge (fun hp => hrfirst.2 u hu ⟨a, ha, hp⟩)
  have hcardr : (trace init ω r).card = n :=
    (Protocol.reachable_card_eq (trace_reachable init ω hsr)).trans hentry.1.1
  have hflooded : ∀ a ∈ trace init ω (r + StageEventSpec.activationHorizon n),
      2 ≤ a.phase.val := by
    by_contra hbad
    exact hflood ⟨r, hr, hcardr, hrfirst.1, hbad⟩
  obtain ⟨t, htfirst, hrt, htbound⟩ :=
    exists_first_all_after_first_seed init ω n 2 r (StageEventSpec.activationHorizon n)
      (by omega) hcardr hrseed hflooded
  have hst : s ≤ t := hsr.trans hrt
  have ht : firstAllTwo init ω = (t : WithTop ℕ) :=
    (exitTime_eq_iff_firstHit init (StageEventSpec.allGE (n := n) 2) ω t).2 htfirst
  have hwindow : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 2 := by
    intro u hsu hut a ha
    refine ⟨phase_lower_reachable 1 _ _ (trace_reachable init ω hsu)
      (fun b hb => (hentry.1.2 b hb).symm.le) a ha, ?_⟩
    apply hupper u hsu
    · unfold outcomeHorizon
      omega
    · exact ha
  have hcardt : (trace init ω t).card = n :=
    (Protocol.reachable_card_eq (trace_reachable init ω hst)).trans hentry.1.1
  have hpure : ∀ a ∈ trace init ω t, a.phase.val = 2 := by
    intro a ha
    exact Nat.le_antisymm (hwindow t hst le_rfl a ha).2 (htfirst.1 a ha)
  have hprov :=
    PhaseTwoProvenance.pure_phase_two_provenance_from_history init ω n s t
      hvalid hst hentry.1.2 hwindow hcardt hpure
  apply hdispatch
  refine ⟨t, ht, hprov, ?_, ?_⟩
  · intro htarget
    have htime : t + Phase2OutcomeWork.commonHorizon init n hn ≤
        s + outcomeHorizon init hn := by
      unfold outcomeHorizon dispatchHorizon
      omega
    have hns := hno ((t + Phase2OutcomeWork.commonHorizon init n hn) - s) (by omega)
    have heq : s + ((t + Phase2OutcomeWork.commonHorizon init n hn) - s) =
        t + Phase2OutcomeWork.commonHorizon init n hn := by omega
    rw [heq] at hns
    exact hns (target_implies_observed init _ n htarget)
  · intro htarget
    have htime : t + dispatchHorizon init n hn ≤ s + outcomeHorizon init hn := by
      unfold outcomeHorizon
      omega
    have hns := hno ((t + dispatchHorizon init n hn) - s) (by omega)
    have heq : s + ((t + dispatchHorizon init n hn) - s) =
        t + dispatchHorizon init n hn := by omega
    rw [heq] at hns
    exact hns (target_implies_observed init _ n htarget)

/-- Uniform original-law production from any observed Phase-1 boundary
with an actual Clock. The start time may be infinite outside this joint event. -/
theorem phase_one_outcome_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init (noOutcomeFailure init hn σ) ≤ outcomeBudget n := by
  have ht := phase_one_timer_conditional_producer init hn σ hσ
  have hf := (threshold_spread_at_past_time init hn 2 (by decide)
    (StageEventSpec.activationHorizon n) (firstLater init) (firstLater_past init)).trans
      (activation_thresholdBudget_le hn)
  have hd := double_dispatch_at_past_time init n hn
    (firstAllTwo init) (firstAllTwo_past init)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcast : ENNReal.ofReal (2 / (n : ℝ) ^ 5) = 2 / (n : ℝ≥0∞) ^ 5 := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    norm_num
  rw [hcast] at hf
  calc law init (noOutcomeFailure init hn σ) ≤
      law init (timerFailure init σ ∪
        (thresholdFailureAt init n 2 (StageEventSpec.activationHorizon n) (firstLater init) ∪
          doubleDispatchFailure init n hn (firstAllTwo init))) :=
        measure_mono (no_outcome_failure_cover init hinput.2.1 hn σ)
    _ ≤ law init (timerFailure init σ) +
        (law init (thresholdFailureAt init n 2 (StageEventSpec.activationHorizon n)
          (firstLater init)) +
         law init (doubleDispatchFailure init n hn (firstAllTwo init))) :=
      (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ 1 / (n : ℝ≥0∞) ^ 5 +
        (2 / (n : ℝ≥0∞) ^ 5 + 1 / (n : ℝ≥0∞) ^ 4) :=
      add_le_add ht (add_le_add hf hd)
    _ = outcomeBudget n := by
      unfold outcomeBudget
      simp only [div_eq_mul_inv]
      ring

theorem exists_firstCrossing_between {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s u : ℕ)
    (hstart : ∀ a ∈ trace init ω s, a.phase.val = 1)
    (hseed : ∃ a ∈ trace init ω u, 3 ≤ a.phase.val) :
    ∃ t : ℕ, StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
        (trace init ω) t ∧ s ≤ t ∧ t ≤ u := by
  classical
  have hex : ∃ t : ℕ, StageEventSpec.someGE (n := n) 3 (trace init ω t) :=
    ⟨u, hseed⟩
  let t := Nat.find hex
  have hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) t :=
    ⟨Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hst : s ≤ t := by
    by_contra h
    have hupper := phase_upper_reachable 1 _ _
      (trace_reachable init ω (by omega : t ≤ s))
      (fun a ha => (hstart a ha).le)
    obtain ⟨a, ha, hp⟩ := hfirst.1
    have hu := hupper a ha
    omega
  exact ⟨t, hfirst, hst, Nat.find_min' hex hseed⟩

def ProfiledOutcomeBy {n : ℕ} (init : InputCfg n) (ω : InputLog n)
    (s N : ℕ) : Prop :=
  (∃ u, s ≤ u ∧ u ≤ s + N ∧ trace init ω u ∈
    StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init) ∨
  ∃ t, s ≤ t ∧ t ≤ s + N ∧
    StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3) (trace init ω) t ∧
    (StrongGapBackup.BackupSeed n (trace init ω t) ∨
      StageEventSpec.SeedProfile n init (trace init ω t))

theorem observed_outcome_gives_profiled {n : ℕ}
    (init : InputCfg n) (hvalid : validInitial init) (ω : InputLog n)
    (s N u : ℕ) (hsu : s ≤ u) (hu : u ≤ s + N)
    (hcard : (trace init ω s).card = n)
    (hstart : ∀ a ∈ trace init ω s, a.phase.val = 1)
    (hroles : RoleSplitConcentration.RoleSplitGood (1 / 25 : ℝ) n (trace init ω s))
    (hout : ObservedOutcome init (trace init ω u)) :
    ProfiledOutcomeBy init ω s N := by
  classical
  rcases hout with hdone | hseed
  · exact Or.inl ⟨u, hsu, hu, hdone⟩
  · obtain ⟨t, hfirst, hst, htu⟩ :=
      exists_firstCrossing_between init ω s u hstart hseed
    refine Or.inr ⟨t, hst, htu.trans hu, hfirst, ?_⟩
    by_cases hbackup : ∃ a ∈ trace init ω t, a.phase.val = 10
    · exact Or.inl ⟨(Protocol.reachable_card_eq
        (trace_reachable init ω hst)).trans hcard, hbackup⟩
    · right
      exact (seed_profile_and_counts_from_phase_one init ω s t hvalid hcard
        hstart hroles hst hfirst (fun a ha hp => hbackup ⟨a, ha, hp⟩)).1

/-- The complete first crossing payload, with backup distinguished from a
genuine fresh Phase-3 seed. This includes the drained endpoint as a special case. -/
theorem profiled_outcome_tail_at_past_time {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      TimerEntry n (trace init ω s) ∧
      RoleSplitConcentration.RoleSplitGood (1 / 25 : ℝ) n (trace init ω s) ∧
      ¬ ProfiledOutcomeBy init ω s (outcomeHorizon init hn)} ≤ outcomeBudget n := by
  refine (measure_mono ?_).trans (phase_one_outcome_tail init hinput hn σ hσ)
  rintro ω ⟨s, hs, he, hr, hbad⟩
  refine ⟨s, hs, he, ?_⟩
  intro k hk hout
  exact hbad (observed_outcome_gives_profiled init hinput.2.1 ω s
    (outcomeHorizon init hn) (s + k) (by omega) (by omega)
    he.1.1 he.1.2 hr hout)

theorem drained_outcome_tail_at_past_time {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      PhaseOneReadyProfile init (trace init ω s) ∧
      ¬ ProfiledOutcomeBy init ω s (outcomeHorizon init hn)} ≤ outcomeBudget n := by
  refine (measure_mono ?_).trans
    (profiled_outcome_tail_at_past_time init hinput hn σ hσ)
  rintro ω ⟨s, hs, hp, hbad⟩
  exact ⟨s, hs, readyProfile_timerEntry (by omega) hp, hp.role_good, hbad⟩

theorem entry_profile_outcome_tail_at_past_time {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) (hn : 2 ≤ n)
    (σ : InputLog n → WithTop ℕ) (hσ : PairLogPastTime σ) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      PhaseZeroEntry.PhaseOneEntryProfile init ω s ∧
      ¬ ProfiledOutcomeBy init ω s (outcomeHorizon init hn)} ≤ outcomeBudget n := by
  refine (measure_mono ?_).trans
    (profiled_outcome_tail_at_past_time init hinput hn σ hσ)
  rintro ω ⟨s, hs, hp, hbad⟩
  exact ⟨s, hs, entryProfile_timerEntry init hinput ω s hp, hp.role_good, hbad⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoEntryProducer

end
