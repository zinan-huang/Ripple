import Ripple.PopulationProtocol.ExactMajority.Probability.StrongGapBackupTail
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStopping

/-!
# Backup recovery on the actual strong-gap branch

The Main count is the observed final-role count. The strict gap test is kept
inside the joint event under the original law. It is not a conditioning event
about a successful future run.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.StrongGapBackup

open TimeTheorem PairLog PhaseOneDrain PhaseOneDrainStopping

theorem gap_floor_of_entry_profile {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (hp : PhaseZeroEntry.PhaseOneEntryProfile init ω s)
    (hstrong : RoleSplitConcentration.mainCount (trace init ω s) <
      40 * gapMagnitude init) : n ≤ 120 * gapMagnitude init := by
  have hM : 99 * n ≤ 200 * RoleSplitConcentration.mainCount (trace init ω s) := by
    have hreal : (99 : ℝ) * (n : ℝ) ≤
        200 * (RoleSplitConcentration.mainCount (trace init ω s) : ℝ) := by
      linarith only [hp.main_lower]
    exact_mod_cast hreal
  exact useful_gap_of_main_floor hM hstrong

theorem gap_floor_of_ready_profile {n : ℕ}
    (init c : InputCfg n) (hp : PhaseOneReadyProfile init c)
    (hstrong : RoleSplitConcentration.mainCount c < 40 * gapMagnitude init) :
    n ≤ 120 * gapMagnitude init := by
  have hM : 99 * n ≤ 200 * RoleSplitConcentration.mainCount c := by
    have hreal : (99 : ℝ) * (n : ℝ) ≤
        200 * (RoleSplitConcentration.mainCount c : ℝ) := by
      linarith only [hp.main_lower]
    exact_mod_cast hreal
  exact useful_gap_of_main_floor hM hstrong

def firstBackup {n : ℕ} (init : InputCfg n) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (StageEventSpec.someGE (n := n) 10)

theorem firstBackup_past {n : ℕ} (init : InputCfg n) :
    PairLogPastTime (firstBackup init) :=
  exitTime_pairLogPastTime init (StageEventSpec.someGE (n := n) 10)

theorem firstBackup_eq_iff {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s : ℕ) :
    firstBackup init ω = (s : WithTop ℕ) ↔
      StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 10)
        (trace init ω) s :=
  exitTime_eq_iff_firstHit init (StageEventSpec.someGE (n := n) 10) ω s

theorem backup_seed_at_firstBackup {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s : ℕ) (hs : firstBackup init ω = (s : WithTop ℕ)) :
    BackupSeed n (trace init ω s) := by
  have hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init ω s) := by
    simpa only [TraceDrain.trace_zero] using
      (trace_reachable init ω (s := 0) (t := s) (Nat.zero_le s))
  refine ⟨(Protocol.reachable_card_eq hreach).trans hinput.2.2, ?_⟩
  obtain ⟨a, ha, hphase⟩ := ((firstBackup_eq_iff init ω s).1 hs).1
  exact ⟨a, ha, by have := a.phase.isLt; omega⟩

theorem exists_firstBackup_before {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (u : ℕ)
    (hhit : ∃ a ∈ trace init ω u, a.phase.val = 10) :
    ∃ s : ℕ, firstBackup init ω = (s : WithTop ℕ) ∧ s ≤ u := by
  classical
  have hsome : StageEventSpec.someGE (n := n) 10 (trace init ω u) := by
    obtain ⟨a, ha, hp⟩ := hhit
    exact ⟨a, ha, hp.ge⟩
  have hex : ∃ s : ℕ, StageEventSpec.someGE (n := n) 10 (trace init ω s) :=
    ⟨u, hsome⟩
  let s := Nat.find hex
  have hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 10)
      (trace init ω) s :=
    ⟨Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  exact ⟨s, (firstBackup_eq_iff init ω s).2 hfirst, Nat.find_min' hex hsome⟩

/-- The paper's actual random-M strong-gap test. The earlier entry profile
and strict test remain in the joint event, never in a future conditioning law. -/
theorem strong_gap_backup_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (τ : InputLog n → WithTop ℕ) (hτ : PairLogPastTime τ) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        BackupSeed n (trace init ω s) ∧
        (∃ u ≤ s, PhaseZeroEntry.PhaseOneEntryProfile init ω u ∧
          RoleSplitConcentration.mainCount (trace init ω u) < 40 * gapMagnitude init) ∧
        ∀ k ≤ backupHorizon n,
          trace init ω (s + k) ∉
            StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init} ≤
      ENNReal.ofReal (5 / (n : ℝ) ^ 3) := by
  classical
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  by_cases hstrong : n ≤ 120 * gapMagnitude init
  · refine (measure_mono ?_).trans
      (backup_no_stable_hit_tail init hinput.2.1 (by omega) hstrong τ hτ)
    rintro ω ⟨s, hs, hseed, -, hbad⟩
    exact ⟨s, hs, hseed, hbad⟩
  · have hempty :
        {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
          BackupSeed n (trace init ω s) ∧
          (∃ u ≤ s, PhaseZeroEntry.PhaseOneEntryProfile init ω u ∧
            RoleSplitConcentration.mainCount (trace init ω u) < 40 * gapMagnitude init) ∧
          ∀ k ≤ backupHorizon n,
            trace init ω (s + k) ∉
              StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨s, hs, hseed, ⟨u, hu, hp, hgap⟩, hbad⟩
      exact hstrong (gap_floor_of_entry_profile init ω u hp hgap)
    rw [hempty, measure_empty]
    exact zero_le

end Ripple.PopulationProtocol.ExactMajority.StrongGapBackup

end
