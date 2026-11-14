-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockLowerPassageRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockLowerPassageFibres
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHighRows
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourTickAssembly

/-!
P7's exact Core predicate and its canonical original-law tail.  The
launch shape is obtained pathwise from P6 at the genuine bulk first hit.
The independent P7 exceptional family was already bounded before this
intersection.  Contact additivity then supplies all
nineteen positive passages needed by LowerTwentyTicks.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageRows

open PhaseThreeClockProducer PhaseThreeClockActivationSeed

open TimeTheorem PairLog StageEventSpec
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockCoreCounts
  PhaseThreeClockSeedTails PhaseThreeClockActivationSeed PhaseThreeClockSharpActivationSeed
  PhaseThreeClockRawLocalRow PhaseThreeClockThinning
  PhaseThreeClockShapeFreeze PhaseThreeClockRareDripCharging
  PhaseThreeClockJointCore PhaseThreeClockJointFields
  PhaseThreeClockContactIntervals PhaseThreeClockHighRows
  PhaseThreeClockLowerPassageProcess PhaseThreeClockLowerPassageFibres
  PhaseThreeClockBeforeTwentyRows PhaseThreeClockHourTickAssembly
  PhaseThreeClockRows PhaseThreeClockProducer
open PhaseThreeModel.Numeric

variable {n : ℕ}

def LowerPositiveTicks (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) : Prop :=
  ∀ i, 1 ≤ i → i < clockTop n →
    (2 / 5 : ℝ) * (RoleSplitConcentration.clockCount (virtualCfg init ω s) : ℝ) ≤
      (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
        (w.bulk i) (w.bulk (i + 1)) : ℝ)

theorem lower_launch_at_bulk (init : InputCfg n) (hn : populationThreshold ≤ n)
    (ω : InputLog n) (C : Finset (Fin init.card)) (s T : ℕ) (w : ClockTimes init)
    (he : AsyncEntry init ω s T) (hp : LevelPassages init ω s w)
    (hjoint : JointFrontFields init ω s w)
    (hmask : C = PhaseThreeClockGatedLaw.clockSet (labelsAt init ω s))
    (ell : ℕ) (hell : 1 ≤ ell) (htop : ell < clockTop n) :
    LowerLaunch init C ell (w.bulk ell) ω := by
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  have hcount : PhaseThreeClockGatedLaw.clockCount (labelsAt init ω s) = C.card := by
    change (PhaseThreeClockGatedLaw.clockSet (labelsAt init ω s)).card = C.card
    rw [← hmask]
  obtain ⟨hm, hlo, hCn⟩ := seed_clock_calibration_inputs init hn ω s C.card hseed hcount
  obtain ⟨hCpos, hx, -⟩ := logarithmic_inputs hm hlo hCn
  have hC := clockMask_card_eq_virtual_seed init C s ω hseed hmask
  have hbulk := core_bulk_first_current init ω C s T w hseed he hmask hp ell hell htop.le
  have hbpos : 1 ≤ bulkThreshold C.card := by
    have hb := Nat.le_ceil ((C.card : ℝ) / 10)
    have hbR : (0 : ℝ) < (bulkThreshold C.card : ℝ) :=
      (div_pos hCpos (by norm_num)).trans_le hb
    have : 0 < bulkThreshold C.card := by exact_mod_cast hbR
    omega
  have hsafe := shapeSafeAt_of_asyncEntry init C s T ω hseed hmask he (w.bulk ell) hbulk.1
  have hX := first_threshold_count_eq init C s ell (bulkThreshold C.card) (w.bulk ell)
    hell hbpos htop.le ω hsafe hbulk
  have hcut : frontCutoff (RoleSplitConcentration.clockCount (virtualCfg init ω s)) ≤
      bulkThreshold (RoleSplitConcentration.clockCount (virtualCfg init ω s)) := by
    rw [← hC]
    exact (cutoff_calibration hCpos hx (le_refl C.card)).2.2.2.1.le
  have hcore :
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω (w.bulk ell)) ell =
        bulkThreshold (RoleSplitConcentration.clockCount (virtualCfg init ω s)) := by
    rw [core_front_eq_current_of_asyncEntry init ω s T (w.bulk ell) ell hseed he hbulk.1,
      hX, hC]
  have hshape := hjoint.front_shape ell (w.bulk ell) hell htop hbulk.1 le_rfl
    (by rw [hcore]; exact hcut) (by rw [hcore])
  rw [core_front_eq_current_of_asyncEntry init ω s T (w.bulk ell) (ell + 1)
      hseed he hbulk.1,
    core_front_eq_current_of_asyncEntry init ω s T (w.bulk ell) ell
      hseed he hbulk.1, hX, ← hC] at hshape
  refine ⟨hX.le, ?_⟩
  have hshapeR :
      (C.card : ℝ) *
        (PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω (w.bulk ell)) (ell + 1) : ℝ) ≤
      (bulkThreshold C.card : ℝ) ^ 2 := by exact_mod_cast hshape
  apply (le_div_iff₀ hCpos).2
  nlinarith only [hshapeR]

theorem lower_positive_of_good (init : InputCfg n) (hn : populationThreshold ≤ n)
    (ω : InputLog n) (s T : ℕ) (w : ClockTimes init)
    (he : AsyncEntry init ω s T) (hp : LevelPassages init ω s w)
    (hjoint : JointFrontFields init ω s w)
    (hgood : ω ∉ allLowerFailure init s) :
    LowerPositiveTicks init ω s w := by
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  let C := PhaseThreeClockGatedLaw.clockSet (labelsAt init ω s)
  have hC := clockMask_card_eq_virtual_seed init C s ω hseed rfl
  intro ell hell htop
  have hbulk := core_bulk_first_current init ω C s T w hseed he rfl hp ell hell htop.le
  have hnext := core_bulk_first_current init ω C s T w hseed he rfl hp (ell + 1)
    (by omega) (by omega)
  have hlaunch := lower_launch_at_bulk init hn ω C s T w he hp hjoint rfl ell hell htop
  have horder := bulk_times_mono init ω s w hp ell (ell + 1) hell (by omega) (by omega)
  rw [core_mask_contacts_eq init ω C s _ _ hseed rfl, ← hC]
  exact lower_contacts_of_family_good init C ell s (w.bulk ell) (w.bulk (ell + 1)) ω
    hell htop horder rfl hbulk hlaunch hnext.2.1
    (shapeSafeAt_of_asyncEntry init C s T ω hseed rfl he (w.bulk (ell + 1)) hnext.1) hgood

theorem lower_twenty_of_good (init : InputCfg n) (hn : populationThreshold ≤ n)
    (ω : InputLog n) (s T : ℕ) (w : ClockTimes init)
    (he : AsyncEntry init ω s T) (hp : LevelPassages init ω s w)
    (hjoint : JointFrontFields init ω s w)
    (hgood : ω ∉ allLowerFailure init s) :
    LowerTwentyTicks init ω s w :=
  lower_twenty_ticks_of_positive init ω s w hp
    (lower_positive_of_good init hn ω s T w he hp hjoint hgood)

/-- The shape/finite-passage guards are intersected only in this event
inclusion, after the actual-law P7 family estimate. -/
theorem seed_lower_positive_after_joint_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ {ω | ∃ T, ∃ w : ClockTimes init,
      AsyncEntry init ω s T ∧ LevelPassages init ω s w ∧
        JointFrontFields init ω s w ∧ ¬ LowerPositiveTicks init ω s w}) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) * law init E := by
  apply (measure_mono ?_).trans (all_lower_prefix_tail init hn s E hE hseed)
  rintro ω ⟨hEω, T, w, he, hp, hjoint, hbad⟩
  refine ⟨hEω, ?_⟩
  by_contra hgood
  exact hbad (lower_positive_of_good init hn ω s T w he hp hjoint hgood)

theorem seed_lower_twenty_after_joint_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ {ω | ∃ T, ∃ w : ClockTimes init,
      AsyncEntry init ω s T ∧ LevelPassages init ω s w ∧
        JointFrontFields init ω s w ∧ ¬ LowerTwentyTicks init ω s w}) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) * law init E := by
  apply (measure_mono ?_).trans (all_lower_prefix_tail init hn s E hE hseed)
  rintro ω ⟨hEω, T, w, he, hp, hjoint, hbad⟩
  refine ⟨hEω, ?_⟩
  by_contra hgood
  exact hbad (lower_twenty_of_good init hn ω s T w he hp hjoint hgood)

def LowerAfterJoint (init : InputCfg n) (ω : InputLog n) (s _T : ℕ) : Prop :=
  LevelPassages init ω s (virtualTimes init ω s) →
    JointFrontFields init ω s (virtualTimes init ω s) →
      LowerPositiveTicks init ω s (virtualTimes init ω s)

theorem lower_after_joint_row_tail (init : InputCfg n) (hn : populationThreshold ≤ n) :
    law init (rowFailure init (LowerAfterJoint init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
  apply splice_of_local (law init) (seedTime init 3)
    (rowFailure init (LowerAfterJoint init)) _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, T, hs, -, -, -⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    apply (measure_mono ?_).trans
      ((seed_lower_positive_after_joint_tail init hn s (seedPrefix init s)
        (seedPrefix_measurable init s) (fun _ h => h)).trans
          (mul_le_mul_left' (measure_mono (show seedPrefix init s ⊆
            {ω | seedTime init 3 ω = (s : WithTop ℕ)} from fun _ h => h.1)) _))
    rintro ω ⟨⟨u, T, hu, -, he, hb⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.symm.trans hs)
    subst u
    have hbad : LevelPassages init ω s (virtualTimes init ω s) ∧
        JointFrontFields init ω s (virtualTimes init ω s) ∧
          ¬ LowerPositiveTicks init ω s (virtualTimes init ω s) := by
      simpa only [LowerAfterJoint, _root_.not_imp] using hb
    exact ⟨⟨hs, he.seed_profile⟩, T, virtualTimes init ω s, he,
      hbad.1, hbad.2.1, hbad.2.2⟩


def LowerTwentyAfterJoint (init : InputCfg n) (ω : InputLog n) (s _T : ℕ) : Prop :=
  LevelPassages init ω s (virtualTimes init ω s) →
    JointFrontFields init ω s (virtualTimes init ω s) →
      LowerTwentyTicks init ω s (virtualTimes init ω s)

theorem lower_twenty_after_joint_row_tail (init : InputCfg n) (hn : populationThreshold ≤ n) :
    law init (rowFailure init (LowerTwentyAfterJoint init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
  apply (measure_mono ?_).trans (lower_after_joint_row_tail init hn)
  rintro ω ⟨s, T, hs, hprofile, he, hbad⟩
  refine ⟨s, T, hs, hprofile, he, ?_⟩
  intro hlower
  apply hbad
  intro hp hjoint
  exact lower_twenty_ticks_of_positive init ω s (virtualTimes init ω s) hp
    (hlower hp hjoint)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageRows

end
