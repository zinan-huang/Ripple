-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockTwoMinuteGap.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockContactIntervals
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockJointCore

/-!
P9's two-minute separation for the implemented floor(C/1000) threshold.
The second shape application is used only when the intermediate count is
above the implemented shape cutoff. Below the cutoff, monotonicity in
the level and the calibrated cutoff-small margin finish the argument.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockTwoMinuteGap

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
  PhaseThreeClockCore PhaseThreeClockVirtual PhaseThreeClockSeedTails
  PhaseThreeClockActivationSeed PhaseThreeClockRawLocalRow
  PhaseThreeClockHourGeometry PhaseThreeClockHourOccupancyRow
  PhaseThreeClockJointFields PhaseThreeClockJointCore
  PhaseThreeClockContactIntervals PhaseThreeClockSharpActivationSeed

variable {n : ℕ}

theorem small_threshold_real_lower (C : ℕ) :
    (C : ℝ) < 1000 * ((smallThreshold C : ℝ) + 1) := by
  have hm := Nat.mod_lt C (by norm_num : 0 < 1000)
  have he := Nat.mod_add_div C 1000
  have hn : C < 1000 * (C / 1000 + 1) := by omega
  change (C : ℝ) < 1000 * (((C / 1000 : ℕ) : ℝ) + 1)
  exact_mod_cast hn

theorem shape_cutoff_lt_small (C : ℕ)
    (hC : 0 < (C : ℝ)) (hx : 536870912 ≤ Real.log (C : ℝ)) :
    shapeCutoff C < smallThreshold C := by
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hC] at hsize
  have hCbig : (4001 : ℝ) ≤ C := by linarith
  have hceil : (shapeCutoff C : ℝ) <
      (C : ℝ) ^ (17 / 25 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hC.le _)
  have hfour : (4000 : ℝ) ≤ (C : ℝ) ^ (8 / 25 : ℝ) := by
    have hr := rpow_linear_lower hC (8 / 25 : ℝ)
    linarith
  have hpower := rpow_scale hC (17 / 25 : ℝ) (8 / 25 : ℝ) hfour
  norm_num at hpower
  have hw : (shapeCutoff C : ℝ) ≤ (C : ℝ) / 2000 := by linarith
  have hsmall := small_threshold_real_lower C
  have hr : (shapeCutoff C : ℝ) < (smallThreshold C : ℝ) := by linarith
  exact_mod_cast hr

theorem bulk_square_tiny (C Y : ℕ) (hC : 10000 ≤ C)
    (hshape : C * Y ≤ bulkThreshold C ^ 2) :
    (Y : ℝ) ≤ (11 / 1000 : ℝ) * C ∧ Y < bulkThreshold C := by
  have hCR : (10000 : ℝ) ≤ C := by exact_mod_cast hC
  have hCp : (0 : ℝ) < C := by linarith
  have hceil : (bulkThreshold C : ℝ) < (C : ℝ) / 10 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hupper : (bulkThreshold C : ℝ) ≤ (101 / 1000 : ℝ) * C := by linarith
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg (bulkThreshold C) : (0 : ℝ) ≤ _)
    hupper 2
  have hshapeR : (C : ℝ) * Y ≤ (bulkThreshold C : ℝ) ^ 2 := by
    exact_mod_cast hshape
  have hy : (Y : ℝ) ≤ (11 / 1000 : ℝ) * C := by
    refine le_of_mul_le_mul_left ?_ hCp
    nlinarith only [hsquare, hshapeR, sq_nonneg (C : ℝ)]
  have hbulk : (C : ℝ) / 10 ≤ (bulkThreshold C : ℝ) := Nat.le_ceil _
  refine ⟨hy, ?_⟩
  have hr : (Y : ℝ) < (bulkThreshold C : ℝ) := by linarith
  exact_mod_cast hr

theorem second_square_below_small (C Y Z : ℕ) (hC : 10000 ≤ C)
    (hy : (Y : ℝ) ≤ (11 / 1000 : ℝ) * C) (hshape : C * Z ≤ Y ^ 2) :
    Z < smallThreshold C := by
  have hCR : (10000 : ℝ) ≤ C := by exact_mod_cast hC
  have hCp : (0 : ℝ) < C := by linarith
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg Y : (0 : ℝ) ≤ _) hy 2
  have hshapeR : (C : ℝ) * Z ≤ (Y : ℝ) ^ 2 := by exact_mod_cast hshape
  have hz : (Z : ℝ) ≤ (121 / 1000000 : ℝ) * C := by
    refine le_of_mul_le_mul_left ?_ hCp
    nlinarith only [hsquare, hshapeR]
  have hsmall := small_threshold_real_lower C
  have hr : (Z : ℝ) < (smallThreshold C : ℝ) := by linarith
  exact_mod_cast hr

/-- At bulk(v-2), the v-front is still strictly below the actual small
threshold. This includes the intermediate-below-cutoff branch. -/
theorem front_below_small_two_minutes (init : InputCfg n)
    (hn : populationThreshold ≤ n) (ω : InputLog n) (s T : ℕ)
    (w : ClockTimes init) (hseed : ω ∈ seedPrefix init s)
    (he : AsyncEntry init ω s T) (hp : LevelPassages init ω s w)
    (hj : JointFrontFields init ω s w) (ell : ℕ)
    (hell : 3 ≤ ell) (hcap : ell ≤ clockTop n) :
    frontCountL init (virtualLabels init ω s)
      (virtualLabels init ω (w.bulk (ell - 2))) ell <
        smallThreshold (clockCount (virtualCfg init ω s)) := by
  let C := clockCount (virtualCfg init ω s)
  let a := ell - 2
  let u := w.bulk a
  let X : ℕ → ℕ → ℕ := fun t k =>
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω t) k
  have hcount : PhaseThreeClockGatedLaw.clockCount (labelsAt init ω s) = C :=
    clockMask_card_eq_virtual_seed init
      (PhaseThreeClockGatedLaw.clockSet (labelsAt init ω s)) s ω hseed rfl
  obtain ⟨hm, hlo, hCm⟩ := seed_clock_calibration_inputs init hn ω s C hseed hcount
  obtain ⟨hCp, hx, -⟩ := logarithmic_inputs hm hlo hCm
  have hsize := Real.add_one_le_exp (Real.log (C : ℝ))
  rw [Real.exp_log hCp] at hsize
  have hCbig : 10000 ≤ C := by
    have hr : (10000 : ℝ) ≤ C := by linarith
    exact_mod_cast hr
  have ha : 1 ≤ a := by dsimp only [a]; omega
  have haQ : a + 2 ≤ clockTop n := by dsimp only [a]; omega
  have hella : a + 2 = ell := by dsimp only [a]; omega
  have hb := hp.2 a ha (by omega)
  have hstart := core_positive_front_zero_at_seed init ω s T a hseed he ha
  have hxa : X u a = bulkThreshold C := by
    apply firstAfter_count_eq hb
    · change frontCountL init (virtualLabels init ω s) (virtualLabels init ω s) a ≤ _
      rw [hstart]
      exact Nat.zero_le _
    · intro v hsv
      exact (core_front_step_bounds_of_asyncEntry init ω s T a v hseed he
        ha (by omega) hsv).2
  have hcut : shapeCutoff C ≤ bulkThreshold C :=
    (cutoff_calibration hCp hx (le_refl C)).2.2.2.1.le
  have hshapea : C * X u (a + 1) ≤ bulkThreshold C ^ 2 := by
    have hs := hj.front_shape a u ha (by omega) hb.1 le_rfl
      (by change shapeCutoff C ≤ X u a; rw [hxa]; exact hcut)
      (by change X u a ≤ bulkThreshold C; rw [hxa])
    change C * X u (a + 1) ≤ X u a ^ 2 at hs
    simpa only [hxa] using hs
  obtain ⟨hytiny, hybelow⟩ := bulk_square_tiny C (X u (a + 1)) hCbig hshapea
  have hbnext := hp.2 (a + 1) (by omega) (by omega)
  have hub : u ≤ w.bulk (a + 1) := by
    by_contra hnot
    have hmono := core_front_mono_of_asyncEntry init ω s T (a + 1)
      (w.bulk (a + 1)) u hseed he (by omega) (by omega)
      hbnext.1 (by omega)
    have hhit : bulkThreshold C ≤ X u (a + 1) := hbnext.2.1.trans hmono
    exact (not_le_of_gt hybelow) hhit
  have hbelow : X u (a + 2) < smallThreshold C := by
    by_cases hylow : X u (a + 1) < shapeCutoff C
    · have hanti := core_front_antitone_level init (virtualLabels init ω s)
        (virtualLabels init ω u) (a + 1) (a + 2) (by omega)
      exact hanti.trans_lt (hylow.trans (shape_cutoff_lt_small C hCp hx))
    · have hshapenext := hj.front_shape (a + 1) u (by omega) (by omega)
        hb.1 hub (by change shapeCutoff C ≤ X u (a + 1); omega)
        (by change X u (a + 1) ≤ bulkThreshold C; exact hybelow.le)
      have hs : C * X u (a + 2) ≤ X u (a + 1) ^ 2 := by
        simpa only [show a + 1 + 1 = a + 2 by omega] using hshapenext
      exact second_square_below_small C (X u (a + 1)) (X u (a + 2))
        hCbig hytiny hs
  simpa only [hella] using hbelow

/-- Genuine small-threshold first passage is strictly after bulk(v-2). -/
theorem bulk_before_small_finish (init : InputCfg n)
    (hn : populationThreshold ≤ n) (ω : InputLog n) (s T : ℕ)
    (w : ClockTimes init) (hseed : ω ∈ seedPrefix init s)
    (he : AsyncEntry init ω s T) (hp : LevelPassages init ω s w)
    (hj : JointFrontFields init ω s w) (ell e : ℕ)
    (hell : 3 ≤ ell) (hcap : ell ≤ clockTop n)
    (hf : firstAfter (fun t => smallThreshold (clockCount (virtualCfg init ω s)) ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω t) ell) s e) :
    w.bulk (ell - 2) < e := by
  have hbelow := front_below_small_two_minutes init hn ω s T w hseed he hp hj
    ell hell hcap
  by_contra hnot
  have hmono := core_front_mono_of_asyncEntry init ω s T ell e (w.bulk (ell - 2))
    hseed he (by omega) hcap hf.1 (by omega)
  exact (not_le_of_gt hbelow) (hf.2.1.trans hmono)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockTwoMinuteGap

end
