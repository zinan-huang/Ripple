/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase1Refactored

/-!
# Diagnostics for the proposed corrected phase-1 interface

This file records mechanically checked consequences of the proposed local
interface while its remaining arithmetic is investigated.
-/

namespace Tri

open scoped ENNReal

set_option exponentiation.threshold 500

/-- A zero-step chain cannot cross a strict deterministic threshold with an
error strictly below one. -/
theorem not_reaches_zero_of_strict_threshold
    {K : ℕ → PMF ℕ} {a b : ℕ} {ε : ℝ≥0∞}
    (hab : a < b) (hε : ε < 1) :
    ¬ Reaches K 0 (fun z => a ≤ z) (fun z => b ≤ z) ε := by
  intro h
  have hsum :
      (∑' z, if b ≤ z then 0 else iter K 0 a z) = (1 : ℝ≥0∞) := by
    rw [tsum_eq_single a]
    · simp [iter, Nat.not_le.mpr hab]
    · intro z hza
      simp [iter, PMF.pure_apply, hza]
  have hone : (1 : ℝ≥0∞) ≤ ε := by
    rw [← hsum]
    exact h a le_rfl
  exact (not_le_of_gt hε) hone

/-- At the headline lower threshold, every advertised dyadic rung envelope is
already strictly below one. -/
theorem phase1RungEnvelopeR_lt_one_of_large
    {n γ j : ℕ} (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ) :
    phase1RungEnvelopeR n γ j < 1 := by
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hlog : 420 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hn
  have hrad : 420 * n ≤ phase1SeedRadicand n γ := by
    unfold phase1SeedRadicand
    calc
      420 * n = 1 * n * 420 := by ring
      _ ≤ γ * n * Nat.log 2 n :=
        Nat.mul_le_mul (Nat.mul_le_mul hγ le_rfl) hlog
  have hseedGap : phase1SeedR n γ ≤ phase1GapR n γ j := by
    unfold phase1GapR
    calc
      phase1SeedR n γ = 1 * phase1SeedR n γ := by simp
      _ ≤ 2 ^ j * phase1SeedR n γ :=
        Nat.mul_le_mul_right _ (one_le_pow₀ (by norm_num))
  have hgapNat : 420 * n ≤ phase1GapR n γ j ^ 2 := by
    exact hrad.trans ((phase1SeedRadicand_le_sq n γ).trans
      (Nat.pow_le_pow_left hseedGap 2))
  have hgapReal : (420 : ℝ) * (n : ℝ) ≤
      (phase1GapR n γ j : ℝ) ^ 2 := by
    exact_mod_cast hgapNat
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hscale : (420 : ℝ) / 48 ≤
      (phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ)) := by
    calc
      (420 : ℝ) / 48 = (420 * (n : ℝ)) / (48 * (n : ℝ)) := by
        field_simp
      _ ≤ (phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ)) :=
        (div_le_div_iff_of_pos_right (by positivity)).2 hgapReal
  have hlogScale : Real.log 2 <
      (phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ)) :=
    (Real.log_two_lt_d9.trans_le (by norm_num)).trans_le hscale
  rw [phase1RungEnvelopeR_eq_gap, ENNReal.ofReal_lt_one]
  calc
    2 * Real.exp
          (-((phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ)))) =
        Real.exp (Real.log 2) * Real.exp
          (-((phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ)))) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (Real.log 2 -
          (phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ))) := by
      rw [← Real.exp_add]
      simp only [sub_eq_add_neg]
    _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- Consequently, the proposed local declaration is false at `C₁ = 0` on
every genuinely moving rung. -/
theorem phase1_uncapped_rung_bound_zero_false
    (n γ j : ℕ) (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ)
    (hj : phase1CheckpointR n γ j < phase1CheckpointR n γ (j + 1)) :
    ¬ Reaches (triChain n) (phase1HorizonR 0 n γ j)
      (Phase1RefactoredCheckpoint n γ j)
      (Phase1RefactoredCheckpoint n γ (j + 1))
      (phase1RungEnvelopeR n γ j) := by
  simpa only [phase1HorizonR, zero_mul, Phase1RefactoredCheckpoint] using
    not_reaches_zero_of_strict_threshold hj
      (phase1RungEnvelopeR_lt_one_of_large hn hγ)

/-- The headline hypotheses do contain a genuinely moving rung: checkpoint
zero is strictly below checkpoint one. -/
theorem phase1CheckpointR_zero_lt_one_of_size
    {n γ : ℕ} (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    phase1CheckpointR n γ 0 < phase1CheckpointR n γ 1 := by
  have hlog : 420 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hn
  have hnlarge : 12 ≤ n := by
    exact (le_trans (by norm_num : 12 ≤ 2 ^ 4)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 4 ≤ 420))).trans hn
  have hseedTwo : 2 ≤ phase1SeedR n γ :=
    phase1SeedR_ge_two (hlog.trans' (by norm_num)) hγ
  have hradMul : 6 * phase1SeedRadicand n γ ≤ n * n := by
    unfold phase1SeedRadicand
    calc
      6 * (γ * n * Nat.log 2 n) =
          (6 * γ * Nat.log 2 n) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hsize
  have hradHalf : phase1SeedRadicand n γ ≤ (n / 2) ^ 2 := by
    have hmod := Nat.mod_lt n (by norm_num : 0 < 2)
    have hdecomp := Nat.mod_add_div n 2
    have hhalfTwo : 2 ≤ n / 2 := by omega
    have hnUpper : n ≤ 2 * (n / 2) + 1 := by omega
    have hnSq : n * n ≤ (2 * (n / 2) + 1) * (2 * (n / 2) + 1) :=
      Nat.mul_le_mul hnUpper hnUpper
    have hfour : 4 * (n / 2) ≤ 2 * (n / 2) ^ 2 := by
      calc
        4 * (n / 2) = 2 * (n / 2) * 2 := by ring
        _ ≤ 2 * (n / 2) * (n / 2) :=
          Nat.mul_le_mul_left _ hhalfTwo
        _ = 2 * (n / 2) ^ 2 := by ring
    nlinarith
  have hseedHalf : phase1SeedR n γ ≤ n / 2 :=
    phase1SeedR_le_of_sq hradHalf
  have hrawTarget : (n + phase1SeedR n γ + 1) / 2 < phase1Target n := by
    unfold phase1Target
    omega
  have hrawStep : (n + phase1SeedR n γ + 1) / 2 <
      (n + 2 * phase1SeedR n γ + 1) / 2 := by
    omega
  unfold phase1CheckpointR phase1GapR
  norm_num only [pow_zero, pow_one, one_mul]
  rw [min_eq_right hrawTarget.le]
  exact lt_min hrawTarget hrawStep

/-- All hypotheses from the proposed declaration are consistent with a moving
rung whose `C₁ = 0` conclusion is false. -/
theorem phase1_uncapped_rung_bound_zero_counterexample
    (n γ : ℕ) (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    ¬ Reaches (triChain n) (phase1HorizonR 0 n γ 0)
      (Phase1RefactoredCheckpoint n γ 0)
      (Phase1RefactoredCheckpoint n γ 1)
      (phase1RungEnvelopeR n γ 0) := by
  exact phase1_uncapped_rung_bound_zero_false n γ 0 hn hγ
    (phase1CheckpointR_zero_lt_one_of_size hn hγ hsize)

/-- A closed instance showing that the hypotheses used by the zero-horizon
counterexample are inhabited. -/
theorem phase1_uncapped_rung_bound_zero_explicit :
    ¬ Reaches (triChain (2 ^ 420))
      (phase1HorizonR 0 (2 ^ 420) 1 0)
      (Phase1RefactoredCheckpoint (2 ^ 420) 1 0)
      (Phase1RefactoredCheckpoint (2 ^ 420) 1 1)
      (phase1RungEnvelopeR (2 ^ 420) 1 0) := by
  apply phase1_uncapped_rung_bound_zero_counterexample
  · exact le_rfl
  · norm_num
  · rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ)) 420]
    norm_num

/-- If the next checkpoint is the capped target and the nominal buffer is
positive, the return exponent does not fit below `phase1UpperR`. -/
theorem phase1_return_gap_fails_at_capped_next
    {n γ j : ℕ} (htarget : 0 < phase1Target n)
    (hnext : phase1CheckpointR n γ (j + 1) = phase1Target n)
    (hbuffer : 0 < phase1UpperBuffer n γ j) :
    ¬ phase1ReturnLoR n γ j + phase1ReturnK n γ j ≤
      phase1UpperR n γ j := by
  rw [phase1UpperR, hnext, min_eq_right (Nat.le_add_right _ _)]
  unfold phase1ReturnLoR phase1ReturnK
  rw [hnext]
  omega

end Tri

#print axioms Tri.not_reaches_zero_of_strict_threshold
#print axioms Tri.phase1RungEnvelopeR_lt_one_of_large
#print axioms Tri.phase1_uncapped_rung_bound_zero_false
#print axioms Tri.phase1CheckpointR_zero_lt_one_of_size
#print axioms Tri.phase1_uncapped_rung_bound_zero_counterexample
#print axioms Tri.phase1_uncapped_rung_bound_zero_explicit
#print axioms Tri.phase1_return_gap_fails_at_capped_next
