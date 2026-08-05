/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBAssembly

/-!
# Heavy-B headline closure for Theorem 2

This file absorbs the fixed coefficient in the assembled Heavy-B power law and
closes the formal Heavy-B statement of Theorem 2.
-/

namespace Tri

open scoped ENNReal

/-! ## Absorbing the fixed coefficient and closing `Theorem2_heavyB_statement` -/

/-- The chosen global threshold clears the coefficient `95`. -/
theorem heavyHeadlineCoefficient_clear
    {n γ : ℕ} (hn : 2 ^ 80000000 ≤ n) (hγ : 1 ≤ γ) :
    95 * (n : ℝ≥0∞)⁻¹ ^
          ((1 / 4000000 : ℝ) * (γ : ℝ)) ≤
      (n : ℝ≥0∞)⁻¹ ^
          ((1 / 8000000 : ℝ) * (γ : ℝ)) := by
  have hnOne : 1 ≤ n := by
    have hpowNe : 2 ^ 80000000 ≠ 0 :=
      pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)
    have hnNe : n ≠ 0 := by
      intro hz
      have hle0 : 2 ^ 80000000 ≤ 0 := by
        simpa only [hz] using hn
      exact hpowNe (Nat.eq_zero_of_le_zero hle0)
    exact Nat.one_le_iff_ne_zero.mpr hnNe
  have hnOneE : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hnOne
  have hbase :
      ((2 : ℝ≥0∞) ^ (80000000 : ℕ)) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hn
  have hrootEq :
      ((2 : ℝ≥0∞) ^ (80000000 : ℕ)) ^ ((1 : ℝ) / 8000000) =
        1024 := by
    rw [← ENNReal.rpow_natCast (2 : ℝ≥0∞) 80000000,
      ← ENNReal.rpow_mul]
    norm_num
  have hroot :
      (1024 : ℝ≥0∞) ≤
        (n : ℝ≥0∞) ^ ((1 : ℝ) / 8000000) := by
    rw [← hrootEq]
    exact ENNReal.rpow_le_rpow hbase (by norm_num)
  have hmono :
      (n : ℝ≥0∞) ^ ((1 : ℝ) / 8000000) ≤
        (n : ℝ≥0∞) ^
          ((1 / 8000000 : ℝ) * (γ : ℝ)) := by
    apply ENNReal.rpow_le_rpow_of_exponent_le hnOneE
    have hγR : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
    nlinarith
  have hthreshold :
      3 * (95 : ℝ≥0∞) ≤
        (n : ℝ≥0∞) ^
          (((1 / 4000000 : ℝ) * (γ : ℝ)) -
            ((1 / 8000000 : ℝ) * (γ : ℝ))) := by
    have h285 :
        (285 : ℝ≥0∞) ≤
          (n : ℝ≥0∞) ^
            ((1 / 8000000 : ℝ) * (γ : ℝ)) :=
      (by norm_num : (285 : ℝ≥0∞) ≤ 1024) |>.trans
        (hroot.trans hmono)
    have hexp :
        ((1 / 4000000 : ℝ) * (γ : ℝ)) -
            ((1 / 8000000 : ℝ) * (γ : ℝ)) =
          ((1 / 8000000 : ℝ) * (γ : ℝ)) := by
      ring
    have hcoef : (3 : ℝ≥0∞) * 95 = 285 := by norm_num
    simpa only [hexp, hcoef] using h285
  have hthird :=
    inv_rpow_third 95
      ((1 / 4000000 : ℝ) * (γ : ℝ))
      ((1 / 8000000 : ℝ) * (γ : ℝ))
      n (by
        have hγ0 : (0 : ℝ) ≤ γ := by positivity
        nlinarith)
      hnOne hthreshold
  exact hthird.trans (by
    calc
      (1 / 3 : ℝ≥0∞) *
            (n : ℝ≥0∞)⁻¹ ^
              ((1 / 8000000 : ℝ) * (γ : ℝ))
          ≤ 1 *
            (n : ℝ≥0∞)⁻¹ ^
              ((1 / 8000000 : ℝ) * (γ : ℝ)) := by
        gcongr
        norm_num
      _ = _ := one_mul _)

/-- The unconditional Heavy-B clause of Theorem 2. -/
theorem theorem2_heavyB : Theorem2_heavyB_statement := by
  refine ⟨280000, 2 ^ 80000000, (1 / 8000000 : ℝ),
    (by norm_num), (by norm_num), ?_, ?_⟩
  · have hpow : 2 ^ 2 ≤ 2 ^ 80000000 :=
      pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2)
        (by decide : 2 ≤ 80000000)
    exact (by decide : 3 ≤ 2 ^ 2).trans hpow
  · intro n γ hn0 hγ hsize s₀ hinv hpaper
    have hn : 3 ≤ n := by
      have hpow : 2 ^ 2 ≤ 2 ^ 80000000 :=
        pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2)
          (by decide : 2 ≤ 80000000)
      exact ((by decide : 3 ≤ 2 ^ 2).trans hpow).trans hn0
    have hlog1024 : 1024 ≤ Nat.log 2 n := by
      have hlogN0 : 80000000 ≤ Nat.log 2 n :=
        Nat.le_log_of_pow_le (by norm_num) hn0
      exact (by decide : 1024 ≤ 80000000).trans hlogN0
    have hlog128 : 128 ≤ Nat.log 2 n :=
      hlog1024.trans' (by norm_num)
    let s : HeavyState n := ⟨s₀, hinv⟩
    have hr :=
      heavyConsensus_reaches n hn γ hlog1024 hγ hsize
    have hH :=
      heavyConsensusHorizon_le n γ hlog128 hγ
    let targetT := 280000 * γ * n * Nat.log 2 n
    have hpad :=
      hr.pad_of_absorbing
        (heavyStateStep_consensus n hn)
        (targetT - heavyConsensusHorizon n γ)
    have htime :
        heavyConsensusHorizon n γ +
            (targetT - heavyConsensusHorizon n γ) = targetT := by
      exact Nat.add_sub_of_le hH
    rw [htime] at hpad
    have hreach :=
      hpad.mono_error (heavyHeadlineCoefficient_clear hn0 hγ)
    have hs : HeavyBEarlyInitial n γ s := by
      rcases hpaper with ⟨_, gap, hgap, hgapSq⟩
      exact ⟨gap, by simpa only [s] using hgap, hgapSq⟩
    have hmass := hreach s hs
    rw [heavyState_nonconsensus_mass_eq n hn targetT s] at hmass
    simpa only [targetT, s] using hmass

end Tri

#print axioms Tri.heavyHeadlineCoefficient_clear
#print axioms Tri.theorem2_heavyB
