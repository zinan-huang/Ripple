/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The global threshold package for the headline

`theorem1bN₀_package` bundles, from the single hypothesis `2 ^ 420 ≤ n`, every
logarithmic and budget threshold the reconciled assembly consumes:

* the phase log-floor bounds `46, 116, 8 ≤ lg n`;
* the three `reconciled_budget` clearing thresholds
  `12, 18, 6 ≤ n ^ (aᵢ γ)`.

The tight one is the phase-2 budget `18 ≤ n ^ (γ/100)`; the others follow by
exponent monotonicity (`33/1700 > 1/100`, `99/100 > 1/100`).  The load-bearing
numeric fact is `18 ^ 100 ≤ 2 ^ 420`, obtained from `18 ^ 5 < 2 ^ 21`.

The paper guard `6 γ lg n ≤ n` is deliberately NOT here: it cannot hold for all
`γ` at fixed `n`, so `Theorem1b_statement` carries it as a caller hypothesis.
-/

namespace Tri

open scoped ENNReal

/-- `18 ^ 100 ≤ 2 ^ 420`, from `18 ^ 5 < 2 ^ 21` raised to the twentieth power. -/
lemma pow_eighteen_hundred_le : (18 : ℕ) ^ 100 ≤ 2 ^ 420 := by
  have hblock : (18 : ℕ) ^ 5 ≤ 2 ^ 21 := by norm_num
  calc (18 : ℕ) ^ 100 = ((18 : ℕ) ^ 5) ^ 20 := by rw [← pow_mul]
    _ ≤ ((2 : ℕ) ^ 21) ^ 20 := Nat.pow_le_pow_left hblock 20
    _ = 2 ^ 420 := by rw [← pow_mul]

/-- The clearing power `n ^ (γ/100)` clears `18` once `2 ^ 420 ≤ n`. -/
lemma eighteen_le_rpow {n γ : ℕ} (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ) :
    18 ≤ (n : ℝ≥0∞) ^ (((1 : ℝ) / 100) * (γ : ℝ)) := by
  have hn1 : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    have : (1 : ℕ) ≤ n := le_trans (Nat.one_le_pow 420 2 (by norm_num)) hn
    exact_mod_cast this
  -- `n ^ (γ/100) ≥ n ^ (1/100)`.
  have hmono : (n : ℝ≥0∞) ^ ((1 : ℝ) / 100)
      ≤ (n : ℝ≥0∞) ^ (((1 : ℝ) / 100) * (γ : ℝ)) := by
    apply ENNReal.rpow_le_rpow_of_exponent_le hn1
    have : (1 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ
    nlinarith
  -- `18 = (18^100) ^ (1/100) ≤ n ^ (1/100)`.
  have h18eq : ((18 : ℝ≥0∞) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) = 18 := by
    rw [← ENNReal.rpow_natCast (18 : ℝ≥0∞) 100, ← ENNReal.rpow_mul]
    norm_num
  have hnbig : ((18 : ℝ≥0∞) ^ (100 : ℕ)) ≤ (n : ℝ≥0∞) := by
    have : (18 : ℕ) ^ 100 ≤ n := le_trans pow_eighteen_hundred_le hn
    exact_mod_cast this
  have hbase : ((18 : ℝ≥0∞) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100)
      ≤ (n : ℝ≥0∞) ^ ((1 : ℝ) / 100) :=
    ENNReal.rpow_le_rpow hnbig (by norm_num)
  rw [h18eq] at hbase
  exact hbase.trans hmono

/-- **The global threshold package.**  Everything the reconciled assembly needs
about `n`, from `2 ^ 420 ≤ n` and `1 ≤ γ`. -/
theorem theorem1bN₀_package {n γ : ℕ} (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ) :
    3 ≤ n ∧ 46 ≤ Nat.log 2 n ∧ 116 ≤ Nat.log 2 n ∧ 8 ≤ Nat.log 2 n ∧
      12 ≤ (n : ℝ≥0∞) ^ (((33 : ℝ) / 1700) * (γ : ℝ)) ∧
      18 ≤ (n : ℝ≥0∞) ^ (((1 : ℝ) / 100) * (γ : ℝ)) ∧
      6 ≤ (n : ℝ≥0∞) ^ (((99 : ℝ) / 100) * (γ : ℝ)) := by
  have hn1 : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    have : (1 : ℕ) ≤ n := le_trans (Nat.one_le_pow 420 2 (by norm_num)) hn
    exact_mod_cast this
  have hγR : (1 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ
  have h116 : 116 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num)
      (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num : 116 ≤ 420)) hn)
  have h18 := eighteen_le_rpow hn hγ
  refine ⟨le_trans (le_trans (by norm_num : (3:ℕ) ≤ 2 ^ 2)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 2 ≤ 420))) hn,
    ?_, h116, ?_, ?_, h18, ?_⟩
  · omega
  · omega
  · -- 12 ≤ n^((33/1700)γ): (33/1700)γ ≥ (1/100)γ, and n^((1/100)γ) ≥ 18 ≥ 12.
    refine le_trans (by norm_num) (h18.trans ?_)
    apply ENNReal.rpow_le_rpow_of_exponent_le hn1
    nlinarith
  · -- 6 ≤ n^((99/100)γ): similarly ≥ 18 ≥ 6.
    refine le_trans (by norm_num) (h18.trans ?_)
    apply ENNReal.rpow_le_rpow_of_exponent_le hn1
    nlinarith

end Tri

#print axioms Tri.pow_eighteen_hundred_le
#print axioms Tri.eighteen_le_rpow
#print axioms Tri.theorem1bN₀_package
