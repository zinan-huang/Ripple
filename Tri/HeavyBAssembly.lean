/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBFinalConsensus
import Tri.HeavyBConstantGap
import Tri.BudgetArith

/-!
# Heavy-B consensus assembly

This composes the Heavy-B early ladder, constant-gap handoff, middle rung,
late dyadic ladder, and direct final consensus block.
-/

namespace Tri

open scoped ENNReal

def heavyConsensusHorizon (n γ : ℕ) : ℕ :=
  heavyEarlyLadderHorizon n γ +
    heavyConstantGapHorizon n +
    (heavyMiddleHorizon n + heavyLateLadderHorizon n γ) +
    heavyFinalHorizon n γ

theorem heavyRealLog_le_natLog
    {n : ℕ} (hlog : 128 ≤ Nat.log 2 n) :
    Real.log (n : ℝ) ≤ (Nat.log 2 n : ℝ) := by
  have hnPos : 0 < n := by
    have hnLarge : 4096 ≤ n :=
      phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hlogn :
      Real.log n ≤
        ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
    have hup : n < 2 ^ (Nat.log 2 n + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) n
    have hlt :
        Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
      Real.log_lt_log (by exact_mod_cast hnPos)
        (by exact_mod_cast hup)
    rw [Real.log_pow] at hlt
    push_cast at hlt
    linarith
  have hL : (128 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hlog
  have hfactor :
      ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤
        (Nat.log 2 n : ℝ) := by
    have hlog2 : Real.log 2 < (0.6931471808 : ℝ) :=
      Real.log_two_lt_d9
    have hlog2Nonneg : 0 ≤ Real.log 2 :=
      (Real.log_pos (by norm_num)).le
    nlinarith
  exact hlogn.trans hfactor

theorem ofReal_exp_neg_le_inv_rpow
    (n : ℕ) (hn : 0 < n) (S a : ℝ)
    (hS : Real.log (n : ℝ) * a ≤ S) :
    ENNReal.ofReal (Real.exp (-S)) ≤
      (n : ℝ≥0∞)⁻¹ ^ a := by
  have hrpow :
      (n : ℝ≥0∞)⁻¹ ^ a =
        ENNReal.ofReal ((n : ℝ) ^ (-a)) := by
    rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
      ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hn),
      ← ENNReal.ofReal_inv_of_pos (by positivity),
      Real.rpow_neg (by positivity)]
  rw [hrpow]
  apply ENNReal.ofReal_le_ofReal
  have hpExp : (0 : ℝ) < Real.exp (-S) := Real.exp_pos _
  have hpPow : (0 : ℝ) < (n : ℝ) ^ (-a) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hlogIneq :
      Real.log (Real.exp (-S)) ≤ Real.log ((n : ℝ) ^ (-a)) := by
    rw [Real.log_exp, Real.log_rpow (by exact_mod_cast hn)]
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogIneq
  rwa [Real.exp_log hpExp, Real.exp_log hpPow] at hexp

/-! ## Early ladder power budget -/

theorem heavyEarlyEnvelopeScale_ge_natLog
    (n γ : ℕ) (hn : 0 < n) :
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 1024 ≤
      heavyEarlyEnvelopeScale n γ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let q := heavyEarlySeedUnit n γ
  let seed := phase1SeedR n γ
  have hqDiv : phase1SeedR n γ / 8 ≤ q := by
    dsimp [q, heavyEarlySeedUnit]
    exact le_max_right _ _
  have hmod := Nat.mod_lt seed (by norm_num : 0 < 8)
  have hdecomp := Nat.mod_add_div seed 8
  have hqDivSeed : seed / 8 ≤ q := by simpa only [seed] using hqDiv
  have hqpos : 1 ≤ q := by
    dsimp only [q, heavyEarlySeedUnit]
    exact le_max_left _ _
  have hdecomp' : seed = seed % 8 + 8 * (seed / 8) := by omega
  have hseedQ : seed ≤ 16 * q := by omega
  have hseedSq : seed ^ 2 ≤ 256 * q ^ 2 := by
    have hp := Nat.pow_le_pow_left hseedQ 2
    nlinarith
  have hrad :
      γ * n * Nat.log 2 n ≤ 256 * q ^ 2 := by
    exact (phase1SeedRadicand_le_sq n γ).trans hseedSq
  have hradR :
      (γ : ℝ) * n * Nat.log 2 n ≤ 256 * (q : ℝ) ^ 2 := by
    exact_mod_cast hrad
  have hscale :
      (γ : ℝ) * Nat.log 2 n / 1024 ≤
        (q : ℝ) ^ 2 / (4 * (n : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)
      (by positivity : (0 : ℝ) < 4 * (n : ℝ))]
    nlinarith
  simpa only [q, heavyEarlyEnvelopeScale] using hscale

theorem heavyEarlyEnvelopeScale_ge_log_two_div_three
    {n γ : ℕ} (hlog : 1024 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Real.log 2 / 3 ≤ heavyEarlyEnvelopeScale n γ := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hmulNat : 1024 ≤ γ * Nat.log 2 n :=
    calc
      1024 = 1 * 1024 := by norm_num
      _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
  have hmulR : (1024 : ℝ) ≤ γ * Nat.log 2 n := by
    exact_mod_cast hmulNat
  have hlogBound : Real.log 2 / 3 ≤ (1 : ℝ) := by
    have hlogTwo : Real.log 2 ≤ (3 : ℝ) / 4 :=
      Real.log_two_lt_d9.le.trans (by norm_num)
    nlinarith
  have hone :
      (1 : ℝ) ≤ (γ : ℝ) * Nat.log 2 n / 1024 := by
    nlinarith
  exact hlogBound.trans
    (hone.trans (heavyEarlyEnvelopeScale_ge_natLog n γ hnNat))

theorem heavyEarlyLadderError_le_geometric
    (n γ : ℕ) (hlog : 1024 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    heavyEarlyLadderError n γ ≤
      ENNReal.ofReal
        (40 * Real.exp (-heavyEarlyEnvelopeScale n γ)) := by
  unfold heavyEarlyLadderError
  calc
    (∑ j ∈ Finset.range (heavyEarlyStages n γ),
        heavyEarlyStageError n (heavyEarlyScale n γ j))
        ≤ ∑ j ∈ Finset.range (heavyEarlyStages n γ),
            ENNReal.ofReal
              (20 * Real.exp
                (-((4 : ℝ) ^ j * heavyEarlyEnvelopeScale n γ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hstage :=
        heavyEarlyStageError_le n (heavyEarlyScale n γ j)
          (heavyEarlyScale_pos n γ j)
          (heavyEarlyScale_small n γ j (Finset.mem_range.mp hj))
      rw [heavyEarlyEnvelope_eq n γ j] at hstage
      simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20)] using hstage
    _ = ENNReal.ofReal
          (∑ j ∈ Finset.range (heavyEarlyStages n γ),
            20 * Real.exp
              (-((4 : ℝ) ^ j * heavyEarlyEnvelopeScale n γ))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j hj
      positivity
    _ ≤ ENNReal.ofReal
          (40 * Real.exp (-heavyEarlyEnvelopeScale n γ)) := by
      apply ENNReal.ofReal_le_ofReal
      have hsum :=
        phase1Envelope_sum_le
          (heavyEarlyEnvelopeScale_ge_log_two_div_three hlog hγ)
          (heavyEarlyStages n γ)
      have heq :
          (∑ j ∈ Finset.range (heavyEarlyStages n γ),
            20 * Real.exp
              (-((4 : ℝ) ^ j * heavyEarlyEnvelopeScale n γ))) =
            10 * (∑ j ∈ Finset.range (heavyEarlyStages n γ),
              2 * Real.exp
                (-((4 : ℝ) ^ j * heavyEarlyEnvelopeScale n γ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      rw [heq]
      nlinarith [Real.exp_pos (-heavyEarlyEnvelopeScale n γ)]

theorem heavyEarlyLadderError_le_power
    (n γ : ℕ) (hlog : 1024 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    heavyEarlyLadderError n γ ≤
      40 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hlog128 : 128 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hlogn := heavyRealLog_le_natLog hlog128
  have hS :
      Real.log (n : ℝ) * ((1 / 4000000 : ℝ) * (γ : ℝ))
        ≤ heavyEarlyEnvelopeScale n γ := by
    calc
      Real.log (n : ℝ) * ((1 / 4000000 : ℝ) * (γ : ℝ))
          = (γ : ℝ) * (Real.log (n : ℝ) / 4000000) := by ring
      _ ≤ (γ : ℝ) * ((Nat.log 2 n : ℝ) / 4000000) := by
        gcongr
      _ ≤ (γ : ℝ) * ((Nat.log 2 n : ℝ) / 1024) := by
        gcongr
        norm_num
      _ = (γ : ℝ) * (Nat.log 2 n : ℝ) / 1024 := by ring
      _ ≤ heavyEarlyEnvelopeScale n γ :=
        heavyEarlyEnvelopeScale_ge_natLog n γ hnNat
  calc
    heavyEarlyLadderError n γ
        ≤ ENNReal.ofReal
          (40 * Real.exp (-heavyEarlyEnvelopeScale n γ)) :=
      heavyEarlyLadderError_le_geometric n γ hlog hγ
    _ ≤ 40 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 40)]
      norm_num only [ENNReal.ofReal_ofNat]
      gcongr
      exact ofReal_exp_neg_le_inv_rpow n hnNat
        (heavyEarlyEnvelopeScale n γ)
        ((1 / 4000000 : ℝ) * (γ : ℝ)) hS

/-! ## Other phase power budgets -/

theorem heavyConstantGapEnvelopeScale_ge_natLog
    (n γ : ℕ) (hsizeNat : 1920 ≤ n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 4000000 ≤
      heavyConstantGapEnvelopeScale n := by
  let q := heavyConstantGapScale n
  have hnNat : 0 < n := by omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hguards := heavyConstantGapScale_guards hsizeNat
  have hq4 : 4 ≤ q := by
    dsimp only [q, heavyConstantGapScale]
    omega
  have hnq : n ≤ 400 * q := by
    dsimp only [q, heavyConstantGapScale]
    have hdiv := Nat.div_add_mod n 320
    have hmod := Nat.mod_lt n (by norm_num : 0 < 320)
    omega
  have hnqSq : n * n ≤ 160000 * (q * q) := by
    have hp := Nat.mul_le_mul hnq hnq
    calc
      n * n ≤ (400 * q) * (400 * q) := hp
      _ = 160000 * (q * q) := by ring
  have hnqSqR : (n : ℝ) ^ 2 ≤ 160000 * (q : ℝ) ^ 2 := by
    have h' : n ^ 2 ≤ 160000 * q ^ 2 := by
      simpa [pow_two] using hnqSq
    exact_mod_cast h'
  have hsizeR :
      6 * (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ n := by
    exact_mod_cast hsize
  change
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 4000000 ≤
      (q : ℝ) ^ 2 / (4 * (n : ℝ))
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4000000)
    (by positivity : (0 : ℝ) < 4 * (n : ℝ))]
  nlinarith [sq_nonneg (n : ℝ)]

theorem heavyConstantGapError_le_power
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    heavyConstantGapError n ≤
      40 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hn1920 : 1920 ≤ n := by
    have := phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hlogn := heavyRealLog_le_natLog hlog
  have hS :
      Real.log (n : ℝ) * ((1 / 4000000 : ℝ) * (γ : ℝ))
        ≤ heavyConstantGapEnvelopeScale n := by
    calc
      Real.log (n : ℝ) * ((1 / 4000000 : ℝ) * (γ : ℝ))
          = (γ : ℝ) * (Real.log (n : ℝ) / 4000000) := by ring
      _ ≤ (γ : ℝ) * ((Nat.log 2 n : ℝ) / 4000000) := by
        gcongr
      _ = (γ : ℝ) * (Nat.log 2 n : ℝ) / 4000000 := by ring
      _ ≤ heavyConstantGapEnvelopeScale n :=
        heavyConstantGapEnvelopeScale_ge_natLog n γ hn1920 hsize
  calc
    heavyConstantGapError n
        ≤ 40 * ENNReal.ofReal
          (Real.exp (-heavyConstantGapEnvelopeScale n)) :=
      heavyConstantGapError_le_gaussian n hn1920
    _ ≤ 40 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
      gcongr
      exact ofReal_exp_neg_le_inv_rpow n hnNat
        (heavyConstantGapEnvelopeScale n)
        ((1 / 4000000 : ℝ) * (γ : ℝ)) hS

theorem heavyInvPower_le_common
    (n γ : ℕ) (hn : 1 ≤ n) (a : ℝ)
    (ha : (1 / 4000000 : ℝ) ≤ a) :
    (n : ℝ≥0∞)⁻¹ ^ (a * (γ : ℝ)) ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
  apply ENNReal.rpow_le_rpow_of_exponent_ge
  · rw [ENNReal.inv_le_one]
    exact_mod_cast hn
  · have hγ0 : (0 : ℝ) ≤ γ := by positivity
    nlinarith

theorem heavyMiddleError_le_power
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    heavyMiddleError n ≤
      4 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by omega
  have hlogn := heavyRealLog_le_natLog hlog
  have hS :
      Real.log (n : ℝ) * ((1 / 4000000 : ℝ) * (γ : ℝ))
        ≤ (n : ℝ) / 2000 := by
    have hsizeR :
        6 * (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ n := by
      exact_mod_cast hsize
    calc
      Real.log (n : ℝ) * ((1 / 4000000 : ℝ) * (γ : ℝ))
          = (γ : ℝ) * Real.log (n : ℝ) / 4000000 := by ring
      _ ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) / 4000000 := by
        gcongr
      _ ≤ (n : ℝ) / 2000 := by nlinarith
  calc
    heavyMiddleError n
        ≤ 4 * ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000)) :=
      heavyMiddleError_le n hn (hlog.trans' (by norm_num))
    _ ≤ 4 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
      gcongr
      simpa only [show (-((n : ℝ) / 2000)) = -(n : ℝ) / 2000 by ring]
        using ofReal_exp_neg_le_inv_rpow n hnNat ((n : ℝ) / 2000)
          ((1 / 4000000 : ℝ) * (γ : ℝ)) hS

theorem heavyLateLadderError_le_power
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    heavyLateLadderError n γ ≤
      8 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by omega
  have hlogn := heavyRealLog_le_natLog hlog
  have hS :
      Real.log (n : ℝ) * ((1 / 4000000 : ℝ) * (γ : ℝ))
        ≤ ((γ * Nat.log 2 n : ℕ) : ℝ) / 160 := by
    calc
      Real.log (n : ℝ) * ((1 / 4000000 : ℝ) * (γ : ℝ))
          = (γ : ℝ) * Real.log (n : ℝ) / 4000000 := by ring
      _ ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) / 4000000 := by
        gcongr
      _ ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) / 160 := by
        gcongr
        norm_num
      _ = ((γ * Nat.log 2 n : ℕ) : ℝ) / 160 := by
        norm_num only [Nat.cast_mul]
  calc
    heavyLateLadderError n γ
        ≤ 8 * ENNReal.ofReal
          (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 160))) :=
      heavyLateLadderError_le_exp n hn γ hlog hγ hsize
    _ ≤ 8 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
      gcongr
      exact ofReal_exp_neg_le_inv_rpow n hnNat
        (((γ * Nat.log 2 n : ℕ) : ℝ) / 160)
        ((1 / 4000000 : ℝ) * (γ : ℝ)) hS

theorem heavyConsensusError_le
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 1024 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    heavyEarlyLadderError n γ +
        heavyConstantGapError n +
        (heavyMiddleError n + heavyLateLadderError n γ) +
        3 * (n : ℝ≥0∞)⁻¹ ^
          ((1 / 200 : ℝ) * (γ : ℝ)) ≤
      95 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ)) := by
  let X :=
    (n : ℝ≥0∞)⁻¹ ^ ((1 / 4000000 : ℝ) * (γ : ℝ))
  have hnOne : 1 ≤ n := by omega
  have hlog128 : 128 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have h200 :
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) ≤ X := by
    dsimp only [X]
    exact heavyInvPower_le_common n γ hnOne (1 / 200) (by norm_num)
  have he :
      heavyEarlyLadderError n γ ≤ 40 * X :=
    heavyEarlyLadderError_le_power n γ hlog hγ
  have hc :
      heavyConstantGapError n ≤ 40 * X :=
    heavyConstantGapError_le_power n γ hlog128 hsize
  have hm :
      heavyMiddleError n ≤ 4 * X :=
    heavyMiddleError_le_power n hn γ hlog128 hsize
  have hl :
      heavyLateLadderError n γ ≤ 8 * X :=
    heavyLateLadderError_le_power n hn γ hlog128 hγ hsize
  change
    heavyEarlyLadderError n γ +
        heavyConstantGapError n +
        (heavyMiddleError n + heavyLateLadderError n γ) +
        3 * (n : ℝ≥0∞)⁻¹ ^
          ((1 / 200 : ℝ) * (γ : ℝ)) ≤ 95 * X
  calc
    _ ≤ 40 * X + 40 * X + (4 * X + 8 * X) + 3 * X := by
      gcongr
    _ = 95 * X := by ring

/-! ## Reachability and horizon assembly -/

theorem heavyConsensus_reaches
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 1024 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (heavyStateStep n) (heavyConsensusHorizon n γ)
      (HeavyBEarlyInitial n γ)
      HeavyXConsensus
      (95 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 4000000 : ℝ) * (γ : ℝ))) := by
  have hlog128 : 128 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hlog12 : 12 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hn1920 : 1920 ≤ n := by
    have := phase1_log_twelve_implies_size hlog12
    omega
  have he := heavyEarly_reaches n hn γ hlog12 hγ
  have hc := heavyConstantGap_reaches n hn hn1920
  have hm := heavyMiddle_reaches_symbolic n hn hlog12
  have hl := heavyLate_ladder_symbolic n hn γ hlog128 hγ
  have hf := heavyFinalConsensus_reaches_power n hn γ hlog128 hγ hsize
  have h := ((he.comp hc).comp (hm.comp hl)).comp hf
  exact (by
    have herr := heavyConsensusError_le n hn γ hlog hγ hsize
    simpa only [heavyConsensusHorizon, add_assoc] using h.mono_error herr)

theorem heavyEarlyStageHorizon_le (n q : ℕ) :
    heavyEarlyStageHorizon n q ≤ 3328 * n := by
  unfold heavyEarlyStageHorizon
  calc
    (∑ t ∈ Finset.range 4, heavyEarlySubrungHorizon n q t)
        ≤ ∑ _t ∈ Finset.range 4, 64 * (13 * n) := by
      apply Finset.sum_le_sum
      intro t ht
      unfold heavyEarlySubrungHorizon heavyEarlyKClock
        heavyEarlyStartCo heavyEarlyResolutions
      have hco : n - heavyEarlyStartLevel n q t ≤ n := Nat.sub_le _ _
      omega
    _ = 3328 * n := by
      simp
      ring

theorem heavyEarlyLadderHorizon_le
    (n γ : ℕ) :
    heavyEarlyLadderHorizon n γ ≤
      3328 * n * Nat.log 2 n := by
  have hk := heavyEarlyStages_le_log n γ
  unfold heavyEarlyLadderHorizon
  calc
    (∑ j ∈ Finset.range (heavyEarlyStages n γ),
        heavyEarlyStageHorizon n (heavyEarlyScale n γ j))
        ≤ ∑ _j ∈ Finset.range (heavyEarlyStages n γ), 3328 * n := by
      apply Finset.sum_le_sum
      intro j hj
      exact heavyEarlyStageHorizon_le n (heavyEarlyScale n γ j)
    _ = heavyEarlyStages n γ * (3328 * n) := by
      simp [Finset.sum_const, Finset.card_range]
    _ ≤ Nat.log 2 n * (3328 * n) := Nat.mul_le_mul_right _ hk
    _ = 3328 * n * Nat.log 2 n := by ring

theorem heavyConstantGapHorizon_le
    (n : ℕ) (hlog : 128 ≤ Nat.log 2 n) :
    heavyConstantGapHorizon n ≤
      6656 * n * Nat.log 2 n := by
  unfold heavyConstantGapHorizon
  calc
    heavyEarlyStageHorizon n (heavyConstantGapScale n) +
        heavyEarlyStageHorizon n (2 * heavyConstantGapScale n)
        ≤ 3328 * n + 3328 * n := by
      gcongr <;> apply heavyEarlyStageHorizon_le
    _ = 6656 * n := by ring
    _ ≤ 6656 * n * Nat.log 2 n := by
      nth_rewrite 1 [← mul_one (6656 * n)]
      exact Nat.mul_le_mul_left _ (by omega)

theorem heavyMiddleLateHorizon_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) :
    heavyMiddleHorizon n + heavyLateLadderHorizon n γ ≤
      131072 * n * Nat.log 2 n := by
  have hk := phase2StageCount_le_log n γ
  unfold heavyMiddleHorizon heavyLateLadderHorizon heavyLateHorizon
  calc
    65536 * n + phase2StageCount n γ * (65536 * n)
        ≤ 65536 * n + Nat.log 2 n * (65536 * n) := by
      gcongr
    _ = 65536 * n * (Nat.log 2 n + 1) := by ring
    _ ≤ 65536 * n * (2 * Nat.log 2 n) := by
      gcongr
      omega
    _ = 131072 * n * Nat.log 2 n := by ring

theorem heavyFinalHorizon_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    heavyFinalHorizon n γ ≤
      131072 * γ * n * Nat.log 2 n := by
  have hpos : 1 ≤ γ * Nat.log 2 n :=
    Nat.mul_pos (by omega) (by omega)
  unfold heavyFinalHorizon heavyFinalScale
  calc
    65536 * n * (γ * Nat.log 2 n + 1)
        ≤ 65536 * n * (2 * (γ * Nat.log 2 n)) := by
      gcongr
      omega
    _ = 131072 * γ * n * Nat.log 2 n := by ring

theorem heavyConsensusHorizon_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    heavyConsensusHorizon n γ ≤
      280000 * γ * n * Nat.log 2 n := by
  have he := heavyEarlyLadderHorizon_le n γ
  have hc := heavyConstantGapHorizon_le n hlog
  have hml := heavyMiddleLateHorizon_le n γ hlog
  have hf := heavyFinalHorizon_le n γ hlog hγ
  unfold heavyConsensusHorizon
  calc
    heavyEarlyLadderHorizon n γ +
          heavyConstantGapHorizon n +
          (heavyMiddleHorizon n + heavyLateLadderHorizon n γ) +
          heavyFinalHorizon n γ
        ≤ 3328 * n * Nat.log 2 n +
          6656 * n * Nat.log 2 n +
          131072 * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by omega
    _ = 141056 * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by ring
    _ ≤ 141056 * γ * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by
      gcongr
      exact Nat.mul_le_mul_left 141056 hγ
    _ = 272128 * γ * n * Nat.log 2 n := by ring
    _ ≤ 280000 * γ * n * Nat.log 2 n := by
      gcongr
      norm_num

end Tri

#print axioms Tri.heavyEarlyEnvelopeScale_ge_natLog
#print axioms Tri.heavyEarlyLadderError_le_power
#print axioms Tri.heavyConstantGapError_le_power
#print axioms Tri.heavyMiddleError_le_power
#print axioms Tri.heavyLateLadderError_le_power
#print axioms Tri.heavyConsensusError_le
#print axioms Tri.heavyConsensus_reaches
#print axioms Tri.heavyConsensusHorizon_le
