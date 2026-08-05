/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBFinalConsensus
import Tri.Assembly
import Tri.BudgetArith

/-!
# Unconditional Double-B consensus assembly

This composes the early joint-clock ladder, constant-gap handoff, middle rung,
dyadic late ladder, and the direct absorbing-consensus block.
-/

namespace Tri

open scoped ENNReal

def doubleConsensusHorizon (n γ : ℕ) : ℕ :=
  doubleEarlyLadderHorizon n γ +
    doubleConstantGapHorizon n +
    (doubleMiddleHorizon n + doubleLateLadderHorizon n γ) +
    doubleFinalHorizon n γ

/-- All-`X` consensus is absorbing on the invariant subtype. -/
theorem doubleStateStep_consensus
    (n : ℕ) (hn : 2 ≤ n) (s : DoubleState n)
    (hs : DoubleXConsensus s) :
    doubleStateStep n hn s = PMF.pure s := by
  have hconst : ∀ k, PairComp.nextDoubleState s k = s := by
    intro k
    unfold PairComp.nextDoubleState
    split_ifs with hk
    · rfl
    · apply Subtype.ext
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [DoubleXConsensus] at hs
      rcases hs with ⟨rfl, rfl, rfl⟩
      cases k <;> simp [PairComp.weight, PairComp.next] at hk ⊢
  unfold doubleStateStep
  rw [show PairComp.nextDoubleState s = (fun _ => s) from funext hconst]
  ext z
  rw [PMF.map_apply, PMF.pure_apply]
  by_cases hz : z = s
  · subst z
    simp only [if_true]
    exact PMF.tsum_coe _
  · simp only [if_neg hz, tsum_zero]

/-- Deeper inverse-power envelopes weaken to the common `1/3000` exponent. -/
theorem doubleInvPower_le_common
    (n γ : ℕ) (hn : 1 ≤ n) (a : ℝ)
    (ha : (1 / 3000 : ℝ) ≤ a) :
    (n : ℝ≥0∞)⁻¹ ^ (a * (γ : ℝ)) ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 3000 : ℝ) * (γ : ℝ)) := by
  apply ENNReal.rpow_le_rpow_of_exponent_ge
  · rw [ENNReal.inv_le_one]
    exact_mod_cast hn
  · have hγ0 : (0 : ℝ) ≤ γ := by positivity
    nlinarith

/-- The four ladder errors plus the direct final block fit one explicit
power-law budget. -/
theorem doubleConsensusError_le
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    doubleEarlyLadderError n γ +
        doubleConstantGapError n +
        (doubleMiddleError n + doubleLateLadderError n γ) +
        3 * (n : ℝ≥0∞)⁻¹ ^
          ((1 / 200 : ℝ) * (γ : ℝ)) ≤
      95 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 3000 : ℝ) * (γ : ℝ)) := by
  let X :=
    (n : ℝ≥0∞)⁻¹ ^ ((1 / 3000 : ℝ) * (γ : ℝ))
  have hnOne : 1 ≤ n := by omega
  have h24 :
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 24 : ℝ) * (γ : ℝ)) ≤ X := by
    dsimp only [X]
    exact doubleInvPower_le_common n γ hnOne (1 / 24) (by norm_num)
  have h200 :
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) ≤ X := by
    dsimp only [X]
    exact doubleInvPower_le_common n γ hnOne (1 / 200) (by norm_num)
  have he :
      doubleEarlyLadderError n γ ≤ 40 * X :=
    (doubleEarlyLadderError_le_power n γ
      (hlog.trans' (by norm_num)) hγ).trans (by gcongr)
  have hc :
      doubleConstantGapError n ≤ 40 * X := by
    simpa only [X] using
      doubleConstantGapError_le_power n γ
        (hlog.trans' (by norm_num)) hsize
  have hm :
      doubleMiddleError n ≤ 4 * X :=
    (doubleMiddleError_le_power n hn γ hlog hγ hsize).trans
      (by gcongr)
  have hl :
      doubleLateLadderError n γ ≤ 8 * X :=
    (doubleLateLadderError_le n hn γ hlog hγ hsize).trans
      (by gcongr)
  change
    doubleEarlyLadderError n γ +
        doubleConstantGapError n +
        (doubleMiddleError n + doubleLateLadderError n γ) +
        3 * (n : ℝ≥0∞)⁻¹ ^
          ((1 / 200 : ℝ) * (γ : ℝ)) ≤ 95 * X
  calc
    _ ≤ 40 * X + 40 * X + (4 * X + 8 * X) + 3 * X := by
      gcongr
    _ = 95 * X := by ring

/-- The complete Double-B construction reaches absorbing all-`X` consensus
from the paper's initial square-gap hypothesis. -/
theorem doubleConsensus_reaches
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (doubleStateStep n hn) (doubleConsensusHorizon n γ)
      (DoubleBEarlyInitial n γ)
      DoubleXConsensus
      (95 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 3000 : ℝ) * (γ : ℝ))) := by
  have he := doubleEarly_reaches n hn γ
    (hlog.trans' (by norm_num)) hγ
  have hc := doubleConstantGap_reaches n hn
    (hlog.trans' (by norm_num))
  have hl := doubleMiddleLate_reaches n hn γ hlog hγ
  have hf :=
    doubleFinalConsensus_reaches_power n hn γ hlog hγ hsize
  have h := ((he.comp hc).comp hl).comp hf
  apply h.mono_error
  simpa only [add_assoc] using
    doubleConsensusError_le n hn γ hlog hγ hsize

/-- The complete Double-B consensus route fits the paper's asymptotic
interaction horizon. -/
theorem doubleConsensusHorizon_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    doubleConsensusHorizon n γ ≤
      270000 * γ * n * Nat.log 2 n := by
  have he := doubleEarlyLadderHorizon_le n γ
  have hc := doubleConstantGapHorizon_le n hlog
  have hl := doubleMiddleLateHorizon_le n γ hlog
  have hf :
      doubleFinalHorizon n γ ≤
        131072 * γ * n * Nat.log 2 n := by
    simpa only [doubleFinalHorizon, doubleFinalScale,
      doubleEndHorizon] using
      doubleEndHorizon_le n γ hlog hγ
  unfold doubleConsensusHorizon
  calc
    doubleEarlyLadderHorizon n γ +
          doubleConstantGapHorizon n +
          (doubleMiddleHorizon n + doubleLateLadderHorizon n γ) +
          doubleFinalHorizon n γ
        ≤ 2304 * n * Nat.log 2 n +
          4608 * n * Nat.log 2 n +
          131072 * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by omega
    _ = 137984 * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by ring
    _ ≤ 137984 * γ * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by
      gcongr
      exact Nat.mul_le_mul_left 137984 hγ
    _ = 269056 * γ * n * Nat.log 2 n := by ring
    _ ≤ 270000 * γ * n * Nat.log 2 n := by
      gcongr
      norm_num

/-! ## Absorbing the fixed coefficient and closing `Theorem2_doubleB_statement` -/

/-- The chosen global threshold clears the coefficient `95`. -/
theorem doubleHeadlineCoefficient_clear
    {n γ : ℕ} (hn : 2 ^ 60000 ≤ n) (hγ : 1 ≤ γ) :
    95 * (n : ℝ≥0∞)⁻¹ ^
          ((1 / 3000 : ℝ) * (γ : ℝ)) ≤
      (n : ℝ≥0∞)⁻¹ ^
          ((1 / 6000 : ℝ) * (γ : ℝ)) := by
  have hnOne : 1 ≤ n := by
    exact le_trans (Nat.one_le_pow 60000 2 (by norm_num)) hn
  have hnOneE : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hnOne
  have hbase :
      ((2 : ℝ≥0∞) ^ (60000 : ℕ)) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hn
  have hrootEq :
      ((2 : ℝ≥0∞) ^ (60000 : ℕ)) ^ ((1 : ℝ) / 6000) =
        1024 := by
    rw [← ENNReal.rpow_natCast (2 : ℝ≥0∞) 60000,
      ← ENNReal.rpow_mul]
    norm_num
  have hroot :
      (1024 : ℝ≥0∞) ≤
        (n : ℝ≥0∞) ^ ((1 : ℝ) / 6000) := by
    rw [← hrootEq]
    exact ENNReal.rpow_le_rpow hbase (by norm_num)
  have hmono :
      (n : ℝ≥0∞) ^ ((1 : ℝ) / 6000) ≤
        (n : ℝ≥0∞) ^
          ((1 / 6000 : ℝ) * (γ : ℝ)) := by
    apply ENNReal.rpow_le_rpow_of_exponent_le hnOneE
    have hγR : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
    nlinarith
  have hthreshold :
      3 * (95 : ℝ≥0∞) ≤
        (n : ℝ≥0∞) ^
          (((1 / 3000 : ℝ) * (γ : ℝ)) -
            ((1 / 6000 : ℝ) * (γ : ℝ))) := by
    have h285 :
        (285 : ℝ≥0∞) ≤
          (n : ℝ≥0∞) ^
            ((1 / 6000 : ℝ) * (γ : ℝ)) :=
      (by norm_num : (285 : ℝ≥0∞) ≤ 1024) |>.trans
        (hroot.trans hmono)
    convert h285 using 1 <;> ring
  have hthird :=
    inv_rpow_third 95
      ((1 / 3000 : ℝ) * (γ : ℝ))
      ((1 / 6000 : ℝ) * (γ : ℝ))
      n (by
        have hγ0 : (0 : ℝ) ≤ γ := by positivity
        nlinarith)
      hnOne hthreshold
  exact hthird.trans (by
    calc
      (1 / 3 : ℝ≥0∞) *
            (n : ℝ≥0∞)⁻¹ ^
              ((1 / 6000 : ℝ) * (γ : ℝ))
          ≤ 1 *
            (n : ℝ≥0∞)⁻¹ ^
              ((1 / 6000 : ℝ) * (γ : ℝ)) := by gcongr <;> norm_num
      _ = _ := one_mul _)

/-- The unconditional Double-B clause of Theorem 2. -/
theorem theorem2_doubleB : Theorem2_doubleB_statement := by
  refine ⟨270000, 2 ^ 60000, (1 / 6000 : ℝ),
    (by norm_num), (by norm_num), ?_, ?_⟩
  · calc
      3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 60000 :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · intro n γ hn0 hγ hsize s₀ hinv hpaper
    have hn : 2 ≤ n := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 60000 :=
          Nat.pow_le_pow_right (by norm_num) (by norm_num)
        _ ≤ n := hn0
    have hlog : 128 ≤ Nat.log 2 n := by
      apply Nat.le_log_of_pow_le (by norm_num)
      exact le_trans
        (Nat.pow_le_pow_right (by norm_num) (by norm_num : 128 ≤ 60000))
        hn0
    let s : DoubleState n := ⟨s₀, hinv⟩
    have hr :=
      doubleConsensus_reaches n hn γ hlog hγ hsize
    have hH :=
      doubleConsensusHorizon_le n γ hlog hγ
    let targetT := 270000 * γ * n * Nat.log 2 n
    have hpad :=
      hr.pad_of_absorbing
        (doubleStateStep_consensus n hn)
        (targetT - doubleConsensusHorizon n γ)
    have htime :
        doubleConsensusHorizon n γ +
            (targetT - doubleConsensusHorizon n γ) = targetT := by
      exact Nat.add_sub_of_le hH
    rw [htime] at hpad
    have hreach :=
      hpad.mono_error (doubleHeadlineCoefficient_clear hn0 hγ)
    have hs : DoubleBEarlyInitial n γ s := by
      rcases hpaper with ⟨_, gap, hgap, hgapSq⟩
      refine ⟨gap, ?_, hgapSq⟩
      dsimp only [s]
      simp only [BiCfg.doubleLevel, BiCfg.DoubleInv] at hinv ⊢
      omega
    have hmass := hreach s hs
    rw [doubleState_nonconsensus_mass_eq n hn targetT s] at hmass
    simpa only [targetT, s] using hmass

end Tri

#print axioms Tri.doubleInvPower_le_common
#print axioms Tri.doubleConsensusError_le
#print axioms Tri.doubleConsensus_reaches
#print axioms Tri.doubleConsensusHorizon_le
#print axioms Tri.doubleStateStep_consensus
#print axioms Tri.doubleHeadlineCoefficient_clear
#print axioms Tri.theorem2_doubleB
