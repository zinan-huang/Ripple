/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBEarlyLadder

/-!
# Double-B handoff to a constant effective gap

The first-hit early ladder exposes the fixed checkpoint
`n + 4⌊n/144⌋`.  Two more admissible joint-clock stages, at scales
`⌊n/144⌋` and `2⌊n/144⌋`, raise this to `n + 16⌊n/144⌋`, hence at least
`n + ⌊n/10⌋` in the headline regime.  At that point the ordinary
level-productivity clock has a constant-fraction lower gap and can take over.
-/

namespace Tri

open scoped ENNReal

/-- Fixed scale used to leave the blank-heavy early regime. -/
def doubleConstantGapScale (n : ℕ) : ℕ :=
  n / 144

/-- Raw horizon of the two-stage constant-gap handoff. -/
def doubleConstantGapHorizon (n : ℕ) : ℕ :=
  2 * doubleEarlyStageHorizon n

/-- Exact error of the two-stage constant-gap handoff. -/
noncomputable def doubleConstantGapError (n : ℕ) : ℝ≥0∞ :=
  doubleEarlyStageError n (doubleConstantGapScale n) +
    doubleEarlyStageError n (2 * doubleConstantGapScale n)

/-- First Gaussian exponent of the constant-gap handoff. -/
noncomputable def doubleConstantGapEnvelopeScale (n : ℕ) : ℝ :=
  4 * (doubleConstantGapScale n : ℝ) ^ 2 / (n : ℝ)

/-- In the large-size regime, both fixed handoff stages satisfy the
joint-clock width guard. -/
theorem doubleConstantGapScale_guards
    {n : ℕ} (hlog : 12 ≤ Nat.log 2 n) :
    0 < doubleConstantGapScale n ∧
      72 * doubleConstantGapScale n ≤ n ∧
      72 * (2 * doubleConstantGapScale n) ≤ n := by
  have hn : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  unfold doubleConstantGapScale
  constructor
  · omega
  constructor
  · calc
      72 * (n / 144) ≤ 144 * (n / 144) := by omega
      _ ≤ n := Nat.mul_div_le n 144
  · calc
      72 * (2 * (n / 144)) = 144 * (n / 144) := by ring
      _ ≤ n := Nat.mul_div_le n 144

/-- The end of the handoff has a fixed one-tenth effective gap. -/
theorem doubleConstantGap_target_arithmetic
    {n : ℕ} (hlog : 12 ≤ Nat.log 2 n) :
    n + n / 10 ≤
      doubleEarlyLevel n (4 * doubleConstantGapScale n) 0 := by
  have hn : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hmod := Nat.mod_lt n (by norm_num : 0 < 144)
  have hdecomp := Nat.mod_add_div n 144
  unfold doubleEarlyLevel doubleConstantGapScale
  omega

/-- Two final joint-clock stages carry the early target into the
constant-gap regime. -/
theorem doubleConstantGap_reaches
    (n : ℕ) (hn : 2 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    Reaches (doubleStateStep n hn) (doubleConstantGapHorizon n)
      (fun s => doubleEarlyTarget n ≤ s.1.doubleLevel)
      (fun s => n + n / 10 ≤ s.1.doubleLevel)
      (doubleConstantGapError n) := by
  let q := doubleConstantGapScale n
  have hguards := doubleConstantGapScale_guards hlog
  have hq : 0 < q := by simpa only [q] using hguards.1
  have hqSmall : 72 * q ≤ n := by
    simpa only [q] using hguards.2.1
  have h2qSmall : 72 * (2 * q) ≤ n := by
    simpa only [q] using hguards.2.2
  have hfirst := doubleEarly_stage n hn q hq hqSmall
  have hsecond :=
    doubleEarly_stage n hn (2 * q) (by omega) h2qSmall
  have hchain := hfirst.comp hsecond
  have hstart :
      (fun s : DoubleState n => doubleEarlyTarget n ≤ s.1.doubleLevel) =
        DoubleEarlyCheckpoint n q 0 := by
    funext s
    unfold doubleEarlyTarget DoubleEarlyCheckpoint doubleEarlyLevel
    apply propext
    rfl
  have hpost := hchain.mono_post (by
    intro s hs
    change doubleEarlyLevel n (2 * (2 * q)) 0 ≤ s.1.doubleLevel at hs
    calc
      n + n / 10 ≤
          doubleEarlyLevel n (4 * doubleConstantGapScale n) 0 :=
        doubleConstantGap_target_arithmetic hlog
      _ = doubleEarlyLevel n (2 * (2 * q)) 0 := by
        unfold doubleEarlyLevel
        dsimp only [q]
        ring
      _ ≤ s.1.doubleLevel := hs)
  simpa only [q, hstart, doubleConstantGapHorizon,
    doubleConstantGapError, two_mul] using hpost

/-- The two handoff stages cost at most forty copies of the first fixed-scale
Gaussian envelope. -/
theorem doubleConstantGapError_le_gaussian
    (n : ℕ) (hlog : 12 ≤ Nat.log 2 n) :
    doubleConstantGapError n ≤
      40 * ENNReal.ofReal
        (Real.exp (-doubleConstantGapEnvelopeScale n)) := by
  let q := doubleConstantGapScale n
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hguards := doubleConstantGapScale_guards hlog
  have hq : 0 < q := by simpa only [q] using hguards.1
  have hqSmall : 72 * q ≤ n := by
    simpa only [q] using hguards.2.1
  have h2qSmall : 72 * (2 * q) ≤ n := by
    simpa only [q] using hguards.2.2
  let E : ℝ≥0∞ :=
    ENNReal.ofReal
      (Real.exp (-((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ))))
  have hfirst :=
    doubleEarlyStageError_le n q hq hqSmall
  have hsecond :=
    doubleEarlyStageError_le n (2 * q) (by omega) h2qSmall
  have hexp :
      ENNReal.ofReal
          (Real.exp
            (-((4 : ℝ) * ((2 * q : ℕ) : ℝ) ^ 2 / (n : ℝ)))) ≤ E := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    change
      -((4 : ℝ) * ((2 * q : ℕ) : ℝ) ^ 2 / (n : ℝ)) ≤
        -((4 : ℝ) * (q : ℝ) ^ 2 / (n : ℝ))
    rw [neg_le_neg_iff]
    push_cast
    apply (div_le_div_iff_of_pos_right hnReal).2
    nlinarith [show (0 : ℝ) ≤ (q : ℝ) ^ 2 by positivity]
  have hsecond' : doubleEarlyStageError n (2 * q) ≤ 20 * E :=
    hsecond.trans (by gcongr)
  unfold doubleConstantGapError
  change doubleEarlyStageError n q +
      doubleEarlyStageError n (2 * q) ≤ _
  calc
    doubleEarlyStageError n q + doubleEarlyStageError n (2 * q)
        ≤ 20 * E + 20 * E := add_le_add hfirst hsecond'
    _ = 40 * E := by ring
    _ = 40 * ENNReal.ofReal
        (Real.exp (-doubleConstantGapEnvelopeScale n)) := by
      congr 3

/-- Under the headline size guard, the fixed handoff exponent retains a
`γ lg n / 3456` scale. -/
theorem doubleConstantGapEnvelopeScale_ge_natLog
    (n γ : ℕ) (hlog : 12 ≤ Nat.log 2 n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 3456 ≤
      doubleConstantGapEnvelopeScale n := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  let q := doubleConstantGapScale n
  have hmod := Nat.mod_lt n (by norm_num : 0 < 144)
  have hdecomp := Nat.mod_add_div n 144
  have hnq : n ≤ 288 * q := by
    dsimp only [q, doubleConstantGapScale]
    omega
  have hnqSq : n ^ 2 ≤ 82944 * q ^ 2 := by
    have hp := Nat.pow_le_pow_left hnq 2
    nlinarith
  have hnqSqR : (n : ℝ) ^ 2 ≤ 82944 * (q : ℝ) ^ 2 := by
    exact_mod_cast hnqSq
  have hsizeR :
      6 * (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ n := by
    exact_mod_cast hsize
  change
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 3456 ≤
      4 * (q : ℝ) ^ 2 / (n : ℝ)
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3456) hnReal]
  nlinarith [sq_nonneg ((n : ℝ))]

/-- The floored binary logarithm leaves the margin needed to convert the
handoff Gaussian to exponent `1/3000`. -/
theorem doubleConstantGap_natLog_margin
    {n : ℕ} (hlog : 12 ≤ Nat.log 2 n) :
    Real.log (n : ℝ) / 3000 ≤
      (Nat.log 2 n : ℝ) / 3456 := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hpowUpper :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have hpowUpperCast :
      (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast hpowUpper
  have hlogUpper :
      Real.log (n : ℝ) <
        ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 := by
    have h := Real.log_lt_log hnReal hpowUpperCast
    simpa only [Real.log_pow] using h
  have hlogTwo : Real.log 2 ≤ (0.6931471808 : ℝ) :=
    Real.log_two_lt_d9.le
  have hmulLog :
      ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        ((Nat.log 2 n + 1 : ℕ) : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hlogTwo (by positivity)
  have hlogCast : (12 : ℝ) ≤ Nat.log 2 n := by
    exact_mod_cast hlog
  have hcoefficient :
      3456 * (((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2) ≤
        3000 * (Nat.log 2 n : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hmulLog ⊢
    nlinarith
  nlinarith

/-- The fixed handoff Gaussian has a coefficient-`40`,
exponent-`1/3000` power-law budget. -/
theorem doubleConstantGapError_le_power
    (n γ : ℕ) (hlog : 12 ≤ Nat.log 2 n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    doubleConstantGapError n ≤
      40 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 3000 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size hlog
    omega
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hmargin := doubleConstantGap_natLog_margin hlog
  have hmarginMul :
      (γ : ℝ) * (Real.log (n : ℝ) / 3000) ≤
        (γ : ℝ) * ((Nat.log 2 n : ℝ) / 3456) :=
    mul_le_mul_of_nonneg_left hmargin (by positivity)
  have htarget :
      Real.log (n : ℝ) * ((1 / 3000 : ℝ) * (γ : ℝ)) ≤
        doubleConstantGapEnvelopeScale n := by
    calc
      Real.log (n : ℝ) * ((1 / 3000 : ℝ) * (γ : ℝ)) =
          (γ : ℝ) * (Real.log (n : ℝ) / 3000) := by ring
      _ ≤ (γ : ℝ) * ((Nat.log 2 n : ℝ) / 3456) := hmarginMul
      _ = (γ : ℝ) * (Nat.log 2 n : ℝ) / 3456 := by ring
      _ ≤ doubleConstantGapEnvelopeScale n :=
        doubleConstantGapEnvelopeScale_ge_natLog n γ hlog hsize
  have hexp :
      Real.exp (-doubleConstantGapEnvelopeScale n) ≤
        ((n : ℝ)⁻¹) ^ ((1 / 3000 : ℝ) * (γ : ℝ)) := by
    calc
      Real.exp (-doubleConstantGapEnvelopeScale n) ≤
          Real.exp
            (-Real.log (n : ℝ) * ((1 / 3000 : ℝ) * (γ : ℝ))) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = ((n : ℝ)⁻¹) ^ ((1 / 3000 : ℝ) * (γ : ℝ)) := by
        rw [Real.rpow_def_of_pos (inv_pos.mpr hnReal), Real.log_inv]
  calc
    doubleConstantGapError n ≤
        40 * ENNReal.ofReal
          (Real.exp (-doubleConstantGapEnvelopeScale n)) :=
      doubleConstantGapError_le_gaussian n hlog
    _ ≤ 40 * ENNReal.ofReal
          (((n : ℝ)⁻¹) ^ ((1 / 3000 : ℝ) * (γ : ℝ))) :=
      by gcongr
    _ = 40 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 3000 : ℝ) * (γ : ℝ)) := by
      rw [← ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hnReal),
        ENNReal.ofReal_inv_of_pos hnReal, ENNReal.ofReal_natCast]

end Tri

#print axioms Tri.doubleConstantGapScale_guards
#print axioms Tri.doubleConstantGap_target_arithmetic
#print axioms Tri.doubleConstantGap_reaches
#print axioms Tri.doubleConstantGapError_le_gaussian
#print axioms Tri.doubleConstantGapEnvelopeScale_ge_natLog
#print axioms Tri.doubleConstantGap_natLog_margin
#print axioms Tri.doubleConstantGapError_le_power
