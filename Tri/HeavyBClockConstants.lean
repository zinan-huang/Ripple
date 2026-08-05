/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBClockProjection
import Tri.RatioExp

/-!
# Scalar constants for the Heavy-B joint clock

The conservative fixed horizon uses

`K = n+2M`, `H = 32K`, `T = 64K`.

The normal clock error is bounded by `(3/4)^K`.  The Heavy-B blank clock has
base `n/(n+g)` and reciprocal tick multiplier
`2(n+g)^2 / (2(n+g)^2 + g^2)`, giving a Gaussian-scale envelope.
-/

namespace Tri

open scoped ENNReal

/-- Fuel budget used by the fixed Heavy-B clock envelope. -/
def heavyClockBudget (n M : ℕ) : ℕ := n + 2 * M

/-- Number of ticks assigned to either occupation branch. -/
def heavyClockHalfHorizon (n M : ℕ) : ℕ :=
  32 * heavyClockBudget n M

/-- Full raw-interaction horizon of one early Heavy-B rung. -/
def heavyClockHorizon (n M : ℕ) : ℕ :=
  64 * heavyClockBudget n M

theorem two_heavyClockHalfHorizon (n M : ℕ) :
    2 * heavyClockHalfHorizon n M = heavyClockHorizon n M := by
  simp [heavyClockHalfHorizon, heavyClockHorizon]
  ring

/-- The concrete normal-occupation error is bounded by `(3/4)^K`. -/
theorem heavyNormalClockError_le
    (K : ℕ) :
    1 / (((32 : ℝ≥0∞) / 31) ^ (32 * K) * (1 / 2) ^ K) ≤
      ((3 : ℝ≥0∞) / 4) ^ K := by
  have hbase :
      (4 : ℝ≥0∞) / 3 ≤
        ((32 : ℝ≥0∞) / 31) ^ 32 * (1 / 2) := by
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    norm_num
  have hden :
      ((4 : ℝ≥0∞) / 3) ^ K ≤
        ((32 : ℝ≥0∞) / 31) ^ (32 * K) * (1 / 2) ^ K := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left' hbase K
  calc
    1 / (((32 : ℝ≥0∞) / 31) ^ (32 * K) * (1 / 2) ^ K)
        ≤ 1 / (((4 : ℝ≥0∞) / 3) ^ K) :=
      ENNReal.div_le_div_left hden 1
    _ = ((3 : ℝ≥0∞) / 4) ^ K := by
      rw [one_div, ENNReal.inv_pow]
      congr 1
      apply (ENNReal.toReal_eq_toReal_iff'
        (ENNReal.inv_ne_top.mpr (by norm_num)) (by finiteness)).mp
      norm_num

/-- Exact natural-ratio form of the reciprocal Heavy-B blank multiplier. -/
theorem heavyBlankEta_inv
    (n g : ℕ) (hn : 0 < n) :
    (heavyBlankEta n g)⁻¹ =
      ((2 * (n + g) ^ 2 : ℕ) : ℝ≥0∞) /
        ((2 * (n + g) ^ 2 + g ^ 2 : ℕ) : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by unfold heavyBlankEta heavyBlankR; finiteness)
    (by finiteness)).mp
  unfold heavyBlankEta
  rw [ENNReal.toReal_inv]
  rw [ENNReal.toReal_add ENNReal.one_ne_top
    (by unfold heavyBlankR; finiteness)]
  unfold heavyBlankR
  simp only [ENNReal.toReal_one, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]
  rw [show ENNReal.toReal 2 = 2 by norm_num]
  have hd : (n + g : ℝ) ≠ 0 := by positivity
  have heta :
      1 + (g : ℝ) ^ 2 / (n + g : ℝ) ^ 2 / 2 ≠ 0 := by
    positivity
  field_simp [heta, hd]
  push_cast
  ring

/-- Exponential upper bound for the reciprocal blank multiplier over `H`
occupation ticks. -/
theorem heavyBlankEta_inv_pow_le_exp
    (n g H : ℕ) (hn : 0 < n) :
    1 / heavyBlankEta n g ^ H ≤
      ENNReal.ofReal
        (Real.exp
          (-(H : ℝ) *
            (((2 * (n + g) ^ 2 + g ^ 2 : ℕ) : ℝ) -
            ((2 * (n + g) ^ 2 : ℕ) : ℝ)) /
            ((2 * (n + g) ^ 2 + g ^ 2 : ℕ) : ℝ))) := by
  rw [one_div, ENNReal.inv_pow, heavyBlankEta_inv n g hn]
  exact ratio_pow_le_exp
    (2 * (n + g) ^ 2 + g ^ 2)
    (2 * (n + g) ^ 2) H
    (by positivity) (by omega)

/-- Simplified exponent in the reciprocal blank-multiplier bound. -/
theorem heavyBlankEta_inv_pow_le_exp'
    (n g H : ℕ) (hn : 0 < n) :
    1 / heavyBlankEta n g ^ H ≤
      ENNReal.ofReal
        (Real.exp
          (-((H : ℝ) * (g : ℝ) ^ 2 /
            (2 * ((n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2)))) := by
  have hraw := heavyBlankEta_inv_pow_le_exp n g H hn
  have hexp :
      -(H : ℝ) *
            (((2 * (n + g) ^ 2 + g ^ 2 : ℕ) : ℝ) -
              ((2 * (n + g) ^ 2 : ℕ) : ℝ)) /
            ((2 * (n + g) ^ 2 + g ^ 2 : ℕ) : ℝ) =
        -((H : ℝ) * (g : ℝ) ^ 2 /
          (2 * ((n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2)) := by
    push_cast
    ring
  rwa [hexp] at hraw

/-- Exact exponential envelope for the full blank-clock error: potential
growth across a band of width `hi-start` minus the occupation decay. -/
theorem heavyBlankClockError_le_exp
    (n g start hi H : ℕ)
    (hn : 0 < n) (hstart : start ≤ hi) :
    heavyBlankW n g ^ start /
        (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) ≤
      ENNReal.ofReal
        (Real.exp
          (((hi : ℝ) - (start : ℝ)) *
              Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ)) -
            (H : ℝ) * (g : ℝ) ^ 2 /
              (2 * ((n : ℝ) + (g : ℝ)) ^ 2 +
                (g : ℝ) ^ 2))) := by
  have hratio :=
    base_pow_ratio_le_ofReal_exp
      n (n + g) start hi
      hn (by omega) hstart
  have hratio' :
      heavyBlankW n g ^ start / heavyBlankW n g ^ hi ≤
        ENNReal.ofReal
          (Real.exp
            (((hi : ℝ) - (start : ℝ)) *
              Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ)))) := by
    simpa [heavyBlankW] using hratio
  have heta := heavyBlankEta_inv_pow_le_exp' n g H hn
  have hw0 : heavyBlankW n g ≠ 0 := by
    unfold heavyBlankW
    exact ne_of_gt (ENNReal.div_pos
      (by simp only [ne_eq, Nat.cast_eq_zero]; omega)
      (ENNReal.natCast_ne_top _))
  have hwt : heavyBlankW n g ≠ ⊤ := by
    unfold heavyBlankW
    finiteness
  have hsplit :
      heavyBlankW n g ^ start /
          (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) =
        (heavyBlankW n g ^ start / heavyBlankW n g ^ hi) *
          (1 / heavyBlankEta n g ^ H) := by
    simpa using
      (ENNReal.mul_div_mul_comm
        (a := heavyBlankW n g ^ start) (b := 1)
        (c := heavyBlankW n g ^ hi) (d := heavyBlankEta n g ^ H)
        (Or.inl (pow_ne_zero _ hw0))
        (Or.inl (ENNReal.pow_ne_top hwt)))
  rw [hsplit]
  calc
    (heavyBlankW n g ^ start / heavyBlankW n g ^ hi) *
          (1 / heavyBlankEta n g ^ H)
        ≤ ENNReal.ofReal
              (Real.exp
                (((hi : ℝ) - (start : ℝ)) *
                  Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ)))) *
            ENNReal.ofReal
              (Real.exp
                (-((H : ℝ) * (g : ℝ) ^ 2 /
                  (2 * ((n : ℝ) + (g : ℝ)) ^ 2 +
                    (g : ℝ) ^ 2)))) :=
      mul_le_mul hratio' heta bot_le bot_le
    _ = ENNReal.ofReal
          (Real.exp
            (((hi : ℝ) - (start : ℝ)) *
                Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ)) -
              (H : ℝ) * (g : ℝ) ^ 2 /
                (2 * ((n : ℝ) + (g : ℝ)) ^ 2 +
                  (g : ℝ) ^ 2))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 3

/-- With at least `32n` blank-exposure budget and band width at most `g`, the
blank-clock exponent is at most `-g²/n`. -/
theorem heavyBlankClockExponent_le
    (n g start hi H : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : start ≤ hi) (hwidth : hi ≤ start + g)
    (hH : 32 * n ≤ H) :
    ((hi : ℝ) - (start : ℝ)) *
          Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ)) -
        (H : ℝ) * (g : ℝ) ^ 2 /
          (2 * ((n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2)
      ≤ -((g : ℝ) ^ 2 / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgR : (g : ℝ) ≤ n := by exact_mod_cast hg
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hratio :
      (0 : ℝ) < (n + g) / n := by positivity
  have hlog :=
    Real.log_le_sub_one_of_pos hratio
  have hratioSub :
      ((n : ℝ) + (g : ℝ)) / (n : ℝ) - 1 =
        (g : ℝ) / (n : ℝ) := by
    field_simp
    ring
  rw [hratioSub] at hlog
  have hratioOne :
      (1 : ℝ) ≤ ((n : ℝ) + (g : ℝ)) / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    linarith
  have hlog0 :
      0 ≤ Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ)) :=
    Real.log_nonneg hratioOne
  have hwidthNat : hi - start ≤ g := by omega
  have hwidthR : (hi : ℝ) - (start : ℝ) ≤ g := by
    rw [← Nat.cast_sub hstart]
    exact_mod_cast hwidthNat
  have hA :
      ((hi : ℝ) - (start : ℝ)) *
          Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ)) ≤
        (g : ℝ) ^ 2 / n := by
    calc
      ((hi : ℝ) - (start : ℝ)) *
            Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ))
          ≤ g * Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hwidthR hlog0
      _ ≤ g * (g / n) :=
        mul_le_mul_of_nonneg_left hlog hg0
      _ = g ^ 2 / n := by ring
  let D : ℝ :=
    2 * ((n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hng : (n : ℝ) + (g : ℝ) ≤ 2 * n := by linarith
  have hDupper : D ≤ 9 * n ^ 2 := by
    dsimp [D]
    nlinarith [mul_pos hnR hnR]
  have hHR : (32 : ℝ) * n ≤ H := by exact_mod_cast hH
  have hcross : 2 * D ≤ n * H := by
    nlinarith [mul_pos hnR hnR]
  have hB :
      2 * (g : ℝ) ^ 2 / n ≤
        (H : ℝ) * (g : ℝ) ^ 2 / D := by
    apply (div_le_div_iff₀ hnR hDpos).2
    have hscaled := mul_le_mul_of_nonneg_right hcross (sq_nonneg (g : ℝ))
    nlinarith
  dsimp [D] at hB
  calc
    ((hi : ℝ) - (start : ℝ)) *
          Real.log (((n : ℝ) + (g : ℝ)) / (n : ℝ)) -
        (H : ℝ) * (g : ℝ) ^ 2 /
          (2 * ((n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2)
      ≤ (g : ℝ) ^ 2 / n -
        (H : ℝ) * (g : ℝ) ^ 2 /
          (2 * ((n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2) := by
        exact sub_le_sub_right hA _
    _ ≤ (g : ℝ) ^ 2 / n - 2 * (g : ℝ) ^ 2 / n := by
        exact sub_le_sub_left hB _
    _ = -((g : ℝ) ^ 2 / (n : ℝ)) := by ring

/-- Gaussian-scale bound for the Heavy-B blank-clock error under the concrete
early band budget. -/
theorem heavyBlankClockError_le_exp_neg
    (n g start hi H : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : start ≤ hi) (hwidth : hi ≤ start + g)
    (hH : 32 * n ≤ H) :
    heavyBlankW n g ^ start /
        (heavyBlankW n g ^ hi * heavyBlankEta n g ^ H) ≤
      ENNReal.ofReal
        (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ))) ) := by
  refine le_trans
    (heavyBlankClockError_le_exp n g start hi H hn hstart) ?_
  exact ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr
      (heavyBlankClockExponent_le
        n g start hi H hn hg hstart hwidth hH))

/-- A uniform envelope for the two occupation-clock errors of one Heavy-B rung. -/
noncomputable def heavyJointClockEnvelope
    (n g M : ℕ) : ℝ≥0∞ :=
  ((3 : ℝ≥0∞) / 4) ^ heavyClockBudget n M +
    ENNReal.ofReal (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ))))

/-- At the concrete half-horizon, the two occupation-clock errors are bounded
by a geometric normal term plus a Gaussian-scale blank term. -/
theorem heavyJointClockError_le
    (n g start hi M : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : start ≤ hi) (hwidth : hi ≤ start + g) :
    1 / (((32 : ℝ≥0∞) / 31) ^ heavyClockHalfHorizon n M *
          (1 / 2) ^ heavyClockBudget n M) +
        heavyBlankW n g ^ start /
          (heavyBlankW n g ^ hi *
            heavyBlankEta n g ^ heavyClockHalfHorizon n M) ≤
      heavyJointClockEnvelope n g M := by
  unfold heavyJointClockEnvelope
  apply add_le_add
  · simpa [heavyClockHalfHorizon, heavyClockBudget] using
      heavyNormalClockError_le (heavyClockBudget n M)
  · apply heavyBlankClockError_le_exp_neg
      n g start hi (heavyClockHalfHorizon n M)
      hn hg hstart hwidth
    simp [heavyClockHalfHorizon, heavyClockBudget]

end Tri

#print axioms Tri.two_heavyClockHalfHorizon
#print axioms Tri.heavyNormalClockError_le
#print axioms Tri.heavyBlankEta_inv
#print axioms Tri.heavyBlankEta_inv_pow_le_exp
#print axioms Tri.heavyBlankClockError_le_exp
#print axioms Tri.heavyBlankClockError_le_exp_neg
#print axioms Tri.heavyJointClockError_le
