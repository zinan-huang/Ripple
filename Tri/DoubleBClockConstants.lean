/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBClockRung
import Tri.RatioExp

/-!
# Scalar constants for the Double-B joint clock

The conservative fixed horizon uses

`K = n+2M`, `H = 32K`, `T = 64K`.

The normal error then decays at least as `(3/4)^K`.  For the blank error, the
reciprocal occupation multiplier is rewritten as an exact natural-number
ratio, so the existing harmonic-ratio exponential lemma applies directly.
-/

namespace Tri

open scoped ENNReal

/-- Fuel budget forced by fewer than `M` resolutions. -/
def doubleClockBudget (n M : ℕ) : ℕ := n + 2 * M

/-- Number of ticks assigned to either occupation branch. -/
def doubleClockHalfHorizon (n M : ℕ) : ℕ :=
  32 * doubleClockBudget n M

/-- Full raw-interaction horizon of one early rung. -/
def doubleClockHorizon (n M : ℕ) : ℕ :=
  64 * doubleClockBudget n M

theorem two_doubleClockHalfHorizon (n M : ℕ) :
    2 * doubleClockHalfHorizon n M = doubleClockHorizon n M := by
  simp [doubleClockHalfHorizon, doubleClockHorizon]
  ring

/-- The concrete normal-occupation error is bounded by `(3/4)^K`. -/
theorem doubleNormalClockError_le
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

/-- Exact natural-ratio form of the reciprocal blank multiplier. -/
theorem doubleBlankEta_inv
    (n g : ℕ) (hn : 0 < n) :
    (doubleBlankEta n g)⁻¹ =
      ((2 * (2 * n + g) ^ 2 : ℕ) : ℝ≥0∞) /
        ((2 * (2 * n + g) ^ 2 + g ^ 2 : ℕ) : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by unfold doubleBlankEta doubleBlankR; finiteness)
    (by finiteness)).mp
  unfold doubleBlankEta
  rw [ENNReal.toReal_inv]
  rw [ENNReal.toReal_add ENNReal.one_ne_top
    (by unfold doubleBlankR; finiteness)]
  unfold doubleBlankR
  simp only [ENNReal.toReal_one, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]
  rw [show ENNReal.toReal 2 = 2 by norm_num]
  have hd : (2 * n + g : ℝ) ≠ 0 := by positivity
  have heta :
      1 + (g : ℝ) ^ 2 / (2 * n + g : ℝ) ^ 2 / 2 ≠ 0 := by
    positivity
  field_simp [heta]
  push_cast
  ring

/-- Exponential upper bound for the reciprocal blank multiplier over `H`
occupation ticks. -/
theorem doubleBlankEta_inv_pow_le_exp
    (n g H : ℕ) (hn : 0 < n) :
    1 / doubleBlankEta n g ^ H ≤
      ENNReal.ofReal
        (Real.exp
          (-(H : ℝ) *
            (((2 * (2 * n + g) ^ 2 + g ^ 2 : ℕ) : ℝ) -
            ((2 * (2 * n + g) ^ 2 : ℕ) : ℝ)) /
            ((2 * (2 * n + g) ^ 2 + g ^ 2 : ℕ) : ℝ))) := by
  rw [one_div, ENNReal.inv_pow, doubleBlankEta_inv n g hn]
  exact ratio_pow_le_exp
    (2 * (2 * n + g) ^ 2 + g ^ 2)
    (2 * (2 * n + g) ^ 2) H
    (by positivity) (by omega)

/-- Simplified exponent in the reciprocal blank-multiplier bound. -/
theorem doubleBlankEta_inv_pow_le_exp'
    (n g H : ℕ) (hn : 0 < n) :
    1 / doubleBlankEta n g ^ H ≤
      ENNReal.ofReal
        (Real.exp
          (-((H : ℝ) * (g : ℝ) ^ 2 /
            (2 * (2 * (n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2)))) := by
  have hraw := doubleBlankEta_inv_pow_le_exp n g H hn
  have hexp :
      -(H : ℝ) *
            (((2 * (2 * n + g) ^ 2 + g ^ 2 : ℕ) : ℝ) -
              ((2 * (2 * n + g) ^ 2 : ℕ) : ℝ)) /
            ((2 * (2 * n + g) ^ 2 + g ^ 2 : ℕ) : ℝ) =
        -((H : ℝ) * (g : ℝ) ^ 2 /
          (2 * (2 * (n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2)) := by
    push_cast
    ring
  rwa [hexp] at hraw

/-- Exact exponential envelope for the full blank-clock error: potential
growth across a band of width `hi-start` minus the occupation decay. -/
theorem doubleBlankClockError_le_exp
    (n g start hi H : ℕ)
    (hn : 0 < n) (hstart : start ≤ hi) :
    doubleBlankW n g ^ start /
        (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) ≤
      ENNReal.ofReal
        (Real.exp
          (((hi : ℝ) - (start : ℝ)) *
              Real.log ((2 * (n : ℝ) + (g : ℝ)) /
                (2 * (n : ℝ))) -
            (H : ℝ) * (g : ℝ) ^ 2 /
              (2 * (2 * (n : ℝ) + (g : ℝ)) ^ 2 +
                (g : ℝ) ^ 2))) := by
  have hratio :=
    base_pow_ratio_le_ofReal_exp
      (2 * n) (2 * n + g) start hi
      (by positivity) (by omega) hstart
  have hratio' :
      doubleBlankW n g ^ start / doubleBlankW n g ^ hi ≤
        ENNReal.ofReal
          (Real.exp
            (((hi : ℝ) - (start : ℝ)) *
              Real.log ((2 * (n : ℝ) + (g : ℝ)) /
                (2 * (n : ℝ))))) := by
    simpa [doubleBlankW] using hratio
  have heta := doubleBlankEta_inv_pow_le_exp' n g H hn
  have hw0 : doubleBlankW n g ≠ 0 := by
    unfold doubleBlankW
    exact ne_of_gt (ENNReal.div_pos
      (by simp only [ne_eq, Nat.cast_eq_zero]; omega)
      (ENNReal.natCast_ne_top _))
  have hwt : doubleBlankW n g ≠ ⊤ := by
    unfold doubleBlankW
    finiteness
  have hsplit :
      doubleBlankW n g ^ start /
          (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) =
        (doubleBlankW n g ^ start / doubleBlankW n g ^ hi) *
          (1 / doubleBlankEta n g ^ H) := by
    simpa using
      (ENNReal.mul_div_mul_comm
        (a := doubleBlankW n g ^ start) (b := 1)
        (c := doubleBlankW n g ^ hi) (d := doubleBlankEta n g ^ H)
        (Or.inl (pow_ne_zero _ hw0))
        (Or.inl (ENNReal.pow_ne_top hwt)))
  rw [hsplit]
  calc
    (doubleBlankW n g ^ start / doubleBlankW n g ^ hi) *
          (1 / doubleBlankEta n g ^ H)
        ≤ ENNReal.ofReal
              (Real.exp
                (((hi : ℝ) - (start : ℝ)) *
                  Real.log ((2 * (n : ℝ) + (g : ℝ)) /
                    (2 * (n : ℝ))))) *
            ENNReal.ofReal
              (Real.exp
                (-((H : ℝ) * (g : ℝ) ^ 2 /
                  (2 * (2 * (n : ℝ) + (g : ℝ)) ^ 2 +
                    (g : ℝ) ^ 2)))) :=
      mul_le_mul hratio' heta bot_le bot_le
    _ = ENNReal.ofReal
          (Real.exp
            (((hi : ℝ) - (start : ℝ)) *
                Real.log ((2 * (n : ℝ) + (g : ℝ)) /
                  (2 * (n : ℝ))) -
              (H : ℝ) * (g : ℝ) ^ 2 /
                (2 * (2 * (n : ℝ) + (g : ℝ)) ^ 2 +
                  (g : ℝ) ^ 2))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 3

/-- With at least `32n` blank-exposure budget and band width at most `g`, the
blank-clock exponent is at most `-g²/n`. -/
theorem doubleBlankClockExponent_le
    (n g start hi H : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : start ≤ hi) (hwidth : hi ≤ start + g)
    (hH : 32 * n ≤ H) :
    ((hi : ℝ) - (start : ℝ)) *
          Real.log ((2 * (n : ℝ) + (g : ℝ)) / (2 * (n : ℝ))) -
        (H : ℝ) * (g : ℝ) ^ 2 /
          (2 * (2 * (n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2)
      ≤ -((g : ℝ) ^ 2 / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgR : (g : ℝ) ≤ n := by exact_mod_cast hg
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hden : 0 < (2 : ℝ) * n := by positivity
  have hratio :
      (0 : ℝ) < (2 * n + g) / (2 * n) := by positivity
  have hlog :=
    Real.log_le_sub_one_of_pos hratio
  have hratioSub :
      (2 * (n : ℝ) + (g : ℝ)) / (2 * (n : ℝ)) - 1 =
        (g : ℝ) / (2 * (n : ℝ)) := by
    field_simp
    ring
  rw [hratioSub] at hlog
  have hratioOne :
      (1 : ℝ) ≤ (2 * n + g) / (2 * n) := by
    apply (le_div_iff₀ hden).2
    linarith
  have hlog0 :
      0 ≤ Real.log ((2 * n + g) / (2 * n)) :=
    Real.log_nonneg hratioOne
  have hwidthNat : hi - start ≤ g := by omega
  have hwidthR : (hi : ℝ) - (start : ℝ) ≤ g := by
    rw [← Nat.cast_sub hstart]
    exact_mod_cast hwidthNat
  have hwidth0 : (0 : ℝ) ≤ (hi : ℝ) - (start : ℝ) := by
    have hstartR : (start : ℝ) ≤ hi := by exact_mod_cast hstart
    linarith
  have hA :
      ((hi : ℝ) - (start : ℝ)) *
          Real.log ((2 * n + g) / (2 * n)) ≤
        (g : ℝ) ^ 2 / (2 * n) := by
    calc
      ((hi : ℝ) - (start : ℝ)) *
            Real.log ((2 * n + g) / (2 * n))
          ≤ g * Real.log ((2 * n + g) / (2 * n)) :=
        mul_le_mul_of_nonneg_right hwidthR hlog0
      _ ≤ g * (g / (2 * n)) :=
        mul_le_mul_of_nonneg_left hlog hg0
      _ = g ^ 2 / (2 * n) := by ring
  let D : ℝ :=
    2 * (2 * (n : ℝ) + (g : ℝ)) ^ 2 + (g : ℝ) ^ 2
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hsquareG :
      0 ≤ ((n : ℝ) - (g : ℝ)) * ((n : ℝ) + (g : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hgR) (by positivity)
  have hthree :
      2 * (n : ℝ) + (g : ℝ) ≤ 3 * (n : ℝ) := by linarith
  have hsquareD :
      0 ≤ (3 * (n : ℝ) - (2 * (n : ℝ) + (g : ℝ))) *
        (3 * (n : ℝ) + (2 * (n : ℝ) + (g : ℝ))) :=
    mul_nonneg (sub_nonneg.mpr hthree) (by positivity)
  have hDupper : D ≤ 19 * n ^ 2 := by
    dsimp [D]
    nlinarith
  have hHR : (32 : ℝ) * n ≤ H := by exact_mod_cast hH
  have hcross : 3 * D ≤ 2 * n * H := by
    nlinarith [mul_pos hnR hnR]
  have hB :
      3 * (g : ℝ) ^ 2 / (2 * n) ≤
        (H : ℝ) * (g : ℝ) ^ 2 / D := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hnR) hDpos).2
    have hscaled := mul_le_mul_of_nonneg_right hcross (sq_nonneg (g : ℝ))
    nlinarith
  have hgap :
      3 * (g : ℝ) ^ 2 / (2 * n) -
          (g : ℝ) ^ 2 / (2 * n) =
        (g : ℝ) ^ 2 / n := by
    field_simp
    ring
  dsimp [D] at hB
  linarith

/-- Gaussian-scale bound for the blank-clock error under the concrete early
band budget. -/
theorem doubleBlankClockError_le_exp_neg
    (n g start hi H : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : start ≤ hi) (hwidth : hi ≤ start + g)
    (hH : 32 * n ≤ H) :
    doubleBlankW n g ^ start /
        (doubleBlankW n g ^ hi * doubleBlankEta n g ^ H) ≤
      ENNReal.ofReal
        (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ))) ) := by
  refine le_trans
    (doubleBlankClockError_le_exp n g start hi H hn hstart) ?_
  exact ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr
      (doubleBlankClockExponent_le
        n g start hi H hn hg hstart hwidth hH))

/-- A uniform envelope for the two occupation-clock errors of one rung. -/
noncomputable def doubleJointClockEnvelope
    (n g M : ℕ) : ℝ≥0∞ :=
  ((3 : ℝ≥0∞) / 4) ^ doubleClockBudget n M +
    ENNReal.ofReal (Real.exp (-((g : ℝ) ^ 2 / (n : ℝ))))

/-- At the concrete half-horizon, the two occupation-clock errors are bounded
by a geometric normal term plus a Gaussian-scale blank term. -/
theorem doubleJointClockError_le
    (n g start hi M : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : start ≤ hi) (hwidth : hi ≤ start + g) :
    1 / (((32 : ℝ≥0∞) / 31) ^ doubleClockHalfHorizon n M *
          (1 / 2) ^ (n + 2 * M)) +
        doubleBlankW n g ^ start /
          (doubleBlankW n g ^ hi *
            doubleBlankEta n g ^ doubleClockHalfHorizon n M) ≤
      doubleJointClockEnvelope n g M := by
  unfold doubleJointClockEnvelope
  apply add_le_add
  · simpa [doubleClockHalfHorizon, doubleClockBudget] using
      doubleNormalClockError_le (doubleClockBudget n M)
  · apply doubleBlankClockError_le_exp_neg
      n g start hi (doubleClockHalfHorizon n M)
      hn hg hstart hwidth
    simp [doubleClockHalfHorizon, doubleClockBudget]

/-- The concrete-rung error after replacing its two exact clock terms by the
uniform joint-clock envelope. -/
noncomputable def doubleBandJointRungClockedError
    (n g aLo bHiR bHiD hi k M
      returnLo bHiRet kRet : ℕ) : ℝ≥0∞ :=
  let u : ℝ≥0∞ := (bHiD : ℝ≥0∞) / (aLo : ℝ≥0∞)
  let w : ℝ≥0∞ := phase1RungBase aLo bHiD
  let η : ℝ≥0∞ := doubleDirectionEta u w
  ((((bHiR : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
      w ^ (aLo + k) / (w ^ (hi - 1) * η ^ M) +
      doubleJointClockEnvelope n g M) +
    ((bHiRet : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ kRet)

/-- The exact concrete-rung error is below its uniform clock envelope. -/
theorem doubleBandJointRungError_le_clocked
    (n g aLo bHiR bHiD hi k M
      returnLo bHiRet kRet : ℕ)
    (hn : 0 < n) (hg : g ≤ n)
    (hstart : aLo + k ≤ hi) (hwidth : hi ≤ aLo + k + g) :
    doubleBandJointRungError
        n g aLo bHiR bHiD hi k M (doubleClockHalfHorizon n M)
          returnLo bHiRet kRet ≤
      doubleBandJointRungClockedError
        n g aLo bHiR bHiD hi k M returnLo bHiRet kRet := by
  unfold doubleBandJointRungError doubleBandJointRungClockedError
  exact add_le_add
    (add_le_add le_rfl
      (doubleJointClockError_le
        n g (aLo + k) hi M hn hg hstart hwidth))
    le_rfl

/-- One Double-B rung with the raw horizon and both occupation-clock budgets
fixed explicitly. -/
theorem doubleBandJointRung_clocked
    (n : ℕ) (hn : 2 ≤ n)
    (g aLo bHiR bHiD hi k M : ℕ)
    (hnLo : n + g ≤ aLo)
    (hsmall : 8 * hi ≤ 9 * n)
    (haLohi : aLo < hi)
    (hpopR : aLo + bHiR + 2 = 2 * n)
    (haLo : 0 < aLo) (hbHiR : 0 < bHiR)
    (hmajR : bHiR ≤ aLo)
    (heqD : aLo + bHiD = 2 * n)
    (hbiasD : bHiD < aLo)
    (hhi : hi ≤ 2 * n)
    (hstart : aLo + k ≤ hi) (hwidth : hi ≤ aLo + k + g)
    (hg : g ≤ n)
    (returnLo bHiRet kRet : ℕ)
    (hpopRet : returnLo + bHiRet + 2 = 2 * n)
    (hreturnLo : 0 < returnLo) (hbHiRet : 0 < bHiRet)
    (hmajRet : bHiRet ≤ returnLo)
    (hlowerTarget : aLo < returnLo + 1)
    (htargetHi : returnLo + 1 ≤ hi)
    (hreturnGap : returnLo + kRet ≤ hi) :
    Reaches (doubleStateStep n hn) (doubleClockHorizon n M)
      (fun s => aLo + k ≤ s.1.doubleLevel)
      (fun s => returnLo + 1 ≤ s.1.doubleLevel)
      (doubleBandJointRungClockedError
        n g aLo bHiR bHiD hi k M returnLo bHiRet kRet) := by
  have hr :=
    doubleBandJointRung
      n hn g aLo bHiR bHiD hi k M
      (doubleClockHorizon n M) (doubleClockHalfHorizon n M)
      hnLo hsmall (two_doubleClockHalfHorizon n M).le
      haLohi hpopR haLo hbHiR hmajR heqD hbiasD hhi
      returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
      hlowerTarget htargetHi hreturnGap
  exact hr.mono_error
    (doubleBandJointRungError_le_clocked
      n g aLo bHiR bHiD hi k M returnLo bHiRet kRet
      (by omega) hg hstart hwidth)

end Tri

#print axioms Tri.doubleNormalClockError_le
#print axioms Tri.doubleBlankEta_inv_pow_le_exp
#print axioms Tri.doubleBlankClockError_le_exp
#print axioms Tri.doubleBlankClockError_le_exp_neg
#print axioms Tri.doubleJointClockError_le
#print axioms Tri.doubleBandJointRung_clocked
