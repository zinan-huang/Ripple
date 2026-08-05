/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RatioExp
import Tri.Phase1PhiRate
import Tri.Phase1Corrected
import Tri.Reconciled

/-!
# Buffered phase-1 assembly

This module gives moving phase-1 rungs room to return above their public
checkpoint while keeping the stopped band near `7n/8`.  It then
chains precisely the moving prefix of the dyadic ladder and supplies the
conditional end-to-end theorem against a quantitative contraction-rate
interface.
-/

namespace Tri

open scoped BigOperators ENNReal

set_option exponentiation.threshold 500

/-- The upper return buffer, separated from the lower Feller exponent and
capped before the near-consensus region. -/
def phase1CorrUpperBuffer (n γ j : ℕ) : ℕ :=
  min (phase1FellerK n γ j) (n / 24)

/-- The stopped-band upper boundary using the capped return buffer. -/
def phase1CorrUpper (n γ j : ℕ) : ℕ :=
  phase1CheckpointR n γ (j + 1) + phase1CorrUpperBuffer n γ j

/-- The quantitative phase-1 contraction interface.  Its contraction gap is
paired with the moving-rung lower bound needed by the assembly. -/
structure Phase1PhiRateHyp (n : ℕ) : Prop where
  progress : ∀ (lower bLo upper start T : ℕ) (E : ℝ),
      3 ≤ n → lower + bLo + 2 = n → 0 < lower → bLo < lower →
      upper ≤ n → lower ≤ start → start ≤ upper →
      E ≤ phase1PhiGap n lower bLo upper * (T : ℝ) -
          ((upper : ℝ) - (start : ℝ)) *
            Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)) →
      phase1RungPhi n lower bLo upper ^ T *
            phase1RungBase lower bLo ^ start /
            phase1RungBase lower bLo ^ upper ≤
        ENNReal.ofReal (Real.exp (-E))
  gap_lower : ∀ (γ j : ℕ), 2 ^ 420 ≤ n → 1 ≤ γ →
      6 * γ * Nat.log 2 n ≤ n →
      phase1CheckpointR n γ j < phase1CheckpointR n γ (j + 1) →
      ((phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ)) +
          ((phase1CorrUpper n γ j : ℝ) -
            (phase1CheckpointR n γ j : ℝ)) *
            Real.log ((2 * phase1LowerR n γ j : ℝ) /
              (phase1LowerR n γ j + phase1LowerMinorityR n γ j : ℝ))) /
        (24 * (n : ℝ)) ≤
        phase1PhiGap n (phase1LowerR n γ j)
          (phase1LowerMinorityR n γ j) (phase1CorrUpper n γ j)

/-- Adding `log 2` to an exponential budget contributes exactly a factor of
one half after transport to `ENNReal`. -/
theorem ofReal_exp_neg_add_log_two (E : ℝ) :
    ENNReal.ofReal (Real.exp (-(E + Real.log 2))) =
      (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-E)) := by
  have hexp : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [show -(E + Real.log 2) = -E + -Real.log 2 by ring, Real.exp_add,
    hexp, ENNReal.ofReal_mul (Real.exp_pos (-E)).le]
  norm_num [ENNReal.ofReal_div_of_pos, mul_comm]

/-- A floor-quarter drift buffer pays half of the Gaussian rung envelope.
The spare `log 2` is absorbed by the large-gap hypothesis. -/
theorem phase1_ratio_half_envelope
    (n gap lower bLo k : ℕ) (hn : 0 < n)
    (hgapSq : 420 * n ≤ gap ^ 2) (hkLower : 4 * k ≤ gap)
    (hkUpper : gap < 4 * k + 4) (hbLo : 0 < bLo)
    (hlowerN : lower ≤ n) (hdiff : bLo + 2 * k ≤ lower) :
    ((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ k ≤
      (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((gap : ℝ) ^ 2 / (48 * (n : ℝ))))) := by
  have hgap20 : 20 ≤ gap := by
    by_contra h
    have hgapSmall : gap ≤ 19 := by omega
    have hnOne : 1 ≤ n := hn
    nlinarith [Nat.pow_le_pow_left hgapSmall 2]
  have hkFour : 4 ≤ k := by omega
  have hgapK : gap ≤ 5 * k := by omega
  have hgapKsq : gap ^ 2 ≤ 25 * k ^ 2 := by nlinarith
  have hbudgetNat : gap ^ 2 + 48 * n ≤ 96 * k ^ 2 := by
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbudgetR : (gap : ℝ) ^ 2 + 48 * (n : ℝ) ≤
      96 * (k : ℝ) ^ 2 := by
    exact_mod_cast hbudgetNat
  have hlog : Real.log 2 ≤ (1 : ℝ) :=
    (Real.log_two_lt_d9.le).trans (by norm_num)
  have hElog : (gap : ℝ) ^ 2 / (48 * (n : ℝ)) + Real.log 2 ≤
      2 * (k : ℝ) ^ 2 / (n : ℝ) := by
    calc
      (gap : ℝ) ^ 2 / (48 * (n : ℝ)) + Real.log 2 ≤
          (gap : ℝ) ^ 2 / (48 * (n : ℝ)) + 1 := by linarith
      _ ≤ 2 * (k : ℝ) ^ 2 / (n : ℝ) := by
        field_simp [hnR.ne']
        nlinarith
  have hbLower : bLo ≤ lower := by omega
  have hlowerPos : 0 < lower := lt_of_lt_of_le hbLo hbLower
  have hlowerR : (0 : ℝ) < lower := by exact_mod_cast hlowerPos
  have hlowerNR : (lower : ℝ) ≤ n := by exact_mod_cast hlowerN
  have hdiffR : (2 : ℝ) * (k : ℝ) ≤
      (lower : ℝ) - (bLo : ℝ) := by
    have hcast : (bLo : ℝ) + 2 * (k : ℝ) ≤ lower := by
      exact_mod_cast hdiff
    linarith
  have hdrift : 2 * (k : ℝ) ^ 2 / (n : ℝ) ≤
      (k : ℝ) * ((lower : ℝ) - (bLo : ℝ)) /
        (lower : ℝ) := by
    rw [div_le_div_iff₀ hnR hlowerR]
    have hkR : (0 : ℝ) ≤ k := by positivity
    have hleft := mul_le_mul_of_nonneg_left hlowerNR
      (show (0 : ℝ) ≤ 2 * (k : ℝ) ^ 2 by positivity)
    have hright := mul_le_mul_of_nonneg_left hdiffR hkR
    nlinarith
  have hratio := ratio_pow_le_ofReal_exp lower bLo k
    ((gap : ℝ) ^ 2 / (48 * (n : ℝ)) + Real.log 2) hbLo hbLower
    (hElog.trans hdrift)
  rw [ofReal_exp_neg_add_log_two] at hratio
  exact hratio

/-- A capped return buffer pays half of the Gaussian rung envelope whenever
its exponent-times-drift budget dominates the Gaussian budget and `log 2`. -/
theorem phase1_return_half_envelope
    (n gap lower bLo r k : ℕ) (hn : 0 < n)
    (hbudget : gap ^ 2 + 48 * n ≤ 96 * r * k)
    (hbLo : 0 < bLo) (hlowerN : lower ≤ n)
    (hdiff : bLo + 2 * k ≤ lower) :
    ((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ r ≤
      (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((gap : ℝ) ^ 2 / (48 * (n : ℝ))))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbudgetR : (gap : ℝ) ^ 2 + 48 * (n : ℝ) ≤
      96 * (r : ℝ) * (k : ℝ) := by
    exact_mod_cast hbudget
  have hlog : Real.log 2 ≤ (1 : ℝ) :=
    (Real.log_two_lt_d9.le).trans (by norm_num)
  have hElog : (gap : ℝ) ^ 2 / (48 * (n : ℝ)) + Real.log 2 ≤
      2 * (r : ℝ) * (k : ℝ) / (n : ℝ) := by
    calc
      (gap : ℝ) ^ 2 / (48 * (n : ℝ)) + Real.log 2 ≤
          (gap : ℝ) ^ 2 / (48 * (n : ℝ)) + 1 := by linarith
      _ ≤ 2 * (r : ℝ) * (k : ℝ) / (n : ℝ) := by
        field_simp [hnR.ne']
        nlinarith
  have hbLower : bLo ≤ lower := by omega
  have hlowerPos : 0 < lower := lt_of_lt_of_le hbLo hbLower
  have hlowerR : (0 : ℝ) < lower := by exact_mod_cast hlowerPos
  have hlowerNR : (lower : ℝ) ≤ n := by exact_mod_cast hlowerN
  have hdiffR : (2 : ℝ) * (k : ℝ) ≤
      (lower : ℝ) - (bLo : ℝ) := by
    have hcast : (bLo : ℝ) + 2 * (k : ℝ) ≤ lower := by
      exact_mod_cast hdiff
    linarith
  have hdrift : 2 * (r : ℝ) * (k : ℝ) / (n : ℝ) ≤
      (r : ℝ) * ((lower : ℝ) - (bLo : ℝ)) /
        (lower : ℝ) := by
    rw [div_le_div_iff₀ hnR hlowerR]
    have hrR : (0 : ℝ) ≤ r := by positivity
    have hleft := mul_le_mul_of_nonneg_left hlowerNR
      (show (0 : ℝ) ≤ 2 * (r : ℝ) * (k : ℝ) by positivity)
    have hright := mul_le_mul_of_nonneg_left hdiffR hrR
    nlinarith
  have hratio := ratio_pow_le_ofReal_exp lower bLo r
    ((gap : ℝ) ^ 2 / (48 * (n : ℝ)) + Real.log 2) hbLo hbLower
    (hElog.trans hdrift)
  rw [ofReal_exp_neg_add_log_two] at hratio
  exact hratio

/-- An abstract rate lower bound pays the quadratic Gaussian budget together
with the band's potential-growth penalty. -/
theorem phase1_phi_deadline_quadratic
    (n lower bLo start upper T gap : ℕ) (hn : 0 < n)
    (hlower : 0 < lower) (hbias : bLo < lower) (hstart : start ≤ upper)
    (hT : 24 * n ≤ T)
    (hgaplb : (((gap : ℝ) ^ 2 / (48 * (n : ℝ)) +
        ((upper : ℝ) - (start : ℝ)) *
          Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ))) /
      (24 * (n : ℝ)) ≤ phase1PhiGap n lower bLo upper)) :
    (gap : ℝ) ^ 2 / (48 * (n : ℝ)) ≤
      phase1PhiGap n lower bLo upper * (T : ℝ) -
        ((upper : ℝ) - (start : ℝ)) *
          Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlowerR : (0 : ℝ) < lower := by exact_mod_cast hlower
  have hsumR : (0 : ℝ) < (lower : ℝ) + (bLo : ℝ) := by positivity
  have hbiasR : (bLo : ℝ) ≤ lower := by exact_mod_cast hbias.le
  have hratioOne : (1 : ℝ) ≤
      (2 * (lower : ℝ)) / ((lower : ℝ) + (bLo : ℝ)) := by
    rw [le_div_iff₀ hsumR]
    linarith
  have hlogNonneg : 0 ≤
      Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)) :=
    Real.log_nonneg hratioOne
  have hdistanceNonneg : 0 ≤ (upper : ℝ) - (start : ℝ) := by
    have hcast : (start : ℝ) ≤ upper := by exact_mod_cast hstart
    linarith
  have hbudgetNonneg : 0 ≤
      (gap : ℝ) ^ 2 / (48 * (n : ℝ)) +
        ((upper : ℝ) - (start : ℝ)) *
          Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)) := by
    positivity
  have hrateNonneg : 0 ≤
      ((gap : ℝ) ^ 2 / (48 * (n : ℝ)) +
        ((upper : ℝ) - (start : ℝ)) *
          Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ))) /
        (24 * (n : ℝ)) := div_nonneg hbudgetNonneg (by positivity)
  have hTReal : (24 : ℝ) * (n : ℝ) ≤ T := by exact_mod_cast hT
  have htime := mul_le_mul_of_nonneg_left hTReal hrateNonneg
  have hgapTime := mul_le_mul_of_nonneg_right hgaplb
    (show (0 : ℝ) ≤ T by positivity)
  have hcancel :
      ((gap : ℝ) ^ 2 / (48 * (n : ℝ)) +
        ((upper : ℝ) - (start : ℝ)) *
          Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ))) /
          (24 * (n : ℝ)) * (24 * (n : ℝ)) =
        (gap : ℝ) ^ 2 / (48 * (n : ℝ)) +
          ((upper : ℝ) - (start : ℝ)) *
            Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)) := by
    field_simp
  rw [hcancel] at htime
  linarith

/-- Arithmetic certificate for one genuinely moving corrected phase-1 rung. -/
structure Phase1CorrRungData
    (n gap k r current next lower bLo upper returnLo bReturn : ℕ) : Prop where
  h3 : 3 ≤ n
  hnPos : 0 < n
  hgapSq : 420 * n ≤ gap ^ 2
  hkLower : 4 * k ≤ gap
  hkUpper : gap < 4 * k + 4
  hkPos : 0 < k
  hgapK : gap ≤ 5 * k
  hrLeK : r ≤ k
  hreturnBudget : gap ^ 2 + 48 * n ≤ 96 * r * k
  hstart : lower + k = current
  hpopLower : lower + bLo + 2 = n
  hlowerPos : 0 < lower
  hbLoPos : 0 < bLo
  hbias : bLo < lower
  hlowerN : lower ≤ n
  hlowerSix : 6 * lower < 5 * n
  hlowerDiffLo : bLo + 2 * k ≤ lower
  hlowerDiffHi : 10 * lower ≤ 10 * bLo + 21 * k
  hdenom : 99 * n ≤ 100 * (lower + bLo)
  hadvance : current ≤ next
  hupperEq : upper = next + r
  hnextUpper : next ≤ upper
  hupperN : upper ≤ n
  hupperSeven : 8 * upper ≤ 7 * n + 8
  hupperDist : 10 * upper ≤ 10 * current + 31 * k
  hpopReturn : returnLo + bReturn + 2 = n
  hreturnLoPos : 0 < returnLo
  hbReturnPos : 0 < bReturn
  hreturnMaj : bReturn ≤ returnLo
  hreturnNext : returnLo + 1 = next
  hreturnGap : returnLo + r ≤ upper
  hreturnN : returnLo ≤ n
  hreturnDiff : bReturn + 2 * k ≤ returnLo

/-- Complement arithmetic at a buffered return boundary, isolated from the
larger dyadic-geometry context. -/
theorem phase1_return_buffer_arithmetic
    (n γ j k : ℕ) (hstrict : phase1ReturnLoR n γ j + 2 < n)
    (hmid : n ≤ 2 * phase1ReturnLoR n γ j)
    (hdrift : n + 2 * k ≤ 2 * phase1ReturnLoR n γ j + 2) :
    phase1ReturnLoR n γ j + phase1ReturnMinorityR n γ j + 2 = n ∧
      0 < phase1ReturnMinorityR n γ j ∧
      phase1ReturnMinorityR n γ j ≤ phase1ReturnLoR n γ j ∧
      phase1ReturnMinorityR n γ j + 2 * k ≤ phase1ReturnLoR n γ j := by
  unfold phase1ReturnMinorityR
  omega

set_option maxHeartbeats 200000 in
-- The dyadic floor and cap certificate requires a large Presburger context.
/-- The dyadic checkpoint geometry supplies the full arithmetic certificate
for every moving rung. -/
theorem phase1_corr_rung_data
    (n γ j : ℕ) (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (hmove : phase1CheckpointR n γ j < phase1CheckpointR n γ (j + 1)) :
    Phase1CorrRungData n (phase1GapR n γ j) (phase1FellerK n γ j)
      (phase1CorrUpperBuffer n γ j)
      (phase1CheckpointR n γ j) (phase1CheckpointR n γ (j + 1))
      (phase1LowerR n γ j) (phase1LowerMinorityR n γ j)
      (phase1CorrUpper n γ j) (phase1ReturnLoR n γ j)
      (phase1ReturnMinorityR n γ j) := by
  have h3 : 3 ≤ n := by
    exact hn.trans' (le_trans (by norm_num : 3 ≤ 2 ^ 2)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 2 ≤ 420)))
  have hnPos : 0 < n := by omega
  have hn12 : 12 ≤ n := phase1_size_ge_twelve h3 hγ hsize
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
  have hgapSq : 420 * n ≤ phase1GapR n γ j ^ 2 :=
    hrad.trans ((phase1SeedRadicand_le_sq n γ).trans
      (Nat.pow_le_pow_left hseedGap 2))
  have hn512 : 512 ≤ n := by
    exact hn.trans' (le_trans (by norm_num : 512 ≤ 2 ^ 9)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 9 ≤ 420)))
  have hgap400 : 400 ≤ phase1GapR n γ j := by
    by_contra h
    have hgapSmall : phase1GapR n γ j ≤ 399 := by omega
    have hsquare := Nat.pow_le_pow_left hgapSmall 2
    nlinarith
  have hkLower : 4 * phase1FellerK n γ j ≤ phase1GapR n γ j := by
    unfold phase1FellerK
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (phase1GapR n γ j) 4
  have hkUpper : phase1GapR n γ j <
      4 * phase1FellerK n γ j + 4 := by
    unfold phase1FellerK
    have hmod := Nat.mod_lt (phase1GapR n γ j) (by norm_num : 0 < 4)
    have hdecomp := Nat.mod_add_div (phase1GapR n γ j) 4
    omega
  have hkHundred : 100 ≤ phase1FellerK n γ j := by omega
  have hkPos : 0 < phase1FellerK n γ j := by omega
  have hgapK : phase1GapR n γ j ≤
      5 * phase1FellerK n γ j := by omega
  have hcurrentTarget :
      phase1CheckpointR n γ j < phase1Target n :=
    hmove.trans_le (min_le_left _ _)
  have hrawTarget :
      (n + phase1GapR n γ j + 1) / 2 < phase1Target n := by
    by_contra h
    have htargetRaw : phase1Target n ≤
        (n + phase1GapR n γ j + 1) / 2 := Nat.le_of_not_gt h
    have hcurrentEq : phase1CheckpointR n γ j = phase1Target n := by
      unfold phase1CheckpointR
      exact min_eq_left htargetRaw
    omega
  have hcurrentRaw : phase1CheckpointR n γ j =
      (n + phase1GapR n γ j + 1) / 2 := by
    unfold phase1CheckpointR
    exact min_eq_right hrawTarget.le
  have hrawDecomp := Nat.div_add_mod
    (n + phase1GapR n γ j + 1) 2
  have hrawMod := Nat.mod_lt (n + phase1GapR n γ j + 1)
    (by norm_num : 0 < 2)
  have hcurrentLo : n + phase1GapR n γ j ≤
      2 * phase1CheckpointR n γ j := by
    rw [hcurrentRaw]
    omega
  have hcurrentHi : 2 * phase1CheckpointR n γ j ≤
      n + phase1GapR n γ j + 1 := by
    rw [hcurrentRaw]
    simpa [Nat.mul_comm] using
      Nat.div_mul_le_self (n + phase1GapR n γ j + 1) 2
  have htargetMul : 6 * phase1Target n ≤ 5 * n + 5 := by
    unfold phase1Target
    simpa [Nat.mul_comm] using Nat.mul_div_le (5 * n + 5) 6
  have hcurrentMul : 6 * phase1CheckpointR n γ j < 5 * n := by omega
  have hgapN : 3 * phase1GapR n γ j < 2 * n := by omega
  have hkN : 6 * phase1FellerK n γ j < n := by omega
  have htargetK : phase1Target n + phase1FellerK n γ j ≤ n := by
    unfold phase1Target
    omega
  have hnextTarget : phase1CheckpointR n γ (j + 1) ≤ phase1Target n :=
    min_le_left _ _
  have hnextK : phase1CheckpointR n γ (j + 1) +
      phase1FellerK n γ j ≤ n := by omega
  have hgapNext : phase1GapR n γ (j + 1) =
      2 * phase1GapR n γ j := by
    unfold phase1GapR
    rw [pow_succ]
    ring
  have hnextRaw : phase1CheckpointR n γ (j + 1) ≤
      (n + 2 * phase1GapR n γ j + 1) / 2 := by
    rw [← hgapNext]
    exact min_le_right _ _
  have hnextRawMul : 2 * phase1CheckpointR n γ (j + 1) ≤
      n + 2 * phase1GapR n γ j + 1 := by
    calc
      2 * phase1CheckpointR n γ (j + 1) ≤
          2 * ((n + 2 * phase1GapR n γ j + 1) / 2) :=
        Nat.mul_le_mul_left 2 hnextRaw
      _ = ((n + 2 * phase1GapR n γ j + 1) / 2) * 2 := by ring
      _ ≤ n + 2 * phase1GapR n γ j + 1 :=
        Nat.div_mul_le_self _ 2
  have hnextDist : phase1CheckpointR n γ (j + 1) ≤
      phase1CheckpointR n γ j + 2 * phase1FellerK n γ j + 2 := by
    omega
  have htargetTwo := phase1Target_add_two_le hn12
  have hcurrentK : phase1FellerK n γ j ≤
      phase1CheckpointR n γ j := by omega
  have hstart : phase1LowerR n γ j + phase1FellerK n γ j =
      phase1CheckpointR n γ j := by
    unfold phase1LowerR
    exact Nat.sub_add_cancel hcurrentK
  have hlowerTarget : phase1LowerR n γ j ≤ phase1Target n := by
    unfold phase1LowerR
    exact (Nat.sub_le _ _).trans (min_le_left _ _)
  have hlowerN : phase1LowerR n γ j ≤ n :=
    hlowerTarget.trans (by omega)
  have hlowerSix : 6 * phase1LowerR n γ j < 5 * n := by
    exact (Nat.mul_le_mul_left 6 (by unfold phase1LowerR; exact Nat.sub_le _ _)).trans_lt
      hcurrentMul
  have hlowerPos : 0 < phase1LowerR n γ j := by
    unfold phase1LowerR
    omega
  have hbLoPos : 0 < phase1LowerMinorityR n γ j := by
    unfold phase1LowerMinorityR phase1LowerR
    omega
  have hpopLower : phase1LowerR n γ j +
      phase1LowerMinorityR n γ j + 2 = n := by
    unfold phase1LowerMinorityR
    omega
  have hbias : phase1LowerMinorityR n γ j < phase1LowerR n γ j := by
    unfold phase1LowerMinorityR phase1LowerR
    omega
  have hlowerDiffLo : phase1LowerMinorityR n γ j +
      2 * phase1FellerK n γ j ≤ phase1LowerR n γ j := by
    unfold phase1LowerMinorityR phase1LowerR
    omega
  have hlowerDiffHi : 10 * phase1LowerR n γ j ≤
      10 * phase1LowerMinorityR n γ j +
        21 * phase1FellerK n γ j := by
    unfold phase1LowerMinorityR phase1LowerR
    omega
  have hdenom : 99 * n ≤ 100 *
      (phase1LowerR n γ j + phase1LowerMinorityR n γ j) := by
    omega
  have hnextPos : 0 < phase1CheckpointR n γ (j + 1) := by omega
  have hreturnNext : phase1ReturnLoR n γ j + 1 =
      phase1CheckpointR n γ (j + 1) := by
    unfold phase1ReturnLoR
    omega
  have hreturnCurrent : phase1CheckpointR n γ j ≤
      phase1ReturnLoR n γ j := by omega
  have hreturnLoPos : 0 < phase1ReturnLoR n γ j := by omega
  have hreturnTarget : phase1ReturnLoR n γ j < phase1Target n := by omega
  have hreturnN : phase1ReturnLoR n γ j ≤ n := by omega
  have hreturnStrict : phase1ReturnLoR n γ j + 2 < n :=
    (Nat.add_lt_add_right hreturnTarget 2).trans_le htargetTwo
  have hreturnMid : n ≤ 2 * phase1ReturnLoR n γ j := by
    calc
      n ≤ n + phase1GapR n γ j := Nat.le_add_right _ _
      _ ≤ 2 * phase1CheckpointR n γ j := hcurrentLo
      _ ≤ 2 * phase1ReturnLoR n γ j :=
        Nat.mul_le_mul_left 2 hreturnCurrent
  have htwoK : 2 * phase1FellerK n γ j ≤ phase1GapR n γ j := by
    calc
      2 * phase1FellerK n γ j ≤ 4 * phase1FellerK n γ j :=
        Nat.mul_le_mul_right _ (by norm_num : 2 ≤ 4)
      _ ≤ phase1GapR n γ j := hkLower
  have hreturnDrift : n + 2 * phase1FellerK n γ j ≤
      2 * phase1ReturnLoR n γ j + 2 := by
    calc
      n + 2 * phase1FellerK n γ j ≤ n + phase1GapR n γ j :=
        Nat.add_le_add_left htwoK n
      _ ≤ 2 * phase1CheckpointR n γ j := hcurrentLo
      _ ≤ 2 * phase1ReturnLoR n γ j :=
        Nat.mul_le_mul_left 2 hreturnCurrent
      _ ≤ 2 * phase1ReturnLoR n γ j + 2 := Nat.le_add_right _ _
  obtain ⟨hpopReturn, hbReturnPos, hreturnMaj, hreturnDiffK⟩ :=
    phase1_return_buffer_arithmetic n γ j (phase1FellerK n γ j)
      hreturnStrict hreturnMid hreturnDrift
  have hrLeK : phase1CorrUpperBuffer n γ j ≤
      phase1FellerK n γ j := min_le_left _ _
  have hrLeN : phase1CorrUpperBuffer n γ j ≤ n / 24 := min_le_right _ _
  have hupperEq : phase1CorrUpper n γ j =
      phase1CheckpointR n γ (j + 1) + phase1CorrUpperBuffer n γ j := rfl
  have hnextUpper : phase1CheckpointR n γ (j + 1) ≤
      phase1CorrUpper n γ j := by
    rw [hupperEq]
    exact Nat.le_add_right _ _
  have hupperRight : phase1CorrUpper n γ j ≤
      phase1CheckpointR n γ (j + 1) + phase1FellerK n γ j := by
    rw [hupperEq]
    exact Nat.add_le_add_left hrLeK _
  have hupperN : phase1CorrUpper n γ j ≤ n := hupperRight.trans hnextK
  have hbuffer24 : 24 * phase1CorrUpperBuffer n γ j ≤ n := by
    calc
      24 * phase1CorrUpperBuffer n γ j ≤ 24 * (n / 24) :=
        Nat.mul_le_mul_left 24 hrLeN
      _ ≤ n := by simpa [Nat.mul_comm] using Nat.div_mul_le_self n 24
  have htarget24 : 24 * phase1Target n ≤ 20 * n + 20 := by
    calc
      24 * phase1Target n = 4 * (6 * phase1Target n) := by ring
      _ ≤ 4 * (5 * n + 5) := Nat.mul_le_mul_left 4 htargetMul
      _ = 20 * n + 20 := by ring
  have hupper24 : 24 * phase1CorrUpper n γ j ≤ 21 * n + 20 := by
    rw [hupperEq]
    calc
      24 * (phase1CheckpointR n γ (j + 1) +
          phase1CorrUpperBuffer n γ j) =
          24 * phase1CheckpointR n γ (j + 1) +
            24 * phase1CorrUpperBuffer n γ j := by ring
      _ ≤ 24 * phase1Target n + n :=
        Nat.add_le_add (Nat.mul_le_mul_left 24 hnextTarget) hbuffer24
      _ ≤ (20 * n + 20) + n := Nat.add_le_add_right htarget24 n
      _ = 21 * n + 20 := by ring
  have hupperSeven : 8 * phase1CorrUpper n γ j ≤ 7 * n + 8 := by
    have hscaled : 3 * (8 * phase1CorrUpper n γ j) ≤
        3 * (7 * n + 8) := by
      calc
        3 * (8 * phase1CorrUpper n γ j) =
            24 * phase1CorrUpper n γ j := by ring
        _ ≤ 21 * n + 20 := hupper24
        _ ≤ 21 * n + 24 := Nat.add_le_add_left (by norm_num) _
        _ = 3 * (7 * n + 8) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled (by norm_num)
  have hupperDist : 10 * phase1CorrUpper n γ j ≤
      10 * phase1CheckpointR n γ j + 31 * phase1FellerK n γ j := by
    calc
      10 * phase1CorrUpper n γ j ≤
          10 * (phase1CheckpointR n γ (j + 1) +
            phase1FellerK n γ j) := Nat.mul_le_mul_left 10 hupperRight
      _ ≤ 10 * (phase1CheckpointR n γ j +
          2 * phase1FellerK n γ j + 2 + phase1FellerK n γ j) :=
        Nat.mul_le_mul_left 10
          (Nat.add_le_add_right hnextDist (phase1FellerK n γ j))
      _ ≤ 10 * phase1CheckpointR n γ j +
          31 * phase1FellerK n γ j := by omega
  have hreturnGap : phase1ReturnLoR n γ j + phase1CorrUpperBuffer n γ j ≤
      phase1CorrUpper n γ j := by
    rw [hupperEq]
    omega
  have hreturnBudget : phase1GapR n γ j ^ 2 + 48 * n ≤
      96 * phase1CorrUpperBuffer n γ j * phase1FellerK n γ j := by
    by_cases hsmall : phase1FellerK n γ j ≤ n / 24
    · rw [phase1CorrUpperBuffer, min_eq_left hsmall]
      have hgapSqUpper : phase1GapR n γ j ^ 2 ≤
          25 * phase1FellerK n γ j ^ 2 := by
        nlinarith only [hgapK]
      nlinarith only [hgapSq, hgapSqUpper]
    · have hcap : n / 24 < phase1FellerK n γ j := by omega
      rw [phase1CorrUpperBuffer, min_eq_right hcap.le]
      have hmod := Nat.mod_lt n (by norm_num : 0 < 24)
      have hdecomp := Nat.mod_add_div n 24
      have hnFloor : n < 24 * (n / 24) + 24 := by omega
      have hgapSqUpper : phase1GapR n γ j ^ 2 ≤
          (4 * phase1FellerK n γ j + 3) ^ 2 := by
        nlinarith only [hkUpper]
      nlinarith only [hn512, hkN, hcap, hnFloor, hgapSqUpper]
  exact
    { h3 := h3
      hnPos := hnPos
      hgapSq := hgapSq
      hkLower := hkLower
      hkUpper := hkUpper
      hkPos := hkPos
      hgapK := hgapK
      hrLeK := hrLeK
      hreturnBudget := hreturnBudget
      hstart := hstart
      hpopLower := hpopLower
      hlowerPos := hlowerPos
      hbLoPos := hbLoPos
      hbias := hbias
      hlowerN := hlowerN
      hlowerSix := hlowerSix
      hlowerDiffLo := hlowerDiffLo
      hlowerDiffHi := hlowerDiffHi
      hdenom := hdenom
      hadvance := hmove.le
      hupperEq := hupperEq
      hnextUpper := hnextUpper
      hupperN := hupperN
      hupperSeven := hupperSeven
      hupperDist := hupperDist
      hpopReturn := hpopReturn
      hreturnLoPos := hreturnLoPos
      hbReturnPos := hbReturnPos
      hreturnMaj := hreturnMaj
      hreturnNext := hreturnNext
      hreturnGap := hreturnGap
      hreturnN := hreturnN
      hreturnDiff := hreturnDiffK }

/-- A moving corrected rung reaches its next public checkpoint with the
advertised dyadic Gaussian envelope. -/
theorem phase1_corrected_rung_bound
    (C₁ n γ j : ℕ) (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (hmove : phase1CheckpointR n γ j < phase1CheckpointR n γ (j + 1))
    (hphi : Phase1PhiRateHyp n) (hC₁ : 24 ≤ C₁) :
    Reaches (triChain n) (phase1HorizonR C₁ n γ j)
      (Phase1RefactoredCheckpoint n γ j)
      (Phase1RefactoredCheckpoint n γ (j + 1))
      (phase1RungEnvelopeR n γ j) := by
  let gap := phase1GapR n γ j
  let k := phase1FellerK n γ j
  let r := phase1CorrUpperBuffer n γ j
  let current := phase1CheckpointR n γ j
  let next := phase1CheckpointR n γ (j + 1)
  let lower := phase1LowerR n γ j
  let bLo := phase1LowerMinorityR n γ j
  let upper := phase1CorrUpper n γ j
  let returnLo := phase1ReturnLoR n γ j
  let bReturn := phase1ReturnMinorityR n γ j
  let T := phase1HorizonR C₁ n γ j
  let E : ℝ := (gap : ℝ) ^ 2 / (48 * (n : ℝ))
  have D : Phase1CorrRungData n gap k r current next lower bLo upper
      returnLo bReturn := by
    simpa only [gap, k, r, current, next, lower, bLo, upper, returnLo, bReturn]
      using phase1_corr_rung_data n γ j hn hγ hsize hmove
  have hT : 24 * n ≤ T := by
    dsimp [T, phase1HorizonR]
    calc
      24 * n ≤ C₁ * n := Nat.mul_le_mul_right n hC₁
      _ ≤ C₁ * γ * n := by
        apply Nat.mul_le_mul_right
        calc
          C₁ = C₁ * 1 := by simp
          _ ≤ C₁ * γ := Nat.mul_le_mul_left C₁ hγ
  have hcurrentUpper : current ≤ upper := D.hadvance.trans D.hnextUpper
  have hlowerCurrent : lower ≤ current := by
    have := D.hstart
    omega
  have hsafety : ((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ k ≤
      (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-E)) := by
    simpa only [E] using phase1_ratio_half_envelope n gap lower bLo k
      D.hnPos D.hgapSq D.hkLower D.hkUpper D.hbLoPos D.hlowerN
      D.hlowerDiffLo
  have hreturn : ((bReturn : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ r ≤
      (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-E)) := by
    simpa only [E] using phase1_return_half_envelope n gap returnLo bReturn r k
      D.hnPos D.hreturnBudget D.hbReturnPos D.hreturnN D.hreturnDiff
  have hgaplb : (E + ((upper : ℝ) - (current : ℝ)) *
        Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ))) /
      (24 * (n : ℝ)) ≤ phase1PhiGap n lower bLo upper := by
    simpa only [E, gap, current, lower, bLo, upper] using
      hphi.gap_lower γ j hn hγ hsize hmove
  have hdeadline : E ≤ phase1PhiGap n lower bLo upper * (T : ℝ) -
      ((upper : ℝ) - (current : ℝ)) *
        Real.log ((2 * lower : ℝ) / (lower + bLo : ℝ)) := by
    exact phase1_phi_deadline_quadratic n lower bLo current upper T gap
      D.hnPos D.hlowerPos D.hbias hcurrentUpper hT hgaplb
  have hprogress : phase1RungPhi n lower bLo upper ^ T *
        phase1RungBase lower bLo ^ current /
          phase1RungBase lower bLo ^ upper ≤
      ENNReal.ofReal (Real.exp (-E)) := by
    exact hphi.progress lower bLo upper current T E D.h3 D.hpopLower
      D.hlowerPos D.hbias D.hupperN hlowerCurrent hcurrentUpper hdeadline
  have hrung : Reaches (triChain n) T (fun z => current ≤ z)
      (fun z => next ≤ z)
      (phase1RungError n lower bLo current next upper k returnLo
        bReturn r T) := by
    exact phase1_staged_rung n lower bLo current next upper k returnLo
      bReturn r T D.h3 D.hpopLower D.hlowerPos D.hbLoPos D.hbias
      D.hstart D.hkPos D.hadvance D.hnextUpper D.hupperN D.hpopReturn
      D.hreturnLoPos D.hbReturnPos D.hreturnMaj D.hreturnNext D.hreturnGap
  have herror :
      phase1RungError n lower bLo current next upper k returnLo bReturn r T ≤
        phase1RungEnvelopeR n γ j := by
    rw [phase1RungEnvelopeR_eq_gap]
    change (((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ k +
        phase1RungPhi n lower bLo upper ^ T *
          phase1RungBase lower bLo ^ current /
            phase1RungBase lower bLo ^ upper) +
      ((bReturn : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ r ≤ _
    calc
      (((bLo : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ k +
          phase1RungPhi n lower bLo upper ^ T *
            phase1RungBase lower bLo ^ current /
              phase1RungBase lower bLo ^ upper) +
          ((bReturn : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ r ≤
          ((1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-E)) +
            ENNReal.ofReal (Real.exp (-E))) +
            (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-E)) :=
        add_le_add (add_le_add hsafety hprogress) hreturn
      _ = ENNReal.ofReal
          (2 * Real.exp (-((phase1GapR n γ j : ℝ) ^ 2 /
            (48 * (n : ℝ))))) := by
        have hEeq : E = (phase1GapR n γ j : ℝ) ^ 2 /
            (48 * (n : ℝ)) := rfl
        rw [hEeq]
        let A := ENNReal.ofReal
          (Real.exp (-((phase1GapR n γ j : ℝ) ^ 2 / (48 * (n : ℝ)))))
        calc
          ((1 / 2 : ℝ≥0∞) * A + A) + (1 / 2 : ℝ≥0∞) * A =
              ((1 / 2 : ℝ≥0∞) + 1 + 1 / 2) * A := by ring
          _ = 2 * A := by
            have hcoef : (1 / 2 : ℝ≥0∞) + 1 + 1 / 2 = 2 := by
              rw [add_assoc, show (1 : ℝ≥0∞) + 1 / 2 = 1 / 2 + 1 by ac_rfl,
                ← add_assoc, ENNReal.div_add_div_same]
              norm_num only [one_add_one_eq_two]
              rw [ENNReal.div_self] <;> norm_num
            rw [hcoef]
          _ = ENNReal.ofReal
              (2 * Real.exp (-((phase1GapR n γ j : ℝ) ^ 2 /
                (48 * (n : ℝ))))) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num [A]
  change Reaches (triChain n) T (fun z => current ≤ z)
    (fun z => next ≤ z) (phase1RungEnvelopeR n γ j)
  exact hrung.mono_error herror

/-- Before the target cap is active, a dyadic gap of at least two makes the
next corrected checkpoint strictly larger. -/
theorem phase1CheckpointR_strict_of_lt_target
    (n γ j : ℕ) (hgap : 2 ≤ phase1GapR n γ j)
    (hlt : phase1CheckpointR n γ j < phase1Target n) :
    phase1CheckpointR n γ j < phase1CheckpointR n γ (j + 1) := by
  have hrawTarget :
      (n + phase1GapR n γ j + 1) / 2 < phase1Target n := by
    by_contra h
    have htargetRaw : phase1Target n ≤
        (n + phase1GapR n γ j + 1) / 2 := Nat.le_of_not_gt h
    have hcurrent : phase1CheckpointR n γ j = phase1Target n := by
      unfold phase1CheckpointR
      exact min_eq_left htargetRaw
    omega
  have hgapNext : phase1GapR n γ (j + 1) =
      2 * phase1GapR n γ j := by
    unfold phase1GapR
    rw [pow_succ]
    ring
  have hrawMove : (n + phase1GapR n γ j + 1) / 2 <
      (n + phase1GapR n γ (j + 1) + 1) / 2 := by
    rw [hgapNext]
    omega
  rw [phase1CheckpointR, min_eq_right hrawTarget.le]
  apply lt_min hrawTarget
  exact hrawMove

/-- The least target-hitting checkpoint cuts off the dyadic ladder after its
moving prefix; an enlarged first block uses the entire prescribed horizon. -/
theorem phase1_reaches_corrected
    (C₁ n γ : ℕ) (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (hphi : Phase1PhiRateHyp n) (hC₁ : 24 ≤ C₁) :
    Reaches (triChain n) (phase1Horizon C₁ n γ)
      (AssemblyInitial n γ) (Phase1Exit n)
      (phase1RefactoredError C₁ n γ) := by
  classical
  have h3 : 3 ≤ n := by
    exact hn.trans' (le_trans (by norm_num : 3 ≤ 2 ^ 2)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 2 ≤ 420)))
  have hlog : 420 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hn
  have hfinal : phase1CheckpointR n γ (Nat.log 2 n) = phase1Target n :=
    phase1CheckpointR_final (by omega) hγ
  let targetHit : ∃ j, phase1CheckpointR n γ j = phase1Target n :=
    ⟨Nat.log 2 n, hfinal⟩
  let J := Nat.find targetHit
  have hJtarget : phase1CheckpointR n γ J = phase1Target n := by
    exact Nat.find_spec targetHit
  have hJle : J ≤ Nat.log 2 n := by
    exact Nat.find_min' targetHit hfinal
  have hzeroMove := phase1CheckpointR_zero_lt_one_of_size hn hγ hsize
  have hJpos : 0 < J := by
    by_contra h
    have hJzero : J = 0 := by omega
    rw [hJzero] at hJtarget
    have hnextTarget : phase1CheckpointR n γ 1 ≤ phase1Target n :=
      min_le_left _ _
    omega
  have hseedTwo : 2 ≤ phase1SeedR n γ :=
    phase1SeedR_ge_two (by omega) hγ
  have hmoving : ∀ i < J,
      phase1CheckpointR n γ i < phase1CheckpointR n γ (i + 1) := by
    intro i hi
    have hnot : phase1CheckpointR n γ i ≠ phase1Target n :=
      Nat.find_min targetHit hi
    have hle : phase1CheckpointR n γ i ≤ phase1Target n :=
      min_le_left _ _
    have hlt : phase1CheckpointR n γ i < phase1Target n := by omega
    have hgapTwo : 2 ≤ phase1GapR n γ i := by
      unfold phase1GapR
      calc
        2 = 1 * 2 := by norm_num
        _ ≤ 2 ^ i * phase1SeedR n γ :=
          Nat.mul_le_mul (one_le_pow₀ (by norm_num)) hseedTwo
    exact phase1CheckpointR_strict_of_lt_target n γ i hgapTwo hlt
  let rungCoeff : ℕ → ℕ := fun i =>
    if i = 0 then C₁ * (Nat.log 2 n - J + 1) else C₁
  let rungTime : ℕ → ℕ := fun i => phase1HorizonR (rungCoeff i) n γ i
  let rungError : ℕ → ℝ≥0∞ := fun i => phase1RungEnvelopeR n γ i
  let P : ℕ → ℕ → Prop := fun i => Phase1RefactoredCheckpoint n γ i
  have hcoeff : ∀ i < J, 24 ≤ rungCoeff i := by
    intro i hi
    by_cases hi0 : i = 0
    · change 24 ≤ if i = 0 then C₁ * (Nat.log 2 n - J + 1) else C₁
      rw [if_pos hi0]
      have hfactor : 1 ≤ Nat.log 2 n - J + 1 := by omega
      calc
        24 ≤ C₁ := hC₁
        _ = C₁ * 1 := by simp
        _ ≤ C₁ * (Nat.log 2 n - J + 1) := Nat.mul_le_mul_left C₁ hfactor
    · change 24 ≤ if i = 0 then C₁ * (Nat.log 2 n - J + 1) else C₁
      rw [if_neg hi0]
      exact hC₁
  have hrungs : ∀ i < J,
      Reaches (triChain n) (rungTime i) (P i) (P (i + 1))
        (rungError i) := by
    intro i hi
    exact phase1_corrected_rung_bound (rungCoeff i) n γ i hn hγ hsize
      (hmoving i hi) hphi (hcoeff i hi)
  have hchain := Reaches.chain
    (K := triChain n) (P := P) (T := rungTime) (ε := rungError) hrungs
  have hzeroMem : 0 ∈ Finset.range J := Finset.mem_range.mpr hJpos
  have hcoeffSum :
      (∑ i ∈ Finset.range J, rungCoeff i) = C₁ * Nat.log 2 n := by
    change (∑ i ∈ Finset.range J,
      if i = 0 then C₁ * (Nat.log 2 n - J + 1) else C₁) = _
    rw [Finset.sum_eq_add_sum_diff_singleton 0 (fun i =>
      if i = 0 then C₁ * (Nat.log 2 n - J + 1) else C₁) (by
      intro hzero
      exact (hzero hzeroMem).elim)]
    simp only [if_pos, Finset.sdiff_singleton_eq_erase]
    have hrest : (∑ i ∈ (Finset.range J).erase 0,
        if i = 0 then C₁ * (Nat.log 2 n - J + 1) else C₁) =
        (J - 1) * C₁ := by
      calc
        _ = ∑ _i ∈ (Finset.range J).erase 0, C₁ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [Finset.ne_of_mem_erase hi]
        _ = (J - 1) * C₁ := by simp [hJpos]
    rw [hrest]
    calc
      C₁ * (Nat.log 2 n - J + 1) + (J - 1) * C₁ =
          C₁ * ((Nat.log 2 n - J + 1) + (J - 1)) := by ring
      _ = C₁ * Nat.log 2 n := by
        congr 1
        omega
  have htimeSum : (∑ i ∈ Finset.range J, rungTime i) =
      phase1Horizon C₁ n γ := by
    calc
      (∑ i ∈ Finset.range J, rungTime i) =
          (∑ i ∈ Finset.range J, rungCoeff i) * γ * n := by
        simp only [rungTime, phase1HorizonR]
        rw [Finset.sum_mul, Finset.sum_mul]
      _ = phase1Horizon C₁ n γ := by
        rw [hcoeffSum]
        unfold phase1Horizon
        ring
  have herrorSum : (∑ i ∈ Finset.range J, rungError i) ≤
      phase1RefactoredError C₁ n γ := by
    unfold phase1RefactoredError rungError
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hJle)
  have hchain' : Reaches (triChain n) (phase1Horizon C₁ n γ)
      (P 0) (P J) (phase1RefactoredError C₁ n γ) := by
    rw [htimeSum] at hchain
    exact hchain.mono_error herrorSum
  have htarget : Reaches (triChain n) (phase1Horizon C₁ n γ)
      (P 0) (fun z => 5 * n ≤ 6 * z)
      (phase1RefactoredError C₁ n γ) :=
    hchain'.mono_post (by
      intro z hz
      change phase1CheckpointR n γ J ≤ z at hz
      rw [hJtarget] at hz
      exact (phase1Target_le_iff n z).1 hz)
  have hstart : Reaches (triChain n) (phase1Horizon C₁ n γ)
      (AssemblyInitial n γ) (fun z => 5 * n ≤ 6 * z)
      (phase1RefactoredError C₁ n γ) := by
    intro x hx
    exact htarget x (phase1CheckpointR_zero_le_initial hx)
  exact hstart.phase1Exit_of_upper h3 (fun x hx => hx.1)

/-- The reconciled headline follows conditionally from the quadratic
phase-1 contraction-rate interface. -/
theorem theorem1b_of_phi (hphi : ∀ n, Phase1PhiRateHyp n) :
    Theorem1b_statement := by
  have hn128 : ∀ n : ℕ, 2 ^ 420 ≤ n → 128 ≤ Nat.log 2 n := fun n hn =>
    Nat.le_log_of_pow_le (by norm_num)
      (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num : 128 ≤ 420)) hn)
  have hn96 : ∀ n : ℕ, 2 ^ 420 ≤ n → 96 ≤ n := fun n hn =>
    le_trans (le_trans (by norm_num : (96 : ℕ) ≤ 2 ^ 7)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 7 ≤ 420))) hn
  have hn₀3 : 3 ≤ 2 ^ 420 :=
    le_trans (by norm_num : (3 : ℕ) ≤ 2 ^ 2)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 2 ≤ 420))
  refine theorem1b_of_reconciled_scheduled 24 (2 ^ 420) (1 / 100)
    (fun n γ => ∑ i ∈ Finset.range (phase2StageCount n γ),
      phase2AdditiveRungError n (2 + i))
    canonicalPhase3Error (by norm_num) hn₀3 ?_ ?_ ?_ ?_
  · intro n γ hn hγ hsize
    exact phase1_reaches_corrected 24 n γ hn hγ hsize (hphi n) (by norm_num)
  · intro n γ hn hγ hsize
    exact phase2_reaches_additive n γ (by have := hn96 n hn; omega)
      (hn96 n hn) hγ hsize (hn128 n hn)
  · intro n γ hn hγ hsize
    obtain ⟨h3, _⟩ := theorem1bN₀_package hn hγ
    exact phase3_reaches_scaled_canonical n γ h3 hγ hsize
  · intro n γ hn hγ hsize
    obtain ⟨h3, h46, _, h8, ht1, ht2, ht3⟩ := theorem1bN₀_package hn hγ
    have hn1 : 1 ≤ n := by omega
    have h1 : phase1RefactoredError 24 n γ ≤
        4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 34 : ℝ) * (γ : ℝ)) :=
      phase1RefactoredError_le_of_log_ge_fortysix 24 n γ h46 hγ
    have h2 : (∑ i ∈ Finset.range (phase2StageCount n γ),
          phase2AdditiveRungError n (2 + i)) ≤
        6 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) :=
      phase2_additive_error_le n γ hγ (by have := hn96 n hn; omega)
        (hn96 n hn) hsize (hn128 n hn)
    have h3e : canonicalPhase3Error n γ ≤
        2 * (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) :=
      canonicalPhase3Error_le_two_inverse n γ h3 hγ hsize h8
    refine reconciled_budget n γ hn1 hγ _ _ _ h1 h2 h3e ?_ ?_ ?_
    · rw [show (1 / 34 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ) =
          (33 / 1700 : ℝ) * (γ : ℝ) by ring]
      exact_mod_cast ht1
    · rw [show (1 / 50 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ) =
          (1 / 100 : ℝ) * (γ : ℝ) by ring]
      exact_mod_cast ht2
    · rw [show (1 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ) =
          (99 / 100 : ℝ) * (γ : ℝ) by ring]
      exact_mod_cast ht3

end Tri

#print axioms Tri.ofReal_exp_neg_add_log_two
#print axioms Tri.phase1_ratio_half_envelope
#print axioms Tri.phase1_return_half_envelope
#print axioms Tri.phase1_phi_deadline_quadratic
#print axioms Tri.phase1_return_buffer_arithmetic
#print axioms Tri.phase1_corr_rung_data
#print axioms Tri.phase1_corrected_rung_bound
#print axioms Tri.phase1CheckpointR_strict_of_lt_target
#print axioms Tri.phase1_reaches_corrected
#print axioms Tri.theorem1b_of_phi
