-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseNineBitAlgebra.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneTimer

/-!
A reciprocal epidemic deficit.  The missing-bit count is divided by the
infected count; one infection step has enough drift at every population
scale, including the initial one-label seed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseNineBitAlgebra

open TimeTheorem

def reciprocalDeficit (n i : ℕ) : ℝ :=
  ((n : ℝ) - 1) * ((n : ℝ) - (i : ℝ)) / (i : ℝ)

def bitRiseRate (n i : ℕ) : ℝ :=
  2 * (i : ℝ) * ((n : ℝ) - (i : ℝ)) /
    ((n : ℝ) * ((n : ℝ) - 1))

theorem reciprocalDeficit_nonneg (n i : ℕ) (hn : 2 ≤ n) (hi : i ≤ n) :
    0 ≤ reciprocalDeficit n i := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiR : (i : ℝ) ≤ n := by exact_mod_cast hi
  unfold reciprocalDeficit
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (Nat.cast_nonneg i)

theorem reciprocalDeficit_zero (n : ℕ) : reciprocalDeficit n 0 = 0 := by
  simp [reciprocalDeficit]

theorem reciprocalDeficit_full (n : ℕ) : reciprocalDeficit n n = 0 := by
  simp [reciprocalDeficit]

theorem reciprocalDeficit_le_square (n i : ℕ) (hn : 2 ≤ n) (hi : i ≤ n) :
    reciprocalDeficit n i ≤ (n : ℝ) ^ 2 := by
  by_cases hz : i = 0
  · rw [hz, reciprocalDeficit_zero]
    exact sq_nonneg _
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hiR : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
    have hip : (0 : ℝ) < i := by linarith
    have hnpos : (0 : ℝ) ≤ n := by linarith
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hnum := mul_le_mul_of_nonneg_left
      (show (n : ℝ) - i ≤ n by linarith)
      (show 0 ≤ (n : ℝ) - 1 by linarith)
    have hden := mul_le_mul_of_nonneg_left hiR (sq_nonneg (n : ℝ))
    unfold reciprocalDeficit
    apply (div_le_iff₀ hip).2
    nlinarith only [hnum, hden, hnpos]

theorem reciprocalDeficit_one_le (n i : ℕ) (hn : 2 ≤ n)
    (hi : 1 ≤ i) (hilt : i < n) :
    1 ≤ reciprocalDeficit n i := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hgap : (i : ℝ) + 1 ≤ n := by exact_mod_cast (show i + 1 ≤ n by omega)
  have hmul := mul_nonneg
    (show 0 ≤ (n : ℝ) - 1 by linarith)
    (show 0 ≤ (n : ℝ) - i - 1 by linarith)
  unfold reciprocalDeficit
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < i)).2
  nlinarith only [hmul, hgap]

theorem reciprocalDeficit_antitone (n i j : ℕ) (hn : 2 ≤ n)
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n) :
    reciprocalDeficit n j ≤ reciprocalDeficit n i := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) * ((j : ℝ) - i) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  unfold reciprocalDeficit
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < j)
    (by linarith : (0 : ℝ) < i)).2
  nlinarith only [hprod]

theorem bitRiseRate_bounds (n i : ℕ) (hn : 2 ≤ n) (hi : i ≤ n) :
    0 ≤ bitRiseRate n i ∧ bitRiseRate n i ≤ 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiR : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hnpos : 0 < (n : ℝ) * ((n : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have hs := sq_nonneg ((n : ℝ) - 2 * (i : ℝ))
  have hm := mul_nonneg (show 0 ≤ (n : ℝ) by linarith)
    (show 0 ≤ (n : ℝ) - 2 by linarith)
  unfold bitRiseRate
  refine ⟨div_nonneg (mul_nonneg (by positivity) (by linarith)) hnpos.le, ?_⟩
  apply (div_le_one hnpos).2
  nlinarith only [hs, hm]

theorem reciprocalDeficit_difference (n i : ℕ) (hn : 2 ≤ n) (hi : 1 ≤ i) :
    reciprocalDeficit n i - reciprocalDeficit n (i + 1) =
      (n : ℝ) * ((n : ℝ) - 1) /
        ((i : ℝ) * ((i : ℝ) + 1)) := by
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hiz : (i : ℝ) ≠ 0 := by linarith
  have hisz : (i : ℝ) + 1 ≠ 0 := by linarith
  unfold reciprocalDeficit
  push_cast
  field_simp [hiz, hisz]
  <;> ring

theorem reciprocalDeficit_rate_drop (n i : ℕ) (hn : 2 ≤ n) (hi : 1 ≤ i) :
    bitRiseRate n i * (reciprocalDeficit n i - reciprocalDeficit n (i + 1)) =
      2 * ((n : ℝ) - i) / ((i : ℝ) + 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  rw [reciprocalDeficit_difference n i hn hi]
  unfold bitRiseRate
  have hnz : (n : ℝ) ≠ 0 := by linarith
  have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
  have hiz : (i : ℝ) ≠ 0 := by linarith
  have hisz : (i : ℝ) + 1 ≠ 0 := by linarith
  field_simp [hnz, hnm, hiz, hisz]
  <;> ring

theorem reciprocalDeficit_step (n i : ℕ) (hn : 2 ≤ n)
    (hi : 1 ≤ i) (hilt : i < n) :
    reciprocalDeficit n i -
        bitRiseRate n i * (reciprocalDeficit n i - reciprocalDeficit n (i + 1)) ≤
      (1 - 1 / (n : ℝ)) * reciprocalDeficit n i := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hiN : (i : ℝ) ≤ n := by exact_mod_cast hilt.le
  have hp : (0 : ℝ) < n := by linarith
  have hip : (0 : ℝ) < i := by linarith
  have hprod := mul_nonneg
    (show 0 ≤ (n : ℝ) + 1 by linarith)
    (show 0 ≤ (i : ℝ) - 1 by linarith)
  have hratio :
      ((n : ℝ) - 1) / ((n : ℝ) * i) ≤ 2 / ((i : ℝ) + 1) := by
    apply (div_le_div_iff₀ (mul_pos hp hip) (by linarith : (0 : ℝ) < i + 1)).2
    nlinarith only [hprod]
  have hscaled := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ (n : ℝ) - i by linarith)
  have he : (1 / (n : ℝ)) * reciprocalDeficit n i =
      (((n : ℝ) - 1) / ((n : ℝ) * i)) * ((n : ℝ) - i) := by
    unfold reciprocalDeficit
    field_simp [hp.ne', hip.ne']
    <;> ring
  rw [reciprocalDeficit_rate_drop n i hn hi]
  have hdrop : (1 / (n : ℝ)) * reciprocalDeficit n i ≤
      2 * ((n : ℝ) - i) / ((i : ℝ) + 1) := by
    rw [he]
    simpa only [div_mul_eq_mul_div] using hscaled
  nlinarith only [hdrop]

theorem reciprocal_tail_real (n : ℕ) (hn : 2 ≤ n) :
    (1 - 1 / (n : ℝ)) ^ logWindow n 12 * (n : ℝ) ^ 2 ≤
      1 / (n : ℝ) ^ 10 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) := by
    have hdiv : 1 / (n : ℝ) ≤ 1 := (div_le_one hp).2 (by linarith)
    linarith
  have hceil : (12 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
      (logWindow n 12 : ℝ) := Nat.le_ceil _
  have hquot : 12 * Real.log (n : ℝ) ≤ (logWindow n 12 : ℝ) / (n : ℝ) := by
    apply (le_div_iff₀ hp).2
    nlinarith only [hceil]
  have hdecay :
      (1 - 1 / (n : ℝ)) ^ logWindow n 12 ≤
        Real.exp (-(12 : ℝ) * Real.log (n : ℝ)) := by
    calc
      _ ≤ Real.exp (-(1 / (n : ℝ))) ^ logWindow n 12 :=
        pow_le_pow_left₀ hbase (by linarith [Real.add_one_le_exp (-(1 / (n : ℝ)))]) _
      _ = Real.exp (-(logWindow n 12 : ℝ) / (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by rw [neg_div]; linarith only [hquot])
  have hsquare : (n : ℝ) ^ 2 = Real.exp ((2 : ℝ) * Real.log (n : ℝ)) := by
    rw [show (2 : ℝ) * Real.log (n : ℝ) = ((2 : ℕ) : ℝ) * Real.log (n : ℝ) by norm_num,
      ← Real.log_pow, Real.exp_log (pow_pos hp 2)]
  calc
    _ ≤ Real.exp (-(12 : ℝ) * Real.log (n : ℝ)) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hdecay (sq_nonneg _)
    _ = Real.exp (-(10 : ℝ) * Real.log (n : ℝ)) := by
      rw [hsquare, ← Real.exp_add]
      congr 1
      ring
    _ = _ := by
      rw [show -(10 : ℝ) * Real.log (n : ℝ) =
        -((10 : ℝ) * Real.log (n : ℝ)) by ring, Real.exp_neg]
      have he : Real.exp ((10 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ 10 := by
        simpa only [Real.exp_log hp] using (Real.exp_nat_mul (Real.log (n : ℝ)) 10)
      rw [he, one_div]

theorem reciprocal_tail_calibration (n : ℕ) (hn : 2 ≤ n) :
    ENNReal.ofReal (1 - 1 / (n : ℝ)) ^ logWindow n 12 *
        ENNReal.ofReal ((n : ℝ) ^ 2) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 10) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) := by
    have hdiv : 1 / (n : ℝ) ≤ 1 := (div_le_one hp).2 (by linarith)
    linarith
  rw [← ENNReal.ofReal_pow hbase, ← ENNReal.ofReal_mul (pow_nonneg hbase _)]
  exact ENNReal.ofReal_le_ofReal (reciprocal_tail_real n hn)

theorem reciprocal_tail_calibration_ennreal (n : ℕ) (hn : 2 ≤ n) :
    (1 - 1 / (n : ℝ≥0∞)) ^ logWindow n 12 * (n : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 10) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have he : 1 - 1 / (n : ℝ≥0∞) = ENNReal.ofReal (1 - 1 / (n : ℝ)) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos hp, ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  rw [he]
  convert reciprocal_tail_calibration n hn using 1
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

end Ripple.PopulationProtocol.ExactMajority.PhaseNineBitAlgebra

end
