-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockActivationHarmonic.lean
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationHarmonic

theorem harmonic_cast_eq_sum_Ico (k : ℕ) :
    (harmonic k : ℝ) = ∑ j ∈ Finset.Ico 1 (k + 1), (j : ℝ)⁻¹ := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    Finset.Ico_add_one_right_eq_Icc]

theorem sum_reciprocal_Ico_le_log (r b : ℕ) (hr : 1 ≤ r) (hrb : r ≤ b) :
    (∑ j ∈ Finset.Ico r b, 1 / (j : ℝ)) ≤
      1 + Real.log (b : ℝ) - Real.log (r : ℝ) := by
  have hlo : Real.log (r : ℝ) ≤ ∑ j ∈ Finset.Ico 1 r, (j : ℝ)⁻¹ := by
    simpa only [harmonic_cast_eq_sum_Ico, Nat.sub_add_cancel hr] using
      log_add_one_le_harmonic (r - 1)
  have hhi := harmonic_le_one_add_log b
  have hsplit := Finset.sum_Ico_consecutive (fun j : ℕ => (j : ℝ)⁻¹) hr hrb
  have htop := Finset.sum_Ico_succ_top (hr.trans hrb) (fun j : ℕ => (j : ℝ)⁻¹)
  rw [← harmonic_cast_eq_sum_Ico b] at htop
  have hnonneg : 0 ≤ (b : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg b)
  simp only [one_div]
  linarith only [hlo, hhi, hsplit, htop, hnonneg]

theorem sum_reciprocal_Ico_le_log_population (n r b : ℕ)
    (hr : 1 ≤ r) (hrb : r ≤ b) (hbn : b ≤ n) :
    (∑ j ∈ Finset.Ico r b, 1 / (j : ℝ)) ≤
      1 + Real.log (n : ℝ) - Real.log (r : ℝ) := by
  have hbp : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hlog := Real.log_le_log hbp (Nat.cast_le.mpr hbn)
  have hsum := sum_reciprocal_Ico_le_log r b hr hrb
  linarith

theorem sum_reverse_reciprocal_le_log_hundred (n r b : ℕ)
    (hr : 1 ≤ r) (hrb : r ≤ b) (hbn : b ≤ n)
    (hgap : (n : ℝ) / 100 ≤ ((n + 1 - b : ℕ) : ℝ)) :
    (∑ j ∈ Finset.Ico r b, 1 / ((n : ℝ) - (j : ℝ))) ≤
      1 + Real.log (100 : ℝ) := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 ≤ n + 1 - b := by omega
  have had : n + 1 - b ≤ n + 1 - r := by omega
  have hdn : n + 1 - r ≤ n := by omega
  have hdp : 0 < ((n + 1 - r : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n + 1 - r by omega)
  have hdlog := Real.log_le_log hdp (Nat.cast_le.mpr hdn)
  have halog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) / 100) hgap
  rw [Real.log_div (ne_of_gt hnp) (by norm_num : (100 : ℝ) ≠ 0)] at halog
  have hsum := sum_reciprocal_Ico_le_log (n + 1 - b) (n + 1 - r) ha had
  have hrewrite :
      (∑ j ∈ Finset.Ico r b, 1 / ((n : ℝ) - (j : ℝ))) =
        ∑ j ∈ Finset.Ico (n + 1 - b) (n + 1 - r), 1 / (j : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.Ico r b, 1 / ((n - j : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j ≤ n := by
          have h := Finset.mem_Ico.mp hj
          omega
        rw [Nat.cast_sub hjn]
      _ = _ := Finset.sum_Ico_reflect (fun j : ℕ => 1 / (j : ℝ)) r (by omega)
  rw [hrewrite]
  linarith only [hsum, hdlog, halog]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationHarmonic

end
