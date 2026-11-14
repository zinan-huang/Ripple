-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingSnapshotNumerics.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCalibration

/-!
# Row-2 finite union and completed-snapshot constants

There is one accepted-trial slot and the frozen-prefix slots for each
of three classes and each integer floor.  The scalar union is taken under one
law and never conditions on a random completed-snapshot value.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingSnapshotNumerics

open LateSamplingCalibration

/-- The exact finite prefactor followed by the polynomial envelope. -/
theorem rowTwo_test_union_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n M : ℕ) (hn : 1 ≤ n) (hM : M ≤ n)
    (E : ClassTestIndex M → Set Ω)
    (hE : ∀ i, μ (E i) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 800000000000000))) :
    μ (⋃ i, E i) ≤
      ENNReal.ofReal
        (13 * (n : ℝ) ^ 2 *
          Real.exp (-(n : ℝ) / 800000000000000)) := by
  have hunion := class_test_union_bound μ n M E hE
  have hprefactor := sampling_finite_prefactor hn hM
  have hmul := mul_le_mul_of_nonneg_right hprefactor
    (Real.exp_nonneg (-(n : ℝ) / 800000000000000))
  exact hunion.trans (ENNReal.ofReal_le_ofReal hmul)

/-- Strict inverse-power form used by the N18 budget. -/
theorem rowTwo_test_union_inverse_power
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n M : ℕ) (hM : M ≤ n)
    (hlog : (1000000000000 : ℝ) < Real.log (n : ℝ))
    (E : ClassTestIndex M → Set Ω)
    (hE : ∀ i, μ (E i) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 800000000000000))) :
    μ (⋃ i, E i) <
      ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) := by
  have hunion := class_test_union_bound μ n M E hE
  have hfactor := sampling_finite_factor hM hlog
  have hn1 : (1 : ℝ) < n := by
    by_contra h
    push_neg at h
    have := Real.log_nonpos (Nat.cast_nonneg n) h
    linarith
  have hnpos : (0 : ℝ) < n := lt_trans one_pos hn1
  have hn1' : 1 ≤ n := by exact_mod_cast hn1.le
  have hmul := mul_le_mul_of_nonneg_right (sampling_finite_prefactor hn1' hM)
    (Real.exp_nonneg (-(n : ℝ) / 800000000000000))
  exact lt_of_le_of_lt (hunion.trans (ENNReal.ofReal_le_ofReal hmul))
    ((ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hnpos _)).mpr hfactor.2)

/-- Integer-floor form of
`S_ell ≥ (A_ell/M - .0021) R`. -/
theorem exact_level_sample_floor
    {M A R S : ℕ} (hM : 0 < M)
    (h : ((A : ℚ) / M - 21 / 10000) * R ≤ S) :
    10000 * A * R ≤ 10000 * M * S + 21 * M * R := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hscale := mul_le_mul_of_nonneg_left h
    (show (0 : ℚ) ≤ 10000 * M by positivity)
  have hq : (10000 : ℚ) * A * R ≤
      10000 * M * S + 21 * M * R := by
    field_simp [hM'] at hscale
    nlinarith only [hscale]
  exact_mod_cast hq

/-- `.5698` live class floor minus the `.0001` accepted-trial loss. -/
theorem first_alternative_sample_floor
    {R S : ℕ}
    (h : ((5698 / 10000 : ℚ) - 1 / 10000) * R ≤ S) :
    5697 * R ≤ 10000 * S := by
  have hq : (5697 : ℚ) * R ≤ 10000 * S := by
    norm_num at h ⊢
    linarith only [h]
  exact_mod_cast hq

/-- `.939` retained-credit class floor minus the same loss. -/
theorem second_alternative_sample_floor
    {R S : ℕ}
    (h : ((939 / 1000 : ℚ) - 1 / 10000) * R ≤ S) :
    9389 * R ≤ 10000 * S := by
  have hq : (9389 : ℚ) * R ≤ 10000 * S := by
    norm_num at h ⊢
    linarith only [h]
  exact_mod_cast hq

/-- A `.9232` protected good class leaves at most `.0769` dangerous
completed samples after the `.0001` accepted-trial loss. -/
theorem dangerous_sample_ceiling
    {R good bad : ℕ}
    (hcomplete : good + bad = R)
    (hgood : ((9232 / 10000 : ℚ) - 1 / 10000) * R ≤ good) :
    10000 * bad ≤ 769 * R := by
  have hcomplete' : (good : ℚ) + bad = R := by exact_mod_cast hcomplete
  have hq : (10000 : ℚ) * bad ≤ 769 * R := by
    norm_num at hgood ⊢
    linarith only [hgood, hcomplete']
  exact_mod_cast hq

/-- Package the four bounds at one actual completed snapshot. -/
theorem simultaneous_snapshot_bounds
    {M A R exactLevel firstBand secondBand protectedGood dangerous : ℕ}
    (hM : 0 < M)
    (hexact : ((A : ℚ) / M - 21 / 10000) * R ≤ exactLevel)
    (hfirst : ((5698 / 10000 : ℚ) - 1 / 10000) * R ≤ firstBand)
    (hsecond : ((939 / 1000 : ℚ) - 1 / 10000) * R ≤ secondBand)
    (hcomplete : protectedGood + dangerous = R)
    (hprotected : ((9232 / 10000 : ℚ) - 1 / 10000) * R ≤ protectedGood) :
    10000 * A * R ≤ 10000 * M * exactLevel + 21 * M * R ∧
      5697 * R ≤ 10000 * firstBand ∧
      9389 * R ≤ 10000 * secondBand ∧
      10000 * dangerous ≤ 769 * R := by
  exact
    ⟨exact_level_sample_floor hM hexact,
      first_alternative_sample_floor hfirst,
      second_alternative_sample_floor hsecond,
      dangerous_sample_ceiling hcomplete hprotected⟩

end Ripple.PopulationProtocol.ExactMajority.LateSamplingSnapshotNumerics

end
