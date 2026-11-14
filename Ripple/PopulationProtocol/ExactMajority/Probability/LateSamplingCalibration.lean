-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingCalibration.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.ScalarTails

/-!
The finite union in DOTY-LATE-TAIL-REVIEW §4.5. The scalar comparison keeps
the factor 3 * (M + 1)^2 + 1. The sharp frozen-pool Hoeffding exponent
with tolerance 1 / 40000 gives the required base error at the first
ceil (n / 1000000) frozen Main agents.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingCalibration

open TimeTheorem
-- the symbolic threshold wrapper is private upstream; going through it keeps the kernel
-- from evaluating `2 ^ (2 ^ 41)`
open private timeThresholdAt time_population_threshold_eq from
  Ripple.PopulationProtocol.ExactMajority.Probability.TimeTheorem

private theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem logarithm_from_power (e n : ℕ)
    (hn : timeThresholdAt e ≤ n) :
    (e : ℝ) / 2 ≤ Real.log (n : ℝ) := by
  unfold timeThresholdAt at hn
  have hp : 2 ^ e ≤ n := by omega
  have hp' : (2 : ℝ) ^ e ≤ (n : ℝ) := by exact_mod_cast hp
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ e) hp'
  rw [Real.log_pow] at h
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hl := mul_le_mul_of_nonneg_left half_le_log_two he
  nlinarith

/-- The stronger logarithmic threshold used in the late sampling calculation. -/
theorem time_threshold_logarithm {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    (1000000000000 : ℝ) < Real.log (n : ℝ) := by
  have hnAt : timeThresholdAt (2 ^ 41) ≤ n :=
    (congrArg (fun q : ℕ => q ≤ n) time_population_threshold_eq).mp hn
  have h := logarithm_from_power (2 ^ 41) n hnAt
  norm_num at h
  linarith

theorem logarithm_population_lower {n : ℕ}
    (hlog : (1000000000000 : ℝ) < Real.log (n : ℝ)) :
    1000000 ≤ n := by
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    rw [hz] at hlog
    norm_num at hlog
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.add_one_le_exp (Real.log (n : ℝ))
  rw [Real.exp_log hn'] at h
  have hreal : (1000000 : ℝ) ≤ n := by linarith
  exact_mod_cast hreal

/-- A cubic lower bound obtained directly from 1 + x ≤ exp x. -/
theorem late_exponential_dominates_logarithm {x : ℝ}
    (hx : (1000000000000 : ℝ) < x) :
    200 * x < Real.exp x / 800000000000000 := by
  have hxpos : 0 < x := by linarith
  have hb : x / 3 ≤ Real.exp (x / 3) := by
    linarith [Real.add_one_le_exp (x / 3)]
  have hc : (x / 3) ^ 3 ≤ (Real.exp (x / 3)) ^ 3 := by
    gcongr <;> linarith
  have he : (Real.exp (x / 3)) ^ 3 = Real.exp x := by
    calc
      (Real.exp (x / 3)) ^ 3 =
          Real.exp (x / 3) * Real.exp (x / 3) * Real.exp (x / 3) := by ring
      _ = Real.exp (x / 3 + x / 3 + x / 3) := by
        rw [Real.exp_add, Real.exp_add]
      _ = Real.exp x := by congr 1; ring
  rw [he] at hc
  have hs : (4320000000000000000 : ℝ) < x ^ 2 := by
    nlinarith [sq_nonneg (x - 1000000000000)]
  have ht := mul_pos hxpos (sub_pos.mpr hs)
  nlinarith

/-- The finite prefactor is bounded without replacing M + 1 by M. -/
theorem sampling_finite_prefactor {n M : ℕ}
    (hn : 1 ≤ n) (hM : M ≤ n) :
    3 * ((M : ℝ) + 1) ^ 2 + 1 ≤ 13 * (n : ℝ) ^ 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM' : (M : ℝ) ≤ n := by exact_mod_cast hM
  have hbase : (M : ℝ) + 1 ≤ 2 * n := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hbase)
    (show (0 : ℝ) ≤ 2 * n + ((M : ℝ) + 1) by positivity)
  nlinarith

/-- Exact review factor, followed by its polynomial bound and inverse-power bound. -/
theorem sampling_finite_factor {n M : ℕ}
    (hM : M ≤ n)
    (hlog : (1000000000000 : ℝ) < Real.log (n : ℝ)) :
    (3 * ((M : ℝ) + 1) ^ 2 + 1) *
          Real.exp (-(n : ℝ) / 800000000000000) ≤
        13 * (n : ℝ) ^ 2 *
          Real.exp (-(n : ℝ) / 800000000000000) ∧
      13 * (n : ℝ) ^ 2 *
          Real.exp (-(n : ℝ) / 800000000000000) <
        Real.rpow (n : ℝ) (-190) := by
  have hn : 1 ≤ n := (by norm_num : 1 ≤ (1000000 : ℕ)).trans
    (logarithm_population_lower hlog)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  constructor
  · exact mul_le_mul_of_nonneg_right (sampling_finite_prefactor hn hM)
      (Real.exp_nonneg _)
  · have hdecay := late_exponential_dominates_logarithm hlog
    rw [Real.exp_log hnpos] at hdecay
    have hconstant : (13 : ℝ) < Real.exp (8 * Real.log (n : ℝ)) := by
      have h := Real.add_one_le_exp (8 * Real.log (n : ℝ))
      linarith
    have hpower : Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hnpos, pow_two]
    change 13 * (n : ℝ) ^ 2 * Real.exp (-(n : ℝ) / 800000000000000) < (n : ℝ) ^ (-190 : ℝ)
    rw [Real.rpow_def_of_pos hnpos]
    calc
      13 * (n : ℝ) ^ 2 * Real.exp (-(n : ℝ) / 800000000000000) =
          13 * Real.exp (2 * Real.log (n : ℝ) -
            (n : ℝ) / 800000000000000) := by
        rw [← hpower, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ < Real.exp (8 * Real.log (n : ℝ)) *
          Real.exp (2 * Real.log (n : ℝ) -
            (n : ℝ) / 800000000000000) :=
        mul_lt_mul_of_pos_right hconstant (Real.exp_pos _)
      _ = Real.exp (10 * Real.log (n : ℝ) -
            (n : ℝ) / 800000000000000) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ < Real.exp (Real.log (n : ℝ) * (-190)) := by
        apply Real.exp_lt_exp.mpr
        linarith

/-- Three classes, M + 1 integer floors, M frozen-prefix tests plus
one accepted-trial test, and one shared early-role test. -/
abbrev ClassTestIndex (M : ℕ) :=
  Option (Fin 3 × Fin (M + 1) × Fin (M + 1))

theorem classTestIndex_card (M : ℕ) :
    Fintype.card (ClassTestIndex M) = 3 * (M + 1) ^ 2 + 1 := by
  simp [ClassTestIndex, pow_two, Nat.mul_assoc]

/-- Each premise bounds one deterministic test under the same law.
There is no event conditioning on a future class size. -/
theorem class_test_union_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n M : ℕ)
    (E : ClassTestIndex M → Set Ω)
    (hE : ∀ i, μ (E i) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 800000000000000))) :
    μ (⋃ i, E i) ≤ ENNReal.ofReal
      ((3 * ((M : ℝ) + 1) ^ 2 + 1) *
        Real.exp (-(n : ℝ) / 800000000000000)) := by
  calc
    μ (⋃ i, E i) ≤ ∑' i, μ (E i) := measure_iUnion_le _
    _ ≤ ∑' _ : ClassTestIndex M,
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 800000000000000)) :=
      ENNReal.tsum_le_tsum hE
    _ = ENNReal.ofReal
        ((3 * ((M : ℝ) + 1) ^ 2 + 1) *
          Real.exp (-(n : ℝ) / 800000000000000)) := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
        ← ENNReal.ofReal_nsmul]
      congr 1
      simp only [nsmul_eq_mul, classTestIndex_card, Nat.cast_add,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

/-- The sharp frozen-pool tail has the required base exponent. -/
theorem frozen_hoeffding_exponent (n : ℕ) :
    (n : ℝ) / 800000000000000 ≤
      2 * (1 / 40000 : ℝ) ^ 2 *
        (Nat.ceil ((n : ℝ) / 1000000) : ℝ) := by
  have h := Nat.le_ceil ((n : ℝ) / 1000000)
  nlinarith

theorem early_role_exponent (n : ℕ) :
    (n : ℝ) / 800000000000000 ≤
      (Nat.ceil ((n : ℝ) / 1000000) : ℝ) / 100 := by
  have h := Nat.le_ceil ((n : ℝ) / 1000000)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

end Ripple.PopulationProtocol.ExactMajority.LateSamplingCalibration

end
