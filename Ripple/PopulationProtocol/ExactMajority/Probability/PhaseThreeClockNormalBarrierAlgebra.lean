-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockNormalBarrierAlgebra.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Model

/-!
# Exact one-step algebra for the normal-front barrier

This file proves PHASE3 P4's exponential increment inequality, including
simultaneous front and normal-high increases, and the rational coefficient
comparison. A finite weighted-pair version gives the one-step exponential
mean bound from the two stated rate estimates.

It does not construct the analytical marks, derive their normal-count rate
from the protocol, or invoke a maximal/stopping theorem. Those remain
separate obligations of the complete shape producer.
-/

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalBarrierAlgebra

theorem exp_tenth_sub_one_le :
    Real.exp (1 / 10 : ℝ) - 1 ≤ (53 / 500 : ℝ) := by
  have h := Real.exp_bound' (x := (1 / 10 : ℝ))
    (by norm_num) (by norm_num) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- A quadratic upper estimate for the negative exponential, proved from
the positive quadratic Taylor lower bound. -/
theorem exp_neg_le_quadratic (v : ℝ) (hv : 0 ≤ v) :
    Real.exp (-v) ≤ 1 - v + v ^ 2 / 2 := by
  have hB : 0 ≤ 1 - v + v ^ 2 / 2 := by nlinarith [sq_nonneg (v - 1)]
  have hq := Real.quadratic_le_exp_of_nonneg hv
  have hp := mul_le_mul_of_nonneg_left hq hB
  have hmul : 1 ≤ (1 - v + v ^ 2 / 2) * Real.exp v := by
    nlinarith [sq_nonneg (v ^ 2)]
  have hdiv : 1 / Real.exp v ≤ 1 - v + v ^ 2 / 2 :=
    (div_le_iff₀ (Real.exp_pos v)).2 hmul
  simpa only [Real.exp_neg, one_div] using hdiv

theorem normal_barrier_decay_lower (z : ℝ)
    (hz : 0 ≤ z) (hzu : z ≤ 101 / 1000) :
    (89 / 500 : ℝ) * z ≤ 1 - Real.exp (-(9 / 50 : ℝ) * z) := by
  have hq := exp_neg_le_quadratic ((9 / 50 : ℝ) * z) (by positivity)
  have hsq : z ^ 2 ≤ (101 / 1000 : ℝ) * z := by
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hzu)]
  have heq : -((9 / 50 : ℝ) * z) = -(9 / 50 : ℝ) * z := by ring
  rw [heq] at hq
  nlinarith

theorem normal_barrier_decay_lower_of_ge (a z : ℝ)
    (hz : 0 ≤ z) (hzu : z ≤ 101 / 1000) (ha : (9 / 50 : ℝ) * z ≤ a) :
    (89 / 500 : ℝ) * z ≤ 1 - Real.exp (-a) := by
  have hm : Real.exp (-a) ≤ Real.exp (-(9 / 50 : ℝ) * z) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith [normal_barrier_decay_lower z hz hzu]

/-- The omitted cross term is nonpositive when both increments are one. -/
theorem exp_pair_increment_bound (a dx dy : ℝ) (ha : 0 ≤ a)
    (hx : dx = 0 ∨ dx = 1) (hy : dy ≤ 0 ∨ dy = 1) :
    Real.exp (dy / 10 - a * dx) ≤
      1 + (Real.exp (1 / 10 : ℝ) - 1) * (if dy = 1 then 1 else 0) -
        (1 - Real.exp (-a)) * dx := by
  classical
  have hepos : 1 ≤ Real.exp (1 / 10 : ℝ) := Real.one_le_exp (by norm_num)
  have heneg : Real.exp (-a) ≤ 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (by linarith : -a ≤ 0))
  by_cases hyone : dy = 1
  · subst dy
    rcases hx with rfl | rfl
    · simp <;> linarith
    · simp only [↓reduceIte, ite_true, mul_one]
      rw [sub_eq_add_neg, Real.exp_add]
      have hp := mul_nonneg (sub_nonneg.mpr hepos) (sub_nonneg.mpr heneg)
      nlinarith
  · have hydown : dy ≤ 0 := hy.resolve_right hyone
    rcases hx with rfl | rfl
    · simp only [if_neg hyone, mul_zero, sub_zero, add_zero]
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (by linarith : dy / 10 ≤ 0))
    · simp only [if_neg hyone, mul_zero, mul_one, add_zero]
      have h := Real.exp_le_exp.mpr (by linarith : dy / 10 - a ≤ -a)
      linarith

def normalPotential (C X Y : ℝ) : ℝ := Y - (9 / 10 : ℝ) * X ^ 2 / C

theorem normalPotential_increment (C X Y dx dy : ℝ)
    (hx : dx = 0 ∨ dx = 1) :
    (normalPotential C (X + dx) (Y + dy) - normalPotential C X Y) / 10 =
      dy / 10 - ((9 / 100 : ℝ) * (2 * X + 1) / C) * dx := by
  rcases hx with rfl | rfl <;> unfold normalPotential <;> ring

theorem normal_barrier_increment_coefficient (C X : ℝ) (hC : 0 < C) :
    (9 / 50 : ℝ) * (X / C) ≤ (9 / 100 : ℝ) * (2 * X + 1) / C := by
  calc
    (9 / 50 : ℝ) * (X / C) ≤
        (9 / 50 : ℝ) * (X / C) + (9 / 100 : ℝ) / C :=
      le_add_of_nonneg_right (div_nonneg (by norm_num) hC.le)
    _ = _ := by ring

theorem normalPotential_exp_increment_bound (C X Y dx dy : ℝ)
    (hC : 0 < C) (hX : 0 ≤ X)
    (hx : dx = 0 ∨ dx = 1) (hy : dy ≤ 0 ∨ dy = 1) :
    Real.exp
      ((normalPotential C (X + dx) (Y + dy) - normalPotential C X Y) / 10) ≤
      1 + (Real.exp (1 / 10 : ℝ) - 1) * (if dy = 1 then 1 else 0) -
        (1 - Real.exp (-((9 / 100 : ℝ) * (2 * X + 1) / C))) * dx := by
  rw [normalPotential_increment C X Y dx dy hx]
  exact exp_pair_increment_bound _ dx dy
    (div_nonneg (by positivity) hC.le) hx hy

/-- The exact polynomial margin 0.2968 < 0.320044 in normalized variables. -/
theorem normal_barrier_coefficient (z y : ℝ)
    (hz : 0 ≤ z) (hzu : z ≤ 101 / 1000) (hy : y ≤ (9 / 10 : ℝ) * z ^ 2) :
    (53 / 500 : ℝ) * (z ^ 2 + 2 * y) -
      (89 / 500 : ℝ) * z * (2 * z * (1 - z)) ≤ 0 := by
  have hp := mul_nonneg (sub_nonneg.mpr hzu) (sq_nonneg z)
  nlinarith [sq_nonneg z]

/-- The scalar rate implication used after taking a one-step expectation. -/
theorem normal_barrier_rate_bound (a z y k pX pY : ℝ)
    (hz : 0 ≤ z) (hzu : z ≤ 101 / 1000)
    (hy : y ≤ (9 / 10 : ℝ) * z ^ 2)
    (hk : 0 ≤ k) (hpX : 0 ≤ pX) (hpY : 0 ≤ pY)
    (ha : (9 / 50 : ℝ) * z ≤ a)
    (hX : 2 * z * (1 - z) * k ≤ pX)
    (hY : pY ≤ (z ^ 2 + 2 * y) * k) :
    1 + (Real.exp (1 / 10 : ℝ) - 1) * pY -
      (1 - Real.exp (-a)) * pX ≤ 1 := by
  have hpositive :
      (Real.exp (1 / 10 : ℝ) - 1) * pY ≤
        (53 / 500 : ℝ) * ((z ^ 2 + 2 * y) * k) :=
    (mul_le_mul_of_nonneg_right exp_tenth_sub_one_le hpY).trans
      (mul_le_mul_of_nonneg_left hY (by norm_num))
  have hnegative :
      (89 / 500 : ℝ) * z * (2 * z * (1 - z) * k) ≤
        (1 - Real.exp (-a)) * pX :=
    (mul_le_mul_of_nonneg_left hX (by positivity)).trans
      (mul_le_mul_of_nonneg_right
        (normal_barrier_decay_lower_of_ge a z hz hzu ha) hpX)
  have hcoef := mul_nonpos_of_nonpos_of_nonneg
    (normal_barrier_coefficient z y hz hzu hy) hk
  nlinarith

/-- Finite weighted-pair form of the normal-front one-step exponential bound.
The hypotheses concern the increment rates, not a desired passage/barrier tail. -/
theorem normal_barrier_weighted_step {ι : Type*} [Fintype ι]
    (w dx dy : ι → ℝ) (a z y k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hx : ∀ i, dx i = 0 ∨ dx i = 1)
    (hyinc : ∀ i, dy i ≤ 0 ∨ dy i = 1)
    (hz : 0 ≤ z) (hzu : z ≤ 101 / 1000)
    (hy : y ≤ (9 / 10 : ℝ) * z ^ 2)
    (hk : 0 ≤ k) (ha : (9 / 50 : ℝ) * z ≤ a)
    (hX : 2 * z * (1 - z) * k ≤ ∑ i, w i * dx i)
    (hY : (∑ i, w i * (if dy i = 1 then 1 else 0)) ≤
      (z ^ 2 + 2 * y) * k) :
    (∑ i, w i * Real.exp (dy i / 10 - a * dx i)) ≤ 1 := by
  classical
  have ha0 : 0 ≤ a := by linarith
  have hpX : 0 ≤ ∑ i, w i * dx i := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (hw i)
    rcases hx i with h | h <;> simp [h]
  have hpY : 0 ≤ ∑ i, w i * (if dy i = 1 then 1 else 0) := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (hw i)
    split_ifs <;> norm_num
  have halg :
      (∑ i, w i *
        (1 + (Real.exp (1 / 10 : ℝ) - 1) * (if dy i = 1 then 1 else 0) -
          (1 - Real.exp (-a)) * dx i)) =
      (∑ i, w i) +
        (Real.exp (1 / 10 : ℝ) - 1) *
          (∑ i, w i * (if dy i = 1 then 1 else 0)) -
        (1 - Real.exp (-a)) * (∑ i, w i * dx i) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    _ ≤ ∑ i, w i *
        (1 + (Real.exp (1 / 10 : ℝ) - 1) * (if dy i = 1 then 1 else 0) -
          (1 - Real.exp (-a)) * dx i) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (exp_pair_increment_bound a (dx i) (dy i) ha0 (hx i) (hyinc i)) (hw i)
    _ = 1 + (Real.exp (1 / 10 : ℝ) - 1) *
        (∑ i, w i * (if dy i = 1 then 1 else 0)) -
        (1 - Real.exp (-a)) * (∑ i, w i * dx i) := by rw [halg, hsum]
    _ ≤ 1 := normal_barrier_rate_bound a z y k _ _
      hz hzu hy hk hpX hpY ha hX hY

/-- The compiled numerical calibration already supplies the desired
polynomial size for the initial exponential barrier height. -/
theorem normal_barrier_initial_error (C : ℕ) (F : ℝ)
    (hC : 0 < (C : ℝ)) (hlog : 4194304 ≤ Real.log (C : ℝ))
    (hF : F ≤ -(9 / 10 : ℝ) * (C : ℝ) ^ (1 / 50 : ℝ)) :
    Real.exp (F / 10) ≤ (C : ℝ) ^ (-100 : ℝ) := by
  have harg : F / 10 ≤ -(9 / 100 : ℝ) * (C : ℝ) ^ (1 / 50 : ℝ) := by
    linarith
  exact (Real.exp_le_exp.mpr harg).trans
    (PhaseThreeModel.Numeric.exponential_error_calibration hC hlog).2.1

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalBarrierAlgebra

end
