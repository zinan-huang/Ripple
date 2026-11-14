-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockTickWeightAlgebra.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRisingFactorial

noncomputable section

open Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRisingFactorial

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockTickWeightAlgebra

theorem tick_weight_affine_identity (P J b d : ℝ)
    (hP : P = 0 ∨ P = 1) (hJ : J = 0 ∨ J = 1) (hPJ : P ≤ J) :
    Real.exp (-d * J) * (1 + b * P) =
      1 + (Real.exp (-d) - 1) * J + Real.exp (-d) * b * P := by
  rcases hP with rfl | rfl <;> rcases hJ with rfl | rfl
  · simp
  · simp only [mul_one, mul_zero, add_zero]
    ring
  · norm_num at hPJ
  · simp only [mul_one]
    ring

theorem exp_neg_mul_one_add_le_one (d : ℝ) :
    Real.exp (-d) * (1 + d) ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp d)
    (Real.exp_nonneg (-d))
  have heq : Real.exp (-d) * Real.exp d = 1 := by
    rw [← Real.exp_add]
    simp
  rw [heq] at h
  linarith

theorem tick_weight_mean_le_one (q p b d : ℝ)
    (hq : 0 ≤ q) (hrate : b * p ≤ q * d) :
    1 + (Real.exp (-d) - 1) * q + Real.exp (-d) * b * p ≤ 1 := by
  have hrate' := mul_le_mul_of_nonneg_left hrate (Real.exp_nonneg (-d))
  have hbase := mul_le_mul_of_nonneg_left (exp_neg_mul_one_add_le_one d) hq
  nlinarith

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockTickWeightAlgebra

end
