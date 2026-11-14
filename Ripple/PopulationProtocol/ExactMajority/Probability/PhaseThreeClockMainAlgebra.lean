-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainAlgebra.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainPath
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainExponential

/-!
# Scalar algebra for the guarded Main row

This file contains only deterministic and real-algebraic facts.  It does not
construct the stopped process or claim the guarded Main tail.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainAlgebra

open PhaseThreeClockMainLedger

variable {L K : ℕ}

/-- A Main/high-Clock contact and a Main/Main deep cancellation cannot occur on
the same ordered pair. -/
theorem contact_cancel_exclusive (h : ℕ) (s t : AgentState L K) :
    contactInd h s t * deepCancelInd h s t = 0 := by
  unfold contactInd deepCancelInd
  split_ifs <;> simp_all

/-- The P11 credit atom is at most two.  The naive bound three loses the
role-exclusivity of the two indicators. -/
theorem step_credit_atom_le_two (h : ℕ) (s t : AgentState L K) :
    contactInd h s t + 2 * deepCancelInd h s t ≤ 2 := by
  have hc := contactInd_le_one h s t
  have hd := deepCancelInd_le_one h s t
  have hx := contact_cancel_exclusive h s t
  by_cases hz : contactInd h s t = 0
  · omega
  · have hc' : contactInd h s t = 1 := by omega
    have hd' : deepCancelInd h s t = 0 := by
      rw [hc', one_mul] at hx
      exact hx
    omega

/-- On a killed unsafe step, discount a nonnegative potential once and freeze a
negative potential.  The result is always at most the one-step discounted
comparison value. -/
theorem killed_discount_le (q x : ℝ) (hq : q⁻¹ ≤ 1) :
    (if 0 ≤ x then q⁻¹ * x else x) ≤ q⁻¹ * x := by
  split_ifs with hx
  · exact le_rfl
  · simpa only [one_mul] using
      (mul_le_mul_of_nonpos_right hq (le_of_not_ge hx))

/-- At the credit barrier, while the Clock front is sparse, the un-discounted
normalized potential is at least `10⁻⁴`. -/
theorem barrier_potential_lower {M C A Z : ℝ}
    (hM : 0 < M) (hC : 0 < C)
    (hcredit : 3 * M ≤ 2500 * A)
    (hsparse : 1000 * Z ≤ C) :
    (1 / 10000 : ℝ) ≤ A / M - (11 / 10 : ℝ) * (Z / C) := by
  have hAM : (3 / 2500 : ℝ) ≤ A / M := by
    rw [le_div_iff₀ hM]
    nlinarith
  have hZC : Z / C ≤ (1 / 1000 : ℝ) := by
    rw [div_le_iff₀ hC]
    nlinarith
  nlinarith

/-- The two `RowMain` failures both force the same credit barrier once the path
ledger gives `H ≤ A` and `V ≤ 2A`. -/
theorem row_failure_forces_credit {M H V A : ℕ}
    (hhour : H ≤ A) (hdeep : V ≤ 2 * A)
    (hbad : 3 * M < 2500 * H ∨ 3 * M < 1250 * V) :
    3 * M < 2500 * A := by
  omega

/-- If `J` is bounded by the ordered positive/negative pairs, the weighted
cancellation term is at most `4 A²` once the total deep population is at most
`2A`. -/
theorem ordered_cancel_weight_le {J p q B A : ℝ}
    (hJ : J ≤ 2 * p * q)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hpq : p + q ≤ B) (hBA : B ≤ 2 * A) :
    2 * J ≤ 4 * A ^ 2 := by
  have hamgm : 4 * p * q ≤ (p + q) ^ 2 := by
    nlinarith only [sq_nonneg (p - q)]
  have hsqB : (p + q) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (add_nonneg hp hq) hpq 2
  have hsqA : B ^ 2 ≤ (2 * A) ^ 2 :=
    pow_le_pow_left₀ hB hBA 2
  nlinarith

/-- The scalar upper bound for the accepted live-step drift of
`A/M - 1.1 Z/C`, including the discount compensation `κ φ`, where
`κ = 12 M / (2500 P)`. -/
def normalizedDrift (M C A Z P : ℝ) : ℝ :=
  (2 * M * Z + 4 * A ^ 2) / (M * P) -
    (11 / 10 : ℝ) * (2 * Z * (C - Z) / (C * P)) -
    (12 * M / (2500 * P)) *
      (A / M - (11 / 10 : ℝ) * (Z / C))

/-- Equations (52)--(53), after the pair-count estimates: the compensated
normalized drift is nonpositive throughout the live sparse window. -/
theorem normalizedDrift_nonpos {n M C A Z P : ℝ}
    (hM : 0 < M) (hC : 0 < C) (hP : 0 < P)
    (hA : 0 ≤ A) (hZ : 0 ≤ Z)
    (hmain : 25 * M ≤ 13 * n)
    (hclock : 6 * n ≤ 25 * C)
    (hcredit : 2500 * A ≤ 3 * M)
    (hsparse : 1000 * Z ≤ C) :
    normalizedDrift M C A Z P ≤ 0 := by
  have hMC : 6 * M ≤ 13 * C := by
    nlinarith only [hmain, hclock]
  have hAroom : 0 ≤ 3 * M - 2500 * A := by
    nlinarith only [hcredit]
  have hAprod : 0 ≤ A * (3 * M - 2500 * A) :=
    mul_nonneg hA hAroom
  have hAbase : 10000 * A ^ 2 ≤ 12 * A * M := by
    nlinarith only [hAprod]
  have hAcross : 10000 * A ^ 2 * P ≤ 12 * A * M * P :=
    mul_le_mul_of_nonneg_right hAbase hP.le
  have hAterm :
      4 * A ^ 2 / (M * P) - 12 * A / (2500 * P) ≤ 0 := by
    apply sub_nonpos.mpr
    apply (div_le_div_iff₀ (mul_pos hM hP)
      (mul_pos (by norm_num : (0 : ℝ) < 2500) hP)).2
    nlinarith only [hAcross]
  have hbracket :
      -(C / 5) + 11 * Z / 5 + 132 * M / 25000 ≤ 0 := by
    linarith only [hMC, hsparse, hC]
  have hZeq :
      2 * Z / P -
          (11 / 10 : ℝ) * (2 * Z * (C - Z) / (C * P)) +
          (12 * M / (2500 * P)) * ((11 / 10 : ℝ) * (Z / C)) =
        Z / (C * P) *
          (-(C / 5) + 11 * Z / 5 + 132 * M / 25000) := by
    field_simp [ne_of_gt hC, ne_of_gt hP]
    <;> ring
  have hZterm :
      2 * Z / P -
          (11 / 10 : ℝ) * (2 * Z * (C - Z) / (C * P)) +
          (12 * M / (2500 * P)) * ((11 / 10 : ℝ) * (Z / C)) ≤ 0 := by
    rw [hZeq]
    exact mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg hZ (mul_pos hC hP).le) hbracket
  have hsplit :
      normalizedDrift M C A Z P =
        (4 * A ^ 2 / (M * P) - 12 * A / (2500 * P)) +
        (2 * Z / P -
          (11 / 10 : ℝ) * (2 * Z * (C - Z) / (C * P)) +
          (12 * M / (2500 * P)) * ((11 / 10 : ℝ) * (Z / C))) := by
    unfold normalizedDrift
    field_simp [ne_of_gt hM, ne_of_gt hC, ne_of_gt hP]
    <;> ring
  rw [hsplit]
  exact add_nonpos hAterm hZterm

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainAlgebra

end
