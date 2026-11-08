import Ripple.PopulationProtocol.PopProto.Convergence.OccupationTime

/-! # Charges for returning to a corner

Outside a corner, increases of its potential are charged to the actual VB/XY
interactions. This is the missing compensation that permits an occupation
supermartingale to run on the original chain through returns.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Ripple.PopulationProtocol.PopProto.Config
variable {n : ℕ}

/-- A single interaction increases the X-corner potential by at most
2 for VB, 1 for XY, and zero otherwise, including infeasible pairs. -/
theorem potentialLargeX_step_charge (c : Config n) (i r : State) :
    (c.stepOrSelf i r).potentialLargeX ≤ c.potentialLargeX +
      2 * (if isVB i r then 1 else 0) + (if isXY i r then 1 else 0) := by
  cases i <;> cases r <;>
    simp [stepOrSelf, step, potentialLargeX, isVB, isXY] <;>
    split_ifs <;> simp_all <;> omega

/-- Outside the X corner the potential is large enough to pay for each
possible one-step increase at a relative cost of 16/n or 8/n. -/
theorem potentialLargeX_outside_lower (c : Config n) (hc : ¬c.inLargeX) :
    n ≤ 8 * c.potentialLargeX := by
  unfold inLargeX at hc
  unfold potentialLargeX
  have := c.sum_eq
  omega

/-- Exponential one-step compensation outside the X corner. -/
theorem potentialLargeX_outside_compensation (hn : 0 < n) (c : Config n)
    (hc : ¬c.inLargeX) (i r : State) :
    Real.exp (-((16 : ℝ) * (if isVB i r then 1 else 0) +
      8 * (if isXY i r then 1 else 0)) / (n : ℝ)) *
      ((c.stepOrSelf i r).potentialLargeX : ℝ) ≤ (c.potentialLargeX : ℝ) := by
  let d : ℝ := 2 * (if isVB i r then 1 else 0) + (if isXY i r then 1 else 0)
  have hd : 0 ≤ d := by dsimp [d]; split_ifs <;> norm_num
  have hp : 0 ≤ (c.potentialLargeX : ℝ) := Nat.cast_nonneg _
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlower : (n : ℝ) ≤ 8 * (c.potentialLargeX : ℝ) := by
    exact_mod_cast potentialLargeX_outside_lower c hc
  have hstep : ((c.stepOrSelf i r).potentialLargeX : ℝ) ≤
      (c.potentialLargeX : ℝ) + d := by
    dsimp [d]
    norm_cast
    simpa [Nat.add_assoc] using potentialLargeX_step_charge c i r
  have hrel : ((c.stepOrSelf i r).potentialLargeX : ℝ) ≤
      (c.potentialLargeX : ℝ) * (1 + 8 * d / (n : ℝ)) := by
    apply hstep.trans
    have hmul := mul_le_mul_of_nonneg_right hlower hd
    have hd_bound : d ≤ 8 * (c.potentialLargeX : ℝ) * d / (n : ℝ) :=
      (le_div_iff₀ hnR).mpr (by nlinarith [hmul])
    calc (c.potentialLargeX : ℝ) + d ≤
        (c.potentialLargeX : ℝ) + 8 * (c.potentialLargeX : ℝ) * d / (n : ℝ) :=
          by linarith [hd_bound]
      _ = (c.potentialLargeX : ℝ) * (1 + 8 * d / (n : ℝ)) := by ring
  have hexp : ((c.stepOrSelf i r).potentialLargeX : ℝ) ≤
      (c.potentialLargeX : ℝ) * Real.exp (8 * d / (n : ℝ)) :=
    hrel.trans (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (8*d/(n:ℝ))]) hp)
  have hcancel : Real.exp (-(8 * d / (n : ℝ))) *
      ((c.potentialLargeX : ℝ) * Real.exp (8 * d / (n : ℝ))) =
      (c.potentialLargeX : ℝ) := by
    rw [mul_left_comm, ← Real.exp_add]
    simp
  have h := mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg (-(8*d/(n:ℝ))))
  rw [hcancel] at h
  convert h using 1 <;> congr 2 <;> dsimp [d] <;> ring

/-- A single interaction increases the Y-corner potential by at most
2 for VB, 1 for XY, and zero otherwise, including infeasible pairs. -/
theorem potentialLargeY_step_charge (c : Config n) (i r : State) :
    (c.stepOrSelf i r).potentialLargeY ≤ c.potentialLargeY +
      2 * (if isVB i r then 1 else 0) + (if isXY i r then 1 else 0) := by
  cases i <;> cases r <;>
    simp [stepOrSelf, step, potentialLargeY, isVB, isXY] <;>
    split_ifs <;> simp_all <;> omega

/-- Outside the Y corner the potential is large enough to pay for each
possible one-step increase at a relative cost of 16/n or 8/n. -/
theorem potentialLargeY_outside_lower (c : Config n) (hc : ¬c.inLargeY) :
    n ≤ 8 * c.potentialLargeY := by
  unfold inLargeY at hc
  unfold potentialLargeY
  have := c.sum_eq
  omega

/-- Exponential one-step compensation outside the Y corner. -/
theorem potentialLargeY_outside_compensation (hn : 0 < n) (c : Config n)
    (hc : ¬c.inLargeY) (i r : State) :
    Real.exp (-((16 : ℝ) * (if isVB i r then 1 else 0) +
      8 * (if isXY i r then 1 else 0)) / (n : ℝ)) *
      ((c.stepOrSelf i r).potentialLargeY : ℝ) ≤ (c.potentialLargeY : ℝ) := by
  let d : ℝ := 2 * (if isVB i r then 1 else 0) + (if isXY i r then 1 else 0)
  have hd : 0 ≤ d := by dsimp [d]; split_ifs <;> norm_num
  have hp : 0 ≤ (c.potentialLargeY : ℝ) := Nat.cast_nonneg _
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlower : (n : ℝ) ≤ 8 * (c.potentialLargeY : ℝ) := by
    exact_mod_cast potentialLargeY_outside_lower c hc
  have hstep : ((c.stepOrSelf i r).potentialLargeY : ℝ) ≤
      (c.potentialLargeY : ℝ) + d := by
    dsimp [d]
    norm_cast
    simpa [Nat.add_assoc] using potentialLargeY_step_charge c i r
  have hrel : ((c.stepOrSelf i r).potentialLargeY : ℝ) ≤
      (c.potentialLargeY : ℝ) * (1 + 8 * d / (n : ℝ)) := by
    apply hstep.trans
    have hmul := mul_le_mul_of_nonneg_right hlower hd
    have hd_bound : d ≤ 8 * (c.potentialLargeY : ℝ) * d / (n : ℝ) :=
      (le_div_iff₀ hnR).mpr (by nlinarith [hmul])
    calc (c.potentialLargeY : ℝ) + d ≤
        (c.potentialLargeY : ℝ) + 8 * (c.potentialLargeY : ℝ) * d / (n : ℝ) :=
          by linarith [hd_bound]
      _ = (c.potentialLargeY : ℝ) * (1 + 8 * d / (n : ℝ)) := by ring
  have hexp : ((c.stepOrSelf i r).potentialLargeY : ℝ) ≤
      (c.potentialLargeY : ℝ) * Real.exp (8 * d / (n : ℝ)) :=
    hrel.trans (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (8*d/(n:ℝ))]) hp)
  have hcancel : Real.exp (-(8 * d / (n : ℝ))) *
      ((c.potentialLargeY : ℝ) * Real.exp (8 * d / (n : ℝ))) =
      (c.potentialLargeY : ℝ) := by
    rw [mul_left_comm, ← Real.exp_add]
    simp
  have h := mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg (-(8*d/(n:ℝ))))
  rw [hcancel] at h
  convert h using 1 <;> congr 2 <;> dsimp [d] <;> ring

end Ripple.PopulationProtocol.PopProto.Config
