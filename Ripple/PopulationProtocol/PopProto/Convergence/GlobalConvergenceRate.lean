import Ripple.PopulationProtocol.PopProto.Convergence.GlobalConvergence

/-! # Uniform exponential convergence rate
The conservative global tail simplifies to 3 n² exp(-k/(15000n)) after
4k interactions. This gives the required n log n high-probability scale.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Ripple.PopulationProtocol.PopProto.Config
variable {n : ℕ}

/-- Division by a positive natural cannot increase a nonnegative quantity. -/
theorem ennreal_div_nat_le_self (x : ℝ≥0∞) (m : ℕ) (hm : 1 ≤ m) :
    x / (m : ℝ≥0∞) ≤ x := by
  rw [div_eq_mul_inv]
  apply mul_le_of_le_one_right (zero_le')
  apply ENNReal.inv_le_one.mpr
  exact_mod_cast hm

/-- The aggregate initial occupation charge is bounded uniformly in c. -/
theorem initialOccupationBound_le (c : Config n) :
    initialOccupationBound c ≤ ((4*n+3 : ℕ) : ℝ≥0∞) := by
  have hb : blankOccupationPotential c ≤ (n : ℝ≥0∞) :=
    ennreal_div_nat_le_self _ _ (le_max_left 1 c.v)
  calc initialOccupationBound c ≤
      1 + (c.potentialLargeX : ℝ≥0∞) + (c.potentialLargeY : ℝ≥0∞) + (n : ℝ≥0∞) := by
        unfold initialOccupationBound
        gcongr
    _ ≤ _ := by
      exact_mod_cast (show 1 + c.potentialLargeX + c.potentialLargeY + n ≤ 4*n+3 from by
        unfold potentialLargeX potentialLargeY
        have := c.sum_eq
        omega)

/-- Uniform original-chain exponential tail, with no state-dependent
potentials or auxiliary process hypotheses in the conclusion. -/
theorem convergence_time_bound_exp (hn : n ≥ 16) (c₀ : Config n)
    (hop : c₀.hasOpinion) (k : ℕ) :
    ((transitionKernel (show n ≥ 2 by omega) ^ (4*k)) c₀)
      {c : Config n | ¬c.isConsensus} ≤
      ENNReal.ofReal (3*(n : ℝ)^2 * Real.exp (-(k : ℝ)/(15000*(n : ℝ)))) := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := by linarith
  let E := ENNReal.ofReal (Real.exp (-(k : ℝ)/(15000*(n : ℝ))))
  have he : ENNReal.ofReal (Real.exp (-(2*(k : ℝ)/25)/(n : ℝ))) ≤ E := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ hnp (by positivity)).mpr
    nlinarith [mul_nonneg hnp.le (Nat.cast_nonneg (α := ℝ) k)]
  have hr0 : 0 ≤ (1 : ℝ) - 1/(15000*n) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have hr1 : (1 : ℝ) - 1/(15000*n) ≤ Real.exp (-1/(15000*(n : ℝ))) := by
    simpa [neg_div, sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-1/(15000*(n : ℝ)))
  have hr : ENNReal.ofReal ((1 - 1/(15000*(n : ℝ)))^k) ≤ E := by
    apply ENNReal.ofReal_le_ofReal
    have h := pow_le_pow_left₀ hr0 hr1 k
    have heq : (Real.exp (-1/(15000*(n : ℝ))))^k =
        Real.exp (-(k : ℝ)/(15000*(n : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq] at h
    exact h
  have hp : (((n^2+2*n : ℕ) : ℝ≥0∞) / (c₀.potential : ℝ≥0∞)) ≤
      ((n^2+2*n : ℕ) : ℝ≥0∞) :=
    ennreal_div_nat_le_self _ _ (potential_pos c₀ (by omega))
  have hcoef : 4*n+3 + 2*(n^2+2*n) ≤ 3*n^2 := by
    have hmul : 16*n ≤ n*n := Nat.mul_le_mul_right n hn
    nlinarith
  calc _ ≤ ENNReal.ofReal (Real.exp (-(2*(k : ℝ)/25)/(n : ℝ))) * initialOccupationBound c₀ +
        2 * ENNReal.ofReal ((1 - 1/(15000*(n : ℝ)))^k) *
          (((n^2+2*n : ℕ) : ℝ≥0∞) / (c₀.potential : ℝ≥0∞)) :=
        convergence_time_bound hn c₀ hop k
    _ ≤ E * ((4*n+3 : ℕ) : ℝ≥0∞) + 2 * E * ((n^2+2*n : ℕ) : ℝ≥0∞) := by
        gcongr
        exact initialOccupationBound_le c₀
    _ = ((4*n+3 + 2*(n^2+2*n) : ℕ) : ℝ≥0∞) * E := by push_cast; ring
    _ ≤ ((3*n^2 : ℕ) : ℝ≥0∞) * E := by
        apply mul_le_mul_right'
        exact_mod_cast hcoef
    _ = _ := by
        dsimp [E]
        rw [ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        norm_num

/-- Polynomially small failure probability after O(n log n) interactions.
The explicit threshold can be met by taking its natural ceiling for k.
The exponent r is independent of n; no initial-majority-gap premise is needed
for consensus time. -/
theorem convergence_time_high_probability (hn : n ≥ 16) (c₀ : Config n)
    (hop : c₀.hasOpinion) (r : ℝ) (k : ℕ)
    (hk : 15000*(n : ℝ)*(Real.log (3*(n : ℝ)^2) + r*Real.log (n : ℝ)) ≤ (k : ℝ)) :
    ((transitionKernel (show n ≥ 2 by omega) ^ (4*k)) c₀)
      {c : Config n | ¬c.isConsensus} ≤ ENNReal.ofReal ((n : ℝ)^(-r)) := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := by linarith
  have hQ : 0 < 3*(n : ℝ)^2 := by positivity
  have hdiv : -(k : ℝ)/(15000*(n : ℝ)) ≤
      -(Real.log (3*(n : ℝ)^2) + r*Real.log (n : ℝ)) := by
    have h : Real.log (3*(n : ℝ)^2) + r*Real.log (n : ℝ) ≤
        (k : ℝ)/(15000*(n : ℝ)) :=
      (le_div_iff₀ (show 0 < 15000*(n : ℝ) by positivity)).mpr (by nlinarith [hk])
    simpa [neg_div] using neg_le_neg h
  have hcancel : 3*(n : ℝ)^2 * Real.exp (-Real.log (3*(n : ℝ)^2)) = 1 := by
    rw [Real.exp_neg, Real.exp_log hQ, mul_inv_cancel₀ hQ.ne']
  have heq : 3*(n : ℝ)^2 *
      Real.exp (-(Real.log (3*(n : ℝ)^2) + r*Real.log (n : ℝ))) = (n : ℝ)^(-r) := by
    rw [neg_add, Real.exp_add, ← mul_assoc, hcancel, one_mul, Real.rpow_def_of_pos hnp]
    congr 1
    ring
  apply (convergence_time_bound_exp hn c₀ hop k).trans
  apply ENNReal.ofReal_le_ofReal
  calc 3*(n : ℝ)^2 * Real.exp (-(k : ℝ)/(15000*(n : ℝ))) ≤
      3*(n : ℝ)^2 * Real.exp (-(Real.log (3*(n : ℝ)^2) + r*Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdiv) hQ.le
    _ = _ := heq

end Ripple.PopulationProtocol.PopProto.Config
