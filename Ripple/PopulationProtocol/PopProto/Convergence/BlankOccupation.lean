import Ripple.PopulationProtocol.PopProto.Convergence.CornerCharge

/-! # Cumulative blank-corner visits
The reciprocal opinion count is continued across region boundaries. A max
with one only makes the potential finite at the unreachable all-blank state;
on every opinionated trajectory it equals n/v exactly.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Ripple.PopulationProtocol.PopProto.Config
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

/-- Finite reciprocal potential, equal to n/v on opinionated states. -/
noncomputable def blankOccupationPotential (c : Config n) : ℝ≥0∞ :=
  (n : ℝ≥0∞) / (max 1 c.v : ℕ)

/-- One interaction reduces the opinion count by at most the XY indicator. -/
theorem v_step_charge (c : Config n) (i r : State) :
    c.v ≤ (c.stepOrSelf i r).v + (if isXY i r then 1 else 0) := by
  cases i <;> cases r <;>
    simp [stepOrSelf, step, v, isXY] <;> split_ifs <;> simp_all <;> omega

/-- The regularized potential agrees with the real reciprocal on every
state with at least one opinion. -/
theorem blankOccupationPotential_eq (c : Config n) (hv : 1 ≤ c.v) :
    blankOccupationPotential c = ENNReal.ofReal ((n : ℝ) / (c.v : ℝ)) := by
  unfold blankOccupationPotential
  rw [max_eq_right hv, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (by omega)),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-- Outside the blank corner, a possible one-opinion loss has bounded
relative cost. The larger n assumption is only used to stay away from v=1. -/
theorem blank_outside_compensation (hn : n ≥ 16) (c : Config n)
    (hc : ¬c.inLargeB) (i r : State) :
    ENNReal.ofReal (Real.exp (-16 * (if isXY i r then 1 else 0) / (n : ℝ))) *
      blankOccupationPotential (c.stepOrSelf i r) ≤ blankOccupationPotential c := by
  let j : ℕ := if isXY i r then 1 else 0
  have hj : j ≤ 1 := by dsimp [j]; split_ifs <;> omega
  have hv : n < 8 * c.v := by
    unfold inLargeB at hc
    have := c.sum_eq
    unfold v
    omega
  have hs : c.v ≤ (c.stepOrSelf i r).v + j := v_step_charge c i r
  have hv1 : 1 ≤ c.v := by omega
  have hv' : 1 ≤ (c.stepOrSelf i r).v := by omega
  have hlow : n ≤ 16 * (c.stepOrSelf i r).v := by omega
  rw [blankOccupationPotential_eq c hv1,
    blankOccupationPotential_eq (c.stepOrSelf i r) hv',
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hvR : 0 < (c.v : ℝ) := by exact_mod_cast hv1
  have hvR' : 0 < ((c.stepOrSelf i r).v : ℝ) := by exact_mod_cast hv'
  have hsR : (c.v : ℝ) ≤ ((c.stepOrSelf i r).v : ℝ) + (j : ℝ) := by exact_mod_cast hs
  have hlR : (n : ℝ) ≤ 16 * ((c.stepOrSelf i r).v : ℝ) := by exact_mod_cast hlow
  have hrel : (n : ℝ) / ((c.stepOrSelf i r).v : ℝ) ≤
      (n : ℝ) / (c.v : ℝ) * (1 + 16 * (j : ℝ) / (n : ℝ)) := by
    apply (div_le_iff₀ hvR').mpr
    have heq : (n : ℝ) / (c.v : ℝ) * (1 + 16 * (j : ℝ) / (n : ℝ)) *
        ((c.stepOrSelf i r).v : ℝ) =
        ((n : ℝ) + 16 * (j : ℝ)) * ((c.stepOrSelf i r).v : ℝ) / (c.v : ℝ) := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ hvR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsR (le_of_lt hnR),
      mul_le_mul_of_nonneg_right hlR (Nat.cast_nonneg (α := ℝ) j)]
  have hexp : (n : ℝ) / ((c.stepOrSelf i r).v : ℝ) ≤
      (n : ℝ) / (c.v : ℝ) * Real.exp (16 * (j : ℝ) / (n : ℝ)) :=
    hrel.trans (mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp (16 * (j : ℝ) / (n : ℝ))]) (by positivity))
  have h := mul_le_mul_of_nonneg_left hexp
    (Real.exp_nonneg (-(16 * (j : ℝ) / (n : ℝ))))
  have heq : Real.exp (-(16 * (j : ℝ) / (n : ℝ))) *
      ((n : ℝ) / (c.v : ℝ) * Real.exp (16 * (j : ℝ) / (n : ℝ))) =
      (n : ℝ) / (c.v : ℝ) := by
    rw [mul_left_comm, ← Real.exp_add]
    simp
  rw [heq] at h
  convert h using 1 <;> dsimp [j] <;> push_cast <;> congr 2 <;> ring

/-- The existing untruncated reciprocal drift pays the blank-corner visit
charge. Regularization can only decrease the integrand. -/
theorem blank_untruncated_moment (hn : n ≥ 2) (c : Config n)
    (hc : c ∈ activeLargeB) :
    ∫⁻ q : State × State, blankOccupationPotential (c.stepOrSelf q.1 q.2)
      ∂(c.interactionPMF hn).toMeasure ≤
      ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) * blankOccupationPotential c := by
  have h := original_lintegral_inv_v_le_largeB c hn hc
  change ∫⁻ c', (c'.v : ℝ≥0∞)⁻¹ ∂(c.stepDist hn).toMeasure ≤ _ at h
  unfold stepDist at h
  rw [← PMF.toMeasure_map _ _ Measurable.of_discrete,
    lintegral_map Measurable.of_discrete Measurable.of_discrete] at h
  have hp : ∀ c' : Config n, blankOccupationPotential c' ≤
      (n : ℝ≥0∞) * (c'.v : ℝ≥0∞)⁻¹ := by
    intro c'
    unfold blankOccupationPotential
    rw [div_eq_mul_inv]
    apply mul_le_mul_left'
    apply ENNReal.inv_le_inv.mpr
    exact_mod_cast (le_max_right 1 c'.v)
  calc _ ≤ ∫⁻ q : State × State, (n : ℝ≥0∞) *
        ((c.stepOrSelf q.1 q.2).v : ℝ≥0∞)⁻¹ ∂(c.interactionPMF hn).toMeasure :=
      lintegral_mono (fun q => hp _)
    _ = _ := lintegral_const_mul _ Measurable.of_discrete
    _ ≤ (n : ℝ≥0∞) * (ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
        (c.v : ℝ≥0∞)⁻¹) := mul_le_mul_left' h _
    _ = _ := by
      simp only [blankOccupationPotential, max_eq_right hc.2, div_eq_mul_inv]
      ring

/-- The blank-corner exponential charge is valid on every original state.
The unreachable all-blank state is handled explicitly, not added to consensus. -/
theorem blank_step_charge (hn : n ≥ 16) (c : Config n) :
    ∫⁻ q, occupationStepCharge blankOccupationPotential
      (fun c => if c ∈ activeLargeB then (1 : ℝ) / 8 else 0) 0 16 c q
      ∂(c.interactionPMF (show n ≥ 2 by omega)).toMeasure ≤ blankOccupationPotential c := by
  classical
  have hn2 : n ≥ 2 := by omega
  by_cases hc : c ∈ activeLargeB
  · have hpoint : ∀ q, occupationStepCharge blankOccupationPotential
        (fun c => if c ∈ activeLargeB then (1 : ℝ) / 8 else 0) 0 16 c q ≤
        ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
          blankOccupationPotential (c.stepOrSelf q.1 q.2) := by
      intro q
      unfold occupationStepCharge
      simp only [hc, if_true, zero_mul, sub_zero]
      apply mul_le_mul_right'
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have he : 0 ≤ (if isXY q.1 q.2 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have heq : ((1 : ℝ) / 8 - 16 * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ) =
          1 / (8 * (n : ℝ)) - 16 * (if isXY q.1 q.2 then 1 else 0) / (n : ℝ) := by ring
      rw [heq]
      apply sub_le_self
      positivity
    calc _ ≤ ∫⁻ q : State × State,
          ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
            blankOccupationPotential (c.stepOrSelf q.1 q.2)
          ∂(c.interactionPMF (show n ≥ 2 by omega)).toMeasure := lintegral_mono hpoint
      _ = _ := lintegral_const_mul _ Measurable.of_discrete
      _ ≤ ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
          (ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) * blankOccupationPotential c) :=
          mul_le_mul_left' (blank_untruncated_moment hn2 c hc) _
      _ ≤ blankOccupationPotential c := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_left (zero_le') (corner_visit_rate hn2)
  · have hpoint : ∀ q, occupationStepCharge blankOccupationPotential
        (fun c => if c ∈ activeLargeB then (1 : ℝ) / 8 else 0) 0 16 c q ≤
        blankOccupationPotential c := by
      intro q
      unfold occupationStepCharge
      simp only [hc, if_false, zero_mul, sub_zero, zero_sub]
      by_cases hlarge : c.inLargeB
      · have hv : c.v = 0 := by
          have hsmall : ¬c.v ≥ 1 := fun h => hc ⟨hlarge, h⟩
          omega
        have hb : c.allB := by
          unfold allB
          unfold v at hv
          have := c.sum_eq
          omega
        rw [allB_step_eq c hb]
        apply mul_le_of_le_one_left (zero_le')
        apply ENNReal.ofReal_le_one.mpr
        apply Real.exp_le_one_iff.mpr
        apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg' n)
        have he : 0 ≤ (if isXY q.1 q.2 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        nlinarith
      · convert blank_outside_compensation hn c hlarge q.1 q.2 using 1 <;> congr 2 <;> ring
    calc _ ≤ ∫⁻ _, blankOccupationPotential c ∂(c.interactionPMF (show n ≥ 2 by omega)).toMeasure :=
        lintegral_mono hpoint
      _ = _ := by simp

/-- Global blank-corner occupation moment, including repeated excursions. -/
theorem blank_occupation_moment (hn : n ≥ 16) (c₀ : Config n) (t : ℕ) :
    ∫⁻ a, weightedOccupation blankOccupationPotential
      (fun s => (s.blank : ℝ) / 8) 0 16 a
      ∂((occupationKernel (show n ≥ 2 by omega) ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)) ≤
        blankOccupationPotential c₀ := by
  apply weightedOccupation_iteration (show n ≥ 2 by omega) _ _
    (fun c => if c ∈ activeLargeB then (1 : ℝ) / 8 else 0) 0 16
  · intro s c
    simp only [RegionCounts.record, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    split_ifs <;> ring
  · norm_num
  · exact blank_step_charge hn

/-- Every configuration has potential at least one; this enables Markov's
inequality to bound visit counts without a carried final-state assumption. -/
theorem one_le_blankOccupationPotential (hn : n ≥ 2) (c : Config n) :
    1 ≤ blankOccupationPotential c := by
  unfold blankOccupationPotential
  have hz : ((max 1 c.v : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show max 1 c.v ≠ 0 by omega)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hz) (Or.inl (ENNReal.natCast_ne_top _))]
  simpa using (show ((max 1 c.v : ℕ) : ℝ≥0∞) ≤ (n : ℝ≥0∞) from by
    exact_mod_cast (max_le (by omega : 1 ≤ n) c.v_le_n))

end Ripple.PopulationProtocol.PopProto.Config
