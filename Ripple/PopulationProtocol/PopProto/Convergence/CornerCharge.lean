import Ripple.PopulationProtocol.PopProto.Convergence.CornerOccupation
import Ripple.PopulationProtocol.PopProto.Convergence.WeightedOccupation

/-! # Original-chain corner charge inequalities
The compensating interaction charge pays for potential growth outside a
corner. Inside the corner, multiplicative drift pays for its visit count.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Ripple.PopulationProtocol.PopProto.Config
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

/-- The corner contraction pays for an exponential visit charge of 1/(8n). -/
theorem corner_visit_rate (hn : n ≥ 2) :
    ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
      ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) ≤ 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm1 : 0 < (n : ℝ) - 1 := by linarith
  have hx : 1 / (8 * (n : ℝ)) ≤ 13 / (64 * ((n : ℝ) - 1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_one.mpr
  have he := Real.add_one_le_exp (-(1 / (8 * (n : ℝ))))
  have hmul := mul_le_mul_of_nonneg_left he (Real.exp_nonneg (1 / (8 * (n : ℝ))))
  have hcancel : Real.exp (1 / (8 * (n : ℝ))) * Real.exp (-(1 / (8 * (n : ℝ)))) = 1 := by
    rw [← Real.exp_add]; simp
  rw [hcancel] at hmul
  nlinarith [mul_nonneg (Real.exp_nonneg (1 / (8 * (n : ℝ))))
    (sub_nonneg.mpr hx)]

/-- Translate a natural-valued potential's real integral estimate into the
nonnegative integral used by the occupation process. -/
theorem corner_nat_lintegral_bound (μ : Measure (Config n))
    (φ : Config n → ℕ) (r : ℝ) (hr : 0 ≤ r) (c : Config n)
    (hfi : Integrable (fun c' => (φ c' : ℝ)) μ)
    (h : ∫ c', (φ c' : ℝ) ∂μ ≤ r * (φ c : ℝ)) :
    ∫⁻ c', (φ c' : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal r * (φ c : ℝ≥0∞) := by
  simp_rw [show ∀ c' : Config n, (φ c' : ℝ≥0∞) = ENNReal.ofReal (φ c' : ℝ) from
    fun c' => (ENNReal.ofReal_natCast (φ c')).symm]
  rw [← ofReal_integral_eq_lintegral_ofReal hfi
    (ae_of_all _ fun c' => Nat.cast_nonneg (φ c'))]
  rw [← ENNReal.ofReal_mul hr]
  exact ENNReal.ofReal_le_ofReal h

/-- The corner rate is nonnegative for every nondegenerate population. -/
theorem corner_rate_nonneg (hn : n ≥ 2) :
    0 ≤ (1 : ℝ) - 13 / (64 * ((n : ℝ) - 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm1 : 0 < (n : ℝ) - 1 := by linarith
  apply sub_nonneg.mpr
  apply (div_le_one (by positivity)).mpr
  nlinarith

/-- Original scheduler expectation of the untruncated X-corner potential. -/
theorem cornerX_untruncated_moment (hn : n ≥ 2) (c : Config n)
    (hc : c ∈ activeLargeX) :
    ∫⁻ q : State × State, ((c.stepOrSelf q.1 q.2).potentialLargeX : ℝ≥0∞)
      ∂(c.interactionPMF hn).toMeasure ≤
      ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeX : ℝ≥0∞) := by
  have h := corner_nat_lintegral_bound (c.stepDist hn).toMeasure
    Config.potentialLargeX _ (corner_rate_nonneg hn) c
    (by
      apply Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
        (4 * (n : ℝ) + 1)
      exact ae_of_all _ (fun c' => by
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast (show c'.potentialLargeX ≤ 4 * n + 1 from by
          unfold potentialLargeX
          have := c'.sum_eq
          omega)))
    (expected_potentialLargeX_le c hc.1 hn hc.2)
  unfold stepDist at h
  rw [← PMF.toMeasure_map _ _ Measurable.of_discrete,
    lintegral_map Measurable.of_discrete Measurable.of_discrete] at h
  exact h

/-- The full X-corner charge is a one-step supermartingale on every
configuration, including region exits, returns and consensus endpoints. -/
theorem cornerX_step_charge (hn : n ≥ 2) (c : Config n) :
    ∫⁻ q, occupationStepCharge (fun c : Config n => (c.potentialLargeX : ℝ≥0∞))
      (fun c => if c ∈ activeLargeX then (1 : ℝ) / 8 else 0) 16 8 c q
      ∂(c.interactionPMF hn).toMeasure ≤ (c.potentialLargeX : ℝ≥0∞) := by
  classical
  let e : State × State → ℝ := fun q =>
    ((16 : ℝ) * (if isVB q.1 q.2 then 1 else 0) +
      8 * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ)
  have he : ∀ q, 0 ≤ e q := by
    intro q; dsimp [e]; positivity
  by_cases hc : c ∈ activeLargeX
  · have hpoint : ∀ q, occupationStepCharge
        (fun c : Config n => (c.potentialLargeX : ℝ≥0∞))
        (fun c => if c ∈ activeLargeX then (1 : ℝ) / 8 else 0) 16 8 c q ≤
        ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
          ((c.stepOrSelf q.1 q.2).potentialLargeX : ℝ≥0∞) := by
      intro q
      unfold occupationStepCharge
      simp only [hc, if_true]
      apply mul_le_mul_right'
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have heq : ((1 : ℝ) / 8 - 16 * (if isVB q.1 q.2 then 1 else 0) -
          8 * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ) =
          1 / (8 * (n : ℝ)) - e q := by dsimp [e]; ring
      rw [heq]
      exact sub_le_self _ (he q)
    calc _ ≤ ∫⁻ q : State × State,
          ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
            ((c.stepOrSelf q.1 q.2).potentialLargeX : ℝ≥0∞)
          ∂(c.interactionPMF hn).toMeasure := lintegral_mono hpoint
      _ = _ := lintegral_const_mul _ Measurable.of_discrete
      _ ≤ ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
          (ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
            (c.potentialLargeX : ℝ≥0∞)) :=
          mul_le_mul_left' (cornerX_untruncated_moment hn c hc) _
      _ ≤ (c.potentialLargeX : ℝ≥0∞) := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_left (zero_le') (corner_visit_rate hn)
  · have hpoint : ∀ q, occupationStepCharge
        (fun c : Config n => (c.potentialLargeX : ℝ≥0∞))
        (fun c => if c ∈ activeLargeX then (1 : ℝ) / 8 else 0) 16 8 c q ≤
        (c.potentialLargeX : ℝ≥0∞) := by
      intro q
      unfold occupationStepCharge
      simp only [hc, if_false]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      by_cases hlarge : c.inLargeX
      · have hz : c.b_count + c.y_count = 0 := by
          have hsmall : ¬(c.b_count + c.y_count ≥ 1) := fun h => hc ⟨hlarge, h⟩
          omega
        have hcons : c.allX := by
          unfold allX
          have := c.sum_eq
          omega
        rw [allX_step_eq c hcons]
        have hexp : Real.exp ((0 - 16 * (if isVB q.1 q.2 then 1 else 0) -
            8 * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ)) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have hzero : (0 - 16 * (if isVB q.1 q.2 then 1 else 0) -
              8 * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ) = -e q := by
            dsimp [e]; ring
          rw [hzero]
          exact neg_nonpos.mpr (he q)
        nlinarith [mul_nonneg (sub_nonneg.mpr hexp)
          (Nat.cast_nonneg (α := ℝ) c.potentialLargeX)]
      · convert potentialLargeX_outside_compensation (by omega) c hlarge q.1 q.2 using 1 <;>
          congr 2 <;> ring
    calc _ ≤ ∫⁻ _, (c.potentialLargeX : ℝ≥0∞) ∂(c.interactionPMF hn).toMeasure :=
        lintegral_mono hpoint
      _ = _ := by simp

/-- All X-corner visits, including repeated visits, have the claimed
exponential moment bound on the original occupation chain. -/
theorem cornerX_occupation_moment (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    ∫⁻ a, weightedOccupation (fun c : Config n => (c.potentialLargeX : ℝ≥0∞))
      (fun s => (s.left : ℝ) / 8) 16 8 a
      ∂((occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)) ≤
        (c₀.potentialLargeX : ℝ≥0∞) := by
  apply weightedOccupation_iteration hn _ _
    (fun c => if c ∈ activeLargeX then (1 : ℝ) / 8 else 0) 16 8
  · intro s c
    simp only [RegionCounts.record, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    split_ifs <;> ring
  · norm_num
  · exact cornerX_step_charge hn

/-- Original scheduler expectation of the untruncated Y-corner potential. -/
theorem cornerY_untruncated_moment (hn : n ≥ 2) (c : Config n)
    (hc : c ∈ activeLargeY) :
    ∫⁻ q : State × State, ((c.stepOrSelf q.1 q.2).potentialLargeY : ℝ≥0∞)
      ∂(c.interactionPMF hn).toMeasure ≤
      ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) * (c.potentialLargeY : ℝ≥0∞) := by
  have h := corner_nat_lintegral_bound (c.stepDist hn).toMeasure
    Config.potentialLargeY _ (corner_rate_nonneg hn) c
    (by
      apply Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
        (4 * (n : ℝ) + 1)
      exact ae_of_all _ (fun c' => by
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast (show c'.potentialLargeY ≤ 4 * n + 1 from by
          unfold potentialLargeY
          have := c'.sum_eq
          omega)))
    (expected_potentialLargeY_le c hc.1 hn hc.2)
  unfold stepDist at h
  rw [← PMF.toMeasure_map _ _ Measurable.of_discrete,
    lintegral_map Measurable.of_discrete Measurable.of_discrete] at h
  exact h

/-- The full Y-corner charge is a one-step supermartingale on every
configuration, including region exits, returns and consensus endpoints. -/
theorem cornerY_step_charge (hn : n ≥ 2) (c : Config n) :
    ∫⁻ q, occupationStepCharge (fun c : Config n => (c.potentialLargeY : ℝ≥0∞))
      (fun c => if c ∈ activeLargeY then (1 : ℝ) / 8 else 0) 16 8 c q
      ∂(c.interactionPMF hn).toMeasure ≤ (c.potentialLargeY : ℝ≥0∞) := by
  classical
  let e : State × State → ℝ := fun q =>
    ((16 : ℝ) * (if isVB q.1 q.2 then 1 else 0) +
      8 * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ)
  have he : ∀ q, 0 ≤ e q := by
    intro q; dsimp [e]; positivity
  by_cases hc : c ∈ activeLargeY
  · have hpoint : ∀ q, occupationStepCharge
        (fun c : Config n => (c.potentialLargeY : ℝ≥0∞))
        (fun c => if c ∈ activeLargeY then (1 : ℝ) / 8 else 0) 16 8 c q ≤
        ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
          ((c.stepOrSelf q.1 q.2).potentialLargeY : ℝ≥0∞) := by
      intro q
      unfold occupationStepCharge
      simp only [hc, if_true]
      apply mul_le_mul_right'
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have heq : ((1 : ℝ) / 8 - 16 * (if isVB q.1 q.2 then 1 else 0) -
          8 * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ) =
          1 / (8 * (n : ℝ)) - e q := by dsimp [e]; ring
      rw [heq]
      exact sub_le_self _ (he q)
    calc _ ≤ ∫⁻ q : State × State,
          ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
            ((c.stepOrSelf q.1 q.2).potentialLargeY : ℝ≥0∞)
          ∂(c.interactionPMF hn).toMeasure := lintegral_mono hpoint
      _ = _ := lintegral_const_mul _ Measurable.of_discrete
      _ ≤ ENNReal.ofReal (Real.exp (1 / (8 * (n : ℝ)))) *
          (ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
            (c.potentialLargeY : ℝ≥0∞)) :=
          mul_le_mul_left' (cornerY_untruncated_moment hn c hc) _
      _ ≤ (c.potentialLargeY : ℝ≥0∞) := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_left (zero_le') (corner_visit_rate hn)
  · have hpoint : ∀ q, occupationStepCharge
        (fun c : Config n => (c.potentialLargeY : ℝ≥0∞))
        (fun c => if c ∈ activeLargeY then (1 : ℝ) / 8 else 0) 16 8 c q ≤
        (c.potentialLargeY : ℝ≥0∞) := by
      intro q
      unfold occupationStepCharge
      simp only [hc, if_false]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      by_cases hlarge : c.inLargeY
      · have hz : c.b_count + c.x_count = 0 := by
          have hsmall : ¬(c.b_count + c.x_count ≥ 1) := fun h => hc ⟨hlarge, h⟩
          omega
        have hcons : c.allY := by
          unfold allY
          have := c.sum_eq
          omega
        rw [allY_step_eq c hcons]
        have hexp : Real.exp ((0 - 16 * (if isVB q.1 q.2 then 1 else 0) -
            8 * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ)) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have hzero : (0 - 16 * (if isVB q.1 q.2 then 1 else 0) -
              8 * (if isXY q.1 q.2 then 1 else 0)) / (n : ℝ) = -e q := by
            dsimp [e]; ring
          rw [hzero]
          exact neg_nonpos.mpr (he q)
        nlinarith [mul_nonneg (sub_nonneg.mpr hexp)
          (Nat.cast_nonneg (α := ℝ) c.potentialLargeY)]
      · convert potentialLargeY_outside_compensation (by omega) c hlarge q.1 q.2 using 1 <;>
          congr 2 <;> ring
    calc _ ≤ ∫⁻ _, (c.potentialLargeY : ℝ≥0∞) ∂(c.interactionPMF hn).toMeasure :=
        lintegral_mono hpoint
      _ = _ := by simp

/-- All Y-corner visits, including repeated visits, have the claimed
exponential moment bound on the original occupation chain. -/
theorem cornerY_occupation_moment (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    ∫⁻ a, weightedOccupation (fun c : Config n => (c.potentialLargeY : ℝ≥0∞))
      (fun s => (s.right : ℝ) / 8) 16 8 a
      ∂((occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)) ≤
        (c₀.potentialLargeY : ℝ≥0∞) := by
  apply weightedOccupation_iteration hn _ _
    (fun c => if c ∈ activeLargeY then (1 : ℝ) / 8 else 0) 16 8
  · intro s c
    simp only [RegionCounts.record, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    split_ifs <;> ring
  · norm_num
  · exact cornerY_step_charge hn

end Ripple.PopulationProtocol.PopProto.Config
