/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib

/-!
# Auxiliary lemmas for the fluctuation theorem (FIX-KURTZ2-FINAL §4, Lemmas L1–L3)

Three Mathlib-only lemmas used by the finite-dimensional central limit theorem for
density-dependent chains.  The probability spaces depend on the index `n` (one canonical record
space per population size), so every statement is about a family `P n : Measure (Ω n)`.

* `tendsto_integral_of_bounded_of_tendsto_measure` (L1): a uniformly bounded nonnegative family
  that tends to `0` in probability has integrals tending to `0`; and the complex-valued form
  `tendsto_integral_complex_of_bounded_of_tendsto_measure`.
* `tendsto_measure_mul_gt_of_tight_of_tendsto` (L2, product): tight times `o_P(1)` is `o_P(1)`;
  `tendsto_measure_sum_gt_of_forall` (L2, finite sum): a finite sum of `o_P(1)` terms is `o_P(1)`.
* `exists_taylor_modulus_on_closedBall` (L3): for a `C¹` map `F` on `Fin d → ℝ`, the first-order
  Taylor remainder on a closed ball is `≤ ε ‖y − x‖` once `‖y − x‖ ≤ δ(ε)`.
-/

namespace Ripple.Kurtz

open MeasureTheory Filter Topology Set

section DependentSpaces

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
  [∀ n, IsProbabilityMeasure (P n)]

/-- The splitting bound behind Lemma L1: if `0 ≤ Z ≤ M` a.e. then
`∫ Z ≤ η + M · P{η < Z}` for every `η ≥ 0`. -/
theorem integral_le_add_mul_measure_gt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ᵐ ω ∂μ, 0 ≤ Z ω ∧ Z ω ≤ M) {η : ℝ} (hη : 0 ≤ η) :
    ∫ ω, Z ω ∂μ ≤ η + M * (μ {ω | η < Z ω}).toReal := by
  set s : Set Ω := {ω | η < Z ω} with hs
  set t : Set Ω := toMeasurable μ s with ht
  have htm : MeasurableSet t := measurableSet_toMeasurable μ s
  have hst : s ⊆ t := subset_toMeasurable μ s
  have hμt : μ t = μ s := measure_toMeasurable s
  have hg : Integrable (fun ω => η + M * t.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const η).add (((integrable_const (1 : ℝ)).indicator htm).const_mul M)
  calc ∫ ω, Z ω ∂μ ≤ ∫ ω, (η + M * t.indicator (fun _ => (1 : ℝ)) ω) ∂μ := by
        refine integral_mono_of_nonneg ?_ hg ?_
        · filter_upwards [hbdd] with ω hω using hω.1
        · filter_upwards [hbdd] with ω hω
          by_cases hωs : ω ∈ s
          · rw [Set.indicator_of_mem (hst hωs)]
            linarith [hω.2]
          · have : Z ω ≤ η := not_lt.mp hωs
            have hind : 0 ≤ t.indicator (fun _ => (1 : ℝ)) ω :=
              Set.indicator_nonneg (fun _ _ => zero_le_one) ω
            nlinarith
    _ = η + M * (μ s).toReal := by
        rw [integral_add (integrable_const η) (((integrable_const (1 : ℝ)).indicator htm).const_mul M),
          integral_const, integral_const_mul, integral_indicator_const _ htm]
        simp [measureReal_def, hμt]

/-- **Lemma L1 (FIX-KURTZ2-FINAL).** On a family of probability spaces, if `0 ≤ Z_n ≤ M`
almost surely with one deterministic `M` and `Z_n → 0` in probability
(`P_n{η < Z_n} → 0` for every `η > 0`), then `∫ Z_n dP_n → 0`. -/
theorem tendsto_integral_of_bounded_of_tendsto_measure (Z : ∀ n, Ω n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ n, ∀ᵐ ω ∂P n, 0 ≤ Z n ω ∧ Z n ω ≤ M)
    (hprob : ∀ η > (0 : ℝ), Tendsto (fun n => P n {ω | η < Z n ω}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, Z n ω ∂P n) atTop (𝓝 0) := by
  -- work with `M + 1 > 0` to avoid the case `M = 0`
  have hM1 : 0 < M + 1 := by linarith
  have hbdd' : ∀ n, ∀ᵐ ω ∂P n, 0 ≤ Z n ω ∧ Z n ω ≤ M + 1 := fun n => by
    filter_upwards [hbdd n] with ω hω using ⟨hω.1, by linarith [hω.2]⟩
  have hnonneg : ∀ n, 0 ≤ ∫ ω, Z n ω ∂P n := fun n =>
    integral_nonneg_of_ae ((hbdd n).mono fun ω hω => hω.1)
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (hnonneg n), fun a ha => ?_⟩
  have hη : (0 : ℝ) < a / 2 := half_pos ha
  have hε : 0 < ENNReal.ofReal (a / (2 * (M + 1))) := ENNReal.ofReal_pos.mpr (by positivity)
  filter_upwards [(hprob (a / 2) hη).eventually (Iio_mem_nhds hε)] with n hn
  have hlt : (P n {ω | a / 2 < Z n ω}).toReal < a / (2 * (M + 1)) :=
    ENNReal.toReal_lt_of_lt_ofReal hn
  have hle := integral_le_add_mul_measure_gt (P n) (Z n) hM1.le (hbdd' n) hη.le
  have h2 : (M + 1) * (P n {ω | a / 2 < Z n ω}).toReal < a / 2 := by
    have := mul_lt_mul_of_pos_left hlt hM1
    rwa [show (M + 1) * (a / (2 * (M + 1))) = a / 2 by field_simp] at this
  linarith

/-- **Lemma L1, complex form.** If `‖W_n‖ ≤ M` almost surely and `‖W_n‖ → 0` in probability,
then `∫ W_n dP_n → 0` in `ℂ`. -/
theorem tendsto_integral_complex_of_bounded_of_tendsto_measure (W : ∀ n, Ω n → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ n, ∀ᵐ ω ∂P n, ‖W n ω‖ ≤ M)
    (hprob : ∀ η > (0 : ℝ), Tendsto (fun n => P n {ω | η < ‖W n ω‖}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, W n ω ∂P n) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n => ∫ ω, ‖W n ω‖ ∂P n) atTop (𝓝 0) :=
    tendsto_integral_of_bounded_of_tendsto_measure P (fun n ω => ‖W n ω‖) hM
      (fun n => by filter_upwards [hbdd n] with ω hω using ⟨norm_nonneg _, hω⟩) hprob
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => norm_integral_le_integral_norm _) hnorm

omit [∀ n, IsProbabilityMeasure (P n)] in
/-- **Lemma L2 (FIX-KURTZ2-FINAL), product form.** If `(U_n)` is tight
(`∀ ε > 0, ∃ R > 0, ∀ n, P_n{R < U_n} ≤ ε`), `V_n ≥ 0` and `V_n → 0` in probability, then
`U_n V_n → 0` in probability. -/
theorem tendsto_measure_mul_gt_of_tight_of_tendsto (U V : ∀ n, Ω n → ℝ)
    (hV0 : ∀ n ω, 0 ≤ V n ω)
    (htight : ∀ ε > (0 : ℝ), ∃ R > (0 : ℝ), ∀ n, P n {ω | R < U n ω} ≤ ENNReal.ofReal ε)
    (hV : ∀ η > (0 : ℝ), Tendsto (fun n => P n {ω | η < V n ω}) atTop (𝓝 0)) :
    ∀ δ > (0 : ℝ), Tendsto (fun n => P n {ω | δ < U n ω * V n ω}) atTop (𝓝 0) := by
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact Eventually.of_forall fun n => hεtop ▸ le_top
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hε2top : ε / 2 ≠ ⊤ := ENNReal.div_ne_top hεtop (by norm_num)
  have hε2real : 0 < (ε / 2).toReal := ENNReal.toReal_pos hε2.ne' hε2top
  obtain ⟨R, hR, hRU⟩ := htight _ hε2real
  have hRU' : ∀ n, P n {ω | R < U n ω} ≤ ε / 2 := fun n => by
    have := hRU n
    rwa [ENNReal.ofReal_toReal hε2top] at this
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp (hV (δ / R) (div_pos hδ hR))) (ε / 2) hε2]
    with n hn
  have hsub : {ω | δ < U n ω * V n ω} ⊆ {ω | R < U n ω} ∪ {ω | δ / R < V n ω} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hnot
    have h1 : U n ω * V n ω ≤ R * V n ω := mul_le_mul_of_nonneg_right hnot.1 (hV0 n ω)
    have h2 : R * V n ω ≤ R * (δ / R) := mul_le_mul_of_nonneg_left hnot.2 hR.le
    rw [mul_div_cancel₀ _ hR.ne'] at h2
    exact absurd hω (not_lt.mpr (h1.trans h2))
  calc P n {ω | δ < U n ω * V n ω}
      ≤ P n ({ω | R < U n ω} ∪ {ω | δ / R < V n ω}) := measure_mono hsub
    _ ≤ P n {ω | R < U n ω} + P n {ω | δ / R < V n ω} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hRU' n) hn
    _ = ε := ENNReal.add_halves ε

omit [∀ n, IsProbabilityMeasure (P n)] in
/-- **Lemma L2 (FIX-KURTZ2-FINAL), finite-sum form.** If each of finitely many families
`W_{n,j}` tends to `0` in probability, so does `Σ_j W_{n,j}`. -/
theorem tendsto_measure_sum_gt_of_forall {J : Type*} [Fintype J] (W : ∀ n, J → Ω n → ℝ)
    (hW : ∀ j, ∀ η > (0 : ℝ), Tendsto (fun n => P n {ω | η < |W n j ω|}) atTop (𝓝 0)) :
    ∀ δ > (0 : ℝ), Tendsto (fun n => P n {ω | δ < |∑ j, W n j ω|}) atTop (𝓝 0) := by
  intro δ hδ
  rcases isEmpty_or_nonempty J with hJ | hJ
  · have : ∀ n, {ω | δ < |∑ j, W n j ω|} = (∅ : Set (Ω n)) := fun n => by
      ext ω
      simp [Finset.univ_eq_empty, not_lt.mpr hδ.le]
    simp only [this, measure_empty]
    exact tendsto_const_nhds
  have hm : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  set δ' : ℝ := δ / Fintype.card J with hδ'
  have hδ'pos : 0 < δ' := div_pos hδ hm
  have hsub : ∀ n, {ω | δ < |∑ j, W n j ω|} ⊆ ⋃ j, {ω | δ' < |W n j ω|} := by
    intro n ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hnot
    have : |∑ j, W n j ω| ≤ ∑ j, |W n j ω| := Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ j, |W n j ω| ≤ ∑ _j : J, δ' := Finset.sum_le_sum fun j _ => hnot j
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hδ',
      mul_div_cancel₀ _ hm.ne'] at h2
    exact absurd hω (not_lt.mpr (this.trans h2))
  have hsum : Tendsto (fun n => ∑ j : J, P n {ω | δ' < |W n j ω|}) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset J) fun j _ => hW j δ' hδ'pos
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => by simp) fun n => ?_
  exact (measure_mono (hsub n)).trans (measure_iUnion_fintype_le _ _)

end DependentSpaces

/-- **Lemma L3 (FIX-KURTZ2-FINAL): uniform Taylor remainder on a closed ball.** For a `C¹` map
`F : (Fin d → ℝ) → (Fin d → ℝ)` and every radius `R`, for every `ε > 0` there is `δ > 0` such
that `‖F y − F x − DF(x)(y − x)‖ ≤ ε ‖y − x‖` whenever `‖x‖ ≤ R`, `‖y‖ ≤ R` and `‖y − x‖ ≤ δ`.
(The modulus `ω` of (4.20)–(4.21) is this `ε ↦ δ(ε)` relation.) -/
theorem exists_taylor_modulus_on_closedBall {d : ℕ} {F : (Fin d → ℝ) → (Fin d → ℝ)}
    (hF : ContDiff ℝ 1 F) (R : ℝ) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x y : Fin d → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R → ‖y - x‖ ≤ δ →
      ‖F y - F x - fderiv ℝ F x (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  have hcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  have hdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have hunif : UniformContinuousOn (fderiv ℝ F) (Metric.closedBall (0 : Fin d → ℝ) R) :=
    (isCompact_closedBall (0 : Fin d → ℝ) R).uniformContinuousOn_of_continuous hcont.continuousOn
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.mp hunif ε hε
  refine ⟨δ / 2, half_pos hδ, fun x y hx hy hxy => ?_⟩
  have hxK : x ∈ Metric.closedBall (0 : Fin d → ℝ) R := by simpa using hx
  have hyK : y ∈ Metric.closedBall (0 : Fin d → ℝ) R := by simpa using hy
  -- the convex neighbourhood of `x` on which `DF` is `ε`-close to `DF(x)`
  set s : Set (Fin d → ℝ) := Metric.closedBall x (δ / 2) ∩ Metric.closedBall (0 : Fin d → ℝ) R
    with hs
  have hsconv : Convex ℝ s := (convex_closedBall x (δ / 2)).inter (convex_closedBall 0 R)
  have hxs : x ∈ s := ⟨Metric.mem_closedBall_self (half_pos hδ).le, hxK⟩
  have hys : y ∈ s := ⟨by rw [Metric.mem_closedBall, dist_eq_norm]; exact hxy, hyK⟩
  have hderiv : ∀ z ∈ s, HasFDerivWithinAt (fun z => F z - fderiv ℝ F x z)
      (fderiv ℝ F z - fderiv ℝ F x) s z := fun z _ =>
    ((hdiff z).hasFDerivAt.sub (fderiv ℝ F x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ s, ‖fderiv ℝ F z - fderiv ℝ F x‖ ≤ ε := by
    intro z hz
    have hzx : dist z x < δ := lt_of_le_of_lt (Metric.mem_closedBall.mp hz.1) (half_lt_self hδ)
    have := hδε z hz.2 x hxK hzx
    rw [dist_eq_norm] at this
    exact this.le
  have := hsconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound hxs hys
  have heq : F y - F x - fderiv ℝ F x (y - x) =
      (F y - fderiv ℝ F x y) - (F x - fderiv ℝ F x x) := by
    rw [map_sub]; abel
  rw [heq]
  exact this

end Ripple.Kurtz
