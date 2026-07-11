/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.CTMC.DensityDependentAbsorbing
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Frozen Random-Index Doob Infrastructure

This file starts the absorbing-aware analogue of
`Ripple.CTMC.RandomIndexDoob`.  The key difference is that the predictable
one-step compensators are guarded at absorbing states: if the current exit
rate is zero, the compensator summand is zero instead of dividing by zero.

The canonical absorbing step kernel is `dirac (0, current_state)`, so after
absorption the jump-index readout is constant and the scaled jump increment is
zero.  The guarded compensator makes the centered increment zero there too.
-/

namespace ProbabilityTheory

open MeasureTheory MeasureTheory.Measure Set

private theorem integral_exp_neg_mul_Ioc_zero {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    ∫ t in Set.Ioc (0 : ℝ) a, Real.exp (-(r * t)) =
      (1 - Real.exp (-(r * a))) / r := by
  have hint : ∫ t in (0)..a, Real.exp (-(r * t)) =
      (1 - Real.exp (-(r * a))) / r := by
    let F : ℝ → ℝ := fun t => -(Real.exp (-(r * t)) / r)
    have hderiv :
        ∀ t ∈ Set.uIcc (0 : ℝ) a, HasDerivAt F (Real.exp (-(r * t))) t := by
      intro t _ht
      dsimp [F]
      have h1 : HasDerivAt (fun y : ℝ => -(r * y)) (-r) t := by
        simpa [neg_mul] using (hasDerivAt_id t).const_mul (-r)
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(r * y)))
          (Real.exp (-(r * t)) * (-r)) t := by
        simpa using (Real.hasDerivAt_exp (-(r * t))).comp t h1
      have h3 : HasDerivAt (fun y : ℝ => Real.exp (-(r * y)) / r)
          ((Real.exp (-(r * t)) * (-r)) / r) t := by
        exact h2.div_const r
      have h4 : HasDerivAt (fun y : ℝ => -(Real.exp (-(r * y)) / r))
          (-((Real.exp (-(r * t)) * (-r)) / r)) t := by
        exact h3.neg
      convert h4 using 1
      field_simp [hr.ne']
    have hcont : Continuous fun t : ℝ => Real.exp (-(r * t)) :=
      Real.continuous_exp.comp (by fun_prop : Continuous fun t : ℝ => -(r * t))
    have hInt : IntervalIntegrable (fun t : ℝ => Real.exp (-(r * t))) volume 0 a :=
      hcont.intervalIntegrable 0 a
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
    dsimp [F] at h
    rw [h]
    field_simp [hr.ne']
    simp
    ring
  rw [← intervalIntegral.integral_of_le ha]
  exact hint

theorem expMeasure_Iic_zero {r : ℝ} (hr : 0 < r) :
    expMeasure r (Set.Iic 0) = 0 := by
  letI := isProbabilityMeasure_expMeasure hr
  have hcdf := cdf_expMeasure_eq hr 0
  have hreal : (expMeasure r).real (Set.Iic 0) = 0 := by
    rw [← cdf_eq_real (expMeasure r) 0]
    simpa using hcdf
  exact (MeasureTheory.measureReal_eq_zero_iff).mp hreal

theorem expMeasure_pos_ae {r : ℝ} (hr : 0 < r) :
    ∀ᵐ t ∂expMeasure r, 0 < t := by
  have hzero := expMeasure_Iic_zero hr
  have hnot : ∀ᵐ t ∂expMeasure r, t ∉ Set.Iic 0 :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hnot] with t ht
  exact lt_of_not_ge ht

theorem expMeasure_real_Ici_eq {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    (expMeasure r).real (Set.Ici t) = Real.exp (-(r * t)) := by
  let μ := expMeasure r
  letI := isProbabilityMeasure_expMeasure hr
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsFiniteMeasure μ := by infer_instance
  have hno : NoAtoms μ := by
    dsimp [μ]
    rw [expMeasure, gammaMeasure]
    infer_instance
  have hreal_eq : μ.real (Set.Ici t) = μ.real (Set.Ioi t) := by
    exact measureReal_congr (Ioi_ae_eq_Ici (μ := μ) (a := t)).symm
  rw [hreal_eq]
  have hcdf := cdf_expMeasure_eq hr t
  have hreal_iic : μ.real (Set.Iic t) = 1 - Real.exp (-(r * t)) := by
    rw [← cdf_eq_real μ t]
    simpa [μ, ht] using hcdf
  have hcompl : Set.Ioi t = (Set.Iic t)ᶜ := by
    ext x
    simp
  rw [hcompl]
  have hsum :=
    measureReal_add_measureReal_compl (μ := μ) (s := Set.Iic t) measurableSet_Iic
  rw [hreal_iic] at hsum
  have huniv : μ.real Set.univ = 1 := by simp [μ]
  rw [huniv] at hsum
  linarith

theorem integral_expMeasure_min {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    ∫ x : ℝ, min x a ∂expMeasure r =
      (1 - Real.exp (-(r * a))) / r := by
  let μ := expMeasure r
  letI := isProbabilityMeasure_expMeasure hr
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsFiniteMeasure μ := by infer_instance
  let f : ℝ → ℝ := fun x => min x a
  have hf_int : Integrable f μ := by
    have hmeas : AEStronglyMeasurable f μ :=
      (continuous_id.min continuous_const).aestronglyMeasurable
    have hdom : Integrable (fun x : ℝ => ‖x‖ + ‖a‖) μ := by
      exact (integrable_id_expMeasure hr).norm.add (integrable_const _)
    refine hdom.mono' hmeas ?_
    filter_upwards with x
    calc
      ‖f x‖ = |min x a| := rfl
      _ ≤ max |x| |a| := abs_min_le_max_abs_abs
      _ ≤ |x| + |a| := max_le_add_of_nonneg (abs_nonneg x) (abs_nonneg a)
      _ = ‖x‖ + ‖a‖ := by simp [Real.norm_eq_abs]
  have hf_nonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [expMeasure_pos_ae hr] with x hx
    exact le_min (le_of_lt hx) ha
  have hf_bdd : f ≤ᵐ[μ] fun _ => a := by
    filter_upwards with x
    exact min_le_right x a
  have hlayer := hf_int.integral_eq_integral_Ioc_meas_le hf_nonneg hf_bdd
  rw [hlayer]
  calc
    ∫ t in Set.Ioc (0 : ℝ) a, μ.real {x | t ≤ f x}
        = ∫ t in Set.Ioc (0 : ℝ) a, Real.exp (-(r * t)) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          change μ.real {x : ℝ | t ≤ f x} = Real.exp (-(r * t))
          have ht0 : 0 ≤ t := le_of_lt ht.1
          have hta : t ≤ a := ht.2
          have hset : {x : ℝ | t ≤ f x} = Set.Ici t := by
            ext x
            constructor
            · intro hx
              change t ≤ min x a at hx
              exact (le_min_iff.mp hx).1
            · intro hx
              change t ≤ min x a
              exact le_min hx hta
          rw [hset]
          exact expMeasure_real_Ici_eq hr ht0
    _ = (1 - Real.exp (-(r * a))) / r := integral_exp_neg_mul_Ioc_zero hr ha

theorem integrable_expMeasure_min_sq {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    Integrable (fun x : ℝ => (min x a) ^ 2) (expMeasure r) := by
  let μ := expMeasure r
  letI := isProbabilityMeasure_expMeasure hr
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsFiniteMeasure μ := by infer_instance
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (min x a) ^ 2) μ :=
    ((continuous_id.min continuous_const).pow 2).aestronglyMeasurable
  have hdom : Integrable (fun _ : ℝ => a ^ 2) μ := integrable_const _
  refine hdom.mono' hmeas ?_
  filter_upwards [expMeasure_pos_ae hr] with x hx
  have hmin_nonneg : 0 ≤ min x a := le_min (le_of_lt hx) ha
  have hmin_le_a : min x a ≤ a := min_le_right x a
  have hsq : (min x a) ^ 2 ≤ a ^ 2 :=
    sq_le_sq' (by nlinarith) hmin_le_a
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (min x a))] using hsq

private theorem integral_two_mul_self_mul_exp_neg_mul_Ioc_zero
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    ∫ t in Set.Ioc (0 : ℝ) a, (2 : ℝ) * t * Real.exp (-(r * t)) =
      (2 / r ^ 2) * (1 - Real.exp (-(r * a)) * (1 + r * a)) := by
  have hint : ∫ t in (0)..a, (2 : ℝ) * t * Real.exp (-(r * t)) =
      (2 / r ^ 2) * (1 - Real.exp (-(r * a)) * (1 + r * a)) := by
    let F : ℝ → ℝ := fun t =>
      -(t * ((2 / r) * Real.exp (-(r * t)))) -
        (2 / r ^ 2) * Real.exp (-(r * t))
    have hderiv :
        ∀ t ∈ Set.uIcc (0 : ℝ) a,
          HasDerivAt F ((2 : ℝ) * t * Real.exp (-(r * t))) t := by
      intro t _ht
      dsimp [F]
      have hlin : HasDerivAt (fun y : ℝ => -(r * y)) (-r) t := by
        simpa [neg_mul] using (hasDerivAt_id t).const_mul (-r)
      have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(r * y)))
          (Real.exp (-(r * t)) * (-r)) t := by
        simpa using (Real.hasDerivAt_exp (-(r * t))).comp t hlin
      have hterm1 :
          HasDerivAt
            (fun y : ℝ => y * ((2 / r) * Real.exp (-(r * y))))
            (1 * ((2 / r) * Real.exp (-(r * t))) +
              t * ((2 / r) * (Real.exp (-(r * t)) * (-r)))) t := by
        simpa using (hasDerivAt_id t).mul (hexp.const_mul (2 / r))
      have hterm2 :
          HasDerivAt
            (fun y : ℝ => (2 / r ^ 2) * Real.exp (-(r * y)))
            ((2 / r ^ 2) * (Real.exp (-(r * t)) * (-r))) t :=
        hexp.const_mul (2 / r ^ 2)
      have hFder : HasDerivAt F
          (-(1 * ((2 / r) * Real.exp (-(r * t))) +
              t * ((2 / r) * (Real.exp (-(r * t)) * (-r)))) -
            ((2 / r ^ 2) * (Real.exp (-(r * t)) * (-r)))) t := by
        exact hterm1.neg.sub hterm2
      convert hFder using 1
      field_simp [hr.ne']
      ring
    have hcont : Continuous fun t : ℝ =>
        (2 : ℝ) * t * Real.exp (-(r * t)) := by
      fun_prop
    have hInt :
        IntervalIntegrable
          (fun t : ℝ => (2 : ℝ) * t * Real.exp (-(r * t))) volume 0 a :=
      hcont.intervalIntegrable 0 a
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
    dsimp [F] at h
    rw [h]
    field_simp [hr.ne']
    simp [Real.exp_zero]
    ring
  rw [← intervalIntegral.integral_of_le ha]
  exact hint

private theorem integral_expMeasure_min_sq_rhs {r a : ℝ} (hr : 0 < r) :
    let μ := expMeasure r
    let f : ℝ → ℝ := fun x => min x a
    ENNReal.toReal
        (∫⁻ t in Set.Ioi (0 : ℝ),
          μ {x : ℝ | t ≤ f x} * ENNReal.ofReal ((2 : ℝ) * t)) =
      ∫ t in Set.Ioc (0 : ℝ) a, (2 : ℝ) * t * Real.exp (-(r * t)) := by
  intro μ f
  letI := isProbabilityMeasure_expMeasure hr
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsFiniteMeasure μ := by infer_instance
  let G : ℝ → ℝ := fun t => μ.real {x : ℝ | t ≤ f x} * ((2 : ℝ) * t)
  have hG_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg measureReal_nonneg
      (mul_nonneg (by norm_num) (le_of_lt ht))
  have hG_meas : AEStronglyMeasurable G (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have htail_meas : Measurable fun t : ℝ => μ.real {x : ℝ | t ≤ f x} := by
      refine Measurable.ennreal_toReal ?_
      exact Antitone.measurable
        (fun s t hst => measure_mono fun _ hx => le_trans hst hx)
    exact (htail_meas.mul (measurable_const.mul measurable_id)).aestronglyMeasurable
  have hright_lint_eq :
      (∫⁻ t in Set.Ioi (0 : ℝ),
          μ {x : ℝ | t ≤ f x} * ENNReal.ofReal ((2 : ℝ) * t)) =
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (G t) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    have hμfin : μ {x : ℝ | t ≤ f x} ≠ ⊤ :=
      measure_ne_top μ {x : ℝ | t ≤ f x}
    change μ {x : ℝ | t ≤ f x} * ENNReal.ofReal ((2 : ℝ) * t) =
      ENNReal.ofReal (μ.real {x : ℝ | t ≤ f x} * ((2 : ℝ) * t))
    rw [measureReal_def]
    rw [← ENNReal.ofReal_toReal hμfin]
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  have hright_real :
      ENNReal.toReal
          (∫⁻ t in Set.Ioi (0 : ℝ),
            μ {x : ℝ | t ≤ f x} * ENNReal.ofReal ((2 : ℝ) * t)) =
        ∫ t in Set.Ioi (0 : ℝ), G t := by
    rw [hright_lint_eq]
    exact (integral_eq_lintegral_of_nonneg_ae hG_nonneg hG_meas).symm
  rw [hright_real]
  have hrestrict :
      ∫ t in Set.Ioi (0 : ℝ), G t = ∫ t in Set.Ioc (0 : ℝ) a, G t := by
    rw [setIntegral_eq_of_subset_of_ae_diff_eq_zero
      nullMeasurableSet_Ioi Ioc_subset_Ioi_self]
    exact Filter.Eventually.of_forall fun t ht => by
      have htpos : 0 < t := ht.1
      have hta : a < t := by
        by_contra hnot
        exact ht.2 ⟨htpos, le_of_not_gt hnot⟩
      have hempty : {x : ℝ | t ≤ f x} = ∅ := by
        ext x
        simp [f]
        intro _htx
        have hfa : f x ≤ a := min_le_right x a
        linarith
      simp [G, hempty]
  rw [hrestrict]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht0 : 0 ≤ t := le_of_lt ht.1
  have hta : t ≤ a := ht.2
  have hset : {x : ℝ | t ≤ f x} = Set.Ici t := by
    ext x
    constructor
    · intro hx
      change t ≤ min x a at hx
      exact (le_min_iff.mp hx).1
    · intro hx
      change t ≤ min x a
      exact le_min hx hta
  change μ.real {x : ℝ | t ≤ f x} * ((2 : ℝ) * t) =
    (2 : ℝ) * t * Real.exp (-(r * t))
  rw [hset]
  rw [show μ.real (Set.Ici t) = Real.exp (-(r * t)) by
    simpa [μ] using expMeasure_real_Ici_eq hr ht0]
  ring

theorem integral_expMeasure_min_sq {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    ∫ x : ℝ, (min x a) ^ 2 ∂expMeasure r =
      ∫ t in Set.Ioc (0 : ℝ) a, (2 : ℝ) * t * Real.exp (-(r * t)) := by
  let μ := expMeasure r
  letI := isProbabilityMeasure_expMeasure hr
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  haveI : IsFiniteMeasure μ := by infer_instance
  let f : ℝ → ℝ := fun x => min x a
  have hf_meas : AEMeasurable f μ :=
    (continuous_id.min continuous_const).aemeasurable
  have hf_nonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [expMeasure_pos_ae hr] with x hx
    exact le_min (le_of_lt hx) ha
  have hg_int :
      ∀ t > 0,
        IntervalIntegrable (fun u : ℝ => (2 : ℝ) * u) volume 0 t := by
    intro t _ht
    exact (by fun_prop : Continuous fun u : ℝ => (2 : ℝ) * u).intervalIntegrable 0 t
  have hg_nonneg :
      ∀ᵐ t ∂volume.restrict (Set.Ioi 0), 0 ≤ (2 : ℝ) * t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (by norm_num) (le_of_lt ht)
  have hlc :=
    MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul
      μ hf_nonneg hf_meas hg_int hg_nonneg
  have hinner :
      (fun x : ℝ => ∫ t in (0)..f x, (2 : ℝ) * t) =ᵐ[μ]
        fun x => (f x) ^ 2 := by
    filter_upwards [hf_nonneg] with x hx
    have hderiv :
        ∀ t ∈ Set.uIcc (0 : ℝ) (f x),
          HasDerivAt (fun y : ℝ => y ^ 2) (2 * t) t := by
      intro t _ht
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id t).mul (hasDerivAt_id t))
    have hcont : Continuous fun t : ℝ => (2 : ℝ) * t := by
      fun_prop
    have hInt :
        IntervalIntegrable (fun t : ℝ => (2 : ℝ) * t) volume 0 (f x) :=
      hcont.intervalIntegrable 0 (f x)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
    simpa using h
  have hlin :
      ∫⁻ x : ℝ, ENNReal.ofReal ((f x) ^ 2) ∂μ =
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {x : ℝ | t ≤ f x} * ENNReal.ofReal ((2 : ℝ) * t) := by
    rw [← lintegral_congr_ae ?_]
    exact hlc
    filter_upwards [hinner] with x hx
    rw [hx]
  have hleft_real :
      ∫ x : ℝ, (f x) ^ 2 ∂μ =
        ENNReal.toReal (∫⁻ x : ℝ, ENNReal.ofReal ((f x) ^ 2) ∂μ) := by
    exact integral_eq_lintegral_of_nonneg_ae
      (by
        filter_upwards with x
        exact sq_nonneg (f x))
      (integrable_expMeasure_min_sq hr ha).aestronglyMeasurable
  rw [hleft_real, hlin]
  exact integral_expMeasure_min_sq_rhs hr

/-- The truncated first moment on `{H ≤ a}` is `(r/2)` times the second
moment of `min H a` for an exponential holding time of rate `r`. -/
theorem integral_expMeasure_Iic_id_eq_rate_half_mul_min_sq
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    ∫ x in Set.Iic a, x ∂expMeasure r =
      (r / 2) * ∫ x : ℝ, (min x a) ^ 2 ∂expMeasure r := by
  have hleft_density :
      ∫ x in Set.Iic a, x ∂expMeasure r =
        ∫ x in Set.Ioc (0 : ℝ) a, r * x * Real.exp (-(r * x)) := by
    rw [expMeasure, gammaMeasure]
    rw [restrict_withDensity measurableSet_Iic]
    rw [integral_withDensity_eq_integral_toReal_smul]
    · simp only [smul_eq_mul]
      change
        ∫ x : ℝ, (gammaPDF 1 r x).toReal * x ∂volume.restrict (Set.Iic a) =
          ∫ x in Set.Ioc (0 : ℝ) a, r * x * Real.exp (-(r * x))
      change
        ∫ x in Set.Iic a, (gammaPDF 1 r x).toReal * x =
          ∫ x in Set.Ioc (0 : ℝ) a, r * x * Real.exp (-(r * x))
      have hsplit : Set.Iic a = Set.Iic (0 : ℝ) ∪ Set.Ioc (0 : ℝ) a := by
        ext x
        constructor
        · intro hx
          by_cases hx0 : x ≤ 0
          · exact Or.inl hx0
          · exact Or.inr ⟨lt_of_not_ge hx0, hx⟩
        · intro hx
          rcases hx with hx | hx
          · exact le_trans hx ha
          · exact hx.2
      rw [hsplit]
      have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioc (0 : ℝ) a) := by
        rw [Set.disjoint_left]
        intro x hx0 hxpos
        exact not_lt_of_ge hx0 hxpos.1
      have hleft_zero :
          ∫ x in Set.Iic (0 : ℝ), (gammaPDF 1 r x).toReal * x = 0 := by
        have hzero_eq : Set.EqOn
            (fun x : ℝ => (gammaPDF 1 r x).toReal * x)
            (fun _ : ℝ => 0) (Set.Iic (0 : ℝ)) := by
          intro x hx
          by_cases hxlt : x < 0
          · have hxnot : ¬ 0 ≤ x := not_le_of_gt hxlt
            have hpdf : (gammaPDF 1 r x).toReal = 0 := by
              simp [gammaPDF, gammaPDFReal, hxnot]
            simp [hpdf]
          · have hxzero : x = 0 := le_antisymm hx (le_of_not_gt hxlt)
            simp [hxzero]
        calc
          ∫ x in Set.Iic (0 : ℝ), (gammaPDF 1 r x).toReal * x
              = ∫ x in Set.Iic (0 : ℝ), (0 : ℝ) := by
                  exact setIntegral_congr_fun measurableSet_Iic hzero_eq
          _ = 0 := by simp
      have hint_left :
          IntegrableOn (fun x : ℝ => (gammaPDF 1 r x).toReal * x)
            (Set.Iic (0 : ℝ)) volume := by
        have hzero_eq : Set.EqOn
            (fun _ : ℝ => 0)
            (fun x : ℝ => (gammaPDF 1 r x).toReal * x)
            (Set.Iic (0 : ℝ)) := by
          intro x hx
          by_cases hxlt : x < 0
          · have hxnot : ¬ 0 ≤ x := not_le_of_gt hxlt
            have hpdf : (gammaPDF 1 r x).toReal = 0 := by
              simp [gammaPDF, gammaPDFReal, hxnot]
            simp [hpdf]
          · have hxzero : x = 0 := le_antisymm hx (le_of_not_gt hxlt)
            simp [hxzero]
        exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ))
          (Set.Iic (0 : ℝ)) volume).congr_fun hzero_eq measurableSet_Iic
      have hint_right :
          IntegrableOn (fun x : ℝ => (gammaPDF 1 r x).toReal * x)
            (Set.Ioc (0 : ℝ) a) volume := by
        let φ : ℝ → ℝ := fun x => r * x * Real.exp (-(r * x))
        have hφ_int : IntegrableOn φ (Set.Ioc (0 : ℝ) a) volume := by
          dsimp [φ]
          have hφ_cont : Continuous fun x : ℝ => r * x * Real.exp (-(r * x)) := by
            fun_prop
          exact hφ_cont.integrableOn_Ioc
        have heq : Set.EqOn φ
            (fun x : ℝ => (gammaPDF 1 r x).toReal * x)
            (Set.Ioc (0 : ℝ) a) := by
          intro x hx
          have hxle : 0 ≤ x := le_of_lt hx.1
          have hpdf_nonneg : 0 ≤ r * Real.exp (-(r * x)) :=
            mul_nonneg hr.le (Real.exp_pos _).le
          simp [φ, gammaPDF, gammaPDFReal, hxle, Real.Gamma_one, hpdf_nonneg]
          ring
        exact hφ_int.congr_fun heq measurableSet_Ioc
      rw [setIntegral_union hdisj measurableSet_Ioc hint_left hint_right]
      rw [hleft_zero, zero_add]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hxle : 0 ≤ x := le_of_lt hx.1
      have hpdf_nonneg : 0 ≤ r * Real.exp (-(r * x)) :=
        mul_nonneg hr.le (Real.exp_pos _).le
      simp [gammaPDF, gammaPDFReal, hxle, Real.Gamma_one, hpdf_nonneg]
      ring
    · exact (measurable_gammaPDFReal 1 r).ennreal_ofReal
    · filter_upwards with x
      simp [gammaPDF]
  rw [hleft_density, integral_expMeasure_min_sq hr ha]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  ring

theorem integral_expMeasure_min_sq_le {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    ∫ x : ℝ, (min x a) ^ 2 ∂expMeasure r ≤
      (2 / r) * ∫ x : ℝ, min x a ∂expMeasure r := by
  rw [integral_expMeasure_min_sq hr ha, integral_expMeasure_min hr ha,
    integral_two_mul_self_mul_exp_neg_mul_Ioc_zero hr ha]
  have hexp_pos : 0 < Real.exp (-(r * a)) := Real.exp_pos _
  have hra_nonneg : 0 ≤ r * a := mul_nonneg (le_of_lt hr) ha
  field_simp [hr.ne']
  nlinarith [hexp_pos, hra_nonneg]

end ProbabilityTheory

namespace Ripple.CTMC

open MeasureTheory MeasureTheory.Measure Topology Finset

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The clock start of sojourn `n`, computed from a finite record history.
It is the sum of holding-time records `1, ..., n`. -/
noncomputable def QMatrix.historySojournStart
    {S : Type*} (n : ℕ)
    (hist : (j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace S j) : ℝ :=
  ∑ j : Fin n, (hist ⟨j.1 + 1,
    Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩).1

theorem QMatrix.historySojournStart_frestrictLe
    {S : Type*} (records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m)
    (n : ℕ) :
    QMatrix.historySojournStart n (Preorder.frestrictLe n records) =
      (QMatrix.recordTrajectoryToPath records).sojournStart n := by
  rw [QMatrix.historySojournStart]
  have hfin :
      (∑ j : Fin n, (records (j.1 + 1)).1) =
        ∑ k ∈ Finset.range n, (records (k + 1)).1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (records (k + 1)).1) n]
  cases n with
  | zero =>
      simp [CTMCPath.sojournStart]
  | succ n =>
      change (∑ j : Fin (n + 1), (records (j.1 + 1)).1) =
        (QMatrix.recordTrajectoryToPath records).sojournStart (n + 1)
      rw [hfin]
      simp [CTMCPath.sojournStart, QMatrix.recordTrajectoryToPath_times]

/-- The history-measurable remaining clock length at sojourn `n`. -/
noncomputable def QMatrix.historyClockRemaining
    {S : Type*} (T : ℝ) (n : ℕ)
    (hist : (j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace S j) : ℝ :=
  max 0 (T - QMatrix.historySojournStart n hist)

theorem QMatrix.historyClockRemaining_nonneg
    {S : Type*} (T : ℝ) (n : ℕ)
    (hist : (j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace S j) :
    0 ≤ QMatrix.historyClockRemaining T n hist := by
  simp [QMatrix.historyClockRemaining]

/-- Predecessor on `WithTop ℕ`, keeping `⊤` fixed and sending `0` to `0`. -/
noncomputable def withTopNatPred : WithTop ℕ → WithTop ℕ
  | ⊤ => ⊤
  | (n : ℕ) => ((n - 1 : ℕ) : WithTop ℕ)

@[simp]
theorem withTopNatPred_top : withTopNatPred (⊤ : WithTop ℕ) = ⊤ := rfl

@[simp]
theorem withTopNatPred_coe_zero :
    withTopNatPred ((0 : ℕ) : WithTop ℕ) = (0 : WithTop ℕ) := rfl

@[simp]
theorem withTopNatPred_coe_succ (n : ℕ) :
    withTopNatPred (((n + 1 : ℕ)) : WithTop ℕ) = (n : WithTop ℕ) := by
  simp [withTopNatPred]

theorem withTopNatPred_le_coe_iff (a : WithTop ℕ) (n : ℕ) :
    withTopNatPred a ≤ (n : WithTop ℕ) ↔
      a ≤ ((n + 1 : ℕ) : WithTop ℕ) := by
  cases a with
  | top =>
      simp [withTopNatPred]
  | coe m =>
      cases m with
      | zero =>
          simp [withTopNatPred]
      | succ m =>
          simp [withTopNatPred]

/-- Product-kernel integrability for one jump-hold step: a finite-state
factor times the holding time is integrable. -/
theorem QMatrix.integrable_jumpHoldStepMeasure_fst_mul_stateFun
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s) (f : S → ℝ) :
    Integrable (fun r : ℝ × S => r.1 * f r.2) (Q.jumpHoldStepMeasure h) := by
  unfold QMatrix.jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  let C : ℝ := (Finset.univ.image fun y : S => ‖f y‖).sup'
    (by exact Finset.image_nonempty.mpr Finset.univ_nonempty) id
  have hC : ∀ y : S, ‖f y‖ ≤ C := by
    intro y
    exact Finset.le_sup'
      (s := Finset.univ.image fun y : S => ‖f y‖) (f := id) (by simp)
  have hmeas : AEStronglyMeasurable (fun r : ℝ × S => r.1 * f r.2)
      ((Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)) := by
    exact (measurable_fst.mul
      ((Measurable.of_discrete (f := f)).comp measurable_snd)).aestronglyMeasurable
  have hdom : Integrable (fun r : ℝ × S => C * ‖r.1‖)
      ((Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)) := by
    have ht : Integrable (fun t : ℝ => C * ‖t‖) (Q.holdingTimeMeasure h) :=
      (Q.integrable_holdingTimeMeasure_id h).norm.const_mul C
    simpa using ht.comp_fst (Q.embeddedStepMeasure s)
  refine hdom.mono' hmeas ?_
  filter_upwards with r
  rw [norm_mul]
  calc
    ‖r.1‖ * ‖f r.2‖ ≤ ‖r.1‖ * C := by
      exact mul_le_mul_of_nonneg_left (hC r.2) (norm_nonneg _)
    _ = C * ‖r.1‖ := by ring

/-- Product-kernel first moment factorization for one jump-hold step. -/
theorem QMatrix.integral_jumpHoldStepMeasure_fst_mul_stateFun
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s) (f : S → ℝ) :
    (∫ r : ℝ × S, r.1 * f r.2 ∂Q.jumpHoldStepMeasure h) =
      (∫ t : ℝ, t ∂Q.holdingTimeMeasure h) *
        (∫ y : S, f y ∂Q.embeddedStepMeasure s) := by
  unfold QMatrix.jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  have hf_int : Integrable (fun r : ℝ × S => r.1 * f r.2)
      ((Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)) := by
    simpa [QMatrix.jumpHoldStepMeasure] using
      Q.integrable_jumpHoldStepMeasure_fst_mul_stateFun h f
  rw [integral_prod (fun r : ℝ × S => r.1 * f r.2) hf_int]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

/-- Product-kernel factorization for a holding-time event times a next-state
observable. -/
theorem QMatrix.integral_jumpHoldStepMeasure_indicator_fst_mul_stateFun
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} (f : S → ℝ) :
    (∫ r : ℝ × S,
        Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * f r.2
        ∂Q.jumpHoldStepMeasure h) =
      (Q.holdingTimeMeasure h).real (Set.Iic a) *
        (∫ y : S, f y ∂Q.embeddedStepMeasure s) := by
  unfold QMatrix.jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  let g : ℝ → ℝ := fun t =>
    Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) t
  let C : ℝ := ∑ y : S, ‖f y‖
  have hC_nonneg : 0 ≤ C := Finset.sum_nonneg fun y _ => norm_nonneg (f y)
  have hC : ∀ y : S, ‖f y‖ ≤ C := by
    intro y
    exact Finset.single_le_sum (fun z _ => norm_nonneg (f z)) (Finset.mem_univ y)
  have hg_meas : Measurable g := by
    exact measurable_const.indicator measurableSet_Iic
  have hf_meas : Measurable f := Measurable.of_discrete
  have hprod_int : Integrable (fun r : ℝ × S => g r.1 * f r.2)
      ((Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)) := by
    refine (integrable_const C).mono'
      ((hg_meas.comp measurable_fst).mul (hf_meas.comp measurable_snd)).aestronglyMeasurable
      ?_
    filter_upwards with r
    have hg_abs : |g r.1| ≤ 1 := by
      by_cases hr : r.1 ≤ a
      · simp [g, Set.indicator, hr]
      · simp [g, Set.indicator, hr]
    have hf_abs : ‖f r.2‖ ≤ C := hC r.2
    rw [norm_mul, Real.norm_eq_abs]
    calc
      |g r.1| * ‖f r.2‖ ≤ 1 * C := by
        exact mul_le_mul hg_abs hf_abs (norm_nonneg _) (by norm_num)
      _ = C := by ring
  have hg_integral :
      ∫ t : ℝ, g t ∂Q.holdingTimeMeasure h =
        (Q.holdingTimeMeasure h).real (Set.Iic a) := by
    dsimp [g]
    rw [integral_indicator measurableSet_Iic]
    simp [measureReal_def]
  rw [integral_prod (fun r : ℝ × S => g r.1 * f r.2) hprod_int]
  simp_rw [integral_const_mul]
  rw [integral_mul_const, hg_integral]

/-- Product-kernel factorization for a truncated holding time times a next-state
observable. -/
theorem QMatrix.integral_jumpHoldStepMeasure_indicator_id_fst_mul_stateFun
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} (f : S → ℝ) :
    (∫ r : ℝ × S,
        Set.indicator (Set.Iic a) (fun t : ℝ => t) r.1 * f r.2
        ∂Q.jumpHoldStepMeasure h) =
      (∫ t in Set.Iic a, t ∂Q.holdingTimeMeasure h) *
        (∫ y : S, f y ∂Q.embeddedStepMeasure s) := by
  unfold QMatrix.jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  let g : ℝ → ℝ := fun t =>
    Set.indicator (Set.Iic a) (fun t : ℝ => t) t
  let C : ℝ := ∑ y : S, ‖f y‖
  have hC_nonneg : 0 ≤ C := Finset.sum_nonneg fun y _ => norm_nonneg (f y)
  have hC : ∀ y : S, ‖f y‖ ≤ C := by
    intro y
    exact Finset.single_le_sum (fun z _ => norm_nonneg (f z)) (Finset.mem_univ y)
  have hg_meas : Measurable g := by
    exact measurable_id.indicator measurableSet_Iic
  have hf_meas : Measurable f := Measurable.of_discrete
  have hprod_int : Integrable (fun r : ℝ × S => g r.1 * f r.2)
      ((Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)) := by
    have hdom : Integrable (fun r : ℝ × S => C * ‖r.1‖)
        ((Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)) := by
      have ht : Integrable (fun t : ℝ => C * ‖t‖) (Q.holdingTimeMeasure h) :=
        (Q.integrable_holdingTimeMeasure_id h).norm.const_mul C
      simpa using ht.comp_fst (Q.embeddedStepMeasure s)
    refine hdom.mono'
      ((hg_meas.comp measurable_fst).mul
        (hf_meas.comp measurable_snd)).aestronglyMeasurable
      ?_
    filter_upwards with r
    have hg_abs : |g r.1| ≤ ‖r.1‖ := by
      by_cases hr : r.1 ≤ a
      · simp [g, Set.indicator, hr, Real.norm_eq_abs]
      · simp [g, Set.indicator, hr]
    have hf_abs : ‖f r.2‖ ≤ C := hC r.2
    rw [norm_mul, Real.norm_eq_abs]
    calc
      |g r.1| * ‖f r.2‖ ≤ ‖r.1‖ * C := by
        exact mul_le_mul hg_abs hf_abs (norm_nonneg _) (norm_nonneg _)
      _ = C * ‖r.1‖ := by ring
  have hg_integral :
      ∫ t : ℝ, g t ∂Q.holdingTimeMeasure h =
        ∫ t in Set.Iic a, t ∂Q.holdingTimeMeasure h := by
    dsimp [g]
    rw [integral_indicator measurableSet_Iic]
  rw [integral_prod (fun r : ℝ × S => g r.1 * f r.2) hprod_int]
  simp_rw [integral_const_mul]
  rw [integral_mul_const, hg_integral]

/-- First moment of an exponentially distributed holding time, truncated at
`a`. -/
theorem QMatrix.integral_holdingTimeMeasure_min
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} (ha : 0 ≤ a) :
    ∫ t : ℝ, min t a ∂Q.holdingTimeMeasure h =
      (1 - Real.exp (-(Q.exitRate s * a))) / Q.exitRate s := by
  simpa [QMatrix.holdingTimeMeasure] using
    ProbabilityTheory.integral_expMeasure_min
      (Q.exitRate_pos_of_nonabsorbing h) ha

/-- The truncated holding time is integrable under a non-absorbing holding-time
law. -/
theorem QMatrix.integrable_holdingTimeMeasure_min
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} :
    Integrable (fun t : ℝ => min t a) (Q.holdingTimeMeasure h) := by
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  have hmeas : AEStronglyMeasurable (fun t : ℝ => min t a)
      (Q.holdingTimeMeasure h) :=
    (continuous_id.min continuous_const).aestronglyMeasurable
  have hdom : Integrable (fun t : ℝ => ‖t‖ + ‖a‖)
      (Q.holdingTimeMeasure h) :=
    (Q.integrable_holdingTimeMeasure_id h).norm.add (integrable_const _)
  refine hdom.mono' hmeas ?_
  filter_upwards with t
  calc
    ‖min t a‖ = |min t a| := rfl
    _ ≤ max |t| |a| := abs_min_le_max_abs_abs
    _ ≤ |t| + |a| := max_le_add_of_nonneg (abs_nonneg t) (abs_nonneg a)
    _ = ‖t‖ + ‖a‖ := by simp [Real.norm_eq_abs]

/-- The squared truncated holding time is integrable under a non-absorbing
holding-time law. -/
theorem QMatrix.integrable_holdingTimeMeasure_min_sq
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun t : ℝ => (min t a) ^ 2) (Q.holdingTimeMeasure h) := by
  simpa [QMatrix.holdingTimeMeasure] using
    ProbabilityTheory.integrable_expMeasure_min_sq
      (Q.exitRate_pos_of_nonabsorbing h) ha

/-- Product-kernel projection for a truncated holding-time observable. -/
theorem QMatrix.integral_jumpHoldStepMeasure_min
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} :
    (∫ r : ℝ × S, min r.1 a ∂Q.jumpHoldStepMeasure h) =
      ∫ t : ℝ, min t a ∂Q.holdingTimeMeasure h := by
  unfold QMatrix.jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  have hint : Integrable (fun r : ℝ × S => min r.1 a)
      ((Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)) := by
    simpa using (Q.integrable_holdingTimeMeasure_min h (a := a)).comp_fst
      (Q.embeddedStepMeasure s)
  rw [integral_prod (fun r : ℝ × S => min r.1 a) hint]
  simp

/-- Product-kernel projection for a squared truncated holding-time
observable. -/
theorem QMatrix.integral_jumpHoldStepMeasure_min_sq
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ r : ℝ × S, (min r.1 a) ^ 2 ∂Q.jumpHoldStepMeasure h) =
      ∫ t : ℝ, (min t a) ^ 2 ∂Q.holdingTimeMeasure h := by
  unfold QMatrix.jumpHoldStepMeasure
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  letI := Q.isProbabilityMeasure_embeddedStepMeasure s
  have hint : Integrable (fun r : ℝ × S => (min r.1 a) ^ 2)
      ((Q.holdingTimeMeasure h).prod (Q.embeddedStepMeasure s)) := by
    simpa using (Q.integrable_holdingTimeMeasure_min_sq h ha).comp_fst
      (Q.embeddedStepMeasure s)
  rw [integral_prod (fun r : ℝ × S => (min r.1 a) ^ 2) hint]
  simp

/-- Distribution function of the non-absorbing holding-time law at a
nonnegative truncation level. -/
theorem QMatrix.holdingTimeMeasure_real_Iic_eq
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} (ha : 0 ≤ a) :
    (Q.holdingTimeMeasure h).real (Set.Iic a) =
      1 - Real.exp (-(Q.exitRate s * a)) := by
  letI := Q.isProbabilityMeasure_holdingTimeMeasure h
  have hcdf := Q.cdf_holdingTimeMeasure_eq h a
  rw [← ProbabilityTheory.cdf_eq_real (Q.holdingTimeMeasure h) a]
  simpa [ha] using hcdf

/-- For an exponential holding time, `P(H ≤ a)` is the exit rate times
`E[min(H,a)]`. -/
theorem QMatrix.holdingTimeMeasure_real_Iic_eq_exitRate_mul_integral_min
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} (ha : 0 ≤ a) :
    (Q.holdingTimeMeasure h).real (Set.Iic a) =
      Q.exitRate s * ∫ t : ℝ, min t a ∂Q.holdingTimeMeasure h := by
  rw [Q.holdingTimeMeasure_real_Iic_eq h ha,
    Q.integral_holdingTimeMeasure_min h ha]
  field_simp [(Q.exitRate_pos_of_nonabsorbing h).ne']

/-- For an exponential holding time, the first moment on `{H ≤ a}` is
`exitRate / 2` times the truncated second moment. -/
theorem QMatrix.integral_holdingTimeMeasure_Iic_id_eq_exitRate_half_mul_min_sq
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in Set.Iic a, t ∂Q.holdingTimeMeasure h =
      (Q.exitRate s / 2) *
        ∫ t : ℝ, (min t a) ^ 2 ∂Q.holdingTimeMeasure h := by
  simpa [QMatrix.holdingTimeMeasure] using
    ProbabilityTheory.integral_expMeasure_Iic_id_eq_rate_half_mul_min_sq
      (Q.exitRate_pos_of_nonabsorbing h) ha

/-- The truncated second moment of an exponentially distributed holding time
is bounded by `(2 / exitRate)` times the truncated first moment. -/
theorem QMatrix.integral_holdingTimeMeasure_min_sq_le
    {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) {s : S} (h : ¬Q.IsAbsorbing s)
    {a : ℝ} (ha : 0 ≤ a) :
    ∫ t : ℝ, (min t a) ^ 2 ∂Q.holdingTimeMeasure h ≤
      (2 / Q.exitRate s) *
        ∫ t : ℝ, min t a ∂Q.holdingTimeMeasure h := by
  simpa [QMatrix.holdingTimeMeasure] using
    ProbabilityTheory.integral_expMeasure_min_sq_le
      (Q.exitRate_pos_of_nonabsorbing h) ha

/-- Conditional truncated-holding-time second moment bound for one canonical
record step, with absorbing histories included by the guarded `dirac 0` law. -/
theorem QMatrix.integral_condDistrib_next_holdingTime_min_sq_le
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    (a : ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) → ℝ)
    (ha : ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      0 ≤ a hist) :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      (∫ t : ℝ,
          (min t (a hist)) ^ 2 ∂ProbabilityTheory.condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              (records (n + 1)).1)
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist) ≤
        (2 / Q.exitRate (QMatrix.currentStateFromHistory (S := S) n hist)) *
          ∫ t : ℝ,
            min t (a hist) ∂ProbabilityTheory.condDistrib
              (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
                (records (n + 1)).1)
              (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist := by
  filter_upwards
    [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n,
      Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing s₀ n,
      ha]
    with hist hnonabs habs ha_hist
  by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
  · rw [habs h]
    have hzero : Q.exitRate (QMatrix.currentStateFromHistory (S := S) n hist) = 0 := h
    simp [hzero, ha_hist]
  · rw [hnonabs h]
    exact Q.integral_holdingTimeMeasure_min_sq_le h ha_hist

/-- Conditional first moment on `{H ≤ a}` for one canonical record step, with
absorbing histories included by the guarded `dirac 0` law. -/
theorem QMatrix.integral_condDistrib_next_holdingTime_Iic_id_eq_exitRate_half_mul_min_sq
    {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    (a : ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) → ℝ)
    (ha : ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      0 ≤ a hist) :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      (∫ t in Set.Iic (a hist), t
          ∂ProbabilityTheory.condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              (records (n + 1)).1)
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist) =
        (Q.exitRate (QMatrix.currentStateFromHistory (S := S) n hist) / 2) *
          ∫ t : ℝ,
            (min t (a hist)) ^ 2 ∂ProbabilityTheory.condDistrib
              (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
                (records (n + 1)).1)
              (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist := by
  filter_upwards
    [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n,
      Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing s₀ n,
      ha]
    with hist hnonabs habs ha_hist
  by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
  · rw [habs h]
    have hzero : Q.exitRate (QMatrix.currentStateFromHistory (S := S) n hist) = 0 := h
    rw [hzero, zero_div, zero_mul]
    rw [setIntegral_dirac]
    simp [ha_hist]
  · rw [hnonabs h]
    exact Q.integral_holdingTimeMeasure_Iic_id_eq_exitRate_half_mul_min_sq h ha_hist

namespace DensityDepCTMC

/-! ## Guarded one-step compensators -/

/-- Guarded drift-over-exit summand.  At absorbing states the summand is
defined to be zero, matching the frozen step kernel. -/
noncomputable def guardedGeneratorDriftDivExit
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) (i : Fin d) : ℝ :=
  if M.exitRateAt x = 0 then 0 else M.generatorDrift x i / M.exitRateAt x

/-- Guarded coordinate-QV-over-exit summand. -/
noncomputable def guardedInstantCoordQVRateDivExit
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) (i : Fin d) : ℝ :=
  if M.exitRateAt x = 0 then 0 else M.instantCoordQVRate x i / M.exitRateAt x

/-- Guarded vector-QV-over-exit summand. -/
noncomputable def guardedInstantQVRateDivExit
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) : ℝ :=
  if M.exitRateAt x = 0 then 0 else M.instantQVRate x / M.exitRateAt x

/-- If the exit rate is zero, every off-diagonal rate from that state is zero. -/
theorem offDiagRate_eq_zero_of_exitRateAt_zero
    (M : DensityDepCTMC d) {x y : Fin d → Fin (M.N + 1)}
    (h : M.exitRateAt x = 0) :
    M.offDiagRate x y = 0 := by
  have hsum0 : (∑ z, M.offDiagRate x z) = 0 := by
    simpa [h] using M.sum_offDiagRate_eq_exitRateAt x
  have hy_le_sum : M.offDiagRate x y ≤ ∑ z, M.offDiagRate x z := by
    exact Finset.single_le_sum
      (fun z _ => M.offDiagRate_nonneg x z) (Finset.mem_univ y)
  exact le_antisymm (by simpa [hsum0] using hy_le_sum)
    (M.offDiagRate_nonneg x y)

/-- Zero exit rate also kills the coordinate instantaneous QV rate. -/
theorem instantCoordQVRate_eq_zero_of_exitRateAt_zero
    (M : DensityDepCTMC d) {x : Fin d → Fin (M.N + 1)}
    (h : M.exitRateAt x = 0) (i : Fin d) :
    M.instantCoordQVRate x i = 0 := by
  simp only [instantCoordQVRate]
  exact Finset.sum_eq_zero fun y _ =>
    by simp [M.offDiagRate_eq_zero_of_exitRateAt_zero h]

/-- Zero exit rate also kills the vector instantaneous QV rate. -/
theorem instantQVRate_eq_zero_of_exitRateAt_zero
    (M : DensityDepCTMC d) {x : Fin d → Fin (M.N + 1)}
    (h : M.exitRateAt x = 0) :
    M.instantQVRate x = 0 := by
  simp only [instantQVRate]
  exact Finset.sum_eq_zero fun y _ =>
    by simp [M.offDiagRate_eq_zero_of_exitRateAt_zero h]

/-- Zero exit rate also kills the generator drift. -/
theorem generatorDrift_eq_zero_of_exitRateAt_zero
    (M : DensityDepCTMC d) {x : Fin d → Fin (M.N + 1)}
    (h : M.exitRateAt x = 0) (i : Fin d) :
    M.generatorDrift x i = 0 := by
  have hle :=
    M.generatorDrift_sq_le_exitRateAt_mul_instantCoordQVRate x i
  have hsquare_nonpos : M.generatorDrift x i ^ 2 ≤ 0 := by
    simpa [h] using hle
  nlinarith [sq_nonneg (M.generatorDrift x i)]

/-- Local vector form of the generator-drift/QV bound used by the absorbing
random-index bridge.  This mirrors the generic lemma in `DensityDependent`
without requiring rebuilt imported `.olean` files during single-file checks. -/
theorem generatorDrift_norm_sq_le_exitRateAt_mul_instantQVRate_frozen
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) :
    ‖M.generatorDrift x‖ ^ 2 ≤ M.exitRateAt x * M.instantQVRate x := by
  let R : ℝ := M.exitRateAt x * M.instantQVRate x
  have hR_nonneg : 0 ≤ R := by
    exact mul_nonneg (M.exitRateAt_nonneg x) (M.instantQVRate_nonneg x)
  have hnorm_le : ‖M.generatorDrift x‖ ≤ Real.sqrt R := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg R)]
    intro i
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    calc
      (M.generatorDrift x i) ^ 2
          ≤ M.exitRateAt x * M.instantCoordQVRate x i :=
            M.generatorDrift_sq_le_exitRateAt_mul_instantCoordQVRate x i
      _ ≤ M.exitRateAt x * M.instantQVRate x := by
            exact mul_le_mul_of_nonneg_left
              (M.instantCoordQVRate_le_instantQVRate x i)
              (M.exitRateAt_nonneg x)
      _ = R := rfl
  have hsq :
      ‖M.generatorDrift x‖ ^ 2 ≤ (Real.sqrt R) ^ 2 := by
    exact sq_le_sq'
      ((neg_nonpos.mpr (Real.sqrt_nonneg R)).trans (norm_nonneg _))
      hnorm_le
  simpa [R, Real.sq_sqrt hR_nonneg] using hsq

@[simp]
theorem guardedGeneratorDriftDivExit_of_exitRate_zero
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) (i : Fin d)
    (h : M.exitRateAt x = 0) :
    M.guardedGeneratorDriftDivExit x i = 0 := by
  simp [guardedGeneratorDriftDivExit, h]

@[simp]
theorem guardedInstantCoordQVRateDivExit_of_exitRate_zero
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) (i : Fin d)
    (h : M.exitRateAt x = 0) :
    M.guardedInstantCoordQVRateDivExit x i = 0 := by
  simp [guardedInstantCoordQVRateDivExit, h]

@[simp]
theorem guardedInstantQVRateDivExit_of_exitRate_zero
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1))
    (h : M.exitRateAt x = 0) :
    M.guardedInstantQVRateDivExit x = 0 := by
  simp [guardedInstantQVRateDivExit, h]

theorem guardedGeneratorDriftDivExit_of_exitRate_ne_zero
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) (i : Fin d)
    (h : M.exitRateAt x ≠ 0) :
    M.guardedGeneratorDriftDivExit x i =
      M.generatorDrift x i / M.exitRateAt x := by
  simp [guardedGeneratorDriftDivExit, h]

theorem guardedInstantCoordQVRateDivExit_of_exitRate_ne_zero
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) (i : Fin d)
    (h : M.exitRateAt x ≠ 0) :
    M.guardedInstantCoordQVRateDivExit x i =
      M.instantCoordQVRate x i / M.exitRateAt x := by
  simp [guardedInstantCoordQVRateDivExit, h]

theorem guardedInstantQVRateDivExit_of_exitRate_ne_zero
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1))
    (h : M.exitRateAt x ≠ 0) :
    M.guardedInstantQVRateDivExit x =
      M.instantQVRate x / M.exitRateAt x := by
  simp [guardedInstantQVRateDivExit, h]

theorem guardedInstantCoordQVRateDivExit_nonneg
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) (i : Fin d) :
    0 ≤ M.guardedInstantCoordQVRateDivExit x i := by
  unfold guardedInstantCoordQVRateDivExit
  split_ifs
  · norm_num
  · exact div_nonneg (M.instantCoordQVRate_nonneg x i) (M.exitRateAt_nonneg x)

theorem guardedInstantQVRateDivExit_nonneg
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) :
    0 ≤ M.guardedInstantQVRateDivExit x := by
  unfold guardedInstantQVRateDivExit
  split_ifs
  · norm_num
  · exact div_nonneg (M.instantQVRate_nonneg x) (M.exitRateAt_nonneg x)

/-! ## Clock-truncated frozen increments -/

/-- The centered coordinate increment of one sojourn, truncated at the remaining
clock length `a`.  If the jump happens before the clock horizon, the state jump
is included; in all cases the drift is compensated only for `min H a`. -/
noncomputable def truncatedCenteredCoordIncrement
    (M : DensityDepCTMC d) (x : Fin d → Fin (M.N + 1)) (i : Fin d)
    (a : ℝ) (r : ℝ × (Fin d → Fin (M.N + 1))) : ℝ :=
  (if r.1 ≤ a then (1 : ℝ) else 0) *
      (M.scaledState r.2 - M.scaledState x) i -
    M.generatorDrift x i * min r.1 a

/-- The history-measurable clock-truncated increment, expressed on the next
canonical record. -/
noncomputable def truncatedCenteredCoordIncrementFromHistory
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ) (i : Fin d)
    (hist : (j : Iic n) →
      QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j)
    (r : QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) :
    ℝ :=
  let x : Fin d → Fin (M.N + 1) :=
    QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist
  M.truncatedCenteredCoordIncrement x i
    (QMatrix.historyClockRemaining T n hist) r

/-- The history-measurable clock-truncated vector jump square, expressed on the
next canonical record. -/
noncomputable def truncatedJumpSqIncrementFromHistory
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ)
    (hist : (j : Iic n) →
      QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j)
    (r : QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) :
    ℝ :=
  let x : Fin d → Fin (M.N + 1) :=
    QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist
  Set.indicator (Set.Iic (QMatrix.historyClockRemaining T n hist))
      (fun _ : ℝ => (1 : ℝ)) r.1 *
    ‖M.scaledState r.2 - M.scaledState x‖ ^ 2

/-- The clock-truncated coordinate martingale skeleton along a realized path. -/
noncomputable def frozenClockTruncatedMartingale
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d)
    (T : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.truncatedCenteredCoordIncrement (path.stateSeq k) i
      (max 0 (T - path.sojournStart k))
      (path.sojournTime k, path.stateSeq (k + 1))

@[simp]
theorem frozenClockTruncatedMartingale_zero
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (T : ℝ) :
    M.frozenClockTruncatedMartingale path i T 0 = 0 := by
  simp [frozenClockTruncatedMartingale]

theorem frozenClockTruncatedMartingale_succ
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d)
    (T : ℝ) (n : ℕ) :
    M.frozenClockTruncatedMartingale path i T (n + 1) =
      M.frozenClockTruncatedMartingale path i T n +
        M.truncatedCenteredCoordIncrement (path.stateSeq n) i
          (max 0 (T - path.sojournStart n))
          (path.sojournTime n, path.stateSeq (n + 1)) := by
  simp [frozenClockTruncatedMartingale, Finset.sum_range_succ]

theorem frozenClockTruncatedMartingale_succ_sub
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d)
    (T : ℝ) (n : ℕ) :
    M.frozenClockTruncatedMartingale path i T (n + 1) -
        M.frozenClockTruncatedMartingale path i T n =
      M.truncatedCenteredCoordIncrement (path.stateSeq n) i
        (max 0 (T - path.sojournStart n))
        (path.sojournTime n, path.stateSeq (n + 1)) := by
  rw [M.frozenClockTruncatedMartingale_succ]
  ring

/-- Under one non-absorbing jump-hold step, the clock-truncated compensated
coordinate increment has mean zero. -/
theorem integral_jumpHoldStepMeasure_truncatedCenteredCoord_eq_zero
    (M : DensityDepCTMC d) {x : Fin d → Fin (M.N + 1)}
    (h : ¬M.toQMatrix.IsAbsorbing x) (i : Fin d)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        (Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 *
            (M.scaledState r.2 - M.scaledState x) i -
          M.generatorDrift x i * min r.1 a)
        ∂M.toQMatrix.jumpHoldStepMeasure h) = 0 := by
  let J : (Fin d → Fin (M.N + 1)) → ℝ :=
    fun y => (M.scaledState y - M.scaledState x) i
  let E : ℝ := ∫ t : ℝ, min t a ∂M.toQMatrix.holdingTimeMeasure h
  let P : ℝ := (M.toQMatrix.holdingTimeMeasure h).real (Set.Iic a)
  let D : ℝ := M.generatorDrift x i
  let lam : ℝ := M.exitRateAt x
  have hlam_ne : lam ≠ 0 := by
    exact ne_of_gt (by
      simpa [lam, exitRateAt] using M.toQMatrix.exitRate_pos_of_nonabsorbing h)
  let C : ℝ := ∑ y : Fin d → Fin (M.N + 1), ‖J y‖
  have hC_nonneg : 0 ≤ C := Finset.sum_nonneg fun y _ => norm_nonneg (J y)
  have hC : ∀ y : Fin d → Fin (M.N + 1), ‖J y‖ ≤ C := by
    intro y
    exact Finset.single_le_sum (fun z _ => norm_nonneg (J z)) (Finset.mem_univ y)
  have hA_int :
      Integrable
        (fun r : ℝ × (Fin d → Fin (M.N + 1)) =>
          Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * J r.2)
        (M.toQMatrix.jumpHoldStepMeasure h) := by
    unfold QMatrix.jumpHoldStepMeasure
    letI := M.toQMatrix.isProbabilityMeasure_holdingTimeMeasure h
    letI := M.toQMatrix.isProbabilityMeasure_embeddedStepMeasure x
    refine (integrable_const C).mono' ?_ ?_
    · exact (((measurable_const.indicator measurableSet_Iic).comp measurable_fst).mul
        ((Measurable.of_discrete (f := J)).comp measurable_snd)).aestronglyMeasurable
    · filter_upwards with r
      rw [norm_mul]
      have hind : ‖Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1‖ ≤ 1 := by
        by_cases hr : r.1 ≤ a
        · simp [Set.indicator, hr]
        · simp [Set.indicator, hr]
      by_cases hr : r.1 ≤ a
      · simpa [Set.indicator, hr] using
          mul_le_mul hind (hC r.2) (norm_nonneg _) (by norm_num : 0 ≤ (1 : ℝ))
      · simp [Set.indicator, hr, hC_nonneg]
  have hB_int :
      Integrable
        (fun r : ℝ × (Fin d → Fin (M.N + 1)) => D * min r.1 a)
        (M.toQMatrix.jumpHoldStepMeasure h) := by
    have hmin : Integrable
        (fun r : ℝ × (Fin d → Fin (M.N + 1)) => min r.1 a)
        (M.toQMatrix.jumpHoldStepMeasure h) := by
      unfold QMatrix.jumpHoldStepMeasure
      letI := M.toQMatrix.isProbabilityMeasure_holdingTimeMeasure h
      letI := M.toQMatrix.isProbabilityMeasure_embeddedStepMeasure x
      simpa using (M.toQMatrix.integrable_holdingTimeMeasure_min h (a := a)).comp_fst
        (M.toQMatrix.embeddedStepMeasure x)
    exact hmin.const_mul D
  have hjump_mul :
      lam * (∫ y : Fin d → Fin (M.N + 1), J y
          ∂M.toQMatrix.embeddedStepMeasure x) = D := by
    simpa [lam, D, J] using
      M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub x h i
  have hP : P = lam * E := by
    simpa [P, E, lam, exitRateAt] using
      M.toQMatrix.holdingTimeMeasure_real_Iic_eq_exitRate_mul_integral_min h ha
  have hA :
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
          Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * J r.2
          ∂M.toQMatrix.jumpHoldStepMeasure h) = D * E := by
    have hfactor :=
      M.toQMatrix.integral_jumpHoldStepMeasure_indicator_fst_mul_stateFun
        (s := x) h (a := a) J
    calc
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
          Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * J r.2
          ∂M.toQMatrix.jumpHoldStepMeasure h)
          = P * ∫ y : Fin d → Fin (M.N + 1), J y
              ∂M.toQMatrix.embeddedStepMeasure x := by
              simpa [P, J] using hfactor
      _ = (lam * E) * ∫ y : Fin d → Fin (M.N + 1), J y
              ∂M.toQMatrix.embeddedStepMeasure x := by rw [hP]
      _ = E * (lam * ∫ y : Fin d → Fin (M.N + 1), J y
              ∂M.toQMatrix.embeddedStepMeasure x) := by ring
      _ = E * D := by rw [hjump_mul]
      _ = D * E := by ring
  have hB :
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)), D * min r.1 a
          ∂M.toQMatrix.jumpHoldStepMeasure h) = D * E := by
    rw [integral_const_mul]
    rw [M.toQMatrix.integral_jumpHoldStepMeasure_min (s := x) h (a := a)]
  calc
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        (Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * J r.2 -
          D * min r.1 a)
        ∂M.toQMatrix.jumpHoldStepMeasure h)
        = (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
              Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * J r.2
              ∂M.toQMatrix.jumpHoldStepMeasure h) -
            ∫ r : ℝ × (Fin d → Fin (M.N + 1)), D * min r.1 a
              ∂M.toQMatrix.jumpHoldStepMeasure h := by
            exact integral_sub hA_int hB_int
    _ = 0 := by rw [hA, hB]; ring

/-- Definition-form version of
`integral_jumpHoldStepMeasure_truncatedCenteredCoord_eq_zero`. -/
theorem integral_jumpHoldStepMeasure_truncatedCenteredCoordIncrement_eq_zero
    (M : DensityDepCTMC d) {x : Fin d → Fin (M.N + 1)}
    (h : ¬M.toQMatrix.IsAbsorbing x) (i : Fin d)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        M.truncatedCenteredCoordIncrement x i a r
        ∂M.toQMatrix.jumpHoldStepMeasure h) = 0 := by
  calc
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        M.truncatedCenteredCoordIncrement x i a r
        ∂M.toQMatrix.jumpHoldStepMeasure h)
        =
      ∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        (Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 *
            (M.scaledState r.2 - M.scaledState x) i -
          M.generatorDrift x i * min r.1 a)
        ∂M.toQMatrix.jumpHoldStepMeasure h := by
          apply integral_congr_ae
          filter_upwards with r
          by_cases hr : r.1 ≤ a <;>
            simp [truncatedCenteredCoordIncrement, Set.indicator, hr]
    _ = 0 :=
      M.integral_jumpHoldStepMeasure_truncatedCenteredCoord_eq_zero h i ha

/-- Exact one-step second moment for a clock-truncated compensated coordinate
increment.  The cross term cancels because
`E[H 1_{H≤a}] = exitRate / 2 * E[min(H,a)^2]`. -/
theorem integral_jumpHoldStepMeasure_truncatedCenteredCoord_sq_eq
    (M : DensityDepCTMC d) {x : Fin d → Fin (M.N + 1)}
    (h : ¬M.toQMatrix.IsAbsorbing x) (i : Fin d)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        (Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 *
            (M.scaledState r.2 - M.scaledState x) i -
          M.generatorDrift x i * min r.1 a) ^ 2
        ∂M.toQMatrix.jumpHoldStepMeasure h) =
      M.instantCoordQVRate x i *
        ∫ t : ℝ, min t a ∂M.toQMatrix.holdingTimeMeasure h := by
  let J : (Fin d → Fin (M.N + 1)) → ℝ :=
    fun y => (M.scaledState y - M.scaledState x) i
  let E1 : ℝ := ∫ t : ℝ, min t a ∂M.toQMatrix.holdingTimeMeasure h
  let E2 : ℝ := ∫ t : ℝ, (min t a) ^ 2 ∂M.toQMatrix.holdingTimeMeasure h
  let D : ℝ := M.generatorDrift x i
  let QV : ℝ := M.instantCoordQVRate x i
  let lam : ℝ := M.exitRateAt x
  have hlam_ne : lam ≠ 0 := by
    exact ne_of_gt (by
      simpa [lam, exitRateAt] using M.toQMatrix.exitRate_pos_of_nonabsorbing h)
  let A : ℝ × (Fin d → Fin (M.N + 1)) → ℝ := fun r =>
    Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * (J r.2) ^ 2
  let B : ℝ × (Fin d → Fin (M.N + 1)) → ℝ := fun r =>
    Set.indicator (Set.Iic a) (fun t : ℝ => t) r.1 * J r.2
  let Cfun : ℝ × (Fin d → Fin (M.N + 1)) → ℝ := fun r =>
    (min r.1 a) ^ 2
  let C₁ : ℝ := ∑ y : Fin d → Fin (M.N + 1), ‖(J y) ^ 2‖
  let C₂ : ℝ := ∑ y : Fin d → Fin (M.N + 1), ‖J y‖
  have hC₁_nonneg : 0 ≤ C₁ := Finset.sum_nonneg fun y _ => norm_nonneg ((J y) ^ 2)
  have hC₂_nonneg : 0 ≤ C₂ := Finset.sum_nonneg fun y _ => norm_nonneg (J y)
  have hC₁ : ∀ y : Fin d → Fin (M.N + 1), ‖(J y) ^ 2‖ ≤ C₁ := by
    intro y
    exact Finset.single_le_sum (fun z _ => norm_nonneg ((J z) ^ 2)) (Finset.mem_univ y)
  have hC₂ : ∀ y : Fin d → Fin (M.N + 1), ‖J y‖ ≤ C₂ := by
    intro y
    exact Finset.single_le_sum (fun z _ => norm_nonneg (J z)) (Finset.mem_univ y)
  have hA_int : Integrable A (M.toQMatrix.jumpHoldStepMeasure h) := by
    unfold QMatrix.jumpHoldStepMeasure
    letI := M.toQMatrix.isProbabilityMeasure_holdingTimeMeasure h
    letI := M.toQMatrix.isProbabilityMeasure_embeddedStepMeasure x
    refine (integrable_const C₁).mono' ?_ ?_
    · exact (((measurable_const.indicator measurableSet_Iic).comp measurable_fst).mul
        ((Measurable.of_discrete (f := fun y => (J y) ^ 2)).comp
          measurable_snd)).aestronglyMeasurable
    · filter_upwards with r
      dsimp [A]
      rw [← Real.norm_eq_abs, norm_mul]
      have hind : ‖Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1‖ ≤ 1 := by
        by_cases hr : r.1 ≤ a
        · simp [Set.indicator, hr]
        · simp [Set.indicator, hr]
      by_cases hr : r.1 ≤ a
      · simpa [Set.indicator, hr] using
          mul_le_mul hind (hC₁ r.2) (norm_nonneg _) (by norm_num : 0 ≤ (1 : ℝ))
      · simp [Set.indicator, hr, hC₁_nonneg]
  have hB_int : Integrable B (M.toQMatrix.jumpHoldStepMeasure h) := by
    unfold QMatrix.jumpHoldStepMeasure
    letI := M.toQMatrix.isProbabilityMeasure_holdingTimeMeasure h
    letI := M.toQMatrix.isProbabilityMeasure_embeddedStepMeasure x
    have hdom : Integrable (fun r : ℝ × (Fin d → Fin (M.N + 1)) => C₂ * ‖r.1‖)
        ((M.toQMatrix.holdingTimeMeasure h).prod
          (M.toQMatrix.embeddedStepMeasure x)) := by
      have ht : Integrable (fun t : ℝ => C₂ * ‖t‖)
          (M.toQMatrix.holdingTimeMeasure h) :=
        (M.toQMatrix.integrable_holdingTimeMeasure_id h).norm.const_mul C₂
      simpa using ht.comp_fst (M.toQMatrix.embeddedStepMeasure x)
    refine hdom.mono' ?_ ?_
    · exact (((measurable_id.indicator measurableSet_Iic).comp measurable_fst).mul
        ((Measurable.of_discrete (f := J)).comp measurable_snd)).aestronglyMeasurable
    · filter_upwards with r
      dsimp [B]
      rw [← Real.norm_eq_abs, norm_mul]
      have hind : ‖Set.indicator (Set.Iic a) (fun t : ℝ => t) r.1‖ ≤ ‖r.1‖ := by
        by_cases hr : r.1 ≤ a
        · simp [Set.indicator, hr]
        · simp [Set.indicator, hr]
      calc
        ‖Set.indicator (Set.Iic a) (fun t : ℝ => t) r.1‖ * ‖J r.2‖
            ≤ ‖r.1‖ * C₂ := by
              exact mul_le_mul hind (hC₂ r.2) (norm_nonneg _) (norm_nonneg _)
        _ = C₂ * ‖r.1‖ := by ring
  have hC_int : Integrable Cfun (M.toQMatrix.jumpHoldStepMeasure h) := by
    unfold QMatrix.jumpHoldStepMeasure
    letI := M.toQMatrix.isProbabilityMeasure_holdingTimeMeasure h
    letI := M.toQMatrix.isProbabilityMeasure_embeddedStepMeasure x
    simpa [Cfun] using (M.toQMatrix.integrable_holdingTimeMeasure_min_sq h ha).comp_fst
      (M.toQMatrix.embeddedStepMeasure x)
  have hjump_mul :
      lam * (∫ y : Fin d → Fin (M.N + 1), J y
          ∂M.toQMatrix.embeddedStepMeasure x) = D := by
    simpa [lam, D, J] using
      M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub x h i
  have hJmean :
      (∫ y : Fin d → Fin (M.N + 1), J y
          ∂M.toQMatrix.embeddedStepMeasure x) = D / lam := by
    calc
      (∫ y : Fin d → Fin (M.N + 1), J y
          ∂M.toQMatrix.embeddedStepMeasure x)
          = (lam * ∫ y : Fin d → Fin (M.N + 1), J y
              ∂M.toQMatrix.embeddedStepMeasure x) / lam := by
              field_simp [hlam_ne]
      _ = D / lam := by rw [hjump_mul]
  have hJ2_mul :
      lam * (∫ y : Fin d → Fin (M.N + 1), (J y) ^ 2
          ∂M.toQMatrix.embeddedStepMeasure x) = QV := by
    simpa [lam, QV, J] using
      M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub_apply_sq x h i
  have hJ2 :
      (∫ y : Fin d → Fin (M.N + 1), (J y) ^ 2
          ∂M.toQMatrix.embeddedStepMeasure x) = QV / lam := by
    calc
      (∫ y : Fin d → Fin (M.N + 1), (J y) ^ 2
          ∂M.toQMatrix.embeddedStepMeasure x)
          = (lam * ∫ y : Fin d → Fin (M.N + 1), (J y) ^ 2
              ∂M.toQMatrix.embeddedStepMeasure x) / lam := by
              field_simp [hlam_ne]
      _ = QV / lam := by rw [hJ2_mul]
  have hP : (M.toQMatrix.holdingTimeMeasure h).real (Set.Iic a) = lam * E1 := by
    simpa [E1, lam, exitRateAt] using
      M.toQMatrix.holdingTimeMeasure_real_Iic_eq_exitRate_mul_integral_min h ha
  have hHid :
      (∫ t in Set.Iic a, t ∂M.toQMatrix.holdingTimeMeasure h) =
        (lam / 2) * E2 := by
    simpa [E2, lam, exitRateAt] using
      M.toQMatrix.integral_holdingTimeMeasure_Iic_id_eq_exitRate_half_mul_min_sq h ha
  have hA_eval :
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)), A r
          ∂M.toQMatrix.jumpHoldStepMeasure h) = QV * E1 := by
    have hfactor :=
      M.toQMatrix.integral_jumpHoldStepMeasure_indicator_fst_mul_stateFun
        (s := x) h (a := a) (fun y => (J y) ^ 2)
    calc
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)), A r
          ∂M.toQMatrix.jumpHoldStepMeasure h)
          = (M.toQMatrix.holdingTimeMeasure h).real (Set.Iic a) *
              ∫ y : Fin d → Fin (M.N + 1), (J y) ^ 2
                ∂M.toQMatrix.embeddedStepMeasure x := by
              simpa [A] using hfactor
      _ = (lam * E1) * (QV / lam) := by rw [hP, hJ2]
      _ = QV * E1 := by field_simp [hlam_ne]
  have hB_eval :
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)), B r
          ∂M.toQMatrix.jumpHoldStepMeasure h) = (D / 2) * E2 := by
    have hfactor :=
      M.toQMatrix.integral_jumpHoldStepMeasure_indicator_id_fst_mul_stateFun
        (s := x) h (a := a) J
    calc
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)), B r
          ∂M.toQMatrix.jumpHoldStepMeasure h)
          = (∫ t in Set.Iic a, t ∂M.toQMatrix.holdingTimeMeasure h) *
              ∫ y : Fin d → Fin (M.N + 1), J y
                ∂M.toQMatrix.embeddedStepMeasure x := by
              simpa [B] using hfactor
      _ = ((lam / 2) * E2) * (D / lam) := by rw [hHid, hJmean]
      _ = (D / 2) * E2 := by field_simp [hlam_ne]
  have hC_eval :
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)), Cfun r
          ∂M.toQMatrix.jumpHoldStepMeasure h) = E2 := by
    simpa [Cfun, E2] using
      M.toQMatrix.integral_jumpHoldStepMeasure_min_sq (s := x) h ha
  have hsplit :
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
          (Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * J r.2 -
            D * min r.1 a) ^ 2
          ∂M.toQMatrix.jumpHoldStepMeasure h) =
        ∫ r, A r ∂M.toQMatrix.jumpHoldStepMeasure h +
          ∫ r, ((-2 * D) * B r) ∂M.toQMatrix.jumpHoldStepMeasure h +
          ∫ r, (D ^ 2 * Cfun r) ∂M.toQMatrix.jumpHoldStepMeasure h := by
    have hpoint :
        (fun r : ℝ × (Fin d → Fin (M.N + 1)) =>
          (Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * J r.2 -
            D * min r.1 a) ^ 2)
          =
        fun r => A r + ((-2 * D) * B r + D ^ 2 * Cfun r) := by
      funext r
      by_cases hr : r.1 ≤ a
      · have hmin : min r.1 a = r.1 := min_eq_left hr
        simp [A, B, Cfun, Set.indicator, hr]
        ring
      · have hnot : ¬ r.1 ≤ a := hr
        simp [A, B, Cfun, Set.indicator, hnot]
        ring
    have hBD_int : Integrable (fun r : ℝ × (Fin d → Fin (M.N + 1)) => (-2 * D) * B r)
        (M.toQMatrix.jumpHoldStepMeasure h) := hB_int.const_mul (-2 * D)
    have hCD_int : Integrable (fun r : ℝ × (Fin d → Fin (M.N + 1)) => D ^ 2 * Cfun r)
        (M.toQMatrix.jumpHoldStepMeasure h) := hC_int.const_mul (D ^ 2)
    rw [hpoint]
    calc
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
          A r + ((-2 * D) * B r + D ^ 2 * Cfun r)
          ∂M.toQMatrix.jumpHoldStepMeasure h)
          = ∫ r, A r ∂M.toQMatrix.jumpHoldStepMeasure h +
              ∫ r, ((-2 * D) * B r + D ^ 2 * Cfun r)
                ∂M.toQMatrix.jumpHoldStepMeasure h := by
              exact integral_add hA_int (hBD_int.add hCD_int)
      _ = ∫ r, A r ∂M.toQMatrix.jumpHoldStepMeasure h +
            (∫ r, ((-2 * D) * B r) ∂M.toQMatrix.jumpHoldStepMeasure h +
              ∫ r, (D ^ 2 * Cfun r) ∂M.toQMatrix.jumpHoldStepMeasure h) := by
            rw [integral_add hBD_int hCD_int]
      _ = ∫ r, A r ∂M.toQMatrix.jumpHoldStepMeasure h +
            ∫ r, ((-2 * D) * B r) ∂M.toQMatrix.jumpHoldStepMeasure h +
            ∫ r, (D ^ 2 * Cfun r) ∂M.toQMatrix.jumpHoldStepMeasure h := by
            ring
  calc
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        (Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 *
            (M.scaledState r.2 - M.scaledState x) i -
          M.generatorDrift x i * min r.1 a) ^ 2
        ∂M.toQMatrix.jumpHoldStepMeasure h)
        = (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
            (Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 * J r.2 -
              D * min r.1 a) ^ 2
            ∂M.toQMatrix.jumpHoldStepMeasure h) := by
            simp [J, D]
    _ = ∫ r, A r ∂M.toQMatrix.jumpHoldStepMeasure h +
          ∫ r, ((-2 * D) * B r) ∂M.toQMatrix.jumpHoldStepMeasure h +
          ∫ r, (D ^ 2 * Cfun r) ∂M.toQMatrix.jumpHoldStepMeasure h := hsplit
    _ = QV * E1 + (-2 * D) * ((D / 2) * E2) + D ^ 2 * E2 := by
          rw [hA_eval, integral_const_mul, hB_eval, integral_const_mul, hC_eval]
    _ = QV * E1 := by ring
    _ = M.instantCoordQVRate x i *
        ∫ t : ℝ, min t a ∂M.toQMatrix.holdingTimeMeasure h := by
          simp [QV, E1]

/-- Definition-form version of
`integral_jumpHoldStepMeasure_truncatedCenteredCoord_sq_eq`. -/
theorem integral_jumpHoldStepMeasure_truncatedCenteredCoordIncrement_sq_eq
    (M : DensityDepCTMC d) {x : Fin d → Fin (M.N + 1)}
    (h : ¬M.toQMatrix.IsAbsorbing x) (i : Fin d)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        (M.truncatedCenteredCoordIncrement x i a r) ^ 2
        ∂M.toQMatrix.jumpHoldStepMeasure h) =
      M.instantCoordQVRate x i *
        ∫ t : ℝ, min t a ∂M.toQMatrix.holdingTimeMeasure h := by
  calc
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        (M.truncatedCenteredCoordIncrement x i a r) ^ 2
        ∂M.toQMatrix.jumpHoldStepMeasure h)
        =
      ∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        (Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 *
            (M.scaledState r.2 - M.scaledState x) i -
          M.generatorDrift x i * min r.1 a) ^ 2
        ∂M.toQMatrix.jumpHoldStepMeasure h := by
          apply integral_congr_ae
          filter_upwards with r
          by_cases hr : r.1 ≤ a <;>
            simp [truncatedCenteredCoordIncrement, Set.indicator, hr]
    _ = M.instantCoordQVRate x i *
        ∫ t : ℝ, min t a ∂M.toQMatrix.holdingTimeMeasure h :=
      M.integral_jumpHoldStepMeasure_truncatedCenteredCoord_sq_eq h i ha

/-- Exact one-step second moment for a clock-truncated vector jump.  This is the
vector jump-only analogue of
`integral_jumpHoldStepMeasure_truncatedCenteredCoordIncrement_sq_eq`, without the
drift-compensation cross terms. -/
theorem integral_jumpHoldStepMeasure_truncatedJumpSq_eq
    (M : DensityDepCTMC d) {x : Fin d → Fin (M.N + 1)}
    (h : ¬M.toQMatrix.IsAbsorbing x)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 *
          ‖M.scaledState r.2 - M.scaledState x‖ ^ 2
        ∂M.toQMatrix.jumpHoldStepMeasure h) =
      M.instantQVRate x *
        ∫ t : ℝ, min t a ∂M.toQMatrix.holdingTimeMeasure h := by
  let J : (Fin d → Fin (M.N + 1)) → ℝ :=
    fun y => ‖M.scaledState y - M.scaledState x‖ ^ 2
  let E : ℝ := ∫ t : ℝ, min t a ∂M.toQMatrix.holdingTimeMeasure h
  let lam : ℝ := M.exitRateAt x
  have hlam_ne : lam ≠ 0 := by
    exact ne_of_gt (by
      simpa [lam, exitRateAt] using M.toQMatrix.exitRate_pos_of_nonabsorbing h)
  have hJ_mul :
      lam * (∫ y : Fin d → Fin (M.N + 1), J y
          ∂M.toQMatrix.embeddedStepMeasure x) = M.instantQVRate x := by
    simpa [lam, J] using
      M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub_sq x h
  have hJ :
      (∫ y : Fin d → Fin (M.N + 1), J y
          ∂M.toQMatrix.embeddedStepMeasure x) = M.instantQVRate x / lam := by
    calc
      (∫ y : Fin d → Fin (M.N + 1), J y
          ∂M.toQMatrix.embeddedStepMeasure x)
          = (lam * ∫ y : Fin d → Fin (M.N + 1), J y
              ∂M.toQMatrix.embeddedStepMeasure x) / lam := by
              field_simp [hlam_ne]
      _ = M.instantQVRate x / lam := by rw [hJ_mul]
  have hP : (M.toQMatrix.holdingTimeMeasure h).real (Set.Iic a) = lam * E := by
    simpa [E, lam, exitRateAt] using
      M.toQMatrix.holdingTimeMeasure_real_Iic_eq_exitRate_mul_integral_min h ha
  have hfactor :=
    M.toQMatrix.integral_jumpHoldStepMeasure_indicator_fst_mul_stateFun
      (s := x) h (a := a) J
  calc
    (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
        Set.indicator (Set.Iic a) (fun _ : ℝ => (1 : ℝ)) r.1 *
          ‖M.scaledState r.2 - M.scaledState x‖ ^ 2
        ∂M.toQMatrix.jumpHoldStepMeasure h)
        = (M.toQMatrix.holdingTimeMeasure h).real (Set.Iic a) *
            ∫ y : Fin d → Fin (M.N + 1), J y
              ∂M.toQMatrix.embeddedStepMeasure x := by
            simpa [J] using hfactor
    _ = (lam * E) * (M.instantQVRate x / lam) := by rw [hP, hJ]
    _ = M.instantQVRate x * E := by field_simp [hlam_ne]
    _ = M.instantQVRate x *
        ∫ t : ℝ, min t a ∂M.toQMatrix.holdingTimeMeasure h := by simp [E]

/-- Conditional next-record integral of a clock-truncated centered coordinate
increment.  This is the history-level martingale-increment identity; it avoids
any stopping-time shift because the remaining clock length is already
finite-history measurable. -/
theorem integral_condDistrib_truncatedCenteredCoordIncrementFromHistory_eq_zero
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) (i : Fin d) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      (∫ r : QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1),
          M.truncatedCenteredCoordIncrementFromHistory T n i hist r
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) = 0 := by
  have hnonabs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ∀ h : ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist),
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => records (n + 1))
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.jumpHoldStepMeasure h := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_of_nonabsorbing
      x₀ n
  have habs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => records (n + 1))
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            Measure.dirac
              (0,
                QMatrix.currentStateFromHistory
                  (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_of_absorbing
      x₀ n
  filter_upwards [hnonabs, habs] with hist hnonabs_hist habs_hist
  let x : Fin d → Fin (M.N + 1) :=
    QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist
  let a : ℝ := QMatrix.historyClockRemaining T n hist
  have ha : 0 ≤ a := by
    simpa [a] using QMatrix.historyClockRemaining_nonneg T n hist
  by_cases hxabs : M.toQMatrix.IsAbsorbing x
  · have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
          Measure.dirac (0, x) := by
      simpa [x] using habs_hist (by simpa [x] using hxabs)
    rw [hdist]
    have hzero : M.exitRateAt x = 0 := by
      simpa [x, exitRateAt] using hxabs
    have hdrift : M.generatorDrift x i = 0 :=
      M.generatorDrift_eq_zero_of_exitRateAt_zero hzero i
    simp [truncatedCenteredCoordIncrementFromHistory,
      truncatedCenteredCoordIncrement, x, a, ha, hdrift]
  · have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
          M.toQMatrix.jumpHoldStepMeasure (by simpa [x] using hxabs) := by
      simpa [x] using hnonabs_hist (by simpa [x] using hxabs)
    rw [hdist]
    simpa [truncatedCenteredCoordIncrementFromHistory, x, a] using
      M.integral_jumpHoldStepMeasure_truncatedCenteredCoordIncrement_eq_zero
        (by simpa [x] using hxabs) i ha

/-- Conditional second moment of a clock-truncated centered coordinate
increment, expressed in terms of the clock-truncated holding-time mass. -/
theorem integral_condDistrib_truncatedCenteredCoordIncrementFromHistory_sq_eq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) (i : Fin d) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      (∫ r : QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1),
          (M.truncatedCenteredCoordIncrementFromHistory T n i hist r) ^ 2
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) =
        let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
        M.instantCoordQVRate x i *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist := by
  have hnonabs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ∀ h : ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist),
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => records (n + 1))
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.jumpHoldStepMeasure h := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_of_nonabsorbing
      x₀ n
  have habs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => records (n + 1))
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            Measure.dirac
              (0,
                QMatrix.currentStateFromHistory
                  (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_of_absorbing
      x₀ n
  have hhold_nonabs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ∀ h : ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist),
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.holdingTimeMeasure h := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing
      x₀ n
  filter_upwards [hnonabs, habs, hhold_nonabs] with hist hnonabs_hist habs_hist
    hhold_nonabs_hist
  let x : Fin d → Fin (M.N + 1) :=
    QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist
  let a : ℝ := QMatrix.historyClockRemaining T n hist
  have ha : 0 ≤ a := by
    simpa [a] using QMatrix.historyClockRemaining_nonneg T n hist
  by_cases hxabs : M.toQMatrix.IsAbsorbing x
  · have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
          Measure.dirac (0, x) := by
      simpa [x] using habs_hist (by simpa [x] using hxabs)
    rw [hdist]
    have hzero : M.exitRateAt x = 0 := by
      simpa [x, exitRateAt] using hxabs
    have hdrift : M.generatorDrift x i = 0 :=
      M.generatorDrift_eq_zero_of_exitRateAt_zero hzero i
    have hqv : M.instantCoordQVRate x i = 0 :=
      M.instantCoordQVRate_eq_zero_of_exitRateAt_zero hzero i
    simp [truncatedCenteredCoordIncrementFromHistory,
      truncatedCenteredCoordIncrement, x, a, ha, hdrift, hqv]
  · have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
          M.toQMatrix.jumpHoldStepMeasure (by simpa [x] using hxabs) := by
      simpa [x] using hnonabs_hist (by simpa [x] using hxabs)
    have hhold :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
          M.toQMatrix.holdingTimeMeasure (by simpa [x] using hxabs) := by
      simpa [x] using hhold_nonabs_hist (by simpa [x] using hxabs)
    rw [hdist, hhold]
    simpa [truncatedCenteredCoordIncrementFromHistory, x, a] using
      M.integral_jumpHoldStepMeasure_truncatedCenteredCoordIncrement_sq_eq
        (by simpa [x] using hxabs) i ha

/-- Conditional second moment of a clock-truncated vector jump square, expressed
in terms of the vector clock-QV increment. -/
theorem integral_condDistrib_truncatedJumpSqIncrementFromHistory_eq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      (∫ r : QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1),
          M.truncatedJumpSqIncrementFromHistory T n hist r
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) =
        let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
        M.instantQVRate x *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist := by
  have hnonabs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ∀ h : ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist),
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => records (n + 1))
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.jumpHoldStepMeasure h := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_of_nonabsorbing
      x₀ n
  have habs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => records (n + 1))
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            Measure.dirac
              (0,
                QMatrix.currentStateFromHistory
                  (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_of_absorbing
      x₀ n
  have hhold_nonabs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ∀ h : ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist),
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.holdingTimeMeasure h := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing
      x₀ n
  filter_upwards [hnonabs, habs, hhold_nonabs] with hist hnonabs_hist habs_hist
    hhold_nonabs_hist
  let x : Fin d → Fin (M.N + 1) :=
    QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist
  let a : ℝ := QMatrix.historyClockRemaining T n hist
  have ha : 0 ≤ a := by
    simpa [a] using QMatrix.historyClockRemaining_nonneg T n hist
  by_cases hxabs : M.toQMatrix.IsAbsorbing x
  · have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
          Measure.dirac (0, x) := by
      simpa [x] using habs_hist (by simpa [x] using hxabs)
    rw [hdist]
    have hzero : M.exitRateAt x = 0 := by
      simpa [x, exitRateAt] using hxabs
    have hqv : M.instantQVRate x = 0 :=
      M.instantQVRate_eq_zero_of_exitRateAt_zero hzero
    simp [truncatedJumpSqIncrementFromHistory, x, a, ha, hqv]
  · have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
          M.toQMatrix.jumpHoldStepMeasure (by simpa [x] using hxabs) := by
      simpa [x] using hnonabs_hist (by simpa [x] using hxabs)
    have hhold :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
          M.toQMatrix.holdingTimeMeasure (by simpa [x] using hxabs) := by
      simpa [x] using hhold_nonabs_hist (by simpa [x] using hxabs)
    rw [hdist, hhold]
    simpa [truncatedJumpSqIncrementFromHistory, x, a] using
      M.integral_jumpHoldStepMeasure_truncatedJumpSq_eq
        (by simpa [x] using hxabs) ha

/-- The clock-truncated vector jump-square increment is integrable under the
canonical record law. -/
theorem integrable_truncatedJumpSqIncrementFromHistory_next
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.truncatedJumpSqIncrementFromHistory T n
          (Preorder.frestrictLe n records) (records (n + 1)))
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let H : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records)
  let J : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.scaledState ((records (n + 1)).2) -
      M.scaledState
        (QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))‖ ^ 2
  let G : M.canonicalRecordΩ → ℝ := fun records =>
    if H records ≤ A records then (1 : ℝ) else 0
  have hH_meas : Measurable H := by
    dsimp [H]
    fun_prop
  have hA_meas : Measurable A := by
    dsimp [A, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
    exact measurable_const.max
      (measurable_const.sub
        (Finset.measurable_sum _ fun j _ => by fun_prop))
  have hcurr : Measurable
      (fun records : M.canonicalRecordΩ =>
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) := by
    exact (QMatrix.measurable_currentStateFromHistory
      (S := Fin d → Fin (M.N + 1)) n).comp
        (Preorder.measurable_frestrictLe n)
  have hnext : Measurable
      (fun records : M.canonicalRecordΩ => (records (n + 1)).2) := by
    fun_prop
  have hvec : Measurable (fun records : M.canonicalRecordΩ =>
      M.scaledState ((records (n + 1)).2) -
        M.scaledState
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))) := by
    rw [measurable_pi_iff]
    intro i
    have hnext_i : Measurable
        (fun records : M.canonicalRecordΩ =>
          M.scaledState ((records (n + 1)).2) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
    have hcurr_i : Measurable
        (fun records : M.canonicalRecordΩ =>
          M.scaledState
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
    simpa [Pi.sub_apply] using hnext_i.sub hcurr_i
  have hJ_meas : Measurable J := by
    dsimp [J]
    exact hvec.norm.pow_const 2
  have hG_meas : Measurable G := by
    dsimp [G]
    exact Measurable.ite (measurableSet_le hH_meas hA_meas)
      measurable_const measurable_const
  have hraw_meas : AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ =>
        M.truncatedJumpSqIncrementFromHistory T n
          (Preorder.frestrictLe n records) (records (n + 1))) μ := by
    refine ((hG_meas.mul hJ_meas).aestronglyMeasurable).congr ?_
    refine ae_of_all _ fun records => ?_
    dsimp [G, J, H, A, truncatedJumpSqIncrementFromHistory]
    by_cases hle : (records (n + 1)).1 ≤
        QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records)
    · simp [Set.indicator, hle]
    · simp [Set.indicator, hle]
  refine Integrable.of_bound hraw_meas 4 ?_
  refine ae_of_all _ fun records => ?_
  rw [Real.norm_eq_abs]
  have hraw_nonneg :
      0 ≤ M.truncatedJumpSqIncrementFromHistory T n
          (Preorder.frestrictLe n records) (records (n + 1)) := by
    dsimp [truncatedJumpSqIncrementFromHistory]
    by_cases hle : (records (n + 1)).1 ≤
        QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records)
    · simp [Set.indicator, hle, sq_nonneg]
    · simp [Set.indicator, hle]
  rw [abs_of_nonneg hraw_nonneg]
  dsimp [truncatedJumpSqIncrementFromHistory]
  by_cases hle : (records (n + 1)).1 ≤
      QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records)
  · simp [Set.indicator, hle]
    let v :=
      M.scaledState ((records (n + 1)).2) -
        M.scaledState
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
    have hv : ‖v‖ ≤ 2 := by
      calc
        ‖v‖ ≤ ‖M.scaledState ((records (n + 1)).2)‖ +
            ‖M.scaledState
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n
                (Preorder.frestrictLe n records))‖ := by
              simpa [v] using norm_sub_le
                (M.scaledState ((records (n + 1)).2))
                (M.scaledState
                  (QMatrix.currentStateFromHistory
                    (S := Fin d → Fin (M.N + 1)) n
                    (Preorder.frestrictLe n records)))
        _ ≤ 1 + 1 := add_le_add
            (M.scaledState_norm_le ((records (n + 1)).2))
            (M.scaledState_norm_le
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n
                (Preorder.frestrictLe n records)))
        _ = 2 := by norm_num
    have hsq : ‖v‖ ^ 2 ≤ (2 : ℝ) ^ 2 :=
      sq_le_sq' (by nlinarith [norm_nonneg v]) hv
    norm_num at hsq
    simpa [v] using hsq
  · simp [Set.indicator, hle]

/-- Unconditional integral form of the clock-truncated vector jump-square
conditional identity. -/
theorem integral_clockQVIntegral_eq_integral_truncatedJumpSqIncrement
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantQVRate x *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist)
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        M.truncatedJumpSqIncrementFromHistory T n
          (Preorder.frestrictLe n records) (records (n + 1))
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ →
      QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1) :=
    fun records => records (n + 1)
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
        QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
    fun p => M.truncatedJumpSqIncrementFromHistory T n p.1 p.2
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => records (n + 1))).aemeasurable
  have hf_meas : Measurable f := by
    have hH : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          p.2.1) := measurable_snd.fst
    have hA : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          QMatrix.historyClockRemaining T n p.1) := by
      dsimp [QMatrix.historyClockRemaining, QMatrix.historySojournStart]
      exact measurable_const.max
        (measurable_const.sub
          (Finset.measurable_sum _ fun j _ => by fun_prop))
    have hgate : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          Set.indicator (Set.Iic (QMatrix.historyClockRemaining T n p.1))
            (fun _ : ℝ => (1 : ℝ)) p.2.1) := by
      have hite : Measurable
          (fun p :
            (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
              QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
            if p.2.1 ≤ QMatrix.historyClockRemaining T n p.1 then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_le hH hA) measurable_const measurable_const
      simpa [Set.indicator] using hite
    have hcurr : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) :=
      (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp measurable_fst
    have hnext : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          p.2.2) := measurable_snd.snd
    have hvec : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          M.scaledState p.2.2 -
            M.scaledState
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n p.1)) := by
      rw [measurable_pi_iff]
      intro i
      have hnext_i : Measurable
          (fun p :
            (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
              QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
            M.scaledState p.2.2 i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
      have hcurr_i : Measurable
          (fun p :
            (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
              QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
            M.scaledState
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n p.1) i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
      simpa [Pi.sub_apply] using hnext_i.sub hcurr_i
    dsimp [f, truncatedJumpSqIncrementFromHistory]
    exact hgate.mul (hvec.norm.pow_const 2)
  have hf_int : Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa using M.integrable_truncatedJumpSqIncrementFromHistory_next x₀ T n
  have hprod :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  have hcond_hist :=
    M.integral_condDistrib_truncatedJumpSqIncrementFromHistory_eq x₀ T n
  have hcond_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      hcond_hist
  have hcond :
      μ[(fun a : M.canonicalRecordΩ => f (X a, Y a)) |
        MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun records : M.canonicalRecordΩ =>
        let hist := X records
        let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
        M.instantQVRate x *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) μ hist := by
    filter_upwards [hprod, hcond_records] with records hprod_records hcond_records
    rw [hprod_records]
    simpa [f, X, Y, μ] using hcond_records
  calc
    ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantQVRate x *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist)
        ∂M.canonicalRecordMeasure x₀
        = ∫ records,
            (μ[(fun a : M.canonicalRecordΩ => f (X a, Y a)) |
              MeasurableSpace.comap X inferInstance]) records ∂μ := by
            exact (integral_congr_ae hcond).symm
    _ = ∫ records, f (X records, Y records) ∂μ := by
          exact integral_condExp
            (μ := μ)
            (m := MeasurableSpace.comap X inferInstance)
            (f := fun a : M.canonicalRecordΩ => f (X a, Y a))
            hX.comap_le
    _ = ∫ records,
        M.truncatedJumpSqIncrementFromHistory T n
          (Preorder.frestrictLe n records) (records (n + 1))
        ∂M.canonicalRecordMeasure x₀ := by
          simp [f, X, Y, μ]

/-- Finite-sum version of
`integral_clockQVIntegral_eq_integral_truncatedJumpSqIncrement` for vector
jump squares. -/
theorem integral_sum_truncatedJumpSqIncrement_eq_sum_clockQVIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∫ records,
        (∑ k ∈ Finset.range n,
          M.truncatedJumpSqIncrementFromHistory T k
            (Preorder.frestrictLe k records) (records (k + 1)))
        ∂M.canonicalRecordMeasure x₀ =
      ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantQVRate x *
            ∫ t : ℝ, min t (QMatrix.historyClockRemaining T k hist)
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (k + 1)).1)
                (Preorder.frestrictLe k) (M.canonicalRecordMeasure x₀) hist)
          ∂M.canonicalRecordMeasure x₀ := by
  rw [integral_finset_sum (Finset.range n)]
  · refine Finset.sum_congr rfl ?_
    intro k _hk
    exact (M.integral_clockQVIntegral_eq_integral_truncatedJumpSqIncrement
      x₀ T k).symm
  · intro k _hk
    exact M.integrable_truncatedJumpSqIncrementFromHistory_next x₀ T k

/-- The clock-truncated one-step coordinate increment is integrable under the
canonical record law. -/
theorem integrable_truncatedCenteredCoordIncrementFromHistory_next
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) (i : Fin d) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1)))
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let H : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records)
  let J : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState
        (QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))) i
  let D : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift
      (QMatrix.currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) i
  let Prev : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ j : Fin n, ‖(records (j.1 + 1)).1‖
  obtain ⟨C, hC_nonneg, hC⟩ := M.exists_generatorDrift_abs_bound i
  have hH_meas : Measurable H := by
    dsimp [H]
    fun_prop
  have hA_meas : Measurable A := by
    dsimp [A, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
    exact measurable_const.max
      (measurable_const.sub
        (Finset.measurable_sum _ fun j _ =>
          (by
            change Measurable
              (fun records : M.canonicalRecordΩ => (records (j.1 + 1)).1)
            fun_prop)))
  have hJ_meas : Measurable J := by
    dsimp [J]
    have hnext : Measurable
        (fun records : M.canonicalRecordΩ => (records (n + 1)).2) := by
      fun_prop
    have hcurr : Measurable
        (fun records : M.canonicalRecordΩ =>
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) := by
      exact (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp
          (Preorder.measurable_frestrictLe n)
    have hnext_coord : Measurable
        (fun records : M.canonicalRecordΩ =>
          M.scaledState ((records (n + 1)).2) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
    have hcurr_coord : Measurable
        (fun records : M.canonicalRecordΩ =>
          M.scaledState
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
    simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord
  have hD_meas : Measurable D := by
    dsimp [D]
    have hcurr : Measurable
        (fun records : M.canonicalRecordΩ =>
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) := by
      exact (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp
          (Preorder.measurable_frestrictLe n)
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x i)).comp hcurr
  have hinc_meas : Measurable
      (fun records : M.canonicalRecordΩ =>
        M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1))) := by
    have hgate : Measurable
        (fun records : M.canonicalRecordΩ =>
          if H records ≤ A records then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le hH_meas hA_meas)
        measurable_const measurable_const
    have hmin : Measurable (fun records : M.canonicalRecordΩ =>
        min (H records) (A records)) :=
      hH_meas.min hA_meas
    dsimp [truncatedCenteredCoordIncrementFromHistory,
      truncatedCenteredCoordIncrement, H, A, J, D]
    simpa using (hgate.mul hJ_meas).sub (hD_meas.mul hmin)
  have hH_int : Integrable H μ := by
    simpa [H, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ n
  have hPrev_int : Integrable Prev μ := by
    dsimp [Prev]
    refine integrable_finsetSum Finset.univ ?_
    intro j _hj
    have hj_int :
        Integrable (fun records : M.canonicalRecordΩ =>
          (records (j.1 + 1)).1) μ := by
      simpa [μ] using
        M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ j.1
    exact hj_int.norm
  have hdom_int : Integrable
      (fun records : M.canonicalRecordΩ =>
        2 + C * (‖H records‖ + (‖T‖ + Prev records))) μ := by
    exact (integrable_const 2).add
      ((hH_int.norm.add ((integrable_const ‖T‖).add hPrev_int)).const_mul C)
  refine hdom_int.mono' hinc_meas.aestronglyMeasurable ?_
  refine ae_of_all _ fun records => ?_
  have hJ_bound : ‖J records‖ ≤ 2 := by
    dsimp [J]
    exact M.scaledState_sub_apply_norm_le_two
      (QMatrix.currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
      ((records (n + 1)).2) i
  have hD_bound : ‖D records‖ ≤ C := by
    dsimp [D]
    exact hC _
  have hA_bound : ‖A records‖ ≤ ‖T‖ + Prev records := by
    dsimp [A, Prev, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
    calc
      ‖max 0 (T -
          ∑ j : Fin n, (records (j.1 + 1)).1)‖
          ≤ max ‖(0 : ℝ)‖ ‖T -
              ∑ j : Fin n, (records (j.1 + 1)).1‖ := by
            simpa [Real.norm_eq_abs] using
              abs_max_le_max_abs_abs (a := (0 : ℝ))
                (b := T - ∑ j : Fin n, (records (j.1 + 1)).1)
      _ ≤ ‖T - ∑ j : Fin n, (records (j.1 + 1)).1‖ := by
            simp
      _ ≤ ‖T‖ + ‖∑ j : Fin n, (records (j.1 + 1)).1‖ := by
            simpa [sub_eq_add_neg, norm_neg] using
              norm_add_le T (-(∑ j : Fin n, (records (j.1 + 1)).1))
      _ ≤ ‖T‖ + ∑ j : Fin n, ‖(records (j.1 + 1)).1‖ := by
            have hsum_abs :
                ‖∑ j : Fin n, (records (j.1 + 1)).1‖ ≤
                  ∑ j : Fin n, ‖(records (j.1 + 1)).1‖ := by
              simpa [Real.norm_eq_abs] using
                Finset.abs_sum_le_sum_abs
                  (fun j : Fin n => (records (j.1 + 1)).1) Finset.univ
            linarith
  have hmin_bound : ‖min (H records) (A records)‖ ≤ ‖H records‖ + (‖T‖ + Prev records) := by
    calc
      ‖min (H records) (A records)‖
          ≤ max ‖H records‖ ‖A records‖ := by
            simpa [Real.norm_eq_abs] using
              abs_min_le_max_abs_abs (a := H records) (b := A records)
      _ ≤ ‖H records‖ + ‖A records‖ :=
            max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖H records‖ + (‖T‖ + Prev records) := by
            linarith
  calc
    ‖M.truncatedCenteredCoordIncrementFromHistory T n i
        (Preorder.frestrictLe n records) (records (n + 1))‖
        ≤ ‖(if H records ≤ A records then (1 : ℝ) else 0) * J records‖ +
            ‖D records * min (H records) (A records)‖ := by
          dsimp [truncatedCenteredCoordIncrementFromHistory,
            truncatedCenteredCoordIncrement, H, A, J, D]
          simpa [Real.norm_eq_abs] using norm_sub_le
            ((if (records (n + 1)).1 ≤
                QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records) then
                (1 : ℝ) else 0) *
              (M.scaledState (records (n + 1)).2 i -
                M.scaledState
                  (QMatrix.currentStateFromHistory
                    (S := Fin d → Fin (M.N + 1)) n
                    (Preorder.frestrictLe n records)) i))
            (M.generatorDrift
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n
                (Preorder.frestrictLe n records)) i *
              min (records (n + 1)).1
                (QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records)))
    _ ≤ 2 + C * (‖H records‖ + (‖T‖ + Prev records)) := by
          have hgate_norm :
              ‖(if H records ≤ A records then (1 : ℝ) else 0)‖ ≤ 1 := by
            by_cases hle : H records ≤ A records <;> simp [hle]
          calc
            ‖(if H records ≤ A records then (1 : ℝ) else 0) * J records‖ +
                ‖D records * min (H records) (A records)‖
                ≤ 1 * 2 + C * (‖H records‖ + (‖T‖ + Prev records)) := by
                  rw [norm_mul, norm_mul]
                  exact add_le_add
                    (mul_le_mul hgate_norm hJ_bound (norm_nonneg _) (by norm_num))
                    (mul_le_mul hD_bound hmin_bound
                      (norm_nonneg _)
                      hC_nonneg)
            _ = 2 + C * (‖H records‖ + (‖T‖ + Prev records)) := by ring

/-- Conditional expectation form of the clock-truncated one-step martingale
increment. -/
theorem condExp_truncatedCenteredCoordIncrementFromHistory_next_eq_zero_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1)))
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  rw [canonicalRecordFiltration,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ →
      QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1) :=
    fun records => records (n + 1)
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
        QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
    fun p => M.truncatedCenteredCoordIncrementFromHistory T n i p.1 p.2
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => records (n + 1))).aemeasurable
  have hf_meas : Measurable f := by
    let H :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => p.2.1
    let A :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => QMatrix.historyClockRemaining T n p.1
    let J :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => (M.scaledState p.2.2 -
        M.scaledState
          (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1)) i
    let D :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => M.generatorDrift
        (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i
    have hH : Measurable H := by
      dsimp [H]
      exact measurable_fst.comp measurable_snd
    have hA : Measurable A := by
      dsimp [A, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
      exact measurable_const.max
        (measurable_const.sub
          (Finset.measurable_sum _ fun j _ =>
            (by
              change Measurable
                (fun p :
                  (((j : Finset.Iic n) →
                      QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
                    QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
                  (p.1 ⟨j.1 + 1, Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩).1)
              fun_prop)))
    have hcurr : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) :=
      (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp measurable_fst
    have hnext : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          p.2.2) := measurable_snd.comp measurable_snd
    have hJ : Measurable J := by
      dsimp [J]
      have hnext_coord : Measurable
          (fun p :
            (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
              QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
            M.scaledState p.2.2 i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
      have hcurr_coord : Measurable
          (fun p :
            (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
              QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
            M.scaledState
              (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
      simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord
    have hD : Measurable D := by
      dsimp [D]
      exact (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x i)).comp hcurr
    have hgate : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          if H p ≤ A p then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le hH hA) measurable_const measurable_const
    have hmin : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          min (H p) (A p)) :=
      hH.min hA
    dsimp [f, truncatedCenteredCoordIncrementFromHistory,
      truncatedCenteredCoordIncrement, H, A, J, D]
    simpa using (hgate.mul hJ).sub (hD.mul hmin)
  have hf_int : Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa using
      M.integrable_truncatedCenteredCoordIncrementFromHistory_next x₀ T n i
  have hprod :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  have hzero_hist :=
    M.integral_condDistrib_truncatedCenteredCoordIncrementFromHistory_eq_zero
      x₀ T n i
  have hzero_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      hzero_hist
  filter_upwards [hprod, hzero_records] with records hprod_records hzero_records
  rw [hprod_records]
  simpa [μ, X, Y, f] using hzero_records

/-- Canonical-record version of the horizon-truncated coordinate martingale. -/
noncomputable def canonicalFrozenClockTruncatedMartingale
    (M : DensityDepCTMC d) (T : ℝ) (i : Fin d)
    (n : ℕ) (records : M.canonicalRecordΩ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.truncatedCenteredCoordIncrementFromHistory T k i
      (Preorder.frestrictLe k records) (records (k + 1))

@[simp]
theorem canonicalFrozenClockTruncatedMartingale_zero
    (M : DensityDepCTMC d) (T : ℝ) (i : Fin d)
    (records : M.canonicalRecordΩ) :
    M.canonicalFrozenClockTruncatedMartingale T i 0 records = 0 := by
  simp [canonicalFrozenClockTruncatedMartingale]

theorem canonicalFrozenClockTruncatedMartingale_succ
    (M : DensityDepCTMC d) (T : ℝ) (i : Fin d)
    (n : ℕ) (records : M.canonicalRecordΩ) :
    M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records =
      M.canonicalFrozenClockTruncatedMartingale T i n records +
        M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1)) := by
  simp [canonicalFrozenClockTruncatedMartingale, Finset.sum_range_succ]

theorem canonicalFrozenClockTruncatedMartingale_succ_sub
    (M : DensityDepCTMC d) (T : ℝ) (i : Fin d)
    (n : ℕ) (records : M.canonicalRecordΩ) :
    M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records -
        M.canonicalFrozenClockTruncatedMartingale T i n records =
      M.truncatedCenteredCoordIncrementFromHistory T n i
        (Preorder.frestrictLe n records) (records (n + 1)) := by
  rw [M.canonicalFrozenClockTruncatedMartingale_succ]
  ring

/-- The path and canonical-record definitions of the truncated martingale
agree on canonical paths. -/
theorem frozenClockTruncatedMartingale_canonicalPathMap_eq
    (M : DensityDepCTMC d) (T : ℝ) (i : Fin d)
    (n : ℕ) (records : M.canonicalRecordΩ) :
    M.frozenClockTruncatedMartingale (M.canonicalPathMap records) i T n =
      M.canonicalFrozenClockTruncatedMartingale T i n records := by
  simp only [frozenClockTruncatedMartingale,
    canonicalFrozenClockTruncatedMartingale]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  have hstart :
      QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
        max 0 (T - (M.canonicalPathMap records).sojournStart k) := by
    simp [QMatrix.historyClockRemaining,
      QMatrix.historySojournStart_frestrictLe, canonicalPathMap]
  simp [truncatedCenteredCoordIncrementFromHistory,
    truncatedCenteredCoordIncrement, canonicalPathMap,
    QMatrix.currentStateFromHistory_frestrictLe,
    QMatrix.recordTrajectoryToPath_stateSeq,
    QMatrix.recordTrajectoryToPath_sojournTime, hstart]

theorem integrable_canonicalFrozenClockTruncatedMartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.canonicalFrozenClockTruncatedMartingale T i n records)
      (M.canonicalRecordMeasure x₀) := by
  simp only [canonicalFrozenClockTruncatedMartingale]
  refine integrable_finsetSum (Finset.range n) ?_
  intro k _hk
  exact M.integrable_truncatedCenteredCoordIncrementFromHistory_next x₀ T k i

theorem measurable_truncatedCenteredCoordIncrementFromHistory_next_canonicalRecordFiltration_le
    (M : DensityDepCTMC d) (T : ℝ) (i : Fin d)
    {k m : ℕ} (hkm : k + 1 ≤ m) :
    Measurable[M.canonicalRecordFiltration m]
      (fun records : M.canonicalRecordΩ =>
        M.truncatedCenteredCoordIncrementFromHistory T k i
          (Preorder.frestrictLe k records) (records (k + 1))) := by
  let H : M.canonicalRecordΩ → ℝ := fun records => (records (k + 1)).1
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)
  let J : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (k + 1)).2) -
      M.scaledState
        (QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records))) i
  let D : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift
      (QMatrix.currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) i
  have hrec :
      Measurable[M.canonicalRecordFiltration m]
        (fun records : M.canonicalRecordΩ => records (k + 1)) := by
    simpa [canonicalRecordFiltration] using
      QMatrix.measurable_record_canonicalRecordFiltration_le
        (S := Fin d → Fin (M.N + 1)) hkm
  have hH : Measurable[M.canonicalRecordFiltration m] H := by
    dsimp [H]
    exact hrec.fst
  have hA : Measurable[M.canonicalRecordFiltration m] A := by
    dsimp [A, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
    exact measurable_const.max
      (measurable_const.sub
        (Finset.measurable_sum _ fun j _ =>
          (by
            have hjm : j.1 + 1 ≤ m := by omega
            simpa [canonicalRecordFiltration] using
              (QMatrix.measurable_record_canonicalRecordFiltration_le
                (S := Fin d → Fin (M.N + 1)) hjm).fst)))
  have hcurr :
      Measurable[M.canonicalRecordFiltration m]
        (fun records : M.canonicalRecordΩ =>
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) := by
    have hkm' : k ≤ m := le_trans (Nat.le_succ k) hkm
    simpa [canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using
      M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le hkm'
  have hnext : Measurable[M.canonicalRecordFiltration m]
      (fun records : M.canonicalRecordΩ => (records (k + 1)).2) := by
    exact hrec.snd
  have hJ : Measurable[M.canonicalRecordFiltration m] J := by
    dsimp [J]
    have hnext_coord : Measurable[M.canonicalRecordFiltration m]
        (fun records : M.canonicalRecordΩ =>
          M.scaledState ((records (k + 1)).2) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
    have hcurr_coord : Measurable[M.canonicalRecordFiltration m]
        (fun records : M.canonicalRecordΩ =>
          M.scaledState
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
    simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord
  have hD : Measurable[M.canonicalRecordFiltration m] D := by
    dsimp [D]
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x i)).comp hcurr
  have hgate : Measurable[M.canonicalRecordFiltration m]
      (fun records : M.canonicalRecordΩ =>
        if H records ≤ A records then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le hH hA) measurable_const measurable_const
  have hmin : Measurable[M.canonicalRecordFiltration m]
      (fun records : M.canonicalRecordΩ => min (H records) (A records)) :=
    hH.min hA
  dsimp [truncatedCenteredCoordIncrementFromHistory,
    truncatedCenteredCoordIncrement, H, A, J, D]
  simpa using (hgate.mul hJ).sub (hD.mul hmin)

theorem measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
    (M : DensityDepCTMC d) (T : ℝ) (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.canonicalFrozenClockTruncatedMartingale T i n records) := by
  simp only [canonicalFrozenClockTruncatedMartingale]
  refine Finset.measurable_sum _ ?_
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  exact
    M.measurable_truncatedCenteredCoordIncrementFromHistory_next_canonicalRecordFiltration_le
      T i (Nat.succ_le_of_lt hklt)

theorem stronglyAdapted_canonicalFrozenClockTruncatedMartingale
    (M : DensityDepCTMC d) (T : ℝ) (i : Fin d) :
    StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.canonicalFrozenClockTruncatedMartingale T i n records) := by
  intro n
  exact (M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
    T i n).stronglyMeasurable

theorem canonicalFrozenClockTruncatedMartingale_condExp_increment_eq_zero_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records -
          M.canonicalFrozenClockTruncatedMartingale T i n records)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  let μ := M.canonicalRecordMeasure x₀
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records -
          M.canonicalFrozenClockTruncatedMartingale T i n records)
        =ᵐ[μ]
      fun records =>
        M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1)) := by
    refine ae_of_all _ fun records => ?_
    exact M.canonicalFrozenClockTruncatedMartingale_succ_sub T i n records
  refine (MeasureTheory.condExp_congr_ae hinc).trans ?_
  exact M.condExp_truncatedCenteredCoordIncrementFromHistory_next_eq_zero_ae
    x₀ T n i

theorem canonicalFrozenClockTruncatedMartingale_martingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) :
    Martingale
      (fun n records =>
        M.canonicalFrozenClockTruncatedMartingale T i n records)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  martingale_of_condExp_sub_eq_zero_nat
    (M.stronglyAdapted_canonicalFrozenClockTruncatedMartingale T i)
    (M.integrable_canonicalFrozenClockTruncatedMartingale x₀ T i)
    (fun n =>
      M.canonicalFrozenClockTruncatedMartingale_condExp_increment_eq_zero_ae
        x₀ T n i)

/- theorem condExp_truncatedCenteredCoordIncrementFromHistory_next_sq_eq_clockQVIntegral_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        (M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1))) ^ 2)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀]
      fun records : M.canonicalRecordΩ =>
        let hist := Preorder.frestrictLe n records
        let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
        M.instantCoordQVRate x i *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist := by
  rw [canonicalRecordFiltration,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ →
      QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1) :=
    fun records => records (n + 1)
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
        QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
    fun p => (M.truncatedCenteredCoordIncrementFromHistory T n i p.1 p.2) ^ 2
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => records (n + 1))).aemeasurable
  have hf_meas : Measurable f := by
    let H :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => p.2.1
    let A :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => QMatrix.historyClockRemaining T n p.1
    let J :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => (M.scaledState p.2.2 -
        M.scaledState
          (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1)) i
    let D :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => M.generatorDrift
        (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i
    have hH : Measurable H := by
      dsimp [H]
      exact measurable_fst.comp measurable_snd
    have hA : Measurable A := by
      dsimp [A, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
      exact measurable_const.max
        (measurable_const.sub
          (Finset.measurable_sum _ fun j _ =>
            (by
              fun_prop)))
    have hcurr : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) :=
      (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp measurable_fst
    have hnext : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          p.2.2) := measurable_snd.comp measurable_snd
    have hJ : Measurable J := by
      dsimp [J]
      have hnext_coord : Measurable
          (fun p :
            (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
              QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
            M.scaledState p.2.2 i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
      have hcurr_coord : Measurable
          (fun p :
            (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
              QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
            M.scaledState
              (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
      simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord
    have hD : Measurable D := by
      dsimp [D]
      exact (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x i)).comp hcurr
    have hgate : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          if H p ≤ A p then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le hH hA) measurable_const measurable_const
    have hmin : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          min (H p) (A p)) :=
      hH.min hA
    dsimp [f, truncatedCenteredCoordIncrementFromHistory,
      truncatedCenteredCoordIncrement, H, A, J, D]
    exact ((hgate.mul hJ).sub (hD.mul hmin)).pow_const 2
  have hf_int : Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa using
      M.integrable_truncatedCenteredCoordIncrementFromHistory_next_sq x₀ T n i
  have hprod :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  have hsq_hist :=
    M.integral_condDistrib_truncatedCenteredCoordIncrementFromHistory_sq_eq
      x₀ T n i
  have hsq_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      hsq_hist
  filter_upwards [hprod, hsq_records] with records hprod_records hsq_records
  rw [hprod_records]
  simpa [μ, X, Y, f] using hsq_records -/

theorem integrable_truncatedCenteredCoordIncrementFromHistory_next_sq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) (i : Fin d) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1))) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let H : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records)
  let J : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState
        (QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))) i
  let D : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift
      (QMatrix.currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) i
  let Prev : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ j : Fin n, ‖(records (j.1 + 1)).1‖
  let G : M.canonicalRecordΩ → ℝ := fun records =>
    if H records ≤ A records then (1 : ℝ) else 0
  let JumpPart : M.canonicalRecordΩ → ℝ := fun records => G records * J records
  let DriftPart : M.canonicalRecordΩ → ℝ := fun records =>
    D records * min (H records) (A records)
  obtain ⟨C, hC_nonneg, hC⟩ := M.exists_generatorDrift_abs_bound i
  have hH_meas : Measurable H := by
    dsimp [H]
    fun_prop
  have hA_meas : Measurable A := by
    dsimp [A, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
    exact measurable_const.max
      (measurable_const.sub
        (Finset.measurable_sum _ fun j _ =>
          (by
            fun_prop)))
  have hcurr : Measurable
      (fun records : M.canonicalRecordΩ =>
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) := by
    exact (QMatrix.measurable_currentStateFromHistory
      (S := Fin d → Fin (M.N + 1)) n).comp
        (Preorder.measurable_frestrictLe n)
  have hnext : Measurable
      (fun records : M.canonicalRecordΩ => (records (n + 1)).2) := by
    fun_prop
  have hJ_meas : Measurable J := by
    dsimp [J]
    have hnext_coord : Measurable
        (fun records : M.canonicalRecordΩ =>
          M.scaledState ((records (n + 1)).2) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
    have hcurr_coord : Measurable
        (fun records : M.canonicalRecordΩ =>
          M.scaledState
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
    simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord
  have hD_meas : Measurable D := by
    dsimp [D]
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x i)).comp hcurr
  have hG_meas : Measurable G := by
    dsimp [G]
    exact Measurable.ite (measurableSet_le hH_meas hA_meas)
      measurable_const measurable_const
  have hmin_meas : Measurable (fun records : M.canonicalRecordΩ =>
      min (H records) (A records)) :=
    hH_meas.min hA_meas
  have hJump_memLp : MemLp JumpPart 2 μ := by
    have hJump_meas : AEStronglyMeasurable JumpPart μ := by
      dsimp [JumpPart]
      exact (hG_meas.mul hJ_meas).aestronglyMeasurable
    refine MemLp.of_bound hJump_meas 2 ?_
    refine ae_of_all _ fun records => ?_
    dsimp [JumpPart, G, J]
    rw [abs_mul]
    have hgate : ‖(if H records ≤ A records then (1 : ℝ) else 0)‖ ≤ 1 := by
      by_cases hle : H records ≤ A records <;> simp [hle]
    have hjump : ‖(M.scaledState ((records (n + 1)).2) -
        M.scaledState
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))) i‖ ≤ 2 :=
      M.scaledState_sub_apply_norm_le_two
        (QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
        ((records (n + 1)).2) i
    calc
      ‖(if H records ≤ A records then (1 : ℝ) else 0)‖ *
          ‖(M.scaledState ((records (n + 1)).2) -
            M.scaledState
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n
                (Preorder.frestrictLe n records))) i‖
          ≤ 1 * 2 := by
            exact mul_le_mul hgate hjump (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hH_memLp : MemLp H 2 μ := by
    exact (memLp_two_iff_integrable_sq hH_meas.aestronglyMeasurable).2
      (by
        simpa [H, μ] using
          M.integrable_next_holdingTime_sq_canonicalRecordMeasure_guarded x₀ n)
  have hPrev_memLp : MemLp Prev 2 μ := by
    dsimp [Prev]
    refine memLp_finset_sum Finset.univ ?_
    intro j _hj
    have hj_meas : Measurable
        (fun records : M.canonicalRecordΩ => (records (j.1 + 1)).1) := by
      fun_prop
    have hj_memLp : MemLp
        (fun records : M.canonicalRecordΩ => (records (j.1 + 1)).1) 2 μ := by
      exact (memLp_two_iff_integrable_sq hj_meas.aestronglyMeasurable).2
        (by
          simpa [μ] using
            M.integrable_next_holdingTime_sq_canonicalRecordMeasure_guarded x₀ j.1)
    simpa using hj_memLp.norm
  have hdom_memLp :
      MemLp
        (fun records : M.canonicalRecordΩ =>
          C * (‖H records‖ + (‖T‖ + Prev records))) 2 μ := by
    have hbase : MemLp
        (fun records : M.canonicalRecordΩ =>
          ‖H records‖ + (‖T‖ + Prev records)) 2 μ := by
      have hconst : MemLp (fun _ : M.canonicalRecordΩ => ‖T‖) 2 μ :=
        memLp_const _
      simpa [Pi.add_apply] using
        hH_memLp.norm.add (hconst.add hPrev_memLp)
    simpa [mul_comm] using hbase.const_mul C
  have hDrift_memLp : MemLp DriftPart 2 μ := by
    have hDrift_meas : AEStronglyMeasurable DriftPart μ := by
      dsimp [DriftPart]
      exact (hD_meas.mul hmin_meas).aestronglyMeasurable
    have hbound :
        ∀ᵐ records ∂μ,
          ‖DriftPart records‖ ≤
            C * (‖H records‖ + (‖T‖ + Prev records)) := by
      refine ae_of_all _ fun records => ?_
      dsimp [DriftPart]
      rw [abs_mul]
      have hD_bound : ‖D records‖ ≤ C := hC _
      have hA_bound : ‖A records‖ ≤ ‖T‖ + Prev records := by
        dsimp [A, Prev, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
        calc
          ‖max 0 (T -
              ∑ j : Fin n, (records (j.1 + 1)).1)‖
              ≤ max ‖(0 : ℝ)‖ ‖T -
                  ∑ j : Fin n, (records (j.1 + 1)).1‖ := by
                simpa [Real.norm_eq_abs] using
                  abs_max_le_max_abs_abs (a := (0 : ℝ))
                    (b := T - ∑ j : Fin n, (records (j.1 + 1)).1)
          _ ≤ ‖T - ∑ j : Fin n, (records (j.1 + 1)).1‖ := by
                simp
          _ ≤ ‖T‖ + ‖∑ j : Fin n, (records (j.1 + 1)).1‖ := by
                simpa [sub_eq_add_neg, norm_neg] using
                  norm_add_le T (-(∑ j : Fin n, (records (j.1 + 1)).1))
          _ ≤ ‖T‖ + ∑ j : Fin n, ‖(records (j.1 + 1)).1‖ := by
                have hsum_abs :
                    ‖∑ j : Fin n, (records (j.1 + 1)).1‖ ≤
                      ∑ j : Fin n, ‖(records (j.1 + 1)).1‖ := by
                  simpa [Real.norm_eq_abs] using
                    Finset.abs_sum_le_sum_abs
                      (fun j : Fin n => (records (j.1 + 1)).1) Finset.univ
                linarith
      have hmin_bound :
          ‖min (H records) (A records)‖ ≤
            ‖H records‖ + (‖T‖ + Prev records) := by
        calc
          ‖min (H records) (A records)‖
              ≤ max ‖H records‖ ‖A records‖ := by
                simpa [Real.norm_eq_abs] using
                  abs_min_le_max_abs_abs (a := H records) (b := A records)
          _ ≤ ‖H records‖ + ‖A records‖ :=
                max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
          _ ≤ ‖H records‖ + (‖T‖ + Prev records) := by
                linarith
      exact mul_le_mul hD_bound hmin_bound
        (abs_nonneg _) hC_nonneg
    exact hdom_memLp.mono' hDrift_meas hbound
  have hinc_memLp : MemLp
      (fun records : M.canonicalRecordΩ =>
        M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1))) 2 μ := by
    refine (memLp_congr_ae ?_).2 (hJump_memLp.sub hDrift_memLp)
    refine ae_of_all _ fun records => ?_
    show
      M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1)) =
        (JumpPart - DriftPart) records
    dsimp [JumpPart, DriftPart, G, H, A, J, D,
      truncatedCenteredCoordIncrementFromHistory,
      truncatedCenteredCoordIncrement]
  simpa [μ] using hinc_memLp.integrable_sq

theorem condExp_truncatedCenteredCoordIncrementFromHistory_next_sq_eq_clockQVIntegral_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        (M.truncatedCenteredCoordIncrementFromHistory T n i
          (Preorder.frestrictLe n records) (records (n + 1))) ^ 2)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀]
      fun records : M.canonicalRecordΩ =>
        let hist := Preorder.frestrictLe n records
        let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
        M.instantCoordQVRate x i *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist := by
  rw [canonicalRecordFiltration,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ →
      QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1) :=
    fun records => records (n + 1)
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
        QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
    fun p => (M.truncatedCenteredCoordIncrementFromHistory T n i p.1 p.2) ^ 2
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => records (n + 1))).aemeasurable
  have hf_meas : Measurable f := by
    let H :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => p.2.1
    let A :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => QMatrix.historyClockRemaining T n p.1
    let J :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => (M.scaledState p.2.2 -
        M.scaledState
          (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1)) i
    let D :
        (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
      fun p => M.generatorDrift
        (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i
    have hH : Measurable H := by
      dsimp [H]
      exact measurable_fst.comp measurable_snd
    have hA : Measurable A := by
      dsimp [A, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
      exact measurable_const.max
        (measurable_const.sub
          (Finset.measurable_sum _ fun j _ =>
            (by
              fun_prop)))
    have hcurr : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) :=
      (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp measurable_fst
    have hnext : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          p.2.2) := measurable_snd.comp measurable_snd
    have hJ : Measurable J := by
      dsimp [J]
      have hnext_coord : Measurable
          (fun p :
            (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
              QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
            M.scaledState p.2.2 i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
      have hcurr_coord : Measurable
          (fun p :
            (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
              QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
            M.scaledState
              (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i) :=
        (Measurable.of_discrete
          (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
      simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord
    have hD : Measurable D := by
      dsimp [D]
      exact (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x i)).comp hcurr
    have hgate : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          if H p ≤ A p then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le hH hA) measurable_const measurable_const
    have hmin : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          min (H p) (A p)) :=
      hH.min hA
    dsimp [f, truncatedCenteredCoordIncrementFromHistory,
      truncatedCenteredCoordIncrement, H, A, J, D]
    exact ((hgate.mul hJ).sub (hD.mul hmin)).pow_const 2
  have hf_int : Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa using
      M.integrable_truncatedCenteredCoordIncrementFromHistory_next_sq x₀ T n i
  have hprod :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  have hsq_hist :=
    M.integral_condDistrib_truncatedCenteredCoordIncrementFromHistory_sq_eq
      x₀ T n i
  have hsq_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      hsq_hist
  filter_upwards [hprod, hsq_records] with records hprod_records hsq_records
  rw [hprod_records]
  simpa [μ, X, Y, f] using hsq_records

theorem integrable_canonicalFrozenClockTruncatedMartingale_sq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  have hterm_memLp : ∀ k ∈ Finset.range n,
      MemLp
        (fun records : M.canonicalRecordΩ =>
          M.truncatedCenteredCoordIncrementFromHistory T k i
            (Preorder.frestrictLe k records) (records (k + 1))) 2 μ := by
    intro k _hk
    have hmeas : AEStronglyMeasurable
        (fun records : M.canonicalRecordΩ =>
          M.truncatedCenteredCoordIncrementFromHistory T k i
            (Preorder.frestrictLe k records) (records (k + 1))) μ :=
      ((M.measurable_truncatedCenteredCoordIncrementFromHistory_next_canonicalRecordFiltration_le
        T i (Nat.le_refl (k + 1))).mono
        (M.canonicalRecordFiltration.le (k + 1)) le_rfl).aestronglyMeasurable
    exact (memLp_two_iff_integrable_sq hmeas).2
      (by
        simpa [μ] using
          M.integrable_truncatedCenteredCoordIncrementFromHistory_next_sq
            x₀ T k i)
  have hsum_memLp : MemLp
      (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range n,
          M.truncatedCenteredCoordIncrementFromHistory T k i
            (Preorder.frestrictLe k records) (records (k + 1))) 2 μ :=
    memLp_finset_sum (Finset.range n) hterm_memLp
  simpa [canonicalFrozenClockTruncatedMartingale, μ] using hsum_memLp.integrable_sq

theorem integrable_canonicalFrozenClockTruncatedMartingale_sup_sq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  have hterm_memLp : ∀ k ∈ Finset.range (n + 1),
      MemLp
        (fun records : M.canonicalRecordΩ =>
          ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖) 2 μ := by
    intro k _hk
    have hmeas : AEStronglyMeasurable
        (fun records : M.canonicalRecordΩ =>
          M.canonicalFrozenClockTruncatedMartingale T i k records) μ :=
      ((M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
        T i k).mono (M.canonicalRecordFiltration.le k) le_rfl).aestronglyMeasurable
    have hmem : MemLp
        (fun records : M.canonicalRecordΩ =>
          M.canonicalFrozenClockTruncatedMartingale T i k records) 2 μ :=
      (memLp_two_iff_integrable_sq hmeas).2
        (by
          simpa [μ] using
            M.integrable_canonicalFrozenClockTruncatedMartingale_sq x₀ T i k)
    simpa using hmem.norm
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
  have hY_meas : AEStronglyMeasurable Y μ := by
    have hY_meas' : Measurable Y := by
      dsimp [Y]
      exact Finset.measurable_range_sup'' (fun k _hk =>
        (((M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
          T i k).mono (M.canonicalRecordFiltration.le k) le_rfl).norm))
    exact hY_meas'.aestronglyMeasurable
  have hsum_memLp : MemLp
      (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range (n + 1),
          ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖) 2 μ :=
    memLp_finset_sum (Finset.range (n + 1)) hterm_memLp
  have hY_memLp : MemLp Y 2 μ := by
    refine hsum_memLp.mono' hY_meas ?_
    refine ae_of_all _ fun records => ?_
    dsimp [Y]
    have hY_nonneg :
        0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => |M.canonicalFrozenClockTruncatedMartingale T i k records|) := by
      exact (abs_nonneg _).trans
        (Finset.le_sup'
          (fun k => |M.canonicalFrozenClockTruncatedMartingale T i k records|)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    rw [abs_of_nonneg hY_nonneg]
    exact Finset.sup'_le _ _ fun k hk =>
      Finset.single_le_sum
        (fun j _hj => abs_nonneg
          (M.canonicalFrozenClockTruncatedMartingale T i j records))
        hk
  simpa [Y, μ] using hY_memLp.integrable_sq

theorem canonicalFrozenClockTruncatedMartingale_norm_submartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) :
    Submartingale
      (fun n records =>
        ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.canonicalFrozenClockTruncatedMartingale T i n records
  have hmart : Martingale Z M.canonicalRecordFiltration μ := by
    simpa [Z, μ] using M.canonicalFrozenClockTruncatedMartingale_martingale x₀ T i
  refine submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.stronglyAdapted_canonicalFrozenClockTruncatedMartingale T i n).norm
  · intro n
    simpa [Z] using
      (M.integrable_canonicalFrozenClockTruncatedMartingale x₀ T i n).norm
  · intro n
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ‖(μ[Z (n + 1) | M.canonicalRecordFiltration n]) records‖)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => ‖Z (n + 1) records‖)
          | M.canonicalRecordFiltration n] :=
      norm_condExp_le
    have hcond : μ[Z (n + 1) | M.canonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

theorem canonicalFrozenClockTruncatedMartingale_norm_maximal_ineq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (ε : NNReal) (n : ℕ) :
    ((ε : ENNReal) * (M.canonicalRecordMeasure x₀)
        {records | (ε : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)})
      ≤ ENNReal.ofReal
        (∫ records in
          {records | (ε : ℝ) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)},
          ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖
          ∂M.canonicalRecordMeasure x₀) := by
  exact MeasureTheory.maximal_ineq
    (M.canonicalFrozenClockTruncatedMartingale_norm_submartingale x₀ T i)
    (by
      intro n records
      exact norm_nonneg _)
    (ε := ε) n

theorem integral_sup_canonicalFrozenClockTruncatedMartingale_norm_sq_le_two_mul_sup_mul_norm
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      2 * ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖) *
        ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖
  have hX_meas : Measurable X := by
    exact Finset.measurable_range_sup'' (fun k _hk =>
      (((M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
        T i k).mono (M.canonicalRecordFiltration.le k) le_rfl).norm))
  have hY_meas : Measurable Y :=
    (((M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
      T i n).mono (M.canonicalRecordFiltration.le n) le_rfl).norm)
  have hX_nonneg : 0 ≤ᵐ[μ] X := by
    refine ae_of_all _ fun records => ?_
    dsimp [X]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    ae_of_all _ fun records => norm_nonneg _
  have hXsq_int : Integrable (fun records => X records ^ 2) μ := by
    simpa [X, μ] using
      M.integrable_canonicalFrozenClockTruncatedMartingale_sup_sq x₀ T i n
  have hY_int : Integrable Y μ := by
    simpa [Y, μ] using
      (M.integrable_canonicalFrozenClockTruncatedMartingale x₀ T i n).norm
  have hY_sq_int : Integrable (fun records => Y records ^ 2) μ := by
    refine (M.integrable_canonicalFrozenClockTruncatedMartingale_sq x₀ T i n).congr ?_
    refine ae_of_all _ fun records => ?_
    dsimp [Y]
    exact (sq_abs (M.canonicalFrozenClockTruncatedMartingale T i n records)).symm
  have hX_memLp_nat : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2 hXsq_int
  have hY_memLp_nat : MemLp Y 2 μ :=
    (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_sq_int
  have hXY_int : Integrable (fun records => X records * Y records) μ :=
    MemLp.integrable_mul hX_memLp_nat hY_memLp_nat
  have hMax : ∀ ε : NNReal,
      ((ε : ENNReal) * μ {records | (ε : ℝ) ≤ X records}) ≤
        ENNReal.ofReal (∫ records in {records | (ε : ℝ) ≤ X records},
          Y records ∂μ) := by
    intro ε
    simpa [X, Y, μ] using
      M.canonicalFrozenClockTruncatedMartingale_norm_maximal_ineq
        x₀ T i ε n
  simpa [X, Y, μ] using
    integral_sq_le_two_integral_mul_of_maximal_ineq
      hX_meas hY_meas hX_nonneg hY_nonneg hXsq_int hY_int hXY_int hMax

theorem integral_canonicalFrozenClockTruncatedMartingale_sup_sq_le_four_terminal_norm_sq_of_layercake
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ)
    (hLayer :
      ∫ records,
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
          ∂M.canonicalRecordMeasure x₀ ≤
        2 * ∫ records,
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖) *
          ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖
          ∂M.canonicalRecordMeasure x₀) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let A : ℝ :=
    ∫ records,
      ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
      ∂M.canonicalRecordMeasure x₀
  let B : ℝ :=
    ∫ records,
      ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖ ^ 2
      ∂M.canonicalRecordMeasure x₀
  let C : ℝ :=
    ∫ records,
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖) *
      ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖
      ∂M.canonicalRecordMeasure x₀
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun records => sq_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun records => sq_nonneg _
  have hCauchy : C ≤ A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
    let μ := M.canonicalRecordMeasure x₀
    let X : M.canonicalRecordΩ → ℝ := fun records =>
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
    let Y : M.canonicalRecordΩ → ℝ := fun records =>
      ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖
    have hX_meas : Measurable X := by
      exact Finset.measurable_range_sup'' (fun k _hk =>
        (((M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
          T i k).mono (M.canonicalRecordFiltration.le k) le_rfl).norm))
    have hY_meas : Measurable Y :=
      (((M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
        T i n).mono (M.canonicalRecordFiltration.le n) le_rfl).norm)
    have hX_nonneg : 0 ≤ᵐ[μ] X := by
      refine ae_of_all _ fun records => ?_
      dsimp [X]
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    have hY_nonneg : 0 ≤ᵐ[μ] Y :=
      ae_of_all _ fun records => norm_nonneg _
    have hX_memLp_nat : MemLp X 2 μ := by
      exact (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2
        (by
          simpa [X, μ] using
            M.integrable_canonicalFrozenClockTruncatedMartingale_sup_sq x₀ T i n)
    have hX_memLp : MemLp X (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hX_memLp_nat
    have hY_int : Integrable (fun records => Y records ^ 2) μ := by
      refine (M.integrable_canonicalFrozenClockTruncatedMartingale_sq x₀ T i n).congr ?_
      refine ae_of_all _ fun records => ?_
      dsimp [Y]
      exact (sq_abs (M.canonicalFrozenClockTruncatedMartingale T i n records)).symm
    have hY_memLp_nat : MemLp Y 2 μ := by
      exact (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_int
    have hY_memLp : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hY_memLp_nat
    have hholder :=
      integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := μ) Real.HolderConjugate.two_two
        hX_nonneg hY_nonneg hX_memLp hY_memLp
    simpa [A, B, C, X, Y, μ] using hholder
  have hA_le_sqrt : A ≤ 2 * (Real.sqrt A * Real.sqrt B) := by
    have hA_le : A ≤ 2 * (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) := by
      exact hLayer.trans (mul_le_mul_of_nonneg_left hCauchy (by norm_num))
    simpa [Real.sqrt_eq_rpow] using hA_le
  have hsq_nonneg : 0 ≤ (Real.sqrt A - 2 * Real.sqrt B) ^ 2 :=
    sq_nonneg _
  have hsqrtA_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA_nonneg
  have hsqrtB_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB_nonneg
  change A ≤ 4 * B
  nlinarith [hA_le_sqrt, hsq_nonneg, hsqrtA_sq, hsqrtB_sq]

theorem integral_canonicalFrozenClockTruncatedMartingale_mul_increment_eq_zero
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    ∫ records,
        M.canonicalFrozenClockTruncatedMartingale T i n records *
          (M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records -
            M.canonicalFrozenClockTruncatedMartingale T i n records)
        ∂M.canonicalRecordMeasure x₀ = 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.canonicalFrozenClockTruncatedMartingale T i n records
  let inc : M.canonicalRecordΩ → ℝ := fun records => Z (n + 1) records - Z n records
  have hZ_memLp : MemLp (Z n) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_canonicalFrozenClockTruncatedMartingale T i n).mono
        (M.canonicalRecordFiltration.le n)).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_canonicalFrozenClockTruncatedMartingale_sq x₀ T i n)
  have hZ_succ_memLp : MemLp (Z (n + 1)) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_canonicalFrozenClockTruncatedMartingale T i (n + 1)).mono
        (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_canonicalFrozenClockTruncatedMartingale_sq x₀ T i (n + 1))
  have hinc_memLp : MemLp inc 2 μ := by
    simpa [inc, Pi.sub_apply] using hZ_succ_memLp.sub hZ_memLp
  have hinc_int : Integrable inc μ := hinc_memLp.integrable one_le_two
  have hprod_int : Integrable (fun records => Z n records * inc records) μ := by
    simpa [mul_comm] using hinc_memLp.integrable_mul hZ_memLp
  have hpull :
      μ[(fun records => Z n records * inc records) | M.canonicalRecordFiltration n]
        =ᵐ[μ]
      fun records => Z n records *
        (μ[inc | M.canonicalRecordFiltration n]) records := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (M.stronglyAdapted_canonicalFrozenClockTruncatedMartingale T i n)
      hprod_int hinc_int
  have hcond_inc :
      μ[inc | M.canonicalRecordFiltration n] =ᵐ[μ] 0 := by
    simpa [inc, Z, μ] using
      M.canonicalFrozenClockTruncatedMartingale_condExp_increment_eq_zero_ae
        x₀ T n i
  have hcond_prod :
      μ[(fun records => Z n records * inc records) | M.canonicalRecordFiltration n]
        =ᵐ[μ] 0 := by
    filter_upwards [hpull, hcond_inc] with records hpull_records hinc_records
    rw [hpull_records, hinc_records]
    simp
  calc
    ∫ records, Z n records * inc records ∂μ
        = ∫ records,
            (μ[(fun records => Z n records * inc records) |
              M.canonicalRecordFiltration n]) records ∂μ := by
            exact (integral_condExp
              (μ := μ)
              (m := M.canonicalRecordFiltration n)
              (f := fun records => Z n records * inc records)
              (M.canonicalRecordFiltration.le n)).symm
    _ = 0 := by
          simpa using integral_congr_ae hcond_prod

theorem integral_canonicalFrozenClockTruncatedMartingale_sq_succ_eq_add_increment_sq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
        ∂M.canonicalRecordMeasure x₀ +
      ∫ records,
        (M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records -
          M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.canonicalFrozenClockTruncatedMartingale T i n records
  let inc : M.canonicalRecordΩ → ℝ := fun records => Z (n + 1) records - Z n records
  have hZ_memLp : MemLp (Z n) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_canonicalFrozenClockTruncatedMartingale T i n).mono
        (M.canonicalRecordFiltration.le n)).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_canonicalFrozenClockTruncatedMartingale_sq x₀ T i n)
  have hZ_succ_memLp : MemLp (Z (n + 1)) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (((M.stronglyAdapted_canonicalFrozenClockTruncatedMartingale T i (n + 1)).mono
        (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.integrable_canonicalFrozenClockTruncatedMartingale_sq x₀ T i (n + 1))
  have hinc_memLp : MemLp inc 2 μ := by
    simpa [inc, Pi.sub_apply] using hZ_succ_memLp.sub hZ_memLp
  have hZ_sq_int : Integrable (fun records => (Z n records) ^ 2) μ :=
    hZ_memLp.integrable_sq
  have hinc_sq_int : Integrable (fun records => (inc records) ^ 2) μ :=
    hinc_memLp.integrable_sq
  have hprod_int : Integrable (fun records => Z n records * inc records) μ := by
    simpa [mul_comm] using hinc_memLp.integrable_mul hZ_memLp
  have hcross :
      ∫ records, Z n records * inc records ∂μ = 0 := by
    simpa [Z, inc, μ] using
      M.integral_canonicalFrozenClockTruncatedMartingale_mul_increment_eq_zero
        x₀ T i n
  let A : M.canonicalRecordΩ → ℝ := fun records => (Z n records) ^ 2
  let B : M.canonicalRecordΩ → ℝ := fun records => 2 * (Z n records * inc records)
  let C : M.canonicalRecordΩ → ℝ := fun records => (inc records) ^ 2
  have hA_int : Integrable A μ := by simpa [A] using hZ_sq_int
  have hB_int : Integrable B μ := by simpa [B] using hprod_int.const_mul 2
  have hC_int : Integrable C μ := by simpa [C] using hinc_sq_int
  have hsum :
      ∫ records, ((A + (B + C)) records) ∂μ =
        ∫ records, A records ∂μ +
          ∫ records, B records ∂μ +
          ∫ records, C records ∂μ := by
    have h1 :
        ∫ records, ((A + (B + C)) records) ∂μ =
          ∫ records, A records ∂μ + ∫ records, ((B + C) records) ∂μ := by
      simpa only [Pi.add_apply] using integral_add hA_int (hB_int.add hC_int)
    have h2 :
        ∫ records, ((B + C) records) ∂μ =
          ∫ records, B records ∂μ + ∫ records, C records ∂μ := by
      simpa only [Pi.add_apply] using integral_add hB_int hC_int
    rw [h1, h2]
    ring
  have hB_zero : ∫ records, B records ∂μ = 0 := by
    calc
      ∫ records, B records ∂μ = 2 * ∫ records, Z n records * inc records ∂μ := by
        simpa [B] using
          (integral_const_mul (μ := μ) (r := (2 : ℝ))
            (f := fun records => Z n records * inc records))
      _ = 0 := by rw [hcross, mul_zero]
  calc
    ∫ records, (Z (n + 1) records) ^ 2 ∂μ
        = ∫ records, A records + B records + C records ∂μ := by
            apply integral_congr_ae
            exact ae_of_all _ fun records => by
              dsimp [A, B, C, inc]
              ring
    _ = ∫ records, ((A + (B + C)) records) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun records => by
            dsimp [A, B, C]
            ring
    _ = ∫ records, A records ∂μ +
          ∫ records, B records ∂μ +
          ∫ records, C records ∂μ := hsum
    _ = ∫ records, (Z n records) ^ 2 ∂μ +
          ∫ records, (inc records) ^ 2 ∂μ := by
          rw [hB_zero]
          simp [A, C]
    _ = ∫ records,
          (M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
          ∂M.canonicalRecordMeasure x₀ +
        ∫ records,
          (M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records -
            M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by
          rfl

theorem integral_canonicalFrozenClockTruncatedMartingale_sq_eq_sum_increment_sq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∑ k ∈ Finset.range n,
        ∫ records,
          (M.canonicalFrozenClockTruncatedMartingale T i (k + 1) records -
            M.canonicalFrozenClockTruncatedMartingale T i k records) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [M.integral_canonicalFrozenClockTruncatedMartingale_sq_succ_eq_add_increment_sq
        x₀ T i n, ih]
      rw [Finset.sum_range_succ]

theorem integral_canonicalFrozenClockTruncatedMartingale_increment_sq_eq_clockQVIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records -
          M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantCoordQVRate x i *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist)
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let inc : M.canonicalRecordΩ → ℝ := fun records =>
    M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records -
      M.canonicalFrozenClockTruncatedMartingale T i n records
  let raw : M.canonicalRecordΩ → ℝ := fun records =>
    M.truncatedCenteredCoordIncrementFromHistory T n i
      (Preorder.frestrictLe n records) (records (n + 1))
  let Q : M.canonicalRecordΩ → ℝ := fun records =>
    let hist := Preorder.frestrictLe n records
    let x : Fin d → Fin (M.N + 1) :=
      QMatrix.currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n hist
    M.instantCoordQVRate x i *
      ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
        ∂ProbabilityTheory.condDistrib
          (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
          (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist
  have hinc_raw : inc =ᵐ[μ] raw := by
    refine ae_of_all _ fun records => ?_
    dsimp [inc, raw]
    exact M.canonicalFrozenClockTruncatedMartingale_succ_sub T i n records
  have hinc_sq_raw : (fun records => (inc records) ^ 2) =ᵐ[μ]
      fun records => (raw records) ^ 2 := by
    filter_upwards [hinc_raw] with records hrecords
    rw [hrecords]
  have hcond :
      μ[(fun records => (inc records) ^ 2) | M.canonicalRecordFiltration n]
        =ᵐ[μ] Q := by
    refine (MeasureTheory.condExp_congr_ae hinc_sq_raw).trans ?_
    simpa [raw, Q, μ] using
      M.condExp_truncatedCenteredCoordIncrementFromHistory_next_sq_eq_clockQVIntegral_ae
        x₀ T n i
  have hinc_sq_int : Integrable (fun records => (inc records) ^ 2) μ := by
    have hZ_succ :=
      M.integrable_canonicalFrozenClockTruncatedMartingale_sq x₀ T i (n + 1)
    have hZ :=
      M.integrable_canonicalFrozenClockTruncatedMartingale_sq x₀ T i n
    have hZ_succ_memLp : MemLp
        (fun records : M.canonicalRecordΩ =>
          M.canonicalFrozenClockTruncatedMartingale T i (n + 1) records) 2 μ := by
      exact (memLp_two_iff_integrable_sq
        (((M.stronglyAdapted_canonicalFrozenClockTruncatedMartingale T i (n + 1)).mono
          (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
        (by simpa [μ] using hZ_succ)
    have hZ_memLp : MemLp
        (fun records : M.canonicalRecordΩ =>
          M.canonicalFrozenClockTruncatedMartingale T i n records) 2 μ := by
      exact (memLp_two_iff_integrable_sq
        (((M.stronglyAdapted_canonicalFrozenClockTruncatedMartingale T i n).mono
          (M.canonicalRecordFiltration.le n)).aestronglyMeasurable)).2
        (by simpa [μ] using hZ)
    simpa [inc, Pi.sub_apply] using (hZ_succ_memLp.sub hZ_memLp).integrable_sq
  calc
    ∫ records, (inc records) ^ 2 ∂μ
        = ∫ records,
            (μ[(fun records => (inc records) ^ 2) |
              M.canonicalRecordFiltration n]) records ∂μ := by
            exact (integral_condExp
              (μ := μ)
              (m := M.canonicalRecordFiltration n)
              (f := fun records => (inc records) ^ 2)
              (M.canonicalRecordFiltration.le n)).symm
    _ = ∫ records, Q records ∂μ := by
          exact integral_congr_ae hcond
    _ = ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantCoordQVRate x i *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist)
        ∂M.canonicalRecordMeasure x₀ := by
          simp [Q, μ]

theorem integrable_clockTruncatedCoordQVIncrement
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantCoordQVRate x i *
          min (records (n + 1)).1 (QMatrix.historyClockRemaining T n hist)))
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let H : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records)
  let Qv : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantCoordQVRate
      (QMatrix.currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) i
  let Prev : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ j : Fin n, ‖(records (j.1 + 1)).1‖
  obtain ⟨C, hC_nonneg, hC⟩ := M.exists_instantCoordQVRate_abs_bound i
  have hH_meas : Measurable H := by
    dsimp [H]
    fun_prop
  have hA_meas : Measurable A := by
    dsimp [A, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
    exact measurable_const.max
      (measurable_const.sub
        (Finset.measurable_sum _ fun j _ => by fun_prop))
  have hcurr : Measurable
      (fun records : M.canonicalRecordΩ =>
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) := by
    exact (QMatrix.measurable_currentStateFromHistory
      (S := Fin d → Fin (M.N + 1)) n).comp
        (Preorder.measurable_frestrictLe n)
  have hQv_meas : Measurable Qv := by
    dsimp [Qv]
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.instantCoordQVRate x i)).comp hcurr
  have hmin_meas : Measurable (fun records : M.canonicalRecordΩ =>
      min (H records) (A records)) :=
    hH_meas.min hA_meas
  have hprod_meas : AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ => Qv records * min (H records) (A records)) μ :=
    (hQv_meas.mul hmin_meas).aestronglyMeasurable
  have hH_int : Integrable H μ := by
    simpa [H, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ n
  have hPrev_int : Integrable Prev μ := by
    dsimp [Prev]
    refine integrable_finsetSum Finset.univ ?_
    intro j _hj
    have hj_int :
        Integrable (fun records : M.canonicalRecordΩ =>
          (records (j.1 + 1)).1) μ := by
      simpa [μ] using
        M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ j.1
    exact hj_int.norm
  have hdom_int : Integrable
      (fun records : M.canonicalRecordΩ =>
        C * (‖H records‖ + (‖T‖ + Prev records))) μ :=
    ((hH_int.norm.add ((integrable_const ‖T‖).add hPrev_int)).const_mul C)
  refine (hdom_int.mono' hprod_meas ?_).congr ?_
  · refine ae_of_all _ fun records => ?_
    rw [norm_mul]
    have hQv_bound : ‖Qv records‖ ≤ C := hC _
    have hA_bound : ‖A records‖ ≤ ‖T‖ + Prev records := by
      dsimp [A, Prev, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
      calc
        ‖max 0 (T -
            ∑ j : Fin n, (records (j.1 + 1)).1)‖
            ≤ max ‖(0 : ℝ)‖ ‖T -
                ∑ j : Fin n, (records (j.1 + 1)).1‖ := by
              simpa [Real.norm_eq_abs] using
                abs_max_le_max_abs_abs (a := (0 : ℝ))
                  (b := T - ∑ j : Fin n, (records (j.1 + 1)).1)
        _ ≤ ‖T - ∑ j : Fin n, (records (j.1 + 1)).1‖ := by
              simp
        _ ≤ ‖T‖ + ‖∑ j : Fin n, (records (j.1 + 1)).1‖ := by
              simpa [sub_eq_add_neg, norm_neg] using
                norm_add_le T (-(∑ j : Fin n, (records (j.1 + 1)).1))
        _ ≤ ‖T‖ + ∑ j : Fin n, ‖(records (j.1 + 1)).1‖ := by
              have hsum_abs :
                  ‖∑ j : Fin n, (records (j.1 + 1)).1‖ ≤
                    ∑ j : Fin n, ‖(records (j.1 + 1)).1‖ := by
                simpa [Real.norm_eq_abs] using
                  Finset.abs_sum_le_sum_abs
                    (fun j : Fin n => (records (j.1 + 1)).1) Finset.univ
              linarith
    have hmin_bound :
        ‖min (H records) (A records)‖ ≤
          ‖H records‖ + (‖T‖ + Prev records) := by
      calc
        ‖min (H records) (A records)‖
            ≤ max ‖H records‖ ‖A records‖ := by
              simpa [Real.norm_eq_abs] using
                abs_min_le_max_abs_abs (a := H records) (b := A records)
        _ ≤ ‖H records‖ + ‖A records‖ :=
              max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
        _ ≤ ‖H records‖ + (‖T‖ + Prev records) := by
              linarith
    exact mul_le_mul hQv_bound hmin_bound (norm_nonneg _) hC_nonneg
  · refine ae_of_all _ fun records => ?_
    dsimp [Qv, H, A]

theorem integral_clockQVIntegral_eq_integral_clockTruncatedCoordQVIncrement
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantCoordQVRate x i *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist)
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
        M.instantCoordQVRate x i *
          min (records (n + 1)).1 (QMatrix.historyClockRemaining T n hist))
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
        ℝ) → ℝ :=
    fun p =>
      let x : Fin d → Fin (M.N + 1) :=
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n p.1
      M.instantCoordQVRate x i *
        min p.2 (QMatrix.historyClockRemaining T n p.1)
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => (records (n + 1)).1)).aemeasurable
  have hf_meas : Measurable f := by
    have hcurr : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            ℝ) =>
          QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) :=
      (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp measurable_fst
    have hqv : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            ℝ) =>
          M.instantCoordQVRate
            (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.instantCoordQVRate x i)).comp hcurr
    have hrem : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            ℝ) =>
          QMatrix.historyClockRemaining T n p.1) := by
      dsimp [QMatrix.historyClockRemaining, QMatrix.historySojournStart]
      exact measurable_const.max
        (measurable_const.sub
          (Finset.measurable_sum _ fun j _ => by fun_prop))
    have hmin : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            ℝ) =>
          min p.2 (QMatrix.historyClockRemaining T n p.1)) :=
      measurable_snd.min hrem
    dsimp [f]
    exact hqv.mul hmin
  have hf_int : Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa using
      M.integrable_clockTruncatedCoordQVIncrement x₀ T i n
  have hprod :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  have hcond :
      μ[(fun a : M.canonicalRecordΩ => f (X a, Y a)) |
        MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun records : M.canonicalRecordΩ =>
        let hist := X records
        let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
        M.instantCoordQVRate x i *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib Y X μ hist := by
    filter_upwards [hprod] with records hprod_records
    rw [hprod_records]
    simp only [f]
    rw [integral_const_mul]
  calc
    ∫ records,
        (let hist := X records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantCoordQVRate x i *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib Y X μ hist)
        ∂μ
        = ∫ records,
            (μ[(fun a : M.canonicalRecordΩ => f (X a, Y a)) |
              MeasurableSpace.comap X inferInstance]) records ∂μ := by
            exact (integral_congr_ae hcond).symm
    _ = ∫ records, f (X records, Y records) ∂μ := by
          exact integral_condExp
            (μ := μ)
            (m := MeasurableSpace.comap X inferInstance)
            (f := fun a : M.canonicalRecordΩ => f (X a, Y a))
            hX.comap_le
    _ = ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantCoordQVRate x i *
          min (records (n + 1)).1 (QMatrix.historyClockRemaining T n hist))
        ∂M.canonicalRecordMeasure x₀ := by
          simp [f, X, Y, μ]

theorem integrable_clockTruncatedQVIncrement
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantQVRate x *
          min (records (n + 1)).1 (QMatrix.historyClockRemaining T n hist)))
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let H : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    QMatrix.historyClockRemaining T n (Preorder.frestrictLe n records)
  let Qv : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantQVRate
      (QMatrix.currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
  let Prev : M.canonicalRecordΩ → ℝ := fun records =>
    ∑ j : Fin n, ‖(records (j.1 + 1)).1‖
  obtain ⟨C, hC_pos, hC⟩ := M.exists_instantQVRate_bound
  have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
  have hH_meas : Measurable H := by
    dsimp [H]
    fun_prop
  have hA_meas : Measurable A := by
    dsimp [A, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
    exact measurable_const.max
      (measurable_const.sub
        (Finset.measurable_sum _ fun j _ => by fun_prop))
  have hcurr : Measurable
      (fun records : M.canonicalRecordΩ =>
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) := by
    exact (QMatrix.measurable_currentStateFromHistory
      (S := Fin d → Fin (M.N + 1)) n).comp
        (Preorder.measurable_frestrictLe n)
  have hQv_meas : Measurable Qv := by
    dsimp [Qv]
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.instantQVRate x)).comp hcurr
  have hmin_meas : Measurable (fun records : M.canonicalRecordΩ =>
      min (H records) (A records)) :=
    hH_meas.min hA_meas
  have hprod_meas : AEStronglyMeasurable
      (fun records : M.canonicalRecordΩ => Qv records * min (H records) (A records)) μ :=
    (hQv_meas.mul hmin_meas).aestronglyMeasurable
  have hH_int : Integrable H μ := by
    simpa [H, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ n
  have hPrev_int : Integrable Prev μ := by
    dsimp [Prev]
    refine integrable_finsetSum Finset.univ ?_
    intro j _hj
    have hj_int :
        Integrable (fun records : M.canonicalRecordΩ =>
          (records (j.1 + 1)).1) μ := by
      simpa [μ] using
        M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ j.1
    exact hj_int.norm
  have hdom_int : Integrable
      (fun records : M.canonicalRecordΩ =>
        C * (‖H records‖ + (‖T‖ + Prev records))) μ :=
    ((hH_int.norm.add ((integrable_const ‖T‖).add hPrev_int)).const_mul C)
  refine (hdom_int.mono' hprod_meas ?_).congr ?_
  · refine ae_of_all _ fun records => ?_
    rw [norm_mul]
    have hQv_bound : ‖Qv records‖ ≤ C := by
      have hNpos : (0 : ℝ) < M.N := Nat.cast_pos.mpr M.hN
      have hNge : (1 : ℝ) ≤ M.N := by
        exact_mod_cast Nat.succ_le_of_lt M.hN
      have hdiv_le : C / (M.N : ℝ) ≤ C := by
        calc
          C / (M.N : ℝ) ≤ C / (1 : ℝ) := by
            exact div_le_div_of_nonneg_left hC_nonneg zero_lt_one hNge
          _ = C := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (M.instantQVRate_nonneg _)]
      exact (hC _).trans hdiv_le
    have hA_bound : ‖A records‖ ≤ ‖T‖ + Prev records := by
      dsimp [A, Prev, QMatrix.historyClockRemaining, QMatrix.historySojournStart]
      calc
        ‖max 0 (T -
            ∑ j : Fin n, (records (j.1 + 1)).1)‖
            ≤ max ‖(0 : ℝ)‖ ‖T -
                ∑ j : Fin n, (records (j.1 + 1)).1‖ := by
              simpa [Real.norm_eq_abs] using
                abs_max_le_max_abs_abs (a := (0 : ℝ))
                  (b := T - ∑ j : Fin n, (records (j.1 + 1)).1)
        _ ≤ ‖T - ∑ j : Fin n, (records (j.1 + 1)).1‖ := by
              simp
        _ ≤ ‖T‖ + ‖∑ j : Fin n, (records (j.1 + 1)).1‖ := by
              simpa [sub_eq_add_neg, norm_neg] using
                norm_add_le T (-(∑ j : Fin n, (records (j.1 + 1)).1))
        _ ≤ ‖T‖ + ∑ j : Fin n, ‖(records (j.1 + 1)).1‖ := by
              have hsum_abs :
                  ‖∑ j : Fin n, (records (j.1 + 1)).1‖ ≤
                    ∑ j : Fin n, ‖(records (j.1 + 1)).1‖ := by
                simpa [Real.norm_eq_abs] using
                  Finset.abs_sum_le_sum_abs
                    (fun j : Fin n => (records (j.1 + 1)).1) Finset.univ
              linarith
    have hmin_bound :
        ‖min (H records) (A records)‖ ≤
          ‖H records‖ + (‖T‖ + Prev records) := by
      calc
        ‖min (H records) (A records)‖
            ≤ max ‖H records‖ ‖A records‖ := by
              simpa [Real.norm_eq_abs] using
                abs_min_le_max_abs_abs (a := H records) (b := A records)
        _ ≤ ‖H records‖ + ‖A records‖ :=
              max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
        _ ≤ ‖H records‖ + (‖T‖ + Prev records) := by
              linarith
    exact mul_le_mul hQv_bound hmin_bound (norm_nonneg _) hC_nonneg
  · refine ae_of_all _ fun records => ?_
    dsimp [Qv, H, A]

theorem integral_clockQVIntegral_eq_integral_clockTruncatedQVIncrement
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantQVRate x *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist)
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
        M.instantQVRate x *
          min (records (n + 1)).1 (QMatrix.historyClockRemaining T n hist))
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
        ℝ) → ℝ :=
    fun p =>
      let x : Fin d → Fin (M.N + 1) :=
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n p.1
      M.instantQVRate x *
        min p.2 (QMatrix.historyClockRemaining T n p.1)
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => (records (n + 1)).1)).aemeasurable
  have hf_meas : Measurable f := by
    have hcurr : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            ℝ) =>
          QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) :=
      (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp measurable_fst
    have hqv : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            ℝ) =>
          M.instantQVRate
            (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1)) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.instantQVRate x)).comp hcurr
    have hrem : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            ℝ) =>
          QMatrix.historyClockRemaining T n p.1) := by
      dsimp [QMatrix.historyClockRemaining, QMatrix.historySojournStart]
      exact measurable_const.max
        (measurable_const.sub
          (Finset.measurable_sum _ fun j _ => by fun_prop))
    have hmin : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            ℝ) =>
          min p.2 (QMatrix.historyClockRemaining T n p.1)) :=
      measurable_snd.min hrem
    dsimp [f]
    exact hqv.mul hmin
  have hf_int : Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa using
      M.integrable_clockTruncatedQVIncrement x₀ T n
  have hprod :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  have hcond :
      μ[(fun a : M.canonicalRecordΩ => f (X a, Y a)) |
        MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun records : M.canonicalRecordΩ =>
        let hist := X records
        let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
        M.instantQVRate x *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib Y X μ hist := by
    filter_upwards [hprod] with records hprod_records
    rw [hprod_records]
    simp only [f]
    rw [integral_const_mul]
  calc
    ∫ records,
        (let hist := X records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantQVRate x *
          ∫ t : ℝ, min t (QMatrix.historyClockRemaining T n hist)
            ∂ProbabilityTheory.condDistrib Y X μ hist)
        ∂μ
        = ∫ records,
            (μ[(fun a : M.canonicalRecordΩ => f (X a, Y a)) |
              MeasurableSpace.comap X inferInstance]) records ∂μ := by
            exact (integral_congr_ae hcond).symm
    _ = ∫ records, f (X records, Y records) ∂μ := by
          exact integral_condExp
            (μ := μ)
            (m := MeasurableSpace.comap X inferInstance)
            (f := fun a : M.canonicalRecordΩ => f (X a, Y a))
            hX.comap_le
    _ = ∫ records,
        (let hist := Preorder.frestrictLe n records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n hist
         M.instantQVRate x *
          min (records (n + 1)).1 (QMatrix.historyClockRemaining T n hist))
        ∂M.canonicalRecordMeasure x₀ := by
          simp [f, X, Y, μ]

/-- Finite-sum version of
`integral_clockQVIntegral_eq_integral_clockTruncatedQVIncrement` for the vector
instantaneous-QV clock increment. -/
theorem integral_sum_clockTruncatedQVIncrement_eq_sum_clockQVIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∫ records,
        (∑ k ∈ Finset.range n,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist)))
        ∂M.canonicalRecordMeasure x₀ =
      ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantQVRate x *
            ∫ t : ℝ, min t (QMatrix.historyClockRemaining T k hist)
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (k + 1)).1)
                (Preorder.frestrictLe k) (M.canonicalRecordMeasure x₀) hist)
          ∂M.canonicalRecordMeasure x₀ := by
  rw [integral_finset_sum (Finset.range n)]
  · refine Finset.sum_congr rfl ?_
    intro k _hk
    exact (M.integral_clockQVIntegral_eq_integral_clockTruncatedQVIncrement
      x₀ T k).symm
  · intro k _hk
    exact M.integrable_clockTruncatedQVIncrement x₀ T k

theorem integral_canonicalFrozenClockTruncatedMartingale_sq_eq_sum_clockQVIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantCoordQVRate x i *
            ∫ t : ℝ, min t (QMatrix.historyClockRemaining T k hist)
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (k + 1)).1)
                (Preorder.frestrictLe k) (M.canonicalRecordMeasure x₀) hist)
          ∂M.canonicalRecordMeasure x₀ := by
  rw [M.integral_canonicalFrozenClockTruncatedMartingale_sq_eq_sum_increment_sq
    x₀ T i n]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  exact M.integral_canonicalFrozenClockTruncatedMartingale_increment_sq_eq_clockQVIntegral
    x₀ T i k

theorem integral_canonicalFrozenClockTruncatedMartingale_sup_sq_le_sum_clockQVIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantCoordQVRate x i *
            ∫ t : ℝ, min t (QMatrix.historyClockRemaining T k hist)
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (k + 1)).1)
                (Preorder.frestrictLe k) (M.canonicalRecordMeasure x₀) hist)
          ∂M.canonicalRecordMeasure x₀ := by
  have hDoob :=
    M.integral_canonicalFrozenClockTruncatedMartingale_sup_sq_le_four_terminal_norm_sq_of_layercake
      x₀ T i n
      (M.integral_sup_canonicalFrozenClockTruncatedMartingale_norm_sq_le_two_mul_sup_mul_norm
        x₀ T i n)
  have hterminal_norm :
      ∫ records,
          ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖ ^ 2
          ∂M.canonicalRecordMeasure x₀ =
        ∫ records,
          (M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by
    apply integral_congr_ae
    refine ae_of_all _ fun records => ?_
    change |M.canonicalFrozenClockTruncatedMartingale T i n records| ^ 2 =
      (M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
    exact sq_abs (M.canonicalFrozenClockTruncatedMartingale T i n records)
  calc
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀
        ≤ 4 * ∫ records,
          ‖M.canonicalFrozenClockTruncatedMartingale T i n records‖ ^ 2
          ∂M.canonicalRecordMeasure x₀ := hDoob
    _ = 4 * ∫ records,
          (M.canonicalFrozenClockTruncatedMartingale T i n records) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by rw [hterminal_norm]
    _ = 4 * ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantCoordQVRate x i *
            ∫ t : ℝ, min t (QMatrix.historyClockRemaining T k hist)
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (k + 1)).1)
                (Preorder.frestrictLe k) (M.canonicalRecordMeasure x₀) hist)
        ∂M.canonicalRecordMeasure x₀ := by
          rw [M.integral_canonicalFrozenClockTruncatedMartingale_sq_eq_sum_clockQVIntegral
            x₀ T i n]

theorem integral_canonicalFrozenClockTruncatedMartingale_sup_sq_le_sum_clockTruncatedCoordQV
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (i : Fin d) (n : ℕ) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantCoordQVRate x i *
            min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
          ∂M.canonicalRecordMeasure x₀ := by
  have h :=
    M.integral_canonicalFrozenClockTruncatedMartingale_sup_sq_le_sum_clockQVIntegral
      x₀ T i n
  refine h.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _hk
  exact M.integral_clockQVIntegral_eq_integral_clockTruncatedCoordQVIncrement
    x₀ T i k

/-- Conditional second-moment control for the drift part of a truncated
holding-time interval.  The truncation length is any nonnegative finite-history
observable. -/
theorem integral_condDistrib_next_holdingTime_generatorDrift_min_sq_le
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d)
    (a : ((j : Iic n) →
        QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) → ℝ)
    (ha : ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      0 ≤ a hist) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      let x : Fin d → Fin (M.N + 1) :=
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n hist
      (M.generatorDrift x i) ^ 2 *
          (∫ t : ℝ, (min t (a hist)) ^ 2
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) ≤
        2 * M.instantCoordQVRate x i *
          (∫ t : ℝ, min t (a hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) := by
  have hminsq :=
    M.toQMatrix.integral_condDistrib_next_holdingTime_min_sq_le
      x₀ n a ha
  have hnonabs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ∀ h : ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist),
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.holdingTimeMeasure h := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing
      x₀ n
  have habs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            Measure.dirac 0 := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing
      x₀ n
  filter_upwards [hminsq, hnonabs, habs, ha] with hist hminsq_hist hnonabs_hist
    habs_hist ha_hist
  let x : Fin d → Fin (M.N + 1) :=
    QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist
  by_cases hxabs : M.toQMatrix.IsAbsorbing x
  · have hzero : M.exitRateAt x = 0 := by
      simpa [x, exitRateAt] using hxabs
    have hdrift : M.generatorDrift x i = 0 :=
      M.generatorDrift_eq_zero_of_exitRateAt_zero hzero i
    have hqv : M.instantCoordQVRate x i = 0 :=
      M.instantCoordQVRate_eq_zero_of_exitRateAt_zero hzero i
    simp [x, hdrift, hqv]
  · have hpos : 0 < M.exitRateAt x := by
      simpa [x, exitRateAt] using
        M.toQMatrix.exitRate_pos_of_nonabsorbing hxabs
    have hdiv :=
      M.generatorDrift_sq_div_exitRateAt_le_instantCoordQVRate x i hpos
    have hI1_nonneg :
        0 ≤ ∫ t : ℝ, min t (a hist)
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist := by
      rw [hnonabs_hist (by simpa [x] using hxabs)]
      exact integral_nonneg_of_ae
        ((M.toQMatrix.holdingTimeMeasure_pos_ae (by simpa [x] using hxabs)).mono
          (fun t ht => le_min (le_of_lt ht) ha_hist))
    calc
      (M.generatorDrift x i) ^ 2 *
          (∫ t : ℝ, (min t (a hist)) ^ 2
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist)
          ≤ (M.generatorDrift x i) ^ 2 *
            ((2 / M.exitRateAt x) *
              ∫ t : ℝ, min t (a hist)
                ∂ProbabilityTheory.condDistrib
                  (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
                  (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [x, exitRateAt] using hminsq_hist)
              (sq_nonneg _)
      _ = 2 * ((M.generatorDrift x i) ^ 2 / M.exitRateAt x) *
            (∫ t : ℝ, min t (a hist)
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
                (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) := by
            ring
      _ ≤ 2 * M.instantCoordQVRate x i *
            (∫ t : ℝ, min t (a hist)
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
                (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdiv (by norm_num))
              hI1_nonneg

/-- Vector-valued version of
`integral_condDistrib_next_holdingTime_generatorDrift_min_sq_le`, using the
instantaneous vector QV rate. -/
theorem integral_condDistrib_next_holdingTime_generatorDrift_norm_min_sq_le
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ)
    (a : ((j : Iic n) →
        QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) → ℝ)
    (ha : ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      0 ≤ a hist) :
    ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
      let x : Fin d → Fin (M.N + 1) :=
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) n hist
      ‖M.generatorDrift x‖ ^ 2 *
          (∫ t : ℝ, (min t (a hist)) ^ 2
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) ≤
        2 * M.instantQVRate x *
          (∫ t : ℝ, min t (a hist)
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) := by
  have hminsq :=
    M.toQMatrix.integral_condDistrib_next_holdingTime_min_sq_le
      x₀ n a ha
  have hnonabs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ∀ h : ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist),
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.holdingTimeMeasure h := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing
      x₀ n
  have habs :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            Measure.dirac 0 := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing
      x₀ n
  filter_upwards [hminsq, hnonabs, habs, ha] with hist hminsq_hist hnonabs_hist
    habs_hist ha_hist
  let x : Fin d → Fin (M.N + 1) :=
    QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n hist
  by_cases hxabs : M.toQMatrix.IsAbsorbing x
  · have hzero : M.exitRateAt x = 0 := by
      simpa [x, exitRateAt] using hxabs
    have hdrift : M.generatorDrift x = 0 := by
      ext i
      exact M.generatorDrift_eq_zero_of_exitRateAt_zero hzero i
    have hqv : M.instantQVRate x = 0 :=
      M.instantQVRate_eq_zero_of_exitRateAt_zero hzero
    simp [x, hdrift, hqv]
  · have hpos : 0 < M.exitRateAt x := by
      simpa [x, exitRateAt] using
        M.toQMatrix.exitRate_pos_of_nonabsorbing hxabs
    have hdiv :
        ‖M.generatorDrift x‖ ^ 2 / M.exitRateAt x ≤ M.instantQVRate x := by
      rw [div_le_iff₀ hpos]
      simpa [mul_comm] using
        M.generatorDrift_norm_sq_le_exitRateAt_mul_instantQVRate_frozen x
    have hI1_nonneg :
        0 ≤ ∫ t : ℝ, min t (a hist)
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist := by
      rw [hnonabs_hist (by simpa [x] using hxabs)]
      exact integral_nonneg_of_ae
        ((M.toQMatrix.holdingTimeMeasure_pos_ae (by simpa [x] using hxabs)).mono
          (fun t ht => le_min (le_of_lt ht) ha_hist))
    calc
      ‖M.generatorDrift x‖ ^ 2 *
          (∫ t : ℝ, (min t (a hist)) ^ 2
            ∂ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist)
          ≤ ‖M.generatorDrift x‖ ^ 2 *
            ((2 / M.exitRateAt x) *
              ∫ t : ℝ, min t (a hist)
                ∂ProbabilityTheory.condDistrib
                  (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
                  (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [x, exitRateAt] using hminsq_hist)
              (sq_nonneg _)
      _ = 2 * (‖M.generatorDrift x‖ ^ 2 / M.exitRateAt x) *
            (∫ t : ℝ, min t (a hist)
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
                (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) := by
            ring
      _ ≤ 2 * M.instantQVRate x *
            (∫ t : ℝ, min t (a hist)
              ∂ProbabilityTheory.condDistrib
                (fun records : M.canonicalRecordΩ => (records (n + 1)).1)
                (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdiv (by norm_num))
              hI1_nonneg

/-! ## Frozen embedded jump-index compensators -/

/-- Frozen drift compensator for one coordinate along the embedded jump index. -/
noncomputable def frozenScaledJumpDriftCompensator
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.guardedGeneratorDriftDivExit (path.stateSeq k) i

/-- Frozen coordinate QV compensator along the embedded jump index. -/
noncomputable def frozenScaledCoordQVCompensator
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.guardedInstantCoordQVRateDivExit (path.stateSeq k) i

/-- Frozen vector QV compensator along the embedded jump index. -/
noncomputable def frozenScaledQVCompensator
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.guardedInstantQVRateDivExit (path.stateSeq k)

/-- Centered frozen coordinate jump-sum process along the embedded jump index. -/
noncomputable def frozenScaledJumpMartingale
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  M.scaledJumpSum path n i - M.frozenScaledJumpDriftCompensator path i n

/-- Centered frozen coordinate squared-jump sum along the embedded jump index. -/
noncomputable def frozenScaledCoordJumpSqMartingale
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  M.scaledCoordJumpSqSum path i n - M.frozenScaledCoordQVCompensator path i n

/-- Centered frozen vector squared-jump sum along the embedded jump index. -/
noncomputable def frozenScaledJumpSqMartingale
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) : ℝ :=
  M.scaledJumpSqSum path n - M.frozenScaledQVCompensator path n

@[simp]
theorem frozenScaledJumpDriftCompensator_zero
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.frozenScaledJumpDriftCompensator path i 0 = 0 := by
  simp [frozenScaledJumpDriftCompensator]

@[simp]
theorem frozenScaledCoordQVCompensator_zero
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.frozenScaledCoordQVCompensator path i 0 = 0 := by
  simp [frozenScaledCoordQVCompensator]

@[simp]
theorem frozenScaledQVCompensator_zero
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) :
    M.frozenScaledQVCompensator path 0 = 0 := by
  simp [frozenScaledQVCompensator]

@[simp]
theorem frozenScaledJumpMartingale_zero
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.frozenScaledJumpMartingale path i 0 = 0 := by
  simp [frozenScaledJumpMartingale, scaledJumpSum]

@[simp]
theorem frozenScaledCoordJumpSqMartingale_zero
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.frozenScaledCoordJumpSqMartingale path i 0 = 0 := by
  simp [frozenScaledCoordJumpSqMartingale, scaledCoordJumpSqSum]

@[simp]
theorem frozenScaledJumpSqMartingale_zero
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) :
    M.frozenScaledJumpSqMartingale path 0 = 0 := by
  simp [frozenScaledJumpSqMartingale, scaledJumpSqSum]

theorem frozenScaledJumpDriftCompensator_succ
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenScaledJumpDriftCompensator path i (n + 1) =
      M.frozenScaledJumpDriftCompensator path i n +
        M.guardedGeneratorDriftDivExit (path.stateSeq n) i := by
  simp [frozenScaledJumpDriftCompensator, Finset.sum_range_succ]

theorem frozenScaledCoordQVCompensator_succ
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenScaledCoordQVCompensator path i (n + 1) =
      M.frozenScaledCoordQVCompensator path i n +
        M.guardedInstantCoordQVRateDivExit (path.stateSeq n) i := by
  simp [frozenScaledCoordQVCompensator, Finset.sum_range_succ]

theorem frozenScaledQVCompensator_succ
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) :
    M.frozenScaledQVCompensator path (n + 1) =
      M.frozenScaledQVCompensator path n +
        M.guardedInstantQVRateDivExit (path.stateSeq n) := by
  simp [frozenScaledQVCompensator, Finset.sum_range_succ]

/-- One-step increment of the frozen centered coordinate jump-sum process. -/
theorem frozenScaledJumpMartingale_succ_sub
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenScaledJumpMartingale path i (n + 1) -
        M.frozenScaledJumpMartingale path i n =
      (M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)) i -
        M.guardedGeneratorDriftDivExit (path.stateSeq n) i := by
  simp only [frozenScaledJumpMartingale, scaledJumpSum,
    frozenScaledJumpDriftCompensator, Finset.sum_range_succ]
  ring

/-- One-step increment of the frozen centered coordinate squared-jump process. -/
theorem frozenScaledCoordJumpSqMartingale_succ_sub
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenScaledCoordJumpSqMartingale path i (n + 1) -
        M.frozenScaledCoordJumpSqMartingale path i n =
      ((M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)) i) ^ 2 -
        M.guardedInstantCoordQVRateDivExit (path.stateSeq n) i := by
  simp only [frozenScaledCoordJumpSqMartingale, scaledCoordJumpSqSum,
    frozenScaledCoordQVCompensator, Finset.sum_range_succ]
  ring

/-- One-step increment of the frozen centered vector squared-jump process. -/
theorem frozenScaledJumpSqMartingale_succ_sub
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) :
    M.frozenScaledJumpSqMartingale path (n + 1) -
        M.frozenScaledJumpSqMartingale path n =
      ‖M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)‖ ^ 2 -
        M.guardedInstantQVRateDivExit (path.stateSeq n) := by
  simp only [frozenScaledJumpSqMartingale, scaledJumpSqSum,
    frozenScaledQVCompensator, Finset.sum_range_succ]
  ring

/-- Before absorption, the guarded frozen increment is the usual drift-divided
increment. -/
theorem frozenScaledJumpMartingale_succ_sub_of_exitRate_ne_zero
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ)
    (h : M.exitRateAt (path.stateSeq n) ≠ 0) :
    M.frozenScaledJumpMartingale path i (n + 1) -
        M.frozenScaledJumpMartingale path i n =
      (M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)) i -
        M.generatorDrift (path.stateSeq n) i /
          M.exitRateAt (path.stateSeq n) := by
  rw [M.frozenScaledJumpMartingale_succ_sub]
  simp [guardedGeneratorDriftDivExit, h]

/-- At an absorbing step with a frozen state, the centered frozen jump
martingale increment is exactly zero. -/
theorem frozenScaledJumpMartingale_succ_sub_eq_zero_of_exitRate_zero_of_stateSeq_succ_eq
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ)
    (hzero : M.exitRateAt (path.stateSeq n) = 0)
    (hstay : path.stateSeq (n + 1) = path.stateSeq n) :
    M.frozenScaledJumpMartingale path i (n + 1) -
        M.frozenScaledJumpMartingale path i n = 0 := by
  rw [M.frozenScaledJumpMartingale_succ_sub]
  have hjump : path.jumps n = path.stateSeq n := by
    simpa [CTMCPath.stateSeq] using hstay
  simp [guardedGeneratorDriftDivExit, hzero, hjump]

/-- At an absorbing step with a frozen state, the centered frozen squared-jump
increment is exactly zero. -/
theorem frozenScaledCoordJumpSqMartingale_succ_sub_eq_zero_of_exitRate_zero_of_stateSeq_succ_eq
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ)
    (hzero : M.exitRateAt (path.stateSeq n) = 0)
    (hstay : path.stateSeq (n + 1) = path.stateSeq n) :
    M.frozenScaledCoordJumpSqMartingale path i (n + 1) -
        M.frozenScaledCoordJumpSqMartingale path i n = 0 := by
  rw [M.frozenScaledCoordJumpSqMartingale_succ_sub]
  have hjump : path.jumps n = path.stateSeq n := by
    simpa [CTMCPath.stateSeq] using hstay
  simp [guardedInstantCoordQVRateDivExit, hzero, hjump]

/-- At an absorbing step with a frozen state, the centered frozen vector
squared-jump increment is exactly zero. -/
theorem frozenScaledJumpSqMartingale_succ_sub_eq_zero_of_exitRate_zero_of_stateSeq_succ_eq
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ)
    (hzero : M.exitRateAt (path.stateSeq n) = 0)
    (hstay : path.stateSeq (n + 1) = path.stateSeq n) :
    M.frozenScaledJumpSqMartingale path (n + 1) -
        M.frozenScaledJumpSqMartingale path n = 0 := by
  rw [M.frozenScaledJumpSqMartingale_succ_sub]
  have hjump : path.jumps n = path.stateSeq n := by
    simpa [CTMCPath.stateSeq] using hstay
  simp [guardedInstantQVRateDivExit, hzero, hjump]

theorem frozenScaledCoordQVCompensator_nonneg
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    0 ≤ M.frozenScaledCoordQVCompensator path i n := by
  simp only [frozenScaledCoordQVCompensator]
  exact Finset.sum_nonneg fun k _ =>
    M.guardedInstantCoordQVRateDivExit_nonneg (path.stateSeq k) i

theorem frozenScaledQVCompensator_nonneg
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) :
    0 ≤ M.frozenScaledQVCompensator path n := by
  simp only [frozenScaledQVCompensator]
  exact Finset.sum_nonneg fun k _ =>
    M.guardedInstantQVRateDivExit_nonneg (path.stateSeq k)

theorem frozenScaledCoordQVCompensator_mono
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) {m n : ℕ}
    (hmn : m ≤ n) :
    M.frozenScaledCoordQVCompensator path i m ≤
      M.frozenScaledCoordQVCompensator path i n := by
  simp only [frozenScaledCoordQVCompensator]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro k hk
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hmn))
    (fun k _ _ => M.guardedInstantCoordQVRateDivExit_nonneg (path.stateSeq k) i)

/-! ## Shifted frozen martingale skeleton -/

/-- The one-step-shifted frozen coordinate jump martingale. -/
noncomputable def shiftedFrozenScaledJumpMartingale
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (i : Fin d) (n : ℕ) (ω : Ω) : ℝ :=
  M.frozenScaledJumpMartingale (pathMap ω) i (n + 1)

theorem measurable_frozenScaledJumpDriftCompensator_canonicalRecordFiltration
    (M : DensityDepCTMC d) (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpDriftCompensator (M.canonicalPathMap records) i n) := by
  simp only [frozenScaledJumpDriftCompensator]
  refine Finset.measurable_sum _ ?_
  intro k hk
  have hk_le : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
  have hstate :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).stateSeq k) :=
    M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le hk_le
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      M.guardedGeneratorDriftDivExit x i)).comp hstate

theorem measurable_frozenScaledCoordQVCompensator_canonicalRecordFiltration
    (M : DensityDepCTMC d) (i : Fin d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n) := by
  simp only [frozenScaledCoordQVCompensator]
  refine Finset.measurable_sum _ ?_
  intro k hk
  have hk_le : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
  have hstate :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).stateSeq k) :=
    M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le hk_le
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      M.guardedInstantCoordQVRateDivExit x i)).comp hstate

theorem stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration
    (M : DensityDepCTMC d) (i : Fin d) :
    StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) :=
  (M.stronglyAdapted_scaledJumpSum_apply_canonicalRecordFiltration i).sub
    (fun n =>
      (M.measurable_frozenScaledJumpDriftCompensator_canonicalRecordFiltration
        i n).stronglyMeasurable)

theorem shiftedFrozenScaledJumpMartingale_stronglyAdapted
    (M : DensityDepCTMC d) (i : Fin d) :
    StronglyAdapted M.shiftedCanonicalRecordFiltration
      (fun n records =>
        M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records) := by
  intro n
  have h :=
    M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i (n + 1)
  simp only [shiftedFrozenScaledJumpMartingale]
  exact h

theorem shiftedFrozenScaledJumpMartingale_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records)
      (M.canonicalRecordMeasure x₀) := by
  simp only [shiftedFrozenScaledJumpMartingale]
  convert M.integrable_scaledJumpMartingale_canonicalRecordMeasure x₀ i (n + 1) using 1
  ext records
  simp only [frozenScaledJumpMartingale, scaledJumpMartingale]
  congr 1
  simp only [frozenScaledJumpDriftCompensator, scaledJumpDriftCompensator]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  by_cases hzero : M.exitRateAt ((M.canonicalPathMap records).stateSeq k) = 0
  · simp [guardedGeneratorDriftDivExit, hzero]
  · simp [guardedGeneratorDriftDivExit, hzero]

theorem shiftedFrozenScaledJumpMartingale_sq_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  simp only [shiftedFrozenScaledJumpMartingale]
  convert M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i (n + 1) using 1
  ext records
  congr 1
  simp only [frozenScaledJumpMartingale, scaledJumpMartingale]
  congr 1
  simp only [frozenScaledJumpDriftCompensator, scaledJumpDriftCompensator]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  by_cases hzero : M.exitRateAt ((M.canonicalPathMap records).stateSeq k) = 0
  · simp [guardedGeneratorDriftDivExit, hzero]
  · simp [guardedGeneratorDriftDivExit, hzero]

/-- Absorbing-aware first conditional moment for the next scaled coordinate
jump.  The proof should split the conditional next-state law into the
non-absorbing embedded row and the absorbing `dirac current_state` row. -/
theorem condExp_next_scaledState_sub_apply_eq_guardedGeneratorDriftDivExit_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        (M.scaledState ((records (n + 1)).2) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)) i)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀]
      fun records =>
        M.guardedGeneratorDriftDivExit
          ((M.canonicalPathMap records).stateSeq n) i := by
  rw [canonicalRecordFiltration,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
  have hcond :=
    M.condExp_next_scaledState_sub_apply_eq_integral_condDistrib x₀ n i
  have hnonabs_hist :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.embeddedStepMeasure
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_state_of_nonabsorbing
      x₀ n
  have habs_hist :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            Measure.dirac
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_state_of_absorbing
      x₀ n
  have hnonabs_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      hnonabs_hist
  have habs_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      habs_hist
  filter_upwards [hcond, hnonabs_records, habs_records] with records hce hnonabs habs
  rw [hce]
  let x := (M.canonicalPathMap records).stateSeq n
  by_cases hzero : M.exitRateAt x = 0
  · have hxabs : M.toQMatrix.IsAbsorbing x := by
      simpa [exitRateAt] using hzero
    have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) =
          Measure.dirac x := by
      have h := habs (by
        simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hxabs)
      simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using h
    rw [hdist]
    simp [guardedGeneratorDriftDivExit, hzero, x]
  · have hxnonabs : ¬M.toQMatrix.IsAbsorbing x := by
      simpa [exitRateAt] using hzero
    have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) =
          M.toQMatrix.embeddedStepMeasure x := by
      have h := hnonabs (by
        simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hxnonabs)
      simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using h
    rw [hdist]
    have hmul :=
      M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub x hxnonabs i
    let ce : ℝ :=
      ∫ y, (M.scaledState y - M.scaledState x) i
        ∂M.toQMatrix.embeddedStepMeasure x
    have hmul' : M.exitRateAt x * ce = M.generatorDrift x i := by
      simpa [ce] using hmul
    calc
      ce = M.generatorDrift x i / M.exitRateAt x := by
        calc
          ce = (M.exitRateAt x * ce) / M.exitRateAt x := by
            field_simp [hzero]
          _ = M.generatorDrift x i / M.exitRateAt x := by rw [hmul']
      _ = M.guardedGeneratorDriftDivExit x i := by
        rw [M.guardedGeneratorDriftDivExit_of_exitRate_ne_zero x i hzero]

/-- Absorbing-aware second conditional moment for the next scaled coordinate
jump. -/
theorem condExp_next_scaledState_sub_apply_sq_eq_guardedInstantCoordQVRateDivExit_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        ((M.scaledState ((records (n + 1)).2) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀]
      fun records =>
        M.guardedInstantCoordQVRateDivExit
          ((M.canonicalPathMap records).stateSeq n) i := by
  rw [canonicalRecordFiltration,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
  have hcond :=
    M.condExp_next_scaledState_sub_apply_sq_eq_integral_condDistrib x₀ n i
  have hnonabs_hist :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.embeddedStepMeasure
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_state_of_nonabsorbing
      x₀ n
  have habs_hist :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            Measure.dirac
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_state_of_absorbing
      x₀ n
  have hnonabs_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      hnonabs_hist
  have habs_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      habs_hist
  filter_upwards [hcond, hnonabs_records, habs_records] with records hce hnonabs habs
  rw [hce]
  let x := (M.canonicalPathMap records).stateSeq n
  by_cases hzero : M.exitRateAt x = 0
  · have hxabs : M.toQMatrix.IsAbsorbing x := by
      simpa [exitRateAt] using hzero
    have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) =
          Measure.dirac x := by
      have h := habs (by
        simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hxabs)
      simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using h
    rw [hdist]
    simp [guardedInstantCoordQVRateDivExit, hzero, x]
  · have hxnonabs : ¬M.toQMatrix.IsAbsorbing x := by
      simpa [exitRateAt] using hzero
    have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) =
          M.toQMatrix.embeddedStepMeasure x := by
      have h := hnonabs (by
        simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hxnonabs)
      simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using h
    rw [hdist]
    have hmul :=
      M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub_apply_sq x hxnonabs i
    let ce : ℝ :=
      ∫ y, ((M.scaledState y - M.scaledState x) i) ^ 2
        ∂M.toQMatrix.embeddedStepMeasure x
    have hmul' : M.exitRateAt x * ce = M.instantCoordQVRate x i := by
      simpa [ce] using hmul
    calc
      ce = M.instantCoordQVRate x i / M.exitRateAt x := by
        calc
          ce = (M.exitRateAt x * ce) / M.exitRateAt x := by
            field_simp [hzero]
          _ = M.instantCoordQVRate x i / M.exitRateAt x := by rw [hmul']
      _ = M.guardedInstantCoordQVRateDivExit x i := by
        rw [M.guardedInstantCoordQVRateDivExit_of_exitRate_ne_zero x i hzero]

/-- The product of the next holding time with the next raw coordinate scaled
jump is integrable. -/
theorem integrable_next_holdingTime_mul_next_scaledState_sub_apply
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (records (n + 1)).1 *
          (M.scaledState ((records (n + 1)).2) -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)) i)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let H : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let J : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
  have hH_int : Integrable H μ := by
    simpa [H, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ n
  have hHJ_meas : AEStronglyMeasurable (fun records => H records * J records) μ := by
    have hH_meas : Measurable H := by
      dsimp [H]
      fun_prop
    exact (hH_meas.mul (M.measurable_next_scaledState_sub_apply n i)).aestronglyMeasurable
  have hdom : Integrable (fun records => 2 * ‖H records‖) μ :=
    hH_int.norm.const_mul 2
  refine hdom.mono' hHJ_meas ?_
  refine ae_of_all _ fun records => ?_
  have hJ_bound : ‖J records‖ ≤ 2 := by
    dsimp [J]
    exact M.scaledState_sub_apply_norm_le_two
      ((M.canonicalPathMap records).stateSeq n) ((records (n + 1)).2) i
  rw [norm_mul]
  calc
    ‖H records‖ * ‖J records‖ ≤ ‖H records‖ * 2 := by
      exact mul_le_mul_of_nonneg_left hJ_bound (norm_nonneg _)
    _ = 2 * ‖H records‖ := by ring

/-- Conditional expectation of `holding_time * next_scaled_jump`, expressed
through the canonical conditional next-record distribution. -/
theorem condExp_next_holdingTime_mul_next_scaledState_sub_apply_eq_integral_condDistrib
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
        fun records : M.canonicalRecordΩ =>
          (records (n + 1)).1 *
            (M.scaledState ((records (n + 1)).2) -
              M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
        | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
        =ᵐ[M.canonicalRecordMeasure x₀]
      fun records : M.canonicalRecordΩ =>
        ∫ r, r.1 * (M.scaledState r.2 -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1) :=
    fun records => records (n + 1)
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
        QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) → ℝ :=
    fun p => p.2.1 * (M.scaledState p.2.2 -
      M.scaledState
        (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1)) i
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => records (n + 1))).aemeasurable
  have hf_meas : Measurable f := by
    dsimp [f]
    have hhold : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          p.2.1) := measurable_fst.comp measurable_snd
    have hnext : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          p.2.2) := measurable_snd.comp measurable_snd
    have hcurr : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) :=
      (QMatrix.measurable_currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) n).comp measurable_fst
    have hnext_coord : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          M.scaledState p.2.2 i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hnext
    have hcurr_coord : Measurable
        (fun p :
          (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) j) ×
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) (n + 1)) =>
          M.scaledState
            (QMatrix.currentStateFromHistory (S := Fin d → Fin (M.N + 1)) n p.1) i) :=
      (Measurable.of_discrete
        (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp hcurr
    simpa [Pi.sub_apply] using hhold.mul (hnext_coord.sub hcurr_coord)
  have hf_int :
      Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa [canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using
      M.integrable_next_holdingTime_mul_next_scaledState_sub_apply x₀ n i
  have h :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  simpa [μ, X, Y, f, canonicalRecordFiltration, canonicalPathMap,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe,
    QMatrix.currentStateFromHistory_frestrictLe] using h

/-- Absorbing-aware conditional cross moment for one jump-hold step. -/
theorem condExp_next_holdingTime_mul_next_scaledState_sub_apply_eq_guardedGeneratorDriftDivExit_mul_invExit_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        (records (n + 1)).1 *
          (M.scaledState ((records (n + 1)).2) -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)) i)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀]
      fun records =>
        M.guardedGeneratorDriftDivExit
          ((M.canonicalPathMap records).stateSeq n) i *
        (M.exitRateAt ((M.canonicalPathMap records).stateSeq n))⁻¹ := by
  rw [canonicalRecordFiltration,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
  have hcond :=
    M.condExp_next_holdingTime_mul_next_scaledState_sub_apply_eq_integral_condDistrib
      x₀ n i
  have hnonabs_hist :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ∀ h : ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist),
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => records (n + 1))
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.jumpHoldStepMeasure h := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_of_nonabsorbing
      x₀ n
  have habs_hist :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => records (n + 1))
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            Measure.dirac
              (0, QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_of_absorbing
      x₀ n
  have hnonabs_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      hnonabs_hist
  have habs_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      habs_hist
  filter_upwards [hcond, hnonabs_records, habs_records] with records hce hnonabs habs
  rw [hce]
  let x := (M.canonicalPathMap records).stateSeq n
  by_cases hzero : M.exitRateAt x = 0
  · have hxabs : M.toQMatrix.IsAbsorbing x := by
      simpa [exitRateAt] using hzero
    have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) =
          Measure.dirac (0, x) := by
      have h := habs (by
        simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hxabs)
      simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using h
    rw [hdist]
    simp [guardedGeneratorDriftDivExit, hzero, x]
  · have hxnonabs : ¬M.toQMatrix.IsAbsorbing x := by
      simpa [exitRateAt] using hzero
    have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => records (n + 1))
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) =
          M.toQMatrix.jumpHoldStepMeasure (by
            simpa [x] using hxnonabs) := by
      have h := hnonabs (by
        simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hxnonabs)
      simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using h
    rw [hdist]
    have hmul :=
      M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub x hxnonabs i
    let jumpMean : ℝ :=
      ∫ y, (M.scaledState y - M.scaledState x) i
        ∂M.toQMatrix.embeddedStepMeasure x
    have hmul' : M.exitRateAt x * jumpMean = M.generatorDrift x i := by
      simpa [jumpMean] using hmul
    have hprod :=
      M.toQMatrix.integral_jumpHoldStepMeasure_fst_mul_stateFun
        (s := x) hxnonabs
        (fun y : Fin d → Fin (M.N + 1) =>
          (M.scaledState y - M.scaledState x) i)
    have hhold :=
      M.toQMatrix.integral_holdingTimeMeasure_eq_inv_exitRate hxnonabs
    have hjump : jumpMean = M.generatorDrift x i / M.exitRateAt x := by
      calc
        jumpMean = (M.exitRateAt x * jumpMean) / M.exitRateAt x := by
          field_simp [hzero]
        _ = M.generatorDrift x i / M.exitRateAt x := by rw [hmul']
    calc
      (∫ r : ℝ × (Fin d → Fin (M.N + 1)),
          r.1 * (M.scaledState r.2 - M.scaledState x) i
          ∂M.toQMatrix.jumpHoldStepMeasure (by simpa [x] using hxnonabs))
          = (M.exitRateAt x)⁻¹ * jumpMean := by
              rw [hprod, hhold]
              rfl
      _ = M.guardedGeneratorDriftDivExit x i * (M.exitRateAt x)⁻¹ := by
              rw [hjump, M.guardedGeneratorDriftDivExit_of_exitRate_ne_zero x i hzero]
              ring

theorem shiftedFrozenScaledJumpMartingale_condExp_increment_eq_zero_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i (n + 1) records -
          M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records)
      | M.shiftedCanonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  simp only [shiftedFrozenScaledJumpMartingale]
  change
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1 + 1) -
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1))
      | M.canonicalRecordFiltration (n + 1)] =ᵐ[M.canonicalRecordMeasure x₀] 0
  let μ := M.canonicalRecordMeasure x₀
  let m := n + 1
  let nextJump : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (m + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq m)) i
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedGeneratorDriftDivExit ((M.canonicalPathMap records).stateSeq m) i
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (m + 1) -
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i m)
        =ᵐ[μ] fun records => nextJump records - comp records := by
    refine ae_of_all _ fun records => ?_
    simp [nextJump, comp, M.frozenScaledJumpMartingale_succ_sub, canonicalPathMap,
      QMatrix.recordTrajectoryToPath_stateSeq]
  have hnext :
      μ[nextJump | M.canonicalRecordFiltration m] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_apply_eq_guardedGeneratorDriftDivExit_ae
        x₀ m i
    dsimp [μ, nextJump, comp]
    simpa [Pi.sub_apply] using h
  have hcomp_meas :
      Measurable[M.canonicalRecordFiltration m] comp := by
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) =>
        M.guardedGeneratorDriftDivExit x i)).comp
          (M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration m)
  have hcomp_int : Integrable comp μ := by
    dsimp [comp, μ]
    convert M.integrable_generatorDrift_div_exitRate_stateSeq_canonicalRecordMeasure
      x₀ i m using 1
    ext records
    by_cases hzero : M.exitRateAt ((M.canonicalPathMap records).stateSeq m) = 0
    · simp [guardedGeneratorDriftDivExit, hzero]
    · simp [guardedGeneratorDriftDivExit, hzero]
  have hcomp :
      μ[comp | M.canonicalRecordFiltration m] = comp := by
    exact MeasureTheory.condExp_of_stronglyMeasurable
      (M.canonicalRecordFiltration.le m)
      hcomp_meas.stronglyMeasurable
      hcomp_int
  have hsub :
      μ[nextJump - comp | M.canonicalRecordFiltration m] =ᵐ[μ]
        μ[nextJump | M.canonicalRecordFiltration m] -
          μ[comp | M.canonicalRecordFiltration m] :=
    MeasureTheory.condExp_sub
      (M.integrable_next_scaledState_sub_apply x₀ m i)
      hcomp_int
      (M.canonicalRecordFiltration m)
  refine (MeasureTheory.condExp_congr_ae hinc).trans ?_
  change μ[nextJump - comp | M.canonicalRecordFiltration m] =ᵐ[μ] 0
  rw [hcomp] at hsub
  filter_upwards [hsub, hnext] with records hsub_eq hnext_eq
  rw [hsub_eq]
  simp [Pi.sub_apply, hnext_eq]

theorem shiftedFrozenScaledJumpMartingale_martingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Martingale
      (fun n records =>
        M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records)
      M.shiftedCanonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  martingale_of_condExp_sub_eq_zero_nat
    (M.shiftedFrozenScaledJumpMartingale_stronglyAdapted i)
    (M.shiftedFrozenScaledJumpMartingale_integrable x₀ i)
    (fun n =>
      M.shiftedFrozenScaledJumpMartingale_condExp_increment_eq_zero_ae x₀ n i)

theorem shiftedFrozenScaledJumpMartingale_sq_submartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Submartingale
      (fun n records =>
        (M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records) ^ 2)
      M.shiftedCanonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records
  let μ := M.canonicalRecordMeasure x₀
  have hmart : Martingale Z M.shiftedCanonicalRecordFiltration μ := by
    simpa [Z, μ] using
      M.shiftedFrozenScaledJumpMartingale_martingale x₀ i
  refine submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.shiftedFrozenScaledJumpMartingale_stronglyAdapted i n).pow 2
  · intro n
    simpa [Z] using
      M.shiftedFrozenScaledJumpMartingale_sq_integrable x₀ i n
  · intro n
    have hcvx : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
      simpa using (show Even (2 : ℕ) by norm_num).convexOn_pow (𝕜 := ℝ)
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ((μ[Z (n + 1) | M.shiftedCanonicalRecordFiltration n]) records) ^ 2)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => (Z (n + 1) records) ^ 2)
          | M.shiftedCanonicalRecordFiltration n] := by
      simpa [Function.comp_def] using
        (ConvexOn.map_condExp_le_univ
          (μ := μ) (m := M.shiftedCanonicalRecordFiltration n)
          (f := Z (n + 1)) (φ := fun x : ℝ => x ^ 2)
          (M.shiftedCanonicalRecordFiltration.le n)
          hcvx (continuous_pow 2).lowerSemicontinuous
          (hmart.integrable (n + 1))
          (by
            simpa [Z] using
              M.shiftedFrozenScaledJumpMartingale_sq_integrable x₀ i (n + 1)))
    have hcond : μ[Z (n + 1) | M.shiftedCanonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

theorem shiftedFrozenScaledJumpMartingale_norm_submartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Submartingale
      (fun n records =>
        ‖M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records‖)
      M.shiftedCanonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records
  have hmart : Martingale Z M.shiftedCanonicalRecordFiltration μ := by
    simpa [Z, μ] using
      M.shiftedFrozenScaledJumpMartingale_martingale x₀ i
  refine submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.shiftedFrozenScaledJumpMartingale_stronglyAdapted i n).norm
  · intro n
    simpa [Z] using
      (M.shiftedFrozenScaledJumpMartingale_integrable x₀ i n).norm
  · intro n
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ‖(μ[Z (n + 1) | M.shiftedCanonicalRecordFiltration n]) records‖)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => ‖Z (n + 1) records‖)
          | M.shiftedCanonicalRecordFiltration n] :=
      norm_condExp_le
    have hcond : μ[Z (n + 1) | M.shiftedCanonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

/-! ## Fixed-time frozen Doob layer-cake infrastructure -/

theorem frozenScaledJumpDriftCompensator_eq_scaledJumpDriftCompensator
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenScaledJumpDriftCompensator path i n =
      M.scaledJumpDriftCompensator path i n := by
  simp only [frozenScaledJumpDriftCompensator, scaledJumpDriftCompensator]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  by_cases hzero : M.exitRateAt (path.stateSeq k) = 0
  · simp [guardedGeneratorDriftDivExit, hzero]
  · simp [guardedGeneratorDriftDivExit, hzero]

theorem frozenScaledJumpMartingale_eq_scaledJumpMartingale
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenScaledJumpMartingale path i n =
      M.scaledJumpMartingale path i n := by
  simp [frozenScaledJumpMartingale, scaledJumpMartingale,
    M.frozenScaledJumpDriftCompensator_eq_scaledJumpDriftCompensator path i n]

theorem frozenScaledCoordQVCompensator_eq_scaledCoordQVCompensator
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenScaledCoordQVCompensator path i n =
      M.scaledCoordQVCompensator path i n := by
  simp only [frozenScaledCoordQVCompensator, scaledCoordQVCompensator]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  by_cases hzero : M.exitRateAt (path.stateSeq k) = 0
  · simp [guardedInstantCoordQVRateDivExit, hzero]
  · simp [guardedInstantCoordQVRateDivExit, hzero]

theorem frozenScaledCoordQVCompensator_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) := by
  convert M.integrable_scaledCoordQVCompensator_canonicalRecordMeasure x₀ i n using 1
  ext records
  exact M.frozenScaledCoordQVCompensator_eq_scaledCoordQVCompensator
    (M.canonicalPathMap records) i n

theorem frozenScaledQVCompensator_eq_scaledQVCompensator
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ) :
    M.frozenScaledQVCompensator path n =
      M.scaledQVCompensator path n := by
  simp only [frozenScaledQVCompensator, scaledQVCompensator]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  by_cases hzero : M.exitRateAt (path.stateSeq k) = 0
  · simp [guardedInstantQVRateDivExit, hzero]
  · simp [guardedInstantQVRateDivExit, hzero]

theorem frozenScaledQVCompensator_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledQVCompensator (M.canonicalPathMap records) n)
      (M.canonicalRecordMeasure x₀) := by
  convert M.integrable_scaledQVCompensator_canonicalRecordMeasure x₀ n using 1
  ext records
  exact M.frozenScaledQVCompensator_eq_scaledQVCompensator
    (M.canonicalPathMap records) n

theorem measurable_next_scaledState_sub_norm_sq
    (M : DensityDepCTMC d) (n : ℕ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ‖M.scaledState ((records (n + 1)).2) -
        M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2) := by
  have hvec : Measurable (fun records : M.canonicalRecordΩ =>
      M.scaledState ((records (n + 1)).2) -
        M.scaledState ((M.canonicalPathMap records).stateSeq n)) := by
    rw [measurable_pi_iff]
    intro i
    exact M.measurable_next_scaledState_sub_apply n i
  exact hvec.norm.pow_const 2

theorem integrable_next_scaledState_sub_norm_sq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (n : ℕ) :
    Integrable (fun records : M.canonicalRecordΩ =>
      ‖M.scaledState ((records (n + 1)).2) -
        M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  refine Integrable.of_bound
    (M.measurable_next_scaledState_sub_norm_sq n).aestronglyMeasurable 4 ?_
  refine ae_of_all _ fun records => ?_
  let v :=
    M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)
  have hv : ‖v‖ ≤ 2 := by
    calc
      ‖v‖ ≤ ‖M.scaledState ((records (n + 1)).2)‖ +
          ‖M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ := by
            simpa [v] using norm_sub_le
              (M.scaledState ((records (n + 1)).2))
              (M.scaledState ((M.canonicalPathMap records).stateSeq n))
      _ ≤ 1 + 1 := add_le_add
          (M.scaledState_norm_le ((records (n + 1)).2))
          (M.scaledState_norm_le ((M.canonicalPathMap records).stateSeq n))
      _ = 2 := by norm_num
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v‖)]
  have hsq : ‖v‖ ^ 2 ≤ (2 : ℝ) ^ 2 :=
    sq_le_sq' (by nlinarith [norm_nonneg v]) hv
  norm_num at hsq
  exact hsq

theorem condExp_next_scaledState_sub_norm_sq_eq_integral_condDistrib
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (n : ℕ) :
    (M.canonicalRecordMeasure x₀)[
        fun records : M.canonicalRecordΩ =>
          ‖M.scaledState ((records (n + 1)).2) -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2
        | MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
        =ᵐ[M.canonicalRecordMeasure x₀]
      fun records : M.canonicalRecordΩ =>
        ∫ y, ‖M.scaledState y -
            M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2
          ∂ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) := by
  let μ := M.canonicalRecordMeasure x₀
  let S := Fin d → Fin (M.N + 1)
  let X : M.canonicalRecordΩ →
      ((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace S j) :=
    Preorder.frestrictLe n
  let Y : M.canonicalRecordΩ → S :=
    fun records => (records (n + 1)).2
  let f :
      (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace S j) × S) → ℝ :=
    fun p => ‖M.scaledState p.2 -
      M.scaledState (QMatrix.currentStateFromHistory (S := S) n p.1)‖ ^ 2
  have hX : Measurable X := by
    dsimp [X]
    exact Preorder.measurable_frestrictLe n
  have hY : AEMeasurable Y μ := by
    dsimp [Y]
    exact (by fun_prop : Measurable
      (fun records : M.canonicalRecordΩ => (records (n + 1)).2)).aemeasurable
  have hf_meas : Measurable f := by
    dsimp [f]
    have hvec : Measurable
        (fun p : (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace S j) × S) =>
          M.scaledState p.2 -
            M.scaledState (QMatrix.currentStateFromHistory (S := S) n p.1)) := by
      rw [measurable_pi_iff]
      intro i
      have hnext_coord : Measurable
          (fun p : (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace S j) × S) =>
            M.scaledState p.2 i) :=
        (Measurable.of_discrete (f := fun x : S => M.scaledState x i)).comp measurable_snd
      have hcurr_coord : Measurable
          (fun p : (((j : Finset.Iic n) → QMatrix.JumpHoldTrajectorySpace S j) × S) =>
            M.scaledState (QMatrix.currentStateFromHistory (S := S) n p.1) i) :=
        (Measurable.of_discrete (f := fun x : S => M.scaledState x i)).comp
          ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
      simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord
    exact hvec.norm.pow_const 2
  have hf_int :
      Integrable (fun a : M.canonicalRecordΩ => f (X a, Y a)) μ := by
    dsimp [f, X, Y, μ]
    simpa [canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using
      M.integrable_next_scaledState_sub_norm_sq x₀ n
  have h :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      (μ := μ) (X := X) (Y := Y) (f := f)
      hX hY hf_meas.stronglyMeasurable hf_int
  simpa [μ, X, Y, f, canonicalRecordFiltration, canonicalPathMap,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe,
    QMatrix.currentStateFromHistory_frestrictLe] using h

theorem condExp_next_scaledState_sub_norm_sq_eq_guardedInstantQVRateDivExit_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        ‖M.scaledState ((records (n + 1)).2) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀]
      fun records =>
        M.guardedInstantQVRateDivExit
          ((M.canonicalPathMap records).stateSeq n) := by
  rw [canonicalRecordFiltration,
    QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
  have hcond :=
    M.condExp_next_scaledState_sub_norm_sq_eq_integral_condDistrib x₀ n
  have hnonabs_hist :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        ¬M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            M.toQMatrix.embeddedStepMeasure
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_state_of_nonabsorbing
      x₀ n
  have habs_hist :
      ∀ᵐ hist ∂(M.canonicalRecordMeasure x₀).map (Preorder.frestrictLe n),
        M.toQMatrix.IsAbsorbing
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) n hist) →
          ProbabilityTheory.condDistrib
              (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
              (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀) hist =
            Measure.dirac
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) n hist) := by
    unfold canonicalRecordMeasure
    exact M.toQMatrix.condDistrib_canonicalRecordMeasure_next_state_of_absorbing
      x₀ n
  have hnonabs_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      hnonabs_hist
  have habs_records :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
      habs_hist
  filter_upwards [hcond, hnonabs_records, habs_records] with records hce hnonabs habs
  rw [hce]
  let x := (M.canonicalPathMap records).stateSeq n
  by_cases hzero : M.exitRateAt x = 0
  · have hxabs : M.toQMatrix.IsAbsorbing x := by
      simpa [exitRateAt] using hzero
    have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) =
          Measure.dirac x := by
      have h := habs (by
        simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hxabs)
      simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using h
    rw [hdist]
    simp [guardedInstantQVRateDivExit, hzero, x]
  · have hxnonabs : ¬M.toQMatrix.IsAbsorbing x := by
      simpa [exitRateAt] using hzero
    have hdist :
        ProbabilityTheory.condDistrib
            (fun records : M.canonicalRecordΩ => (records (n + 1)).2)
            (Preorder.frestrictLe n) (M.canonicalRecordMeasure x₀)
            (Preorder.frestrictLe n records) =
          M.toQMatrix.embeddedStepMeasure x := by
      have h := hnonabs (by
        simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using hxnonabs)
      simpa [x, canonicalPathMap, QMatrix.currentStateFromHistory_frestrictLe] using h
    rw [hdist]
    have hmul :=
      M.exitRateAt_mul_integral_embeddedStepMeasure_scaledState_sub_sq x hxnonabs
    let ce : ℝ :=
      ∫ y, ‖M.scaledState y - M.scaledState x‖ ^ 2
        ∂M.toQMatrix.embeddedStepMeasure x
    have hmul' : M.exitRateAt x * ce = M.instantQVRate x := by
      simpa [ce] using hmul
    calc
      ce = M.instantQVRate x / M.exitRateAt x := by
        calc
          ce = (M.exitRateAt x * ce) / M.exitRateAt x := by
            field_simp [hzero]
          _ = M.instantQVRate x / M.exitRateAt x := by rw [hmul']
      _ = M.guardedInstantQVRateDivExit x := by
        rw [M.guardedInstantQVRateDivExit_of_exitRate_ne_zero x hzero]

theorem integral_next_scaledState_sub_norm_sq_eq_integral_guardedInstantQVRateDivExit
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) :
    ∫ records,
        ‖M.scaledState ((records (n + 1)).2) -
          M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        M.guardedInstantQVRateDivExit
          ((M.canonicalPathMap records).stateSeq n)
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2
  let B : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedInstantQVRateDivExit ((M.canonicalPathMap records).stateSeq n)
  have hcond :
      μ[A | M.canonicalRecordFiltration n] =ᵐ[μ] B := by
    simpa [A, B, μ] using
      M.condExp_next_scaledState_sub_norm_sq_eq_guardedInstantQVRateDivExit_ae
        x₀ n
  calc
    ∫ records, A records ∂μ
        = ∫ records,
            (μ[A | M.canonicalRecordFiltration n]) records ∂μ := by
            exact (integral_condExp
              (μ := μ)
              (m := M.canonicalRecordFiltration n)
              (f := A)
              (M.canonicalRecordFiltration.le n)).symm
    _ = ∫ records, B records ∂μ := by
          exact integral_congr_ae hcond
    _ = ∫ records,
        M.guardedInstantQVRateDivExit
          ((M.canonicalPathMap records).stateSeq n)
        ∂M.canonicalRecordMeasure x₀ := by
          simp [B, μ]

theorem integrable_guardedInstantQVRateDivExit_stateSeq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.guardedInstantQVRateDivExit ((M.canonicalPathMap records).stateSeq n))
      (M.canonicalRecordMeasure x₀) := by
  have hsucc :
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.frozenScaledQVCompensator (M.canonicalPathMap records) (n + 1))
        (M.canonicalRecordMeasure x₀) :=
    M.frozenScaledQVCompensator_integrable x₀ (n + 1)
  have hprev :
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.frozenScaledQVCompensator (M.canonicalPathMap records) n)
        (M.canonicalRecordMeasure x₀) :=
    M.frozenScaledQVCompensator_integrable x₀ n
  refine (hsucc.sub hprev).congr ?_
  refine ae_of_all _ fun records => ?_
  have hsucc_eq :=
    M.frozenScaledQVCompensator_succ (M.canonicalPathMap records) n
  change M.frozenScaledQVCompensator (M.canonicalPathMap records) (n + 1) -
      M.frozenScaledQVCompensator (M.canonicalPathMap records) n =
    M.guardedInstantQVRateDivExit ((M.canonicalPathMap records).stateSeq n)
  rw [hsucc_eq]
  ring

theorem integral_scaledJumpSqSum_eq_integral_frozenScaledQVCompensator
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) :
    ∫ records, M.scaledJumpSqSum (M.canonicalPathMap records) n
      ∂M.canonicalRecordMeasure x₀ =
    ∫ records, M.frozenScaledQVCompensator (M.canonicalPathMap records) n
      ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  have hleft_int : ∀ k ∈ Finset.range n,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          ‖M.scaledState ((records (k + 1)).2) -
            M.scaledState ((M.canonicalPathMap records).stateSeq k)‖ ^ 2)
        μ := by
    intro k _hk
    simpa [μ] using M.integrable_next_scaledState_sub_norm_sq x₀ k
  have hguard_int : ∀ k ∈ Finset.range n,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.guardedInstantQVRateDivExit
            ((M.canonicalPathMap records).stateSeq k))
        μ := by
    intro k _hk
    simpa [μ] using M.integrable_guardedInstantQVRateDivExit_stateSeq x₀ k
  calc
    ∫ records, M.scaledJumpSqSum (M.canonicalPathMap records) n ∂μ
        = ∫ records,
            (∑ k ∈ Finset.range n,
              ‖M.scaledState ((records (k + 1)).2) -
                M.scaledState ((M.canonicalPathMap records).stateSeq k)‖ ^ 2)
            ∂μ := by
            apply integral_congr_ae
            refine ae_of_all _ fun records => ?_
            simp [scaledJumpSqSum, canonicalPathMap,
              QMatrix.recordTrajectoryToPath_stateSeq]
    _ = ∑ k ∈ Finset.range n,
          ∫ records,
            ‖M.scaledState ((records (k + 1)).2) -
              M.scaledState ((M.canonicalPathMap records).stateSeq k)‖ ^ 2
            ∂μ := by
          rw [integral_finset_sum]
          intro k hk
          exact hleft_int k hk
    _ = ∑ k ∈ Finset.range n,
          ∫ records,
            M.guardedInstantQVRateDivExit
              ((M.canonicalPathMap records).stateSeq k)
            ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          simpa [μ] using
            M.integral_next_scaledState_sub_norm_sq_eq_integral_guardedInstantQVRateDivExit
              x₀ k
    _ = ∫ records,
        (∑ k ∈ Finset.range n,
          M.guardedInstantQVRateDivExit
            ((M.canonicalPathMap records).stateSeq k))
        ∂μ := by
          rw [integral_finset_sum]
          intro k hk
          exact hguard_int k hk
    _ = ∫ records,
        M.frozenScaledQVCompensator (M.canonicalPathMap records) n
        ∂M.canonicalRecordMeasure x₀ := by
          simp [frozenScaledQVCompensator, μ]

theorem measurable_scaledJumpSqSum_canonicalRecordFiltration
    (M : DensityDepCTMC d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.scaledJumpSqSum (M.canonicalPathMap records) n) := by
  induction n with
  | zero =>
      simp [scaledJumpSqSum]
  | succ n ih =>
      have ih_later :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              M.scaledJumpSqSum (M.canonicalPathMap records) n) :=
        ih.mono ((M.canonicalRecordFiltration).mono (Nat.le_succ n)) le_rfl
      have hnext_state :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              (M.canonicalPathMap records).stateSeq (n + 1)) :=
        M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration (n + 1)
      have hcurr_state :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              (M.canonicalPathMap records).stateSeq n) :=
        M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le
          (Nat.le_succ n)
      have hvec :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              M.scaledState ((M.canonicalPathMap records).stateSeq (n + 1)) -
                M.scaledState ((M.canonicalPathMap records).stateSeq n)) := by
        refine (@measurable_pi_iff M.canonicalRecordΩ (Fin d) (fun _ => ℝ)
          (M.canonicalRecordFiltration (n + 1)) (fun _ => inferInstance)
          (g := fun records : M.canonicalRecordΩ =>
            M.scaledState ((M.canonicalPathMap records).stateSeq (n + 1)) -
              M.scaledState ((M.canonicalPathMap records).stateSeq n))).2 ?_
        intro i
        have hnext_coord :
            Measurable[M.canonicalRecordFiltration (n + 1)]
              (fun records : M.canonicalRecordΩ =>
                M.scaledState ((M.canonicalPathMap records).stateSeq (n + 1)) i) :=
          (Measurable.of_discrete
            (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp
              hnext_state
        have hcurr_coord :
            Measurable[M.canonicalRecordFiltration (n + 1)]
              (fun records : M.canonicalRecordΩ =>
                M.scaledState ((M.canonicalPathMap records).stateSeq n) i) :=
          (Measurable.of_discrete
            (f := fun x : Fin d → Fin (M.N + 1) => M.scaledState x i)).comp
              hcurr_state
        simpa [Pi.sub_apply] using hnext_coord.sub hcurr_coord
      have hjump :
          Measurable[M.canonicalRecordFiltration (n + 1)]
            (fun records : M.canonicalRecordΩ =>
              ‖M.scaledState ((M.canonicalPathMap records).stateSeq (n + 1)) -
                M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2) :=
        (measurable_norm.comp hvec).pow_const 2
      simpa [scaledJumpSqSum, Finset.sum_range_succ] using ih_later.add hjump

theorem stronglyAdapted_scaledJumpSqSum_canonicalRecordFiltration
    (M : DensityDepCTMC d) :
    StronglyAdapted M.canonicalRecordFiltration
      (fun n records => M.scaledJumpSqSum (M.canonicalPathMap records) n) :=
  fun n => (M.measurable_scaledJumpSqSum_canonicalRecordFiltration n).stronglyMeasurable

theorem integrable_scaledJumpSqSum_canonicalRecordMeasure
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.scaledJumpSqSum (M.canonicalPathMap records) n)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  simp only [scaledJumpSqSum]
  exact integrable_finset_sum (Finset.range n) fun k _hk => by
    simpa [μ, canonicalPathMap, QMatrix.recordTrajectoryToPath_stateSeq] using
      M.integrable_next_scaledState_sub_norm_sq x₀ k

theorem measurable_frozenScaledQVCompensator_canonicalRecordFiltration
    (M : DensityDepCTMC d) (n : ℕ) :
    Measurable[M.canonicalRecordFiltration n]
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledQVCompensator (M.canonicalPathMap records) n) := by
  simp only [frozenScaledQVCompensator]
  refine Finset.measurable_sum _ fun k hk => ?_
  have hk_le_n : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
  have hstate :
      Measurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ =>
          (M.canonicalPathMap records).stateSeq k) :=
    M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le hk_le_n
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) =>
      M.guardedInstantQVRateDivExit x)).comp hstate

theorem stronglyAdapted_frozenScaledJumpSqMartingale_canonicalRecordFiltration
    (M : DensityDepCTMC d) :
    StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.frozenScaledJumpSqMartingale (M.canonicalPathMap records) n) :=
  (M.stronglyAdapted_scaledJumpSqSum_canonicalRecordFiltration).sub
    (fun n =>
      (M.measurable_frozenScaledQVCompensator_canonicalRecordFiltration
        n).stronglyMeasurable)

theorem integrable_frozenScaledJumpSqMartingale_canonicalRecordMeasure
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpSqMartingale (M.canonicalPathMap records) n)
      (M.canonicalRecordMeasure x₀) :=
  (M.integrable_scaledJumpSqSum_canonicalRecordMeasure x₀ n).sub
    (M.frozenScaledQVCompensator_integrable x₀ n)

theorem condExp_frozenScaledJumpSqMartingale_increment_eq_zero_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpSqMartingale (M.canonicalPathMap records) (n + 1) -
          M.frozenScaledJumpSqMartingale (M.canonicalPathMap records) n)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let nextSqJump : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)‖ ^ 2
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedInstantQVRateDivExit
      ((M.canonicalPathMap records).stateSeq n)
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpSqMartingale (M.canonicalPathMap records) (n + 1) -
          M.frozenScaledJumpSqMartingale (M.canonicalPathMap records) n)
        =ᵐ[μ] fun records => nextSqJump records - comp records := by
    refine ae_of_all _ fun records => ?_
    simp [nextSqJump, comp, M.frozenScaledJumpSqMartingale_succ_sub,
      canonicalPathMap, QMatrix.recordTrajectoryToPath_stateSeq]
  have hnext :
      μ[nextSqJump | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_norm_sq_eq_guardedInstantQVRateDivExit_ae
        x₀ n
    dsimp [μ, nextSqJump, comp]
    simpa using h
  have hcomp_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n] comp := by
    have hstate :=
      M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n
    have hg : Measurable (fun x : Fin d → Fin (M.N + 1) =>
        M.guardedInstantQVRateDivExit x) := Measurable.of_discrete
    exact (hg.comp hstate).stronglyMeasurable
  have hcomp_int : Integrable comp μ := by
    exact (M.frozenScaledQVCompensator_integrable x₀ (n + 1)).sub
      (M.frozenScaledQVCompensator_integrable x₀ n) |>.congr
        (ae_of_all _ fun records => by
          have hsucc :=
            M.frozenScaledQVCompensator_succ
              (M.canonicalPathMap records) n
          dsimp [comp]
          linarith)
  have hcomp :
      μ[comp | M.canonicalRecordFiltration n] = comp := by
    exact condExp_of_stronglyMeasurable
      (M.canonicalRecordFiltration.le n) hcomp_sm hcomp_int
  have hsub :
      μ[nextSqJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ]
        μ[nextSqJump | M.canonicalRecordFiltration n] -
          μ[comp | M.canonicalRecordFiltration n] :=
    condExp_sub
      (M.integrable_next_scaledState_sub_norm_sq x₀ n)
      hcomp_int
      (M.canonicalRecordFiltration n)
  refine (condExp_congr_ae hinc).trans ?_
  change μ[nextSqJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ] 0
  rw [hcomp] at hsub
  filter_upwards [hsub, hnext] with records hsub_eq hnext_eq
  rw [hsub_eq]
  simp [hnext_eq]

theorem frozenScaledJumpSqMartingale_martingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    Martingale
      (fun n records =>
        M.frozenScaledJumpSqMartingale (M.canonicalPathMap records) n)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  martingale_of_condExp_sub_eq_zero_nat
    (M.stronglyAdapted_frozenScaledJumpSqMartingale_canonicalRecordFiltration)
    (M.integrable_frozenScaledJumpSqMartingale_canonicalRecordMeasure x₀)
    (fun n =>
      M.condExp_frozenScaledJumpSqMartingale_increment_eq_zero_ae x₀ n)

theorem stronglyAdapted_frozenScaledCoordJumpSqMartingale_canonicalRecordFiltration
    (M : DensityDepCTMC d) (i : Fin d) :
    StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.frozenScaledCoordJumpSqMartingale (M.canonicalPathMap records) i n) :=
  (M.stronglyAdapted_scaledCoordJumpSqSum_canonicalRecordFiltration i).sub
    (fun n =>
      (M.measurable_frozenScaledCoordQVCompensator_canonicalRecordFiltration
        i n).stronglyMeasurable)

theorem integrable_frozenScaledCoordJumpSqMartingale_canonicalRecordMeasure
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledCoordJumpSqMartingale (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) :=
  (M.integrable_scaledCoordJumpSqSum_canonicalRecordMeasure x₀ i n).sub
    (M.frozenScaledCoordQVCompensator_integrable x₀ i n)

theorem condExp_frozenScaledCoordJumpSqMartingale_increment_eq_zero_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledCoordJumpSqMartingale (M.canonicalPathMap records) i (n + 1) -
          M.frozenScaledCoordJumpSqMartingale (M.canonicalPathMap records) i n)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let nextSqJump : M.canonicalRecordΩ → ℝ := fun records =>
    ((M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i) ^ 2
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedInstantCoordQVRateDivExit
      ((M.canonicalPathMap records).stateSeq n) i
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledCoordJumpSqMartingale (M.canonicalPathMap records) i (n + 1) -
          M.frozenScaledCoordJumpSqMartingale (M.canonicalPathMap records) i n)
        =ᵐ[μ] fun records => nextSqJump records - comp records := by
    refine ae_of_all _ fun records => ?_
    simp [nextSqJump, comp, M.frozenScaledCoordJumpSqMartingale_succ_sub,
      canonicalPathMap, QMatrix.recordTrajectoryToPath_stateSeq]
  have hnext :
      μ[nextSqJump | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_apply_sq_eq_guardedInstantCoordQVRateDivExit_ae
        x₀ n i
    dsimp [μ, nextSqJump, comp]
    simpa [Pi.sub_apply] using h
  have hcomp_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n] comp := by
    have hstate :=
      M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n
    have hg : Measurable (fun x : Fin d → Fin (M.N + 1) =>
        M.guardedInstantCoordQVRateDivExit x i) := Measurable.of_discrete
    exact (hg.comp hstate).stronglyMeasurable
  have hcomp_int : Integrable comp μ := by
    exact (M.frozenScaledCoordQVCompensator_integrable x₀ i (n + 1)).sub
      (M.frozenScaledCoordQVCompensator_integrable x₀ i n) |>.congr
        (ae_of_all _ fun records => by
          have hsucc :=
            M.frozenScaledCoordQVCompensator_succ
              (M.canonicalPathMap records) i n
          dsimp [comp]
          linarith)
  have hcomp :
      μ[comp | M.canonicalRecordFiltration n] = comp := by
    exact condExp_of_stronglyMeasurable
      (M.canonicalRecordFiltration.le n) hcomp_sm hcomp_int
  have hsub :
      μ[nextSqJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ]
        μ[nextSqJump | M.canonicalRecordFiltration n] -
          μ[comp | M.canonicalRecordFiltration n] :=
    condExp_sub
      (M.integrable_next_scaledState_sub_apply_sq x₀ n i)
      hcomp_int
      (M.canonicalRecordFiltration n)
  refine (condExp_congr_ae hinc).trans ?_
  change μ[nextSqJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ] 0
  rw [hcomp] at hsub
  filter_upwards [hsub, hnext] with records hsub_eq hnext_eq
  rw [hsub_eq]
  simp [Pi.sub_apply, hnext_eq]

theorem frozenScaledCoordJumpSqMartingale_martingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) (i : Fin d) :
    Martingale
      (fun n records =>
        M.frozenScaledCoordJumpSqMartingale (M.canonicalPathMap records) i n)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  martingale_of_condExp_sub_eq_zero_nat
    (M.stronglyAdapted_frozenScaledCoordJumpSqMartingale_canonicalRecordFiltration i)
    (M.integrable_frozenScaledCoordJumpSqMartingale_canonicalRecordMeasure x₀ i)
    (fun n =>
      M.condExp_frozenScaledCoordJumpSqMartingale_increment_eq_zero_ae x₀ n i)

theorem integral_frozenScaledCoordJumpSqMartingale_eq_zero
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    ∫ records, M.frozenScaledCoordJumpSqMartingale (M.canonicalPathMap records) i n
      ∂M.canonicalRecordMeasure x₀ = 0 := by
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.frozenScaledCoordJumpSqMartingale (M.canonicalPathMap records) i n
  have hmart : Martingale Z M.canonicalRecordFiltration
      (M.canonicalRecordMeasure x₀) := by
    simpa [Z] using M.frozenScaledCoordJumpSqMartingale_martingale x₀ i
  have hset := hmart.setIntegral_eq (Nat.zero_le n)
    (s := Set.univ) (by simp)
  simpa [Z] using hset.symm

theorem integral_scaledCoordJumpSqSum_eq_integral_frozenScaledCoordQVCompensator
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    ∫ records, M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n
      ∂M.canonicalRecordMeasure x₀ =
    ∫ records, M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
      ∂M.canonicalRecordMeasure x₀ := by
  have hzero :=
    M.integral_frozenScaledCoordJumpSqMartingale_eq_zero x₀ i n
  have hsub :
      ∫ records,
          (M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n -
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n)
          ∂M.canonicalRecordMeasure x₀ =
        ∫ records, M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n
          ∂M.canonicalRecordMeasure x₀ -
        ∫ records, M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
          ∂M.canonicalRecordMeasure x₀ := by
    exact integral_sub
      (M.integrable_scaledCoordJumpSqSum_canonicalRecordMeasure x₀ i n)
      (M.frozenScaledCoordQVCompensator_integrable x₀ i n)
  have hdiff :
      ∫ records, M.scaledCoordJumpSqSum (M.canonicalPathMap records) i n
          ∂M.canonicalRecordMeasure x₀ -
        ∫ records, M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
          ∂M.canonicalRecordMeasure x₀ = 0 := by
    rw [← hsub]
    simpa [frozenScaledCoordJumpSqMartingale] using hzero
  linarith

/-- Multiplying the next holding time by a predictable finite-state
coordinate-QV coefficient preserves integrability under the guarded absorbing
canonical law. -/
theorem integrable_instantCoordQVRate_mul_next_holdingTime_guarded
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i *
          (records (n + 1)).1)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i
  let Y : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  obtain ⟨C, _hC_nonneg, hC⟩ := M.exists_instantCoordQVRate_abs_bound i
  have hA_meas : Measurable A := by
    exact (M.measurable_instantCoordQVRate_stateSeq_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n) le_rfl
  have hY_int : Integrable Y μ := by
    simpa [Y, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ n
  have hAY_sm : AEStronglyMeasurable (fun records => A records * Y records) μ :=
    hA_meas.aestronglyMeasurable.mul hY_int.aestronglyMeasurable
  have hbound :
      ∀ᵐ records ∂μ, ‖A records * Y records‖ ≤ C * ‖Y records‖ := by
    refine ae_of_all _ fun records => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hC ((M.canonicalPathMap records).stateSeq n)) (norm_nonneg _)
  have hdom : Integrable (fun records => C * ‖Y records‖) μ :=
    hY_int.norm.const_mul C
  exact hdom.mono' hAY_sm hbound

/-- Guarded fixed-step compensator bridge: a predictable coordinate-QV rate
times the next raw holding time has expectation equal to the corresponding
guarded embedded QV-compensator summand. -/
theorem integral_instantCoordQVRate_mul_next_holdingTime_eq_integral_guardedDivExit
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    ∫ records,
        M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i *
          (records (n + 1)).1
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        M.guardedInstantCoordQVRateDivExit
          ((M.canonicalPathMap records).stateSeq n) i
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq n) i
  let Y : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let B : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedInstantCoordQVRateDivExit
      ((M.canonicalPathMap records).stateSeq n) i
  have hA_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n] A :=
    (M.measurable_instantCoordQVRate_stateSeq_canonicalRecordFiltration
      i n).stronglyMeasurable
  have hY_int : Integrable Y μ := by
    simpa [Y, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ n
  have hAY_int : Integrable (fun records => A records * Y records) μ := by
    simpa [A, Y, μ] using
      M.integrable_instantCoordQVRate_mul_next_holdingTime_guarded x₀ i n
  have hY_cond :
      μ[Y | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => (M.exitRateAt ((M.canonicalPathMap records).stateSeq n))⁻¹ := by
    have h :=
      M.condExp_next_holdingTime_eq_inv_exitRate x₀ n
    dsimp [μ, Y]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa using h
  have hpull :
      μ[(fun records => A records * Y records) | M.canonicalRecordFiltration n]
        =ᵐ[μ]
      fun records => A records * (μ[Y | M.canonicalRecordFiltration n]) records := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      hA_sm hAY_int hY_int
  have hcond_prod :
      μ[(fun records => A records * Y records) | M.canonicalRecordFiltration n]
        =ᵐ[μ] B := by
    filter_upwards [hpull, hY_cond] with records hpull_records hY_records
    rw [hpull_records, hY_records]
    dsimp [A, B]
    by_cases hzero : M.exitRateAt ((M.canonicalPathMap records).stateSeq n) = 0
    · simp [guardedInstantCoordQVRateDivExit, hzero]
    · simp [guardedInstantCoordQVRateDivExit, hzero, div_eq_mul_inv]
  calc
    ∫ records, A records * Y records ∂μ
        = ∫ records,
            (μ[(fun records => A records * Y records) |
              M.canonicalRecordFiltration n]) records ∂μ := by
            exact (integral_condExp
              (μ := μ)
              (m := M.canonicalRecordFiltration n)
              (f := fun records => A records * Y records)
              (M.canonicalRecordFiltration.le n)).symm
    _ = ∫ records, B records ∂μ := by
          exact integral_congr_ae hcond_prod
    _ = ∫ records,
        M.guardedInstantCoordQVRateDivExit
          ((M.canonicalPathMap records).stateSeq n) i
        ∂M.canonicalRecordMeasure x₀ := by
          simp [B, μ]

/-- Deterministic finite-sum bridge from clock holding times to guarded embedded
coordinate-QV. -/
theorem integral_sum_instantCoordQVRate_mul_next_holdingTime_eq_integral_frozenQvComp
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (∑ k ∈ Finset.range n,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (records (k + 1)).1)
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  have hleft_int : ∀ k ∈ Finset.range n,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (records (k + 1)).1)
        μ := by
    intro k _hk
    simpa [μ] using
      M.integrable_instantCoordQVRate_mul_next_holdingTime_guarded x₀ i k
  have hguard_int : ∀ k ∈ Finset.range n,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.guardedInstantCoordQVRateDivExit
            ((M.canonicalPathMap records).stateSeq k) i)
        μ := by
    intro k _hk
    have hsucc :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (k + 1))
          μ := by
      simpa [μ] using M.frozenScaledCoordQVCompensator_integrable x₀ i (k + 1)
    have hprev :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i k)
          μ := by
      simpa [μ] using M.frozenScaledCoordQVCompensator_integrable x₀ i k
    refine (hsucc.sub hprev).congr ?_
    refine ae_of_all _ fun records => ?_
    have hsucc_eq :=
      M.frozenScaledCoordQVCompensator_succ (M.canonicalPathMap records) i k
    simp only [Pi.sub_apply]
    rw [hsucc_eq]
    ring
  calc
    ∫ records,
        (∑ k ∈ Finset.range n,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (records (k + 1)).1)
        ∂M.canonicalRecordMeasure x₀
        = ∑ k ∈ Finset.range n,
            ∫ records,
              M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
                (records (k + 1)).1
              ∂μ := by
            rw [integral_finset_sum]
            intro k hk
            exact hleft_int k hk
    _ = ∑ k ∈ Finset.range n,
          ∫ records,
            M.guardedInstantCoordQVRateDivExit
              ((M.canonicalPathMap records).stateSeq k) i
            ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          simpa [μ] using
            M.integral_instantCoordQVRate_mul_next_holdingTime_eq_integral_guardedDivExit
              x₀ i k
    _ = ∫ records,
        (∑ k ∈ Finset.range n,
          M.guardedInstantCoordQVRateDivExit
            ((M.canonicalPathMap records).stateSeq k) i)
        ∂μ := by
          rw [integral_finset_sum]
          intro k hk
          exact hguard_int k hk
    _ = ∫ records,
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
          simp [frozenScaledCoordQVCompensator, μ]

/-- Same finite-sum QV bridge, expressed with `CTMCPath.sojournTime`. -/
theorem integral_sum_instantCoordQVRate_mul_sojournTime_eq_integral_frozenQvComp
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (∑ k ∈ Finset.range n,
          M.instantCoordQVRate ((M.canonicalPathMap records).stateSeq k) i *
            (M.canonicalPathMap records).sojournTime k)
        ∂M.canonicalRecordMeasure x₀ =
      ∫ records,
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
    M.integral_sum_instantCoordQVRate_mul_next_holdingTime_eq_integral_frozenQvComp
      x₀ i n

theorem frozenScaledJumpMartingale_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) := by
  convert M.integrable_scaledJumpMartingale_canonicalRecordMeasure x₀ i n using 1
  ext records
  exact M.frozenScaledJumpMartingale_eq_scaledJumpMartingale
    (M.canonicalPathMap records) i n

theorem frozenScaledJumpMartingale_sq_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  convert M.integrable_scaledJumpMartingale_sq_canonicalRecordMeasure x₀ i n using 1
  ext records
  rw [M.frozenScaledJumpMartingale_eq_scaledJumpMartingale
    (M.canonicalPathMap records) i n]

theorem integrable_frozenScaledJumpMartingale_sup_sq_canonicalRecordMeasure
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  convert M.integrable_scaledJumpMartingale_sup_sq_canonicalRecordMeasure x₀ i n using 1
  ext records
  congr 1
  refine Finset.sup'_congr Finset.nonempty_range_add_one rfl ?_
  intro k _hk
  rw [M.frozenScaledJumpMartingale_eq_scaledJumpMartingale
    (M.canonicalPathMap records) i k]

theorem frozenScaledJumpMartingale_condExp_increment_eq_zero_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let nextJump : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedGeneratorDriftDivExit ((M.canonicalPathMap records).stateSeq n) i
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n)
        =ᵐ[μ] fun records => nextJump records - comp records := by
    refine ae_of_all _ fun records => ?_
    simp [nextJump, comp, M.frozenScaledJumpMartingale_succ_sub, canonicalPathMap,
      QMatrix.recordTrajectoryToPath_stateSeq]
  have hnext :
      μ[nextJump | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_apply_eq_guardedGeneratorDriftDivExit_ae
        x₀ n i
    dsimp [μ, nextJump, comp]
    simpa [Pi.sub_apply] using h
  have hcomp_meas :
      Measurable[M.canonicalRecordFiltration n] comp := by
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) =>
        M.guardedGeneratorDriftDivExit x i)).comp
          (M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n)
  have hcomp_int : Integrable comp μ := by
    dsimp [comp, μ]
    convert M.integrable_generatorDrift_div_exitRate_stateSeq_canonicalRecordMeasure
      x₀ i n using 1
    ext records
    by_cases hzero : M.exitRateAt ((M.canonicalPathMap records).stateSeq n) = 0
    · simp [guardedGeneratorDriftDivExit, hzero]
    · simp [guardedGeneratorDriftDivExit, hzero]
  have hcomp :
      μ[comp | M.canonicalRecordFiltration n] = comp := by
    exact MeasureTheory.condExp_of_stronglyMeasurable
      (M.canonicalRecordFiltration.le n)
      hcomp_meas.stronglyMeasurable
      hcomp_int
  have hsub :
      μ[nextJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ]
        μ[nextJump | M.canonicalRecordFiltration n] -
          μ[comp | M.canonicalRecordFiltration n] :=
    MeasureTheory.condExp_sub
      (M.integrable_next_scaledState_sub_apply x₀ n i)
      hcomp_int
      (M.canonicalRecordFiltration n)
  refine (MeasureTheory.condExp_congr_ae hinc).trans ?_
  change μ[nextJump - comp | M.canonicalRecordFiltration n] =ᵐ[μ] 0
  rw [hcomp] at hsub
  filter_upwards [hsub, hnext] with records hsub_eq hnext_eq
  rw [hsub_eq]
  simp [Pi.sub_apply, hnext_eq]

theorem frozenScaledJumpMartingale_martingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Martingale
      (fun n records =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  martingale_of_condExp_sub_eq_zero_nat
    (M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i)
    (M.frozenScaledJumpMartingale_integrable x₀ i)
    (fun n =>
      M.frozenScaledJumpMartingale_condExp_increment_eq_zero_ae x₀ n i)

theorem frozenScaledJumpMartingale_norm_submartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Submartingale
      (fun n records =>
        ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n
  have hmart : Martingale Z M.canonicalRecordFiltration μ := by
    simpa [Z, μ] using M.frozenScaledJumpMartingale_martingale x₀ i
  refine submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i n).norm
  · intro n
    simpa [Z] using
      (M.frozenScaledJumpMartingale_integrable x₀ i n).norm
  · intro n
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ‖(μ[Z (n + 1) | M.canonicalRecordFiltration n]) records‖)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => ‖Z (n + 1) records‖)
          | M.canonicalRecordFiltration n] :=
      norm_condExp_le
    have hcond : μ[Z (n + 1) | M.canonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

theorem frozenScaledJumpMartingale_norm_maximal_ineq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (ε : NNReal) (n : ℕ) :
    ((ε : ENNReal) * (M.canonicalRecordMeasure x₀)
        {records | (ε : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)})
      ≤ ENNReal.ofReal
        (∫ records in
          {records | (ε : ℝ) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)},
          ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖
          ∂M.canonicalRecordMeasure x₀) := by
  exact MeasureTheory.maximal_ineq
    (M.frozenScaledJumpMartingale_norm_submartingale x₀ i)
    (by
      intro n records
      exact norm_nonneg _)
    (ε := ε) n

theorem integral_sup_frozenScaledJumpMartingale_norm_sq_le_two_mul_sup_mul_norm
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      2 * ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖) *
        ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖
  have hX_meas : Measurable X := by
    exact Finset.measurable_range_sup'' (fun k _hk =>
      (((M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i k).mono
        (M.canonicalRecordFiltration.le k)).measurable.norm))
  have hY_meas : Measurable Y :=
    (((M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i n).mono
      (M.canonicalRecordFiltration.le n)).measurable.norm)
  have hX_nonneg : 0 ≤ᵐ[μ] X := by
    refine ae_of_all _ fun records => ?_
    dsimp [X]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hY_nonneg : 0 ≤ᵐ[μ] Y :=
    ae_of_all _ fun records => norm_nonneg _
  have hXsq_int : Integrable (fun records => X records ^ 2) μ := by
    simpa [X, μ] using
      M.integrable_frozenScaledJumpMartingale_sup_sq_canonicalRecordMeasure x₀ i n
  have hY_int : Integrable Y μ := by
    simpa [Y, μ] using
      (M.frozenScaledJumpMartingale_integrable x₀ i n).norm
  have hX_memLp_nat : MemLp X 2 μ := by
    exact (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2 hXsq_int
  have hY_sq_int : Integrable (fun records => Y records ^ 2) μ := by
    have hterminal :=
      M.frozenScaledJumpMartingale_sq_integrable x₀ i n
    refine hterminal.congr ?_
    refine ae_of_all _ fun records => ?_
    dsimp [Y]
    exact (sq_abs (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n)).symm
  have hY_memLp_nat : MemLp Y 2 μ := by
    exact (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_sq_int
  have hXY_int : Integrable (fun records => X records * Y records) μ := by
    exact MemLp.integrable_mul hX_memLp_nat hY_memLp_nat
  have hMax : ∀ ε : NNReal,
      ((ε : ENNReal) * μ {records | (ε : ℝ) ≤ X records}) ≤
        ENNReal.ofReal (∫ records in {records | (ε : ℝ) ≤ X records},
          Y records ∂μ) := by
    intro ε
    simpa [X, Y, μ] using
      M.frozenScaledJumpMartingale_norm_maximal_ineq x₀ i ε n
  simpa [X, Y, μ] using
    integral_sq_le_two_integral_mul_of_maximal_ineq
      hX_meas hY_meas hX_nonneg hY_nonneg hXsq_int hY_int hXY_int hMax

/-! ## Doob/QV endpoint placeholders -/

theorem condExp_frozenScaledJumpMartingale_increment_sq_le_qvComp_increment_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalRecordMeasure x₀)[
        fun records : M.canonicalRecordΩ =>
          (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        | M.canonicalRecordFiltration n] records ≤
        M.guardedInstantCoordQVRateDivExit
          ((M.canonicalPathMap records).stateSeq n) i := by
  let μ := M.canonicalRecordMeasure x₀
  let nextJump : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedGeneratorDriftDivExit ((M.canonicalPathMap records).stateSeq n) i
  have hX_memLp : MemLp nextJump 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (M.measurable_next_scaledState_sub_apply n i).aestronglyMeasurable).2
      (by simpa [nextJump, μ] using M.integrable_next_scaledState_sub_apply_sq x₀ n i)
  have hnext_condExp :
      μ[nextJump | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_apply_eq_guardedGeneratorDriftDivExit_ae
        x₀ n i
    dsimp [μ, nextJump, comp]
    simpa [Pi.sub_apply] using h
  have hinc_eq :
      (fun records : M.canonicalRecordΩ =>
        (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
        =ᵐ[μ]
      fun records =>
        (nextJump records -
          (μ[nextJump | M.canonicalRecordFiltration n]) records) ^ 2 := by
    filter_upwards [hnext_condExp] with records hnext_records
    have hstep :
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n =
          nextJump records - comp records := by
      simp [nextJump, comp, M.frozenScaledJumpMartingale_succ_sub, canonicalPathMap,
        QMatrix.recordTrajectoryToPath_stateSeq]
    rw [hstep, ← hnext_records]
  have hvar_le :
      ProbabilityTheory.condVar (M.canonicalRecordFiltration n) nextJump μ
        ≤ᵐ[μ]
      μ[(nextJump ^ 2) | M.canonicalRecordFiltration n] :=
    ProbabilityTheory.condVar_ae_le_condExp_sq
      (hm := M.canonicalRecordFiltration.le n) (X := nextJump) (μ := μ) hX_memLp
  have hcondExp_sq :
      μ[(nextJump ^ 2) | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => M.guardedInstantCoordQVRateDivExit
          ((M.canonicalPathMap records).stateSeq n) i := by
    have h :=
      M.condExp_next_scaledState_sub_apply_sq_eq_guardedInstantCoordQVRateDivExit_ae
        x₀ n i
    dsimp [μ, nextJump]
    filter_upwards [h] with records hrec
    simpa [Pi.pow_apply] using hrec
  have hcondExp_inc_le_condExp_sq :
      μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
        | M.canonicalRecordFiltration n] ≤ᵐ[μ]
      μ[(nextJump ^ 2) | M.canonicalRecordFiltration n] := by
    have hcongr :
        μ[(fun records : M.canonicalRecordΩ =>
            (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) -
              M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
          | M.canonicalRecordFiltration n]
          =ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ =>
            (nextJump records -
              (μ[nextJump | M.canonicalRecordFiltration n]) records) ^ 2)
          | M.canonicalRecordFiltration n] :=
      condExp_congr_ae hinc_eq
    filter_upwards [hcongr, hvar_le] with records hcongr_rec hvar_rec
    exact le_trans (le_of_eq hcongr_rec) hvar_rec
  filter_upwards [hcondExp_inc_le_condExp_sq, hcondExp_sq] with records hle hsq
  exact le_trans hle (le_of_eq hsq)

theorem shiftedFrozenMartingale_sq_minus_qvComp_supermartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Supermartingale
      (fun n records =>
        (M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records) ^ 2 -
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1))
      M.shiftedCanonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let B : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    (M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records) ^ 2 -
      M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)
  have hqv_int_fixed : ∀ k : ℕ,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i k)
        μ := by
    intro k
    dsimp [μ]
    convert M.integrable_scaledCoordQVCompensator_canonicalRecordMeasure x₀ i k using 1
    ext records
    simp only [frozenScaledCoordQVCompensator, scaledCoordQVCompensator]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hzero : M.exitRateAt ((M.canonicalPathMap records).stateSeq j) = 0
    · simp [guardedInstantCoordQVRateDivExit, hzero]
    · simp [guardedInstantCoordQVRateDivExit, hzero]
  have hmart : Martingale
      (fun n records => M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records)
      M.shiftedCanonicalRecordFiltration μ := by
    simpa [μ] using M.shiftedFrozenScaledJumpMartingale_martingale x₀ i
  refine supermartingale_nat ?hadp ?hint ?hstep
  · intro n
    exact (M.shiftedFrozenScaledJumpMartingale_stronglyAdapted i n).pow 2 |>.sub
      (M.measurable_frozenScaledCoordQVCompensator_canonicalRecordFiltration
        i (n + 1)).stronglyMeasurable
  · intro n
    exact (M.shiftedFrozenScaledJumpMartingale_sq_integrable x₀ i n).sub
      (hqv_int_fixed (n + 1))
  · intro n
    simp only [shiftedFrozenScaledJumpMartingale]
    have hqv_meas :
        StronglyMeasurable[M.shiftedCanonicalRecordFiltration n]
          (fun records : M.canonicalRecordΩ =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1)) := by
      have hdecomp : ∀ records : M.canonicalRecordΩ,
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1) =
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1) +
              M.guardedInstantCoordQVRateDivExit
                ((M.canonicalPathMap records).stateSeq (n + 1)) i :=
        fun records => M.frozenScaledCoordQVCompensator_succ
          (M.canonicalPathMap records) i (n + 1)
      simp_rw [hdecomp]
      exact
        (M.measurable_frozenScaledCoordQVCompensator_canonicalRecordFiltration
          i (n + 1)).stronglyMeasurable.add
        (by
          have hst := M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le
            (show n + 1 ≤ n + 1 from le_refl _)
          have hg : Measurable (fun x : Fin d → Fin (M.N + 1) =>
              M.guardedInstantCoordQVRateDivExit x i) := Measurable.of_discrete
          exact (hg.comp hst).stronglyMeasurable)
    have hqv_int :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 2))
          μ :=
      hqv_int_fixed (n + 2)
    have hmsq_int :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2)) ^ 2)
          μ := by
      simpa [shiftedFrozenScaledJumpMartingale, μ] using
        M.shiftedFrozenScaledJumpMartingale_sq_integrable x₀ i (n + 1)
    have hM_memLp : MemLp
        (fun records : M.canonicalRecordΩ =>
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2)) 2 μ := by
      exact (memLp_two_iff_integrable_sq
        ((M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i (n + 2)).mono
          (M.canonicalRecordFiltration.le (n + 2))).aestronglyMeasurable).2
        (by simpa [μ] using hmsq_int)
    have hcondVar_eq := ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp
      (m := M.shiftedCanonicalRecordFiltration n)
      (M.shiftedCanonicalRecordFiltration.le n) hM_memLp
    have hcondExp_M := hmart.condExp_ae_eq (show n ≤ n + 1 by omega)
    have hvar_le :=
      M.condExp_frozenScaledJumpMartingale_increment_sq_le_qvComp_increment_ae
        x₀ (n + 1) i
    have hcenter_sq :
        (fun records : M.canonicalRecordΩ =>
          (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2) -
            μ[(fun r => M.frozenScaledJumpMartingale (M.canonicalPathMap r) i (n + 2))
              | M.shiftedCanonicalRecordFiltration n] records) ^ 2)
          =ᵐ[μ]
        fun records =>
          (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2) -
            M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 := by
      filter_upwards [hcondExp_M] with records hM
      simp only [shiftedFrozenScaledJumpMartingale] at hM
      congr 1; linarith
    have hcondVar_eq_inc :
        ProbabilityTheory.condVar (M.shiftedCanonicalRecordFiltration n)
          (fun records => M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2)) μ
          =ᵐ[μ]
        μ[(fun records =>
            (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2) -
              M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2)
          | M.shiftedCanonicalRecordFiltration n] := by
      simp only [ProbabilityTheory.condVar]
      exact condExp_congr_ae hcenter_sq
    have hcondExp_sub := condExp_sub hmsq_int hqv_int (M.shiftedCanonicalRecordFiltration n)
    have hqv_pull := condExp_of_stronglyMeasurable
      (M.shiftedCanonicalRecordFiltration.le n) hqv_meas hqv_int
    filter_upwards [hcondExp_sub, hcondVar_eq, hcondExp_M, hvar_le,
      hcondVar_eq_inc]
      with records hsub hvar hcond hincr hcvar_inc
    have hqv_pt := congr_fun hqv_pull records
    simp only [Pi.sub_apply] at hsub
    simp only [shiftedFrozenScaledJumpMartingale] at hcond
    have key : μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1 + 1)) ^ 2 -
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1))
        | M.shiftedCanonicalRecordFiltration n] records =
      μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1 + 1)) ^ 2)
        | M.shiftedCanonicalRecordFiltration n] records -
      μ[(fun records : M.canonicalRecordΩ =>
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1))
        | M.shiftedCanonicalRecordFiltration n] records := hsub
    rw [key, congr_fun hqv_pull records]
    have hsucc := M.frozenScaledCoordQVCompensator_succ (M.canonicalPathMap records) i (n + 1)
    have h1 : μ[(fun r : M.canonicalRecordΩ =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap r) i (n + 1 + 1))
      | M.shiftedCanonicalRecordFiltration n] records =
      M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) := hcond
    have h2 : μ[(fun r : M.canonicalRecordΩ =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap r) i (n + 1 + 1))
      | M.shiftedCanonicalRecordFiltration n] records ^ 2 =
      (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 := by
      rw [h1]
    have hbridge : μ[(fun r : M.canonicalRecordΩ =>
          (M.frozenScaledJumpMartingale (M.canonicalPathMap r) i (n + 1 + 1)) ^ 2)
        | M.shiftedCanonicalRecordFiltration n] records =
      μ[(fun records : M.canonicalRecordΩ =>
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2)) ^ 2
        | M.shiftedCanonicalRecordFiltration n] records := rfl
    rw [hbridge]
    simp only [Pi.sub_apply, Pi.pow_apply] at hvar hcvar_inc
    have h_elim := hvar.symm.trans hcvar_inc
    have h_combined :
      μ[(fun records : M.canonicalRecordΩ =>
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2)) ^ 2
        | M.shiftedCanonicalRecordFiltration n] records ≤
      (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 +
      (M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1) -
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)) := by
      have h1_alt : μ[(fun r : M.canonicalRecordΩ =>
          M.frozenScaledJumpMartingale (M.canonicalPathMap r) i (n + 2))
        | M.shiftedCanonicalRecordFiltration n] records =
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) := h1
      calc μ[(fun r : M.canonicalRecordΩ =>
              M.frozenScaledJumpMartingale (M.canonicalPathMap r) i (n + 2)) ^ 2
            | M.shiftedCanonicalRecordFiltration n] records
          = μ[(fun r : M.canonicalRecordΩ =>
              M.frozenScaledJumpMartingale (M.canonicalPathMap r) i (n + 2))
            | M.shiftedCanonicalRecordFiltration n] records ^ 2 +
            μ[(fun records : M.canonicalRecordΩ =>
              (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2) -
                M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2)
            | M.shiftedCanonicalRecordFiltration n] records := by linarith [h_elim]
        _ = (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 +
            μ[(fun records : M.canonicalRecordΩ =>
              (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 2) -
                M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2)
            | M.shiftedCanonicalRecordFiltration n] records := by rw [h1_alt]
        _ ≤ (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 +
            (M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1) -
              M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)) := by
            gcongr
            exact le_trans hincr (le_of_eq (by linarith [hsucc]))
    linarith [h_combined]

theorem integral_frozenScaledJumpMartingale_sq_one_le_integral_frozenScaledCoordQVCompensator_one
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    ∫ records,
        (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i 1) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let inc : M.canonicalRecordΩ → ℝ := fun records =>
    M.frozenScaledJumpMartingale (M.canonicalPathMap records) i 1 -
      M.frozenScaledJumpMartingale (M.canonicalPathMap records) i 0
  have hinc_sq_int : Integrable (fun records => inc records ^ 2) μ := by
    refine (M.frozenScaledJumpMartingale_sq_integrable x₀ i 1).congr ?_
    refine ae_of_all _ fun records => ?_
    simp [inc]
  have hce_le :
      μ[(fun records : M.canonicalRecordΩ => inc records ^ 2)
        | M.canonicalRecordFiltration 0] ≤ᵐ[μ]
      fun records =>
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1 := by
    have hraw :=
      M.condExp_frozenScaledJumpMartingale_increment_sq_le_qvComp_increment_ae
        x₀ 0 i
    filter_upwards [hraw] with records hle
    have hqv1 :
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1 =
          M.guardedInstantCoordQVRateDivExit
            ((M.canonicalPathMap records).stateSeq 0) i := by
      simpa using
        M.frozenScaledCoordQVCompensator_succ
          (M.canonicalPathMap records) i 0
    exact hle.trans (le_of_eq hqv1.symm)
  have hcond_int :
      ∫ records,
          (μ[(fun records : M.canonicalRecordΩ => inc records ^ 2)
            | M.canonicalRecordFiltration 0]) records ∂μ =
        ∫ records, inc records ^ 2 ∂μ := by
    exact integral_condExp
      (μ := μ)
      (m := M.canonicalRecordFiltration 0)
      (f := fun records : M.canonicalRecordΩ => inc records ^ 2)
      (M.canonicalRecordFiltration.le 0)
  have hmono :
      ∫ records,
          (μ[(fun records : M.canonicalRecordΩ => inc records ^ 2)
            | M.canonicalRecordFiltration 0]) records ∂μ ≤
        ∫ records,
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1 ∂μ :=
    integral_mono_ae integrable_condExp
      (M.frozenScaledCoordQVCompensator_integrable x₀ i 1) hce_le
  calc
    ∫ records,
        (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i 1) ^ 2
        ∂M.canonicalRecordMeasure x₀
        = ∫ records, inc records ^ 2 ∂μ := by
            apply integral_congr_ae
            refine ae_of_all _ fun records => ?_
            simp [inc]
    _ = ∫ records,
          (μ[(fun records : M.canonicalRecordΩ => inc records ^ 2)
            | M.canonicalRecordFiltration 0]) records ∂μ := hcond_int.symm
    _ ≤ ∫ records,
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1 ∂μ := hmono

theorem integral_shiftedFrozenMartingale_sq_stoppedValue_le_integral_frozenQvComp_stoppedValue
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) (N : ℕ) :
    let τ : M.canonicalRecordΩ → WithTop ℕ := fun records =>
      min ((M.canonicalPathMap records).jumpCountTop T) (N : WithTop ℕ)
    ∫ records,
        stoppedValue
          (fun n records =>
            (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i
              (n + 1)) ^ 2)
          τ records
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i
              (n + 1))
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
  intro τ
  let μ := M.canonicalRecordMeasure x₀
  let B : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 -
      M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)
  have hsupermart :=
    M.shiftedFrozenMartingale_sq_minus_qvComp_supermartingale x₀ i
  have hsubmart : Submartingale (-B) M.shiftedCanonicalRecordFiltration μ := by
    simpa [B, μ, shiftedFrozenScaledJumpMartingale] using hsupermart.neg
  have hτ_stop : IsStoppingTime M.shiftedCanonicalRecordFiltration τ := by
    simpa [τ] using (M.isStoppingTime_canonicalPathMap_jumpCountTop_shifted T).min_const N
  have h0_stop : IsStoppingTime M.shiftedCanonicalRecordFiltration
      (fun _ : M.canonicalRecordΩ => (0 : WithTop ℕ)) := isStoppingTime_const _ _
  have h0_le : (fun _ : M.canonicalRecordΩ => (0 : WithTop ℕ)) ≤ τ := fun _ => bot_le
  have hopt := hsubmart.expected_stoppedValue_mono h0_stop hτ_stop h0_le
    (fun ω => min_le_right _ _)
  have hstop_neg : ∀ (σ : M.canonicalRecordΩ → WithTop ℕ),
      stoppedValue (-B) σ = fun ω => -(stoppedValue B σ ω) := by
    intro σ
    ext ω
    simp [stoppedValue, Pi.neg_apply]
  simp only [hstop_neg, integral_neg] at hopt
  have hopt' : ∫ ω, stoppedValue B τ ω ∂μ ≤
      ∫ ω, stoppedValue B (fun _ => (0 : WithTop ℕ)) ω ∂μ := by
    exact neg_le_neg_iff.1 hopt
  have hstop0 : stoppedValue B (fun _ => (0 : WithTop ℕ)) = B 0 := by
    ext ω
    simp [stoppedValue]
  rw [hstop0] at hopt'
  have hB0_le : ∫ records, B 0 records ∂μ ≤ 0 := by
    simp only [B]
    have hsplit := integral_sub
      (M.frozenScaledJumpMartingale_sq_integrable x₀ i 1)
      (M.frozenScaledCoordQVCompensator_integrable x₀ i 1)
    have hterm :=
      M.integral_frozenScaledJumpMartingale_sq_one_le_integral_frozenScaledCoordQVCompensator_one
        x₀ i
    linarith
  have hB_le : ∫ records, stoppedValue B τ records ∂μ ≤ 0 :=
    hopt'.trans hB0_le
  let X : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2
  let Q : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)
  have hX_int : Integrable (stoppedValue X τ) μ := by
    exact integrable_stoppedValue ℕ hτ_stop
      (fun n => M.frozenScaledJumpMartingale_sq_integrable x₀ i (n + 1))
      (N := N) (fun ω => min_le_right _ _)
  have hQ_int : Integrable (stoppedValue Q τ) μ := by
    exact integrable_stoppedValue ℕ hτ_stop
      (fun n => M.frozenScaledCoordQVCompensator_integrable x₀ i (n + 1))
      (N := N) (fun ω => min_le_right _ _)
  have hBQ :
      stoppedValue B τ = fun ω => stoppedValue X τ ω - stoppedValue Q τ ω := by
    ext ω
    simp [stoppedValue, B, X, Q]
  have hsplit := integral_sub hX_int hQ_int
  have hB_split :
      ∫ ω, stoppedValue B τ ω ∂μ =
        ∫ ω, stoppedValue X τ ω ∂μ - ∫ ω, stoppedValue Q τ ω ∂μ := by
    rw [hBQ]
    exact hsplit
  dsimp [X, Q, μ] at hB_split ⊢
  linarith

/-- Stopped finite-horizon Doob L2 estimate for the shifted frozen embedded
jump martingale.  The stopping time is the clock-horizon jump count, truncated
at the deterministic index `N`. -/
theorem integral_stopped_shiftedFrozenScaledJumpMartingale_sup_sq_le_frozenQvComp_stoppedValue
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) (N : ℕ) :
    let τ : M.canonicalRecordΩ → WithTop ℕ := fun records =>
      min ((M.canonicalPathMap records).jumpCountTop T) (N : WithTop ℕ)
    ∫ records,
        ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            stoppedProcess
              (fun n records =>
                ‖M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records‖)
              τ k records)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i
              (n + 1))
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
  intro τ
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    ‖M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records‖
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => stoppedProcess Z τ k records)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    stoppedProcess Z τ N records
  let Xfixed : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (N + 2)).sup' (by simp)
      (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
  have hτ_stop : IsStoppingTime M.shiftedCanonicalRecordFiltration τ := by
    simpa [τ] using (M.isStoppingTime_canonicalPathMap_jumpCountTop_shifted T).min_const N
  have hτ_le : ∀ records, τ records ≤ (N : WithTop ℕ) := by
    intro records
    exact min_le_right _ _
  have hsub :=
    (M.shiftedFrozenScaledJumpMartingale_norm_submartingale x₀ i).stoppedProcess hτ_stop
  have hX_meas : Measurable X := by
    dsimp [X]
    refine Finset.measurable_range_sup'' ?_
    intro k _hk
    simpa [Z] using
      ((hsub.stronglyAdapted k).mono (M.shiftedCanonicalRecordFiltration.le k)).measurable
  have hY_meas : Measurable Y := by
    dsimp [Y]
    simpa [Z] using
      ((hsub.stronglyAdapted N).mono (M.shiftedCanonicalRecordFiltration.le N)).measurable
  have hX_nonneg : 0 ≤ᵐ[μ] X := by
    refine ae_of_all _ fun records => ?_
    dsimp [X, Z]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => stoppedProcess
          (fun n records =>
            ‖M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records‖)
          τ k records)
        (Finset.mem_range.mpr (Nat.succ_pos N)))
  have hY_nonneg : 0 ≤ᵐ[μ] Y := by
    refine ae_of_all _ fun records => ?_
    dsimp [Y, Z, stoppedProcess]
    exact abs_nonneg _
  have hX_le_fixed : ∀ records, X records ≤ Xfixed records := by
    intro records
    dsimp [X, Xfixed, Z, stoppedProcess, shiftedFrozenScaledJumpMartingale]
    refine Finset.sup'_le _ _ ?_
    intro k hk
    let m : ℕ := (min (k : WithTop ℕ) (τ records)).untopA
    have hm_le_k : m ≤ k := by
      exact WithTop.untopA_le (min_le_left (k : WithTop ℕ) (τ records))
    have hk_le_N : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hm_mem : m + 1 ∈ Finset.range (N + 2) := by
      exact Finset.mem_range.mpr (by omega)
    exact Finset.le_sup'
      (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
      hm_mem
  have hXfixed_nonneg : ∀ records, 0 ≤ Xfixed records := by
    intro records
    dsimp [Xfixed]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos (N + 1))))
  have hXsq_int : Integrable (fun records => X records ^ 2) μ := by
    have hfixed_int :
        Integrable (fun records => Xfixed records ^ 2) μ := by
      simpa [Xfixed, μ] using
        M.integrable_frozenScaledJumpMartingale_sup_sq_canonicalRecordMeasure
          x₀ i (N + 1)
    refine hfixed_int.mono' (hX_meas.pow_const 2).aestronglyMeasurable ?_
    refine ae_of_all _ fun records => ?_
    have hX_nonneg_record : 0 ≤ X records := by
      dsimp [X, Z]
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (fun k => stoppedProcess
            (fun n records =>
              ‖M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records‖)
            τ k records)
          (Finset.mem_range.mpr (Nat.succ_pos N)))
    have hXfixed_nonneg_record : 0 ≤ Xfixed records := hXfixed_nonneg records
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq'
      ((neg_nonpos.mpr hXfixed_nonneg_record).trans hX_nonneg_record)
      (hX_le_fixed records)
  have hY_int : Integrable Y μ := by
    simpa [Y, Z, μ] using hsub.integrable N
  have hY_sq_int : Integrable (fun records => Y records ^ 2) μ := by
    refine hXsq_int.mono' (hY_meas.pow_const 2).aestronglyMeasurable ?_
    refine ae_of_all _ fun records => ?_
    have hY_le_X : Y records ≤ X records := by
      dsimp [X, Y]
      exact Finset.le_sup'
        (fun k => stoppedProcess Z τ k records)
        (Finset.mem_range.mpr (Nat.lt_succ_self N))
    have hY_nonneg_record : 0 ≤ Y records := by
      dsimp [Y, Z, stoppedProcess]
      exact abs_nonneg _
    have hX_nonneg_record : 0 ≤ X records :=
      hY_nonneg_record.trans hY_le_X
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq'
      ((neg_nonpos.mpr hX_nonneg_record).trans hY_nonneg_record)
      hY_le_X
  have hX_memLp_nat : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2 hXsq_int
  have hY_memLp_nat : MemLp Y 2 μ :=
    (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_sq_int
  have hXY_int : Integrable (fun records => X records * Y records) μ :=
    MemLp.integrable_mul hX_memLp_nat hY_memLp_nat
  have hMax : ∀ ε : NNReal,
      ((ε : ENNReal) * μ {records | (ε : ℝ) ≤ X records}) ≤
        ENNReal.ofReal (∫ records in {records | (ε : ℝ) ≤ X records},
          Y records ∂μ) := by
    intro ε
    simpa [X, Y, Z, μ] using
      MeasureTheory.maximal_ineq hsub
        (by
          intro n records
          dsimp [Z, stoppedProcess]
          exact abs_nonneg _)
        (ε := ε) N
  have hLayer :
      ∫ records, X records ^ 2 ∂μ ≤
        2 * ∫ records, X records * Y records ∂μ := by
    exact integral_sq_le_two_integral_mul_of_maximal_ineq
      hX_meas hY_meas hX_nonneg hY_nonneg hXsq_int hY_int hXY_int hMax
  let A : ℝ := ∫ records, X records ^ 2 ∂μ
  let B : ℝ := ∫ records, Y records ^ 2 ∂μ
  let C : ℝ := ∫ records, X records * Y records ∂μ
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun records => sq_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun records => sq_nonneg _
  have hCauchy : C ≤ A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
    have hX_memLp : MemLp X (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hX_memLp_nat
    have hY_memLp : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hY_memLp_nat
    have hholder :=
      integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := μ) Real.HolderConjugate.two_two
        hX_nonneg hY_nonneg hX_memLp hY_memLp
    simpa [A, B, C] using hholder
  have hA_le_fourB : A ≤ 4 * B := by
    have hA_le_sqrt : A ≤ 2 * (Real.sqrt A * Real.sqrt B) := by
      have hA_le : A ≤ 2 * (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) := by
        exact hLayer.trans (mul_le_mul_of_nonneg_left hCauchy (by norm_num))
      simpa [Real.sqrt_eq_rpow] using hA_le
    have hsq_nonneg : 0 ≤ (Real.sqrt A - 2 * Real.sqrt B) ^ 2 :=
      sq_nonneg _
    have hsqrtA_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA_nonneg
    have hsqrtB_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB_nonneg
    nlinarith [hA_le_sqrt, hsq_nonneg, hsqrtA_sq, hsqrtB_sq]
  have hYsq_eq_stopped :
      ∫ records, Y records ^ 2 ∂μ =
        ∫ records,
          stoppedValue
            (fun n records =>
              (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i
                (n + 1)) ^ 2)
            τ records ∂μ := by
    apply integral_congr_ae
    refine ae_of_all _ fun records => ?_
    have hmin : min (N : WithTop ℕ) (τ records) = τ records :=
      min_eq_right (hτ_le records)
    simp [Y, Z, stoppedProcess, stoppedValue, shiftedFrozenScaledJumpMartingale,
      hmin, sq_abs]
  have hterminal :=
    M.integral_shiftedFrozenMartingale_sq_stoppedValue_le_integral_frozenQvComp_stoppedValue
      x₀ i T N
  dsimp [τ] at hterminal
  calc
    ∫ records,
        ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            stoppedProcess
              (fun n records =>
                ‖M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records‖)
              τ k records)) ^ 2
        ∂M.canonicalRecordMeasure x₀
        = A := by rfl
    _ ≤ 4 * B := hA_le_fourB
    _ = 4 * ∫ records,
          stoppedValue
            (fun n records =>
              (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i
                (n + 1)) ^ 2)
            τ records ∂μ := by
              dsimp [B]
              rw [hYsq_eq_stopped]
    _ ≤ 4 * ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i
              (n + 1))
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
          exact mul_le_mul_of_nonneg_left hterminal (by norm_num)

/-- Terminal L2 bound by the expected guarded coordinate QV compensator.  This
is the absorbing-aware analogue of the non-frozen terminal endpoint estimate;
the shift by one in the supermartingale is discharged by optional stopping
against deterministic times. -/
theorem integral_frozenScaledJumpMartingale_sq_le_integral_frozenScaledCoordQVCompensator
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    ∫ records,
        (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  cases n with
  | zero =>
      simp
  | succ n =>
      let μ := M.canonicalRecordMeasure x₀
      let B : ℕ → M.canonicalRecordΩ → ℝ := fun k records =>
        (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (k + 1)) ^ 2 -
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (k + 1)
      have hsupermart :=
        M.shiftedFrozenMartingale_sq_minus_qvComp_supermartingale x₀ i
      have hsubmart : Submartingale (-B) M.shiftedCanonicalRecordFiltration μ := by
        simpa [B, μ, shiftedFrozenScaledJumpMartingale] using hsupermart.neg
      have h0_stop : IsStoppingTime M.shiftedCanonicalRecordFiltration
          (fun _ : M.canonicalRecordΩ => (0 : WithTop ℕ)) := isStoppingTime_const _ _
      have hn_stop : IsStoppingTime M.shiftedCanonicalRecordFiltration
          (fun _ : M.canonicalRecordΩ => (n : WithTop ℕ)) := isStoppingTime_const _ _
      have h0_le :
          (fun _ : M.canonicalRecordΩ => (0 : WithTop ℕ)) ≤
            (fun _ : M.canonicalRecordΩ => (n : WithTop ℕ)) := fun _ => by simp
      have hopt := hsubmart.expected_stoppedValue_mono h0_stop hn_stop h0_le
        (fun _ => le_rfl)
      have hstop_neg : ∀ (σ : M.canonicalRecordΩ → WithTop ℕ),
          stoppedValue (-B) σ = fun ω => -(stoppedValue B σ ω) := by
        intro σ
        ext ω
        simp [stoppedValue, Pi.neg_apply]
      simp only [hstop_neg, integral_neg] at hopt
      have hopt' : ∫ ω, stoppedValue B (fun _ => (n : WithTop ℕ)) ω ∂μ ≤
          ∫ ω, stoppedValue B (fun _ => (0 : WithTop ℕ)) ω ∂μ := by
        exact neg_le_neg_iff.1 hopt
      have hstop0 : stoppedValue B (fun _ => (0 : WithTop ℕ)) = B 0 := by
        exact stoppedValue_const B 0
      have hstopn : stoppedValue B (fun _ => (n : WithTop ℕ)) = B n := by
        exact stoppedValue_const B n
      rw [hstop0, hstopn] at hopt'
      have hB0_le : ∫ records, B 0 records ∂μ ≤ 0 := by
        simp only [B]
        have hsplit := integral_sub
          (M.frozenScaledJumpMartingale_sq_integrable x₀ i 1)
          (M.frozenScaledCoordQVCompensator_integrable x₀ i 1)
        have hterm :=
          M.integral_frozenScaledJumpMartingale_sq_one_le_integral_frozenScaledCoordQVCompensator_one
            x₀ i
        linarith
      have hBn_le : ∫ records, B n records ∂μ ≤ 0 := hopt'.trans hB0_le
      have hsplit := integral_sub
        (M.frozenScaledJumpMartingale_sq_integrable x₀ i (n + 1))
        (M.frozenScaledCoordQVCompensator_integrable x₀ i (n + 1))
      simp only [B] at hBn_le
      linarith

/-- Algebraic landing step for the frozen coordinate Doob L2 estimate after
the layer-cake maximal inequality and Cauchy-Schwarz. -/
theorem integral_frozenScaledJumpMartingale_sup_sq_le_four_terminal_norm_sq_of_layercake
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ)
    (hLayer :
      ∫ records,
          ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
          ∂M.canonicalRecordMeasure x₀ ≤
        2 * ∫ records,
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖) *
          ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖
          ∂M.canonicalRecordMeasure x₀) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ := by
  let A : ℝ :=
    ∫ records,
      ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
      ∂M.canonicalRecordMeasure x₀
  let B : ℝ :=
    ∫ records,
      ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2
      ∂M.canonicalRecordMeasure x₀
  let C : ℝ :=
    ∫ records,
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖) *
      ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖
      ∂M.canonicalRecordMeasure x₀
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun records => sq_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun records => sq_nonneg _
  have hCauchy : C ≤ A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
    let μ := M.canonicalRecordMeasure x₀
    let X : M.canonicalRecordΩ → ℝ := fun records =>
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
    let Y : M.canonicalRecordΩ → ℝ := fun records =>
      ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖
    have hX_meas : Measurable X := by
      exact Finset.measurable_range_sup'' (fun k _hk =>
        (((M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i k).mono
          (M.canonicalRecordFiltration.le k)).measurable.norm))
    have hY_meas : Measurable Y :=
      (((M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i n).mono
        (M.canonicalRecordFiltration.le n)).measurable.norm)
    have hX_nonneg : 0 ≤ᵐ[μ] X := by
      refine ae_of_all _ fun records => ?_
      dsimp [X]
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    have hY_nonneg : 0 ≤ᵐ[μ] Y :=
      ae_of_all _ fun records => norm_nonneg _
    have hX_memLp_nat : MemLp X 2 μ := by
      exact (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2
        (by
          simpa [X, μ] using
            M.integrable_frozenScaledJumpMartingale_sup_sq_canonicalRecordMeasure x₀ i n)
    have hX_memLp : MemLp X (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hX_memLp_nat
    have hY_int : Integrable (fun records => Y records ^ 2) μ := by
      refine (M.frozenScaledJumpMartingale_sq_integrable x₀ i n).congr ?_
      refine ae_of_all _ fun records => ?_
      dsimp [Y]
      exact (sq_abs (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n)).symm
    have hY_memLp_nat : MemLp Y 2 μ := by
      exact (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_int
    have hY_memLp : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hY_memLp_nat
    have hholder :=
      integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := μ) Real.HolderConjugate.two_two
        hX_nonneg hY_nonneg hX_memLp hY_memLp
    simpa [A, B, C, X, Y, μ] using hholder
  have hA_le_sqrt : A ≤ 2 * (Real.sqrt A * Real.sqrt B) := by
    have hA_le : A ≤ 2 * (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) := by
      exact hLayer.trans (mul_le_mul_of_nonneg_left hCauchy (by norm_num))
    simpa [Real.sqrt_eq_rpow] using hA_le
  have hsq_nonneg : 0 ≤ (Real.sqrt A - 2 * Real.sqrt B) ^ 2 :=
    sq_nonneg _
  have hsqrtA_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA_nonneg
  have hsqrtB_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB_nonneg
  change A ≤ 4 * B
  nlinarith [hA_le_sqrt, hsq_nonneg, hsqrtA_sq, hsqrtB_sq]

/-- Direct finite jump-index coordinate Doob/QV estimate for the frozen
embedded martingale. -/
theorem integral_frozenScaledJumpMartingale_sup_sq_le_scaledCoordQV_maximal
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
  have hDoob :=
    M.integral_frozenScaledJumpMartingale_sup_sq_le_four_terminal_norm_sq_of_layercake
      x₀ i n
      (M.integral_sup_frozenScaledJumpMartingale_norm_sq_le_two_mul_sup_mul_norm
        x₀ i n)
  have hterminal_eq :
      ∫ records,
          ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2
          ∂M.canonicalRecordMeasure x₀ =
        ∫ records,
          (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by
    apply integral_congr_ae
    refine ae_of_all _ fun records => ?_
    change |M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n| ^ 2 =
      (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
    exact sq_abs (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n)
  calc
    ∫ records,
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2
        ∂M.canonicalRecordMeasure x₀
        ≤ 4 * ∫ records,
          ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n‖ ^ 2
          ∂M.canonicalRecordMeasure x₀ := hDoob
    _ = 4 * ∫ records,
          (M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n) ^ 2
          ∂M.canonicalRecordMeasure x₀ := by rw [hterminal_eq]
    _ ≤ 4 * ∫ records,
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
        ∂M.canonicalRecordMeasure x₀ := by
          exact mul_le_mul_of_nonneg_left
            (M.integral_frozenScaledJumpMartingale_sq_le_integral_frozenScaledCoordQVCompensator
              x₀ i n)
            (by norm_num)

/-- Actual clock-time compensated coordinate jump martingale at frozen jump
indices.  The compensator uses the realized sojourn time of `stateSeq k`,
so the `k = 0` term is the initial sojourn length `path.times 0` and
successor terms are differences of consecutive jump times. -/
noncomputable def frozenTimeCompensatedJumpMartingale
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  M.scaledJumpSum path n i -
    ∑ k ∈ Finset.range n,
      M.generatorDrift (path.stateSeq k) i * path.sojournTime k

@[simp]
theorem frozenTimeCompensatedJumpMartingale_zero
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) :
    M.frozenTimeCompensatedJumpMartingale path i 0 = 0 := by
  simp [frozenTimeCompensatedJumpMartingale, scaledJumpSum]

theorem frozenTimeCompensatedJumpMartingale_succ_sub
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenTimeCompensatedJumpMartingale path i (n + 1) -
        M.frozenTimeCompensatedJumpMartingale path i n =
      (M.scaledState (path.stateSeq (n + 1)) -
          M.scaledState (path.stateSeq n)) i -
        M.generatorDrift (path.stateSeq n) i * path.sojournTime n := by
  simp only [frozenTimeCompensatedJumpMartingale, scaledJumpSum,
    Finset.sum_range_succ]
  ring

/-- Direct conditional bracket for the clock-time compensated frozen jump
martingale.  The product jump-hold kernel cancels the cross term exactly, so
the one-step conditional second moment is the guarded coordinate QV increment. -/
theorem condExp_frozenTimeCompensatedJumpMartingale_increment_sq_eq_qvComp_increment_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (M.canonicalRecordMeasure x₀)[
        fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2
        | M.canonicalRecordFiltration n] records =
        M.guardedInstantCoordQVRateDivExit
          ((M.canonicalPathMap records).stateSeq n) i := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
  let H : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i
  let X2 : M.canonicalRecordΩ → ℝ := fun records => X records ^ 2
  let HX : M.canonicalRecordΩ → ℝ := fun records => H records * X records
  let T2 : M.canonicalRecordΩ → ℝ := fun records => (2 * A records) * HX records
  let D : M.canonicalRecordΩ → ℝ := fun records => (A records) ^ 2 * (H records) ^ 2
  let Qv : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedInstantCoordQVRateDivExit
      ((M.canonicalPathMap records).stateSeq n) i
  let G : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedGeneratorDriftDivExit
      ((M.canonicalPathMap records).stateSeq n) i
  let Einv : M.canonicalRecordΩ → ℝ := fun records =>
    (M.exitRateAt ((M.canonicalPathMap records).stateSeq n))⁻¹
  have hA_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n] A := by
    exact (M.measurable_generatorDrift_stateSeq_canonicalRecordFiltration i n).stronglyMeasurable
  have htwoA_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ => 2 * A records) :=
    hA_sm.const_mul 2
  have hA2_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n]
        (fun records : M.canonicalRecordΩ => (A records) ^ 2) := by
    exact ((M.measurable_generatorDrift_stateSeq_canonicalRecordFiltration
      i n).pow measurable_const).stronglyMeasurable
  have hX2_int : Integrable X2 μ := by
    simpa [X2, X, μ] using M.integrable_next_scaledState_sub_apply_sq x₀ n i
  have hH2_int : Integrable (fun records : M.canonicalRecordΩ => (H records) ^ 2) μ := by
    simpa [H, μ] using M.integrable_next_holdingTime_sq_canonicalRecordMeasure_guarded x₀ n
  have hHX_int : Integrable HX μ := by
    simpa [HX, H, X, μ] using
      M.integrable_next_holdingTime_mul_next_scaledState_sub_apply x₀ n i
  have hclock_int :
      Integrable (fun records : M.canonicalRecordΩ => A records * H records) μ := by
    simpa [A, H, μ, canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      M.integrable_generatorDrift_mul_sojournTime_guarded x₀ i n
  have hAHX_int :
      Integrable (fun records : M.canonicalRecordΩ =>
        A records * (H records * X records)) μ := by
    have hmeas : AEStronglyMeasurable
        (fun records : M.canonicalRecordΩ =>
          (A records * H records) * X records) μ :=
      hclock_int.aestronglyMeasurable.mul
        (M.measurable_next_scaledState_sub_apply n i).aestronglyMeasurable
    have hdom : Integrable
        (fun records : M.canonicalRecordΩ => 2 * ‖A records * H records‖) μ :=
      hclock_int.norm.const_mul 2
    refine (hdom.mono' hmeas ?_).congr ?_
    · refine ae_of_all _ fun records => ?_
      have hX_bound : ‖X records‖ ≤ 2 := by
        dsimp [X]
        exact M.scaledState_sub_apply_norm_le_two
          ((M.canonicalPathMap records).stateSeq n) ((records (n + 1)).2) i
      rw [norm_mul]
      calc
        ‖A records * H records‖ * ‖X records‖
            ≤ ‖A records * H records‖ * 2 := by
              exact mul_le_mul_of_nonneg_left hX_bound (norm_nonneg _)
        _ = 2 * ‖A records * H records‖ := by ring
    · refine ae_of_all _ fun records => ?_
      ring
  have hT2_int : Integrable T2 μ := by
    exact (hAHX_int.const_mul 2).congr
      (ae_of_all _ fun records => by
        dsimp [T2, HX]
        ring)
  have hD_int : Integrable D μ := by
    exact (M.integrable_generatorDrift_mul_sojournTime_sq_guarded x₀ i n).congr
      (ae_of_all _ fun records => by
        dsimp [D, A, H]
        simp [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime]
        ring)
  have hX2_cond :
      μ[X2 | M.canonicalRecordFiltration n] =ᵐ[μ] Qv := by
    have h :=
      M.condExp_next_scaledState_sub_apply_sq_eq_guardedInstantCoordQVRateDivExit_ae
        x₀ n i
    dsimp [μ, X2, X, Qv]
    filter_upwards [h] with records hrec
    simpa [Pi.pow_apply] using hrec
  have hHX_cond :
      μ[HX | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => G records * Einv records := by
    have h :=
      M.condExp_next_holdingTime_mul_next_scaledState_sub_apply_eq_guardedGeneratorDriftDivExit_mul_invExit_ae
        x₀ n i
    dsimp [μ, HX, H, X, G, Einv]
    simpa [Pi.sub_apply] using h
  have hT2_pull :
      μ[T2 | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => (2 * A records) *
          (μ[HX | M.canonicalRecordFiltration n]) records := by
    dsimp [T2]
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      htwoA_sm hT2_int hHX_int
  have hT2_cond :
      μ[T2 | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => (2 * A records) * (G records * Einv records) := by
    filter_upwards [hT2_pull, hHX_cond] with records hpull hHXrec
    rw [hpull, hHXrec]
  have hH2_cond :
      μ[(fun records : M.canonicalRecordΩ => (H records) ^ 2)
          | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => 2 * (Einv records) ^ 2 := by
    have h :=
      M.condExp_next_holdingTime_sq_eq_two_div_exitRate_sq x₀ n
    dsimp [μ, H, Einv]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa [one_div] using h
  have hD_pull :
      μ[D | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => (A records) ^ 2 *
          (μ[(fun records : M.canonicalRecordΩ => (H records) ^ 2)
            | M.canonicalRecordFiltration n]) records := by
    dsimp [D]
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      hA2_sm hD_int hH2_int
  have hD_cond :
      μ[D | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => (A records) ^ 2 * (2 * (Einv records) ^ 2) := by
    filter_upwards [hD_pull, hH2_cond] with records hpull hH2rec
    rw [hpull, hH2rec]
  have hlin_sub :
      μ[X2 - T2 | M.canonicalRecordFiltration n] =ᵐ[μ]
        μ[X2 | M.canonicalRecordFiltration n] -
          μ[T2 | M.canonicalRecordFiltration n] :=
    MeasureTheory.condExp_sub hX2_int hT2_int (M.canonicalRecordFiltration n)
  have hlin_add :
      μ[(X2 - T2) + D | M.canonicalRecordFiltration n] =ᵐ[μ]
        μ[X2 - T2 | M.canonicalRecordFiltration n] +
          μ[D | M.canonicalRecordFiltration n] :=
    MeasureTheory.condExp_add (hX2_int.sub hT2_int) hD_int
      (M.canonicalRecordFiltration n)
  have hinc_sq :
      (fun records : M.canonicalRecordΩ =>
        (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
        =ᵐ[μ] (X2 - T2) + D := by
    refine ae_of_all _ fun records => ?_
    simp [X2, T2, D, HX, X, H, A,
      M.frozenTimeCompensatedJumpMartingale_succ_sub, canonicalPathMap,
      QMatrix.recordTrajectoryToPath_stateSeq, QMatrix.recordTrajectoryToPath_sojournTime]
    ring
  refine (MeasureTheory.condExp_congr_ae hinc_sq).trans ?_
  filter_upwards [hlin_add, hlin_sub, hX2_cond, hT2_cond, hD_cond]
    with records hadd hsub hX2 hT2 hD
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hX2, hT2, hD]
  dsimp [Qv, G, Einv, A]
  let x := (M.canonicalPathMap records).stateSeq n
  change
    M.guardedInstantCoordQVRateDivExit x i -
        (2 * M.generatorDrift x i) *
          (M.guardedGeneratorDriftDivExit x i * (M.exitRateAt x)⁻¹) +
        (M.generatorDrift x i) ^ 2 * (2 * (M.exitRateAt x)⁻¹ ^ 2) =
      M.guardedInstantCoordQVRateDivExit x i
  by_cases hzero : M.exitRateAt x = 0
  · simp [guardedGeneratorDriftDivExit, hzero]
  · rw [M.guardedGeneratorDriftDivExit_of_exitRate_ne_zero x i hzero]
    field_simp [hzero]
    ring

/-- Holding-time compensation between the clock-time compensated martingale and
the embedded-chain frozen martingale.  Each summand is guarded at absorbing
states: if the exit rate of `stateSeq k` is zero, its contribution is defined
to be zero instead of dividing by the exit rate. -/
noncomputable def frozenHoldingTimeCompensation
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    if M.exitRateAt (path.stateSeq k) = 0 then 0
    else
      M.generatorDrift (path.stateSeq k) i *
        (1 / M.exitRateAt (path.stateSeq k) - path.sojournTime k)

theorem frozenHoldingTimeCompensation_eq_scaledHoldingTimeDriftResidual
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenHoldingTimeCompensation path i n =
      M.scaledHoldingTimeDriftResidual path i n := by
  simp only [frozenHoldingTimeCompensation, scaledHoldingTimeDriftResidual]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  by_cases hzero : M.exitRateAt (path.stateSeq k) = 0
  · have hdrift : M.generatorDrift (path.stateSeq k) i = 0 := by
      have hle :=
        M.generatorDrift_sq_le_exitRateAt_mul_instantCoordQVRate
          (path.stateSeq k) i
      have hsquare_nonpos : M.generatorDrift (path.stateSeq k) i ^ 2 ≤ 0 := by
        simpa [hzero] using hle
      nlinarith [sq_nonneg (M.generatorDrift (path.stateSeq k) i)]
    simp [hzero, hdrift]
  · simp [hzero, div_eq_mul_inv]

private lemma sq_add_le_two_mul_sq_add (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - y)]

/-- Algebraic identity: the time-compensated jump martingale equals
the embedded-chain martingale plus the holding-time compensation. -/
theorem frozenTimeCompensatedJumpMartingale_eq_add_holdingComp
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (i : Fin d) (n : ℕ) :
    M.frozenTimeCompensatedJumpMartingale path i n =
      M.frozenScaledJumpMartingale path i n +
      M.frozenHoldingTimeCompensation path i n := by
  simp only [frozenTimeCompensatedJumpMartingale, frozenScaledJumpMartingale,
    frozenScaledJumpDriftCompensator, frozenHoldingTimeCompensation]
  have hsum :
      (∑ k ∈ Finset.range n,
          M.generatorDrift (path.stateSeq k) i * path.sojournTime k) =
        (∑ k ∈ Finset.range n,
          M.guardedGeneratorDriftDivExit (path.stateSeq k) i) -
        ∑ k ∈ Finset.range n,
          if M.exitRateAt (path.stateSeq k) = 0 then 0
          else
            M.generatorDrift (path.stateSeq k) i *
              (1 / M.exitRateAt (path.stateSeq k) - path.sojournTime k) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    by_cases hzero : M.exitRateAt (path.stateSeq k) = 0
    · have hdrift : M.generatorDrift (path.stateSeq k) i = 0 := by
        have hle :=
          M.generatorDrift_sq_le_exitRateAt_mul_instantCoordQVRate
            (path.stateSeq k) i
        have hsquare_nonpos : M.generatorDrift (path.stateSeq k) i ^ 2 ≤ 0 := by
          simpa [hzero] using hle
        nlinarith [sq_nonneg (M.generatorDrift (path.stateSeq k) i)]
      simp [guardedGeneratorDriftDivExit, hzero, hdrift]
    · simp [guardedGeneratorDriftDivExit, hzero]
      ring
  rw [hsum]
  ring

/-- On a completed sojourn interval, the frozen readout agrees with the
corresponding state-sequence value. -/
private theorem frozenStateAt_eq_stateSeq_of_mem_sojournInterval
    {S : Type*} (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (n : ℕ) {t : ℝ} (ht : t ∈ path.sojournInterval n) :
    path.frozenStateAt t = path.stateSeq n := by
  have hfuture : ∃ m, t < path.times m := by
    exact ⟨n, by simpa [CTMCPath.sojournInterval, CTMCPath.sojournEnd] using ht.2⟩
  rw [path.frozenStateAt_eq_stateAt_of_lt_times t hfuture]
  exact path.stateAt_eq_stateSeq_of_mem_sojournInterval hstrict n ht

/-- The union of the first `n` completed sojourn intervals is exactly the
half-open clock interval from `0` to the start of sojourn `n`. -/
private theorem biUnion_sojournInterval_range_eq_Ico_sojournStart
    {S : Type*} (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ) :
    (⋃ k ∈ Finset.range n, path.sojournInterval k) =
      Set.Ico (0 : ℝ) (path.sojournStart n) := by
  induction n with
  | zero =>
      ext t
      simp
  | succ n ih =>
      ext t
      constructor
      · intro ht
        simp only [Set.mem_iUnion, exists_prop] at ht
        obtain ⟨k, hk, htk⟩ := ht
        have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rcases Nat.lt_or_eq_of_le hk_le with hk_lt | hk_eq
        · have htU : t ∈ ⋃ k ∈ Finset.range n, path.sojournInterval k := by
            simp only [Set.mem_iUnion, exists_prop]
            exact ⟨k, Finset.mem_range.mpr hk_lt, htk⟩
          have htI : t ∈ Set.Ico (0 : ℝ) (path.sojournStart n) := by
            rw [ih] at htU
            exact htU
          have hstart_le_end : path.sojournStart n ≤ path.sojournEnd n := by
            simpa [CTMCPath.sojournTime, sub_nonneg] using
              path.sojournTime_nonneg hstrict hpos n
          exact ⟨htI.1, by
            have hlt_end : t < path.sojournEnd n :=
              lt_of_lt_of_le htI.2 hstart_le_end
            simpa [CTMCPath.sojournEnd, CTMCPath.sojournStart] using hlt_end⟩
        · subst k
          have hstart_nonneg : 0 ≤ path.sojournStart n :=
            path.sojournStart_nonneg hstrict hpos n
          exact ⟨le_trans hstart_nonneg htk.1, by
            simpa [CTMCPath.sojournInterval, CTMCPath.sojournEnd,
              CTMCPath.sojournStart] using htk.2⟩
      · intro ht
        simp only [Set.mem_iUnion, exists_prop]
        by_cases hlt : t < path.sojournStart n
        · have htI : t ∈ Set.Ico (0 : ℝ) (path.sojournStart n) := ⟨ht.1, hlt⟩
          have htU : t ∈ ⋃ k ∈ Finset.range n, path.sojournInterval k := by
            rw [ih]
            exact htI
          simp only [Set.mem_iUnion, exists_prop] at htU
          obtain ⟨k, hk, htk⟩ := htU
          exact ⟨k, Finset.mem_range.mpr
            (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)), htk⟩
        · have hge : path.sojournStart n ≤ t := le_of_not_gt hlt
          have htk : t ∈ path.sojournInterval n := by
            constructor
            · exact hge
            · simpa [CTMCPath.sojournInterval, CTMCPath.sojournEnd,
                CTMCPath.sojournStart] using ht.2
          exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), htk⟩

/-- On one completed sojourn interval, the frozen density drift is constant. -/
private theorem frozen_setIntegral_drift_sojournInterval
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ) :
    ∫ t in path.sojournInterval n,
        M.rateSpec.drift
          (M.frozenDensityProcess (fun _ : PUnit => path) t PUnit.unit) =
      path.sojournTime n •
        M.rateSpec.drift (M.scaledState (path.stateSeq n)) := by
  have hconst : Set.EqOn
      (fun t => M.rateSpec.drift
        (M.frozenDensityProcess (fun _ : PUnit => path) t PUnit.unit))
      (fun _ : ℝ => M.rateSpec.drift (M.scaledState (path.stateSeq n)))
      (path.sojournInterval n) := by
    intro t ht
    have hstate :
        path.frozenStateAt t = path.stateSeq n :=
      frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict n ht
    have hdensity :
        M.frozenDensityProcess (fun _ : PUnit => path) t PUnit.unit =
          M.scaledState (path.stateSeq n) := by
      ext i
      simp [DensityDepCTMC.frozenDensityProcess, DensityDepCTMC.scaledState,
        hstate]
    change M.rateSpec.drift
        (M.frozenDensityProcess (fun _ : PUnit => path) t PUnit.unit) =
      M.rateSpec.drift (M.scaledState (path.stateSeq n))
    rw [hdensity]
  have hstart_le_end : path.sojournStart n ≤ path.sojournEnd n := by
    simpa [CTMCPath.sojournTime, sub_nonneg] using
      path.sojournTime_nonneg hstrict hpos n
  calc
    ∫ t in path.sojournInterval n,
        M.rateSpec.drift
          (M.frozenDensityProcess (fun _ : PUnit => path) t PUnit.unit)
        = ∫ t in path.sojournInterval n,
            M.rateSpec.drift (M.scaledState (path.stateSeq n)) := by
            exact setIntegral_congr_fun
              (path.measurableSet_sojournInterval n) hconst
    _ = volume.real (path.sojournInterval n) •
          M.rateSpec.drift (M.scaledState (path.stateSeq n)) := by
          rw [setIntegral_const]
    _ = path.sojournTime n •
          M.rateSpec.drift (M.scaledState (path.stateSeq n)) := by
          rw [CTMCPath.sojournInterval, Real.volume_real_Ico_of_le hstart_le_end]
          simp [CTMCPath.sojournTime]

/-- For a path with positive, strictly increasing jump times, the frozen drift
integral up to the clock time after `n` completed sojourns is the sum of the
constant drift values on those sojourns. -/
theorem frozen_setIntegral_drift_eq_sum_sojournTime_mul
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ) :
    ∫ t in Set.Icc (0 : ℝ) (path.sojournStart n),
        M.rateSpec.drift
          (M.frozenDensityProcess (fun _ : PUnit => path) t PUnit.unit) =
      ∑ k ∈ Finset.range n,
        path.sojournTime k •
          M.rateSpec.drift (M.scaledState (path.stateSeq k)) := by
  let U : Set ℝ := ⋃ k ∈ Finset.range n, path.sojournInterval k
  let g : ℝ → Fin d → ℝ :=
    fun t => M.rateSpec.drift
      (M.frozenDensityProcess (fun _ : PUnit => path) t PUnit.unit)
  have hU_eq : U = Set.Ico (0 : ℝ) (path.sojournStart n) := by
    simpa [U] using
      biUnion_sojournInterval_range_eq_Ico_sojournStart path hstrict hpos n
  have hU_ae : U =ᵐ[volume] Set.Icc (0 : ℝ) (path.sojournStart n) := by
    rw [hU_eq]
    exact Ico_ae_eq_Icc' (by simp)
  have hmeas : ∀ k ∈ Finset.range n, MeasurableSet (path.sojournInterval k) :=
    fun k _ => path.measurableSet_sojournInterval k
  have hpair : Set.Pairwise (↑(Finset.range n))
      (fun k l => Disjoint (path.sojournInterval k) (path.sojournInterval l)) := by
    intro k hk l hl hkl
    exact (path.pairwise_disjoint_sojournInterval hstrict) (by simp) (by simp) hkl
  have hint : ∀ k ∈ Finset.range n,
      IntegrableOn g (path.sojournInterval k) volume := by
    intro k _hk
    have hconst : Set.EqOn g
        (fun _ : ℝ => M.rateSpec.drift (M.scaledState (path.stateSeq k)))
        (path.sojournInterval k) := by
      intro t ht
      have hstate :
          path.frozenStateAt t = path.stateSeq k :=
        frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict k ht
      have hdensity :
          M.frozenDensityProcess (fun _ : PUnit => path) t PUnit.unit =
            M.scaledState (path.stateSeq k) := by
        ext i
        simp [DensityDepCTMC.frozenDensityProcess, DensityDepCTMC.scaledState,
          hstate]
      simp only [g]
      change M.rateSpec.drift
          (M.frozenDensityProcess (fun _ : PUnit => path) t PUnit.unit) =
        M.rateSpec.drift (M.scaledState (path.stateSeq k))
      rw [hdensity]
    exact (integrableOn_const measure_Ico_lt_top.ne).congr_fun hconst.symm
      (path.measurableSet_sojournInterval k)
  calc
    ∫ t in Set.Icc (0 : ℝ) (path.sojournStart n), g t
        = ∫ t in U, g t := by
            exact (setIntegral_congr_set hU_ae.symm)
    _ = ∑ k ∈ Finset.range n,
          ∫ t in path.sojournInterval k, g t := by
          exact integral_biUnion_finset (Finset.range n) hmeas hpair hint
    _ = ∑ k ∈ Finset.range n,
          path.sojournTime k •
            M.rateSpec.drift (M.scaledState (path.stateSeq k)) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          exact frozen_setIntegral_drift_sojournInterval M path hstrict hpos k

/-- On one completed sojourn interval, a scalar frozen-state observable is
constant. -/
private theorem frozen_setIntegral_observable_sojournInterval
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (f : (Fin d → Fin (M.N + 1)) → ℝ)
    (n : ℕ) :
    ∫ t in path.sojournInterval n, f (path.frozenStateAt t) =
      path.sojournTime n * f (path.stateSeq n) := by
  have hconst : Set.EqOn
      (fun t => f (path.frozenStateAt t))
      (fun _ : ℝ => f (path.stateSeq n))
      (path.sojournInterval n) := by
    intro t ht
    exact congrArg f
      (frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict n ht)
  have hstart_le_end : path.sojournStart n ≤ path.sojournEnd n := by
    simpa [CTMCPath.sojournTime, sub_nonneg] using
      path.sojournTime_nonneg hstrict hpos n
  calc
    ∫ t in path.sojournInterval n, f (path.frozenStateAt t)
        = ∫ t in path.sojournInterval n, f (path.stateSeq n) := by
            exact setIntegral_congr_fun
              (path.measurableSet_sojournInterval n) hconst
    _ = volume.real (path.sojournInterval n) * f (path.stateSeq n) := by
          rw [setIntegral_const, smul_eq_mul]
    _ = path.sojournTime n * f (path.stateSeq n) := by
          rw [CTMCPath.sojournInterval, Real.volume_real_Ico_of_le hstart_le_end]
          simp [CTMCPath.sojournTime]

/-- For a path with positive, strictly increasing jump times, a scalar
frozen-state observable integrated up to a completed-sojourn boundary is the
sum of its constant sojourn contributions. -/
theorem frozen_setIntegral_observable_eq_sum_sojournTime_mul
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (f : (Fin d → Fin (M.N + 1)) → ℝ)
    (n : ℕ) :
    ∫ t in Set.Icc (0 : ℝ) (path.sojournStart n), f (path.frozenStateAt t) =
      ∑ k ∈ Finset.range n, path.sojournTime k * f (path.stateSeq k) := by
  let U : Set ℝ := ⋃ k ∈ Finset.range n, path.sojournInterval k
  let g : ℝ → ℝ := fun t => f (path.frozenStateAt t)
  have hU_eq : U = Set.Ico (0 : ℝ) (path.sojournStart n) := by
    simpa [U] using
      biUnion_sojournInterval_range_eq_Ico_sojournStart path hstrict hpos n
  have hU_ae : U =ᵐ[volume] Set.Icc (0 : ℝ) (path.sojournStart n) := by
    rw [hU_eq]
    exact Ico_ae_eq_Icc' (by simp)
  have hmeas : ∀ k ∈ Finset.range n, MeasurableSet (path.sojournInterval k) :=
    fun k _ => path.measurableSet_sojournInterval k
  have hpair : Set.Pairwise (↑(Finset.range n))
      (fun k l => Disjoint (path.sojournInterval k) (path.sojournInterval l)) := by
    intro k hk l hl hkl
    exact (path.pairwise_disjoint_sojournInterval hstrict) (by simp) (by simp) hkl
  have hint : ∀ k ∈ Finset.range n,
      IntegrableOn g (path.sojournInterval k) volume := by
    intro k _hk
    have hconst : Set.EqOn g
        (fun _ : ℝ => f (path.stateSeq k))
        (path.sojournInterval k) := by
      intro t ht
      exact congrArg f
        (frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict k ht)
    exact (integrableOn_const measure_Ico_lt_top.ne).congr_fun hconst.symm
      (path.measurableSet_sojournInterval k)
  calc
    ∫ t in Set.Icc (0 : ℝ) (path.sojournStart n), g t
        = ∫ t in U, g t := by
            exact setIntegral_congr_set hU_ae.symm
    _ = ∑ k ∈ Finset.range n, ∫ t in path.sojournInterval k, g t := by
          exact integral_biUnion_finset (Finset.range n) hmeas hpair hint
    _ = ∑ k ∈ Finset.range n, path.sojournTime k * f (path.stateSeq k) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          exact frozen_setIntegral_observable_sojournInterval M path hstrict hpos f k

/-- Frozen vector-QV clock integral up to a completed-sojourn boundary. -/
theorem frozen_setIntegral_instantQVRate_eq_sum_sojournTime_mul
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ) :
    ∫ t in Set.Icc (0 : ℝ) (path.sojournStart n),
        M.instantQVRate (path.frozenStateAt t) =
      ∑ k ∈ Finset.range n,
        path.sojournTime k * M.instantQVRate (path.stateSeq k) := by
  simpa using
    M.frozen_setIntegral_observable_eq_sum_sojournTime_mul
      path hstrict hpos (fun x => M.instantQVRate x) n

/-- Frozen coordinate-QV clock integral up to a completed-sojourn boundary. -/
theorem frozen_setIntegral_instantCoordQVRate_eq_sum_sojournTime_mul
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (i : Fin d) (n : ℕ) :
    ∫ t in Set.Icc (0 : ℝ) (path.sojournStart n),
        M.instantCoordQVRate (path.frozenStateAt t) i =
      ∑ k ∈ Finset.range n,
        path.sojournTime k * M.instantCoordQVRate (path.stateSeq k) i := by
  simpa using
    M.frozen_setIntegral_observable_eq_sum_sojournTime_mul
      path hstrict hpos (fun x => M.instantCoordQVRate x i) n

/-- On the current partial sojourn before a future jump time, the frozen
readout is constant with value `stateSeq (jumpCount T)`. -/
theorem frozenStateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
    {S : Type*} (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    {T t : ℝ} (hfuture : ∃ n, T < path.times n)
    (ht : t ∈ Set.Icc (path.sojournStart (path.jumpCount T)) T) :
    path.frozenStateAt t = path.stateSeq (path.jumpCount T) := by
  have ht_future : ∃ n, t < path.times n := by
    rcases hfuture with ⟨n, hn⟩
    exact ⟨n, lt_of_le_of_lt ht.2 hn⟩
  rw [path.frozenStateAt_eq_stateAt_of_lt_times t ht_future]
  exact path.stateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
    hstrict hfuture ht

/-- Integral over the current partial frozen sojourn ending at `T`. -/
theorem frozen_setIntegral_currentSojourn_observable
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (f : (Fin d → Fin (M.N + 1)) → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n) :
    ∫ t in Set.Icc (path.sojournStart (path.jumpCount T)) T,
        f (path.frozenStateAt t) =
      f (path.stateSeq (path.jumpCount T)) *
        path.currentSojournElapsed T := by
  have hconst : Set.EqOn (fun t => f (path.frozenStateAt t))
      (fun _ : ℝ => f (path.stateSeq (path.jumpCount T)))
      (Set.Icc (path.sojournStart (path.jumpCount T)) T) := by
    intro t ht
    exact congrArg f
      (frozenStateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
        path hstrict hfuture ht)
  have hstart_le : path.sojournStart (path.jumpCount T) ≤ T :=
    path.sojournStart_jumpCount_le_of_exists hT hfuture
  calc
    ∫ t in Set.Icc (path.sojournStart (path.jumpCount T)) T,
        f (path.frozenStateAt t)
        = ∫ t in Set.Icc (path.sojournStart (path.jumpCount T)) T,
            f (path.stateSeq (path.jumpCount T)) := by
            exact setIntegral_congr_fun measurableSet_Icc hconst
    _ = volume.real (Set.Icc (path.sojournStart (path.jumpCount T)) T) *
          f (path.stateSeq (path.jumpCount T)) := by
          rw [setIntegral_const, smul_eq_mul]
    _ = f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T := by
          rw [Real.volume_real_Icc_of_le hstart_le]
          simp [CTMCPath.currentSojournElapsed]
          ring

/-- Completed sojourns plus the current partial frozen sojourn give the
clock integral over `[0,T]`, provided a future jump time exists. -/
theorem frozen_sum_observable_mul_sojournTime_add_currentSojourn_eq_setIntegral
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (f : (Fin d → Fin (M.N + 1)) → ℝ)
    {T : ℝ} (hT : 0 ≤ T) (hfuture : ∃ n, T < path.times n) :
    (∑ k ∈ Finset.range (path.jumpCount T),
      f (path.stateSeq k) * path.sojournTime k) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T =
      ∫ t in Set.Icc (0 : ℝ) T, f (path.frozenStateAt t) := by
  let U : Set ℝ := ⋃ k ∈ Finset.range (path.jumpCount T), path.sojournInterval k
  let C : Set ℝ := Set.Icc (path.sojournStart (path.jumpCount T)) T
  let g : ℝ → ℝ := fun t => f (path.frozenStateAt t)
  have hUC_eq : Set.union U C = Set.Icc (0 : ℝ) T := by
    simpa [U, C] using
      path.completed_union_current_sojourn_eq_Icc hstrict hpos hfuture
  have hU_subset : U ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    have htUC : t ∈ Set.union U C := Or.inl ht
    simpa [hUC_eq] using htUC
  have hC_subset : C ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    have htUC : t ∈ Set.union U C := Or.inr ht
    simpa [hUC_eq] using htUC
  have hU_int : IntegrableOn g U volume := by
    have hmeas : ∀ k ∈ Finset.range (path.jumpCount T),
        MeasurableSet (path.sojournInterval k) :=
      fun k _ => path.measurableSet_sojournInterval k
    have hpair : Set.Pairwise (↑(Finset.range (path.jumpCount T)))
        (fun k l => Disjoint (path.sojournInterval k) (path.sojournInterval l)) := by
      intro k hk l hl hkl
      exact (path.pairwise_disjoint_sojournInterval hstrict) (by simp) (by simp) hkl
    have hint : ∀ k ∈ Finset.range (path.jumpCount T),
        IntegrableOn g (path.sojournInterval k) volume := by
      intro k _hk
      have hconst : Set.EqOn g
          (fun _ : ℝ => f (path.stateSeq k))
          (path.sojournInterval k) := by
        intro t ht
        exact congrArg f
          (frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict k ht)
      exact (integrableOn_const measure_Ico_lt_top.ne).congr_fun hconst.symm
        (path.measurableSet_sojournInterval k)
    rw [show U = ⋃ k ∈ Finset.range (path.jumpCount T), path.sojournInterval k by rfl]
    exact integrableOn_finset_iUnion.2 hint
  have hC_int : IntegrableOn g C volume := by
    have hconst : Set.EqOn g
        (fun _ : ℝ => f (path.stateSeq (path.jumpCount T))) C := by
      intro t ht
      exact congrArg f
        (frozenStateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
          path hstrict hfuture (by simpa [C] using ht))
    exact (integrableOn_const measure_Icc_lt_top.ne).congr_fun hconst.symm measurableSet_Icc
  have hdisj : Disjoint U C := by
    rw [Set.disjoint_left]
    intro t htU htC
    simp only [U, Set.mem_iUnion, exists_prop] at htU
    obtain ⟨k, hk, htk⟩ := htU
    have hend_start :
        path.sojournEnd k ≤ path.sojournStart (path.jumpCount T) :=
      path.sojournEnd_le_sojournStart_of_lt hstrict (Finset.mem_range.mp hk)
    exact not_lt_of_ge (le_trans hend_start htC.1) htk.2
  have hsplitU :
      ∫ t in U, g t =
        ∑ k ∈ Finset.range (path.jumpCount T),
          path.sojournTime k * f (path.stateSeq k) := by
    have hmeas : ∀ k ∈ Finset.range (path.jumpCount T),
        MeasurableSet (path.sojournInterval k) :=
      fun k _ => path.measurableSet_sojournInterval k
    have hpair : Set.Pairwise (↑(Finset.range (path.jumpCount T)))
        (fun k l => Disjoint (path.sojournInterval k) (path.sojournInterval l)) := by
      intro k hk l hl hkl
      exact (path.pairwise_disjoint_sojournInterval hstrict) (by simp) (by simp) hkl
    have hint : ∀ k ∈ Finset.range (path.jumpCount T),
        IntegrableOn g (path.sojournInterval k) volume := by
      intro k _hk
      have hconst : Set.EqOn g
          (fun _ : ℝ => f (path.stateSeq k))
          (path.sojournInterval k) := by
        intro t ht
        exact congrArg f
          (frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict k ht)
      exact (integrableOn_const measure_Ico_lt_top.ne).congr_fun hconst.symm
        (path.measurableSet_sojournInterval k)
    calc
      ∫ t in U, g t
          = ∑ k ∈ Finset.range (path.jumpCount T),
              ∫ t in path.sojournInterval k, g t := by
            exact integral_biUnion_finset
              (Finset.range (path.jumpCount T)) hmeas hpair hint
      _ = ∑ k ∈ Finset.range (path.jumpCount T),
            path.sojournTime k * f (path.stateSeq k) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            exact frozen_setIntegral_observable_sojournInterval
              M path hstrict hpos f k
  have hsplitC :
      ∫ t in C, g t =
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T := by
    simpa [C, g] using
      M.frozen_setIntegral_currentSojourn_observable
        path hstrict f hT hfuture
  have hsplit :
      ∫ t in Set.union U C, g t =
        (∑ k ∈ Finset.range (path.jumpCount T),
          path.sojournTime k * f (path.stateSeq k)) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T := by
    change ∫ t in U ∪ C, g t =
      (∑ k ∈ Finset.range (path.jumpCount T),
        path.sojournTime k * f (path.stateSeq k)) +
      f (path.stateSeq (path.jumpCount T)) *
        path.currentSojournElapsed T
    rw [setIntegral_union hdisj measurableSet_Icc hU_int hC_int]
    rw [hsplitU, hsplitC]
  calc
    (∑ k ∈ Finset.range (path.jumpCount T),
      f (path.stateSeq k) * path.sojournTime k) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T
        = (∑ k ∈ Finset.range (path.jumpCount T),
            path.sojournTime k * f (path.stateSeq k)) +
          f (path.stateSeq (path.jumpCount T)) *
            path.currentSojournElapsed T := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro k _hk
            ring
    _ = ∫ t in Set.union U C, g t := hsplit.symm
    _ = ∫ t in Set.Icc (0 : ℝ) T, g t := by
          rw [hUC_eq]

/-- At the start of the `n`-th frozen sojourn, the clock-time frozen
martingale residual is the finite time-compensated jump martingale through the
first `n` completed sojourns, provided the finite-lattice generator drift
agrees with the `RateSpec` drift along the relevant state sequence. -/
theorem frozenMartingalePart_at_sojournStart_eq_frozenTimeCompensated
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ)
    (hDrift : ∀ k < n,
      M.generatorDrift (path.stateSeq k) =
        M.rateSpec.drift (M.scaledState (path.stateSeq k))) :
    M.frozenMartingalePart (fun _ : Unit => path) (path.sojournStart n) Unit.unit =
      fun i => M.frozenTimeCompensatedJumpMartingale path i n := by
  have hmem_start : path.sojournStart n ∈ path.sojournInterval n := by
    cases n with
    | zero =>
        simp [CTMCPath.sojournInterval, hpos]
    | succ n =>
        simp [CTMCPath.sojournInterval, CTMCPath.sojournStart, CTMCPath.sojournEnd,
          hstrict n]
  have hstate_start :
      path.frozenStateAt (path.sojournStart n) = path.stateSeq n :=
    frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict n hmem_start
  have hmem_zero : (0 : ℝ) ∈ path.sojournInterval 0 := by
    simp [CTMCPath.sojournInterval, hpos]
  have hstate_zero : path.frozenStateAt 0 = path.stateSeq 0 :=
    frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict 0 hmem_zero
  have htel := M.scaledState_stateSeq_eq_init_add_scaledJumpSum path n
  ext i
  have htel_i :
      M.scaledState (path.stateSeq n) i - M.scaledState (path.stateSeq 0) i =
        M.scaledJumpSum path n i := by
    have h := congr_fun htel i
    simp only [Pi.add_apply] at h
    rw [CTMCPath.stateSeq_zero]
    linarith
  have hint_i :
      ∫ t in Set.Icc (0 : ℝ) (path.sojournStart n),
          (M.rateSpec.drift
            (M.frozenDensityProcess (fun _ : Unit => path) t Unit.unit)) i =
        ∑ k ∈ Finset.range n,
          M.generatorDrift (path.stateSeq k) i * path.sojournTime k := by
    let U : Set ℝ := ⋃ k ∈ Finset.range n, path.sojournInterval k
    let g : ℝ → ℝ := fun t =>
      (M.rateSpec.drift
        (M.frozenDensityProcess (fun _ : Unit => path) t Unit.unit)) i
    have hU_eq : U = Set.Ico (0 : ℝ) (path.sojournStart n) := by
      simpa [U] using
        biUnion_sojournInterval_range_eq_Ico_sojournStart path hstrict hpos n
    have hU_ae : U =ᵐ[volume] Set.Icc (0 : ℝ) (path.sojournStart n) := by
      rw [hU_eq]
      exact Ico_ae_eq_Icc' (by simp)
    have hmeas : ∀ k ∈ Finset.range n, MeasurableSet (path.sojournInterval k) :=
      fun k _ => path.measurableSet_sojournInterval k
    have hpair : Set.Pairwise (↑(Finset.range n))
        (fun k l => Disjoint (path.sojournInterval k) (path.sojournInterval l)) := by
      intro k hk l hl hkl
      exact (path.pairwise_disjoint_sojournInterval hstrict) (by simp) (by simp) hkl
    have hint : ∀ k ∈ Finset.range n,
        IntegrableOn g (path.sojournInterval k) volume := by
      intro k _hk
      have hconst : Set.EqOn g
          (fun _ : ℝ =>
            (M.rateSpec.drift (M.scaledState (path.stateSeq k))) i)
          (path.sojournInterval k) := by
        intro t ht
        have hstate :
            path.frozenStateAt t = path.stateSeq k :=
          frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict k ht
        have hdensity :
            M.frozenDensityProcess (fun _ : Unit => path) t Unit.unit =
              M.scaledState (path.stateSeq k) := by
          ext j
          simp [DensityDepCTMC.frozenDensityProcess, DensityDepCTMC.scaledState,
            hstate]
        simp only [g]
        change (M.rateSpec.drift
            (M.frozenDensityProcess (fun _ : Unit => path) t Unit.unit)) i =
          (M.rateSpec.drift (M.scaledState (path.stateSeq k))) i
        rw [hdensity]
      exact (integrableOn_const measure_Ico_lt_top.ne).congr_fun hconst.symm
        (path.measurableSet_sojournInterval k)
    calc
      ∫ t in Set.Icc (0 : ℝ) (path.sojournStart n),
          (M.rateSpec.drift
            (M.frozenDensityProcess (fun _ : Unit => path) t Unit.unit)) i
          = ∫ t in U, g t := by
            exact (setIntegral_congr_set hU_ae.symm)
      _ = ∑ k ∈ Finset.range n,
            ∫ t in path.sojournInterval k, g t := by
            exact integral_biUnion_finset (Finset.range n) hmeas hpair hint
      _ = ∑ k ∈ Finset.range n,
            path.sojournTime k *
              (M.rateSpec.drift (M.scaledState (path.stateSeq k))) i := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            have hconst : Set.EqOn g
                (fun _ : ℝ =>
                  (M.rateSpec.drift (M.scaledState (path.stateSeq k))) i)
                (path.sojournInterval k) := by
              intro t ht
              have hstate :
                  path.frozenStateAt t = path.stateSeq k :=
                frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict k ht
              have hdensity :
                  M.frozenDensityProcess (fun _ : Unit => path) t Unit.unit =
                    M.scaledState (path.stateSeq k) := by
                ext j
                simp [DensityDepCTMC.frozenDensityProcess, DensityDepCTMC.scaledState,
                  hstate]
              simp only [g]
              change (M.rateSpec.drift
                  (M.frozenDensityProcess (fun _ : Unit => path) t Unit.unit)) i =
                (M.rateSpec.drift (M.scaledState (path.stateSeq k))) i
              rw [hdensity]
            have hstart_le_end : path.sojournStart k ≤ path.sojournEnd k := by
              simpa [CTMCPath.sojournTime, sub_nonneg] using
                path.sojournTime_nonneg hstrict hpos k
            calc
              ∫ t in path.sojournInterval k, g t
                  = ∫ t in path.sojournInterval k,
                      (M.rateSpec.drift (M.scaledState (path.stateSeq k))) i := by
                    exact setIntegral_congr_fun
                      (path.measurableSet_sojournInterval k) hconst
              _ = volume.real (path.sojournInterval k) *
                    (M.rateSpec.drift (M.scaledState (path.stateSeq k))) i := by
                    rw [setIntegral_const]
                    simp
              _ = path.sojournTime k *
                    (M.rateSpec.drift (M.scaledState (path.stateSeq k))) i := by
                    rw [CTMCPath.sojournInterval,
                      Real.volume_real_Ico_of_le hstart_le_end]
                    simp [CTMCPath.sojournTime]
      _ = ∑ k ∈ Finset.range n,
            M.generatorDrift (path.stateSeq k) i * path.sojournTime k := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hklt : k < n := Finset.mem_range.mp hk
            have h := congr_fun (hDrift k hklt) i
            rw [h]
            ring
  simp only [frozenMartingalePart, frozenDensityProcess, frozenInitialCondition,
    frozenTimeCompensatedJumpMartingale, Pi.sub_apply]
  rw [hstate_start, hstate_zero, hint_i]
  simp [DensityDepCTMC.scaledState] at htel_i ⊢
  linarith

/-- At an arbitrary clock time before a future jump, the frozen martingale
coordinate is the completed-sojourn time-compensated jump martingale minus the
current partial-sojourn drift contribution. -/
theorem frozenMartingalePart_apply_eq_frozenTimeCompensated_sub_current
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {t : ℝ} (ht : 0 ≤ t)
    (hfuture : ∃ n, t < path.times n)
    (hDrift : ∀ k ≤ path.jumpCount t,
      M.generatorDrift (path.stateSeq k) =
        M.rateSpec.drift (M.scaledState (path.stateSeq k)))
    (i : Fin d) :
    M.frozenMartingalePart (fun _ : Unit => path) t Unit.unit i =
      M.frozenTimeCompensatedJumpMartingale path i (path.jumpCount t) -
        M.generatorDrift (path.stateSeq (path.jumpCount t)) i *
          path.currentSojournElapsed t := by
  let j := path.jumpCount t
  have hstate_t :
      path.frozenStateAt t = path.stateSeq j := by
    simpa [j] using
      frozenStateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
        path hstrict hfuture
        (by
          have hstart_le : path.sojournStart (path.jumpCount t) ≤ t :=
            path.sojournStart_jumpCount_le_of_exists ht hfuture
          exact ⟨hstart_le, le_rfl⟩)
  have hmem_zero : (0 : ℝ) ∈ path.sojournInterval 0 := by
    simp [CTMCPath.sojournInterval, hpos]
  have hstate_zero : path.frozenStateAt 0 = path.stateSeq 0 :=
    frozenStateAt_eq_stateSeq_of_mem_sojournInterval path hstrict 0 hmem_zero
  have htel := M.scaledState_stateSeq_eq_init_add_scaledJumpSum path j
  have htel_i :
      M.scaledState (path.stateSeq j) i - M.scaledState (path.stateSeq 0) i =
        M.scaledJumpSum path j i := by
    have h := congr_fun htel i
    simp only [Pi.add_apply] at h
    rw [CTMCPath.stateSeq_zero]
    linarith
  let f : (Fin d → Fin (M.N + 1)) → ℝ :=
    fun x => (M.rateSpec.drift (M.scaledState x)) i
  have hclock :=
    M.frozen_sum_observable_mul_sojournTime_add_currentSojourn_eq_setIntegral
      path hstrict hpos f ht hfuture
  have hintegral_eq :
      ∫ u in Set.Icc (0 : ℝ) t,
          (M.rateSpec.drift
            (M.frozenDensityProcess (fun _ : Unit => path) u Unit.unit)) i =
        (∑ k ∈ Finset.range j,
          M.generatorDrift (path.stateSeq k) i * path.sojournTime k) +
          M.generatorDrift (path.stateSeq j) i *
            path.currentSojournElapsed t := by
    have hcongr :
        (∫ u in Set.Icc (0 : ℝ) t,
          (M.rateSpec.drift
            (M.frozenDensityProcess (fun _ : Unit => path) u Unit.unit)) i) =
        ∫ u in Set.Icc (0 : ℝ) t, f (path.frozenStateAt u) := by
      exact setIntegral_congr_fun measurableSet_Icc (by
        intro u _hu
        have hdensity :
            M.frozenDensityProcess (fun _ : Unit => path) u Unit.unit =
              M.scaledState (path.frozenStateAt u) := by
          ext m
          simp [DensityDepCTMC.frozenDensityProcess, DensityDepCTMC.scaledState]
        simp [f, hdensity])
    rw [hcongr]
    rw [← hclock]
    have hsum :
        (∑ k ∈ Finset.range j, f (path.stateSeq k) * path.sojournTime k) =
          ∑ k ∈ Finset.range j,
            M.generatorDrift (path.stateSeq k) i * path.sojournTime k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hkj : k ≤ j := le_of_lt (Finset.mem_range.mp hk)
      have h := congr_fun (hDrift k hkj) i
      dsimp [f]
      rw [← h]
    have hcur :
        f (path.stateSeq j) * path.currentSojournElapsed t =
          M.generatorDrift (path.stateSeq j) i *
            path.currentSojournElapsed t := by
      have h := congr_fun (hDrift j le_rfl) i
      dsimp [f]
      rw [← h]
    rw [hsum, hcur]
  simp only [DensityDepCTMC.frozenMartingalePart,
    DensityDepCTMC.frozenDensityProcess, DensityDepCTMC.frozenInitialCondition,
    frozenTimeCompensatedJumpMartingale, Pi.sub_apply]
  rw [hstate_t, hstate_zero, hintegral_eq]
  simp [DensityDepCTMC.scaledState] at htel_i ⊢
  linarith

/-- At a fixed clock horizon before a future jump, the finite
clock-truncated skeleton through the current sojourn is the corresponding
coordinate of the continuous frozen martingale. -/
theorem frozenClockTruncatedMartingale_jumpCount_succ_eq_frozenMartingalePart
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n)
    (hDrift : ∀ k ≤ path.jumpCount T,
      M.generatorDrift (path.stateSeq k) =
        M.rateSpec.drift (M.scaledState (path.stateSeq k)))
    (i : Fin d) :
    M.frozenClockTruncatedMartingale path i T (path.jumpCount T + 1) =
      M.frozenMartingalePart (fun _ : Unit => path) T Unit.unit i := by
  let j := path.jumpCount T
  have hcompleted :
      (∑ k ∈ Finset.range j,
        M.truncatedCenteredCoordIncrement (path.stateSeq k) i
          (max 0 (T - path.sojournStart k))
          (path.sojournTime k, path.stateSeq (k + 1))) =
        M.frozenTimeCompensatedJumpMartingale path i j := by
    simp only [frozenTimeCompensatedJumpMartingale, scaledJumpSum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < j := Finset.mem_range.mp hk
    have hend : path.sojournEnd k ≤ T := by
      simpa [CTMCPath.sojournEnd] using
        path.times_le_of_lt_jumpCount hfuture hklt
    have hstart_le_end : path.sojournStart k ≤ path.sojournEnd k := by
      simpa [CTMCPath.sojournTime, sub_nonneg] using
        path.sojournTime_nonneg hstrict hpos k
    have hT_start_nonneg : 0 ≤ T - path.sojournStart k := by
      linarith
    have hsoj_le :
        path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
      rw [max_eq_right hT_start_nonneg]
      simp only [CTMCPath.sojournTime]
      linarith
    have hmin :
        min (path.sojournTime k) (max 0 (T - path.sojournStart k)) =
          path.sojournTime k := min_eq_left hsoj_le
    simp [truncatedCenteredCoordIncrement, hsoj_le]
  have hstart_j_le : path.sojournStart j ≤ T := by
    simpa [j] using path.sojournStart_jumpCount_le_of_exists hT hfuture
  have helapsed_nonneg : 0 ≤ T - path.sojournStart j := by
    linarith
  have hclock_j :
      max 0 (T - path.sojournStart j) = path.currentSojournElapsed T := by
    simp [CTMCPath.currentSojournElapsed, j, max_eq_right helapsed_nonneg]
  have hcur_lt :
      path.currentSojournElapsed T < path.sojournTime j := by
    have hend_lt : T < path.sojournEnd j := by
      simpa [CTMCPath.sojournEnd, j] using
        path.lt_times_jumpCount_of_exists hfuture
    simp only [CTMCPath.currentSojournElapsed, CTMCPath.sojournTime]
    linarith
  have hcur_le :
      path.currentSojournElapsed T ≤ path.sojournTime j :=
    le_of_lt hcur_lt
  have hnot_jump :
      ¬ path.sojournTime j ≤ max 0 (T - path.sojournStart j) := by
    rw [hclock_j]
    exact not_le_of_gt hcur_lt
  have hmin_cur :
      min (path.sojournTime j) (max 0 (T - path.sojournStart j)) =
        path.currentSojournElapsed T := by
    rw [hclock_j]
    exact min_eq_right hcur_le
  have hcurrent :
      M.truncatedCenteredCoordIncrement (path.stateSeq j) i
          (max 0 (T - path.sojournStart j))
          (path.sojournTime j, path.stateSeq (j + 1)) =
        -M.generatorDrift (path.stateSeq j) i *
          path.currentSojournElapsed T := by
    simp [truncatedCenteredCoordIncrement, hnot_jump, hmin_cur]
  have happly :=
    M.frozenMartingalePart_apply_eq_frozenTimeCompensated_sub_current
      path hstrict hpos hT hfuture hDrift i
  calc
    M.frozenClockTruncatedMartingale path i T (path.jumpCount T + 1)
        =
      (∑ k ∈ Finset.range j,
        M.truncatedCenteredCoordIncrement (path.stateSeq k) i
          (max 0 (T - path.sojournStart k))
          (path.sojournTime k, path.stateSeq (k + 1))) +
        M.truncatedCenteredCoordIncrement (path.stateSeq j) i
          (max 0 (T - path.sojournStart j))
          (path.sojournTime j, path.stateSeq (j + 1)) := by
          simp [frozenClockTruncatedMartingale, j, Finset.sum_range_succ]
    _ = M.frozenTimeCompensatedJumpMartingale path i j -
        M.generatorDrift (path.stateSeq j) i *
          path.currentSojournElapsed T := by
          rw [hcompleted, hcurrent]
          ring
    _ = M.frozenMartingalePart (fun _ : Unit => path) T Unit.unit i := by
          simpa [j] using happly.symm

/-! ## Clock-time compensated frozen jump martingale -/

theorem frozenTimeCompensatedJumpMartingale_stronglyAdapted
    (M : DensityDepCTMC d) (i : Fin d) :
    StronglyAdapted M.canonicalRecordFiltration
      (fun n records =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) := by
  intro n
  change StronglyMeasurable[M.canonicalRecordFiltration n]
    (fun records : M.canonicalRecordΩ =>
      M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n)
  have hdecomp : (fun records : M.canonicalRecordΩ =>
      M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) =
      fun records =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n +
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n := by
    ext records
    rw [M.frozenTimeCompensatedJumpMartingale_eq_add_holdingComp,
      M.frozenHoldingTimeCompensation_eq_scaledHoldingTimeDriftResidual]
  rw [hdecomp]
  exact
    (M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i n).add
      (M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i n)

theorem frozenTimeCompensatedJumpMartingale_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n)
      (M.canonicalRecordMeasure x₀) := by
  have hdecomp : (fun records : M.canonicalRecordΩ =>
      M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) =
      fun records =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n +
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n := by
    ext records
    rw [M.frozenTimeCompensatedJumpMartingale_eq_add_holdingComp,
      M.frozenHoldingTimeCompensation_eq_scaledHoldingTimeDriftResidual]
  rw [hdecomp]
  exact
    (M.frozenScaledJumpMartingale_integrable x₀ i n).add
      (M.integrable_scaledHoldingTimeDriftResidual_canonicalRecordMeasure_guarded
        x₀ i n)

theorem frozenTimeCompensatedJumpMartingale_condExp_increment_eq_zero_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n)
      | M.canonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  let μ := M.canonicalRecordMeasure x₀
  let nextJump : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (n + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq n)) i
  let hold : M.canonicalRecordΩ → ℝ := fun records => (records (n + 1)).1
  let drift : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq n) i
  let clock : M.canonicalRecordΩ → ℝ := fun records => drift records * hold records
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedGeneratorDriftDivExit ((M.canonicalPathMap records).stateSeq n) i
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n)
        =ᵐ[μ] fun records => nextJump records - clock records := by
    refine ae_of_all _ fun records => ?_
    simp [nextJump, hold, drift, clock,
      M.frozenTimeCompensatedJumpMartingale_succ_sub, canonicalPathMap,
      QMatrix.recordTrajectoryToPath_stateSeq, QMatrix.recordTrajectoryToPath_sojournTime]
  have hnext :
      μ[nextJump | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_apply_eq_guardedGeneratorDriftDivExit_ae
        x₀ n i
    dsimp [μ, nextJump, comp]
    simpa [Pi.sub_apply] using h
  have hdrift_sm :
      StronglyMeasurable[M.canonicalRecordFiltration n] drift := by
    exact (M.measurable_generatorDrift_stateSeq_canonicalRecordFiltration i n).stronglyMeasurable
  have hhold_int : Integrable hold μ := by
    simpa [hold, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ n
  have hclock_int : Integrable clock μ := by
    dsimp [clock, drift, hold, μ]
    simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      M.integrable_generatorDrift_mul_sojournTime_guarded x₀ i n
  have hhold_cond :
      μ[hold | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => (M.exitRateAt ((M.canonicalPathMap records).stateSeq n))⁻¹ := by
    have h := M.condExp_next_holdingTime_eq_inv_exitRate x₀ n
    dsimp [μ, hold]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa using h
  have hclock_pull :
      μ[clock | M.canonicalRecordFiltration n] =ᵐ[μ]
        fun records => drift records *
          (μ[hold | M.canonicalRecordFiltration n]) records := by
    dsimp [clock]
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      hdrift_sm hclock_int hhold_int
  have hclock :
      μ[clock | M.canonicalRecordFiltration n] =ᵐ[μ] comp := by
    filter_upwards [hclock_pull, hhold_cond] with records hpull hhold
    rw [hpull, hhold]
    dsimp [drift, comp]
    by_cases hzero : M.exitRateAt ((M.canonicalPathMap records).stateSeq n) = 0
    · simp [guardedGeneratorDriftDivExit, hzero]
    · simp [guardedGeneratorDriftDivExit, hzero, div_eq_mul_inv]
  have hsub :
      μ[nextJump - clock | M.canonicalRecordFiltration n] =ᵐ[μ]
        μ[nextJump | M.canonicalRecordFiltration n] -
          μ[clock | M.canonicalRecordFiltration n] :=
    MeasureTheory.condExp_sub
      (M.integrable_next_scaledState_sub_apply x₀ n i)
      hclock_int
      (M.canonicalRecordFiltration n)
  refine (MeasureTheory.condExp_congr_ae hinc).trans ?_
  change μ[nextJump - clock | M.canonicalRecordFiltration n] =ᵐ[μ] 0
  filter_upwards [hsub, hnext, hclock] with records hsub_eq hnext_eq hclock_eq
  rw [hsub_eq]
  simp only [Pi.sub_apply]
  rw [hnext_eq, hclock_eq]
  simp

theorem frozenTimeCompensatedJumpMartingale_martingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Martingale
      (fun n records =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  martingale_of_condExp_sub_eq_zero_nat
    (M.frozenTimeCompensatedJumpMartingale_stronglyAdapted i)
    (M.frozenTimeCompensatedJumpMartingale_integrable x₀ i)
    (fun n =>
      M.frozenTimeCompensatedJumpMartingale_condExp_increment_eq_zero_ae x₀ n i)

theorem frozenTimeCompensatedJumpMartingale_sq_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : M.canonicalRecordΩ → ℝ := fun records =>
    M.frozenScaledJumpMartingale (M.canonicalPathMap records) i n
  let R : M.canonicalRecordΩ → ℝ := fun records =>
    M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i n
  let W : M.canonicalRecordΩ → ℝ := fun records =>
    M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n
  have hZ_memLp : MemLp Z 2 μ := by
    exact (memLp_two_iff_integrable_sq (μ := μ)
      (((M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i n).mono
        (M.canonicalRecordFiltration.le n)).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.frozenScaledJumpMartingale_sq_integrable x₀ i n)
  have hR_memLp : MemLp R 2 μ := by
    exact (memLp_two_iff_integrable_sq (μ := μ)
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
        i n).mono (M.canonicalRecordFiltration.le n)).aestronglyMeasurable)).2
      (by
        simpa [R, μ] using
          M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure_guarded
            x₀ i n)
  have hW_eq : W =ᵐ[μ] Z + R := by
    refine ae_of_all _ fun records => ?_
    simp [W, Z, R]
    rw [M.frozenTimeCompensatedJumpMartingale_eq_add_holdingComp,
      M.frozenHoldingTimeCompensation_eq_scaledHoldingTimeDriftResidual]
  have hW_memLp : MemLp W 2 μ := by
    exact (memLp_congr_ae hW_eq).2 (hZ_memLp.add hR_memLp)
  simpa [W, μ] using hW_memLp.integrable_sq

theorem frozenTimeCompensatedJumpMartingale_norm_submartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Submartingale
      (fun n records =>
        ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n‖)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n
  have hmart : Martingale Z M.canonicalRecordFiltration μ := by
    simpa [Z, μ] using
      M.frozenTimeCompensatedJumpMartingale_martingale x₀ i
  refine submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.frozenTimeCompensatedJumpMartingale_stronglyAdapted i n).norm
  · intro n
    simpa [Z] using
      (M.frozenTimeCompensatedJumpMartingale_integrable x₀ i n).norm
  · intro n
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ‖(μ[Z (n + 1) | M.canonicalRecordFiltration n]) records‖)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => ‖Z (n + 1) records‖)
          | M.canonicalRecordFiltration n] :=
      norm_condExp_le
    have hcond : μ[Z (n + 1) | M.canonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

theorem frozenTimeCompensatedJumpMartingale_sq_minus_qvComp_supermartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Supermartingale
      (fun n records =>
        (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2 -
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n)
      M.canonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  have hqv_int_fixed : ∀ k : ℕ,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i k)
        μ := by
    intro k
    simpa [μ] using M.frozenScaledCoordQVCompensator_integrable x₀ i k
  have hmart : Martingale
      (fun n records => M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n)
      M.canonicalRecordFiltration μ := by
    simpa [μ] using M.frozenTimeCompensatedJumpMartingale_martingale x₀ i
  refine supermartingale_nat ?hadp ?hint ?hstep
  · intro n
    exact (M.frozenTimeCompensatedJumpMartingale_stronglyAdapted i n).pow 2 |>.sub
      (M.measurable_frozenScaledCoordQVCompensator_canonicalRecordFiltration
        i n).stronglyMeasurable
  · intro n
    exact (M.frozenTimeCompensatedJumpMartingale_sq_integrable x₀ i n).sub
      (hqv_int_fixed n)
  · intro n
    have hqv_meas :
        StronglyMeasurable[M.canonicalRecordFiltration n]
          (fun records : M.canonicalRecordΩ =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)) := by
      have hdecomp : ∀ records : M.canonicalRecordΩ,
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1) =
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n +
              M.guardedInstantCoordQVRateDivExit
                ((M.canonicalPathMap records).stateSeq n) i :=
        fun records => M.frozenScaledCoordQVCompensator_succ
          (M.canonicalPathMap records) i n
      simp_rw [hdecomp]
      exact
        (M.measurable_frozenScaledCoordQVCompensator_canonicalRecordFiltration
          i n).stronglyMeasurable.add
        (by
          have hst := M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration n
          have hg : Measurable (fun x : Fin d → Fin (M.N + 1) =>
              M.guardedInstantCoordQVRateDivExit x i) := Measurable.of_discrete
          exact (hg.comp hst).stronglyMeasurable)
    have hqv_int :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1))
          μ :=
      hqv_int_fixed (n + 1)
    have hmsq_int :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2)
          μ := by
      simpa [μ] using
        M.frozenTimeCompensatedJumpMartingale_sq_integrable x₀ i (n + 1)
    have hM_memLp : MemLp
        (fun records : M.canonicalRecordΩ =>
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) 2 μ := by
      exact (memLp_two_iff_integrable_sq
        (((M.frozenTimeCompensatedJumpMartingale_stronglyAdapted i (n + 1)).mono
          (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
        (by simpa [μ] using hmsq_int)
    have hcondVar_eq := ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp
      (m := M.canonicalRecordFiltration n)
      (M.canonicalRecordFiltration.le n) hM_memLp
    have hcondExp_M := hmart.condExp_ae_eq (show n ≤ n + 1 by omega)
    have hvar_le :
        μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
          | M.canonicalRecordFiltration n] ≤ᵐ[μ]
        fun records =>
          M.guardedInstantCoordQVRateDivExit
            ((M.canonicalPathMap records).stateSeq n) i := by
      have hraw :=
        M.condExp_frozenTimeCompensatedJumpMartingale_increment_sq_eq_qvComp_increment_ae
          x₀ n i
      filter_upwards [hraw] with records hraw_records
      exact le_of_eq hraw_records
    have hcenter_sq :
        (fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            μ[(fun r => M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 1))
              | M.canonicalRecordFiltration n] records) ^ 2)
          =ᵐ[μ]
        fun records =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
            M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2 := by
      filter_upwards [hcondExp_M] with records hM
      congr 1; linarith
    have hcondVar_eq_inc :
        ProbabilityTheory.condVar (M.canonicalRecordFiltration n)
          (fun records => M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) μ
          =ᵐ[μ]
        μ[(fun records =>
            (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
              M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
          | M.canonicalRecordFiltration n] := by
      simp only [ProbabilityTheory.condVar]
      exact condExp_congr_ae hcenter_sq
    have hcondExp_sub := condExp_sub hmsq_int hqv_int (M.canonicalRecordFiltration n)
    have hqv_pull := condExp_of_stronglyMeasurable
      (M.canonicalRecordFiltration.le n) hqv_meas hqv_int
    filter_upwards [hcondExp_sub, hcondVar_eq, hcondExp_M, hvar_le,
      hcondVar_eq_inc]
      with records hsub hvar hcond hincr hcvar_inc
    simp only [Pi.sub_apply] at hsub
    have key : μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 -
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1))
        | M.canonicalRecordFiltration n] records =
      μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2)
        | M.canonicalRecordFiltration n] records -
      μ[(fun records : M.canonicalRecordΩ =>
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1))
        | M.canonicalRecordFiltration n] records := hsub
    rw [key, congr_fun hqv_pull records]
    have hsucc := M.frozenScaledCoordQVCompensator_succ (M.canonicalPathMap records) i n
    have h1 : μ[(fun r : M.canonicalRecordΩ =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 1))
      | M.canonicalRecordFiltration n] records =
      M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n := hcond
    simp only [Pi.sub_apply, Pi.pow_apply] at hvar hcvar_inc
    have h_elim := hvar.symm.trans hcvar_inc
    have h_combined :
      μ[(fun records : M.canonicalRecordΩ =>
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2
        | M.canonicalRecordFiltration n] records ≤
      (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2 +
      (M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1) -
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n) := by
      calc μ[(fun r : M.canonicalRecordΩ =>
              M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 1)) ^ 2
            | M.canonicalRecordFiltration n] records
          = μ[(fun r : M.canonicalRecordΩ =>
              M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 1))
            | M.canonicalRecordFiltration n] records ^ 2 +
            μ[(fun records : M.canonicalRecordΩ =>
              (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
                M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
            | M.canonicalRecordFiltration n] records := by linarith [h_elim]
        _ = (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2 +
            μ[(fun records : M.canonicalRecordΩ =>
              (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) -
                M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
            | M.canonicalRecordFiltration n] records := by rw [h1]
        _ ≤ (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2 +
            (M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1) -
              M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n) := by
            gcongr
            exact le_trans hincr (le_of_eq (by linarith [hsucc]))
    calc
      μ[(fun records : M.canonicalRecordΩ =>
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) ^ 2)
        | M.canonicalRecordFiltration n] records -
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)
          ≤ ((M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2 +
              (M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1) -
                M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n)) -
              M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1) := by
              exact sub_le_sub_right h_combined _
      _ = (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2 -
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n := by ring

theorem integral_frozenTimeCompensatedJumpMartingale_sq_stoppedValue_le_integral_frozenQvComp_stoppedValue_of_stopping
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (τ : M.canonicalRecordΩ → WithTop ℕ) (N : ℕ)
    (hτ_stop : IsStoppingTime M.canonicalRecordFiltration τ)
    (hτ_le : ∀ records, τ records ≤ (N : WithTop ℕ)) :
    ∫ records,
        stoppedValue
          (fun n records =>
            (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
          τ records
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n)
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let B : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2 -
      M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
  have hsupermart :=
    M.frozenTimeCompensatedJumpMartingale_sq_minus_qvComp_supermartingale x₀ i
  have hsubmart : Submartingale (-B) M.canonicalRecordFiltration μ := by
    simpa [B, μ] using hsupermart.neg
  have h0_stop : IsStoppingTime M.canonicalRecordFiltration
      (fun _ : M.canonicalRecordΩ => (0 : WithTop ℕ)) := isStoppingTime_const _ _
  have h0_le : (fun _ : M.canonicalRecordΩ => (0 : WithTop ℕ)) ≤ τ := fun _ => bot_le
  have hopt := hsubmart.expected_stoppedValue_mono h0_stop hτ_stop h0_le hτ_le
  have hstop_neg : ∀ (σ : M.canonicalRecordΩ → WithTop ℕ),
      stoppedValue (-B) σ = fun ω => -(stoppedValue B σ ω) := by
    intro σ
    ext ω
    simp [stoppedValue, Pi.neg_apply]
  simp only [hstop_neg, integral_neg] at hopt
  have hopt' : ∫ ω, stoppedValue B τ ω ∂μ ≤
      ∫ ω, stoppedValue B (fun _ => (0 : WithTop ℕ)) ω ∂μ := by
    exact neg_le_neg_iff.1 hopt
  have hstop0 : stoppedValue B (fun _ => (0 : WithTop ℕ)) = B 0 := by
    ext ω
    simp [stoppedValue]
  rw [hstop0] at hopt'
  have hB0_zero : (fun records : M.canonicalRecordΩ => B 0 records) = fun _ => 0 := by
    ext records
    simp [B]
  have hB_le : ∫ records, stoppedValue B τ records ∂μ ≤ 0 := by
    calc
      ∫ records, stoppedValue B τ records ∂μ
          ≤ ∫ records, B 0 records ∂μ := hopt'
      _ = 0 := by simp [hB0_zero]
  let X : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2
  let Q : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n
  have hX_int : Integrable (stoppedValue X τ) μ := by
    exact integrable_stoppedValue ℕ hτ_stop
      (fun n => by
        simpa [μ] using M.frozenTimeCompensatedJumpMartingale_sq_integrable x₀ i n)
      (N := N) hτ_le
  have hQ_int : Integrable (stoppedValue Q τ) μ := by
    exact integrable_stoppedValue ℕ hτ_stop
      (fun n => M.frozenScaledCoordQVCompensator_integrable x₀ i n)
      (N := N) hτ_le
  have hBQ :
      stoppedValue B τ = fun ω => stoppedValue X τ ω - stoppedValue Q τ ω := by
    ext ω
    simp [stoppedValue, B, X, Q]
  have hsplit := integral_sub hX_int hQ_int
  have hB_split :
      ∫ ω, stoppedValue B τ ω ∂μ =
        ∫ ω, stoppedValue X τ ω ∂μ - ∫ ω, stoppedValue Q τ ω ∂μ := by
    rw [hBQ]
    exact hsplit
  dsimp [X, Q, μ] at hB_split ⊢
  linarith

/-! ## Shifted clock-time compensated frozen jump martingale -/

noncomputable def shiftedFrozenTimeCompensatedJumpMartingale
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (i : Fin d) (n : ℕ) (ω : Ω) : ℝ :=
  M.frozenTimeCompensatedJumpMartingale (pathMap ω) i (n + 1)

theorem shiftedFrozenTimeCompensatedJumpMartingale_stronglyAdapted
    (M : DensityDepCTMC d) (i : Fin d) :
    StronglyAdapted M.shiftedCanonicalRecordFiltration
      (fun n records =>
        M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records) := by
  intro n
  simp only [shiftedFrozenTimeCompensatedJumpMartingale]
  have hdecomp : (fun records : M.canonicalRecordΩ =>
      M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) =
      fun records =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) +
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1) := by
    ext records
    rw [M.frozenTimeCompensatedJumpMartingale_eq_add_holdingComp,
      M.frozenHoldingTimeCompensation_eq_scaledHoldingTimeDriftResidual]
  rw [hdecomp]
  exact
    (M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i (n + 1)).add
      (M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i (n + 1))

theorem shiftedFrozenTimeCompensatedJumpMartingale_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records)
      (M.canonicalRecordMeasure x₀) := by
  simp only [shiftedFrozenTimeCompensatedJumpMartingale]
  have hdecomp : (fun records : M.canonicalRecordΩ =>
      M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) =
      fun records =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i (n + 1) +
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1) := by
    ext records
    rw [M.frozenTimeCompensatedJumpMartingale_eq_add_holdingComp,
      M.frozenHoldingTimeCompensation_eq_scaledHoldingTimeDriftResidual]
  rw [hdecomp]
  exact
    (M.frozenScaledJumpMartingale_integrable x₀ i (n + 1)).add
      (M.integrable_scaledHoldingTimeDriftResidual_canonicalRecordMeasure_guarded
        x₀ i (n + 1))

theorem shiftedFrozenTimeCompensatedJumpMartingale_condExp_increment_eq_zero_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (n : ℕ) (i : Fin d) :
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i (n + 1) records -
          M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records)
      | M.shiftedCanonicalRecordFiltration n] =ᵐ[M.canonicalRecordMeasure x₀] 0 := by
  simp only [shiftedFrozenTimeCompensatedJumpMartingale]
  change
    (M.canonicalRecordMeasure x₀)[
      (fun records : M.canonicalRecordΩ =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1 + 1) -
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1))
      | M.canonicalRecordFiltration (n + 1)] =ᵐ[M.canonicalRecordMeasure x₀] 0
  let μ := M.canonicalRecordMeasure x₀
  let m := n + 1
  let nextJump : M.canonicalRecordΩ → ℝ := fun records =>
    (M.scaledState ((records (m + 1)).2) -
      M.scaledState ((M.canonicalPathMap records).stateSeq m)) i
  let hold : M.canonicalRecordΩ → ℝ := fun records => (records (m + 1)).1
  let drift : M.canonicalRecordΩ → ℝ := fun records =>
    M.generatorDrift ((M.canonicalPathMap records).stateSeq m) i
  let clock : M.canonicalRecordΩ → ℝ := fun records => drift records * hold records
  let comp : M.canonicalRecordΩ → ℝ := fun records =>
    M.guardedGeneratorDriftDivExit ((M.canonicalPathMap records).stateSeq m) i
  have hinc :
      (fun records : M.canonicalRecordΩ =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (m + 1) -
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i m)
        =ᵐ[μ] fun records => nextJump records - clock records := by
    refine ae_of_all _ fun records => ?_
    simp [nextJump, hold, drift, clock,
      M.frozenTimeCompensatedJumpMartingale_succ_sub, canonicalPathMap,
      QMatrix.recordTrajectoryToPath_stateSeq, QMatrix.recordTrajectoryToPath_sojournTime]
  have hnext :
      μ[nextJump | M.canonicalRecordFiltration m] =ᵐ[μ] comp := by
    have h :=
      M.condExp_next_scaledState_sub_apply_eq_guardedGeneratorDriftDivExit_ae
        x₀ m i
    dsimp [μ, nextJump, comp]
    simpa [Pi.sub_apply] using h
  have hdrift_sm :
      StronglyMeasurable[M.canonicalRecordFiltration m] drift := by
    exact (M.measurable_generatorDrift_stateSeq_canonicalRecordFiltration i m).stronglyMeasurable
  have hhold_int : Integrable hold μ := by
    simpa [hold, μ] using
      M.integrable_next_holdingTime_canonicalRecordMeasure_guarded x₀ m
  have hclock_int : Integrable clock μ := by
    dsimp [clock, drift, hold, μ]
    simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_sojournTime] using
      M.integrable_generatorDrift_mul_sojournTime_guarded x₀ i m
  have hhold_cond :
      μ[hold | M.canonicalRecordFiltration m] =ᵐ[μ]
        fun records => (M.exitRateAt ((M.canonicalPathMap records).stateSeq m))⁻¹ := by
    have h := M.condExp_next_holdingTime_eq_inv_exitRate x₀ m
    dsimp [μ, hold]
    rw [canonicalRecordFiltration,
      QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe]
    simpa using h
  have hclock_pull :
      μ[clock | M.canonicalRecordFiltration m] =ᵐ[μ]
        fun records => drift records *
          (μ[hold | M.canonicalRecordFiltration m]) records := by
    dsimp [clock]
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      hdrift_sm hclock_int hhold_int
  have hclock :
      μ[clock | M.canonicalRecordFiltration m] =ᵐ[μ] comp := by
    filter_upwards [hclock_pull, hhold_cond] with records hpull hhold
    rw [hpull, hhold]
    dsimp [drift, comp]
    by_cases hzero : M.exitRateAt ((M.canonicalPathMap records).stateSeq m) = 0
    · simp [guardedGeneratorDriftDivExit, hzero]
    · simp [guardedGeneratorDriftDivExit, hzero, div_eq_mul_inv]
  have hsub :
      μ[nextJump - clock | M.canonicalRecordFiltration m] =ᵐ[μ]
        μ[nextJump | M.canonicalRecordFiltration m] -
          μ[clock | M.canonicalRecordFiltration m] :=
    MeasureTheory.condExp_sub
      (M.integrable_next_scaledState_sub_apply x₀ m i)
      hclock_int
      (M.canonicalRecordFiltration m)
  refine (MeasureTheory.condExp_congr_ae hinc).trans ?_
  change μ[nextJump - clock | M.canonicalRecordFiltration m] =ᵐ[μ] 0
  filter_upwards [hsub, hnext, hclock] with records hsub_eq hnext_eq hclock_eq
  rw [hsub_eq]
  simp only [Pi.sub_apply]
  rw [hnext_eq, hclock_eq]
  simp

theorem shiftedFrozenTimeCompensatedJumpMartingale_martingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Martingale
      (fun n records =>
        M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records)
      M.shiftedCanonicalRecordFiltration (M.canonicalRecordMeasure x₀) :=
  martingale_of_condExp_sub_eq_zero_nat
    (M.shiftedFrozenTimeCompensatedJumpMartingale_stronglyAdapted i)
    (M.shiftedFrozenTimeCompensatedJumpMartingale_integrable x₀ i)
    (fun n =>
      M.shiftedFrozenTimeCompensatedJumpMartingale_condExp_increment_eq_zero_ae x₀ n i)

theorem shiftedFrozenTimeCompensatedJumpMartingale_sq_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        (M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : M.canonicalRecordΩ → ℝ := fun records =>
    M.shiftedFrozenScaledJumpMartingale M.canonicalPathMap i n records
  let R : M.canonicalRecordΩ → ℝ := fun records =>
    M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i (n + 1)
  let W : M.canonicalRecordΩ → ℝ := fun records =>
    M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records
  have hZ_memLp : MemLp Z 2 μ := by
    exact (memLp_two_iff_integrable_sq (μ := μ)
      (((M.shiftedFrozenScaledJumpMartingale_stronglyAdapted i n).mono
        (M.shiftedCanonicalRecordFiltration.le n)).aestronglyMeasurable)).2
      (by
        simpa [Z, μ] using
          M.shiftedFrozenScaledJumpMartingale_sq_integrable x₀ i n)
  have hR_memLp : MemLp R 2 μ := by
    exact (memLp_two_iff_integrable_sq (μ := μ)
      (((M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration
        i (n + 1)).mono (M.canonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
      (by
        simpa [R, μ] using
          M.integrable_scaledHoldingTimeDriftResidual_sq_canonicalRecordMeasure_guarded
            x₀ i (n + 1))
  have hW_eq : W =ᵐ[μ] Z + R := by
    refine ae_of_all _ fun records => ?_
    simp [W, Z, R, shiftedFrozenTimeCompensatedJumpMartingale,
      shiftedFrozenScaledJumpMartingale]
    rw [M.frozenTimeCompensatedJumpMartingale_eq_add_holdingComp,
      M.frozenHoldingTimeCompensation_eq_scaledHoldingTimeDriftResidual]
  have hW_memLp : MemLp W 2 μ := by
    exact (memLp_congr_ae hW_eq).2 (hZ_memLp.add hR_memLp)
  simpa [W, μ] using hW_memLp.integrable_sq

theorem integrable_frozenTimeCompensatedJumpMartingale_sup_sq_canonicalRecordMeasure
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖)) ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let W : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k =>
        ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖)
  let J : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
  let R : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)
  have hW_meas : Measurable W := by
    dsimp [W]
    refine Finset.measurable_range_sup'' ?_
    intro k _hk
    have hdecomp : (fun records : M.canonicalRecordΩ =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k) =
        fun records =>
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k +
            M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k := by
      ext records
      rw [M.frozenTimeCompensatedJumpMartingale_eq_add_holdingComp,
        M.frozenHoldingTimeCompensation_eq_scaledHoldingTimeDriftResidual]
    have hdecomp_abs : (fun records : M.canonicalRecordΩ =>
        |M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k|) =
        fun records =>
          |M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k +
            M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k| := by
      ext records
      rw [show M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k =
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k +
            M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k by
        exact congr_fun hdecomp records]
    rw [hdecomp_abs]
    have hbase : Measurable (fun records : M.canonicalRecordΩ =>
        M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k +
          M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k) :=
      (((M.stronglyAdapted_frozenScaledJumpMartingale_canonicalRecordFiltration i k).add
        (M.stronglyAdapted_scaledHoldingTimeDriftResidual_canonicalRecordFiltration i k)).mono
          (M.canonicalRecordFiltration.le k)).measurable
    simpa [Real.norm_eq_abs] using hbase.norm
  have hJ_int :
      Integrable (fun records : M.canonicalRecordΩ => (J records) ^ 2) μ := by
    simpa [J, μ] using
      M.integrable_frozenScaledJumpMartingale_sup_sq_canonicalRecordMeasure x₀ i n
  have hR_int :
      Integrable (fun records : M.canonicalRecordΩ => (R records) ^ 2) μ := by
    simpa [R, μ] using
      M.integrable_scaledHoldingTimeDriftResidual_sup_sq_canonicalRecordMeasure_guarded
        x₀ i n
  have hdom :
      Integrable (fun records : M.canonicalRecordΩ =>
        2 * (J records) ^ 2 + 2 * (R records) ^ 2) μ :=
    (hJ_int.const_mul 2).add (hR_int.const_mul 2)
  refine hdom.mono' (hW_meas.pow_const 2).aestronglyMeasurable ?_
  refine ae_of_all _ fun records => ?_
  have hW_nonneg : 0 ≤ W records := by
    dsimp [W]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k =>
          ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hJ_nonneg : 0 ≤ J records := by
    dsimp [J]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hR_nonneg : 0 ≤ R records := by
    dsimp [R]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos n)))
  have hW_le : W records ≤ J records + R records := by
    dsimp [W]
    refine Finset.sup'_le _ _ ?_
    intro k hk
    have hdecomp :
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k =
          M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k +
            M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k := by
      rw [M.frozenTimeCompensatedJumpMartingale_eq_add_holdingComp,
        M.frozenHoldingTimeCompensation_eq_scaledHoldingTimeDriftResidual]
    calc
      ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖
          ≤ ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖ +
              ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖ := by
            rw [hdecomp]
            exact norm_add_le _ _
      _ ≤ J records + R records := by
            exact add_le_add
              (Finset.le_sup'
                (fun k => ‖M.frozenScaledJumpMartingale (M.canonicalPathMap records) i k‖)
                hk)
              (Finset.le_sup'
                (fun k => ‖M.scaledHoldingTimeDriftResidual (M.canonicalPathMap records) i k‖)
                hk)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsquare_le : (W records) ^ 2 ≤ (J records + R records) ^ 2 :=
    sq_le_sq' ((neg_nonpos.mpr (add_nonneg hJ_nonneg hR_nonneg)).trans hW_nonneg) hW_le
  have hsplit : (J records + R records) ^ 2 ≤ 2 * (J records) ^ 2 + 2 * (R records) ^ 2 := by
    nlinarith [sq_nonneg (J records - R records)]
  exact hsplit.trans' hsquare_le

theorem integral_stopped_frozenTimeCompensatedJumpMartingale_sup_sq_le_frozenQvComp_stoppedValue_of_stopping
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (τ : M.canonicalRecordΩ → WithTop ℕ) (N : ℕ)
    (hτ_stop : IsStoppingTime M.canonicalRecordFiltration τ)
    (hτ_le : ∀ records, τ records ≤ (N : WithTop ℕ)) :
    ∫ records,
        ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            stoppedProcess
              (fun n records =>
                ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n‖)
              τ k records)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n)
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n‖
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => stoppedProcess Z τ k records)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    stoppedProcess Z τ N records
  let Xfixed : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖)
  have hsub :=
    (M.frozenTimeCompensatedJumpMartingale_norm_submartingale x₀ i).stoppedProcess hτ_stop
  have hX_meas : Measurable X := by
    dsimp [X]
    refine Finset.measurable_range_sup'' ?_
    intro k _hk
    simpa [Z] using
      ((hsub.stronglyAdapted k).mono (M.canonicalRecordFiltration.le k)).measurable
  have hY_meas : Measurable Y := by
    dsimp [Y]
    simpa [Z] using
      ((hsub.stronglyAdapted N).mono (M.canonicalRecordFiltration.le N)).measurable
  have hX_nonneg : 0 ≤ᵐ[μ] X := by
    refine ae_of_all _ fun records => ?_
    dsimp [X, Z]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => stoppedProcess
          (fun n records =>
            ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n‖)
          τ k records)
        (Finset.mem_range.mpr (Nat.succ_pos N)))
  have hY_nonneg : 0 ≤ᵐ[μ] Y := by
    refine ae_of_all _ fun records => ?_
    dsimp [Y, Z, stoppedProcess]
    exact abs_nonneg _
  have hX_le_fixed : ∀ records, X records ≤ Xfixed records := by
    intro records
    dsimp [X, Xfixed, Z, stoppedProcess]
    refine Finset.sup'_le _ _ ?_
    intro k hk
    let m : ℕ := (min (k : WithTop ℕ) (τ records)).untopA
    have hm_le_k : m ≤ k := by
      exact WithTop.untopA_le (min_le_left (k : WithTop ℕ) (τ records))
    have hk_le_N : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hm_mem : m ∈ Finset.range (N + 1) := by
      exact Finset.mem_range.mpr (by omega)
    exact Finset.le_sup'
      (fun k => ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖)
      hm_mem
  have hXfixed_nonneg : ∀ records, 0 ≤ Xfixed records := by
    intro records
    dsimp [Xfixed]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos N)))
  have hXsq_int : Integrable (fun records => X records ^ 2) μ := by
    have hfixed_int :
        Integrable (fun records => Xfixed records ^ 2) μ := by
      simpa [Xfixed, μ] using
        M.integrable_frozenTimeCompensatedJumpMartingale_sup_sq_canonicalRecordMeasure
          x₀ i N
    refine hfixed_int.mono' (hX_meas.pow_const 2).aestronglyMeasurable ?_
    refine ae_of_all _ fun records => ?_
    have hX_nonneg_record : 0 ≤ X records := by
      dsimp [X, Z]
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (fun k => stoppedProcess
            (fun n records =>
              ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n‖)
            τ k records)
          (Finset.mem_range.mpr (Nat.succ_pos N)))
    have hXfixed_nonneg_record : 0 ≤ Xfixed records := hXfixed_nonneg records
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq'
      ((neg_nonpos.mpr hXfixed_nonneg_record).trans hX_nonneg_record)
      (hX_le_fixed records)
  have hY_int : Integrable Y μ := by
    simpa [Y, Z, μ] using hsub.integrable N
  have hY_sq_int : Integrable (fun records => Y records ^ 2) μ := by
    refine hXsq_int.mono' (hY_meas.pow_const 2).aestronglyMeasurable ?_
    refine ae_of_all _ fun records => ?_
    have hY_le_X : Y records ≤ X records := by
      dsimp [X, Y]
      exact Finset.le_sup'
        (fun k => stoppedProcess Z τ k records)
        (Finset.mem_range.mpr (Nat.lt_succ_self N))
    have hY_nonneg_record : 0 ≤ Y records := by
      dsimp [Y, Z, stoppedProcess]
      exact abs_nonneg _
    have hX_nonneg_record : 0 ≤ X records :=
      hY_nonneg_record.trans hY_le_X
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq'
      ((neg_nonpos.mpr hX_nonneg_record).trans hY_nonneg_record)
      hY_le_X
  have hX_memLp_nat : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2 hXsq_int
  have hY_memLp_nat : MemLp Y 2 μ :=
    (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_sq_int
  have hXY_int : Integrable (fun records => X records * Y records) μ :=
    MemLp.integrable_mul hX_memLp_nat hY_memLp_nat
  have hMax : ∀ ε : NNReal,
      ((ε : ENNReal) * μ {records | (ε : ℝ) ≤ X records}) ≤
        ENNReal.ofReal (∫ records in {records | (ε : ℝ) ≤ X records},
          Y records ∂μ) := by
    intro ε
    simpa [X, Y, Z, μ] using
      MeasureTheory.maximal_ineq hsub
        (by
          intro n records
          dsimp [Z, stoppedProcess]
          exact abs_nonneg _)
        (ε := ε) N
  have hLayer :
      ∫ records, X records ^ 2 ∂μ ≤
        2 * ∫ records, X records * Y records ∂μ := by
    exact integral_sq_le_two_integral_mul_of_maximal_ineq
      hX_meas hY_meas hX_nonneg hY_nonneg hXsq_int hY_int hXY_int hMax
  let A : ℝ := ∫ records, X records ^ 2 ∂μ
  let B : ℝ := ∫ records, Y records ^ 2 ∂μ
  let C : ℝ := ∫ records, X records * Y records ∂μ
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun records => sq_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun records => sq_nonneg _
  have hCauchy : C ≤ A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
    have hX_memLp : MemLp X (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hX_memLp_nat
    have hY_memLp : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hY_memLp_nat
    have hholder :=
      integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := μ) Real.HolderConjugate.two_two
        hX_nonneg hY_nonneg hX_memLp hY_memLp
    simpa [A, B, C] using hholder
  have hA_le_fourB : A ≤ 4 * B := by
    have hA_le_sqrt : A ≤ 2 * (Real.sqrt A * Real.sqrt B) := by
      have hA_le : A ≤ 2 * (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) := by
        exact hLayer.trans (mul_le_mul_of_nonneg_left hCauchy (by norm_num))
      simpa [Real.sqrt_eq_rpow] using hA_le
    have hsq_nonneg : 0 ≤ (Real.sqrt A - 2 * Real.sqrt B) ^ 2 :=
      sq_nonneg _
    have hsqrtA_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA_nonneg
    have hsqrtB_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB_nonneg
    nlinarith [hA_le_sqrt, hsq_nonneg, hsqrtA_sq, hsqrtB_sq]
  have hYsq_eq_stopped :
      ∫ records, Y records ^ 2 ∂μ =
        ∫ records,
          stoppedValue
            (fun n records =>
              (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
            τ records ∂μ := by
    apply integral_congr_ae
    refine ae_of_all _ fun records => ?_
    have hmin : min (N : WithTop ℕ) (τ records) = τ records :=
      min_eq_right (hτ_le records)
    simp [Y, Z, stoppedProcess, stoppedValue, hmin, sq_abs]
  have hterminal :=
    M.integral_frozenTimeCompensatedJumpMartingale_sq_stoppedValue_le_integral_frozenQvComp_stoppedValue_of_stopping
      x₀ i τ N hτ_stop hτ_le
  calc
    ∫ records,
        ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            stoppedProcess
              (fun n records =>
                ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n‖)
              τ k records)) ^ 2
        ∂M.canonicalRecordMeasure x₀
        = A := by rfl
    _ ≤ 4 * B := hA_le_fourB
    _ = 4 * ∫ records,
          stoppedValue
            (fun n records =>
              (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i n) ^ 2)
            τ records ∂μ := by
              dsimp [B]
              rw [hYsq_eq_stopped]
    _ ≤ 4 * ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i n)
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
          exact mul_le_mul_of_nonneg_left hterminal (by norm_num)

theorem shiftedFrozenTimeCompensatedJumpMartingale_norm_submartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Submartingale
      (fun n records =>
        ‖M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records‖)
      M.shiftedCanonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records
  have hmart : Martingale Z M.shiftedCanonicalRecordFiltration μ := by
    simpa [Z, μ] using
      M.shiftedFrozenTimeCompensatedJumpMartingale_martingale x₀ i
  refine submartingale_nat ?hadp ?hint ?hstep
  · intro n
    simpa [Z] using
      (M.shiftedFrozenTimeCompensatedJumpMartingale_stronglyAdapted i n).norm
  · intro n
    simpa [Z] using
      (M.shiftedFrozenTimeCompensatedJumpMartingale_integrable x₀ i n).norm
  · intro n
    have hJ :
        (fun records : M.canonicalRecordΩ =>
          ‖(μ[Z (n + 1) | M.shiftedCanonicalRecordFiltration n]) records‖)
          ≤ᵐ[μ]
        μ[(fun records : M.canonicalRecordΩ => ‖Z (n + 1) records‖)
          | M.shiftedCanonicalRecordFiltration n] :=
      norm_condExp_le
    have hcond : μ[Z (n + 1) | M.shiftedCanonicalRecordFiltration n] =ᵐ[μ] Z n :=
      hmart.condExp_ae_eq (Nat.le_succ n)
    filter_upwards [hJ, hcond] with records hJrecords hcond_records
    simpa [Z, hcond_records] using hJrecords

theorem shiftedFrozenTimeCompensatedJumpMartingale_sq_minus_qvComp_supermartingale
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    Supermartingale
      (fun n records =>
        (M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records) ^ 2 -
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1))
      M.shiftedCanonicalRecordFiltration (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  have hqv_int_fixed : ∀ k : ℕ,
      Integrable
        (fun records : M.canonicalRecordΩ =>
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i k)
        μ := by
    intro k
    simpa [μ] using M.frozenScaledCoordQVCompensator_integrable x₀ i k
  have hmart : Martingale
      (fun n records => M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records)
      M.shiftedCanonicalRecordFiltration μ := by
    simpa [μ] using M.shiftedFrozenTimeCompensatedJumpMartingale_martingale x₀ i
  refine supermartingale_nat ?hadp ?hint ?hstep
  · intro n
    exact (M.shiftedFrozenTimeCompensatedJumpMartingale_stronglyAdapted i n).pow 2 |>.sub
      (M.measurable_frozenScaledCoordQVCompensator_canonicalRecordFiltration
        i (n + 1)).stronglyMeasurable
  · intro n
    exact (M.shiftedFrozenTimeCompensatedJumpMartingale_sq_integrable x₀ i n).sub
      (hqv_int_fixed (n + 1))
  · intro n
    simp only [shiftedFrozenTimeCompensatedJumpMartingale]
    have hqv_meas :
        StronglyMeasurable[M.shiftedCanonicalRecordFiltration n]
          (fun records : M.canonicalRecordΩ =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1)) := by
      have hdecomp : ∀ records : M.canonicalRecordΩ,
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1) =
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1) +
              M.guardedInstantCoordQVRateDivExit
                ((M.canonicalPathMap records).stateSeq (n + 1)) i :=
        fun records => M.frozenScaledCoordQVCompensator_succ
          (M.canonicalPathMap records) i (n + 1)
      simp_rw [hdecomp]
      exact
        (M.measurable_frozenScaledCoordQVCompensator_canonicalRecordFiltration
          i (n + 1)).stronglyMeasurable.add
        (by
          have hst := M.measurable_canonicalPathMap_stateSeq_canonicalRecordFiltration_le
            (show n + 1 ≤ n + 1 from le_refl _)
          have hg : Measurable (fun x : Fin d → Fin (M.N + 1) =>
              M.guardedInstantCoordQVRateDivExit x i) := Measurable.of_discrete
          exact (hg.comp hst).stronglyMeasurable)
    have hqv_int :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 2))
          μ :=
      hqv_int_fixed (n + 2)
    have hmsq_int :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2)) ^ 2)
          μ := by
      simpa [shiftedFrozenTimeCompensatedJumpMartingale, μ] using
        M.shiftedFrozenTimeCompensatedJumpMartingale_sq_integrable x₀ i (n + 1)
    have hM_memLp : MemLp
        (fun records : M.canonicalRecordΩ =>
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2)) 2 μ := by
      exact (memLp_two_iff_integrable_sq
        (((M.shiftedFrozenTimeCompensatedJumpMartingale_stronglyAdapted i (n + 1)).mono
          (M.shiftedCanonicalRecordFiltration.le (n + 1))).aestronglyMeasurable)).2
        (by simpa [shiftedFrozenTimeCompensatedJumpMartingale, μ] using hmsq_int)
    have hcondVar_eq := ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp
      (m := M.shiftedCanonicalRecordFiltration n)
      (M.shiftedCanonicalRecordFiltration.le n) hM_memLp
    have hcondExp_M := hmart.condExp_ae_eq (show n ≤ n + 1 by omega)
    have hvar_le :
        μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2) -
            M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2)
          | M.shiftedCanonicalRecordFiltration n] ≤ᵐ[μ]
        fun records =>
          M.guardedInstantCoordQVRateDivExit
            ((M.canonicalPathMap records).stateSeq (n + 1)) i := by
      have hraw :=
        M.condExp_frozenTimeCompensatedJumpMartingale_increment_sq_eq_qvComp_increment_ae
          x₀ (n + 1) i
      filter_upwards [hraw] with records hraw_records
      exact le_of_eq hraw_records
    have hcenter_sq :
        (fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2) -
            μ[(fun r => M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 2))
              | M.shiftedCanonicalRecordFiltration n] records) ^ 2)
          =ᵐ[μ]
        fun records =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2) -
            M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 := by
      filter_upwards [hcondExp_M] with records hM
      simp only [shiftedFrozenTimeCompensatedJumpMartingale] at hM
      congr 1; linarith
    have hcondVar_eq_inc :
        ProbabilityTheory.condVar (M.shiftedCanonicalRecordFiltration n)
          (fun records => M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2)) μ
          =ᵐ[μ]
        μ[(fun records =>
            (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2) -
              M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2)
          | M.shiftedCanonicalRecordFiltration n] := by
      simp only [ProbabilityTheory.condVar]
      exact condExp_congr_ae hcenter_sq
    have hcondExp_sub := condExp_sub hmsq_int hqv_int (M.shiftedCanonicalRecordFiltration n)
    have hqv_pull := condExp_of_stronglyMeasurable
      (M.shiftedCanonicalRecordFiltration.le n) hqv_meas hqv_int
    filter_upwards [hcondExp_sub, hcondVar_eq, hcondExp_M, hvar_le,
      hcondVar_eq_inc]
      with records hsub hvar hcond hincr hcvar_inc
    simp only [Pi.sub_apply] at hsub
    simp only [shiftedFrozenTimeCompensatedJumpMartingale] at hcond
    have key : μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1 + 1)) ^ 2 -
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1))
        | M.shiftedCanonicalRecordFiltration n] records =
      μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1 + 1)) ^ 2)
        | M.shiftedCanonicalRecordFiltration n] records -
      μ[(fun records : M.canonicalRecordΩ =>
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1))
        | M.shiftedCanonicalRecordFiltration n] records := hsub
    rw [key, congr_fun hqv_pull records]
    have hsucc := M.frozenScaledCoordQVCompensator_succ (M.canonicalPathMap records) i (n + 1)
    have h1 : μ[(fun r : M.canonicalRecordΩ =>
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 1 + 1))
      | M.shiftedCanonicalRecordFiltration n] records =
      M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) := hcond
    have hbridge : μ[(fun r : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 1 + 1)) ^ 2)
        | M.shiftedCanonicalRecordFiltration n] records =
      μ[(fun records : M.canonicalRecordΩ =>
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2)) ^ 2
        | M.shiftedCanonicalRecordFiltration n] records := rfl
    rw [hbridge]
    simp only [Pi.sub_apply, Pi.pow_apply] at hvar hcvar_inc
    have h_elim := hvar.symm.trans hcvar_inc
    have h_combined :
      μ[(fun records : M.canonicalRecordΩ =>
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2)) ^ 2
        | M.shiftedCanonicalRecordFiltration n] records ≤
      (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 +
      (M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1) -
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)) := by
      have h1_alt : μ[(fun r : M.canonicalRecordΩ =>
          M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 2))
        | M.shiftedCanonicalRecordFiltration n] records =
        M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1) := h1
      calc μ[(fun r : M.canonicalRecordΩ =>
              M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 2)) ^ 2
            | M.shiftedCanonicalRecordFiltration n] records
          = μ[(fun r : M.canonicalRecordΩ =>
              M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap r) i (n + 2))
            | M.shiftedCanonicalRecordFiltration n] records ^ 2 +
            μ[(fun records : M.canonicalRecordΩ =>
              (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2) -
                M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2)
            | M.shiftedCanonicalRecordFiltration n] records := by linarith [h_elim]
        _ = (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 +
            μ[(fun records : M.canonicalRecordΩ =>
              (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 2) -
                M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2)
            | M.shiftedCanonicalRecordFiltration n] records := by rw [h1_alt]
        _ ≤ (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 +
            (M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1 + 1) -
              M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)) := by
            gcongr
            exact le_trans hincr (le_of_eq (by linarith [hsucc]))
    linarith [h_combined]

theorem integral_frozenTimeCompensatedJumpMartingale_sq_one_le_integral_frozenScaledCoordQVCompensator_one
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) :
    ∫ records,
        (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i 1) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let inc : M.canonicalRecordΩ → ℝ := fun records =>
    M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i 1 -
      M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i 0
  have hinc_sq_int : Integrable (fun records => inc records ^ 2) μ := by
    refine (M.shiftedFrozenTimeCompensatedJumpMartingale_sq_integrable x₀ i 0).congr ?_
    refine ae_of_all _ fun records => ?_
    simp [inc, shiftedFrozenTimeCompensatedJumpMartingale]
  have hce_le :
      μ[(fun records : M.canonicalRecordΩ => inc records ^ 2)
        | M.canonicalRecordFiltration 0] ≤ᵐ[μ]
      fun records =>
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1 := by
    have hraw :=
      M.condExp_frozenTimeCompensatedJumpMartingale_increment_sq_eq_qvComp_increment_ae
        x₀ 0 i
    filter_upwards [hraw] with records hle
    have hqv1 :
        M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1 =
          M.guardedInstantCoordQVRateDivExit
            ((M.canonicalPathMap records).stateSeq 0) i := by
      simpa using
        M.frozenScaledCoordQVCompensator_succ
          (M.canonicalPathMap records) i 0
    have hinc_eq :
        μ[(fun records : M.canonicalRecordΩ => inc records ^ 2)
          | M.canonicalRecordFiltration 0] records =
        μ[(fun records : M.canonicalRecordΩ =>
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i 1 -
            M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i 0) ^ 2)
          | M.canonicalRecordFiltration 0] records := rfl
    rw [hinc_eq]
    exact (le_of_eq hle).trans (le_of_eq hqv1.symm)
  have hcond_int :
      ∫ records,
          (μ[(fun records : M.canonicalRecordΩ => inc records ^ 2)
            | M.canonicalRecordFiltration 0]) records ∂μ =
        ∫ records, inc records ^ 2 ∂μ := by
    exact integral_condExp
      (μ := μ)
      (m := M.canonicalRecordFiltration 0)
      (f := fun records : M.canonicalRecordΩ => inc records ^ 2)
      (M.canonicalRecordFiltration.le 0)
  have hmono :
      ∫ records,
          (μ[(fun records : M.canonicalRecordΩ => inc records ^ 2)
            | M.canonicalRecordFiltration 0]) records ∂μ ≤
        ∫ records,
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1 ∂μ :=
    integral_mono_ae integrable_condExp
      (M.frozenScaledCoordQVCompensator_integrable x₀ i 1) hce_le
  calc
    ∫ records,
        (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i 1) ^ 2
        ∂M.canonicalRecordMeasure x₀
        = ∫ records, inc records ^ 2 ∂μ := by
            apply integral_congr_ae
            refine ae_of_all _ fun records => ?_
            simp [inc]
    _ = ∫ records,
          (μ[(fun records : M.canonicalRecordΩ => inc records ^ 2)
            | M.canonicalRecordFiltration 0]) records ∂μ := hcond_int.symm
    _ ≤ ∫ records,
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1 ∂μ := hmono

theorem integral_shiftedFrozenTimeCompensatedJumpMartingale_sq_stoppedValue_le_integral_frozenQvComp_stoppedValue_of_stopping
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (τ : M.canonicalRecordΩ → WithTop ℕ) (N : ℕ)
    (hτ_stop : IsStoppingTime M.shiftedCanonicalRecordFiltration τ)
    (hτ_le : ∀ records, τ records ≤ (N : WithTop ℕ)) :
    ∫ records,
        stoppedValue
          (fun n records =>
            (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i
              (n + 1)) ^ 2)
          τ records
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i
              (n + 1))
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let B : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2 -
      M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)
  have hsupermart :=
    M.shiftedFrozenTimeCompensatedJumpMartingale_sq_minus_qvComp_supermartingale x₀ i
  have hsubmart : Submartingale (-B) M.shiftedCanonicalRecordFiltration μ := by
    simpa [B, μ, shiftedFrozenTimeCompensatedJumpMartingale] using hsupermart.neg
  have h0_stop : IsStoppingTime M.shiftedCanonicalRecordFiltration
      (fun _ : M.canonicalRecordΩ => (0 : WithTop ℕ)) := isStoppingTime_const _ _
  have h0_le : (fun _ : M.canonicalRecordΩ => (0 : WithTop ℕ)) ≤ τ := fun _ => bot_le
  have hopt := hsubmart.expected_stoppedValue_mono h0_stop hτ_stop h0_le
    hτ_le
  have hstop_neg : ∀ (σ : M.canonicalRecordΩ → WithTop ℕ),
      stoppedValue (-B) σ = fun ω => -(stoppedValue B σ ω) := by
    intro σ
    ext ω
    simp [stoppedValue, Pi.neg_apply]
  simp only [hstop_neg, integral_neg] at hopt
  have hopt' : ∫ ω, stoppedValue B τ ω ∂μ ≤
      ∫ ω, stoppedValue B (fun _ => (0 : WithTop ℕ)) ω ∂μ := by
    exact neg_le_neg_iff.1 hopt
  have hstop0 : stoppedValue B (fun _ => (0 : WithTop ℕ)) = B 0 := by
    ext ω
    simp [stoppedValue]
  rw [hstop0] at hopt'
  have hB0_le : ∫ records, B 0 records ∂μ ≤ 0 := by
    simp only [B]
    have hW1_int :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i 1) ^ 2)
          μ := by
      simpa [shiftedFrozenTimeCompensatedJumpMartingale, μ] using
        M.shiftedFrozenTimeCompensatedJumpMartingale_sq_integrable x₀ i 0
    have hQ1_int :
        Integrable
          (fun records : M.canonicalRecordΩ =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1)
          μ := by
      simpa [μ] using M.frozenScaledCoordQVCompensator_integrable x₀ i 1
    have hsplit := integral_sub hW1_int hQ1_int
    have hterm :=
      M.integral_frozenTimeCompensatedJumpMartingale_sq_one_le_integral_frozenScaledCoordQVCompensator_one
        x₀ i
    rw [hsplit]
    simpa [shiftedFrozenTimeCompensatedJumpMartingale, μ] using
      (by linarith : ∫ records,
          (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i 1) ^ 2
          ∂μ -
        ∫ records,
          M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i 1 ∂μ ≤ 0)
  have hB_le : ∫ records, stoppedValue B τ records ∂μ ≤ 0 :=
    hopt'.trans hB0_le
  let X : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i (n + 1)) ^ 2
  let Q : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i (n + 1)
  have hX_int : Integrable (stoppedValue X τ) μ := by
    exact integrable_stoppedValue ℕ hτ_stop
      (fun n => by
        simpa [shiftedFrozenTimeCompensatedJumpMartingale, μ] using
          M.shiftedFrozenTimeCompensatedJumpMartingale_sq_integrable x₀ i n)
      (N := N) hτ_le
  have hQ_int : Integrable (stoppedValue Q τ) μ := by
    exact integrable_stoppedValue ℕ hτ_stop
      (fun n => M.frozenScaledCoordQVCompensator_integrable x₀ i (n + 1))
      (N := N) hτ_le
  have hBQ :
      stoppedValue B τ = fun ω => stoppedValue X τ ω - stoppedValue Q τ ω := by
    ext ω
    simp [stoppedValue, B, X, Q]
  have hsplit := integral_sub hX_int hQ_int
  have hB_split :
      ∫ ω, stoppedValue B τ ω ∂μ =
        ∫ ω, stoppedValue X τ ω ∂μ - ∫ ω, stoppedValue Q τ ω ∂μ := by
    rw [hBQ]
    exact hsplit
  dsimp [X, Q, μ] at hB_split ⊢
  linarith

theorem integral_shiftedFrozenTimeCompensatedJumpMartingale_sq_stoppedValue_le_integral_frozenQvComp_stoppedValue
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) (N : ℕ) :
    let τ : M.canonicalRecordΩ → WithTop ℕ := fun records =>
      min ((M.canonicalPathMap records).jumpCountTop T) (N : WithTop ℕ)
    ∫ records,
        stoppedValue
          (fun n records =>
            (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i
              (n + 1)) ^ 2)
          τ records
        ∂M.canonicalRecordMeasure x₀ ≤
      ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i
              (n + 1))
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
  intro τ
  exact
    M.integral_shiftedFrozenTimeCompensatedJumpMartingale_sq_stoppedValue_le_integral_frozenQvComp_stoppedValue_of_stopping
      x₀ i τ N
      (by
        simpa [τ] using
          (M.isStoppingTime_canonicalPathMap_jumpCountTop_shifted T).min_const N)
      (fun records => min_le_right _ _)

theorem integral_stopped_shiftedFrozenTimeCompensatedJumpMartingale_sup_sq_le_frozenQvComp_stoppedValue_of_stopping
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (τ : M.canonicalRecordΩ → WithTop ℕ) (N : ℕ)
    (hτ_stop : IsStoppingTime M.shiftedCanonicalRecordFiltration τ)
    (hτ_le : ∀ records, τ records ≤ (N : WithTop ℕ)) :
    ∫ records,
        ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            stoppedProcess
              (fun n records =>
                ‖M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records‖)
              τ k records)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i
              (n + 1))
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let Z : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    ‖M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records‖
  let X : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => stoppedProcess Z τ k records)
  let Y : M.canonicalRecordΩ → ℝ := fun records =>
    stoppedProcess Z τ N records
  let Xfixed : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (N + 2)).sup' (by simp)
      (fun k => ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖)
  have hsub :=
    (M.shiftedFrozenTimeCompensatedJumpMartingale_norm_submartingale x₀ i).stoppedProcess hτ_stop
  have hX_meas : Measurable X := by
    dsimp [X]
    refine Finset.measurable_range_sup'' ?_
    intro k _hk
    simpa [Z] using
      ((hsub.stronglyAdapted k).mono (M.shiftedCanonicalRecordFiltration.le k)).measurable
  have hY_meas : Measurable Y := by
    dsimp [Y]
    simpa [Z] using
      ((hsub.stronglyAdapted N).mono (M.shiftedCanonicalRecordFiltration.le N)).measurable
  have hX_nonneg : 0 ≤ᵐ[μ] X := by
    refine ae_of_all _ fun records => ?_
    dsimp [X, Z]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => stoppedProcess
          (fun n records =>
            ‖M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records‖)
          τ k records)
        (Finset.mem_range.mpr (Nat.succ_pos N)))
  have hY_nonneg : 0 ≤ᵐ[μ] Y := by
    refine ae_of_all _ fun records => ?_
    dsimp [Y, Z, stoppedProcess]
    exact abs_nonneg _
  have hX_le_fixed : ∀ records, X records ≤ Xfixed records := by
    intro records
    dsimp [X, Xfixed, Z, stoppedProcess, shiftedFrozenTimeCompensatedJumpMartingale]
    refine Finset.sup'_le _ _ ?_
    intro k hk
    let m : ℕ := (min (k : WithTop ℕ) (τ records)).untopA
    have hm_le_k : m ≤ k := by
      exact WithTop.untopA_le (min_le_left (k : WithTop ℕ) (τ records))
    have hk_le_N : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hm_mem : m + 1 ∈ Finset.range (N + 2) := by
      exact Finset.mem_range.mpr (by omega)
    exact Finset.le_sup'
      (fun k => ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖)
      hm_mem
  have hXfixed_nonneg : ∀ records, 0 ≤ Xfixed records := by
    intro records
    dsimp [Xfixed]
    exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i k‖)
        (Finset.mem_range.mpr (Nat.succ_pos (N + 1))))
  have hXsq_int : Integrable (fun records => X records ^ 2) μ := by
    have hfixed_int :
        Integrable (fun records => Xfixed records ^ 2) μ := by
      simpa [Xfixed, μ] using
        M.integrable_frozenTimeCompensatedJumpMartingale_sup_sq_canonicalRecordMeasure
          x₀ i (N + 1)
    refine hfixed_int.mono' (hX_meas.pow_const 2).aestronglyMeasurable ?_
    refine ae_of_all _ fun records => ?_
    have hX_nonneg_record : 0 ≤ X records := by
      dsimp [X, Z]
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (fun k => stoppedProcess
            (fun n records =>
              ‖M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records‖)
            τ k records)
          (Finset.mem_range.mpr (Nat.succ_pos N)))
    have hXfixed_nonneg_record : 0 ≤ Xfixed records := hXfixed_nonneg records
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq'
      ((neg_nonpos.mpr hXfixed_nonneg_record).trans hX_nonneg_record)
      (hX_le_fixed records)
  have hY_int : Integrable Y μ := by
    simpa [Y, Z, μ] using hsub.integrable N
  have hY_sq_int : Integrable (fun records => Y records ^ 2) μ := by
    refine hXsq_int.mono' (hY_meas.pow_const 2).aestronglyMeasurable ?_
    refine ae_of_all _ fun records => ?_
    have hY_le_X : Y records ≤ X records := by
      dsimp [X, Y]
      exact Finset.le_sup'
        (fun k => stoppedProcess Z τ k records)
        (Finset.mem_range.mpr (Nat.lt_succ_self N))
    have hY_nonneg_record : 0 ≤ Y records := by
      dsimp [Y, Z, stoppedProcess]
      exact abs_nonneg _
    have hX_nonneg_record : 0 ≤ X records :=
      hY_nonneg_record.trans hY_le_X
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq'
      ((neg_nonpos.mpr hX_nonneg_record).trans hY_nonneg_record)
      hY_le_X
  have hX_memLp_nat : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hX_meas.aestronglyMeasurable).2 hXsq_int
  have hY_memLp_nat : MemLp Y 2 μ :=
    (memLp_two_iff_integrable_sq hY_meas.aestronglyMeasurable).2 hY_sq_int
  have hXY_int : Integrable (fun records => X records * Y records) μ :=
    MemLp.integrable_mul hX_memLp_nat hY_memLp_nat
  have hMax : ∀ ε : NNReal,
      ((ε : ENNReal) * μ {records | (ε : ℝ) ≤ X records}) ≤
        ENNReal.ofReal (∫ records in {records | (ε : ℝ) ≤ X records},
          Y records ∂μ) := by
    intro ε
    simpa [X, Y, Z, μ] using
      MeasureTheory.maximal_ineq hsub
        (by
          intro n records
          dsimp [Z, stoppedProcess]
          exact abs_nonneg _)
        (ε := ε) N
  have hLayer :
      ∫ records, X records ^ 2 ∂μ ≤
        2 * ∫ records, X records * Y records ∂μ := by
    exact integral_sq_le_two_integral_mul_of_maximal_ineq
      hX_meas hY_meas hX_nonneg hY_nonneg hXsq_int hY_int hXY_int hMax
  let A : ℝ := ∫ records, X records ^ 2 ∂μ
  let B : ℝ := ∫ records, Y records ^ 2 ∂μ
  let C : ℝ := ∫ records, X records * Y records ∂μ
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun records => sq_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun records => sq_nonneg _
  have hCauchy : C ≤ A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
    have hX_memLp : MemLp X (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hX_memLp_nat
    have hY_memLp : MemLp Y (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using hY_memLp_nat
    have hholder :=
      integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := μ) Real.HolderConjugate.two_two
        hX_nonneg hY_nonneg hX_memLp hY_memLp
    simpa [A, B, C] using hholder
  have hA_le_fourB : A ≤ 4 * B := by
    have hA_le_sqrt : A ≤ 2 * (Real.sqrt A * Real.sqrt B) := by
      have hA_le : A ≤ 2 * (A ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) := by
        exact hLayer.trans (mul_le_mul_of_nonneg_left hCauchy (by norm_num))
      simpa [Real.sqrt_eq_rpow] using hA_le
    have hsq_nonneg : 0 ≤ (Real.sqrt A - 2 * Real.sqrt B) ^ 2 :=
      sq_nonneg _
    have hsqrtA_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA_nonneg
    have hsqrtB_sq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB_nonneg
    nlinarith [hA_le_sqrt, hsq_nonneg, hsqrtA_sq, hsqrtB_sq]
  have hYsq_eq_stopped :
      ∫ records, Y records ^ 2 ∂μ =
        ∫ records,
          stoppedValue
            (fun n records =>
              (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i
                (n + 1)) ^ 2)
            τ records ∂μ := by
    apply integral_congr_ae
    refine ae_of_all _ fun records => ?_
    have hmin : min (N : WithTop ℕ) (τ records) = τ records :=
      min_eq_right (hτ_le records)
    simp [Y, Z, stoppedProcess, stoppedValue, shiftedFrozenTimeCompensatedJumpMartingale,
      hmin, sq_abs]
  have hterminal :=
    M.integral_shiftedFrozenTimeCompensatedJumpMartingale_sq_stoppedValue_le_integral_frozenQvComp_stoppedValue_of_stopping
      x₀ i τ N hτ_stop hτ_le
  calc
    ∫ records,
        ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            stoppedProcess
              (fun n records =>
                ‖M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records‖)
              τ k records)) ^ 2
        ∂M.canonicalRecordMeasure x₀
        = A := by rfl
    _ ≤ 4 * B := hA_le_fourB
    _ = 4 * ∫ records,
          stoppedValue
            (fun n records =>
              (M.frozenTimeCompensatedJumpMartingale (M.canonicalPathMap records) i
                (n + 1)) ^ 2)
            τ records ∂μ := by
              dsimp [B]
              rw [hYsq_eq_stopped]
    _ ≤ 4 * ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i
              (n + 1))
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
          exact mul_le_mul_of_nonneg_left hterminal (by norm_num)

theorem integral_stopped_shiftedFrozenTimeCompensatedJumpMartingale_sup_sq_le_frozenQvComp_stoppedValue
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (i : Fin d) (T : ℝ) (N : ℕ) :
    let τ : M.canonicalRecordΩ → WithTop ℕ := fun records =>
      min ((M.canonicalPathMap records).jumpCountTop T) (N : WithTop ℕ)
    ∫ records,
        ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k =>
            stoppedProcess
              (fun n records =>
                ‖M.shiftedFrozenTimeCompensatedJumpMartingale M.canonicalPathMap i n records‖)
              τ k records)) ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∫ records,
        stoppedValue
          (fun n records =>
            M.frozenScaledCoordQVCompensator (M.canonicalPathMap records) i
              (n + 1))
          τ records
        ∂M.canonicalRecordMeasure x₀ := by
  intro τ
  exact
    M.integral_stopped_shiftedFrozenTimeCompensatedJumpMartingale_sup_sq_le_frozenQvComp_stoppedValue_of_stopping
      x₀ i τ N
      (by
        simpa [τ] using
          (M.isStoppingTime_canonicalPathMap_jumpCountTop_shifted T).min_const N)
      (fun records => min_le_right _ _)

/-! ## Generic finite-clock skeleton Doob constants -/

/-- Dimension-only constant for the generic frozen Doob L2 clock bridge.

The term `(4 / 3) * (4 * card(Fin d))` is the continuous-interpolation
endpoint cost applied after the coordinate Doob estimates are summed; the
final `+ 4` is the jump-size interpolation cost.  Concrete systems may improve
`card(Fin d)` by proving a sharper coordinate-QV/vector-QV comparison. -/
noncomputable def frozenMartingalePartDoobL2Constant (d : ℕ) : ℝ :=
  (4 / 3 : ℝ) * (4 * (Fintype.card (Fin d) : ℝ)) + 4

theorem frozenMartingalePartDoobL2Constant_pos (d : ℕ) :
    0 < frozenMartingalePartDoobL2Constant d := by
  unfold frozenMartingalePartDoobL2Constant
  positivity

/-- Vector-valued clock-truncated martingale skeleton at embedded index `k`. -/
noncomputable def frozenClockSkeletonVec
    (M : DensityDepCTMC d) (T : ℝ) (k : ℕ)
    (records : M.canonicalRecordΩ) : Fin d → ℝ :=
  fun i => M.canonicalFrozenClockTruncatedMartingale T i k records

/-- Finite supremum of the vector-valued clock skeleton through `n`. -/
noncomputable def frozenClockSkeletonSupSq
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ)
    (records : M.canonicalRecordΩ) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => ‖M.frozenClockSkeletonVec T k records‖ ^ 2)

/-- Finite sum of the vector squared-jump increments truncated at clock horizon
`T`. -/
noncomputable def frozenTruncatedJumpSqSum
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ)
    (records : M.canonicalRecordΩ) : ℝ :=
  ∑ k ∈ Finset.range n,
    M.truncatedJumpSqIncrementFromHistory T k
      (Preorder.frestrictLe k records) (records (k + 1))

/-- Finite sum of the vector instantaneous-QV clock increments. -/
noncomputable def frozenClockTruncatedQVIntegralSum
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    ∫ records,
      (let hist := Preorder.frestrictLe k records
       let x : Fin d → Fin (M.N + 1) :=
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) k hist
       M.instantQVRate x *
        min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
      ∂M.canonicalRecordMeasure x₀

theorem frozenTruncatedJumpSqSum_nonneg
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ)
    (records : M.canonicalRecordΩ) :
    0 ≤ M.frozenTruncatedJumpSqSum T n records := by
  classical
  unfold frozenTruncatedJumpSqSum
  refine Finset.sum_nonneg ?_
  intro k _hk
  by_cases hle :
      (records (k + 1)).1 ≤
        QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)
  · simp [truncatedJumpSqIncrementFromHistory, Set.indicator, hle]
  · simp [truncatedJumpSqIncrementFromHistory, Set.indicator, hle]

theorem frozenClockSkeletonSupSq_nonneg
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ)
    (records : M.canonicalRecordΩ) :
    0 ≤ M.frozenClockSkeletonSupSq T n records := by
  classical
  unfold frozenClockSkeletonSupSq
  exact (sq_nonneg ‖M.frozenClockSkeletonVec T 0 records‖).trans
    (Finset.le_sup'
      (s := Finset.range (n + 1))
      (f := fun k => ‖M.frozenClockSkeletonVec T k records‖ ^ 2)
      (Finset.mem_range.mpr (Nat.succ_pos n)))

/-- The finite vector clock-skeleton supremum is integrable. -/
theorem integrable_frozenClockSkeletonSupSq
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        M.frozenClockSkeletonSupSq T n records)
      (M.canonicalRecordMeasure x₀) := by
  let μ := M.canonicalRecordMeasure x₀
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.frozenClockSkeletonSupSq T n records
  let C : Fin d → M.canonicalRecordΩ → ℝ := fun i records =>
    ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
  have hC_int : ∀ i : Fin d, Integrable (C i) μ := by
    intro i
    simpa [C, μ] using
      M.integrable_canonicalFrozenClockTruncatedMartingale_sup_sq x₀ T i n
  have hsumC_int : Integrable (fun records => ∑ i : Fin d, C i records) μ :=
    integrable_finsetSum Finset.univ fun i _ => hC_int i
  have hA_meas : AEStronglyMeasurable A μ := by
    dsimp [A, frozenClockSkeletonSupSq, frozenClockSkeletonVec]
    refine (Finset.measurable_range_sup'' ?_).aestronglyMeasurable
    intro k _hk
    exact (measurable_norm.comp
      (measurable_pi_lambda _ fun i =>
        (M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
          T i k).mono (M.canonicalRecordFiltration.le k) le_rfl)).pow measurable_const
  have hpoint :
      ∀ records : M.canonicalRecordΩ, A records ≤ ∑ i : Fin d, C i records := by
    intro records
    dsimp [A, C, frozenClockSkeletonSupSq, frozenClockSkeletonVec]
    refine Finset.sup'_le _ _ ?_
    intro k hk
    have hcoord :
        ‖(fun i : Fin d =>
          M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2 ≤
        ∑ i : Fin d,
          (M.canonicalFrozenClockTruncatedMartingale T i k records) ^ 2 :=
      Ripple.Kurtz.vector_norm_sq_le_sum_sq _
    refine hcoord.trans ?_
    refine Finset.sum_le_sum fun i _hi => ?_
    let S : ℝ :=
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
    have hS_nonneg : 0 ≤ S := by
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
          hk)
    have habs_le :
        |M.canonicalFrozenClockTruncatedMartingale T i k records| ≤ S := by
      simpa [S, Real.norm_eq_abs] using
        Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
          hk
    have hsquare :
        (M.canonicalFrozenClockTruncatedMartingale T i k records) ^ 2 ≤ S ^ 2 := by
      rw [← sq_abs]
      exact sq_le_sq' (by
        nlinarith [hS_nonneg,
          abs_nonneg (M.canonicalFrozenClockTruncatedMartingale T i k records)]) habs_le
    simpa [S] using hsquare
  refine hsumC_int.mono' hA_meas ?_
  refine ae_of_all _ fun records => ?_
  have hA_nonneg :
      0 ≤ M.frozenClockSkeletonSupSq T n records :=
    M.frozenClockSkeletonSupSq_nonneg T n records
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, C i records := by
    exact Finset.sum_nonneg fun i _ => by
      dsimp [C]
      exact sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hA_nonneg]
  exact hpoint records

/-- Generic coordinate-QV/vector-QV comparison for one clock-truncated embedded
increment.  The constant is only the ambient dimension. -/
theorem sum_clockTruncatedCoordQV_integral_le_card_mul_vector
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (k : ℕ) :
    (∑ i : Fin d,
      ∫ records,
        (let hist := Preorder.frestrictLe k records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k hist
         M.instantCoordQVRate x i *
          min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
        ∂M.canonicalRecordMeasure x₀) ≤
      (Fintype.card (Fin d) : ℝ) * ∫ records,
        (let hist := Preorder.frestrictLe k records
         let x : Fin d → Fin (M.N + 1) :=
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) k hist
         M.instantQVRate x *
          min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
        ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let X : M.canonicalRecordΩ → Fin d → Fin (M.N + 1) := fun records =>
    QMatrix.currentStateFromHistory
      (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    min (records (k + 1)).1
      (QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records))
  let C : Fin d → M.canonicalRecordΩ → ℝ := fun i records =>
    M.instantCoordQVRate (X records) i * A records
  let V : M.canonicalRecordΩ → ℝ := fun records =>
    M.instantQVRate (X records) * A records
  change (∑ i : Fin d, ∫ records, C i records ∂μ) ≤
    (Fintype.card (Fin d) : ℝ) * ∫ records, V records ∂μ
  have hC_int : ∀ i : Fin d, Integrable (C i) μ := by
    intro i
    simpa [C, X, A, μ] using
      M.integrable_clockTruncatedCoordQVIncrement x₀ T i k
  have hV_int : Integrable V μ := by
    simpa [V, X, A, μ] using
      M.integrable_clockTruncatedQVIncrement x₀ T k
  have hsumC_int : Integrable (fun records => ∑ i : Fin d, C i records) μ :=
    integrable_finsetSum Finset.univ fun i _ => hC_int i
  have hcardV_int : Integrable
      (fun records : M.canonicalRecordΩ =>
        (Fintype.card (Fin d) : ℝ) * V records) μ :=
    hV_int.const_mul _
  have hpoint :
      (fun records : M.canonicalRecordΩ => ∑ i : Fin d, C i records)
        ≤ᵐ[μ]
      fun records => (Fintype.card (Fin d) : ℝ) * V records := by
    filter_upwards
      [M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae x₀]
      with records hhold
    have hA_nonneg : 0 ≤ A records := by
      dsimp [A]
      exact le_min (hhold k)
        (QMatrix.historyClockRemaining_nonneg T k (Preorder.frestrictLe k records))
    calc
      (∑ i : Fin d, C i records)
          = (∑ i : Fin d, M.instantCoordQVRate (X records) i) * A records := by
            simp [C, Finset.sum_mul]
      _ ≤ ((Fintype.card (Fin d) : ℝ) * M.instantQVRate (X records)) *
            A records := by
            exact mul_le_mul_of_nonneg_right
              (M.sum_instantCoordQVRate_le_card_mul_instantQVRate (X records))
              hA_nonneg
      _ = (Fintype.card (Fin d) : ℝ) * V records := by ring
  calc
    (∑ i : Fin d, ∫ records, C i records ∂μ)
        = ∫ records, (∑ i : Fin d, C i records) ∂μ := by
            rw [integral_finsetSum]
            intro i _hi
            exact hC_int i
    _ ≤ ∫ records, (Fintype.card (Fin d) : ℝ) * V records ∂μ :=
          integral_mono_ae hsumC_int hcardV_int hpoint
    _ = (Fintype.card (Fin d) : ℝ) * ∫ records, V records ∂μ := by
          rw [integral_const_mul]

/-- Summing the coordinate clock-skeleton Doob estimates gives a vector bound
against the sum of coordinate QV increments. -/
theorem integral_frozenClockTruncated_vector_sup_sq_le_coord_qv
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.frozenClockSkeletonVec T k records‖ ^ 2)
        ∂M.canonicalRecordMeasure x₀ ≤
      4 * ∑ i : Fin d, ∑ k ∈ Finset.range n,
        ∫ records,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantCoordQVRate x i *
            min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
          ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let V : M.canonicalRecordΩ → ℝ := fun records =>
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.frozenClockSkeletonVec T k records‖ ^ 2)
  let C : Fin d → M.canonicalRecordΩ → ℝ := fun i records =>
    ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)) ^ 2
  have hC_int : ∀ i : Fin d, Integrable (C i) μ := by
    intro i
    simpa [C, μ] using
      M.integrable_canonicalFrozenClockTruncatedMartingale_sup_sq x₀ T i n
  have hsumC_int : Integrable (fun records => ∑ i : Fin d, C i records) μ :=
    integrable_finsetSum Finset.univ fun i _ => hC_int i
  have hV_meas : AEStronglyMeasurable V μ := by
    dsimp [V, frozenClockSkeletonVec]
    refine (Finset.measurable_range_sup'' ?_).aestronglyMeasurable
    intro k _hk
    exact (measurable_norm.comp
      (measurable_pi_lambda _ fun i =>
        (M.measurable_canonicalFrozenClockTruncatedMartingale_canonicalRecordFiltration
          T i k).mono (M.canonicalRecordFiltration.le k) le_rfl)).pow measurable_const
  have hpoint : ∀ records : M.canonicalRecordΩ, V records ≤ ∑ i : Fin d, C i records := by
    intro records
    dsimp [V, C, frozenClockSkeletonVec]
    refine Finset.sup'_le _ _ ?_
    intro k hk
    have hcoord :
        ‖(fun i : Fin d =>
          M.canonicalFrozenClockTruncatedMartingale T i k records)‖ ^ 2 ≤
        ∑ i : Fin d,
          (M.canonicalFrozenClockTruncatedMartingale T i k records) ^ 2 :=
      Ripple.Kurtz.vector_norm_sq_le_sum_sq _
    refine hcoord.trans ?_
    refine Finset.sum_le_sum fun i _hi => ?_
    let S : ℝ :=
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
    have hS_nonneg : 0 ≤ S := by
      exact (norm_nonneg _).trans
        (Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    have habs_le :
        |M.canonicalFrozenClockTruncatedMartingale T i k records| ≤ S := by
      simpa [S, Real.norm_eq_abs] using
        Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k => ‖M.canonicalFrozenClockTruncatedMartingale T i k records‖)
          hk
    have hsquare :
        (M.canonicalFrozenClockTruncatedMartingale T i k records) ^ 2 ≤ S ^ 2 := by
      rw [← sq_abs]
      exact sq_le_sq' (by
        nlinarith [hS_nonneg,
          abs_nonneg (M.canonicalFrozenClockTruncatedMartingale T i k records)]) habs_le
    simpa [S] using hsquare
  have hV_int : Integrable V μ := by
    refine hsumC_int.mono' hV_meas ?_
    refine ae_of_all _ fun records => ?_
    have hV_nonneg : 0 ≤ V records := by
      dsimp [V]
      exact sq_nonneg _ |>.trans
        (Finset.le_sup'
          (s := Finset.range (n + 1))
          (f := fun k => ‖M.frozenClockSkeletonVec T k records‖ ^ 2)
          (Finset.mem_range.mpr (Nat.succ_pos n)))
    have hsum_nonneg : 0 ≤ ∑ i : Fin d, C i records := by
      exact Finset.sum_nonneg fun i _ => by
        dsimp [C]
        exact sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hV_nonneg, abs_of_nonneg hsum_nonneg]
      using hpoint records
  have hmono :
      ∫ records, V records ∂μ ≤ ∫ records, (∑ i : Fin d, C i records) ∂μ :=
    integral_mono hV_int hsumC_int hpoint
  have hcalc :
      ∫ records, V records ∂μ ≤
        4 * ∑ i : Fin d, ∑ k ∈ Finset.range n,
          ∫ records,
            (let hist := Preorder.frestrictLe k records
             let x : Fin d → Fin (M.N + 1) :=
              QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) k hist
             M.instantCoordQVRate x i *
              min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
            ∂M.canonicalRecordMeasure x₀ := by
    calc
      ∫ records, V records ∂μ
          ≤ ∫ records, (∑ i : Fin d, C i records) ∂μ := hmono
      _ = ∑ i : Fin d, ∫ records, C i records ∂μ := by
            rw [integral_finsetSum]
            intro i _hi
            exact hC_int i
      _ ≤ ∑ i : Fin d, 4 * ∑ k ∈ Finset.range n,
          ∫ records,
            (let hist := Preorder.frestrictLe k records
             let x : Fin d → Fin (M.N + 1) :=
              QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) k hist
             M.instantCoordQVRate x i *
              min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
            ∂M.canonicalRecordMeasure x₀ := by
            exact Finset.sum_le_sum fun i _hi => by
              simpa [C, μ] using
                M.integral_canonicalFrozenClockTruncatedMartingale_sup_sq_le_sum_clockTruncatedCoordQV
                  x₀ T i n
      _ = 4 * ∑ i : Fin d, ∑ k ∈ Finset.range n,
          ∫ records,
            (let hist := Preorder.frestrictLe k records
             let x : Fin d → Fin (M.N + 1) :=
              QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) k hist
             M.instantCoordQVRate x i *
              min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
            ∂M.canonicalRecordMeasure x₀ := by
            rw [Finset.mul_sum]
  simpa [V, μ, frozenClockSkeletonVec] using hcalc

/-- Dimension-only vector form of the finite clock-skeleton Doob/QV estimate. -/
theorem integral_frozenClockTruncated_vector_sup_sq_le_vector_qv
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.frozenClockSkeletonVec T k records‖ ^ 2)
        ∂M.canonicalRecordMeasure x₀ ≤
      (4 * (Fintype.card (Fin d) : ℝ)) *
        M.frozenClockTruncatedQVIntegralSum x₀ T n := by
  let A : Fin d → ℕ → ℝ := fun i k =>
    ∫ records,
      (let hist := Preorder.frestrictLe k records
       let x : Fin d → Fin (M.N + 1) :=
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) k hist
       M.instantCoordQVRate x i *
        min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
      ∂M.canonicalRecordMeasure x₀
  let B : ℕ → ℝ := fun k =>
    ∫ records,
      (let hist := Preorder.frestrictLe k records
       let x : Fin d → Fin (M.N + 1) :=
        QMatrix.currentStateFromHistory
          (S := Fin d → Fin (M.N + 1)) k hist
       M.instantQVRate x *
        min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))
      ∂M.canonicalRecordMeasure x₀
  have hbase :
      ∫ records,
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖M.frozenClockSkeletonVec T k records‖ ^ 2)
          ∂M.canonicalRecordMeasure x₀ ≤
        4 * ∑ i : Fin d, ∑ k ∈ Finset.range n, A i k := by
    simpa [A] using
      M.integral_frozenClockTruncated_vector_sup_sq_le_coord_qv x₀ T n
  have hsum :
      (∑ i : Fin d, ∑ k ∈ Finset.range n, A i k) ≤
        (Fintype.card (Fin d) : ℝ) * ∑ k ∈ Finset.range n, B k := by
    calc
      (∑ i : Fin d, ∑ k ∈ Finset.range n, A i k)
          = ∑ k ∈ Finset.range n, ∑ i : Fin d, A i k := by
            rw [Finset.sum_comm]
      _ ≤ ∑ k ∈ Finset.range n, (Fintype.card (Fin d) : ℝ) * B k := by
            refine Finset.sum_le_sum ?_
            intro k hk
            simpa [A, B] using
              M.sum_clockTruncatedCoordQV_integral_le_card_mul_vector x₀ T k
      _ = (Fintype.card (Fin d) : ℝ) * ∑ k ∈ Finset.range n, B k := by
            rw [Finset.mul_sum]
  calc
    ∫ records,
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖M.frozenClockSkeletonVec T k records‖ ^ 2)
        ∂M.canonicalRecordMeasure x₀
        ≤ 4 * ∑ i : Fin d, ∑ k ∈ Finset.range n, A i k := hbase
    _ ≤ 4 * ((Fintype.card (Fin d) : ℝ) * ∑ k ∈ Finset.range n, B k) := by
          exact mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)
    _ = (4 * (Fintype.card (Fin d) : ℝ)) *
          M.frozenClockTruncatedQVIntegralSum x₀ T n := by
          simp [frozenClockTruncatedQVIntegralSum, B]
          ring

/-- Integral identity between the raw truncated vector jump-square sum and the
clock-truncated vector QV sum. -/
theorem integral_frozenTruncatedJumpSqSum_eq_clockTruncatedQV
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (n : ℕ) :
    ∫ records, M.frozenTruncatedJumpSqSum T n records
        ∂M.canonicalRecordMeasure x₀ =
      M.frozenClockTruncatedQVIntegralSum x₀ T n := by
  calc
    ∫ records, M.frozenTruncatedJumpSqSum T n records
        ∂M.canonicalRecordMeasure x₀
        =
      ∫ records,
        (∑ k ∈ Finset.range n,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist)))
        ∂M.canonicalRecordMeasure x₀ := by
          simpa [frozenTruncatedJumpSqSum] using
            (M.integral_sum_truncatedJumpSqIncrement_eq_sum_clockQVIntegral
              x₀ T n).trans
              (M.integral_sum_clockTruncatedQVIncrement_eq_sum_clockQVIntegral
                x₀ T n).symm
    _ = M.frozenClockTruncatedQVIntegralSum x₀ T n := by
          rw [integral_finsetSum]
          · simp [frozenClockTruncatedQVIntegralSum]
          · intro k _hk
            simpa using M.integrable_clockTruncatedQVIncrement x₀ T k

/-- Generic finite-clock landing theorem for the frozen Doob L2 argument.
The two hypotheses isolate the only clock-time work not contained in the
finite-index Doob/QV skeleton:

* `hAffineBridge` says the continuous clock-time supremum is controlled by the
  finite skeleton plus the truncated jump-square sum.
* `hClockQV` compares that finite clock-QV sum with the desired QV time
  integral.

Both assumptions are system-independent in shape.  Concrete systems discharge
them either by a deterministic finite jump bound, or by a stopped/random-index
limit argument. -/
theorem frozenMartingalePart_DoobL2_general
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (hT : 0 < T) (n : ℕ)
    (hAffineBridge :
      (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2)
        ≤ᵐ[M.canonicalRecordMeasure x₀]
      fun records =>
        (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
          4 * M.frozenTruncatedJumpSqSum T n records)
    (hClockQV :
      M.frozenClockTruncatedQVIntegralSum x₀ T n ≤
        ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
          ∂M.canonicalRecordMeasure x₀) :
    ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      frozenMartingalePartDoobL2Constant d *
        ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
          ∂M.canonicalRecordMeasure x₀ := by
  let μ := M.canonicalRecordMeasure x₀
  let F : M.canonicalRecordΩ → ℝ := fun records =>
    ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
  let A : M.canonicalRecordΩ → ℝ := fun records =>
    M.frozenClockSkeletonSupSq T n records
  let J : M.canonicalRecordΩ → ℝ := fun records =>
    M.frozenTruncatedJumpSqSum T n records
  let Q : ℝ := M.frozenClockTruncatedQVIntegralSum x₀ T n
  let R : ℝ :=
    ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)) ∂μ
  have hF_int : Integrable F μ := by
    simpa [F, μ] using
      M.canonical_frozen_martingale_sup_sq_integrable x₀ T hT
  have hA_int : Integrable A μ := by
    simpa [A, μ] using
      M.integrable_frozenClockSkeletonSupSq x₀ T n
  have hJ_int : Integrable J μ := by
    dsimp [J, frozenTruncatedJumpSqSum]
    exact integrable_finsetSum (Finset.range n) fun k _hk => by
      simpa using M.integrable_truncatedJumpSqIncrementFromHistory_next x₀ T k
  have hBridge_int :
      Integrable
        (fun records : M.canonicalRecordΩ =>
          (4 / 3 : ℝ) * A records + 4 * J records) μ :=
    (hA_int.const_mul (4 / 3 : ℝ)).add (hJ_int.const_mul 4)
  have hmono :
      ∫ records, F records ∂μ ≤
        ∫ records, ((4 / 3 : ℝ) * A records + 4 * J records) ∂μ :=
    integral_mono_ae hF_int hBridge_int (by simpa [F, A, J] using hAffineBridge)
  have hA_le :
      ∫ records, A records ∂μ ≤
        (4 * (Fintype.card (Fin d) : ℝ)) * Q := by
    simpa [A, Q, μ] using
      M.integral_frozenClockTruncated_vector_sup_sq_le_vector_qv x₀ T n
  have hJ_eq :
      ∫ records, J records ∂μ = Q := by
    simpa [J, Q, μ] using
      M.integral_frozenTruncatedJumpSqSum_eq_clockTruncatedQV x₀ T n
  have hQ_le_R : Q ≤ R := by
    simpa [Q, R, μ] using hClockQV
  calc
    ∫ records, F records ∂μ
        ≤ ∫ records, ((4 / 3 : ℝ) * A records + 4 * J records) ∂μ := hmono
    _ = (4 / 3 : ℝ) * ∫ records, A records ∂μ +
          4 * ∫ records, J records ∂μ := by
          rw [integral_add]
          · rw [integral_const_mul, integral_const_mul]
          · exact hA_int.const_mul (4 / 3 : ℝ)
          · exact hJ_int.const_mul 4
    _ ≤ (4 / 3 : ℝ) * ((4 * (Fintype.card (Fin d) : ℝ)) * Q) + 4 * Q := by
          have hmulA := mul_le_mul_of_nonneg_left hA_le
            (by norm_num : (0 : ℝ) ≤ 4 / 3)
          rw [hJ_eq]
          nlinarith
    _ = frozenMartingalePartDoobL2Constant d * Q := by
          unfold frozenMartingalePartDoobL2Constant
          ring
    _ ≤ frozenMartingalePartDoobL2Constant d * R := by
          exact mul_le_mul_of_nonneg_left hQ_le_R
            (le_of_lt (frozenMartingalePartDoobL2Constant_pos d))
    _ = frozenMartingalePartDoobL2Constant d *
        ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
          ∂M.canonicalRecordMeasure x₀ := by
          simp [R, μ]

/-- Finite-horizon vector supremum of the frozen martingale residual is bounded
by the sum of coordinate finite-horizon suprema. -/
theorem frozenMartingalePart_timeSup_norm_sq_le_sum_coord_timeSup_sq
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart pathMap s ω‖ ^ 2) ≤
      ∑ i, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        (M.frozenMartingalePart pathMap s ω i) ^ 2 := by
  exact Ripple.Kurtz.vector_timeSup_norm_sq_le_sum_coord_timeSup_sq
    (fun s => M.frozenMartingalePart pathMap s ω) hT
    (by
      obtain ⟨C, _hC, hbound⟩ :=
        M.exists_frozenMartingalePart_norm_bound pathMap T hT
      exact ⟨C, fun s hs0 hsT => hbound s ω hs0 hsT⟩)

/-- Per-horizon frozen martingale QV-style bound, with the same crude
deterministic-bound proof used for the non-frozen martingale in
`RandomIndexDoob.lean`.  The constant is allowed to depend on the fixed CTMC
`M` and on the horizon `T`, matching the current `DensityProcess` interface. -/
theorem canonical_frozen_martingale_qv_bound_uniform
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    ∀ T > 0, ∃ C > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤ C * T / M.N := by
  intro T hT
  obtain ⟨K, _hK, hbound⟩ :=
    M.exists_frozen_martingale_sup_sq_bound M.canonicalPathMap T (le_of_lt hT)
  have hNpos : (0 : ℝ) < M.N := Nat.cast_pos.mpr M.hN
  refine ⟨K * M.N / T + 1, by positivity, ?_⟩
  calc
    ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀
        ≤ ∫ _records, K ∂M.canonicalRecordMeasure x₀ := by
          exact integral_mono_ae
            (M.canonical_frozen_martingale_sup_sq_integrable x₀ T hT)
            (integrable_const K)
            (ae_of_all _ fun records => hbound records)
    _ = K := by simp
    _ ≤ (K * M.N / T + 1) * T / M.N := by
          have hT_ne : T ≠ 0 := ne_of_gt hT
          have hN_ne : (M.N : ℝ) ≠ 0 := ne_of_gt hNpos
          field_simp
          nlinarith [mul_pos hT hNpos]

/-- A single raw truncated jump-square increment is nonnegative. -/
theorem truncatedJumpSqIncrementFromHistory_nonneg
    (M : DensityDepCTMC d) (T : ℝ) (records : M.canonicalRecordΩ)
    (k : ℕ) :
    0 ≤ M.truncatedJumpSqIncrementFromHistory T k
      (Preorder.frestrictLe k records) (records (k + 1)) := by
  unfold truncatedJumpSqIncrementFromHistory
  by_cases hmem :
      (records (k + 1)).1 ∈
        Set.Iic (QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records))
  · rw [Set.indicator_of_mem hmem]
    exact mul_nonneg zero_le_one (sq_nonneg _)
  · rw [Set.indicator_of_notMem hmem]
    simp

/-- The finite frozen clock skeleton supremum is monotone in the embedded
clock cutoff. -/
theorem frozenClockSkeletonSupSq_mono
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ)
    (records : M.canonicalRecordΩ) :
    M.frozenClockSkeletonSupSq T n records ≤
      M.frozenClockSkeletonSupSq T (n + 1) records := by
  classical
  unfold frozenClockSkeletonSupSq
  let f : ℕ → ℝ := fun k => ‖M.frozenClockSkeletonVec T k records‖ ^ 2
  have hsub : Finset.range (n + 1) ⊆ Finset.range (n + 1 + 1) := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hk))
  have hmono :=
    Finset.sup'_mono (f := f) hsub Finset.nonempty_range_add_one
  simpa [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmono

/-- The finite frozen truncated jump-square sum is monotone in the embedded
clock cutoff. -/
theorem frozenTruncatedJumpSqSum_mono
    (M : DensityDepCTMC d) (T : ℝ) (n : ℕ)
    (records : M.canonicalRecordΩ) :
    M.frozenTruncatedJumpSqSum T n records ≤
      M.frozenTruncatedJumpSqSum T (n + 1) records := by
  classical
  unfold frozenTruncatedJumpSqSum
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right
    (M.truncatedJumpSqIncrementFromHistory_nonneg T records n)

/-- Canonical-path current history agrees with the clock-tail state sequence. -/
theorem canonicalClockTail_currentState_eq_stateSeq
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (k : ℕ) :
    QMatrix.currentStateFromHistory
        (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records) =
      (M.canonicalPathMap records).stateSeq k := by
  simpa [canonicalPathMap] using
    (QMatrix.currentStateFromHistory_frestrictLe
      (S := Fin d → Fin (M.N + 1)) records k)

/-- Canonical-path sojourn time is the holding time stored in the next record. -/
theorem canonicalClockTail_sojournTime_eq_record
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (k : ℕ) :
    (M.canonicalPathMap records).sojournTime k = (records (k + 1)).1 := by
  simpa [canonicalPathMap] using
    (QMatrix.recordTrajectoryToPath_sojournTime
      (S := Fin d → Fin (M.N + 1)) records k)

/-- Pure finite-sum comparison: adding a nonnegative tail and a zero eventual
tail can only increase a finite prefix. -/
theorem sum_range_le_prefix_of_nonneg_zero_tail
    {f : ℕ → ℝ} (n a : ℕ)
    (hnonneg : ∀ k, 0 ≤ f k)
    (hzero_tail : ∀ k, a ≤ k → f k = 0) :
    (∑ k ∈ Finset.range n, f k) ≤ ∑ k ∈ Finset.range a, f k := by
  classical
  by_cases hna : n ≤ a
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro k hk
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hna))
      (by
        intro k _hk _hnot
        exact hnonneg k)
  · have han : a ≤ n := le_of_not_ge hna
    have hsplit :
        (∑ k ∈ Finset.range n, f k) =
          ∑ k ∈ (Finset.range n).filter (fun k => k < a), f k := by
      symm
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro k _hk
      by_cases hka : k < a
      · simp [hka]
      · have hak : a ≤ k := le_of_not_gt hka
        simp [hka, hzero_tail k hak]
    have hfilter :
        (Finset.range n).filter (fun k => k < a) = Finset.range a := by
      ext k
      constructor
      · intro hk
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
      · intro hk
        have hka : k < a := Finset.mem_range.mp hk
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (lt_of_lt_of_le hka han), hka⟩
    rw [hsplit, hfilter]

/-- Strict completion of a finite CTMC prefix.  It preserves all states and the
clock data through index `n`, and then appends unit-spaced artificial times. -/
noncomputable def strictCompletionThrough
    {S : Type*} (path : CTMCPath S) (n : ℕ) : CTMCPath S where
  init := path.init
  jumps := fun k => path.jumps k
  times := fun k => if hk : k ≤ n then path.times k else path.times n + (k - n : ℝ)

theorem strictCompletionThrough_stateSeq_eq
    {S : Type*} (path : CTMCPath S) (n m : ℕ) :
    (strictCompletionThrough path n).stateSeq m = path.stateSeq m := by
  cases m <;> rfl

theorem strictCompletionThrough_sojournStart_eq_of_le
    {S : Type*} (path : CTMCPath S) (n m : ℕ) (hm : m ≤ n) :
    (strictCompletionThrough path n).sojournStart m =
      path.sojournStart m := by
  cases m with
  | zero => rfl
  | succ m =>
      have hm' : m ≤ n := Nat.le_of_succ_le hm
      simp [strictCompletionThrough, hm']

theorem strictCompletionThrough_sojournStart_succ_eq
    {S : Type*} (path : CTMCPath S) (n : ℕ) :
    (strictCompletionThrough path n).sojournStart (n + 1) =
      path.sojournStart (n + 1) := by
  simp [CTMCPath.sojournStart, strictCompletionThrough]

theorem strictCompletionThrough_sojournTime_eq_of_le
    {S : Type*} (path : CTMCPath S) {n m : ℕ} (hm : m ≤ n) :
    (strictCompletionThrough path n).sojournTime m =
      path.sojournTime m := by
  cases m with
  | zero =>
      have hn : 0 ≤ n := Nat.zero_le n
      simp [CTMCPath.sojournTime, strictCompletionThrough, hn]
  | succ m =>
      have hm_le : m ≤ n := by omega
      have hms_le : m + 1 ≤ n := hm
      simp [CTMCPath.sojournTime, strictCompletionThrough, hm_le, hms_le]

theorem strictCompletionThrough_strict
    {S : Type*} (path : CTMCPath S) (n : ℕ)
    (hpos0 : 0 < path.times 0)
    (hstrict_prefix : ∀ k < n, path.times k < path.times (k + 1)) :
    0 < (strictCompletionThrough path n).times 0 ∧
      ∀ k,
        (strictCompletionThrough path n).times k <
          (strictCompletionThrough path n).times (k + 1) := by
  constructor
  · simp [strictCompletionThrough, hpos0]
  · intro k
    by_cases hk1 : k + 1 ≤ n
    · have hk : k ≤ n := Nat.le_trans (Nat.le_succ k) hk1
      have hklt : k < n := Nat.lt_of_succ_le hk1
      simpa [strictCompletionThrough, hk, hk1] using hstrict_prefix k hklt
    · by_cases hk : k ≤ n
      · have hkeq : k = n := by
          have hnlt : ¬ k < n := by
            simpa [Nat.succ_le_iff] using hk1
          exact le_antisymm hk (Nat.le_of_not_gt hnlt)
        subst k
        simp [strictCompletionThrough]
      · have hsub_succ : (k + 1 - n : ℕ) = (k - n) + 1 := by omega
        simp [strictCompletionThrough, hk, hk1, hsub_succ]

theorem strictCompletionThrough_frozenStateAt_eq_of_lt_succ
    {S : Type*} (path : CTMCPath S) (n : ℕ) {t : ℝ}
    (ht : t < path.sojournStart (n + 1)) :
    (strictCompletionThrough path n).frozenStateAt t = path.frozenStateAt t := by
  classical
  let path' := strictCompletionThrough path n
  have ht_time : t < path.times n := by
    simpa [CTMCPath.sojournStart] using ht
  let hex : ∃ m : ℕ, t < path.times m := ⟨n, ht_time⟩
  let m : ℕ := Nat.find hex
  have hm_le_n : m ≤ n := by
    simpa [m, hex] using Nat.find_min' hex ht_time
  have hm_time : t < path.times m := by
    simpa [m, hex] using Nat.find_spec hex
  have hm_time' : t < path'.times m := by
    simpa [path', strictCompletionThrough, hm_le_n] using hm_time
  have hmin : ∀ j ∈ Finset.range m, ¬ t < path.times j := by
    intro j hj
    exact Nat.find_min hex (Finset.mem_range.mp hj)
  have hmin' : ∀ j ∈ Finset.range m, ¬ t < path'.times j := by
    intro j hj htj
    have hj_le_n : j ≤ n := le_trans (le_of_lt (Finset.mem_range.mp hj)) hm_le_n
    have htj_path : t < path.times j := by
      simpa [path', strictCompletionThrough, hj_le_n] using htj
    exact hmin j hj htj_path
  have hstate' :
      path'.frozenStateAt t = path'.stateSeq m :=
    path'.frozenStateAt_eq_stateSeq_of_first_time_gt t m hm_time' hmin'
  have hstate :
      path.frozenStateAt t = path.stateSeq m :=
    path.frozenStateAt_eq_stateSeq_of_first_time_gt t m hm_time hmin
  rw [hstate', hstate, strictCompletionThrough_stateSeq_eq]

/-- On a strict path with a future jump after `T`, the frozen QV clock sum
through `jumpCount T + 1` is exactly the frozen QV integral over `[0,T]`. -/
theorem frozenClockTruncatedQV_sum_jumpCount_succ_eq_setIntegral
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n) :
    (∑ k ∈ Finset.range (path.jumpCount T + 1),
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k))) =
      ∫ t in Set.Icc (0 : ℝ) T,
        M.instantQVRate (path.frozenStateAt t) := by
  classical
  let j := path.jumpCount T
  let F : (Fin d → Fin (M.N + 1)) → ℝ := fun x => M.instantQVRate x
  have hcompleted :
      (∑ k ∈ Finset.range j,
          M.instantQVRate (path.stateSeq k) *
            min (path.sojournTime k) (max 0 (T - path.sojournStart k))) =
        ∑ k ∈ Finset.range j,
          M.instantQVRate (path.stateSeq k) * path.sojournTime k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < j := Finset.mem_range.mp hk
    have hend : path.sojournEnd k ≤ T := by
      simpa [CTMCPath.sojournEnd, j] using
        path.times_le_of_lt_jumpCount hfuture hklt
    have hstart_le_end : path.sojournStart k ≤ path.sojournEnd k := by
      simpa [CTMCPath.sojournTime, sub_nonneg] using
        path.sojournTime_nonneg hstrict hpos k
    have hT_start_nonneg : 0 ≤ T - path.sojournStart k := by
      linarith
    have hsoj_le :
        path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
      rw [max_eq_right hT_start_nonneg]
      simp only [CTMCPath.sojournTime]
      linarith
    rw [min_eq_left hsoj_le]
  have hstart_j_le : path.sojournStart j ≤ T := by
    simpa [j] using path.sojournStart_jumpCount_le_of_exists hT hfuture
  have helapsed_nonneg : 0 ≤ T - path.sojournStart j := by
    linarith
  have hclock_j :
      max 0 (T - path.sojournStart j) = path.currentSojournElapsed T := by
    simp [CTMCPath.currentSojournElapsed, j, max_eq_right helapsed_nonneg]
  have hcur_le :
      path.currentSojournElapsed T ≤ path.sojournTime j :=
    path.currentSojournElapsed_le_sojournTime hfuture
  have hmin_cur :
      min (path.sojournTime j) (max 0 (T - path.sojournStart j)) =
        path.currentSojournElapsed T := by
    rw [hclock_j]
    exact min_eq_right hcur_le
  have hclock :=
    M.frozen_sum_observable_mul_sojournTime_add_currentSojourn_eq_setIntegral
      path hstrict hpos F hT hfuture
  calc
    (∑ k ∈ Finset.range (path.jumpCount T + 1),
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k)))
        =
      (∑ k ∈ Finset.range j,
          M.instantQVRate (path.stateSeq k) *
            min (path.sojournTime k) (max 0 (T - path.sojournStart k))) +
        M.instantQVRate (path.stateSeq j) *
          min (path.sojournTime j) (max 0 (T - path.sojournStart j)) := by
          simp [j, Finset.sum_range_succ]
    _ =
      (∑ k ∈ Finset.range j,
          M.instantQVRate (path.stateSeq k) * path.sojournTime k) +
        M.instantQVRate (path.stateSeq j) *
          path.currentSojournElapsed T := by
          rw [hcompleted, hmin_cur]
    _ =
      (∑ k ∈ Finset.range (path.jumpCount T),
          F (path.stateSeq k) * path.sojournTime k) +
        F (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T := by
          simp [F, j]
    _ = ∫ t in Set.Icc (0 : ℝ) T,
        M.instantQVRate (path.frozenStateAt t) := by
          simpa [F] using hclock

/-- On a strict path with a future jump after `T`, every finite frozen QV
clock prefix is bounded by the frozen QV integral over `[0,T]`. -/
theorem frozenClockTruncatedQV_sum_range_le_setIntegral
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k))) ≤
      ∫ t in Set.Icc (0 : ℝ) T,
        M.instantQVRate (path.frozenStateAt t) := by
  classical
  let j := path.jumpCount T
  let f : ℕ → ℝ := fun k =>
    M.instantQVRate (path.stateSeq k) *
      min (path.sojournTime k) (max 0 (T - path.sojournStart k))
  have hnonneg : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    exact mul_nonneg (M.instantQVRate_nonneg _)
      (le_min (path.sojournTime_nonneg hstrict hpos k) (le_max_left _ _))
  have hzero_tail : ∀ k, j + 1 ≤ k → f k = 0 := by
    intro k hk
    have hj_lt_k : j < k := Nat.lt_of_succ_le hk
    have hT_lt_start : T < path.sojournStart k := by
      have hT_lt_end_j : T < path.sojournEnd j := by
        simpa [CTMCPath.sojournEnd, j] using
          path.lt_times_jumpCount_of_exists hfuture
      have hend_le_start :
          path.sojournEnd j ≤ path.sojournStart k :=
        path.sojournEnd_le_sojournStart_of_lt hstrict hj_lt_k
      exact lt_of_lt_of_le hT_lt_end_j hend_le_start
    have hrem_nonpos : T - path.sojournStart k ≤ 0 := by linarith
    have hmax : max 0 (T - path.sojournStart k) = 0 :=
      max_eq_left hrem_nonpos
    have hmin : min (path.sojournTime k) (max 0 (T - path.sojournStart k)) = 0 := by
      rw [hmax]
      exact min_eq_right (path.sojournTime_nonneg hstrict hpos k)
    simp [f, hmin]
  have hprefix :
      (∑ k ∈ Finset.range n, f k) ≤
        ∑ k ∈ Finset.range (j + 1), f k :=
    sum_range_le_prefix_of_nonneg_zero_tail n (j + 1) hnonneg hzero_tail
  have hfull :
      (∑ k ∈ Finset.range (j + 1), f k) =
        ∫ t in Set.Icc (0 : ℝ) T,
          M.instantQVRate (path.frozenStateAt t) := by
    simpa [f, j] using
      M.frozenClockTruncatedQV_sum_jumpCount_succ_eq_setIntegral
        path hstrict hpos hT hfuture
  exact hprefix.trans_eq hfull

set_option maxHeartbeats 800000 in
/-- If a canonical path has a positive `k`-th sojourn, then all earlier
sojourn boundaries are strictly ordered.  This is generic; the hypotheses are
the standard a.e. canonical-record regularity facts for absorbing chains. -/
theorem canonical_positive_sojourn_prefix_strict
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ)
    (hhold_pos : ∀ n,
      ¬M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1)
    (hstate_abs : ∀ n,
      M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 =
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records))
    (hhold_zero : ∀ n,
      M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).1 = 0)
    {k : ℕ} (hkpos : 0 < (M.canonicalPathMap records).sojournTime k) :
    0 < (M.canonicalPathMap records).times 0 ∧
      ∀ m < k,
        (M.canonicalPathMap records).times m <
          (M.canonicalPathMap records).times (m + 1) := by
  classical
  let path := M.canonicalPathMap records
  have hstate_abs_path : ∀ n,
      M.toQMatrix.IsAbsorbing (path.stateSeq n) →
        path.stateSeq (n + 1) = path.stateSeq n := by
    intro n hn
    have h := hstate_abs n (by
      simpa [path, DensityDepCTMC.canonicalPathMap,
        QMatrix.currentStateFromHistory_frestrictLe] using hn)
    simpa [path, DensityDepCTMC.canonicalPathMap,
      QMatrix.recordTrajectoryToPath_stateSeq,
      QMatrix.currentStateFromHistory_frestrictLe] using h
  have hhold_zero_path : ∀ n,
      M.toQMatrix.IsAbsorbing (path.stateSeq n) →
        path.sojournTime n = 0 := by
    intro n hn
    have h := hhold_zero n (by
      simpa [path, DensityDepCTMC.canonicalPathMap,
        QMatrix.currentStateFromHistory_frestrictLe] using hn)
    simpa [path, DensityDepCTMC.canonicalPathMap,
      QMatrix.recordTrajectoryToPath_sojournTime] using h
  have hsoj_pos_of_le : ∀ j ≤ k, 0 < path.sojournTime j := by
    intro j hjk
    by_contra hnot
    have habs_j : M.toQMatrix.IsAbsorbing (path.stateSeq j) := by
      by_contra hnon
      have hp := hhold_pos j (by
        simpa [path, DensityDepCTMC.canonicalPathMap,
          QMatrix.currentStateFromHistory_frestrictLe] using hnon)
      have hp_path : 0 < path.sojournTime j := by
        simpa [path, DensityDepCTMC.canonicalPathMap,
          QMatrix.recordTrajectoryToPath_sojournTime] using hp
      exact hnot hp_path
    have hconst_ge : ∀ n, j ≤ n → path.stateSeq n = path.stateSeq j := by
      intro n hjn
      induction n with
      | zero =>
          have hj0 : j = 0 := Nat.eq_zero_of_le_zero hjn
          subst j
          rfl
      | succ n ih =>
          by_cases hle : j ≤ n
          · have ihn := ih hle
            have habs_n : M.toQMatrix.IsAbsorbing (path.stateSeq n) := by
              simpa [ihn] using habs_j
            simpa [ihn] using hstate_abs_path n habs_n
          · have hj : j = n + 1 := by omega
            subst j
            rfl
    have hconst : path.stateSeq k = path.stateSeq j := hconst_ge k hjk
    have habs_k : M.toQMatrix.IsAbsorbing (path.stateSeq k) := by
      simpa [hconst] using habs_j
    have hzero_k := hhold_zero_path k habs_k
    exact (ne_of_gt hkpos) hzero_k
  constructor
  · have h0 := hsoj_pos_of_le 0 (Nat.zero_le k)
    simpa [path, CTMCPath.sojournTime] using h0
  · intro m hm
    have hsucc : 0 < path.sojournTime (m + 1) :=
      hsoj_pos_of_le (m + 1) (Nat.succ_le_of_lt hm)
    simpa [path, CTMCPath.sojournTime] using hsucc

/-- Along a fixed canonical record, the frozen instantaneous vector-QV rate is
integrable on every compact time interval. -/
theorem integrableOn_canonicalFrozenInstantQVRate_Icc
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (T : ℝ) :
    IntegrableOn
      (fun s : ℝ =>
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
      (Set.Icc (0 : ℝ) T) volume := by
  obtain ⟨C, hC_pos, hC⟩ := M.exists_instantQVRate_bound
  have hCN_nonneg : 0 ≤ C / (M.N : ℝ) := by positivity
  let f : ℝ → ℝ := fun s =>
    M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
  have hmeas : Measurable f := by
    have hpair : Measurable (fun s : ℝ => (s, records)) :=
      Measurable.prodMk measurable_id measurable_const
    have hstate : Measurable (fun s : ℝ =>
        (M.canonicalPathMap records).frozenStateAt s) :=
      M.measurable_prod_canonicalPathMap_frozenStateAt.comp hpair
    change Measurable (fun s : ℝ =>
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
    exact (Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.instantQVRate x)).comp hstate
  refine IntegrableOn.of_bound measure_Icc_lt_top
    hmeas.aestronglyMeasurable (C / (M.N : ℝ)) ?_
  filter_upwards with s
  rw [Real.norm_eq_abs]
  refine abs_le.mpr
    ⟨(neg_nonpos.mpr hCN_nonneg).trans (M.instantQVRate_nonneg _), ?_⟩
  exact hC ((M.canonicalPathMap records).frozenStateAt s)

/-- Joint measurability of the frozen instantaneous vector-QV rate. -/
theorem measurable_prod_canonicalFrozenInstantQVRate
    (M : DensityDepCTMC d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      M.instantQVRate ((M.canonicalPathMap p.2).frozenStateAt p.1)) := by
  exact (Measurable.of_discrete
    (f := fun x : Fin d → Fin (M.N + 1) => M.instantQVRate x)).comp
      M.measurable_prod_canonicalPathMap_frozenStateAt

/-- Measurability in records of the finite-horizon frozen QV time integral. -/
theorem measurable_canonicalFrozenInstantQVRate_setIntegral
    (M : DensityDepCTMC d) (T : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)) := by
  have hjoint : StronglyMeasurable
      (fun p : M.canonicalRecordΩ × ℝ =>
        M.instantQVRate ((M.canonicalPathMap p.1).frozenStateAt p.2)) :=
    (M.measurable_prod_canonicalFrozenInstantQVRate.comp
      measurable_swap).stronglyMeasurable
  exact (hjoint.integral_prod_right'
    (ν := MeasureTheory.Measure.restrict volume (Set.Icc 0 T))).measurable

/-- The frozen instantaneous-QV time integral is nonnegative pathwise. -/
theorem canonical_frozenInstantQVRate_setIntegral_nonneg
    (M : DensityDepCTMC d) (T : ℝ) (records : M.canonicalRecordΩ) :
    0 ≤ ∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
  exact setIntegral_nonneg measurableSet_Icc fun _ _ =>
    M.instantQVRate_nonneg _

/-- The finite-horizon frozen instantaneous-QV time integral is integrable
under the canonical record law. -/
theorem integrable_canonicalFrozenInstantQVRate_setIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (hT : 0 ≤ T) :
    Integrable
      (fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨C, _hC_pos, hC⟩ := M.exists_instantQVRate_bound
  let B : ℝ := C / (M.N : ℝ) * T
  refine MeasureTheory.Integrable.of_bound
    (M.measurable_canonicalFrozenInstantQVRate_setIntegral T).aestronglyMeasurable
    B ?_
  filter_upwards with records
  have hvol : volume.real (Set.Icc (0 : ℝ) T) = T := by
    rw [Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 0)]
    ring
  have hnorm :
      ‖∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)‖ ≤
        (C / (M.N : ℝ)) * volume.real (Set.Icc (0 : ℝ) T) := by
    refine norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Set.Icc (0 : ℝ) T)
      (f := fun s : ℝ =>
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
      measure_Icc_lt_top ?_
    intro s _hs
    rw [Real.norm_eq_abs]
    refine abs_le.mpr ⟨?_, hC ((M.canonicalPathMap records).frozenStateAt s)⟩
    have hCN_nonneg : 0 ≤ C / (M.N : ℝ) := by positivity
    exact (neg_nonpos.mpr hCN_nonneg).trans (M.instantQVRate_nonneg _)
  simpa [B, hvol] using hnorm

/-- The frozen instantaneous-QV set integral is monotone in the right endpoint. -/
theorem frozenInstantQVRate_setIntegral_mono_Icc
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ)
    {T' T : ℝ} (hle : T' ≤ T) :
    ∫ s in Set.Icc (0 : ℝ) T',
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) ≤
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
  have hsubset : Set.Icc (0 : ℝ) T' ⊆ Set.Icc (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 hle⟩
  have hU_ae : Set.Icc (0 : ℝ) T' ≤ᵐ[volume] Set.Icc (0 : ℝ) T :=
    Filter.Eventually.of_forall fun s hs => hsubset hs
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
        fun s => M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) :=
    Filter.Eventually.of_forall fun _ => M.instantQVRate_nonneg _
  exact setIntegral_mono_set
    (M.integrableOn_canonicalFrozenInstantQVRate_Icc records T)
    hnonneg hU_ae

/-- Strict completion does not change the frozen-QV integral before the next
unmodified sojourn boundary, up to the irrelevant endpoint. -/
theorem strictCompletionThrough_setIntegral_frozenQV_eq_of_le_succ
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1))) (n : ℕ)
    {T : ℝ} (_hT0 : 0 ≤ T) (hT_le : T ≤ path.sojournStart (n + 1)) :
    ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((strictCompletionThrough path n).frozenStateAt s) =
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate (path.frozenStateAt s) := by
  let path' := strictCompletionThrough path n
  have hIcoIcc : Set.Ico (0 : ℝ) T =ᵐ[volume] Set.Icc (0 : ℝ) T :=
    Ico_ae_eq_Icc' (by simp)
  calc
    ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate (path'.frozenStateAt s)
        = ∫ s in Set.Ico (0 : ℝ) T,
            M.instantQVRate (path'.frozenStateAt s) := by
          exact setIntegral_congr_set hIcoIcc.symm
    _ = ∫ s in Set.Ico (0 : ℝ) T,
            M.instantQVRate (path.frozenStateAt s) := by
          apply setIntegral_congr_fun measurableSet_Ico
          intro s hs
          have hs_lt : s < path.sojournStart (n + 1) :=
            lt_of_lt_of_le hs.2 hT_le
          have hstate : path'.frozenStateAt s = path.frozenStateAt s := by
            simpa [path'] using
              strictCompletionThrough_frozenStateAt_eq_of_lt_succ path n hs_lt
          simp [hstate]
    _ = ∫ s in Set.Icc (0 : ℝ) T,
            M.instantQVRate (path.frozenStateAt s) := by
          exact setIntegral_congr_set hIcoIcc

set_option maxHeartbeats 0 in
/-- Pathwise finite-prefix QV comparison for canonical absorbing trajectories. -/
theorem frozenClockTruncatedQV_sum_canonical_le_setIntegral
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ)
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hhold_pos : ∀ m,
      ¬M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) m (Preorder.frestrictLe m records)) →
        0 < (records (m + 1)).1)
    (hstate_abs : ∀ m,
      M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) m (Preorder.frestrictLe m records)) →
        (records (m + 1)).2 =
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) m (Preorder.frestrictLe m records))
    (hhold_zero : ∀ m,
      M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) m (Preorder.frestrictLe m records)) →
        (records (m + 1)).1 = 0)
    (hnext_ne : ∀ m,
      ¬M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) m (Preorder.frestrictLe m records)) →
        (records (m + 1)).2 ≠
          QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) m (Preorder.frestrictLe m records)) :
    (∑ k ∈ Finset.range n,
        M.instantQVRate ((M.canonicalPathMap records).stateSeq k) *
          min ((M.canonicalPathMap records).sojournTime k)
            (max 0 (T - (M.canonicalPathMap records).sojournStart k))) ≤
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
  classical
  let path := M.canonicalPathMap records
  have hstate_abs_path : ∀ m,
      M.toQMatrix.IsAbsorbing (path.stateSeq m) →
        path.stateSeq (m + 1) = path.stateSeq m := by
    intro m hm
    have h := hstate_abs m (by
      simpa [path, DensityDepCTMC.canonicalPathMap,
        QMatrix.currentStateFromHistory_frestrictLe] using hm)
    simpa [path, DensityDepCTMC.canonicalPathMap,
      QMatrix.recordTrajectoryToPath_stateSeq,
      QMatrix.currentStateFromHistory_frestrictLe] using h
  have hhold_zero_path : ∀ m,
      M.toQMatrix.IsAbsorbing (path.stateSeq m) →
        path.sojournTime m = 0 := by
    intro m hm
    have h := hhold_zero m (by
      simpa [path, DensityDepCTMC.canonicalPathMap,
        QMatrix.currentStateFromHistory_frestrictLe] using hm)
    simpa [path, DensityDepCTMC.canonicalPathMap,
      QMatrix.recordTrajectoryToPath_sojournTime] using h
  by_cases hAbs : ∃ a, a < n ∧ M.toQMatrix.IsAbsorbing (path.stateSeq a)
  · let a : ℕ := Nat.find hAbs
    have ha_spec : a < n ∧ M.toQMatrix.IsAbsorbing (path.stateSeq a) := by
      simpa [a] using Nat.find_spec hAbs
    have ha_lt_n : a < n := ha_spec.1
    have ha_le_n : a ≤ n := le_of_lt ha_lt_n
    have haAbs : M.toQMatrix.IsAbsorbing (path.stateSeq a) := ha_spec.2
    have hnot_before : ∀ k, k < a →
        ¬M.toQMatrix.IsAbsorbing (path.stateSeq k) := by
      intro k hk hkAbs
      exact (Nat.find_min hAbs hk) ⟨lt_trans hk ha_lt_n, hkAbs⟩
    have hstate_tail : ∀ k, a ≤ k → path.stateSeq k = path.stateSeq a := by
      intro k hak
      induction k with
      | zero =>
          have ha0 : a = 0 := Nat.eq_zero_of_le_zero hak
          rw [ha0]
      | succ k ih =>
          by_cases hle : a ≤ k
          · have ihk := ih hle
            have habs_k : M.toQMatrix.IsAbsorbing (path.stateSeq k) := by
              simpa [ihk] using haAbs
            simpa [ihk] using hstate_abs_path k habs_k
          · have ha_eq : a = k + 1 := by omega
            rw [ha_eq]
    have hhold_zero_tail : ∀ k, a ≤ k → path.sojournTime k = 0 := by
      intro k hak
      have hstate_k : path.stateSeq k = path.stateSeq a := hstate_tail k hak
      exact hhold_zero_path k (by simpa [hstate_k] using haAbs)
    have hqv_zero : ∀ k, a ≤ k → M.instantQVRate (path.stateSeq k) = 0 := by
      intro k hak
      have hstate_k : path.stateSeq k = path.stateSeq a := hstate_tail k hak
      rw [hstate_k]
      exact M.instantQVRate_eq_zero_of_exitRateAt_zero
        (by simpa [DensityDepCTMC.exitRateAt] using haAbs)
    have hsum_split :
        (∑ k ∈ Finset.range n,
          M.instantQVRate (path.stateSeq k) *
            min (path.sojournTime k) (max 0 (T - path.sojournStart k))) =
        ∑ k ∈ Finset.range a,
          M.instantQVRate (path.stateSeq k) *
            min (path.sojournTime k) (max 0 (T - path.sojournStart k)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono ha_le_n)
      intro k _hkN hka
      have hak : a ≤ k := Nat.le_of_not_gt (by
        intro hklt
        exact hka (Finset.mem_range.mpr hklt))
      simp [hqv_zero k hak]
    rw [hsum_split]
    by_cases ha0 : a = 0
    · simp [ha0]
      exact setIntegral_nonneg measurableSet_Icc fun _ _ =>
        M.instantQVRate_nonneg _
    · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
      let liveLast : ℕ := a - 1
      have hlive_succ : liveLast + 1 = a := Nat.succ_pred_eq_of_pos ha_pos
      have hlive_lt_a : liveLast < a := by omega
      have hlive_soj_pos : 0 < path.sojournTime liveLast := by
        rw [M.canonicalClockTail_sojournTime_eq_record records liveLast]
        exact hhold_pos liveLast (by
          rw [M.canonicalClockTail_currentState_eq_stateSeq records liveLast]
          exact hnot_before liveLast hlive_lt_a)
      obtain ⟨hpos0, hstrict_prefix⟩ :=
        canonical_positive_sojourn_prefix_strict M records
          hhold_pos hstate_abs hhold_zero hlive_soj_pos
      let path' := strictCompletionThrough path liveLast
      have hcomp := strictCompletionThrough_strict
        path liveLast hpos0 hstrict_prefix
      have hfuture : ∃ m, T < path'.times m := by
        obtain ⟨m, hm⟩ := exists_nat_gt (T - path.times liveLast)
        refine ⟨liveLast + (m + 1), ?_⟩
        have hnot : ¬ liveLast + (m + 1) ≤ liveLast := by omega
        have hsub : liveLast + (m + 1) - liveLast = m + 1 := by omega
        have htime :
            path'.times (liveLast + (m + 1)) =
              path.times liveLast + (m + 1 : ℝ) := by
          simp [path', strictCompletionThrough, hnot, hsub]
        have hm' : (m : ℝ) < (m + 1 : ℝ) := by
          exact_mod_cast Nat.lt_succ_self m
        rw [htime]
        nlinarith
      have hbridge :=
        M.frozenClockTruncatedQV_sum_range_le_setIntegral
          path' hcomp.2 hcomp.1 hT hfuture a
      have hstart_eq : path'.sojournStart a = path.sojournStart a := by
        rw [← hlive_succ]
        simpa [path'] using
          strictCompletionThrough_sojournStart_succ_eq path liveLast
      have htail_readout : ∀ {t : ℝ}, path.sojournStart a ≤ t →
          path.frozenStateAt t = path.stateSeq a := by
        intro t ht_tail
        by_cases hfuture_t : ∃ m, t < path.times m
        · let m : ℕ := Nat.find hfuture_t
          have hm_time : t < path.times m := by
            simpa [m] using Nat.find_spec hfuture_t
          have hm_min : ∀ j ∈ Finset.range m, ¬ t < path.times j := by
            intro j hj
            exact Nat.find_min hfuture_t (Finset.mem_range.mp hj)
          have ha_le_m : a ≤ m := by
            by_contra hnot_ge
            have hm_lt_a : m < a := Nat.lt_of_not_ge hnot_ge
            have hm_le_live : m ≤ liveLast := by omega
            have hend_le_start :
                path.sojournEnd m ≤ path.sojournStart a := by
              have hend_le_start' :
                  path'.sojournEnd m ≤ path'.sojournStart a :=
                path'.sojournEnd_le_sojournStart_of_lt hcomp.2 hm_lt_a
              have hend_eq :
                  path'.sojournEnd m = path.sojournEnd m := by
                change path'.times m = path.times m
                simpa [path', strictCompletionThrough, hm_le_live]
              calc
                path.sojournEnd m = path'.sojournEnd m := hend_eq.symm
                _ ≤ path'.sojournStart a := hend_le_start'
                _ = path.sojournStart a := hstart_eq
            exact not_lt_of_ge (le_trans hend_le_start ht_tail) hm_time
          have hstate_m :
              path.frozenStateAt t = path.stateSeq m :=
            path.frozenStateAt_eq_stateSeq_of_first_time_gt t m hm_time hm_min
          rw [hstate_m, hstate_tail m ha_le_m]
        · have hno : ∀ m, ¬ t < path.times m := by
            simpa [not_exists] using hfuture_t
          have hstable_a : path.stateSeq a = path.stateSeq (a + 1) :=
            (hstate_abs_path a haAbs).symm
          have hmin_stable : ∀ k ∈ Finset.range a,
              path.stateSeq k ≠ path.stateSeq (k + 1) := by
            intro k hk heq
            have hk_lt_a : k < a := Finset.mem_range.mp hk
            have hnot_abs := hnot_before k hk_lt_a
            have hne := hnext_ne k (by
              rw [M.canonicalClockTail_currentState_eq_stateSeq records k]
              exact hnot_abs)
            have hrecord_eq :
                (records (k + 1)).2 =
                  QMatrix.currentStateFromHistory
                    (S := Fin d → Fin (M.N + 1)) k
                    (Preorder.frestrictLe k records) := by
              rw [M.canonicalClockTail_currentState_eq_stateSeq records k]
              simpa [path, DensityDepCTMC.canonicalPathMap,
                QMatrix.recordTrajectoryToPath_stateSeq] using heq.symm
            exact hne hrecord_eq
          exact path.frozenStateAt_eq_stateSeq_of_first_stable
            t a hno hstable_a hmin_stable
      calc
        (∑ k ∈ Finset.range a,
          M.instantQVRate (path.stateSeq k) *
            min (path.sojournTime k) (max 0 (T - path.sojournStart k)))
            =
          ∑ k ∈ Finset.range a,
            M.instantQVRate (path'.stateSeq k) *
              min (path'.sojournTime k) (max 0 (T - path'.sojournStart k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hk_lt_a := Finset.mem_range.mp hk
              have hk_le : k ≤ liveLast := by omega
              rw [strictCompletionThrough_stateSeq_eq,
                strictCompletionThrough_sojournTime_eq_of_le
                  path (n := liveLast) (m := k) hk_le,
                strictCompletionThrough_sojournStart_eq_of_le
                  path (n := liveLast) (m := k) hk_le]
        _ ≤ ∫ t in Set.Icc (0 : ℝ) T,
              M.instantQVRate (path'.frozenStateAt t) := hbridge
        _ = ∫ t in Set.Icc (0 : ℝ) T,
              M.instantQVRate (path.frozenStateAt t) := by
              apply setIntegral_congr_fun measurableSet_Icc
              intro t ht
              by_cases hlt : t < path.sojournStart a
              · have hlt_succ : t < path.sojournStart (liveLast + 1) := by
                  simpa [hlive_succ] using hlt
                have hstate :
                    path'.frozenStateAt t = path.frozenStateAt t := by
                  rw [strictCompletionThrough_frozenStateAt_eq_of_lt_succ
                    path liveLast hlt_succ]
                simpa [hstate]
              · have htail_t : path.sojournStart a ≤ t := le_of_not_gt hlt
                have hstate_path : path.frozenStateAt t = path.stateSeq a :=
                  htail_readout htail_t
                have hqv_path : M.instantQVRate (path.frozenStateAt t) = 0 := by
                  rw [hstate_path]
                  exact hqv_zero a le_rfl
                have hfuture_t : ∃ m, t < path'.times m := by
                  rcases hfuture with ⟨m, hm⟩
                  exact ⟨m, lt_of_le_of_lt ht.2 hm⟩
                have hstate_path' :
                    path'.frozenStateAt t = path'.stateSeq (path'.jumpCount t) := by
                  exact frozenStateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
                    path' hcomp.2 hfuture_t
                    ⟨path'.sojournStart_jumpCount_le_of_exists ht.1 hfuture_t, le_rfl⟩
                have hj_ge_a : a ≤ path'.jumpCount t := by
                  by_contra hnot_ge
                  have hjlt : path'.jumpCount t < a := Nat.lt_of_not_ge hnot_ge
                  have hmem := path'.mem_sojournInterval_jumpCount ht.1 hfuture_t
                  have hend_le :
                      path'.sojournEnd (path'.jumpCount t) ≤
                        path'.sojournStart a :=
                    path'.sojournEnd_le_sojournStart_of_lt hcomp.2 hjlt
                  have htail_t' : path'.sojournStart a ≤ t := by
                    simpa [hstart_eq] using htail_t
                  exact (not_lt_of_ge (le_trans hend_le htail_t')) hmem.2
                have hqv_path' : M.instantQVRate (path'.frozenStateAt t) = 0 := by
                  rw [hstate_path']
                  have hsseq :
                      path'.stateSeq (path'.jumpCount t) =
                        path.stateSeq (path'.jumpCount t) := by
                    simpa [path'] using
                      strictCompletionThrough_stateSeq_eq
                        path liveLast (path'.jumpCount t)
                  rw [hsseq]
                  exact hqv_zero (path'.jumpCount t) hj_ge_a
                exact hqv_path'.trans hqv_path.symm
  · have hnot_before_n : ∀ k, k < n →
        ¬M.toQMatrix.IsAbsorbing (path.stateSeq k) := by
      intro k hk hkAbs
      exact hAbs ⟨k, hk, hkAbs⟩
    by_cases hn0 : n = 0
    · simp [hn0]
      exact setIntegral_nonneg measurableSet_Icc fun _ _ =>
        M.instantQVRate_nonneg _
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      let liveLast : ℕ := n - 1
      have hlive_succ : liveLast + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
      have hlive_lt_n : liveLast < n := by omega
      have hlive_soj_pos : 0 < path.sojournTime liveLast := by
        rw [M.canonicalClockTail_sojournTime_eq_record records liveLast]
        exact hhold_pos liveLast (by
          rw [M.canonicalClockTail_currentState_eq_stateSeq records liveLast]
          exact hnot_before_n liveLast hlive_lt_n)
      obtain ⟨hpos0, hstrict_prefix⟩ :=
        canonical_positive_sojourn_prefix_strict M records
          hhold_pos hstate_abs hhold_zero hlive_soj_pos
      let path' := strictCompletionThrough path liveLast
      have hcomp := strictCompletionThrough_strict
        path liveLast hpos0 hstrict_prefix
      have hstartn_eq : path'.sojournStart n = path.sojournStart n := by
        rw [← hlive_succ]
        simpa [path'] using
          strictCompletionThrough_sojournStart_succ_eq path liveLast
      let T' : ℝ := min T (path.sojournStart n)
      have hT'_le_T : T' ≤ T := min_le_left _ _
      have hT'_le_start : T' ≤ path.sojournStart n := min_le_right _ _
      have hstartn_nonneg : 0 ≤ path.sojournStart n := by
        simpa [hstartn_eq] using
          path'.sojournStart_nonneg hcomp.2 hcomp.1 n
      have hT'_nonneg : 0 ≤ T' := le_min hT hstartn_nonneg
      have hfuture' : ∃ m, T' < path'.times m := by
        obtain ⟨m, hm⟩ := exists_nat_gt (T' - path.times liveLast)
        refine ⟨liveLast + (m + 1), ?_⟩
        have hnot : ¬ liveLast + (m + 1) ≤ liveLast := by omega
        have hsub : liveLast + (m + 1) - liveLast = m + 1 := by omega
        have htime :
            path'.times (liveLast + (m + 1)) =
              path.times liveLast + (m + 1 : ℝ) := by
          simp [path', strictCompletionThrough, hnot, hsub]
        have hm' : (m : ℝ) < (m + 1 : ℝ) := by
          exact_mod_cast Nat.lt_succ_self m
        rw [htime]
        nlinarith
      have hbridge' :=
        M.frozenClockTruncatedQV_sum_range_le_setIntegral
          path' hcomp.2 hcomp.1 hT'_nonneg hfuture' n
      have hterms_eq :
          (∑ k ∈ Finset.range n,
            M.instantQVRate (path.stateSeq k) *
              min (path.sojournTime k) (max 0 (T - path.sojournStart k))) =
          ∑ k ∈ Finset.range n,
            M.instantQVRate (path'.stateSeq k) *
              min (path'.sojournTime k) (max 0 (T' - path'.sojournStart k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk_lt_n : k < n := Finset.mem_range.mp hk
        have hk_le_live : k ≤ liveLast := by omega
        have hstart_eq_k :
            path'.sojournStart k = path.sojournStart k :=
          strictCompletionThrough_sojournStart_eq_of_le
            path (n := liveLast) (m := k) hk_le_live
        have hsoj_eq_k :
            path'.sojournTime k = path.sojournTime k :=
          strictCompletionThrough_sojournTime_eq_of_le
            path (n := liveLast) (m := k) hk_le_live
        have hend_le_startn :
            path.sojournEnd k ≤ path.sojournStart n := by
          have hend_le_startn' :
              path'.sojournEnd k ≤ path'.sojournStart n :=
            path'.sojournEnd_le_sojournStart_of_lt hcomp.2 hk_lt_n
          have hend_eq :
              path'.sojournEnd k = path.sojournEnd k := by
            change path'.times k = path.times k
            simpa [path', strictCompletionThrough, hk_le_live]
          calc
            path.sojournEnd k = path'.sojournEnd k := hend_eq.symm
            _ ≤ path'.sojournStart n := hend_le_startn'
            _ = path.sojournStart n := hstartn_eq
        have hclock_eq :
            min (path.sojournTime k) (max 0 (T - path.sojournStart k)) =
              min (path.sojournTime k) (max 0 (T' - path.sojournStart k)) := by
          by_cases hTle : T ≤ path.sojournStart n
          · have hT' : T' = T := by
              exact min_eq_left hTle
            simp [hT']
          · have hstart_le_T : path.sojournStart n ≤ T := le_of_not_ge hTle
            have hT' : T' = path.sojournStart n := by
              exact min_eq_right hstart_le_T
            have hsoj_le_start :
                path.sojournTime k ≤
                  max 0 (path.sojournStart n - path.sojournStart k) := by
              have hnonneg :
                  0 ≤ path.sojournStart n - path.sojournStart k := by
                have hstart_le_end :
                    path.sojournStart k ≤ path.sojournEnd k := by
                  have hsoj_pos : 0 < path.sojournTime k := by
                    rw [M.canonicalClockTail_sojournTime_eq_record records k]
                    exact hhold_pos k (by
                      rw [M.canonicalClockTail_currentState_eq_stateSeq records k]
                      exact hnot_before_n k hk_lt_n)
                  simpa [CTMCPath.sojournTime, sub_nonneg] using le_of_lt hsoj_pos
                exact sub_nonneg.mpr (le_trans hstart_le_end hend_le_startn)
              rw [max_eq_right hnonneg]
              calc
                path.sojournTime k =
                    path.sojournEnd k - path.sojournStart k := rfl
                _ ≤ path.sojournStart n - path.sojournStart k :=
                    sub_le_sub_right hend_le_startn _
            have hsoj_le_T :
                path.sojournTime k ≤ max 0 (T - path.sojournStart k) := by
              have hnonneg : 0 ≤ T - path.sojournStart k := by
                have hstart_le_end :
                    path.sojournStart k ≤ path.sojournEnd k := by
                  have hsoj_pos : 0 < path.sojournTime k := by
                    rw [M.canonicalClockTail_sojournTime_eq_record records k]
                    exact hhold_pos k (by
                      rw [M.canonicalClockTail_currentState_eq_stateSeq records k]
                      exact hnot_before_n k hk_lt_n)
                  simpa [CTMCPath.sojournTime, sub_nonneg] using le_of_lt hsoj_pos
                exact sub_nonneg.mpr
                  (le_trans hstart_le_end (le_trans hend_le_startn hstart_le_T))
              rw [max_eq_right hnonneg]
              calc
                path.sojournTime k =
                    path.sojournEnd k - path.sojournStart k := rfl
                _ ≤ T - path.sojournStart k :=
                    sub_le_sub_right (le_trans hend_le_startn hstart_le_T) _
            rw [hT', min_eq_left hsoj_le_T, min_eq_left hsoj_le_start]
        rw [strictCompletionThrough_stateSeq_eq path liveLast k,
          hsoj_eq_k, hstart_eq_k, hclock_eq]
      calc
        (∑ k ∈ Finset.range n,
          M.instantQVRate (path.stateSeq k) *
            min (path.sojournTime k) (max 0 (T - path.sojournStart k)))
            =
          ∑ k ∈ Finset.range n,
            M.instantQVRate (path'.stateSeq k) *
              min (path'.sojournTime k) (max 0 (T' - path'.sojournStart k)) :=
              hterms_eq
        _ ≤ ∫ t in Set.Icc (0 : ℝ) T',
              M.instantQVRate (path'.frozenStateAt t) := hbridge'
        _ = ∫ t in Set.Icc (0 : ℝ) T',
              M.instantQVRate (path.frozenStateAt t) := by
              exact strictCompletionThrough_setIntegral_frozenQV_eq_of_le_succ
                M path liveLast hT'_nonneg (by
                  rw [hlive_succ]
                  exact hT'_le_start)
        _ ≤ ∫ t in Set.Icc (0 : ℝ) T,
              M.instantQVRate (path.frozenStateAt t) := by
              exact M.frozenInstantQVRate_setIntegral_mono_Icc records hT'_le_T

set_option maxHeartbeats 0 in
/-- Finite clock-truncated QV sums are bounded by the expected frozen QV time
integral for canonical absorbing density-dependent CTMC paths. -/
theorem frozenClockTruncatedQVIntegralSum_le_frozenQV_setIntegral
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hinit : M.InSimplex x₀) (T : ℝ) (hT : 0 < T) (n : ℕ) :
    M.frozenClockTruncatedQVIntegralSum x₀ T n ≤
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀ := by
  classical
  have _hinit := hinit
  let μ := M.canonicalRecordMeasure x₀
  have hsum_int :
      M.frozenClockTruncatedQVIntegralSum x₀ T n =
        ∫ records,
          (∑ k ∈ Finset.range n,
            (let hist := Preorder.frestrictLe k records
             let x : Fin d → Fin (M.N + 1) :=
              QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) k hist
             M.instantQVRate x *
              min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist)))
          ∂μ := by
    symm
    rw [integral_finsetSum]
    · simp [frozenClockTruncatedQVIntegralSum, μ]
    · intro k _hk
      simpa [μ] using M.integrable_clockTruncatedQVIncrement x₀ T k
  rw [hsum_int]
  have hleft_int : Integrable
      (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range n,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist))) μ := by
    exact integrable_finsetSum (Finset.range n) fun k _hk => by
      simpa [μ] using M.integrable_clockTruncatedQVIncrement x₀ T k
  have hright_int : Integrable
      (fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)) μ := by
    simpa [μ] using
      M.integrable_canonicalFrozenInstantQVRate_setIntegral x₀ T (le_of_lt hT)
  have hpoint :
      (fun records : M.canonicalRecordΩ =>
        ∑ k ∈ Finset.range n,
          (let hist := Preorder.frestrictLe k records
           let x : Fin d → Fin (M.N + 1) :=
            QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k hist
           M.instantQVRate x *
            min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist)))
      ≤ᵐ[μ]
      fun records : M.canonicalRecordΩ =>
        ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s) := by
    filter_upwards [M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing x₀,
      M.toQMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing x₀,
      M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing x₀,
      M.toQMatrix.canonicalRecordMeasure_all_next_state_ne_current_ae_of_nonabsorbing x₀]
      with records hhold_pos hstate_abs hhold_zero hnext_ne
    let path := M.canonicalPathMap records
    have hconv : ∀ k,
        (let hist := Preorder.frestrictLe k records
         let x := QMatrix.currentStateFromHistory
           (S := Fin d → Fin (M.N + 1)) k hist
         M.instantQVRate x *
          min (records (k + 1)).1 (QMatrix.historyClockRemaining T k hist)) =
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k)) := by
      intro k
      have hcur :
          QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records) =
            path.stateSeq k := by
        simpa [path] using
          M.canonicalClockTail_currentState_eq_stateSeq records k
      have hsoj : (records (k + 1)).1 = path.sojournTime k := by
        simpa [path] using
          (M.canonicalClockTail_sojournTime_eq_record records k).symm
      have hremaining :
          QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
            max 0 (T - path.sojournStart k) := by
        have hraw :
            QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records) =
              max 0 (T - (M.canonicalPathMap records).sojournStart k) := by
          simp [QMatrix.historyClockRemaining,
            QMatrix.historySojournStart_frestrictLe,
            DensityDepCTMC.canonicalPathMap]
        simpa [path] using hraw
      change
        M.instantQVRate
            (QMatrix.currentStateFromHistory
              (S := Fin d → Fin (M.N + 1)) k (Preorder.frestrictLe k records)) *
          min (records (k + 1)).1
            (QMatrix.historyClockRemaining T k (Preorder.frestrictLe k records)) =
        M.instantQVRate (path.stateSeq k) *
          min (path.sojournTime k) (max 0 (T - path.sojournStart k))
      rw [hcur, hsoj, hremaining]
    rw [Finset.sum_congr rfl (fun k _ => hconv k)]
    exact M.frozenClockTruncatedQV_sum_canonical_le_setIntegral records
      (le_of_lt hT) n hhold_pos hstate_abs hhold_zero hnext_ne
  simpa [μ] using integral_mono_ae hleft_int hright_int hpoint

set_option maxHeartbeats 0 in
/-- Canonical absorbing density-dependent CTMC paths either hit an absorbing
state or have a future jump time beyond every fixed positive horizon. -/
theorem canonical_absorption_or_nonExplosive_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hinit : M.InSimplex x₀) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      (∃ a, M.toQMatrix.IsAbsorbing
        ((M.canonicalPathMap records).stateSeq a)) ∨
      (∃ n, T < (M.canonicalPathMap records).times n) := by
  classical
  let μ := M.canonicalRecordMeasure x₀
  let ℱ : MeasureTheory.Filtration ℕ
      (inferInstance : MeasurableSpace M.canonicalRecordΩ) :=
    { seq := fun n => MeasureTheory.Filtration.piLE
        (X := fun n : ℕ =>
          QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) n) (n + 1)
      mono' := by
        intro i j hij
        exact (MeasureTheory.Filtration.piLE
          (X := fun n : ℕ =>
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) n)).mono
            (Nat.succ_le_succ hij)
      le' := by
        intro i
        exact (MeasureTheory.Filtration.piLE
          (X := fun n : ℕ =>
            QMatrix.JumpHoldTrajectorySpace (Fin d → Fin (M.N + 1)) n)).le
            (i + 1) }
  let A : ℕ → Set M.canonicalRecordΩ :=
    fun n => {records | (1 : ℝ) < (records (n + 1)).1}
  have hA_meas : ∀ n, MeasurableSet[ℱ n] (A n) := by
    intro n
    simpa [ℱ, A] using
      QMatrix.measurableSet_record_holdingTime_Ioi_piLE
        (S := Fin d → Fin (M.N + 1)) (1 : ℝ) (n + 1)
  have hBC := MeasureTheory.tendsto_sum_indicator_atTop_iff'
    (μ := μ) (ℱ := ℱ) (s := A) hA_meas
  have htail : ∀ᵐ records ∂μ, ∀ k : ℕ,
      ¬M.toQMatrix.IsAbsorbing
          (QMatrix.currentStateFromHistory
            (S := Fin d → Fin (M.N + 1)) (k + 1)
            (Preorder.frestrictLe (k + 1) records)) →
        Real.exp (-(M.toQMatrix.uniformRate * (1 : ℝ))) ≤
          MeasureTheory.condExp (ℱ k) μ
            ((A (k + 1)).indicator fun _ => (1 : ℝ)) records := by
    rw [ae_all_iff]
    intro k
    let X : M.canonicalRecordΩ →
        ((i : Iic (k + 1)) → QMatrix.JumpHoldTrajectorySpace
          (Fin d → Fin (M.N + 1)) i) :=
      Preorder.frestrictLe (k + 1)
    let Y : M.canonicalRecordΩ → ℝ :=
      fun records => (records (k + 1 + 1)).1
    have htail_hist :
        ∀ᵐ hist ∂μ.map X,
          ∀ h : ¬M.toQMatrix.IsAbsorbing
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) (k + 1) hist),
            Real.exp (-(M.toQMatrix.uniformRate * (1 : ℝ))) ≤
              (ProbabilityTheory.condDistrib Y X μ hist).real (Set.Ioi (1 : ℝ)) := by
      simpa [μ, X, Y, canonicalRecordMeasure] using
        M.toQMatrix.condDistrib_next_holdingTime_Ioi_ge_uniformRate_of_nonabsorbing
          x₀ (k + 1) (by norm_num : (0 : ℝ) ≤ 1)
    have htail_records :
        ∀ᵐ records ∂μ,
          ∀ h : ¬M.toQMatrix.IsAbsorbing
              (QMatrix.currentStateFromHistory
                (S := Fin d → Fin (M.N + 1)) (k + 1) (X records)),
            Real.exp (-(M.toQMatrix.uniformRate * (1 : ℝ))) ≤
              (ProbabilityTheory.condDistrib Y X μ (X records)).real (Set.Ioi (1 : ℝ)) :=
      MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe (k + 1)).aemeasurable
        htail_hist
    have hcond :
        (fun records =>
          (ProbabilityTheory.condDistrib Y X μ (X records)).real (Set.Ioi (1 : ℝ)))
        =ᵐ[μ]
        MeasureTheory.condExp (MeasurableSpace.comap X inferInstance) μ
          ((Y ⁻¹' Set.Ioi (1 : ℝ)).indicator fun _ => (1 : ℝ)) :=
      ProbabilityTheory.condDistrib_ae_eq_condExp
        (X := X) (Y := Y) (μ := μ) (s := Set.Ioi (1 : ℝ))
        (Preorder.measurable_frestrictLe (k + 1)) (by fun_prop) measurableSet_Ioi
    filter_upwards [htail_records, hcond] with records htail_record hcond_eq hnonabs
    have htail_bound := htail_record hnonabs
    simpa [μ, ℱ, A, X, Y, Function.comp_def,
      MeasureTheory.Filtration.piLE_eq_comap_frestrictLe, hcond_eq]
      using htail_bound
  have hhold_nonneg :=
    M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae x₀
  filter_upwards [hBC, htail, hhold_nonneg]
    with records hBC_records htail_records hhold_nonneg_records
  by_cases hAbs :
      ∃ a, M.toQMatrix.IsAbsorbing
        ((M.canonicalPathMap records).stateSeq a)
  · exact Or.inl hAbs
  · refine Or.inr ?_
    have hpred : Filter.Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n,
          MeasureTheory.condExp (ℱ k) μ
            ((A (k + 1)).indicator fun _ => (1 : ℝ)) records)
        Filter.atTop Filter.atTop := by
      have hp : 0 < Real.exp (-(M.toQMatrix.uniformRate * (1 : ℝ))) :=
        Real.exp_pos _
      have hconst : Filter.Tendsto
          (fun n : ℕ =>
            (n : ℝ) * Real.exp (-(M.toQMatrix.uniformRate * (1 : ℝ))))
          Filter.atTop Filter.atTop :=
        by simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop hp
      refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hconst
      filter_upwards with n
      calc
        (n : ℝ) * Real.exp (-(M.toQMatrix.uniformRate * (1 : ℝ)))
            = ∑ k ∈ Finset.range n,
                Real.exp (-(M.toQMatrix.uniformRate * (1 : ℝ))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ∑ k ∈ Finset.range n,
              MeasureTheory.condExp (ℱ k) μ
                ((A (k + 1)).indicator fun _ => (1 : ℝ)) records := by
              refine Finset.sum_le_sum fun k _hk => ?_
              exact htail_records k (by
                rw [M.canonicalClockTail_currentState_eq_stateSeq records (k + 1)]
                exact fun h => hAbs ⟨k + 1, h⟩)
    have hindicator : Filter.Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n,
          (A (k + 1)).indicator (fun _ => (1 : ℝ)) records)
        Filter.atTop Filter.atTop :=
      hBC_records.2 hpred
    have hcount : Filter.Tendsto
        (fun n : ℕ =>
          (((Finset.range n).filter fun k =>
            (1 : ℝ) <
              (M.canonicalPathMap records).holdingTime k).card : ℝ))
        Filter.atTop Filter.atTop := by
      refine hindicator.congr' ?_
      filter_upwards with n
      rw [Finset.sum_indicator_eq_sum_filter]
      simp [A, canonicalPathMap, QMatrix.recordTrajectoryToPath_holdingTime]
    have hnonneg : ∀ n, 0 ≤ (M.canonicalPathMap records).holdingTime n := by
      intro n
      simpa [canonicalPathMap, QMatrix.recordTrajectoryToPath_holdingTime] using
        hhold_nonneg_records (n + 1)
    have hne : (M.canonicalPathMap records).NonExplosive :=
      (M.canonicalPathMap records).nonExplosive_of_large_holdingTime_strict_count_tendsto
        hnonneg (by norm_num : (0 : ℝ) < 1) hcount
    exact (M.canonicalPathMap records).exists_bound_of_nonExplosive hne T

set_option maxHeartbeats 0 in
/-- Glue a random finite clock-bridge index into the generic frozen Doob L2
bound.  The bridge may choose a different finite skeleton horizon on each
canonical record, provided these horizons exist almost everywhere. -/
theorem frozenMartingalePart_DoobL2_of_bridge_exists_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (_hinit : M.InSimplex x₀) {T : ℝ} (hT : 0 < T)
    (hBridge : ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∃ n, (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2) ≤
      (4 / 3 : ℝ) * M.frozenClockSkeletonSupSq T n records +
        4 * M.frozenTruncatedJumpSqSum T n records)
    (hQV : ∀ n, M.frozenClockTruncatedQVIntegralSum x₀ T n ≤
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀) :
    ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      frozenMartingalePartDoobL2Constant d *
        ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
          ∂M.canonicalRecordMeasure x₀ := by
  classical
  let μ := M.canonicalRecordMeasure x₀
  let F : M.canonicalRecordΩ → ℝ := fun records =>
    ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
  let A : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.frozenClockSkeletonSupSq T n records
  let J : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    M.frozenTruncatedJumpSqSum T n records
  let G : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    (4 / 3 : ℝ) * A n records + 4 * J n records
  let Q : ℕ → ℝ := fun n => M.frozenClockTruncatedQVIntegralSum x₀ T n
  let R : ℝ :=
    ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
      M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)) ∂μ
  let B : ℕ → Set M.canonicalRecordΩ := fun n => {records | F records ≤ G n records}
  let f : ℕ → M.canonicalRecordΩ → ℝ := fun n records =>
    (B n).indicator F records
  have hF_int : Integrable F μ := by
    simpa [F, μ] using
      M.canonical_frozen_martingale_sup_sq_integrable x₀ T hT
  have hF_nonneg : ∀ records : M.canonicalRecordΩ, 0 ≤ F records := by
    intro records
    dsimp [F]
    exact Real.iSup_nonneg fun s =>
      Real.iSup_nonneg fun hs =>
        sq_nonneg ‖M.frozenMartingalePart M.canonicalPathMap s records‖
  have hA_int : ∀ n, Integrable (A n) μ := by
    intro n
    simpa [A, μ] using
      M.integrable_frozenClockSkeletonSupSq x₀ T n
  have hJ_int : ∀ n, Integrable (J n) μ := by
    intro n
    dsimp [J, frozenTruncatedJumpSqSum]
    exact integrable_finsetSum (Finset.range n) fun k _hk => by
      simpa [μ] using M.integrable_truncatedJumpSqIncrementFromHistory_next x₀ T k
  have hG_int : ∀ n, Integrable (G n) μ := by
    intro n
    dsimp [G]
    exact ((hA_int n).const_mul (4 / 3 : ℝ)).add ((hJ_int n).const_mul 4)
  have hB_null : ∀ n, NullMeasurableSet (B n) μ := by
    intro n
    dsimp [B]
    exact hF_int.aestronglyMeasurable.nullMeasurableSet_le
      (hG_int n).aestronglyMeasurable
  have hf_int : ∀ n, Integrable (f n) μ := by
    intro n
    dsimp [f]
    exact hF_int.indicator₀ (hB_null n)
  have hG_mono : ∀ n records, G n records ≤ G (n + 1) records := by
    intro n records
    have hA_mono : A n records ≤ A (n + 1) records := by
      simpa [A] using M.frozenClockSkeletonSupSq_mono T n records
    have hJ_mono : J n records ≤ J (n + 1) records := by
      simpa [J] using M.frozenTruncatedJumpSqSum_mono T n records
    dsimp [G]
    nlinarith
  have hB_succ : ∀ n, B n ⊆ B (n + 1) := by
    intro n records hrecords
    exact hrecords.trans (hG_mono n records)
  have hB_mono : Monotone B := by
    exact monotone_nat_of_le_succ hB_succ
  have hBridge_B : ∀ᵐ records ∂μ, ∃ n, records ∈ B n := by
    simpa [B, F, G, μ] using hBridge
  have hf_mono : ∀ᵐ records ∂μ, Monotone fun n => f n records := by
    refine ae_of_all _ fun records => ?_
    intro n m hnm
    by_cases hn : records ∈ B n
    · have hm : records ∈ B m := hB_mono hnm hn
      simp [f, hn, hm]
    · by_cases hm : records ∈ B m
      · simp [f, hn, hm, hF_nonneg records]
      · simp [f, hn, hm]
  have hf_tendsto : ∀ᵐ records ∂μ,
      Filter.Tendsto (fun n => f n records) Filter.atTop (𝓝 (F records)) := by
    filter_upwards [hBridge_B] with records hrecords
    rcases hrecords with ⟨n₀, hn₀⟩
    refine tendsto_atTop_of_eventually_const (i₀ := n₀) ?_
    intro n hn
    have hn_mem : records ∈ B n := hB_mono hn hn₀
    simp [f, hn_mem]
  have hf_integral_tendsto :
      Filter.Tendsto (fun n => ∫ records, f n records ∂μ) Filter.atTop
        (𝓝 (∫ records, F records ∂μ)) :=
    integral_tendsto_of_tendsto_of_monotone hf_int hF_int hf_mono hf_tendsto
  have hf_le_bound : ∀ n,
      ∫ records, f n records ∂μ ≤ frozenMartingalePartDoobL2Constant d * R := by
    intro n
    have hf_le_G :
        f n ≤ᵐ[μ] G n := by
      refine ae_of_all _ fun records => ?_
      by_cases hrecords : records ∈ B n
      · have hF_le : F records ≤ G n records := by
          simpa [B] using hrecords
        simpa [f, hrecords] using hF_le
      · have hG_nonneg : 0 ≤ G n records := by
          have hA_nonneg : 0 ≤ A n records := by
            simpa [A] using M.frozenClockSkeletonSupSq_nonneg T n records
          have hJ_nonneg : 0 ≤ J n records := by
            simpa [J] using M.frozenTruncatedJumpSqSum_nonneg T n records
          dsimp [G]
          nlinarith
        simpa [f, hrecords] using hG_nonneg
    have hmono_int :
        ∫ records, f n records ∂μ ≤ ∫ records, G n records ∂μ :=
      integral_mono_ae (hf_int n) (hG_int n) hf_le_G
    have hA_le :
        ∫ records, A n records ∂μ ≤
          (4 * (Fintype.card (Fin d) : ℝ)) * Q n := by
      simpa [A, Q, μ] using
        M.integral_frozenClockTruncated_vector_sup_sq_le_vector_qv x₀ T n
    have hJ_eq :
        ∫ records, J n records ∂μ = Q n := by
      simpa [J, Q, μ] using
        M.integral_frozenTruncatedJumpSqSum_eq_clockTruncatedQV x₀ T n
    have hQ_le_R : Q n ≤ R := by
      simpa [Q, R, μ] using hQV n
    calc
      ∫ records, f n records ∂μ
          ≤ ∫ records, G n records ∂μ := hmono_int
      _ = (4 / 3 : ℝ) * ∫ records, A n records ∂μ +
            4 * ∫ records, J n records ∂μ := by
            dsimp [G]
            rw [integral_add]
            · rw [integral_const_mul, integral_const_mul]
            · exact (hA_int n).const_mul (4 / 3 : ℝ)
            · exact (hJ_int n).const_mul 4
      _ ≤ (4 / 3 : ℝ) * ((4 * (Fintype.card (Fin d) : ℝ)) * Q n) +
            4 * Q n := by
            have hmulA := mul_le_mul_of_nonneg_left hA_le
              (by norm_num : (0 : ℝ) ≤ 4 / 3)
            rw [hJ_eq]
            nlinarith
      _ = frozenMartingalePartDoobL2Constant d * Q n := by
            unfold frozenMartingalePartDoobL2Constant
            ring
      _ ≤ frozenMartingalePartDoobL2Constant d * R := by
            exact mul_le_mul_of_nonneg_left hQ_le_R
              (le_of_lt (frozenMartingalePartDoobL2Constant_pos d))
  have hfinal :
      ∫ records, F records ∂μ ≤ frozenMartingalePartDoobL2Constant d * R :=
    le_of_tendsto' hf_integral_tendsto hf_le_bound
  simpa [F, R, μ] using hfinal

end DensityDepCTMC
end Ripple.CTMC
