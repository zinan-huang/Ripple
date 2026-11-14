/-
  Ripple.Kurtz.StrongApprox.GaussianCdf — the standard normal cdf is Lipschitz, strictly
  increasing, and `Φ(Z)` is uniform

  `Φ = cdf (gaussianReal 0 1)`.  Facts: `Φ y − Φ x = μ.real (Ioc x y)`; `0 < μ (Ioc x y)` for `x < y`
  (Lebesgue is absolutely continuous w.r.t. the Gaussian); `μ.real (Ioc x y) ≤ (y − x)/√(2π)`.
  Hence `Φ` is strictly monotone and continuous, `0 < Φ x < 1`, and for `Z ~ gaussianReal 0 1`
  and `t ∈ [0,1]`, `P {Φ(Z) ≤ t} = ofReal t`: the input needed by `QuantileLaw`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.QuantileLaw

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- The standard normal cdf. -/
noncomputable def stdNormalCdf : ℝ → ℝ := cdf (gaussianReal 0 1)

local notation "μ₀" => gaussianReal 0 1

theorem stdNormalCdf_eq_real (x : ℝ) : stdNormalCdf x = (μ₀).real (Iic x) := cdf_eq_real μ₀ x

theorem ofReal_stdNormalCdf (x : ℝ) : ENNReal.ofReal (stdNormalCdf x) = μ₀ (Iic x) := ofReal_cdf μ₀ x

theorem stdNormalCdf_sub {x y : ℝ} (hxy : x ≤ y) :
    stdNormalCdf y - stdNormalCdf x = (μ₀).real (Ioc x y) := by
  rw [stdNormalCdf_eq_real, stdNormalCdf_eq_real, ← Iic_union_Ioc_eq_Iic hxy,
    measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  ring

theorem gaussian_Ioc_pos {x y : ℝ} (hxy : x < y) : 0 < μ₀ (Ioc x y) := by
  rw [pos_iff_ne_zero]
  intro h
  have := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero h
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at this
  linarith

theorem gaussianPDFReal_zero_one_le (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_of_le_one_right (by positivity)
  rw [Real.exp_le_one_iff]
  have : 0 ≤ x ^ 2 := sq_nonneg x
  linarith [show -(x ^ 2) / (2 * (1 : ℝ)) ≤ 0 by
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)]

theorem gaussian_real_Ioc_le {x y : ℝ} (hxy : x ≤ y) :
    (μ₀).real (Ioc x y) ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (y - x) := by
  have hμ : μ₀ (Ioc x y) = ENNReal.ofReal (∫ t in Ioc x y, gaussianPDFReal 0 1 t) :=
    gaussianReal_apply_eq_integral 0 one_ne_zero _
  have hint_nonneg : 0 ≤ ∫ t in Ioc x y, gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioc fun t _ => gaussianPDFReal_nonneg 0 1 t
  rw [measureReal_def, hμ, ENNReal.toReal_ofReal hint_nonneg]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc x y)
    (f := gaussianPDFReal 0 1) (C := (Real.sqrt (2 * Real.pi))⁻¹) measure_Ioc_lt_top
    (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 t)]
      exact gaussianPDFReal_zero_one_le t)
  rw [Real.norm_eq_abs, abs_of_nonneg hint_nonneg] at h
  have hvol : volume.real (Ioc x y) = y - x := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  rw [hvol] at h
  exact h

theorem stdNormalCdf_strictMono : StrictMono stdNormalCdf := by
  intro x y hxy
  have h := stdNormalCdf_sub hxy.le
  have hpos : 0 < (μ₀).real (Ioc x y) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (gaussian_Ioc_pos hxy).ne' (measure_ne_top _ _)
  linarith

theorem stdNormalCdf_monotone : Monotone stdNormalCdf := stdNormalCdf_strictMono.monotone

theorem abs_stdNormalCdf_sub_le (x y : ℝ) :
    |stdNormalCdf y - stdNormalCdf x| ≤ (Real.sqrt (2 * Real.pi))⁻¹ * |y - x| := by
  rcases le_total x y with hxy | hxy
  · rw [stdNormalCdf_sub hxy, abs_of_nonneg (by rw [measureReal_def]; exact ENNReal.toReal_nonneg),
      abs_of_nonneg (by linarith)]
    exact gaussian_real_Ioc_le hxy
  · rw [abs_sub_comm, stdNormalCdf_sub hxy,
      abs_of_nonneg (by rw [measureReal_def]; exact ENNReal.toReal_nonneg), abs_sub_comm,
      abs_of_nonneg (by linarith)]
    exact gaussian_real_Ioc_le hxy

theorem stdNormalCdf_continuous : Continuous stdNormalCdf := by
  rw [Metric.continuous_iff]
  intro x ε hε
  set C : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ with hC
  have hC0 : 0 < C := by positivity
  refine ⟨ε / C, by positivity, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  calc |stdNormalCdf y - stdNormalCdf x| ≤ C * |y - x| := abs_stdNormalCdf_sub_le x y
    _ < C * (ε / C) := by gcongr
    _ = ε := by field_simp

theorem stdNormalCdf_pos (x : ℝ) : 0 < stdNormalCdf x := by
  have h := stdNormalCdf_strictMono (show x - 1 < x by linarith)
  have h0 : 0 ≤ stdNormalCdf (x - 1) := by
    rw [stdNormalCdf_eq_real, measureReal_def]; exact ENNReal.toReal_nonneg
  linarith

theorem stdNormalCdf_lt_one (x : ℝ) : stdNormalCdf x < 1 := by
  have h := stdNormalCdf_strictMono (show x < x + 1 by linarith)
  have h1 : stdNormalCdf (x + 1) ≤ 1 := cdf_le_one μ₀ _
  linarith

theorem stdNormalCdf_le_one (x : ℝ) : stdNormalCdf x ≤ 1 := (stdNormalCdf_lt_one x).le

/-- Every `t ∈ (0,1)` is attained by the standard normal cdf. -/
theorem exists_stdNormalCdf_eq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ x, stdNormalCdf x = t := by
  have hbot : Tendsto stdNormalCdf atBot (𝓝 0) := tendsto_cdf_atBot μ₀
  have htop : Tendsto stdNormalCdf atTop (𝓝 1) := tendsto_cdf_atTop μ₀
  obtain ⟨a, ha⟩ := (hbot.eventually (gt_mem_nhds ht0)).exists
  obtain ⟨b, hb⟩ := (htop.eventually (lt_mem_nhds ht1)).exists
  have hab : a ≤ b := by
    by_contra h
    push Not at h
    have := stdNormalCdf_strictMono h
    linarith
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hab stdNormalCdf_continuous.continuousOn
    ⟨ha.le, hb.le⟩
  exact ⟨x, hx⟩

/-- `Φ(Z)` is uniform on `[0,1]` when `Z ~ gaussianReal 0 1`. -/
theorem measure_stdNormalCdf_comp_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hlaw : P.map Z = μ₀)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P {ω | stdNormalCdf (Z ω) ≤ t} = ENNReal.ofReal t := by
  rcases ht0.lt_or_eq with ht0 | rfl
  · rcases ht1.lt_or_eq with ht1 | rfl
    · obtain ⟨x₀, hx₀⟩ := exists_stdNormalCdf_eq ht0 ht1
      have hset : {ω | stdNormalCdf (Z ω) ≤ t} = Z ⁻¹' Iic x₀ := by
        ext ω
        simp only [mem_setOf_eq, mem_preimage, mem_Iic, ← hx₀]
        exact stdNormalCdf_strictMono.le_iff_le
      rw [hset, ← Measure.map_apply hZ measurableSet_Iic, hlaw, ← ofReal_stdNormalCdf, hx₀]
    · have hset : {ω | stdNormalCdf (Z ω) ≤ 1} = univ := by
        ext ω; simp [stdNormalCdf_le_one]
      rw [hset, measure_univ, ENNReal.ofReal_one]
  · have hset : {ω | stdNormalCdf (Z ω) ≤ 0} = ∅ := by
      ext ω; simp [not_le.mpr (stdNormalCdf_pos (Z ω))]
    rw [hset, measure_empty, ENNReal.ofReal_zero]

/-- The quantile coupling with a standard normal input has cdf `F`. -/
theorem measure_natQuantile_stdNormalCdf_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hlaw : P.map Z = μ₀)
    {F : ℕ → ℝ} (hF : Monotone F) (hF0 : ∀ k, 0 ≤ F k) (hF1 : ∀ k, F k ≤ 1)
    (hFtop : ∃ k, F k = 1) (k : ℕ) :
    P {ω | natQuantile F (stdNormalCdf (Z ω)) ≤ k} = ENNReal.ofReal (F k) := by
  apply measure_natQuantile_le P hF hF0 hF1
  · intro ω
    obtain ⟨j, hj⟩ := hFtop
    exact ⟨j, by rw [hj]; exact stdNormalCdf_le_one _⟩
  · intro t ht0 ht1
    exact measure_stdNormalCdf_comp_le P hZ hlaw ht0 ht1

end Ripple.Kurtz.StrongApprox
