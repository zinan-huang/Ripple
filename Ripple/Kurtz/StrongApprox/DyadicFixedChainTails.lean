-- Ripple/Kurtz/StrongApprox/DyadicFixedChainTails.lean
import Ripple.Kurtz.StrongApprox.GaussianBlockSum

/-!
# Exponential tails for one fixed dyadic ancestor chain

This file is independent of the Gaussian and Poisson tree implementations.
It assumes only a finite independent family whose one-dimensional laws are
standard Gaussian.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal NNReal

namespace Ripple.Kurtz.StrongApprox.DyadicFixedChainTails

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ}

/-- Sum of squares of a finite Gaussian family. -/
def chiSquareSum (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, Z i ω ^ 2

/-- Weighted absolute-value sum. -/
def weightedAbsSum
    (v : Fin m → ℝ) (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, v i * |Z i ω|

/-- Deterministic squared mass of the weights. -/
def weightSquareMass (v : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, v i ^ 2

private theorem chiSquareSum_measurable
    (Z : Fin m → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) :
    Measurable (chiSquareSum Z) := by
  unfold chiSquareSum
  fun_prop

private theorem weightedAbsSum_measurable
    (v : Fin m → ℝ) (Z : Fin m → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) :
    Measurable (weightedAbsSum v Z) := by
  unfold weightedAbsSum
  fun_prop

private theorem weightSquareMass_nonneg (v : Fin m → ℝ) :
    0 ≤ weightSquareMass v := by
  unfold weightSquareMass
  exact Finset.sum_nonneg fun i _ => sq_nonneg (v i)

/-! ## The one-dimensional square exponential moment -/

private theorem gaussianPDFReal_mul_exp_quarter_sq :
    (fun x : ℝ =>
      gaussianPDFReal 0 1 x *
        Real.exp ((1 / 4 : ℝ) * x ^ 2)) =
      fun x : ℝ =>
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  have hexp : -x ^ 2 / 2 + (1 / 4 : ℝ) * x ^ 2 = -(1 / 4 : ℝ) * x ^ 2 := by
    ring
  rw [mul_assoc, ← Real.exp_add, hexp]

private theorem gaussian_quarter_normalization :
    (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 4 : ℝ)) =
      Real.sqrt 2 := by
  have hsqrtPi : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.2 Real.pi_pos
  have hsqrtTwo : 0 < Real.sqrt (2 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.sqrt (Real.pi / (1 / 4 : ℝ)) =
        (Real.sqrt 2 * Real.sqrt Real.pi)⁻¹ *
          (2 * Real.sqrt Real.pi) := by
      rw [show Real.pi / (1 / 4 : ℝ) = 4 * Real.pi by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    _ = (Real.sqrt 2)⁻¹ * 2 := by
      field_simp [hsqrtPi.ne', hsqrtTwo.ne']
      <;> ring
    _ = 2 / Real.sqrt 2 := by
      rw [div_eq_mul_inv]
      ring
    _ = Real.sqrt 2 := by
      apply (div_eq_iff hsqrtTwo.ne').2
      exact (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm

private theorem standardGaussian_exp_quarter_sq_integrable :
    Integrable
      (fun x : ℝ => Real.exp ((1 / 4 : ℝ) * x ^ 2))
      (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0
    (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul₀'
    (measurable_gaussianPDF 0 1).aemeasurable
    (ae_of_all _ fun x =>
      (gaussianPDF_lt_top :
        gaussianPDF (0 : ℝ) (1 : ℝ≥0) x < ∞))]
  have hfun :
      (fun x : ℝ =>
        (gaussianPDF 0 1 x).toReal •
          Real.exp ((1 / 4 : ℝ) * x ^ 2)) =
        fun x : ℝ =>
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
    simpa only [toReal_gaussianPDF, smul_eq_mul] using
      gaussianPDFReal_mul_exp_quarter_sq
  rw [hfun]
  exact
    (integrable_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _

private theorem standardGaussian_exp_quarter_sq_integral :
    ∫ x : ℝ, Real.exp ((1 / 4 : ℝ) * x ^ 2)
        ∂(gaussianReal 0 1) =
      Real.sqrt 2 := by
  rw [integral_gaussianReal_eq_integral_smul
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hfun :
      (fun x : ℝ =>
        gaussianPDFReal 0 1 x •
          Real.exp ((1 / 4 : ℝ) * x ^ 2)) =
        fun x : ℝ =>
          (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
    simpa only [smul_eq_mul] using
      gaussianPDFReal_mul_exp_quarter_sq
  rw [hfun, integral_const_mul, integral_gaussian]
  exact gaussian_quarter_normalization

private theorem integrable_exp_quarter_sq_of_gaussian
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hlaw : μ.map Z = gaussianReal 0 1) :
    Integrable
      (fun ω => Real.exp ((1 / 4 : ℝ) * Z ω ^ 2)) μ := by
  have h := standardGaussian_exp_quarter_sq_integrable
  rw [← hlaw] at h
  exact h.comp_measurable hZ

private theorem mgf_square_quarter_of_gaussian
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hlaw : μ.map Z = gaussianReal 0 1) :
    mgf (fun ω => Z ω ^ 2) μ (1 / 4 : ℝ) =
      Real.sqrt 2 := by
  unfold mgf
  have hmap := integral_map (μ := μ) (φ := Z)
    hZ.aemeasurable
    (f := fun x : ℝ => Real.exp ((1 / 4 : ℝ) * x ^ 2))
    (by fun_prop)
  rw [hlaw, standardGaussian_exp_quarter_sq_integral] at hmap
  exact hmap.symm

private theorem sqrt_two_le_exp_half :
    Real.sqrt 2 ≤ Real.exp (1 / 2 : ℝ) := by
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hexp := Real.add_one_le_exp (1 / 2 : ℝ)
  nlinarith

private theorem mgf_square_quarter_le_exp_half
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hlaw : μ.map Z = gaussianReal 0 1) :
    mgf (fun ω => Z ω ^ 2) μ (1 / 4 : ℝ) ≤
      Real.exp (1 / 2 : ℝ) := by
  rw [mgf_square_quarter_of_gaussian hZ hlaw]
  exact sqrt_two_le_exp_half

/-! ## Chi-square tail -/

private theorem chiSquareSum_mgf_quarter_le
    (Z : Fin m → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = gaussianReal 0 1) :
    mgf (chiSquareSum Z) μ (1 / 4 : ℝ) ≤
      Real.exp ((m : ℝ) / 2) := by
  have hindepSq :
      iIndepFun (fun i ω => Z i ω ^ 2) μ := by
    simpa [Function.comp_def] using
      hindep.comp
        (fun _ : Fin m => fun x : ℝ => x ^ 2)
        (fun _ => measurable_id.pow_const 2)
  have hmeasSq :
      ∀ i, Measurable (fun ω => Z i ω ^ 2) :=
    fun i => (hZ i).pow_const 2
  have hmgf :
      mgf (chiSquareSum Z) μ (1 / 4 : ℝ) =
        ∏ i : Fin m,
          mgf (fun ω => Z i ω ^ 2) μ (1 / 4 : ℝ) := by
    have hfun : chiSquareSum Z =
        ∑ i : Fin m, (fun ω => Z i ω ^ 2) := by
      funext ω
      simp [chiSquareSum, Finset.sum_apply]
    rw [hfun]
    exact hindepSq.mgf_sum (t := (1 / 4 : ℝ)) hmeasSq
      (Finset.univ : Finset (Fin m))
  rw [hmgf]
  calc
    (∏ i : Fin m,
        mgf (fun ω => Z i ω ^ 2) μ (1 / 4 : ℝ)) ≤
      ∏ _i : Fin m, Real.exp (1 / 2 : ℝ) :=
        Finset.prod_le_prod
          (fun _ _ => mgf_nonneg)
          (fun i _ => mgf_square_quarter_le_exp_half
            (hZ i) (hlaw i))
    _ = Real.exp (1 / 2 : ℝ) ^ m := by simp
    _ = Real.exp ((m : ℝ) / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- K16 chi-square bound.  The proof actually obtains `exp (-u/4)` and then
weakens it to the requested `exp (-u/8)`. -/
theorem chiSquareSum_tail
    (Z : Fin m → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = gaussianReal 0 1)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | 2 * (m : ℝ) + u < chiSquareSum Z ω} ≤
      Real.exp (-u / 8) := by
  have hindepSq :
      iIndepFun (fun i ω => Z i ω ^ 2) μ := by
    simpa [Function.comp_def] using
      hindep.comp
        (fun _ : Fin m => fun x : ℝ => x ^ 2)
        (fun _ => measurable_id.pow_const 2)
  have hmeasSq :
      ∀ i, Measurable (fun ω => Z i ω ^ 2) :=
    fun i => (hZ i).pow_const 2
  have hint :
      Integrable
        (fun ω => Real.exp ((1 / 4 : ℝ) * chiSquareSum Z ω)) μ := by
    have h := hindepSq.integrable_exp_mul_sum
      (t := (1 / 4 : ℝ)) hmeasSq
      (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => integrable_exp_quarter_sq_of_gaussian
        (hZ i) (hlaw i))
    simpa [chiSquareSum] using h
  have hchernoff :=
    measure_ge_le_exp_mul_mgf
      (μ := μ) (X := chiSquareSum Z)
      (2 * (m : ℝ) + u) (t := (1 / 4 : ℝ))
      (by norm_num) hint
  have hmgf := chiSquareSum_mgf_quarter_le Z hZ hindep hlaw
  calc
    μ.real {ω | 2 * (m : ℝ) + u < chiSquareSum Z ω} ≤
        μ.real {ω | 2 * (m : ℝ) + u ≤ chiSquareSum Z ω} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      have hω' : 2 * (m : ℝ) + u < chiSquareSum Z ω := hω
      exact le_of_lt hω'
    _ ≤ Real.exp (-(1 / 4 : ℝ) * (2 * (m : ℝ) + u)) *
        mgf (chiSquareSum Z) μ (1 / 4 : ℝ) := hchernoff
    _ ≤ Real.exp (-(1 / 4 : ℝ) * (2 * (m : ℝ) + u)) *
        Real.exp ((m : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-u / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-u / 8) := by
      apply Real.exp_le_exp.mpr
      linarith

/-! ## Weighted absolute-value tail -/

private theorem exp_weighted_abs_le_two_sides
    (θ v z : ℝ) :
    Real.exp (θ * (v * |z|)) ≤
      Real.exp ((θ * v) * z) +
        Real.exp (-(θ * v) * z) := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
    have heq : θ * (v * z) = (θ * v) * z := by ring
    rw [heq]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · have hz' : z < 0 := lt_of_not_ge hz
    rw [abs_of_neg hz']
    have heq : θ * (v * -z) = -(θ * v) * z := by ring
    rw [heq]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

private theorem integrable_exp_weighted_abs_of_gaussian
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hlaw : μ.map Z = gaussianReal 0 1)
    (θ v : ℝ) :
    Integrable
      (fun ω => Real.exp (θ * (v * |Z ω|))) μ := by
  have hplus := integrable_exp_mul_of_gaussian
    hZ hlaw (θ * v)
  have hminus := integrable_exp_mul_of_gaussian
    hZ hlaw (-(θ * v))
  refine (hplus.add hminus).mono' (by fun_prop) ?_
  filter_upwards with ω
  have hpoint := exp_weighted_abs_le_two_sides θ v (Z ω)
  have hright :
      0 ≤ Real.exp ((θ * v) * Z ω) +
        Real.exp (-(θ * v) * Z ω) := by positivity
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonneg hright] using hpoint

private theorem mgf_weighted_abs_le
    {Z : Ω → ℝ} (hZ : Measurable Z)
    (hlaw : μ.map Z = gaussianReal 0 1)
    (θ v : ℝ) :
    mgf (fun ω => v * |Z ω|) μ θ ≤
      2 * Real.exp ((θ * v) ^ 2 / 2) := by
  have hleft := integrable_exp_weighted_abs_of_gaussian
    hZ hlaw θ v
  have hplus := integrable_exp_mul_of_gaussian
    hZ hlaw (θ * v)
  have hminus := integrable_exp_mul_of_gaussian
    hZ hlaw (-(θ * v))
  have hmono :
      mgf (fun ω => v * |Z ω|) μ θ ≤
        mgf Z μ (θ * v) + mgf Z μ (-(θ * v)) := by
    unfold mgf
    rw [← integral_add hplus hminus]
    exact integral_mono_ae hleft (hplus.add hminus)
      (ae_of_all _ fun ω =>
        exp_weighted_abs_le_two_sides θ v (Z ω))
  calc
    mgf (fun ω => v * |Z ω|) μ θ ≤
        mgf Z μ (θ * v) + mgf Z μ (-(θ * v)) := hmono
    _ = Real.exp ((θ * v) ^ 2 / 2) +
        Real.exp ((-(θ * v)) ^ 2 / 2) := by
      rw [mgf_of_gaussian hlaw, mgf_of_gaussian hlaw]
    _ = 2 * Real.exp ((θ * v) ^ 2 / 2) := by
      rw [show (-(θ * v)) ^ 2 = (θ * v) ^ 2 by ring]
      ring

private theorem mgf_weightedAbsSum_le
    (v : Fin m → ℝ) (Z : Fin m → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = gaussianReal 0 1)
    (θ : ℝ) :
    mgf (weightedAbsSum v Z) μ θ ≤
      (2 : ℝ) ^ m *
        Real.exp (θ ^ 2 * weightSquareMass v / 2) := by
  have hindepWeighted :
      iIndepFun (fun i ω => v i * |Z i ω|) μ := by
    simpa [Function.comp_def] using
      hindep.comp
        (fun i : Fin m => fun x : ℝ => v i * |x|)
        (fun _ => by fun_prop)
  have hmeasWeighted :
      ∀ i, Measurable (fun ω => v i * |Z i ω|) :=
    fun i => by fun_prop
  have hmgf :
      mgf (weightedAbsSum v Z) μ θ =
        ∏ i : Fin m,
          mgf (fun ω => v i * |Z i ω|) μ θ := by
    have hfun : weightedAbsSum v Z =
        ∑ i : Fin m, (fun ω => v i * |Z i ω|) := by
      funext ω
      simp [weightedAbsSum, Finset.sum_apply]
    rw [hfun]
    exact hindepWeighted.mgf_sum (t := θ) hmeasWeighted
      (Finset.univ : Finset (Fin m))
  have hexponent :
      (∑ i : Fin m, (θ * v i) ^ 2 / 2) =
        θ ^ 2 * weightSquareMass v / 2 := by
    calc
      (∑ i : Fin m, (θ * v i) ^ 2 / 2) =
          ∑ i : Fin m, (θ ^ 2 / 2) * v i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (θ ^ 2 / 2) * ∑ i : Fin m, v i ^ 2 := by
        rw [Finset.mul_sum]
      _ = θ ^ 2 * weightSquareMass v / 2 := by
        unfold weightSquareMass
        ring
  rw [hmgf]
  calc
    (∏ i : Fin m,
        mgf (fun ω => v i * |Z i ω|) μ θ) ≤
      ∏ i : Fin m,
        (2 * Real.exp ((θ * v i) ^ 2 / 2)) :=
      Finset.prod_le_prod
        (fun _ _ => mgf_nonneg)
        (fun i _ => mgf_weighted_abs_le
          (hZ i) (hlaw i) θ (v i))
    _ = (2 : ℝ) ^ m *
        ∏ i : Fin m, Real.exp ((θ * v i) ^ 2 / 2) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ = (2 : ℝ) ^ m *
        Real.exp (θ ^ 2 * weightSquareMass v / 2) := by
      rw [← Real.exp_sum, hexponent]

private theorem weightedAbsSum_tail_of_positive_mass
    (v : Fin m → ℝ) (Z : Fin m → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = gaussianReal 0 1)
    (hV : 0 < weightSquareMass v)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u < weightedAbsSum v Z ω} ≤
      (2 : ℝ) ^ m *
        Real.exp (-(u ^ 2 / (2 * weightSquareMass v))) := by
  let V := weightSquareMass v
  let θ := u / V
  have hθ : 0 ≤ θ := by
    dsimp [θ, V]
    positivity
  have hindepWeighted :
      iIndepFun (fun i ω => v i * |Z i ω|) μ := by
    simpa [Function.comp_def] using
      hindep.comp
        (fun i : Fin m => fun x : ℝ => v i * |x|)
        (fun _ => by fun_prop)
  have hmeasWeighted :
      ∀ i, Measurable (fun ω => v i * |Z i ω|) :=
    fun i => by fun_prop
  have hint :
      Integrable
        (fun ω => Real.exp (θ * weightedAbsSum v Z ω)) μ := by
    have h := hindepWeighted.integrable_exp_mul_sum
      (t := θ) hmeasWeighted
      (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => integrable_exp_weighted_abs_of_gaussian
        (hZ i) (hlaw i) θ (v i))
    simpa [weightedAbsSum] using h
  have hchernoff :=
    measure_ge_le_exp_mul_mgf
      (μ := μ) (X := weightedAbsSum v Z)
      u (t := θ) hθ hint
  have hmgf := mgf_weightedAbsSum_le
    v Z hZ hindep hlaw θ
  have hexponent :
      -θ * u + θ ^ 2 * V / 2 =
        -(u ^ 2 / (2 * V)) := by
    dsimp [θ]
    field_simp [hV.ne']
    ring
  calc
    μ.real {ω | u < weightedAbsSum v Z ω} ≤
        μ.real {ω | u ≤ weightedAbsSum v Z ω} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      have hω' : u < weightedAbsSum v Z ω := hω
      exact le_of_lt hω'
    _ ≤ Real.exp (-θ * u) *
        mgf (weightedAbsSum v Z) μ θ := hchernoff
    _ ≤ Real.exp (-θ * u) *
        ((2 : ℝ) ^ m *
          Real.exp (θ ^ 2 * V / 2)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = (2 : ℝ) ^ m *
        Real.exp (-(u ^ 2 / (2 * V))) := by
      calc
        Real.exp (-θ * u) *
            ((2 : ℝ) ^ m * Real.exp (θ ^ 2 * V / 2)) =
          (2 : ℝ) ^ m *
            (Real.exp (-θ * u) *
              Real.exp (θ ^ 2 * V / 2)) := by ring
        _ = (2 : ℝ) ^ m *
            Real.exp (-θ * u + θ ^ 2 * V / 2) := by
          rw [Real.exp_add]
        _ = (2 : ℝ) ^ m *
            Real.exp (-(u ^ 2 / (2 * V))) := by
          rw [hexponent]
    _ = (2 : ℝ) ^ m *
        Real.exp (-(u ^ 2 /
          (2 * weightSquareMass v))) := rfl

/-- Zero squared weight mass forces every weight, and hence the weighted sum,
to vanish. -/
theorem weightedAbsSum_eq_zero_of_weightSquareMass_eq_zero
    (v : Fin m → ℝ) (Z : Fin m → Ω → ℝ)
    (hzero : weightSquareMass v = 0) :
    weightedAbsSum v Z = 0 := by
  have hsquares : ∀ i : Fin m, v i ^ 2 = 0 := by
    unfold weightSquareMass at hzero
    have hterms :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
          sq_nonneg (v i))).mp hzero
    intro i
    exact hterms i (by simp)
  have hweights : ∀ i : Fin m, v i = 0 := by
    intro i
    nlinarith [hsquares i]
  funext ω
  simp [weightedAbsSum, hweights]

/-- K16 weighted absolute-value tail.  `max 1` makes the statement total and
also covers the edge case in which every selected weight is zero. -/
theorem weightedAbsSum_tail
    (v : Fin m → ℝ) (Z : Fin m → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = gaussianReal 0 1)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u < weightedAbsSum v Z ω} ≤
      (2 : ℝ) ^ m *
        Real.exp
          (-(u ^ 2 /
            (2 * max 1 (weightSquareMass v)))) := by
  by_cases hzero : weightSquareMass v = 0
  · have hsum := weightedAbsSum_eq_zero_of_weightSquareMass_eq_zero
      v Z hzero
    have hevent :
        {ω | u < weightedAbsSum v Z ω} = (∅ : Set Ω) := by
      rw [hsum]
      ext ω
      simp [not_lt_of_ge hu]
    rw [hevent, measureReal_empty]
    positivity
  · have hV : 0 < weightSquareMass v :=
      lt_of_le_of_ne (weightSquareMass_nonneg v) (Ne.symm hzero)
    have hsharp := weightedAbsSum_tail_of_positive_mass
      v Z hZ hindep hlaw hV hu
    have hmaxPos : 0 < max 1 (weightSquareMass v) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hfrac :
        u ^ 2 / (2 * max 1 (weightSquareMass v)) ≤
          u ^ 2 / (2 * weightSquareMass v) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hle :
          weightSquareMass v ≤ max 1 (weightSquareMass v) :=
        le_max_right _ _
      nlinarith [sq_nonneg u]
    exact hsharp.trans <|
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hfrac))
        (pow_nonneg (by norm_num) m)

/-! ## Deterministic transfer and the `DyadicChainEstimate` constants -/

/-- Generic hypothesis-free transfer.  A pointwise deterministic estimate
implies a union of the square and weighted-absolute tail events. -/
theorem deterministicEnvelope_tail
    (v : Fin m → ℝ) (Z : Fin m → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = gaussianReal 0 1)
    (G : Ω → ℝ)
    {a b c L r q : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hr : 0 ≤ r) (hq : 0 ≤ q)
    (hdet : ∀ ω,
      G ω ≤ a * (m : ℝ) +
        b * chiSquareSum Z ω +
        c * Real.sqrt L * weightedAbsSum v Z ω) :
    μ.real
        {ω |
          (a + 2 * b) * (m : ℝ) +
              b * r + c * Real.sqrt L * q < G ω} ≤
      Real.exp (-r / 8) +
        (2 : ℝ) ^ m *
          Real.exp
            (-(q ^ 2 /
              (2 * max 1 (weightSquareMass v)))) := by
  let squareBad : Set Ω :=
    {ω | 2 * (m : ℝ) + r < chiSquareSum Z ω}
  let weightedBad : Set Ω :=
    {ω | q < weightedAbsSum v Z ω}
  have hsubset :
      {ω |
          (a + 2 * b) * (m : ℝ) +
              b * r + c * Real.sqrt L * q < G ω} ⊆
        squareBad ∪ weightedBad := by
    intro ω hlarge
    by_cases hsquare : ω ∈ squareBad
    · exact Or.inl hsquare
    · apply Or.inr
      by_contra hweight
      have hsquareLe :
          chiSquareSum Z ω ≤ 2 * (m : ℝ) + r :=
        le_of_not_gt hsquare
      have hweightLe :
          weightedAbsSum v Z ω ≤ q :=
        le_of_not_gt hweight
      have hbpart := mul_le_mul_of_nonneg_left hsquareLe hb
      have hcpart := mul_le_mul_of_nonneg_left hweightLe
        (mul_nonneg hc (Real.sqrt_nonneg L))
      have hpoint := hdet ω
      simp only [Set.mem_setOf_eq] at hlarge
      nlinarith
  calc
    μ.real
        {ω |
          (a + 2 * b) * (m : ℝ) +
              b * r + c * Real.sqrt L * q < G ω} ≤
        μ.real (squareBad ∪ weightedBad) :=
      measureReal_mono hsubset
    _ ≤ μ.real squareBad + μ.real weightedBad :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-r / 8) +
        (2 : ℝ) ^ m *
          Real.exp
            (-(q ^ 2 /
              (2 * max 1 (weightSquareMass v)))) := by
      apply add_le_add
      · exact chiSquareSum_tail Z hZ hindep hlaw hr
      · exact weightedAbsSum_tail v Z hZ hindep hlaw hq

/-- K18-ready specialization of the sharp deterministic estimate of `DyadicChainEstimate`.
Only `Σ v_i² ≤ 64` is needed by this weaker MGF route; the additional
`Σ v_i ≤ 16` from `DyadicChainEstimate` is harmless but unused here. -/
theorem kmtChainEnvelope_tail
    {K : ℕ}
    (v : Fin (K + 1) → ℝ)
    (Z : Fin (K + 1) → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ)
    (hlaw : ∀ i, μ.map (Z i) = gaussianReal 0 1)
    (G : Ω → ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u)
    (hV : weightSquareMass v ≤ 64)
    (hdet : ∀ ω,
      G ω ≤ (4 / 3 : ℝ) * (K + 1 : ℝ) +
        (32 / 3 : ℝ) * chiSquareSum Z ω +
        (1 / 6 : ℝ) * Real.sqrt L * weightedAbsSum v Z ω) :
    μ.real
        {ω | (68 / 3 : ℝ) * (K + 1 : ℝ) + u < G ω} ≤
      Real.exp (-(3 * u / 512)) +
        (2 : ℝ) ^ (K + 1) *
          Real.exp (-(9 * u ^ 2 / (128 * L))) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hsqrtPos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hr : 0 ≤ (3 * u / 64 : ℝ) := by positivity
  have hq : 0 ≤ 3 * u / Real.sqrt L := by positivity
  have hdet' : ∀ ω,
      G ω ≤ (4 / 3 : ℝ) * ((K + 1 : ℕ) : ℝ) +
        (32 / 3 : ℝ) * chiSquareSum Z ω +
        (1 / 6 : ℝ) * Real.sqrt L * weightedAbsSum v Z ω := by
    intro ω
    have h := hdet ω
    push_cast
    exact h
  have hbase := deterministicEnvelope_tail
    (μ := μ) v Z hZ hindep hlaw G
    (a := (4 / 3 : ℝ)) (b := (32 / 3 : ℝ))
    (c := (1 / 6 : ℝ)) (L := L)
    (r := 3 * u / 64) (q := 3 * u / Real.sqrt L)
    (by norm_num) (by norm_num) hr hq hdet'
  have hthreshold :
      ((4 / 3 : ℝ) + 2 * (32 / 3 : ℝ)) * ((K + 1 : ℕ) : ℝ) +
          (32 / 3 : ℝ) * (3 * u / 64) +
          (1 / 6 : ℝ) * Real.sqrt L *
            (3 * u / Real.sqrt L) =
        (68 / 3 : ℝ) * (K + 1 : ℝ) + u := by
    push_cast
    field_simp [hsqrtPos.ne']
    ring
  have hrExponent :
      -(3 * u / 64) / 8 = -(3 * u / 512) := by ring
  rw [hthreshold, hrExponent] at hbase
  let V := weightSquareMass v
  let M := max 1 V
  have hMpos : 0 < M := by
    dsimp [M]
    exact zero_lt_one.trans_le (le_max_left _ _)
  have hM64 : M ≤ 64 := by
    dsimp [M, V]
    exact max_le (by norm_num) hV
  have hqSq :
      (3 * u / Real.sqrt L) ^ 2 =
        9 * u ^ 2 / L := by
    rw [div_pow, Real.sq_sqrt hLpos.le]
    ring
  have hdenLe : 2 * M * L ≤ 128 * L := by
    have htwo : 2 * M ≤ 128 := by nlinarith
    exact mul_le_mul_of_nonneg_right htwo hLpos.le
  have hfrac :
      9 * u ^ 2 / (128 * L) ≤
        (3 * u / Real.sqrt L) ^ 2 / (2 * M) := by
    rw [hqSq]
    have hreassoc :
        (9 * u ^ 2 / L) / (2 * M) =
          9 * u ^ 2 / (2 * M * L) := by
      field_simp [hLpos.ne', hMpos.ne']
    rw [hreassoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact mul_le_mul_of_nonneg_left hdenLe (by positivity)
  have hexp :
      Real.exp
          (-((3 * u / Real.sqrt L) ^ 2 /
            (2 * M))) ≤
        Real.exp (-(9 * u ^ 2 / (128 * L))) :=
    Real.exp_le_exp.mpr (neg_le_neg hfrac)
  change
    μ.real {ω | (68 / 3 : ℝ) * (K + 1 : ℝ) + u < G ω} ≤
      Real.exp (-(3 * u / 512)) +
        (2 : ℝ) ^ (K + 1) *
          Real.exp
            (-((3 * u / Real.sqrt L) ^ 2 / (2 * M))) at hbase
  exact hbase.trans <|
    add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hexp
        (pow_nonneg (by norm_num) (K + 1)))

/-!
THEOREM LIST
* `chiSquareSum_tail`
* `weightedAbsSum_eq_zero_of_weightSquareMass_eq_zero`
* `weightedAbsSum_tail`
* `deterministicEnvelope_tail`
* `kmtChainEnvelope_tail`

CLOSES
* Item 1: `P(S > 2m+u) ≤ exp(-u/8)` for every `u ≥ 0`.
* Item 2: the permitted weaker absolute-value tail with the explicit `2^m`
  factor and a total `max 1` denominator.
* Item 3: a general deterministic-envelope transfer and the `DyadicChainEstimate`
  specialization
  `exp(-3u/512) + 2^(K+1) exp(-9u²/(128L))`.
* Edge cases `m = 0` and zero weight mass are included.

UNFINISHED
* The sharper centered half-normal MGF is intentionally absent: K17–K18 do
  not need it, because the displayed `2^(K+1)` factor is absorbed at the same
  `O(K+x)` deterministic threshold.
* The later adapter only has to identify the `quadraticNoise` of `DyadicChainEstimate` with
  `chiSquareSum` and `kmtLinearTerm` with `weightedAbsSum`.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicFixedChainTails

end
