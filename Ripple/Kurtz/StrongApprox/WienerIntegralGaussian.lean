import Ripple.Kurtz.StrongApprox.BrownianEntropyModulus
import Ripple.Analysis.BVQuadrature
import Ripple.Analysis.DyadicQuadrature
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Deterministic Wiener integrals via integration by parts

Finite dyadic sums have an exact Gaussian law. Deterministic quadrature and
characteristic-function convergence identify their almost-sure limit with the
integration-by-parts integral at every time in the Brownian horizon. The
zero-start condition is explicit because the increment interface omits it.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal Topology

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Independent centered Gaussian variables can be summed over any finite set. -/
theorem centeredGaussian_finset_sum_law
    {X : ι → Ω → ℝ} {v : ι → ℝ≥0}
    (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
    (hind : iIndepFun X P) (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, X i ω) = gaussianReal 0 (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [sum_empty]
      rw [Measure.map_const, measure_univ, one_smul, gaussianReal_zero_var]
  | @insert i s hi ih =>
      have hiS : IndepFun (∑ j ∈ s, X j) (X i) P :=
        hind.indepFun_finsetSum_of_notMem hX hi
      have hs : P.map (∑ j ∈ s, X j) = gaussianReal 0 (∑ j ∈ s, v j) := by
        rw [Finset.sum_fn]
        exact ih
      have h := gaussianReal_add_gaussianReal_of_indepFun hiS hs (hlaw i)
      simp only [sum_insert hi]
      have hfun : (fun ω => X i ω + ∑ j ∈ s, X j ω) = (∑ j ∈ s, X j) + X i := by
        funext ω
        simp only [Pi.add_apply, Finset.sum_apply]
        ring
      rw [hfun, h]
      congr 1 <;> ring

/-- A deterministic weighted sum, including zero variances and zero weights. -/
theorem centeredGaussian_weighted_sum_law [Fintype ι]
    {X : ι → Ω → ℝ} {v : ι → ℝ≥0}
    (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
    (hind : iIndepFun X P) (c : ι → ℝ) :
    P.map (fun ω => ∑ i, c i * X i ω) =
      gaussianReal 0 (∑ i, ⟨c i ^ 2, sq_nonneg _⟩ * v i) := by
  have hc : ∀ i, Measurable (fun ω => c i * X i ω) :=
    fun i => (hX i).const_mul (c i)
  have hcLaw : ∀ i, P.map (fun ω => c i * X i ω) =
      gaussianReal 0 (⟨c i ^ 2, sq_nonneg _⟩ * v i) := by
    intro i
    change P.map ((fun x : ℝ => c i * x) ∘ X i) = _
    rw [← Measure.map_map (by fun_prop) (hX i), hlaw i,
      gaussianReal_map_const_mul, mul_zero]
    first
      | rfl
      | exact congrArg (gaussianReal 0) (NNReal.coe_injective rfl)
  have hcInd : iIndepFun (fun i ω => c i * X i ω) P :=
    hind.comp (fun i x => c i * x) (fun _ => by fun_prop)
  exact centeredGaussian_finset_sum_law hc hcLaw hcInd Finset.univ

/-- The dyadic step integral at the right endpoint of the given horizon. -/
def brownianDyadicIntegral (a : ℝ → ℝ) (W : ℝ → Ω → ℝ) (H : ℝ)
    (m : ℕ) (ω : Ω) : ℝ :=
  ∑ k : Fin (2 ^ m), a (brownianDyadicPoint H m k.val) *
    (W (brownianDyadicPoint H m (k.val + 1)) ω -
      W (brownianDyadicPoint H m k.val) ω)

/-- Discrete variance of the dyadic step integral. -/
def brownianDyadicIntegralVariance (a : ℝ → ℝ) (H : ℝ) (m : ℕ) : ℝ≥0 :=
  ∑ k : Fin (2 ^ m),
    ⟨a (brownianDyadicPoint H m k.val) ^ 2, sq_nonneg _⟩ *
      Real.toNNReal (brownianDyadicMesh H m)

/-- Every approximation is measurable, without a path measurability hypothesis. -/
theorem measurable_brownianDyadicIntegral
    {W : ℝ → Ω → ℝ} {H : ℝ} (hW : DyadicBrownianOn P W H)
    (a : ℝ → ℝ) (m : ℕ) : Measurable (brownianDyadicIntegral a W H m) := by
  unfold brownianDyadicIntegral
  exact Finset.measurable_sum _ (fun k _ =>
    ((hW.eval_measurable _).sub (hW.eval_measurable _)).const_mul _)

/-- Exact law of the step integral from the actual dyadic Brownian interface. -/
theorem brownianDyadicIntegral_law
    {W : ℝ → Ω → ℝ} {H : ℝ} (hW : DyadicBrownianOn P W H)
    (a : ℝ → ℝ) (m : ℕ) :
    P.map (brownianDyadicIntegral a W H m) =
      gaussianReal 0 (brownianDyadicIntegralVariance a H m) := by
  exact centeredGaussian_weighted_sum_law
    (fun k => (hW.eval_measurable _).sub (hW.eval_measurable _))
    (hW.cell_law m) (hW.cell_independent m)
    (fun k => a (brownianDyadicPoint H m k.val))

/-- The finite approximations are centered. -/
theorem brownianDyadicIntegral_mean
    {W : ℝ → Ω → ℝ} {H : ℝ} (hW : DyadicBrownianOn P W H)
    (a : ℝ → ℝ) (m : ℕ) :
    ∫ ω, brownianDyadicIntegral a W H m ω ∂P = 0 := by
  have h : HasLaw (brownianDyadicIntegral a W H m)
      (gaussianReal 0 (brownianDyadicIntegralVariance a H m)) P :=
    ⟨(measurable_brownianDyadicIntegral hW a m).aemeasurable,
      brownianDyadicIntegral_law hW a m⟩
  rw [h.integral_eq, integral_id_gaussianReal]

/-- The finite approximations have the stated variance. -/
theorem brownianDyadicIntegral_variance
    {W : ℝ → Ω → ℝ} {H : ℝ} (hW : DyadicBrownianOn P W H)
    (a : ℝ → ℝ) (m : ℕ) :
    Var[brownianDyadicIntegral a W H m; P] =
      (brownianDyadicIntegralVariance a H m : ℝ) := by
  have h : HasLaw (brownianDyadicIntegral a W H m)
      (gaussianReal 0 (brownianDyadicIntegralVariance a H m)) P :=
    ⟨(measurable_brownianDyadicIntegral hW a m).aemeasurable,
      brownianDyadicIntegral_law hW a m⟩
  rw [h.variance_eq, variance_id_gaussianReal]

/-- Gaussian laws pass to an almost-sure limit when their variances converge.
The limit is automatically measurable in the completed-measure sense. -/
theorem centeredGaussian_law_of_ae_tendsto
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {v : ℕ → ℝ≥0} {vlim : ℝ≥0}
    (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, P.map (X n) = gaussianReal 0 (v n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (vlim : ℝ))) :
    HasLaw Y (gaussianReal 0 vlim) P := by
  have hY : AEMeasurable Y P :=
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun n => (hX n).aemeasurable) hlim
  refine ⟨hY, Measure.ext_of_charFun (funext fun t => ?_)⟩
  let f : ℝ → ℂ := fun x => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
  have hf : Continuous f := by fun_prop
  have hfBound : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    simpa only [f, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
      using (le_refl (1 : ℝ))
  have hcf (Z : Ω → ℝ) (hZ : AEMeasurable Z P) :
      charFun (P.map Z) t = ∫ ω, f (Z ω) ∂P := by
    rw [charFun_apply_real]
    exact integral_map hZ (by fun_prop)
  have hfirst : Tendsto (fun n => charFun (P.map (X n)) t) atTop
      (𝓝 (charFun (P.map Y) t)) := by
    have hi : Tendsto (fun n => ∫ ω, f (X n ω) ∂P) atTop
        (𝓝 (∫ ω, f (Y ω) ∂P)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      · intro n
        exact (hf.measurable.comp (hX n)).aestronglyMeasurable
      · exact integrable_const _
      · intro n
        exact Filter.Eventually.of_forall (fun ω => hfBound (X n ω))
      · filter_upwards [hlim] with ω hω
        exact hf.continuousAt.tendsto.comp hω
    have hcfX : ∀ n, charFun (P.map (X n)) t = ∫ ω, f (X n ω) ∂P :=
      fun n => hcf (X n) (hX n).aemeasurable
    simpa only [hcfX, hcf Y hY] using hi
  have hsecond : Tendsto (fun n => charFun (P.map (X n)) t) atTop
      (𝓝 (charFun (gaussianReal 0 vlim) t)) := by
    simp_rw [hlaw, charFun_gaussianReal]
    have he : Continuous (fun r : ℝ =>
        Complex.exp ((t : ℂ) * 0 * Complex.I - (r : ℂ) * (t : ℂ) ^ 2 / 2)) :=
      by fun_prop
    simpa only [Complex.ofReal_zero] using he.continuousAt.tendsto.comp hv
  exact tendsto_nhds_unique hfirst hsecond

/-- A limit of the actual dyadic step integrals has the limiting Gaussian law. -/
theorem brownianDyadicIntegral_limit_law
    {W : ℝ → Ω → ℝ} {H : ℝ} (hW : DyadicBrownianOn P W H)
    (a : ℝ → ℝ) {Y : Ω → ℝ} {v : ℝ≥0}
    (hlim : ∀ᵐ ω ∂P,
      Tendsto (fun m => brownianDyadicIntegral a W H m ω) atTop (𝓝 (Y ω)))
    (hv : Tendsto (fun m => (brownianDyadicIntegralVariance a H m : ℝ))
      atTop (𝓝 (v : ℝ))) :
    HasLaw Y (gaussianReal 0 v) P :=
  centeredGaussian_law_of_ae_tendsto
    (measurable_brownianDyadicIntegral hW a)
    (brownianDyadicIntegral_law hW a) hlim hv

/-- Almost-sure convergence of the actual finite Gaussian approximations to
integration by parts, with the zero-start assumption explicitly supplied. -/
theorem brownianDyadicIntegral_tendsto_J
    {W : ℝ → Ω → ℝ} {H : ℝ} {a : ℝ → ℝ} {K : ℝ≥0}
    (hW : DyadicBrownianOn P W H) (hH : 0 ≤ H)
    (ha : LipschitzOnWith K a (Set.Icc 0 H))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun m => brownianDyadicIntegral a W H m ω) atTop
      (𝓝 (Ripple.Analysis.BVIntegrationByParts.J a (fun s => W s ω) H)) := by
  filter_upwards [hW.continuous_ae, hzero] with ω hw hz
  simpa only [brownianDyadicIntegral, brownianDyadicPoint, Nat.cast_add, Nat.cast_one] using
    Ripple.Analysis.BVIntegrationByParts.dyadic_leftSum_tendsto_J hH ha hw.continuousOn hz

/-- The discrete Gaussian variances converge to the energy of the integrand. -/
theorem brownianDyadicIntegralVariance_tendsto
    {H : ℝ} {a : ℝ → ℝ} {K : ℝ≥0}
    (hH : 0 ≤ H) (ha : LipschitzOnWith K a (Set.Icc 0 H)) :
    Tendsto (fun m => (brownianDyadicIntegralVariance a H m : ℝ)) atTop
      (𝓝 (∫ s in 0..H, a s ^ 2)) := by
  have heq (m : ℕ) : (brownianDyadicIntegralVariance a H m : ℝ) =
      ∑ k : Fin (2 ^ m), a (H * (k : ℝ) / (2 : ℝ) ^ m) ^ 2 *
        (H / (2 : ℝ) ^ m) := by
    have hmesh : 0 ≤ H / (2 : ℝ) ^ m := div_nonneg hH (by positivity)
    simp only [brownianDyadicIntegralVariance, NNReal.coe_sum, NNReal.coe_mul,
      brownianDyadicPoint, brownianDyadicMesh, Real.coe_toNNReal _ hmesh]
    rfl
  simp_rw [heq]
  exact Ripple.Analysis.DyadicQuadrature.tendsto_dyadic_variance ha hH

/-- Wiener identification at the horizon of the supplied dyadic Brownian law.
Both convergence premises are produced by deterministic quadrature theorems. -/
theorem wienerIntegral_gaussian_at_horizon
    {W : ℝ → Ω → ℝ} {H : ℝ} {a : ℝ → ℝ} {K : ℝ≥0}
    (hW : DyadicBrownianOn P W H) (hH : 0 ≤ H)
    (ha : LipschitzOnWith K a (Set.Icc 0 H))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    HasLaw (fun ω => Ripple.Analysis.BVIntegrationByParts.J a (fun s => W s ω) H)
      (gaussianReal 0 (Real.toNNReal (∫ s in 0..H, a s ^ 2))) P := by
  have hvnonneg : 0 ≤ ∫ s in 0..H, a s ^ 2 :=
    intervalIntegral.integral_nonneg hH (fun _ _ => sq_nonneg _)
  apply brownianDyadicIntegral_limit_law hW a
    (brownianDyadicIntegral_tendsto_J hW hH ha hzero)
  rw [Real.coe_toNNReal _ hvnonneg]
  exact brownianDyadicIntegralVariance_tendsto hH ha

/-- Centering of the actual pathwise integral. -/
theorem wienerIntegral_mean_at_horizon
    {W : ℝ → Ω → ℝ} {H : ℝ} {a : ℝ → ℝ} {K : ℝ≥0}
    (hW : DyadicBrownianOn P W H) (hH : 0 ≤ H)
    (ha : LipschitzOnWith K a (Set.Icc 0 H))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    ∫ ω, Ripple.Analysis.BVIntegrationByParts.J a (fun s => W s ω) H ∂P = 0 := by
  rw [(wienerIntegral_gaussian_at_horizon hW hH ha hzero).integral_eq,
    integral_id_gaussianReal]

/-- The scalar variance equals the integral of the squared coefficient. -/
theorem wienerIntegral_variance_at_horizon
    {W : ℝ → Ω → ℝ} {H : ℝ} {a : ℝ → ℝ} {K : ℝ≥0}
    (hW : DyadicBrownianOn P W H) (hH : 0 ≤ H)
    (ha : LipschitzOnWith K a (Set.Icc 0 H))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    Var[fun ω => Ripple.Analysis.BVIntegrationByParts.J a (fun s => W s ω) H; P] =
      ∫ s in 0..H, a s ^ 2 := by
  rw [(wienerIntegral_gaussian_at_horizon hW hH ha hzero).variance_eq,
    variance_id_gaussianReal, Real.coe_toNNReal _
      (intervalIntegral.integral_nonneg hH (fun _ _ => sq_nonneg _))]

/-- The truncated step variances converge on the original Brownian grid. -/
theorem brownianDyadicIntegralVariance_cutoff_tendsto
    {H t : ℝ} {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Set.Icc 0 H)) (ht : t ∈ Set.Icc 0 H) :
    Tendsto (fun m => (brownianDyadicIntegralVariance
      (fun s => if s < t then a s else 0) H m : ℝ)) atTop
      (𝓝 (∫ s in 0..t, a s ^ 2)) := by
  have heq (m : ℕ) : (brownianDyadicIntegralVariance
      (fun s => if s < t then a s else 0) H m : ℝ) =
      ∑ k : Fin (2 ^ m),
        (if H * (k : ℝ) / (2 : ℝ) ^ m < t then
          a (H * (k : ℝ) / (2 : ℝ) ^ m) ^ 2 else 0) * (H / (2 : ℝ) ^ m) := by
    have hmesh : 0 ≤ H / (2 : ℝ) ^ m := div_nonneg (ht.1.trans ht.2) (by positivity)
    simp only [brownianDyadicIntegralVariance, NNReal.coe_sum, NNReal.coe_mul,
      NNReal.coe_mk, brownianDyadicMesh, Real.coe_toNNReal _ hmesh]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [brownianDyadicPoint]
    split_ifs
    · rfl
    · exact congrArg (fun x : ℝ => x * (H / (2 : ℝ) ^ m)) (zero_pow two_ne_zero)
  simp_rw [heq]
  exact Ripple.Analysis.DyadicQuadrature.tendsto_cutoff_dyadic_variance ha ht

/-- One-dimensional Wiener identification at every time in the supplied horizon.
The Brownian interface is used only at `H`; no rescaled or restricted Brownian
law is assumed. A zero initial value is necessary for this definition of J. -/
theorem wienerIntegral_gaussian
    {W : ℝ → Ω → ℝ} {H t : ℝ} {a : ℝ → ℝ} {K : ℝ≥0}
    (hW : DyadicBrownianOn P W H)
    (ha : LipschitzOnWith K a (Set.Icc 0 H)) (ht : t ∈ Set.Icc 0 H)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    HasLaw (fun ω => Ripple.Analysis.BVIntegrationByParts.J a (fun s => W s ω) t)
      (gaussianReal 0 (Real.toNNReal (∫ s in 0..t, a s ^ 2))) P := by
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun m => brownianDyadicIntegral (fun s => if s < t then a s else 0)
        W H m ω) atTop
        (𝓝 (Ripple.Analysis.BVIntegrationByParts.J a (fun s => W s ω) t)) := by
    filter_upwards [hW.continuous_ae, hzero] with ω hw hz
    simpa only [brownianDyadicIntegral, brownianDyadicPoint, Nat.cast_add, Nat.cast_one] using
      Ripple.Analysis.BVIntegrationByParts.dyadic_cutoff_leftSum_tendsto_J
        ha hw.continuousOn hz ht
  apply brownianDyadicIntegral_limit_law hW (fun s => if s < t then a s else 0) hlim
  rw [Real.coe_toNNReal _ (intervalIntegral.integral_nonneg ht.1 (fun _ _ => sq_nonneg _))]
  exact brownianDyadicIntegralVariance_cutoff_tendsto ha ht

/-- The pathwise Wiener integral is centered at every time in the horizon. -/
theorem wienerIntegral_mean
    {W : ℝ → Ω → ℝ} {H t : ℝ} {a : ℝ → ℝ} {K : ℝ≥0}
    (hW : DyadicBrownianOn P W H)
    (ha : LipschitzOnWith K a (Set.Icc 0 H)) (ht : t ∈ Set.Icc 0 H)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    ∫ ω, Ripple.Analysis.BVIntegrationByParts.J a (fun s => W s ω) t ∂P = 0 := by
  rw [(wienerIntegral_gaussian hW ha ht hzero).integral_eq, integral_id_gaussianReal]

/-- Variance identification at every time in the horizon. -/
theorem wienerIntegral_variance
    {W : ℝ → Ω → ℝ} {H t : ℝ} {a : ℝ → ℝ} {K : ℝ≥0}
    (hW : DyadicBrownianOn P W H)
    (ha : LipschitzOnWith K a (Set.Icc 0 H)) (ht : t ∈ Set.Icc 0 H)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    Var[fun ω => Ripple.Analysis.BVIntegrationByParts.J a (fun s => W s ω) t; P] =
      ∫ s in 0..t, a s ^ 2 := by
  rw [(wienerIntegral_gaussian hW ha ht hzero).variance_eq,
    variance_id_gaussianReal, Real.coe_toNNReal _
      (intervalIntegral.integral_nonneg ht.1 (fun _ _ => sq_nonneg _))]

end Ripple.Kurtz.StrongApprox
