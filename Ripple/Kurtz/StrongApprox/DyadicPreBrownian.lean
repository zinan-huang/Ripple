import Ripple.Kurtz.StrongApprox.WienerIntegralGaussian
import Ripple.Stochastic.BrownianMotion.Gaussian.BrownianMotion

/-!
# From dyadic increment laws to all finite Brownian laws

Common-grid cutoff sums approximate every finite linear combination of path
values. Expanding the square of their coefficient identifies the limiting
variance as the Brownian covariance quadratic form. No independence at
non-dyadic times is assumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal Topology

namespace Ripple.Kurtz.StrongApprox

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Coefficients of a finite linear combination of stopped constant integrands. -/
def brownianFiniteCutoff [Fintype ι] (t c : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ i, if s < t i then c i else 0

/-- The quadratic form of the Brownian covariance kernel on finitely many times. -/
def brownianFiniteVariance [Fintype ι] (t c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * min (t i) (t j)

/-- A constant integrand in the integration-by-parts definition returns the path. -/
theorem brownian_J_one (w : ℝ → ℝ) (t : ℝ) :
    Ripple.Analysis.BVIntegrationByParts.J (fun _ => 1) w t = w t := by
  simp [Ripple.Analysis.BVIntegrationByParts.J]

/-- A finite cutoff sum is precisely the linear combination of the individual
cutoff sums, on the same original Brownian grid. -/
theorem brownianDyadicIntegral_finiteCutoff [Fintype ι]
    (t c : ι → ℝ) (W : ℝ → Ω → ℝ) (H : ℝ) (m : ℕ) (ω : Ω) :
    brownianDyadicIntegral (brownianFiniteCutoff t c) W H m ω =
      ∑ i, c i * brownianDyadicIntegral (fun s => if s < t i then 1 else 0)
        W H m ω := by
  classical
  unfold brownianDyadicIntegral brownianFiniteCutoff
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

/-- Constant cutoff variances converge to the cutoff time, including zero. -/
theorem brownianDyadicVariance_cutoff_one_tendsto {H t : ℝ}
    (ht : t ∈ Set.Icc 0 H) :
    Tendsto (fun m => (brownianDyadicIntegralVariance
      (fun s => if s < t then 1 else 0) H m : ℝ)) atTop (𝓝 t) := by
  have h := brownianDyadicIntegralVariance_cutoff_tendsto
    (a := fun _ => (1 : ℝ)) (K := 0)
    (by simpa using (LipschitzWith.const (1 : ℝ)).lipschitzOnWith) ht
  simpa using h

/-- Expansion of the discrete variance into pairwise overlap lengths. -/
theorem brownianDyadicVariance_finiteCutoff [Fintype ι]
    (t c : ι → ℝ) {H : ℝ} (hH : 0 ≤ H) (m : ℕ) :
    (brownianDyadicIntegralVariance (brownianFiniteCutoff t c) H m : ℝ) =
      ∑ i, ∑ j, c i * c j * (brownianDyadicIntegralVariance
        (fun s => if s < min (t i) (t j) then 1 else 0) H m : ℝ) := by
  classical
  have hmesh : 0 ≤ brownianDyadicMesh H m := div_nonneg hH (by positivity)
  have hcoerce (a : ℝ → ℝ) :
      (brownianDyadicIntegralVariance a H m : ℝ) =
        ∑ k : Fin (2 ^ m), a (brownianDyadicPoint H m k.val) ^ 2 *
          brownianDyadicMesh H m := by
    simp only [brownianDyadicIntegralVariance, NNReal.coe_sum, NNReal.coe_mul,
      Real.coe_toNNReal _ hmesh]
    rfl
  rw [hcoerce]
  calc
    _ = ∑ k : Fin (2 ^ m), ∑ i, ∑ j,
        c i * c j * ((if brownianDyadicPoint H m k.val < min (t i) (t j)
          then 1 else 0) ^ 2 * brownianDyadicMesh H m) := by
      apply Finset.sum_congr rfl
      intro k _
      unfold brownianFiniteCutoff
      rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hi : brownianDyadicPoint H m k.val < t i <;>
        by_cases hj : brownianDyadicPoint H m k.val < t j <;>
        simp [hi, hj, lt_min_iff]
    _ = ∑ i, ∑ j, ∑ k : Fin (2 ^ m),
        c i * c j * ((if brownianDyadicPoint H m k.val < min (t i) (t j)
          then 1 else 0) ^ 2 * brownianDyadicMesh H m) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum, hcoerce (fun s => if s < min (t i) (t j) then 1 else 0)]

/-- The variance limit for an arbitrary finite combination of non-dyadic times. -/
theorem brownianDyadicVariance_finiteCutoff_tendsto [Fintype ι]
    (t c : ι → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (ht : ∀ i, t i ∈ Set.Icc 0 H) :
    Tendsto (fun m => (brownianDyadicIntegralVariance
      (brownianFiniteCutoff t c) H m : ℝ)) atTop
      (𝓝 (brownianFiniteVariance t c)) := by
  simp_rw [brownianDyadicVariance_finiteCutoff t c hH]
  unfold brownianFiniteVariance
  apply tendsto_finset_sum
  intro i _
  apply tendsto_finset_sum
  intro j _
  exact (brownianDyadicVariance_cutoff_one_tendsto
    ⟨le_min (ht i).1 (ht j).1, (min_le_left _ _).trans (ht i).2⟩).const_mul _

/-- Continuity and the zero initial value give simultaneous convergence of
all the cutoff sums in a finite linear combination. -/
theorem brownianDyadicIntegral_finiteCutoff_tendsto [Fintype ι]
    {W : ℝ → Ω → ℝ} {H : ℝ} (hW : DyadicBrownianOn P W H)
    (t c : ι → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 H)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    ∀ᵐ ω ∂P, Tendsto
      (fun m => brownianDyadicIntegral (brownianFiniteCutoff t c) W H m ω)
      atTop (𝓝 (∑ i, c i * W (t i) ω)) := by
  filter_upwards [hW.continuous_ae, hzero] with ω hw hz
  simp_rw [brownianDyadicIntegral_finiteCutoff]
  apply tendsto_finset_sum
  intro i _
  have h := Ripple.Analysis.BVIntegrationByParts.dyadic_cutoff_leftSum_tendsto_J
    (a := fun _ => (1 : ℝ)) (K := 0)
    (by simpa using (LipschitzWith.const (1 : ℝ)).lipschitzOnWith)
    hw.continuousOn hz (ht i)
  have hi : Tendsto (fun m => brownianDyadicIntegral
      (fun s => if s < t i then 1 else 0) W H m ω) atTop (𝓝 (W (t i) ω)) := by
    simpa only [brownianDyadicIntegral, brownianDyadicPoint, Nat.cast_add,
      Nat.cast_one, brownian_J_one] using h
  exact hi.const_mul _

/-- Full scalar projection laws at arbitrary times in a dyadic horizon.
The variance is the Brownian covariance quadratic form, rather than a
variance parameter supplied as a separate premise. -/
theorem dyadicBrownian_finite_linearCombination_law [Fintype ι]
    {W : ℝ → Ω → ℝ} {H : ℝ} (hW : DyadicBrownianOn P W H)
    (hH : 0 ≤ H) (t c : ι → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 H)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    HasLaw (fun ω => ∑ i, c i * W (t i) ω)
      (gaussianReal 0 (Real.toNNReal (brownianFiniteVariance t c))) P := by
  have hv := brownianDyadicVariance_finiteCutoff_tendsto t c hH ht
  have hnonneg : 0 ≤ brownianFiniteVariance t c :=
    ge_of_tendsto' hv (fun m => NNReal.coe_nonneg _)
  apply brownianDyadicIntegral_limit_law hW (brownianFiniteCutoff t c)
    (brownianDyadicIntegral_finiteCutoff_tendsto hW t c ht hzero)
  rw [Real.coe_toNNReal _ hnonneg]
  exact hv

/-- A continuous linear functional on a finite scalar product is a weighted sum. -/
theorem continuousLinearMap_apply_eq_finite_sum [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  classical
  have hx : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    L x = L (∑ i, x i • Pi.single i (1 : ℝ)) := congrArg L hx
    _ = ∑ i, L (Pi.single i 1) * x i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp only [smul_eq_mul, mul_comm]

/-- Every finite set of nonnegative times lies in one dyadic horizon. -/
theorem finite_times_le_dyadic_horizon [Fintype ι] (t : ι → ℝ≥0) :
    ∃ j : ℕ, ∀ i, (t i : ℝ) ≤ (2 : ℝ) ^ j := by
  have hp : Tendsto (fun j : ℕ => (2 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨j, hj⟩ := (hp.eventually (eventually_ge_atTop (∑ i, (t i : ℝ)))).exists
  refine ⟨j, fun i => ?_⟩
  exact (Finset.single_le_sum (fun k _ => (t k).coe_nonneg)
    (Finset.mem_univ i)).trans hj

/-- All finite scalar projections of the original all-time process have their
Brownian laws. The only probabilistic hypotheses are the supplied dyadic laws. -/
theorem allDyadicBrownian_finite_linearCombination_law [Fintype ι]
    {W : ℝ → Ω → ℝ} (hW : ∀ j : ℕ, DyadicBrownianOn P W ((2 : ℝ) ^ j))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (t : ι → ℝ≥0) (c : ι → ℝ) :
    HasLaw (fun ω => ∑ i, c i * W (t i) ω)
      (gaussianReal 0 (Real.toNNReal
        (brownianFiniteVariance (fun i => (t i : ℝ)) c))) P := by
  obtain ⟨j, hj⟩ := finite_times_le_dyadic_horizon t
  exact dyadicBrownian_finite_linearCombination_law (hW j) (by positivity)
    (fun i => (t i : ℝ)) c (fun i => ⟨(t i).coe_nonneg, hj i⟩) hzero

/-- Arbitrary finite scalar projections produce the Gaussian-process structure. -/
theorem allDyadicBrownian_isGaussianProcess
    {W : ℝ → Ω → ℝ} (hW : ∀ j : ℕ, DyadicBrownianOn P W ((2 : ℝ) ^ j))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    IsGaussianProcess (fun t : ℝ≥0 => W t) P where
  hasGaussianLaw I := by
    classical
    constructor
    apply isGaussian_of_map_eq_gaussianReal
    intro L
    let c : I → ℝ := fun i => L (Pi.single i 1)
    have h := allDyadicBrownian_finite_linearCombination_law hW hzero
      (fun i : I => i.val) c
    refine ⟨0, Real.toNNReal (brownianFiniteVariance (fun i : I => (i.val : ℝ)) c), ?_⟩
    have hmeas : Measurable (fun ω => I.restrict fun x : ℝ≥0 => W x ω) :=
      measurable_pi_iff.mpr (fun i => (hW 0).eval_measurable _)
    rw [Measure.map_map L.continuous.measurable hmeas]
    convert h.map_eq using 1
    congr 1
    ext ω
    exact continuousLinearMap_apply_eq_finite_sum L _

/-- The all-time scalar marginal at any nonnegative time. -/
theorem allDyadicBrownian_eval_law
    {W : ℝ → Ω → ℝ} (hW : ∀ j : ℕ, DyadicBrownianOn P W ((2 : ℝ) ^ j))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (t : ℝ≥0) :
    HasLaw (W t) (gaussianReal 0 t) P := by
  have h := allDyadicBrownian_finite_linearCombination_law (ι := Unit) hW hzero
    (fun _ => t) (fun _ => 1)
  simpa [brownianFiniteVariance] using h

/-- The covariance at arbitrary times follows by polarization of the sum law. -/
theorem allDyadicBrownian_covariance
    {W : ℝ → Ω → ℝ} (hW : ∀ j : ℕ, DyadicBrownianOn P W ((2 : ℝ) ^ j))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (s t : ℝ≥0) :
    cov[W s, W t; P] = min (s : ℝ) (t : ℝ) := by
  have hs := allDyadicBrownian_eval_law hW hzero s
  have ht := allDyadicBrownian_eval_law hW hzero t
  have hsum := allDyadicBrownian_finite_linearCombination_law
    (ι := Fin 2) hW hzero ![s, t] (fun _ => 1)
  have hq : brownianFiniteVariance (fun i => ((![s, t] : Fin 2 → ℝ≥0) i : ℝ))
      (fun _ => 1) = (s : ℝ) + 2 * min (s : ℝ) (t : ℝ) + (t : ℝ) := by
    simp [brownianFiniteVariance, Fin.sum_univ_succ, min_comm]
    ring
  have hv := hsum.variance_eq
  rw [variance_id_gaussianReal, hq, Real.coe_toNNReal _ (by positivity)] at hv
  have hvariance := variance_fun_add hs.hasGaussianLaw.memLp_two ht.hasGaussianLaw.memLp_two
  have hsvar := hs.variance_eq
  have htvar := ht.variance_eq
  rw [variance_id_gaussianReal] at hsvar htvar
  have hvsum : Var[fun ω => W s ω + W t ω; P] =
      (s : ℝ) + 2 * min (s : ℝ) (t : ℝ) + (t : ℝ) := by
    simpa [Fin.sum_univ_succ] using hv
  rw [hvariance, hsvar, htvar] at hvsum
  linarith

/-- The dyadic increment producer satisfies the full scalar pre-Brownian class
at all nonnegative real times, including non-dyadic finite-dimensional laws. -/
theorem allDyadicBrownian_isPreBrownian
    {W : ℝ → Ω → ℝ} (hW : ∀ j : ℕ, DyadicBrownianOn P W ((2 : ℝ) ^ j))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    IsPreBrownian (fun t : ℝ≥0 => W t) P := by
  apply (allDyadicBrownian_isGaussianProcess hW hzero).isPreBrownian_of_covariance
  · intro t
    rw [(allDyadicBrownian_eval_law hW hzero t).integral_eq, integral_id_gaussianReal]
  · intro s t hst
    rw [allDyadicBrownian_covariance hW hzero, min_eq_left (by exact_mod_cast hst)]

end Ripple.Kurtz.StrongApprox
