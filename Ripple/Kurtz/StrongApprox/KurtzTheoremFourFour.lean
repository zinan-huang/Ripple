import Ripple.Kurtz.StrongApprox.KurtzPaperConstruction
import Ripple.Kurtz.StrongApprox.SectionFourGlobalLaw
import Ripple.Kurtz.StrongApprox.SectionFourEuclideanEstimate

/-!
# Kurtz's simultaneous strong Gaussian approximation

The input record has the paper's bounded nonnegative rates, uniform
approximation, summed square-root bound, and bounded first and second
coordinate partials. The concrete sample type, measure, chains, diffusions,
common physical Brownian paths and single Gaussian limit precede the horizon.
The chain is specified by (1.4) and its driving code law. No off-lattice Borel
assumption or Knight datum is supplied by the caller.

This theorem does not include the fundamental-matrix covariance formula.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox
open PaperSectionFourHypotheses
namespace SectionFourPaperData

variable {m d : ℕ} {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ}
  {fN : ℕ → Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {Gamma M firstBound secondBound : ℝ}
  (h : SectionFourPaperData v f fN eps Gamma M firstBound secondBound)

/-- The common physical Brownian family has the original channel law. -/
theorem brownian_isPreBrownian (x0 : Fin d → ℝ) (l : Fin m) :
    IsPreBrownian (h.brownian x0 l) (h.couplingMeasure x0) := by
  letI := channelBrownian_isPreBrownian (ι := Fin m) l
  refine ⟨fun I => ?_⟩
  exact (IsPreBrownian.hasLaw (X := channelBrownian l)
    (P := channelKMTMeasure (Fin m)) I).comp
    ⟨(h.projection_measurePreserving x0).measurable.aemeasurable,
      (h.projection_measurePreserving x0).map_eq⟩

theorem brownian_independent (x0 : Fin d → ℝ) :
    iIndepFun (fun l z t => h.brownian x0 l t z) (h.couplingMeasure x0) := by
  apply iIndepFun_comp_of_map (h.projection_measurePreserving x0).measurable
    (fun l => measurable_pi_lambda _ fun t => measurable_channelBrownian l t)
  rw [(h.projection_measurePreserving x0).map_eq]
  exact channelBrownian_paths_independent

/-- The transferred codes have the full independent reference joint law for
one population size. Taking Poisson marginals gives independent unit Poisson
channel codes; no independence between different population sizes is asserted. -/
theorem driving_code_law (x0 : Fin d → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    (h.couplingMeasure x0).map
      (KMTTransfer.familyPairCode (h.construction x0).K.β N) =
        Measure.pi (fun _ : Fin m => KMTTransfer.kmtReferenceJointLaw) :=
  KMTTransfer.map_familyPairCode (hβ := (h.construction x0).K.measurable_β)
    ((h.construction x0).K.isPreBrownian N hN)
    ((h.construction x0).K.iIndep N hN)

/-- Equation (1.4), with the original finite-scale rates, holds pointwise. -/
theorem chain_equation (x0 : Fin d → ℝ) (N : ℕ) (hN : 2 ≤ N)
    (z : sectionFourCouplingSpace m) {t : ℝ} (ht : 0 ≤ t) :
    h.chain x0 N z t = x0 + ∑ l,
      (KMTTransfer.transferredCellPath N l
        (scaledTcClock (N : ℝ) (fN N) (h.chain x0 N z) l t) z / (N : ℝ)) • v l := by
  have hX : h.chain x0 N z =
      KMTTransfer.transferredChain (N := N) (by omega) v
        ((h.chainRate_bounds x0).1 N hN) ((h.chainRate_bounds x0).2 N hN)
        (h.chainRate_measurable x0 N) x0 z := by
    funext s
    simp only [chain, KMTTransfer.transferredChainFamily, dif_pos hN]
  rw [hX]
  exact KMTTransfer.transferredChain_countableRateExtension_equation (by omega)
    v x0 h.rate (fN N) ((h.chainRate_bounds x0).1 N hN)
    ((h.chainRate_bounds x0).2 N hN) (h.chainRate_measurable x0 N) z ht

/-- The fluid trajectory solves the original drift equation. -/
theorem fluid_equation (x0 : Fin d → ℝ) : Continuous (h.fluid x0) ∧
    ∀ t : ℝ≥0, h.fluid x0 t = x0 +
      ∫ s in (0 : ℝ)..(t : ℝ), tcDrift f v (h.fluid x0 s.toNNReal) := by
  refine ⟨continuous_kurtzFluidLimit h.eps_nonneg h.rate_lipschitz.1
    h.rate_bounds.1 h.rate_bounds.2 h.rate_lipschitz.2 x0, ?_⟩
  intro t
  have ht := kurtzFluidLimit_eq (v := v) h.eps_nonneg h.rate_lipschitz.1
    h.rate_bounds.1 h.rate_bounds.2 h.rate_lipschitz.2 x0 t
  simpa only [rate, tcDrift_maskZeroRate] using ht

/-- The SDE's actual integral is pulled from the physical channel space.
The vector sum is unchanged by masking zero directions. -/
theorem diffusion_equation (x0 : Fin d → ℝ) (N : ℕ) (hN : 2 ≤ N) (T : ℝ≥0) :
    ∀ᵐ z ∂h.couplingMeasure x0,
      KMTTransfer.KurtzSDEPathsNN N f v T (h.diffusion x0 N)
        (fun l t z => channelRateIntegral T N f ((h.construction x0).Z N)
          l t (h.projection x0 z)) (fun _ => x0) z := by
  have hs := (h.projection_measurePreserving x0).quasiMeasurePreserving.ae
    ((h.construction x0).sde N hN T)
  filter_upwards [hs] with z hz
  refine ⟨hz.1, fun t ht => ?_⟩
  have he := hz.2 t ht
  have hsum : (∑ l, (channelRateIntegral T N h.rate ((h.construction x0).Z N)
      l t (h.projection x0 z) / (N : ℝ)) • v l) =
      ∑ l, (channelRateIntegral T N f ((h.construction x0).Z N)
        l t (h.projection x0 z) / (N : ℝ)) • v l := by
    apply sum_smul_congr_of_nonzero
    intro l hl
    simp only [channelRateIntegral, rate, maskZeroRate, hl, if_false]
  rw [hsum] at he
  simpa only [rate, tcDrift_maskZeroRate, diffusion] using he

/-- The Gaussian limit has continuous sample paths on every finite window. -/
theorem gaussian_continuousOn (x0 : Fin d → ℝ) (T : ℝ≥0) :
    ∀ᵐ z ∂h.couplingMeasure x0, ContinuousOn (h.gaussian x0 z) (Icc (0 : ℝ) T) :=
  (h.projection_measurePreserving x0).quasiMeasurePreserving.ae
    (sectionFourVAll_ae_continuousOn h.eps_nonneg h.rate_lipschitz.1
      h.rate_bounds.1 h.rate_bounds.2 h.rate_lipschitz.2 h.derivative_hypotheses.2.1
      h.derivative_hypotheses.2.2.1 h.derivative_hypotheses.2.2.2 x0 T)

/-- A countable intersection of integer-window events gives continuous sample
paths on the entire nonnegative time axis. -/
theorem gaussian_continuous_nonneg (x0 : Fin d → ℝ) :
    ∀ᵐ z ∂h.couplingMeasure x0,
      Continuous (fun t : ℝ≥0 => h.gaussian x0 z (t : ℝ)) := by
  have hall : ∀ᵐ z ∂h.couplingMeasure x0, ∀ n : ℕ,
      ContinuousOn (h.gaussian x0 z) (Icc (0 : ℝ) (n : ℝ≥0)) :=
    ae_all_iff.mpr (fun n => h.gaussian_continuousOn x0 (n : ℝ≥0))
  filter_upwards [hall] with z hz
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hc : ContinuousOn (fun s : ℝ≥0 => h.gaussian x0 z (s : ℝ))
      (Iic (n : ℝ≥0)) := by
    apply (hz n).comp NNReal.continuous_coe.continuousOn
    intro s hs
    exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  exact hc.continuousAt (Filter.mem_of_superset (Iio_mem_nhds hn) Iio_subset_Iic_self)

/-- All finite observations of the single process have centered joint Gaussian law. -/
theorem gaussian_finiteDimensional (x0 : Fin d → ℝ) (T : ℝ≥0)
    {k : ℕ} (t : Fin k → Icc (0 : ℝ) T) :
    HasGaussianLaw (fun z q => h.gaussian x0 z (t q)) (h.couplingMeasure x0) ∧
    (∫ z, (fun q => h.gaussian x0 z (t q)) ∂h.couplingMeasure x0) = 0 := by
  have hg := sectionFourVAll_finiteDimensional_centeredGaussian (v := v) h.eps_nonneg
    h.rate_lipschitz.1 h.rate_bounds.1 h.rate_bounds.2 h.rate_lipschitz.2
    h.derivative_hypotheses.2.1 h.derivative_hypotheses.2.2.1
    h.derivative_hypotheses.2.2.2 h.sqrtConstant h.sqrt_lipschitz x0 T t
  exact centeredGaussian_comp_measurePreserving (h.projection_measurePreserving x0) hg.1 hg.2

/-- The single limit solves the linear equation with the same physical
Brownian paths as every diffusion, and with the original rates. -/
theorem gaussian_equation (x0 : Fin d → ℝ) (T : ℝ≥0) :
    ∀ᵐ z ∂h.couplingMeasure x0, ∀ t ∈ Icc (0 : ℝ) T,
      h.gaussian x0 z t =
        (∑ l, Ripple.Analysis.BVIntegrationByParts.J
          (fun s => Real.sqrt (f l (h.fluid x0 s.toNNReal)))
          (fun s => h.brownian x0 l s.toNNReal z) t • v l) +
        ∫ s in (0 : ℝ)..t,
          h.derivative (h.fluid x0 s.toNNReal) (h.gaussian x0 z s) := by
  have hg := (h.projection_measurePreserving x0).quasiMeasurePreserving.ae
    (sectionFourVAll_ae_equation_J (v := v) h.eps_nonneg h.rate_lipschitz.1
      h.rate_bounds.1 h.rate_bounds.2 h.rate_lipschitz.2 h.derivative_hypotheses.2.1
      h.derivative_hypotheses.2.2.1 h.derivative_hypotheses.2.2.2
      h.sqrtConstant h.sqrt_lipschitz x0 T)
  filter_upwards [hg] with z hz
  intro t ht
  have he := hz t ht
  have hsum : (∑ l, Ripple.Analysis.BVIntegrationByParts.J
      (fun s => Real.sqrt (h.rate l (h.fluid x0 s.toNNReal)))
      (fun s => h.brownian x0 l s.toNNReal z) t • v l) =
      ∑ l, Ripple.Analysis.BVIntegrationByParts.J
        (fun s => Real.sqrt (f l (h.fluid x0 s.toNNReal)))
        (fun s => h.brownian x0 l s.toNNReal z) t • v l := by
    apply sum_smul_congr_of_nonzero
    intro l hl
    simp only [rate, maskZeroRate, hl, if_false]
  change h.gaussian x0 z t =
    (∑ l, Ripple.Analysis.BVIntegrationByParts.J
      (fun s => Real.sqrt (h.rate l (h.fluid x0 s.toNNReal)))
      (fun s => h.brownian x0 l s.toNNReal z) t • v l) +
    ∫ s in (0 : ℝ)..t,
      h.derivative (h.fluid x0 s.toNNReal) (h.gaussian x0 z s) at he
  rw [hsum] at he
  exact he

/-- The approximation in the paper's Euclidean norm retains a uniform
exponential moment after rescaling the random coefficient by `d + 1`. -/
theorem approximation_euclidean (x0 : Fin d → ℝ) (T : ℝ≥0) :
    ∃ (gamma : ℕ → sectionFourCouplingSpace m → ℝ) (eta C : ℝ),
      0 < eta ∧ (∀ N, 2 ≤ N → Measurable (gamma N)) ∧
      (∀ N, 2 ≤ N → ∀ z, 0 ≤ gamma N z) ∧
      (∀ N, 2 ≤ N → Integrable (fun z => Real.exp (eta * gamma N z))
        (h.couplingMeasure x0) ∧
        ∫ z, Real.exp (eta * gamma N z) ∂h.couplingMeasure x0 ≤ C) ∧
      ∀ᵐ z ∂h.couplingMeasure x0, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        paperNorm (Real.sqrt N • (h.chain x0 N z t - h.fluid x0 t.toNNReal) -
          h.gaussian x0 z t) ≤ gamma N z * Real.log (N : ℝ) / Real.sqrt N := by
  obtain ⟨gamma, eta, C, heta, hmeas, hpos, hint, hbound⟩ :=
    (h.construction x0).estimate T
  have hR : SectionFourAssembly.UniformExpMoment gamma eta C (h.couplingMeasure x0) :=
    ⟨heta, hmeas, hpos, fun N hN => (hint N hN).1, fun N hN => (hint N hN).2⟩
  let c : ℝ := (d : ℝ) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hs := uniformExpMoment_scale hR hc
  refine ⟨(fun N z => c * gamma N z), eta / c, C, hs.eta_pos,
    hs.measurable, hs.nonneg, ?_, ?_⟩
  · exact fun N hN => ⟨hs.integrable N hN, hs.integral_le N hN⟩
  · filter_upwards [hbound] with z hz
    intro N hN t ht
    exact paperNorm_error_le (hz N hN t ht)

/-- The complete conclusion on the fixed coupling. The chain is identified
by its Poisson driving law and original time-change equation. -/
structure Conclusion (x0 : Fin d → ℝ) : Prop where
  physical_law : MeasurePreserving (h.projection x0) (h.couplingMeasure x0)
    (channelKMTMeasure (Fin m))
  brownian_law : ∀ l, IsPreBrownian (h.brownian x0 l) (h.couplingMeasure x0)
  brownian_indep : iIndepFun (fun l z t => h.brownian x0 l t z) (h.couplingMeasure x0)
  brownian_continuous : ∀ l z, Continuous (fun t => h.brownian x0 l t z)
  poisson_code_law : ∀ N, 2 ≤ N → (h.couplingMeasure x0).map
    (KMTTransfer.familyPairCode (h.construction x0).K.β N) =
      Measure.pi (fun _ : Fin m => KMTTransfer.kmtReferenceJointLaw)
  chain_equation : ∀ N, 2 ≤ N → ∀ z t, 0 ≤ t →
    h.chain x0 N z t = x0 + ∑ l,
      (KMTTransfer.transferredCellPath N l
        (scaledTcClock (N : ℝ) (fN N) (h.chain x0 N z) l t) z / (N : ℝ)) • v l
  fluid_continuous : Continuous (h.fluid x0)
  fluid_equation : ∀ t : ℝ≥0, h.fluid x0 t = x0 +
    ∫ s in (0 : ℝ)..(t : ℝ), tcDrift f v (h.fluid x0 s.toNNReal)
  diffusion_adapted : ∀ N t,
    Measurable[augmentedChannelBrownianFiltration t] ((h.construction x0).Z N t)
  diffusion_continuous : ∀ N z, Continuous (fun t => h.diffusion x0 N t z)
  diffusion_equation : ∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ z ∂h.couplingMeasure x0,
    KMTTransfer.KurtzSDEPathsNN N f v T (h.diffusion x0 N)
      (fun l t z => channelRateIntegral T N f ((h.construction x0).Z N)
        l t (h.projection x0 z)) (fun _ => x0) z
  gaussian_continuous : ∀ T : ℝ≥0, ∀ᵐ z ∂h.couplingMeasure x0,
    ContinuousOn (h.gaussian x0 z) (Icc (0 : ℝ) T)
  gaussian_continuous_nonneg : ∀ᵐ z ∂h.couplingMeasure x0,
    Continuous (fun t : ℝ≥0 => h.gaussian x0 z (t : ℝ))
  gaussian_law : ∀ (T : ℝ≥0) (k : ℕ) (t : Fin k → Icc (0 : ℝ) T),
    HasGaussianLaw (fun z q => h.gaussian x0 z (t q)) (h.couplingMeasure x0) ∧
    (∫ z, (fun q => h.gaussian x0 z (t q)) ∂h.couplingMeasure x0) = 0
  gaussian_equation : ∀ T : ℝ≥0, ∀ᵐ z ∂h.couplingMeasure x0,
    ∀ t ∈ Icc (0 : ℝ) T, h.gaussian x0 z t =
      (∑ l, Ripple.Analysis.BVIntegrationByParts.J
        (fun s => Real.sqrt (f l (h.fluid x0 s.toNNReal)))
        (fun s => h.brownian x0 l s.toNNReal z) t • v l) +
      ∫ s in (0 : ℝ)..t, h.derivative (h.fluid x0 s.toNNReal) (h.gaussian x0 z s)
  approximation : ∀ T : ℝ≥0,
    ∃ (gamma : ℕ → sectionFourCouplingSpace m → ℝ) (eta C : ℝ),
      0 < eta ∧ (∀ N, 2 ≤ N → Measurable (gamma N)) ∧
      (∀ N, 2 ≤ N → ∀ z, 0 ≤ gamma N z) ∧
      (∀ N, 2 ≤ N → Integrable (fun z => Real.exp (eta * gamma N z)) (h.couplingMeasure x0) ∧
        ∫ z, Real.exp (eta * gamma N z) ∂h.couplingMeasure x0 ≤ C) ∧
      ∀ᵐ z ∂h.couplingMeasure x0, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        paperNorm (Real.sqrt N • (h.chain x0 N z t - h.fluid x0 t.toNNReal) -
          h.gaussian x0 z t) ≤ gamma N z * Real.log (N : ℝ) / Real.sqrt N

end SectionFourPaperData

/-- Kurtz's Theorem 4.4 on a single concrete coupling, from the printed
coefficient hypotheses. All internal Lipschitz and Knight premises are
produced by the construction, and the exponential moments include integrability. -/
theorem kurtz_theorem_four_four {m d : ℕ}
    {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ}
    {fN : ℕ → Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
    {Gamma M firstBound secondBound : ℝ}
    (h : SectionFourPaperData v f fN eps Gamma M firstBound secondBound)
    (x0 : Fin d → ℝ) : h.Conclusion x0 where
  physical_law := h.projection_measurePreserving x0
  brownian_law := h.brownian_isPreBrownian x0
  brownian_indep := h.brownian_independent x0
  brownian_continuous := fun l z => channelBrownian_continuous l (h.projection x0 z)
  poisson_code_law := h.driving_code_law x0
  chain_equation := fun N hN z t ht => h.chain_equation x0 N hN z ht
  fluid_continuous := (h.fluid_equation x0).1
  fluid_equation := (h.fluid_equation x0).2
  diffusion_adapted := (h.construction x0).adapted
  diffusion_continuous := fun N z => (h.construction x0).continuous N (h.projection x0 z)
  diffusion_equation := h.diffusion_equation x0
  gaussian_continuous := h.gaussian_continuousOn x0
  gaussian_continuous_nonneg := h.gaussian_continuous_nonneg x0
  gaussian_law := fun T _ t => h.gaussian_finiteDimensional x0 T t
  gaussian_equation := h.gaussian_equation x0
  approximation := h.approximation_euclidean x0

end Ripple.Kurtz.StrongApprox
