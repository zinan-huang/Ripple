import Ripple.Kurtz.StrongApprox.WienerIntegralGaussian
import Ripple.Kurtz.StrongApprox.ChannelProductTransport

/-!
# Finite independent Gaussian channels

The abstract assembly step converts scalar channel laws into a Gaussian vector
law, zero coordinate means, and its full covariance matrix. The final theorem
supplies these scalar laws from the constructed Brownian channels.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal Topology

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Linear assembly of scalar channel values along fixed jump vectors. -/
def gaussianChannelAssembly {d : ℕ} (l : ι → Fin d → ℝ) :
    (ι → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (l i)

@[simp] theorem gaussianChannelAssembly_apply {d : ℕ}
    (l : ι → Fin d → ℝ) (x : ι → ℝ) :
    gaussianChannelAssembly l x = ∑ i, x i • l i := by
  simp [gaussianChannelAssembly]

/-- Independence of scalar Gaussian channels gives a Gaussian vector. -/
theorem independentGaussianChannels_gaussian {d : ℕ}
    {X : ι → Ω → ℝ} {v : ι → ℝ≥0}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 (v i)) P)
    (hind : iIndepFun X P) (l : ι → Fin d → ℝ) :
    HasGaussianLaw (fun ω => ∑ i, X i ω • l i) P := by
  have hjoint : HasGaussianLaw (fun ω i => X i ω) P :=
    hind.hasGaussianLaw (fun i => (hlaw i).hasGaussianLaw)
  simpa using hjoint.map_fun (gaussianChannelAssembly l)

/-- Centering, stated coordinatewise so it applies to the ordinary finite Pi norm. -/
theorem independentGaussianChannels_mean {d : ℕ}
    {X : ι → Ω → ℝ} {v : ι → ℝ≥0}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 (v i)) P)
    (l : ι → Fin d → ℝ) (j : Fin d) :
    ∫ ω, ∑ i, X i ω * l i j ∂P = 0 := by
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (hlaw i).hasGaussianLaw.integrable.mul_const (l i j))]
  have hm : ∀ i, ∫ ω, X i ω ∂P = 0 := by
    intro i
    rw [(hlaw i).integral_eq, integral_id_gaussianReal]
  simp_rw [integral_mul_const, hm, zero_mul]
  simp

/-- Covariance of two deterministic scalar linear combinations of the channels. -/
theorem independentGaussianChannels_covariance
    {X : ι → Ω → ℝ} {v : ι → ℝ≥0}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 (v i)) P)
    (hind : iIndepFun X P) (c b : ι → ℝ) :
    cov[fun ω => ∑ i, c i * X i ω, fun ω => ∑ i, b i * X i ω; P] =
      ∑ i, (v i : ℝ) * c i * b i := by
  classical
  have htwo : ∀ i, MemLp (X i) 2 P :=
    fun i => (hlaw i).hasGaussianLaw.memLp_two
  rw [covariance_fun_sum_fun_sum
    (fun i => (htwo i).const_mul (c i))
    (fun i => (htwo i).const_mul (b i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_self (hlaw i).aemeasurable, (hlaw i).variance_eq,
      variance_id_gaussianReal]
    ring
  · intro j _ hji
    rw [covariance_const_mul_left, covariance_const_mul_right,
      (hind.indepFun hji.symm).covariance_eq_zero (htwo i) (htwo j)]
    simp
  · simp

/-- Full covariance matrix: the sum of variance-weighted outer products. -/
theorem independentGaussianChannels_covariance_matrix {d : ℕ}
    {X : ι → Ω → ℝ} {v : ι → ℝ≥0}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 (v i)) P)
    (hind : iIndepFun X P) (l : ι → Fin d → ℝ) (j k : Fin d) :
    cov[fun ω => (∑ i, X i ω • l i) j,
      fun ω => (∑ i, X i ω • l i) k; P] =
      ∑ i, (v i : ℝ) * l i j * l i k := by
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
    independentGaussianChannels_covariance hlaw hind (fun i => l i j) (fun i => l i k)

/-- Channel functionals inherit independence from the actual product construction.
Almost-everywhere measurability is sufficient, as supplied by the Gaussian limit theorem. -/
theorem channelKMT_functional_independent
    (F : ι → AllTimeKMT.AllTimeKMTSpace → ℝ)
    (hF : ∀ i, AEMeasurable (F i) AllTimeKMT.allTimeKMTMeasure) :
    iIndepFun (fun i (ω : channelKMTSpace ι) => F i (ω i))
      (channelKMTMeasure ι) := by
  apply channelKMTEval_iIndep.comp₀ F
    (fun i => (measurable_pi_apply i).aemeasurable)
  intro i
  rw [(channelKMTEval_measurePreserving i).map_eq]
  exact hF i

/-- Transport a scalar functional's law through each product coordinate. -/
theorem channelKMT_functional_law
    (F : ι → AllTimeKMT.AllTimeKMTSpace → ℝ) (v : ι → ℝ≥0)
    (hlaw : ∀ i, HasLaw (F i) (gaussianReal 0 (v i)) AllTimeKMT.allTimeKMTMeasure)
    (i : ι) :
    HasLaw (fun ω : channelKMTSpace ι => F i (ω i))
      (gaussianReal 0 (v i)) (channelKMTMeasure ι) :=
  (hlaw i).fun_comp (channelKMTEval_measurePreserving i).hasLaw

/-- The concrete Brownian channels do satisfy the zero-start condition omitted
from `DyadicBrownianOn`. -/
theorem channelKMTBrownian_zero_start (i : ι) (ω : channelKMTSpace ι) :
    channelKMTBrownian i 0 ω = 0 :=
  AllTimeKMTLaws.allTimeKMTBrownian_zero_time (ω i)

/-- The scalar pathwise Wiener functional on a canonical Brownian channel. -/
def channelWienerIntegral (a : ι → ℝ → ℝ) (i : ι) (t : ℝ)
    (ω : channelKMTSpace ι) : ℝ :=
  Ripple.Analysis.BVIntegrationByParts.J (a i) (fun s => channelKMTBrownian i s ω) t

/-- Scalar law at every time within a dyadic horizon of the constructed channel. -/
theorem channelWienerIntegral_law
    (a : ι → ℝ → ℝ) (j : ℕ) (K : ι → ℝ≥0) {t : ℝ}
    (ha : ∀ i, LipschitzOnWith (K i) (a i) (Set.Icc 0 ((2 : ℝ) ^ j)))
    (ht : t ∈ Set.Icc 0 ((2 : ℝ) ^ j)) (i : ι) :
    HasLaw (channelWienerIntegral a i t)
      (gaussianReal 0 (Real.toNNReal (∫ s in 0..t, a i s ^ 2)))
      (channelKMTMeasure ι) := by
  exact wienerIntegral_gaussian (channelKMTBrownian_dyadicBrownianOn i j)
    (ha i) ht (Filter.Eventually.of_forall (channelKMTBrownian_zero_start i))

/-- Independence of the actual pathwise channel integrals, including completion-measurable
functionals obtained as almost-sure limits. -/
theorem channelWienerIntegral_independent
    (a : ι → ℝ → ℝ) (j : ℕ) (K : ι → ℝ≥0) {t : ℝ}
    (ha : ∀ i, LipschitzOnWith (K i) (a i) (Set.Icc 0 ((2 : ℝ) ^ j)))
    (ht : t ∈ Set.Icc 0 ((2 : ℝ) ^ j)) :
    iIndepFun (fun i => channelWienerIntegral a i t) (channelKMTMeasure ι) := by
  let F : ι → AllTimeKMT.AllTimeKMTSpace → ℝ := fun i ω =>
    Ripple.Analysis.BVIntegrationByParts.J (a i)
      (fun s => AllTimeKMT.allTimeKMTBrownian s ω) t
  have hF : ∀ i, AEMeasurable (F i) AllTimeKMT.allTimeKMTMeasure := by
    intro i
    exact (wienerIntegral_gaussian
      (AllTimeKMTBrownianLaw.allTimeKMTBrownian_dyadicBrownianOn j)
      (ha i) ht
      (Filter.Eventually.of_forall AllTimeKMTLaws.allTimeKMTBrownian_zero_time)).aemeasurable
  exact channelKMT_functional_independent F hF

/-- At each time the actual independent Wiener channels form a centered Gaussian vector,
with the integral-weighted outer-product covariance matrix. -/
theorem channelWienerIntegral_vector {d : ℕ}
    (a : ι → ℝ → ℝ) (j : ℕ) (K : ι → ℝ≥0) {t : ℝ}
    (ha : ∀ i, LipschitzOnWith (K i) (a i) (Set.Icc 0 ((2 : ℝ) ^ j)))
    (ht : t ∈ Set.Icc 0 ((2 : ℝ) ^ j)) (l : ι → Fin d → ℝ) :
    HasGaussianLaw (fun ω => ∑ i, channelWienerIntegral a i t ω • l i)
      (channelKMTMeasure ι) ∧
    (∀ r : Fin d, ∫ ω, ∑ i, channelWienerIntegral a i t ω * l i r
      ∂channelKMTMeasure ι = 0) ∧
    (∀ r q : Fin d,
      cov[fun ω => (∑ i, channelWienerIntegral a i t ω • l i) r,
        fun ω => (∑ i, channelWienerIntegral a i t ω • l i) q;
        channelKMTMeasure ι] =
      ∑ i, (∫ s in 0..t, a i s ^ 2) * l i r * l i q) := by
  have hlaw := channelWienerIntegral_law a j K ha ht
  have hind := channelWienerIntegral_independent a j K ha ht
  refine ⟨independentGaussianChannels_gaussian hlaw hind l,
    independentGaussianChannels_mean hlaw l, ?_⟩
  intro r q
  have h := independentGaussianChannels_covariance_matrix hlaw hind l r q
  calc
    _ = ∑ i, (Real.toNNReal (∫ s in 0..t, a i s ^ 2) : ℝ) * l i r * l i q := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.coe_toNNReal _ (intervalIntegral.integral_nonneg ht.1
        (fun _ _ => sq_nonneg _))]

end Ripple.Kurtz.StrongApprox
