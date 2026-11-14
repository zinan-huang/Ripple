import Ripple.Kurtz.StrongApprox.SectionFourGaussianLaw
import Ripple.Kurtz.StrongApprox.SectionFourPathLaw

/-!
# Identifying the chosen Section Four process with its linear path image

The arbitrary extensions selected by the Volterra solver have no effect on
observations inside the construction horizon.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox
namespace VolterraGaussian

variable {m d : ℕ}

/-- Assemble scalar continuous channel paths along their jump directions. -/
def assemblePaths {T : ℝ} (v : Fin m → Fin d → ℝ) :
    (Fin m → C(Icc (0 : ℝ) T, ℝ)) →L[ℝ] C(Icc (0 : ℝ) T, Fin d → ℝ) where
  toFun c := ⟨fun t => ∑ l, c l t • v l,
    continuous_finsetSum _ fun l _ => (c l).continuous.smul continuous_const⟩
  map_add' c b := by
    ext t j
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext t j
    simp [Finset.mul_sum, mul_assoc]
  cont := by
    have hC : 0 ≤ ∑ l, ‖v l‖ := Finset.sum_nonneg fun l _ => norm_nonneg _
    have hLip : LipschitzWith ⟨∑ l, ‖v l‖, hC⟩
        (fun c : Fin m → C(Icc (0 : ℝ) T, ℝ) =>
          (⟨fun t => ∑ l, c l t • v l,
            continuous_finsetSum _ fun l _ => (c l).continuous.smul continuous_const⟩ :
              C(Icc (0 : ℝ) T, Fin d → ℝ))) := by
      refine LipschitzWith.of_dist_le_mul fun c b => ?_
      rw [dist_eq_norm, dist_eq_norm]
      apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))).2
      intro t
      change ‖(∑ l, c l t • v l) - ∑ l, b l t • v l‖ ≤ _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ l, ‖c l t • v l - b l t • v l‖ := norm_sum_le _ _
        _ ≤ ∑ l, ‖c - b‖ * ‖v l‖ := by
          apply Finset.sum_le_sum
          intro l _
          rw [← sub_smul, norm_smul]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact (ContinuousMap.norm_coe_le_norm (c l - b l) t).trans
            (norm_le_pi_norm (c - b) l)
        _ = (∑ l, ‖v l‖) * ‖c - b‖ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    exact hLip.continuous

@[simp] theorem assemblePaths_apply {T : ℝ} (v : Fin m → Fin d → ℝ)
    (c : Fin m → C(Icc (0 : ℝ) T, ℝ)) (t : Icc (0 : ℝ) T) :
    assemblePaths v c t = ∑ l, c l t • v l := rfl

/-- Uniqueness identifies any solution with the observation operator, even
when the chosen functions differ outside the time window. -/
theorem observations_eq {k : ℕ}
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hT : 0 ≤ T)
    (hAb : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K)
    (t : Fin k → Icc (0 : ℝ) T) (c : C(Icc (0 : ℝ) T, Fin d → ℝ))
    {V : ℝ → Fin d → ℝ}
    (hV : Analysis.LinearVolterra.IsSolution A (extendPath hT c) V T) :
    (fun q => V (t q)) = observationCLM hA hT hAb t c := by
  funext q
  exact Analysis.LinearVolterra.eqOn_of_solution hA hV
    (volterraSol_spec hA (continuous_extendPath hT c) hT)
    hT K.coe_nonneg hAb (t q).property

end VolterraGaussian

open VolterraGaussian

/-- Every finite vector of observations of the installed limit is centered
Gaussian on the original Brownian channel space. -/
theorem sectionFourV_finiteDimensional_centeredGaussian
    {m d k : ℕ} {v : Fin m → Fin d → ℝ}
    {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ} {M : ℝ}
    {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L1 L2 : ℝ}
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) (t : Fin k → Icc (0 : ℝ) T) :
    HasGaussianLaw (fun ω q => sectionFourV F' f v x0 T ω (t q))
      (channelKMTMeasure (Fin m)) ∧
    (∫ ω, (fun q => sectionFourV F' f v x0 T ω (t q))
      ∂channelKMTMeasure (Fin m)) = 0 := by
  have hA := continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  have hL1n : 0 ≤ L1 := (norm_nonneg (F' 0)).trans (hL1 0)
  let K : ℝ≥0 := ⟨L1, hL1n⟩
  have hAb : ∀ s ∈ Icc (0 : ℝ) T, ‖sectionFourCoeff F' f v x0 s‖ ≤ K :=
    fun s _ => hL1 _
  let B := fun ω : channelKMTSpace (Fin m) => fun l : Fin m => brownianPath T l ω
  let Jmap : (Fin m → C(Icc (0 : ℝ) T, ℝ)) →L[ℝ]
      (Fin m → C(Icc (0 : ℝ) T, ℝ)) :=
    ContinuousLinearMap.pi fun l =>
      (JPathCLM T (lipschitzOn_sqrt_fluid (v := v) heps hM hf0 hfB h319 Lg hLg x0 T l)).comp
        (ContinuousLinearMap.proj l)
  let L := (observationCLM hA T.coe_nonneg hAb t).comp ((assemblePaths v).comp Jmap)
  have hBG : HasGaussianLaw B (channelKMTMeasure (Fin m)) := brownianPath_joint_gaussian T
  have heq : (fun ω => L (B ω)) =ᵐ[channelKMTMeasure (Fin m)]
      (fun ω q => sectionFourV F' f v x0 T ω (t q)) := by
    filter_upwards [sectionFourV_ae_equation_J heps hM hf0 hfB h319 hL2n hL2 Lg hLg x0 T]
      with ω hω
    let c := assemblePaths v (Jmap (B ω))
    have hsol : Analysis.LinearVolterra.IsSolution (sectionFourCoeff F' f v x0)
        (extendPath T.coe_nonneg c) (sectionFourV F' f v x0 T ω) T := by
      refine ⟨continuous_sectionFourV heps hM hf0 hfB h319 hL2n hL2 x0 T ω, ?_⟩
      intro s hs
      rw [extendPath_of_mem T.coe_nonneg c hs, hω s hs]
      congr 1
      change (∑ l, Ripple.Analysis.BVIntegrationByParts.J
        (fun r => Real.sqrt (f l (kurtzFluidLimit f v x0 r.toNNReal)))
        (fun r => channelBrownian l r.toNNReal ω) s • v l) =
          ∑ l, (JPathCLM T
            (lipschitzOn_sqrt_fluid (v := v) heps hM hf0 hfB h319 Lg hLg x0 T l)
            (brownianPath T l ω)) ⟨s, hs⟩ • v l
      apply Finset.sum_congr rfl
      intro l _
      rw [JPathCLM_brownianPath]
    exact (observations_eq hA T.coe_nonneg hAb t c hsol).symm
  refine ⟨(hBG.map_fun L).congr heq, ?_⟩
  calc
    (∫ ω, (fun q => sectionFourV F' f v x0 T ω (t q))
      ∂channelKMTMeasure (Fin m)) = ∫ ω, L (B ω) ∂channelKMTMeasure (Fin m) :=
        integral_congr_ae heq.symm
    _ = L (∫ ω, B ω ∂channelKMTMeasure (Fin m)) := L.integral_comp_comm hBG.integrable
    _ = 0 := by
      rw [show (∫ ω, B ω ∂channelKMTMeasure (Fin m)) = 0 from brownianPath_joint_mean T]
      exact map_zero L

end Ripple.Kurtz.StrongApprox
