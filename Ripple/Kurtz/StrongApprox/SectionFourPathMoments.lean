import Ripple.Kurtz.StrongApprox.SectionFourGaussianIdentification

/-!
# Uniform path moments of the actual Section Four process

The full compact solution path is a continuous linear image of the forcing
path. The actual chosen process agrees with this image on one common event,
by its pathwise integral equation and Volterra uniqueness.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox
namespace VolterraGaussian

variable {d : ℕ}

/-- Solve the linear Volterra equation as a continuous linear map on compact paths. -/
def solutionPathCLM
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hT : 0 ≤ T)
    (hAb : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K) :
    C(Icc (0 : ℝ) T, Fin d → ℝ) →L[ℝ] C(Icc (0 : ℝ) T, Fin d → ℝ) where
  toFun c := ⟨fun t => volterraSol A T (extendPath hT c) t,
    (volterraSol_spec hA (continuous_extendPath hT c) hT).continuous.comp
      continuous_subtype_val⟩
  map_add' c b := by
    have hsum : extendPath hT (c + b) = fun s => extendPath hT c s + extendPath hT b s := rfl
    ext t j
    change volterraSol A T (extendPath hT (c + b)) t j = _
    rw [hsum, volterraSol_add hA hT hAb
      (continuous_extendPath hT c) (continuous_extendPath hT b) t.property]
    rfl
  map_smul' a c := by
    have hsmul : extendPath hT (a • c) = fun s => a • extendPath hT c s := rfl
    ext t j
    change volterraSol A T (extendPath hT (a • c)) t j = _
    rw [hsmul, volterraSol_smul hA hT hAb (continuous_extendPath hT c) a t.property]
    rfl
  cont := by
    have hLip : LipschitzWith (Real.exp ((K : ℝ) * T)).toNNReal
        (fun c : C(Icc (0 : ℝ) T, Fin d → ℝ) =>
          (⟨fun t => volterraSol A T (extendPath hT c) t,
            (volterraSol_spec hA (continuous_extendPath hT c) hT).continuous.comp
              continuous_subtype_val⟩ : C(Icc (0 : ℝ) T, Fin d → ℝ))) := by
      refine LipschitzWith.of_dist_le_mul fun c b => ?_
      rw [Real.coe_toNNReal _ (Real.exp_nonneg _), dist_eq_norm, dist_eq_norm]
      apply (ContinuousMap.norm_le _
        (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).2
      intro t
      have h := norm_volterraSol_sub_le hA hT K.coe_nonneg hAb
        (continuous_extendPath hT c) (continuous_extendPath hT b)
        (norm_nonneg (c - b)) (fun s _ => by
          exact ContinuousMap.norm_coe_le_norm (c - b)
            ⟨max 0 (min T s), le_max_left _ _, max_le hT (min_le_left _ _)⟩)
        t.property
      simpa only [ContinuousMap.sub_apply, ContinuousMap.coe_mk, mul_comm] using h
    exact hLip.continuous

@[simp] theorem solutionPathCLM_apply
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hT : 0 ≤ T)
    (hAb : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K)
    (c : C(Icc (0 : ℝ) T, Fin d → ℝ)) (t : Icc (0 : ℝ) T) :
    solutionPathCLM hA hT hAb c t = volterraSol A T (extendPath hT c) t := rfl

/-- Uniqueness identifies the whole restricted solution path at once. -/
theorem solutionPath_eq
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hT : 0 ≤ T)
    (hAb : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K)
    (c : C(Icc (0 : ℝ) T, Fin d → ℝ)) {V : ℝ → Fin d → ℝ}
    (hV : Analysis.LinearVolterra.IsSolution A (extendPath hT c) V T) :
    (⟨fun t => V t, hV.continuous.comp continuous_subtype_val⟩ :
      C(Icc (0 : ℝ) T, Fin d → ℝ)) = solutionPathCLM hA hT hAb c := by
  ext t j
  exact congrFun (Analysis.LinearVolterra.eqOn_of_solution hA hV
    (volterraSol_spec hA (continuous_extendPath hT c) hT)
    hT K.coe_nonneg hAb t.property) j

end VolterraGaussian

section SectionFour

variable {m d : ℕ} {v : Fin m → Fin d → ℝ}
    {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ} {M : ℝ}
    {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L2 : ℝ}
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)

/-- The actual chosen process restricted to its construction horizon. -/
def sectionFourVPath (x0 : Fin d → ℝ) (T : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) : C(Icc (0 : ℝ) (T : ℝ), Fin d → ℝ) :=
  ⟨fun t => sectionFourV F' f v x0 T ω t,
    (continuous_sectionFourV heps hM hf0 hfB h319 hL2n hL2 x0 T ω).comp
      continuous_subtype_val⟩

@[simp] theorem sectionFourVPath_apply (x0 : Fin d → ℝ) (T : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) (t : Icc (0 : ℝ) (T : ℝ)) :
    sectionFourVPath (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T ω t =
      sectionFourV F' f v x0 T ω t := rfl

/-- A single square-integrable path norm dominates every time evaluation. -/
theorem norm_sectionFourV_le_pathNorm (x0 : Fin d → ℝ) (T : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) {s : ℝ} (hs : s ∈ Icc 0 (T : ℝ)) :
    ‖sectionFourV F' f v x0 T ω s‖ ≤
      ‖sectionFourVPath (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T ω‖ :=
  ContinuousMap.norm_coe_le_norm
    (sectionFourVPath (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T ω) ⟨s, hs⟩

open VolterraGaussian

/-- The actual compact solution path is Gaussian and has a square-integrable
uniform norm. Measurability is transported by equality on one common event. -/
theorem sectionFourVPath_moments {L1 : ℝ}
    (hL1 : ∀ x, ‖F' x‖ ≤ L1) (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) :
    HasGaussianLaw (sectionFourVPath (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T)
      (channelKMTMeasure (Fin m)) ∧
    MemLp (sectionFourVPath (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T) 2
      (channelKMTMeasure (Fin m)) := by
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
  let L := (solutionPathCLM hA T.coe_nonneg hAb).comp ((assemblePaths v).comp Jmap)
  have hBG : HasGaussianLaw B (channelKMTMeasure (Fin m)) := brownianPath_joint_gaussian T
  have heq : (fun ω => L (B ω)) =ᵐ[channelKMTMeasure (Fin m)]
      sectionFourVPath (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T := by
    filter_upwards [sectionFourV_ae_equation_J heps hM hf0 hfB h319 hL2n hL2 Lg hLg x0 T]
      with ω hω
    let c := assemblePaths v (Jmap (B ω))
    have hsol : Analysis.LinearVolterra.IsSolution (sectionFourCoeff F' f v x0)
        (extendPath T.coe_nonneg c) (sectionFourV F' f v x0 T ω) T := by
      refine ⟨continuous_sectionFourV heps hM hf0 hfB h319 hL2n hL2 x0 T ω, ?_⟩
      intro s hs
      rw [extendPath_of_mem T.coe_nonneg c hs, hω s hs]
      congr 1
      change (∑ l, Analysis.BVIntegrationByParts.J
        (fun r => Real.sqrt (f l (kurtzFluidLimit f v x0 r.toNNReal)))
        (fun r => channelBrownian l r.toNNReal ω) s • v l) =
          ∑ l, (JPathCLM T
            (lipschitzOn_sqrt_fluid (v := v) heps hM hf0 hfB h319 Lg hLg x0 T l)
            (brownianPath T l ω)) ⟨s, hs⟩ • v l
      apply Finset.sum_congr rfl
      intro l _
      rw [JPathCLM_brownianPath]
    exact (solutionPath_eq hA T.coe_nonneg hAb c hsol).symm
  have hG := (hBG.map_fun L).congr heq
  exact ⟨hG, hG.memLp_two⟩

/-- Direct scalar form of the uniform second-moment bound. -/
theorem sectionFourVPath_integrable_norm_sq {L1 : ℝ}
    (hL1 : ∀ x, ‖F' x‖ ≤ L1) (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) :
    Integrable (fun ω =>
      ‖sectionFourVPath (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T ω‖ ^ 2)
      (channelKMTMeasure (Fin m)) :=
  (sectionFourVPath_moments (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T).2.norm.integrable_sq

end SectionFour
end Ripple.Kurtz.StrongApprox
