import Ripple.Kurtz.StrongApprox.SectionFourRTailKurtz
import Ripple.Kurtz.StrongApprox.DeterministicItoBridge

/-!
# Continuous paths and the deterministic forcing of the Section Four limit

The integral representative used by `sectionFourV` agrees with the deterministic
integration-by-parts functional simultaneously on the whole time window.
The Lipschitz constant of the fluid path is derived from the bounded drift.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic Ripple.Stochastic.ContinuousItoLinear
open Ripple.Stochastic.ContinuousAdaptedIntegrand
open Ripple.Stochastic.FilteredItoIntegralCLM

variable {m d : ℕ} {v : Fin m → Fin d → ℝ}
  {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ} {M : ℝ}
  {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L2 : ℝ}

/-- Bounded rates give a global time-Lipschitz constant for the fluid solution. -/
theorem lipschitzWith_kurtzFluidLimit (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (x0 : Fin d → ℝ) :
    LipschitzWith ⟨kurtzDriftBound v eps, kurtzDriftBound_nonneg heps⟩
      (kurtzFluidLimit f v x0) := by
  have hc : Continuous fun r : ℝ => tcDrift f v (kurtzFluidLimit f v x0 r.toNNReal) :=
    (continuous_tcDrift (continuous_rate_of_lip heps hM h319) v).comp
    ((continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0).comp continuous_real_toNNReal)
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [dist_eq_norm, kurtzFluidLimit_eq heps hM hf0 hfB h319 x0 s,
    kurtzFluidLimit_eq heps hM hf0 hfB h319 x0 t, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 s) (hc.intervalIntegrable 0 t), NNReal.dist_eq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (t : ℝ)) (b := (s : ℝ)) (C := kurtzDriftBound v eps)
    (f := fun r => tcDrift f v (kurtzFluidLimit f v x0 r.toNNReal))
    (fun r _ => norm_tcDrift_le_kurtzDriftBound hf0 hfB (kurtzFluidLimit f v x0 r.toNNReal))
  exact h

/-- The deterministic noise coefficient along the fluid trajectory is Lipschitz. -/
theorem lipschitzOn_sqrt_fluid (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) (l : Fin m) :
    LipschitzOnWith (Lg l * ⟨kurtzDriftBound v eps, kurtzDriftBound_nonneg heps⟩)
      (fun s : ℝ => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal)))
      (Icc 0 (T : ℝ)) := by
  have hXl := lipschitzWith_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0
  apply LipschitzOnWith.of_dist_le_mul
    (K := Lg l * ⟨kurtzDriftBound v eps, kurtzDriftBound_nonneg heps⟩)
  intro s hs t ht
  have hx := hXl.dist_le_mul s.toNNReal t.toNNReal
  rw [dist_eq_norm, NNReal.dist_eq, Real.coe_toNNReal s hs.1,
    Real.coe_toNNReal t ht.1] at hx
  rw [Real.dist_eq, Real.dist_eq]
  calc
    |Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal)) -
        Real.sqrt (f l (kurtzFluidLimit f v x0 t.toNNReal))| ≤
        Lg l * ‖kurtzFluidLimit f v x0 s.toNNReal -
          kurtzFluidLimit f v x0 t.toNNReal‖ := hLg l _ _
    _ ≤ Lg l * (kurtzDriftBound v eps * |s - t|) :=
      mul_le_mul_of_nonneg_left hx (Lg l).coe_nonneg
    _ = _ := by
      rw [NNReal.coe_mul]
      change (Lg l : ℝ) * (kurtzDriftBound v eps * |s - t|) =
        (Lg l : ℝ) * kurtzDriftBound v eps * |s - t|
      ring

/-- Every chosen path is continuous, including the null-set choices of the integral. -/
theorem continuous_sectionFourV (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) (ω : channelKMTSpace (Fin m)) :
    Continuous (sectionFourV F' f v x0 T ω) :=
  (sectionFourV_isSolution heps hM hf0 hfB h319 hL2n hL2 x0 T ω).continuous

attribute [local instance] channelBrownian_isFilteredPreBrownian_augmented

/-- Equality of the actual channel integral with `J`, on one full-measure event.
The Lipschitz condition here concerns the deterministic time integrand. -/
theorem channelSqrtIntegral_ae_forall_eq_J
    (hf : ∀ l, Continuous (f l)) (hfB : ∀ l x, f l x ≤ eps l)
    {X : ℝ≥0 → Fin d → ℝ} (hX : Continuous X) (T : ℝ≥0) (l : Fin m)
    {K : ℝ≥0}
    (ha : LipschitzOnWith K (fun s : ℝ => Real.sqrt (f l (X s.toNNReal)))
      (Icc 0 (T : ℝ))) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t : Icc (0 : ℝ≥0) T,
      channelSqrtIntegral T f (fun s _ => X s) l t.val ω =
        Ripple.Analysis.BVIntegrationByParts.J
          (fun s => Real.sqrt (f l (X s.toNNReal)))
          (fun s => channelBrownian l s.toNNReal ω) (t.val : ℝ) := by
  let hm := memLp_sqrt_rate (μ := channelKMTMeasure (Fin m))
    (F := augmentedChannelBrownianFiltration) (Z := fun s _ => X s) T
    (measurable_channelBrownian l) (hf l) (hfB l)
    (fun _ => measurable_const) (fun _ => hX)
  let φ := hm.toLp _
  have hband : ∀ᵐ z ∂(trimMeasure_T (𝓖 := augmentedChannelBrownianFiltration)
      (μ := channelKMTMeasure (Fin m)) T (measurable_channelBrownian l)),
      z ∈ Ioc 0 T ×ˢ (univ : Set (channelKMTSpace (Fin m))) := by
    rw [trimMeasure_T_eq_restrict]
    exact ae_restrict_mem (measurableSet_predictable_Ioc_prod
      (𝓕 := augmentedChannelBrownianFiltration) 0 T MeasurableSet.univ)
  have hφ : (φ : ℝ≥0 × channelKMTSpace (Fin m) → ℝ) =ᵐ[
      trimMeasure_T (𝓖 := augmentedChannelBrownianFiltration)
        (μ := channelKMTMeasure (Fin m)) T (measurable_channelBrownian l)]
      DeterministicItoBridge.targetFn (fun s => Real.sqrt (f l (X s.toNNReal))) T := by
    filter_upwards [hm.coeFn_toLp, hband] with z hz hzt
    rw [hz]
    simp [DeterministicItoBridge.targetFn, hzt.1, Function.uncurry]
  have heq : channelSqrtIntegral T f (fun s _ => X s) l =
      continuousItoNN T (channelBrownian_continuous l) (measurable_channelBrownian l) φ := by
    unfold channelSqrtIntegral
    exact continuousItoOfFun_of_memLp T _ _ hm
  apply DeterministicItoBridge.ae_forall_eq_J
    (𝓖 := augmentedChannelBrownianFiltration) T ha (measurable_channelBrownian l)
    (Filter.Eventually.of_forall (channelBrownian_continuous l)) φ hφ
    (fun t ω => channelSqrtIntegral T f (fun s _ => X s) l t.val ω)
  · intro t
    rw [heq]
    exact continuousItoNN_ae_eq T _ _ φ t.2.2
  · exact Filter.Eventually.of_forall fun ω =>
      (continuous_channelSqrtIntegral hf hfB (fun _ => measurable_const)
        (fun _ => hX) l ω).comp continuous_subtype_val

/-- The installed limit solves the pathwise `J` equation, for all window times
on one event. No equality of independently selected time-slice versions is assumed. -/
theorem sectionFourV_ae_equation_J (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t ∈ Icc (0 : ℝ) T,
      sectionFourV F' f v x0 T ω t =
        (∑ l, Ripple.Analysis.BVIntegrationByParts.J
          (fun s => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal)))
          (fun s => channelBrownian l s.toNNReal ω) t • v l) +
        ∫ s in (0 : ℝ)..t, sectionFourCoeff F' f v x0 s (sectionFourV F' f v x0 T ω s) := by
  have hf := continuous_rate_of_lip heps hM h319
  have hXc := continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0
  have hXl := lipschitzWith_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0
  have hall : ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ l : Fin m,
      ∀ t : Icc (0 : ℝ≥0) T,
      channelSqrtIntegral T f (fun s _ => kurtzFluidLimit f v x0 s) l t.val ω =
        Ripple.Analysis.BVIntegrationByParts.J
          (fun s => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal)))
          (fun s => channelBrownian l s.toNNReal ω) (t.val : ℝ) := by
    rw [ae_all_iff]
    intro l
    apply channelSqrtIntegral_ae_forall_eq_J hf hfB hXc T l
    exact lipschitzOn_sqrt_fluid heps hM hf0 hfB h319 Lg hLg x0 T l
  filter_upwards [hall] with ω hω t ht
  rw [(sectionFourV_isSolution heps hM hf0 hfB h319 hL2n hL2 x0 T ω).equation t ht]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have h := hω l ⟨t.toNNReal, zero_le, Real.toNNReal_le_iff_le_coe.2 ht.2⟩
  rw [Real.coe_toNNReal t ht.1] at h
  exact congrArg (fun z : ℝ => z • v l) h

/-- Different horizon choices give the same limit on their common window,
up to one null set for the pair of horizons. -/
theorem sectionFourV_ae_horizon_eq (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    {L1 : ℝ} (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) {S T : ℝ≥0} (hST : S ≤ T) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      EqOn (sectionFourV F' f v x0 S ω) (sectionFourV F' f v x0 T ω)
        (Icc (0 : ℝ) S) := by
  have hA := continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  have hK : 0 ≤ L1 := (norm_nonneg (F' 0)).trans (hL1 0)
  filter_upwards [sectionFourV_ae_equation_J heps hM hf0 hfB h319 hL2n hL2 Lg hLg x0 S,
    sectionFourV_ae_equation_J heps hM hf0 hfB h319 hL2n hL2 Lg hLg x0 T]
    with ω hS hT
  apply Analysis.LinearVolterra.eqOn_of_solution hA
    (⟨continuous_sectionFourV heps hM hf0 hfB h319 hL2n hL2 x0 S ω, hS⟩)
    (⟨continuous_sectionFourV heps hM hf0 hfB h319 hL2n hL2 x0 T ω,
      fun t ht => hT t ⟨ht.1, ht.2.trans (by exact_mod_cast hST)⟩⟩)
    S.coe_nonneg hK
  exact fun t _ => hL1 _

end Ripple.Kurtz.StrongApprox
