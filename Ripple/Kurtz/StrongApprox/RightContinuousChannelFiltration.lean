import Ripple.Kurtz.StrongApprox.KurtzStrongSolution
import Ripple.Stochastic.StoppedContinuousIto
import Ripple.Stochastic.AmbientNullAugmentation

/-!
# The right-continuous channel filtration

Let `F` be the augmented channel Brownian filtration (`augmentedChannelBrownianFiltration`)
and `G t = ⨅_{s > t} F s` its right-continuous regularization
(`rightContinuousChannelFiltration`, Mathlib's `Filtration.rightCont`).

1. `G` is a right-continuous filtration, `F ≤ G`, and every `G t` contains the measurable
   null sets of the channel measure.
2. Each channel Brownian motion is `IsFilteredPreBrownian` with respect to `G`, and the vector
   of channel increments after `t` is independent of `G t`
   (`channelBrownian_vectorIncrement_indep_rightCont`). The increment `W_u - W_{s_n}` is
   independent of `F (s_n) ⊇ G t` for `s_n ↓ t`; it converges pointwise to `W_u - W_t` by path
   continuity, and independence of a sub-σ-algebra passes to pointwise limits
   (`indep_comap_of_tendsto`, via the conditional laws `P(· | A)` tested on bounded continuous
   functions).
3. For a filtration enlargement `F ≤ G` (both making `B` a filtered pre-Brownian motion), the
   continuous Itô integrals of an integrand in the predictable `L²` space of `F` with respect to
   `F` and to `G` coincide: the two path-valued operators agree on `F`-simple processes and the
   inclusion of predictable `L²` spaces is an isometry (`continuousItoOfFun_eq_of_le`). As a
   consequence the strong solutions of Kurtz's SDE and the `U_N` tail transfer to `G`
   (`exists_kurtz_strong_solution_rightCont`, `sectionFour_U_tail_kurtz_strong_rightCont`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

/-! ## Independence passes to pointwise limits -/

namespace Ripple.Stochastic.FiltrationEnlargement

/-- If `X n` is independent of a sub-σ-algebra `m` for every `n` and `X n → Y` pointwise, then
`Y` is independent of `m`. For `C ∈ m`, the law of `X n` under `P(· ∩ C)` is `P C` times its
law under `P`; testing on bounded continuous functions and dominated convergence carry this
identity to `Y`. -/
theorem indep_comap_of_tendsto {Ω E : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    [IsProbabilityMeasure P] [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {X : ℕ → Ω → E} {Y : Ω → E} (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hlim : ∀ ω, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) m P) :
    Indep (MeasurableSpace.comap Y inferInstance) m P := by
  rw [Indep_iff]
  rintro _ C ⟨S, hS, rfl⟩ hC
  have hkey : ∀ n, (P.restrict C).map (X n) = P C • P.map (X n) := by
    intro n
    ext S' hS'
    have hi := (Indep_iff _ _ _).mp (hind n) (X n ⁻¹' S') C ⟨S', hS', rfl⟩ hC
    rw [Measure.map_apply (hX n) hS', Measure.restrict_apply (hX n hS'), Measure.smul_apply,
      Measure.map_apply (hX n) hS', smul_eq_mul, hi, mul_comm]
  haveI : IsFiniteMeasure (P C • P.map Y) := ⟨by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)⟩
  have hY' : (P.restrict C).map Y = P C • P.map Y := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have hfm : ∀ ν : Measure E, AEStronglyMeasurable (fun x => f x) ν := fun ν =>
      f.continuous.measurable.aestronglyMeasurable
    rw [integral_map hY.aemeasurable (hfm _), integral_smul_measure,
      integral_map hY.aemeasurable (hfm _)]
    have h1 : Tendsto (fun n => ∫ ω, f (X n ω) ∂(P.restrict C)) atTop
        (𝓝 (∫ ω, f (Y ω) ∂(P.restrict C))) :=
      tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp (hX n)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _)
        (ae_of_all _ fun ω => (f.continuous.tendsto _).comp (hlim ω))
    have h2 : Tendsto (fun n => ∫ ω, f (X n ω) ∂P) atTop (𝓝 (∫ ω, f (Y ω) ∂P)) :=
      tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp (hX n)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _)
        (ae_of_all _ fun ω => (f.continuous.tendsto _).comp (hlim ω))
    have heq : ∀ n, ∫ ω, f (X n ω) ∂(P.restrict C) = (P C).toReal • ∫ ω, f (X n ω) ∂P := by
      intro n
      have h := congrArg (fun ν : Measure E => ∫ x, f x ∂ν) (hkey n)
      simp only at h
      rwa [integral_map (hX n).aemeasurable (hfm _), integral_smul_measure,
        integral_map (hX n).aemeasurable (hfm _)] at h
    exact tendsto_nhds_unique (h1.congr heq) (h2.const_smul _)
  have h := congrArg (fun ν : Measure E => ν S) hY'
  simp only at h
  rw [Measure.map_apply hY hS, Measure.restrict_apply (hY hS), Measure.smul_apply,
    Measure.map_apply hY hS, smul_eq_mul] at h
  rw [h, mul_comm]

/-! ## Enlarging the filtration of a continuous Itô integral -/

open FilteredItoIntegralCLM ContinuousItoElementary ContinuousItoLinear

section Enlargement

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {F G : Filtration ℝ≥0 mΩ}

/-- The predictable σ-algebra is monotone in the filtration. -/
theorem predictable_le_of_le (hFG : F ≤ G) : F.predictable ≤ G.predictable := by
  have hb : ∀ t, Measurable ((fun (_ : ℝ≥0) (_ : Ω) => (0 : ℝ)) t) := fun _ => measurable_const
  rw [← generateFrom_predictableRect (𝓖 := F) (mΩ := mΩ) hb,
    ← generateFrom_predictableRect (𝓖 := G) (mΩ := mΩ) hb]
  refine MeasurableSpace.generateFrom_le fun S hS => MeasurableSpace.measurableSet_generateFrom ?_
  rcases hS with ⟨A, hA, rfl⟩ | ⟨a, b, A, hab, hA, rfl⟩
  · exact Or.inl ⟨A, hFG 0 A hA, rfl⟩
  · exact Or.inr ⟨a, b, A, hab, hFG a A hA, rfl⟩

/-- An `F`-simple process is a `G`-simple process with the same values. -/
def simpleProcessOfLE (hFG : F ≤ G) (V : SimpleProcess ℝ F) : SimpleProcess ℝ G where
  valueBot := V.valueBot
  value := V.value
  le_of_mem_support_value := V.le_of_mem_support_value
  measurable_valueBot := V.measurable_valueBot.mono (hFG ⊥) le_rfl
  measurable_value' p _ := (V.measurable_value p).mono (hFG p.1) le_rfl
  bounded_valueBot := V.bounded_valueBot
  bounded_value := V.bounded_value

/-- The same for horizon-bounded simple processes. -/
def tBoundedOfLE (hFG : F ≤ G) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP (𝓖 := F) T hBmeas) : TBoundedSP (𝓖 := G) T hBmeas :=
  ⟨simpleProcessOfLE hFG V.1, fun p hp => V.2 p hp⟩

/-- The identity map from the `G`-predictable to the `F`-predictable product space preserves the
trimmed measures. -/
theorem measurePreserving_trim (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (hFG : F ≤ G) :
    @MeasurePreserving (ℝ≥0 × Ω) (ℝ≥0 × Ω) G.predictable F.predictable id
      (trimMeasure_T (𝓖 := G) (μ := μ) T hBmeas) (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  have hle := predictable_le_of_le hFG
  have hm : @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) G.predictable F.predictable id :=
    fun s hs => hle s hs
  refine @MeasurePreserving.mk _ _ G.predictable F.predictable id _ _ hm ?_
  refine @Measure.ext _ F.predictable _ _ fun s hs => ?_
  rw [Measure.map_apply hm hs]
  show (((timeMeasure_T T).prod μ).trim G.predictable_le_prod) s =
    (((timeMeasure_T T).prod μ).trim F.predictable_le_prod) s
  rw [trim_measurableSet_eq _ (hle s hs), trim_measurableSet_eq _ hs]

/-- Almost-everywhere equality for the `F`-trimmed measure implies it for the `G`-trimmed
measure. -/
theorem ae_trim_of_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (hFG : F ≤ G)
    {f g : ℝ≥0 × Ω → ℝ} (h : f =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas] g) :
    f =ᵐ[trimMeasure_T (𝓖 := G) (μ := μ) T hBmeas] g :=
  @Measure.QuasiMeasurePreserving.ae_eq_comp _ _ _ G.predictable F.predictable _ _ id f g
    (@MeasurePreserving.quasiMeasurePreserving _ _ G.predictable F.predictable _ _ id
      (measurePreserving_trim T hBmeas hFG)) h

/-- The isometric inclusion of the `F`-predictable `L²` space into the `G`-predictable one. -/
def predictableInclusion (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (hFG : F ≤ G) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) →L[ℝ]
      Lp ℝ 2 (trimMeasure_T (𝓖 := G) (μ := μ) T hBmeas) :=
  (@Lp.compMeasurePreservingₗᵢ (ℝ≥0 × Ω) ℝ G.predictable 2
    (trimMeasure_T (𝓖 := G) (μ := μ) T hBmeas) _ (ℝ≥0 × Ω) F.predictable
    (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) ℝ _ _ _ _ id
    (measurePreserving_trim T hBmeas hFG)).toContinuousLinearMap

/-- The inclusion does not change the function. -/
theorem predictableInclusion_ae (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (hFG : F ≤ G)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    (predictableInclusion T hBmeas hFG φ : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := G) (μ := μ) T hBmeas]
      (φ : ℝ≥0 × Ω → ℝ) :=
  @Lp.coeFn_compMeasurePreserving (ℝ≥0 × Ω) ℝ G.predictable 2
    (trimMeasure_T (𝓖 := G) (μ := μ) T hBmeas) _ (ℝ≥0 × Ω) F.predictable
    (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) id φ (measurePreserving_trim T hBmeas hFG)

variable [IsFilteredPreBrownian B F μ] [IsFilteredPreBrownian B G μ]

/-- The inclusion maps the `L²` class of an `F`-simple process to the `L²` class of the same
process read as a `G`-simple process. -/
theorem predictableInclusion_simpleAssembly (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hFG : F ≤ G) (V : TBoundedSP (𝓖 := F) T hBmeas) :
    predictableInclusion T hBmeas hFG (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V) =
      simpleAssembly_T (𝓖 := G) (μ := μ) T hBmeas (tBoundedOfLE hFG T hBmeas V) := by
  apply Lp.ext
  have h1 : (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V : ℝ≥0 × Ω → ℝ)
      =ᵐ[trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas] Function.uncurry ⇑V.val :=
    (memLp_uncurry_trim_T (𝓖 := F) (μ := μ) T hBmeas V.val).coeFn_toLp
  have h3 : (simpleAssembly_T (𝓖 := G) (μ := μ) T hBmeas (tBoundedOfLE hFG T hBmeas V) :
      ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (𝓖 := G) (μ := μ) T hBmeas]
        Function.uncurry ⇑(tBoundedOfLE hFG T hBmeas V).val :=
    (memLp_uncurry_trim_T (𝓖 := G) (μ := μ) T hBmeas (tBoundedOfLE hFG T hBmeas V).val).coeFn_toLp
  exact (predictableInclusion_ae T hBmeas hFG _).trans
    ((ae_trim_of_le T hBmeas hFG h1).trans h3.symm)

/-- **The continuous Itô integral does not see the enlargement.** On the `F`-predictable `L²`
space, the continuous Itô operator of `G` composed with the inclusion is the continuous Itô
operator of `F`. Both are continuous and agree on the dense image of the `F`-simple processes,
where both are the finite elementary path sums. -/
theorem continuousIto_predictableInclusion (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t)) (hFG : F ≤ G)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    continuousIto (F := G) (μ := μ) T hB hBmeas (predictableInclusion T hBmeas hFG φ) =
      continuousIto (F := F) (μ := μ) T hB hBmeas φ := by
  refine DenseRange.induction_on
    (p := fun φ => continuousIto (F := G) (μ := μ) T hB hBmeas
      (predictableInclusion T hBmeas hFG φ) = continuousIto (F := F) (μ := μ) T hB hBmeas φ)
    (simpleAssembly_T_denseRange (𝓖 := F) (μ := μ) T hBmeas) φ ?_ ?_
  · exact isClosed_eq ((continuousIto (F := G) (μ := μ) T hB hBmeas).continuous.comp
      (predictableInclusion T hBmeas hFG).continuous)
      (continuousIto (F := F) (μ := μ) T hB hBmeas).continuous
  · intro V
    show continuousIto (F := G) (μ := μ) T hB hBmeas
      (predictableInclusion T hBmeas hFG (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V)) =
        continuousIto (F := F) (μ := μ) T hB hBmeas (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V)
    rw [predictableInclusion_simpleAssembly, StoppedContinuousIto.continuousIto_simple,
      StoppedContinuousIto.continuousIto_simple]
    rfl

/-- **Filtration enlargement for the continuous Itô integral of a function.** If `F ≤ G`, `B`
is a filtered pre-Brownian motion for both, and `H` lies in the predictable `L²` space of `F`,
then the continuous Itô integrals of `H` with respect to `G` and to `F` are the same function
of time and sample. -/
theorem continuousItoOfFun_eq_of_le (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t)) (hFG : F ≤ G)
    {H : ℝ≥0 → Ω → ℝ}
    (hH : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    continuousItoOfFun μ G T hB hBmeas H = continuousItoOfFun μ F T hB hBmeas H := by
  have hae : (predictableInclusion T hBmeas hFG (hH.toLp _) : ℝ≥0 × Ω → ℝ)
      =ᵐ[trimMeasure_T (𝓖 := G) (μ := μ) T hBmeas] Function.uncurry H :=
    (predictableInclusion_ae T hBmeas hFG _).trans (ae_trim_of_le T hBmeas hFG hH.coeFn_toLp)
  have hG : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := G) (μ := μ) T hBmeas) :=
    (Lp.memLp _).ae_eq hae
  have hto : hG.toLp _ = predictableInclusion T hBmeas hFG (hH.toLp _) := by
    apply Lp.ext
    exact hG.coeFn_toLp.trans hae.symm
  rw [continuousItoOfFun_of_memLp T hB hBmeas hH, continuousItoOfFun_of_memLp T hB hBmeas hG]
  funext t ω
  unfold continuousItoNN
  rw [hto, continuousIto_predictableInclusion]

end Enlargement

end Ripple.Stochastic.FiltrationEnlargement

/-! ## The right-continuous channel filtration -/

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic Ripple.Stochastic.ContinuousItoLinear
open Ripple.Stochastic.FilteredItoIntegralCLM Ripple.Stochastic.FiltrationEnlargement
open SectionFourAssembly

section Filtration

variable {ι : Type*} [Fintype ι]

/-- The right-continuous regularization `G t = ⨅_{s > t} F s` of the augmented channel
filtration `F`. -/
def rightContinuousChannelFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (channelKMTSpace ι)) :=
  (augmentedChannelBrownianFiltration (ι := ι)).rightCont

theorem rightContinuousChannelFiltration_eq (t : ℝ≥0) :
    rightContinuousChannelFiltration (ι := ι) t =
      ⨅ s > t, augmentedChannelBrownianFiltration (ι := ι) s :=
  Filtration.rightCont_eq _ t

instance rightContinuousChannelFiltration_isRightContinuous :
    (rightContinuousChannelFiltration (ι := ι)).IsRightContinuous :=
  Filtration.instIsRightContinuousRightCont

theorem augmented_le_rightContinuousChannelFiltration :
    augmentedChannelBrownianFiltration (ι := ι) ≤ rightContinuousChannelFiltration :=
  Filtration.le_rightCont _

/-- Every level of `G` contains the measurable null sets. -/
theorem rightContinuousChannelFiltration_null (t : ℝ≥0)
    (A : Set (channelKMTSpace ι)) (hA : MeasurableSet A)
    (hzero : channelKMTMeasure ι A = 0) :
    MeasurableSet[rightContinuousChannelFiltration t] A :=
  augmented_le_rightContinuousChannelFiltration t A
    (augmentedChannelBrownianFiltration_null t A hA hzero)

/-- **Fresh increments are independent of `G`.** For `r ≤ t`, the vector of channel increments
`(W_i t - W_i r)_i` is independent of `G r`. -/
theorem channelBrownian_vectorIncrement_indep_rightCont {r t : ℝ≥0} (hrt : r ≤ t) :
    Indep (MeasurableSpace.comap
      (fun ω i => channelBrownian i t ω - channelBrownian i r ω) inferInstance)
      (rightContinuousChannelFiltration (ι := ι) r) (channelKMTMeasure ι) := by
  rcases eq_or_lt_of_le hrt with rfl | hlt
  · have h0 : (fun ω (i : ι) => channelBrownian i r ω - channelBrownian i r ω) =
        fun _ => (0 : ι → ℝ) := by
      funext ω i
      simp
    rw [h0, MeasurableSpace.comap_const]
    exact indep_bot_left _
  · let s : ℕ → ℝ≥0 := fun n => min (r + 1 / ((n : ℝ≥0) + 1)) t
    have hs_gt : ∀ n, r < s n := fun n =>
      lt_min (lt_add_of_pos_right _ (by positivity)) hlt
    have hs_le : ∀ n, s n ≤ t := fun n => min_le_right _ _
    have hs_lim : Tendsto s atTop (𝓝 r) := by
      have h1 : Tendsto (fun n : ℕ => r + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 (r + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h1
      have h2 := h1.min (tendsto_const_nhds (x := t))
      rwa [min_eq_left hrt] at h2
    have hGF : ∀ n, rightContinuousChannelFiltration (ι := ι) r ≤
        augmentedChannelBrownianFiltration (ι := ι) (s n) := fun n => by
      rw [rightContinuousChannelFiltration_eq]
      exact iInf₂_le (s n) (hs_gt n)
    refine indep_comap_of_tendsto
      (X := fun n ω i => channelBrownian i t ω - channelBrownian i (s n) ω)
      (fun n => measurable_pi_lambda _ fun i =>
        (measurable_channelBrownian i t).sub (measurable_channelBrownian i (s n)))
      (measurable_pi_lambda _ fun i =>
        (measurable_channelBrownian i t).sub (measurable_channelBrownian i r))
      (fun ω => tendsto_pi_nhds.2 fun i =>
        tendsto_const_nhds.sub (((channelBrownian_continuous i ω).tendsto r).comp hs_lim))
      (fun n => indep_of_indep_of_le_right
        (channelBrownian_vectorIncrement_indep_augmented (hs_le n)) (hGF n))

/-- Each channel Brownian motion is a filtered pre-Brownian motion for `G`. -/
theorem channelBrownian_isFilteredPreBrownian_rightCont (i : ι) :
    IsFilteredPreBrownian (channelBrownian i) rightContinuousChannelFiltration
      (channelKMTMeasure ι) where
  toIsPreBrownian := (channelBrownian_isFilteredPreBrownian_augmented i).toIsPreBrownian
  stronglyAdapted t := ((channelBrownian_isFilteredPreBrownian_augmented i).stronglyAdapted t).mono
    (augmented_le_rightContinuousChannelFiltration t)
  indep s t hst := by
    refine indep_of_indep_of_le_left (channelBrownian_vectorIncrement_indep_rightCont hst) ?_
    have hV : Measurable[MeasurableSpace.comap
        (fun ω (j : ι) => channelBrownian j t ω - channelBrownian j s ω) inferInstance]
        (fun ω (j : ι) => channelBrownian j t ω - channelBrownian j s ω) :=
      Measurable.of_comap_le le_rfl
    exact ((measurable_pi_apply i).comp hV).comap_le

end Filtration

/-! ## Transfer of the strong solution and the `U_N` tail to `G` -/

section Transfer

attribute [local instance] channelBrownian_isFilteredPreBrownian_augmented
  channelBrownian_isFilteredPreBrownian_rightCont

/-- For an integrand in the predictable `L²` space of the augmented filtration, the continuous
Itô integrals with respect to `G` and to the augmented filtration coincide. -/
theorem continuousItoOfFun_rightCont_eq {ι : Type*} [Fintype ι] (T : ℝ≥0) (l : ι)
    {H : ℝ≥0 → channelKMTSpace ι → ℝ}
    (hH : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := augmentedChannelBrownianFiltration)
      (μ := channelKMTMeasure ι) T (measurable_channelBrownian l))) :
    continuousItoOfFun (channelKMTMeasure ι) rightContinuousChannelFiltration T
        (channelBrownian_continuous l) (measurable_channelBrownian l) H =
      continuousItoOfFun (channelKMTMeasure ι) augmentedChannelBrownianFiltration T
        (channelBrownian_continuous l) (measurable_channelBrownian l) H :=
  continuousItoOfFun_eq_of_le T _ _ augmented_le_rightContinuousChannelFiltration hH

variable {m d : ℕ} {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {M : ℝ}

/-- The channel noise integrals `∫ sqrt (N f_l (Z)) dW_l` with respect to `G`. -/
def rightContChannelRateIntegral (T : ℝ≥0) (N : ℕ) (f : Fin m → (Fin d → ℝ) → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (l : Fin m) :
    ℝ≥0 → channelKMTSpace (Fin m) → ℝ :=
  continuousItoOfFun (channelKMTMeasure (Fin m)) rightContinuousChannelFiltration T
    (channelBrownian_continuous l) (measurable_channelBrownian l)
    (fun s ω => Real.sqrt ((N : ℝ) * f l (Z s ω)))

/-- For a continuous state adapted to the augmented filtration and bounded continuous rates, the
noise integrals with respect to `G` are those with respect to the augmented filtration. -/
theorem rightContChannelRateIntegral_eq {T : ℝ≥0} {N : ℕ} (hf : ∀ l, Continuous (f l))
    (hfB : ∀ l x, f l x ≤ eps l) {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) :
    rightContChannelRateIntegral T N f Z = channelRateIntegral T N f Z := by
  funext l
  exact continuousItoOfFun_rightCont_eq T l
    (memLp_sqrt_rate (μ := channelKMTMeasure (Fin m)) T (measurable_channelBrownian l)
      (g := fun x => (N : ℝ) * f l x) (continuous_const.mul (hf l)) (e := (N : ℝ) * eps l)
      (fun x => mul_le_mul_of_nonneg_left (hfB l x) (Nat.cast_nonneg N)) hZa hZc)

/-- **Kurtz's SDE has strong solutions for the right-continuous filtration.** The strong
solutions `Z_N`, `N ≥ 2`, are adapted to the augmented filtration, hence to `G`, and solve the
SDE with the noise integrals taken with respect to `G`. -/
theorem exists_kurtz_strong_solution_rightCont (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) :
    ∃ Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ,
      (∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t)) ∧
      (∀ N t, Measurable[rightContinuousChannelFiltration t] (Z N t)) ∧
      (∀ N ω, Continuous fun t => Z N t ω) ∧
      (∀ N, 2 ≤ N → ∀ T : ℝ≥0, Integrable (fun ω => ⨆ t : StrongSDEConcreteMaps.Window T,
        ‖Z N t.val ω‖ ^ 2) (channelKMTMeasure (Fin m))) ∧
      ∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
        KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (rightContChannelRateIntegral T N f (Z N))
          (fun _ => x0) ω := by
  obtain ⟨Z, hZa, hZc, hZm, hSDE⟩ :=
    exists_kurtz_strong_solution_family (v := v) heps hM hf0 hfB h319 Lg hLg x0
  refine ⟨Z, hZa, fun N t => (hZa N t).mono (augmented_le_rightContinuousChannelFiltration t)
    le_rfl, hZc, hZm, fun N hN T => ?_⟩
  rw [rightContChannelRateIntegral_eq (continuous_rate_of_lip heps hM h319) hfB (hZa N) (hZc N)]
  exact hSDE N hN T

/-- **The `U_N` tail for Kurtz's strong solutions, with the right-continuous filtration.** The
statement of `sectionFour_U_tail_kurtz_strong` with the solutions adapted to `G` and the SDE
written with the noise integrals taken with respect to `G`. -/
theorem sectionFour_U_tail_kurtz_strong_rightCont (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (x0 : Fin d → ℝ) :
    ∃ Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ,
      (∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t)) ∧
      (∀ N t, Measurable[rightContinuousChannelFiltration t] (Z N t)) ∧
      (∀ N ω, Continuous fun t => Z N t ω) ∧
      (∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
        KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (rightContChannelRateIntegral T N f (Z N))
          (fun _ => x0) ω) ∧
      ∀ (T : ℝ≥0) (Q : ℝ), sectionFourQZero v eps T ≤ Q → 0 < Q →
        ∀ X : ℝ≥0 → Fin d → ℝ, Continuous X →
        (∀ t ≤ T, X t = x0 + ∫ s in (0 : ℝ)..(t : ℝ), tcDrift f v (X s.toNNReal)) →
        ∀ N, 2 ≤ N → ∀ r : ℝ, 0 ≤ r →
          channelKMTMeasure (Fin m) {ω | r < sectionFourRemainderU N X (Z N) T ω} ≤
            ENNReal.ofReal (sectionFourAU d *
              Real.exp (-sectionFourBU (Real.exp (kurtzDriftLip v eps M * T)) Q * r ^ 2)) := by
  obtain ⟨Z, hZa, hZc, hSDE, htail⟩ :=
    sectionFour_U_tail_kurtz_strong (v := v) heps hM hf0 hfB h319 Lg hLg x0
  refine ⟨Z, hZa, fun N t => (hZa N t).mono (augmented_le_rightContinuousChannelFiltration t)
    le_rfl, hZc, fun N hN T => ?_, htail⟩
  rw [rightContChannelRateIntegral_eq (continuous_rate_of_lip heps hM h319) hfB (hZa N) (hZc N)]
  exact hSDE N hN T

end Transfer

end Ripple.Kurtz.StrongApprox
