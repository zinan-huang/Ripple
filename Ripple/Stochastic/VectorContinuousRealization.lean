import Ripple.Stochastic.AdaptedContinuousSpace
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Vector realization of the adapted continuous path space

One measurable continuous-path representative supplies all
time evaluations simultaneously. Exact adaptation uses precisely the ambient
null-set condition constructed by `AmbientNullAugmentation`.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Ripple.Stochastic.AdaptedContinuousSpace

variable {Ω K E : Type*} [mΩ : MeasurableSpace Ω]
  [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω}

def vectorRepresentative (X : VectorPathLp K E μ) : Ω → C(K, E) :=
  (Lp.memLp X).aestronglyMeasurable.mk X

theorem vectorRepresentative_stronglyMeasurable (X : VectorPathLp K E μ) :
    StronglyMeasurable (vectorRepresentative X) :=
  (Lp.memLp X).aestronglyMeasurable.stronglyMeasurable_mk

theorem vectorRepresentative_ae (X : VectorPathLp K E μ) :
    (X : Ω → C(K, E)) =ᵐ[μ] vectorRepresentative X :=
  (Lp.memLp X).aestronglyMeasurable.ae_eq_mk

theorem vectorRepresentative_memLp (X : VectorPathLp K E μ) :
    MemLp (vectorRepresentative X) 2 μ :=
  (Lp.memLp X).ae_eq (vectorRepresentative_ae X)

theorem vectorEvalLp_ae (t : K) (X : VectorPathLp K E μ) :
    vectorEvalLp t X =ᵐ[μ] fun ω => X ω t := by
  have h := (ContinuousMap.evalCLM ℝ t).coeFn_compLpL (p := 2) (μ := μ) X
  filter_upwards [h] with ω hω
  rw [show vectorEvalLp t X = (ContinuousMap.evalCLM ℝ t).compLpL 2 μ X from rfl, hω]
  rfl

theorem vectorRepresentative_aeAdapted (F : K → MeasurableSpace Ω)
    (X : vectorAdaptedSubmodule (E := E) (μ := μ) F) (t : K) :
    AEStronglyMeasurable[F t] (fun ω => vectorRepresentative X.val ω t) μ := by
  have hx := (mem_vectorAdaptedSubmodule F X.val).mp X.property t
  have h := mem_lpMeas_iff_aestronglyMeasurable.mp hx
  apply h.congr
  exact (vectorEvalLp_ae t X.val).trans
    ((vectorRepresentative_ae X.val).mono fun ω hω =>
      congrArg (fun f : C(K, E) => f t) hω)

/-- The null-set transfer argument is independent of the dimension. -/
theorem vectorMeasurable_of_ae_eq_of_null_sets {m : MeasurableSpace Ω}
    {f g : Ω → E}
    (hnull : ∀ A : Set Ω, MeasurableSet[mΩ] A → μ A = 0 → MeasurableSet[m] A)
    (hf : Measurable[mΩ] f) (hg : Measurable[m] g) (hfg : f =ᵐ[μ] g) :
    Measurable[m] f := by
  letI : MeasurableSpace Ω := mΩ
  obtain ⟨A, hsub, hAm, hAzero⟩ :=
    exists_measurable_superset_of_null (μ := μ) (ae_iff.mp hfg)
  intro s hs
  have hsplit : f ⁻¹' s = (f ⁻¹' s ∩ Aᶜ) ∪ (f ⁻¹' s ∩ A) := by
    rw [← Set.inter_union_distrib_left, Set.compl_union_self, Set.inter_univ]
  have hleft : f ⁻¹' s ∩ Aᶜ = g ⁻¹' s ∩ Aᶜ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    apply and_congr_left
    intro hωA
    have heq : f ω = g ω := by
      by_contra hne
      exact hωA (hsub hne)
    rw [heq]
  rw [hsplit, hleft]
  refine ((hg hs).inter (hnull A hAm hAzero).compl).union
    (hnull _ ((hf hs).inter hAm) ?_)
  exact measure_mono_null Set.inter_subset_right hAzero

theorem vectorRepresentative_adapted (F : K → MeasurableSpace Ω)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (X : vectorAdaptedSubmodule (E := E) (μ := μ) F) (t : K) :
    StronglyMeasurable[F t] (fun ω => vectorRepresentative X.val ω t) := by
  let h := vectorRepresentative_aeAdapted F X t
  have hamb : Measurable (fun ω => vectorRepresentative X.val ω t) :=
    ((ContinuousMap.evalCLM ℝ t).continuous.comp_stronglyMeasurable
      (vectorRepresentative_stronglyMeasurable X.val)).measurable
  exact (vectorMeasurable_of_ae_eq_of_null_sets (hnull t) hamb
    h.measurable_mk h.ae_eq_mk).stronglyMeasurable

/-- A norm-square supremum is the square of the actual continuous-path norm. -/
theorem vectorPath_sup_sq [Nonempty K] (f : C(K, E)) :
    (⨆ t, ‖f t‖ ^ 2) = ‖f‖ ^ 2 := by
  have hb : BddAbove (Set.range fun t => ‖f t‖ ^ 2) := by
    refine ⟨‖f‖ ^ 2, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm t) 2
  obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMaxOn
    Set.univ_nonempty f.continuous.norm.continuousOn
  have hnorm : ‖f‖ = ‖f t‖ := by
    apply le_antisymm
    · rw [ContinuousMap.norm_eq_iSup_norm]
      exact ciSup_le fun s => ht (Set.mem_univ s)
    · exact f.norm_coe_le_norm t
  apply le_antisymm
  · exact ciSup_le fun s => pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm s) 2
  · rw [hnorm]
    exact le_ciSup hb t

/-- The realization has the exact squared-supremum moment required by the SDE consumer. -/
theorem vectorRepresentative_integrable_sup_sq [Nonempty K] (X : VectorPathLp K E μ) :
    Integrable (fun ω => ⨆ t, ‖vectorRepresentative X ω t‖ ^ 2) μ := by
  have hm := vectorRepresentative_memLp X
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  simpa only [vectorPath_sup_sq] using hi

/-- Equality in the path space gives equality of every time on one event. -/
theorem vectorRepresentative_eq_of_eq {X Y : VectorPathLp K E μ} (h : X = Y) :
    ∀ᵐ ω ∂μ, ∀ t, vectorRepresentative X ω t = vectorRepresentative Y ω t := by
  subst Y
  exact ae_of_all _ fun _ _ => rfl

/-- Evaluation after embedding a scalar path along a fixed state-space direction. -/
def directionPathCLM (v : E) : C(K, ℝ) →L[ℝ] C(K, E) :=
  LinearMap.mkContinuous
    { toFun f := ⟨fun t => f t • v, f.continuous.smul continuous_const⟩
      map_add' f g := by ext t; simp [add_smul]
      map_smul' c f := by ext t; simp [smul_smul] }
    ‖v‖ (by
      intro f
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro t
      change ‖f t • v‖ ≤ ‖v‖ * ‖f‖
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) (norm_nonneg _))

def directionPathLp (v : E) : PathLp K μ →L[ℝ] VectorPathLp K E μ :=
  (directionPathCLM v).compLpL 2 μ

theorem directionPathLp_ae (v : E) (X : PathLp K μ) :
    directionPathLp v X =ᵐ[μ] fun ω => directionPathCLM v (X ω) := by
  have h := (directionPathCLM v).coeFn_compLpL (p := 2) (μ := μ) X
  filter_upwards [h] with ω hω
  rw [show directionPathLp v X = (directionPathCLM v).compLpL 2 μ X from rfl, hω]

theorem directionPathLp_norm_le (v : E) (X : PathLp K μ) :
    ‖directionPathLp v X‖ ≤ ‖v‖ * ‖X‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [directionPathLp_ae v X] with ω hω
  rw [hω]
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro t
  change ‖X ω t • v‖ ≤ ‖v‖ * ‖X ω‖
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left ((X ω).norm_coe_le_norm t) (norm_nonneg _)

/-- A scalar adapted integral yields an adapted vector integral in direction v. -/
theorem directionPathLp_mem (F : K → MeasurableSpace Ω) (v : E)
    (X : PathLp K μ) (hX : X ∈ adaptedSubmodule F) :
    directionPathLp v X ∈ vectorAdaptedSubmodule F := by
  apply (mem_vectorAdaptedSubmodule _ _).mpr
  intro t
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have h := mem_lpMeas_iff_aestronglyMeasurable.mp
    ((mem_adaptedSubmodule F X).mp hX t)
  have hv := h.smul_const v
  apply hv.congr
  filter_upwards [evalLp_ae t X, vectorEvalLp_ae t (directionPathLp v X),
    directionPathLp_ae v X] with ω hs he hp
  rw [he, hp, hs]
  rfl

end Ripple.Stochastic.AdaptedContinuousSpace
