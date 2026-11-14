import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The continuous adapted path space

The ambient space is the genuine Bochner space
`L²(Ω; C(K,ℝ))`, where `K` is a compact time window. Its norm is the
L² norm of the uniform path norm. Adaptation is imposed by closed slice
conditions, with no auxiliary metric. No completeness premise is carried.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace Ripple.Stochastic.AdaptedContinuousSpace

variable {Ω K : Type*} [mΩ : MeasurableSpace Ω]
  [TopologicalSpace K] [CompactSpace K] {μ : Measure Ω}

abbrev PathLp (K : Type*) [TopologicalSpace K] [CompactSpace K]
    (μ : Measure Ω) := Lp C(K, ℝ) 2 μ

/-- Evaluation is a continuous linear map between the actual L² spaces. -/
def evalLp (t : K) : PathLp K μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousMap.evalCLM ℝ t).compLpL 2 μ

/-- The defining representative identity for L² evaluation. -/
theorem evalLp_ae (t : K) (X : PathLp K μ) :
    evalLp t X =ᵐ[μ] fun ω => X ω t := by
  have h := (ContinuousMap.evalCLM ℝ t).coeFn_compLpL (p := 2) (μ := μ) X
  filter_upwards [h] with ω hω
  rw [show evalLp t X = (ContinuousMap.evalCLM ℝ t).compLpL 2 μ X from rfl, hω]
  rfl

/-- The filtration may be restricted from a larger time domain before use here. -/
def adaptedSubmodule (F : K → MeasurableSpace Ω) : Submodule ℝ (PathLp K μ) :=
  ⨅ t, (lpMeas ℝ ℝ (F t) 2 μ).comap (evalLp t).toLinearMap

@[simp] theorem mem_adaptedSubmodule (F : K → MeasurableSpace Ω)
    (X : PathLp K μ) :
    X ∈ adaptedSubmodule F ↔ ∀ t, evalLp t X ∈ lpMeas ℝ ℝ (F t) 2 μ := by
  simp [adaptedSubmodule]

/-- Adaptation is closed for the uniform path L² norm. -/
theorem isClosed_adaptedSubmodule (F : K → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ mΩ) :
    IsClosed (adaptedSubmodule (μ := μ) F : Set (PathLp K μ)) := by
  have hslice : ∀ t, IsClosed (lpMeas ℝ ℝ (F t) 2 μ : Set (Lp ℝ 2 μ)) := by
    intro t
    letI : Fact (F t ≤ mΩ) := ⟨hF t⟩
    exact (completeSpace_coe_iff_isComplete.mp
      (inferInstance : CompleteSpace (lpMeas ℝ ℝ (F t) 2 μ))).isClosed
  have heq : (adaptedSubmodule (μ := μ) F : Set (PathLp K μ)) =
      ⋂ t, (evalLp t) ⁻¹' (lpMeas ℝ ℝ (F t) 2 μ : Set (Lp ℝ 2 μ)) := by
    ext X
    simp
  rw [heq]
  exact isClosed_iInter fun t => (hslice t).preimage (evalLp t).continuous

/-- The continuous adapted S² space, with its inherited norm. -/
abbrev Space (F : K → MeasurableSpace Ω) := adaptedSubmodule (μ := μ) F

/-- Completeness comes from a closed subspace of the Bochner path space. -/
theorem completeSpace (F : K → MeasurableSpace Ω) (hF : ∀ t, F t ≤ mΩ) :
    CompleteSpace (Space (μ := μ) F) :=
  completeSpace_coe_iff_isComplete.mpr (isClosed_adaptedSubmodule F hF).isComplete

/-- A single strongly measurable path-valued representative; every path is continuous. -/
def representative (X : PathLp K μ) : Ω → C(K, ℝ) :=
  (Lp.memLp X).aestronglyMeasurable.mk X

theorem representative_stronglyMeasurable (X : PathLp K μ) :
    StronglyMeasurable (representative X) :=
  (Lp.memLp X).aestronglyMeasurable.stronglyMeasurable_mk

theorem representative_ae (X : PathLp K μ) :
    (X : Ω → C(K, ℝ)) =ᵐ[μ] representative X :=
  (Lp.memLp X).aestronglyMeasurable.ae_eq_mk

/-- This identity is on one event for the entire path, not a separate event per time. -/
theorem representative_indistinguishable (X : PathLp K μ) :
    ∀ᵐ ω ∂μ, ∀ t, X ω t = representative X ω t := by
  filter_upwards [representative_ae X] with ω hω
  exact fun t => congrArg (fun f : C(K, ℝ) => f t) hω

theorem representative_memLp (X : PathLp K μ) :
    MemLp (representative X) 2 μ :=
  (Lp.memLp X).ae_eq (representative_ae X)

/-- The continuous representative has adapted slices modulo null sets. -/
theorem representative_aeAdapted (F : K → MeasurableSpace Ω)
    (X : Space (μ := μ) F) (t : K) :
    AEStronglyMeasurable[F t] (fun ω => representative X.val ω t) μ := by
  have hx := (mem_adaptedSubmodule F X.val).mp X.property t
  have h := mem_lpMeas_iff_aestronglyMeasurable.mp hx
  apply h.congr
  exact (evalLp_ae t X.val).trans
    ((representative_ae X.val).mono fun ω hω => congrArg (fun f : C(K, ℝ) => f t) hω)

/-- Transfer exact measurability through an ambient measurable null set.
This is the precise filtration-completeness condition used for realization. -/
theorem measurable_of_ae_eq_of_null_sets {m : MeasurableSpace Ω}
    {f g : Ω → ℝ}
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

/-- With ambient measurable null sets included at each time, the same single
continuous representative is exactly adapted. No right-continuity is used. -/
theorem representative_adapted (F : K → MeasurableSpace Ω)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (X : Space (μ := μ) F) (t : K) :
    StronglyMeasurable[F t] (fun ω => representative X.val ω t) := by
  let h := representative_aeAdapted F X t
  have hamb : Measurable (fun ω => representative X.val ω t) :=
    ((ContinuousMap.evalCLM ℝ t).continuous.comp_stronglyMeasurable
      (representative_stronglyMeasurable X.val)).measurable
  exact (measurable_of_ae_eq_of_null_sets (hnull t) hamb h.measurable_mk
    h.ae_eq_mk).stronglyMeasurable

/-- The path norm being integrated is exactly the supremum over time. -/
theorem pathNorm_eq_iSup (X : PathLp K μ) (ω : Ω) :
    ‖representative X ω‖₊ = ⨆ t, ‖representative X ω t‖₊ :=
  ContinuousMap.nnnorm_eq_iSup_nnnorm _

/-- On a compact metric time window, measurable evaluations imply strong
measurability of the entire continuous path. Countably many dense evaluations
form a continuous injective map from the Polish path space, hence a measurable
embedding. This avoids assuming joint continuity in time and sample. -/
theorem stronglyMeasurable_of_evaluations {L : Type*} [MetricSpace L]
    [CompactSpace L] [SecondCountableTopology L] [Nonempty L]
    (f : Ω → C(L, ℝ)) (hf : ∀ t, Measurable (fun ω => f ω t)) :
    StronglyMeasurable f := by
  letI : MeasurableSpace C(L, ℝ) := borel C(L, ℝ)
  haveI : BorelSpace C(L, ℝ) := ⟨rfl⟩
  let d : ℕ → L := TopologicalSpace.denseSeq L
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq L
  let e : C(L, ℝ) → ℕ → ℝ := fun g n => g (d n)
  have hecont : Continuous e :=
    continuous_pi fun n => (ContinuousMap.evalCLM ℝ (d n)).continuous
  have heinj : Function.Injective e := by
    intro f g hfg
    apply ContinuousMap.coe_injective
    apply hd.equalizer f.continuous g.continuous
    exact hfg
  have he : MeasurableEmbedding e := hecont.measurableEmbedding heinj
  have hcomp : Measurable (e ∘ f) :=
    measurable_pi_iff.mpr fun n => hf (d n)
  exact (he.measurable_comp_iff.mp hcomp).stronglyMeasurable

section VectorSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Vector-valued continuous processes carry the same uniform-path Bochner norm. -/
abbrev VectorPathLp (K : Type*) [TopologicalSpace K] [CompactSpace K]
    (E : Type*) [NormedAddCommGroup E] (μ : Measure Ω) := Lp C(K, E) 2 μ

def vectorEvalLp (t : K) : VectorPathLp K E μ →L[ℝ] Lp E 2 μ :=
  (ContinuousMap.evalCLM ℝ t).compLpL 2 μ

/-- Coordinate-free adaptation, so the Euclidean state dimension is unrestricted. -/
def vectorAdaptedSubmodule (F : K → MeasurableSpace Ω) :
    Submodule ℝ (VectorPathLp K E μ) :=
  ⨅ t, (lpMeas E ℝ (F t) 2 μ).comap (vectorEvalLp t).toLinearMap

@[simp] theorem mem_vectorAdaptedSubmodule (F : K → MeasurableSpace Ω)
    (X : VectorPathLp K E μ) :
    X ∈ vectorAdaptedSubmodule F ↔
      ∀ t, vectorEvalLp t X ∈ lpMeas E ℝ (F t) 2 μ := by
  simp [vectorAdaptedSubmodule]

/-- Closedness is proved in the vector uniform-path L² norm as well. -/
theorem isClosed_vectorAdaptedSubmodule (F : K → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ mΩ) :
    IsClosed (vectorAdaptedSubmodule (E := E) (μ := μ) F : Set (VectorPathLp K E μ)) := by
  have hslice : ∀ t, IsClosed (lpMeas E ℝ (F t) 2 μ : Set (Lp E 2 μ)) := by
    intro t
    letI : Fact (F t ≤ mΩ) := ⟨hF t⟩
    exact (completeSpace_coe_iff_isComplete.mp
      (inferInstance : CompleteSpace (lpMeas E ℝ (F t) 2 μ))).isClosed
  have heq : (vectorAdaptedSubmodule (E := E) (μ := μ) F : Set (VectorPathLp K E μ)) =
      ⋂ t, (vectorEvalLp t) ⁻¹' (lpMeas E ℝ (F t) 2 μ : Set (Lp E 2 μ)) := by
    ext X
    simp
  rw [heq]
  exact isClosed_iInter fun t => (hslice t).preimage (vectorEvalLp t).continuous

/-- This supplies the actual Banach carrier for finite-dimensional Picard iteration. -/
theorem vectorSpace_complete (F : K → MeasurableSpace Ω) (hF : ∀ t, F t ≤ mΩ) :
    CompleteSpace (vectorAdaptedSubmodule (E := E) (μ := μ) F) :=
  completeSpace_coe_iff_isComplete.mpr
    (isClosed_vectorAdaptedSubmodule (E := E) F hF).isComplete

/-- The vector norm has the required path supremum, before taking its L² norm. -/
theorem vectorPathNorm_eq_iSup (X : VectorPathLp K E μ) (ω : Ω) :
    ‖X ω‖₊ = ⨆ t, ‖X ω t‖₊ :=
  ContinuousMap.nnnorm_eq_iSup_nnnorm _

end VectorSpace

/-- Explicit specialization for the Euclidean state space of a strong SDE. -/
theorem euclideanSpace_complete (d : ℕ) (F : K → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ mΩ) :
    CompleteSpace
      (vectorAdaptedSubmodule (E := EuclideanSpace ℝ (Fin d)) (μ := μ) F) :=
  vectorSpace_complete F hF

end Ripple.Stochastic.AdaptedContinuousSpace
