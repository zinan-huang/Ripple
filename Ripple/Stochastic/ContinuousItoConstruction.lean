import Ripple.Stochastic.AdaptedContinuousSpace
import Ripple.Stochastic.FilteredItoIntegralProcess
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Continuous Itô extension in the uniform path L² norm

The extension is constructed in `L²(Ω; C(K,ℝ))`.
Only elementary integrals are supplied as data. The general continuous
modification and the completeness of its target are conclusions.
The norm estimate for elementary integrals is the Doob L² dependency.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Ripple.Stochastic.ContinuousItoConstruction
open AdaptedContinuousSpace

variable {Ω K : Type*} [mΩ : MeasurableSpace Ω]
  [TopologicalSpace K] [CompactSpace K] {μ : Measure Ω}

section ElementaryExtension
variable {S H : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Bundle only the elementary path integrals in the Bochner L² space. -/
def elementaryPathLM (j : S →ₗ[ℝ] Ω → C(K, ℝ))
    (hj : ∀ V, MemLp (j V) 2 μ) : S →ₗ[ℝ] PathLp K μ where
  toFun V := (hj V).toLp (j V)
  map_add' V W := by
    apply Lp.ext
    filter_upwards [(hj (V + W)).coeFn_toLp,
      (hj V).coeFn_toLp, (hj W).coeFn_toLp,
      Lp.coeFn_add ((hj V).toLp (j V)) ((hj W).toLp (j W))] with ω hsum hV hW hadd
    rw [hadd, Pi.add_apply, hsum, hV, hW]
    exact congrFun (map_add j V W) ω
  map_smul' c V := by
    apply Lp.ext
    filter_upwards [(hj (c • V)).coeFn_toLp, (hj V).coeFn_toLp,
      Lp.coeFn_smul c ((hj V).toLp (j V))] with ω hc hV hsmul
    rw [RingHom.id_apply, hsmul, Pi.smul_apply, hc, hV]
    exact congrFun (map_smul j c V) ω

/-- Construction by uniform-path L² completion. `A` is the dense simple-process
embedding into predictable L². No process for a general integrand is supplied. -/
def continuousIntegralCLM (A : S →ₗ[ℝ] H)
    (j : S →ₗ[ℝ] Ω → C(K, ℝ)) (hj : ∀ V, MemLp (j V) 2 μ) :
    H →L[ℝ] PathLp K μ :=
  (elementaryPathLM j hj).extendOfNorm A

/-- The constructed extension agrees with every elementary integral. -/
theorem continuousIntegral_simple (A : S →ₗ[ℝ] H) (hA : DenseRange A)
    (j : S →ₗ[ℝ] Ω → C(K, ℝ)) (hj : ∀ V, MemLp (j V) 2 μ)
    (hDoob : ∀ V, ‖elementaryPathLM j hj V‖ ≤ 2 * ‖A V‖) (V : S) :
    continuousIntegralCLM A j hj (A V) = elementaryPathLM j hj V :=
  LinearMap.extendOfNorm_eq hA ⟨2, hDoob⟩ V

/-- The Doob factor two in norm, equivalently four in squared norm, survives completion. -/
theorem continuousIntegral_norm_le (A : S →ₗ[ℝ] H) (hA : DenseRange A)
    (j : S →ₗ[ℝ] Ω → C(K, ℝ)) (hj : ∀ V, MemLp (j V) 2 μ)
    (hDoob : ∀ V, ‖elementaryPathLM j hj V‖ ≤ 2 * ‖A V‖) (φ : H) :
    ‖continuousIntegralCLM A j hj φ‖ ≤ 2 * ‖φ‖ :=
  LinearMap.norm_extendOfNorm_apply_le hA 2 hDoob φ

/-- This is convergence in L² of the uniform path norm, not uniformity of
separate time-slice L² distances. -/
theorem continuousIntegral_tendsto (A : S →ₗ[ℝ] H) (hA : DenseRange A)
    (j : S →ₗ[ℝ] Ω → C(K, ℝ)) (hj : ∀ V, MemLp (j V) 2 μ)
    (hDoob : ∀ V, ‖elementaryPathLM j hj V‖ ≤ 2 * ‖A V‖)
    {V : ℕ → S} {φ : H} (hV : Tendsto (fun n => A (V n)) atTop (𝓝 φ)) :
    Tendsto (fun n => elementaryPathLM j hj (V n)) atTop
      (𝓝 (continuousIntegralCLM A j hj φ)) := by
  have h := (continuousIntegralCLM A j hj).continuous.continuousAt.tendsto.comp hV
  refine Filter.Tendsto.congr (fun n => ?_) h
  exact continuousIntegral_simple A hA j hj hDoob (V n)

/-- The continuous integral has adapted slices because that condition defines a
closed subspace of the actual path norm. -/
theorem continuousIntegral_mem_adapted (A : S →ₗ[ℝ] H) (hA : DenseRange A)
    (j : S →ₗ[ℝ] Ω → C(K, ℝ)) (hj : ∀ V, MemLp (j V) 2 μ)
    (hDoob : ∀ V, ‖elementaryPathLM j hj V‖ ≤ 2 * ‖A V‖)
    (F : K → MeasurableSpace Ω) (hF : ∀ t, F t ≤ mΩ)
    (hadapt : ∀ V, elementaryPathLM j hj V ∈ adaptedSubmodule F) (φ : H) :
    continuousIntegralCLM A j hj φ ∈ adaptedSubmodule F := by
  refine hA.induction_on
    (p := fun ψ => continuousIntegralCLM A j hj ψ ∈ adaptedSubmodule F) φ ?_ ?_
  · exact (isClosed_adaptedSubmodule F hF).preimage
      (continuousIntegralCLM A j hj).continuous
  · intro V
    rw [continuousIntegral_simple A hA j hj hDoob]
    exact hadapt V

/-- Evaluation of the new extension agrees with an independently constructed
slice-wise Itô CLM, by equality on the dense elementary processes. -/
theorem continuousIntegral_eval_eq (A : S →ₗ[ℝ] H) (hA : DenseRange A)
    (j : S →ₗ[ℝ] Ω → C(K, ℝ)) (hj : ∀ V, MemLp (j V) 2 μ)
    (hDoob : ∀ V, ‖elementaryPathLM j hj V‖ ≤ 2 * ‖A V‖)
    (I : K → H →L[ℝ] Lp ℝ 2 μ)
    (hI : ∀ t V, I t (A V) = evalLp t (elementaryPathLM j hj V))
    (φ : H) (t : K) :
    evalLp t (continuousIntegralCLM A j hj φ) = I t φ := by
  refine hA.induction_on
    (p := fun ψ => evalLp t (continuousIntegralCLM A j hj ψ) = I t ψ) φ ?_ ?_
  · exact isClosed_eq
      ((evalLp t).continuous.comp (continuousIntegralCLM A j hj).continuous)
      (I t).continuous
  · intro V
    rw [continuousIntegral_simple A hA j hj hDoob]
    exact (hI t V).symm

/-- The actual process is obtained from one path-valued representative. -/
def continuousIntegralProcess (A : S →ₗ[ℝ] H)
    (j : S →ₗ[ℝ] Ω → C(K, ℝ)) (hj : ∀ V, MemLp (j V) 2 μ)
    (φ : H) (t : K) (ω : Ω) : ℝ :=
  representative (continuousIntegralCLM A j hj φ) ω t

/-- Continuity is everywhere, since the representative takes values in `C(K,ℝ)`. -/
theorem continuousIntegralProcess_continuous (A : S →ₗ[ℝ] H)
    (j : S →ₗ[ℝ] Ω → C(K, ℝ)) (hj : ∀ V, MemLp (j V) 2 μ)
    (φ : H) (ω : Ω) : Continuous (fun t => continuousIntegralProcess A j hj φ t ω) :=
  (representative (continuousIntegralCLM A j hj φ) ω).continuous

/-- Fixed-time agreement with the pre-existing slice integral is proved, rather
than included in the construction's input. -/
theorem continuousIntegralProcess_modification (A : S →ₗ[ℝ] H) (hA : DenseRange A)
    (j : S →ₗ[ℝ] Ω → C(K, ℝ)) (hj : ∀ V, MemLp (j V) 2 μ)
    (hDoob : ∀ V, ‖elementaryPathLM j hj V‖ ≤ 2 * ‖A V‖)
    (I : K → H →L[ℝ] Lp ℝ 2 μ)
    (hI : ∀ t V, I t (A V) = evalLp t (elementaryPathLM j hj V))
    (φ : H) (t : K) :
    continuousIntegralProcess A j hj φ t =ᵐ[μ] (I t φ : Ω → ℝ) := by
  have heval := evalLp_ae t (continuousIntegralCLM A j hj φ)
  rw [continuousIntegral_eval_eq A hA j hj hDoob I hI φ t] at heval
  have hrep : (fun ω => (continuousIntegralCLM A j hj φ : Ω → C(K, ℝ)) ω t) =ᵐ[μ]
      fun ω => representative (continuousIntegralCLM A j hj φ) ω t :=
    (representative_indistinguishable (continuousIntegralCLM A j hj φ)).mono fun ω hω => hω t
  exact hrep.symm.trans heval.symm

end ElementaryExtension

section ElementaryBrownianPaths
open ProbabilityTheory FilteredItoIntegralProcess
variable {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

/-- A stopped Brownian path on a compact window, constructed directly from B. -/
def stoppedBrownianPath (T a : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) : C(Set.Icc (0 : ℝ≥0) T, ℝ) :=
  ⟨fun t => B (min a t.val) ω,
    (hB ω).comp (continuous_const.min continuous_subtype_val)⟩

/-- The continuous elementary integral is its finite truncated increment sum.
This constructs elementary paths; it does not assume a general continuous version. -/
def simpleIntegralPath (T : ℝ≥0) (hB : ∀ ω, Continuous (fun t => B t ω))
    (V : SimpleProcess ℝ F) (ω : Ω) : C(Set.Icc (0 : ℝ≥0) T, ℝ) :=
  ∑ p ∈ V.value.support, V.value p ω •
    (stoppedBrownianPath T p.2 hB ω - stoppedBrownianPath T p.1 hB ω)

/-- The elementary path construction agrees literally with the installed
truncated-increment formula at every time and sample. -/
theorem simpleIntegralPath_apply (T : ℝ≥0) (hB : ∀ ω, Continuous (fun t => B t ω))
    (hBmeas : ∀ t, Measurable (B t)) (V : SimpleProcess ℝ F)
    (ω : Ω) (t : Set.Icc (0 : ℝ≥0) T) :
    simpleIntegralPath T hB V ω t = itoSimpleProcess hBmeas V t.val ω := by
  rw [itoSimpleProcess_apply]
  simp [simpleIntegralPath, stoppedBrownianPath, Finsupp.sum, smul_eq_mul]

/-- The elementary continuous path construction is linear before taking any quotient. -/
def simplePathLM (T : ℝ≥0) (hB : ∀ ω, Continuous (fun t => B t ω))
    (hBmeas : ∀ t, Measurable (B t)) :
    SimpleProcess ℝ F →ₗ[ℝ] Ω → C(Set.Icc (0 : ℝ≥0) T, ℝ) where
  toFun V := simpleIntegralPath T hB V
  map_add' V W := by
    funext ω
    apply ContinuousMap.ext
    intro t
    simp only [Pi.add_apply, ContinuousMap.add_apply]
    rw [simpleIntegralPath_apply T hB hBmeas,
      simpleIntegralPath_apply T hB hBmeas,
      simpleIntegralPath_apply T hB hBmeas]
    exact congrFun (itoSimpleProcess_add hBmeas V W t.val) ω
  map_smul' c V := by
    funext ω
    apply ContinuousMap.ext
    intro t
    simp only [Pi.smul_apply, ContinuousMap.smul_apply]
    rw [simpleIntegralPath_apply T hB hBmeas,
      simpleIntegralPath_apply T hB hBmeas]
    exact congrFun (itoSimpleProcess_smul hBmeas c V t.val) ω

end ElementaryBrownianPaths
end Ripple.Stochastic.ContinuousItoConstruction
