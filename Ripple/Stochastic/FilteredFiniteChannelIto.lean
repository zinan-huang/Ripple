import Ripple.Stochastic.FilteredItoIntegralCLM
import Ripple.Stochastic.FiniteChannelIto

/-!
# Finite-channel assembly of the constructed filtered Itô operators

Each scalar map, its isometry, and the dense simple-process embedding are taken from
`FilteredItoIntegralCLM`. Only the cross pairing on the actual simple-process images is
assumed. This is a conditional common-filtration finite-channel isometry; the weighted
cross-increment argument that produces its remaining premise is not constructed here.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace NNReal

namespace Ripple.Stochastic.FilteredFiniteChannelIto

open FilteredItoIntegralCLM

variable {ι Ω : Type*} [Fintype ι] [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {F : Filtration ℝ≥0 mΩ} {W : ι → ℝ≥0 → Ω → ℝ}
variable [∀ i, IsFilteredPreBrownian (W i) F μ]

/-- The finite sum of the constructed filtered scalar integral maps on one horizon.
All channels use the same filtration; the integrand domain is written with its own
channel's measurability proof so no domain identification lemma is required. -/
noncomputable def itoIntegralSum_T (T : ℝ≥0)
    (hWmeas : ∀ i t, Measurable (W i t))
    (H : ∀ i, Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hWmeas i))) :
    Lp ℝ 2 μ :=
  letI : ∀ i, NormedAddCommGroup (Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hWmeas i))) :=
    fun i => inferInstance
  letI : ∀ i, NormedSpace ℝ (Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hWmeas i))) :=
    fun i => inferInstance
  FiniteChannelIto.finiteChannelIntegral
    (E := fun i => Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hWmeas i))) (V := Lp ℝ 2 μ)
    (fun i => itoIntegralCLM_T (𝓖 := F) (μ := μ) T (hWmeas i)) H

/-- Conditional finite-channel Itô isometry for the delivered filtered scalar construction.
Scalar isometry and density are supplied by their actual theorems. The only stochastic
bridge left as a hypothesis is orthogonality for distinct channels on the images of the
actual T-bounded simple-process assemblies. -/
theorem itoIntegralSum_T_norm_sq_of_simple_cross (T : ℝ≥0)
    (hWmeas : ∀ i t, Measurable (W i t))
    (hsimple : ∀ i j, i ≠ j →
      ∀ (U : TBoundedSP (𝓖 := F) T (hWmeas i))
        (V : TBoundedSP (𝓖 := F) T (hWmeas j)),
      inner ℝ
        (itoIntegralCLM_T (𝓖 := F) (μ := μ) T (hWmeas i)
          (simpleAssembly_T (𝓖 := F) (μ := μ) T (hWmeas i) U))
        (itoIntegralCLM_T (𝓖 := F) (μ := μ) T (hWmeas j)
          (simpleAssembly_T (𝓖 := F) (μ := μ) T (hWmeas j) V)) = 0)
    (H : ∀ i, Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hWmeas i))) :
    ‖itoIntegralSum_T T hWmeas H‖ ^ 2 = ∑ i, ‖H i‖ ^ 2 := by
  letI : ∀ i, NormedAddCommGroup (Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hWmeas i))) :=
    fun i => inferInstance
  letI : ∀ i, NormedSpace ℝ (Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hWmeas i))) :=
    fun i => inferInstance
  exact FiniteChannelIto.finiteChannelIntegral_norm_sq_of_denseRange
    (E := fun i => Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hWmeas i))) (V := Lp ℝ 2 μ)
    (fun i => simpleAssembly_T (𝓖 := F) (μ := μ) T (hWmeas i))
    (fun i => simpleAssembly_T_denseRange (𝓖 := F) (μ := μ) T (hWmeas i))
    (fun i => itoIntegralCLM_T (𝓖 := F) (μ := μ) T (hWmeas i))
    (fun i x => itoIntegralCLM_T_norm (𝓖 := F) (μ := μ) T (hWmeas i) x)
    hsimple H

end Ripple.Stochastic.FilteredFiniteChannelIto
