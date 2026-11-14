import Ripple.Stochastic.StrongSDEGlobal
import Ripple.Kurtz.StrongApprox.ChannelStrongSDE

/-!
# Global strong solutions on the constructed channel space

State dimension and number of noise channels are
independent. The probability space, filtration augmentation, Brownian drivers,
completed integrals, running-moment estimates, and complete carrier all have
concrete producers. No short-window, Doob, isometry, compatibility, or
abstract fixed-point hypothesis occurs in these headlines.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox
open Ripple.Stochastic StrongSDEConcreteMaps

variable {ι : Type*} [Fintype ι] {d : ℕ}

def channelAllTimeIto (i : ι) :
    (ℝ≥0 → channelKMTSpace ι → ℝ) → ℝ≥0 → channelKMTSpace ι → ℝ := by
  letI := channelBrownian_isFilteredPreBrownian_augmented i
  exact AllTimeIto.globalIto (μ := channelKMTMeasure ι) augmentedChannelBrownianFiltration (channelBrownian i)
    (channelBrownian_continuous i) (measurable_channelBrownian i)

section Coefficients
variable (ell : ι → EuclideanSpace ℝ (Fin d))
    (g : ι → EuclideanSpace ℝ (Fin d) → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (x₀ : EuclideanSpace ℝ (Fin d))
include hLip hK hb hC hbC

/-- For every finite T and every N≥1 the original d-dimensional channel SDE
has a continuous adapted solution, with its compact path moment. -/
theorem exists_channel_solution (T : ℝ≥0) (N : ℕ) (hN : 1 ≤ N) :
    ∃ Z : ℝ≥0 → channelKMTSpace ι → EuclideanSpace ℝ (Fin d),
      StronglyAdapted augmentedChannelBrownianFiltration Z ∧
      (∀ ω, Continuous (fun t => Z t ω)) ∧
      Integrable (fun ω => ⨆ t : Window T, ‖Z t.val ω‖ ^ 2) (channelKMTMeasure ι) ∧
      (∀ᵐ ω ∂channelKMTMeasure ι, ∀ t ≤ T,
        Z t ω = StrongSDE.sdeRhs (channelWindowIto T) ell g b x₀ N Z t ω) := by
  letI : ∀ i : ι, IsFilteredPreBrownian (channelBrownian i)
      augmentedChannelBrownianFiltration (channelKMTMeasure ι) :=
    channelBrownian_isFilteredPreBrownian_augmented
  obtain ⟨X, ha, hc, hm, he⟩ := StrongSDEGlobal.exists_solution
    augmentedChannelBrownianFiltration channelBrownian channelBrownian_continuous
    measurable_channelBrownian augmentedChannelBrownianFiltration_null
    ell g L hLip K hK b Lb hb C hC hbC x₀ T N hN
  exact ⟨realize augmentedChannelBrownianFiltration T X, ha, hc, hm, he⟩

/-- Finite-horizon pathwise uniqueness among all adapted a.s. continuous
solutions; no square-moment hypothesis on the two solutions is needed. -/
theorem channel_pathwise_unique (T : ℝ≥0) (N : ℕ) (hN : 1 ≤ N)
    (Z W : ℝ≥0 → channelKMTSpace ι → EuclideanSpace ℝ (Fin d))
    (hZa : StronglyAdapted augmentedChannelBrownianFiltration Z)
    (hWa : StronglyAdapted augmentedChannelBrownianFiltration W)
    (hZc : ∀ᵐ ω ∂channelKMTMeasure ι, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    (hWc : ∀ᵐ ω ∂channelKMTMeasure ι, ContinuousOn (fun t => W t ω) (Set.Icc 0 T))
    (hZ : ∀ᵐ ω ∂channelKMTMeasure ι, ∀ t ≤ T,
      Z t ω = StrongSDE.sdeRhs (channelWindowIto T) ell g b x₀ N Z t ω)
    (hW : ∀ᵐ ω ∂channelKMTMeasure ι, ∀ t ≤ T,
      W t ω = StrongSDE.sdeRhs (channelWindowIto T) ell g b x₀ N W t ω) :
    ∀ᵐ ω ∂channelKMTMeasure ι, ∀ t ≤ T, Z t ω = W t ω := by
  letI : ∀ i : ι, IsFilteredPreBrownian (channelBrownian i)
      augmentedChannelBrownianFiltration (channelKMTMeasure ι) :=
    channelBrownian_isFilteredPreBrownian_augmented
  exact StrongSDEGlobal.pathwise_unique_on_window augmentedChannelBrownianFiltration
    channelBrownian channelBrownian_continuous measurable_channelBrownian
    augmentedChannelBrownianFiltration_null ell g L hLip K hK b Lb hb C hC hbC
    x₀ T N hN Z W hZa hWa hZc hWc hZ hW

/-- A single process solves the equation for every nonnegative time on one
full-measure event, using the original channel probability space and drivers. -/
theorem exists_channel_all_time_solution (N : ℕ) (hN : 1 ≤ N) :
    ∃ Z : ℝ≥0 → channelKMTSpace ι → EuclideanSpace ℝ (Fin d),
      StronglyAdapted augmentedChannelBrownianFiltration Z ∧
      (∀ ω, Continuous (fun t => Z t ω)) ∧
      (∀ T : ℝ≥0, Integrable (fun ω => ⨆ t : Window T, ‖Z t.val ω‖ ^ 2)
        (channelKMTMeasure ι)) ∧
      (∀ᵐ ω ∂channelKMTMeasure ι, ∀ t,
        Z t ω = StrongSDE.sdeRhs channelAllTimeIto ell g b x₀ N Z t ω) := by
  letI : ∀ i : ι, IsFilteredPreBrownian (channelBrownian i)
      augmentedChannelBrownianFiltration (channelKMTMeasure ι) :=
    channelBrownian_isFilteredPreBrownian_augmented
  exact StrongSDEGlobal.exists_all_time_solution augmentedChannelBrownianFiltration
    channelBrownian channelBrownian_continuous measurable_channelBrownian
    augmentedChannelBrownianFiltration_null ell g L hLip K hK b Lb hb C hC hbC x₀ N hN

/-- All-time pathwise uniqueness with the original common Brownian drivers. -/
theorem channel_all_time_pathwise_unique (N : ℕ) (hN : 1 ≤ N)
    (Z W : ℝ≥0 → channelKMTSpace ι → EuclideanSpace ℝ (Fin d))
    (hZa : StronglyAdapted augmentedChannelBrownianFiltration Z)
    (hWa : StronglyAdapted augmentedChannelBrownianFiltration W)
    (hZc : ∀ᵐ ω ∂channelKMTMeasure ι, Continuous (fun t => Z t ω))
    (hWc : ∀ᵐ ω ∂channelKMTMeasure ι, Continuous (fun t => W t ω))
    (hZ : ∀ᵐ ω ∂channelKMTMeasure ι, ∀ t,
      Z t ω = StrongSDE.sdeRhs channelAllTimeIto ell g b x₀ N Z t ω)
    (hW : ∀ᵐ ω ∂channelKMTMeasure ι, ∀ t,
      W t ω = StrongSDE.sdeRhs channelAllTimeIto ell g b x₀ N W t ω) :
    ∀ᵐ ω ∂channelKMTMeasure ι, ∀ t, Z t ω = W t ω := by
  letI : ∀ i : ι, IsFilteredPreBrownian (channelBrownian i)
      augmentedChannelBrownianFiltration (channelKMTMeasure ι) :=
    channelBrownian_isFilteredPreBrownian_augmented
  exact StrongSDEGlobal.all_time_pathwise_unique augmentedChannelBrownianFiltration
    channelBrownian channelBrownian_continuous measurable_channelBrownian
    augmentedChannelBrownianFiltration_null ell g L hLip K hK b Lb hb C hC hbC
    x₀ N hN Z W hZa hWa hZc hWc hZ hW

end Coefficients
end Ripple.Kurtz.StrongApprox
