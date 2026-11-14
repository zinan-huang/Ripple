import Ripple.Stochastic.StrongSDEShortWindows
import Ripple.Stochastic.AmbientNullAugmentation

/-!
# Strong solutions on a short window of the actual channel space

The state dimension and number of channels are independent.
The window length is positive and chosen from the Lipschitz constants; it is
the same for every positive population scale. No Brownian, null-completeness,
Doob, terminal-isometry, state-completeness, or realization premise is carried.
Extension to arbitrary horizons requires the separate integral-pasting proof.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox
open Ripple.Stochastic
open StrongSDEConcreteMaps StrongSDEShortWindows

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- The actual Kurtz state space, with Euclidean state norm and common drivers. -/
abbrev ChannelState (T : ℝ≥0) :=
  State (E := EuclideanSpace ℝ (Fin d)) (μ := channelKMTMeasure ι)
    augmentedChannelBrownianFiltration T

def channelRealize (T : ℝ≥0) (X : ChannelState (ι := ι) (d := d) T) :
    ℝ≥0 → channelKMTSpace ι → EuclideanSpace ℝ (Fin d) :=
  realize augmentedChannelBrownianFiltration T X

def channelWindowIto (T : ℝ≥0) (i : ι) :
    (ℝ≥0 → channelKMTSpace ι → ℝ) → ℝ≥0 → channelKMTSpace ι → ℝ := by
  letI := channelBrownian_isFilteredPreBrownian_augmented i
  exact windowIto (μ := channelKMTMeasure ι) augmentedChannelBrownianFiltration T (channelBrownian i)
    (channelBrownian_continuous i) (measurable_channelBrownian i)

/-- Every positive scale has an actual solution of the original finite-channel
equation on the explicitly chosen positive window. -/
theorem exists_channel_solution_on_shortWindow
    (ell : ι → EuclideanSpace ℝ (Fin d))
    (g : ι → EuclideanSpace ℝ (Fin d) → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (x₀ : EuclideanSpace ℝ (Fin d)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ X : ChannelState (ι := ι) (d := d) (shortWindow Lb (channelSize ell L)),
      StronglyAdapted augmentedChannelBrownianFiltration
        (channelRealize (shortWindow Lb (channelSize ell L)) X) ∧
      (∀ ω, Continuous (fun t => channelRealize (shortWindow Lb (channelSize ell L)) X t ω)) ∧
      Integrable (fun ω => ⨆ t : Window (shortWindow Lb (channelSize ell L)),
        ‖channelRealize (shortWindow Lb (channelSize ell L)) X t.val ω‖ ^ 2)
        (channelKMTMeasure ι) ∧
      (∀ᵐ ω ∂channelKMTMeasure ι, ∀ t ≤ shortWindow Lb (channelSize ell L),
        channelRealize (shortWindow Lb (channelSize ell L)) X t ω =
          StrongSDE.sdeRhs (channelWindowIto (shortWindow Lb (channelSize ell L)))
            ell g b x₀ N (channelRealize (shortWindow Lb (channelSize ell L)) X) t ω) := by
  letI : ∀ i : ι, IsFilteredPreBrownian (channelBrownian i)
      augmentedChannelBrownianFiltration (channelKMTMeasure ι) :=
    channelBrownian_isFilteredPreBrownian_augmented
  apply exists_concrete_solution augmentedChannelBrownianFiltration
    (shortWindow Lb (channelSize ell L)) channelBrownian
    channelBrownian_continuous measurable_channelBrownian
    augmentedChannelBrownianFiltration_null ell g L hLip K hK b Lb hb C hC hbC x₀ N hN
  simpa only [channelSize_coe] using shortWindow_small Lb (channelSize ell L)

/-- Positive scales are selected on one carrier and one common event. No
independent copies of solution laws are introduced. -/
theorem exists_simultaneous_channel_solutions_on_shortWindow
    (ell : ι → EuclideanSpace ℝ (Fin d))
    (g : ι → EuclideanSpace ℝ (Fin d) → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (x₀ : EuclideanSpace ℝ (Fin d)) :
    ∃ Z : ℕ → ChannelState (ι := ι) (d := d) (shortWindow Lb (channelSize ell L)),
      (∀ N, 1 ≤ N →
        StronglyAdapted augmentedChannelBrownianFiltration
          (channelRealize (shortWindow Lb (channelSize ell L)) (Z N)) ∧
        (∀ ω, Continuous (fun t => channelRealize (shortWindow Lb (channelSize ell L)) (Z N) t ω)) ∧
        Integrable (fun ω => ⨆ t : Window (shortWindow Lb (channelSize ell L)),
          ‖channelRealize (shortWindow Lb (channelSize ell L)) (Z N) t.val ω‖ ^ 2)
          (channelKMTMeasure ι)) ∧
      (∀ᵐ ω ∂channelKMTMeasure ι, ∀ N, 1 ≤ N → ∀ t ≤ shortWindow Lb (channelSize ell L),
        channelRealize (shortWindow Lb (channelSize ell L)) (Z N) t ω =
          StrongSDE.sdeRhs (channelWindowIto (shortWindow Lb (channelSize ell L)))
            ell g b x₀ N (channelRealize (shortWindow Lb (channelSize ell L)) (Z N)) t ω) := by
  classical
  let hex := fun N hN => exists_channel_solution_on_shortWindow ell g L hLip K hK
    b Lb hb C hC hbC x₀ N hN
  let Z : ℕ → ChannelState (ι := ι) (d := d) (shortWindow Lb (channelSize ell L)) :=
    fun N => if hN : 1 ≤ N then Classical.choose (hex N hN) else 0
  have hZ : ∀ N, ∀ hN : 1 ≤ N,
      Z N = Classical.choose (hex N hN) := fun N hN => dif_pos hN
  refine ⟨Z, ?_, ae_all_iff.mpr ?_⟩
  · intro N hN
    rw [hZ N hN]
    exact ⟨(Classical.choose_spec (hex N hN)).1,
      (Classical.choose_spec (hex N hN)).2.1, (Classical.choose_spec (hex N hN)).2.2.1⟩
  · intro N
    by_cases hN : 1 ≤ N
    · rw [hZ N hN]
      filter_upwards [(Classical.choose_spec (hex N hN)).2.2.2] with ω hω
      exact fun _ => hω
    · exact ae_of_all _ fun _ h => (hN h).elim

/-- Pathwise uniqueness in the constructed carrier on the same short window. -/
theorem channel_solution_unique_on_shortWindow
    (ell : ι → EuclideanSpace ℝ (Fin d))
    (g : ι → EuclideanSpace ℝ (Fin d) → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (x₀ : EuclideanSpace ℝ (Fin d)) (N : ℕ) (hN : 1 ≤ N)
    (X Y : ChannelState (ι := ι) (d := d) (shortWindow Lb (channelSize ell L)))
    (hX : ∀ᵐ ω ∂channelKMTMeasure ι, ∀ t ≤ shortWindow Lb (channelSize ell L),
      channelRealize (shortWindow Lb (channelSize ell L)) X t ω =
        StrongSDE.sdeRhs (channelWindowIto (shortWindow Lb (channelSize ell L)))
          ell g b x₀ N (channelRealize (shortWindow Lb (channelSize ell L)) X) t ω)
    (hY : ∀ᵐ ω ∂channelKMTMeasure ι, ∀ t ≤ shortWindow Lb (channelSize ell L),
      channelRealize (shortWindow Lb (channelSize ell L)) Y t ω =
        StrongSDE.sdeRhs (channelWindowIto (shortWindow Lb (channelSize ell L)))
          ell g b x₀ N (channelRealize (shortWindow Lb (channelSize ell L)) Y) t ω) :
    X = Y ∧ ∀ᵐ ω ∂channelKMTMeasure ι, ∀ t,
      channelRealize (shortWindow Lb (channelSize ell L)) X t ω =
        channelRealize (shortWindow Lb (channelSize ell L)) Y t ω := by
  letI : ∀ i : ι, IsFilteredPreBrownian (channelBrownian i)
      augmentedChannelBrownianFiltration (channelKMTMeasure ι) :=
    channelBrownian_isFilteredPreBrownian_augmented
  apply concrete_solution_unique augmentedChannelBrownianFiltration
    (shortWindow Lb (channelSize ell L)) channelBrownian channelBrownian_continuous
    measurable_channelBrownian augmentedChannelBrownianFiltration_null
    ell g L hLip K hK b Lb hb C hC hbC x₀ N hN _ X Y hX hY
  simpa only [channelSize_coe] using shortWindow_small Lb (channelSize ell L)

end Ripple.Kurtz.StrongApprox
