import Ripple.Stochastic.HorizonItoRestriction
import Ripple.Stochastic.ConsistentHorizonProcess

/-!
# An all-time integral from coherent integer horizons

The definition selects the actual continuous
window integral on an integer horizon beyond the evaluation time. Membership
of the integrand in every integer-window predictable L² space gives agreement
with every integer-window integral on one common full-measure event. Neither
continuity nor boundedness of the integrand is assumed here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Ripple.Stochastic.AllTimeIto
open StrongSDEConcreteMaps FilteredItoIntegralCLM
open AdaptedContinuousSpace ContinuousItoElementary

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- The canonical integer-horizon selection of the actual window Itô integral. -/
def globalIto (F : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ)
    [IsFilteredPreBrownian B F μ]
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  windowIto (μ := μ) F (ConsistentHorizonProcess.horizon t : ℝ≥0) B hB hBmeas H t ω

/-- Every total window integral has continuous paths, including its zero branch
outside the predictable L² domain. This is continuity of the selected output,
not a regularity assumption on the input process. -/
theorem windowIto_continuous (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) [IsFilteredPreBrownian B F μ]
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Continuous (fun t => windowIto (μ := μ) F T B hB hBmeas H t ω) := by
  classical
  by_cases hm : MemLp (Function.uncurry H) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)
  · simp only [windowIto, dif_pos hm]
    exact (representative (continuousIto T hB hBmeas
      (hm.toLp (Function.uncurry H))) ω).continuous.comp (cappedTime_continuous T)
  · simp only [windowIto, dif_neg hm]
    exact continuous_const

/-- The total window operator is exactly adapted when the filtration contains
ambient measurable null sets. No input-domain premise is needed for its zero
branch. -/
theorem windowIto_adapted (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) [IsFilteredPreBrownian B F μ]
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (H : ℝ≥0 → Ω → ℝ) :
    StronglyAdapted F (windowIto (μ := μ) F T B hB hBmeas H) := by
  classical
  by_cases hm : MemLp (Function.uncurry H) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)
  · intro t
    show StronglyMeasurable[F t] (fun ω => windowIto (μ := μ) F T B hB hBmeas H t ω)
    simp only [windowIto, dif_pos hm]
    exact (continuousIto_representative_adapted T hB hBmeas hnull
      (hm.toLp (Function.uncurry H)) (cappedTime T t)).mono
        (F.mono (min_le_left t T))
  · intro t
    show StronglyMeasurable[F t] (fun ω => windowIto (μ := μ) F T B hB hBmeas H t ω)
    simp only [windowIto, dif_neg hm]
    exact stronglyMeasurable_const

/-- Actual integer-window integrals are indistinguishable on their common
smaller window. The larger domain membership is the only analytic premise. -/
theorem integer_window_consistency (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) [IsFilteredPreBrownian B F μ]
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ)
    (hm : ∀ n : ℕ, MemLp (Function.uncurry H) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas))
    (m n : ℕ) (hmn : m ≤ n) :
    ∀ᵐ ω ∂μ, ∀ t ≤ (m : ℝ≥0),
      windowIto (μ := μ) F (m : ℝ≥0) B hB hBmeas H t ω =
        windowIto (μ := μ) F (n : ℝ≥0) B hB hBmeas H t ω := by
  have hle : (m : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hmn
  exact (HorizonItoRestriction.windowIto_restrict hle hB hBmeas H (hm n)).mono
    fun _ h t ht => (h t ht).symm

/-- One full-measure event witnesses agreement at every time of every integer
prefix. Countability is used only for the horizon pairs. -/
theorem globalIto_integer_agreement (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) [IsFilteredPreBrownian B F μ]
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ)
    (hm : ∀ n : ℕ, MemLp (Function.uncurry H) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ t ≤ (n : ℝ≥0),
      globalIto (μ := μ) F B hB hBmeas H t ω = windowIto (μ := μ) F (n : ℝ≥0) B hB hBmeas H t ω := by
  exact ConsistentHorizonProcess.diagonal_agrees_ae
    (fun n : ℕ => windowIto (μ := μ) F (n : ℝ≥0) B hB hBmeas H)
    (integer_window_consistency F B hB hBmeas H hm)

/-- The all-time selected integral has continuous paths almost surely. Local
agreement with one longer fixed horizon handles each index-switching time. -/
theorem globalIto_continuous_ae (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) [IsFilteredPreBrownian B F μ]
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ)
    (hm : ∀ n : ℕ, MemLp (Function.uncurry H) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas)) :
    ∀ᵐ ω ∂μ, Continuous (fun t => globalIto (μ := μ) F B hB hBmeas H t ω) := by
  exact ConsistentHorizonProcess.diagonal_continuous_ae
    (fun n : ℕ => windowIto (μ := μ) F (n : ℝ≥0) B hB hBmeas H)
    (fun n => ae_of_all _ (windowIto_continuous (μ := μ) F (n : ℝ≥0) B hB hBmeas H))
    (integer_window_consistency F B hB hBmeas H hm)

/-- Time selection among adapted window integrals preserves adaptation exactly.
Integer-window domain membership is needed for coherence and continuity, but
not for this adaptation statement. -/
theorem globalIto_adapted (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) [IsFilteredPreBrownian B F μ]
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (H : ℝ≥0 → Ω → ℝ) :
    StronglyAdapted F (globalIto (μ := μ) F B hB hBmeas H) := by
  intro t
  exact windowIto_adapted (μ := μ) F (ConsistentHorizonProcess.horizon t : ℝ≥0)
    B hB hBmeas hnull H t

end Ripple.Stochastic.AllTimeIto
