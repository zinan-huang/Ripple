import Ripple.Stochastic.BrownianMotion.Gaussian.BrownianMotion
import Ripple.Kurtz.StrongApprox.ChannelBrownianFiltration

/-!
# Adding ambient measurable null sets to a Brownian filtration

The probability space and measure are unchanged. Each
slice consists of ambient measurable sets equal almost everywhere to an old
slice-measurable set. This is sufficient for the continuous representative
construction; no right-continuity of the augmented filtration is asserted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Ripple.Stochastic.AmbientNullAugmentation

variable {Ω : Type*}

/-- Completion inside the fixed ambient sigma algebra. The sub-sigma-algebra is bound
before the ambient instance, so the ambient one is used by default below. -/
def within (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) :
    MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[mΩ] A ∧ ∃ B, MeasurableSet[m] B ∧ A =ᵐ[μ] B
  measurableSet_empty := ⟨MeasurableSet.empty, ∅, @MeasurableSet.empty Ω m, ae_eq_refl _⟩
  measurableSet_compl := by
    rintro A ⟨hA, B, hB, hAB⟩
    exact ⟨hA.compl, Bᶜ, hB.compl, hAB.compl⟩
  measurableSet_iUnion := by
    intro A hA
    choose hAm B hBm hAB using hA
    exact ⟨MeasurableSet.iUnion hAm, ⋃ n, B n, MeasurableSet.iUnion hBm,
      Filter.EventuallyEq.countable_iUnion hAB⟩

theorem within_le (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {μ : Measure Ω} :
    within m μ ≤ mΩ :=
  fun _ h => h.1

theorem le_within {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (hm : m ≤ mΩ) : m ≤ within m μ :=
  fun A hA => ⟨hm A hA, A, hA, ae_eq_refl _⟩

theorem within_mono {m n : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (hmn : m ≤ n) : within m μ ≤ within n μ := by
  rintro A ⟨hA, B, hB, hAB⟩
  exact ⟨hA, B, hmn B hB, hAB⟩

/-- The exact null-set absorption condition used by path realization. -/
theorem null_measurable (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {A : Set Ω} (hA : MeasurableSet[mΩ] A) (hzero : μ A = 0) :
    MeasurableSet[within m μ] A :=
  ⟨hA, ∅, @MeasurableSet.empty Ω m, ae_eq_empty.mpr hzero⟩

/-- Adjoining only null information preserves independence. -/
theorem indep_within_right {m n : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} (h : Indep m n μ) :
    Indep m (within n μ) μ := by
  apply (Indep_iff _ _ _).mpr
  rintro A B hA ⟨_, C, hC, hBC⟩
  have hi : (A ∩ B : Set Ω) =ᵐ[μ] (A ∩ C : Set Ω) :=
    (EventuallyEq.refl _ A).inter hBC
  rw [measure_congr hi, measure_congr hBC]
  exact (Indep_iff _ _ _).mp h A C hA hC

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- The original ambient space remains fixed. -/
def filtration {I : Type*} [Preorder I] (F : Filtration I mΩ) (μ : Measure Ω) :
    Filtration I mΩ where
  seq t := within (F t) μ
  mono' _ _ h := within_mono (F.mono h)
  le' t := within_le (F t)

theorem filtration_le {I : Type*} [Preorder I] (F : Filtration I mΩ) (t : I) :
    F t ≤ filtration F μ t := le_within (F.le t)

theorem filtration_null {I : Type*} [Preorder I] (F : Filtration I mΩ)
    (t : I) (A : Set Ω) (hA : MeasurableSet A) (hzero : μ A = 0) :
    MeasurableSet[filtration F μ t] A := null_measurable (F t) hA hzero

/-- Both adaptedness and increment independence survive on the same measure. -/
theorem isFilteredPreBrownian {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    [hB : IsFilteredPreBrownian B F μ] :
    IsFilteredPreBrownian B (filtration F μ) μ where
  toIsPreBrownian := hB.toIsPreBrownian
  stronglyAdapted t := (hB.stronglyAdapted t).mono (filtration_le F t)
  indep s t hst := indep_within_right (hB.indep s t hst)

end Ripple.Stochastic.AmbientNullAugmentation

namespace Ripple.Kurtz.StrongApprox
open Ripple.Stochastic Ripple.Stochastic.AmbientNullAugmentation
variable {ι : Type*} [Fintype ι]

/-- The common channel filtration augmented only by ambient measurable null sets. -/
def augmentedChannelBrownianFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (channelKMTSpace ι)) :=
  filtration channelBrownianFiltration (channelKMTMeasure ι)

theorem augmentedChannelBrownianFiltration_null (t : ℝ≥0)
    (A : Set (channelKMTSpace ι)) (hA : MeasurableSet A)
    (hzero : channelKMTMeasure ι A = 0) :
    MeasurableSet[augmentedChannelBrownianFiltration t] A :=
  filtration_null channelBrownianFiltration t A hA hzero

theorem channelBrownian_isFilteredPreBrownian_augmented (i : ι) :
    IsFilteredPreBrownian (channelBrownian i) augmentedChannelBrownianFiltration
      (channelKMTMeasure ι) := by
  letI := channelBrownian_isFilteredPreBrownian i
  exact AmbientNullAugmentation.isFilteredPreBrownian

/-- Joint independence, not only scalar independence, survives augmentation. -/
theorem channelBrownian_vectorIncrement_indep_augmented {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun ω i => channelBrownian i t ω - channelBrownian i s ω) inferInstance)
      (augmentedChannelBrownianFiltration (ι := ι) s) (channelKMTMeasure ι) :=
  indep_within_right (channelBrownian_vectorIncrement_indep hst)

end Ripple.Kurtz.StrongApprox
