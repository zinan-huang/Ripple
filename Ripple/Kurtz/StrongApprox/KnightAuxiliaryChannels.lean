import Ripple.Kurtz.StrongApprox.ChannelBrownianFiltration
import Ripple.Stochastic.ContinuousAdaptedIntegrand
import Ripple.Stochastic.KnightBrownianLaw

/-!
# Concrete auxiliary Brownian channels for Knight completion

The auxiliary factor is the already constructed channel KMT product space.
Its actual Brownian coordinates have pointwise continuous paths and pointwise
zero initial values. Joint evaluation is measurable because these coordinates
are adapted continuous processes for their common natural filtration.

The construction has no population-size parameter. The same auxiliary factor
may therefore complete all population sizes on a single product extension.
Only independence of channels within each population size is asserted.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic
open Ripple.Stochastic.Knight

variable {ι : Type} [Fintype ι]

/-- The actual channel Brownian evaluation is jointly measurable in internal
time and sample. Predictability is first obtained from filtered adaptedness
and pointwise continuity, then enlarged to the ambient product sigma-algebra. -/
theorem measurable_uncurry_channelBrownian (i : ι) :
    Measurable (Function.uncurry (channelBrownian i)) := by
  have ha : ∀ t, Measurable[channelBrownianFiltration (ι := ι) t]
      (channelBrownian i t) := fun t =>
    ((channelBrownian_isFilteredPreBrownian i).stronglyAdapted t).measurable
  have hp : StronglyMeasurable[(channelBrownianFiltration (ι := ι)).predictable]
      (Function.uncurry (channelBrownian i)) :=
    ContinuousAdaptedIntegrand.stronglyMeasurable_uncurry ha
      (channelBrownian_continuous i)
  have hm : StronglyMeasurable (Function.uncurry (channelBrownian i)) :=
    hp.mono (channelBrownianFiltration (ι := ι)).predictable_le_prod
  exact hm.measurable

/-- The auxiliary process has continuous paths on one event for all channels;
in this construction continuity holds at every sample. -/
theorem channelBrownian_continuous_ae :
    ∀ᵐ z ∂channelKMTMeasure ι, ∀ i : ι,
      Continuous (fun t => channelBrownian i t z) :=
  ae_of_all _ fun z i => channelBrownian_continuous i z

/-- All rectangular auxiliary increment laws follow from the constructed
Brownian finite-dimensional laws and the actual product-channel independence. -/
theorem channelBrownian_rectangular_gaussian :
    HasRectangularGaussianIncrements (channelBrownian (ι := ι)) (channelKMTMeasure ι) :=
  rectangular_of_brownian_family channelBrownian_isPreBrownian
    channelBrownian_paths_independent

/-- All auxiliary inputs to completed Knight, discharged for the actual
channel KMT product space rather than supplied as fields of auxiliary data. -/
theorem channelBrownian_knight_auxiliary :
    (∀ (i : ι) z, channelBrownian i 0 z = 0) ∧
    (∀ i : ι, Measurable (Function.uncurry (channelBrownian i))) ∧
    (∀ i : ι, ∀ᵐ z ∂channelKMTMeasure ι,
      Continuous (fun t => channelBrownian i t z)) ∧
    (∀ i : ι, IsPreBrownian (channelBrownian i) (channelKMTMeasure ι)) ∧
    iIndepFun (fun (i : ι) z t => channelBrownian i t z) (channelKMTMeasure ι) ∧
    HasRectangularGaussianIncrements (channelBrownian (ι := ι)) (channelKMTMeasure ι) := by
  refine ⟨channelBrownian_zero, measurable_uncurry_channelBrownian, ?_,
    channelBrownian_isPreBrownian, channelBrownian_paths_independent,
    channelBrownian_rectangular_gaussian⟩
  intro i
  exact ae_of_all _ (channelBrownian_continuous i)

end Ripple.Kurtz.StrongApprox
