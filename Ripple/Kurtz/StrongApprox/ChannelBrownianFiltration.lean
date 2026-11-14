import Ripple.Kurtz.StrongApprox.ChannelProductTransport
import Ripple.Kurtz.StrongApprox.DyadicPreBrownian
import Ripple.Stochastic.IndependentBrownianFiltration

/-!
# The natural filtration of the constructed KMT Brownian channels

Only Brownian evaluations generate this filtration. The auxiliary Poisson
coordinates of the coupling remain in the ambient space.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory
open Ripple.Stochastic Ripple.Stochastic.IndependentBrownianFiltration
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

/-- Restriction of the actual all-time channel to nonnegative times. -/
def channelBrownian (i : ι) (t : ℝ≥0) : channelKMTSpace ι → ℝ :=
  channelKMTBrownian i t

theorem measurable_channelBrownian (i : ι) (t : ℝ≥0) :
    Measurable (channelBrownian i t) := measurable_channelKMTBrownian i t

/-- The complete nonnegative-time Brownian paths are independent coordinates
as random elements of the cylinder-measurable path space. -/
theorem channelBrownian_paths_independent :
    iIndepFun (fun i (ω : channelKMTSpace ι) (t : ℝ≥0) => channelBrownian i t ω)
      (channelKMTMeasure ι) := by
  exact channelKMTEval_iIndep.comp
    (fun _ x (t : ℝ≥0) => AllTimeKMT.allTimeKMTBrownian t x)
    (fun _ => measurable_pi_lambda _ fun t =>
      AllTimeKMT.measurable_allTimeKMTBrownian t)

/-- The common natural filtration, on the original coupling space and measure. -/
def channelBrownianFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (channelKMTSpace ι)) :=
  vectorNatural channelBrownian measurable_channelBrownian

theorem channelBrownian_continuous (i : ι) (ω : channelKMTSpace ι) :
    Continuous (fun t : ℝ≥0 => channelBrownian i t ω) :=
  (channelKMTBrownian_continuous i ω).comp NNReal.continuous_coe

theorem channelBrownian_zero (i : ι) (ω : channelKMTSpace ι) :
    channelBrownian i 0 ω = 0 :=
  AllTimeKMTLaws.allTimeKMTBrownian_zero_time (ω i)

/-- The concrete channel producer supplies all finite-dimensional laws, not
merely the dyadic increment laws exported by its original interface. -/
theorem channelBrownian_isPreBrownian (i : ι) :
    IsPreBrownian (channelBrownian i) (channelKMTMeasure ι) := by
  exact allDyadicBrownian_isPreBrownian
    (channelKMTBrownian_dyadicBrownianOn i)
    (Filter.Eventually.of_forall (channelBrownian_zero i))

/-- All original channels are filtered Brownian motions for one common natural
filtration on the original channel product coupling space. -/
theorem channelBrownian_isFilteredPreBrownian (i : ι) :
    IsFilteredPreBrownian (channelBrownian i) channelBrownianFiltration
      (channelKMTMeasure ι) :=
  isFilteredPreBrownian_vectorNatural channelBrownian_isPreBrownian
    measurable_channelBrownian channelBrownian_paths_independent i

/-- The complete vector increment is independent of the common past. -/
theorem channelBrownian_vectorIncrement_indep {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun ω i => channelBrownian i t ω - channelBrownian i s ω) inferInstance)
      (channelBrownianFiltration (ι := ι) s) (channelKMTMeasure ι) :=
  vectorIncrement_indep_natural channelBrownian_isPreBrownian
    measurable_channelBrownian channelBrownian_paths_independent hst

/-- The vector increment law has independent centered Gaussian coordinates,
each with variance `t-s`, for arbitrary nonnegative real times. -/
theorem channelBrownian_vectorIncrement_law {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun (ω : channelKMTSpace ι) i => channelBrownian i t ω - channelBrownian i s ω)
      (Measure.pi fun _ : ι => gaussianReal 0 (t - s)) (channelKMTMeasure ι) :=
  vectorIncrement_hasLaw channelBrownian_isPreBrownian
    measurable_channelBrownian channelBrownian_paths_independent hst

/-- The vector finite-dimensional laws are jointly Gaussian across both
coordinate and time indices. -/
theorem channelBrownian_tagged_isGaussianProcess :
    IsGaussianProcess (fun p : ι × ℝ≥0 => channelBrownian p.1 p.2)
      (channelKMTMeasure ι) :=
  tagged_isGaussianProcess (fun i => (channelBrownian_isPreBrownian i).isGaussianProcess)
    channelBrownian_paths_independent

/-- The actual Brownian vector has continuous paths. -/
theorem channelBrownian_vector_continuous (ω : channelKMTSpace ι) :
    Continuous (fun t : ℝ≥0 => fun i => channelBrownian i t ω) :=
  continuous_pi fun i => channelBrownian_continuous i ω

end Ripple.Kurtz.StrongApprox
