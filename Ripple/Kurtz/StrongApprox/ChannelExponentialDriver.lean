import Ripple.Stochastic.FiniteChannelExponentialLimit
import Ripple.Stochastic.AmbientNullAugmentation

/-!
# Stochastic exponentials on the constructed Brownian channel space

The original product coupling supplies coordinate independence of increments
and independence of the entire fresh increment vector from the common past.
Ambient null augmentation does not change the carrier or probability measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Ripple.Kurtz.StrongApprox
open Ripple.Stochastic Ripple.Stochastic.FiniteChannelExponentialLimit

variable {d : ℕ}

/-- Independent path coordinates give independent fresh increment coordinates.
This statement is separate from independence of the whole increment vector
from the common past, which is supplied by the channel filtration producer. -/
theorem channelBrownian_increment_coordinates_independent (s t : ℝ≥0) :
    iIndepFun (fun j (ω : channelKMTSpace (Fin d)) =>
      channelBrownian j t ω - channelBrownian j s ω) (channelKMTMeasure (Fin d)) :=
  channelBrownian_paths_independent.comp (fun _ f => f t - f s)
    (fun _ => (measurable_pi_apply t).sub (measurable_pi_apply s))

/-- All Gaussian-driver premises of the finite-channel exponential producer
are discharged by the constructed channel paths on their original carrier. -/
theorem channel_bounded_approximation_exponential_martingale
    (s : ℕ → ℕ → ℝ≥0) (hs : ∀ n, Monotone (s n)) (hz : ∀ n, s n 0 = 0)
    (c : ℕ → ℕ → channelKMTSpace (Fin d) → Fin d → ℝ)
    (hc : ∀ n i, Measurable[augmentedChannelBrownianFiltration (s n i)] (c n i))
    (N : ℕ → ℕ) {K : ℝ} (hK : ∀ n i ω j, |c n i ω j| ≤ K)
    (M Q : ℝ≥0 → channelKMTSpace (Fin d) → ℝ)
    (hM : StronglyAdapted augmentedChannelBrownianFiltration M)
    (hQ : StronglyAdapted augmentedChannelBrownianFiltration Q)
    (hlimM : ∀ t, ∀ᵐ ω ∂(channelKMTMeasure (Fin d)), Tendsto
      (fun n => vectorSum channelBrownian (s n) (c n) (N n) t ω) atTop (nhds (M t ω)))
    (hlimQ : ∀ t, ∀ᵐ ω ∂(channelKMTMeasure (Fin d)), Tendsto
      (fun n => vectorBracket (s n) (c n) (N n) t ω) atTop (nhds (Q t ω))) (lam : ℝ) :
    Martingale (fun t ω => Real.exp (lam * M t ω - lam ^ 2 * Q t ω / 2))
      augmentedChannelBrownianFiltration (channelKMTMeasure (Fin d)) := by
  exact vector_stochastic_exponential_of_bounded_approximation channelBrownian
    channelBrownian_isFilteredPreBrownian_augmented
    (fun r t _ => channelBrownian_increment_coordinates_independent r t)
    (fun _ _ h => channelBrownian_vectorIncrement_indep_augmented h)
    s hs hz c hc N hK M Q hM hQ hlimM hlimQ lam

/-- Exact constrained maximal inequality on the actual channel coupling space.
The remaining approximation premises refer to a single common partition. -/
theorem channel_bounded_approximation_exponential_maximal
    (s : ℕ → ℕ → ℝ≥0) (hs : ∀ n, Monotone (s n)) (hz : ∀ n, s n 0 = 0)
    (c : ℕ → ℕ → channelKMTSpace (Fin d) → Fin d → ℝ)
    (hc : ∀ n i, Measurable[augmentedChannelBrownianFiltration (s n i)] (c n i))
    (N : ℕ → ℕ) {K : ℝ} (hK : ∀ n i ω j, |c n i ω j| ≤ K)
    (M Q : ℝ≥0 → channelKMTSpace (Fin d) → ℝ)
    (hM : StronglyAdapted augmentedChannelBrownianFiltration M)
    (hQ : StronglyAdapted augmentedChannelBrownianFiltration Q)
    (hlimM : ∀ t, ∀ᵐ ω ∂(channelKMTMeasure (Fin d)), Tendsto
      (fun n => vectorSum channelBrownian (s n) (c n) (N n) t ω) atTop (nhds (M t ω)))
    (hlimQ : ∀ t, ∀ᵐ ω ∂(channelKMTMeasure (Fin d)), Tendsto
      (fun n => vectorBracket (s n) (c n) (N n) t ω) atTop (nhds (Q t ω)))
    (hQmono : ∀ᵐ ω ∂(channelKMTMeasure (Fin d)), Monotone (fun t => Q t ω))
    (hMcont : ∀ᵐ ω ∂(channelKMTMeasure (Fin d)), Continuous (fun t => M t ω))
    (hQcont : ∀ᵐ ω ∂(channelKMTMeasure (Fin d)), Continuous (fun t => Q t ω))
    (T : ℝ≥0) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    channelKMTMeasure (Fin d) (ExponentialMaximal.crossingEvent M Q T r q) ≤
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  exact vector_bounded_approximation_exponential_maximal channelBrownian
    channelBrownian_isFilteredPreBrownian_augmented
    (fun r t _ => channelBrownian_increment_coordinates_independent r t)
    (fun _ _ h => channelBrownian_vectorIncrement_indep_augmented h)
    s hs hz c hc N hK M Q hM hQ hlimM hlimQ hQmono hMcont hQcont T hr hq

/-- Continuous versions of the actual scalar channel integrals, summed in the
sharp maximal theorem below. All driver data come from the channel producer. -/
def channelContinuousIntegral (T : ℝ≥0)
    (H : Fin d → ℝ≥0 → channelKMTSpace (Fin d) → ℝ)
    (ha : ∀ j t, Measurable[augmentedChannelBrownianFiltration t] (H j t))
    (hc : ∀ j ω, Continuous (fun t => H j t ω)) (K : ℝ)
    (hb : ∀ j t ω, |H j t ω| ≤ K) (j : Fin d) :
    channelKMTSpace (Fin d) → C(Icc (0 : ℝ≥0) T, ℝ) :=
  continuousChannelIntegral channelBrownian channelBrownian_isFilteredPreBrownian_augmented T
    channelBrownian_continuous measurable_channelBrownian H ha hc K hb j

/-- Exact finite-channel exponential maximal inequality for bounded continuous
adapted input on the constructed coupling space. The common approximation,
square bound, UI, Vitali, and joint-driver premises are all supplied internally. -/
theorem channel_bounded_continuous_exponential_maximal (T : ℝ≥0)
    (H : Fin d → ℝ≥0 → channelKMTSpace (Fin d) → ℝ)
    (ha : ∀ j t, Measurable[augmentedChannelBrownianFiltration t] (H j t))
    (hc : ∀ j ω, Continuous (fun t => H j t ω)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ j t ω, |H j t ω| ≤ K) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    channelKMTMeasure (Fin d) {ω | (∃ t : Icc (0 : ℝ≥0) T,
      r ≤ ∑ j, channelContinuousIntegral T H ha hc K hb j ω t) ∧
      (∑ j, ∫ s in Ioc (0 : ℝ≥0) T, (H j s ω) ^ 2 ∂FilteredItoIntegralL2.timeMeasure) ≤ q} ≤
        ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  exact bounded_continuous_vector_exponential_maximal channelBrownian
    channelBrownian_isFilteredPreBrownian_augmented
    (fun r t _ => channelBrownian_increment_coordinates_independent r t)
    (fun _ _ h => channelBrownian_vectorIncrement_indep_augmented h)
    T channelBrownian_continuous measurable_channelBrownian
    augmentedChannelBrownianFiltration_null H ha hc hK hb hr hq

end Ripple.Kurtz.StrongApprox
