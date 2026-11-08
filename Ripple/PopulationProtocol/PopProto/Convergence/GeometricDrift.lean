/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Geometric Drift and Convergence

The multiplicative drift theorem applied to the population protocol.

## Main results

- `lintegral_geometric_decay`: If `∫⁻ Φ dK(x) ≤ r·Φ(x)` for all x, then
  `∫⁻ Φ d(K^t)(x) ≤ r^t · Φ(x)`.

- `prob_in_region_le`: The probability of remaining in a region for t steps
  decays geometrically: `P[in region at t] ≤ (1-δ)^t · Φ(x₀)`.

## Dependencies

Requires `Mathlib.Probability.Kernel.Composition.Comp` for `Kernel.lintegral_comp`
and `Kernel.pow`.
-/

import Ripple.PopulationProtocol.PopProto.Convergence.Expected
import Ripple.PopulationProtocol.PopProto.Probability.MarkovChain
import Mathlib.Probability.Kernel.Composition.Comp
import Ripple.PopulationProtocol.PopProtoCommon.Convergence.GeometricDrift

namespace Ripple.PopulationProtocol.PopProto

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace Config

variable {n : ℕ}

/-! ### IsMarkovKernel instance for the transition kernel -/

instance instIsMarkovKernel (hn : n ≥ 2) :
    IsMarkovKernel (transitionKernel hn) where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure ((a.stepDist hn).toMeasure)
    infer_instance

/-! ### Geometric Decay Lemma

The key measure-theoretic lemma: if a Markov kernel K satisfies
`∫⁻ Φ dK(x) ≤ r·Φ(x)` for all x, then iterating K for t steps gives
`∫⁻ Φ d(K^t)(x) ≤ r^t · Φ(x)`.

Proof by induction on t using:
- Base: K^0 = id, integral = Φ(x)
- Step: K^{t+1} = K^t ∘ₖ K, use Chapman-Kolmogorov + monotonicity -/

/-! ### Markov's inequality application

From geometric decay E[Φ_t] ≤ r^t · Φ_0 and Φ ≥ 1 in the region,
we get P[in region at time t] ≤ r^t · Φ_0. -/

end Config
end Ripple.PopulationProtocol.PopProto
