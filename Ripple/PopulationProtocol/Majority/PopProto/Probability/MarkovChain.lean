/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Markov Chain Framework

This file constructs the Markov transition kernel for the population protocol
from the one-step distribution `stepDist`.

## Main definitions

- `transitionKernel` : the `ProbabilityTheory.Kernel` mapping each configuration
  to its one-step successor distribution.

## Future Work

- Show that absorbing states (all-X, all-Y) are the only recurrent classes
  when starting with at least one opinionated agent
- Prove convergence to consensus with probability 1
- Bound the expected convergence time (O(n log n) from the paper)
-/

import Ripple.PopulationProtocol.Majority.PopProto.Probability.StepDist
import Mathlib.Probability.Kernel.Defs

namespace PopProto

namespace Config

variable {n : ℕ}

/-- The measurable space on `Config n` is the discrete σ-algebra,
    since `Config n` is (morally) a finite type for each `n`. -/
noncomputable instance instMeasurableSpaceConfig : MeasurableSpace (Config n) := ⊤

/-- With the discrete σ-algebra, every set is measurable. -/
instance instDiscreteMeasurableSpaceConfig : DiscreteMeasurableSpace (Config n) where
  forall_measurableSet _ := trivial

/-- The Markov transition kernel for the population protocol.
    Maps each configuration to the distribution over next configurations.

    Construction: for each configuration `c`, we use `(stepDist c hn).toMeasure`
    to produce a probability measure on `Config n`. The measurability condition
    is trivially satisfied because we use the discrete σ-algebra (⊤). -/
noncomputable def transitionKernel (hn : n ≥ 2) :
    ProbabilityTheory.Kernel (Config n) (Config n) where
  toFun c := (c.stepDist hn).toMeasure
  measurable' := Measurable.of_discrete

end Config
end PopProto
