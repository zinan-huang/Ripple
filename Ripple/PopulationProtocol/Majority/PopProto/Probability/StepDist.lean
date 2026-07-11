/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# One-Step Distribution

The one-step distribution over configurations: given a current configuration
`c`, the random scheduler picks an interaction `(s₁, s₂)`, and we apply the
deterministic step function to get the next configuration.

This composes the scheduler PMF with the step function via `PMF.map`.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Step
import Ripple.PopulationProtocol.Majority.PopProto.Probability.Scheduler
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace PopProto

namespace Config

variable {n : ℕ}

/-- The one-step distribution: given config `c` and `n ≥ 2`, produce a
    distribution over successor configurations by sampling a random
    interaction and applying `stepOrSelf`. -/
noncomputable def stepDist (c : Config n) (hn : n ≥ 2) : PMF (Config n) :=
  PMF.map (fun p => c.stepOrSelf p.1 p.2) (c.interactionPMF hn)

/-- The support of the step distribution is the set of configs reachable
    from `c` in one step. -/
theorem stepDist_support (c : Config n) (hn : n ≥ 2) (c' : Config n) :
    c' ∈ (c.stepDist hn).support →
    ∃ s₁ s₂ : State, c.stepOrSelf s₁ s₂ = c' := by
  intro h
  simp only [stepDist, PMF.support_map, Set.mem_image] at h
  obtain ⟨⟨s₁, s₂⟩, _, heq⟩ := h
  exact ⟨s₁, s₂, heq⟩

end Config
end PopProto
