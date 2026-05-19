/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Support Invariants for the Nonuniform Exact Majority Markov Chain

The concrete transition kernel is stochastic, but every support point of its
one-step distribution is a deterministic protocol-reachable configuration.
This file packages the deterministic invariants in that support form.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.NonuniformMarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.WellFormedConfig

namespace ExactMajority

variable {L K : ℕ}

/-- A stochastic one-step support point preserves the initial input gap. -/
theorem nonuniformStepDistOrSelf_support_initialGap_eq
    (c c' : Config (AgentState L K)) :
    c' ∈ (nonuniformStepDistOrSelf L K c).support →
      initialGap c' = initialGap c := by
  intro hsupp
  exact reachable_initialGap_invariant (L := L) (K := K) c c'
    (nonuniformStepDistOrSelf_support_reachable (L := L) (K := K) c c' hsupp)

/-- A stochastic one-step support point preserves the majority verdict. -/
theorem nonuniformStepDistOrSelf_support_majorityVerdict_eq
    (c c' : Config (AgentState L K)) :
    c' ∈ (nonuniformStepDistOrSelf L K c).support →
      majorityVerdict c' = majorityVerdict c := by
  intro hsupp
  exact majorityVerdict_reachable_invariant (L := L) (K := K) c c'
    (nonuniformStepDistOrSelf_support_reachable (L := L) (K := K) c c' hsupp)

/-- A stochastic one-step support point preserves well-formedness. -/
theorem nonuniformStepDistOrSelf_support_well_formed_config
    (c c' : Config (AgentState L K))
    (hwell : well_formed_config c) :
    c' ∈ (nonuniformStepDistOrSelf L K c).support →
      well_formed_config c' := by
  intro hsupp
  exact well_formed_config_preserved_by_reachable (L := L) (K := K) c c'
    hwell
    (nonuniformStepDistOrSelf_support_reachable (L := L) (K := K) c c' hsupp)

/-- If the current configuration is reachable from a valid initial
configuration, then every stochastic one-step support point remains
well-formed. -/
theorem validInitial_nonuniformStepDistOrSelf_support_well_formed_config
    (init c c' : Config (AgentState L K))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    c' ∈ (nonuniformStepDistOrSelf L K c).support →
      well_formed_config c' := by
  intro hsupp
  have hwell : well_formed_config c :=
    validInitial_well_formed_config_of_reachable (L := L) (K := K)
      init c hvalid hreach
  exact nonuniformStepDistOrSelf_support_well_formed_config
    (L := L) (K := K) c c' hwell hsupp

/-- If the current configuration is reachable from a valid initial
configuration, then every stochastic one-step support point has the same
majority verdict as the initial configuration. -/
theorem validInitial_nonuniformStepDistOrSelf_support_majorityVerdict_eq
    (init c c' : Config (AgentState L K))
    (_hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    c' ∈ (nonuniformStepDistOrSelf L K c).support →
      majorityVerdict c' = majorityVerdict init := by
  intro hsupp
  have hc : majorityVerdict c = majorityVerdict init :=
    majorityVerdict_reachable_invariant (L := L) (K := K) init c hreach
  exact (nonuniformStepDistOrSelf_support_majorityVerdict_eq
    (L := L) (K := K) c c' hsupp).trans hc

end ExactMajority
