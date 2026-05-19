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

open MeasureTheory ProbabilityTheory

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

/-- The initial-gap invariant holds almost surely after any finite number of
steps of the concrete nonuniform Markov chain. -/
theorem nonuniformTransitionKernel_pow_initialGap_eq
    (c : Config (AgentState L K)) (t : ℕ) :
    ∀ᵐ c' ∂((nonuniformTransitionKernel L K ^ t) c),
      initialGap c' = initialGap c := by
  exact Protocol.ae_of_stepDistOrSelf_support_preserved
    (P := NonuniformMajority L K)
    (Q := fun c' => initialGap c' = initialGap c)
    (fun c₀ c₁ hgap hsupp =>
      (nonuniformStepDistOrSelf_support_initialGap_eq
        (L := L) (K := K) c₀ c₁ hsupp).trans hgap)
    c rfl t

/-- The majority-verdict invariant holds almost surely after any finite number
of steps of the concrete nonuniform Markov chain. -/
theorem nonuniformTransitionKernel_pow_majorityVerdict_eq
    (c : Config (AgentState L K)) (t : ℕ) :
    ∀ᵐ c' ∂((nonuniformTransitionKernel L K ^ t) c),
      majorityVerdict c' = majorityVerdict c := by
  exact Protocol.ae_of_stepDistOrSelf_support_preserved
    (P := NonuniformMajority L K)
    (Q := fun c' => majorityVerdict c' = majorityVerdict c)
    (fun c₀ c₁ hverdict hsupp =>
      (nonuniformStepDistOrSelf_support_majorityVerdict_eq
        (L := L) (K := K) c₀ c₁ hsupp).trans hverdict)
    c rfl t

/-- Well-formedness holds almost surely after any finite number of steps of
the concrete nonuniform Markov chain. -/
theorem nonuniformTransitionKernel_pow_well_formed_config
    (c : Config (AgentState L K)) (hwell : well_formed_config c) (t : ℕ) :
    ∀ᵐ c' ∂((nonuniformTransitionKernel L K ^ t) c),
      well_formed_config c' := by
  exact Protocol.ae_of_stepDistOrSelf_support_preserved
    (P := NonuniformMajority L K)
    (Q := well_formed_config)
    (fun c₀ c₁ hwell₀ hsupp =>
      nonuniformStepDistOrSelf_support_well_formed_config
        (L := L) (K := K) c₀ c₁ hwell₀ hsupp)
    c hwell t

/-- Valid initial configurations remain well formed almost surely after any
finite number of nonuniform Markov-chain steps. -/
theorem validInitial_nonuniformTransitionKernel_pow_well_formed_config
    (init : Config (AgentState L K)) (hvalid : validInitial init) (t : ℕ) :
    ∀ᵐ c' ∂((nonuniformTransitionKernel L K ^ t) init),
      well_formed_config c' :=
  nonuniformTransitionKernel_pow_well_formed_config
    (L := L) (K := K) init (validInitial_well_formed_config init hvalid) t

/-- Valid initial configurations retain their initial majority verdict almost
surely after any finite number of nonuniform Markov-chain steps. -/
theorem validInitial_nonuniformTransitionKernel_pow_majorityVerdict_eq
    (init : Config (AgentState L K)) (_hvalid : validInitial init) (t : ℕ) :
    ∀ᵐ c' ∂((nonuniformTransitionKernel L K ^ t) init),
      majorityVerdict c' = majorityVerdict init :=
  nonuniformTransitionKernel_pow_majorityVerdict_eq (L := L) (K := K) init t

/-- Valid initial configurations retain their initial input gap almost surely
after any finite number of nonuniform Markov-chain steps. -/
theorem validInitial_nonuniformTransitionKernel_pow_initialGap_eq
    (init : Config (AgentState L K)) (_hvalid : validInitial init) (t : ℕ) :
    ∀ᵐ c' ∂((nonuniformTransitionKernel L K ^ t) init),
      initialGap c' = initialGap init :=
  nonuniformTransitionKernel_pow_initialGap_eq (L := L) (K := K) init t

end ExactMajority
