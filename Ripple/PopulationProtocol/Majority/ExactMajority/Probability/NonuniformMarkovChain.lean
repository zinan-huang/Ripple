/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Markov Chain for the Nonuniform Exact Majority Protocol

This file specializes the generic scheduler/kernel infrastructure to the
Doty et al. nonuniform exact-majority protocol `NonuniformMajority L K`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain

namespace ExactMajority

open MeasureTheory ProbabilityTheory

variable (L K : ℕ)

/-- One-step distribution for the concrete nonuniform majority protocol, with a
point-mass fallback on populations of size less than two. -/
noncomputable def nonuniformStepDistOrSelf (c : Config (AgentState L K)) :
    PMF (Config (AgentState L K)) :=
  (NonuniformMajority L K).stepDistOrSelf c

/-- Markov transition kernel for the concrete nonuniform majority protocol. -/
noncomputable def nonuniformTransitionKernel :
    ProbabilityTheory.Kernel (Config (AgentState L K)) (Config (AgentState L K)) :=
  (NonuniformMajority L K).transitionKernel

/-- Every support point of the concrete one-step distribution is reachable by
the nonuniform majority protocol. -/
theorem nonuniformStepDistOrSelf_support_reachable
    (c c' : Config (AgentState L K)) :
    c' ∈ (nonuniformStepDistOrSelf L K c).support →
      (NonuniformMajority L K).Reachable c c' := by
  exact Protocol.stepDistOrSelf_support_reachable (NonuniformMajority L K) c c'

/-- Every support point of the concrete one-step distribution preserves
population size. -/
theorem nonuniformStepDistOrSelf_support_card_eq
    (c c' : Config (AgentState L K)) :
    c' ∈ (nonuniformStepDistOrSelf L K c).support → c'.card = c.card := by
  exact Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c'

/-- Every finite stochastic execution of the concrete nonuniform Markov chain
is almost surely a deterministic reachable execution. -/
theorem ae_nonuniformReachable_transitionKernel_pow
    (c : Config (AgentState L K)) (t : ℕ) :
    ∀ᵐ c' ∂((nonuniformTransitionKernel L K ^ t) c),
      (NonuniformMajority L K).Reachable c c' := by
  exact Protocol.ae_reachable_transitionKernel_pow (NonuniformMajority L K) c t

/-- Probability-zero form of
`ae_nonuniformReachable_transitionKernel_pow`. -/
theorem nonuniformTransitionKernel_pow_not_reachable_eq_zero
    (c : Config (AgentState L K)) (t : ℕ) :
    (nonuniformTransitionKernel L K ^ t) c
        {c' : Config (AgentState L K) |
          ¬(NonuniformMajority L K).Reachable c c'} = 0 := by
  exact Protocol.transitionKernel_pow_not_reachable_eq_zero
    (NonuniformMajority L K) c t

/-- Any event disjoint from the concrete nonuniform reachability closure of the
starting configuration has probability zero at every finite Markov time. -/
theorem nonuniformTransitionKernel_pow_eq_zero_of_forall_not_reachable
    (c : Config (AgentState L K)) (t : ℕ)
    (S : Set (Config (AgentState L K)))
    (hS : ∀ c' : Config (AgentState L K), c' ∈ S →
      ¬(NonuniformMajority L K).Reachable c c') :
    (nonuniformTransitionKernel L K ^ t) c S = 0 := by
  exact Protocol.transitionKernel_pow_eq_zero_of_forall_not_reachable
    (NonuniformMajority L K) c t S hS

end ExactMajority
