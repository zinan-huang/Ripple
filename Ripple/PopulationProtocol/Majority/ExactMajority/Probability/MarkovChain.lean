/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Markov Chain Kernel for ExactMajority Protocols

The scheduler in `Probability.Scheduler` needs at least two agents.  The kernel
defined here uses that scheduler on configurations of size at least two and
falls back to a point mass at the current configuration on smaller populations.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Scheduler
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace ExactMajority

namespace Protocol

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- One-step distribution with a degenerate fallback for populations of size
less than two. -/
noncomputable def stepDistOrSelf (P : Protocol Λ) (c : Config Λ) :
    PMF (Config Λ) :=
  if hc : 2 ≤ c.card then
    P.stepDist c hc
  else
    PMF.pure c

/-- The fallback one-step distribution only reaches protocol-reachable
configurations. -/
theorem stepDistOrSelf_support_reachable (P : Protocol Λ) (c c' : Config Λ) :
    c' ∈ (P.stepDistOrSelf c).support → P.Reachable c c' := by
  intro h
  unfold stepDistOrSelf at h
  by_cases hc : 2 ≤ c.card
  · rw [dif_pos hc] at h
    exact stepDist_support_reachable P c hc c' h
  · rw [dif_neg hc] at h
    rw [PMF.mem_support_pure_iff] at h
    subst c'
    exact Relation.ReflTransGen.refl

/-- The fallback one-step distribution preserves population size on every
support point. -/
theorem stepDistOrSelf_support_card_eq (P : Protocol Λ) (c c' : Config Λ) :
    c' ∈ (P.stepDistOrSelf c).support → c'.card = c.card := by
  intro h
  exact reachable_card_eq (stepDistOrSelf_support_reachable P c c' h)

namespace Config

/-- The measurable space on generic configurations is discrete. -/
noncomputable instance instMeasurableSpaceConfig : MeasurableSpace (Config Λ) := ⊤

/-- With the discrete σ-algebra, every set is measurable. -/
instance instDiscreteMeasurableSpaceConfig : DiscreteMeasurableSpace (Config Λ) where
  forall_measurableSet _ := trivial

end Config

/-- Markov transition kernel induced by the ExactMajority random scheduler. -/
noncomputable def transitionKernel (P : Protocol Λ) :
    ProbabilityTheory.Kernel (Config Λ) (Config Λ) where
  toFun c := (P.stepDistOrSelf c).toMeasure
  measurable' := Measurable.of_discrete

end Protocol

end ExactMajority
