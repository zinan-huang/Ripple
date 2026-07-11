/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `CardConservation` — population size is a deterministic kernel invariant.

The ExactMajority scheduler updates a chosen pair into a pair, so it never
changes the population size.  Lifting that single-step fact through the generic
support-preservation engine
`Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved`
gives, for free, that the kernel-`t` mass of any size-`≠ n` event started from a
size-`n` configuration is exactly `0`.

This is the deterministic card half consumed by the slot-0 `htail` assembly
(the `allPhaseEq p n = (card = n) ∧ allPhase…` window has its `card = n` conjunct
discharged here, leaving only the genuinely-probabilistic phase/role parts).

Engine: `Probability/MarkovChain.lean`.  All proofs are 0-sorry / axiom-clean.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain

namespace ExactMajority

open MeasureTheory ProbabilityTheory

namespace Protocol

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Card conservation (generic).** From a size-`n` start, the kernel-`t` mass
of the size-`≠ n` event is `0`: population size is preserved on every support
point, so the invariant `card = n` is closed under one step and the generic
support-preservation engine zeroes the complement. -/
theorem transitionKernel_pow_card_ne_eq_zero
    (P : Protocol Λ) (n : ℕ) (c : Config Λ)
    (hc : Multiset.card c = n) (t : ℕ) :
    (P.transitionKernel ^ t) c {c' : Config Λ | Multiset.card c' ≠ n} = 0 :=
  transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    P (fun c' => Multiset.card c' = n)
    (fun c₀ c₁ h hsupp => (stepDistOrSelf_support_card_eq P c₀ c₁ hsupp).trans h)
    c hc t

end Protocol

end ExactMajority
