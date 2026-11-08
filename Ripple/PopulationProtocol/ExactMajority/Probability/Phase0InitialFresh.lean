/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Phase0InitialFresh` — the strengthened Phase-0 initializer (C0 fix).

Companion to `RoleSplitPhase0Counterexample.lean` (the verified `¬`-theorem showing the *weak*
`Phase0Initial` is too weak — it omits `assigned = false`, so the unconditional role-split bound is
provably false).  This file lands the **fix** the user chose ("strengthen"): a strengthened
initializer that adds the per-agent freshness flag, the bridge proving the **real** protocol start
(`validInitial`) satisfies it, and the payoff — the previously hand-*carried* `NoAssignedMcrConfig`
side-condition is now **derivable** from the start hypothesis.

Three load-bearing facts:

* `Phase0InitialFresh n c := Phase0Initial n c ∧ ∀ a ∈ c, a.assigned = false`, with the forgetful
  projection `Phase0InitialFresh.toPhase0Initial` (so every one of the ~40 lemmas consuming the weak
  `Phase0Initial` still fires unchanged from the strengthened start — no re-proof of the frozen
  interface, exactly as `TopSplitInward.lean:638` intended).
* `phase0InitialFresh_of_validInitial` — `validInitial c₀ ∧ c₀.card = n ⟹ Phase0InitialFresh n c₀`.
  This is the load-bearing soundness fact: the genuine Doty start (MainTheorem `validInitial`, which
  pins `assigned = false`) satisfies the strengthened initializer, so the corrected unconditional
  C0 bound is TRUE at the real start.  Extends the existing lossy bridge
  `FaithfulDeterministicFacts.phase0Initial_of_validInitial` (which discarded freshness — the documented
  defect) into a freshness-preserving one.
* `noAssignedMcrConfig_of_phase0InitialFresh` — the **payoff**: `NoAssignedMcrConfig` (carried as an
  explicit hypothesis throughout `TopSplitInward` / `KilledTailConsumers` *because* it does not follow
  from the weak `Phase0Initial`) is now a one-line consequence of the strengthened start.  This is the
  concrete demonstration that the strengthening does its job.

No existing file edited; purely additive; no sorry/admit/axiom/native_decide.
Reference: `AUDIT_HEADLINE_THEOREMS.md` ⚠️ FORMAL-STATEMENT BUG section.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.FaithfulDeterministicFacts
import Ripple.PopulationProtocol.ExactMajority.Probability.TopSplitInward

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RoleSplitConcentration

variable {L K : ℕ}

/-- The **strengthened** Phase-0 initializer: the weak `Phase0Initial` (population size `n`, every
agent at phase `0`, role `mcr`) PLUS the per-agent freshness flag `assigned = false` that the
one-sided absorption Rules 2/3 (`Transition.lean`) require to clear a lone remaining `mcr`.  The weak
initializer omits this conjunct, which is exactly why the unconditional role-split tail bound is
refutable over it (`RoleSplitPhase0Counterexample.poisonedCfg3_never_good`). -/
def Phase0InitialFresh (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase0Initial (L := L) (K := K) n c ∧ ∀ a ∈ c, a.assigned = false

/-- The strengthened initializer forgets to the weak one, so every lemma stated over the frozen
`Phase0Initial` interface fires unchanged from a `Phase0InitialFresh` start. -/
theorem Phase0InitialFresh.toPhase0Initial {n : ℕ} {c : Config (AgentState L K)}
    (h : Phase0InitialFresh (L := L) (K := K) n c) :
    Phase0Initial (L := L) (K := K) n c := h.1

/-- The freshness conjunct, extracted. -/
theorem Phase0InitialFresh.assigned_false {n : ℕ} {c : Config (AgentState L K)}
    (h : Phase0InitialFresh (L := L) (K := K) n c) :
    ∀ a ∈ c, a.assigned = false := h.2

/-- **The fixed bridge (D5, freshness-preserving).**  From the genuine Doty start `validInitial c₀`
(which pins `phase = 0`, `role = mcr`, AND `assigned = false`) plus the population-size carry
`c₀.card = n`, the *strengthened* initializer `Phase0InitialFresh n c₀` holds.  This replaces the
lossy `FaithfulDeterministicFacts.phase0Initial_of_validInitial`, which discarded the `assigned = false`
fact — the documented C0 defect. -/
theorem phase0InitialFresh_of_validInitial (n : ℕ) (c₀ : Config (AgentState L K))
    (hvalid : validInitial c₀) (hcard : Multiset.card c₀ = n) :
    Phase0InitialFresh (L := L) (K := K) n c₀ := by
  refine ⟨FaithfulDeterministicFacts.phase0Initial_of_validInitial n c₀ hvalid hcard, ?_⟩
  intro a ha
  obtain ⟨_, _, hassigned, _, _, _⟩ := hvalid a ha
  exact hassigned

/-- **The payoff.**  `NoAssignedMcrConfig c₀` — carried as an explicit hypothesis throughout
`TopSplitInward` / `KilledTailConsumers` precisely because it is *not* derivable from the weak
`Phase0Initial` (`TopSplitInward.lean:633`) — is a one-line consequence of the strengthened start:
every agent has `assigned = false`, so none is an assigned `mcr`. -/
theorem noAssignedMcrConfig_of_phase0InitialFresh {n : ℕ} {c₀ : Config (AgentState L K)}
    (h : Phase0InitialFresh (L := L) (K := K) n c₀) :
    NoAssignedMcrConfig (L := L) (K := K) c₀ := by
  intro a ha
  rintro ⟨-, hassigned⟩
  rw [h.2 a ha] at hassigned
  simp at hassigned

end RoleSplitConcentration

end Ripple.PopulationProtocol.ExactMajority
