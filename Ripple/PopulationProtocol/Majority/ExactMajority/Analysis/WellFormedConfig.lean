/-
Lift the per-agent `well_formed_agent` predicate (defined in Invariants.lean)
to configurations (multisets of agent states), and prove the key preservation
lemma: a single step of the protocol preserves well-formedness.

Author: DeepSeek (scaffold), Codex2 (Transition_preserves_well_formed).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants
import Ripple.PopulationProtocol.Majority.ExactMajority.Basic.PopulationProtocol

open Multiset

namespace ExactMajority

variable {L K : ℕ}

/-- A configuration is well-formed iff every agent in it is well-formed. -/
def well_formed_config (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, well_formed_agent a

/-- A valid initial configuration is well-formed (trivial from the per-agent
lemma proved by Codex2 in Invariants.lean). -/
theorem validInitial_well_formed_config (c : Config (AgentState L K))
    (hvalid : validInitial c) : well_formed_config c := by
  intro a ha
  exact validInitial_well_formed_agent c hvalid a ha

/-- Well-formedness is preserved by one protocol step. -/
theorem well_formed_config_preserved_by_step (c c' : Config (AgentState L K))
    (h_c : well_formed_config c) (h_step : (NonuniformMajority L K).StepRel c c') :
    well_formed_config c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  have htrans := Transition_preserves_well_formed (L := L) (K := K) r₁ r₂
    (h_c r₁ hr₁_mem) (h_c r₂ hr₂_mem)
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

/-- Well-formedness is preserved along any reachable sequence of protocol steps. -/
theorem well_formed_config_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : well_formed_config c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    well_formed_config c' := by
  induction h_reach with
  | refl =>
      exact h_c
  | tail _ hstep ih =>
      exact well_formed_config_preserved_by_step (L := L) (K := K) _ _ ih hstep

/-- Every configuration reachable from a valid initial configuration is well-formed. -/
theorem validInitial_well_formed_config_of_reachable
    (init c : Config (AgentState L K))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    well_formed_config c :=
  well_formed_config_preserved_by_reachable
    (L := L) (K := K) init c (validInitial_well_formed_config init hvalid) hreach

end ExactMajority
