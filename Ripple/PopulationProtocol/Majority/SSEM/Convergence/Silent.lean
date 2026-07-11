/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Silent / Output-Stable Configurations of P_EM

A *consensus configuration* of P_EM is one in which:

  1. every agent has `role = .Settled`;
  2. the `rank` field is a bijection `Fin n → Fin n`;
  3. inputs are sorted by rank — agents with input `.A` occupy ranks
     `0, …, n_A − 1`, agents with input `.B` occupy ranks `n_A, …, n − 1`;
  4. every agent's `answer` already matches the correct majority output.

This file builds the structural foundation: the `IsConsensusConfig`
predicate, the `majorityAnswer` function, and the immediate consequences
that an arbitrary consensus configuration outputs the correct majority
opinion uniformly.  The deeper claim — that `transitionPEM` preserves
this configuration through every step (and hence consensus is
output-stable) — is broken into the more granular pair-level case
analysis carried out in `Convergence.AnswerPreservation` (next
milestone).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Protocol.Correctness
import Ripple.PopulationProtocol.Majority.SSEM.Defs.Execution
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

namespace SSEM

variable {n : ℕ}

/-- The number of agents with input `.A`. -/
def nAOf (C : Config (AgentState n) Opinion n) : ℕ :=
  (C.agentsWithInput Opinion.A).card

/-- The number of agents with input `.B`. -/
def nBOf (C : Config (AgentState n) Opinion n) : ℕ :=
  (C.agentsWithInput Opinion.B).card

/-- The "correct" majority answer for a configuration, computed from input
counts: `.outA` if A's strictly outnumber B's, `.outB` if B's outnumber
A's, `.outT` (tie) otherwise. -/
def majorityAnswer (C : Config (AgentState n) Opinion n) : Answer :=
  if nAOf C > nBOf C then .outA
  else if nBOf C > nAOf C then .outB
  else .outT

/-- Inputs partition agents by `.A` / `.B`. -/
theorem nAOf_add_nBOf (C : Config (AgentState n) Opinion n) :
    nAOf C + nBOf C = n := by
  classical
  unfold nAOf nBOf Config.agentsWithInput
  set sA := (Finset.univ : Finset (Fin n)).filter (fun v => C.inputOf v = Opinion.A)
  set sB := (Finset.univ : Finset (Fin n)).filter (fun v => C.inputOf v = Opinion.B)
  have hdisj : Disjoint sA sB := by
    refine Finset.disjoint_filter.mpr ?_
    intro v _ hA hB
    rw [hA] at hB; cases hB
  have hunion : sA ∪ sB = (Finset.univ : Finset (Fin n)) := by
    ext v
    simp only [sA, sB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    cases h : (C v).2 with
    | A => exact Or.inl (by simp [Config.inputOf, h])
    | B => exact Or.inr (by simp [Config.inputOf, h])
  have hcard := Finset.card_union_of_disjoint hdisj
  have huniv : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
  rw [hunion, huniv] at hcard
  omega

/-- A **consensus configuration** of P_EM. -/
structure IsConsensusConfig (C : Config (AgentState n) Opinion n) : Prop where
  /-- Every agent is in the Settled role. -/
  allSettled : ∀ v, (C v).1.role = .Settled
  /-- The `rank` field is injective; together with `Fintype` this gives a
  bijection `Fin n → Fin n`. -/
  ranks_inj : Function.Injective (fun v => (C v).1.rank)
  /-- Inputs are sorted by rank: `(C v).2 = .A` iff `rank v < n_A`. -/
  input_rank : ∀ v, ((C v).2 = Opinion.A ↔ ((C v).1.rank.val < nAOf C))
  /-- Every agent's `answer` field equals the correct majority answer. -/
  allAnswerCorrect : ∀ v, (C v).1.answer = majorityAnswer C

/-- Hypothesis on the (parameterized) ranking subprotocol: applied to two
already-Settled agents, it returns them unchanged. Any well-formed ranking
subprotocol (in particular Burman et al.'s Optimal-Silent-SSR after
stabilization) satisfies this. -/
def RankDeltaSettledFix
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) :
    Prop :=
  ∀ s t : AgentState n, s.role = .Settled → t.role = .Settled →
    s.rank ≠ t.rank → rankDelta (s, t) = (s, t)

/-! ### Helper lemmas about input distribution under sorted-rank consensus -/

namespace IsConsensusConfig

variable {C : Config (AgentState n) Opinion n}

/-- Under a consensus, an agent has input `.B` iff its rank is at least
`n_A`. -/
theorem inputB_iff_rank_ge (h : IsConsensusConfig C) (v : Fin n) :
    (C v).2 = Opinion.B ↔ nAOf C ≤ (C v).1.rank.val := by
  constructor
  · intro hB
    by_contra hlt
    push_neg at hlt
    have hA : (C v).2 = Opinion.A := (h.input_rank v).mpr hlt
    rw [hA] at hB; cases hB
  · intro hge
    have hnotA : (C v).2 ≠ Opinion.A := by
      intro hA
      have := (h.input_rank v).mp hA
      omega
    cases hcase : (C v).2 with
    | A => exact (hnotA hcase).elim
    | B => rfl

/-- Under a consensus, an A-input agent's rank is `< n_A`. -/
theorem rank_lt_of_inputA (h : IsConsensusConfig C) {v : Fin n}
    (hA : (C v).2 = Opinion.A) : (C v).1.rank.val < nAOf C :=
  (h.input_rank v).mp hA

/-- Under a consensus, a B-input agent's rank is `≥ n_A`. -/
theorem rank_ge_of_inputB (h : IsConsensusConfig C) {v : Fin n}
    (hB : (C v).2 = Opinion.B) : nAOf C ≤ (C v).1.rank.val :=
  (inputB_iff_rank_ge h v).mp hB

/-- The swap condition fails under a consensus: an agent with input B never
has a strictly lower rank than an agent with input A. -/
theorem swap_does_not_fire (h : IsConsensusConfig C) {u v : Fin n}
    (hxu : (C u).2 = Opinion.B) (hxv : (C v).2 = Opinion.A) :
    ¬ (C u).1.rank < (C v).1.rank := by
  intro hlt
  have h1 : nAOf C ≤ (C u).1.rank.val := h.rank_ge_of_inputB hxu
  have h2 : (C v).1.rank.val < nAOf C := h.rank_lt_of_inputA hxv
  have hltVal : (C u).1.rank.val < (C v).1.rank.val := hlt
  omega

end IsConsensusConfig

/-! ### Immediate consequences for output

The output function depends only on the `.answer` field, so once every
agent has the correct answer, every agent has the correct output.
-/

/-- At any consensus configuration, the protocol's output function applied
to every agent yields `(majorityAnswer C).toOutput`. -/
theorem IsConsensusConfig.allOutput {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C : Config (AgentState n) Opinion n} (h : IsConsensusConfig C) :
    C.allOutput (protocolPEM n trank Rmax rankDelta) (majorityAnswer C).toOutput :=
  allOutput_of_all_answer h.allAnswerCorrect

/-- The output of every agent at a consensus configuration is determined
by the majority of inputs. -/
theorem IsConsensusConfig.exactMajoritySafe {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C : Config (AgentState n) Opinion n} (h : IsConsensusConfig C) :
    ExactMajoritySafe' (protocolPEM n trank Rmax rankDelta) C
      Opinion.A Opinion.B Output.A Output.B Output.T := by
  -- Unfold the definition: it dispatches on which input count is bigger.
  unfold ExactMajoritySafe'
  -- The hypothesis fields directly translate, since
  --   majorityAnswer C = .outA  iff  nA > nB,
  --   majorityAnswer C = .outB  iff  nB > nA,
  --   majorityAnswer C = .outT  otherwise.
  have hsum := nAOf_add_nBOf C
  have hAll := h.allOutput (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  -- Translate `allOutput (majorityAnswer C).toOutput` to the dispatched form.
  change
    (if (C.agentsWithInput Opinion.A).card > (C.agentsWithInput Opinion.B).card then
      C.allOutput (protocolPEM n trank Rmax rankDelta) Output.A
    else if (C.agentsWithInput Opinion.A).card < (C.agentsWithInput Opinion.B).card then
      C.allOutput (protocolPEM n trank Rmax rankDelta) Output.B
    else C.allOutput (protocolPEM n trank Rmax rankDelta) Output.T)
  by_cases hAB : nAOf C > nBOf C
  · simp only [show (C.agentsWithInput Opinion.A).card > (C.agentsWithInput Opinion.B).card
        from hAB, if_true]
    -- majorityAnswer C = .outA, so its toOutput is .A.
    have : majorityAnswer C = Answer.outA := by unfold majorityAnswer; simp [hAB]
    rw [this] at hAll; exact hAll
  · by_cases hBA : nBOf C > nAOf C
    · have hne : ¬ ((C.agentsWithInput Opinion.A).card >
                    (C.agentsWithInput Opinion.B).card) := hAB
      have hlt : (C.agentsWithInput Opinion.A).card <
                 (C.agentsWithInput Opinion.B).card := hBA
      simp only [hne, hlt, if_false, if_true]
      have : majorityAnswer C = Answer.outB := by
        unfold majorityAnswer; simp [hAB, hBA]
      rw [this] at hAll; exact hAll
    · -- Tie.
      have hne1 : ¬ ((C.agentsWithInput Opinion.A).card >
                    (C.agentsWithInput Opinion.B).card) := hAB
      have hne2 : ¬ ((C.agentsWithInput Opinion.A).card <
                    (C.agentsWithInput Opinion.B).card) := hBA
      simp only [hne1, hne2, if_false]
      have : majorityAnswer C = Answer.outT := by
        unfold majorityAnswer; simp [hAB, hBA]
      rw [this] at hAll; exact hAll

end SSEM
