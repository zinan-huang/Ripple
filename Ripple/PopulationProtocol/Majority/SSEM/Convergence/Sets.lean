/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Configuration Sets along the Stabilization Chain

Following Section 5.2.1 of Kanaya et al. (2025), the convergence proof
of P_EM proceeds along a chain of configuration sets:

  Call ⊃ Srank ⊃ Sswap ⊃ Stim ⊃ Sem

where:

  * `Srank` = all agents Settled with bijective ranks;
  * `Sswap` = `Srank` with A-inputs below B-inputs (rank-sorted);
  * `Sout`  = all agents' `.answer` equals the exact-majority opinion;
  * `Stim`  = `Sswap ∩ Sout`;
  * `Sem`   = `Stim` with median agent's `.timer` = 0 (fully silent).

Our existing `IsConsensusConfig` corresponds exactly to `Stim`.

This file defines the sets and proves the basic identifications.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Step
import Mathlib.Data.Fintype.EquivFin

namespace SSEM

variable {n : ℕ}

/-- `Srank` of Kanaya et al.: all agents are Settled with pairwise-distinct
ranks (so the rank function is a bijection `Fin n → Fin n`). -/
structure InSrank (C : Config (AgentState n) Opinion n) : Prop where
  allSettled : ∀ v, (C v).1.role = .Settled
  ranks_inj : Function.Injective (fun v => (C v).1.rank)

/-- `Sswap` of Kanaya et al.: an `Srank` configuration in which inputs are
sorted by rank — A-agents have lower ranks than B-agents. -/
structure InSswap (C : Config (AgentState n) Opinion n) extends InSrank C : Prop where
  input_rank : ∀ v, ((C v).2 = Opinion.A ↔ ((C v).1.rank.val < nAOf C))

/-- `Sout` of Kanaya et al.: every agent's `.answer` equals the exact
majority opinion. -/
def InSout (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ v, (C v).1.answer = majorityAnswer C

/-- `Stim = Sswap ∩ Sout` of Kanaya et al.: rank-sorted, all-answers-correct. -/
structure InStim (C : Config (AgentState n) Opinion n) extends InSswap C : Prop where
  allAnswerCorrect : InSout C

/-- `Stim` is the same predicate as `IsConsensusConfig`. -/
theorem InStim_iff_IsConsensusConfig (C : Config (AgentState n) Opinion n) :
    InStim C ↔ IsConsensusConfig C where
  mp := fun h => ⟨h.allSettled, h.ranks_inj, h.input_rank, h.allAnswerCorrect⟩
  mpr := fun h => ⟨⟨⟨h.allSettled, h.ranks_inj⟩, h.input_rank⟩, h.allAnswerCorrect⟩

/-- `Sem` of Kanaya et al.: a `Stim` configuration in which the median
agent's `.timer` is `0`. (At an `Sem` configuration, no agent ever
changes state — fully silent.) -/
structure InSem (C : Config (AgentState n) Opinion n) extends InStim C : Prop where
  median_timer_zero : ∀ v, (C v).1.rank.val + 1 = ceilHalf n → (C v).1.timer = 0

/-- A consensus configuration's median agent has rank exactly `ceilHalf n − 1`. -/
theorem IsConsensusConfig.exists_median {C : Config (AgentState n) Opinion n}
    (hC : IsConsensusConfig C) (hn : n > 0) :
    ∃ v, (C v).1.rank.val + 1 = ceilHalf n := by
  have hsurj : Function.Surjective (fun v => (C v).1.rank) :=
    Finite.injective_iff_surjective.mp hC.ranks_inj
  have : ceilHalf n - 1 < n := by
    have := ceilHalf_le n; have := ceilHalf_pos hn; omega
  obtain ⟨v, hv⟩ := hsurj ⟨ceilHalf n - 1, this⟩
  refine ⟨v, ?_⟩
  have hpos : ceilHalf n > 0 := ceilHalf_pos hn
  have h_rank_val : (C v).1.rank.val = ceilHalf n - 1 :=
    congrArg Fin.val hv
  omega

/-- The same existence claim for an `InSrank` configuration (which has the
same `ranks_inj` field). -/
theorem InSrank.exists_median {C : Config (AgentState n) Opinion n}
    (hC : InSrank C) (hn : n > 0) :
    ∃ v, (C v).1.rank.val + 1 = ceilHalf n := by
  have hsurj : Function.Surjective (fun v => (C v).1.rank) :=
    Finite.injective_iff_surjective.mp hC.ranks_inj
  have : ceilHalf n - 1 < n := by
    have := ceilHalf_le n; have := ceilHalf_pos hn; omega
  obtain ⟨v, hv⟩ := hsurj ⟨ceilHalf n - 1, this⟩
  refine ⟨v, ?_⟩
  have hpos : ceilHalf n > 0 := ceilHalf_pos hn
  have h_rank_val : (C v).1.rank.val = ceilHalf n - 1 :=
    congrArg Fin.val hv
  omega

end SSEM
