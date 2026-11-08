/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reachable Phase-4 stable ties are correct stable endpoints

`Phase4Convergence.StableTie4` records the local terminal data produced by
work slot 4: every agent is in Phase 4, reports `T`, and has no big dyadic
bias.  Correctness additionally requires that the initial majority verdict is
`T`.  This file derives that fact for reachable configurations in the paper's
size regime and connects the slot-4 postcondition to `StableDone`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase4Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.ExpectedTimeCore
import Ripple.PopulationProtocol.ExactMajority.Analysis.DeterministicChain

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase4StableEndpoint

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The slot-4 no-big-bias predicate excludes the deterministic Phase-4
advance trigger. -/
private theorem not_phase4HasBigBias_of_noBigBias
    (a : AgentState L K)
    (hno : Phase4Convergence.noBigBias (L := L) (K := K) a) :
    ¬ phase4HasBigBias (L := L) (K := K) a := by
  intro hbig
  rcases hbig with ⟨sgn, i, hbias, hi⟩
  unfold Phase4Convergence.noBigBias at hno
  rw [hbias] at hno
  exact hno hi

/-- A stable-tie slot-4 postcondition is locally stable in the deterministic
Phase-4 sense. -/
theorem locallyStable_of_stableTie4
    (c : Config (AgentState L K))
    (htie : Phase4Convergence.StableTie4 (L := L) (K := K) c) :
    phase4LocallyStable (L := L) (K := K) c := by
  constructor
  · intro a ha
    exact (htie a ha).1
  · intro a ha b hb _happ hbig
    rcases hbig with hbig | hbig
    · exact not_phase4HasBigBias_of_noBigBias a (htie a ha).2.2 hbig
    · exact not_phase4HasBigBias_of_noBigBias b (htie b hb).2.2 hbig

/-- A reachable carded stable tie has zero initial input gap.  The equality
case `n = 2^L` is discharged by the parity argument already contained in
`phase4LocallyStable_initialGap_zero`. -/
theorem stableTie4Card_initialGap_zero
    {n : ℕ} (hn : 2 ≤ n) (hcap : n ≤ 2 ^ L)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (htie : Phase4Convergence.StableTie4Card
      (L := L) (K := K) n c) :
    initialGap init = 0 := by
  have hstable : phase4LocallyStable (L := L) (K := K) c :=
    locallyStable_of_stableTie4 c htie.2
  apply phase4LocallyStable_initialGap_zero
    (L := L) (K := K) init c hinit hreach
      (fun a ha => (htie.2 a ha).1)
  · rw [htie.1]
    exact hn
  · exact hstable
  · rw [htie.1]
    exact hcap

/-- A reachable carded stable tie is the concrete Phase-4 tie endpoint for
the original initial configuration. -/
theorem stableTie4Card_to_phase4TieEndpoint
    {n : ℕ} (hn : 2 ≤ n) (hcap : n ≤ 2 ^ L)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (htie : Phase4Convergence.StableTie4Card
      (L := L) (K := K) n c) :
    phase4TieEndpoint (L := L) (K := K) init c := by
  have hgap : initialGap init = 0 :=
    stableTie4Card_initialGap_zero hn hcap init c hinit hreach htie
  have hmajor : majorityVerdict init = outputTripleOfOutput .T :=
    majorityVerdict_eq_T_of_initialGap_zero
      (L := L) (K := K) init hgap
  apply phase4TieEndpoint_of_data (L := L) (K := K) init c hmajor
  intro a ha
  have haTie := htie.2 a ha
  refine ⟨haTie.1, haTie.2.1, ?_⟩
  intro sgn i hbias
  have hno := haTie.2.2
  unfold Phase4Convergence.noBigBias at hno
  rw [hbias] at hno
  exact hno

/-- Carded Phase-4 tie outcomes belong to the absorbing stable target. -/
theorem stableTie4Card_mem_stableDone
    {n : ℕ} (hn : 2 ≤ n) (hcap : n ≤ 2 ^ L)
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (htie : Phase4Convergence.StableTie4Card
      (L := L) (K := K) n c) :
    c ∈ StableDone L K init := by
  exact Or.inr (Or.inl (stableTie4Card_to_phase4TieEndpoint
    hn hcap init c hinit hreach htie))

/-- Reachability-scoped bridge for outcome-aware assembly.  Work slot 4 uses
the card-free `StableTie4`; reachability plus the initial card equation restores
the carded postcondition needed by the correctness proof. -/
theorem reachable_stableTie4_mem_stableDone
    {n : ℕ} (hn : 2 ≤ n) (hcap : n ≤ 2 ^ L)
    (init c : Config (AgentState L K))
    (hinit : validInitial init) (hcard : init.card = n)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (htie : Phase4Convergence.StableTie4 (L := L) (K := K) c) :
    c ∈ StableDone L K init := by
  have hcardReach : c.card = init.card :=
    Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach
  apply stableTie4Card_mem_stableDone hn hcap init c hinit hreach
  exact ⟨hcardReach.trans hcard, htie⟩

/-- On a reachable slot-4 postcondition, failure to be already done eliminates
the stable-tie disjunct.  This is the exact active-branch projection consumed by
the outcome-aware work-to-seam bridge. -/
theorem advFinished_of_post_not_stableDone
    {n : ℕ} (hn : 2 ≤ n) (hcap : n ≤ 2 ^ L)
    (init c : Config (AgentState L K))
    (hinit : validInitial init) (hcard : init.card = n)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hpost : Phase4Convergence.StableTie4 (L := L) (K := K) c ∨
      Phase4Convergence.advFinished (L := L) (K := K) n c)
    (hnot : c ∉ StableDone L K init) :
    Phase4Convergence.advFinished (L := L) (K := K) n c := by
  rcases hpost with htie | hadv
  · exact False.elim (hnot (reachable_stableTie4_mem_stableDone
      hn hcap init c hinit hcard hreach htie))
  · exact hadv

#print axioms locallyStable_of_stableTie4
#print axioms stableTie4Card_initialGap_zero
#print axioms stableTie4Card_to_phase4TieEndpoint
#print axioms stableTie4Card_mem_stableDone
#print axioms reachable_stableTie4_mem_stableDone
#print axioms advFinished_of_post_not_stableDone

end Phase4StableEndpoint
end Ripple.PopulationProtocol.ExactMajority
