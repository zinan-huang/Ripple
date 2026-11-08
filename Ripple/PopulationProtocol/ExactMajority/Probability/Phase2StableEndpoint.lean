/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-2 consensus outcomes are stable endpoints

This file closes the deterministic endpoint side of all three non-advancing
Phase-2 outcomes.  In particular, the neutral-opinion outcome is kept as a
first-class `T` branch rather than being folded into either signed branch.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2ConsensusBranch
import Ripple.PopulationProtocol.ExactMajority.Probability.ExpectedTimeCore

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase2StableEndpoint

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

private theorem minus_union_false
    (x y : Fin 8)
    (hx : hasMinusOne x = false) (hy : hasMinusOne y = false) :
    hasMinusOne (opinionsUnion x y) = false := by
  revert hx hy
  revert x y
  decide

private theorem plus_union_false
    (x y : Fin 8)
    (hx : hasPlusOne x = false) (hy : hasPlusOne y = false) :
    hasPlusOne (opinionsUnion x y) = false := by
  revert hx hy
  revert x y
  decide

/-- Vanishing wrong-output count means every agent carries the branch output. -/
theorem output_eq_of_post
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hpost : Phase2OutputCleanup.Phase2Post
      (L := L) (K := K) out n c) :
    ∀ a ∈ c, a.output = out := by
  intro a ha
  have hzero :
      Multiset.countP (fun x : AgentState L K => x.output ≠ out) c = 0 := by
    simpa [Phase2OutputCleanup.wrongOutputCount2] using hpost.2
  have hnot : ¬a.output ≠ out :=
    (Multiset.countP_eq_zero.1 hzero) a ha
  exact not_not.1 hnot

/-- Each of the `A`, `B`, and `T` cleanup posts is locally absorbing at Phase 2.
The proof uses the missing-sign side of the public support predicate; no
singleton-opinion strengthening is imposed on the signed branches. -/
theorem locallyStable_of_post
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hpost : Phase2OutputCleanup.Phase2Post
      (L := L) (K := K) out n c) :
    phase2LocallyStable (L := L) (K := K) c := by
  cases out with
  | A =>
      constructor
      · intro a ha
        have hs := hpost.1.2 a ha
        exact hs.1
      · intro a b hab hbad
        have ha : a ∈ c := Multiset.mem_of_le hab (by simp)
        have hb : b ∈ c := Multiset.mem_of_le hab (by simp)
        have hsa := hpost.1.2 a ha
        have hsb := hpost.1.2 b hb
        have hminus :
            hasMinusOne (opinionsUnion a.opinions b.opinions) = false :=
          minus_union_false a.opinions b.opinions
            hsa.2.2 hsb.2.2
        rw [hminus] at hbad
        simp at hbad
  | B =>
      constructor
      · intro a ha
        have hs := hpost.1.2 a ha
        exact hs.1
      · intro a b hab hbad
        have ha : a ∈ c := Multiset.mem_of_le hab (by simp)
        have hb : b ∈ c := Multiset.mem_of_le hab (by simp)
        have hsa := hpost.1.2 a ha
        have hsb := hpost.1.2 b hb
        have hplus :
            hasPlusOne (opinionsUnion a.opinions b.opinions) = false :=
          plus_union_false a.opinions b.opinions
            hsa.2.2 hsb.2.2
        rw [hplus] at hbad
        simp at hbad
  | T =>
      constructor
      · intro a ha
        have hs := hpost.1.2 a ha
        exact hs.1
      · intro a b hab hbad
        have ha : a ∈ c := Multiset.mem_of_le hab (by simp)
        have hb : b ∈ c := Multiset.mem_of_le hab (by simp)
        have hsa := hpost.1.2 a ha
        have hsb := hpost.1.2 b hb
        have haminus : hasMinusOne a.opinions = false := by
          simp [hsa.2, phase2OpinionT, hasMinusOne]
        have hbminus : hasMinusOne b.opinions = false := by
          simp [hsb.2, phase2OpinionT, hasMinusOne]
        have hminus :
            hasMinusOne (opinionsUnion a.opinions b.opinions) = false :=
          minus_union_false a.opinions b.opinions
            haminus hbminus
        rw [hminus] at hbad
        simp at hbad

/-- A completed Phase-2 branch is a concrete Phase-2 consensus endpoint once
the branch verdict is identified with the initial majority verdict. -/
theorem post_to_consensusEndpoint
    (out : Output) (n : ℕ)
    (init c : Config (AgentState L K))
    (hmajor : majorityVerdict init = outputTripleOfOutput out)
    (hpost : Phase2OutputCleanup.Phase2Post
      (L := L) (K := K) out n c) :
    phase2ConsensusEndpoint (L := L) (K := K) init c := by
  have hstable := locallyStable_of_post
    (L := L) (K := K) out n c hpost
  have hout := output_eq_of_post (L := L) (K := K) out n c hpost
  cases out with
  | A =>
      apply phase2ConsensusEndpoint_of_A
        (L := L) (K := K) init c hmajor hstable
      intro a ha
      have hs := hpost.1.2 a ha
      exact ⟨hout a ha, hs.2.1, hs.2.2⟩
  | B =>
      apply phase2ConsensusEndpoint_of_B
        (L := L) (K := K) init c hmajor hstable
      intro a ha
      have hs := hpost.1.2 a ha
      exact ⟨hout a ha, hs.2.1, hs.2.2⟩
  | T =>
      apply phase2ConsensusEndpoint_of_T
        (L := L) (K := K) init c hmajor hstable
      intro a ha
      have hs := hpost.1.2 a ha
      have hminus : hasMinusOne a.opinions = false := by
        simp [hs.2, phase2OpinionT, hasMinusOne]
      have hplus : hasPlusOne a.opinions = false := by
        simp [hs.2, phase2OpinionT, hasPlusOne]
      exact ⟨hout a ha, hminus, hplus⟩

/-- Membership bridge used by the absorbing-outcome assembly.  It covers all
three consensus values, including the neutral `DoneT` outcome. -/
theorem post_mem_stableDone
    (out : Output) (n : ℕ)
    (init c : Config (AgentState L K))
    (hmajor : majorityVerdict init = outputTripleOfOutput out)
    (hpost : Phase2OutputCleanup.Phase2Post
      (L := L) (K := K) out n c) :
    c ∈ StableDone L K init := by
  exact Or.inl (post_to_consensusEndpoint
    (L := L) (K := K) out n init c hmajor hpost)

#print axioms output_eq_of_post
#print axioms locallyStable_of_post
#print axioms post_to_consensusEndpoint
#print axioms post_mem_stableDone

end Phase2StableEndpoint
end Ripple.PopulationProtocol.ExactMajority
