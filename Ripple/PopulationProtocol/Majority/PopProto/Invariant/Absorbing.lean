/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Absorbing States

Configurations where all agents agree are absorbing: once the population
reaches all-X, all-Y, or all-B, it stays there forever.

Additionally, the all-B configuration is unreachable from any configuration
that has at least one opinionated agent, because `hasOpinion` is preserved
by every step.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Probability.StepDist

namespace PopProto

open State

namespace Config

variable {n : ℕ}

set_option linter.unnecessarySeqFocus false in
/-- If all agents hold state X, every interaction is a no-op. -/
theorem allX_step_eq (c : Config n) (hx : c.allX) (i r : State) :
    c.stepOrSelf i r = c := by
  unfold allX at hx
  obtain ⟨hxn, hb0, hy0⟩ := hx
  unfold stepOrSelf step
  have hs := c.sum_eq
  cases i <;> cases r <;> simp_all <;> split_ifs <;> simp_all

set_option linter.unnecessarySeqFocus false in
/-- If all agents hold state Y, every interaction is a no-op. -/
theorem allY_step_eq (c : Config n) (hy : c.allY) (i r : State) :
    c.stepOrSelf i r = c := by
  unfold allY at hy
  obtain ⟨hx0, hb0, hyn⟩ := hy
  unfold stepOrSelf step
  have hs := c.sum_eq
  cases i <;> cases r <;> simp_all <;> split_ifs <;> simp_all

set_option linter.unnecessarySeqFocus false in
/-- If all agents are blank, every interaction is a no-op. -/
theorem allB_step_eq (c : Config n) (hb : c.allB) (i r : State) :
    c.stepOrSelf i r = c := by
  unfold allB at hb
  obtain ⟨hx0, hbn, hy0⟩ := hb
  unfold stepOrSelf step
  have hs := c.sum_eq
  cases i <;> cases r <;> simp_all <;> split_ifs <;> simp_all

private theorem interactionPMF_sum_eq_one (c : Config n) (hn : n ≥ 2) :
    (Finset.univ.sum fun p : State × State => c.interactionPMF hn p) = 1 := by
  simpa using (c.interactionPMF hn).tsum_coe

/-- At all-X consensus, the one-step random transition distribution is a
point mass at the same configuration. -/
theorem allX_stepDist_eq_pure (c : Config n) (hn : n ≥ 2) (hx : c.allX) :
    c.stepDist hn = PMF.pure c := by
  ext c'
  by_cases h : c' = c
  · simp [stepDist, allX_step_eq c hx, h, interactionPMF_sum_eq_one c hn]
  · simp [stepDist, allX_step_eq c hx, h]

/-- At all-Y consensus, the one-step random transition distribution is a
point mass at the same configuration. -/
theorem allY_stepDist_eq_pure (c : Config n) (hn : n ≥ 2) (hy : c.allY) :
    c.stepDist hn = PMF.pure c := by
  ext c'
  by_cases h : c' = c
  · simp [stepDist, allY_step_eq c hy, h, interactionPMF_sum_eq_one c hn]
  · simp [stepDist, allY_step_eq c hy, h]

/-- At all-blank consensus, the one-step random transition distribution is a
point mass at the same configuration. -/
theorem allB_stepDist_eq_pure (c : Config n) (hn : n ≥ 2) (hb : c.allB) :
    c.stepDist hn = PMF.pure c := by
  ext c'
  by_cases h : c' = c
  · simp [stepDist, allB_step_eq c hb, h, interactionPMF_sum_eq_one c hn]
  · simp [stepDist, allB_step_eq c hb, h]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- If we have at least one opinionated agent, this is preserved by any step.
    This is the key lemma: the "last non-blank agent" cannot be eliminated
    because when it interacts with a blank, it converts the blank. -/
theorem hasOpinion_preserved (c : Config n) (i r : State) (c' : Config n)
    (h : c.step i r = some c') (hop : c.hasOpinion) :
    c'.hasOpinion := by
  unfold hasOpinion opinionated at *
  simp only [step] at h
  cases i <;> cases r <;> simp_all <;>
    (try omega) <;>
    (first | (obtain ⟨_, rfl⟩ := h) | (obtain ⟨⟨_, _⟩, rfl⟩ := h)) <;>
    simp <;> omega

/-- If the initial configuration has at least one opinionated agent,
    then all-B is unreachable in one step. -/
theorem not_allB_of_opinionated_step (c : Config n) (i r : State) (c' : Config n)
    (h : c.step i r = some c') (hop : c.hasOpinion) :
    ¬c'.allB := by
  intro hb
  have hop' := hasOpinion_preserved c i r c' h hop
  unfold allB at hb
  unfold hasOpinion opinionated at hop'
  omega

end Config
end PopProto
