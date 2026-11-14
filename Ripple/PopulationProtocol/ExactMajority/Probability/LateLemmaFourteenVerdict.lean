import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaFourteenSpreads

/-!
# Lemma 14: identify the propagated sign with the input verdict

The reachable mass ledger supplies a bias with the input's strict sign.
The Phase-9 support invariant puts that sign in an opinion mask, so a
compatible homogeneous Phase-9 state cannot propagate the opposite sign.
-/

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenVerdict

open LateLemmaFourteenSpreads

variable {L K n : ℕ}

/-- Lemma 14's compatible signed Phase-9 state determines the input sign. -/
theorem opinionSpreadPre_input_sign
    (init c : Config (AgentState L K)) (out : Output)
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hpre : OpinionSpreadPre out n c)
    (hsigned : out = .A ∨ out = .B)
    (hgap : initialGap init ≠ 0) :
    (if 0 < initialGap init then Output.A else Output.B) = out := by
  have hall : ∀ a ∈ c, a.phase.val = 9 := fun a ha => (hpre.2.1 a ha).1
  have hsupp := reachable_phase9Support init c hvalid hreach
    (fun a ha => by have := hall a ha; omega)
  rcases hsigned with rfl | rfl
  · by_cases hpos : 0 < initialGap init
    · simp [hpos]
    · have hneg : initialGap init < 0 := by omega
      obtain ⟨a, ha, i, hb⟩ :=
        exists_neg_bias_of_initialGap_neg init c hvalid hreach hall hneg
      have hbit := (hsupp a ha (hall a ha)).1.2 i hb
      have hnone : hasMinusOne a.opinions = false := (hpre.2.1 a ha).2
      simp [hnone] at hbit
  · by_cases hpos : 0 < initialGap init
    · obtain ⟨a, ha, i, hb⟩ :=
        exists_pos_bias_of_initialGap_pos init c hvalid hreach hall hpos
      have hbit := (hsupp a ha (hall a ha)).1.1 i hb
      have hnone : hasPlusOne a.opinions = false := (hpre.2.1 a ha).2
      simp [hnone] at hbit
    · simp [hpos]

/-- The sign selected by Lemma 14 is the original strict majority verdict. -/
theorem opinionSpreadPre_majorityVerdict
    (init c : Config (AgentState L K)) (out : Output)
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hpre : OpinionSpreadPre out n c)
    (hsigned : out = .A ∨ out = .B)
    (hgap : initialGap init ≠ 0) :
    majorityVerdict init = outputTripleOfOutput out := by
  have hout := opinionSpreadPre_input_sign init c out hvalid hreach hpre hsigned hgap
  rw [← hout]
  by_cases hpos : 0 < initialGap init
  · simpa only [if_pos hpos] using majorityVerdict_eq_A_of_initialGap_pos init hpos
  · have hneg : initialGap init < 0 := by omega
    simpa only [if_neg hpos] using majorityVerdict_eq_B_of_initialGap_neg init hneg

end Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenVerdict

