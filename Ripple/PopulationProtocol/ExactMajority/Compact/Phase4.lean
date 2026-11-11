/-
# Phase 4 respects the live table

`Phase4Transition` reads only the two biases (`hasBigBias s || hasBigBias t`), which are live
for every role at phase 4, and advances both agents through `advancePhaseWithInit` or leaves
them unchanged.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- The normal form keeps a live bias. -/
lemma phase4_normalize_bias_of_live (a : AgentState L K) (h : liveBias a.phase.val a.role) :
    (normalize a).bias = a.bias := by
  simp [normalize, normalizeAtVal, h]

/-- At phase 4 the transition reads only the biases, live for every role. -/
theorem phase4_normalize (s t : AgentState L K) (hs : s.phase.val = 4) (ht : t.phase.val = 4)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase4Transition L K s t).1 =
        normalize (Phase4Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase4Transition L K s t).2 =
        normalize (Phase4Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase4Transition L K s t).1 ∧ Good (Phase4Transition L K s t).2 := by
  have hbs : (normalize s).bias = s.bias :=
    phase4_normalize_bias_of_live s (by simp [liveBias, hs])
  have hbt : (normalize t).bias = t.bias :=
    phase4_normalize_bias_of_live t (by simp [liveBias, ht])
  have has := advancePhaseWithInit_normalize s hgs
  have hat := advancePhaseWithInit_normalize t hgt
  simp only [Phase4Transition, hbs, hbt]
  split_ifs
  all_goals first
    | exact ⟨has.1, hat.1, has.2, hat.2⟩
    | exact ⟨(normalize_normalize s).symm, (normalize_normalize t).symm, hgs, hgt⟩
    | (exfalso; simp_all)

end Compact

end Ripple.PopulationProtocol.ExactMajority
