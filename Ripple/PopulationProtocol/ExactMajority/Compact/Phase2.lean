/-
# Phases 2 and 9 respect the live table

`Phase2Transition` (also `Phase9Transition`) reads only `opinions`, writes `opinions` and
`output`, and advances both agents through `advancePhaseWithInit`. Nothing is live for any
role at phases 2 and 9, and the advance is covered by `advancePhaseWithInit_normalize`; the
statement in fact holds at every phase.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- `normalize` does not see the `opinions` field. -/
lemma normalize_set_opinions (a : AgentState L K) (u : Fin 8) :
    normalize { a with opinions := u } = { normalize a with opinions := u } := rfl

/-- `normalize` does not see the `output` and `opinions` fields. -/
lemma normalize_set_output_opinions (a : AgentState L K) (o : Output) (u : Fin 8) :
    normalize { a with output := o, opinions := u } =
      { normalize a with output := o, opinions := u } := rfl

lemma good_set_opinions (a : AgentState L K) (u : Fin 8) :
    Good { a with opinions := u } ↔ Good a := Iff.rfl

lemma good_set_output_opinions (a : AgentState L K) (o : Output) (u : Fin 8) :
    Good { a with output := o, opinions := u } ↔ Good a := Iff.rfl

/-- The advancing rule of phase 2: both signs present. -/
lemma phase2_advance (a : AgentState L K) (u : Fin 8) (hg : Good a) :
    normalize (advancePhaseWithInit L K { a with opinions := u }) =
        normalize (advancePhaseWithInit L K { normalize a with opinions := u }) ∧
      Good (advancePhaseWithInit L K { a with opinions := u }) := by
  first
    | exact advancePhaseWithInit_normalize { a with opinions := u } hg
    | simpa only [normalize_set_opinions] using
        advancePhaseWithInit_normalize { a with opinions := u } ((good_set_opinions a u).mpr hg)

/-- The consensus rules of phase 2: the output is written. -/
lemma phase2_consensus (a : AgentState L K) (o : Output) (u : Fin 8) (hg : Good a) :
    normalize { a with output := o, opinions := u } =
        normalize { normalize a with output := o, opinions := u } ∧
      Good { a with output := o, opinions := u } := by
  refine ⟨?_, (good_set_output_opinions a o u).mpr hg⟩
  exact congrArg (fun x : AgentState L K => { x with output := o, opinions := u })
    (normalize_normalize a).symm

/-- The remaining rule of phase 2: only the opinion set is updated. -/
lemma phase2_keep (a : AgentState L K) (u : Fin 8) (hg : Good a) :
    normalize { a with opinions := u } = normalize { normalize a with opinions := u } ∧
      Good { a with opinions := u } := by
  refine ⟨?_, (good_set_opinions a u).mpr hg⟩
  exact congrArg (fun x : AgentState L K => { x with opinions := u })
    (normalize_normalize a).symm

/-- Phases 2 and 9 respect the live table (nothing is live) and preserve the invariant. -/
theorem phase2_normalize (k : ℕ) (hk : k = 2 ∨ k = 9) (s t : AgentState L K)
    (hs : s.phase.val = k) (ht : t.phase.val = k) (hgs : Good s) (hgt : Good t) :
    normalize (Phase2Transition L K s t).1 =
        normalize (Phase2Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase2Transition L K s t).2 =
        normalize (Phase2Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase2Transition L K s t).1 ∧ Good (Phase2Transition L K s t).2 := by
  simp only [Phase2Transition, normalize_opinions]
  split_ifs
  all_goals first
    | exact ⟨(phase2_advance s _ hgs).1, (phase2_advance t _ hgt).1,
        (phase2_advance s _ hgs).2, (phase2_advance t _ hgt).2⟩
    | exact ⟨(phase2_consensus s _ _ hgs).1, (phase2_consensus t _ _ hgt).1,
        (phase2_consensus s _ _ hgs).2, (phase2_consensus t _ _ hgt).2⟩
    | exact ⟨(phase2_keep s _ hgs).1, (phase2_keep t _ hgt).1,
        (phase2_keep s _ hgs).2, (phase2_keep t _ hgt).2⟩

end Compact

end Ripple.PopulationProtocol.ExactMajority
