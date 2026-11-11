/-
# Phase 1 respects the live table

At phase 1 the only live `Θ(log n)` field is a Clock's `counter` (table in `Live.lean`).
`Phase1Transition` averages the `smallBias` of two Mains (an `O(1)` field, always kept by
`normalize`) and runs `clockCounterStep`, which is `stdCounterSubroutine` on a Clock and the
identity otherwise. The congruence therefore reduces to `stdCounterSubroutine_normalize`.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- `normalize` does not read `smallBias`. -/
lemma normalize_set_smallBias (a : AgentState L K) (x : Fin 7) :
    normalize { a with smallBias := x } = { normalize a with smallBias := x } := by
  cases a; rfl

/-- `Phase1Transition` with the destructuring `let`s resolved. -/
lemma Phase1Transition_eq (s t : AgentState L K) :
    Phase1Transition L K s t =
      if s.role = .main ∧ t.role = .main then
        (clockCounterStep L K { s with smallBias := (avgFin7 s.smallBias t.smallBias).1 },
          clockCounterStep L K { t with smallBias := (avgFin7 s.smallBias t.smallBias).2 })
      else (clockCounterStep L K s, clockCounterStep L K t) := by
  unfold Phase1Transition
  split_ifs <;> first | rfl | simp [avgFin7]

/-- The timed-phase counter step respects the live table in every phase where a Clock's
counter is live, and preserves `Good`. -/
lemma clockCounterStep_normalize (a : AgentState L K)
    (hp : a.phase.val = 0 ∨ a.phase.val = 1 ∨ a.phase.val = 5 ∨ a.phase.val = 6 ∨
      a.phase.val = 7 ∨ a.phase.val = 8)
    (hg : Good a) :
    normalize (clockCounterStep L K a) = normalize (clockCounterStep L K (normalize a)) ∧
      Good (clockCounterStep L K a) := by
  unfold clockCounterStep
  rw [normalize_role]
  split_ifs with hc
  · have hlive : liveCounter a.phase.val a.role (a.minute.val = K * (L + 1)) := by
      rcases hp with h | h | h | h | h | h <;> simp [liveCounter, hc, h]
    exact stdCounterSubroutine_normalize a hc hg hlive
  · exact ⟨(normalize_normalize a).symm, hg⟩

/-- `clockCounterStep` after a `smallBias` write, in the normalized form used by phase 1. -/
lemma clockCounterStep_set_smallBias_normalize (a : AgentState L K) (x : Fin 7)
    (hp : a.phase.val = 1) :
    normalize (clockCounterStep L K { a with smallBias := x }) =
        normalize (clockCounterStep L K { normalize a with smallBias := x }) ∧
      Good (clockCounterStep L K { a with smallBias := x }) := by
  rw [← normalize_set_smallBias]
  exact clockCounterStep_normalize { a with smallBias := x } (Or.inr (Or.inl hp))
    (good_of_phase_ne_three _ (by show a.phase.val ≠ 3; omega))

/-- Phase 1 reads only the live fields and preserves `Good`. -/
theorem phase1_normalize (s t : AgentState L K) (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hgs : Good s) (hgt : Good t) :
    normalize (Phase1Transition L K s t).1 =
        normalize (Phase1Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Phase1Transition L K s t).2 =
        normalize (Phase1Transition L K (normalize s) (normalize t)).2 ∧
      Good (Phase1Transition L K s t).1 ∧ Good (Phase1Transition L K s t).2 := by
  rw [Phase1Transition_eq, Phase1Transition_eq]
  by_cases hmm : s.role = .main ∧ t.role = .main
  · have hmm' : (normalize s).role = .main ∧ (normalize t).role = .main :=
      ⟨(normalize_role s).trans hmm.1, (normalize_role t).trans hmm.2⟩
    rw [if_pos hmm, if_pos hmm']
    simp only [normalize_smallBias]
    have h₁ := clockCounterStep_set_smallBias_normalize s
      (avgFin7 s.smallBias t.smallBias).1 hs
    have h₂ := clockCounterStep_set_smallBias_normalize t
      (avgFin7 s.smallBias t.smallBias).2 ht
    exact ⟨h₁.1, h₂.1, h₁.2, h₂.2⟩
  · have hmm' : ¬ ((normalize s).role = .main ∧ (normalize t).role = .main) := by
      simpa only [normalize_role] using hmm
    rw [if_neg hmm, if_neg hmm']
    have h₁ := clockCounterStep_normalize s (Or.inr (Or.inl hs)) hgs
    have h₂ := clockCounterStep_normalize t (Or.inr (Or.inl ht)) hgt
    exact ⟨h₁.1, h₂.1, h₁.2, h₂.2⟩

end Compact

end Ripple.PopulationProtocol.ExactMajority
