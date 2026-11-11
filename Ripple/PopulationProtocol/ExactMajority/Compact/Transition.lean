/-
# The flat transition respects the live table

Assembly of the per-phase congruences: `Transition_normalize` says that on good agents the
normal form of `Transition s t` depends only on the normal forms of `s` and `t`, and that the
invariant `Good` is preserved. This is the `enc_δ` / `good_δ` of the state simulation in
`Compact/State.lean`.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Inits
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase0
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase1
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase2
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase3
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase4
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase5
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase6
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase7
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase8
import Ripple.PopulationProtocol.ExactMajority.Compact.Phase10

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- The per-phase dispatch of `Transition`, as a function of the phase. -/
def dispatch (L K : ℕ) (p : Fin 11) (s t : AgentState L K) : AgentState L K × AgentState L K :=
  match p with
  | ⟨0, _⟩ => Phase0Transition L K s t
  | ⟨1, _⟩ => Phase1Transition L K s t
  | ⟨2, _⟩ => Phase2Transition L K s t
  | ⟨3, _⟩ => Phase3Transition L K s t
  | ⟨4, _⟩ => Phase4Transition L K s t
  | ⟨5, _⟩ => Phase5Transition L K s t
  | ⟨6, _⟩ => Phase6Transition L K s t
  | ⟨7, _⟩ => Phase7Transition L K s t
  | ⟨8, _⟩ => Phase8Transition L K s t
  | ⟨9, _⟩ => Phase9Transition L K s t
  | ⟨10, _⟩ => Phase10Transition L K s t
  | _ => (s, t)

/-- `Transition` is the phase epidemic, the dispatch, then the phase-10 entry. -/
theorem Transition_eq (s t : AgentState L K) :
    Transition L K s t =
      (finishPhase10Entry L K (phaseEpidemicUpdate L K s t).1
        (dispatch L K (phaseEpidemicUpdate L K s t).1.phase
          (phaseEpidemicUpdate L K s t).1 (phaseEpidemicUpdate L K s t).2).1,
       finishPhase10Entry L K (phaseEpidemicUpdate L K s t).2
        (dispatch L K (phaseEpidemicUpdate L K s t).1.phase
          (phaseEpidemicUpdate L K s t).1 (phaseEpidemicUpdate L K s t).2).2) := rfl

/-- The dispatch respects the live table when both agents are in the same phase. -/
theorem dispatch_normalize (s t : AgentState L K) (hph : s.phase = t.phase)
    (hgs : Good s) (hgt : Good t) :
    normalize (dispatch L K s.phase s t).1 =
        normalize (dispatch L K s.phase (normalize s) (normalize t)).1 ∧
      normalize (dispatch L K s.phase s t).2 =
        normalize (dispatch L K s.phase (normalize s) (normalize t)).2 ∧
      Good (dispatch L K s.phase s t).1 ∧ Good (dispatch L K s.phase s t).2 := by
  have ht : t.phase.val = s.phase.val := by rw [hph]
  rcases hs : s.phase with ⟨k, hk⟩
  rw [hs] at ht
  simp only at ht
  interval_cases k <;> simp only [dispatch]
  · exact phase0_normalize s t (by rw [hs]) ht hgs hgt
  · exact phase1_normalize s t (by rw [hs]) ht hgs hgt
  · exact phase2_normalize 2 (Or.inl rfl) s t (by rw [hs]) ht hgs hgt
  · exact phase3_normalize s t (by rw [hs]) ht hgs hgt
  · exact phase4_normalize s t (by rw [hs]) ht hgs hgt
  · exact phase5_normalize s t (by rw [hs]) ht hgs hgt
  · exact phase6_normalize s t (by rw [hs]) ht hgs hgt
  · exact phase7_normalize s t (by rw [hs]) ht hgs hgt
  · exact phase8_normalize s t (by rw [hs]) ht hgs hgt
  · exact phase2_normalize 9 (Or.inr rfl) s t (by rw [hs]) ht hgs hgt
  · exact phase10_normalize s t (by rw [hs]) ht hgs hgt

/-- `finishPhase10Entry` respects the live table. -/
theorem finishPhase10Entry_normalize (b b' o o' : AgentState L K) (hb : b.phase = b'.phase)
    (ho : normalize o = normalize o') (hgo : Good o) :
    normalize (finishPhase10Entry L K b o) = normalize (finishPhase10Entry L K b' o') ∧
      Good (finishPhase10Entry L K b o) := by
  have hoph : o'.phase = o.phase := by
    have := congrArg AgentState.phase ho; simpa using this.symm
  unfold finishPhase10Entry canonicalPhase10Entry
  rw [hoph, ← hb]
  split_ifs
  · exact ⟨enterPhase10_normalize _ _ ho, good_enterPhase10 _⟩
  · exact ⟨ho, hgo⟩

/-- **The flat transition respects the live table.** On good agents, the normal form of the
result depends only on the normal forms of the inputs, and goodness is preserved. -/
theorem Transition_normalize (s t : AgentState L K) (hgs : Good s) (hgt : Good t) :
    normalize (Transition L K s t).1 =
        normalize (Transition L K (normalize s) (normalize t)).1 ∧
      normalize (Transition L K s t).2 =
        normalize (Transition L K (normalize s) (normalize t)).2 ∧
      Good (Transition L K s t).1 ∧ Good (Transition L K s t).2 := by
  obtain ⟨h1, h2, hg1, hg2, hph⟩ := phaseEpidemicUpdate_normalize s t hgs hgt
  obtain ⟨_, _, hg1', hg2', hph'⟩ :=
    phaseEpidemicUpdate_normalize (normalize s) (normalize t) (good_normalize s)
      (good_normalize t)
  rw [Transition_eq, Transition_eq]
  generalize hE : phaseEpidemicUpdate L K s t = E at *
  generalize hE' : phaseEpidemicUpdate L K (normalize s) (normalize t) = E' at *
  obtain ⟨s', t'⟩ := E
  obtain ⟨s'', t''⟩ := E'
  simp only at h1 h2 hg1 hg2 hph hg1' hg2' hph' ⊢
  have hs'' : s''.phase = s'.phase := by
    have := congrArg AgentState.phase h1; simpa using this.symm
  rw [hs'']
  obtain ⟨d1, d2, dg1, dg2⟩ := dispatch_normalize s' t' hph hg1 hg2
  obtain ⟨d1', d2', dg1', dg2'⟩ := dispatch_normalize s'' t'' hph' hg1' hg2'
  rw [← h1, ← h2] at d1' d2'
  rw [hs''] at d1' d2' dg1' dg2'
  have e1 : normalize (dispatch L K s'.phase s' t').1 =
      normalize (dispatch L K s'.phase s'' t'').1 := d1.trans d1'.symm
  have e2 : normalize (dispatch L K s'.phase s' t').2 =
      normalize (dispatch L K s'.phase s'' t'').2 := d2.trans d2'.symm
  obtain ⟨f1, fg1⟩ := finishPhase10Entry_normalize s' s'' _ _ hs''.symm e1 dg1
  obtain ⟨f2, fg2⟩ := finishPhase10Entry_normalize t' t'' _ _
    (by rw [← hph, ← hph', hs'']) e2 dg2
  exact ⟨f1, f2, fg1, fg2⟩

end Compact

end Ripple.PopulationProtocol.ExactMajority
