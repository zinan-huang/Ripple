/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-1 exact-reset seam obstruction

The Phase-1 Init resets a newly-entering Clock, but the full dispatcher then
runs the Phase-1 transition in the same mixed-phase interaction.  The selected
Clock is therefore decremented immediately.  Hence an exact Phase-1 window does
not imply that every Clock is still at the reset value.
-/

import Ripple.PopulationProtocol.ExactMajority.Protocol.Transition

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1ExactResetObstruction

/-- A phase-0 Clock about to be infected by the phase epidemic. -/
def lateClock : AgentState 1 0 :=
  { input := .A
    output := .A
    phase := ⟨0, by decide⟩
    role := .clock
    assigned := true
    bias := .zero
    smallBias := ⟨3, by decide⟩
    hour := ⟨0, by decide⟩
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨0, by decide⟩
    counter := ⟨0, by decide⟩ }

/-- A non-Clock phase-1 carrier of the epidemic. -/
def infectedMain : AgentState 1 0 :=
  { input := .A
    output := .A
    phase := ⟨1, by decide⟩
    role := .main
    assigned := true
    bias := .zero
    smallBias := ⟨3, by decide⟩
    hour := ⟨0, by decide⟩
    minute := ⟨0, by decide⟩
    full := false
    opinions := ⟨0, by decide⟩
    counter := ⟨0, by decide⟩ }

/-- The newly-entered Clock is first reset to `100 = 50(1+1)` and then
decremented to `99` by the Phase-1 clock subroutine in the same interaction. -/
theorem mixed_entry_transition_behavior :
    Transition 1 0 lateClock infectedMain =
      ({lateClock with
          phase := ⟨1, by decide⟩
          counter := ⟨99, by decide⟩},
       infectedMain) := by
  rfl

/-- Both outputs are now exactly in Phase 1. -/
theorem mixed_entry_outputs_phase_one :
    (Transition 1 0 lateClock infectedMain).1.phase.val = 1 ∧
      (Transition 1 0 lateClock infectedMain).2.phase.val = 1 := by
  rw [mixed_entry_transition_behavior]
  decide

/-- Nevertheless the output Clock is not at the literal Phase-1 reset. -/
theorem mixed_entry_clock_not_exact_reset :
    (Transition 1 0 lateClock infectedMain).1.role = Role.clock ∧
      (Transition 1 0 lateClock infectedMain).1.counter.val ≠ 50 * (1 + 1) := by
  rw [mixed_entry_transition_behavior]
  decide

/-- Concrete two-agent exact-window counterexample to the blanket seam bridge
“all phase 1 implies all Clocks are at reset”. -/
theorem exact_phase_one_does_not_imply_clock_reset :
    ∃ c : Config (AgentState 1 0),
      (∀ a ∈ c, a.phase.val = 1) ∧
      ¬ (∀ a ∈ c, a.role = Role.clock → a.counter.val = 50 * (1 + 1)) := by
  let out := Transition 1 0 lateClock infectedMain
  refine ⟨out.1 ::ₘ out.2 ::ₘ 0, ?_, ?_⟩
  · intro a ha
    simp at ha
    rcases ha with rfl | rfl
    · exact mixed_entry_outputs_phase_one.1
    · exact mixed_entry_outputs_phase_one.2
  · intro hreset
    exact mixed_entry_clock_not_exact_reset.2
      (hreset out.1 (by simp) mixed_entry_clock_not_exact_reset.1)

#print axioms mixed_entry_transition_behavior
#print axioms mixed_entry_outputs_phase_one
#print axioms mixed_entry_clock_not_exact_reset
#print axioms exact_phase_one_does_not_imply_clock_reset

end Phase1ExactResetObstruction
end Ripple.PopulationProtocol.ExactMajority
