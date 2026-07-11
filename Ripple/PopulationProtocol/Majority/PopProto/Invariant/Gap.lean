/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gap Invariant

The gap `u = x_count - y_count` (as an integer) changes by at most 1
in absolute value per interaction.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Step

namespace PopProto

open State

namespace Config

variable {n : ℕ}

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The gap of a configuration produced by `step` differs from the original
    gap by at most 1. -/
theorem gap_step_bounded (c : Config n) (i r : State) (c' : Config n)
    (h : c.step i r = some c') :
    Int.natAbs (c'.gap - c.gap) ≤ 1 := by
  unfold gap step at *
  cases i <;> cases r <;> simp_all <;>
    (try omega) <;>
    (first | (obtain ⟨_, rfl⟩ := h) | (obtain ⟨⟨_, _⟩, rfl⟩ := h)) <;>
    simp <;> omega

/-- The total one-step wrapper changes the input gap by at most one.  In
infeasible scheduler cases it returns the original configuration. -/
theorem gap_stepOrSelf_bounded (c : Config n) (i r : State) :
    Int.natAbs ((c.stepOrSelf i r).gap - c.gap) ≤ 1 := by
  unfold stepOrSelf
  cases h : c.step i r with
  | none =>
      simp
  | some c' =>
      simpa [h] using gap_step_bounded c i r c' h

end Config
end PopProto
