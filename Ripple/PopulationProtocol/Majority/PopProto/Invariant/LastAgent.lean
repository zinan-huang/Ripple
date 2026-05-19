/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Last Agent Invariant

If a population has at least one agent with opinion X and no Y agents,
then X cannot be eliminated — it persists or spreads.  Symmetrically for Y.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Step

namespace PopProto

open State

namespace Config

variable {n : ℕ}

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
/-- If `x_count ≥ 1` and `y_count = 0`, then after any successful step,
    `x_count ≥ 1` and `y_count = 0` still hold. -/
theorem x_survives_without_y (c : Config n) (i r : State) (c' : Config n)
    (h : c.step i r = some c')
    (hx : c.x_count ≥ 1) (hy : c.y_count = 0) :
    c'.x_count ≥ 1 ∧ c'.y_count = 0 := by
  unfold step at h
  cases i <;> cases r <;> simp_all <;>
    (try omega) <;>
    (first | (obtain ⟨_, rfl⟩ := h) | (obtain ⟨⟨_, _⟩, rfl⟩ := h)) <;>
    simp <;> omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
/-- Symmetric version: Y agents survive when there are no X agents. -/
theorem y_survives_without_x (c : Config n) (i r : State) (c' : Config n)
    (h : c.step i r = some c')
    (hy : c.y_count ≥ 1) (hx : c.x_count = 0) :
    c'.y_count ≥ 1 ∧ c'.x_count = 0 := by
  unfold step at h
  cases i <;> cases r <;> simp_all <;>
    (try omega) <;>
    (first | (obtain ⟨_, rfl⟩ := h) | (obtain ⟨⟨_, _⟩, rfl⟩ := h)) <;>
    simp <;> omega

end Config
end PopProto
