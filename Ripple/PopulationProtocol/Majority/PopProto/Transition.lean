/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transition Function

The deterministic output function δ(s₁, s₂) = (s₁', s₂') for the
3-state approximate majority protocol from Angluin–Aspnes–Eisenstat (2008).

Key rule: the *initiator* (first component) never changes; only the
*responder* (second component) may be converted to the initiator's opinion.
A blank responder always adopts the initiator's opinion.
An opinionated responder only changes when the initiator has a different
non-blank opinion — the responder becomes blank.
-/

import Ripple.PopulationProtocol.Majority.PopProto.State

namespace PopProto

open State

/-- The transition function δ : State × State → State × State.
    `delta (initiator, responder)` returns `(initiator', responder')`.
    The initiator never changes; the responder may be converted. -/
def delta : State × State → State × State
  | (.x, .x) => (.x, .x)
  | (.x, .b) => (.x, .x)
  | (.x, .y) => (.x, .b)
  | (.b, .x) => (.b, .x)
  | (.b, .b) => (.b, .b)
  | (.b, .y) => (.b, .y)
  | (.y, .x) => (.y, .b)
  | (.y, .b) => (.y, .y)
  | (.y, .y) => (.y, .y)

/-! ## Properties of the transition function -/

/-- **One-way property**: the initiator is never changed by the transition. -/
@[simp]
theorem delta_fst (p : State × State) : (delta p).1 = p.1 := by
  rcases p with ⟨i, r⟩; cases i <;> cases r <;> rfl

/-- The output of δ is always a fixed point when both components agree
    or the initiator is blank.  In general, applying δ three times
    always equals applying it twice (δ is "eventually idempotent"). -/
theorem delta_eventually_idempotent (p : State × State) :
    delta (delta (delta p)) = delta (delta p) := by
  rcases p with ⟨i, r⟩; cases i <;> cases r <;> rfl

/-- When both agents share the same state, nothing changes. -/
theorem delta_same (s : State) : delta (s, s) = (s, s) := by
  cases s <;> rfl

/-- A blank initiator never changes the responder. -/
theorem delta_blank_init (r : State) : delta (.b, r) = (.b, r) := by
  cases r <;> rfl

end PopProto
