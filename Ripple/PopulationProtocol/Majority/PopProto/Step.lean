/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Single-Step Configuration Update

Applies one interaction (initiator state, responder state) to a configuration,
producing the successor configuration.  We define a partial version `step`
that requires the interaction to be feasible (sufficient counts) and a total
wrapper `stepOrSelf` that returns the original configuration when the
interaction is infeasible.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Config
import Ripple.PopulationProtocol.Majority.PopProto.Transition

namespace PopProto

open State

namespace Config

variable {n : ℕ}

/-! ## Effect of a single interaction on counts

Given an interaction between an agent in state `i` (initiator) and an agent
in state `r` (responder), we compute the resulting configuration.  The
transition `delta (i, r) = (i', r')` tells us:
- The initiator keeps state `i' = i` (one-way property)
- The responder moves from `r` to `r'`

So the net effect on counts is: `countOf r` decreases by 1 and
`countOf r'` increases by 1 (when `r ≠ r'`; otherwise no change).
-/

/-- The new responder state after an `(i, r)` interaction. -/
def responderResult (i r : State) : State :=
  (delta (i, r)).2

@[simp]
theorem responderResult_xx : responderResult .x .x = .x := rfl
@[simp]
theorem responderResult_xb : responderResult .x .b = .x := rfl
@[simp]
theorem responderResult_xy : responderResult .x .y = .b := rfl
@[simp]
theorem responderResult_bx : responderResult .b .x = .x := rfl
@[simp]
theorem responderResult_bb : responderResult .b .b = .b := rfl
@[simp]
theorem responderResult_by : responderResult .b .y = .y := rfl
@[simp]
theorem responderResult_yx : responderResult .y .x = .b := rfl
@[simp]
theorem responderResult_yb : responderResult .y .b = .y := rfl
@[simp]
theorem responderResult_yy : responderResult .y .y = .y := rfl

/-- Apply one interaction `(i, r)` to a configuration.  Returns `none` when the
    interaction is infeasible (not enough agents in the required states).

    The 9 cases are enumerated explicitly so that `sum_eq` proofs close by `omega`. -/
def step (c : Config n) (i r : State) : Option (Config n) :=
  have hs := c.sum_eq
  match i, r with
  -- (x, x): no change, need x ≥ 2
  | .x, .x => if c.x_count ≥ 2 then some c else none
  -- (x, b): b→x, need x ≥ 1 and b ≥ 1
  | .x, .b => if h : c.x_count ≥ 1 ∧ c.b_count ≥ 1 then
      some ⟨c.x_count + 1, c.b_count - 1, c.y_count, by omega⟩
    else none
  -- (x, y): y→b, need x ≥ 1 and y ≥ 1
  | .x, .y => if h : c.x_count ≥ 1 ∧ c.y_count ≥ 1 then
      some ⟨c.x_count, c.b_count + 1, c.y_count - 1, by omega⟩
    else none
  -- (b, x): no change, need b ≥ 1 and x ≥ 1
  | .b, .x => if c.b_count ≥ 1 ∧ c.x_count ≥ 1 then some c else none
  -- (b, b): no change, need b ≥ 2
  | .b, .b => if c.b_count ≥ 2 then some c else none
  -- (b, y): no change, need b ≥ 1 and y ≥ 1
  | .b, .y => if c.b_count ≥ 1 ∧ c.y_count ≥ 1 then some c else none
  -- (y, x): x→b, need y ≥ 1 and x ≥ 1
  | .y, .x => if h : c.y_count ≥ 1 ∧ c.x_count ≥ 1 then
      some ⟨c.x_count - 1, c.b_count + 1, c.y_count, by omega⟩
    else none
  -- (y, b): b→y, need y ≥ 1 and b ≥ 1
  | .y, .b => if h : c.y_count ≥ 1 ∧ c.b_count ≥ 1 then
      some ⟨c.x_count, c.b_count - 1, c.y_count + 1, by omega⟩
    else none
  -- (y, y): no change, need y ≥ 2
  | .y, .y => if c.y_count ≥ 2 then some c else none

/-- Total wrapper: if the interaction is infeasible, return the original config. -/
def stepOrSelf (c : Config n) (i r : State) : Config n :=
  (c.step i r).getD c

end Config
end PopProto
