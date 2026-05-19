/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# 3-State Approximate Majority Protocol — State Type

The three opinions in the Angluin–Aspnes–Eisenstat approximate majority protocol.
-/

import Mathlib.Data.Fintype.Basic

namespace PopProto

/-- The three states of the approximate majority protocol.
  - `x` : opinion X
  - `b` : blank (undecided)
  - `y` : opinion Y -/
inductive State
  | x
  | b
  | y
  deriving DecidableEq, Repr

namespace State

instance : Fintype State where
  elems := {.x, .b, .y}
  complete s := by cases s <;> simp

instance : Inhabited State := ⟨.b⟩

/-- String representation of states. -/
def toString : State → String
  | .x => "x"
  | .b => "b"
  | .y => "y"

instance : ToString State := ⟨toString⟩

end State
end PopProto
