/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Population Protocol — General Definition

A protocol P = (Q, X, Y, δ, π_out) following Section 2.1 of
Kanaya–Eguchi–Sasada–Ooshita–Inoue (2025).

- Q : agent states
- X : input symbols
- Y : output symbols
- δ : (Q × X) × (Q × X) → Q × Q   (transition, keyed on state+input)
- π_out : Q × X → Y                 (output function)
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

namespace SSEM

/-- A population protocol over finite types. -/
structure Protocol (Q X Y : Type*) where
  δ : (Q × X) × (Q × X) → Q × Q
  π_out : Q × X → Y

/-- An agent is identified by its index in Fin n. -/
abbrev Agent (n : ℕ) := Fin n

/-- The two possible input opinions. -/
inductive Opinion
  | A
  | B
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Opinion where
  elems := {.A, .B}
  complete s := by cases s <;> simp

/-- The three possible output values. -/
inductive Output
  | A
  | B
  | T
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Output where
  elems := {.A, .B, .T}
  complete s := by cases s <;> simp

namespace Opinion

def toString : Opinion → String
  | .A => "A"
  | .B => "B"

instance : ToString Opinion := ⟨toString⟩

end Opinion

namespace Output

def toString : Output → String
  | .A => "A"
  | .B => "B"
  | .T => "T"

instance : ToString Output := ⟨toString⟩

end Output

end SSEM
