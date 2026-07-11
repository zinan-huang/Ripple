/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Configuration

A configuration C : V → Q × X assigns each agent a state and input.
The input is immutable throughout execution.

Following Section 2.1: C changes to C' via interaction (u, v) ∈ E if
  (C'(u), C'(v)) = δ(C(u), C(v))  and  ∀ w ≠ u, v : C'(w) = C(w).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.Protocol
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

namespace SSEM

variable {Q X Y : Type*}

/-- A configuration assigns each agent a (state, input) pair. -/
def Config (Q X : Type*) (n : ℕ) := Fin n → Q × X

namespace Config

variable {n : ℕ}

/-- The state of agent v. -/
def stateOf (C : Config Q X n) (v : Fin n) : Q := (C v).1

/-- The input of agent v. -/
def inputOf (C : Config Q X n) (v : Fin n) : X := (C v).2

/-- The output of agent v under protocol P. -/
def outputOf (P : Protocol Q X Y) (C : Config Q X n) (v : Fin n) : Y :=
  P.π_out (C v)

/-- Apply one interaction: agents u (initiator) and v (responder) interact.
    Self-interactions (u = v) are no-ops, matching the standard population
    protocol model where E = {(u,v) ∈ V×V | u ≠ v}. -/
def step (P : Protocol Q X Y) (C : Config Q X n) (u v : Fin n) : Config Q X n :=
  if u = v then C
  else
    let result := P.δ (C u, C v)
    fun w =>
      if w = u then (result.1, (C u).2)
      else if w = v then (result.2, (C v).2)
      else C w

/-- All agents output the same value y. -/
def allOutput (P : Protocol Q X Y) (C : Config Q X n) (y : Y) : Prop :=
  ∀ v : Fin n, C.outputOf P v = y

/-- A configuration is silent if no interaction changes any agent's state. -/
def isSilent [DecidableEq Q] [DecidableEq X] (P : Protocol Q X Y) (C : Config Q X n) : Prop :=
  ∀ u v : Fin n, C.step P u v = C

/-- The set of agents with a given input. -/
def agentsWithInput [DecidableEq X] [Fintype (Fin n)]
    (C : Config Q X n) (x : X) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.inputOf v = x)

end Config

end SSEM
