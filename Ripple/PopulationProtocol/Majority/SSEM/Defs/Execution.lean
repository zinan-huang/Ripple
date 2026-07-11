/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Execution and Schedulers

A deterministic scheduler γ picks an ordered pair of agents at each step.
An execution applies γ to the configuration step by step.

Key definition: isOutputStable = "safe" in the paper (outputs never change
in any execution from this config).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.Config
import Mathlib.Data.Finset.Card

namespace SSEM

variable {Q X Y : Type*} {n : ℕ}

/-- A deterministic scheduler picks an ordered pair of agents at each step. -/
def DetScheduler (n : ℕ) := ℕ → Fin n × Fin n

/-- Execute protocol P from C₀ under scheduler γ for t steps. -/
def execution (P : Protocol Q X Y) (C₀ : Config Q X n)
    (γ : DetScheduler n) : ℕ → Config Q X n
  | 0 => C₀
  | t + 1 => (execution P C₀ γ t).step P (γ t).1 (γ t).2

/-- A configuration is output-stable ("safe" in the paper):
    for any execution from C, all agents' outputs are unchanged. -/
def Config.isOutputStable (P : Protocol Q X Y) (C : Config Q X n) : Prop :=
  ∀ (γ : DetScheduler n) (t : ℕ) (w : Fin n),
    C.outputOf P w = (execution P C γ t).outputOf P w

/-- The correct majority output given counts. -/
def ExactMajoritySafe' [DecidableEq X] (P : Protocol Q X Y)
    (C : Config Q X n) (inA inB : X) (outA outB outT : Y) : Prop :=
  let Va := C.agentsWithInput inA
  let Vb := C.agentsWithInput inB
  if Va.card > Vb.card then C.allOutput P outA
  else if Va.card < Vb.card then C.allOutput P outB
  else C.allOutput P outT

/-- Protocol P solves self-stabilizing exact majority on n agents:
    from any initial config, some execution reaches an output-stable config
    with the correct majority output. -/
def SolvesSSEM [DecidableEq Q] [DecidableEq Opinion]
    (P : Protocol Q Opinion Output) (n : ℕ) : Prop :=
  ∀ C₀ : Config Q Opinion n,
    ∃ (γ : DetScheduler n) (t : ℕ),
      let C := execution P C₀ γ t
      C.isOutputStable P ∧
      ExactMajoritySafe' P C Opinion.A Opinion.B Output.A Output.B Output.T

end SSEM
