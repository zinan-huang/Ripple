/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Self-Stabilizing Exact Majority — Problem Definition

Definition 1 from Kanaya et al. (2025):
A protocol P = (Q, X, Y, δ, π_out) is a self-stabilizing exact majority protocol
if X = {A, B}, Y = {A, B, T}, and for any initial configuration C₀:
  1. For any safe C_safe reachable from C₀: ∀ v, π_out(C_safe(v)) = majority opinion
  2. Any execution from C₀ reaches safe configurations with probability 1.

The exact majority opinion is:
  - A  if |V_a| > |V_b|
  - B  if |V_a| < |V_b|
  - T  if |V_a| = |V_b|
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.Execution

namespace SSEM

/-- The exact majority opinion given counts of A and B agents. -/
def majorityOpinion (countA countB : ℕ) : Output :=
  if countA > countB then .A
  else if countA < countB then .B
  else .T

/-- A protocol is "uniform" (does not use knowledge of n) if the same
    transition function δ works for all population sizes.
    Formally, P_m and P_n share the same δ and π_out. -/
def UniformProtocol (Q X Y : Type*) := Protocol Q X Y

end SSEM
