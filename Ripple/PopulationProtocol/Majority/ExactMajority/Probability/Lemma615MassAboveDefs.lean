/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lemma615MassAboveDefs

Low-level readout definitions for Doty's Lemma 6.15.

This file deliberately contains only definitions, so Core/slot-3 scaffolding can
refer to the `muAbove` and `phase3OFuelCount` surfaces without importing the
probabilistic Lemma 6.15 discharge file and its higher-level drain dependencies.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6Convergence

namespace ExactMajority
namespace Lemma615MassAbove

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## The weighted upper-tail mass -/

/-- The dyadic upper-tail mass contribution scaled by `2^l`.

For a biased Main at dyadic index `i < l`, the unscaled mass is `2^{-i}`.
Multiplying the whole upper-tail mass by `2^l` gives the natural weight
`2^(l-i)`. -/
def biasMassAboveScaledW (l : ℕ) (b : Bias L) : ℕ :=
  match b with
  | .zero => 0
  | .dyadic _ i => if i.val < l then 2 ^ (l - i.val) else 0

/-- Scaled dyadic upper-tail mass contribution of one agent.  Only Main agents
count in Doty's phase-3 exponent profile. -/
def agentMassAboveScaledW (l : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = Role.main then biasMassAboveScaledW (L := L) l a.bias else 0

/-- The dyadic upper-tail mass `mu(> -l)`, scaled by `2^l`. -/
def massAboveScaled (l : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.map (fun a => agentMassAboveScaledW (L := L) (K := K) l a)).sum

/-- The real dyadic upper-tail mass `mu(> -l)`.

The definition is `2^{-l}` times the scaled natural mass.  This keeps the
integer combinatorics inspectable while exposing the paper's real-valued mass
surface. -/
noncomputable def muAbove (l : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (massAboveScaled (L := L) (K := K) l c : ℝ) * (2 : ℝ) ^ (-(l : ℤ))

/-! ## Phase-3 split arithmetic -/

/-- The phase-3 `O_l` split-fuel pool: unbiased Main agents whose hour is at
least `l`, hence above every exponent index `j < l`. -/
def phase3OFuel (l : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter
    (fun a => a.role = Role.main ∧ a.bias = Bias.zero ∧ l ≤ a.hour.val)

/-- The number of phase-3 `O_l` split-fuel agents in a configuration. -/
def phase3OFuelCount (l : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (phase3OFuel (L := L) (K := K) l).sum c.count

end Lemma615MassAbove

end ExactMajority
