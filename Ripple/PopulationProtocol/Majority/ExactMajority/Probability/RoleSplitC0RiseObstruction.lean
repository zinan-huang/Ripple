
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

# RoleSplitC0RiseObstruction — why strict-rise q for mainCount cannot be sharp

The `GatedCountRiseFact` abstraction for the `mainCount` upper tail asks for
a bound on the event `{c' | mainCount c < mainCount c'}`.  At a fresh all-MCR
Phase-0 start this event has mass `1`, because every scheduled interaction is
Rule 1 and creates one Main.  Hence no `q < 1` theorem can hold on any gate that
contains all Phase0Initial starts.

No sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitC0MicroFacts
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0InitialFresh

namespace ExactMajority
namespace RoleSplitFloorDischarge

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

open RoleSplitConcentration
open FloorPrefix

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/--
If a gate contains a Phase-0 initial configuration at which `mainCount` rises
with one-step mass `1`, then any gated `mainCount` strict-rise fact forces
`1 ≤ ofReal q`.

This is the formal shape of the C0 obstruction.  The concrete all-MCR fresh start
supplies `hmass = 1`.
-/
theorem mainCount_strictRise_q_obstruction
    (Gate : Config (AgentState L K) → Prop)
    (q : ℝ)
    (R : GatedCountRiseFact (L := L) (K := K)
      Gate (mainCount (L := L) (K := K)) q)
    {c₀ : Config (AgentState L K)}
    (hGate : Gate c₀)
    (hmass :
      ((NonuniformMajority L K).transitionKernel c₀)
        {c' | mainCount (L := L) (K := K) c₀
            < mainCount (L := L) (K := K) c'} = 1) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
  have h := R.hrise c₀ hGate
  rw [hmass] at h
  simpa using h

/--
If additionally `ofReal q < 1`, the gated strict-rise fact is impossible.
-/
theorem not_mainCount_strictRise_fact_of_mass_one_of_q_lt_one
    (Gate : Config (AgentState L K) → Prop)
    (q : ℝ)
    {c₀ : Config (AgentState L K)}
    (hGate : Gate c₀)
    (hmass :
      ((NonuniformMajority L K).transitionKernel c₀)
        {c' | mainCount (L := L) (K := K) c₀
            < mainCount (L := L) (K := K) c'} = 1)
    (hq_lt_one : ENNReal.ofReal q < 1) :
    ¬ GatedCountRiseFact (L := L) (K := K)
      Gate (mainCount (L := L) (K := K)) q := by
  intro R
  have hle :=
    mainCount_strictRise_q_obstruction
      (L := L) (K := K) Gate q R hGate hmass
  exact not_lt_of_ge hle hq_lt_one

end RoleSplitFloorDischarge
end ExactMajority
