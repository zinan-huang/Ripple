/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-1 ready/post obstruction

The current slot-1 ready gate requires a positive `+3` extreme floor, while
the survival postcondition requires the two-sided extreme count to be zero.
Since every `+3` extreme is counted by that potential, the postcondition is
empty.  This file records the contradiction against both the ready-gate
constructor and the concrete work wrapper.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseWorkFamily
import Ripple.PopulationProtocol.ExactMajority.Probability.SeedStepAndSignThreading

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1ReadyPostObstruction

variable {L K : ℕ}

/-- A positive `+3` floor cannot coexist with a zero saturated-extreme
potential. -/
theorem ready_and_extreme_zero_false
    (n P1 : ℕ) (c : Config (AgentState L K))
    (hready : Phase1ReadySurvival.Phase1DrainReady
      (L := L) (K := K) n P1 c)
    (hzero : Phase1Convergence.extremeU c = 0) : False := by
  have hpos := SeedStepAndSignThreading.extremeU_pos_of_extremePos_sum
    (L := L) (K := K) c hready.hext
  omega

/-- The literal postcondition of the current concrete slot-1 work wrapper is
uninhabited. -/
theorem phase1Work_of_inputs_post_empty
    {n : ℕ} (A : PhaseWorkFamily.WorkFamilyData (L := L) (K := K) n)
    (c : Config (AgentState L K))
    (hpost : (PhaseWorkFamily.phase1Work_of_familyData
      (L := L) (K := K) A).Post c) : False := by
  change
    Phase1ReadySurvival.Phase1DrainReady
        (L := L) (K := K) n A.P1 c ∧
      Phase1Convergence.extremeU c = 0 at hpost
  exact ready_and_extreme_zero_false n A.P1 c hpost.1 hpost.2

#print axioms ready_and_extreme_zero_false
#print axioms phase1Work_of_inputs_post_empty

end Phase1ReadyPostObstruction
end Ripple.PopulationProtocol.ExactMajority
