/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Axiom Check

This file uses `#print axioms` to verify that the master theorems depend
only on the standard Lean / Mathlib classical axioms (`propext`,
`Classical.choice`, `Quot.sound`).  Run via `lake env lean` or by
inspecting the editor's info pane.

Run:
```
lake env lean SSExactMajority/AxiomCheck.lean
```
-/

import Ripple.PopulationProtocol.Majority.SSEM

namespace SSEM

-- Theorem 1
#print axioms impossibility_without_n

-- Theorem 2
#print axioms space_lower_bound

-- Theorem 4 — fully discharged (modulo Burman + invariants)
#print axioms P_EM_solves_SSEM_fully_discharged_modulo_burman

-- Theorem 4 — original modulo Burman
#print axioms P_EM_solves_SSEM_full_modulo_burman

-- Composite (four-way + median-wrong)
#print axioms P_EM_solves_SSEM_via_four_way_and_median_wrong_decision

-- Single-step bedrock (sample)
#print axioms swap_step_decreases_eight_way

-- Concrete protocol — single hypothesis
#print axioms P_EM_solves_SSEM_concrete_burman

-- Concrete ranking subprotocol
#print axioms rankDeltaOSSR_settled_distinct_ranks
#print axioms rankDeltaStable_satisfies_fix

end SSEM
