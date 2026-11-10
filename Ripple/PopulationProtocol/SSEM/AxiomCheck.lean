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

import Ripple.PopulationProtocol.SSEM
import Ripple.PopulationProtocol.SSEM.Convergence.BurmanConvergenceLinear

namespace Ripple.PopulationProtocol.SSEM

-- Theorem 1
#print axioms impossibility_without_n

-- Theorem 2
#print axioms space_lower_bound

-- Theorem 3
#print axioms time_lower_bound_omega_n_expected
#print axioms time_lower_bound_expected
#print axioms time_lower_bound_tail
#print axioms time_lower_bound_whp
#print axioms twoAgentProtocol_solvesSilentSSEM

-- Definitions: the paper's probability-one forms imply the reachability forms
#print axioms silentProtocol_of_almostSure
#print axioms solvesSSEM_of_kanayaDefinition1

-- Theorem 4 — fully discharged (modulo Burman + invariants)
#print axioms P_EM_solves_SSEM_of_BurmanMacroDecision_and_timer_invariants

-- Theorem 4 — original modulo Burman
#print axioms P_EM_solves_SSEM_of_BurmanMacroDecision_and_step_existence

-- Composite (four-way + median-wrong)
#print axioms P_EM_solves_SSEM_via_four_way_and_median_wrong_decision

-- Single-step bedrock (sample)
#print axioms swap_step_decreases_eight_way

-- Concrete protocol — single hypothesis
#print axioms P_EM_solves_SSEM_of_BurmanConvergence_rankDeltaOSSR

-- Final: fully unconditional (Burman discharged via burmanConvergence_concrete)
#print axioms P_EM_solves_SSEM_linear

-- Theorem 4, qualitative: P_EM is silent SSEM
#print axioms P_EM_silent_linear
#print axioms P_EM_solves_silent_SSEM_linear

-- Theorem 4, state count: P_EM on the finite role-indexed state set
#print axioms card_PEMFinState_le
#print axioms P_EM_fin_solves_silent_SSEM_linear
#print axioms P_EM_fin_card_le
#print axioms P_EM_fin_silent_SSEM_states

-- P_EM with the paper's parameters (trank constant, Rmax = ⌈60 ln n⌉, Emax = e n, Dmax = d n)
#print axioms two_clog_add_two_le_rmaxPaper
#print axioms P_EM_paper_solves_silent_SSEM
#print axioms P_EM_paper_fin_solves_silent_SSEM
#print axioms card_PEMPaperFin_le

-- Burman et al. Lemma 3.2 (propagation), potential form
#print axioms Probability.probNotHitBy_le_prefixMass
#print axioms Probability.schedulerPrefix_expect_le_pow
#print axioms transitionPEM_effRc
#print axioms effRc_runPrefix_ge
#print axioms propagation_not_full_le
#print axioms epidemic_incomplete_le
#print axioms P_EM_paper_propagation

-- Definition 1 with probability one for the finite instances; transfer and composition
#print axioms Probability.kanayaDefinition1_of_solvesSSEM_of_fintype
#print axioms P_EM_paper_fin_kanayaDefinition1
#print axioms P_EM_paper_fin_silent_almostSurely
#print axioms P_EM_fin_kanayaDefinition1
#print axioms StateSimulation.probNotHitBy_encC
#print axioms StateSimulation.expectedHittingTime_encC
#print axioms probNotHitBy_compose_le

-- B33 at the paper constants; Theorem 4 time part from the window and the stages
#print axioms count_tail_some_le
#print axioms P_EM_paper_dormancy
#print axioms P_EM_paper_dormancy_bound
#print axioms kanayaThm4Time_of_window
#print axioms two_tOne_le
#print axioms pemPaperWindow_of_stages
#print axioms kanayaThm4Time_of_stages
#print axioms epoch1_of_stages
#print axioms epoch2_of_stages
#print axioms Probability.probNotHitBy_le_prefixMass_avoid
#print axioms Probability.probNotHitBy_le_potential
#print axioms Probability.probNotHitBy_window_le_drift
#print axioms Probability.probNotHitBy_window_le_drift_guarded
#print axioms exists_leader_step
#print axioms stageB1
#print axioms stageB2
#print axioms stageB2M
#print axioms stageB1Za
#print axioms stageB1Zb
#print axioms stageB1Z
#print axioms zInv_step
#print axioms dormancy_answers
#print axioms stageE
#print axioms stageC
#print axioms stageA'
#print axioms stageB56
#print axioms stageB56M
#print axioms stageA
#print axioms kanayaThm4Time_explicit_of_window
#print axioms stageB34
#print axioms stageB34M
#print axioms P_EM_paper_window
#print axioms P_EM_paper_thm4_time
#print axioms kanayaThm4Time

-- Concrete ranking subprotocol
#print axioms rankDeltaOSSR_settled_distinct_ranks
#print axioms rankDeltaStable_satisfies_fix

end Ripple.PopulationProtocol.SSEM
