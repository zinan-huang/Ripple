/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Initializer-error recovery through Phase 10 to the correct stable endpoint

`Recovery10EntryTime` bounds the global epidemic from one active Phase-10
initializer-error seed to `Phase10Ready`.  This file composes that bound with
the three existing Phase-10 drain engines and the conserved-sign bridges to
`StableDone`.  Reachability from the original valid input is threaded
explicitly, so the final output is the verdict of that input rather than merely
an arbitrary unanimous output.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Recovery10EntryTime
import Ripple.PopulationProtocol.ExactMajority.Probability.FinalRungStability

namespace Ripple.PopulationProtocol.ExactMajority
namespace Recovery10ToStable

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal Classical
open Phase10Drop

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

private noncomputable def phase10DrainBudget (n : ℕ) : ℝ≥0∞ :=
  3 * (((n ^ 2 : ℕ) : ℝ≥0∞) *
    ENNReal.ofReal (1 + 2 * Real.log n))

/-- A reachable `Phase10Ready` configuration reaches the stable endpoint with
the verdict of the original valid input within the common three-stage Phase-10
budget.  The three ready branches are discharged separately; conservation of
the active signed sum supplies the required input-sign bridge in each branch. -/
theorem phase10Ready_reachable_expectedHitting_stableDone_le
    (n : ℕ) (hn : 2 ≤ n)
    (init y : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init y)
    (hready : Phase10Ready (L := L) (K := K) n y) :
    expectedHitting (NonuniformMajority L K).transitionKernel y
        (StableDone L K init) ≤ phase10DrainBudget n := by
  classical
  let ker := (NonuniformMajority L K).transitionKernel
  have hDone : MeasurableSet (StableDone L K init) :=
    measurableSet_StableDone L K init
  have hAbs : ∀ x ∈ StableDone L K init,
      ker x (StableDone L K init)ᶜ = 0 := by
    intro x hx
    exact StableDone_kernel_absorbing L K init x hx
  rcases hready with hS1 | hS0 | hTie
  · have hsum : phase10ActiveSignedSum y =
        initialGap (L := L) (K := K) init :=
      phase10ActiveSignedSum_eq_initialGap_of_reachable
        (L := L) (K := K) init y hinit hreach hS1.1
    have hgap : 0 < initialGap (L := L) (K := K) init := by
      rw [← hsum]
      exact hS1.2.2
    have hA : expectedHitting ker y
          (potBelow (fun c => wrongACount c) 1) ≤
        phase10DrainBudget n := by
      simpa [ker, phase10DrainBudget] using
        phase10_expected_stabilization_O_nsq_log
          (L := L) (K := K) n hn y hS1
    have hcomp := expectedHitting_seqcomp_on_of_uniform ker
      (fun c => MajorityAStage1 (L := L) (K := K) n c)
      (invClosed_majorityAStage1 (L := L) (K := K) n)
      (potBelow_measurable (fun c => wrongACount c) 1)
      hDone (phase10DrainBudget n) 0 y hS1 hA
      (fun z hzS1 hzMid =>
        phase10Majority_drained_expectedHitting_le
          (L := L) (K := K) (n := n) init 0 hDone hAbs hgap z
          ⟨hzS1, hzMid⟩)
    simpa [add_zero] using hcomp
  · have hsum : phase10ActiveSignedSum y =
        initialGap (L := L) (K := K) init :=
      phase10ActiveSignedSum_eq_initialGap_of_reachable
        (L := L) (K := K) init y hinit hreach hS0.1
    have hgap : initialGap (L := L) (K := K) init < 0 := by
      rw [← hsum]
      exact hS0.2.2
    have hA : expectedHitting ker y
          (potBelow (fun c => wrongBCount c) 1) ≤
        phase10DrainBudget n := by
      simpa [ker, phase10DrainBudget] using
        phase10_expected_stabilization_B_O_nsq_log
          (L := L) (K := K) n hn y hS0
    have hcomp := expectedHitting_seqcomp_on_of_uniform ker
      (fun c => MajorityBStage1 (L := L) (K := K) n c)
      (invClosed_majorityBStage1 (L := L) (K := K) n)
      (potBelow_measurable (fun c => wrongBCount c) 1)
      hDone (phase10DrainBudget n) 0 y hS0 hA
      (fun z hzS0 hzMid =>
        phase10BMajority_drained_expectedHitting_le
          (L := L) (K := K) (n := n) init 0 hDone hAbs hgap z
          ⟨hzS0, hzMid⟩)
    simpa [add_zero] using hcomp
  · have hsum : phase10ActiveSignedSum y =
        initialGap (L := L) (K := K) init :=
      phase10ActiveSignedSum_eq_initialGap_of_reachable
        (L := L) (K := K) init y hinit hreach hTie.1.1
    have hgap : initialGap (L := L) (K := K) init = 0 := by
      rw [← hsum]
      exact hTie.1.2.2
    have hA : expectedHitting ker y
          (potBelow (fun c => wrongTCount c) 1) ≤
        phase10DrainBudget n := by
      refine le_trans (phase10_expected_stabilization_tie_O_nsq_log
        (L := L) (K := K) n hn y hTie) ?_
      unfold phase10DrainBudget
      gcongr
      norm_num
    have hcomp := expectedHitting_seqcomp_on_of_uniform ker
      (fun c => Tie1plus (L := L) (K := K) n c)
      (invClosed_Tie1plus (L := L) (K := K) n)
      (potBelow_measurable (fun c => wrongTCount c) 1)
      hDone (phase10DrainBudget n) 0 y hTie hA
      (fun z hzTie hzMid =>
        phase10Tie_drained_expectedHitting_le
          (L := L) (K := K) (n := n) init 0 hDone hAbs hgap z
          ⟨hzTie, hzMid⟩)
    simpa [add_zero] using hcomp

/-- **Complete initializer-error recovery branch.**  From a recovery seed that
is reachable from the original valid input, the expected time to the correct
stable endpoint is at most the `n²` global spread budget plus the common
Phase-10 drain budget. -/
theorem recovery10Entry_expectedHitting_stableDone_le
    (n : ℕ) (hn : 2 ≤ n)
    (init root : Config (AgentState L K))
    (hinit : validInitial init)
    (hroot : ReachableFrom L K init root)
    (hentry : Phase2EntryDispatcher.Recovery10Entry
      (L := L) (K := K) n root) :
    expectedHitting (NonuniformMajority L K).transitionKernel root
        (StableDone L K init) ≤
      ((n * n : ℕ) : ℝ≥0∞) + phase10DrainBudget n := by
  let ker := (NonuniformMajority L K).transitionKernel
  have hReady : MeasurableSet
      {y | Phase10Ready (L := L) (K := K) n y} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hDone : MeasurableSet (StableDone L K init) :=
    measurableSet_StableDone L K init
  have hA : expectedHitting ker root
        {y | Phase10Ready (L := L) (K := K) n y} ≤
      ((n * n : ℕ) : ℝ≥0∞) := by
    simpa [ker] using
      Recovery10EntryTime.recovery10Entry_expectedHitting_ready_le_nsq
        (L := L) (K := K) n hn root hentry
  exact expectedHitting_seqcomp_on_of_uniform ker
    (ReachableFrom L K init) (reachableFrom_kernel_closed init)
    hReady hDone ((n * n : ℕ) : ℝ≥0∞) (phase10DrainBudget n)
    root hroot hA
    (fun y hyReach hyReady =>
      phase10Ready_reachable_expectedHitting_stableDone_le
        (L := L) (K := K) n hn init y hinit hyReach hyReady)

#print axioms phase10Ready_reachable_expectedHitting_stableDone_le
#print axioms recovery10Entry_expectedHitting_stableDone_le

end Recovery10ToStable
end Ripple.PopulationProtocol.ExactMajority
