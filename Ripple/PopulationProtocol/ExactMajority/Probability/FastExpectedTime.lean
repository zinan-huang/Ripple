/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expected time from a fast-prefix tail and recovery

This file deliberately does not expose a `Fin 21` phase family.  The fast prefix ends
before Phase 10; all information about the fast block has already been compressed into
the scalar tail bound `hFast`.  Phase 10 belongs only to the reachable recovery ladder.

The missing protocol theorem at the fast endpoint (currently the Phase-9 output closure)
must therefore be proved before `hFast` can be supplied.  It is not hidden inside the
expected-time algebra.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ChainEndExpectedTime

namespace Ripple.PopulationProtocol.ExactMajority
namespace FastExpectedTime

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- Split-geometric expected-time bound from a scalar fast-prefix tail.

Unlike the historical expected-time surface, this theorem has no phase-indexed time or
error hypotheses.  In particular, it cannot accidentally demand an `O(n log n)` cap for
the Phase-10 recovery process. -/
theorem expected_time_from_fast_tail_on_reachable
    {Brecover : ℕ}
    (init c₀ : Config (AgentState L K))
    (hc₀Reach : ReachableFrom L K init c₀)
    (Tfast : ℕ) (δfast : ℝ≥0∞)
    (hFast :
      ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
        (StableDone L K init)ᶜ ≤ δfast)
    (hBpos : 0 < Brecover)
    (hRecover : ∀ b,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ (Brecover : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ (Tfast : ℝ≥0∞) +
        δfast * ((2 * Brecover : ℕ) : ℝ≥0∞) *
          (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by
  have hsRecCast :
      ((2 * Brecover : ℕ) : ℝ≥0∞) = 2 * (Brecover : ℝ≥0∞) := by
    push_cast
    ring
  exact expected_time_from_whp_and_recovery_on
    (NonuniformMajority L K).transitionKernel
    (ReachableFrom L K init)
    (reachableFrom_kernel_closed init)
    c₀ hc₀Reach (measurableSet_StableDone L K init)
    (fun x hx _ => StableDone_kernel_absorbing L K init x hx)
    Tfast (2 * Brecover) (by omega : 2 * Brecover ≠ 0)
    δfast (Brecover : ℝ≥0∞)
    (ENNReal.natCast_ne_top Brecover)
    (by omega : 0 < 2 * Brecover)
    (by rw [hsRecCast]; exact le_of_eq (mul_comm (Brecover : ℝ≥0∞) 2))
    hFast hRecover

/-- Build the recovery cap from the genuine reachable regime classification, then apply
the scalar fast-tail split.  Phase-10 majority/tie recovery is carried inside the
classification's ladder payload, not in a fast-phase family. -/
theorem expected_time_from_fast_tail_of_classification
    {n Brecover : ℕ}
    (init c₀ : Config (AgentState L K))
    (hc₀Reach : ReachableFrom L K init c₀)
    (Tfast : ℕ) (δfast : ℝ≥0∞)
    (hFast :
      ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
        (StableDone L K init)ᶜ ≤ δfast)
    (hBpos : 0 < Brecover)
    (hClassify : ∀ b,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      ReachablePhaseRegimeClassification
        L K n init b (Brecover : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ (Tfast : ℝ≥0∞) +
        δfast * ((2 * Brecover : ℕ) : ℝ≥0∞) *
          (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by
  have hLadder : ∀ b,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      LadderData L K init b (Brecover : ℝ≥0∞) := by
    intro b hbReach hbBad
    exact ChainEndExpectedTime.reachable_hLadder
      (L := L) (K := K) (n := n) init b hbReach hbBad
      (hClassify b hbReach hbBad)
  have hRecover : ∀ b,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ (Brecover : ℝ≥0∞) :=
    recovery_bound_via_ladder_on_reachable
      (L := L) (K := K) (n := n)
      init (Brecover : ℝ≥0∞)
      (measurableSet_StableDone L K init)
      (fun x hx => StableDone_kernel_absorbing L K init x hx)
      (reachableFrom_kernel_closed init) hLadder
  exact expected_time_from_fast_tail_on_reachable
    (L := L) (K := K) (Brecover := Brecover)
    init c₀ hc₀Reach Tfast δfast hFast hBpos hRecover

/-- `O(n log n)`-shaped arithmetic wrapper around the scalar fast/recovery split.

`Cfast` bounds only the pre-Phase-10 fast prefix.  `Crecover` bounds the tail-weighted
recovery contribution, which may use the quadratic Phase-10 process internally. -/
theorem expected_time_fast_recovery_bound
    {n Cfast Crecover Brecover : ℕ}
    (init c₀ : Config (AgentState L K))
    (hc₀Reach : ReachableFrom L K init c₀)
    (Tfast : ℕ) (δfast : ℝ≥0∞)
    (hFast :
      ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
        (StableDone L K init)ᶜ ≤ δfast)
    (hTfast : Tfast ≤ Cfast * n * (L + 1))
    (hBpos : 0 < Brecover)
    (hClassify : ∀ b,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      ReachablePhaseRegimeClassification
        L K n init b (Brecover : ℝ≥0∞))
    (hRecoveryMass :
      δfast * ((2 * Brecover : ℕ) : ℝ≥0∞) *
          (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((Crecover * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ (((Cfast + Crecover) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  have hsplit := expected_time_from_fast_tail_of_classification
    (L := L) (K := K) (n := n) (Brecover := Brecover)
    init c₀ hc₀Reach Tfast δfast hFast hBpos hClassify
  calc
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
        (StableDone L K init)
        ≤ (Tfast : ℝ≥0∞) +
            δfast * ((2 * Brecover : ℕ) : ℝ≥0∞) *
              (1 - (1 / 2 : ℝ≥0∞))⁻¹ := hsplit
    _ ≤ ((Cfast * n * (L + 1) : ℕ) : ℝ≥0∞) +
          ((Crecover * n * (L + 1) : ℕ) : ℝ≥0∞) := by
        exact add_le_add (by exact_mod_cast hTfast) hRecoveryMass
    _ = (((Cfast + Crecover) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
        push_cast
        ring

#print axioms expected_time_from_fast_tail_on_reachable
#print axioms expected_time_from_fast_tail_of_classification
#print axioms expected_time_fast_recovery_bound

end FastExpectedTime
end Ripple.PopulationProtocol.ExactMajority
