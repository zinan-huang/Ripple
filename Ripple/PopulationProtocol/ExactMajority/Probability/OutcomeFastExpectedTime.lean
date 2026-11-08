/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expected time from the outcome-aware fast prefix

This file connects the genuine nineteen-instance fast prefix to the recovery
algebra.  Phase 10 is not inserted as a twentieth fast phase: it remains in the
reachable recovery classification.  All protocol-specific fast assumptions are
therefore visible in `OutcomeFastAssembly.Assembly` and `hWork9Done`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.OutcomeFastAssembly
import Ripple.PopulationProtocol.ExactMajority.Probability.FastExpectedTime

namespace Ripple.PopulationProtocol.ExactMajority
namespace OutcomeFastExpectedTime

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

variable {L K : ℕ}

/-- Feed the outcome-aware fast tail directly into the reachable recovery
classification.  The fast failure probability is the explicit nineteen-phase
union bound `19 / n²`. -/
theorem expected_time_of_outcome_assembly
    {n Brecover : ℕ}
    (init : Config (AgentState L K))
    (asm : OutcomeFastAssembly.Assembly (L := L) (K := K) n init)
    (hStart : (asm.work ⟨0, by omega⟩).Pre init)
    (T : ℕ) (Esum : ℝ≥0∞)
    (hT : T = ∑ i : Fin 19, (OutcomeFastAssembly.phases asm i).t)
    (hEsum : Esum = ∑ i : Fin 19,
      ((OutcomeFastAssembly.phases asm i).ε : ℝ≥0∞))
    (Cphase : Fin 19 → ℕ)
    (ht : ∀ i, (OutcomeFastAssembly.phases asm i).t ≤
      Cphase i * n * (L + 1))
    (hε : ∀ i, ((OutcomeFastAssembly.phases asm i).ε : ℝ≥0∞) ≤
      1 / (n : ℝ≥0∞) ^ 2)
    (hWork9Done : ∀ c : Config (AgentState L K),
      (NonuniformMajority L K).Reachable init c →
      (asm.work ⟨9, by omega⟩).Post c →
      c ∈ StableDone L K init)
    (hBpos : 0 < Brecover)
    (hClassify : ∀ b,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      ReachablePhaseRegimeClassification
        L K n init b (Brecover : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel init
        (StableDone L K init)
      ≤ (T : ℝ≥0∞) +
        ((19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2) *
          ((2 * Brecover : ℕ) : ℝ≥0∞) *
          (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by
  have htail := OutcomeFastAssembly.done_tail
    (L := L) (K := K) asm hStart T Esum hT hEsum Cphase ht hε hWork9Done
  apply FastExpectedTime.expected_time_from_fast_tail_of_classification
    (L := L) (K := K) (n := n) (Brecover := Brecover)
    init init
    (show ReachableFrom L K init init from Relation.ReflTransGen.refl)
    T ((19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2) htail.1 hBpos hClassify

/-- Arithmetic `O(n log n)` wrapper.  `Cphase` accounts only for the nineteen
fast work/seam instances; `Crecover` accounts for the tail-weighted reachable
recovery contribution. -/
theorem expected_time_outcome_bound
    {n Crecover Brecover : ℕ}
    (init : Config (AgentState L K))
    (asm : OutcomeFastAssembly.Assembly (L := L) (K := K) n init)
    (hStart : (asm.work ⟨0, by omega⟩).Pre init)
    (T : ℕ) (Esum : ℝ≥0∞)
    (hT : T = ∑ i : Fin 19, (OutcomeFastAssembly.phases asm i).t)
    (hEsum : Esum = ∑ i : Fin 19,
      ((OutcomeFastAssembly.phases asm i).ε : ℝ≥0∞))
    (Cphase : Fin 19 → ℕ)
    (ht : ∀ i, (OutcomeFastAssembly.phases asm i).t ≤
      Cphase i * n * (L + 1))
    (hε : ∀ i, ((OutcomeFastAssembly.phases asm i).ε : ℝ≥0∞) ≤
      1 / (n : ℝ≥0∞) ^ 2)
    (hWork9Done : ∀ c : Config (AgentState L K),
      (NonuniformMajority L K).Reachable init c →
      (asm.work ⟨9, by omega⟩).Post c →
      c ∈ StableDone L K init)
    (hBpos : 0 < Brecover)
    (hClassify : ∀ b,
      ReachableFrom L K init b →
      b ∈ (StableDone L K init)ᶜ →
      ReachablePhaseRegimeClassification
        L K n init b (Brecover : ℝ≥0∞))
    (hRecoveryMass :
      ((19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2) *
          ((2 * Brecover : ℕ) : ℝ≥0∞) *
          (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((Crecover * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel init
        (StableDone L K init)
      ≤ ((((∑ i, Cphase i) + Crecover) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  have htail := OutcomeFastAssembly.done_tail
    (L := L) (K := K) asm hStart T Esum hT hEsum Cphase ht hε hWork9Done
  exact FastExpectedTime.expected_time_fast_recovery_bound
    (L := L) (K := K) (n := n)
    (Cfast := ∑ i, Cphase i) (Crecover := Crecover) (Brecover := Brecover)
    init init
    (show ReachableFrom L K init init from Relation.ReflTransGen.refl)
    T ((19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2) htail.1 htail.2 hBpos
    hClassify hRecoveryMass

#print axioms expected_time_of_outcome_assembly
#print axioms expected_time_outcome_bound

end
end OutcomeFastExpectedTime
end Ripple.PopulationProtocol.ExactMajority
