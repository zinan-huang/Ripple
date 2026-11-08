/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conditional fast-prefix plus recovery reduction

This file joins the honest `Fin 19` prefix with the reachable recovery ladder.
Phase 10 is not a member of the fast family: its (possibly quadratic) cost appears
only through `Brecover` and the tail-weighted recovery budget.

This is deliberately a residual theorem.  In particular, `hWork9Stable` records the
still-missing reachable Phase-9 output-closing map, while `TerminalAssemblyR` still
contains the work/seam payload obligations.  Consequently this declaration is not an
unconditional quantitative theorem about the concrete protocol.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.FastPrefix
import Ripple.PopulationProtocol.ExactMajority.Probability.FastExpectedTime

namespace Ripple.PopulationProtocol.ExactMajority
namespace FastRecoveryReduction

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Expected-time reduction for the 19-instance fast prefix followed by reachable
recovery.

The fast error is exactly the union-bound value `19 / n²`.  The Phase-10 process is
absent from `Cphase`; it may occur only inside `hClassify`/`Brecover`. -/
theorem expected_time_of_fast_prefix_of_recovery
    {n Brecover Crecover : ℕ}
    (init c₀ : Config (AgentState L K))
    (hc₀Reach : ReachableFrom L K init c₀)
    (asm : Theorem31.TerminalAssemblyR (L := L) (K := K) n c₀)
    (hStart : (asm.work ⟨0, by omega⟩).Pre c₀)
    (Cphase : Fin 19 → ℕ)
    (Tfast : ℕ)
    (hTfastDef : Tfast = ∑ i, (Theorem31.FastPrefix.phases asm i).t)
    (ht : ∀ i, (Theorem31.FastPrefix.phases asm i).t ≤
      Cphase i * n * (L + 1))
    (hε : ∀ i, (((Theorem31.FastPrefix.phases asm i).ε : ℝ≥0∞) ≤
      (1 / (n : ℝ≥0∞) ^ 2)))
    (hWork9Stable : ∀ c,
      (NonuniformMajority L K).Reachable c₀ c →
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
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
        (StableDone L K init)
      ≤ ((((∑ i, Cphase i) + Crecover) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  have hprefix :
      ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
          {c | ¬ (asm.work ⟨9, by omega⟩).Post c}
        ≤ (19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
      ∧ Tfast ≤ (∑ i, Cphase i) * n * (L + 1) := by
    exact Theorem31.FastPrefix.post_tail
      asm hStart Cphase Tfast hTfastDef ht hε
  have hsubset :
      (StableDone L K init)ᶜ ⊆
        {c | ¬ (asm.work ⟨9, by omega⟩).Post c} ∪
          {c | ¬ (NonuniformMajority L K).Reachable c₀ c} := by
    intro c hc
    by_cases hreach : (NonuniformMajority L K).Reachable c₀ c
    · refine Or.inl ?_
      simp only [Set.mem_setOf_eq]
      intro hpost
      exact hc (hWork9Stable c hreach hpost)
    · exact Or.inr hreach
  have hunreach :
      ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
          {c | ¬ (NonuniformMajority L K).Reachable c₀ c} = 0 :=
    nonuniformTransitionKernel_pow_not_reachable_eq_zero L K c₀ Tfast
  have hFast :
      ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
          (StableDone L K init)ᶜ
        ≤ (19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by
    calc
      ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
          (StableDone L K init)ᶜ
          ≤ ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
              ({c | ¬ (asm.work ⟨9, by omega⟩).Post c} ∪
                {c | ¬ (NonuniformMajority L K).Reachable c₀ c}) :=
            measure_mono hsubset
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
              {c | ¬ (asm.work ⟨9, by omega⟩).Post c} +
            ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
              {c | ¬ (NonuniformMajority L K).Reachable c₀ c} :=
            measure_union_le _ _
      _ = ((NonuniformMajority L K).transitionKernel ^ Tfast) c₀
              {c | ¬ (asm.work ⟨9, by omega⟩).Post c} := by
            rw [hunreach, add_zero]
      _ ≤ (19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := hprefix.1
  exact FastExpectedTime.expected_time_fast_recovery_bound
    (L := L) (K := K) (n := n)
    (Cfast := ∑ i, Cphase i) (Crecover := Crecover)
    (Brecover := Brecover)
    init c₀ hc₀Reach Tfast
    ((19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2) hFast hprefix.2
    hBpos hClassify hRecoveryMass

#print axioms expected_time_of_fast_prefix_of_recovery

end
end FastRecoveryReduction
end Ripple.PopulationProtocol.ExactMajority
