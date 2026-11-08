import Ripple.PopulationProtocol.ExactMajority.Probability.Theorem31
import Ripple.PopulationProtocol.ExactMajority.Probability.BudgetTightening

/-!
# The honest 19-instance fast prefix

The full terminal interleave has 21 instances:
`work₀, seam₀, ..., work₉, seam₉, work₁₀`.  The fast prefix stops after
`work₉`, so its index type is `Fin 19`.  In particular, neither the final
seam nor the quadratic Phase-10 recovery work contributes to the fast
horizon or its per-instance calibration surface.

This file proves only the tail for failure of `work₉.Post`.  Turning that
postcondition into stable majority output is a separate, explicitly named
reachable-scoped obligation, not a conclusion of this file.

This is an algebraic recut conditional on a supplied `TerminalAssemblyR`; it
does not prove that the assembly residuals are jointly inhabited.  In
particular, it does not resolve the Phase-4 stable-tie branch against the
subsequent seam payload, so it must not be read as a closed concrete fast path.
-/

namespace Ripple.PopulationProtocol.ExactMajority
namespace Theorem31
namespace FastPrefix

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The first nineteen instances of the reachable terminal interleave.

Index `18` is `work₉`; indices `19` and `20` (the last seam and Phase 10)
are outside this family by construction. -/
def phases {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) :
    Fin 19 → PhaseConvergenceWR (NonuniformMajority L K) c₀ :=
  fun i => phasesR asm ⟨i.val, by omega⟩

/-- The inherited reachable chain law for the nineteen-instance prefix. -/
theorem phases_h_chain {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) :
    ∀ (i : Fin 19) (hi : i.val + 1 < 19),
      ∀ x, (NonuniformMajority L K).Reachable c₀ x →
        (phases asm i).Post x →
          (phases asm ⟨i.val + 1, hi⟩).Pre x := by
  intro i hi x hreach hpost
  have hi21 : i.val < 21 := lt_trans i.isLt (by norm_num)
  let j : Fin 21 := ⟨i.val, hi21⟩
  have hj : j.val + 1 < 21 := by
    change i.val + 1 < 21
    exact lt_trans hi (by norm_num)
  have hpost' : (phasesR asm j).Post x := by
    simpa only [phases, j] using hpost
  have hout := phasesR_h_chain asm j hj x hreach hpost'
  simpa only [phases, j] using hout

/-- The last prefix instance is exactly `work₉`. -/
theorem phases_last_eq_work9 {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) :
    phases asm ⟨19 - 1, by omega⟩ =
      PhaseConvergenceWR.ofW (NonuniformMajority L K) c₀
        (asm.work ⟨9, by omega⟩) := by
  rw [phases, phasesR_even asm _ (by norm_num)]
  congr 2

/-- Projection form of `phases_last_eq_work9`, used without unfolding either
phase-convergence proof record. -/
theorem phases_last_post_eq_work9 {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀) :
    (phases asm ⟨19 - 1, by omega⟩).Post =
      (asm.work ⟨9, by omega⟩).Post := by
  exact congrArg PhaseConvergenceWR.Post (phases_last_eq_work9 asm)

/-- Fin-19 fast-prefix tail and heterogeneous time bound.

The calibration hypotheses range only over the fast prefix.  The result is a
tail for failure of `work₉.Post`; it deliberately makes no stable-output claim. -/
theorem post_tail
    {n : ℕ} {c₀ : Config (AgentState L K)}
    (asm : TerminalAssemblyR (L := L) (K := K) n c₀)
    (hStart : (asm.work ⟨0, by omega⟩).Pre c₀)
    (Cphase : Fin 19 → ℕ)
    (T : ℕ) (hT : T = ∑ i, (phases asm i).t)
    (ht : ∀ i, (phases asm i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases asm i).ε : ℝ≥0∞) ≤
      (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ (asm.work ⟨9, by omega⟩).Post c}
      ≤ (19 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ (∑ i, Cphase i) * n * (L + 1) := by
  have hx₀ : (phases asm ⟨0, by omega⟩).Pre c₀ := by
    change (phasesR asm ⟨0, by omega⟩).Pre c₀
    rw [phasesR_even asm _ (by rfl)]
    show (asm.work (ExactAdvanceChain.workIdx ⟨0, by omega⟩)).Pre c₀
    simpa [ExactAdvanceChain.workIdx] using hStart
  have hreach₀ : (NonuniformMajority L K).Reachable c₀ c₀ :=
    Relation.ReflTransGen.refl
  have hcompose :
      ((NonuniformMajority L K).transitionKernel ^
          (∑ i : Fin 19, (phases asm i).t)) c₀
          {c | ¬ (phases asm ⟨19 - 1, by omega⟩).Post c}
        ≤ ∑ i : Fin 19, ((phases asm i).ε : ℝ≥0∞) :=
    composeWR_n_phases (NonuniformMajority L K)
      (m := 19) (by omega) (phases asm)
      (phases_h_chain asm) c₀ hreach₀ hx₀
  rw [← hT] at hcompose
  have htail :
      ((NonuniformMajority L K).transitionKernel ^
          T) c₀
          {c | ¬ (asm.work ⟨9, by omega⟩).Post c}
        ≤ ∑ i, ((phases asm i).ε : ℝ≥0∞) := by
    have hset :
        {c | ¬ (asm.work ⟨9, by omega⟩).Post c} =
          {c | ¬ (phases asm ⟨19 - 1, by omega⟩).Post c} := by
      ext c
      change (¬ (asm.work ⟨9, by omega⟩).Post c) ↔
        ¬ (phases asm ⟨19 - 1, by omega⟩).Post c
      rw [phases_last_post_eq_work9 asm]
    rw [hset]
    exact hcompose
  refine ⟨le_trans htail ?_, ?_⟩
  · exact BudgetTightening.sum_inv_sq_le
      (m := 19) (n := n) (fun i => (phases asm i).ε) hε
  · rw [hT]
    exact total_time_le_W (fun i => (phases asm i).t) Cphase ht

#print axioms phases_h_chain
#print axioms phases_last_eq_work9
#print axioms phases_last_post_eq_work9
#print axioms post_tail

end
end FastPrefix
end Theorem31
end Ripple.PopulationProtocol.ExactMajority
