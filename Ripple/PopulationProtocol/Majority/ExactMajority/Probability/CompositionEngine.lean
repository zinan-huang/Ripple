/-
# CompositionEngine — the abstract 21-instance composition engine.

Extracted from `SlotEngine.lean` to isolate the two generic theorems (`fold_pair_to_T` and
`whp_of_asm'`) that operate on a FREE `SeedTrigWiring.Assembly'` and do NOT depend on
`WorkInputsHonest`, `ResidualAtoms`, `DrainEngine`, or any chain-specific structure.

`whp_of_asm'` is the core composition engine: given a generic `Assembly'` whose 21-instance
`phases'` family has per-phase budgets `≤ δ i` and per-phase times `≤ Cphase i * n * (L+1)`,
it produces the headline failure bound `≤ 21/n²` and the time bound `T ≤ 21·C0·n·(L+1)`.
It consumes `BudgetTightening.time_headline_W2_inv_sq` (which does the union-bound
internally) and folds the result to the opaque horizon `T` through `fold_pair_to_T`.

## Imports
Only `SeedTrigWiring` (for `Assembly'`, `phases'`, `phases'_h_chain`) and `BudgetTightening`
(for `time_headline_W2_inv_sq`, `majorityStableEndpoint`).  No `DrainEngine`, no `PaperRegime`,
no chain-level structures.

## Discipline
Append-only extract; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedTrigWiring
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PaperRegime
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BudgetTightening

namespace ExactMajority
namespace SlotEngine

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-- **The F1 whp half PRODUCED over an ABSTRACT assembly, at the OPAQUE horizon `T`.**  The engineering
attack on the kernel-power obstruction, executed where it is tractable — over a FREE
`asm : Assembly'`, and via the LANDED in-file `.1`-producer `BudgetTightening.time_headline_
W2_inv_sq` (which extracts the composition's failure-side `.1` and chains it to `21/n²` INSIDE its own
file, where the kernel-power `whnf` is transparent).

`whp_of_asm'` instantiates that producer at `phases' asm` and folds both clauses to the OPAQUE `T`
through the abstract horizon-fold `fold_pair_to_T` (whose `rw [hT]; exact …` is the landed
`AssemblyBridges.hcompFail_of_composition` idiom — `hpair` arrives as a FREE hypothesis, so the fold
is syntactic).  Because `asm` is free and the produced bound is supplied to `fold_pair_to_T` as an
opaque hypothesis (never re-projected in this file), the divergent ConcreteAssembly whnf — which fires
only when a CONCRETE unfolded family's kernel-power is matched in place — never triggers.

The conclusion is at the opaque `T`, so the concrete theorem CONSUMES it cheaply (the crude landed
`time_headline_CONCRETE'` is consumable at a concrete family for exactly this reason: its output
is at opaque `T`).  `hcompFail` is a free binder NOWHERE. -/
theorem fold_pair_to_T {n C0 : ℕ} {S : ℕ} (init c₀ : Config (AgentState L K))
    (hpair :
      ((NonuniformMajority L K).transitionKernel ^ S) c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
      ∧ S ≤ 21 * C0 * n * (L + 1))
    (T : ℕ) (hT : T = S) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1) := by
  subst hT; exact hpair

theorem whp_of_asm' {n C0 : ℕ} (init c₀ : Config (AgentState L K))
    (asm : SeedTrigWiring.Assembly' (L := L) (K := K) n)
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (T : ℕ) (hT : T = ∑ i, (SeedTrigWiring.phases' asm i).t)
    (ht : ∀ i, (SeedTrigWiring.phases' asm i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((SeedTrigWiring.phases' asm i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (hx₀ : (SeedTrigWiring.phases' asm ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (SeedTrigWiring.phases' asm ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1) :=
  fold_pair_to_T (C0 := C0) init c₀
    (BudgetTightening.time_headline_W2_inv_sq (C0 := C0) init c₀ Cphase δ
      (SeedTrigWiring.phases' asm) ht hε (SeedTrigWiring.phases'_h_chain asm) hx₀ h_post
      hC0 hδ)
    T hT

end SlotEngine
end ExactMajority
