import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6SurvivalContracting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CounterGuardedPhase

/-!
# Phase-6 honest-window leak is ZERO on the clock-positive gate

`phase6_survival_contracting` carries a per-step leak hypothesis
`hLeak : ∀ x ∈ {Phase6Win}, x ∈ S → K x {¬ Phase6Win} ≤ q_leak`.

This file discharges it with `q_leak = 0` on the clock-positive gate
`S = ClockPos` (every `Role.clock` agent has `counter.val > 0`):

* `Phase6Win` = `card = n ∧ all agents at phase 6`;
* card is conserved on the step support (`stepDistOrSelf_support_card_eq`);
* on a clock-positive phase-6 config no clock is at counter 0, so the phase-
  advancing guard never fires and every step successor is still all-phase-6
  (`CounterGuardedPhase.allPhaseN_preserved_of_counterPos`).

Hence every support point of one step is again `Phase6Win`, so the
`{¬ Phase6Win}` event is disjoint from the step support and has measure `0`.

This is exactly the per-step leak `q_leak = 0`.  (Clock-positivity is itself
NOT step-invariant — clocks tick down — so this is a single-step bound, not a
cumulative one; the cumulative clock-failure prefix `∑ τ, Kᵗ c₀ Sᶜ` is the
separate clock-layer tail `η_clock`.)
-/

namespace ExactMajority
namespace Phase6LeakZero

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {L K : ℕ}

/-- The clock-positive gate: every `Role.clock` agent has a strictly positive counter. -/
def ClockPos (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.clock → 0 < a.counter.val

/-- **Phase-6 honest-window leak is zero on the clock-positive gate.**
On a `Phase6Win` config whose clocks all have positive counter, one protocol
step cannot leave `Phase6Win`: the leak probability is exactly `0`. -/
theorem phase6_leak_zero_on_clockPos (n : ℕ) (c : Config (AgentState L K))
    (hWin : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hpos : ClockPos (L := L) (K := K) c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n c'} = 0 := by
  have hmeas : (NonuniformMajority L K).transitionKernel c
      = ((NonuniformMajority L K).stepDistOrSelf c).toMeasure := rfl
  rw [hmeas,
    PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (s := {c' : Config (AgentState L K) |
        ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n c'})
      (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  apply hbad
  refine ⟨?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hsupp]
    exact hWin.1
  · exact CounterGuardedPhase.allPhaseN_preserved_of_counterPos
      6 n (by norm_num) (by norm_num) c c' hWin.1 hWin.2 hpos hsupp

/-- The leak bound in the `≤ q_leak` shape `phase6_survival_contracting.hLeak`
expects, with `q_leak = 0` and the clock-positive gate `S = ClockPos`. -/
theorem phase6_leak_le_zero_on_clockPos (n : ℕ) :
    ∀ x ∈ {c : Config (AgentState L K) |
        Phase6Convergence.Phase6Win (L := L) (K := K) n c},
      ClockPos (L := L) (K := K) x →
      (NonuniformMajority L K).transitionKernel x
          {c | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n c} ≤ (0 : ℝ≥0∞) := by
  intro x hx hpos
  rw [phase6_leak_zero_on_clockPos n x hx hpos]

end Phase6LeakZero
end ExactMajority
