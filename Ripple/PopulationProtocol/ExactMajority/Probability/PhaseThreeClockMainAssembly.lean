import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCapDeadlineTail
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockContactTail
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockExitTail

/-!
# The N12 headline modulo the open rows (assembly)

`PhaseThreeClockRowsGuarded.GuardedRowTails` has six fields. Two are proved on `main`
(`PhaseThreeClockCapDeadlineTail.guarded_cap_tail`,
`PhaseThreeClockContactTail.guarded_contact_tail`). This file assembles the structure,
and the N12 headline `asynchronous_clock_estimate` of `PhaseThreeClockProducer`, from
the remaining rows given as hypotheses:

* `StepThreeRows`: the activation, passage and shape rows in their guarded form
  (the batches, `n^{-8}`, `n^{-8}`, `2 n^{-10}`);
* `hmain`: the guarded Main row (`n^{-29}`, P11–P12).

`asynchronous_clock_estimate_of_four_rows` is the headline from these four rows and
`GoodInput n init` alone; once the Main row is a theorem the headline is
`asynchronous_clock_estimate_of_four_rows init hinput h3 (that theorem)`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainAssembly

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer PhaseThreeClockAssembly
  PhaseThreeClockExit PhaseThreeClockRows PhaseThreeClockRowsGuarded PhaseThreeClockBudget
  PhaseThreeClockExitTail PhaseThreeClockCapDeadlineTail PhaseThreeClockContactTail

variable {n : ℕ} (init : InputCfg n)

/-- The step-3 rows in the guarded form of `GuardedRowTails`. -/
structure StepThreeRows : Prop where
  activation : law init (rowFailure init (activationRow init)) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8)
  passage : law init (guardedFailure init (guardPassage init) (passageRow init)) ≤
    ENNReal.ofReal (1 / (n : ℝ) ^ 8)
  shape : law init (guardedFailure init (guardShape init) (shapeRow init)) ≤
    ENNReal.ofReal (2 / (n : ℝ) ^ 10)

/-- The contact field of `GuardedRowTails` is `guarded_contact_tail`. -/
theorem contact_field (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (guardedFailure init (guardMain init) (contactRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) :=
  le_trans (measure_mono (by
    rintro ω ⟨S, T, hs, hT, hentry, ⟨h1, h2, h3, h4⟩, hnot⟩
    exact ⟨S, T, hs, hT, hentry, h1, h2, h3, h4, hnot⟩)) (guarded_contact_tail init hinput)

/-- `GuardedRowTails` from the step-3 rows and the Main row. -/
theorem guardedRowTails_of_rows (hinput : ThresholdEpidemic.GoodInput n init)
    (h3 : StepThreeRows init)
    (hmain : law init (guardedFailure init (guardMain init) (mainRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 29)) :
    GuardedRowTails init :=
  ⟨h3.activation, h3.passage, h3.shape, guarded_cap_tail init hinput, hmain,
    contact_field init hinput⟩

/-- The virtual-core tail `hcore` from the four open rows. -/
theorem virtual_core_tail_of_four_rows (hinput : ThresholdEpidemic.GoodInput n init)
    (h3 : StepThreeRows init)
    (hmain : law init (guardedFailure init (guardMain init) (mainRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 29)) :
    law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) := by
  have h40 : 40 ≤ n := (time_population_bounds hinput.1).2
  exact virtual_core_tail_of_guarded_rows init (by omega)
    (guardedRowTails_of_rows init hinput h3 hmain)

/-- The N12 headline (`asynchronous_clock_estimate`) from `GoodInput`, the three
step-3 guarded rows and the guarded Main row. -/
theorem asynchronous_clock_estimate_of_four_rows (hinput : ThresholdEpidemic.GoodInput n init)
    (h3 : StepThreeRows init)
    (hmain : law init (guardedFailure init (guardMain init) (mainRow init)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 29)) :
    law init (phaseClockFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) :=
  asynchronous_clock_estimate_of_tails init hinput
    (virtual_core_tail_of_four_rows init hinput h3 hmain) (exit_deadline_tail init hinput)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainAssembly

end
