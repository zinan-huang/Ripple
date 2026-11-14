-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingMassCountProducer.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingMassCountTransport
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingRowTwoConsumer

/-!
# The `CompletionProducer.mass_counts` field

This file packages the deterministic transport results at the actual completed
sampling snapshot.  `FirstBranchShapeData` is retained in the output so the
actual Main count and the reachable mass-ledger derivation remain explicit.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingMassCountProducer

open TimeTheorem PairLog
open StageEventSpec
open LateSamplingCompletion
open LateSamplingFirstBranchShape
open LateSamplingMassCountTransport
open LateSamplingSeedReceipt
open LateSamplingRowTwoConsumer

variable {n : ℕ}

/-- The elementary rounding and final debt budgets not present in a
`CompletionReceipt`. -/
structure MassCountBudget
    (n : ℕ) (M : ℝ)
    (Rlo Rhi Btail Bmajority Bminority : ℕ) : Prop where
  tail_round :
    (1 / 500 : ℝ) * M < (Btail + 1 : ℕ)
  majority_round :
    (19 / 100 : ℝ) * M < (Bmajority + 1 : ℕ)
  minority_round :
    (1 / 250 : ℝ) * M < (Bminority + 1 : ℕ)
  lower_budget :
    LatePotential.fuelFloor n + Btail ≤ Rlo
  higher_budget :
    LatePotential.fuelFloor n +
      (2 * Btail + 2 * (Bmajority + Bminority)) ≤ Rhi

/-- The complete deterministic receipt at the actual completed snapshot.

The `shape` field is produced by `firstBranchShapeData_at`; that theorem invokes
`reachable_ledger_bounds` internally.  Its mass-shape inequality remains
available for the separate class-floor item, while `main_count_real` records
the exact alignment required by this item. -/
structure CompletedMassCountReceipt
    {init : InputCfg n} {ω : InputLog n}
    (four u m : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (sigma : Sign) (M : ℝ) (Rlo Rhi : ℕ) : Prop where
  shape :
    FirstBranchShapeData
      (init := init) (ω := ω) four u m ell.val sigma
  main_count_real :
    (timeMainCount (trace init ω u) : ℝ) = M
  mass_counts :
    Phase5To6FuelProducer.Lemma72MassCountBounds
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      sigma ell M (LatePotential.fuelFloor n) Rlo Rhi
      (trace init ω u)

/-- Produce Lemma 7.2's two deterministic branch inequalities at the exact
sampling-completion snapshot. -/
theorem completedMassCountReceipt
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n} {a four five u m : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {sigma : Sign} {M : ℝ}
    {Rlo Rhi Btail Bmajority Bminority : ℕ}
    (hcompletion : CompletionReceipt
      init ω a four five u TrivialSnapshot)
    (hseed : LateSamplingSeedReceipt
      init m ell.val sigma (trace init ω four))
    (hM : (m : ℝ) = M)
    (hbudget : MassCountBudget
      n M Rlo Rhi Btail Bmajority Bminority) :
    CompletedMassCountReceipt
      (init := init) (ω := ω)
      four u m ell sigma M Rlo Rhi := by
  have hshape :=
    firstBranchShapeData_at
      hvalid hcompletion.observed_path hseed
      hcompletion.observed_path.observed le_rfl
  have htail :
      Lemma615MassAbove.massAboveScaled
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          ell.val (trace init ω u) ≤ Btail :=
    massAboveScaled_le_natCap_at_observed
      hcompletion.observed_path hseed hM hbudget.tail_round
  have hminority :
      Phase5Convergence.biasedMainClassU
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          (Phase3Post3.minoritySignOfMajority sigma) ell
          (trace init ω u) ≤ Bminority :=
    minorityClassU_le_natCap_at_observed
      ell sigma hcompletion.observed_path hseed
      hM hbudget.minority_round
  refine
    { shape := hshape
      main_count_real := ?_
      mass_counts := ?_ }
  · rw [hshape.main_count, hM]
  · exact
      Phase5To6FuelProducer.Lemma72MassCountBounds.of_paper_caps
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma ell M (LatePotential.fuelFloor n) Rlo Rhi
        Btail Bmajority Bminority (trace init ω u)
        htail hbudget.majority_round hminority
        hbudget.lower_budget hbudget.higher_budget

/-- A function with literally the type of
`LateSamplingRowTwoConsumer.CompletionProducer.mass_counts`.

The N16 seed selector is explicit because `CompletionReceipt` intentionally
contains only completion data; it does not recover the earlier retained-credit
receipt by itself. -/
theorem completionProducer_mass_counts
    {init : InputCfg n} (hvalid : validInitial init)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (_hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma : Sign) (M : ℝ) (Rlo Rhi : ℕ)
    {rowFailure : Set (InputLog n)}
    {m Btail Bmajority Bminority : ℕ}
    (hM : (m : ℝ) = M)
    (hseed : ∀ ω a four five u,
      ω ∉ rowFailure →
      CompletionReceipt init ω a four five u TrivialSnapshot →
      LateSamplingSeedReceipt
        init m ell.val sigma (trace init ω four))
    (hbudget : MassCountBudget
      n M Rlo Rhi Btail Bmajority Bminority) :
    ∀ ω a four five u,
      ω ∉ rowFailure →
      CompletionReceipt init ω a four five u TrivialSnapshot →
      Phase5To6FuelProducer.Lemma72MassCountBounds
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma ell M (LatePotential.fuelFloor n) Rlo Rhi
        (trace init ω u) := by
  intro ω a four five u hrow hcompletion
  exact
    (completedMassCountReceipt
      hvalid hcompletion
      (hseed ω a four five u hrow hcompletion)
      hM hbudget).mass_counts

/-- The rounding inequalities and the budget arithmetic are always satisfiable
for the floor caps: the minimal `Rlo`, `Rhi` are explicit.  (Whether those
minimal `Rlo`, `Rhi` are compatible with the class floors is a separate numeric
question and is not decided here.) -/
theorem massCountBudget_floor (n : ℕ) (M : ℝ) :
    MassCountBudget n M
      (LatePotential.fuelFloor n + ⌊(1 / 500 : ℝ) * M⌋₊)
      (LatePotential.fuelFloor n +
        (2 * ⌊(1 / 500 : ℝ) * M⌋₊ +
          2 * (⌊(19 / 100 : ℝ) * M⌋₊ + ⌊(1 / 250 : ℝ) * M⌋₊)))
      ⌊(1 / 500 : ℝ) * M⌋₊ ⌊(19 / 100 : ℝ) * M⌋₊ ⌊(1 / 250 : ℝ) * M⌋₊ :=
  { tail_round := by
      exact_mod_cast Nat.lt_floor_add_one ((1 / 500 : ℝ) * M)
    majority_round := by
      exact_mod_cast Nat.lt_floor_add_one ((19 / 100 : ℝ) * M)
    minority_round := by
      exact_mod_cast Nat.lt_floor_add_one ((1 / 250 : ℝ) * M)
    lower_budget := le_rfl
    higher_budget := le_rfl }

/-!
THEOREM LIST
* `MassCountBudget`
* `CompletedMassCountReceipt`
* `completedMassCountReceipt`
* `completionProducer_mass_counts`
* `massCountBudget_floor`

CLOSES
* `LateSamplingRowTwoConsumer.CompletionProducer.mass_counts` once the N16
  seed selector and the five elementary arithmetic inputs are supplied.
* The actual completed-snapshot alignment `(timeMainCount : ℝ) = M`.
* The corrected Lemma-7.2 higher branch using majority plus minority exact-level
  caps, with no carried implication.
* Explicit use of `FirstBranchShapeData`; its producer is the route through
  `reachable_ledger_bounds`.

UNFINISHED
* The row-failure complement must supply the N16 seed receipt at `four`; this
  is the retained-credit selection input owned by the N16/row-two event
  assembly, not by sampling completion.
* A numerical file must instantiate `Btail`, `Bmajority`, `Bminority`, `Rlo`,
  and `Rhi` and prove the five fields of `MassCountBudget`.
* `CompletionProducer.base`, `CompletionProducer.class_floors`, and the row-2
  probability headline remain separate items.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingMassCountProducer

end
