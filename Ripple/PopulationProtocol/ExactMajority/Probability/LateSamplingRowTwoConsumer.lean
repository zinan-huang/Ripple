-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingRowTwoConsumer.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingRowTwoChoices
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFuel

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingRowTwoConsumer

open TimeTheorem PairLog
open LateSamplingRowTwoChoices

variable {n : ℕ}

/-- Row 3 may first produce a completion receipt with no row-two payload. -/
def TrivialSnapshot (_c : InputCfg n) : Prop := True

/-- Exact explicit inputs still needed after the original-law row-two family
has been fixed.  `class_floors` is the output of the repaired four-inequality
cover.  `mass_counts` is the separate deterministic Lemma 7.2 producer and is
not a consequence of sampling completion. -/
structure CompletionProducer
    (init : InputCfg n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi : ℕ)
    (rowFailure : Set (InputLog n)) : Prop where
  base : ∀ ω,
    ω ∉ LateSamplingCompletion.completionFailure init n →
    ∃ a four five u,
      LateSamplingCompletion.CompletionReceipt
        init ω a four five u TrivialSnapshot
  class_floors : ∀ ω a four five u,
    ω ∉ rowFailure →
    LateSamplingCompletion.CompletionReceipt
        init ω a four five u TrivialSnapshot →
    Phase5To6FuelProducer.TwoClassSampleFloors
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      ell hell Rlo Rhi (trace init ω u)
  mass_counts : ∀ ω a four five u,
    ω ∉ rowFailure →
    LateSamplingCompletion.CompletionReceipt
        init ω a four five u TrivialSnapshot →
    Phase5To6FuelProducer.Lemma72MassCountBounds
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      σ ell M (LatePotential.fuelFloor n) Rlo Rhi
      (trace init ω u)

/-- This is literally the `hcompletion` argument consumed by
`LateMixedFuel.law_compatibleFuelFailure_tail`. -/
theorem CompletionProducer.hcompletion
    {init : InputCfg n}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {σ : Sign} {M : ℝ} {Rlo Rhi : ℕ}
    {rowFailure : Set (InputLog n)}
    (P : CompletionProducer init ell hell σ M Rlo Rhi rowFailure) :
    ∀ ω,
      ω ∉ LateSamplingCompletion.completionFailure init n →
      ω ∉ rowFailure →
      ∃ a four five u,
        LateSamplingCompletion.CompletionReceipt
          init ω a four five u
            (LateMixedFuel.EntryFuelCertificate
              n ell hell σ M Rlo Rhi) := by
  intro ω hcompletion hrow
  rcases P.base ω hcompletion with ⟨a, four, five, u, hreceipt⟩
  refine ⟨a, four, five, u, ?_⟩
  exact
    { observed_path := hreceipt.observed_path
      five_start := hreceipt.five_start
      completed_at := hreceipt.completed_at
      start_le := hreceipt.start_le
      within_sixteen := hreceipt.within_sixteen
      complete := hreceipt.complete
      snapshot :=
        { class_floors := P.class_floors ω a four five u hrow hreceipt
          mass_counts := P.mass_counts ω a four five u hrow hreceipt } }

/-- The pair `(hrow, hcompletion)` in exactly the form required by the row-four
consumer. -/
theorem rowTwo_consumer_inputs
    (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (σ : Sign) (M : ℝ) (Rlo Rhi H : ℕ)
    (P : CompletionProducer init ell hell σ M Rlo Rhi
      (rowTwoFailure init ell hell H)) :
    law init (rowTwoFailure init ell hell H) ≤
        ENNReal.ofReal
          (13 * (n : ℝ) ^ 2 *
            Real.exp (-(n : ℝ) / 800000000000000)) ∧
      (∀ ω,
        ω ∉ LateSamplingCompletion.completionFailure init n →
        ω ∉ rowTwoFailure init ell hell H →
        ∃ a four five u,
          LateSamplingCompletion.CompletionReceipt
            init ω a four five u
              (LateMixedFuel.EntryFuelCertificate
                n ell hell σ M Rlo Rhi)) := by
  exact ⟨law_rowTwoFailure_tail init hcard hn ell hell H,
    P.hcompletion⟩

/-!
THEOREM LIST
* `CompletionProducer.hcompletion`
* `rowTwo_consumer_inputs`

CLOSES
* Exact assembly of `EntryFuelCertificate` at `CompletionReceipt.snapshot`.
* Exact `hrow` and `hcompletion` interface consumed by
  `LateMixedFuel.law_compatibleFuelFailure_tail`.
* No conditioning on eventual completion is introduced.

UNFINISHED
* Construct `CompletionProducer.class_floors` from the repaired accepted-trial
  finite union and the four snapshot inequalities.
* Construct `CompletionProducer.mass_counts` from the separate deterministic
  Lemma 7.2 mass/count item.
* Supply the row-3 `base` completion producer.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingRowTwoConsumer

end
