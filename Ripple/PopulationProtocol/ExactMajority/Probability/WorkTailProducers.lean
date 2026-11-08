import Ripple.PopulationProtocol.ExactMajority.Probability.Phase035Work
import Ripple.PopulationProtocol.ExactMajority.Probability.TransitionClockPairBound
import Ripple.PopulationProtocol.ExactMajority.Probability.UniformRoleSplitMilestone
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3ConfinementTail
import Ripple.PopulationProtocol.ExactMajority.Probability.ReadyEscapeCounterTail
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6Containment
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase78EscapeEta
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase10SignResolved

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace WorkTailProducers

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable section

/-! Slots 2/4/9 are supplied directly by `WorkSlotsTightEpidemic` in the work
family.  They therefore carry no scalar/opinion residual in this producer. -/

/-! ## Slot 0 -/

structure Phase0RoleSplitBudgetHypotheses (n : ℕ) where
  η : ℝ
  U : RoleSplitConcentration.UniformRoleSplitMilestone (L := L) (K := K) η n
  hWindowTime : U.tRole ≤ n * (L + 1)
  hSlotTime : U.tRole ≤ 17 * n * (L + 1)
  hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)
  ε : ℝ≥0
  hε :
    Phase0WorkTail.phase0TailBudgetENN L n U.tRole ≤ (ε : ℝ≥0∞)

noncomputable def phase0RoleSplitTail_of_budget
    {n : ℕ} (hn : 2 ≤ n)
    (R : Phase0RoleSplitBudgetHypotheses (L := L) (K := K) n) :
    Phase035Work.Phase0RoleSplitTail (L := L) (K := K) n :=
  Phase0WorkTail.phase0RoleSplitTail_of_prefixTail
    (L := L) (K := K)
    (by omega : 1 ≤ n)
    R.U
    (TransitionClockPairBound.phase0ClockZeroPrefixTail_of_log_le
      (L := L) (K := K)
      (by omega : 1 ≤ n) R.hWindowTime R.hlog)
    R.ε R.hε R.hSlotTime

/-! ## Slot 1 -/

structure Phase1ReadyEscapeHypotheses (n M₀ : ℕ) (δ : ℝ≥0) where
  P1 : ℕ
  tWin : ℕ → ℕ
  ηCounter : ℝ≥0∞
  ηFloor : ℝ≥0∞
  hCounter :
    ∀ x,
      Phase1ReadySurvival.Phase1DrainReady (L := L) (K := K) n P1 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n y}
        ≤ ηCounter
  hFloor :
    ∀ x,
      Phase1ReadySurvival.Phase1DrainReady (L := L) (K := K) n P1 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ ReadyEscapeCounterTail.phase1Floors (L := L) (K := K) n P1 y}
        ≤ ηFloor
  drainε : ℝ≥0
  hDrain :
    (∑ m ∈ Finset.Icc 1 M₀,
      (DrainEngine.qHat P1 n m) ^ (tWin m) : ℝ≥0∞)
        ≤ (drainε : ℝ≥0∞)
  escapeε : ℝ≥0
  hescε :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞)
        * (ηCounter + ηFloor)
      ≤ (escapeε : ℝ≥0∞)
  hTotal :
    (drainε : ℝ≥0∞) + (escapeε : ℝ≥0∞) ≤ (δ : ℝ≥0∞)

noncomputable def phase1ReadyEscapeBound_of_hypotheses
    {n M₀ : ℕ} {δ : ℝ≥0}
    (R : Phase1ReadyEscapeHypotheses (L := L) (K := K) n M₀ δ) :
    Phase1ReadySurvival.Phase1ReadyEscapeBound
      (L := L) (K := K) n R.P1 (R.ηCounter + R.ηFloor) :=
  ReadyEscapeCounterTail.phase1ReadyEscape_of_counterTail
    (L := L) (K := K)
    n R.P1 R.ηCounter R.ηFloor R.hCounter R.hFloor

/-- Package slot 1 with the `D`-divided drain calibration.  The remaining
escape allocation and the total fit inside `δ` stay explicit. -/
noncomputable def phase1ReadyEscapeHypotheses_of_dividedDrain
    {D n M₀ : ℕ} {δ : ℝ≥0}
    (hD1 : 1 ≤ D) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (P1 : ℕ) (tWin : ℕ → ℕ)
    (ηCounter ηFloor : ℝ≥0∞)
    (hCounter :
      ∀ x,
        Phase1ReadySurvival.Phase1DrainReady (L := L) (K := K) n P1 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor :
      ∀ x,
        Phase1ReadySurvival.Phase1DrainReady (L := L) (K := K) n P1 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ ReadyEscapeCounterTail.phase1Floors (L := L) (K := K) n P1 y}
          ≤ ηFloor)
    (hpt : ∀ m ∈ Finset.Icc 1 M₀,
      (DrainEngine.qHat P1 n m) ^ (tWin m) ≤
        (DrainCalibration.budgetNN (D * M₀) n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε :
      (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞) *
          (ηCounter + ηFloor) ≤ (escapeε : ℝ≥0∞))
    (hTotal :
      ((Real.toNNReal (1 / ((D : ℝ) * (n : ℝ) ^ 2)) : ℝ≥0) : ℝ≥0∞) +
          (escapeε : ℝ≥0∞) ≤ (δ : ℝ≥0∞)) :
    Phase1ReadyEscapeHypotheses (L := L) (K := K) n M₀ δ where
  P1 := P1
  tWin := tWin
  ηCounter := ηCounter
  ηFloor := ηFloor
  hCounter := hCounter
  hFloor := hFloor
  drainε := Real.toNNReal (1 / ((D : ℝ) * (n : ℝ) ^ 2))
  hDrain := DrainEngine.qHat_sum_budget_div hD1 hn hM1 tWin hpt
  escapeε := escapeε
  hescε := hescε
  hTotal := hTotal

/-! ## Slot 5 -/

structure Phase5SampleEscapeHypotheses (n : ℕ) where
  i5 : Fin (L + 1)
  K₀ : ℕ
  hK₀n : K₀ ≤ n
  hK₀linear : n ≤ 25 * K₀
  t : ℕ
  ε : ℝ≥0
  htail :
    ∀ c₀,
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) 5 n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬
          (AdvanceEpidemics.allPhaseEq (L := L) (K := K) 5 n c ∧
            Phase5Convergence.ReserveSampleGood
              (L := L) (K := K) i5 K₀ c)}
        ≤ (ε : ℝ≥0∞)

noncomputable def phase5C5aTail_of_hypotheses
    {n : ℕ} (R : Phase5SampleEscapeHypotheses (L := L) (K := K) n) :
    Phase035Work.Phase5C5aTail (L := L) (K := K) n where
  i5 := R.i5
  K₀ := R.K₀
  hK₀n := R.hK₀n
  hK₀linear := R.hK₀linear
  t := R.t
  ε := R.ε
  htail := R.htail

/-! ## Slots 6, 7, and 8 -/

structure Phase6ReadyEscapeBudgetHypotheses
    (n : ℕ) (σ : Sign) (δ : ℝ≥0)
    (i6 : Fin (L + 1)) (K₀ : ℕ) where
  l : ℕ
  hl1 : 1 ≤ l
  hlL : l ≤ L
  hhgt : l - 1 < i6.val
  hhne : i6.val ≠ L
  ηCounter : ℝ≥0∞
  ηFloor : ℝ≥0∞
  hCounter :
    ∀ x,
      Phase678ReadySurvival.Phase6DrainReady
          (L := L) (K := K) n σ l hl1 hlL i6 K₀ x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n y}
        ≤ ηCounter
  hFloor :
    ∀ x,
      Phase678ReadySurvival.Phase6DrainReady
          (L := L) (K := K) n σ l hl1 hlL i6 K₀ x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ ReadyEscapeCounterTail.phase6Floors
            (L := L) (K := K) n σ l hl1 hlL i6 K₀ y}
        ≤ ηFloor
  escapeε : ℝ≥0
  hescε :
    ((DriftSurvival.driftHorizon (K₀ : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) 2 : ℕ) : ℝ≥0∞)
        * (ηCounter + ηFloor)
      ≤ (escapeε : ℝ≥0∞)
  hTotal :
    (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) + (escapeε : ℝ≥0∞)
      ≤ (δ : ℝ≥0∞)

noncomputable def phase6ReadyEscapeBound_of_hypotheses
    {n : ℕ} {σ : Sign} {δ : ℝ≥0} {i6 : Fin (L + 1)} {K₀ : ℕ}
    (_hn : 2 ≤ n)
    (R : Phase6ReadyEscapeBudgetHypotheses (L := L) (K := K) n σ δ i6 K₀) :
    Phase678ReadySurvival.Phase6ReadyEscapeBound
      (L := L) (K := K) n σ R.l R.hl1 R.hlL i6 K₀
      (R.ηCounter + R.ηFloor) :=
  ReadyEscapeCounterTail.phase6ReadyEscape_of_counterTail
    (L := L) (K := K)
    n σ R.l R.hl1 R.hlL i6 K₀ R.ηCounter R.ηFloor R.hCounter R.hFloor

structure Phase7BandEscapeBudgetHypotheses
    (n : ℕ) (σ : Sign) (l : ℕ) where
  E7 : ℕ
  hE7pos : 1 ≤ E7
  hE7top : 2 * E7 ≤ n * (n - 1)
  hE7linear : n ≤ 4 * E7
  η : ℝ≥0∞
  hesc : Phase7BandSurvival.Phase7BandEscapeBound
    (L := L) (K := K) n σ l E7 η
  escapeε : ℝ≥0
  hescε :
    ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
      ≤ (escapeε : ℝ≥0∞)
  hescape : escapeε ≤ DriftSurvival.driftBudgetNN 6 n

structure Phase8ReadyEscapeBudgetHypotheses
    (n : ℕ) (σ : Sign) (M₀ : ℕ) (δ : ℝ≥0) where
  E8 : ℕ
  ηCounter : ℝ≥0∞
  ηFloor : ℝ≥0∞
  hCounter :
    ∀ x,
      Phase678ReadySurvival.Phase8DrainReady
          (L := L) (K := K) n σ E8 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ PhaseOnlyWindows.Phase8Win (L := L) (K := K) n y}
        ≤ ηCounter
  hFloor :
    ∀ x,
      Phase678ReadySurvival.Phase8DrainReady
          (L := L) (K := K) n σ E8 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ ReadyEscapeCounterTail.phase8Floors
            (L := L) (K := K) n σ E8 y}
        ≤ ηFloor
  tWin : ℕ → ℕ
  drainε : ℝ≥0
  hDrain :
    (∑ m ∈ Finset.Icc 1 M₀,
      (DrainEngine.qHat E8 n m) ^ (tWin m) : ℝ≥0∞)
        ≤ (drainε : ℝ≥0∞)
  escapeε : ℝ≥0
  hescε :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞)
        * (ηCounter + ηFloor)
      ≤ (escapeε : ℝ≥0∞)
  hTotal :
    (drainε : ℝ≥0∞) + (escapeε : ℝ≥0∞) ≤ (δ : ℝ≥0∞)

noncomputable def phase8ReadyEscapeBound_of_hypotheses
    {n M₀ : ℕ} {σ : Sign} {δ : ℝ≥0} (_hn : 2 ≤ n)
    (R : Phase8ReadyEscapeBudgetHypotheses (L := L) (K := K) n σ M₀ δ) :
    Phase678ReadySurvival.Phase8ReadyEscapeBound
      (L := L) (K := K) n σ R.E8
      (R.ηCounter + R.ηFloor) :=
  ReadyEscapeCounterTail.phase8ReadyEscape_of_counterTail
    (L := L) (K := K)
    n σ R.E8 R.ηCounter R.ηFloor R.hCounter R.hFloor

/-- Package slot 8 with the `D`-divided drain calibration. -/
noncomputable def phase8ReadyEscapeBudgetHypotheses_of_dividedDrain
    {D n M₀ : ℕ} {σ : Sign} {δ : ℝ≥0}
    (hD1 : 1 ≤ D) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (E8 : ℕ) (tWin : ℕ → ℕ)
    (ηCounter ηFloor : ℝ≥0∞)
    (hCounter :
      ∀ x,
        Phase678ReadySurvival.Phase8DrainReady
            (L := L) (K := K) n σ E8 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ PhaseOnlyWindows.Phase8Win (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor :
      ∀ x,
        Phase678ReadySurvival.Phase8DrainReady
            (L := L) (K := K) n σ E8 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ ReadyEscapeCounterTail.phase8Floors
              (L := L) (K := K) n σ E8 y}
          ≤ ηFloor)
    (hpt : ∀ m ∈ Finset.Icc 1 M₀,
      (DrainEngine.qHat E8 n m) ^ (tWin m) ≤
        (DrainCalibration.budgetNN (D * M₀) n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε :
      (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞) *
          (ηCounter + ηFloor) ≤ (escapeε : ℝ≥0∞))
    (hTotal :
      ((Real.toNNReal (1 / ((D : ℝ) * (n : ℝ) ^ 2)) : ℝ≥0) : ℝ≥0∞) +
          (escapeε : ℝ≥0∞) ≤ (δ : ℝ≥0∞)) :
    Phase8ReadyEscapeBudgetHypotheses (L := L) (K := K) n σ M₀ δ where
  E8 := E8
  ηCounter := ηCounter
  ηFloor := ηFloor
  hCounter := hCounter
  hFloor := hFloor
  tWin := tWin
  drainε := Real.toNNReal (1 / ((D : ℝ) * (n : ℝ) ^ 2))
  hDrain := DrainEngine.qHat_sum_budget_div hD1 hn hM1 tWin hpt
  escapeε := escapeε
  hescε := hescε
  hTotal := hTotal

/-! ## Full concrete A producer -/

structure WorkTailProducerHypotheses (n : ℕ) where
  σ : Sign
  δ : ℝ≥0
  hδ : (δ : ℝ≥0∞) ≤ 1 / (n : ℝ≥0∞) ^ 2
  slot0 : Phase0RoleSplitBudgetHypotheses (L := L) (K := K) n
  slot1 : Phase1ReadyEscapeHypotheses (L := L) (K := K) n n δ
  slot3 : Phase3ConfinementTail.Phase3ConfinementHourHypotheses
    (L := L) (K := K) n
  slot5 : Phase5SampleEscapeHypotheses (L := L) (K := K) n
  /-- Slot 6 consumes exactly the hour and floor produced by slot 5. -/
  slot6 : Phase6ReadyEscapeBudgetHypotheses
    (L := L) (K := K) n σ δ slot5.i5 slot5.K₀
  slot7 : Phase7BandEscapeBudgetHypotheses
    (L := L) (K := K) n σ slot6.l
  slot8 : Phase8ReadyEscapeBudgetHypotheses (L := L) (K := K) n σ n δ
  k10 : ℕ

noncomputable def workFamilyTailData_of_hypotheses
    {n : ℕ} (hn : 2 ≤ n)
    (I : WorkTailProducerHypotheses (L := L) (K := K) n) :
    Phase035Work.WorkFamilyTailData (L := L) (K := K) n where
  σ := I.σ
  hn := hn
  δ := I.δ
  hδ := I.hδ
  slot0 := phase0RoleSplitTail_of_budget (L := L) (K := K) hn I.slot0
  slot3 :=
    Phase3ConfinementTail.phase3ConfinementTail_of_hours
      (L := L) (K := K) I.slot3
  slot5 := phase5C5aTail_of_hypotheses (L := L) (K := K) I.slot5
  P1 := I.slot1.P1
  tWin1 := I.slot1.tWin
  η1 := I.slot1.ηCounter + I.slot1.ηFloor
  hesc1 := phase1ReadyEscapeBound_of_hypotheses (L := L) (K := K) (M₀ := n) I.slot1
  drainε1 := I.slot1.drainε
  hDrain1 := I.slot1.hDrain
  escapeε1 := I.slot1.escapeε
  hescε1 := I.slot1.hescε
  hTotal1 := I.slot1.hTotal
  l := I.slot6.l
  hl1 := I.slot6.hl1
  hlL := I.slot6.hlL
  hhgt6 := I.slot6.hhgt
  hhne6 := I.slot6.hhne
  η6 := I.slot6.ηCounter + I.slot6.ηFloor
  hesc6 := phase6ReadyEscapeBound_of_hypotheses (L := L) (K := K) hn I.slot6
  escapeε6 := I.slot6.escapeε
  hescε6 := I.slot6.hescε
  hTotal6 := I.slot6.hTotal
  E7 := I.slot7.E7
  hE7pos := I.slot7.hE7pos
  hE7top := I.slot7.hE7top
  hE7linear := I.slot7.hE7linear
  η7 := I.slot7.η
  hesc7 := I.slot7.hesc
  escapeε7 := I.slot7.escapeε
  hescε7 := I.slot7.hescε
  hescape7 := I.slot7.hescape
  E8 := I.slot8.E8
  tWin8 := I.slot8.tWin
  η8 := I.slot8.ηCounter + I.slot8.ηFloor
  hesc8 := phase8ReadyEscapeBound_of_hypotheses (L := L) (K := K) (M₀ := n) hn I.slot8
  drainε8 := I.slot8.drainε
  hDrain8 := I.slot8.hDrain
  escapeε8 := I.slot8.escapeε
  hescε8 := I.slot8.hescε
  hTotal8 := I.slot8.hTotal
  k10 := I.k10

#print axioms phase0RoleSplitTail_of_budget
#print axioms phase1ReadyEscapeBound_of_hypotheses
#print axioms phase1ReadyEscapeHypotheses_of_dividedDrain
#print axioms phase5C5aTail_of_hypotheses
#print axioms phase6ReadyEscapeBound_of_hypotheses
#print axioms phase8ReadyEscapeBound_of_hypotheses
#print axioms phase8ReadyEscapeBudgetHypotheses_of_dividedDrain
#print axioms workFamilyTailData_of_hypotheses

end

end WorkTailProducers
end Ripple.PopulationProtocol.ExactMajority
