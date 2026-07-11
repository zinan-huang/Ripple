import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot035Expose
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WorkConstructed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TransitionClockPairBound
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.UniformRoleSplitMilestone
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot3ConfinementTailDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReadyEscapeCounterTail
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot6Containment
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot78RealEta
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase10SignResolved

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace SlotProducers

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Regime-closed epidemic slots 2, 4, and 9 -/

noncomputable def slot4ScalarFitConcrete
    {n : ℕ} (hn : 2 ≤ n) :
    WorkBuilder.Slot4ScalarFit n where
  s := 1
  hs := by norm_num
  t := WorkConstructed.epiHorizon n
  ε := Real.toNNReal (1 / (n : ℝ) ^ 2)
  hε := WorkConstructed.epi_budget_fit n hn

noncomputable def slot2OpinionInputsConcrete
    {n : ℕ} (hn : 2 ≤ n) :
    WorkBuilder.Slot2OpinionInputs n where
  U := WorkConstructed.opU
  v := WorkConstructed.opV
  hUsign := WorkConstructed.opU_singleSign
  hvsign := WorkConstructed.opV_singleSign
  hvU := WorkConstructed.op_vU
  hUv := WorkConstructed.op_Uv
  hvv := WorkConstructed.op_vv
  hUU := WorkConstructed.op_UU
  hUv_ne := WorkConstructed.op_Uv_ne
  s := 1
  hs := by norm_num
  t := WorkConstructed.epiHorizon n
  ε := Real.toNNReal (1 / (n : ℝ) ^ 2)
  hε := WorkConstructed.epi_budget_fit n hn

noncomputable def slot9OpinionInputsConcrete
    {n : ℕ} (hn : 2 ≤ n) :
    WorkFromSlots.Slot9OpinionInputs n :=
  slot2OpinionInputsConcrete (n := n) hn

/-! ## Slot 0 -/

structure Slot0RoleSplitBudgetResidual (n : ℕ) where
  η : ℝ
  U : RoleSplitConcentration.UniformRoleSplitMilestone (L := L) (K := K) η n
  hWindowTime : U.tRole ≤ n * (L + 1)
  hSlotTime : U.tRole ≤ 17 * n * (L + 1)
  hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)
  ε : ℝ≥0
  hε :
    Slot0HtailAssembly.slot0TailBudgetENN L n U.tRole ≤ (ε : ℝ≥0∞)

noncomputable def slot0RoleSplitTailConcrete
    {n : ℕ} (hn : 2 ≤ n)
    (R : Slot0RoleSplitBudgetResidual (L := L) (K := K) n) :
    WorkConcreteSlots.Slot0RoleSplitTail (L := L) (K := K) n :=
  Slot0HtailAssembly.slot0RoleSplitTail_of_prefixTail
    (L := L) (K := K)
    (by omega : 1 ≤ n)
    R.U
    (TransitionClockPairBound.phase0ClockZeroPrefixTail_unconditional
      (L := L) (K := K)
      (by omega : 1 ≤ n) R.hWindowTime R.hlog)
    R.ε R.hε R.hSlotTime

/-! ## Slot 1 -/

structure Slot1ReadyEscapeResidual (n M₀ : ℕ) where
  P1 : ℕ
  tWin : ℕ → ℕ
  ηCounter : ℝ≥0∞
  ηFloor : ℝ≥0∞
  hCounter :
    ∀ x,
      Slot1SurvivalInputs.Phase1DrainReady (L := L) (K := K) n P1 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ HonestWindows.Phase1Honest (L := L) (K := K) n y}
        ≤ ηCounter
  hFloor :
    ∀ x,
      Slot1SurvivalInputs.Phase1DrainReady (L := L) (K := K) n P1 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ ReadyEscapeCounterTail.phase1Floors (L := L) (K := K) n P1 y}
        ≤ ηFloor
  hpt :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat P1 n m) ^ (tWin m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε : ℝ≥0
  hescε :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞)
        * (ηCounter + ηFloor)
      ≤ (escapeε : ℝ≥0∞)

noncomputable def slot1ReadyEscapeAtomConcrete
    {n M₀ : ℕ} (R : Slot1ReadyEscapeResidual (L := L) (K := K) n M₀) :
    Slot1SurvivalInputs.Slot1ReadyEscapeAtom
      (L := L) (K := K) n R.P1 (R.ηCounter + R.ηFloor) :=
  ReadyEscapeCounterTail.slot1ReadyEscape_of_counterTail
    (L := L) (K := K)
    n R.P1 R.ηCounter R.ηFloor R.hCounter R.hFloor

/-! ## Slot 5 -/

structure Slot5SampleEscapeResidual (n : ℕ) where
  i5 : Fin (L + 1)
  K₀ : ℕ
  t : ℕ
  ε : ℝ≥0
  htail :
    ∀ c₀,
      SeamEpidemics.allPhaseEq (L := L) (K := K) 5 n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬
          (SeamEpidemics.allPhaseEq (L := L) (K := K) 5 n c ∧
            Phase5Convergence.ReserveSampleGood
              (L := L) (K := K) i5 K₀ c)}
        ≤ (ε : ℝ≥0∞)

noncomputable def slot5C5aTailConcrete
    {n : ℕ} (R : Slot5SampleEscapeResidual (L := L) (K := K) n) :
    WorkConcreteSlots.Slot5C5aTail (L := L) (K := K) n where
  i5 := R.i5
  K₀ := R.K₀
  t := R.t
  ε := R.ε
  htail := R.htail

/-! ## Slots 6, 7, and 8 -/

structure Slot6ReadyEscapeBudgetResidual
    (n : ℕ) (σ : Sign) (M₀ : ℕ) where
  l : ℕ
  hl1 : 1 ≤ l
  hlL : l ≤ L
  i6 : Fin (L + 1)
  K₀ : ℕ
  hhgt : l - 1 < i6.val
  hhne : i6.val ≠ L
  ηCounter : ℝ≥0∞
  ηFloor : ℝ≥0∞
  hCounter :
    ∀ x,
      Slot678SurvivalInputs.Phase6DrainReady
          (L := L) (K := K) n σ l hl1 hlL i6 K₀ x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n y}
        ≤ ηCounter
  hFloor :
    ∀ x,
      Slot678SurvivalInputs.Phase6DrainReady
          (L := L) (K := K) n σ l hl1 hlL i6 K₀ x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ ReadyEscapeCounterTail.phase6Floors
            (L := L) (K := K) n σ l hl1 hlL i6 K₀ y}
        ≤ ηFloor
  tWin : ℕ → ℕ
  hpt :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat K₀ n m) ^ (tWin m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε : ℝ≥0
  hescε :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞)
        * (ηCounter + ηFloor)
      ≤ (escapeε : ℝ≥0∞)

noncomputable def slot6ReadyEscapeAtomConcrete
    {n M₀ : ℕ} {σ : Sign} (_hn : 2 ≤ n)
    (R : Slot6ReadyEscapeBudgetResidual (L := L) (K := K) n σ M₀) :
    Slot678SurvivalInputs.Slot6ReadyEscapeAtom
      (L := L) (K := K) n σ R.l R.hl1 R.hlL R.i6 R.K₀
      (R.ηCounter + R.ηFloor) :=
  ReadyEscapeCounterTail.slot6ReadyEscape_of_counterTail
    (L := L) (K := K)
    n σ R.l R.hl1 R.hlL R.i6 R.K₀ R.ηCounter R.ηFloor R.hCounter R.hFloor

structure Slot7ReadyEscapeBudgetResidual
    (n : ℕ) (σ : Sign) (M₀ : ℕ) where
  E7 : ℕ
  ηCounter : ℝ≥0∞
  ηFloor : ℝ≥0∞
  hCounter :
    ∀ x,
      Slot678SurvivalInputs.Phase7DrainReady
          (L := L) (K := K) n σ E7 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ HonestWindows.Phase7Honest (L := L) (K := K) n y}
        ≤ ηCounter
  hFloor :
    ∀ x,
      Slot678SurvivalInputs.Phase7DrainReady
          (L := L) (K := K) n σ E7 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ ReadyEscapeCounterTail.phase7Floors
            (L := L) (K := K) n σ E7 y}
        ≤ ηFloor
  tWin : ℕ → ℕ
  hpt :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E7 n m) ^ (tWin m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε : ℝ≥0
  hescε :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞)
        * (ηCounter + ηFloor)
      ≤ (escapeε : ℝ≥0∞)

noncomputable def slot7ReadyEscapeAtomConcrete
    {n M₀ : ℕ} {σ : Sign} (_hn : 2 ≤ n)
    (R : Slot7ReadyEscapeBudgetResidual (L := L) (K := K) n σ M₀) :
    Slot678SurvivalInputs.Slot7ReadyEscapeAtom
      (L := L) (K := K) n σ R.E7
      (R.ηCounter + R.ηFloor) :=
  ReadyEscapeCounterTail.slot7ReadyEscape_of_counterTail
    (L := L) (K := K)
    n σ R.E7 R.ηCounter R.ηFloor R.hCounter R.hFloor

structure Slot8ReadyEscapeBudgetResidual
    (n : ℕ) (σ : Sign) (M₀ : ℕ) where
  E8 : ℕ
  ηCounter : ℝ≥0∞
  ηFloor : ℝ≥0∞
  hCounter :
    ∀ x,
      Slot678SurvivalInputs.Phase8DrainReady
          (L := L) (K := K) n σ E8 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ HonestWindows.Phase8Honest (L := L) (K := K) n y}
        ≤ ηCounter
  hFloor :
    ∀ x,
      Slot678SurvivalInputs.Phase8DrainReady
          (L := L) (K := K) n σ E8 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ ReadyEscapeCounterTail.phase8Floors
            (L := L) (K := K) n σ E8 y}
        ≤ ηFloor
  tWin : ℕ → ℕ
  hpt :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E8 n m) ^ (tWin m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε : ℝ≥0
  hescε :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞)
        * (ηCounter + ηFloor)
      ≤ (escapeε : ℝ≥0∞)

noncomputable def slot8ReadyEscapeAtomConcrete
    {n M₀ : ℕ} {σ : Sign} (_hn : 2 ≤ n)
    (R : Slot8ReadyEscapeBudgetResidual (L := L) (K := K) n σ M₀) :
    Slot678SurvivalInputs.Slot8ReadyEscapeAtom
      (L := L) (K := K) n σ R.E8
      (R.ηCounter + R.ηFloor) :=
  ReadyEscapeCounterTail.slot8ReadyEscape_of_counterTail
    (L := L) (K := K)
    n σ R.E8 R.ηCounter R.ηFloor R.hCounter R.hFloor

/-! ## Full concrete A producer -/

structure ConcreteAProducerInputs (n : ℕ) where
  σ : Sign
  M₀ : ℕ
  hM1 : 1 ≤ M₀
  slot0 : Slot0RoleSplitBudgetResidual (L := L) (K := K) n
  slot1 : Slot1ReadyEscapeResidual (L := L) (K := K) n M₀
  slot3 : Slot3ConfinementTailDischarge.Slot3ConfinementHourInputs
    (L := L) (K := K) n
  slot5 : Slot5SampleEscapeResidual (L := L) (K := K) n
  slot6 : Slot6ReadyEscapeBudgetResidual (L := L) (K := K) n σ M₀
  slot7 : Slot7ReadyEscapeBudgetResidual (L := L) (K := K) n σ M₀
  slot8 : Slot8ReadyEscapeBudgetResidual (L := L) (K := K) n σ M₀
  k10 : ℕ

noncomputable def slotInputsConcrete
    {n : ℕ} (hn : 2 ≤ n)
    (I : ConcreteAProducerInputs (L := L) (K := K) n) :
    WorkConcreteSlots.SlotInputsConcrete (L := L) (K := K) n where
  σ := I.σ
  M₀ := I.M₀
  hn := hn
  hM1 := I.hM1
  slot0 := slot0RoleSplitTailConcrete (L := L) (K := K) hn I.slot0
  slot2 := slot2OpinionInputsConcrete (n := n) hn
  slot3 :=
    Slot3ConfinementTailDischarge.slot3ConfinementTail_concrete
      (L := L) (K := K) I.slot3
  slot4 := slot4ScalarFitConcrete (n := n) hn
  slot5 := slot5C5aTailConcrete (L := L) (K := K) I.slot5
  P1 := I.slot1.P1
  tWin1 := I.slot1.tWin
  η1 := I.slot1.ηCounter + I.slot1.ηFloor
  hesc1 := slot1ReadyEscapeAtomConcrete (L := L) (K := K) (M₀ := I.M₀) I.slot1
  hpt1 := I.slot1.hpt
  escapeε1 := I.slot1.escapeε
  hescε1 := I.slot1.hescε
  l := I.slot6.l
  hl1 := I.slot6.hl1
  hlL := I.slot6.hlL
  i6 := I.slot6.i6
  K₀6 := I.slot6.K₀
  hhgt6 := I.slot6.hhgt
  hhne6 := I.slot6.hhne
  tWin6 := I.slot6.tWin
  η6 := I.slot6.ηCounter + I.slot6.ηFloor
  hesc6 := slot6ReadyEscapeAtomConcrete (L := L) (K := K) hn I.slot6
  hpt6 := I.slot6.hpt
  escapeε6 := I.slot6.escapeε
  hescε6 := I.slot6.hescε
  E7 := I.slot7.E7
  tWin7 := I.slot7.tWin
  η7 := I.slot7.ηCounter + I.slot7.ηFloor
  hesc7 := slot7ReadyEscapeAtomConcrete (L := L) (K := K) hn I.slot7
  hpt7 := I.slot7.hpt
  escapeε7 := I.slot7.escapeε
  hescε7 := I.slot7.hescε
  E8 := I.slot8.E8
  tWin8 := I.slot8.tWin
  η8 := I.slot8.ηCounter + I.slot8.ηFloor
  hesc8 := slot8ReadyEscapeAtomConcrete (L := L) (K := K) hn I.slot8
  hpt8 := I.slot8.hpt
  escapeε8 := I.slot8.escapeε
  hescε8 := I.slot8.hescε
  slot9 := slot9OpinionInputsConcrete (n := n) hn
  k10 := I.k10

#print axioms slot4ScalarFitConcrete
#print axioms slot2OpinionInputsConcrete
#print axioms slot9OpinionInputsConcrete
#print axioms slot0RoleSplitTailConcrete
#print axioms slot1ReadyEscapeAtomConcrete
#print axioms slot5C5aTailConcrete
#print axioms slot6ReadyEscapeAtomConcrete
#print axioms slot7ReadyEscapeAtomConcrete
#print axioms slot8ReadyEscapeAtomConcrete
#print axioms slotInputsConcrete

end

end SlotProducers
end ExactMajority
