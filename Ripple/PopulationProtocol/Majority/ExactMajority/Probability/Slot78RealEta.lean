import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot78ReadyEscapeResidual
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FloorMasses

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Slot78RealEta

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

local instance instMeasurableSpaceAgentStatePair :
    MeasurableSpace (AgentState L K × AgentState L K) := ⊤

local instance instDiscreteMeasurableSpaceAgentStatePair :
    DiscreteMeasurableSpace (AgentState L K × AgentState L K) :=
  ⟨fun _ => trivial⟩

/-! ## A. Shared block-square residual -/

/--
The concrete ready-escape eta obtained from a small block of size/count at most
`A` in a population of size `n`.
-/
noncomputable def readyEscapeEta (A n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((A * A : ℕ) : ℝ) / (n * (n - 1) : ℝ))

/--
The one forced protocol sub-fact for real-eta slot-7/slot-8 ready escape.

`Ready` is the slot ready predicate; `Bad x` is the set of bad scheduled pairs
from `x`.  The hypothesis supplies a block `block x` such that all bad pairs lie
in `block x × block x`, and the block count is at most `A`.
-/
structure ReadyEscapeBlockHyp
    (Ready : Config (AgentState L K) → Prop)
    (Bad : Config (AgentState L K) → Set (AgentState L K × AgentState L K))
    (A n : ℕ) where
  block : Config (AgentState L K) → Finset (AgentState L K)
  contain :
    ∀ x, Ready x →
      Bad x ⊆ {pr | pr.1 ∈ block x ∧ pr.2 ∈ block x}
  block_le :
    ∀ x, Ready x →
      ∑ a ∈ block x, x.count a ≤ A
  A_le_n : A ≤ n

/--
Generic death-rectangle counting lemma for a ready-escape bad-pair residual.

This is the reusable core for slots 7 and 8.
-/
theorem badPairMass_le_of_blockHyp
    {Ready : Config (AgentState L K) → Prop}
    {Bad : Config (AgentState L K) → Set (AgentState L K × AgentState L K)}
    {A n : ℕ}
    (hn : 2 ≤ n)
    (H : ReadyEscapeBlockHyp (L := L) (K := K) Ready Bad A n)
    (hcard : ∀ x, Ready x → x.card = n) :
    ∀ x,
      Ready x →
      ∀ hxcard : 2 ≤ x.card,
        (x.interactionPMF hxcard).toMeasure (Bad x)
          ≤ readyEscapeEta A n := by
  intro x hxReady hxcard
  calc
    (x.interactionPMF hxcard).toMeasure (Bad x)
        ≤ (x.interactionPMF hxcard).toMeasure
            {pr | pr.1 ∈ H.block x ∧ pr.2 ∈ H.block x} :=
          measure_mono (H.contain x hxReady)
    _ ≤ ENNReal.ofReal
          ((((∑ m ∈ H.block x, x.count m : ℕ) : ℝ) / (x.card : ℝ)) ^ 2) :=
          FloorMasses.block_pair_prob_le_sq (L := L) (K := K) x hxcard (H.block x)
    _ ≤ readyEscapeEta A n := by
          rw [hcard x hxReady]
          simpa [readyEscapeEta] using
            ENNReal.ofReal_le_ofReal
              (FloorMasses.pair_block_sq_le_buffer
                (∑ m ∈ H.block x, x.count m) A n
                (H.block_le x hxReady) H.A_le_n hn)

/-! ## B. Slot 7 real-eta residual and atom -/

/-- Slot-7 ready predicate abbreviation. -/
abbrev Slot7Ready
    (n : ℕ) (σ : Sign) (E7 : ℕ)
    (x : Config (AgentState L K)) : Prop :=
  Slot678SurvivalInputs.Phase7DrainReady
    (L := L) (K := K) n σ E7 x

/-- The slot-7 instance of the one forced block-square sub-fact. -/
abbrev Slot7ReadyEscapeBlockHyp
    (n : ℕ) (σ : Sign) (E7 A7 : ℕ) :=
  ReadyEscapeBlockHyp
    (L := L) (K := K)
    (Slot7Ready (L := L) (K := K) n σ E7)
    (fun x =>
      Slot78ReadyEscapeResidual.slot7BadReadyPairs
        (L := L) (K := K) n σ E7 x)
    A7 n

/--
Construct the slot-7 scheduler bad-pair residual with paper-scale eta.
-/
theorem slot7ReadyEscapeResidual_of_blockHyp
    {n : ℕ} (σ : Sign) (E7 A7 : ℕ) (hn : 2 ≤ n)
    (H : Slot7ReadyEscapeBlockHyp (L := L) (K := K) n σ E7 A7) :
    Slot78ReadyEscapeResidual.Slot7ReadyEscapeResidual
      (L := L) (K := K) n σ E7 (readyEscapeEta A7 n) where
  badPairMass_le := by
    exact
      badPairMass_le_of_blockHyp
        (L := L) (K := K)
        (A := A7) (n := n) hn H
        (fun x hx => hx.honest.1)

/--
Direct kernel form for slot 7, using
`FloorMasses.stepDist_toMeasure_eq_preimage`.
-/
theorem slot7_ready_escape_kernel_le_of_blockHyp
    {n : ℕ} (σ : Sign) (E7 A7 : ℕ) (hn : 2 ≤ n)
    (H : Slot7ReadyEscapeBlockHyp (L := L) (K := K) n σ E7 A7) :
    ∀ x,
      Slot678SurvivalInputs.Phase7DrainReady
        (L := L) (K := K) n σ E7 x →
      (NonuniformMajority L K).transitionKernel x
        {y |
          ¬ Slot678SurvivalInputs.Phase7DrainReady
            (L := L) (K := K) n σ E7 y}
        ≤ readyEscapeEta A7 n := by
  intro x hxReady
  change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
    {y : Config (AgentState L K) |
      ¬ Slot678SurvivalInputs.Phase7DrainReady
        (L := L) (K := K) n σ E7 y}
    ≤ readyEscapeEta A7 n
  by_cases hxcard : 2 ≤ x.card
  · rw [FloorMasses.stepDist_toMeasure_eq_preimage
        (L := L) (K := K) x hxcard
        ({y : Config (AgentState L K) |
          ¬ Slot678SurvivalInputs.Phase7DrainReady
            (L := L) (K := K) n σ E7 y})]
    simpa [Slot78ReadyEscapeResidual.slot7BadReadyPairs] using
      (slot7ReadyEscapeResidual_of_blockHyp
        (L := L) (K := K) σ E7 A7 hn H).badPairMass_le x hxReady hxcard
  · have hpure :
        (NonuniformMajority L K).stepDistOrSelf x = PMF.pure x := by
      unfold Protocol.stepDistOrSelf
      rw [dif_neg hxcard]
    have hbad_meas :
        MeasurableSet
          {y : Config (AgentState L K) |
            ¬ Slot678SurvivalInputs.Phase7DrainReady
              (L := L) (K := K) n σ E7 y} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    rw [hpure]
    have hzero :
        (PMF.pure x).toMeasure
          {y : Config (AgentState L K) |
            ¬ Slot678SurvivalInputs.Phase7DrainReady
              (L := L) (K := K) n σ E7 y}
          = 0 := by
      rw [PMF.toMeasure_apply_eq_zero_iff _ hbad_meas]
      rw [Set.disjoint_left]
      intro y hy hbad
      rw [PMF.mem_support_pure_iff] at hy
      subst y
      exact hbad hxReady
    rw [hzero]
    exact zero_le'

/--
Construct the public slot-7 ready-escape atom with paper-scale eta.
-/
theorem slot7ReadyEscapeAtom_of_residual
    {n : ℕ} (σ : Sign) (E7 A7 : ℕ) (hn : 2 ≤ n)
    (H : Slot7ReadyEscapeBlockHyp (L := L) (K := K) n σ E7 A7) :
    Slot678SurvivalInputs.Slot7ReadyEscapeAtom
      (L := L) (K := K) n σ E7 (readyEscapeEta A7 n) where
  hesc := slot7_ready_escape_kernel_le_of_blockHyp
    (L := L) (K := K) σ E7 A7 hn H

/--
Slot-7 survival on the strengthened ready gate, packaged from the real-eta
block residual.
-/
noncomputable def slot7SurvivalReady_of_residual
    {n : ℕ} (σ : Sign) (E7 A7 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (H : Slot7ReadyEscapeBlockHyp (L := L) (K := K) n σ E7 A7)
    (tWin7 : ℕ → ℕ)
    (hpt7 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E7 n m) ^ (tWin7 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞)
        * readyEscapeEta A7 n ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Slot678SurvivalInputs.slot7SurvivalReady
    (L := L) (K := K)
    σ E7 M₀ hn hM1
    (readyEscapeEta A7 n)
    (slot7ReadyEscapeAtom_of_residual
      (L := L) (K := K) σ E7 A7 hn H)
    tWin7 hpt7 escapeε hescε

/--
Survival-factor helper specialised to slot-7 bad-pair probabilities.
This reuses the slot-6 arithmetic helper on the interaction-PMF probability.
-/
theorem slot7_survivalFactor_of_badPairs
    {n : ℕ} (σ : Sign) (E7 : ℕ)
    (x : Config (AgentState L K)) (hxcard : 2 ≤ x.card)
    (s E : ℝ) (hs : 0 ≤ s) (hE : 0 ≤ E) :
    ENNReal.ofReal
        ((1 - ((x.interactionPMF hxcard).toMeasure
              (Slot78ReadyEscapeResidual.slot7BadReadyPairs
                (L := L) (K := K) n σ E7 x)).toReal
            * (1 - Real.exp (-s))) * E)
      =
    ENNReal.ofReal
        (1 - ((x.interactionPMF hxcard).toMeasure
              (Slot78ReadyEscapeResidual.slot7BadReadyPairs
                (L := L) (K := K) n σ E7 x)).toReal
            * (1 - Real.exp (-s)))
      * ENNReal.ofReal E := by
  haveI : IsProbabilityMeasure ((x.interactionPMF hxcard).toMeasure) :=
    PMF.toMeasure.isProbabilityMeasure _
  exact
    Slot6ReadyEscapeResidual.survivalFactor_ofReal_mul_prob_toReal
      ((x.interactionPMF hxcard).toMeasure)
      (Slot78ReadyEscapeResidual.slot7BadReadyPairs
        (L := L) (K := K) n σ E7 x)
      s E hs hE

/-! ## C. Slot 8 real-eta residual and atom -/

/-- Slot-8 ready predicate abbreviation. -/
abbrev Slot8Ready
    (n : ℕ) (σ : Sign) (E8 : ℕ)
    (x : Config (AgentState L K)) : Prop :=
  Slot678SurvivalInputs.Phase8DrainReady
    (L := L) (K := K) n σ E8 x

/-- The slot-8 instance of the one forced block-square sub-fact. -/
abbrev Slot8ReadyEscapeBlockHyp
    (n : ℕ) (σ : Sign) (E8 A8 : ℕ) :=
  ReadyEscapeBlockHyp
    (L := L) (K := K)
    (Slot8Ready (L := L) (K := K) n σ E8)
    (fun x =>
      Slot78ReadyEscapeResidual.slot8BadReadyPairs
        (L := L) (K := K) n σ E8 x)
    A8 n

/--
Construct the slot-8 scheduler bad-pair residual with paper-scale eta.
-/
theorem slot8ReadyEscapeResidual_of_blockHyp
    {n : ℕ} (σ : Sign) (E8 A8 : ℕ) (hn : 2 ≤ n)
    (H : Slot8ReadyEscapeBlockHyp (L := L) (K := K) n σ E8 A8) :
    Slot78ReadyEscapeResidual.Slot8ReadyEscapeResidual
      (L := L) (K := K) n σ E8 (readyEscapeEta A8 n) where
  badPairMass_le := by
    exact
      badPairMass_le_of_blockHyp
        (L := L) (K := K)
        (A := A8) (n := n) hn H
        (fun x hx => hx.honest.1)

/--
Direct kernel form for slot 8, using
`FloorMasses.stepDist_toMeasure_eq_preimage`.
-/
theorem slot8_ready_escape_kernel_le_of_blockHyp
    {n : ℕ} (σ : Sign) (E8 A8 : ℕ) (hn : 2 ≤ n)
    (H : Slot8ReadyEscapeBlockHyp (L := L) (K := K) n σ E8 A8) :
    ∀ x,
      Slot678SurvivalInputs.Phase8DrainReady
        (L := L) (K := K) n σ E8 x →
      (NonuniformMajority L K).transitionKernel x
        {y |
          ¬ Slot678SurvivalInputs.Phase8DrainReady
            (L := L) (K := K) n σ E8 y}
        ≤ readyEscapeEta A8 n := by
  intro x hxReady
  change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
    {y : Config (AgentState L K) |
      ¬ Slot678SurvivalInputs.Phase8DrainReady
        (L := L) (K := K) n σ E8 y}
    ≤ readyEscapeEta A8 n
  by_cases hxcard : 2 ≤ x.card
  · rw [FloorMasses.stepDist_toMeasure_eq_preimage
        (L := L) (K := K) x hxcard
        ({y : Config (AgentState L K) |
          ¬ Slot678SurvivalInputs.Phase8DrainReady
            (L := L) (K := K) n σ E8 y})]
    simpa [Slot78ReadyEscapeResidual.slot8BadReadyPairs] using
      (slot8ReadyEscapeResidual_of_blockHyp
        (L := L) (K := K) σ E8 A8 hn H).badPairMass_le x hxReady hxcard
  · have hpure :
        (NonuniformMajority L K).stepDistOrSelf x = PMF.pure x := by
      unfold Protocol.stepDistOrSelf
      rw [dif_neg hxcard]
    have hbad_meas :
        MeasurableSet
          {y : Config (AgentState L K) |
            ¬ Slot678SurvivalInputs.Phase8DrainReady
              (L := L) (K := K) n σ E8 y} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    rw [hpure]
    have hzero :
        (PMF.pure x).toMeasure
          {y : Config (AgentState L K) |
            ¬ Slot678SurvivalInputs.Phase8DrainReady
              (L := L) (K := K) n σ E8 y}
          = 0 := by
      rw [PMF.toMeasure_apply_eq_zero_iff _ hbad_meas]
      rw [Set.disjoint_left]
      intro y hy hbad
      rw [PMF.mem_support_pure_iff] at hy
      subst y
      exact hbad hxReady
    rw [hzero]
    exact zero_le'

/--
Construct the public slot-8 ready-escape atom with paper-scale eta.
-/
theorem slot8ReadyEscapeAtom_of_residual
    {n : ℕ} (σ : Sign) (E8 A8 : ℕ) (hn : 2 ≤ n)
    (H : Slot8ReadyEscapeBlockHyp (L := L) (K := K) n σ E8 A8) :
    Slot678SurvivalInputs.Slot8ReadyEscapeAtom
      (L := L) (K := K) n σ E8 (readyEscapeEta A8 n) where
  hesc := slot8_ready_escape_kernel_le_of_blockHyp
    (L := L) (K := K) σ E8 A8 hn H

/--
Slot-8 survival on the strengthened ready gate, packaged from the real-eta
block residual.
-/
noncomputable def slot8SurvivalReady_of_residual
    {n : ℕ} (σ : Sign) (E8 A8 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (H : Slot8ReadyEscapeBlockHyp (L := L) (K := K) n σ E8 A8)
    (tWin8 : ℕ → ℕ)
    (hpt8 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E8 n m) ^ (tWin8 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞)
        * readyEscapeEta A8 n ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Slot678SurvivalInputs.slot8SurvivalReady
    (L := L) (K := K)
    σ E8 M₀ hn hM1
    (readyEscapeEta A8 n)
    (slot8ReadyEscapeAtom_of_residual
      (L := L) (K := K) σ E8 A8 hn H)
    tWin8 hpt8 escapeε hescε

/--
Survival-factor helper specialised to slot-8 bad-pair probabilities.
This reuses the slot-6 arithmetic helper on the interaction-PMF probability.
-/
theorem slot8_survivalFactor_of_badPairs
    {n : ℕ} (σ : Sign) (E8 : ℕ)
    (x : Config (AgentState L K)) (hxcard : 2 ≤ x.card)
    (s E : ℝ) (hs : 0 ≤ s) (hE : 0 ≤ E) :
    ENNReal.ofReal
        ((1 - ((x.interactionPMF hxcard).toMeasure
              (Slot78ReadyEscapeResidual.slot8BadReadyPairs
                (L := L) (K := K) n σ E8 x)).toReal
            * (1 - Real.exp (-s))) * E)
      =
    ENNReal.ofReal
        (1 - ((x.interactionPMF hxcard).toMeasure
              (Slot78ReadyEscapeResidual.slot8BadReadyPairs
                (L := L) (K := K) n σ E8 x)).toReal
            * (1 - Real.exp (-s)))
      * ENNReal.ofReal E := by
  haveI : IsProbabilityMeasure ((x.interactionPMF hxcard).toMeasure) :=
    PMF.toMeasure.isProbabilityMeasure _
  exact
    Slot6ReadyEscapeResidual.survivalFactor_ofReal_mul_prob_toReal
      ((x.interactionPMF hxcard).toMeasure)
      (Slot78ReadyEscapeResidual.slot8BadReadyPairs
        (L := L) (K := K) n σ E8 x)
      s E hs hE

#print axioms readyEscapeEta
#print axioms badPairMass_le_of_blockHyp
#print axioms slot7ReadyEscapeResidual_of_blockHyp
#print axioms slot7_ready_escape_kernel_le_of_blockHyp
#print axioms slot7ReadyEscapeAtom_of_residual
#print axioms slot7SurvivalReady_of_residual
#print axioms slot7_survivalFactor_of_badPairs
#print axioms slot8ReadyEscapeResidual_of_blockHyp
#print axioms slot8_ready_escape_kernel_le_of_blockHyp
#print axioms slot8ReadyEscapeAtom_of_residual
#print axioms slot8SurvivalReady_of_residual
#print axioms slot8_survivalFactor_of_badPairs

end Slot78RealEta

end ExactMajority
