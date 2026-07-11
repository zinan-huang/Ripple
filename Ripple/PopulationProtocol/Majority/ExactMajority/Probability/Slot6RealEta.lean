import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot6ReadyEscapeResidual
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FloorMasses

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Slot6RealEta

A paper-scale slot-6 ready-escape residual from a bad-pair rectangle.

The trivial fallback in `Slot6ReadyEscapeResidual` gives `η = 1`.  This file
proves the reusable rectangle-counting reduction:

* define the exact bad-pair participant block for a source configuration `x`;
* prove, definitionally, that every scheduled pair whose output leaves
  `Phase6DrainReady` lies in the square of that block;
* use the landed FloorMasses rectangle route:
  `stepDist_toMeasure_eq_preimage`,
  `block_pair_prob_le_sq`,
  `pair_block_sq_le_buffer`;
* package the resulting `Slot6ReadyEscapeResidual` at
  `η = ofReal (B^2 / (n * (n - 1)))`.

The only named paper-scale input left is `Slot6BadPairBlockBound`: a uniform
bound saying that the exact bad-pair participant block has count at most `B`
on every slot-6 ready source.  This is the protocol/counting fact that identifies
which concrete interactions can break the ready gate and proves that their
participant block is small.
-/

namespace ExactMajority
namespace Slot6RealEta

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- Abbreviation for the slot-6 ready gate. -/
abbrev Ready6
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  Slot678SurvivalInputs.Phase6DrainReady
    (L := L) (K := K) n σ l hl1 hlL i K₀ c

/-- The bad output event for the slot-6 ready gate. -/
abbrev BadReady6
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) :
    Set (Config (AgentState L K)) :=
  {y |
    ¬ Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ y}

/--
The exact bad-pair participant block at a source configuration `x`.

An agent state `a` is in the block if it can participate, in either coordinate,
in some scheduled ordered pair whose output leaves the slot-6 ready gate.

This is deliberately defined from the real scheduled transition.  Therefore the
preimage containment into `slot6BadPairBlock × slot6BadPairBlock` is a theorem,
not a carried hypothesis.
-/
noncomputable def slot6BadPairBlock
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (x : Config (AgentState L K)) :
    Finset (AgentState L K) :=
  Finset.univ.filter
    (fun a : AgentState L K =>
      ∃ b : AgentState L K,
        (¬ Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀
          ((NonuniformMajority L K).scheduledStep x (a, b))) ∨
        (¬ Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀
          ((NonuniformMajority L K).scheduledStep x (b, a))))

/--
Every scheduled pair whose output leaves the slot-6 ready gate is contained in
the square of the exact bad-pair participant block.
-/
theorem slot6_escape_preimage_subset_badPairBlock_square
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (x : Config (AgentState L K)) :
    ((NonuniformMajority L K).scheduledStep x ⁻¹'
        BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀)
      ⊆
    {pr : AgentState L K × AgentState L K |
      pr.1 ∈ slot6BadPairBlock
        (L := L) (K := K) n σ l hl1 hlL i K₀ x ∧
      pr.2 ∈ slot6BadPairBlock
        (L := L) (K := K) n σ l hl1 hlL i K₀ x} := by
  classical
  rintro ⟨a, b⟩ hbad
  constructor
  · unfold slot6BadPairBlock
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨b, Or.inl hbad⟩
  · unfold slot6BadPairBlock
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, Or.inr hbad⟩

/--
The single named paper-scale bad-block input.

`hblock` is the genuine protocol/counting fact: on every slot-6 ready source,
the exact set of agents that can participate in a ready-breaking scheduled pair
has total multiplicity at most `B`.

The `hcard` field is included so this adapter does not depend on how
`Phase6Win` exposes its cardinality conjunct.
-/
structure Slot6BadPairBlockBound
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (B : ℕ) : Prop where
  hcard :
    ∀ x,
      Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ x →
      x.card = n
  hblock :
    ∀ x,
      Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ x →
      (∑ a ∈ slot6BadPairBlock
          (L := L) (K := K) n σ l hl1 hlL i K₀ x, x.count a) ≤ B

/-- The paper-scale rectangle budget for the slot-6 ready escape block. -/
noncomputable def slot6BadBlockEta (B n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((B * B : ℕ) : ℝ) / (n * (n - 1) : ℝ))

/--
One-step escape from `Phase6DrainReady` is bounded by the bad-block rectangle.

This is the core rectangle-counting proof:
`stepDist_toMeasure_eq_preimage` turns the kernel event into an interaction
preimage, the bad-pair block containment puts that preimage inside a block
square, and `block_pair_prob_le_sq` + `pair_block_sq_le_buffer` give the
calibrated `B²/(n(n−1))` budget.
-/
theorem slot6_ready_escape_mass_le_badBlockEta
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (B : ℕ)
    (hn2 : 2 ≤ n) (hB : B ≤ n)
    (H : Slot6BadPairBlockBound
      (L := L) (K := K) n σ l hl1 hlL i K₀ B)
    (x : Config (AgentState L K))
    (hx : Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ x) :
    (NonuniformMajority L K).transitionKernel x
      (BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀)
      ≤ slot6BadBlockEta B n := by
  classical
  have hcard : x.card = n := H.hcard x hx
  have hx2 : 2 ≤ x.card := by
    rw [hcard]
    exact hn2
  let S : Finset (AgentState L K) :=
    slot6BadPairBlock (L := L) (K := K) n σ l hl1 hlL i K₀ x
  have hcontain :
      ((NonuniformMajority L K).scheduledStep x ⁻¹'
          BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀)
        ⊆
      {pr : AgentState L K × AgentState L K | pr.1 ∈ S ∧ pr.2 ∈ S} := by
    simpa [S] using
      slot6_escape_preimage_subset_badPairBlock_square
        (L := L) (K := K) n σ l hl1 hlL i K₀ x
  have hblock :
      (∑ a ∈ S, x.count a) ≤ B := by
    simpa [S] using H.hblock x hx
  calc
    (NonuniformMajority L K).transitionKernel x
      (BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀)
        =
      ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
        (BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀) := rfl
    _ =
      (x.interactionPMF hx2).toMeasure
        ((NonuniformMajority L K).scheduledStep x ⁻¹'
          BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀) :=
        FloorMasses.stepDist_toMeasure_eq_preimage x hx2 _
    _ ≤
      (x.interactionPMF hx2).toMeasure
        {pr : AgentState L K × AgentState L K | pr.1 ∈ S ∧ pr.2 ∈ S} :=
        measure_mono hcontain
    _ ≤ ENNReal.ofReal ((((∑ a ∈ S, x.count a : ℕ) : ℝ) / (x.card : ℝ)) ^ 2) :=
        FloorMasses.block_pair_prob_le_sq x hx2 S
    _ ≤ slot6BadBlockEta B n := by
        unfold slot6BadBlockEta
        rw [hcard]
        exact ENNReal.ofReal_le_ofReal
          (FloorMasses.pair_block_sq_le_buffer
            (∑ a ∈ S, x.count a) B n hblock hB hn2)

/--
The real paper-scale slot-6 ready-escape residual.

This replaces the `η = 1` fallback with the rectangle budget
`η = B²/(n(n−1))`, from the single bad-block bound `H`.
-/
theorem slot6ReadyEscapeResidual_of_badPairBlockBound
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (B : ℕ)
    (hn2 : 2 ≤ n) (hB : B ≤ n)
    (H : Slot6BadPairBlockBound
      (L := L) (K := K) n σ l hl1 hlL i K₀ B) :
    Slot6ReadyEscapeResidual.Slot6ReadyEscapeResidual
      (L := L) (K := K) n σ l hl1 hlL i K₀
      (slot6BadBlockEta B n) where
  hesc := by
    intro x hx
    exact
      slot6_ready_escape_mass_le_badBlockEta
        (L := L) (K := K)
        n σ l hl1 hlL i K₀ B hn2 hB H x hx

/--
The corresponding landed `Slot6ReadyEscapeAtom`, produced from the real-η
residual.
-/
theorem slot6ReadyEscapeAtom_of_badPairBlockBound
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (B : ℕ)
    (hn2 : 2 ≤ n) (hB : B ≤ n)
    (H : Slot6BadPairBlockBound
      (L := L) (K := K) n σ l hl1 hlL i K₀ B) :
    Slot678SurvivalInputs.Slot6ReadyEscapeAtom
      (L := L) (K := K) n σ l hl1 hlL i K₀
      (slot6BadBlockEta B n) :=
  Slot6ReadyEscapeResidual.slot6ReadyEscapeAtom_of_residual
    (L := L) (K := K)
    (slot6ReadyEscapeResidual_of_badPairBlockBound
      (L := L) (K := K)
      n σ l hl1 hlL i K₀ B hn2 hB H)

/--
Slot-6 survival using the real-η residual, ready for the existing slot-6
survival builder.
-/
noncomputable def slot6SurvivalReady_of_badPairBlockBound
    {n : ℕ} (σ : Sign) (l M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (B : ℕ) (hB : B ≤ n)
    (H : Slot6BadPairBlockBound
      (L := L) (K := K) n σ l hl1 hlL i K₀ B)
    (tWin6 : ℕ → ℕ)
    (hpt6 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat K₀ n m) ^ (tWin6 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞)
        * slot6BadBlockEta B n ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Slot6ReadyEscapeResidual.slot6SurvivalReady_of_residual
    (L := L) (K := K)
    σ l M₀ hn hM1
    hl1 hlL i K₀ hhgt hhne
    (slot6BadBlockEta B n)
    (slot6ReadyEscapeResidual_of_badPairBlockBound
      (L := L) (K := K)
      n σ l hl1 hlL i K₀ B hn hB H)
    tWin6 hpt6 escapeε hescε

#check slot6_escape_preimage_subset_badPairBlock_square
#check slot6_ready_escape_mass_le_badBlockEta
#check slot6ReadyEscapeResidual_of_badPairBlockBound
#check slot6ReadyEscapeAtom_of_badPairBlockBound
#check slot6SurvivalReady_of_badPairBlockBound

end Slot6RealEta
end ExactMajority
