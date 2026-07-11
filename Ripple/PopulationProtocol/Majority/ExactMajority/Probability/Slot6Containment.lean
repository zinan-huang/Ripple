import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot6RealEta

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Slot6Containment

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## A. Aliases for the landed slot-6 ready/bad surfaces -/

/-- Alias for the landed slot-6 ready gate. -/
abbrev Ready6
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  Slot6RealEta.Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ c

/-- Alias for the landed slot-6 bad-ready output event. -/
abbrev BadReady6
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) :
    Set (Config (AgentState L K)) :=
  Slot6RealEta.BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀

/-! ## B. The single deterministic protocol-counting hypothesis -/

/--
The single deterministic fact left for the real protocol.

For every slot-6 ready source `x`, it supplies a concrete at-risk block
`block x` such that:

* every scheduled pair whose output breaks `Phase6DrainReady` lies in
  `(block x) × (block x)`;
* the total multiplicity of that block in `x` is at most `B`;
* the ready source has card `n`.

The intended instantiation is the concrete at-risk clock / ready-counter block.
This file does not assume any probabilistic tail here; this is purely a
deterministic containment/counting object.
-/
structure Phase6BreakingPairsInBlock
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (B : ℕ) where
  block : Config (AgentState L K) → Finset (AgentState L K)
  hcard :
    ∀ x,
      Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ x →
      x.card = n
  hbreaking_pairs :
    ∀ x,
      Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ x →
      ((NonuniformMajority L K).scheduledStep x ⁻¹'
          BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀)
        ⊆
      {pr : AgentState L K × AgentState L K |
        pr.1 ∈ block x ∧ pr.2 ∈ block x}
  hblock_count :
    ∀ x,
      Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ x →
      (∑ a ∈ block x, x.count a) ≤ B

/-! ## C. From the concrete block to the landed exact bad-pair block -/

/--
If every ready-breaking pair lies in the supplied concrete block square, then
the landed exact participant block `slot6BadPairBlock x` is a subset of that
concrete block.
-/
theorem slot6BadPairBlock_subset_of_phase6BreakingPairsInBlock
    {n : ℕ} {σ : Sign} {l : ℕ} {hl1 : 1 ≤ l} {hlL : l ≤ L}
    {i : Fin (L + 1)} {K₀ B : ℕ}
    (H : Phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B)
    {x : Config (AgentState L K)}
    (hx : Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ x) :
    Slot6RealEta.slot6BadPairBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ x
      ⊆ H.block x := by
  classical
  intro a ha
  unfold Slot6RealEta.slot6BadPairBlock at ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  rcases ha with ⟨b, hbad | hbad⟩
  · have hp :
        (a, b) ∈
          ((NonuniformMajority L K).scheduledStep x ⁻¹'
            BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀) := by
      change
        ¬ Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀
          ((NonuniformMajority L K).scheduledStep x (a, b))
      exact hbad
    exact (H.hbreaking_pairs x hx hp).1
  · have hp :
        (b, a) ∈
          ((NonuniformMajority L K).scheduledStep x ⁻¹'
            BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀) := by
      change
        ¬ Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀
          ((NonuniformMajority L K).scheduledStep x (b, a))
      exact hbad
    exact (H.hbreaking_pairs x hx hp).2

/--
The landed exact bad-pair block has count at most `B`, by subseting it into
the concrete block supplied by `Phase6BreakingPairsInBlock`.
-/
theorem slot6BadPairBlock_count_le_of_phase6BreakingPairsInBlock
    {n : ℕ} {σ : Sign} {l : ℕ} {hl1 : 1 ≤ l} {hlL : l ≤ L}
    {i : Fin (L + 1)} {K₀ B : ℕ}
    (H : Phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B)
    {x : Config (AgentState L K)}
    (hx : Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ x) :
    (∑ a ∈ Slot6RealEta.slot6BadPairBlock
        (L := L) (K := K) n σ l hl1 hlL i K₀ x, x.count a) ≤ B := by
  classical
  have hsub :
      Slot6RealEta.slot6BadPairBlock
        (L := L) (K := K) n σ l hl1 hlL i K₀ x
        ⊆ H.block x :=
    slot6BadPairBlock_subset_of_phase6BreakingPairsInBlock
      (L := L) (K := K) H hx
  calc
    (∑ a ∈ Slot6RealEta.slot6BadPairBlock
        (L := L) (K := K) n σ l hl1 hlL i K₀ x, x.count a)
        ≤ (∑ a ∈ H.block x, x.count a) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (by
              intro a _haBlock _haNotExact
              exact Nat.zero_le _)
    _ ≤ B := H.hblock_count x hx

/-! ## D. The landed `Slot6BadPairBlockBound` from the deterministic fact -/

/--
Produce the exact landed `Slot6BadPairBlockBound` from the one deterministic
protocol-counting fact.
-/
theorem slot6BadPairBlockBound_of_phase6BreakingPairsInBlock
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ B : ℕ)
    (H : Phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B) :
    Slot6RealEta.Slot6BadPairBlockBound
      (L := L) (K := K) n σ l hl1 hlL i K₀ B where
  hcard := H.hcard
  hblock := by
    intro x hx
    exact
      slot6BadPairBlock_count_le_of_phase6BreakingPairsInBlock
        (L := L) (K := K) H hx

/-! ## E. Real-η residual, atom, and survival wrappers -/

/--
One-step slot-6 ready escape mass bound from the deterministic containment/count
fact.
-/
theorem slot6_ready_escape_mass_le_of_phase6BreakingPairsInBlock
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ B : ℕ)
    (hn2 : 2 ≤ n) (hB : B ≤ n)
    (H : Phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B)
    (x : Config (AgentState L K))
    (hx : Ready6 (L := L) (K := K) n σ l hl1 hlL i K₀ x) :
    (NonuniformMajority L K).transitionKernel x
      (BadReady6 (L := L) (K := K) n σ l hl1 hlL i K₀)
      ≤ Slot6RealEta.slot6BadBlockEta B n :=
  Slot6RealEta.slot6_ready_escape_mass_le_badBlockEta
    (L := L) (K := K)
    n σ l hl1 hlL i K₀ B hn2 hB
    (slot6BadPairBlockBound_of_phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B H)
    x hx

/--
The real paper-scale slot-6 ready-escape residual from the deterministic
containment/count fact.
-/
theorem slot6ReadyEscapeResidual_of_phase6BreakingPairsInBlock
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ B : ℕ)
    (hn2 : 2 ≤ n) (hB : B ≤ n)
    (H : Phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B) :
    Slot6ReadyEscapeResidual.Slot6ReadyEscapeResidual
      (L := L) (K := K) n σ l hl1 hlL i K₀
      (Slot6RealEta.slot6BadBlockEta B n) :=
  Slot6RealEta.slot6ReadyEscapeResidual_of_badPairBlockBound
    (L := L) (K := K)
    n σ l hl1 hlL i K₀ B hn2 hB
    (slot6BadPairBlockBound_of_phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B H)

/--
The corresponding landed `Slot6ReadyEscapeAtom`.
-/
theorem slot6ReadyEscapeAtom_of_phase6BreakingPairsInBlock
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ B : ℕ)
    (hn2 : 2 ≤ n) (hB : B ≤ n)
    (H : Phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B) :
    Slot678SurvivalInputs.Slot6ReadyEscapeAtom
      (L := L) (K := K) n σ l hl1 hlL i K₀
      (Slot6RealEta.slot6BadBlockEta B n) :=
  Slot6RealEta.slot6ReadyEscapeAtom_of_badPairBlockBound
    (L := L) (K := K)
    n σ l hl1 hlL i K₀ B hn2 hB
    (slot6BadPairBlockBound_of_phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B H)

/--
Slot-6 survival using the real-η residual, ready for the existing slot-6
survival builder.
-/
noncomputable def slot6SurvivalReady_of_phase6BreakingPairsInBlock
    {n : ℕ} (σ : Sign) (l M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (B : ℕ) (hB : B ≤ n)
    (H : Phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B)
    (tWin6 : ℕ → ℕ)
    (hpt6 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat K₀ n m) ^ (tWin6 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞)
        * Slot6RealEta.slot6BadBlockEta B n ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Slot6RealEta.slot6SurvivalReady_of_badPairBlockBound
    (L := L) (K := K)
    σ l M₀ hn hM1
    hl1 hlL i K₀ hhgt hhne
    B hB
    (slot6BadPairBlockBound_of_phase6BreakingPairsInBlock
      (L := L) (K := K) n σ l hl1 hlL i K₀ B H)
    tWin6 hpt6 escapeε hescε

#print axioms slot6BadPairBlock_subset_of_phase6BreakingPairsInBlock
#print axioms slot6BadPairBlock_count_le_of_phase6BreakingPairsInBlock
#print axioms slot6BadPairBlockBound_of_phase6BreakingPairsInBlock
#print axioms slot6_ready_escape_mass_le_of_phase6BreakingPairsInBlock
#print axioms slot6ReadyEscapeResidual_of_phase6BreakingPairsInBlock
#print axioms slot6ReadyEscapeAtom_of_phase6BreakingPairsInBlock
#print axioms slot6SurvivalReady_of_phase6BreakingPairsInBlock

end Slot6Containment

end ExactMajority
