
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ReadyEscapeCounterTail

Uniform escape decomposition for the strengthened slot Ready gates.

The strengthened slot gates have shape

  Ready c ↔ HonestWindow c ∧ FloorPayload c.

Therefore the one-step escape event decomposes as

  {¬ Ready} ⊆ {¬ HonestWindow} ∪ {¬ FloorPayload}.

This file turns a landed counter/window escape tail plus a floor-persistence tail into
the Ready-gate escape atoms consumed by:

* `Slot1SurvivalInputs.Slot1ReadyEscapeAtom`;
* `Slot678SurvivalInputs.Slot6ReadyEscapeAtom`;
* `Slot678SurvivalInputs.Slot7ReadyEscapeAtom`;
* `Slot678SurvivalInputs.Slot8ReadyEscapeAtom`.

Important boundary:

The current Ready gates do not include a “no at-risk zero clock” predicate.  Thus a
small one-step tail cannot be produced from a reset-prefix at-risk tail alone for
arbitrary Ready states.  The honest small bound must enter as the gated
`counterEscape` field below, and each structural floor either persists with zero
mass or contributes its own explicit `floorEscape` budget.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot1SurvivalInputs
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Slot678SurvivalInputs

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace ReadyEscapeCounterTail

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Generic decomposition engine -/

/-- Generic Ready-gate escape inputs.

`Ready` is the strengthened gate, `Honest` is the phase-only honest window, and
`Floor` is the structural witness/floor payload. -/
structure ReadyEscapeInputs
    (Ready Honest Floor : Config (AgentState L K) → Prop)
    (ηCounter ηFloor : ℝ≥0∞) : Prop where
  /-- The strengthened Ready gate is exactly the honest window plus floor payload. -/
  ready_iff : ∀ c, Ready c ↔ Honest c ∧ Floor c

  /-- Counter/window escape tail on the Ready gate.  This is the slot-specific
  at-risk-counter input supplied by the clock/counter layer. -/
  counterEscape :
    ∀ x, Ready x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Honest y} ≤ ηCounter

  /-- Structural floor escape/persistence tail on the Ready gate.  In the common
  persistence case this is discharged with budget `0`. -/
  floorEscape :
    ∀ x, Ready x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Floor y} ≤ ηFloor

/-- Set containment behind the Ready-gate escape decomposition. -/
theorem not_ready_subset_not_honest_union_not_floor
    (Ready Honest Floor : Config (AgentState L K) → Prop)
    (hReady : ∀ c, Ready c ↔ Honest c ∧ Floor c) :
    {y : Config (AgentState L K) | ¬ Ready y}
      ⊆ {y | ¬ Honest y} ∪ {y | ¬ Floor y} := by
  intro y hy
  by_cases hH : Honest y
  · exact Or.inr (by
      intro hF
      exact hy ((hReady y).mpr ⟨hH, hF⟩))
  · exact Or.inl hH

/-- Generic Ready-gate escape bound: counter escape plus floor escape. -/
theorem ready_escape_le_add
    (Ready Honest Floor : Config (AgentState L K) → Prop)
    (ηCounter ηFloor : ℝ≥0∞)
    (A : ReadyEscapeInputs (L := L) (K := K)
      Ready Honest Floor ηCounter ηFloor) :
    ∀ x, Ready x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Ready y} ≤ ηCounter + ηFloor := by
  intro x hx
  calc
    (NonuniformMajority L K).transitionKernel x {y | ¬ Ready y}
        ≤ (NonuniformMajority L K).transitionKernel x
            ({y | ¬ Honest y} ∪ {y | ¬ Floor y}) :=
          measure_mono
            (not_ready_subset_not_honest_union_not_floor
              (L := L) (K := K) Ready Honest Floor A.ready_iff)
    _ ≤ (NonuniformMajority L K).transitionKernel x {y | ¬ Honest y}
          + (NonuniformMajority L K).transitionKernel x {y | ¬ Floor y} :=
          measure_union_le _ _
    _ ≤ ηCounter + ηFloor :=
          add_le_add (A.counterEscape x hx) (A.floorEscape x hx)

/-- Floor persistence as a zero-budget `ReadyEscapeInputs` field. -/
def ReadyEscapeInputs.of_floorPersistence
    (Ready Honest Floor : Config (AgentState L K) → Prop)
    (ηCounter : ℝ≥0∞)
    (hReady : ∀ c, Ready c ↔ Honest c ∧ Floor c)
    (hCounter :
      ∀ x, Ready x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ Honest y} ≤ ηCounter)
    (hFloor0 :
      ∀ x, Ready x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ Floor y} = 0) :
    ReadyEscapeInputs (L := L) (K := K) Ready Honest Floor ηCounter 0 where
  ready_iff := hReady
  counterEscape := hCounter
  floorEscape := by
    intro x hx
    rw [hFloor0 x hx]

/-- Generic Ready-gate escape bound with floor persistence, so the final budget is
exactly the counter-tail budget. -/
theorem ready_escape_le_of_floorPersistence
    (Ready Honest Floor : Config (AgentState L K) → Prop)
    (ηCounter : ℝ≥0∞)
    (hReady : ∀ c, Ready c ↔ Honest c ∧ Floor c)
    (hCounter :
      ∀ x, Ready x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ Honest y} ≤ ηCounter)
    (hFloor0 :
      ∀ x, Ready x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ Floor y} = 0) :
    ∀ x, Ready x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Ready y} ≤ ηCounter := by
  intro x hx
  have A :=
    ReadyEscapeInputs.of_floorPersistence
      (L := L) (K := K) Ready Honest Floor ηCounter
      hReady hCounter hFloor0
  simpa using
    (ready_escape_le_add
      (L := L) (K := K) Ready Honest Floor ηCounter 0 A x hx)

/-! ## Slot-specific floor predicates -/

/-- Slot-1 structural floor payload. -/
def phase1Floors (n P1 : ℕ) (c : Config (AgentState L K)) : Prop :=
  1 ≤ (DrainThreading.extremePosSet L K).sum c.count ∧
    P1 ≤ (DrainThreading.pullPosSet L K).sum c.count

/-- Slot-6 structural floor payload. -/
def phase6Floors
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ c ∧
    1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum c.count

/-- Slot-7 eliminator-margin witness payload. -/
def phase7Floors
    (n : ℕ) (σ : Sign) (E7 : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  Phase7Convergence.classMassN σ c ≥ 1 →
    ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count ∧
      E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count

/-- Slot-8 above-level eliminator witness payload. -/
def phase8Floors
    (n : ℕ) (σ : Sign) (E8 : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  Phase7Convergence.minorityU σ c ≥ 1 →
    ∃ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count ∧
      E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count

/-! ## Ready iff honest ∧ floors -/

theorem phase1DrainReady_iff
    (n P1 : ℕ) :
    ∀ c, Slot1SurvivalInputs.Phase1DrainReady (L := L) (K := K) n P1 c ↔
      HonestWindows.Phase1Honest (L := L) (K := K) n c ∧
        phase1Floors (L := L) (K := K) n P1 c := by
  intro c
  constructor
  · intro h
    exact ⟨h.honest, h.hext, h.hpull⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2⟩

theorem phase6DrainReady_iff
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) :
    ∀ c, Slot678SurvivalInputs.Phase6DrainReady
        (L := L) (K := K) n σ l hl1 hlL i K₀ c ↔
      Phase6Convergence.Phase6Win (L := L) (K := K) n c ∧
        phase6Floors (L := L) (K := K) n σ l hl1 hlL i K₀ c := by
  intro c
  constructor
  · intro h
    exact ⟨h.win, h.sampled, h.mainFloor⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2⟩

theorem phase7DrainReady_iff
    (n : ℕ) (σ : Sign) (E7 : ℕ) :
    ∀ c, Slot678SurvivalInputs.Phase7DrainReady
        (L := L) (K := K) n σ E7 c ↔
      HonestWindows.Phase7Honest (L := L) (K := K) n c ∧
        phase7Floors (L := L) (K := K) n σ E7 c := by
  intro c
  constructor
  · intro h
    exact ⟨h.honest, h.witness⟩
  · intro h
    exact ⟨h.1, h.2⟩

theorem phase8DrainReady_iff
    (n : ℕ) (σ : Sign) (E8 : ℕ) :
    ∀ c, Slot678SurvivalInputs.Phase8DrainReady
        (L := L) (K := K) n σ E8 c ↔
      HonestWindows.Phase8Honest (L := L) (K := K) n c ∧
        phase8Floors (L := L) (K := K) n σ E8 c := by
  intro c
  constructor
  · intro h
    exact ⟨h.honest, h.witness⟩
  · intro h
    exact ⟨h.1, h.2⟩

/-! ## Slot 1 -/

/-- Slot-1 Ready escape from a counter/window tail and a floor-drop tail. -/
theorem slot1ReadyEscape_of_counterTail
    (n P1 : ℕ) (ηCounter ηFloor : ℝ≥0∞)
    (hCounter :
      ∀ x, Slot1SurvivalInputs.Phase1DrainReady
          (L := L) (K := K) n P1 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ HonestWindows.Phase1Honest (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor :
      ∀ x, Slot1SurvivalInputs.Phase1DrainReady
          (L := L) (K := K) n P1 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ phase1Floors (L := L) (K := K) n P1 y}
          ≤ ηFloor) :
    Slot1SurvivalInputs.Slot1ReadyEscapeAtom
      (L := L) (K := K) n P1 (ηCounter + ηFloor) where
  hesc := by
    exact ready_escape_le_add
      (L := L) (K := K)
      (Slot1SurvivalInputs.Phase1DrainReady (L := L) (K := K) n P1)
      (HonestWindows.Phase1Honest (L := L) (K := K) n)
      (phase1Floors (L := L) (K := K) n P1)
      ηCounter ηFloor
      { ready_iff := phase1DrainReady_iff (L := L) (K := K) n P1
        counterEscape := hCounter
        floorEscape := hFloor }

/-- Slot-1 Ready escape with floor persistence, so the final budget is just `ηCounter`. -/
theorem slot1ReadyEscape_of_counterTail_of_floorPersistence
    (n P1 : ℕ) (ηCounter : ℝ≥0∞)
    (hCounter :
      ∀ x, Slot1SurvivalInputs.Phase1DrainReady
          (L := L) (K := K) n P1 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ HonestWindows.Phase1Honest (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor0 :
      ∀ x, Slot1SurvivalInputs.Phase1DrainReady
          (L := L) (K := K) n P1 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ phase1Floors (L := L) (K := K) n P1 y}
          = 0) :
    Slot1SurvivalInputs.Slot1ReadyEscapeAtom
      (L := L) (K := K) n P1 ηCounter where
  hesc :=
    ready_escape_le_of_floorPersistence
      (L := L) (K := K)
      (Slot1SurvivalInputs.Phase1DrainReady (L := L) (K := K) n P1)
      (HonestWindows.Phase1Honest (L := L) (K := K) n)
      (phase1Floors (L := L) (K := K) n P1)
      ηCounter
      (phase1DrainReady_iff (L := L) (K := K) n P1)
      hCounter hFloor0

/-! ## Slot 6 -/

/-- Slot-6 Ready escape from a counter/window tail and a floor-drop tail. -/
theorem slot6ReadyEscape_of_counterTail
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (ηCounter ηFloor : ℝ≥0∞)
    (hCounter :
      ∀ x, Slot678SurvivalInputs.Phase6DrainReady
          (L := L) (K := K) n σ l hl1 hlL i K₀ x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor :
      ∀ x, Slot678SurvivalInputs.Phase6DrainReady
          (L := L) (K := K) n σ l hl1 hlL i K₀ x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ phase6Floors (L := L) (K := K) n σ l hl1 hlL i K₀ y}
          ≤ ηFloor) :
    Slot678SurvivalInputs.Slot6ReadyEscapeAtom
      (L := L) (K := K) n σ l hl1 hlL i K₀ (ηCounter + ηFloor) where
  hesc := by
    exact ready_escape_le_add
      (L := L) (K := K)
      (Slot678SurvivalInputs.Phase6DrainReady (L := L) (K := K)
        n σ l hl1 hlL i K₀)
      (Phase6Convergence.Phase6Win (L := L) (K := K) n)
      (phase6Floors (L := L) (K := K) n σ l hl1 hlL i K₀)
      ηCounter ηFloor
      { ready_iff := phase6DrainReady_iff
          (L := L) (K := K) n σ l hl1 hlL i K₀
        counterEscape := hCounter
        floorEscape := hFloor }

/-- Slot-6 Ready escape with floor persistence. -/
theorem slot6ReadyEscape_of_counterTail_of_floorPersistence
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (ηCounter : ℝ≥0∞)
    (hCounter :
      ∀ x, Slot678SurvivalInputs.Phase6DrainReady
          (L := L) (K := K) n σ l hl1 hlL i K₀ x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor0 :
      ∀ x, Slot678SurvivalInputs.Phase6DrainReady
          (L := L) (K := K) n σ l hl1 hlL i K₀ x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ phase6Floors (L := L) (K := K) n σ l hl1 hlL i K₀ y}
          = 0) :
    Slot678SurvivalInputs.Slot6ReadyEscapeAtom
      (L := L) (K := K) n σ l hl1 hlL i K₀ ηCounter where
  hesc :=
    ready_escape_le_of_floorPersistence
      (L := L) (K := K)
      (Slot678SurvivalInputs.Phase6DrainReady (L := L) (K := K)
        n σ l hl1 hlL i K₀)
      (Phase6Convergence.Phase6Win (L := L) (K := K) n)
      (phase6Floors (L := L) (K := K) n σ l hl1 hlL i K₀)
      ηCounter
      (phase6DrainReady_iff (L := L) (K := K) n σ l hl1 hlL i K₀)
      hCounter hFloor0

/-! ## Slot 7 -/

/-- Slot-7 Ready escape from a counter/window tail and a floor-drop tail. -/
theorem slot7ReadyEscape_of_counterTail
    (n : ℕ) (σ : Sign) (E7 : ℕ)
    (ηCounter ηFloor : ℝ≥0∞)
    (hCounter :
      ∀ x, Slot678SurvivalInputs.Phase7DrainReady
          (L := L) (K := K) n σ E7 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ HonestWindows.Phase7Honest (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor :
      ∀ x, Slot678SurvivalInputs.Phase7DrainReady
          (L := L) (K := K) n σ E7 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ phase7Floors (L := L) (K := K) n σ E7 y}
          ≤ ηFloor) :
    Slot678SurvivalInputs.Slot7ReadyEscapeAtom
      (L := L) (K := K) n σ E7 (ηCounter + ηFloor) where
  hesc := by
    exact ready_escape_le_add
      (L := L) (K := K)
      (Slot678SurvivalInputs.Phase7DrainReady (L := L) (K := K) n σ E7)
      (HonestWindows.Phase7Honest (L := L) (K := K) n)
      (phase7Floors (L := L) (K := K) n σ E7)
      ηCounter ηFloor
      { ready_iff := phase7DrainReady_iff (L := L) (K := K) n σ E7
        counterEscape := hCounter
        floorEscape := hFloor }

/-- Slot-7 Ready escape with floor persistence. -/
theorem slot7ReadyEscape_of_counterTail_of_floorPersistence
    (n : ℕ) (σ : Sign) (E7 : ℕ)
    (ηCounter : ℝ≥0∞)
    (hCounter :
      ∀ x, Slot678SurvivalInputs.Phase7DrainReady
          (L := L) (K := K) n σ E7 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ HonestWindows.Phase7Honest (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor0 :
      ∀ x, Slot678SurvivalInputs.Phase7DrainReady
          (L := L) (K := K) n σ E7 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ phase7Floors (L := L) (K := K) n σ E7 y}
          = 0) :
    Slot678SurvivalInputs.Slot7ReadyEscapeAtom
      (L := L) (K := K) n σ E7 ηCounter where
  hesc :=
    ready_escape_le_of_floorPersistence
      (L := L) (K := K)
      (Slot678SurvivalInputs.Phase7DrainReady (L := L) (K := K) n σ E7)
      (HonestWindows.Phase7Honest (L := L) (K := K) n)
      (phase7Floors (L := L) (K := K) n σ E7)
      ηCounter
      (phase7DrainReady_iff (L := L) (K := K) n σ E7)
      hCounter hFloor0

/-! ## Slot 8 -/

/-- Slot-8 Ready escape from a counter/window tail and a floor-drop tail. -/
theorem slot8ReadyEscape_of_counterTail
    (n : ℕ) (σ : Sign) (E8 : ℕ)
    (ηCounter ηFloor : ℝ≥0∞)
    (hCounter :
      ∀ x, Slot678SurvivalInputs.Phase8DrainReady
          (L := L) (K := K) n σ E8 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ HonestWindows.Phase8Honest (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor :
      ∀ x, Slot678SurvivalInputs.Phase8DrainReady
          (L := L) (K := K) n σ E8 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ phase8Floors (L := L) (K := K) n σ E8 y}
          ≤ ηFloor) :
    Slot678SurvivalInputs.Slot8ReadyEscapeAtom
      (L := L) (K := K) n σ E8 (ηCounter + ηFloor) where
  hesc := by
    exact ready_escape_le_add
      (L := L) (K := K)
      (Slot678SurvivalInputs.Phase8DrainReady (L := L) (K := K) n σ E8)
      (HonestWindows.Phase8Honest (L := L) (K := K) n)
      (phase8Floors (L := L) (K := K) n σ E8)
      ηCounter ηFloor
      { ready_iff := phase8DrainReady_iff (L := L) (K := K) n σ E8
        counterEscape := hCounter
        floorEscape := hFloor }

/-- Slot-8 Ready escape with floor persistence. -/
theorem slot8ReadyEscape_of_counterTail_of_floorPersistence
    (n : ℕ) (σ : Sign) (E8 : ℕ)
    (ηCounter : ℝ≥0∞)
    (hCounter :
      ∀ x, Slot678SurvivalInputs.Phase8DrainReady
          (L := L) (K := K) n σ E8 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ HonestWindows.Phase8Honest (L := L) (K := K) n y}
          ≤ ηCounter)
    (hFloor0 :
      ∀ x, Slot678SurvivalInputs.Phase8DrainReady
          (L := L) (K := K) n σ E8 x →
        (NonuniformMajority L K).transitionKernel x
          {y | ¬ phase8Floors (L := L) (K := K) n σ E8 y}
          = 0) :
    Slot678SurvivalInputs.Slot8ReadyEscapeAtom
      (L := L) (K := K) n σ E8 ηCounter where
  hesc :=
    ready_escape_le_of_floorPersistence
      (L := L) (K := K)
      (Slot678SurvivalInputs.Phase8DrainReady (L := L) (K := K) n σ E8)
      (HonestWindows.Phase8Honest (L := L) (K := K) n)
      (phase8Floors (L := L) (K := K) n σ E8)
      ηCounter
      (phase8DrainReady_iff (L := L) (K := K) n σ E8)
      hCounter hFloor0

#print axioms not_ready_subset_not_honest_union_not_floor
#print axioms ready_escape_le_add
#print axioms ready_escape_le_of_floorPersistence
#print axioms phase1DrainReady_iff
#print axioms phase6DrainReady_iff
#print axioms phase7DrainReady_iff
#print axioms phase8DrainReady_iff
#print axioms slot1ReadyEscape_of_counterTail
#print axioms slot1ReadyEscape_of_counterTail_of_floorPersistence
#print axioms slot6ReadyEscape_of_counterTail
#print axioms slot6ReadyEscape_of_counterTail_of_floorPersistence
#print axioms slot7ReadyEscape_of_counterTail
#print axioms slot7ReadyEscape_of_counterTail_of_floorPersistence
#print axioms slot8ReadyEscape_of_counterTail
#print axioms slot8ReadyEscape_of_counterTail_of_floorPersistence

end ReadyEscapeCounterTail

end ExactMajority
