
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Slot678SurvivalInputs

Slots 6/7/8 survival-ready gates, mirroring the slot-1 strengthened-gate repair.

The bare V5.1 surfaces quantify witness floors over phase-only windows:

* slot 6: `Phase6Win`;
* slot 7: `HonestWindows.Phase7Honest`;
* slot 8: `HonestWindows.Phase8Honest`.

Those bare windows are satisfiable, but they do not themselves contain the structural
floor/witness facts.  This file strengthens each window to a ready gate carrying the
required prior-phase cascade witness, then reuses the landed
`WindowSurvival.slotSurvival` and the landed honest drop machinery.

Landed/open boundary:

* slot 6: the per-level drop is landed from `PhaseFloors.phase6_hdrop_wired`
  (as exposed by `DrainRates.hdrop6_of_chain`).  The ready gate carries exactly the
  two structural facts that theorem consumes: Phase-5 sampled floor and a band-main
  witness.  The escape atom is still the at-risk counter survival tail.
* slot 7: the honest monotonicity and drop rectangle are landed in `HonestDrainSlots`;
  the ready gate carries the gap-1 eliminator witness from the Phase-6→7 cascade.
* slot 8: same pattern; the ready gate carries the above-level eliminator witness
  from the Phase-7→8 cascade.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowSurvival

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Slot678SurvivalInputs

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## A. Trivial fallback escape bounds on the bare V5.1 windows -/

/-- Slot 6 fallback escape bound with `η = 1`.

This is always valid but not the paper-scale at-risk counter tail. -/
theorem hescW6_trivial (n : ℕ) :
    ∀ x, Phase6Convergence.Phase6Win (L := L) (K := K) n x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n y} ≤ (1 : ℝ≥0∞) := by
  intro x _hx
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel x) :=
    (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure x
  exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

/-- Slot 7 fallback escape bound with `η = 1`.

This is always valid but not the paper-scale at-risk counter tail. -/
theorem hescW7_trivial (n : ℕ) :
    ∀ x, HonestWindows.Phase7Honest (L := L) (K := K) n x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ HonestWindows.Phase7Honest (L := L) (K := K) n y} ≤ (1 : ℝ≥0∞) := by
  intro x _hx
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel x) :=
    (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure x
  exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

/-- Slot 8 fallback escape bound with `η = 1`.

This is always valid but not the paper-scale at-risk counter tail. -/
theorem hescW8_trivial (n : ℕ) :
    ∀ x, HonestWindows.Phase8Honest (L := L) (K := K) n x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ HonestWindows.Phase8Honest (L := L) (K := K) n y} ≤ (1 : ℝ≥0∞) := by
  intro x _hx
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel x) :=
    (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure x
  exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

/-! ## B. Slot 6 ready gate -/

/-- Slot 6 ready gate.

It strengthens `Phase6Win` with the two structural facts consumed by the landed
Phase-6 per-level drop theorem: the Phase-5 sampled floor and a band-main witness. -/
structure Phase6DrainReady
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K)) : Prop where
  win : Phase6Convergence.Phase6Win (L := L) (K := K) n c
  sampled :
    Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ c
  mainFloor :
    1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum c.count

/-- The Phase-5→6 cascade facts needed to enter the slot-6 ready gate. -/
structure Phase5PostToSlot6Ready
    (Post5 : Config (AgentState L K) → Prop)
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) : Prop where
  to_win :
    ∀ b, Post5 b → Phase6Convergence.Phase6Win (L := L) (K := K) n b
  sampled :
    ∀ b, Post5 b → Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ b
  mainFloor :
    ∀ b, Post5 b →
      1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum b.count

/-- Build a slot-6 ready state from the Phase-5→6 cascade. -/
theorem phase6DrainReady_of_phase5Post
    {Post5 : Config (AgentState L K) → Prop}
    {n : ℕ} {σ : Sign} {l : ℕ} {hl1 : 1 ≤ l} {hlL : l ≤ L}
    {i : Fin (L + 1)} {K₀ : ℕ}
    (h : Phase5PostToSlot6Ready (L := L) (K := K) Post5 n σ l hl1 hlL i K₀)
    {b : Config (AgentState L K)} (hb : Post5 b) :
    Phase6DrainReady (L := L) (K := K) n σ l hl1 hlL i K₀ b :=
  ⟨h.to_win b hb, h.sampled b hb, h.mainFloor b hb⟩

/-- `highMass` is non-increasing on the slot-6 ready gate, by the landed
`Phase6Convergence.potNonincrOn_highMass`. -/
theorem potNonincrOn_highMass_ready
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) :
    OneSidedCancel.PotNonincrOn
      (fun c => Phase6DrainReady (L := L) (K := K) n σ l hl1 hlL i K₀ c)
      (NonuniformMajority L K).transitionKernel
      (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) := by
  intro c hc
  exact (Phase6Convergence.potNonincrOn_highMass (L := L) (K := K) l n) c hc.win

/-- Slot-6 per-level `hdrop` on the ready gate, using the landed
`PhaseFloors.phase6_hdrop_wired` rate. -/
theorem hdrop6_ready
    (n : ℕ) (σ : Sign) (l : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L) :
    ∀ m, ∀ b : Config (AgentState L K),
      Phase6DrainReady (L := L) (K := K) n σ l hl1 hlL i K₀ b →
      Phase6Convergence.highMass (L := L) (K := K) l b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ
        ≤ SlotEngine.qHat K₀ n m := by
  intro m b hb hbm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact SlotEngine.qHat_zero_bound K₀ n
      (fun c : Config (AgentState L K) =>
        Phase6Convergence.highMass (L := L) (K := K) l c) b
  · rw [SlotEngine.qHat_eq_on_pos K₀ n m hmpos]
    exact PhaseFloors.phase6_hdrop_wired
      (L := L) (K := K) σ l n m hn hl1 hlL b hb.win hbm
      i K₀ hhgt hhne hb.sampled hb.mainFloor

/-- Slot-6 ready-gate escape atom.

This combines phase-window survival and persistence of the slot-6 structural floors.
The paper-scale discharge is the at-risk counter tail plus the Phase-5→6 cascade
persistence. -/
structure Slot6ReadyEscapeAtom
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (η : ℝ≥0∞) : Prop where
  hesc :
    ∀ x, Phase6DrainReady (L := L) (K := K) n σ l hl1 hlL i K₀ x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Phase6DrainReady (L := L) (K := K) n σ l hl1 hlL i K₀ y} ≤ η

/-- Trivial ready-gate escape atom for slot 6, with `η = 1`. -/
theorem slot6ReadyEscape_trivial
    (n : ℕ) (σ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) :
    Slot6ReadyEscapeAtom (L := L) (K := K) n σ l hl1 hlL i K₀ (1 : ℝ≥0∞) where
  hesc := by
    intro x _hx
    haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel x) :=
      (inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure x
    exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

/-- Slot 6 survival on the strengthened ready gate. -/
noncomputable def slot6SurvivalReady
    {n : ℕ} (σ : Sign) (l M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞)
    (hesc : Slot6ReadyEscapeAtom (L := L) (K := K) n σ l hl1 hlL i K₀ η)
    (tWin6 : ℕ → ℕ)
    (hpt6 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat K₀ n m) ^ (tWin6 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  WindowSurvival.slotSurvival
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase6DrainReady (L := L) (K := K) n σ l hl1 hlL i K₀ c)
    (fun c => Phase6Convergence.highMass (L := L) (K := K) l c)
    (potNonincrOn_highMass_ready (L := L) (K := K) n σ l hl1 hlL i K₀)
    (SlotEngine.qHat K₀ n)
    (by rw [SlotEngine.qHat_zero])
    (hdrop6_ready (L := L) (K := K) n σ l hn hl1 hlL i K₀ hhgt hhne)
    η hesc.hesc
    tWin6 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) escapeε
    (SlotEngine.qHat_sum_budget hn hM1 tWin6 hpt6) hescε

/-! ## C. Slot 7 ready gate -/

/-- Slot 7 ready gate: `Phase7Honest` plus the gap-1 eliminator-margin witness. -/
structure Phase7DrainReady
    (n : ℕ) (σ : Sign) (E7 : ℕ)
    (c : Config (AgentState L K)) : Prop where
  honest : HonestWindows.Phase7Honest (L := L) (K := K) n c
  witness :
    Phase7Convergence.classMassN σ c ≥ 1 →
      ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count ∧
        E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count

/-- Phase-6→7 cascade facts needed to enter the slot-7 ready gate. -/
structure Phase6PostToSlot7Ready
    (Post6 : Config (AgentState L K) → Prop)
    (n : ℕ) (σ : Sign) (E7 : ℕ) : Prop where
  to_honest :
    ∀ b, Post6 b → HonestWindows.Phase7Honest (L := L) (K := K) n b
  witness :
    ∀ b, Post6 b →
      Phase7Convergence.classMassN σ b ≥ 1 →
        ∃ i j : Fin (L + 1), i.val + 1 = j.val ∧
          1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
          E7 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count

/-- Build a slot-7 ready state from the Phase-6→7 cascade. -/
theorem phase7DrainReady_of_phase6Post
    {Post6 : Config (AgentState L K) → Prop}
    {n : ℕ} {σ : Sign} {E7 : ℕ}
    (h : Phase6PostToSlot7Ready (L := L) (K := K) Post6 n σ E7)
    {b : Config (AgentState L K)} (hb : Post6 b) :
    Phase7DrainReady (L := L) (K := K) n σ E7 b :=
  ⟨h.to_honest b hb, h.witness b hb⟩

/-- `classMassN` is non-increasing on the slot-7 ready gate, by the landed
honest slot-7 monotonicity. -/
theorem potNonincrOn_classMassN_ready7
    (n : ℕ) (σ : Sign) (E7 : ℕ) :
    OneSidedCancel.PotNonincrOn
      (fun c => Phase7DrainReady (L := L) (K := K) n σ E7 c)
      (NonuniformMajority L K).transitionKernel
      (fun c => Phase7Convergence.classMassN σ c) := by
  intro c hc
  exact (HonestDrainSlots.potNonincrOn_classMassN_honest7
    (L := L) (K := K) σ n) c hc.honest

/-- Slot-7 per-level `hdrop` on the ready gate. -/
theorem hdrop7_ready
    (n : ℕ) (σ : Sign) (E7 : ℕ) (hn : 2 ≤ n) :
    ∀ m, ∀ b : Config (AgentState L K),
      Phase7DrainReady (L := L) (K := K) n σ E7 b →
      Phase7Convergence.classMassN σ b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN σ) m)ᶜ
        ≤ SlotEngine.qHat E7 n m := by
  intro m b hb hbm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact SlotEngine.qHat_zero_bound E7 n
      (fun c : Config (AgentState L K) => Phase7Convergence.classMassN σ c) b
  · rw [SlotEngine.qHat_eq_on_pos E7 n m hmpos]
    have hmass1 : Phase7Convergence.classMassN σ b ≥ 1 := by omega
    obtain ⟨ii, jj, hg1, hmin, helim⟩ := hb.witness hmass1
    unfold DrainRates.levelRate
    exact Phase7Convergence.classMassN_hdrop_of_floor7 σ m
      (ENNReal.ofReal ((E7 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
      (HonestDrainSlots.phase7_drop_floor_honest
        (L := L) (K := K) σ n hn b hb.honest ii jj hg1 E7 hmin helim)

/-- Slot-7 ready-gate escape atom.

It combines phase-7 window survival with persistence of the gap-1 eliminator witness. -/
structure Slot7ReadyEscapeAtom
    (n : ℕ) (σ : Sign) (E7 : ℕ) (η : ℝ≥0∞) : Prop where
  hesc :
    ∀ x, Phase7DrainReady (L := L) (K := K) n σ E7 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Phase7DrainReady (L := L) (K := K) n σ E7 y} ≤ η

/-- Trivial ready-gate escape atom for slot 7, with `η = 1`. -/
theorem slot7ReadyEscape_trivial
    (n : ℕ) (σ : Sign) (E7 : ℕ) :
    Slot7ReadyEscapeAtom (L := L) (K := K) n σ E7 (1 : ℝ≥0∞) where
  hesc := by
    intro x _hx
    haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel x) :=
      (inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure x
    exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

/-- Slot 7 survival on the strengthened ready gate. -/
noncomputable def slot7SurvivalReady
    {n : ℕ} (σ : Sign) (E7 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (η : ℝ≥0∞)
    (hesc : Slot7ReadyEscapeAtom (L := L) (K := K) n σ E7 η)
    (tWin7 : ℕ → ℕ)
    (hpt7 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E7 n m) ^ (tWin7 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  WindowSurvival.slotSurvival
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase7DrainReady (L := L) (K := K) n σ E7 c)
    (fun c => Phase7Convergence.classMassN σ c)
    (potNonincrOn_classMassN_ready7 (L := L) (K := K) n σ E7)
    (SlotEngine.qHat E7 n)
    (by rw [SlotEngine.qHat_zero])
    (hdrop7_ready (L := L) (K := K) n σ E7 hn)
    η hesc.hesc
    tWin7 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) escapeε
    (SlotEngine.qHat_sum_budget hn hM1 tWin7 hpt7) hescε

/-! ## D. Slot 8 ready gate -/

/-- Slot 8 ready gate: `Phase8Honest` plus the above-level eliminator witness. -/
structure Phase8DrainReady
    (n : ℕ) (σ : Sign) (E8 : ℕ)
    (c : Config (AgentState L K)) : Prop where
  honest : HonestWindows.Phase8Honest (L := L) (K := K) n c
  witness :
    Phase7Convergence.minorityU σ c ≥ 1 →
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count ∧
        E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count

/-- Phase-7→8 cascade facts needed to enter the slot-8 ready gate. -/
structure Phase7PostToSlot8Ready
    (Post7 : Config (AgentState L K) → Prop)
    (n : ℕ) (σ : Sign) (E8 : ℕ) : Prop where
  to_honest :
    ∀ b, Post7 b → HonestWindows.Phase8Honest (L := L) (K := K) n b
  witness :
    ∀ b, Post7 b →
      Phase7Convergence.minorityU σ b ≥ 1 →
        ∃ i : Fin (L + 1),
          1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
          E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count

/-- Build a slot-8 ready state from the Phase-7→8 cascade. -/
theorem phase8DrainReady_of_phase7Post
    {Post7 : Config (AgentState L K) → Prop}
    {n : ℕ} {σ : Sign} {E8 : ℕ}
    (h : Phase7PostToSlot8Ready (L := L) (K := K) Post7 n σ E8)
    {b : Config (AgentState L K)} (hb : Post7 b) :
    Phase8DrainReady (L := L) (K := K) n σ E8 b :=
  ⟨h.to_honest b hb, h.witness b hb⟩

/-- `minorityU` is non-increasing on the slot-8 ready gate, by the landed honest
slot-8 monotonicity. -/
theorem potNonincrOn_minorityU_ready8
    (n : ℕ) (σ : Sign) (E8 : ℕ) :
    OneSidedCancel.PotNonincrOn
      (fun c => Phase8DrainReady (L := L) (K := K) n σ E8 c)
      (NonuniformMajority L K).transitionKernel
      (fun c => Phase7Convergence.minorityU σ c) := by
  intro c hc
  exact (HonestWindows.potNonincrOn_minorityU_honest8
    (L := L) (K := K) σ n) c hc.honest

/-- Slot-8 per-level `hdrop` on the ready gate. -/
theorem hdrop8_ready
    (n : ℕ) (σ : Sign) (E8 : ℕ) (hn : 2 ≤ n) :
    ∀ m, ∀ b : Config (AgentState L K),
      Phase8DrainReady (L := L) (K := K) n σ E8 b →
      Phase7Convergence.minorityU σ b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
        ≤ SlotEngine.qHat E8 n m := by
  intro m b hb hbm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact SlotEngine.qHat_zero_bound E8 n
      (fun c : Config (AgentState L K) => Phase7Convergence.minorityU σ c) b
  · rw [SlotEngine.qHat_eq_on_pos E8 n m hmpos]
    have hmass1 : Phase7Convergence.minorityU σ b ≥ 1 := by omega
    obtain ⟨ii, hmin, helim⟩ := hb.witness hmass1
    unfold DrainRates.levelRate
    set p := ENNReal.ofReal ((E8 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) with hp
    have hfloor :
        p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          {c' | Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ b} := by
      rw [hp]
      exact HonestDrainSlots.phase8_drop_floor_honest
        (L := L) (K := K) σ n hn b hb.honest ii E8 hmin helim
    classical
    have hKb : (NonuniformMajority L K).transitionKernel b
        = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
    have hsucc_eq : {c' : Config (AgentState L K) |
          Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ b}
        = OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m := by
      ext c'
      simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hbm]
      omega
    have hmeas : MeasurableSet (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m) :=
      OneSidedCancel.potBelow_measurable (Phase7Convergence.minorityU σ (L := L) (K := K)) m
    haveI hprob : IsProbabilityMeasure (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
      rw [← hKb]
      exact (inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
    have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
        = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
            (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m) := by
      rw [measure_compl hmeas (measure_ne_top _ _), hprob.measure_univ]
    rw [hKb, hcompl]
    have hp_le : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m) := by
      rw [← hsucc_eq]
      exact hfloor
    exact tsub_le_tsub_left hp_le 1

/-- Slot-8 ready-gate escape atom.

It combines phase-8 window survival with persistence of the above-level eliminator witness. -/
structure Slot8ReadyEscapeAtom
    (n : ℕ) (σ : Sign) (E8 : ℕ) (η : ℝ≥0∞) : Prop where
  hesc :
    ∀ x, Phase8DrainReady (L := L) (K := K) n σ E8 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Phase8DrainReady (L := L) (K := K) n σ E8 y} ≤ η

/-- Trivial ready-gate escape atom for slot 8, with `η = 1`. -/
theorem slot8ReadyEscape_trivial
    (n : ℕ) (σ : Sign) (E8 : ℕ) :
    Slot8ReadyEscapeAtom (L := L) (K := K) n σ E8 (1 : ℝ≥0∞) where
  hesc := by
    intro x _hx
    haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel x) :=
      (inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure x
    exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

/-- Slot 8 survival on the strengthened ready gate. -/
noncomputable def slot8SurvivalReady
    {n : ℕ} (σ : Sign) (E8 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (η : ℝ≥0∞)
    (hesc : Slot8ReadyEscapeAtom (L := L) (K := K) n σ E8 η)
    (tWin8 : ℕ → ℕ)
    (hpt8 : ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E8 n m) ^ (tWin8 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  WindowSurvival.slotSurvival
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase8DrainReady (L := L) (K := K) n σ E8 c)
    (fun c => Phase7Convergence.minorityU σ c)
    (potNonincrOn_minorityU_ready8 (L := L) (K := K) n σ E8)
    (SlotEngine.qHat E8 n)
    (by rw [SlotEngine.qHat_zero])
    (hdrop8_ready (L := L) (K := K) n σ E8 hn)
    η hesc.hesc
    tWin8 M₀ (Real.toNNReal (1 / (n : ℝ) ^ 2)) escapeε
    (SlotEngine.qHat_sum_budget hn hM1 tWin8 hpt8) hescε

#print axioms hescW6_trivial
#print axioms hescW7_trivial
#print axioms hescW8_trivial
#print axioms phase6DrainReady_of_phase5Post
#print axioms potNonincrOn_highMass_ready
#print axioms hdrop6_ready
#print axioms slot6SurvivalReady
#print axioms phase7DrainReady_of_phase6Post
#print axioms potNonincrOn_classMassN_ready7
#print axioms hdrop7_ready
#print axioms slot7SurvivalReady
#print axioms phase8DrainReady_of_phase7Post
#print axioms potNonincrOn_minorityU_ready8
#print axioms hdrop8_ready
#print axioms slot8SurvivalReady

end Slot678SurvivalInputs

end ExactMajority
