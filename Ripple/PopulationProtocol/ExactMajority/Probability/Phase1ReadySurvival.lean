
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Slot1SurvivalInputs

Slot-1 (Phase 1, D7) survival input reduction.

The V5.1 slot-1 surface asks for three facts over the bare phase-only window

  `PhaseOnlyWindows.Phase1Win n c := c.card = n ∧ ∀ a ∈ c, a.phase.val = 1`.

That bare window does not include the structural floors (`extremePos`, `pullPos`) and
does not include any counter-safety/full-counter invariant.  Thus:

* the nontrivial `hescW1` tail is exactly the at-risk counter escape atom; a trivial
  probability-`≤ 1` version is proved here, but the small `e^{-40(L+1)}`-style bound
  must come from the clock/counter layer;
* `hext1H` and `hpull1H` must come from the Phase-0 Post / D15 cascade and persist
  through the slot-1 window; they are not consequences of bare `Phase1Win`.

This file packages the sound replacement: a strengthened, satisfiable slot-1 ready
window carrying the structural floors.  On that window, the landed genuine D7 drain
machinery discharges the slot-1 levels engine with no all-Main assumption.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.SurvivalWorkFamily
import Ripple.PopulationProtocol.ExactMajority.Probability.WindowSurvival

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Phase1ReadySurvival

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The trivial, always-valid escape bound for the bare slot-1 genuine window.

This is axiom-clean and useful as a sanity fallback, but it is not the paper-scale
at-risk counter tail.  The nontrivial small `η₁` must be supplied by the clock/counter
layer. -/
theorem hescW1_trivial (n : ℕ) :
    ∀ x, PhaseOnlyWindows.Phase1Win (L := L) (K := K) n x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n y} ≤ (1 : ℝ≥0∞) := by
  intro x _hx
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel x) :=
    (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure x
  exact le_trans (measure_mono (Set.subset_univ _)) prob_le_one

/-- The exact slot-1 readiness predicate: the phase-only genuine window plus the two
persistent D7 structural floors.

This is the satisfiable strengthened gate that the landed slot-1 drop rectangle actually
needs.  It avoids the false claim that every bare `Phase1Win` configuration has a
`+3` extreme and a partner pool. -/
structure Phase1DrainReady (n P1 : ℕ) (c : Config (AgentState L K)) : Prop where
  genuine : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c
  hext : 1 ≤ (DrainThreading.extremePosSet L K).sum c.count
  hpull : P1 ≤ (DrainThreading.pullPosSet L K).sum c.count

/-- The Phase-0 Post / D15 cascade facts needed to enter slot 1.

A downstream Phase-0 Post predicate must provide exactly these three structural facts:
the phase-1 genuine window, a `+3` extreme witness, and the partner-pool floor. -/
structure Phase0PostToPhase1Floors
    (Post0 : Config (AgentState L K) → Prop) (n P1 : ℕ) : Prop where
  to_phase1 : ∀ b, Post0 b → PhaseOnlyWindows.Phase1Win (L := L) (K := K) n b
  hext : ∀ b, Post0 b → 1 ≤ (DrainThreading.extremePosSet L K).sum b.count
  hpull : ∀ b, Post0 b → P1 ≤ (DrainThreading.pullPosSet L K).sum b.count

/-- Build the strengthened slot-1 ready predicate from a Phase-0 Post / D15 cascade
witness. -/
theorem phase1DrainReady_of_phase0Post
    {Post0 : Config (AgentState L K) → Prop} {n P1 : ℕ}
    (hpost : Phase0PostToPhase1Floors (L := L) (K := K) Post0 n P1)
    {b : Config (AgentState L K)} (hb : Post0 b) :
    Phase1DrainReady (L := L) (K := K) n P1 b :=
  ⟨hpost.to_phase1 b hb, hpost.hext b hb, hpost.hpull b hb⟩

/-- `extremeU` is non-increasing on the strengthened slot-1 ready window.

This reuses the landed genuine `Phase1Win` monotonicity. -/
theorem potNonincrOn_extremeU_ready (n P1 : ℕ) :
    OneSidedCancel.PotNonincrOn
      (fun c => Phase1DrainReady (L := L) (K := K) n P1 c)
      (NonuniformMajority L K).transitionKernel
      (fun c => Phase1Convergence.extremeU c) := by
  intro c hc
  exact (PhaseOnlyWindows.potNonincrOn_extremeU_phase1Win
    (L := L) (K := K) n) c hc.genuine

/-- Slot-1 per-level `hdrop` on the strengthened ready window.

This is exactly the landed D7 rectangle/floor path:
`Phase1DrainReady` supplies `hext` and `hpull`, and
`PhaseWinDrain.phase1_drop_floor_of_phase1Win` supplies the one-step drop floor. -/
theorem hdrop1_ready (n P1 : ℕ) (hn : 2 ≤ n) :
    ∀ m, ∀ b : Config (AgentState L K),
      Phase1DrainReady (L := L) (K := K) n P1 b →
      Phase1Convergence.extremeU b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ
        ≤ DrainEngine.qHat P1 n m := by
  intro m b hb hbm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact DrainEngine.qHat_zero_bound P1 n
      (Phase1Convergence.extremeU (L := L) (K := K)) b
  · rw [DrainEngine.qHat_eq_on_pos P1 n m hmpos]
    unfold DrainRates.levelRate
    exact DrainThreading.extremeU_hdrop_of_floor m
      (ENNReal.ofReal ((P1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
      (PhaseWinDrain.phase1_drop_floor_of_phase1Win
        (L := L) (K := K) n hn b hb.genuine P1 hb.hext hb.hpull)

/-- The single nontrivial slot-1 survival atom over the strengthened ready window.

This is the minimal satisfiable replacement for trying to prove a small escape tail from
bare `Phase1Win`.  It says: while in the strengthened ready gate, the one-step mass
of leaving that gate is at most `η`.

A concrete discharge should clone the `WindowSurvival`/`ClockZeroTail` at-risk-counter
pattern, but additionally prove persistence of the D15 structural floors through the
slot-1 window. -/
structure Phase1ReadyEscapeBound (n P1 : ℕ) (η : ℝ≥0∞) : Prop where
  hesc :
    ∀ x, Phase1DrainReady (L := L) (K := K) n P1 x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ Phase1DrainReady (L := L) (K := K) n P1 y} ≤ η

/-- Slot 1 survival on the strengthened ready window with an explicit internal
drain budget.  The summed tail is accepted directly: this is the exact contract
of `WindowSurvival.slotSurvival`, and unlike `budgetNN` it leaves room for a
strictly positive escape allocation. -/
noncomputable def phase1ReadySurvivalBudgeted {n : ℕ}
    (P1 M₀ : ℕ) (hn : 2 ≤ n)
    (η : ℝ≥0∞) (hesc : Phase1ReadyEscapeBound (L := L) (K := K) n P1 η)
    (tWin1 : ℕ → ℕ)
    (drainε : ℝ≥0)
    (hDrain : (∑ m ∈ Finset.Icc 1 M₀,
        (DrainEngine.qHat P1 n m) ^ (tWin1 m) : ℝ≥0∞)
          ≤ (drainε : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  WindowSurvival.slotSurvival
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase1DrainReady (L := L) (K := K) n P1 c)
    (fun c => Phase1Convergence.extremeU c)
    (potNonincrOn_extremeU_ready (L := L) (K := K) n P1)
    (DrainEngine.qHat P1 n)
    (by rw [DrainEngine.qHat_zero])
    (hdrop1_ready (L := L) (K := K) n P1 hn)
    η hesc.hesc
    tWin1 M₀ drainε escapeε hDrain hescε

/-- `D`-calibrated specialization: the drain tail spends `1/(D n²)` and the
escape tail remains separately allocated. -/
noncomputable def phase1ReadySurvivalDivided {D n : ℕ}
    (P1 M₀ : ℕ) (hD1 : 1 ≤ D) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (η : ℝ≥0∞) (hesc : Phase1ReadyEscapeBound (L := L) (K := K) n P1 η)
    (tWin1 : ℕ → ℕ)
    (hpt1 : ∀ m ∈ Finset.Icc 1 M₀,
      (DrainEngine.qHat P1 n m) ^ (tWin1 m) ≤
        (DrainCalibration.budgetNN (D * M₀) n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  phase1ReadySurvivalBudgeted
    (L := L) (K := K)
    P1 M₀ hn η hesc tWin1
    (Real.toNNReal (1 / ((D : ℝ) * (n : ℝ) ^ 2)))
    (DrainEngine.qHat_sum_budget_div hD1 hn hM1 tWin1 hpt1)
    escapeε hescε

/-- Legacy full-budget specialization of `phase1ReadySurvivalBudgeted`.

This is the sound slot-1 survival constructor: no all-Main assumption, and no false
universal structural floors over bare `Phase1Win`.  It reuses
`WindowSurvival.slotSurvival` and the landed genuine D7 drop machinery. -/
noncomputable def phase1ReadySurvival {n : ℕ}
    (P1 M₀ : ℕ) (hn : 2 ≤ n) (hM1 : 1 ≤ M₀)
    (η : ℝ≥0∞) (hesc : Phase1ReadyEscapeBound (L := L) (K := K) n P1 η)
    (tWin1 : ℕ → ℕ)
    (hpt1 : ∀ m ∈ Finset.Icc 1 M₀,
      (DrainEngine.qHat P1 n m) ^ (tWin1 m) ≤
        (DrainCalibration.budgetNN M₀ n : ℝ≥0∞))
    (escapeε : ℝ≥0)
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  phase1ReadySurvivalBudgeted
    (L := L) (K := K)
    P1 M₀ hn η hesc tWin1
    (Real.toNNReal (1 / (n : ℝ) ^ 2))
    (DrainEngine.qHat_sum_budget hn hM1 tWin1 hpt1)
    escapeε hescε

/-- The exact old V5.1 slot-1 input surface, bundled as one atom.

This is provided only to make the landed/open boundary explicit: these are precisely the
three facts `SurvivalWorkHypotheses` still asks over the bare `Phase1Win` gate.  The nontrivial
escape tail and the two floors are not derivable from the definition of `Phase1Win`
alone. -/
structure Phase1WinFloorHypotheses (n P1 : ℕ) (η : ℝ≥0∞) : Prop where
  hescW1 : ∀ x, PhaseOnlyWindows.Phase1Win (L := L) (K := K) n x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n y} ≤ η
  hext1H : ∀ b : Config (AgentState L K),
    PhaseOnlyWindows.Phase1Win (L := L) (K := K) n b →
      1 ≤ (DrainThreading.extremePosSet L K).sum b.count
  hpull1H : ∀ b : Config (AgentState L K),
    PhaseOnlyWindows.Phase1Win (L := L) (K := K) n b →
      P1 ≤ (DrainThreading.pullPosSet L K).sum b.count

/-- Fill the three V5.1 slot-1 fields from the bundled atom. -/
theorem hescW1_of_floorHypotheses {n P1 : ℕ} {η : ℝ≥0∞}
    (A : Phase1WinFloorHypotheses (L := L) (K := K) n P1 η) :
    ∀ x, PhaseOnlyWindows.Phase1Win (L := L) (K := K) n x →
      (NonuniformMajority L K).transitionKernel x
        {y | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n y} ≤ η :=
  A.hescW1

theorem hext1H_of_floorHypotheses {n P1 : ℕ} {η : ℝ≥0∞}
    (A : Phase1WinFloorHypotheses (L := L) (K := K) n P1 η) :
    ∀ b : Config (AgentState L K),
      PhaseOnlyWindows.Phase1Win (L := L) (K := K) n b →
        1 ≤ (DrainThreading.extremePosSet L K).sum b.count :=
  A.hext1H

theorem hpull1H_of_floorHypotheses {n P1 : ℕ} {η : ℝ≥0∞}
    (A : Phase1WinFloorHypotheses (L := L) (K := K) n P1 η) :
    ∀ b : Config (AgentState L K),
      PhaseOnlyWindows.Phase1Win (L := L) (K := K) n b →
        P1 ≤ (DrainThreading.pullPosSet L K).sum b.count :=
  A.hpull1H

#print axioms hescW1_trivial
#print axioms phase1DrainReady_of_phase0Post
#print axioms potNonincrOn_extremeU_ready
#print axioms hdrop1_ready
#print axioms phase1ReadySurvival
#print axioms phase1ReadySurvivalBudgeted
#print axioms phase1ReadySurvivalDivided
#print axioms hescW1_of_floorHypotheses
#print axioms hext1H_of_floorHypotheses
#print axioms hpull1H_of_floorHypotheses

end Phase1ReadySurvival

end Ripple.PopulationProtocol.ExactMajority
