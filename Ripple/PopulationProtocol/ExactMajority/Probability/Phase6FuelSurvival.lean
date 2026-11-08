/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-6 drift on the persistent Reserve-fuel ledger

The earlier `Phase6DrainReady` gate retained a transient Main witness in the
working invariant.  That witness is incompatible with the desired zero-mass
postcondition.  The weighted rectangle never uses it: it needs only the
Phase-6 window and a live Reserve floor.

This file obtains that floor from `Phase6FuelLedger.FuelLedger`.  The ledger
accounts for every future split below the sampled hour and is deterministically
preserved while the chain remains in Phase 6.  Consequently the only escape
budget left in this work instance is the genuine Phase-6 clock/window escape.
Producing the ledger at the Phase-5/6 boundary remains an explicit upstream
obligation.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.DriftHorizon
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6FuelLedger
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiBound
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiDropSum

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6FuelSurvival

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-- Persistent Phase-6 work gate: the honest phase window plus the exact
Reserve-fuel ledger. -/
structure Phase6FuelReady (n : ℕ) (i : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K)) : Prop where
  win : Phase6Convergence.Phase6Win (L := L) (K := K) n c
  ledger : Phase6FuelLedger.FuelLedger (L := L) (K := K) i K₀ c

/-- The fuel ledger exposes exactly the live Reserve floor consumed by the
weighted Phase-6 rectangle. -/
theorem reserve_floor_of_fuelReady
    (n : ℕ) (i : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K))
    (hc : Phase6FuelReady (L := L) (K := K) n i K₀ c) :
    K₀ ≤ (Phase6Convergence.reserveAtHour6
      (L := L) (K := K) i).sum c.count := by
  rw [← Phase6FuelLedger.reserveFuel_eq_reserveAtHour6
    (L := L) (K := K) i c]
  exact Phase6FuelLedger.fuelLedger_reserveFuel_floor
    (L := L) (K := K) i K₀ c hc.ledger

/-- Base-4 multiplicative drift on the persistent fuel gate. -/
theorem phase6_phi_weighted_drift_fuel
    (n l : ℕ) (hn : 2 ≤ n)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L) :
    DyadicMassDrainTight.WeightedDyadicMassDrift (L := L) (K := K)
      (fun c => Phase6FuelReady (L := L) (K := K) n i K₀ c)
      (fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l c)
      (1 - ENNReal.ofReal
        ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) := by
  refine WeightedDriftDropSum.weighted_dyadic_mass_drift_on_of_dropSum
    (L := L) (K := K)
    (fun c => Phase6FuelReady (L := L) (K := K) n i K₀ c)
    (fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l c)
    (ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))))
    (by simp) ?_ ?_ ?_
  · intro c hc
    rw [hc.win.1]
    exact hn
  · intro c hc pair
    exact Phase6PhiDrift.phiMass_stepOrSelf_le
      (L := L) (K := K) l n c hc.win pair.1 pair.2
  · intro c hc
    exact Phase6PhiDropSum.phase6_phi_dropSum_floor_of_reserveFloor
      (L := L) (K := K) l n hn i K₀ hhgt hhne c hc.win
      (reserve_floor_of_fuelReady
        (L := L) (K := K) n i K₀ c hc)

/-- A one-step escape estimate for the genuine Phase-6 phase window. -/
structure Phase6WinEscapeBound (n : ℕ) (η : ℝ≥0∞) : Prop where
  hesc : ∀ c, Phase6Convergence.Phase6Win (L := L) (K := K) n c →
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n c'} ≤ η

/-- The fuel gate has no structural escape beyond the Phase-6 window escape.
The ledger-failure event has real-kernel mass zero. -/
theorem fuelReady_escape_le_winEscape
    (n : ℕ) (i : Fin (L + 1)) (K₀ : ℕ) (η : ℝ≥0∞)
    (hesc : Phase6WinEscapeBound (L := L) (K := K) n η)
    (c : Config (AgentState L K))
    (hc : Phase6FuelReady (L := L) (K := K) n i K₀ c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ Phase6FuelReady (L := L) (K := K) n i K₀ c'} ≤ η := by
  let badWin : Set (Config (AgentState L K)) :=
    {c' | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n c'}
  let badLedger : Set (Config (AgentState L K)) :=
    {c' | ¬ Phase6FuelLedger.FuelLedger (L := L) (K := K) i K₀ c'}
  have hsub :
      {c' | ¬ Phase6FuelReady (L := L) (K := K) n i K₀ c'} ⊆
        badWin ∪ badLedger := by
    intro c' hc'
    by_cases hw : Phase6Convergence.Phase6Win (L := L) (K := K) n c'
    · right
      intro hl
      exact hc' ⟨hw, hl⟩
    · exact Or.inl hw
  have hledgerZero :
      (NonuniformMajority L K).transitionKernel c badLedger = 0 := by
    simpa [badLedger] using
      (Phase6FuelLedger.transitionKernel_not_fuelLedger_eq_zero
        (L := L) (K := K) i K₀ n c hc.win hc.ledger)
  calc
    (NonuniformMajority L K).transitionKernel c
          {c' | ¬ Phase6FuelReady (L := L) (K := K) n i K₀ c'}
        ≤ (NonuniformMajority L K).transitionKernel c (badWin ∪ badLedger) :=
          measure_mono hsub
    _ ≤ (NonuniformMajority L K).transitionKernel c badWin +
          (NonuniformMajority L K).transitionKernel c badLedger :=
        measure_union_le _ _
    _ ≤ η + 0 := add_le_add (by simpa [badWin] using hesc.hesc c hc.win)
      (le_of_eq hledgerZero)
    _ = η := add_zero η

/-- Honest Phase-6 work instance on the persistent fuel gate.

Its drift budget is `1/(D n²)`; `escapeε` is reserved only for leaving the
Phase-6 clock window. -/
noncomputable def phase6FuelSurvival
    {n : ℕ} (hn : 2 ≤ n)
    (D : ℕ) (hD : 1 ≤ D)
    (l : ℕ) (i : Fin (L + 1))
    (K₀ : ℕ) (hK₀ : 1 ≤ K₀) (hK₀n : K₀ ≤ n)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞) (hesc : Phase6WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon (K₀ : ℝ) n
          (Phase6PhiPotential.phase6PhiMax n l) D : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel := by
  let Inv : Config (AgentState L K) → Prop :=
    fun c => Phase6FuelReady (L := L) (K := K) n i K₀ c
  let Φ : Config (AgentState L K) → ℕ :=
    fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l c
  let Φmax : ℕ := Phase6PhiPotential.phase6PhiMax n l
  let r : ℝ≥0∞ :=
    1 - ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
  let T : ℕ := DriftSurvival.driftHorizon (K₀ : ℝ) n Φmax D
  have hn1 : 1 ≤ n := by omega
  have hΦmax : 1 ≤ Φmax :=
    Phase6PhiPotential.one_le_phase6PhiMax n l hn1
  have hK₀R0 : (0 : ℝ) < (K₀ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK₀)
  have hnMul : n ≤ n * (n - 1) := by
    calc
      n = n * 1 := by omega
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
  have hK₀Mul : K₀ ≤ n * (n - 1) := hK₀n.trans hnMul
  have hK₀R : (K₀ : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    exact_mod_cast hK₀Mul
  have hr : r ≤ 1 := by
    dsimp [r]
    exact tsub_le_self
  have hdrift :
      ∀ c, Inv c →
        ∫⁻ c', (Φ c' : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel c)
          ≤ r * (Φ c : ℝ≥0∞) := by
    simpa [Inv, Φ, r] using
      (phase6_phi_weighted_drift_fuel
        (L := L) (K := K) n l hn i K₀ hhgt hhne)
  have hescape :
      ∀ c, Inv c →
        (NonuniformMajority L K).transitionKernel c {c' | ¬ Inv c'} ≤ η := by
    intro c hc
    simpa [Inv] using fuelReady_escape_le_winEscape
      (L := L) (K := K) n i K₀ η hesc c hc
  have hdrain :
      r ^ T * (Φmax : ℝ≥0∞) ≤
        (DriftSurvival.driftBudgetNN D n : ℝ≥0∞) := by
    simpa [r, T, Φmax] using
      (DriftSurvival.drift_pow_le_budget_sub
        (B := (K₀ : ℝ)) (n := n)
        (Φmax := Phase6PhiPotential.phase6PhiMax n l) (D := D)
        hn hΦmax hD hK₀R0 hK₀R)
  let base : PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
    DriftSurvival.driftSurvivalPhase
      (NonuniformMajority L K).transitionKernel Inv Φ r hr hdrift
      η hescape T Φmax (DriftSurvival.driftBudgetNN D n) escapeε
      hdrain (by simpa [T, Φmax] using hescε)
  exact
    { Pre := Inv
      Post := fun c => Inv c ∧
        Phase6Convergence.highMass (L := L) (K := K) l c = 0
      t := T
      ε := DriftSurvival.driftBudgetNN D n + escapeε
      convergence := by
        intro c hc
        have hΦ : Φ c ≤ Φmax :=
          Phase6PhiPotential.phiMass_le_phase6PhiMax l n c hc.win
        refine le_trans (measure_mono ?_) (base.convergence c ⟨hc, hΦ⟩)
        intro c' hc'
        dsimp only [Inv, Φ] at hc' ⊢
        intro hpost
        exact hc' ⟨hpost.1,
          Phase6PhiDrift.highMass_eq_zero_of_phiMass_eq_zero
            (L := L) (K := K) l c' hpost.2⟩ }

@[simp] theorem phase6FuelSurvival_t
    {n : ℕ} (hn : 2 ≤ n) (D : ℕ) (hD : 1 ≤ D)
    (l : ℕ) (i : Fin (L + 1))
    (K₀ : ℕ) (hK₀ : 1 ≤ K₀) (hK₀n : K₀ ≤ n)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞) (hesc : Phase6WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0) (hescε :
      ((DriftSurvival.driftHorizon (K₀ : ℝ) n
          (Phase6PhiPotential.phase6PhiMax n l) D : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase6FuelSurvival (L := L) (K := K) hn D hD l i K₀ hK₀ hK₀n
      hhgt hhne η hesc escapeε hescε).t =
      DriftSurvival.driftHorizon (K₀ : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) D := rfl

@[simp] theorem phase6FuelSurvival_epsilon
    {n : ℕ} (hn : 2 ≤ n) (D : ℕ) (hD : 1 ≤ D)
    (l : ℕ) (i : Fin (L + 1))
    (K₀ : ℕ) (hK₀ : 1 ≤ K₀) (hK₀n : K₀ ≤ n)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞) (hesc : Phase6WinEscapeBound (L := L) (K := K) n η)
    (escapeε : ℝ≥0) (hescε :
      ((DriftSurvival.driftHorizon (K₀ : ℝ) n
          (Phase6PhiPotential.phase6PhiMax n l) D : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase6FuelSurvival (L := L) (K := K) hn D hD l i K₀ hK₀ hK₀n
      hhgt hhne η hesc escapeε hescε).ε =
      DriftSurvival.driftBudgetNN D n + escapeε := rfl

#print axioms reserve_floor_of_fuelReady
#print axioms phase6_phi_weighted_drift_fuel
#print axioms fuelReady_escape_le_winEscape
#print axioms phase6FuelSurvival
#print axioms phase6FuelSurvival_t
#print axioms phase6FuelSurvival_epsilon

end Phase6FuelSurvival
end Ripple.PopulationProtocol.ExactMajority
