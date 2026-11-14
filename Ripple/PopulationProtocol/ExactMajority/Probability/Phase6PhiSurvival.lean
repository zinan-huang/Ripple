/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-6 survival from the base-4 multiplicative drift

This file specializes the killed-kernel multiplicative-drift engine to the
paper's phase-6 potential.  The invariant is the strengthened
`Phase6DrainReady` window: in particular, the sampled Reserve floor is carried
explicitly and is not inferred from the bare phase window.

The drift tail spends `1 / (D n^2)` and the window-escape tail is kept as a
separate positive budget.  The public postcondition is expressed with the
existing `highMass` potential used by the phase chain; the base-4 potential has
the same zero set.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.DriftHorizon
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiBound
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiDropSum

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6PhiSurvival

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-- Genuine phase-6 survival from the scheduler-weighted base-4 drift.

The output keeps the exact ready-gate precondition and the phase-chain's
`highMass = 0` postcondition.  Internally, `phiMass` is bounded at entry by
`phase6PhiMax n l`; its zero-set is then recut to `highMass = 0`.
-/
noncomputable def phase6PhiSurvival
    {n : ℕ} (hn : 2 ≤ n)
    (D : ℕ) (hD : 1 ≤ D)
    (rσ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hK₀ : 1 ≤ K₀) (hK₀n : K₀ ≤ n)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞)
    (hesc : Phase678ReadySurvival.Phase6ReadyEscapeBound
      (L := L) (K := K) n rσ l hl1 hlL i K₀ η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon (K₀ : ℝ) n
          (Phase6PhiPotential.phase6PhiMax n l) D : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel := by
  let Inv : Config (AgentState L K) → Prop :=
    fun c => Phase678ReadySurvival.Phase6DrainReady
      (L := L) (K := K) n rσ l hl1 hlL i K₀ c
  let Φ : Config (AgentState L K) → ℕ :=
    fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l c
  let Φmax : ℕ := Phase6PhiPotential.phase6PhiMax n l
  let r : ℝ≥0∞ :=
    1 - ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
  let T : ℕ := DriftSurvival.driftHorizon (K₀ : ℝ) n Φmax D

  have hn1 : 1 ≤ n := by omega
  have hΦmax : 1 ≤ Φmax := by
    exact Phase6PhiPotential.one_le_phase6PhiMax n l hn1
  have hK₀R0 : (0 : ℝ) < (K₀ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK₀)
  have hn_mul : n ≤ n * (n - 1) := by
    calc
      n = n * 1 := by omega
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
  have hK₀mul : K₀ ≤ n * (n - 1) := hK₀n.trans hn_mul
  have hK₀R : (K₀ : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    exact_mod_cast hK₀mul
  have hr : r ≤ 1 := by
    dsimp [r]
    exact tsub_le_self
  have hdrift :
      ∀ c, Inv c →
        ∫⁻ c', (Φ c' : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel c)
          ≤ r * (Φ c : ℝ≥0∞) := by
    simpa [Inv, Φ, r] using
      (Phase6PhiDropSum.phase6_phi_weighted_drift
        (L := L) (K := K) n rσ l hn hl1 hlL i K₀ hhgt hhne)
  have hdrain :
      r ^ T * (Φmax : ℝ≥0∞) ≤
        (DriftSurvival.driftBudgetNN D n : ℝ≥0∞) := by
    simpa [r, T, Φmax] using
      (DriftSurvival.drift_pow_le_budget_sub
        (B := (K₀ : ℝ)) (n := n) (Φmax := Phase6PhiPotential.phase6PhiMax n l)
        (D := D) hn hΦmax hD hK₀R0 hK₀R)
  let base : PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
    DriftSurvival.driftSurvivalPhase
      (NonuniformMajority L K).transitionKernel Inv Φ r hr hdrift
      η hesc.hesc T Φmax (DriftSurvival.driftBudgetNN D n) escapeε
      hdrain (by simpa [T, Φmax] using hescε)
  exact
    { Pre := Inv
      Post := fun c => Inv c ∧
        Phase6Convergence.highMass (L := L) (K := K) l c = 0
      t := T
      ε := DriftSurvival.driftBudgetNN D n + escapeε
      convergence := by
        intro c hc
        have hΦ : Φ c ≤ Φmax := by
          exact Phase6PhiPotential.phiMass_le_phase6PhiMax l n c hc.win
        refine le_trans (measure_mono ?_) (base.convergence c ⟨hc, hΦ⟩)
        intro c' hc'
        dsimp only [Inv, Φ] at hc' ⊢
        intro hpost
        exact hc' ⟨hpost.1,
          Phase6PhiDrift.highMass_eq_zero_of_phiMass_eq_zero
            (L := L) (K := K) l c' hpost.2⟩ }

@[simp] theorem phase6PhiSurvival_t
    {n : ℕ} (hn : 2 ≤ n)
    (D : ℕ) (hD : 1 ≤ D)
    (rσ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hK₀ : 1 ≤ K₀) (hK₀n : K₀ ≤ n)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞)
    (hesc : Phase678ReadySurvival.Phase6ReadyEscapeBound
      (L := L) (K := K) n rσ l hl1 hlL i K₀ η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon (K₀ : ℝ) n
          (Phase6PhiPotential.phase6PhiMax n l) D : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase6PhiSurvival (L := L) (K := K) hn D hD rσ l hl1 hlL i K₀ hK₀ hK₀n
      hhgt hhne η hesc escapeε hescε).t =
      DriftSurvival.driftHorizon (K₀ : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) D := by
  rfl

@[simp] theorem phase6PhiSurvival_epsilon
    {n : ℕ} (hn : 2 ≤ n)
    (D : ℕ) (hD : 1 ≤ D)
    (rσ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hK₀ : 1 ≤ K₀) (hK₀n : K₀ ≤ n)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞)
    (hesc : Phase678ReadySurvival.Phase6ReadyEscapeBound
      (L := L) (K := K) n rσ l hl1 hlL i K₀ η)
    (escapeε : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon (K₀ : ℝ) n
          (Phase6PhiPotential.phase6PhiMax n l) D : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞)) :
    (phase6PhiSurvival (L := L) (K := K) hn D hD rσ l hl1 hlL i K₀ hK₀ hK₀n
      hhgt hhne η hesc escapeε hescε).ε =
      DriftSurvival.driftBudgetNN D n + escapeε := by
  rfl

theorem phase6PhiSurvival_epsilon_le_delta
    {n : ℕ} (hn : 2 ≤ n)
    (D : ℕ) (hD : 1 ≤ D)
    (rσ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hK₀ : 1 ≤ K₀) (hK₀n : K₀ ≤ n)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞)
    (hesc : Phase678ReadySurvival.Phase6ReadyEscapeBound
      (L := L) (K := K) n rσ l hl1 hlL i K₀ η)
    (escapeε δ : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon (K₀ : ℝ) n
          (Phase6PhiPotential.phase6PhiMax n l) D : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞))
    (hTotal :
      (DriftSurvival.driftBudgetNN D n : ℝ≥0∞) + (escapeε : ℝ≥0∞)
        ≤ (δ : ℝ≥0∞)) :
    ((phase6PhiSurvival (L := L) (K := K) hn D hD rσ l hl1 hlL i K₀ hK₀ hK₀n
      hhgt hhne η hesc escapeε hescε).ε : ℝ≥0∞) ≤ (δ : ℝ≥0∞) := by
  rw [phase6PhiSurvival_epsilon, ENNReal.coe_add]
  exact hTotal

theorem phase6PhiSurvival_epsilon_le_inv_sq
    {n : ℕ} (hn : 2 ≤ n)
    (D : ℕ) (hD : 1 ≤ D)
    (rσ : Sign) (l : ℕ) (hl1 : 1 ≤ l) (hlL : l ≤ L)
    (i : Fin (L + 1)) (K₀ : ℕ) (hK₀ : 1 ≤ K₀) (hK₀n : K₀ ≤ n)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (η : ℝ≥0∞)
    (hesc : Phase678ReadySurvival.Phase6ReadyEscapeBound
      (L := L) (K := K) n rσ l hl1 hlL i K₀ η)
    (escapeε δ : ℝ≥0)
    (hescε :
      ((DriftSurvival.driftHorizon (K₀ : ℝ) n
          (Phase6PhiPotential.phase6PhiMax n l) D : ℕ) : ℝ≥0∞) * η
        ≤ (escapeε : ℝ≥0∞))
    (hTotal :
      (DriftSurvival.driftBudgetNN D n : ℝ≥0∞) + (escapeε : ℝ≥0∞)
        ≤ (δ : ℝ≥0∞))
    (hδ : (δ : ℝ≥0∞) ≤ 1 / (n : ℝ≥0∞) ^ 2) :
    ((phase6PhiSurvival (L := L) (K := K) hn D hD rσ l hl1 hlL i K₀ hK₀ hK₀n
      hhgt hhne η hesc escapeε hescε).ε : ℝ≥0∞) ≤
        1 / (n : ℝ≥0∞) ^ 2 :=
  (phase6PhiSurvival_epsilon_le_delta (L := L) (K := K)
    hn D hD rσ l hl1 hlL i K₀ hK₀ hK₀n hhgt hhne η hesc escapeε δ hescε hTotal).trans hδ

#print axioms phase6PhiSurvival
#print axioms phase6PhiSurvival_t
#print axioms phase6PhiSurvival_epsilon
#print axioms phase6PhiSurvival_epsilon_le_delta
#print axioms phase6PhiSurvival_epsilon_le_inv_sq

end Phase6PhiSurvival
end Ripple.PopulationProtocol.ExactMajority
