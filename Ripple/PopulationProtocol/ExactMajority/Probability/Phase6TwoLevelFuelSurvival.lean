/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-6 drift from the paper's two-case Reserve fuel

Lemma 7.2 of the paper chooses either Reserve class `l`, or the adjacent
classes `l,l+1`.  The persistent deterministic resource for that choice is
`TwoLevelFuelLedger`.  This file consumes that disjunction without selecting a
branch globally: an adjacent union of size `K₀` contains a single class of size
at least `ceil(K₀/2)`, which is enough for the existing weighted rectangle.

Producing the two-level ledger at the Phase-5/6 seam remains an explicit
upstream concentration-and-mass obligation.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6FuelSurvival

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6TwoLevelFuelSurvival

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-- The integer half-floor retained after choosing one of two adjacent pools. -/
def halfFuel (K₀ : ℕ) : ℕ := (K₀ + 1) / 2

theorem halfFuel_le_left_or_right {K₀ a b : ℕ} (h : K₀ ≤ a + b) :
    halfFuel K₀ ≤ a ∨ halfFuel K₀ ≤ b := by
  unfold halfFuel
  omega

theorem one_le_halfFuel {K₀ : ℕ} (hK₀ : 1 ≤ K₀) :
    1 ≤ halfFuel K₀ := by
  unfold halfFuel
  omega

theorem halfFuel_le_self {K₀ : ℕ} (hK₀ : 1 ≤ K₀) :
    halfFuel K₀ ≤ K₀ := by
  unfold halfFuel
  omega

/-- Persistent Phase-6 work gate for the two cases in paper Lemma 7.2. -/
structure Phase6TwoLevelReady (n : ℕ) (l : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K)) : Prop where
  win : Phase6Convergence.Phase6Win (L := L) (K := K) n c
  ledger : Phase6FuelLedger.TwoLevelFuelLedger
    (L := L) (K := K) l K₀ c

/-- A two-level ledger supplies one of the two concrete scheduler rectangles
with the `ceil(K₀/2)` floor. -/
theorem adjacent_reserve_floor_choice
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ : ℕ) (c : Config (AgentState L K))
    (hledger : Phase6FuelLedger.TwoLevelFuelLedger
      (L := L) (K := K) l K₀ c) :
    halfFuel K₀ ≤
        (Phase6Convergence.reserveAtHour6
          (L := L) (K := K) l).sum c.count ∨
      halfFuel K₀ ≤
        (Phase6Convergence.reserveAtHour6 (L := L) (K := K)
          (Phase6FuelLedger.highIndex l hl)).sum c.count := by
  have hfloor := Phase6FuelLedger.twoLevelFuelLedger_union_floor
    (L := L) (K := K) l hl K₀ c hledger
  rw [Phase6FuelLedger.twoReserveFuel_eq_reserveAtHour6_add
    (L := L) (K := K) l hl c] at hfloor
  exact halfFuel_le_left_or_right hfloor

/-- The paper's lower-or-adjacent fuel case gives the same base-4 drift as a
single live rectangle, losing only the unavoidable factor two in the displayed
rate when we choose one of the two adjacent classes. -/
theorem phase6_phi_dropSum_floor_of_twoLevelFuel
    (n : ℕ) (hn : 2 ≤ n)
    (l : Fin (L + 1)) (hlpos : 1 ≤ l.val) (hl : l.val + 2 ≤ L)
    (K₀ : ℕ) (c : Config (AgentState L K))
    (hc : Phase6TwoLevelReady (L := L) (K := K) n l K₀ c) :
    ENNReal.ofReal
          ((halfFuel K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) *
        (Phase6PhiPotential.phiMass
          (L := L) (K := K) l.val c : ℝ≥0∞) ≤
      WeightedDriftDropSum.weightedDropSum (NonuniformMajority L K)
        (fun b => Phase6PhiPotential.phiMass
          (L := L) (K := K) l.val b) c := by
  rcases adjacent_reserve_floor_choice
      (L := L) (K := K) l hl K₀ c hc.ledger with hlo | hhi
  · exact Phase6PhiDropSum.phase6_phi_dropSum_floor_of_reserveFloor
      (L := L) (K := K) l.val n hn l (halfFuel K₀)
      (by omega) (by omega) c hc.win hlo
  · exact Phase6PhiDropSum.phase6_phi_dropSum_floor_of_reserveFloor
      (L := L) (K := K) l.val n hn
      (Phase6FuelLedger.highIndex l hl) (halfFuel K₀)
      (by simp [Phase6FuelLedger.highIndex])
      (by simp [Phase6FuelLedger.highIndex]; omega) c hc.win hhi

/-- Multiplicative base-4 drift on the persistent two-level fuel gate. -/
theorem phase6_phi_weighted_drift_twoLevel
    (n : ℕ) (hn : 2 ≤ n)
    (l : Fin (L + 1)) (hlpos : 1 ≤ l.val) (hl : l.val + 2 ≤ L)
    (K₀ : ℕ) :
    DyadicMassDrainTight.WeightedDyadicMassDrift (L := L) (K := K)
      (fun c => Phase6TwoLevelReady (L := L) (K := K) n l K₀ c)
      (fun c => Phase6PhiPotential.phiMass
        (L := L) (K := K) l.val c)
      (1 - ENNReal.ofReal
        ((halfFuel K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) := by
  refine WeightedDriftDropSum.weighted_dyadic_mass_drift_on_of_dropSum
    (L := L) (K := K)
    (fun c => Phase6TwoLevelReady (L := L) (K := K) n l K₀ c)
    (fun c => Phase6PhiPotential.phiMass
      (L := L) (K := K) l.val c)
    (ENNReal.ofReal
      ((halfFuel K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))))
    (by simp) ?_ ?_ ?_
  · intro c hc
    rw [hc.win.1]
    exact hn
  · intro c hc pair
    exact Phase6PhiDrift.phiMass_stepOrSelf_le
      (L := L) (K := K) l.val n c hc.win pair.1 pair.2
  · intro c hc
    exact phase6_phi_dropSum_floor_of_twoLevelFuel
      (L := L) (K := K) n hn l hlpos hl K₀ c hc

/-- The two-level ledger has zero structural escape; only the real Phase-6
window can fail. -/
theorem twoLevelReady_escape_le_winEscape
    (n : ℕ) (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ : ℕ) (eta : ℝ≥0∞)
    (hesc : Phase6FuelSurvival.Phase6WinEscapeBound
      (L := L) (K := K) n eta)
    (c : Config (AgentState L K))
    (hc : Phase6TwoLevelReady (L := L) (K := K) n l K₀ c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ Phase6TwoLevelReady (L := L) (K := K) n l K₀ c'} ≤ eta := by
  let badWin : Set (Config (AgentState L K)) :=
    {c' | ¬ Phase6Convergence.Phase6Win (L := L) (K := K) n c'}
  let badLedger : Set (Config (AgentState L K)) :=
    {c' | ¬ Phase6FuelLedger.TwoLevelFuelLedger
      (L := L) (K := K) l K₀ c'}
  have hsub :
      {c' | ¬ Phase6TwoLevelReady (L := L) (K := K) n l K₀ c'} ⊆
        badWin ∪ badLedger := by
    intro c' hc'
    by_cases hw : Phase6Convergence.Phase6Win (L := L) (K := K) n c'
    · right
      intro hledger
      exact hc' ⟨hw, hledger⟩
    · exact Or.inl hw
  have hledgerZero :
      (NonuniformMajority L K).transitionKernel c badLedger = 0 := by
    simpa [badLedger] using
      (Phase6FuelLedger.transitionKernel_not_twoLevelFuelLedger_eq_zero
        (L := L) (K := K) l hl K₀ n c hc.win hc.ledger)
  calc
    (NonuniformMajority L K).transitionKernel c
          {c' | ¬ Phase6TwoLevelReady (L := L) (K := K) n l K₀ c'}
        ≤ (NonuniformMajority L K).transitionKernel c
            (badWin ∪ badLedger) := measure_mono hsub
    _ ≤ (NonuniformMajority L K).transitionKernel c badWin +
          (NonuniformMajority L K).transitionKernel c badLedger :=
        measure_union_le _ _
    _ ≤ eta + 0 := add_le_add
      (by simpa [badWin] using hesc.hesc c hc.win)
      (le_of_eq hledgerZero)
    _ = eta := add_zero eta

/-- Genuine Phase-6 work for the full two-case paper resource. -/
noncomputable def phase6TwoLevelFuelSurvival
    {n : ℕ} (hn : 2 ≤ n)
    (D : ℕ) (hD : 1 ≤ D)
    (l : Fin (L + 1)) (hlpos : 1 ≤ l.val) (hl : l.val + 2 ≤ L)
    (K₀ : ℕ) (hK₀ : 1 ≤ K₀) (hK₀n : K₀ ≤ n)
    (eta : ℝ≥0∞)
    (hesc : Phase6FuelSurvival.Phase6WinEscapeBound
      (L := L) (K := K) n eta)
    (escapeEps : ℝ≥0)
    (hescEps :
      ((DriftSurvival.driftHorizon (halfFuel K₀ : ℝ) n
          (Phase6PhiPotential.phase6PhiMax n l.val) D : ℕ) : ℝ≥0∞) * eta
        ≤ (escapeEps : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel := by
  let Inv : Config (AgentState L K) → Prop :=
    fun c => Phase6TwoLevelReady (L := L) (K := K) n l K₀ c
  let Phi : Config (AgentState L K) → ℕ :=
    fun c => Phase6PhiPotential.phiMass (L := L) (K := K) l.val c
  let PhiMax : ℕ := Phase6PhiPotential.phase6PhiMax n l.val
  let rate : ℝ≥0∞ :=
    1 - ENNReal.ofReal
      ((halfFuel K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
  let T : ℕ := DriftSurvival.driftHorizon (halfFuel K₀ : ℝ) n PhiMax D
  have hn1 : 1 ≤ n := by omega
  have hPhiMax : 1 ≤ PhiMax :=
    Phase6PhiPotential.one_le_phase6PhiMax n l.val hn1
  have hhalfPosN : 1 ≤ halfFuel K₀ := one_le_halfFuel hK₀
  have hhalfPos : (0 : ℝ) < (halfFuel K₀ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hhalfPosN)
  have hnMul : n ≤ n * (n - 1) := by
    calc
      n = n * 1 := by omega
      _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
  have hhalfN : halfFuel K₀ ≤ n :=
    (halfFuel_le_self hK₀).trans hK₀n
  have hhalfMul : halfFuel K₀ ≤ n * (n - 1) := hhalfN.trans hnMul
  have hhalfR : (halfFuel K₀ : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    exact_mod_cast hhalfMul
  have hrate : rate ≤ 1 := by
    dsimp [rate]
    exact tsub_le_self
  have hdrift :
      ∀ c, Inv c →
        ∫⁻ c', (Phi c' : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel c)
          ≤ rate * (Phi c : ℝ≥0∞) := by
    simpa [Inv, Phi, rate] using
      (phase6_phi_weighted_drift_twoLevel
        (L := L) (K := K) n hn l hlpos hl K₀)
  have hescape :
      ∀ c, Inv c →
        (NonuniformMajority L K).transitionKernel c {c' | ¬ Inv c'} ≤ eta := by
    intro c hc
    simpa [Inv] using twoLevelReady_escape_le_winEscape
      (L := L) (K := K) n l hl K₀ eta hesc c hc
  have hdrain :
      rate ^ T * (PhiMax : ℝ≥0∞) ≤
        (DriftSurvival.driftBudgetNN D n : ℝ≥0∞) := by
    simpa [rate, T, PhiMax] using
      (DriftSurvival.drift_pow_le_budget_sub
        (B := (halfFuel K₀ : ℝ)) (n := n)
        (Φmax := Phase6PhiPotential.phase6PhiMax n l.val) (D := D)
        hn hPhiMax hD hhalfPos hhalfR)
  let base : PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
    DriftSurvival.driftSurvivalPhase
      (NonuniformMajority L K).transitionKernel Inv Phi rate hrate hdrift
      eta hescape T PhiMax (DriftSurvival.driftBudgetNN D n) escapeEps
      hdrain (by simpa [T, PhiMax] using hescEps)
  exact
    { Pre := Inv
      Post := fun c => Inv c ∧
        Phase6Convergence.highMass (L := L) (K := K) l.val c = 0
      t := T
      ε := DriftSurvival.driftBudgetNN D n + escapeEps
      convergence := by
        intro c hc
        have hPhi : Phi c ≤ PhiMax :=
          Phase6PhiPotential.phiMass_le_phase6PhiMax l.val n c hc.win
        refine le_trans (measure_mono ?_) (base.convergence c ⟨hc, hPhi⟩)
        intro c' hc'
        dsimp only [Inv, Phi] at hc' ⊢
        intro hpost
        exact hc' ⟨hpost.1,
          Phase6PhiDrift.highMass_eq_zero_of_phiMass_eq_zero
            (L := L) (K := K) l.val c' hpost.2⟩ }

#print axioms halfFuel_le_left_or_right
#print axioms adjacent_reserve_floor_choice
#print axioms phase6_phi_dropSum_floor_of_twoLevelFuel
#print axioms phase6_phi_weighted_drift_twoLevel
#print axioms twoLevelReady_escape_le_winEscape
#print axioms phase6TwoLevelFuelSurvival

end Phase6TwoLevelFuelSurvival
end Ripple.PopulationProtocol.ExactMajority
