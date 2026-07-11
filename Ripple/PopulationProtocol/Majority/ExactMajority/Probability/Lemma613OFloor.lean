/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty Lemma 6.13: the Phase-3 `O_h` split-fuel floor

This file proves the pointwise arithmetic part of Doty's Lemma 6.13:
if at least `0.97 |M|` Main agents have reached hour `h`, and at most
`2 rho |M|` Main agents are biased, then the unbiased reached-Main pool
`O_h` has size at least `(0.97 - 2 rho) |M|`.

The clock-synchronization input `0.97 |M| <= reachedMainCount` is kept as an
explicit hypothesis here.  The file then specializes `rho = rho_{ell-1}=0.408`
from `Lemma616TotalMass`, giving the final-hour `0.15 |M|` floor consumed by
`Lemma615MassAbove`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma615MassAboveDefs
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma616TotalMass
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6Convergence
import Mathlib.Tactic

namespace ExactMajority
namespace Lemma613OFloor

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- Main agents whose hour has reached `l`.  This is the pointwise
clock-synchronization surface for Doty Lemma 6.13. -/
def phase3ReachedMainCount (l : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = Role.main ∧ l ≤ a.hour.val) c

/-- Biased Main agents whose hour has reached `l`. -/
def phase3BiasedReachedMainCount (l : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = Role.main ∧ a.bias ≠ Bias.zero ∧ l ≤ a.hour.val) c

/-- All biased Main agents.  This is the count bounded from the previous-hour
total mass by the usual mass-to-count conversion. -/
def phase3BiasedMainCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = Role.main ∧ a.bias ≠ Bias.zero) c

/-- `phase3OFuelCount` as a multiset count. -/
theorem phase3OFuelCount_eq_countP (l : ℕ) (c : Config (AgentState L K)) :
    Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c =
      Multiset.countP
        (fun a : AgentState L K =>
          a.role = Role.main ∧ a.bias = Bias.zero ∧ l ≤ a.hour.val) c := by
  simpa [Lemma615MassAbove.phase3OFuelCount, Lemma615MassAbove.phase3OFuel] using
    (Phase6Convergence.countP_eq_sum_count6 (L := L) (K := K)
      (fun a : AgentState L K =>
        a.role = Role.main ∧ a.bias = Bias.zero ∧ l ≤ a.hour.val) c).symm

/-- Reached Main agents split into unbiased reached Mains (`O_l`) and biased
reached Mains. -/
theorem reachedMain_eq_ofuel_add_biasedReached (l : ℕ)
    (c : Config (AgentState L K)) :
    phase3ReachedMainCount (L := L) (K := K) l c =
      Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c
        + phase3BiasedReachedMainCount (L := L) (K := K) l c := by
  rw [phase3OFuelCount_eq_countP (L := L) (K := K) l c]
  let P : AgentState L K → Prop := fun a => a.role = Role.main ∧ l ≤ a.hour.val
  let Z : AgentState L K → Prop :=
    fun a => a.role = Role.main ∧ a.bias = Bias.zero ∧ l ≤ a.hour.val
  let B : AgentState L K → Prop :=
    fun a => a.role = Role.main ∧ a.bias ≠ Bias.zero ∧ l ≤ a.hour.val
  change Multiset.countP P c = Multiset.countP Z c + Multiset.countP B c
  induction c using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons]
      by_cases hr : a.role = Role.main
      · by_cases hh : l ≤ a.hour.val
        · have hP : P a := by
            simp [P, hr, hh]
          by_cases hb : a.bias = Bias.zero
          · have hZ : Z a := by
              simp [Z, hr, hh, hb]
            have hB : ¬ B a := by
              simp [B, hb]
            simp [hP, hZ, hB]
            omega
          · have hZ : ¬ Z a := by
              simp [Z, hb]
            have hB : B a := by
              simp [B, hr, hh, hb]
            simp [hP, hZ, hB]
            omega
        · have hP : ¬ P a := by
            simp [P, hh]
          have hZ : ¬ Z a := by
            simp [Z, hh]
          have hB : ¬ B a := by
            simp [B, hh]
          simpa [hP, hZ, hB] using ih
      · have hP : ¬ P a := by
          simp [P, hr]
        have hZ : ¬ Z a := by
          simp [Z, hr]
        have hB : ¬ B a := by
          simp [B, hr]
        simpa [hP, hZ, hB] using ih

/-- Biased reached Mains are a subcount of all biased Mains. -/
theorem biasedReachedMainCount_le_biasedMainCount (l : ℕ)
    (c : Config (AgentState L K)) :
    phase3BiasedReachedMainCount (L := L) (K := K) l c
      ≤ phase3BiasedMainCount (L := L) (K := K) c := by
  let P : AgentState L K → Prop :=
    fun a => a.role = Role.main ∧ a.bias ≠ Bias.zero ∧ l ≤ a.hour.val
  let Q : AgentState L K → Prop :=
    fun a => a.role = Role.main ∧ a.bias ≠ Bias.zero
  change Multiset.countP P c ≤ Multiset.countP Q c
  induction c using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons]
      by_cases hp : P a
      · have hq' : Q a := by
          dsimp [P, Q] at hp ⊢
          exact ⟨hp.1, hp.2.1⟩
        simp [hp, hq']
        omega
      · by_cases hq : Q a
        · simp [hp, hq]
          omega
        · simpa [hp, hq] using ih

/-- **Doty Lemma 6.13, pointwise arithmetic form.**

The theorem deliberately takes the clock-synchronization floor as `hReach`.
The mass-to-count input is the total biased-Main bound `hBiased`; only the
reached biased agents are subtracted, and they are a subcount of all biased
Mains. -/
theorem ofuel_floor (l : ℕ) (rho M : ℝ) (c : Config (AgentState L K))
    (hReach :
      (97 / 100 : ℝ) * M ≤ (phase3ReachedMainCount (L := L) (K := K) l c : ℝ))
    (hBiased :
      (phase3BiasedMainCount (L := L) (K := K) c : ℝ) ≤ 2 * rho * M) :
    (97 / 100 - 2 * rho) * M
      ≤ (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ) := by
  have hPart := reachedMain_eq_ofuel_add_biasedReached
    (L := L) (K := K) l c
  have hBiasedReachedLeTotalNat :=
    biasedReachedMainCount_le_biasedMainCount (L := L) (K := K) l c
  have hBiasedReachedLeTotal :
      (phase3BiasedReachedMainCount (L := L) (K := K) l c : ℝ)
        ≤ (phase3BiasedMainCount (L := L) (K := K) c : ℝ) := by
    exact_mod_cast hBiasedReachedLeTotalNat
  have hBiasedReached :
      (phase3BiasedReachedMainCount (L := L) (K := K) l c : ℝ) ≤ 2 * rho * M := by
    exact hBiasedReachedLeTotal.trans hBiased
  have hPartReal :
      (phase3ReachedMainCount (L := L) (K := K) l c : ℝ) =
        (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ)
          + (phase3BiasedReachedMainCount (L := L) (K := K) l c : ℝ) := by
    exact_mod_cast hPart
  nlinarith [hReach, hBiasedReached, hPartReal]

/-- Final-hour Doty Lemma 6.13: with `rho_{ell-1}=0.408`, the split-fuel
floor is at least `0.15 |M|`. -/
theorem ofuel_floor_final_hour (l : ℕ) (M : ℝ) (c : Config (AgentState L K))
    (hM : 0 ≤ M)
    (hReach :
      (97 / 100 : ℝ) * M ≤ (phase3ReachedMainCount (L := L) (K := K) l c : ℝ))
    (hBiased :
      (phase3BiasedMainCount (L := L) (K := K) c : ℝ)
        ≤ 2 * Lemma616TotalMass.Constants.rho_lm1 * M) :
    (15 / 100 : ℝ) * M
      ≤ (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ) := by
  have hfloor :=
    ofuel_floor (L := L) (K := K) l Lemma616TotalMass.Constants.rho_lm1 M c
      hReach hBiased
  have hcoef :
      (15 / 100 : ℝ) ≤ 97 / 100 - 2 * Lemma616TotalMass.Constants.rho_lm1 := by
    rw [(Lemma616TotalMass.rho_lm1_export).1]
    norm_num
  exact (mul_le_mul_of_nonneg_right hcoef hM).trans hfloor

/-- Natural-main-count real form of the final-hour `0.15 |M|` floor. -/
theorem ofuel_floor_final_hour_nat_real (l m : ℕ) (c : Config (AgentState L K))
    (hReach :
      (97 / 100 : ℝ) * (m : ℝ)
        ≤ (phase3ReachedMainCount (L := L) (K := K) l c : ℝ))
    (hBiased :
      (phase3BiasedMainCount (L := L) (K := K) c : ℝ)
        ≤ 2 * Lemma616TotalMass.Constants.rho_lm1 * (m : ℝ)) :
    (((15 * m : ℕ) : ℝ) / 100)
      ≤ (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ) := by
  have h :=
    ofuel_floor_final_hour (L := L) (K := K) l (m : ℝ) c
      (by positivity) hReach hBiased
  have hcast : (((15 * m : ℕ) : ℝ) / 100) = (15 / 100 : ℝ) * (m : ℝ) := by
    norm_num [Nat.cast_mul]
    ring
  rw [hcast]
  exact h

/-- The final-hour `0.15 |M|` floor in the exact `ℝ≥0∞` shape consumed by
`Lemma615MassAbove.phase3_phiMass_multiplicative_drift_of_fuel_floor15`. -/
theorem ofuel_floor_final_hour_ennreal (l m : ℕ) (c : Config (AgentState L K))
    (hReach :
      (97 / 100 : ℝ) * (m : ℝ)
        ≤ (phase3ReachedMainCount (L := L) (K := K) l c : ℝ))
    (hBiased :
      (phase3BiasedMainCount (L := L) (K := K) c : ℝ)
        ≤ 2 * Lemma616TotalMass.Constants.rho_lm1 * (m : ℝ)) :
    (((15 * m : ℕ) : ℝ≥0∞) / (100 : ℝ≥0∞))
      ≤ (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ≥0∞) := by
  have hreal :=
    ofuel_floor_final_hour_nat_real (L := L) (K := K) l m c hReach hBiased
  have hleft_top :
      (((15 * m : ℕ) : ℝ≥0∞) / (100 : ℝ≥0∞)) ≠ ∞ := by
    refine ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_
    norm_num
  have hright_top :
      (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) l c : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.toReal_le_toReal hleft_top hright_top).mp
  simpa [ENNReal.toReal_div, ENNReal.toReal_natCast] using hreal

#print axioms ofuel_floor
#print axioms ofuel_floor_final_hour
#print axioms ofuel_floor_final_hour_ennreal

end Lemma613OFloor
end ExactMajority
