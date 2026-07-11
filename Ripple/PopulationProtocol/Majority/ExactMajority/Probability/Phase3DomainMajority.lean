/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase3DomainMajority — Concrete Phase3ModeDomain for the majority case

Constructs the `Phase3Core.Phase3ModeDomain L` from the paper's majority-sign
Phase 3 parameters (dominant level `ell`, main count `M`, log-floor `q`).

The rho table uses the exact rational constants from Lemma 6.16
(`Lemma616TotalMass.Constants`), indexed by offset from `ell`:

  early (h + 5 ≤ ell) :  1/10      = rho_early = rho_lm5
  ell - 4             : 13/125      = rho_lm4
  ell - 3             : 13/100      = rho_lm3
  ell - 2             : 53/250      = rho_lm2
  ell - 1             : 51/125      = rho_lm1
  ell                 : 101/125     = rho_l

The tau table uses `max(0, 0.97 - 2·rho_h)` from the paper's O-fuel floor
(Lemma 6.13):

  early               : 77/100     = 0.97 - 2·(1/10)
  ell - 4             : 381/500    = 0.97 - 2·(13/125)
  ell - 3             : 71/100     = 0.97 - 2·(13/100)
  ell - 2             : 273/500    = 0.97 - 2·(53/250)
  ell - 1             : 77/500     = 0.97 - 2·(51/125)
  ell                 : 0          (0.97 - 2·(101/125) < 0)

All tie-case obligations are vacuously discharged (mode = majority σ ≠ tie).

This file is 0-sorry.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Core
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma616TotalMass

namespace ExactMajority
namespace Phase3DomainMajority

open Phase3Core Phase3Pre3

/-! ## Concrete rho/tau tables -/

/-- Concrete rho table for Phase 3, matching Lemma 6.16 constants.
Indexed by hour `h` relative to the dominant level `ell`. -/
noncomputable def concreteRho (ell : ℕ) : ℕ → ℝ := fun h =>
  if h + 5 ≤ ell then 1 / 10          -- rho_early (includes h = ell - 5)
  else if h + 4 = ell then 13 / 125   -- rho_lm4
  else if h + 3 = ell then 13 / 100   -- rho_lm3
  else if h + 2 = ell then 53 / 250   -- rho_lm2
  else if h + 1 = ell then 51 / 125   -- rho_lm1
  else if h = ell then 101 / 125      -- rho_l
  else 1                               -- h > ell (unused, but nonneg)

/-- Concrete tau (O-fuel floor) table for Phase 3.
tau_h = max(0, 0.97 - 2 * rho_h). At hour ell the formula gives a negative
value, so tau is clamped to 0. -/
noncomputable def concreteTau (ell : ℕ) : ℕ → ℝ := fun h =>
  if h + 5 ≤ ell then 77 / 100        -- 0.97 - 2 * (1/10)
  else if h + 4 = ell then 381 / 500  -- 0.97 - 2 * (13/125)
  else if h + 3 = ell then 71 / 100   -- 0.97 - 2 * (13/100)
  else if h + 2 = ell then 273 / 500  -- 0.97 - 2 * (53/250)
  else if h + 1 = ell then 77 / 500   -- 0.97 - 2 * (51/125)
  else 0                               -- h = ell or h > ell

/-! ## Nonnegativity proofs -/

theorem concreteRho_nonneg (ell : ℕ) : ∀ h, 0 ≤ concreteRho ell h := by
  intro h; unfold concreteRho; split_ifs <;> norm_num

theorem concreteTau_nonneg (ell : ℕ) : ∀ h, 0 ≤ concreteTau ell h := by
  intro h; unfold concreteTau; split_ifs <;> norm_num

/-! ## Phase3ModeDomain construction -/

/-- Construct `Phase3ModeDomain L` for the majority case.

Given:
- `σ` : majority sign
- `ell` : dominant level from `DominantLevelChoice.Window`
- `M_val` : main count at Phase 3 entry (natural number)
- `q_val` : `⌊ln n / 3⌋` (paper Lemma 6.14)
- `h5` : `5 ≤ ell`
- `h_ell_L` : `ell + 2 ≤ L` (paper dominant-level constraint)
- `hq` : `0 < q_val`
- `hM` : `0 < M_val`

In the majority case, `lastCoreHour = ell` (the induction runs through the
dominant level) and all tie obligations are vacuously true. -/
noncomputable def phase3ModeDomain_majority
    {L : ℕ} (σ : Sign) (ell : ℕ) (M_val : ℕ) (q_val : ℕ)
    (h5 : 5 ≤ ell) (h_ell_L : ell + 2 ≤ L)
    (hq : 0 < q_val) (hM : 0 < M_val) :
    Phase3ModeDomain L where
  mode := Pre3Mode.majority σ
  ell := ell
  lastCoreHour := ell
  five_le_ell := h5
  lastCore_le_L := by omega
  lastCore_le_ell := le_refl ell
  tie_ell := by intro h; exact Pre3Mode.noConfusion h
  tie_lastCore := by intro h; exact Pre3Mode.noConfusion h
  tie_all_hours_early := by intro h; exact Pre3Mode.noConfusion h
  majority_lastCore := by intro _; rfl
  majority_l_plus_two_le_L := by intro _; exact h_ell_L
  q := q_val
  q_pos := hq
  M := M_val
  M_pos := hM
  rho := concreteRho ell
  tau := concreteTau ell
  rho_nonneg := concreteRho_nonneg ell
  tau_nonneg := concreteTau_nonneg ell

/-! ## Field accessors for the constructed domain -/

@[simp]
theorem phase3ModeDomain_majority_mode {L : ℕ}
    (σ : Sign) (ell M_val q_val : ℕ) (h5 : 5 ≤ ell) (h_ell_L : ell + 2 ≤ L)
    (hq : 0 < q_val) (hM : 0 < M_val) :
    (phase3ModeDomain_majority σ ell M_val q_val h5 h_ell_L hq hM).mode =
      Pre3Mode.majority σ := rfl

@[simp]
theorem phase3ModeDomain_majority_ell {L : ℕ}
    (σ : Sign) (ell M_val q_val : ℕ) (h5 : 5 ≤ ell) (h_ell_L : ell + 2 ≤ L)
    (hq : 0 < q_val) (hM : 0 < M_val) :
    (phase3ModeDomain_majority σ ell M_val q_val h5 h_ell_L hq hM).ell = ell := rfl

@[simp]
theorem phase3ModeDomain_majority_lastCoreHour {L : ℕ}
    (σ : Sign) (ell M_val q_val : ℕ) (h5 : 5 ≤ ell) (h_ell_L : ell + 2 ≤ L)
    (hq : 0 < q_val) (hM : 0 < M_val) :
    (phase3ModeDomain_majority σ ell M_val q_val h5 h_ell_L hq hM).lastCoreHour = ell := rfl

@[simp]
theorem phase3ModeDomain_majority_q {L : ℕ}
    (σ : Sign) (ell M_val q_val : ℕ) (h5 : 5 ≤ ell) (h_ell_L : ell + 2 ≤ L)
    (hq : 0 < q_val) (hM : 0 < M_val) :
    (phase3ModeDomain_majority σ ell M_val q_val h5 h_ell_L hq hM).q = q_val := rfl

@[simp]
theorem phase3ModeDomain_majority_M {L : ℕ}
    (σ : Sign) (ell M_val q_val : ℕ) (h5 : 5 ≤ ell) (h_ell_L : ell + 2 ≤ L)
    (hq : 0 < q_val) (hM : 0 < M_val) :
    (phase3ModeDomain_majority σ ell M_val q_val h5 h_ell_L hq hM).M = M_val := rfl

/-! ## RhoTable compatibility

The concrete rho function matches the `Lemma616TotalMass.Constants` at the
paper's six named rows.  This is exactly the `RhoTable` predicate needed by
the H16 marked-cancel engine. -/

theorem concreteRho_eq_rho_early {ell : ℕ} (h5 : 5 ≤ ell) (h : ℕ)
    (hE : h + 5 ≤ ell) :
    concreteRho ell h = Lemma616TotalMass.Constants.rho_early := by
  unfold concreteRho
  simp [hE, Lemma616TotalMass.Constants.rho_early]

theorem concreteRho_eq_rho_lm5 {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteRho ell (ell - 5) = Lemma616TotalMass.Constants.rho_lm5 := by
  unfold concreteRho Lemma616TotalMass.Constants.rho_lm5
  have : ell - 5 + 5 ≤ ell := by omega
  simp [this]

theorem concreteRho_eq_rho_lm4 {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteRho ell (ell - 4) = Lemma616TotalMass.Constants.rho_lm4 := by
  unfold concreteRho Lemma616TotalMass.Constants.rho_lm4
  have h1 : ¬(ell - 4 + 5 ≤ ell) := by omega
  have h2 : ell - 4 + 4 = ell := by omega
  simp [h1, h2]

theorem concreteRho_eq_rho_lm3 {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteRho ell (ell - 3) = Lemma616TotalMass.Constants.rho_lm3 := by
  unfold concreteRho Lemma616TotalMass.Constants.rho_lm3
  have h1 : ¬(ell - 3 + 5 ≤ ell) := by omega
  have h2 : ¬(ell - 3 + 4 = ell) := by omega
  have h3 : ell - 3 + 3 = ell := by omega
  simp [h1, h2, h3]

theorem concreteRho_eq_rho_lm2 {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteRho ell (ell - 2) = Lemma616TotalMass.Constants.rho_lm2 := by
  unfold concreteRho Lemma616TotalMass.Constants.rho_lm2
  have h1 : ¬(ell - 2 + 5 ≤ ell) := by omega
  have h2 : ¬(ell - 2 + 4 = ell) := by omega
  have h3 : ¬(ell - 2 + 3 = ell) := by omega
  have h4 : ell - 2 + 2 = ell := by omega
  simp [h1, h2, h3, h4]

theorem concreteRho_eq_rho_lm1 {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteRho ell (ell - 1) = Lemma616TotalMass.Constants.rho_lm1 := by
  unfold concreteRho Lemma616TotalMass.Constants.rho_lm1
  have h1 : ¬(ell - 1 + 5 ≤ ell) := by omega
  have h2 : ¬(ell - 1 + 4 = ell) := by omega
  have h3 : ¬(ell - 1 + 3 = ell) := by omega
  have h4 : ¬(ell - 1 + 2 = ell) := by omega
  have h5' : ell - 1 + 1 = ell := by omega
  simp [h1, h2, h3, h4, h5']

theorem concreteRho_eq_rho_l {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteRho ell ell = Lemma616TotalMass.Constants.rho_l := by
  unfold concreteRho Lemma616TotalMass.Constants.rho_l
  have h1 : ¬(ell + 5 ≤ ell) := by omega
  have h2 : ¬(ell + 4 = ell) := by omega
  have h3 : ¬(ell + 3 = ell) := by omega
  have h4 : ¬(ell + 2 = ell) := by omega
  have h5' : ¬(ell + 1 = ell) := by omega
  simp [h1, h2, h3, h4, h5']

/-! ## Tau-rho bridge inequality

For the O-fuel bridge (`Phase3Bridges`, `Lemma613MarkedPullDrop`), the
hypothesis `D.tau h ≤ 97/100 - 2 * rho` holds at every early and final-four
hour (not at hour ell, where tau = 0 and 97/100 - 2*rho_l < 0). -/

theorem concreteTau_le_coeff_early {ell : ℕ} (h : ℕ) (hE : h + 5 ≤ ell) :
    concreteTau ell h ≤ 97 / 100 - 2 * concreteRho ell h := by
  unfold concreteTau concreteRho
  simp [hE]
  norm_num

theorem concreteTau_le_coeff_lm4 {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteTau ell (ell - 4) ≤ 97 / 100 - 2 * concreteRho ell (ell - 4) := by
  unfold concreteTau concreteRho
  have h1 : ¬(ell - 4 + 5 ≤ ell) := by omega
  have h2 : ell - 4 + 4 = ell := by omega
  simp [h1, h2]
  norm_num

theorem concreteTau_le_coeff_lm3 {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteTau ell (ell - 3) ≤ 97 / 100 - 2 * concreteRho ell (ell - 3) := by
  unfold concreteTau concreteRho
  have h1 : ¬(ell - 3 + 5 ≤ ell) := by omega
  have h2 : ¬(ell - 3 + 4 = ell) := by omega
  have h3 : ell - 3 + 3 = ell := by omega
  simp [h1, h2, h3]
  norm_num

theorem concreteTau_le_coeff_lm2 {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteTau ell (ell - 2) ≤ 97 / 100 - 2 * concreteRho ell (ell - 2) := by
  unfold concreteTau concreteRho
  have h1 : ¬(ell - 2 + 5 ≤ ell) := by omega
  have h2 : ¬(ell - 2 + 4 = ell) := by omega
  have h3 : ¬(ell - 2 + 3 = ell) := by omega
  have h4 : ell - 2 + 2 = ell := by omega
  simp [h1, h2, h3, h4]
  norm_num

theorem concreteTau_le_coeff_lm1 {ell : ℕ} (h5 : 5 ≤ ell) :
    concreteTau ell (ell - 1) ≤ 97 / 100 - 2 * concreteRho ell (ell - 1) := by
  unfold concreteTau concreteRho
  have h1 : ¬(ell - 1 + 5 ≤ ell) := by omega
  have h2 : ¬(ell - 1 + 4 = ell) := by omega
  have h3 : ¬(ell - 1 + 3 = ell) := by omega
  have h4 : ¬(ell - 1 + 2 = ell) := by omega
  have h5' : ell - 1 + 1 = ell := by omega
  simp [h1, h2, h3, h4, h5']
  norm_num

#print axioms phase3ModeDomain_majority
#print axioms concreteRho_nonneg
#print axioms concreteTau_nonneg

end Phase3DomainMajority
end ExactMajority
