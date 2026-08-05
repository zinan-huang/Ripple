/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionReveal

/-!
# Deterministic label bookkeeping for Lemma 16

This file separates the immutable labels of newly activated identities from
the distinguished initial active molecule.  The initial molecule contributes
at most one adverse unit; it is not a draw from the inactive urn.
-/

namespace Tri

def infectionRevealXCount {k : ℕ}
    (ell : Fin k → InfectionLabel) : ℕ :=
  (Finset.univ.filter fun i => ell i = .X).card

def infectionRevealYCount {k : ℕ}
    (ell : Fin k → InfectionLabel) : ℕ :=
  (Finset.univ.filter fun i => ell i = .Y).card

/-- Every revealed label is exactly one of `X` and `Y`. -/
theorem infectionRevealXCount_add_infectionRevealYCount
    {k : ℕ} (ell : Fin k → InfectionLabel) :
    infectionRevealXCount ell + infectionRevealYCount ell = k := by
  classical
  have hfilter :
      Finset.univ.filter (fun i => ¬ ell i = .X) =
        Finset.univ.filter (fun i => ell i = .Y) := by
    ext i
    cases hlabel : ell i <;> simp [hlabel]
  unfold infectionRevealXCount infectionRevealYCount
  rw [← hfilter]
  simpa using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k)))
      (fun i => ell i = .X))

/-- The newly activated prefix has more than `rho` adverse `Y` excess. -/
def Lemma16NewLabelBad {k : ℕ} (rho : ℕ)
    (ell : Fin k → InfectionLabel) : Prop :=
  infectionRevealXCount ell + rho < infectionRevealYCount ell

def infectionSeedX : InfectionLabel → ℕ
  | .X => 1
  | .Y => 0

def infectionSeedY : InfectionLabel → ℕ
  | .X => 0
  | .Y => 1

def infectionSeededX {k : ℕ}
    (seed : InfectionLabel)
    (ell : Fin k → InfectionLabel) : ℕ :=
  infectionRevealXCount ell + infectionSeedX seed

def infectionSeededY {k : ℕ}
    (seed : InfectionLabel)
    (ell : Fin k → InfectionLabel) : ℕ :=
  infectionRevealYCount ell + infectionSeedY seed

/-- Adding the initial active molecule costs at most one adverse unit. -/
theorem infection_seeded_ledger_of_newLabel_good
    {k rho : ℕ}
    (seed : InfectionLabel)
    (ell : Fin k → InfectionLabel)
    (hnew :
      infectionRevealYCount ell ≤ infectionRevealXCount ell + rho) :
    infectionSeededY seed ell ≤
      infectionSeededX seed ell + rho + 1 := by
  cases seed <;>
    simp [infectionSeededX, infectionSeededY,
      infectionSeedX, infectionSeedY] at * <;>
    omega

/-- Contrapositive event containment for the seeded label ledger. -/
theorem infection_seeded_bad_implies_newLabel_bad
    {k rho : ℕ}
    (seed : InfectionLabel)
    (ell : Fin k → InfectionLabel)
    (hbad :
      infectionSeededX seed ell + rho + 1 <
        infectionSeededY seed ell) :
    Lemma16NewLabelBad rho ell := by
  cases seed <;>
    simp [infectionSeededX, infectionSeededY,
      infectionSeedX, infectionSeedY,
      Lemma16NewLabelBad] at * <;>
    omega

/-- The discrete adverse-prefix event implies the positive centered-red
deviation consumed by the direct urn tail. -/
theorem lemma16_newLabelBad_implies_centeredRed
    (R B nu k xSel ySel rho : ℕ)
    (hnu : 0 < nu)
    (hRB : R + B = nu)
    (hmajor : R ≤ B)
    (hcount : xSel + ySel = k)
    (hbad : xSel + rho < ySel) :
    (rho : ℝ) / 2 <
      (ySel : ℝ) -
        (k : ℝ) * ((R : ℝ) / (nu : ℝ)) := by
  have hnuR : (0 : ℝ) < (nu : ℝ) := by exact_mod_cast hnu
  have hcenter : (R : ℝ) / (nu : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hnuR]
    have htwo : 2 * R ≤ nu := by omega
    have htwoR : (2 : ℝ) * (R : ℝ) ≤ (nu : ℝ) := by
      exact_mod_cast htwo
    nlinarith
  have hgap : (k : ℝ) + (rho : ℝ) < 2 * (ySel : ℝ) := by
    exact_mod_cast (show k + rho < 2 * ySel by omega)
  have hprod :
      (k : ℝ) * ((R : ℝ) / (nu : ℝ)) ≤ (k : ℝ) * (1 / 2) :=
    mul_le_mul_of_nonneg_left hcenter (by positivity)
  nlinarith

end Tri

#print axioms Tri.infectionRevealXCount_add_infectionRevealYCount
#print axioms Tri.infection_seeded_ledger_of_newLabel_good
#print axioms Tri.infection_seeded_bad_implies_newLabel_bad
#print axioms Tri.lemma16_newLabelBad_implies_centeredRed
