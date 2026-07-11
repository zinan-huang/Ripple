/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Majority-mass lower bound from the conserved signed gap

This file isolates the short arithmetic input used by the §46 repair.  The
dominant-level choice is intentionally a hypothesis: the current paper-regime
surface records `l` but does not yet carry a formal
`0.4 * |M| <= g * 2^l` field.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7Convergence
import Mathlib.Tactic

namespace ExactMajority

namespace GapMassLower

variable {L K : ℕ}

/-- The elementary reciprocal identity for the dyadic scale. -/
theorem two_pow_mul_zpow_neg (ell : ℕ) :
    (2 : ℝ) ^ ell * (2 : ℝ) ^ (-(ell : ℤ)) = 1 := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

/-- The symmetric reciprocal identity for the dyadic scale. -/
theorem two_zpow_neg_mul_pow (ell : ℕ) :
    (2 : ℝ) ^ (-(ell : ℤ)) * (2 : ℝ) ^ ell = 1 := by
  rw [mul_comm, two_pow_mul_zpow_neg ell]

/-- Abstract majority-mass lower bound.

If the signed gap is `g = betaPos - betaNeg`, the opposite-sign mass is
nonnegative, and the dominant-level choice gives `0.4 * M <= g * 2^ell`, then
the majority mass is at least `0.4 * M * 2^{-ell}`. -/
theorem gapMassLower {g betaPos betaNeg M : ℝ} (ell : ℕ)
    (hgap : g = betaPos - betaNeg)
    (hneg : 0 ≤ betaNeg)
    (hdom : (0.4 : ℝ) * M ≤ g * (2 : ℝ) ^ ell) :
    (0.4 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ)) ≤ betaPos := by
  have hscale_nonneg : 0 ≤ (2 : ℝ) ^ (-(ell : ℤ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hdom hscale_nonneg
  have hmul : (g * (2 : ℝ) ^ ell) * (2 : ℝ) ^ (-(ell : ℤ)) = g := by
    rw [mul_assoc, two_pow_mul_zpow_neg ell, mul_one]
  have hgm : (0.4 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ)) ≤ g := by
    simpa [hmul] using hscaled
  nlinarith

/-- Conjunctive-hypothesis wrapper for consumers that carry the gap facts as one package. -/
theorem gapMassLower_of_conj {g betaPos betaNeg M : ℝ} (ell : ℕ)
    (h :
      g = betaPos - betaNeg ∧
        0 ≤ betaNeg ∧
        (0.4 : ℝ) * M ≤ g * (2 : ℝ) ^ ell) :
    (0.4 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ)) ≤ betaPos :=
  gapMassLower ell h.1 h.2.1 h.2.2

/-- Unsigned version for the negative-majority case: use `|g|` as the conserved
gap and the unsigned majority/minority masses. -/
theorem absGapMassLower {g betaMaj betaMin M : ℝ} (ell : ℕ)
    (hgap : |g| = betaMaj - betaMin)
    (hmin : 0 ≤ betaMin)
    (hdom : (0.4 : ℝ) * M ≤ |g| * (2 : ℝ) ^ ell) :
    (0.4 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ)) ≤ betaMaj :=
  gapMassLower ell hgap hmin hdom

/-! ## Phase-7 class-mass adapters -/

/-- One agent's signed mass is the positive class mass minus the negative class mass. -/
theorem agentSignedMass_eq_pos_sub_neg (a : AgentState L K) :
    Phase7Convergence.agentSignedMass a =
      Phase7Convergence.agentClassMass Sign.pos a -
        Phase7Convergence.agentClassMass Sign.neg a := by
  unfold Phase7Convergence.agentSignedMass Phase7Convergence.agentClassMass
  unfold Phase7Convergence.biasSignedMass Phase7Convergence.biasClassMass
  cases a.bias with
  | zero => simp
  | dyadic s _ => cases s <;> simp

/-- The Phase-7 signed sum is exactly positive class mass minus negative class mass.

All three quantities are in the existing `2^L`-scaled integer units. -/
theorem phase7SignedSum_eq_classMass_pos_sub_neg
    (c : Config (AgentState L K)) :
    Phase7Convergence.phase7SignedSum c =
      Phase7Convergence.classMass Sign.pos c -
        Phase7Convergence.classMass Sign.neg c := by
  unfold Phase7Convergence.phase7SignedSum Phase7Convergence.classMass
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a c ih =>
      simp [ih, agentSignedMass_eq_pos_sub_neg (L := L) (K := K) a]
      ring

/-- Phase-7 adapter when the positive sign is the majority sign.

The dominant-level lower bound is carried in the same scaled units as
`phase7SignedSum` and `classMass`. -/
theorem gapMassLower_phase7_posMajority
    (c : Config (AgentState L K)) (M : ℝ) (ell : ℕ)
    (hdom :
      (0.4 : ℝ) * M ≤
        (Phase7Convergence.phase7SignedSum c : ℝ) * (2 : ℝ) ^ ell) :
    (0.4 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
      ≤ (Phase7Convergence.classMass Sign.pos c : ℝ) := by
  have hgapZ := phase7SignedSum_eq_classMass_pos_sub_neg (L := L) (K := K) c
  have hgap :
      (Phase7Convergence.phase7SignedSum c : ℝ) =
        (Phase7Convergence.classMass Sign.pos c : ℝ) -
          (Phase7Convergence.classMass Sign.neg c : ℝ) := by
    exact_mod_cast hgapZ
  exact gapMassLower ell hgap
    (by exact_mod_cast Phase7Convergence.classMass_nonneg (L := L) (K := K) Sign.neg c)
    hdom

/-- Phase-7 adapter when the negative sign is the majority sign. -/
theorem gapMassLower_phase7_negMajority
    (c : Config (AgentState L K)) (M : ℝ) (ell : ℕ)
    (hdom :
      (0.4 : ℝ) * M ≤
        (-(Phase7Convergence.phase7SignedSum c : ℝ)) * (2 : ℝ) ^ ell) :
    (0.4 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
      ≤ (Phase7Convergence.classMass Sign.neg c : ℝ) := by
  have hgapZ := phase7SignedSum_eq_classMass_pos_sub_neg (L := L) (K := K) c
  have hgap :
      -(Phase7Convergence.phase7SignedSum c : ℝ) =
        (Phase7Convergence.classMass Sign.neg c : ℝ) -
          (Phase7Convergence.classMass Sign.pos c : ℝ) := by
    have hgapR :
        (Phase7Convergence.phase7SignedSum c : ℝ) =
          (Phase7Convergence.classMass Sign.pos c : ℝ) -
            (Phase7Convergence.classMass Sign.neg c : ℝ) := by
      exact_mod_cast hgapZ
    linarith
  exact gapMassLower ell hgap
    (by exact_mod_cast Phase7Convergence.classMass_nonneg (L := L) (K := K) Sign.pos c)
    hdom

#print axioms two_pow_mul_zpow_neg
#print axioms two_zpow_neg_mul_pow
#print axioms gapMassLower
#print axioms gapMassLower_of_conj
#print axioms absGapMassLower
#print axioms agentSignedMass_eq_pos_sub_neg
#print axioms phase7SignedSum_eq_classMass_pos_sub_neg
#print axioms gapMassLower_phase7_posMajority
#print axioms gapMassLower_phase7_negMajority

end GapMassLower
end ExactMajority
