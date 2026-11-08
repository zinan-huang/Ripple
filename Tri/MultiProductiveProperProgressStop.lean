/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProperProgress
import Tri.MultiProductiveProgressLocalConstants

/-!
# Stopped proper-stage four-jump progress

The repaired proper-stage tilt is threaded through the existing local stopped
kernel and joint involvement/relevant counter.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- One-step relevant-event conservation at the repaired proper-stage tilt. -/
theorem productivePairRelevantCount_proper_conserve_of_mass
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X Y : Species m) (hXY : X ≠ Y)
    (k S d : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hd3S : 3 * d ≤ S)
    (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    expect (productivePairRelevantCount h3 X Y (c, k))
        (pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)) ≤
      pairProgressPotential X Y
        (pairProperProgressTilt S d) (pairProperProgressFactor S d) (c, k) := by
  let w := pairProperProgressTilt S d
  let φ := pairProperProgressFactor S d
  let g := pairGapNat c X Y
  let A := pairIrrelevantProductiveMass c h3 X Y
  let R := pairRelevantMass c h3 X Y
  let P := productiveMass c h3
  have hg2 : 2 ≤ g := by
    have hXYgap := hgap Y (Ne.symm hXY)
    dsimp only [g, pairGapNat]
    omega
  have hφ0 : φ ≠ 0 := by
    dsimp only [φ]
    exact pairProperProgressFactor_ne_zero S d hS
  have hφtop : φ ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    dsimp only [φ]
    exact pairProperProgressFactor_le_one S d hS
  have hPtop : P ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    dsimp only [P]
    exact productiveMass_le_one c h3
  have hmgf :
      pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
          pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
          pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
          pairDeltaMass c h3 X Y 2 * w ^ (g + 2) ≤
        φ * R * w ^ g := by
    apply Tri.four_jump_geometric_of_core hg2
    dsimp only [w, φ, R, pairRelevantMass]
    exact pairDeltaMass_relevant_proper_mgf_of_count_le
      c h3 X Y hXY S d hS hd3S hxS hgap
  have hrel :
      (pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
          pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
          pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
          pairDeltaMass c h3 X Y 2 * w ^ (g + 2)) *
            (φ⁻¹) ^ (k + 1) ≤
        R * w ^ g * (φ⁻¹) ^ k := by
    calc
      (pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
            pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
            pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
            pairDeltaMass c h3 X Y 2 * w ^ (g + 2)) *
              (φ⁻¹) ^ (k + 1) ≤
          (φ * R * w ^ g) * (φ⁻¹) ^ (k + 1) :=
        by
          simpa only [mul_comm] using
            (mul_le_mul_right hmgf ((φ⁻¹) ^ (k + 1)))
      _ = R * w ^ g * (φ⁻¹) ^ k := by
        rw [pow_succ]
        calc
          φ * R * w ^ g * ((φ⁻¹) ^ k * φ⁻¹) =
              (φ * φ⁻¹) * (R * w ^ g * (φ⁻¹) ^ k) := by
            ring
          _ = R * w ^ g * (φ⁻¹) ^ k := by
            rw [ENNReal.mul_inv_cancel hφ0 hφtop, one_mul]
  have hnum :
      A * w ^ g * (φ⁻¹) ^ k +
          (pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
            pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
            pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
            pairDeltaMass c h3 X Y 2 * w ^ (g + 2)) *
              (φ⁻¹) ^ (k + 1) ≤
        P * (w ^ g * (φ⁻¹) ^ k) := by
    calc
      A * w ^ g * (φ⁻¹) ^ k +
            (pairDeltaMass c h3 X Y (-2) * w ^ (g - 2) +
              pairDeltaMass c h3 X Y (-1) * w ^ (g - 1) +
              pairDeltaMass c h3 X Y 1 * w ^ (g + 1) +
              pairDeltaMass c h3 X Y 2 * w ^ (g + 2)) *
                (φ⁻¹) ^ (k + 1) ≤
          A * w ^ g * (φ⁻¹) ^ k +
            R * w ^ g * (φ⁻¹) ^ k :=
        add_le_add_right hrel _
      _ = (A + R) * (w ^ g * (φ⁻¹) ^ k) := by ring
      _ = P * (w ^ g * (φ⁻¹) ^ k) := by
        rw [show A + R = P by
          dsimp only [A, R, P]
          exact pairIrrelevant_add_relevant_eq_productiveMass c h3 X Y]
  rw [expect_productivePairRelevantCount c h3 hprod X Y k w φ hg2]
  dsimp only [pairProgressPotential, w, φ, g, A, R, P] at hnum ⊢
  have hdiv := ENNReal.div_le_div_right hnum (productiveMass c h3)
  have hcancel (a : ℝ≥0∞) :
      productiveMass c h3 * a / productiveMass c h3 = a := by
    rw [div_eq_mul_inv]
    calc
      productiveMass c h3 * a * (productiveMass c h3)⁻¹ =
          (productiveMass c h3 * (productiveMass c h3)⁻¹) * a := by
        ring
      _ = a := by
        rw [ENNReal.mul_inv_cancel hprod hPtop, one_mul]
  rw [hcancel] at hdiv
  exact hdiv

/-- Totalized one-step conservation at the repaired proper-stage tilt. -/
theorem productivePairRelevantCount_proper_conserve
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (k S d : ℕ) (hS : 0 < S) (hd2 : 2 ≤ d) (hd3S : 3 * d ≤ S)
    (hxS : count c X ≤ S)
    (hgap : HasPairwiseGap c X d) :
    expect (productivePairRelevantCount h3 X Y (c, k))
        (pairProgressPotential X Y
          (pairProperProgressTilt S d) (pairProperProgressFactor S d)) ≤
      pairProgressPotential X Y
        (pairProperProgressTilt S d) (pairProperProgressFactor S d) (c, k) := by
  classical
  by_cases hprod : productiveMass c h3 ≠ 0
  · exact productivePairRelevantCount_proper_conserve_of_mass
      c h3 hprod X Y hXY k S d hS hd2 hd3S hxS hgap
  · unfold productivePairRelevantCount
    simp [hprod]

theorem three_halfGap_le_properStageScale
    (D x0 : ℕ) (hDx0 : D ≤ x0) :
    3 * (D / 2) ≤ properStageScale x0 := by
  unfold properStageScale
  omega

end Tri.Multi

#print axioms Tri.Multi.productivePairRelevantCount_proper_conserve
