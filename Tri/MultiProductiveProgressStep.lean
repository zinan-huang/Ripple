/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgress

/-!
# One-step productive progress for a fixed competitor

This file combines the strict four-jump MGF with the full-state counter of
nonzero fixed-pair jumps.  The counter keeps the proof adapted to the physical
configuration rather than projecting the gap to a Markov chain.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Exact one-step decomposition for the joint gap/relevant-event potential,
before applying the strict four-jump contraction. -/
theorem expect_productivePairRelevantCount
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X Y : Species m) (k : ℕ) (w φ : ℝ≥0∞)
    (hg2 : 2 ≤ pairGapNat c X Y) :
    expect (productivePairRelevantCount h3 X Y (c, k))
        (pairProgressPotential X Y w φ) =
      (pairIrrelevantProductiveMass c h3 X Y *
            w ^ pairGapNat c X Y * (φ⁻¹) ^ k +
        (pairDeltaMass c h3 X Y (-2) *
              w ^ (pairGapNat c X Y - 2) +
          pairDeltaMass c h3 X Y (-1) *
              w ^ (pairGapNat c X Y - 1) +
          pairDeltaMass c h3 X Y 1 *
              w ^ (pairGapNat c X Y + 1) +
          pairDeltaMass c h3 X Y 2 *
              w ^ (pairGapNat c X Y + 2)) *
            (φ⁻¹) ^ (k + 1)) /
        productiveMass c h3 := by
  classical
  rw [show productivePairRelevantCount h3 X Y (c, k) =
      (productiveSamplePMF c h3 hprod).map
        (fun t =>
          (sampleNext c t,
            if samplePairDelta t X Y = 0 then k else k + 1)) by
    unfold productivePairRelevantCount
    simp [hprod]]
  rw [expect_map, expect_productiveSamplePMF]
  congr 1
  simp only [pairProgressPotential]
  let g := pairGapNat c X Y
  have hpoint :
      ∀ t : TripleSample c,
        pairGapNat (sampleNext c t) X Y =
          if samplePairDelta t X Y = -2 then g - 2
          else if samplePairDelta t X Y = -1 then g - 1
          else if samplePairDelta t X Y = 0 then g
          else if samplePairDelta t X Y = 1 then g + 1
          else g + 2 := by
    intro t
    have hlo := samplePairDelta_lower t X Y
    have hhi := samplePairDelta_upper t X Y
    have hcases :
        samplePairDelta t X Y = -2 ∨
        samplePairDelta t X Y = -1 ∨
        samplePairDelta t X Y = 0 ∨
        samplePairDelta t X Y = 1 ∨
        samplePairDelta t X Y = 2 := by
      omega
    rcases hcases with h | h | h | h | h
    · simp only [h, ↓reduceIte]
      apply pairGapNat_sampleNext_of_delta c t X Y hg2 (-2) (g - 2) h
      dsimp only [g]
      omega
    · simp [h]
      apply pairGapNat_sampleNext_of_delta c t X Y hg2 (-1) (g - 1) h
      dsimp only [g]
      omega
    · simp [h]
      apply pairGapNat_sampleNext_of_delta c t X Y hg2 0 g h
      rfl
    · simp [h]
      apply pairGapNat_sampleNext_of_delta c t X Y hg2 1 (g + 1) h
      dsimp only [g]
      omega
    · simp [h]
      apply pairGapNat_sampleNext_of_delta c t X Y hg2 2 (g + 2) h
      dsimp only [g]
      omega
  rw [show pairGapNat c X Y = g from rfl]
  unfold pairIrrelevantProductiveMass pairDeltaMass
  simp only [tsum_fintype]
  symm
  calc
    (∑ t : TripleSample c,
          if IsProductiveSample t ∧ samplePairDelta t X Y = 0 then
            triplePMF c h3 t else 0) *
          w ^ g * (φ⁻¹) ^ k +
        (((∑ t : TripleSample c,
              if samplePairDelta t X Y = -2 then triplePMF c h3 t else 0) *
                w ^ (g - 2) +
            (∑ t : TripleSample c,
              if samplePairDelta t X Y = -1 then triplePMF c h3 t else 0) *
                w ^ (g - 1) +
            (∑ t : TripleSample c,
              if samplePairDelta t X Y = 1 then triplePMF c h3 t else 0) *
                w ^ (g + 1) +
            (∑ t : TripleSample c,
              if samplePairDelta t X Y = 2 then triplePMF c h3 t else 0) *
                w ^ (g + 2)) *
              (φ⁻¹) ^ (k + 1)) =
      ∑ t : TripleSample c,
        ((if IsProductiveSample t ∧ samplePairDelta t X Y = 0 then
            triplePMF c h3 t else 0) * w ^ g * (φ⁻¹) ^ k +
          ((((if samplePairDelta t X Y = -2 then triplePMF c h3 t else 0) *
                  w ^ (g - 2) +
              (if samplePairDelta t X Y = -1 then triplePMF c h3 t else 0) *
                  w ^ (g - 1)) +
            (if samplePairDelta t X Y = 1 then triplePMF c h3 t else 0) *
                w ^ (g + 1)) +
            (if samplePairDelta t X Y = 2 then triplePMF c h3 t else 0) *
                w ^ (g + 2)) * (φ⁻¹) ^ (k + 1)) := by
      simp only [Finset.sum_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    _ = ∑ t : TripleSample c,
        if IsProductiveSample t then
          triplePMF c h3 t *
            (w ^ pairGapNat (sampleNext c t) X Y *
              (φ⁻¹) ^
                (if samplePairDelta t X Y = 0 then k else k + 1))
        else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [hpoint t]
      have hlo := samplePairDelta_lower t X Y
      have hhi := samplePairDelta_upper t X Y
      have hcases :
          samplePairDelta t X Y = -2 ∨
          samplePairDelta t X Y = -1 ∨
          samplePairDelta t X Y = 0 ∨
          samplePairDelta t X Y = 1 ∨
          samplePairDelta t X Y = 2 := by
        omega
      rcases hcases with h | h | h | h | h
      · have hp :=
          isProductiveSample_of_pairDelta_ne_zero t X Y (by omega)
        simp [h, hp]
        ring
      · have hp :=
          isProductiveSample_of_pairDelta_ne_zero t X Y (by omega)
        simp [h, hp]
        ring
      · by_cases hp : IsProductiveSample t
        · simp [h, hp]
          ring
        · simp [h, hp]
      · have hp :=
          isProductiveSample_of_pairDelta_ne_zero t X Y (by omega)
        simp [h, hp]
        ring
      · have hp :=
          isProductiveSample_of_pairDelta_ne_zero t X Y (by omega)
        simp [h, hp]
        ring

/-- At the strict progress tilt, the joint potential is a one-step
supermartingale whenever productive conditioning is defined. -/
theorem productivePairRelevantCount_progress_conserve_of_mass
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X Y : Species m) (hXY : X ≠ Y)
    (k d : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n)
    (hgap : HasPairwiseGap c X d) :
    expect (productivePairRelevantCount h3 X Y (c, k))
        (pairProgressPotential X Y
          (pairProgressTilt n d) (pairProgressFactor n d)) ≤
      pairProgressPotential X Y
        (pairProgressTilt n d) (pairProgressFactor n d) (c, k) := by
  let w := pairProgressTilt n d
  let φ := pairProgressFactor n d
  let g := pairGapNat c X Y
  let A := pairIrrelevantProductiveMass c h3 X Y
  let R := pairRelevantMass c h3 X Y
  let P := productiveMass c h3
  have hn : 0 < n := by omega
  have hg2 : 2 ≤ g := by
    have hXYgap := hgap Y (Ne.symm hXY)
    dsimp only [g, pairGapNat]
    omega
  have hφ0 : φ ≠ 0 := by
    dsimp only [φ]
    exact pairProgressFactor_ne_zero n d hn
  have hφtop : φ ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    dsimp only [φ]
    exact pairProgressFactor_le_one n d hn
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
    exact pairDeltaMass_relevant_strict_mgf
      c h3 X Y hXY d hdn hgap
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

/-- The totalized full-state relevant-event kernel has the same one-step
supermartingale inequality; zero-productive-mass states are self-loops. -/
theorem productivePairRelevantCount_progress_conserve
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (k d : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n)
    (hgap : HasPairwiseGap c X d) :
    expect (productivePairRelevantCount h3 X Y (c, k))
        (pairProgressPotential X Y
          (pairProgressTilt n d) (pairProgressFactor n d)) ≤
      pairProgressPotential X Y
        (pairProgressTilt n d) (pairProgressFactor n d) (c, k) := by
  classical
  by_cases hprod : productiveMass c h3 ≠ 0
  · exact productivePairRelevantCount_progress_conserve_of_mass
      c h3 hprod X Y hXY k d hd2 hdn hgap
  · unfold productivePairRelevantCount
    simp [hprod]

end Tri.Multi

#print axioms Tri.Multi.expect_productivePairRelevantCount
#print axioms Tri.Multi.productivePairRelevantCount_progress_conserve_of_mass
#print axioms Tri.Multi.productivePairRelevantCount_progress_conserve
