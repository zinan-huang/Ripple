/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiPairMass

/-!
# Physical fixed-pair geometric supermartingale

This file transports the five physical jump masses to the actual
multi-species state kernel.  The full configuration remains the Markov state;
no Markov property is claimed for the projected pair gap.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Natural gap used in the one-sided region where `X` leads `Y`. -/
def pairGapNat
    (c : Config m n) (X Y : Species m) : ℕ :=
  count c X - count c Y

/-- Geometric potential of a one-sided fixed-pair gap. -/
noncomputable def pairGapPotential
    (u : ℝ≥0∞) (X Y : Species m) (c : Config m n) : ℝ≥0∞ :=
  u ^ pairGapNat c X Y

theorem pairGap_eq_nat
    (c : Config m n) (X Y : Species m)
    (hYX : count c Y ≤ count c X) :
    pairGap c X Y = (pairGapNat c X Y : ℤ) := by
  unfold pairGap pairGapNat
  rw [Int.ofNat_sub hYX]

/-- Convert the exact signed update into a natural-gap update while the
current gap is at least two. -/
theorem pairGapNat_sampleNext_of_delta
    (c : Config m n) (t : TripleSample c)
    (X Y : Species m)
    (hg2 : 2 ≤ pairGapNat c X Y)
    (k : ℤ) (a : ℕ)
    (hk : samplePairDelta t X Y = k)
    (ha : (pairGapNat c X Y : ℤ) + k = (a : ℤ)) :
    pairGapNat (sampleNext c t) X Y = a := by
  have hYX : count c Y ≤ count c X := by
    unfold pairGapNat at hg2
    omega
  have hupdate := pairGap_sampleNext c t X Y
  rw [pairGap_eq_nat c X Y hYX, hk, ha] at hupdate
  have hnextYX :
      count (sampleNext c t) Y ≤ count (sampleNext c t) X := by
    unfold pairGap at hupdate
    omega
  rw [pairGap_eq_nat (sampleNext c t) X Y hnextYX] at hupdate
  exact_mod_cast hupdate

/-- Exact expectation decomposition of one physical raw interaction into the
five fixed-pair jump masses. -/
theorem expect_multiStep_pairGapPotential
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (u : ℝ≥0∞)
    (hg2 : 2 ≤ pairGapNat c X Y) :
    expect (multiStep c h3) (pairGapPotential u X Y) =
      pairDeltaMass c h3 X Y (-2) *
          u ^ (pairGapNat c X Y - 2) +
      pairDeltaMass c h3 X Y (-1) *
          u ^ (pairGapNat c X Y - 1) +
      pairDeltaMass c h3 X Y 0 *
          u ^ pairGapNat c X Y +
      pairDeltaMass c h3 X Y 1 *
          u ^ (pairGapNat c X Y + 1) +
      pairDeltaMass c h3 X Y 2 *
          u ^ (pairGapNat c X Y + 2) := by
  classical
  unfold multiStep
  rw [expect_map]
  unfold expect pairDeltaMass
  simp only [tsum_fintype, pairGapPotential]
  let g := pairGapNat c X Y
  have hg : 2 ≤ g := hg2
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
  symm
  calc
    (∑ t : TripleSample c,
          (if samplePairDelta t X Y = -2 then triplePMF c h3 t else 0)) *
            u ^ (g - 2) +
        (∑ t : TripleSample c,
          (if samplePairDelta t X Y = -1 then triplePMF c h3 t else 0)) *
            u ^ (g - 1) +
        (∑ t : TripleSample c,
          (if samplePairDelta t X Y = 0 then triplePMF c h3 t else 0)) *
            u ^ g +
        (∑ t : TripleSample c,
          (if samplePairDelta t X Y = 1 then triplePMF c h3 t else 0)) *
            u ^ (g + 1) +
        (∑ t : TripleSample c,
          (if samplePairDelta t X Y = 2 then triplePMF c h3 t else 0)) *
            u ^ (g + 2) =
      ∑ t : TripleSample c,
        (((((if samplePairDelta t X Y = -2 then triplePMF c h3 t else 0) *
              u ^ (g - 2) +
            (if samplePairDelta t X Y = -1 then triplePMF c h3 t else 0) *
              u ^ (g - 1)) +
          (if samplePairDelta t X Y = 0 then triplePMF c h3 t else 0) *
              u ^ g) +
          (if samplePairDelta t X Y = 1 then triplePMF c h3 t else 0) *
              u ^ (g + 1)) +
          (if samplePairDelta t X Y = 2 then triplePMF c h3 t else 0) *
              u ^ (g + 2)) := by
      simp only [Finset.sum_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = ∑ t : TripleSample c,
          triplePMF c h3 t *
            u ^ pairGapNat (sampleNext c t) X Y := by
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
      rcases hcases with h | h | h | h | h <;> simp [h]

/-- The actual physical multi-species kernel conserves the fixed-pair
geometric potential while the global pairwise gap assumption holds. -/
theorem multiStep_pairGapPotential_conserve
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (hgap : HasPairwiseGap c X d) :
    expect (multiStep c h3)
        (pairGapPotential (pairGapBase n d) X Y) ≤
      pairGapPotential (pairGapBase n d) X Y c := by
  have hXYgap := hgap Y (Ne.symm hXY)
  have hg2 : 2 ≤ pairGapNat c X Y := by
    unfold pairGapNat
    omega
  rw [expect_multiStep_pairGapPotential
    c h3 X Y (pairGapBase n d) hg2]
  unfold pairGapPotential
  exact five_jump_geometric_of_core hg2
    (pairDeltaMass_five_mgf c h3 X Y hXY d hgap)

end Tri.Multi

#print axioms Tri.Multi.pairGapNat_sampleNext_of_delta
#print axioms Tri.Multi.expect_multiStep_pairGapPotential
#print axioms Tri.Multi.multiStep_pairGapPotential_conserve
