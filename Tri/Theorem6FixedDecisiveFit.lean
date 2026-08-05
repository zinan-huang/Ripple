/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18FixedExplicit

/-!
# Primitive decisive reaction fit

The critical-stage reaction interval is reduced to one integral capacity and
the two exact numerator bounds defining the reaction lower endpoint.
-/

namespace Tri

noncomputable section

/-- Exact slot decomposition of a multiplicative fit for the fixed reaction
lower. -/
theorem lemma17FixedReactionLower_fit_iff_slots
    (n q cStar scale A B : ℕ) :
    A * lemma17FixedReactionLower n q cStar scale ≤ B ↔
      A ≤ B ∧
      A * lemma17FixedReactionMeanLower n scale ≤ B ∧
      A * lemma17FixedReactionActiveLower q cStar ≤ B := by
  unfold lemma17FixedReactionLower
  rw [mul_max, mul_max, max_le_iff, max_le_iff]
  simp only [Nat.mul_one]

/-- The decisive fit follows from the exact floor capacity at the critical
scale. -/
theorem theorem6FixedCriticalReactionLower_fit_of_capacity
    {n q cStar : ℕ}
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hcapacity :
      1200 * cStar ≤
        7 * theorem6FixedCriticalScale n)
    (hmean :
      (2 * theorem6FixedCriticalScale n) ^ 3 ≤
        n ^ 2 *
          ((7 * theorem6FixedCriticalScale n) ⌊/⌋
            (1200 * cStar)))
    (hactive :
      15 * q ≤
        4 * cStar *
          ((7 * theorem6FixedCriticalScale n) ⌊/⌋
            (1200 * cStar))) :
    1200 * cStar *
        lemma17FixedReactionLower n q cStar
          (theorem6FixedCriticalScale n) ≤
      7 * theorem6FixedCriticalScale n := by
  let A := 1200 * cStar
  let B := 7 * theorem6FixedCriticalScale n
  let r := B ⌊/⌋ A
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hnSq : 0 < n ^ 2 := Nat.pow_pos hn
  have hFour : 0 < 4 * cStar := by
    positivity
  have hrOne : 1 ≤ r := by
    apply (le_floorDiv_iff_mul_le hA).2
    simpa [A, B] using hcapacity
  have hrFit : A * r ≤ B := by
    have h :=
      (le_floorDiv_iff_mul_le hA).1
        (le_rfl : B ⌊/⌋ A ≤ B ⌊/⌋ A)
    simpa [A, B, r, mul_comm] using h
  apply
    (lemma17FixedReactionLower_fit_iff_slots
      n q cStar (theorem6FixedCriticalScale n)
      A B).2
  refine ⟨by simpa [A, B] using hcapacity, ?_, ?_⟩
  · have hceil :
        lemma17FixedReactionMeanLower n
            (theorem6FixedCriticalScale n) ≤ r := by
      apply (ceilDiv_le_iff_le_mul hnSq).2
      simpa [lemma17FixedReactionMeanLower, r, B, A] using
        hmean
    exact
      (Nat.mul_le_mul_left A hceil).trans hrFit
  · have hceil :
        lemma17FixedReactionActiveLower q cStar ≤ r := by
      apply (ceilDiv_le_iff_le_mul hFour).2
      simpa [lemma17FixedReactionActiveLower, r, B, A] using
        hactive
    exact
      (Nat.mul_le_mul_left A hceil).trans hrFit

end

end Tri

#print axioms Tri.lemma17FixedReactionLower_fit_iff_slots
#print axioms
  Tri.theorem6FixedCriticalReactionLower_fit_of_capacity
