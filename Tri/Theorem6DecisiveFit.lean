/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18Explicit

/-!
# Primitive decisive reaction fit

The critical-stage reaction interval is reduced to one integral capacity and
the two exact numerator bounds defining the reaction lower endpoint.
-/

namespace Tri

noncomputable section

/-- Exact slot decomposition of a multiplicative fit for the fixed reaction
lower. -/
theorem lemma17ReactionLower_fit_iff_slots
    (n q cStar scale A B : ℕ) :
    A * lemma17ReactionLower n q cStar scale ≤ B ↔
      A ≤ B ∧
      A * lemma17ReactionMeanLower n scale ≤ B ∧
      A * lemma17ReactionActiveLower q cStar ≤ B := by
  unfold lemma17ReactionLower
  rw [mul_max, mul_max, max_le_iff, max_le_iff]
  simp only [Nat.mul_one]

/-- The decisive fit follows from the exact floor capacity at the critical
scale. -/
theorem theorem6CriticalReactionLower_fit_of_capacity
    {n q cStar : ℕ}
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hcapacity :
      1200 * cStar ≤
        7 * theorem6CriticalScale n)
    (hmean :
      (2 * theorem6CriticalScale n) ^ 3 ≤
        n ^ 2 *
          ((7 * theorem6CriticalScale n) ⌊/⌋
            (1200 * cStar)))
    (hactive :
      15 * q ≤
        4 * cStar *
          ((7 * theorem6CriticalScale n) ⌊/⌋
            (1200 * cStar))) :
    1200 * cStar *
        lemma17ReactionLower n q cStar
          (theorem6CriticalScale n) ≤
      7 * theorem6CriticalScale n := by
  let A := 1200 * cStar
  let B := 7 * theorem6CriticalScale n
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
    (lemma17ReactionLower_fit_iff_slots
      n q cStar (theorem6CriticalScale n)
      A B).2
  refine ⟨by simpa [A, B] using hcapacity, ?_, ?_⟩
  · have hceil :
        lemma17ReactionMeanLower n
            (theorem6CriticalScale n) ≤ r := by
      apply (ceilDiv_le_iff_le_mul hnSq).2
      simpa [lemma17ReactionMeanLower, r, B, A] using
        hmean
    exact
      (Nat.mul_le_mul_left A hceil).trans hrFit
  · have hceil :
        lemma17ReactionActiveLower q cStar ≤ r := by
      apply (ceilDiv_le_iff_le_mul hFour).2
      simpa [lemma17ReactionActiveLower, r, B, A] using
        hactive
    exact
      (Nat.mul_le_mul_left A hceil).trans hrFit

end

end Tri

#print axioms Tri.lemma17ReactionLower_fit_iff_slots
#print axioms
  Tri.theorem6CriticalReactionLower_fit_of_capacity
