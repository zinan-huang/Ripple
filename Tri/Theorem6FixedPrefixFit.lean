/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedPrefix

/-!
# Endpoint certificate for the fixed-prefix reaction fit

One reaction capacity at the initial scale pays the constant and active
lower bounds.  Bounding the cubic mean at the last dyadic source then pays
the whole indexed prefix.
-/

namespace Tri

noncomputable section

/-- The indexed integral reaction fit follows from one initial capacity and
one last-source cubic bound. -/
theorem lemma17FixedReactionLower_fit_of_endpoint
    (n q cStar a m : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hcapacity : 76 * cStar ≤ a)
    (hmean :
      (2 * lemma17FixedScale a m) ^ 3 ≤
        (a ⌊/⌋ (76 * cStar)) * n ^ 2)
    (hactive :
      15 * q ≤
        4 * cStar * (a ⌊/⌋ (76 * cStar))) :
    ∀ j ≤ m,
      76 * cStar *
          lemma17FixedReactionLower n q cStar
            (lemma17FixedScale a j) ≤
        lemma17FixedScale a j := by
  have hC : 0 < 76 * cStar := by
    positivity
  have hnSq : 0 < n ^ 2 := Nat.pow_pos hn
  have hcapOne : 1 ≤ a ⌊/⌋ (76 * cStar) := by
    apply (le_floorDiv_iff_mul_le hC).2
    simpa using hcapacity
  have hcapFit :
      76 * cStar * (a ⌊/⌋ (76 * cStar)) ≤ a := by
    have h :=
      (le_floorDiv_iff_mul_le hC).1
        (le_rfl :
          a ⌊/⌋ (76 * cStar) ≤
            a ⌊/⌋ (76 * cStar))
    simpa [mul_comm] using h
  intro j hj
  have hscale :
      lemma17FixedScale a j ≤
        lemma17FixedScale a m :=
    lemma17FixedScale_mono a j m hj
  have hbase :
      a ≤ lemma17FixedScale a j := by
    simpa [lemma17FixedScale_zero] using
      lemma17FixedScale_mono a 0 j (Nat.zero_le j)
  have hmeanJ :
      lemma17FixedReactionMeanLower n
          (lemma17FixedScale a j) ≤
        a ⌊/⌋ (76 * cStar) := by
    apply (ceilDiv_le_iff_le_mul hnSq).2
    calc
      (2 * lemma17FixedScale a j) ^ 3 ≤
          (2 * lemma17FixedScale a m) ^ 3 :=
        Nat.pow_le_pow_left
          (Nat.mul_le_mul_left 2 hscale) 3
      _ ≤
          (a ⌊/⌋ (76 * cStar)) * n ^ 2 :=
        hmean
      _ = n ^ 2 * (a ⌊/⌋ (76 * cStar)) := by
        ring
  have hactiveJ :
      lemma17FixedReactionActiveLower q cStar ≤
        a ⌊/⌋ (76 * cStar) := by
    have hFour : 0 < 4 * cStar := by
      positivity
    apply (ceilDiv_le_iff_le_mul hFour).2
    simpa [mul_comm] using hactive
  have hlower :
      lemma17FixedReactionLower n q cStar
          (lemma17FixedScale a j) ≤
        a ⌊/⌋ (76 * cStar) := by
    unfold lemma17FixedReactionLower
    exact max_le hcapOne (max_le hmeanJ hactiveJ)
  calc
    76 * cStar *
          lemma17FixedReactionLower n q cStar
            (lemma17FixedScale a j) ≤
        76 * cStar * (a ⌊/⌋ (76 * cStar)) :=
      Nat.mul_le_mul_left (76 * cStar) hlower
    _ ≤ a := hcapFit
    _ ≤ lemma17FixedScale a j := hbase

end

end Tri

#print axioms Tri.lemma17FixedReactionLower_fit_of_endpoint
