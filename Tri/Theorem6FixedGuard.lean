/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedLandingRadius

/-!
# Population bound for the fixed decisive guard

The square-root envelope for the canonical terminal radius removes both the
maximum and the reserve expression from the final guard condition.
-/

namespace Tri

noncomputable section

/-- Exact affine expansion of the decisive reserve at the fixed epidemic
constant. -/
theorem theorem6FixedDecisiveGuard_eq
    (R : ℕ) :
    60 *
        lemma19FixedDdec theorem6FixedPostStages
          (4 * R) theorem6FixedCStar R =
      4_179_180 * R + 1_020 := by
  norm_num [lemma19FixedDdec, theorem6FixedPostStages,
    lemma19FixedHalfDrop, theorem6FixedCStar]
  ring

/-- A square-root-sized population bound implies the literal decisive guard
at the canonical terminal radius. -/
theorem theorem6FixedDecisiveGuard_of_sqrt_size
    {n γ : ℕ}
    (S : Theorem6InitialScaleFacts n γ)
    (hN : 0 < theorem6Q n γ * n)
    (hsize :
      theorem6FixedCStarSq *
          (4_179_180 *
              (8 *
                (Nat.sqrt
                    (theorem6Q n γ * n) +
                  1)) +
            1_020) ≤
        n) :
    60 *
        lemma19FixedDdec theorem6FixedPostStages
          (4 * theorem6FixedTerminalRadius
            n γ S.hpositive)
          theorem6FixedCStar
          (theorem6FixedTerminalRadius
            n γ S.hpositive) ≤
      theorem6FixedCriticalScale n := by
  have hR :
      theorem6FixedTerminalRadius n γ S.hpositive ≤
        8 * (Nat.sqrt (theorem6Q n γ * n) + 1) :=
    theorem6FixedTerminalRadius_le_sqrt S hN
  have hcap :
      4_179_180 *
            theorem6FixedTerminalRadius n γ S.hpositive +
          1_020 ≤
        theorem6FixedCriticalScale n := by
    apply theorem6FixedCriticalScale_lower
    exact hsize.trans'
      (Nat.mul_le_mul_left theorem6FixedCStarSq
        (Nat.add_le_add_right
          (Nat.mul_le_mul_left 4_179_180 hR)
          1_020))
  rw [theorem6FixedDecisiveGuard_eq]
  exact hcap

end

end Tri

#print axioms Tri.theorem6FixedDecisiveGuard_eq
#print axioms
  Tri.theorem6FixedDecisiveGuard_of_sqrt_size
