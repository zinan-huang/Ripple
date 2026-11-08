/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6LandingRadius

/-!
# Population bound for the fixed decisive guard

The square-root envelope for the canonical terminal radius removes both the
maximum and the reserve expression from the final guard condition.
-/

namespace Tri

noncomputable section

/-- Exact affine expansion of the decisive reserve at the fixed epidemic
constant. -/
theorem theorem6DecisiveGuard_eq
    (R : ℕ) :
    60 *
        lemma19Ddec theorem6PostStages
          (4 * R) theorem6CStar R =
      4_179_180 * R + 1_020 := by
  norm_num [lemma19Ddec, theorem6PostStages,
    lemma19HalfDrop, theorem6CStar]
  ring

/-- A square-root-sized population bound implies the literal decisive guard
at the canonical terminal radius. -/
theorem theorem6DecisiveGuard_of_sqrt_size
    {n γ : ℕ}
    (S : Theorem6InitialScaleFacts n γ)
    (hN : 0 < theorem6Q n γ * n)
    (hsize :
      theorem6CStarSq *
          (4_179_180 *
              (8 *
                (Nat.sqrt
                    (theorem6Q n γ * n) +
                  1)) +
            1_020) ≤
        n) :
    60 *
        lemma19Ddec theorem6PostStages
          (4 * theorem6TerminalRadius
            n γ S.hpositive)
          theorem6CStar
          (theorem6TerminalRadius
            n γ S.hpositive) ≤
      theorem6CriticalScale n := by
  have hR :
      theorem6TerminalRadius n γ S.hpositive ≤
        8 * (Nat.sqrt (theorem6Q n γ * n) + 1) :=
    theorem6TerminalRadius_le_sqrt S hN
  have hcap :
      4_179_180 *
            theorem6TerminalRadius n γ S.hpositive +
          1_020 ≤
        theorem6CriticalScale n := by
    apply theorem6CriticalScale_lower
    exact hsize.trans'
      (Nat.mul_le_mul_left theorem6CStarSq
        (Nat.add_le_add_right
          (Nat.mul_le_mul_left 4_179_180 hR)
          1_020))
  rw [theorem6DecisiveGuard_eq]
  exact hcap

end

end Tri

#print axioms Tri.theorem6DecisiveGuard_eq
#print axioms
  Tri.theorem6DecisiveGuard_of_sqrt_size
