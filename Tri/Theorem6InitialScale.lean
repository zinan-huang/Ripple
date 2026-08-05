/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17FixedScale
import Mathlib.Algebra.Order.Floor.Div

/-!
# Initial activation scale for Theorem 6

The fifth-root parameter is the denominator in the Lemma 16 scale.  The
additional strict condition placing this scale below the fixed critical scale
is kept explicit; it is a genuine stronger large-population requirement.
-/

namespace Tri

noncomputable section

/-- Lemma 16 scale obtained by dividing the population by the binary upper
fifth root of the common concentration volume. -/
def theorem6InitialScale
    (n γ : ℕ) : ℕ :=
  n ⌊/⌋ theorem6FifthRoot n γ

/-- The quotient scale automatically satisfies the fifth-power condition. -/
theorem theorem6InitialScale_root
    (n γ : ℕ)
    (hN : 0 < theorem6Q n γ * n) :
    theorem6InitialScale n γ ^ 5 *
          theorem6Q n γ * n ≤
      n ^ 5 := by
  have hd :
      0 < theorem6FifthRoot n γ := by
    unfold theorem6FifthRoot binaryFifthRoot
    positivity
  have hmul :
      theorem6InitialScale n γ *
          theorem6FifthRoot n γ ≤
        n := by
    unfold theorem6InitialScale
    have h :=
      (le_floorDiv_iff_mul_le hd).1
        (le_rfl :
          n ⌊/⌋ theorem6FifthRoot n γ ≤
            n ⌊/⌋ theorem6FifthRoot n γ)
    simpa [mul_comm] using h
  have hrootUpper :=
    (theorem6FifthRoot_bounds n γ hN).1.le
  calc
    theorem6InitialScale n γ ^ 5 *
          theorem6Q n γ * n =
        theorem6InitialScale n γ ^ 5 *
          (theorem6Q n γ * n) := by ring
    _ ≤ theorem6InitialScale n γ ^ 5 *
          theorem6FifthRoot n γ ^ 5 :=
      Nat.mul_le_mul_left
        (theorem6InitialScale n γ ^ 5)
        hrootUpper
    _ =
        (theorem6InitialScale n γ *
          theorem6FifthRoot n γ) ^ 5 := by ring
    _ ≤ n ^ 5 :=
      Nat.pow_le_pow_left hmul 5

/-- Arithmetic facts needed to start the fixed Lemma 16--17 route. -/
structure Theorem6InitialScaleFacts
    (n γ : ℕ) : Prop where
  hpositive :
    0 < theorem6InitialScale n γ
  hfour :
    4 ≤ theorem6InitialScale n γ
  hquarter :
    4 * theorem6InitialScale n γ ≤ n
  hroot :
    theorem6InitialScale n γ ^ 5 *
          theorem6Q n γ * n ≤
      n ^ 5
  hq :
    theorem6Q n γ ≤ theorem6InitialScale n γ
  hbelow :
    theorem6FixedCStarSq *
        theorem6InitialScale n γ <
      n

/-- Three transparent multiplicative room conditions supply the complete
initial-scale package.  The strict fifth-root condition is exactly what makes
the subsequent fixed critical scale larger than the Lemma 16 scale. -/
theorem theorem6InitialScaleFacts
    (n γ : ℕ)
    (hN : 0 < theorem6Q n γ * n)
    (hfourRoom :
      4 * theorem6FifthRoot n γ ≤ n)
    (hqRoom :
      theorem6Q n γ *
          theorem6FifthRoot n γ ≤
        n)
    (hcritical :
      theorem6FixedCStarSq <
        theorem6FifthRoot n γ) :
    Theorem6InitialScaleFacts n γ := by
  have hd :
      0 < theorem6FifthRoot n γ := by
    unfold theorem6FifthRoot binaryFifthRoot
    positivity
  have ha4 :
      4 ≤ theorem6InitialScale n γ := by
    unfold theorem6InitialScale
    apply (le_floorDiv_iff_mul_le hd).2
    simpa [mul_comm] using hfourRoom
  have hq :
      theorem6Q n γ ≤ theorem6InitialScale n γ := by
    unfold theorem6InitialScale
    apply (le_floorDiv_iff_mul_le hd).2
    simpa [mul_comm] using hqRoom
  have hmul :
      theorem6InitialScale n γ *
          theorem6FifthRoot n γ ≤
        n := by
    unfold theorem6InitialScale
    have h :=
      (le_floorDiv_iff_mul_le hd).1
        (le_rfl :
          n ⌊/⌋ theorem6FifthRoot n γ ≤
            n ⌊/⌋ theorem6FifthRoot n γ)
    simpa [mul_comm] using h
  have hquarter :
      4 * theorem6InitialScale n γ ≤ n := by
    have hfourD :
        4 ≤ theorem6FifthRoot n γ := by
      have hfixed :
          4 ≤ theorem6FixedCStarSq := by
        norm_num [theorem6FixedCStarSq,
          theorem6FixedCStar]
      omega
    calc
      4 * theorem6InitialScale n γ ≤
          theorem6FifthRoot n γ *
            theorem6InitialScale n γ :=
        Nat.mul_le_mul_right
          (theorem6InitialScale n γ) hfourD
      _ =
          theorem6InitialScale n γ *
            theorem6FifthRoot n γ := by ring
      _ ≤ n := hmul
  have hbelow :
      theorem6FixedCStarSq *
          theorem6InitialScale n γ <
        n := by
    have haPos :
        0 < theorem6InitialScale n γ := by
      omega
    calc
      theorem6FixedCStarSq *
            theorem6InitialScale n γ <
          theorem6FifthRoot n γ *
            theorem6InitialScale n γ :=
        Nat.mul_lt_mul_of_pos_right
          hcritical haPos
      _ =
          theorem6InitialScale n γ *
            theorem6FifthRoot n γ := by ring
      _ ≤ n := hmul
  exact
    { hpositive := by omega
      hfour := ha4
      hquarter := hquarter
      hroot :=
        theorem6InitialScale_root n γ hN
      hq := hq
      hbelow := hbelow }

end

end Tri

#print axioms Tri.theorem6InitialScale_root
#print axioms Tri.theorem6InitialScaleFacts
