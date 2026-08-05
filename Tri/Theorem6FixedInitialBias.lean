/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6InitialRadius

/-!
# Polynomial room for the fixed initial radius

The fifth-root denominator controls the square-root radius by a cubic
polynomial.  Consequently one transparent size inequality pays the initial
bias condition used by the fixed Lemma 16--17 prefix.
-/

namespace Tri

noncomputable section

/-- The canonical initial radius is at most one plus the square of the
binary fifth-root denominator. -/
theorem theorem6InitialRadius_le_fifthRoot_sq_add_two
    {n γ : ℕ}
    (S : Theorem6InitialScaleFacts n γ)
    (hN : 0 < theorem6Q n γ * n) :
    theorem6InitialRadius
        (theorem6Q n γ)
        (theorem6InitialScale n γ) ≤
      theorem6FifthRoot n γ ^ 2 + 2 := by
  let q := theorem6Q n γ
  let d := theorem6FifthRoot n γ
  let a := theorem6InitialScale n γ
  have hd : 0 < d := by
    unfold d theorem6FifthRoot binaryFifthRoot
    positivity
  have hrootLower : q * n < d ^ 5 := by
    simpa [q, d] using
      (theorem6FifthRoot_bounds n γ hN).1
  have hfloor :
      (n ⌊/⌋ d) * d ≤ n := by
    have h :=
      (le_floorDiv_iff_mul_le hd).1
        (le_rfl : n ⌊/⌋ d ≤ n ⌊/⌋ d)
    simpa [mul_comm] using h
  have hqd : q * d ≤ n := by
    calc
      q * d ≤ a * d :=
        Nat.mul_le_mul_right d (by
          simpa [q, a] using S.hq)
      _ ≤ n := by
        unfold a theorem6InitialScale
        exact hfloor
  have hqSqMul : q ^ 2 * d < d ^ 5 := by
    calc
      q ^ 2 * d = q * (q * d) := by ring
      _ ≤ q * n := Nat.mul_le_mul_left q hqd
      _ < d ^ 5 := hrootLower
  have hq : q ≤ d ^ 2 := by
    by_contra hnot
    have hdq : d ^ 2 < q := Nat.lt_of_not_ge hnot
    have hpow : d ^ 4 < q ^ 2 := by
      nlinarith
    have : d ^ 5 ≤ q ^ 2 * d := by
      calc
        d ^ 5 = d ^ 4 * d := by ring
        _ ≤ q ^ 2 * d :=
          Nat.mul_le_mul_right d hpow.le
    omega
  have had : a * d ≤ n := by
    unfold a theorem6InitialScale
    exact hfloor
  have hrad :
      q * (a + 1) ≤ (d ^ 2 + 1) ^ 2 := by
    have hmul :
        d * (q * (a + 1)) ≤
          d * ((d ^ 2 + 1) ^ 2) := by
      calc
        d * (q * (a + 1)) =
            q * (a * d) + q * d := by ring
        _ ≤ q * n + d ^ 2 * d :=
          Nat.add_le_add
            (Nat.mul_le_mul_left q had)
            (Nat.mul_le_mul_right d hq)
        _ ≤ d ^ 5 + d ^ 2 * d :=
          Nat.add_le_add_right hrootLower.le _
        _ ≤ d * ((d ^ 2 + 1) ^ 2) := by
          nlinarith
    exact Nat.le_of_mul_le_mul_left hmul hd
  have hsqrt :
      Nat.sqrt (q * (a + 1)) ≤ d ^ 2 + 1 := by
    calc
      Nat.sqrt (q * (a + 1)) ≤
          Nat.sqrt ((d ^ 2 + 1) ^ 2) :=
        Nat.sqrt_le_sqrt hrad
      _ = d ^ 2 + 1 := Nat.sqrt_eq' _
  simpa [theorem6InitialRadius, q, d, a,
    Nat.add_assoc] using
    Nat.add_le_add_right hsqrt 1

/-- One polynomial size condition pays the initial bias inequality. -/
theorem theorem6InitialRadius_bias_of_size
    {n γ cStar : ℕ}
    (S : Theorem6InitialScaleFacts n γ)
    (hN : 0 < theorem6Q n γ * n)
    (hsize :
      38 * cStar * theorem6FifthRoot n γ *
          (theorem6FifthRoot n γ ^ 2 + 2) ≤ n) :
    38 * cStar *
        theorem6InitialRadius
          (theorem6Q n γ)
          (theorem6InitialScale n γ) ≤
      theorem6InitialScale n γ := by
  let d := theorem6FifthRoot n γ
  have hd : 0 < d := by
    unfold d theorem6FifthRoot binaryFifthRoot
    positivity
  have hrho :
      theorem6InitialRadius
          (theorem6Q n γ)
          (theorem6InitialScale n γ) ≤
        d ^ 2 + 2 := by
    have h :=
      theorem6InitialRadius_le_fifthRoot_sq_add_two
        S hN
    simpa [d] using h
  have hdiv :
      38 * cStar * (d ^ 2 + 2) ≤ n ⌊/⌋ d := by
    apply (le_floorDiv_iff_mul_le hd).2
    simpa [d, mul_assoc, mul_comm, mul_left_comm] using
      hsize
  calc
    38 * cStar *
          theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ) ≤
        38 * cStar * (d ^ 2 + 2) :=
      Nat.mul_le_mul_left (38 * cStar) hrho
    _ ≤ n ⌊/⌋ d := hdiv
    _ = theorem6InitialScale n γ := by
      simp [theorem6InitialScale, d]

end

end Tri

#print axioms
  Tri.theorem6InitialRadius_le_fifthRoot_sq_add_two
#print axioms Tri.theorem6InitialRadius_bias_of_size
