/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6InitialScale

/-!
# Size separation for the fixed initial scale

The binary fifth-root upper bound converts one fourth-power population
condition into the quotient room needed by the fixed prefix.  A separate
fifth-power separation places the initial scale below the fixed critical
scale.
-/

namespace Tri

noncomputable section

private theorem nat_le_of_pow_five_le
    {x y : ℕ}
    (h : x ^ 5 ≤ y ^ 5) :
    x ≤ y := by
  by_contra hnot
  have hyx : y < x := Nat.lt_of_not_ge hnot
  have hp : y ^ 5 < x ^ 5 :=
    Nat.pow_lt_pow_left hyx (by norm_num)
  omega

private theorem nat_lt_of_pow_five_lt
    {x y : ℕ}
    (h : x ^ 5 < y ^ 5) :
    x < y := by
  by_contra hnot
  have hyx : y ≤ x := Nat.le_of_not_gt hnot
  have hp : y ^ 5 ≤ x ^ 5 :=
    Nat.pow_le_pow_left hyx 5
  omega

/-- Explicit size separation constructs the complete initial-scale
certificate. -/
theorem theorem6InitialScaleFacts_of_size_separation
    {n γ : ℕ}
    (hN : 0 < theorem6Q n γ * n)
    (hqFour : 4 ≤ theorem6Q n γ)
    (hseed :
      32 * theorem6Q n γ ^ 6 ≤ n ^ 4)
    (hcritical :
      theorem6FixedCStarSq ^ 5 <
        theorem6Q n γ * n) :
    Theorem6InitialScaleFacts n γ := by
  let q := theorem6Q n γ
  let d := theorem6FifthRoot n γ
  let C := theorem6FixedCStarSq
  have hrootUpper :
      d ^ 5 ≤ 32 * (q * n) := by
    simpa [q, d] using
      (theorem6FifthRoot_bounds n γ hN).2
  have hqdPow :
      (q * d) ^ 5 ≤ n ^ 5 := by
    calc
      (q * d) ^ 5 = q ^ 5 * d ^ 5 := by ring
      _ ≤ q ^ 5 * (32 * (q * n)) :=
        Nat.mul_le_mul_left (q ^ 5) hrootUpper
      _ = (32 * q ^ 6) * n := by ring
      _ ≤ n ^ 4 * n := by
        exact Nat.mul_le_mul_right n (by
          simpa [q] using hseed)
      _ = n ^ 5 := by ring
  have hqd : q * d ≤ n :=
    nat_le_of_pow_five_le hqdPow
  have hfourRoom : 4 * d ≤ n := by
    calc
      4 * d ≤ q * d :=
        Nat.mul_le_mul_right d (by
          simpa [q] using hqFour)
      _ ≤ n := hqd
  have hrootLower :
      q * n < d ^ 5 := by
    simpa [q, d] using
      (theorem6FifthRoot_bounds n γ hN).1
  have hcritical' : C < d := by
    apply nat_lt_of_pow_five_lt
    calc
      C ^ 5 < q * n := by
        simpa [C, q] using hcritical
      _ < d ^ 5 := hrootLower
  exact
    theorem6InitialScaleFacts n γ hN
      (by simpa [d] using hfourRoom)
      (by simpa [q, d] using hqd)
      (by simpa [C, d] using hcritical')

end

end Tri

#print axioms
  Tri.theorem6InitialScaleFacts_of_size_separation
