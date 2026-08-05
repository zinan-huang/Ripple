/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBInvariant

/-!
# Arithmetic split for the Double-B raw-interaction clock

In an early small-gap band, every live state either contains a constant
fraction of free `Y` molecules or is blank-heavy.  These two cases support
different raw-time progress mechanisms and must not be collapsed to one
level-only productivity floor.
-/

namespace Tri

/-- A state whose `X-Y` gap is at most `n/8` either has at least `n/16`
free `Y` molecules or at least `3n/4` blanks.  All inequalities are
cross-multiplied. -/
theorem doubleB_freeY_or_blankHeavy
    {n x y b : ℕ}
    (hinv : x + y + b = n)
    (hgapUpper : 8 * x ≤ 8 * y + n) :
    n ≤ 16 * y ∨ 3 * n ≤ 4 * b := by
  omega

/-- The split specialized to the invariant subtype. -/
theorem doubleState_freeY_or_blankHeavy
    {n : ℕ} (s : DoubleState n)
    (hgapUpper : 8 * s.1.x ≤ 8 * s.1.y + n) :
    n ≤ 16 * s.1.y ∨ 3 * n ≤ 4 * s.1.b :=
  doubleB_freeY_or_blankHeavy s.2 hgapUpper

/-- The two fuel-producing pair classes (`xy` and `yb`) have total
unnormalized mass `y(x+b)`. -/
theorem doubleB_fuel_weight (x y b : ℕ) :
    PairComp.weight x y b .xy + PairComp.weight x y b .yb =
      y * (x + b) := by
  simp only [PairComp.weight]
  ring

/-- The exact unnormalized resolution drift at a witnessed gap `x=y+g`. -/
theorem doubleB_resolution_gap_weight
    {x y b g : ℕ} (hgap : y + g = x) :
    PairComp.weight x y b .yb + b * g =
      PairComp.weight x y b .xb := by
  subst x
  simp only [PairComp.weight]
  ring

/-- Monotone form of the resolution drift identity. -/
theorem doubleB_resolution_gap_weight_le
    {x y b g : ℕ} (hgap : y + g ≤ x) :
    PairComp.weight x y b .yb + b * g ≤
      PairComp.weight x y b .xb := by
  simp only [PairComp.weight]
  nlinarith [Nat.mul_le_mul_left b hgap]

/-- In a blank-heavy state, the unnormalized resolution drift dominates
`C(n,2) * g / n`.  This cross-multiplied form avoids both natural and
`ℝ≥0∞` subtraction. -/
theorem doubleB_blank_drift_cross
    {n x y b g : ℕ}
    (hn : 2 ≤ n)
    (hinv : x + y + b = n)
    (hgap : y + g ≤ x)
    (hblank : 3 * n ≤ 4 * b) :
    Nat.choose n 2 * g +
        n * PairComp.weight x y b .yb ≤
      n * PairComp.weight x y b .xb := by
  have hnb : n ≤ 2 * b := by omega
  have hsub : n * (n - 1) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 1)
  have hnnb : n * n ≤ n * (2 * b) :=
    Nat.mul_le_mul_left n hnb
  have hchoose := two_mul_choose_two n
  have hCb : Nat.choose n 2 ≤ n * b := by
    nlinarith
  have hCg : Nat.choose n 2 * g ≤ n * b * g :=
    Nat.mul_le_mul_right g hCb
  calc
    Nat.choose n 2 * g +
          n * PairComp.weight x y b .yb
        ≤ n * b * g + n * PairComp.weight x y b .yb :=
      Nat.add_le_add_right hCg _
    _ = n * b * (y + g) := by
      simp only [PairComp.weight]
      ring
    _ ≤ n * b * x := Nat.mul_le_mul_left (n * b) hgap
    _ = n * PairComp.weight x y b .xb := by
      simp only [PairComp.weight]
      ring

/-- A gap of at least `g` makes the resolution-down mass small enough for the
geometric base `2n/(2n+g)`, independently of the blank count. -/
theorem doubleB_gap_direction_cross
    {n x y b g : ℕ}
    (hinv : x + y + b = n)
    (hgap : y + g ≤ x) :
    (2 * n + g) * PairComp.weight x y b .yb ≤
      2 * n * PairComp.weight x y b .xb := by
  have hy : y ≤ n := by omega
  have hgy : g * y ≤ 2 * n * g := by
    have := Nat.mul_le_mul_left g hy
    nlinarith
  have hgyb := Nat.mul_le_mul_right b hgy
  have hgapb := Nat.mul_le_mul_left (2 * n * b) hgap
  calc
    (2 * n + g) * PairComp.weight x y b .yb
        = 2 * n * b * y + g * y * b := by
          simp only [PairComp.weight]
          ring
    _ ≤ 2 * n * b * y + 2 * n * g * b :=
      Nat.add_le_add_left hgyb _
    _ = 2 * n * b * (y + g) := by ring
    _ ≤ 2 * n * b * x := hgapb
    _ = 2 * n * PairComp.weight x y b .xb := by
      simp only [PairComp.weight]
      ring

/-- On a normal/free-`Y` tick, fuel pairs carry at least one sixteenth of the
total pair mass.  This is stated without division for direct use in the PMF
lower-bound layer. -/
theorem doubleB_normal_fuel_cross
    {n x y b : ℕ}
    (hinv : x + y + b = n)
    (hmaj : y ≤ x)
    (hnormal : n ≤ 16 * y) :
    Nat.choose n 2 ≤
      16 * (PairComp.weight x y b .xy +
        PairComp.weight x y b .yb) := by
  have hnxb : n ≤ 2 * (x + b) := by omega
  have hmul : n * n ≤ (16 * y) * (2 * (x + b)) :=
    Nat.mul_le_mul hnormal hnxb
  have hchoose := two_mul_choose_two n
  have hsub : n * (n - 1) ≤ n * n :=
    Nat.mul_le_mul_left n (Nat.sub_le n 1)
  rw [doubleB_fuel_weight]
  nlinarith

end Tri

#print axioms Tri.doubleB_freeY_or_blankHeavy
#print axioms Tri.doubleB_blank_drift_cross
#print axioms Tri.doubleB_gap_direction_cross
#print axioms Tri.doubleB_normal_fuel_cross
