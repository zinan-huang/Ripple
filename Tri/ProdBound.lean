/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Regions
import Tri.Rung

/-!
# Concrete lower bounds for productive interaction mass

This module turns the two productive reaction counts into the corresponding
one-step probability and then supplies arithmetic lower bounds for that mass.
All public statements use successor-indexed populations, so no truncated
natural-number subtraction is needed.

The phase-1 result gives the uniform constant `21 / 64` at every state in the
open region `n / 2 < x < 7n / 8`.
-/

namespace Tri

open scoped ENNReal

/-- Six times `C(s+2,3)` is the subtraction-free falling-factorial formula. -/
theorem six_mul_choose_three_add_two (s : ℕ) :
    6 * Nat.choose (s + 2) 3 = (s + 2) * (s + 1) * s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [show s + 1 + 2 = (s + 2) + 1 by omega,
        Nat.choose_succ_succ, Nat.mul_add, ih]
      have htwo := two_mul_choose_two_succ (s + 1)
      calc
        6 * Nat.choose (s + 2) 2 + (s + 2) * (s + 1) * s =
            3 * (2 * Nat.choose (s + 2) 2) + (s + 2) * (s + 1) * s := by ring
        _ = 3 * ((s + 2) * (s + 1)) + (s + 2) * (s + 1) * s := by rw [htwo]
        _ = ((s + 1) + 2) * ((s + 1) + 1) * (s + 1) := by ring

/-- The productive count cross-multiplied with the closed-form denominator. -/
theorem productive_count_cross (a b : ℕ) :
    ((a + b + 2) * (a + b + 1)) * (upCount a b + downCount a b) =
      Nat.choose (a + b + 2) 3 * (3 * ((a + 1) * (b + 1))) := by
  have hprod := productive_two_mul (a + 1) (b + 1)
  have hchoose := six_mul_choose_three_add_two (a + b)
  have hcount : 2 * (upCount a b + downCount a b) =
      (a + 1) * (b + 1) * (a + b) := by
    simp only [upCount, downCount]
    nlinarith [hprod]
  have htwice :
      2 * (((a + b + 2) * (a + b + 1)) * (upCount a b + downCount a b)) =
        2 * (Nat.choose (a + b + 2) 3 * (3 * ((a + 1) * (b + 1)))) := by
    calc
      2 * (((a + b + 2) * (a + b + 1)) * (upCount a b + downCount a b)) =
          ((a + b + 2) * (a + b + 1)) *
            (2 * (upCount a b + downCount a b)) := by ring
      _ = ((a + b + 2) * (a + b + 1)) *
            ((a + 1) * (b + 1) * (a + b)) := by rw [hcount]
      _ = ((a + b + 2) * (a + b + 1) * (a + b)) *
            ((a + 1) * (b + 1)) := by ring
      _ = (6 * Nat.choose (a + b + 2) 3) * ((a + 1) * (b + 1)) := by rw [hchoose]
      _ = 2 * (Nat.choose (a + b + 2) 3 * (3 * ((a + 1) * (b + 1)))) := by ring
  omega

/-- The two reaction atoms have exactly the productive count divided by the
total number of unordered triples. -/
theorem productive_mass_eq (a b n : ℕ) (h3 : 3 ≤ n) (hb : a + b + 2 = n) :
    triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2) =
      ((upCount a b + downCount a b : ℕ) : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  rw [triStep_down, triStep_up, ENNReal.div_add_div_same]
  rw [show (a + 1) + (b + 1) = n by omega]
  simp only [upCount, downCount]
  push_cast
  ring_nf

/-- The productive mass in closed form, with the predecessor of `n` written
as `a+b+1` rather than by natural subtraction. -/
theorem productive_mass_closed (a b n : ℕ) (h3 : 3 ≤ n)
    (hb : a + b + 2 = n) :
    triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2) =
      ((3 * ((a + 1) * (b + 1)) : ℕ) : ℝ≥0∞) /
        ((n * (a + b + 1) : ℕ) : ℝ≥0∞) := by
  rw [productive_mass_eq a b n h3 hb]
  have hchoose0 : ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (choose_three_pos h3).ne'
  have hchooseTop : ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hden0 : ((n * (a + b + 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]
    omega
  have hdenTop : ((n * (a + b + 1) : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.div_eq_div_iff hden0 hdenTop hchoose0 hchooseTop).2
  have hcross := productive_count_cross a b
  rw [hb] at hcross
  exact_mod_cast hcross

/-- If `K` lower-bounds `x*y`, then the productive probability is at least
`3K / (n(n-1))`, with `n-1` represented subtraction-free as `a+b+1`. -/
theorem productive_mass_ge (a b n K : ℕ) (h3 : 3 ≤ n)
    (hb : a + b + 2 = n) (hK : K ≤ (a + 1) * (b + 1)) :
    ((3 * K : ℕ) : ℝ≥0∞) / ((n * (a + b + 1) : ℕ) : ℝ≥0∞) ≤
      triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2) := by
  rw [productive_mass_closed a b n h3 hb]
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.mul_le_mul_left 3 hK

/-- Every interior state has productive probability at least `3/n`.  Unlike
the phase-1 constant, this bound remains valid up to the one-minority boundary
and therefore supplies the current one-sided rung premise on its whole live
region. -/
theorem productive_mass_ge_interior (a b n : ℕ) (h3 : 3 ≤ n)
    (hb : a + b + 2 = n) :
    (3 : ℝ≥0∞) / (n : ℝ≥0∞) ≤
      triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2) := by
  have hxy : a + b + 1 ≤ (a + 1) * (b + 1) := by
    have hphase3 := (productive_ge_phase3 (x := a + 1) (y := b + 1)
      (n := n) (by omega) (by omega) (by omega)).2
    omega
  have hge := productive_mass_ge a b n (a + b + 1) h3 hb hxy
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hnTop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hden0 : ((n * (a + b + 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]
    omega
  have hdenTop : ((n * (a + b + 1) : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hcancel :
      ((3 * (a + b + 1) : ℕ) : ℝ≥0∞) /
          ((n * (a + b + 1) : ℕ) : ℝ≥0∞) =
        (3 : ℝ≥0∞) / (n : ℝ≥0∞) := by
    apply (ENNReal.div_eq_div_iff hn0 hnTop hden0 hdenTop).2
    push_cast
    ring
  rw [← hcancel]
  exact hge

/-- The subtraction-free `3/n` bound supplies the productive-mass premise for
every successor-indexed interior state of a population of size `n`. -/
theorem hprod_interior (n : ℕ) (h3 : 3 ≤ n) :
    ∀ (a b : ℕ) (hb : a + b + 2 = n),
      (3 : ℝ≥0∞) / (n : ℝ≥0∞) ≤
        triStep (a + 1) (b + 1) (by omega) a +
          triStep (a + 1) (b + 1) (by omega) (a + 2) := by
  intro a b hb
  exact productive_mass_ge_interior a b n h3 hb

/-- In the phase-1 region, every interaction is productive with probability at
least the concrete constant `21 / 64`. -/
theorem hprod_phase1 (a b n : ℕ) (h3 : 3 ≤ n) (hb : a + b + 2 = n)
    (hxLo : n < 2 * (a + 1)) (hxHi : 8 * (a + 1) < 7 * n) :
    (21 : ℝ≥0∞) / 64 ≤
      triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2) := by
  rw [productive_mass_closed a b n h3 hb]
  have hxy : 7 * n * n < 64 * (a + 1) * (b + 1) :=
    xy_ge_phase1 hxLo hxHi (by omega)
  have hden : n * (a + b + 1) ≤ n * n := by
    exact Nat.mul_le_mul_left n (by omega)
  have hcross : 21 * (n * (a + b + 1)) ≤
      (3 * ((a + 1) * (b + 1))) * 64 := by
    nlinarith
  have hden0 : ((n * (a + b + 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]
    omega
  have hdenTop : ((n * (a + b + 1) : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)).2
  calc
    (21 : ℝ≥0∞) / 64 * ((n * (a + b + 1) : ℕ) : ℝ≥0∞) =
        ((21 : ℝ≥0∞) * ((n * (a + b + 1) : ℕ) : ℝ≥0∞)) / 64 := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ ((3 * ((a + 1) * (b + 1)) : ℕ) : ℝ≥0∞) := by
      apply ENNReal.div_le_of_le_mul
      exact_mod_cast hcross

end Tri
