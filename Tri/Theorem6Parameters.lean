/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib

/-!
# Finite arithmetic parameters for Theorem 6

This file begins the explicit finite parameter construction used to discharge
the arithmetic premises of the Lemma 16--19 headline.
-/

namespace Tri

/-- The common logarithmic concentration parameter. -/
def theorem6Q (n γ : ℕ) : ℕ :=
  γ * Nat.log 2 n

/-- Exponent of a binary upper approximation to the positive fifth root. -/
def binaryFifthRootExp (N : ℕ) : ℕ :=
  (Nat.log 2 N + 5) / 5

/-- A power-of-two upper approximation to the positive fifth root of `N`. -/
def binaryFifthRoot (N : ℕ) : ℕ :=
  2 ^ binaryFifthRootExp N

theorem five_mul_binaryFifthRootExp_lower (N : ℕ) :
    Nat.log 2 N + 1 ≤ 5 * binaryFifthRootExp N := by
  unfold binaryFifthRootExp
  omega

theorem five_mul_binaryFifthRootExp_upper (N : ℕ) :
    5 * binaryFifthRootExp N ≤ Nat.log 2 N + 5 := by
  unfold binaryFifthRootExp
  omega

/-- The binary approximation lies strictly above the fifth root and loses at
most a factor `32` after taking fifth powers. -/
theorem binaryFifthRoot_bounds
    (N : ℕ) (hN : 0 < N) :
    N < binaryFifthRoot N ^ 5 ∧
      binaryFifthRoot N ^ 5 ≤ 32 * N := by
  have hlogUpper :
      N < 2 ^ (Nat.log 2 N + 1) :=
    Nat.lt_pow_succ_log_self
      (by norm_num : 1 < (2 : ℕ)) N
  have hexpLower :
      2 ^ (Nat.log 2 N + 1) ≤
        2 ^ (5 * binaryFifthRootExp N) :=
    Nat.pow_le_pow_right (by norm_num)
      (five_mul_binaryFifthRootExp_lower N)
  have hexpUpper :
      2 ^ (5 * binaryFifthRootExp N) ≤
        2 ^ (Nat.log 2 N + 5) :=
    Nat.pow_le_pow_right (by norm_num)
      (five_mul_binaryFifthRootExp_upper N)
  have hlogLower :
      2 ^ Nat.log 2 N ≤ N :=
    Nat.pow_log_le_self 2 hN.ne'
  constructor
  · calc
      N < 2 ^ (Nat.log 2 N + 1) := hlogUpper
      _ ≤ 2 ^ (5 * binaryFifthRootExp N) :=
        hexpLower
      _ = binaryFifthRoot N ^ 5 := by
        unfold binaryFifthRoot
        rw [show 5 * binaryFifthRootExp N =
            binaryFifthRootExp N * 5 by omega,
          pow_mul]
  · calc
      binaryFifthRoot N ^ 5 =
          2 ^ (5 * binaryFifthRootExp N) := by
        unfold binaryFifthRoot
        rw [show 5 * binaryFifthRootExp N =
            binaryFifthRootExp N * 5 by omega,
          pow_mul]
      _ ≤ 2 ^ (Nat.log 2 N + 5) := hexpUpper
      _ = 32 * 2 ^ Nat.log 2 N := by
        rw [pow_add]
        ring
      _ ≤ 32 * N :=
        Nat.mul_le_mul_left 32 hlogLower

/-- The binary fifth-root denominator for the Theorem 6 concentration
parameter. -/
def theorem6FifthRoot (n γ : ℕ) : ℕ :=
  binaryFifthRoot (theorem6Q n γ * n)

theorem theorem6FifthRoot_bounds
    (n γ : ℕ)
    (hN : 0 < theorem6Q n γ * n) :
    theorem6Q n γ * n <
        theorem6FifthRoot n γ ^ 5 ∧
      theorem6FifthRoot n γ ^ 5 ≤
        32 * (theorem6Q n γ * n) := by
  simpa [theorem6FifthRoot] using
    binaryFifthRoot_bounds
      (theorem6Q n γ * n) hN

end Tri

#print axioms Tri.five_mul_binaryFifthRootExp_lower
#print axioms Tri.five_mul_binaryFifthRootExp_upper
#print axioms Tri.binaryFifthRoot_bounds
#print axioms Tri.theorem6FifthRoot_bounds
