/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6LandingRadius

/-!
# Explicit large-population threshold for fixed Theorem 6 parameters

For each fixed `γ`, an explicit power-of-two threshold makes the logarithmic
parameter large and makes both population guards used by the finite
construction automatic.
-/

namespace Tri

noncomputable section

/-- Coefficient used after taking fifth powers in the cubic fifth-root
guard. -/
def theorem6CubePolynomialCoefficient : ℕ :=
  (2 * theorem6CStarSq * 4_179_180) ^ 5 *
    32 ^ 3

/-- Coefficient that pays the square-root terminal-radius guard after
squaring. -/
def theorem6SqrtPolynomialCoefficient : ℕ :=
  (4 *
      (theorem6CStarSq *
        (8 * 4_179_180))) ^ 2

/-- Constant part shared by the two population guards. -/
def theorem6GuardConstant : ℕ :=
  2 * theorem6CStarSq * 1_020

/-- Logarithmic exponent sufficient for a fixed `γ`. -/
def theorem6ThresholdExponent
    (γ : ℕ) : ℕ :=
  max 8192
    (max 64
      (max theorem6GuardConstant
        (max
          (theorem6CubePolynomialCoefficient *
            γ ^ 3)
          (theorem6SqrtPolynomialCoefficient *
            γ))))

/-- Explicit population threshold for a fixed `γ`. -/
def theorem6Threshold
    (γ : ℕ) : ℕ :=
  2 ^ theorem6ThresholdExponent γ

/-- Above exponent `64`, the binary exponential dominates the sixth
power. -/
theorem theorem6PowSix_le_twoPow
    (k : ℕ)
    (hk : 64 ≤ k) :
    k ^ 6 ≤ 2 ^ k := by
  revert hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      by_cases hsmall : k < 70
      · interval_cases k <;> norm_num
      · have hk6 : 64 ≤ k - 6 := by omega
        have hlt : k - 6 < k := by omega
        have hprev :
            (k - 6) ^ 6 ≤ 2 ^ (k - 6) :=
          ih (k - 6) hlt hk6
        have hstep : k ≤ 2 * (k - 6) := by omega
        have hdecomp : k - 6 + 6 = k := by omega
        calc
          k ^ 6 ≤ (2 * (k - 6)) ^ 6 :=
            Nat.pow_le_pow_left hstep 6
          _ = 64 * (k - 6) ^ 6 := by ring
          _ ≤ 64 * 2 ^ (k - 6) :=
            Nat.mul_le_mul_left 64 hprev
          _ = 2 ^ 6 * 2 ^ (k - 6) := by norm_num
          _ = 2 ^ (k - 6 + 6) := by
            rw [mul_comm, ← pow_add]
          _ = 2 ^ k := by rw [hdecomp]

/-- A fixed coefficient times a bounded power of `γ log₂ n` is eventually
dominated by `n`. -/
theorem theorem6Polynomial_le_population
    (D γ n r : ℕ)
    (hn : 0 < n)
    (hr : r + 1 ≤ 6)
    (hlog64 : 64 ≤ Nat.log 2 n)
    (hcoefficient :
      D * γ ^ r ≤ Nat.log 2 n) :
    D * (γ * Nat.log 2 n) ^ r ≤ n := by
  let L := Nat.log 2 n
  have hL : 1 ≤ L := by omega
  calc
    D * (γ * Nat.log 2 n) ^ r =
        (D * γ ^ r) * L ^ r := by
      simp [L]
      ring
    _ ≤ L * L ^ r :=
      Nat.mul_le_mul_right (L ^ r) hcoefficient
    _ = L ^ (r + 1) := by
      rw [pow_succ]
      ring
    _ ≤ L ^ 6 :=
      Nat.pow_le_pow_right hL hr
    _ ≤ 2 ^ L :=
      theorem6PowSix_le_twoPow L hlog64
    _ ≤ n := by
      simpa [L] using
        Nat.pow_log_le_self 2 hn.ne'

/-- The explicit population threshold yields its defining logarithmic lower
bound. -/
theorem theorem6Threshold_log
    {n γ : ℕ}
    (hn : theorem6Threshold γ ≤ n) :
    theorem6ThresholdExponent γ ≤
      Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by norm_num)
  simpa [theorem6Threshold] using hn

private theorem nat_le_of_pow_five_le
    {x y : ℕ}
    (h : x ^ 5 ≤ y ^ 5) :
    x ≤ y := by
  by_contra hnot
  have hyx : y < x := Nat.lt_of_not_ge hnot
  have hp : y ^ 5 < x ^ 5 :=
    Nat.pow_lt_pow_left hyx (by norm_num)
  omega

private theorem add_le_of_two_mul_le
    {x y n : ℕ}
    (hx : 2 * x ≤ n)
    (hy : 2 * y ≤ n) :
    x + y ≤ n := by
  omega

/-- Above the fixed-`γ` threshold, the common logarithmic parameter is at
least `8192`. -/
theorem theorem6Threshold_qLarge
    {n γ : ℕ}
    (hγ : 1 ≤ γ)
    (hn : theorem6Threshold γ ≤ n) :
    8192 ≤ theorem6Q n γ := by
  have hlog :=
    theorem6Threshold_log hn
  have h8192 :
      8192 ≤ theorem6ThresholdExponent γ := by
    simp [theorem6ThresholdExponent]
  have hlog8192 :
      8192 ≤ Nat.log 2 n :=
    h8192.trans hlog
  unfold theorem6Q
  calc
    8192 ≤ Nat.log 2 n := hlog8192
    _ = 1 * Nat.log 2 n := by simp
    _ ≤ γ * Nat.log 2 n :=
      Nat.mul_le_mul_right (Nat.log 2 n) hγ

/-- Above the fixed-`γ` threshold, the sparsity condition used by the finite
construction is automatic. -/
theorem theorem6Threshold_size
    {n γ : ℕ}
    (hn : theorem6Threshold γ ≤ n) :
    6 * theorem6Q n γ ≤ n := by
  have hlog :=
    theorem6Threshold_log hn
  have hlog64 :
      64 ≤ Nat.log 2 n := by
    exact
      (by
        simp [theorem6ThresholdExponent] :
          64 ≤ theorem6ThresholdExponent γ).trans hlog
  have hlargeCoefficient :
      theorem6SqrtPolynomialCoefficient * γ ≤
        Nat.log 2 n := by
    exact
      (by
        simp [theorem6ThresholdExponent] :
          theorem6SqrtPolynomialCoefficient * γ ≤
            theorem6ThresholdExponent γ).trans hlog
  have hcoefficient :
      6 * γ ≤ Nat.log 2 n := by
    exact
      (Nat.mul_le_mul_right γ
        (by
          norm_num
            [theorem6SqrtPolynomialCoefficient,
              theorem6CStarSq,
              theorem6CStar])).trans
        hlargeCoefficient
  have hthresholdPositive :
      0 < theorem6Threshold γ := by
    simp [theorem6Threshold]
  have hnPos : 0 < n :=
    hthresholdPositive.trans_le hn
  simpa [theorem6Q] using
    theorem6Polynomial_le_population
      6 γ n 1 hnPos (by norm_num) hlog64
      (by simpa using hcoefficient)

/-- Above the fixed-`γ` threshold, the cubic fifth-root population guard is
automatic. -/
theorem theorem6Threshold_cubeGuard
    {n γ : ℕ}
    (hγ : 1 ≤ γ)
    (hn : theorem6Threshold γ ≤ n) :
    theorem6CStarSq *
        (4_179_180 *
            theorem6FifthRoot n γ ^ 3 +
          1_020) ≤
      n := by
  let q := theorem6Q n γ
  let d := theorem6FifthRoot n γ
  let K := 2 * theorem6CStarSq * 4_179_180
  let D := theorem6CubePolynomialCoefficient
  have hlog :=
    theorem6Threshold_log hn
  have hlog64 :
      64 ≤ Nat.log 2 n := by
    exact
      (by
        simp [theorem6ThresholdExponent] :
          64 ≤ theorem6ThresholdExponent γ).trans hlog
  have hcoefficient :
      D * γ ^ 3 ≤ Nat.log 2 n := by
    exact
      (by
        simp [D, theorem6ThresholdExponent] :
          D * γ ^ 3 ≤
            theorem6ThresholdExponent γ).trans hlog
  have hthresholdPositive :
      0 < theorem6Threshold γ := by
    simp [theorem6Threshold]
  have hnPos : 0 < n :=
    hthresholdPositive.trans_le hn
  have hqLarge :=
    theorem6Threshold_qLarge hγ hn
  have hqPos : 0 < q := by
    dsimp [q]
    omega
  have hN : 0 < q * n :=
    Nat.mul_pos hqPos hnPos
  have hpoly :
      D * q ^ 3 ≤ n := by
    simpa [D, q, theorem6Q] using
      theorem6Polynomial_le_population
        D γ n 3 hnPos (by norm_num)
        hlog64 hcoefficient
  have hd5 : d ^ 5 ≤ 32 * (q * n) := by
    simpa [d, q] using
      (theorem6FifthRoot_bounds n γ
        (by simpa [q] using hN)).2
  have hmainPow :
      (K * d ^ 3) ^ 5 ≤ n ^ 5 := by
    calc
      (K * d ^ 3) ^ 5 =
          K ^ 5 * (d ^ 5) ^ 3 := by ring
      _ ≤ K ^ 5 * (32 * (q * n)) ^ 3 :=
        Nat.mul_le_mul_left (K ^ 5)
          (Nat.pow_le_pow_left hd5 3)
      _ = (D * q ^ 3) * n ^ 3 := by
        simp [D, K,
          theorem6CubePolynomialCoefficient]
        ring
      _ ≤ n * n ^ 3 :=
        Nat.mul_le_mul_right (n ^ 3) hpoly
      _ = n ^ 4 := by ring
      _ ≤ n ^ 5 := by
        calc
          n ^ 4 = n ^ 4 * 1 := by ring
          _ ≤ n ^ 4 * n :=
            Nat.mul_le_mul_left (n ^ 4)
              (by omega)
          _ = n ^ 5 := by ring
  have hmain : K * d ^ 3 ≤ n :=
    nat_le_of_pow_five_le hmainPow
  have hconstantLog :
      theorem6GuardConstant ≤
        Nat.log 2 n := by
    exact
      (by
        simp [theorem6ThresholdExponent] :
          theorem6GuardConstant ≤
            theorem6ThresholdExponent γ).trans hlog
  have hlogSelf :
      Nat.log 2 n ≤ n := by
    calc
      Nat.log 2 n ≤ 2 ^ Nat.log 2 n :=
        (Nat.log 2 n).lt_two_pow_self.le
      _ ≤ n := Nat.pow_log_le_self 2 hnPos.ne'
  have hconstant :
      2 * (theorem6CStarSq * 1_020) ≤ n := by
    simpa [theorem6GuardConstant] using
      hconstantLog.trans hlogSelf
  have hmain' :
      2 *
          (theorem6CStarSq *
            (4_179_180 * d ^ 3)) ≤
        n := by
    calc
      2 *
          (theorem6CStarSq *
            (4_179_180 * d ^ 3)) =
          K * d ^ 3 := by
        simp [K]
        ring
      _ ≤ n := hmain
  calc
    theorem6CStarSq *
          (4_179_180 * d ^ 3 + 1_020) =
        theorem6CStarSq *
            (4_179_180 * d ^ 3) +
          theorem6CStarSq * 1_020 := by
      rw [Nat.mul_add]
    _ ≤ n :=
      add_le_of_two_mul_le hmain' hconstant

/-- Above the fixed-`γ` threshold, the square-root terminal-radius population
guard is automatic. -/
theorem theorem6Threshold_sqrtGuard
    {n γ : ℕ}
    (hγ : 1 ≤ γ)
    (hn : theorem6Threshold γ ≤ n) :
    theorem6CStarSq *
        (4_179_180 *
            (8 *
              (Nat.sqrt (theorem6Q n γ * n) + 1)) +
          1_020) ≤
      n := by
  let q := theorem6Q n γ
  let x := q * n
  let r := Nat.sqrt x
  let K :=
    theorem6CStarSq * (8 * 4_179_180)
  let D := theorem6SqrtPolynomialCoefficient
  have hlog :=
    theorem6Threshold_log hn
  have hlog64 :
      64 ≤ Nat.log 2 n := by
    exact
      (by
        simp [theorem6ThresholdExponent] :
          64 ≤ theorem6ThresholdExponent γ).trans hlog
  have hcoefficient :
      D * γ ≤ Nat.log 2 n := by
    exact
      (by
        simp [D, theorem6ThresholdExponent] :
          D * γ ≤
            theorem6ThresholdExponent γ).trans hlog
  have hthresholdPositive :
      0 < theorem6Threshold γ := by
    simp [theorem6Threshold]
  have hnPos : 0 < n :=
    hthresholdPositive.trans_le hn
  have hqLarge :=
    theorem6Threshold_qLarge hγ hn
  have hqPos : 0 < q := by
    dsimp [q]
    omega
  have hxPos : 0 < x :=
    Nat.mul_pos hqPos hnPos
  have hrPos : 1 ≤ r := by
    exact (Nat.sqrt_pos).2 hxPos
  have hrSq : r ^ 2 ≤ x := by
    simpa [r] using Nat.sqrt_le' x
  have hpoly :
      D * q ≤ n := by
    have hcoefficient' :
        D * γ ^ 1 ≤ Nat.log 2 n := by
      simpa using hcoefficient
    simpa [D, q, theorem6Q] using
      theorem6Polynomial_le_population
        D γ n 1 hnPos (by norm_num)
        hlog64 hcoefficient'
  have hKrSq :
      ((4 * K) * r) ^ 2 ≤ n ^ 2 := by
    calc
      ((4 * K) * r) ^ 2 =
          (4 * K) ^ 2 * r ^ 2 := by ring
      _ ≤ (4 * K) ^ 2 * x :=
        Nat.mul_le_mul_left ((4 * K) ^ 2) hrSq
      _ = (D * q) * n := by
        simp [D, K, x,
          theorem6SqrtPolynomialCoefficient]
        ring
      _ ≤ n * n :=
        Nat.mul_le_mul_right n hpoly
      _ = n ^ 2 := by ring
  have hKr : (4 * K) * r ≤ n := by
    exact
      (Nat.pow_le_pow_iff_left
        (by norm_num : (2 : ℕ) ≠ 0)).1 hKrSq
  have hroot :
      2 * (K * (r + 1)) ≤ n := by
    have hradius : r + 1 ≤ 2 * r := by omega
    calc
      2 * (K * (r + 1)) ≤
          2 * (K * (2 * r)) :=
        Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left K hradius)
      _ = (4 * K) * r := by ring
      _ ≤ n := hKr
  have hconstantLog :
      theorem6GuardConstant ≤
        Nat.log 2 n := by
    exact
      (by
        simp [theorem6ThresholdExponent] :
          theorem6GuardConstant ≤
            theorem6ThresholdExponent γ).trans hlog
  have hlogSelf :
      Nat.log 2 n ≤ n := by
    calc
      Nat.log 2 n ≤ 2 ^ Nat.log 2 n :=
        (Nat.log 2 n).lt_two_pow_self.le
      _ ≤ n := Nat.pow_log_le_self 2 hnPos.ne'
  have hconstant :
      2 * (theorem6CStarSq * 1_020) ≤ n := by
    simpa [theorem6GuardConstant] using
      hconstantLog.trans hlogSelf
  have hroot' :
      2 *
          (theorem6CStarSq *
            (4_179_180 * (8 * (r + 1)))) ≤
        n := by
    calc
      2 *
          (theorem6CStarSq *
            (4_179_180 * (8 * (r + 1)))) =
          2 * (K * (r + 1)) := by
        simp [K]
        ring
      _ ≤ n := hroot
  change
    theorem6CStarSq *
        (4_179_180 * (8 * (r + 1)) + 1_020) ≤
      n
  calc
    theorem6CStarSq *
          (4_179_180 * (8 * (r + 1)) + 1_020) =
        theorem6CStarSq *
            (4_179_180 * (8 * (r + 1))) +
          theorem6CStarSq * 1_020 := by
      rw [Nat.mul_add]
    _ ≤ n :=
      add_le_of_two_mul_le hroot' hconstant

end

end Tri

#print axioms Tri.theorem6PowSix_le_twoPow
#print axioms
  Tri.theorem6Polynomial_le_population
#print axioms Tri.theorem6Threshold_log
#print axioms Tri.theorem6Threshold_qLarge
#print axioms Tri.theorem6Threshold_size
#print axioms Tri.theorem6Threshold_cubeGuard
#print axioms Tri.theorem6Threshold_sqrtGuard
