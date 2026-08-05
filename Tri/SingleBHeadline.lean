/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBAssembly
import Tri.BudgetArith
import Tri.Theorem2
import Tri.HeavyBBand
import Tri.Phase2AdditiveBudget

/-!
# Single-B headline support

This file collects the headline-facing bookkeeping for the Single-B clause.
The probabilistic pre-final power budget is intentionally kept separate from
the already-closed final co-level block; the lemmas below are the deterministic
pieces needed by the capstone.
-/

namespace Tri

open scoped ENNReal

/-! ## Scalar utilities -/

/-- A derivative-free lower-tail logarithmic contraction bound. -/
theorem log_one_sub_le_neg_add_sq_half
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.log (1 - x) ≤ -(x + x ^ 2 / 2) := by
  have hxlt : x < 1 := by nlinarith
  have hpos : 0 < 1 - x := by linarith
  let y : ℝ := x / (1 - x)
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    positivity
  have hlog := Real.le_log_one_add_of_nonneg hy0
  have hyid : 1 + y = (1 - x)⁻¹ := by
    dsimp only [y]
    field_simp [hpos.ne']
    ring
  have hlogid : Real.log (1 + y) = -Real.log (1 - x) := by
    rw [hyid, Real.log_inv]
  have hquad : x + x ^ 2 / 2 ≤ 2 * y / (y + 2) := by
    dsimp only [y]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < x / (1 - x) + 2)]
    field_simp [hpos.ne']
    nlinarith [sq_nonneg x, sq_nonneg (x - 1)]
  nlinarith

/-- Quadratic exponential decay for a Bernoulli half-clock base. -/
theorem one_sub_pow_le_exp_quadratic
    (x : ℝ) (T : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (1 - x) ^ T ≤
      Real.exp (-((x + x ^ 2 / 2) * (T : ℝ))) := by
  have hxlt : x < 1 := by nlinarith
  have hpos : 0 < 1 - x := by linarith
  rw [← Real.exp_log (pow_pos hpos T), Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hlog := log_one_sub_le_neg_add_sq_half hx0 hx1
  have hT0 : 0 ≤ (T : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hT0
  nlinarith

/-- Convert the raw `w = 1/2` lower-tail clock term using a real lower bound
`x ≤ pp/2`, retaining the second-order `log(1-x)` gain. -/
theorem halfClock_div_le_ofReal_exp_quadratic
    (pp : ℝ≥0∞) (hpp1 : pp ≤ 1) (x : ℝ) (T K : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hxpp : ENNReal.ofReal x ≤ pp * ((1 : ℝ≥0∞) / 2)) :
    ((1 - pp) + pp * ((1 : ℝ≥0∞) / 2)) ^ T /
        ((1 : ℝ≥0∞) / 2) ^ K ≤
      ENNReal.ofReal
        (Real.exp
          (-((x + x ^ 2 / 2) * (T : ℝ)) +
            (K : ℝ) * Real.log 2)) := by
  let half : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  let xe : ℝ≥0∞ := ENNReal.ofReal x
  have hhalfCancel : (2 : ℝ≥0∞) * half = 1 := by
    dsimp only [half]
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hhalfAdd : half + half = 1 := by
    calc
      half + half = 2 * half := by ring
      _ = 1 := hhalfCancel
  have hxx : pp * half + pp * half = pp := by
    calc
      pp * half + pp * half = pp * (half + half) := by ring
      _ = pp := by rw [hhalfAdd, mul_one]
  have hppsum : (1 - pp) + pp = 1 := by
    exact tsub_add_cancel_of_le hpp1
  have hphiSum :
      ((1 - pp) + pp * half) + xe ≤ 1 := by
    calc
      ((1 - pp) + pp * half) + xe
          ≤ ((1 - pp) + pp * half) + pp * half := by
            simpa [xe, half, one_div, add_comm, add_left_comm, add_assoc] using
              add_le_add_left hxpp ((1 - pp) + pp * half)
      _ = (1 - pp) + (pp * half + pp * half) := by ring
      _ = (1 - pp) + pp := by rw [hxx]
      _ = 1 := hppsum
  have hxTop : xe ≠ ⊤ := by
    dsimp only [xe]
    exact ENNReal.ofReal_ne_top
  have hphiSub :
      (1 - pp) + pp * half ≤ 1 - xe :=
    ENNReal.le_sub_of_add_le_right hxTop hphiSum
  have hsub : 1 - xe = ENNReal.ofReal (1 - x) := by
    dsimp only [xe]
    rw [ENNReal.ofReal_sub 1 hx0, ENNReal.ofReal_one]
  have hnum :
      ((1 - pp) + pp * half) ^ T ≤
        ENNReal.ofReal ((1 - x) ^ T) := by
    calc
      ((1 - pp) + pp * half) ^ T ≤ (1 - xe) ^ T :=
        pow_le_pow_left' hphiSub T
      _ = ENNReal.ofReal ((1 - x) ^ T) := by
        rw [hsub, ENNReal.ofReal_pow (by linarith : 0 ≤ 1 - x)]
  have hnumExp :
      ((1 - pp) + pp * half) ^ T ≤
        ENNReal.ofReal
          (Real.exp (-((x + x ^ 2 / 2) * (T : ℝ)))) :=
    hnum.trans (ENNReal.ofReal_le_ofReal
      (one_sub_pow_le_exp_quadratic x T hx0 hx1))
  have hdiv :
      ((1 - pp) + pp * half) ^ T / half ^ K ≤
        ENNReal.ofReal
          (Real.exp (-((x + x ^ 2 / 2) * (T : ℝ)))) / half ^ K :=
    ENNReal.div_le_div_right hnumExp _
  have hhalf :
      half = ENNReal.ofReal (1 / 2 : ℝ) := by
    dsimp only [half]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hquot :
      ENNReal.ofReal
          (Real.exp (-((x + x ^ 2 / 2) * (T : ℝ)))) / half ^ K =
        ENNReal.ofReal
          (Real.exp
            (-((x + x ^ 2 / 2) * (T : ℝ)) +
              (K : ℝ) * Real.log 2)) := by
    rw [hhalf, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← ENNReal.ofReal_div_of_pos
      (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ K)]
    congr 2
    have hhalfReal :
        (1 / 2 : ℝ) ^ K =
          Real.exp (-(K : ℝ) * Real.log 2) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ K),
        Real.log_pow]
      have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hlogHalf]
      congr 1
      ring
    rw [hhalfReal, ← Real.exp_sub]
    congr 1
    ring
  exact hdiv.trans hquot.le

/-- The elementary lower Taylor bound for `log(1+x)` on `[0,1]`, derived from
the already-used lower-tail bound for `log(1-x)`. -/
theorem log_one_add_ge_sub_sq_half
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  let y : ℝ := x / (1 + x)
  have hpos : 0 < 1 + x := by linarith
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    positivity
  have hy1 : y ≤ 1 / 2 := by
    dsimp only [y]
    rw [div_le_iff₀ hpos]
    nlinarith
  have hlog := log_one_sub_le_neg_add_sq_half hy0 hy1
  have honeSub : 1 - y = (1 + x)⁻¹ := by
    dsimp only [y]
    field_simp [hpos.ne']
    ring
  have hlogid : Real.log (1 - y) = -Real.log (1 + x) := by
    rw [honeSub, Real.log_inv]
  have hquad : x - x ^ 2 / 2 ≤ y + y ^ 2 / 2 := by
    dsimp only [y]
    field_simp [hpos.ne']
    nlinarith [sq_nonneg x, mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  rw [hlogid] at hlog
  nlinarith

/-- Two positive terms from the `log(1+x)` series in the
`x/(x+2)` variable. -/
theorem log_one_add_ge_two_terms
    {x : ℝ} (hx0 : 0 ≤ x) :
    2 * (x / (x + 2)) +
        2 * (1 / 3 : ℝ) * (x / (x + 2)) ^ 3 ≤
      Real.log (1 + x) := by
  have hs := sum_le_hasSum (Finset.range 2)
    (fun n _ => by positivity)
    (Real.hasSum_log_one_add hx0)
  have hs' :
      2 * (x / (x + 2)) +
          2 * ((2 + 1 : ℝ)⁻¹) * (x / (x + 2)) ^ 3 ≤
        Real.log (1 + x) := by
    simpa [Finset.sum_range_succ, pow_one] using hs
  norm_num at hs'
  simpa [one_div, div_eq_mul_inv, mul_assoc] using hs'

theorem log_five_four_ge_223 :
    (223 : ℝ) / 1000 ≤ Real.log ((5 : ℝ) / 4) := by
  have h := log_one_add_ge_two_terms
    (x := (1 : ℝ) / 4) (by norm_num)
  norm_num at h ⊢
  linarith

theorem log_2499_2000_ge_2227 :
    (2227 : ℝ) / 10000 ≤ Real.log ((2499 : ℝ) / 2000) := by
  have h := log_one_add_ge_two_terms
    (x := (499 : ℝ) / 2000) (by norm_num)
  norm_num at h ⊢
  linarith

theorem singleLateDirEta_ge_2499_2000
    (n Q : ℕ) (hnLarge : 2998 ≤ n) (hQ : 8 * Q ≤ n + 4) :
    ENNReal.ofReal ((2499 : ℝ) / 2000) ≤ singleLateDirEta n Q := by
  unfold singleLateDirEta singleLateDirP
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (by finiteness)).mp
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2499 / 2000)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hden :
      (0 : ℝ) < ((n + 4 * (2 * Q) : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hden]
  push_cast
  have hQR : (8 : ℝ) * Q ≤ n + 4 := by exact_mod_cast hQ
  have hnR : (2998 : ℝ) ≤ n := by exact_mod_cast hnLarge
  nlinarith

theorem singleLate_direction_stream_aux
    (L target M : ℕ) (η : ℝ≥0∞) (S : ℝ)
    (hηT : η ≠ ⊤)
    (hηLower : ENNReal.ofReal ((2499 : ℝ) / 2000) ≤ η)
    (hL : L ≤ target)
    (hexp :
      ((target - L : ℕ) : ℝ) * (0.6931471808 : ℝ) -
          (M : ℝ) * ((2227 : ℝ) / 10000) ≤ -S) :
    singleLateDirW ^ L /
        (singleLateDirW ^ target * η ^ M) ≤
      ENNReal.ofReal (Real.exp (-S)) := by
  have hηReal :
      (2499 : ℝ) / 2000 ≤ η.toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hηT).mpr
      hηLower
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2499 / 2000)] at h
    exact h
  have hηpos : 0 < η.toReal := by nlinarith
  have hη0 : η ≠ 0 := by
    intro hz
    rw [hz] at hηReal
    simp at hηReal
    nlinarith
  have hw0 : singleLateDirW ≠ 0 := by
    unfold singleLateDirW
    norm_num
  have hwT : singleLateDirW ≠ ⊤ := by
    unfold singleLateDirW
    norm_num
  have hden0 : singleLateDirW ^ target * η ^ M ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hη0)
  have htermT :
      singleLateDirW ^ L /
          (singleLateDirW ^ target * η ^ M) ≠ ⊤ :=
    ENNReal.div_ne_top (by finiteness) hden0
  apply (ENNReal.toReal_le_toReal htermT ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow, ENNReal.toReal_pow]
  have hW : singleLateDirW.toReal = (1 : ℝ) / 2 := by
    unfold singleLateDirW
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [hW]
  have hwpos : (0 : ℝ) < 1 / 2 := by norm_num
  have hdenpos : 0 < (1 / 2 : ℝ) ^ target * η.toReal ^ M := by
    positivity
  have htermpos :
      0 < (1 / 2 : ℝ) ^ L /
          ((1 / 2 : ℝ) ^ target * η.toReal ^ M) := by
    positivity
  have hlogw : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hlogeq :
      Real.log
          ((1 / 2 : ℝ) ^ L /
            ((1 / 2 : ℝ) ^ target * η.toReal ^ M)) =
        ((target - L : ℕ) : ℝ) * Real.log 2 -
          (M : ℝ) * Real.log η.toReal := by
    rw [Real.log_div (pow_ne_zero _ (ne_of_gt hwpos))
      (ne_of_gt hdenpos),
      Real.log_mul (pow_ne_zero _ (ne_of_gt hwpos))
        (pow_ne_zero _ (ne_of_gt hηpos)),
      Real.log_pow, Real.log_pow, hlogw]
    rw [Real.log_pow]
    rw [Nat.cast_sub hL]
    ring_nf
  have hlogη :
      (2227 : ℝ) / 10000 ≤ Real.log η.toReal := by
    have hbase := log_2499_2000_ge_2227
    have hmono : Real.log ((2499 : ℝ) / 2000) ≤ Real.log η.toReal :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2499 / 2000) hηReal
    linarith
  have hlog2 : Real.log 2 ≤ (0.6931471808 : ℝ) :=
    Real.log_two_lt_d9.le
  have hlogBound :
      Real.log
          ((1 / 2 : ℝ) ^ L /
            ((1 / 2 : ℝ) ^ target * η.toReal ^ M)) ≤ -S := by
    rw [hlogeq]
    have hleft :
        ((target - L : ℕ) : ℝ) * Real.log 2 ≤
          ((target - L : ℕ) : ℝ) * (0.6931471808 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
    have hright :
        (M : ℝ) * ((2227 : ℝ) / 10000) ≤
          (M : ℝ) * Real.log η.toReal := by
      exact mul_le_mul_of_nonneg_left hlogη (by positivity)
    nlinarith
  calc
    (1 / 2 : ℝ) ^ L /
          ((1 / 2 : ℝ) ^ target * η.toReal ^ M)
        = Real.exp (Real.log
          ((1 / 2 : ℝ) ^ L /
            ((1 / 2 : ℝ) ^ target * η.toReal ^ M))) := by
          rw [Real.exp_log htermpos]
    _ ≤ Real.exp (-S) :=
      Real.exp_le_exp.mpr hlogBound

theorem singleLateConst_productive_x_le
    (n d R : ℕ) (hn : 2 ≤ n) (hR : 0 < R)
    (hd : 7 * (n - 1) ≤ 10 * d) :
    ENNReal.ofReal ((7 : ℝ) * (R : ℝ) / (2 * (n : ℝ))) ≤
      singleBandProductivity n d (singleLateConstCoFloor R) *
        ((1 : ℝ≥0∞) / 2) := by
  have hleftT :
      ENNReal.ofReal ((7 : ℝ) * (R : ℝ) / (2 * (n : ℝ))) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hrightT :
      singleBandProductivity n d (singleLateConstCoFloor R) *
          ((1 : ℝ≥0∞) / 2) ≠ ⊤ := by
    unfold singleBandProductivity
    apply ENNReal.mul_ne_top
    · apply ENNReal.div_ne_top
      · exact ENNReal.natCast_ne_top _
      · simp only [ne_eq, Nat.cast_eq_zero]
        exact (Nat.choose_pos hn).ne'
    · norm_num
  apply (ENNReal.toReal_le_toReal hleftT hrightT).mp
  rw [ENNReal.toReal_ofReal (by positivity :
    (0 : ℝ) ≤ (7 : ℝ) * (R : ℝ) / (2 * (n : ℝ)))]
  unfold singleBandProductivity singleLateConstCoFloor
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have hchoose : 2 * Nat.choose n 2 = n * (n - 1) := by
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hchooseR :
      (2 : ℝ) * (Nat.choose n 2 : ℝ) =
        (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hchoose
  have hdR : (7 : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ 10 * (d : ℝ) := by
    exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1R : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  have hRposR : (0 : ℝ) < R := by exact_mod_cast hR
  have hchoosePos : (0 : ℝ) < Nat.choose n 2 := by
    exact_mod_cast Nat.choose_pos hn
  norm_num only [Nat.cast_mul]
  calc
    (7 : ℝ) * (R : ℝ) / (2 * (n : ℝ))
        ≤ (d : ℝ) * (5 * (R : ℝ)) /
            ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))
            (mul_pos hnR hn1R)]
          have hmul := mul_le_mul_of_nonneg_right hdR
            (mul_nonneg hRposR.le hnR.le)
          nlinarith
    _ = (d : ℝ) * (5 * (R : ℝ)) / (Nat.choose n 2 : ℝ) *
          (1 / 2) := by
      rw [← hchooseR]
      field_simp [hchoosePos.ne']

/-! ## Constant-base late scalar budgets -/

theorem singleLateConst_backslide_stream_le_exp (R : ℕ) :
    singleLateDirW ^ R ≤
      ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100))) := by
  unfold singleLateDirW
  simpa using
    ratio_pow_le_ofReal_exp 2 1 R ((R : ℝ) / 1100)
      (by norm_num) (by norm_num) (by
        norm_num
        have hR0 : (0 : ℝ) ≤ R := by positivity
        nlinarith)

theorem singleLateConst_creation_stream_le_exp
    (P R : ℕ) (hR : 16 ≤ R) (hP : P ≤ 68 * R + 1) :
    ENNReal.ofReal
        (Real.exp
          (-((R : ℝ) ^ 2 /
            (2 * (singleLateConstH P R : ℝ))))) ≤
      ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100))) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  have hHpos : 0 < singleLateConstH P R := by
    unfold singleLateConstH
    omega
  have hHupper : singleLateConstH P R ≤ 114 * R := by
    unfold singleLateConstH singleLateConstMhi
    omega
  have hRposR : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hHposR : (0 : ℝ) < singleLateConstH P R := by
    exact_mod_cast hHpos
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1100)
    (by positivity : (0 : ℝ) < 2 * (singleLateConstH P R : ℝ))]
  have hHupperR : (singleLateConstH P R : ℝ) ≤ 114 * (R : ℝ) := by
    exact_mod_cast hHupper
  nlinarith [sq_nonneg (R : ℝ)]

theorem singleLateConst_main_direction_stream_le_exp
    (n Qbase R Lentry Lexit : ℕ)
    (hnLarge : 2998 ≤ n) (hR : 1024 ≤ R)
    (hQdir : 8 * Qbase ≤ n + 4)
    (hL : Lentry ≤ Lexit + R)
    (hspan : Lexit + R - Lentry ≤ 2 * R + 32) :
    singleLateDirW ^ Lentry /
        (singleLateDirW ^ (Lexit + R) *
          singleLateDirEta n Qbase ^ singleLateConstM R) ≤
      ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100))) := by
  have hηT : singleLateDirEta n Qbase ≠ ⊤ := by
    unfold singleLateDirEta
    finiteness
  have hηLower :=
    singleLateDirEta_ge_2499_2000 n Qbase hnLarge hQdir
  have hspanR :
      ((Lexit + R - Lentry : ℕ) : ℝ) ≤ 2 * (R : ℝ) + 32 := by
    exact_mod_cast hspan
  have hRlargeR : (1024 : ℝ) ≤ R := by exact_mod_cast hR
  have hexp :
      ((Lexit + R - Lentry : ℕ) : ℝ) * (0.6931471808 : ℝ) -
          (singleLateConstM R : ℝ) * ((2227 : ℝ) / 10000) ≤
        -((R : ℝ) / 1100) := by
    unfold singleLateConstM
    norm_num only [Nat.cast_mul]
    nlinarith
  exact singleLate_direction_stream_aux Lentry (Lexit + R)
    (singleLateConstM R) (singleLateDirEta n Qbase)
    ((R : ℝ) / 1100) hηT hηLower hL hexp

theorem singleLateConst_high_direction_stream_le_exp
    (n Qbase R Lentry hiΛ : ℕ)
    (hnLarge : 2998 ≤ n) (hR : 1024 ≤ R)
    (hQdir : 8 * Qbase ≤ n + 4)
    (hL : Lentry ≤ hiΛ)
    (hspan : hiΛ - Lentry ≤ 7 * R + 32) :
    singleLateDirW ^ Lentry /
        (singleLateDirW ^ hiΛ *
          singleLateDirEta n Qbase ^ singleLateConstMhi R) ≤
      ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100))) := by
  have hηT : singleLateDirEta n Qbase ≠ ⊤ := by
    unfold singleLateDirEta
    finiteness
  have hηLower :=
    singleLateDirEta_ge_2499_2000 n Qbase hnLarge hQdir
  have hspanR :
      ((hiΛ - Lentry : ℕ) : ℝ) ≤ 7 * (R : ℝ) + 32 := by
    exact_mod_cast hspan
  have hRlargeR : (1024 : ℝ) ≤ R := by exact_mod_cast hR
  have hexp :
      ((hiΛ - Lentry : ℕ) : ℝ) * (0.6931471808 : ℝ) -
          (singleLateConstMhi R : ℝ) * ((2227 : ℝ) / 10000) ≤
        -((R : ℝ) / 1100) := by
    unfold singleLateConstMhi
    norm_num only [Nat.cast_mul]
    nlinarith
  exact singleLate_direction_stream_aux Lentry hiΛ
    (singleLateConstMhi R) (singleLateDirEta n Qbase)
    ((R : ℝ) / 1100) hηT hηLower hL hexp

theorem singleLateConst_productive_stream_le_exp
    (n P R d : ℕ) (hn : 2 ≤ n) (hR : 16 ≤ R)
    (hP : P ≤ 68 * R + 1)
    (hd : 7 * (n - 1) ≤ 10 * d)
    (hRn : 7 * R ≤ n)
    (hprodRoom : d + 2 * singleLateConstCoFloor R ≤ n) :
    ((1 - singleBandProductivity n d (singleLateConstCoFloor R)) +
        singleBandProductivity n d (singleLateConstCoFloor R) *
          ((1 : ℝ≥0∞) / 2)) ^ singleLateConstSubHorizon n /
      ((1 : ℝ≥0∞) / 2) ^ singleLateConstK P R ≤
      ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100))) := by
  let x : ℝ := (7 : ℝ) * (R : ℝ) / (2 * (n : ℝ))
  have hpp1 :
      singleBandProductivity n d (singleLateConstCoFloor R) ≤ 1 :=
    singleBandProductivity_le_one_of_sum n hn d
      (singleLateConstCoFloor R) hprodRoom
  have hxpp := singleLateConst_productive_x_le n d R hn
    (by omega : 0 < R) hd
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hx1 : x ≤ 1 / 2 := by
    dsimp only [x]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
    have hRnR : (7 : ℝ) * (R : ℝ) ≤ n := by
      exact_mod_cast hRn
    nlinarith
  have hraw := halfClock_div_le_ofReal_exp_quadratic
    (singleBandProductivity n d (singleLateConstCoFloor R))
    hpp1 x (singleLateConstSubHorizon n) (singleLateConstK P R)
    hx0 hx1 hxpp
  have hexp :
      -((x + x ^ 2 / 2) * (singleLateConstSubHorizon n : ℝ)) +
          (singleLateConstK P R : ℝ) * Real.log 2 ≤
        -((R : ℝ) / 1100) := by
    have hKnat : singleLateConstK P R ≤ 121 * R := by
      unfold singleLateConstK singleLateConstH singleLateConstM
        singleLateConstMhi
      omega
    have hKupper :
        (singleLateConstK P R : ℝ) ≤ 121 * (R : ℝ) := by
      exact_mod_cast hKnat
    have hlog2 : Real.log 2 ≤ (0.6931471808 : ℝ) :=
      Real.log_two_lt_d9.le
    have hlog2Nonneg : 0 ≤ Real.log 2 :=
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hKlog :
        (singleLateConstK P R : ℝ) * Real.log 2 ≤
          (121 * (R : ℝ)) * (0.6931471808 : ℝ) := by
      calc
        (singleLateConstK P R : ℝ) * Real.log 2
            ≤ (121 * (R : ℝ)) * Real.log 2 := by
              exact mul_le_mul_of_nonneg_right hKupper hlog2Nonneg
        _ ≤ (121 * (R : ℝ)) * (0.6931471808 : ℝ) := by
              exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
    have hnRpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hxT :
        x * (singleLateConstSubHorizon n : ℝ) = 84 * (R : ℝ) := by
      dsimp only [x, singleLateConstSubHorizon]
      norm_num only [Nat.cast_mul]
      field_simp [hnRpos.ne']
      ring
    have hquadT :
        x * (singleLateConstSubHorizon n : ℝ) ≤
          (x + x ^ 2 / 2) * (singleLateConstSubHorizon n : ℝ) := by
      have hT0 : 0 ≤ (singleLateConstSubHorizon n : ℝ) := by positivity
      have hxextra : 0 ≤ x ^ 2 / 2 := by positivity
      nlinarith [mul_nonneg hxextra hT0]
    have hRlargeR : (16 : ℝ) ≤ R := by exact_mod_cast hR
    calc
      -((x + x ^ 2 / 2) * (singleLateConstSubHorizon n : ℝ)) +
          (singleLateConstK P R : ℝ) * Real.log 2
          ≤ -(x * (singleLateConstSubHorizon n : ℝ)) +
              (singleLateConstK P R : ℝ) * Real.log 2 := by
            nlinarith
      _ = -(84 * (R : ℝ)) +
              (singleLateConstK P R : ℝ) * Real.log 2 := by
            rw [hxT]
      _ ≤ -(84 * (R : ℝ)) +
              (121 * (R : ℝ)) * (0.6931471808 : ℝ) := by
            nlinarith
      _ ≤ -((R : ℝ) / 1100) := by
            nlinarith
  exact hraw.trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr hexp))

theorem singleLateConst_return_exponent_le
    (n Q R : ℕ) (hnLarge : 385 ≤ n) (hR : 0 < R)
    (hBupper : Q + 1 ≤ 66 * R) :
    let T : ℕ := singleLateConstSubHorizon n
    let S : ℕ := singleLateConstSret R
    let B : ℕ := Q + 1
    let e : ℝ := ((S + 1 : ℕ) : ℝ) / (96 * (B : ℝ))
    (T : ℝ) * (e ^ 2 * (B : ℝ) / ((n - 1 : ℕ) : ℝ)) -
          ((S + 1 : ℕ) : ℝ) * e / 2 ≤ -((R : ℝ) / 1100) := by
  intro T S B e
  have hn1R : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  have hBposR : (0 : ℝ) < (B : ℝ) := by positivity
  have hratio :
      (n : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ (385 : ℝ) / 384 := by
    rw [div_le_iff₀ hn1R]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
    have hnR : (385 : ℝ) ≤ n := by exact_mod_cast hnLarge
    linarith
  have hBupperR : (B : ℝ) ≤ 66 * (R : ℝ) := by
    dsimp only [B]
    exact_mod_cast hBupper
  have hRposR : (0 : ℝ) < R := by exact_mod_cast hR
  have hrewrite :
      (T : ℝ) * (e ^ 2 * (B : ℝ) / ((n - 1 : ℕ) : ℝ)) -
          ((S + 1 : ℕ) : ℝ) * e / 2 =
        ((((S + 1 : ℕ) : ℝ) ^ 2) / (B : ℝ)) *
          (((n : ℝ) / ((n - 1 : ℕ) : ℝ)) / 384 - (1 : ℝ) / 192) := by
    have hdenpos : (0 : ℝ) < 96 * (B : ℝ) := by positivity
    dsimp only [T, S, B, e, singleLateConstSubHorizon,
      singleLateConstSret]
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hn1R.ne', hBposR.ne', hdenpos.ne']
    ring
  have hcoeff :
      (((n : ℝ) / ((n - 1 : ℕ) : ℝ)) / 384 - (1 : ℝ) / 192) ≤
        -((383 : ℝ) / 147456) := by
    nlinarith
  have hleftNonneg :
      0 ≤ (((S + 1 : ℕ) : ℝ) ^ 2) / (B : ℝ) := by positivity
  have hupper1 :
      ((((S + 1 : ℕ) : ℝ) ^ 2) / (B : ℝ)) *
          (((n : ℝ) / ((n - 1 : ℕ) : ℝ)) / 384 - (1 : ℝ) / 192) ≤
        -((383 : ℝ) / 147456) *
          ((((S + 1 : ℕ) : ℝ) ^ 2) / (B : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hcoeff hleftNonneg]
  have hupper2 :
      -((383 : ℝ) / 147456) *
          ((((S + 1 : ℕ) : ℝ) ^ 2) / (B : ℝ)) ≤
        -((R : ℝ) / 1100) := by
    dsimp only [S, B, singleLateConstSret] at *
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at *
    rw [neg_mul, neg_le_neg_iff]
    field_simp [hBposR.ne']
    ring_nf
    nlinarith [sq_nonneg ((R : ℝ) - 1), sq_nonneg (R : ℝ)]
  rw [hrewrite]
  exact hupper1.trans hupper2

theorem singleLateConst_return_stream_le_exp
    (n Q R : ℕ) (hn : 2 ≤ n) (hnLarge : 385 ≤ n)
    (hR : 0 < R) (hBupper : Q + 1 ≤ 66 * R)
    (hRetRoom : singleLateConstSret R + 1 ≤ 96 * (Q + 1)) :
    (1 + singleLateConstRetEps Q R ^ 2 *
          (((Q + 1 : ℕ) : ℝ≥0∞) /
            ((n - 1 : ℕ) : ℝ≥0∞))) ^ singleLateConstSubHorizon n /
        (1 + singleLateConstRetEps Q R) ^ (singleLateConstSret R + 1) ≤
      ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100))) := by
  let T := singleLateConstSubHorizon n
  let S := singleLateConstSret R
  let B := Q + 1
  let e : ℝ := ((S + 1 : ℕ) : ℝ) / (96 * (B : ℝ))
  have he0 : 0 ≤ e := by
    dsimp only [e]
    positivity
  have he1 : e ≤ 1 := by
    dsimp only [e, S, B]
    have hden : (0 : ℝ) < 96 * ((Q + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_one hden]
    exact_mod_cast hRetRoom
  have hraw := singleCoReturn_exp n T S B hn e he0 he1
  have hexp :=
    singleLateConst_return_exponent_le n Q R hnLarge hR hBupper
  have hraw' :
      (1 + singleLateConstRetEps Q R ^ 2 *
            (((Q + 1 : ℕ) : ℝ≥0∞) /
              ((n - 1 : ℕ) : ℝ≥0∞))) ^ singleLateConstSubHorizon n /
          (1 + singleLateConstRetEps Q R) ^ (singleLateConstSret R + 1) ≤
        ENNReal.ofReal
          (Real.exp ((T : ℝ) *
            (e ^ 2 * (B : ℝ) / ((n - 1 : ℕ) : ℝ)) -
            ((S + 1 : ℕ) : ℝ) * e / 2)) := by
    simpa [T, S, B, e, singleLateConstRetEps] using hraw
  exact hraw'.trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (by simpa [T, S, B, e] using hexp)))

theorem singleLateConstSubRungError_le_exp
    (n Qbase P Q R Lentry Lexit hiΛ d : ℕ)
    (hn : 2 ≤ n) (hnLarge : 2998 ≤ n) (hR : 1024 ≤ R)
    (hQdir : 8 * Qbase ≤ n + 4)
    (hP : P ≤ 68 * R + 1)
    (hMainL : Lentry ≤ Lexit + R)
    (hMainSpan : Lexit + R - Lentry ≤ 2 * R + 32)
    (hHiL : Lentry ≤ hiΛ)
    (hHiSpan : hiΛ - Lentry ≤ 7 * R + 32)
    (hd : 7 * (n - 1) ≤ 10 * d)
    (hRn : 7 * R ≤ n)
    (hprodRoom : d + 2 * singleLateConstCoFloor R ≤ n)
    (hBupper : Q + 1 ≤ 66 * R)
    (hRetRoom : singleLateConstSret R + 1 ≤ 96 * (Q + 1)) :
    singleLateConstSubRungError n Qbase P Q R Lentry Lexit hiΛ d ≤
      8 * ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100))) := by
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100)))
  have hback : singleLateDirW ^ R ≤ e := by
    dsimp only [e]
    exact singleLateConst_backslide_stream_le_exp R
  have hmain :
      singleLateDirW ^ Lentry /
          (singleLateDirW ^ (Lexit + R) *
            singleLateDirEta n Qbase ^ singleLateConstM R) ≤ e := by
    dsimp only [e]
    exact singleLateConst_main_direction_stream_le_exp n Qbase R
      Lentry Lexit hnLarge hR hQdir hMainL hMainSpan
  have hprod :
      ((1 - singleBandProductivity n d (singleLateConstCoFloor R)) +
          singleBandProductivity n d (singleLateConstCoFloor R) *
            ((1 : ℝ≥0∞) / 2)) ^ singleLateConstSubHorizon n /
        ((1 : ℝ≥0∞) / 2) ^ singleLateConstK P R ≤ e := by
    dsimp only [e]
    exact singleLateConst_productive_stream_le_exp n P R d hn (by omega) hP
      hd hRn hprodRoom
  have hcreate :
      ENNReal.ofReal
          (Real.exp (-((R : ℝ) ^ 2 /
            (2 * (singleLateConstH P R : ℝ))))) ≤ e := by
    dsimp only [e]
    exact singleLateConst_creation_stream_le_exp P R (by omega) hP
  have hhigh :
      singleLateDirW ^ Lentry /
          (singleLateDirW ^ hiΛ *
            singleLateDirEta n Qbase ^ singleLateConstMhi R) ≤ e := by
    dsimp only [e]
    exact singleLateConst_high_direction_stream_le_exp n Qbase R
      Lentry hiΛ hnLarge hR hQdir hHiL hHiSpan
  have hret :
      (1 + singleLateConstRetEps Q R ^ 2 *
            (((Q + 1 : ℕ) : ℝ≥0∞) /
              ((n - 1 : ℕ) : ℝ≥0∞))) ^ singleLateConstSubHorizon n /
          (1 + singleLateConstRetEps Q R) ^ (singleLateConstSret R + 1) ≤ e := by
    dsimp only [e]
    exact singleLateConst_return_stream_le_exp n Q R hn
      (by omega : 385 ≤ n) (by omega : 0 < R) hBupper hRetRoom
  dsimp [singleLateConstSubRungError, singleLateRungError,
    singleLateResolvedClockError, singleLevelPhaseStructuralError, e]
  calc
    (((((singleLateDirW ^ R +
          singleLateDirW ^ Lentry /
            (singleLateDirW ^ (Lexit + R) *
              singleLateDirEta n Qbase ^ singleLateConstM R)) +
          (((1 - singleBandProductivity n d (singleLateConstCoFloor R)) +
              singleBandProductivity n d (singleLateConstCoFloor R) *
                ((1 : ℝ≥0∞) / 2)) ^ singleLateConstSubHorizon n /
              ((1 : ℝ≥0∞) / 2) ^ singleLateConstK P R +
            ENNReal.ofReal
              (Real.exp (-((R : ℝ) ^ 2 /
                (2 * (singleLateConstH P R : ℝ))))))) +
        ENNReal.ofReal
          (Real.exp (-((R : ℝ) ^ 2 /
            (2 * (singleLateConstH P R : ℝ)))))) +
        singleLateDirW ^ Lentry /
          (singleLateDirW ^ hiΛ *
            singleLateDirEta n Qbase ^ singleLateConstMhi R)) +
        ENNReal.ofReal
          (Real.exp (-((R : ℝ) ^ 2 /
            (2 * (singleLateConstH P R : ℝ)))))) +
        (1 + singleLateConstRetEps Q R ^ 2 *
            (((Q + 1 : ℕ) : ℝ≥0∞) /
              ((n - 1 : ℕ) : ℝ≥0∞))) ^ singleLateConstSubHorizon n /
          (1 + singleLateConstRetEps Q R) ^ (singleLateConstSret R + 1)
        ≤ ((((((e + e) + (e + e)) + e) + e) + e) + e) := by
          exact add_le_add
            (add_le_add
              (add_le_add
                (add_le_add
                  (add_le_add (add_le_add hback hmain)
                    (add_le_add hprod hcreate))
                  hcreate)
                hhigh)
              hcreate)
            hret
    _ = 8 * e := by ring

theorem singleLateConstDyadicR_lower
    {Q : ℕ} (hQ : 32768 ≤ Q) :
    1024 ≤ singleLateConstDyadicR Q := by
  unfold singleLateConstDyadicR
  have hdiv := Nat.div_add_mod Q 32
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 32)
  omega

theorem singleLateConstDyadicR_fit_lower (Q : ℕ) :
    32 * singleLateConstDyadicR Q ≤ Q := by
  unfold singleLateConstDyadicR
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self Q 32

theorem singleLateConstDyadicR_q_upper34
    {Q : ℕ} (hQ : 512 ≤ Q) :
    Q ≤ 34 * singleLateConstDyadicR Q := by
  unfold singleLateConstDyadicR
  have hdiv := Nat.div_add_mod Q 32
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 32)
  omega

theorem singleLateConstDyadicR_q_upper32_add31 (Q : ℕ) :
    Q ≤ 32 * singleLateConstDyadicR Q + 31 := by
  unfold singleLateConstDyadicR
  have hdiv := Nat.div_add_mod Q 32
  have hmod := Nat.mod_lt Q (by norm_num : 0 < 32)
  omega

theorem singleLateConstDyadicFlexError_le_exp
    (n P Q : ℕ) (hn : 2 ≤ n) (hnLarge : 2998 ≤ n)
    (hPlo : 2 * Q ≤ P) (hPhi : P ≤ 2 * Q + 1)
    (hPquarter : 4 * P ≤ n)
    (hQlarge : 32768 ≤ Q) (hQsmall : 8 * Q ≤ n) :
    singleLateConstDyadicFlexError n P Q ≤
      8 * ENNReal.ofReal
        (Real.exp (-((singleLateConstDyadicR Q : ℝ) / 1100))) := by
  let R := singleLateConstDyadicR Q
  let E := singleLateConstDyadicFlexExit Q
  let Qbase := singleLateConstDyadicFlexQbase P
  let Lentry := singleLateConstDyadicFlexLentry n P
  let Lexit := singleLateConstDyadicFlexLexit n Q
  let Hi := singleLateConstDyadicFlexHi n Q
  let d := singleLateConstDyadicFlexD n P Q
  have hQ512 : 512 ≤ Q := hQlarge.trans' (by norm_num)
  have hRlarge : 1024 ≤ R := by
    dsimp only [R]
    exact singleLateConstDyadicR_lower hQlarge
  have hRpos : 0 < R := by omega
  have hRfit : 32 * R ≤ Q := by
    dsimp only [R]
    exact singleLateConstDyadicR_fit_lower Q
  have hQupper34 : Q ≤ 34 * R := by
    dsimp only [R]
    exact singleLateConstDyadicR_q_upper34 hQ512
  have hQupper32 : Q ≤ 32 * R + 31 := by
    dsimp only [R]
    exact singleLateConstDyadicR_q_upper32_add31 Q
  have hQbaseDiv := Nat.div_add_mod (P + 1) 2
  have hQbaseMod := Nat.mod_lt (P + 1) (by norm_num : 0 < 2)
  have hQdir : 8 * Qbase ≤ n + 4 := by
    dsimp only [Qbase, singleLateConstDyadicFlexQbase] at hQbaseDiv hQbaseMod ⊢
    omega
  have hPbound : P ≤ 68 * R + 1 := by omega
  have hMainL : Lentry ≤ Lexit + R := by
    dsimp only [Lentry, Lexit, E, R, singleLateConstDyadicFlexLentry,
      singleLateConstDyadicFlexLexit, singleLateConstDyadicFlexExit]
    omega
  have hMainSpan : Lexit + R - Lentry ≤ 2 * R + 32 := by
    dsimp only [Lentry, Lexit, E, R, singleLateConstDyadicFlexLentry,
      singleLateConstDyadicFlexLexit, singleLateConstDyadicFlexExit]
    omega
  have hHiL : Lentry ≤ Hi := by
    dsimp only [Lentry, Lexit, Hi, E, R, singleLateConstDyadicFlexLentry,
      singleLateConstDyadicFlexLexit, singleLateConstDyadicFlexHi,
      singleLateConstDyadicFlexExit]
    omega
  have hHiSpan : Hi - Lentry ≤ 7 * R + 32 := by
    dsimp only [Lentry, Lexit, Hi, E, R, singleLateConstDyadicFlexLentry,
      singleLateConstDyadicFlexLexit, singleLateConstDyadicFlexHi,
      singleLateConstDyadicFlexExit]
    omega
  have hd : 7 * (n - 1) ≤ 10 * d := by
    dsimp only [d, R, singleLateConstDyadicFlexD]
    omega
  have hRn : 7 * R ≤ n := by omega
  have hprodRoom : d + 2 * singleLateConstCoFloor R ≤ n := by
    dsimp only [d, singleLateConstCoFloor, R,
      singleLateConstDyadicFlexD]
    omega
  have hBupper : E + 1 ≤ 66 * R := by
    dsimp only [E, R, singleLateConstDyadicFlexExit]
    omega
  have hRetRoom :
      singleLateConstSret R + 1 ≤ 96 * (E + 1) := by
    dsimp only [E, singleLateConstSret, R,
      singleLateConstDyadicFlexExit]
    omega
  have h :=
    singleLateConstSubRungError_le_exp n Qbase P E R Lentry Lexit Hi d
      hn hnLarge hRlarge hQdir hPbound hMainL hMainSpan hHiL hHiSpan
      hd hRn hprodRoom hBupper hRetRoom
  simpa [singleLateConstDyadicFlexError, R, E, Qbase, Lentry, Lexit,
    Hi, d] using h

theorem singleLateConstStageError_le_exp
    (n Q : ℕ) (hn : 2 ≤ n) (hnLarge : 2998 ≤ n)
    (hQlarge : 32768 ≤ Q) (hQsmall : 8 * Q ≤ n) :
    singleLateConstStageError n Q (singleLateConstDyadicR Q)
        (singleLateConstCap32 Q (singleLateConstDyadicR Q))
        (singleLateConstLentry32 (singleLateConstDyadicL0 n Q)
          (singleLateConstDyadicR Q))
        (singleLateConstLexit32 (singleLateConstDyadicL0 n Q)
          (singleLateConstDyadicR Q))
        (singleLateConstHi32 (singleLateConstDyadicL0 n Q)
          (singleLateConstDyadicR Q))
        (singleLateConstD32 (singleLateConstDyadicD0 n Q)
          (singleLateConstDyadicR Q)) ≤
      256 * ENNReal.ofReal
        (Real.exp (-((singleLateConstDyadicR Q : ℝ) / 1100))) := by
  let R := singleLateConstDyadicR Q
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100)))
  have hQ512 : 512 ≤ Q := hQlarge.trans' (by norm_num)
  have hRlarge : 1024 ≤ R := by
    dsimp only [R]
    exact singleLateConstDyadicR_lower hQlarge
  have hRpos : 0 < R := by omega
  have hRfit : 32 * R ≤ Q := by
    dsimp only [R]
    exact singleLateConstDyadicR_fit_lower Q
  have hQupper34 : Q ≤ 34 * R := by
    dsimp only [R]
    exact singleLateConstDyadicR_q_upper34 hQ512
  have hprodSmall : 7 * R + 1 ≤ Q := by
    dsimp only [R]
    exact singleLateConstDyadic_prodRoom hQ512
  have hfit : Q + 34 * R ≤ n := by
    dsimp only [R]
    exact singleLateConstDyadic_fit hQ512 hQsmall
  unfold singleLateConstStageError
  calc
    (∑ i ∈ Finset.range singleLateConstStageLength,
        singleLateConstSubRungError n Q
          (singleLateConstCap32 Q (singleLateConstDyadicR Q) i)
          (singleLateConstCap32 Q (singleLateConstDyadicR Q) (i + 1))
          (singleLateConstDyadicR Q)
          (singleLateConstLentry32 (singleLateConstDyadicL0 n Q)
            (singleLateConstDyadicR Q) i)
          (singleLateConstLexit32 (singleLateConstDyadicL0 n Q)
            (singleLateConstDyadicR Q) i)
          (singleLateConstHi32 (singleLateConstDyadicL0 n Q)
            (singleLateConstDyadicR Q) i)
          (singleLateConstD32 (singleLateConstDyadicD0 n Q)
            (singleLateConstDyadicR Q) i))
        ≤ ∑ _i ∈ Finset.range singleLateConstStageLength, 8 * e := by
          apply Finset.sum_le_sum
          intro i hi
          have hiLt : i < singleLateConstStageLength :=
            Finset.mem_range.1 hi
          have hidx := singleLateConstIdx32_of_lt hiLt
          have hidxs := singleLateConstIdx32_succ_of_lt hiLt
          have hrem : singleLateConstRem32 i = 32 - i := by
            unfold singleLateConstRem32
            simp [hidx, singleLateConstStageLength]
          have hremS : singleLateConstRem32 (i + 1) = 31 - i := by
            unfold singleLateConstRem32
            simp [hidxs, singleLateConstStageLength]
          have hi31 : i ≤ 31 := by
            unfold singleLateConstStageLength at hiLt
            omega
          have hremLe : 32 - i ≤ 32 := by omega
          have hremSLe : 31 - i ≤ 31 := by omega
          have hremMulLe : (32 - i) * R ≤ 32 * R :=
            Nat.mul_le_mul_right R hremLe
          have hremSMulLe : (31 - i) * R ≤ 31 * R :=
            Nat.mul_le_mul_right R hremSLe
          have hmul1 : (i + 1) * R = i * R + R := by ring
          have hmul7 : (i + 7) * R = i * R + 7 * R := by ring
          have hPbound :
              singleLateConstCap32 Q R i ≤ 68 * R + 1 := by
            simp [singleLateConstCap32, hrem]
            omega
          have hMainL :
              singleLateConstLentry32 (singleLateConstDyadicL0 n Q) R i ≤
                singleLateConstLexit32 (singleLateConstDyadicL0 n Q) R i + R := by
            simp [singleLateConstLentry32, singleLateConstLexit32, hidx,
              hmul1]
            omega
          have hMainSpan :
              singleLateConstLexit32 (singleLateConstDyadicL0 n Q) R i + R -
                  singleLateConstLentry32 (singleLateConstDyadicL0 n Q) R i ≤
                2 * R + 32 := by
            simp [singleLateConstLentry32, singleLateConstLexit32, hidx,
              hmul1]
            omega
          have hHiL :
              singleLateConstLentry32 (singleLateConstDyadicL0 n Q) R i ≤
                singleLateConstHi32 (singleLateConstDyadicL0 n Q) R i := by
            simp [singleLateConstLentry32, singleLateConstHi32, hidx,
              hmul7]
          have hHiSpan :
              singleLateConstHi32 (singleLateConstDyadicL0 n Q) R i -
                  singleLateConstLentry32 (singleLateConstDyadicL0 n Q) R i ≤
                7 * R + 32 := by
            simp [singleLateConstLentry32, singleLateConstHi32, hidx,
              hmul7]
            omega
          have hd :
              7 * (n - 1) ≤
                10 * singleLateConstD32 (singleLateConstDyadicD0 n Q) R i := by
            have hdBase : 7 * (n - 1) ≤
                10 * (n - Q - 34 * R + 1) := by
              omega
            have hdLower :
                n - Q - 34 * R + 1 ≤
                  singleLateConstD32 (singleLateConstDyadicD0 n Q) R i := by
              simp [singleLateConstD32, singleLateConstDyadicD0, hidx]
              omega
            exact hdBase.trans (Nat.mul_le_mul_left 10 hdLower)
          have hRn : 7 * R ≤ n := by omega
          have hprodRoom :
              singleLateConstD32 (singleLateConstDyadicD0 n Q) R i +
                  2 * singleLateConstCoFloor R ≤ n := by
            have hprodDirect :
                (n - Q - 34 * R + 1 + i * R) + 2 * (5 * R) ≤ n := by
              have hiR : i * R ≤ 31 * R :=
                Nat.mul_le_mul_right R hi31
              have hneed : i * R + 10 * R + 1 ≤ Q + 34 * R := by
                omega
              omega
            simpa [singleLateConstD32, singleLateConstDyadicD0,
              singleLateConstCoFloor, hidx] using hprodDirect
          have hBupper :
              singleLateConstCap32 Q R (i + 1) + 1 ≤ 66 * R := by
            simp [singleLateConstCap32, hremS]
            omega
          have hRetRoom :
              singleLateConstSret R + 1 ≤
                96 * (singleLateConstCap32 Q R (i + 1) + 1) := by
            simp [singleLateConstCap32, hremS, singleLateConstSret]
            omega
          have hterm :=
            singleLateConstSubRungError_le_exp n Q
              (singleLateConstCap32 Q R i)
              (singleLateConstCap32 Q R (i + 1)) R
              (singleLateConstLentry32 (singleLateConstDyadicL0 n Q) R i)
              (singleLateConstLexit32 (singleLateConstDyadicL0 n Q) R i)
              (singleLateConstHi32 (singleLateConstDyadicL0 n Q) R i)
              (singleLateConstD32 (singleLateConstDyadicD0 n Q) R i)
              hn hnLarge hRlarge (by omega : 8 * Q ≤ n + 4) hPbound
              hMainL hMainSpan hHiL hHiSpan hd hRn hprodRoom hBupper
              hRetRoom
          simpa [R, e] using hterm
    _ = 256 * e := by
      simp [singleLateConstStageLength, e]
      ring

theorem singleLateConstRelaxedStageError_le_exp
    (n P Q : ℕ) (hn : 2 ≤ n) (hnLarge : 2998 ≤ n)
    (hPlo : 2 * Q ≤ P) (hPhi : P ≤ 2 * Q + 1)
    (hPquarter : 4 * P ≤ n)
    (hQlarge : 32768 ≤ Q) (hQsmall : 8 * Q ≤ n) :
    singleLateConstRelaxedStageError n P Q ≤
      264 * ENNReal.ofReal (Real.exp (-((Q : ℝ) / 50000))) := by
  let R := singleLateConstDyadicR Q
  let eR : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((R : ℝ) / 1100)))
  let eQ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((Q : ℝ) / 50000)))
  have hQ512 : 512 ≤ Q := hQlarge.trans' (by norm_num)
  have hQupper34 : Q ≤ 34 * R := by
    dsimp only [R]
    exact singleLateConstDyadicR_q_upper34 hQ512
  have hflex :
      singleLateConstDyadicFlexError n P Q ≤ 8 * eR := by
    dsimp only [eR, R]
    exact singleLateConstDyadicFlexError_le_exp n P Q hn hnLarge
      hPlo hPhi hPquarter hQlarge hQsmall
  have hstage :
      singleLateConstStageError n Q R
          (singleLateConstCap32 Q R)
          (singleLateConstLentry32 (singleLateConstDyadicL0 n Q) R)
          (singleLateConstLexit32 (singleLateConstDyadicL0 n Q) R)
          (singleLateConstHi32 (singleLateConstDyadicL0 n Q) R)
          (singleLateConstD32 (singleLateConstDyadicD0 n Q) R) ≤
        256 * eR := by
    dsimp only [eR, R]
    exact singleLateConstStageError_le_exp n Q hn hnLarge
      hQlarge hQsmall
  have heRQ : eR ≤ eQ := by
    dsimp only [eR, eQ, R]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    have hQupperR : (Q : ℝ) ≤ 34 * (singleLateConstDyadicR Q : ℝ) := by
      exact_mod_cast hQupper34
    nlinarith
  unfold singleLateConstRelaxedStageError
  calc
    singleLateConstDyadicFlexError n P Q +
        singleLateConstStageError n Q R
          (singleLateConstCap32 Q R)
          (singleLateConstLentry32 (singleLateConstDyadicL0 n Q) R)
          (singleLateConstLexit32 (singleLateConstDyadicL0 n Q) R)
          (singleLateConstHi32 (singleLateConstDyadicL0 n Q) R)
          (singleLateConstD32 (singleLateConstDyadicD0 n Q) R)
        ≤ 8 * eR + 256 * eR := by
          exact add_le_add hflex hstage
    _ = 264 * eR := by ring
    _ ≤ 264 * eQ := by gcongr

theorem singleLateConstDyadicStepError_le_exp
    (n γ i : ℕ) (hn : 2 ≤ n)
    (hlog : 100000000 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hi : i < singleLateConstDyadicStages n γ) :
    singleLateConstDyadicStepError n γ i ≤
      264 * ENNReal.ofReal
        (Real.exp
          (-(((singleLateConstDyadicCap n γ (i + 1) : ℕ) : ℝ) /
            50000))) := by
  let P := singleLateConstDyadicCap n γ i
  let Q := phase2Scale n (3 + i)
  have hcapQ :
      singleLateConstDyadicCap n γ (i + 1) = Q := by
    simp only [singleLateConstDyadicCap, Q]
    congr 1
    omega
  have hk : i + 1 < phase2StageCount n γ := by
    unfold singleLateConstDyadicStages at hi
    omega
  have hmin := phase2StageCount_minimal (n := n) (γ := γ) hk
  have hminQ : γ * Nat.log 2 n < 2 * Q := by
    dsimp only [Q, phase2Scale]
    simpa [show 2 + (i + 1) = 3 + i by omega] using hmin
  have hγlog : 100000000 ≤ γ * Nat.log 2 n := by
    calc
      100000000 = 1 * 100000000 := by norm_num
      _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
  have hQlarge : 32768 ≤ Q := by omega
  have hnLarge : 2998 ≤ n := by
    have hn4096 :=
      phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hQsmall : 8 * Q ≤ n := by
    dsimp only [Q, phase2Scale]
    have hden : 8 ≤ 2 ^ (3 + i) := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 + i) :=
          Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)
    have hmul : 2 ^ (3 + i) * (n / 2 ^ (3 + i)) ≤ n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self n (2 ^ (3 + i))
    exact (Nat.mul_le_mul_right (n / 2 ^ (3 + i)) hden).trans hmul
  have hPscale :
      P = n / 2 ^ (2 + i) := by
    simp only [P, singleLateConstDyadicCap, phase2Scale]
  have hQscale :
      Q = n / 2 ^ (3 + i) := by
    rfl
  have hdenSucc :
      2 ^ (3 + i) = 2 * 2 ^ (2 + i) := by
    rw [show 3 + i = (2 + i) + 1 by omega, pow_succ]
    ring
  have hPlo : 2 * Q ≤ P := by
    rw [hPscale, hQscale, hdenSucc]
    set a := 2 ^ (2 + i)
    rw [Nat.le_div_iff_mul_le (by positivity : 0 < a)]
    calc
      (2 * (n / (2 * a))) * a = (n / (2 * a)) * (2 * a) := by ring
      _ ≤ n := Nat.div_mul_le_self n (2 * a)
  have hPhi : P ≤ 2 * Q + 1 := by
    rw [hPscale, hQscale, hdenSucc]
    let a := 2 ^ (2 + i)
    have ha : 0 < a := by dsimp only [a]; positivity
    change n / a ≤ 2 * (n / (2 * a)) + 1
    have hdiv := Nat.div_add_mod n (2 * a)
    have hmod := Nat.mod_lt n (by positivity : 0 < 2 * a)
    have hlt :
        n < a * (2 * (n / (2 * a)) + 2) := by
      calc
        n = 2 * a * (n / (2 * a)) + n % (2 * a) := by
          exact hdiv.symm
        _ = 2 * a * (n / (2 * a)) + n % (2 * a) := by ring
        _ < 2 * a * (n / (2 * a)) + 2 * a :=
          Nat.add_lt_add_left hmod _
        _ = a * (2 * (n / (2 * a)) + 2) := by ring
    have hlt' :
        n < (2 * (n / (2 * a)) + 2) * a := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
    have hdivlt :
        n / a < 2 * (n / (2 * a)) + 2 :=
      (@Nat.div_lt_iff_lt_mul a n (2 * (n / (2 * a)) + 2) ha).mpr hlt'
    omega
  have hPquarter : 4 * P ≤ n := by
    rw [hPscale]
    have hden : 4 ≤ 2 ^ (2 + i) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 + i) :=
          Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)
    calc
      4 * (n / 2 ^ (2 + i))
          ≤ 2 ^ (2 + i) * (n / 2 ^ (2 + i)) := by
            exact Nat.mul_le_mul_right (n / 2 ^ (2 + i)) hden
      _ ≤ n := by
            rw [Nat.mul_comm]
            exact Nat.div_mul_le_self n (2 ^ (2 + i))
  have hstage :=
    singleLateConstRelaxedStageError_le_exp n P Q hn hnLarge
      hPlo hPhi hPquarter hQlarge hQsmall
  simpa [singleLateConstDyadicStepError, hcapQ, Q, P] using hstage

theorem singleLateConstDyadicLadderError_le_exp
    (n γ : ℕ) (hn : 2 ≤ n)
    (hlog : 100000000 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (_hsize : 6 * γ * Nat.log 2 n ≤ n) :
    singleLateConstDyadicLadderError n γ ≤
      528 * ENNReal.ofReal
        (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 100000))) := by
  let K := singleLateConstDyadicStages n γ
  by_cases hK0 : K = 0
  · unfold singleLateConstDyadicLadderError
    simp [K, hK0]
  have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
  let g : ℕ → ℝ≥0∞ := fun i =>
    ENNReal.ofReal
      (Real.exp
        (-(((singleLateConstDyadicCap n γ (i + 1) : ℕ) : ℝ) / 50000)))
  have hγlog : 100000000 ≤ γ * Nat.log 2 n := by
    calc
      100000000 = 1 * 100000000 := by norm_num
      _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
  have hsum :
      (∑ i ∈ Finset.range K, singleLateConstDyadicStepError n γ i) ≤
        ∑ i ∈ Finset.range K, 264 * g i := by
    apply Finset.sum_le_sum
    intro i hi
    have hiK : i < K := Finset.mem_range.1 hi
    have hr := singleLateConstDyadicStepError_le_exp n γ i hn hlog hγ
      (by simpa only [K] using hiK)
    simpa only [g] using hr
  have hdouble : ∀ i, i + 1 < K → 2 * g i ≤ g (i + 1) := by
    intro i hi
    let Qi := singleLateConstDyadicCap n γ (i + 1)
    let Qnext := singleLateConstDyadicCap n γ (i + 2)
    have hnextActive : i + 2 < phase2StageCount n γ := by
      dsimp only [K, singleLateConstDyadicStages] at hi
      omega
    have hmin := phase2StageCount_minimal (n := n) (γ := γ) hnextActive
    have hminNext : γ * Nat.log 2 n < 2 * Qnext := by
      dsimp only [Qnext, singleLateConstDyadicCap, phase2Scale]
      simpa [show 2 + (i + 2) = 2 + (i + 2) by rfl] using hmin
    have hQnextLarge : 50000 ≤ Qnext := by omega
    have htwice : 2 * Qnext ≤ Qi := by
      dsimp only [Qi, Qnext, singleLateConstDyadicCap, phase2Scale]
      have hsucc :
          n / 2 ^ (2 + (i + 2)) =
            n / 2 ^ (2 + (i + 1)) / 2 := by
        rw [show 2 + (i + 2) = (2 + (i + 1)) + 1 by omega,
          pow_succ, Nat.div_div_eq_div_mul]
      rw [hsucc]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self
        (n / 2 ^ (2 + (i + 1))) 2
    have hnextLe : Qnext ≤ Qi := by omega
    have hgap : 50000 ≤ Qi - Qnext := by omega
    simp only [g]
    rw [← ENNReal.ofReal_ofNat (n := 2),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [show
        (2 : ℝ) *
            Real.exp
              (-(((singleLateConstDyadicCap n γ (i + 1) : ℕ) : ℝ) /
                50000)) =
          Real.exp (Real.log 2) *
            Real.exp
              (-(((singleLateConstDyadicCap n γ (i + 1) : ℕ) : ℝ) /
                50000)) by
      rw [Real.exp_log (by norm_num)], ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hgapR :
        (50000 : ℝ) ≤
          ((singleLateConstDyadicCap n γ (i + 1) : ℕ) : ℝ) -
            ((singleLateConstDyadicCap n γ (i + 2) : ℕ) : ℝ) := by
      rw [← Nat.cast_sub hnextLe]
      exact_mod_cast hgap
    have hlog2 : Real.log 2 < (1 : ℝ) := by
      exact Real.log_two_lt_d9.trans (by norm_num)
    nlinarith
  have hgeom := enn_sum_le_two_last_of_double g K hKpos hdouble
  have hlast :
      g (K - 1) ≤
        ENNReal.ofReal
          (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 100000))) := by
    have hlastActive : K - 1 + 1 < phase2StageCount n γ := by
      have hKdef : K = phase2StageCount n γ - 2 := by rfl
      dsimp only [K, singleLateConstDyadicStages]
      omega
    have hmin := phase2StageCount_minimal (n := n) (γ := γ) hlastActive
    have hminLast :
        γ * Nat.log 2 n <
          2 * singleLateConstDyadicCap n γ (K - 1 + 1) := by
      dsimp only [singleLateConstDyadicCap, phase2Scale]
      simpa [show 2 + (K - 1 + 1) = 2 + (K - 1 + 1) by rfl] using hmin
    simp only [g]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hminR :
        ((γ * Nat.log 2 n : ℕ) : ℝ) <
          2 * ((singleLateConstDyadicCap n γ (K - 1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hminLast
    nlinarith
  change
    (∑ i ∈ Finset.range K, singleLateConstDyadicStepError n γ i) ≤ _
  calc
    (∑ i ∈ Finset.range K, singleLateConstDyadicStepError n γ i)
        ≤ ∑ i ∈ Finset.range K, 264 * g i := hsum
    _ = 264 * (∑ i ∈ Finset.range K, g i) := by
      rw [Finset.mul_sum]
    _ ≤ 264 * (2 * g (K - 1)) := by gcongr
    _ ≤ 528 * ENNReal.ofReal
          (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 100000))) := by
      calc
        264 * (2 * g (K - 1)) = 528 * g (K - 1) := by ring
        _ ≤ _ := by gcongr

theorem singleLateConstDyadicLadderError_le_power
    (n γ : ℕ) (hn : 2 ≤ n)
    (hlog : 100000000 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    singleLateConstDyadicLadderError n γ ≤
      528 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by omega
  have hlog128 : 128 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hlogn := singleFinal_realLog_le_natLog n hnNat hlog128
  have hS :
      Real.log (n : ℝ) *
          ((1 / 100000000000000 : ℝ) * (γ : ℝ)) ≤
        ((γ * Nat.log 2 n : ℕ) : ℝ) / 100000 := by
    calc
      Real.log (n : ℝ) *
          ((1 / 100000000000000 : ℝ) * (γ : ℝ))
          = (γ : ℝ) * Real.log (n : ℝ) / 100000000000000 := by ring
      _ ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) / 100000000000000 := by
        gcongr
      _ ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) / 100000 := by
        gcongr
        norm_num
      _ = ((γ * Nat.log 2 n : ℕ) : ℝ) / 100000 := by
        norm_num only [Nat.cast_mul]
  calc
    singleLateConstDyadicLadderError n γ
        ≤ 528 * ENNReal.ofReal
          (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 100000))) :=
      singleLateConstDyadicLadderError_le_exp n γ hn hlog hγ hsize
    _ ≤ 528 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
      gcongr
      exact singleFinal_ofReal_exp_neg_le_inv_rpow n hnNat
        (((γ * Nat.log 2 n : ℕ) : ℝ) / 100000)
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) hS

/-- Deeper inverse-power envelopes weaken to the common Single-B exponent. -/
theorem singleInvPower_le_common
    (n γ : ℕ) (hn : 1 ≤ n) (a : ℝ)
    (ha : (1 / 100000000000000 : ℝ) ≤ a) :
    (n : ℝ≥0∞)⁻¹ ^ (a * (γ : ℝ)) ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
  apply ENNReal.rpow_le_rpow_of_exponent_ge
  · rw [ENNReal.inv_le_one]
    exact_mod_cast hn
  · have hγ0 : (0 : ℝ) ≤ γ := by positivity
    nlinarith

/-! ## Early and middle power budgets -/

noncomputable def singleEarlyEnvelopeScale (n γ : ℕ) : ℝ :=
  (singleEarlySeedUnit n γ : ℝ) ^ 2 / (1024 * (n : ℝ))

/-- The early Single-B dyadic stage exponent is `4^j` times the first scale. -/
theorem singleEarlyEnvelope_eq (n γ j : ℕ) :
    (singleEarlyScale n γ j : ℝ) ^ 2 / (1024 * (n : ℝ)) =
      (4 : ℝ) ^ j * singleEarlyEnvelopeScale n γ := by
  unfold singleEarlyScale singleEarlyEnvelopeScale
  push_cast
  have hpow : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul]
    calc
      (2 : ℝ) ^ (j * 2) = ((2 : ℝ) ^ 2) ^ j := by
        rw [← pow_mul, Nat.mul_comm]
      _ = (4 : ℝ) ^ j := by norm_num
  rw [mul_pow, hpow]
  ring

/-- The first early Single-B scale keeps an explicit fraction of the square-gap
logarithmic exponent after the `132`-way unit split. -/
theorem singleEarlyEnvelopeScale_ge_natLog
    (n γ : ℕ) (hn : 0 < n) :
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 100000000 ≤
      singleEarlyEnvelopeScale n γ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let q := singleEarlySeedUnit n γ
  let seed := phase1SeedR n γ
  have hqDiv : seed / 132 ≤ q := by
    dsimp [q, singleEarlySeedUnit, seed]
    exact le_max_right _ _
  have hqpos : 1 ≤ q := by
    dsimp [q, singleEarlySeedUnit]
    exact le_max_left _ _
  have hmod := Nat.mod_lt seed (by norm_num : 0 < 132)
  have hdecomp := Nat.mod_add_div seed 132
  have hseedQ : seed ≤ 264 * q := by omega
  have hseedSq : seed ^ 2 ≤ 69696 * q ^ 2 := by
    have hp := Nat.pow_le_pow_left hseedQ 2
    nlinarith
  have hrad :
      γ * n * Nat.log 2 n ≤ 69696 * q ^ 2 := by
    exact (phase1SeedRadicand_le_sq n γ).trans hseedSq
  have hradR :
      (γ : ℝ) * n * Nat.log 2 n ≤ 69696 * (q : ℝ) ^ 2 := by
    exact_mod_cast hrad
  have hscale :
      (γ : ℝ) * Nat.log 2 n / 100000000 ≤
        (q : ℝ) ^ 2 / (1024 * (n : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 100000000)
      (by positivity : (0 : ℝ) < 1024 * (n : ℝ))]
    nlinarith
  simpa only [q, singleEarlyEnvelopeScale] using hscale

/-- At the headline logarithmic threshold, the first early scale is large enough
for geometric summation of the dyadic-square envelopes. -/
theorem singleEarlyEnvelopeScale_ge_log_two_div_three
    {n γ : ℕ} (hlog : 100000000 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Real.log 2 / 3 ≤ singleEarlyEnvelopeScale n γ := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hmulNat : 100000000 ≤ γ * Nat.log 2 n := by
    calc
      100000000 = 1 * 100000000 := by norm_num
      _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
  have hmulR : (100000000 : ℝ) ≤ γ * Nat.log 2 n := by
    exact_mod_cast hmulNat
  have hlogBound : Real.log 2 / 3 ≤ (1 : ℝ) := by
    have hlogTwo : Real.log 2 ≤ (3 : ℝ) / 4 :=
      Real.log_two_lt_d9.le.trans (by norm_num)
    nlinarith
  have hone :
      (1 : ℝ) ≤ (γ : ℝ) * Nat.log 2 n / 100000000 := by
    nlinarith
  exact hlogBound.trans
    (hone.trans (singleEarlyEnvelopeScale_ge_natLog n γ hnNat))

/-- The selected early Single-B ladder errors geometrically sum once the first
scale has crossed the explicit logarithmic threshold. -/
theorem singleEarlyLadderError_le_geometric
    (n γ : ℕ) (hlog : 100000000 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    singleEarlyLadderError n γ ≤
      ENNReal.ofReal
        (2112 * Real.exp (-singleEarlyEnvelopeScale n γ)) := by
  unfold singleEarlyLadderError
  have hterm : ∀ j ∈ Finset.range (singleEarlyStages n γ),
      132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j)) ≤
        ENNReal.ofReal
          (1056 * Real.exp
            (-((4 : ℝ) ^ j * singleEarlyEnvelopeScale n γ))) := by
    intro j _hj
    have heq := singleEarlyEnvelope_eq n γ j
    calc
      132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j))
          = 1056 * ENNReal.ofReal
              (Real.exp (-((4 : ℝ) ^ j *
                singleEarlyEnvelopeScale n γ))) := by
            rw [singleGapEnvelope, heq]
            ring
      _ ≤ ENNReal.ofReal
              (1056 * Real.exp
                (-((4 : ℝ) ^ j * singleEarlyEnvelopeScale n γ))) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1056),
              ENNReal.ofReal_ofNat]
  calc
    (∑ j ∈ Finset.range (singleEarlyStages n γ),
        132 * (8 * singleGapEnvelope n (singleEarlyScale n γ j)))
        ≤ ∑ j ∈ Finset.range (singleEarlyStages n γ),
            ENNReal.ofReal
              (1056 * Real.exp
                (-((4 : ℝ) ^ j * singleEarlyEnvelopeScale n γ))) :=
      Finset.sum_le_sum hterm
    _ = ENNReal.ofReal
          (∑ j ∈ Finset.range (singleEarlyStages n γ),
            1056 * Real.exp
              (-((4 : ℝ) ^ j * singleEarlyEnvelopeScale n γ))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j hj
      positivity
    _ ≤ ENNReal.ofReal
          (2112 * Real.exp (-singleEarlyEnvelopeScale n γ)) := by
      apply ENNReal.ofReal_le_ofReal
      have hsum :=
        phase1Envelope_sum_le
          (singleEarlyEnvelopeScale_ge_log_two_div_three hlog hγ)
          (singleEarlyStages n γ)
      have heq :
          (∑ j ∈ Finset.range (singleEarlyStages n γ),
            1056 * Real.exp
              (-((4 : ℝ) ^ j * singleEarlyEnvelopeScale n γ))) =
            528 * (∑ j ∈ Finset.range (singleEarlyStages n γ),
              2 * Real.exp
                (-((4 : ℝ) ^ j * singleEarlyEnvelopeScale n γ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      rw [heq]
      nlinarith [Real.exp_pos (-singleEarlyEnvelopeScale n γ)]

theorem singleEarlyLadderError_le_power
    (n γ : ℕ) (hlog : 100000000 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    singleEarlyLadderError n γ ≤
      2112 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 200000000 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hlog128 : 128 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hlogn := singleFinal_realLog_le_natLog n hnNat hlog128
  have hS :
      Real.log (n : ℝ) * ((1 / 200000000 : ℝ) * (γ : ℝ))
        ≤ singleEarlyEnvelopeScale n γ := by
    calc
      Real.log (n : ℝ) * ((1 / 200000000 : ℝ) * (γ : ℝ))
          = (γ : ℝ) * (Real.log (n : ℝ) / 200000000) := by ring
      _ ≤ (γ : ℝ) * ((Nat.log 2 n : ℝ) / 200000000) := by
        gcongr
      _ ≤ (γ : ℝ) * ((Nat.log 2 n : ℝ) / 100000000) := by
        gcongr
        norm_num
      _ = (γ : ℝ) * (Nat.log 2 n : ℝ) / 100000000 := by ring
      _ ≤ singleEarlyEnvelopeScale n γ :=
        singleEarlyEnvelopeScale_ge_natLog n γ hnNat
  calc
    singleEarlyLadderError n γ
        ≤ ENNReal.ofReal
          (2112 * Real.exp (-singleEarlyEnvelopeScale n γ)) :=
      singleEarlyLadderError_le_geometric n γ hlog hγ
    _ ≤ 2112 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 200000000 : ℝ) * (γ : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2112)]
      norm_num only [ENNReal.ofReal_ofNat]
      gcongr
      exact singleFinal_ofReal_exp_neg_le_inv_rpow n hnNat
        (singleEarlyEnvelopeScale n γ)
        ((1 / 200000000 : ℝ) * (γ : ℝ)) hS

theorem singleMiddleEnvelopeScale_ge_natLog
    (n γ : ℕ) (hlog : 100000000 ≤ Nat.log 2 n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    (γ : ℝ) * (Nat.log 2 n : ℝ) / 100000000000000 ≤
      (singleMiddleUnit n : ℝ) ^ 2 / (1024 * (n : ℝ)) := by
  let q := singleMiddleUnit n
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hqpos : 0 < q := by
    simpa [q] using singleMiddleUnit_pos (hlog.trans' (by norm_num))
  have hnq : n ≤ 524288 * q := by
    change n ≤ 524288 * singleMiddleUnit n
    unfold singleMiddleUnit
    have hdiv := Nat.div_add_mod n 262144
    have hmod := Nat.mod_lt n (by norm_num : 0 < 262144)
    have hqpos' : 0 < n / 262144 := by
      simpa [q, singleMiddleUnit] using hqpos
    omega
  have hnqSq : n ^ 2 ≤ 274877906944 * q ^ 2 := by
    have hp := Nat.pow_le_pow_left hnq 2
    nlinarith
  have hnqSqR : (n : ℝ) ^ 2 ≤ 274877906944 * (q : ℝ) ^ 2 := by
    have h' : n ^ 2 ≤ 274877906944 * q ^ 2 := by
      simpa [pow_two] using hnqSq
    exact_mod_cast h'
  have hsizeR :
      6 * (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ n := by
    exact_mod_cast hsize
  rw [div_le_div_iff₀
    (by norm_num : (0 : ℝ) < 100000000000000)
    (by positivity : (0 : ℝ) < 1024 * (n : ℝ))]
  nlinarith [sq_nonneg (n : ℝ), sq_nonneg (q : ℝ)]

theorem singleGapEnvelope_middle_le_power
    (n γ : ℕ) (hlog : 100000000 ≤ Nat.log 2 n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    singleGapEnvelope n (singleMiddleUnit n) ≤
      (n : ℝ≥0∞)⁻¹ ^
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hlog128 : 128 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hlogn := singleFinal_realLog_le_natLog n hnNat hlog128
  have hS :
      Real.log (n : ℝ) *
          ((1 / 100000000000000 : ℝ) * (γ : ℝ))
        ≤ (singleMiddleUnit n : ℝ) ^ 2 / (1024 * (n : ℝ)) := by
    calc
      Real.log (n : ℝ) *
          ((1 / 100000000000000 : ℝ) * (γ : ℝ))
          = (γ : ℝ) * (Real.log (n : ℝ) / 100000000000000) := by ring
      _ ≤ (γ : ℝ) *
          ((Nat.log 2 n : ℝ) / 100000000000000) := by
        gcongr
      _ = (γ : ℝ) * (Nat.log 2 n : ℝ) / 100000000000000 := by ring
      _ ≤ (singleMiddleUnit n : ℝ) ^ 2 / (1024 * (n : ℝ)) :=
        singleMiddleEnvelopeScale_ge_natLog n γ hlog hsize
  unfold singleGapEnvelope
  exact singleFinal_ofReal_exp_neg_le_inv_rpow n hnNat
    ((singleMiddleUnit n : ℝ) ^ 2 / (1024 * (n : ℝ)))
    ((1 / 100000000000000 : ℝ) * (γ : ℝ)) hS

theorem singleMiddleError_le_power
    (n : ℕ) (γ : ℕ) (hlog : 100000000 ≤ Nat.log 2 n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    singleMiddleError n ≤
      785600 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
  have hgap := singleGapEnvelope_middle_le_power n γ hlog hsize
  unfold singleMiddleError singleMiddleBootstrapRungs singleMiddleMainRungs
  calc
    126 * (8 * singleGapEnvelope n (singleMiddleUnit n)) +
        98074 * (8 * singleGapEnvelope n (singleMiddleUnit n))
        = 785600 * singleGapEnvelope n (singleMiddleUnit n) := by ring
    _ ≤ 785600 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
      gcongr

/-! ## High-cap bridge scalar budgets -/

theorem singleHighCapBw_lower
    {n i : ℕ} (hi : i < singleHighCapBridgeLength) :
    n ≤ 10000 * singleHighCapBw n i := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBw,
      singleHighCapCeilPM, singleHighCapBwPM, singleHighCapPMDen] <;>
    omega

theorem singleHighCapD_lower82
    {n i : ℕ} (hi : i < singleHighCapBridgeLength) :
    82 * n ≤ 10000 * singleHighCapD n i := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapD,
      singleHighCapCeilPM, singleHighCapDPM, singleHighCapPMDen] <;>
    omega

theorem singleHighCapH_upper_two
    {n i : ℕ} (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    singleHighCapH n i ≤ 2 * n := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapH, singleHighCapP,
      singleHighCapCoCap, singleLateEntryCoCap, singleHighCapMhi,
      singleHighCapFloorPM, singleHighCapMhiPM, singleHighCapD,
      singleHighCapCeilPM, singleHighCapDPM, singleHighCapPMDen] <;>
    omega

theorem singleHighCapK_upper_three
    {n i : ℕ} (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    singleHighCapK n i ≤ 3 * n := by
  unfold singleHighCapK
  have hH := singleHighCapH_upper_two (n := n) (i := i) hnLarge hi
  have hM : singleHighCapM n i ≤ n := by
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;>
      simp [singleHighCapM,
        singleHighCapFloorPM, singleHighCapMPM, singleHighCapPMDen] <;>
      omega
  omega

theorem singleHighCap_creation_stream_le_exp
    (n i : ℕ) (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    ENNReal.ofReal
        (Real.exp
          (-((singleHighCapD n i : ℝ) ^ 2 /
            (2 * (singleHighCapH n i : ℝ))))) ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  have hnPos : 0 < n := by omega
  have hHpos : 0 < singleHighCapH n i := by
    unfold singleHighCapH
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hHR : (0 : ℝ) < singleHighCapH n i := by exact_mod_cast hHpos
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 200000)
    (by positivity : (0 : ℝ) < 2 * (singleHighCapH n i : ℝ))]
  have hD :
      (82 : ℝ) * (n : ℝ) ≤
        10000 * (singleHighCapD n i : ℝ) := by
    exact_mod_cast singleHighCapD_lower82 (n := n) (i := i) hi
  have hH :
      (singleHighCapH n i : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast singleHighCapH_upper_two (n := n) (i := i) hnLarge hi
  nlinarith [sq_nonneg (10000 * (singleHighCapD n i : ℝ) -
    82 * (n : ℝ))]

theorem singleHighCap_backslide_stream_le_exp
    (n i : ℕ) (hi : i < singleHighCapBridgeLength) :
    singleHighCapDirW ^ singleHighCapBw n i ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) := by
  have hw :
      singleHighCapDirW = ((19 : ℝ≥0∞) / (20 : ℝ≥0∞)) := by
    unfold singleHighCapDirW
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 20)]
    norm_num
  rw [hw]
  refine ratio_pow_le_ofReal_exp 20 19 (singleHighCapBw n i)
    ((n : ℝ) / 200000) (by norm_num) (by norm_num) ?_
  have hBw :
      (n : ℝ) ≤ 10000 * (singleHighCapBw n i : ℝ) := by
    exact_mod_cast singleHighCapBw_lower (n := n) (i := i) hi
  norm_num only [Nat.cast_ofNat]
  nlinarith

def singleHighCapEtaDeltaPM : ℕ → ℕ
  | 0 => 1744
  | 1 => 1908
  | 2 => 2074
  | 3 => 2241
  | 4 => 2410
  | 5 => 2581
  | 6 => 2753
  | 7 => 2927
  | 8 => 3102
  | 9 => 3278
  | 10 => 3456
  | 11 => 3636
  | _ => 1744

def singleHighCapProductiveXPM : ℕ → ℕ
  | 0 => 24314
  | 1 => 25192
  | 2 => 25716
  | 3 => 25950
  | 4 => 25957
  | 5 => 25592
  | 6 => 25028
  | 7 => 24060
  | 8 => 22761
  | 9 => 21257
  | 10 => 19552
  | 11 => 17521
  | _ => 17521

def singleHighCapLiveGapLowerPM : ℕ → ℕ
  | 0 => 3597
  | 1 => 3906
  | 2 => 4216
  | 3 => 4529
  | 4 => 4843
  | 5 => 5160
  | 6 => 5477
  | 7 => 5798
  | 8 => 6119
  | 9 => 6442
  | 10 => 6766
  | 11 => 7094
  | _ => 3597

def singleHighCapCoFloorLowerPM : ℕ → ℕ
  | 0 => 676
  | 1 => 645
  | 2 => 610
  | 3 => 573
  | 4 => 536
  | 5 => 496
  | 6 => 457
  | 7 => 415
  | 8 => 372
  | 9 => 330
  | 10 => 289
  | 11 => 247
  | _ => 247

def singleHighCapKUpperPM : ℕ → ℕ
  | 0 => 20551
  | 1 => 18853
  | 2 => 17273
  | 3 => 15814
  | 4 => 14436
  | 5 => 13163
  | 6 => 11954
  | 7 => 10823
  | 8 => 9757
  | 9 => 8738
  | 10 => 7754
  | 11 => 6817
  | _ => 6817

def singleHighCapBretUpperPM : ℕ → ℕ
  | 0 => 5939
  | 1 => 5626
  | 2 => 5314
  | 3 => 5001
  | 4 => 4689
  | 5 => 4376
  | 6 => 4064
  | 7 => 3751
  | 8 => 3439
  | 9 => 3126
  | 10 => 2814
  | 11 => 2501
  | _ => 2501

theorem singleHighCapHorizon_lower_pm (n i : ℕ) :
    singleHighCapTPM i * n ≤
      singleHighCapPMDen * singleHighCapHorizon n i := by
  unfold singleHighCapHorizon singleHighCapCeilPM singleHighCapPMDen
  omega

theorem singleHighCapHorizon_upper_pm
    (n i : ℕ) (hnLarge : 65536 ≤ n) :
    singleHighCapPMDen * singleHighCapHorizon n i ≤
      (singleHighCapTPM i + 1) * n := by
  unfold singleHighCapHorizon singleHighCapCeilPM singleHighCapPMDen
  have hdiv := Nat.mul_div_le
    (singleHighCapTPM i * n + (10000 - 1)) 10000
  norm_num at hdiv ⊢
  calc
    10000 * ((singleHighCapTPM i * n + 9999) / 10000)
        ≤ singleHighCapTPM i * n + 9999 := hdiv
    _ ≤ (singleHighCapTPM i + 1) * n := by
      rw [Nat.add_mul]
      omega

theorem singleHighCapK_upper_pm
    (n i : ℕ) (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    singleHighCapPMDen * singleHighCapK n i ≤
      singleHighCapKUpperPM i * n := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapKUpperPM, singleHighCapK, singleHighCapH,
      singleHighCapP, singleHighCapCoCap, singleLateEntryCoCap,
      singleHighCapMhi, singleHighCapD, singleHighCapM,
      singleHighCapCeilPM, singleHighCapFloorPM,
      singleHighCapMhiPM, singleHighCapDPM, singleHighCapMPM,
      singleHighCapPMDen] <;>
    omega

theorem singleHighCapBret_upper_pm
    (n i : ℕ) (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    singleHighCapPMDen * (singleHighCapQ n i + 1) ≤
      singleHighCapBretUpperPM i * n := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    simp [singleHighCapBretUpperPM, singleHighCapQ,
      singleHighCapCoCap, singleHighCapPMDen] <;>
    omega

theorem singleHighCapSret_lower_pm (n i : ℕ) :
    singleHighCapSretPM i * n ≤
      singleHighCapPMDen * (singleHighCapSret n i + 1) := by
  unfold singleHighCapSret singleHighCapFloorPM singleHighCapPMDen
  omega

theorem singleHighCap_return_exp_coeff
    (i : ℕ) (hi : i < singleHighCapBridgeLength) :
    2 * (singleHighCapTPM i + 1) * singleHighCapBretUpperPM i +
        500000000 ≤ singleHighCapSretPM i * 5000000 := by
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  interval_cases i <;>
    norm_num [singleHighCapTPM, singleHighCapBretUpperPM,
      singleHighCapSretPM]

theorem singleHighCapDirEta_toReal_eq
    {n i : ℕ} (hdlt : singleHighCapLiveGap n i < n) :
    (singleHighCapDirEta n i).toReal =
      (760 * (n : ℝ)) /
        (761 * (n : ℝ) - 39 * (singleHighCapLiveGap n i : ℝ)) := by
  let d := singleHighCapLiveGap n i
  have hdle : d ≤ n := le_of_lt hdlt
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le d) hdlt
  have hdenU : (0 : ℝ) < (n : ℝ) + (d : ℝ) := by positivity
  have hdenEta : (0 : ℝ) < 761 * (n : ℝ) - 39 * (d : ℝ) := by
    have hdR : (d : ℝ) < n := by exact_mod_cast hdlt
    nlinarith
  have huT : singleHighCapDirU n i ≠ ⊤ := by
    dsimp only [singleHighCapDirU, singleHighCapDirP, singleHighCapDirQ, d]
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega)
  have hwT : singleHighCapDirW ≠ ⊤ := by
    unfold singleHighCapDirW
    exact ENNReal.ofReal_ne_top
  have hU :
      (singleHighCapDirU n i).toReal =
        ((n : ℝ) - (d : ℝ)) / ((n : ℝ) + (d : ℝ)) := by
    dsimp only [singleHighCapDirU, singleHighCapDirP, singleHighCapDirQ, d]
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      Nat.cast_sub hdle, Nat.cast_add]
  have hW : singleHighCapDirW.toReal = (19 : ℝ) / 20 := by
    unfold singleHighCapDirW
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 19 / 20)]
  unfold singleHighCapDirEta
  rw [ENNReal.toReal_div, ENNReal.toReal_mul]
  rw [ENNReal.toReal_add huT ENNReal.one_ne_top]
  rw [ENNReal.toReal_add huT (ENNReal.pow_ne_top hwT)]
  rw [ENNReal.toReal_pow, hU, hW]
  field_simp [hdenU.ne', hdenEta.ne']
  simp only [ENNReal.toReal_one]
  dsimp only [d]
  ring_nf

theorem singleHighCapDirEta_lower
    {n i : ℕ} (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    ENNReal.ofReal
        (1 + (singleHighCapEtaDeltaPM i : ℝ) / 100000) ≤
      singleHighCapDirEta n i := by
  have hnPos : 0 < n := by omega
  have hdlt := singleHighCap_d_lt_n (n := n) (i := i) hnLarge hi
  have hleftT :
      ENNReal.ofReal
          (1 + (singleHighCapEtaDeltaPM i : ℝ) / 100000) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hrightT : singleHighCapDirEta n i ≠ ⊤ := by
    have hparams :=
      singleHighCapDir_params (n := n) (i := i) hnPos hdlt
        (singleHighCap_d_large (n := n) (i := i) hnLarge hi)
    exact hparams.2.2.2.1
  apply (ENNReal.toReal_le_toReal hleftT hrightT).mp
  rw [ENNReal.toReal_ofReal (by positivity :
    (0 : ℝ) ≤ 1 + (singleHighCapEtaDeltaPM i : ℝ) / 100000)]
  rw [singleHighCapDirEta_toReal_eq (n := n) (i := i) hdlt]
  have hdenEta :
      (0 : ℝ) <
        761 * (n : ℝ) - 39 * (singleHighCapLiveGap n i : ℝ) := by
    have hdR : (singleHighCapLiveGap n i : ℝ) < n := by
      exact_mod_cast hdlt
    nlinarith
  have hdenNat : 39 * singleHighCapLiveGap n i ≤ 761 * n := by
    have hdle : singleHighCapLiveGap n i ≤ n := le_of_lt hdlt
    omega
  have hnat :
      (100000 + singleHighCapEtaDeltaPM i) *
          (761 * n - 39 * singleHighCapLiveGap n i) ≤
        76000000 * n := by
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;>
      unfold singleHighCapLiveGap singleHighCapAlo singleHighCapBw
        singleHighCapD singleHighCapLentry singleHighCapP
        singleHighCapCoCap singleLateEntryCoCap singleHighCapCeilPM
        singleHighCapBwPM singleHighCapDPM singleHighCapPMDen
        singleHighCapEtaDeltaPM <;>
      simp <;>
      omega
  have hnatR :
      ((100000 + singleHighCapEtaDeltaPM i) : ℝ) *
          (761 * (n : ℝ) -
            39 * (singleHighCapLiveGap n i : ℝ)) ≤
        76000000 * (n : ℝ) := by
    have hcast :
        (((100000 + singleHighCapEtaDeltaPM i) *
          (761 * n - 39 * singleHighCapLiveGap n i) : ℕ) : ℝ) ≤
            ((76000000 * n : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_sub hdenNat, Nat.cast_mul, Nat.cast_add] using hcast
  have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
  rw [le_div_iff₀ hdenEta]
  nlinarith

theorem singleHighCap_log_twenty_nineteen_le :
    Real.log ((20 : ℝ) / 19) ≤ (39 : ℝ) / 760 := by
  have hp := log_one_add_le_pade (x := (1 : ℝ) / 19) (by norm_num)
  norm_num at hp ⊢
  simpa [show (1 : ℝ) + 1 / 19 = 20 / 19 by norm_num] using hp

theorem singleHighCap_direction_stream_aux
    (n L target M : ℕ) (η : ℝ≥0∞) (a : ℝ)
    (hηT : η ≠ ⊤)
    (hηLower : ENNReal.ofReal (1 + a) ≤ η)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hL : L ≤ target)
    (hexp :
      ((target - L : ℕ) : ℝ) * ((39 : ℝ) / 760) -
          (M : ℝ) * (a - a ^ 2 / 2) ≤
        -((n : ℝ) / 200000)) :
    singleHighCapDirW ^ L /
        (singleHighCapDirW ^ target * η ^ M) ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) := by
  have hηReal :
      1 + a ≤ η.toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hηT).mpr
      hηLower
    rw [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 + a)] at h
    exact h
  have hηpos : 0 < η.toReal := by nlinarith
  have hη0 : η ≠ 0 := by
    intro hz
    rw [hz] at hηReal
    simp at hηReal
    nlinarith
  have hw0 : singleHighCapDirW ≠ 0 := by
    unfold singleHighCapDirW
    simp [ENNReal.ofReal_eq_zero]
  have hwT : singleHighCapDirW ≠ ⊤ := by
    unfold singleHighCapDirW
    exact ENNReal.ofReal_ne_top
  have hden0 : singleHighCapDirW ^ target * η ^ M ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hη0)
  have htermT :
      singleHighCapDirW ^ L /
          (singleHighCapDirW ^ target * η ^ M) ≠ ⊤ :=
    ENNReal.div_ne_top (by finiteness) hden0
  apply (ENNReal.toReal_le_toReal htermT ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow, ENNReal.toReal_pow]
  have hW : singleHighCapDirW.toReal = (19 : ℝ) / 20 := by
    unfold singleHighCapDirW
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 19 / 20)]
  rw [hW]
  have hwpos : (0 : ℝ) < 19 / 20 := by norm_num
  have hdenpos : 0 < (19 / 20 : ℝ) ^ target * η.toReal ^ M := by
    positivity
  have htermpos :
      0 < (19 / 20 : ℝ) ^ L /
          ((19 / 20 : ℝ) ^ target * η.toReal ^ M) := by
    positivity
  have hlogw : Real.log ((19 : ℝ) / 20) =
      -Real.log ((20 : ℝ) / 19) := by
    rw [show ((19 : ℝ) / 20) = (((20 : ℝ) / 19)⁻¹) by norm_num,
      Real.log_inv]
  have hlogeq :
      Real.log
          ((19 / 20 : ℝ) ^ L /
            ((19 / 20 : ℝ) ^ target * η.toReal ^ M)) =
        ((target - L : ℕ) : ℝ) * Real.log ((20 : ℝ) / 19) -
          (M : ℝ) * Real.log η.toReal := by
    rw [Real.log_div (pow_ne_zero _ (ne_of_gt hwpos))
      (ne_of_gt hdenpos),
      Real.log_mul (pow_ne_zero _ (ne_of_gt hwpos))
        (pow_ne_zero _ (ne_of_gt hηpos)),
      Real.log_pow, Real.log_pow, hlogw]
    rw [Real.log_pow]
    rw [Nat.cast_sub hL]
    ring_nf
  have hlogη :
      a - a ^ 2 / 2 ≤ Real.log η.toReal := by
    have hbase := log_one_add_ge_sub_sq_half ha0 ha1
    have hmono : Real.log (1 + a) ≤ Real.log η.toReal :=
      Real.log_le_log (by linarith : (0 : ℝ) < 1 + a) hηReal
    linarith
  have hlog20 := singleHighCap_log_twenty_nineteen_le
  have hlogBound :
      Real.log
          ((19 / 20 : ℝ) ^ L /
            ((19 / 20 : ℝ) ^ target * η.toReal ^ M))
        ≤ -((n : ℝ) / 200000) := by
    rw [hlogeq]
    have hA :
        ((target - L : ℕ) : ℝ) * Real.log ((20 : ℝ) / 19) ≤
          ((target - L : ℕ) : ℝ) * ((39 : ℝ) / 760) :=
      mul_le_mul_of_nonneg_left hlog20 (by positivity)
    have hB :
        (M : ℝ) * (a - a ^ 2 / 2) ≤
          (M : ℝ) * Real.log η.toReal :=
      mul_le_mul_of_nonneg_left hlogη (by positivity)
    nlinarith
  calc
    (19 / 20 : ℝ) ^ L /
          ((19 / 20 : ℝ) ^ target * η.toReal ^ M)
        = Real.exp (Real.log
          ((19 / 20 : ℝ) ^ L /
            ((19 / 20 : ℝ) ^ target * η.toReal ^ M))) := by
          rw [Real.exp_log htermpos]
    _ ≤ Real.exp (-((n : ℝ) / 200000)) :=
      Real.exp_le_exp.mpr hlogBound

theorem singleHighCap_main_direction_stream_le_exp
    (n i : ℕ) (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    singleHighCapDirW ^ singleHighCapLentry n i /
        (singleHighCapDirW ^
            (singleHighCapLexit n i + singleHighCapD n i) *
          singleHighCapDirEta n i ^ singleHighCapM n i) ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) := by
  let L := singleHighCapLentry n i
  let target := singleHighCapLexit n i + singleHighCapD n i
  let M := singleHighCapM n i
  let apm := singleHighCapEtaDeltaPM i
  have hnPos : 0 < n := by omega
  have hdlt := singleHighCap_d_lt_n (n := n) (i := i) hnLarge hi
  have hηT : singleHighCapDirEta n i ≠ ⊤ := by
    have hparams :=
      singleHighCapDir_params (n := n) (i := i) hnPos hdlt
        (singleHighCap_d_large (n := n) (i := i) hnLarge hi)
    exact hparams.2.2.2.1
  have hηLower :=
    singleHighCapDirEta_lower (n := n) (i := i) hnLarge hi
  have hL : L ≤ target := by
    dsimp only [L, target]
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;>
      simp [singleHighCapLentry, singleHighCapLexit,
        singleHighCapP, singleHighCapQ, singleHighCapCoCap,
        singleLateEntryCoCap, singleHighCapD, singleHighCapCeilPM,
        singleHighCapDPM, singleHighCapPMDen] <;>
      omega
  have hnat :
      19500000000 * (target - L) + 1900000 * n ≤
        19 * M * apm * (200000 - apm) := by
    dsimp only [L, target, M, apm]
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;>
      simp [singleHighCapEtaDeltaPM, singleHighCapLentry,
        singleHighCapLexit, singleHighCapP, singleHighCapQ,
        singleHighCapCoCap, singleLateEntryCoCap, singleHighCapD,
        singleHighCapM, singleHighCapCeilPM, singleHighCapFloorPM,
        singleHighCapDPM, singleHighCapMPM, singleHighCapPMDen] <;>
      omega
  have hexp :
      ((target - L : ℕ) : ℝ) * ((39 : ℝ) / 760) -
          (M : ℝ) * ((apm : ℝ) / 100000 -
            ((apm : ℝ) / 100000) ^ 2 / 2) ≤
        -((n : ℝ) / 200000) := by
    have hnatR : (19500000000 : ℝ) * (target - L : ℝ) +
          1900000 * (n : ℝ) ≤
        19 * (M : ℝ) * (apm : ℝ) * (200000 - (apm : ℝ)) := by
      have hapm : apm ≤ 200000 := by
        dsimp only [apm]
        have hi12 : i < 12 := by
          simpa [singleHighCapBridgeLength] using hi
        interval_cases i <;> norm_num [singleHighCapEtaDeltaPM]
      have hcast :
          (((19500000000 * (target - L) + 1900000 * n : ℕ) : ℝ) ≤
            ((19 * M * apm * (200000 - apm) : ℕ) : ℝ)) :=
        Nat.cast_le.mpr hnat
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hL,
        Nat.cast_sub hapm] using hcast
    rw [Nat.cast_sub hL]
    nlinarith
  exact singleHighCap_direction_stream_aux n L target M
    (singleHighCapDirEta n i) ((apm : ℝ) / 100000) hηT hηLower
    (by positivity) (by
      dsimp only [apm]
      have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
      interval_cases i <;> norm_num [singleHighCapEtaDeltaPM])
    hL hexp

theorem singleHighCap_high_direction_stream_le_exp
    (n i : ℕ) (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    singleHighCapDirW ^ singleHighCapLentry n i /
        (singleHighCapDirW ^ singleHighCapHi n i *
          singleHighCapDirEta n i ^ singleHighCapMhi n i) ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) := by
  let L := singleHighCapLentry n i
  let target := singleHighCapHi n i
  let M := singleHighCapMhi n i
  let apm := singleHighCapEtaDeltaPM i
  have hnPos : 0 < n := by omega
  have hdlt := singleHighCap_d_lt_n (n := n) (i := i) hnLarge hi
  have hηT : singleHighCapDirEta n i ≠ ⊤ := by
    have hparams :=
      singleHighCapDir_params (n := n) (i := i) hnPos hdlt
        (singleHighCap_d_large (n := n) (i := i) hnLarge hi)
    exact hparams.2.2.2.1
  have hηLower :=
    singleHighCapDirEta_lower (n := n) (i := i) hnLarge hi
  have hL : L ≤ target := by
    dsimp only [L, target]
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;>
      simp [singleHighCapLentry, singleHighCapHi,
        singleHighCapLexit, singleHighCapP, singleHighCapQ,
        singleHighCapCoCap, singleLateEntryCoCap, singleHighCapSret,
        singleHighCapD, singleHighCapCeilPM, singleHighCapFloorPM,
        singleHighCapSretPM, singleHighCapDPM, singleHighCapPMDen] <;>
      omega
  have hnat :
      19500000000 * (target - L) + 1900000 * n ≤
        19 * M * apm * (200000 - apm) := by
    dsimp only [L, target, M, apm]
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;>
      simp [singleHighCapEtaDeltaPM, singleHighCapLentry,
        singleHighCapHi, singleHighCapLexit, singleHighCapP,
        singleHighCapQ, singleHighCapCoCap, singleLateEntryCoCap,
        singleHighCapSret, singleHighCapD, singleHighCapMhi,
        singleHighCapCeilPM, singleHighCapFloorPM,
        singleHighCapSretPM, singleHighCapDPM, singleHighCapMhiPM,
        singleHighCapPMDen] <;>
      omega
  have hexp :
      ((target - L : ℕ) : ℝ) * ((39 : ℝ) / 760) -
          (M : ℝ) * ((apm : ℝ) / 100000 -
            ((apm : ℝ) / 100000) ^ 2 / 2) ≤
        -((n : ℝ) / 200000) := by
    have hnatR : (19500000000 : ℝ) * (target - L : ℝ) +
          1900000 * (n : ℝ) ≤
        19 * (M : ℝ) * (apm : ℝ) * (200000 - (apm : ℝ)) := by
      have hapm : apm ≤ 200000 := by
        dsimp only [apm]
        have hi12 : i < 12 := by
          simpa [singleHighCapBridgeLength] using hi
        interval_cases i <;> norm_num [singleHighCapEtaDeltaPM]
      have hcast :
          (((19500000000 * (target - L) + 1900000 * n : ℕ) : ℝ) ≤
            ((19 * M * apm * (200000 - apm) : ℕ) : ℝ)) :=
        Nat.cast_le.mpr hnat
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hL,
        Nat.cast_sub hapm] using hcast
    rw [Nat.cast_sub hL]
    nlinarith
  exact singleHighCap_direction_stream_aux n L target M
    (singleHighCapDirEta n i) ((apm : ℝ) / 100000) hηT hηLower
    (by positivity) (by
      dsimp only [apm]
      have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
      interval_cases i <;> norm_num [singleHighCapEtaDeltaPM])
    hL hexp

theorem singleHighCap_productive_x_le
    (n i : ℕ) (hn : 2 ≤ n) (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    ENNReal.ofReal
        ((singleHighCapProductiveXPM i : ℝ) / 1000000) ≤
      singleBandProductivity n (singleHighCapLiveGap n i)
        (singleHighCapCoFloor n i) * ((1 : ℝ≥0∞) / 2) := by
  let xpm := singleHighCapProductiveXPM i
  let A := singleHighCapLiveGapLowerPM i
  let C := singleHighCapCoFloorLowerPM i
  let d := singleHighCapLiveGap n i
  let c := singleHighCapCoFloor n i
  have hA : A * n ≤ 10000 * d := by
    dsimp only [A, d]
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;>
      simp [singleHighCapLiveGapLowerPM, singleHighCapLiveGap,
        singleHighCapAlo, singleHighCapBw, singleHighCapD,
        singleHighCapLentry, singleHighCapP, singleHighCapCoCap,
        singleLateEntryCoCap, singleHighCapCeilPM, singleHighCapBwPM,
        singleHighCapDPM, singleHighCapPMDen] <;>
      omega
  have hC : C * n ≤ 10000 * c := by
    dsimp only [C, c]
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;>
      simp [singleHighCapCoFloorLowerPM, singleHighCapCoFloor,
        singleHighCapFloorPM, singleHighCapCoFloorPM,
        singleHighCapPMDen] <;>
      omega
  have hAC : 100 * xpm ≤ A * C := by
    dsimp only [xpm, A, C]
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;> norm_num [singleHighCapProductiveXPM,
      singleHighCapLiveGapLowerPM, singleHighCapCoFloorLowerPM]
  have hprodR :
      (xpm : ℝ) / 1000000 ≤
        (d : ℝ) * (c : ℝ) / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1R : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < n - 1)
    have hAR : (A : ℝ) * (n : ℝ) ≤ 10000 * (d : ℝ) := by
      exact_mod_cast hA
    have hCR : (C : ℝ) * (n : ℝ) ≤ 10000 * (c : ℝ) := by
      exact_mod_cast hC
    have hACR : 100 * (xpm : ℝ) ≤ (A : ℝ) * (C : ℝ) := by
      exact_mod_cast hAC
    have hnn : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : n - 1 ≤ n)
    have hmul :
        ((A : ℝ) * (n : ℝ)) * ((C : ℝ) * (n : ℝ)) ≤
          (10000 * (d : ℝ)) * (10000 * (c : ℝ)) := by
      exact mul_le_mul hAR hCR (by positivity) (by positivity)
    have hleft :
        100 * (xpm : ℝ) * (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤
          ((A : ℝ) * (C : ℝ)) * (n : ℝ) * (n : ℝ) := by
      calc
        100 * (xpm : ℝ) * (n : ℝ) * ((n - 1 : ℕ) : ℝ)
            = (100 * (xpm : ℝ)) * ((n - 1 : ℕ) : ℝ) * (n : ℝ) := by ring
        _ ≤ (100 * (xpm : ℝ)) * (n : ℝ) * (n : ℝ) := by
          gcongr
        _ ≤ ((A : ℝ) * (C : ℝ)) * (n : ℝ) * (n : ℝ) := by
          gcongr
    have hbound :
        100 * (xpm : ℝ) * (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤
          100000000 * ((d : ℝ) * (c : ℝ)) := by
      calc
        100 * (xpm : ℝ) * (n : ℝ) * ((n - 1 : ℕ) : ℝ)
            ≤ ((A : ℝ) * (C : ℝ)) * (n : ℝ) * (n : ℝ) := hleft
        _ = ((A : ℝ) * (n : ℝ)) * ((C : ℝ) * (n : ℝ)) := by ring
        _ ≤ (10000 * (d : ℝ)) * (10000 * (c : ℝ)) := hmul
        _ = 100000000 * ((d : ℝ) * (c : ℝ)) := by ring
    rw [div_le_div_iff₀
      (by norm_num : (0 : ℝ) < 1000000)
      (by positivity : (0 : ℝ) < (n : ℝ) * ((n - 1 : ℕ) : ℝ))]
    nlinarith
  have hrightT :
      singleBandProductivity n d c * ((1 : ℝ≥0∞) / 2) ≠ ⊤ := by
    unfold singleBandProductivity
    apply ENNReal.mul_ne_top
    · apply ENNReal.div_ne_top
      · exact ENNReal.natCast_ne_top _
      · simp only [ne_eq, Nat.cast_eq_zero]
        exact (Nat.choose_pos hn).ne'
    · norm_num
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hrightT).mp
  rw [ENNReal.toReal_ofReal (by positivity :
    (0 : ℝ) ≤ (xpm : ℝ) / 1000000)]
  unfold singleBandProductivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]
  have hchoose : 2 * Nat.choose n 2 = n * (n - 1) := by
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hchooseR :
      (2 : ℝ) * (Nat.choose n 2 : ℝ) =
        (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hchoose
  norm_num only [Nat.cast_mul]
  calc
    (xpm : ℝ) / 1000000
        ≤ (d : ℝ) * (c : ℝ) /
            ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := hprodR
    _ = (d : ℝ) * (c : ℝ) / (Nat.choose n 2 : ℝ) * (1 / 2) := by
      rw [← hchooseR]
      field_simp [show (Nat.choose n 2 : ℝ) ≠ 0 by
        exact_mod_cast (Nat.choose_pos hn).ne']

theorem singleHighCap_productive_stream_le_exp
    (n i : ℕ) (hn : 2 ≤ n) (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    ((1 - singleBandProductivity n (singleHighCapLiveGap n i)
          (singleHighCapCoFloor n i)) +
        singleBandProductivity n (singleHighCapLiveGap n i)
          (singleHighCapCoFloor n i) * ((1 : ℝ≥0∞) / 2)) ^
        singleHighCapHorizon n i /
      ((1 : ℝ≥0∞) / 2) ^ singleHighCapK n i ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) := by
  let x := (singleHighCapProductiveXPM i : ℝ) / 1000000
  have hpp1 :
      singleBandProductivity n (singleHighCapLiveGap n i)
          (singleHighCapCoFloor n i) ≤ 1 :=
    singleBandProductivity_le_one_of_sum n hn
      (singleHighCapLiveGap n i) (singleHighCapCoFloor n i)
      (singleHighCap_prodRoom (n := n) (i := i) hnLarge hi)
  have hxpp := singleHighCap_productive_x_le n i hn hnLarge hi
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    dsimp only [x]
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    interval_cases i <;> norm_num [singleHighCapProductiveXPM]
  have hraw := halfClock_div_le_ofReal_exp_quadratic
    (singleBandProductivity n (singleHighCapLiveGap n i)
      (singleHighCapCoFloor n i))
    hpp1 x (singleHighCapHorizon n i) (singleHighCapK n i)
    hx0 hx1 hxpp
  have hexp :
      -((x + x ^ 2 / 2) * (singleHighCapHorizon n i : ℝ)) +
          (singleHighCapK n i : ℝ) * Real.log 2 ≤
        -((n : ℝ) / 200000) := by
    have hlog2 : Real.log 2 ≤ (0.6931471808 : ℝ) :=
      Real.log_two_lt_d9.le
    have hKlog :
        (singleHighCapK n i : ℝ) * Real.log 2 ≤
          (singleHighCapK n i : ℝ) * (0.6931471808 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
    have hHnat := singleHighCapHorizon_lower_pm n i
    have hKnat := singleHighCapK_upper_pm n i hnLarge hi
    have hHlow :
        (singleHighCapTPM i : ℝ) / 10000 * (n : ℝ) ≤
          (singleHighCapHorizon n i : ℝ) := by
      have hHnatR :
          (singleHighCapTPM i : ℝ) * (n : ℝ) ≤
            10000 * (singleHighCapHorizon n i : ℝ) := by
        exact_mod_cast hHnat
      nlinarith
    have hKupper :
        (singleHighCapK n i : ℝ) ≤
          (singleHighCapKUpperPM i : ℝ) / 10000 * (n : ℝ) := by
      have hKnatR :
          10000 * (singleHighCapK n i : ℝ) ≤
            (singleHighCapKUpperPM i : ℝ) * (n : ℝ) := by
        exact_mod_cast hKnat
      nlinarith
    have hKlogUpper :
        (singleHighCapK n i : ℝ) * Real.log 2 ≤
          ((singleHighCapKUpperPM i : ℝ) / 10000 * (n : ℝ)) *
            (0.6931471808 : ℝ) := by
      calc
        (singleHighCapK n i : ℝ) * Real.log 2
            ≤ (singleHighCapK n i : ℝ) * (0.6931471808 : ℝ) := hKlog
        _ ≤ ((singleHighCapKUpperPM i : ℝ) / 10000 * (n : ℝ)) *
            (0.6931471808 : ℝ) := by
          exact mul_le_mul_of_nonneg_right hKupper (by norm_num)
    have hXHlow :
        ((singleHighCapProductiveXPM i : ℝ) / 1000000 +
            ((singleHighCapProductiveXPM i : ℝ) / 1000000) ^ 2 / 2) *
            ((singleHighCapTPM i : ℝ) / 10000 * (n : ℝ)) ≤
          (x + x ^ 2 / 2) * (singleHighCapHorizon n i : ℝ) := by
      dsimp only [x]
      exact mul_le_mul_of_nonneg_left hHlow (by positivity)
    have hnLargeR : (65536 : ℝ) ≤ n := by exact_mod_cast hnLarge
    dsimp only [x] at hXHlow
    dsimp only [x]
    have hi12 : i < 12 := by simpa [singleHighCapBridgeLength] using hi
    calc
      -(((singleHighCapProductiveXPM i : ℝ) / 1000000 +
            ((singleHighCapProductiveXPM i : ℝ) / 1000000) ^ 2 / 2) *
            (singleHighCapHorizon n i : ℝ)) +
          (singleHighCapK n i : ℝ) * Real.log 2
          ≤ -(((singleHighCapProductiveXPM i : ℝ) / 1000000 +
                ((singleHighCapProductiveXPM i : ℝ) / 1000000) ^ 2 / 2) *
                ((singleHighCapTPM i : ℝ) / 10000 * (n : ℝ))) +
              ((singleHighCapKUpperPM i : ℝ) / 10000 * (n : ℝ)) *
                (0.6931471808 : ℝ) := by
            nlinarith
      _ ≤ -((n : ℝ) / 200000) := by
        interval_cases i <;>
          norm_num [singleHighCapProductiveXPM, singleHighCapTPM,
            singleHighCapKUpperPM] <;>
          nlinarith
  exact hraw.trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr hexp))

theorem singleHighCap_return_stream_le_exp
    (n i : ℕ) (hn : 2 ≤ n) (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    (1 + singleHighCapRetEps n i ^ 2 *
          (((singleHighCapQ n i + 1 : ℕ) : ℝ≥0∞) /
            ((n - 1 : ℕ) : ℝ≥0∞))) ^ singleHighCapHorizon n i /
        (1 + singleHighCapRetEps n i) ^ (singleHighCapSret n i + 1) ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) := by
  let T := singleHighCapHorizon n i
  let B := singleHighCapQ n i + 1
  let S := singleHighCapSret n i
  have hraw := singleCoReturn_exp n T S B hn
    ((1 : ℝ) / 1000)
    (by norm_num : (0 : ℝ) ≤ 1 / 1000)
    (by norm_num : (1 : ℝ) / 1000 ≤ 1)
  have hexp :
      (T : ℝ) *
          (((1 : ℝ) / 1000) ^ 2 * (B : ℝ) /
            ((n - 1 : ℕ) : ℝ)) -
          ((S + 1 : ℕ) : ℝ) * ((1 : ℝ) / 1000) / 2 ≤
        -((n : ℝ) / 200000) := by
    have hn1R : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < n - 1)
    have hratio :
        (n : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ 2 := by
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_le_iff₀ hn1R]
      have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      rw [hsub]
      nlinarith
    have hTnat := singleHighCapHorizon_upper_pm n i hnLarge
    have hBnat := singleHighCapBret_upper_pm n i hnLarge hi
    have hSnat := singleHighCapSret_lower_pm n i
    have hTupper :
        (T : ℝ) ≤
          ((singleHighCapTPM i + 1 : ℕ) : ℝ) / 10000 * (n : ℝ) := by
      dsimp only [T]
      have hTnatR :
          10000 * (singleHighCapHorizon n i : ℝ) ≤
            ((singleHighCapTPM i + 1 : ℕ) : ℝ) * (n : ℝ) := by
        exact_mod_cast hTnat
      nlinarith
    have hBupper :
        (B : ℝ) ≤
          (singleHighCapBretUpperPM i : ℝ) / 10000 * (n : ℝ) := by
      dsimp only [B]
      have hBnatR :
          10000 * ((singleHighCapQ n i + 1 : ℕ) : ℝ) ≤
            (singleHighCapBretUpperPM i : ℝ) * (n : ℝ) := by
        exact_mod_cast hBnat
      nlinarith
    have hSlo :
        (singleHighCapSretPM i : ℝ) / 10000 * (n : ℝ) ≤
          ((S + 1 : ℕ) : ℝ) := by
      dsimp only [S]
      have hSnatR :
          (singleHighCapSretPM i : ℝ) * (n : ℝ) ≤
            10000 * ((singleHighCapSret n i + 1 : ℕ) : ℝ) := by
        exact_mod_cast hSnat
      nlinarith
    have hBdiv :
        (B : ℝ) / ((n - 1 : ℕ) : ℝ) ≤
          2 * ((singleHighCapBretUpperPM i : ℝ) / 10000) := by
      calc
        (B : ℝ) / ((n - 1 : ℕ) : ℝ)
            ≤ ((singleHighCapBretUpperPM i : ℝ) / 10000 * (n : ℝ)) /
                ((n - 1 : ℕ) : ℝ) := by
              exact div_le_div_of_nonneg_right hBupper hn1R.le
        _ = ((singleHighCapBretUpperPM i : ℝ) / 10000) *
              ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
              field_simp [hn1R.ne']
        _ ≤ ((singleHighCapBretUpperPM i : ℝ) / 10000) * 2 := by
              exact mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = 2 * ((singleHighCapBretUpperPM i : ℝ) / 10000) := by ring
    have hfactor :
        (((1 : ℝ) / 1000) ^ 2 * (B : ℝ) /
            ((n - 1 : ℕ) : ℝ)) ≤
          ((1 : ℝ) / 1000) ^ 2 *
            (2 * ((singleHighCapBretUpperPM i : ℝ) / 10000)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hBdiv (by norm_num)
    have hfirst :
        (T : ℝ) *
            (((1 : ℝ) / 1000) ^ 2 * (B : ℝ) /
              ((n - 1 : ℕ) : ℝ)) ≤
          (((singleHighCapTPM i + 1 : ℕ) : ℝ) / 10000 * (n : ℝ)) *
            (((1 : ℝ) / 1000) ^ 2 *
              (2 * ((singleHighCapBretUpperPM i : ℝ) / 10000))) := by
      exact mul_le_mul hTupper hfactor (by positivity) (by positivity)
    have hsecond :
        ((singleHighCapSretPM i : ℝ) / 10000 * (n : ℝ)) *
            ((1 : ℝ) / 1000) / 2 ≤
          ((S + 1 : ℕ) : ℝ) * ((1 : ℝ) / 1000) / 2 := by
      nlinarith
    have hcoeffNat := singleHighCap_return_exp_coeff i hi
    have hcoeff :
        2 * (((singleHighCapTPM i + 1 : ℕ) : ℝ)) *
              (singleHighCapBretUpperPM i : ℝ) + 500000000 ≤
            (singleHighCapSretPM i : ℝ) * 5000000 := by
      exact_mod_cast hcoeffNat
    have hcoeffn :
        (2 * (((singleHighCapTPM i + 1 : ℕ) : ℝ)) *
              (singleHighCapBretUpperPM i : ℝ) + 500000000) * (n : ℝ) ≤
            ((singleHighCapSretPM i : ℝ) * 5000000) * (n : ℝ) := by
      exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
    calc
      (T : ℝ) *
          (((1 : ℝ) / 1000) ^ 2 * (B : ℝ) /
            ((n - 1 : ℕ) : ℝ)) -
          ((S + 1 : ℕ) : ℝ) * ((1 : ℝ) / 1000) / 2
          ≤ (((singleHighCapTPM i + 1 : ℕ) : ℝ) / 10000 * (n : ℝ)) *
              (((1 : ℝ) / 1000) ^ 2 *
                (2 * ((singleHighCapBretUpperPM i : ℝ) / 10000))) -
            ((singleHighCapSretPM i : ℝ) / 10000 * (n : ℝ)) *
              ((1 : ℝ) / 1000) / 2 := by
            nlinarith
      _ ≤ -((n : ℝ) / 200000) := by
        nlinarith
  have hraw' :
      (1 + singleHighCapRetEps n i ^ 2 *
            (((singleHighCapQ n i + 1 : ℕ) : ℝ≥0∞) /
              ((n - 1 : ℕ) : ℝ≥0∞))) ^ singleHighCapHorizon n i /
          (1 + singleHighCapRetEps n i) ^ (singleHighCapSret n i + 1) ≤
        ENNReal.ofReal
          (Real.exp ((T : ℝ) *
            (((1 : ℝ) / 1000) ^ 2 * (B : ℝ) /
              ((n - 1 : ℕ) : ℝ)) -
            ((S + 1 : ℕ) : ℝ) * ((1 : ℝ) / 1000) / 2)) := by
    simpa [T, B, S, singleHighCapRetEps] using hraw
  exact hraw'.trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr hexp))

theorem singleHighCapRungError_le_exp
    (n i : ℕ) (hn : 2 ≤ n) (hnLarge : 65536 ≤ n)
    (hi : i < singleHighCapBridgeLength) :
    singleHighCapRungError n i ≤
      8 * ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) := by
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000)))
  have hback : singleHighCapDirW ^ singleHighCapBw n i ≤ e := by
    dsimp only [e]
    exact singleHighCap_backslide_stream_le_exp n i hi
  have hmain :
      singleHighCapDirW ^ singleHighCapLentry n i /
          (singleHighCapDirW ^
              (singleHighCapLexit n i + singleHighCapD n i) *
            singleHighCapDirEta n i ^ singleHighCapM n i) ≤ e := by
    dsimp only [e]
    exact singleHighCap_main_direction_stream_le_exp n i hnLarge hi
  have hprod :
      ((1 - singleBandProductivity n (singleHighCapLiveGap n i)
            (singleHighCapCoFloor n i)) +
          singleBandProductivity n (singleHighCapLiveGap n i)
            (singleHighCapCoFloor n i) * ((1 : ℝ≥0∞) / 2)) ^
          singleHighCapHorizon n i /
        ((1 : ℝ≥0∞) / 2) ^ singleHighCapK n i ≤ e := by
    dsimp only [e]
    exact singleHighCap_productive_stream_le_exp n i hn hnLarge hi
  have hcreate :
      ENNReal.ofReal
          (Real.exp (-((singleHighCapD n i : ℝ) ^ 2 /
            (2 * (singleHighCapH n i : ℝ))))) ≤ e := by
    dsimp only [e]
    exact singleHighCap_creation_stream_le_exp n i hnLarge hi
  have hhigh :
      singleHighCapDirW ^ singleHighCapLentry n i /
          (singleHighCapDirW ^ singleHighCapHi n i *
            singleHighCapDirEta n i ^ singleHighCapMhi n i) ≤ e := by
    dsimp only [e]
    exact singleHighCap_high_direction_stream_le_exp n i hnLarge hi
  have hret :
      (1 + singleHighCapRetEps n i ^ 2 *
            (((singleHighCapQ n i + 1 : ℕ) : ℝ≥0∞) /
              ((n - 1 : ℕ) : ℝ≥0∞))) ^ singleHighCapHorizon n i /
          (1 + singleHighCapRetEps n i) ^ (singleHighCapSret n i + 1) ≤ e := by
    dsimp only [e]
    exact singleHighCap_return_stream_le_exp n i hn hnLarge hi
  dsimp [singleHighCapRungError, singleLateRungError,
    singleLateResolvedClockError, singleLevelPhaseStructuralError, e]
  calc
    (((((singleHighCapDirW ^ singleHighCapBw n i +
          singleHighCapDirW ^ singleHighCapLentry n i /
            (singleHighCapDirW ^
                (singleHighCapLexit n i + singleHighCapD n i) *
              singleHighCapDirEta n i ^ singleHighCapM n i)) +
          (((1 - singleBandProductivity n (singleHighCapLiveGap n i)
                (singleHighCapCoFloor n i)) +
              singleBandProductivity n (singleHighCapLiveGap n i)
                (singleHighCapCoFloor n i) * ((1 : ℝ≥0∞) / 2)) ^
              singleHighCapHorizon n i /
            ((1 : ℝ≥0∞) / 2) ^ singleHighCapK n i +
            ENNReal.ofReal
              (Real.exp (-((singleHighCapD n i : ℝ) ^ 2 /
                (2 * (singleHighCapH n i : ℝ))))))) +
        ENNReal.ofReal
          (Real.exp (-((singleHighCapD n i : ℝ) ^ 2 /
            (2 * (singleHighCapH n i : ℝ)))))) +
        singleHighCapDirW ^ singleHighCapLentry n i /
          (singleHighCapDirW ^ singleHighCapHi n i *
            singleHighCapDirEta n i ^ singleHighCapMhi n i)) +
        ENNReal.ofReal
          (Real.exp (-((singleHighCapD n i : ℝ) ^ 2 /
            (2 * (singleHighCapH n i : ℝ)))))) +
        (1 + singleHighCapRetEps n i ^ 2 *
            (((singleHighCapQ n i + 1 : ℕ) : ℝ≥0∞) /
              ((n - 1 : ℕ) : ℝ≥0∞))) ^ singleHighCapHorizon n i /
          (1 + singleHighCapRetEps n i) ^ (singleHighCapSret n i + 1)
        ≤ ((((((e + e) + (e + e)) + e) + e) + e) + e) := by
          exact add_le_add
            (add_le_add
              (add_le_add
                (add_le_add
                  (add_le_add (add_le_add hback hmain)
                    (add_le_add hprod hcreate))
                  hcreate)
                hhigh)
              hcreate)
            hret
    _ = 8 * e := by ring

theorem singleHighCapBridgeError_le_exp
    (n : ℕ) (hn : 2 ≤ n) (hnLarge : 65536 ≤ n) :
    singleHighCapBridgeError n ≤
      96 * ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) := by
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000)))
  unfold singleHighCapBridgeError
  calc
    (∑ i ∈ Finset.range singleHighCapBridgeLength,
        singleHighCapRungError n i)
        ≤ ∑ _i ∈ Finset.range singleHighCapBridgeLength, 8 * e := by
          gcongr with i hi
          dsimp only [e]
          exact singleHighCapRungError_le_exp n i hn hnLarge
            (by simpa using hi)
    _ = 96 * e := by
      simp [singleHighCapBridgeLength, e]
      ring

theorem singleHighCapBridgeError_le_power
    (n γ : ℕ) (hlog : 100000000 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    singleHighCapBridgeError n ≤
      96 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
  have hn4096 : 4096 ≤ n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  have hnNat : 0 < n := by omega
  have hn : 2 ≤ n := by omega
  have hlog128 : 128 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hnLarge : 65536 ≤ n := by
    have hlog30 : 30 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
    calc
      65536 = 2 ^ 16 := by norm_num
      _ ≤ 2 ^ Nat.log 2 n :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := Nat.pow_log_le_self 2 (by
        intro h0
        rw [h0, Nat.log_zero_right] at hlog30
        omega)
  have hlogn := singleFinal_realLog_le_natLog n hnNat hlog128
  have hS :
      Real.log (n : ℝ) *
          ((1 / 100000000000000 : ℝ) * (γ : ℝ)) ≤
        (n : ℝ) / 200000 := by
    have hsizeR :
        6 * (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ n := by
      exact_mod_cast hsize
    calc
      Real.log (n : ℝ) *
          ((1 / 100000000000000 : ℝ) * (γ : ℝ))
          = (γ : ℝ) * Real.log (n : ℝ) / 100000000000000 := by ring
      _ ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) / 100000000000000 := by
        gcongr
      _ ≤ (n : ℝ) / 200000 := by
        nlinarith
  calc
    singleHighCapBridgeError n
        ≤ 96 * ENNReal.ofReal (Real.exp (-((n : ℝ) / 200000))) :=
      singleHighCapBridgeError_le_exp n hn hnLarge
    _ ≤ 96 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
      gcongr
      exact singleFinal_ofReal_exp_neg_le_inv_rpow n hnNat
        ((n : ℝ) / 200000)
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) hS

theorem singleMiddleHighCapConstLateError_le_power
    (n γ : ℕ) (hlog : 100000000 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    singleMiddleHighCapConstLateError n γ ≤
      786224 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
  let X :=
    (n : ℝ≥0∞)⁻¹ ^ ((1 / 100000000000000 : ℝ) * (γ : ℝ))
  have hn4096 : 4096 ≤ n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  have hn : 2 ≤ n := (by norm_num : 2 ≤ 4096).trans hn4096
  have hm : singleMiddleError n ≤ 785600 * X := by
    simpa only [X] using singleMiddleError_le_power n γ hlog hsize
  have hh : singleHighCapBridgeError n ≤ 96 * X := by
    simpa only [X] using
      singleHighCapBridgeError_le_power n γ hlog hγ hsize
  have hl : singleLateConstDyadicLadderError n γ ≤ 528 * X := by
    simpa only [X] using
      singleLateConstDyadicLadderError_le_power n γ hn hlog hγ hsize
  unfold singleMiddleHighCapConstLateError singleMiddleHighCapError
  calc
    singleMiddleError n + singleHighCapBridgeError n +
        singleLateConstDyadicLadderError n γ
        ≤ 785600 * X + 96 * X + 528 * X := by
          exact add_le_add (add_le_add hm hh) hl
    _ = 786224 * X := by ring

theorem singleConsensusError_le
    (n γ : ℕ) (hlog : 100000000 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    singleConsensusError n γ ≤
      1000000 * (n : ℝ≥0∞)⁻¹ ^
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) := by
  let X :=
    (n : ℝ≥0∞)⁻¹ ^ ((1 / 100000000000000 : ℝ) * (γ : ℝ))
  have hnNat : 0 < n := by
    have := phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hnOne : 1 ≤ n := by omega
  have heCommon :
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 200000000 : ℝ) * (γ : ℝ)) ≤ X := by
    dsimp only [X]
    exact singleInvPower_le_common n γ hnOne (1 / 200000000)
      (by norm_num)
  have hfCommon :
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 64 : ℝ) * (γ : ℝ)) ≤ X := by
    dsimp only [X]
    exact singleInvPower_le_common n γ hnOne (1 / 64)
      (by norm_num)
  have he : singleEarlyLadderError n γ ≤ 2112 * X :=
    (singleEarlyLadderError_le_power n γ hlog hγ).trans (by gcongr)
  have hml :
      singleMiddleHighCapConstLateError n γ ≤ 786224 * X :=
    singleMiddleHighCapConstLateError_le_power n γ hlog hγ hsize
  unfold singleConsensusError
  calc
    singleEarlyLadderError n γ +
        singleMiddleHighCapConstLateError n γ +
        2 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 64 : ℝ) * (γ : ℝ))
        ≤ 2112 * X + 786224 * X + 2 * X := by
          exact add_le_add (add_le_add he hml) (by gcongr)
    _ = 788338 * X := by ring
    _ ≤ 1000000 * X := by
      gcongr
      norm_num

/-- The fixed Single-B middle extension has a linear raw horizon. -/
theorem singleMiddleHorizon_le (n : ℕ) :
    singleMiddleHorizon n ≤ 110000000 * n := by
  unfold singleMiddleHorizon
  have hboot :
      singleWideHorizon n (n / 8) ≤ 1024 * n := by
    rw [singleWideHorizon_linear]
    have hdiv : n / 8 ≤ n := Nat.div_le_self n 8
    omega
  have hmain :
      singleWideHorizon n (singleMiddleQuota n) ≤ 1024 * n := by
    rw [singleWideHorizon_linear]
    unfold singleMiddleQuota
    have hdiv : n / 30 ≤ n := Nat.div_le_self n 30
    omega
  calc
    singleMiddleBootstrapRungs * singleWideHorizon n (n / 8) +
        singleMiddleMainRungs * singleWideHorizon n (singleMiddleQuota n)
        ≤ singleMiddleBootstrapRungs * (1024 * n) +
          singleMiddleMainRungs * (1024 * n) := by
          gcongr
    _ ≤ 110000000 * n := by
      unfold singleMiddleBootstrapRungs singleMiddleMainRungs
      calc
        126 * (1024 * n) + 98074 * (1024 * n)
            = 100556800 * n := by ring
        _ ≤ 110000000 * n := by
          exact Nat.mul_le_mul_right n (by norm_num)

/-- Each high-cap bridge table row has a crude linear raw horizon. -/
theorem singleHighCapHorizon_le_linear
    (n i : ℕ) (hn : 1 ≤ n) :
    singleHighCapHorizon n i ≤ 1000000 * n := by
  unfold singleHighCapHorizon singleHighCapCeilPM
  have hpm : singleHighCapTPM i ≤ 1000000 := by
    unfold singleHighCapTPM
    split <;> norm_num
  have hnum :
      singleHighCapTPM i * n + (singleHighCapPMDen - 1) ≤
        1000000 * n * singleHighCapPMDen := by
    have htail : singleHighCapPMDen - 1 ≤
        (singleHighCapPMDen - 1) * n := by
      simpa using Nat.mul_le_mul_left (singleHighCapPMDen - 1) hn
    calc
      singleHighCapTPM i * n + (singleHighCapPMDen - 1)
          ≤ 1000000 * n + (singleHighCapPMDen - 1) * n := by
            exact Nat.add_le_add (Nat.mul_le_mul_right n hpm) htail
      _ ≤ 1000000 * n * singleHighCapPMDen := by
        unfold singleHighCapPMDen
        omega
  exact (Nat.div_le_iff_le_mul_add_pred (by
    unfold singleHighCapPMDen
    norm_num)).2 (by
      unfold singleHighCapPMDen at hnum ⊢
      omega)

/-- The 12-row high-cap bridge has a crude linear raw horizon. -/
theorem singleHighCapBridgeHorizon_le
    (n : ℕ) (hn : 1 ≤ n) :
    singleHighCapBridgeHorizon n ≤ 12000000 * n := by
  unfold singleHighCapBridgeHorizon
  calc
    (∑ i ∈ Finset.range singleHighCapBridgeLength,
        singleHighCapHorizon n i)
        ≤ ∑ _i ∈ Finset.range singleHighCapBridgeLength,
          1000000 * n := by
          apply Finset.sum_le_sum
          intro i _hi
          exact singleHighCapHorizon_le_linear n i hn
    _ = singleHighCapBridgeLength * (1000000 * n) := by
      simp [Finset.sum_const, Finset.card_range]
    _ = 12000000 * n := by
      unfold singleHighCapBridgeLength
      ring

/-- The relaxed constant-base late ladder has `O(n log n)` raw horizon. -/
theorem singleLateConstDyadicLadderHorizon_le
    (n γ : ℕ) :
    singleLateConstDyadicLadderHorizon n γ ≤
      30000 * n * Nat.log 2 n := by
  have hstages :
      singleLateConstDyadicStages n γ ≤ Nat.log 2 n := by
    unfold singleLateConstDyadicStages
    exact Nat.sub_le_iff_le_add.mpr
      (by
        have h := phase2StageCount_le_log n γ
        omega)
  have hrelaxed :
      singleLateConstRelaxedStageHorizon n ≤ 1000 * n := by
    unfold singleLateConstRelaxedStageHorizon singleLateConstSubHorizon
      singleLateConstStageHorizon singleLateConstStageLength
    calc
      24 * n + 32 * (24 * n) = 792 * n := by ring
      _ ≤ 1000 * n := Nat.mul_le_mul_right n (by norm_num)
  unfold singleLateConstDyadicLadderHorizon
  calc
    singleLateConstDyadicStages n γ *
        singleLateConstRelaxedStageHorizon n
        ≤ Nat.log 2 n * (1000 * n) :=
          Nat.mul_le_mul hstages hrelaxed
    _ = 1000 * n * Nat.log 2 n := by ring
    _ ≤ 30000 * n * Nat.log 2 n := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul_right (n * Nat.log 2 n)
          (by norm_num : 1000 ≤ 30000)

/-- The middle, high-cap, and constant-base late part fits a coarse
`O(n log n)` raw horizon. -/
theorem singleMiddleHighCapConstLateHorizon_le
    (n γ : ℕ) (hlog : 1 ≤ Nat.log 2 n) :
    singleMiddleHighCapConstLateHorizon n γ ≤
      130000000 * n * Nat.log 2 n := by
  have hnOne : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos (by simpa using h)
    subst n
    simp at hlog
  have hm := singleMiddleHorizon_le n
  have hh := singleHighCapBridgeHorizon_le n hnOne
  have hl := singleLateConstDyadicLadderHorizon_le n γ
  unfold singleMiddleHighCapConstLateHorizon singleMiddleHighCapHorizon
  calc
    singleMiddleHorizon n + singleHighCapBridgeHorizon n +
        singleLateConstDyadicLadderHorizon n γ
        ≤ 110000000 * n + 12000000 * n +
          30000 * n * Nat.log 2 n := by omega
    _ ≤ 130000000 * n * Nat.log 2 n := by
      have h1 :
          110000000 * n ≤ 110000000 * n * Nat.log 2 n := by
        simpa using Nat.mul_le_mul_left (110000000 * n) hlog
      have h2 :
          12000000 * n ≤ 12000000 * n * Nat.log 2 n := by
        simpa using Nat.mul_le_mul_left (12000000 * n) hlog
      calc
        110000000 * n + 12000000 * n +
            30000 * n * Nat.log 2 n
            ≤ 110000000 * n * Nat.log 2 n +
              12000000 * n * Nat.log 2 n +
              30000 * n * Nat.log 2 n := by
              exact Nat.add_le_add (Nat.add_le_add h1 h2) le_rfl
        _ = 122030000 * (n * Nat.log 2 n) := by ring
        _ ≤ 130000000 * (n * Nat.log 2 n) :=
          Nat.mul_le_mul_right (n * Nat.log 2 n)
            (by norm_num : 122030000 ≤ 130000000)
        _ = 130000000 * n * Nat.log 2 n := by ring

/-- The final physical co-level block has the expected
`O(γ n log n)` horizon. -/
theorem singleFinalHorizon_le
    (n γ : ℕ) (hlog : 1024 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    singleFinalHorizon n γ ≤
      131072 * γ * n * Nat.log 2 n := by
  unfold singleFinalHorizon singleFinalScale
  have hscale : γ * Nat.log 2 n + 1 ≤
      2 * γ * Nat.log 2 n := by
    have hγlog : 1 ≤ γ * Nat.log 2 n := by
      calc
        1 ≤ 1 * 1024 := by norm_num
        _ ≤ γ * Nat.log 2 n := Nat.mul_le_mul hγ hlog
    calc
      γ * Nat.log 2 n + 1
          ≤ γ * Nat.log 2 n + γ * Nat.log 2 n :=
            Nat.add_le_add_left hγlog _
      _ = 2 * γ * Nat.log 2 n := by ring
  calc
    65536 * n * (γ * Nat.log 2 n + 1)
        ≤ 65536 * n * (2 * γ * Nat.log 2 n) := by
          gcongr
    _ = 131072 * γ * n * Nat.log 2 n := by ring

/-- The complete Single-B consensus route fits the paper's asymptotic
interaction horizon. -/
theorem singleConsensusHorizon_le
    (n γ : ℕ) (hlog : 1024 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    singleConsensusHorizon n γ ≤
      290000000 * γ * n * Nat.log 2 n := by
  have he := singleEarlyLadderHorizon_le n γ
  have hm :=
    singleMiddleHighCapConstLateHorizon_le n γ (hlog.trans' (by norm_num))
  have hf := singleFinalHorizon_le n γ hlog hγ
  unfold singleConsensusHorizon
  calc
    singleEarlyLadderHorizon n γ +
        singleMiddleHighCapConstLateHorizon n γ +
        singleFinalHorizon n γ
        ≤ 42240 * n * Nat.log 2 n +
          130000000 * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by omega
    _ ≤ 42240 * γ * n * Nat.log 2 n +
          130000000 * γ * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by
      gcongr
      · exact Nat.mul_le_mul_left 42240 hγ
      · exact Nat.mul_le_mul_left 130000000 hγ
    _ = 130173312 * (γ * n * Nat.log 2 n) := by ring
    _ ≤ 290000000 * (γ * n * Nat.log 2 n) :=
      Nat.mul_le_mul_right (γ * n * Nat.log 2 n)
        (by norm_num : 130173312 ≤ 290000000)
    _ = 290000000 * γ * n * Nat.log 2 n := by ring

/-! ## Single-B headline closure -/

theorem singleHeadlineCoefficient_clear
    {n γ : ℕ} (hn : 2 ^ 12800000000000000 ≤ n) (hγ : 1 ≤ γ) :
    1000000 * (n : ℝ≥0∞)⁻¹ ^
          ((1 / 100000000000000 : ℝ) * (γ : ℝ)) ≤
      (n : ℝ≥0∞)⁻¹ ^
          ((1 / 200000000000000 : ℝ) * (γ : ℝ)) := by
  have hnOne : 1 ≤ n := by
    have hpowNe : 2 ^ 12800000000000000 ≠ 0 :=
      pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)
    have hnNe : n ≠ 0 := by
      intro hz
      have hle0 : 2 ^ 12800000000000000 ≤ 0 := by
        simpa only [hz] using hn
      exact hpowNe (Nat.eq_zero_of_le_zero hle0)
    exact Nat.one_le_iff_ne_zero.mpr hnNe
  have hnOneE : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hnOne
  have hbase :
      ((2 : ℝ≥0∞) ^ (12800000000000000 : ℕ)) ≤
        (n : ℝ≥0∞) := by
    exact_mod_cast hn
  have hrootEq :
      ((2 : ℝ≥0∞) ^ (12800000000000000 : ℕ)) ^
          ((1 : ℝ) / 200000000000000) =
        (2 : ℝ≥0∞) ^ (64 : ℕ) := by
    rw [← ENNReal.rpow_natCast (2 : ℝ≥0∞) 12800000000000000,
      ← ENNReal.rpow_mul]
    norm_num
  have hroot :
      (2 : ℝ≥0∞) ^ (64 : ℕ) ≤
        (n : ℝ≥0∞) ^ ((1 : ℝ) / 200000000000000) := by
    rw [← hrootEq]
    exact ENNReal.rpow_le_rpow hbase (by norm_num)
  have hmono :
      (n : ℝ≥0∞) ^ ((1 : ℝ) / 200000000000000) ≤
        (n : ℝ≥0∞) ^
          ((1 / 200000000000000 : ℝ) * (γ : ℝ)) := by
    apply ENNReal.rpow_le_rpow_of_exponent_le hnOneE
    have hγR : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
    nlinarith
  have hthreshold :
      3 * (1000000 : ℝ≥0∞) ≤
        (n : ℝ≥0∞) ^
          (((1 / 100000000000000 : ℝ) * (γ : ℝ)) -
            ((1 / 200000000000000 : ℝ) * (γ : ℝ))) := by
    have hclear :
        (3 : ℝ≥0∞) * 1000000 ≤
          (n : ℝ≥0∞) ^
            ((1 / 200000000000000 : ℝ) * (γ : ℝ)) :=
      (by norm_num : (3 : ℝ≥0∞) * 1000000 ≤
          (2 : ℝ≥0∞) ^ (64 : ℕ)) |>.trans (hroot.trans hmono)
    have hexp :
        ((1 / 100000000000000 : ℝ) * (γ : ℝ)) -
            ((1 / 200000000000000 : ℝ) * (γ : ℝ)) =
          ((1 / 200000000000000 : ℝ) * (γ : ℝ)) := by
      ring
    simpa only [hexp] using hclear
  have hthird :=
    inv_rpow_third 1000000
      ((1 / 100000000000000 : ℝ) * (γ : ℝ))
      ((1 / 200000000000000 : ℝ) * (γ : ℝ))
      n (by
        have hγ0 : (0 : ℝ) ≤ γ := by positivity
        nlinarith)
      hnOne hthreshold
  exact hthird.trans (by
    calc
      (1 / 3 : ℝ≥0∞) *
            (n : ℝ≥0∞)⁻¹ ^
              ((1 / 200000000000000 : ℝ) * (γ : ℝ))
          ≤ 1 *
            (n : ℝ≥0∞)⁻¹ ^
              ((1 / 200000000000000 : ℝ) * (γ : ℝ)) := by
        gcongr
        norm_num
      _ = _ := one_mul _)

theorem theorem2_singleB : Theorem2_singleB_statement := by
  refine ⟨290000000, 2 ^ 12800000000000000,
    (1 / 200000000000000 : ℝ),
    (by norm_num), (by norm_num), ?_, ?_⟩
  · have hpow : 2 ^ 2 ≤ 2 ^ 12800000000000000 :=
      pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2)
        (by decide : 2 ≤ 12800000000000000)
    exact (by decide : 3 ≤ 2 ^ 2).trans hpow
  · intro n γ hn0 hγ hsize s₀ hinv hpaper
    have hn : 2 ≤ n := by
      have hpow : 2 ^ 1 ≤ 2 ^ 12800000000000000 :=
        pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2)
          (by decide : 1 ≤ 12800000000000000)
      exact (by norm_num : 2 ≤ 2 ^ 1).trans (hpow.trans hn0)
    have hlog : 100000000 ≤ Nat.log 2 n := by
      have hlogN0 : 12800000000000000 ≤ Nat.log 2 n := by
        apply Nat.le_log_of_pow_le (by norm_num)
        exact hn0
      exact (by decide : 100000000 ≤ 12800000000000000).trans hlogN0
    have hlog1024 : 1024 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
    let s : SingleState n := ⟨s₀, hinv⟩
    have hr :=
      singleConsensus_reaches n γ hn hlog1024 hγ hsize
    have hreach :=
      hr.mono_error (singleConsensusError_le n γ hlog hγ hsize)
    have hH :=
      singleConsensusHorizon_le n γ hlog1024 hγ
    let targetT := 290000000 * γ * n * Nat.log 2 n
    have hpad :=
      hreach.pad_of_absorbing
        (singleStateStep_biXConsensus n hn)
        (targetT - singleConsensusHorizon n γ)
    have htime :
        singleConsensusHorizon n γ +
            (targetT - singleConsensusHorizon n γ) = targetT := by
      exact Nat.add_sub_of_le hH
    rw [htime] at hpad
    have hreachHeadline :=
      hpad.mono_error (singleHeadlineCoefficient_clear hn0 hγ)
    have hs : SingleBEarlyInitial n γ s := by
      rcases hpaper with ⟨_, gap, hgap, hgapSq⟩
      exact ⟨gap, by simpa only [s] using hgap, hgapSq⟩
    have hmass := hreachHeadline s hs
    rw [singleState_nonconsensus_mass_eq n hn targetT s] at hmass
    simpa only [targetT, s] using hmass

end Tri

#print axioms Tri.singleInvPower_le_common
#print axioms Tri.singleEarlyEnvelopeScale_ge_natLog
#print axioms Tri.singleEarlyLadderError_le_power
#print axioms Tri.singleMiddleEnvelopeScale_ge_natLog
#print axioms Tri.singleMiddleError_le_power
#print axioms Tri.singleLateConstDyadicLadderError_le_power
#print axioms Tri.singleMiddleHighCapConstLateError_le_power
#print axioms Tri.singleConsensusError_le
#print axioms Tri.singleMiddleHorizon_le
#print axioms Tri.singleHighCapBridgeHorizon_le
#print axioms Tri.singleLateConstDyadicLadderHorizon_le
#print axioms Tri.singleMiddleHighCapConstLateHorizon_le
#print axioms Tri.singleFinalHorizon_le
#print axioms Tri.singleConsensusHorizon_le
#print axioms Tri.singleHeadlineCoefficient_clear
#print axioms Tri.theorem2_singleB
