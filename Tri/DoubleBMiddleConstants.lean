/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBLateBudget

/-!
# Scalar constants for the Double-B middle rung

The middle rung starts at a fixed `n/10` effective gap and reaches half
co-level.  Every explicit error term is exponentially small in `n`.
-/

namespace Tri

open scoped ENNReal

/-- The lower-boundary ruin term of the middle rung is exponentially small. -/
theorem doubleMiddleSafetyError_le
    (n : ℕ) (hlog : 12 ≤ Nat.log 2 n) :
    (((doubleMiddleLowerR n : ℕ) : ℝ≥0∞) /
        ((doubleMiddleLower n : ℕ) : ℝ≥0∞)) ^
          doubleMiddleStartGap n ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  let g := n / 20
  let a := doubleMiddleLower n
  let b := doubleMiddleLowerR n
  let k := doubleMiddleStartGap n
  have h20g : 20 * g ≤ n := by
    dsimp only [g]
    exact Nat.mul_div_le n 20
  have h20u : n < 20 * g + 20 := by
    dsimp only [g]
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have hng : n ≤ 21 * g := by omega
  have ha : a = n + g := by rfl
  have hb : b = n - g - 2 := by
    dsimp only [b, doubleMiddleLowerR, doubleMiddleLower, g]
    omega
  have hk : k = g := by rfl
  have hbPos : 0 < b := by rw [hb]; omega
  have hba : b ≤ a := by rw [ha, hb]; omega
  have hdiff : a ≤ 11 * (a - b) := by
    rw [ha, hb]
    omega
  have hnk : n ≤ 21 * k := by rw [hk]; exact hng
  have hcross : n * a ≤ 231 * k * (a - b) := by
    calc
      n * a ≤ (21 * k) * a := Nat.mul_le_mul_right a hnk
      _ ≤ (21 * k) * (11 * (a - b)) :=
        Nat.mul_le_mul_left (21 * k) hdiff
      _ = 231 * k * (a - b) := by ring
  change ((b : ℝ≥0∞) / (a : ℝ≥0∞)) ^ k ≤
    ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000))
  have hE :
      (n : ℝ) / 1000 ≤
        (k : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ) := by
    have haR : (0 : ℝ) < a := by
      exact_mod_cast (lt_of_lt_of_le hbPos hba)
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1000) haR]
    have hcross' : n * a ≤ k * (a - b) * 1000 := by
      calc
        n * a ≤ 231 * k * (a - b) := hcross
        _ ≤ 1000 * k * (a - b) := by
          have hcoef : 231 ≤ 1000 := by norm_num
          simpa only [mul_assoc] using
            Nat.mul_le_mul_right (k * (a - b)) hcoef
        _ = k * (a - b) * 1000 := by ring
    exact_mod_cast hcross'
  simpa only [show (-((n : ℝ) / 1000)) = -(n : ℝ) / 1000 by ring]
    using ratio_pow_le_ofReal_exp a b k ((n : ℝ) / 1000)
      hbPos hba hE

/-- The event-indexed direction term of the middle rung is exponentially
small in `n`. -/
theorem doubleMiddleDirectionError_le
    (n : ℕ) (hlog : 12 ≤ Nat.log 2 n) :
    phase1RungBase (doubleMiddleLower n) (doubleMiddleLowerD n) ^
        (doubleMiddleLower n + doubleMiddleStartGap n) /
      (phase1RungBase (doubleMiddleLower n) (doubleMiddleLowerD n) ^
          (doubleMiddleHi n - 1) *
        doubleDirectionEta
          (((doubleMiddleLowerD n : ℕ) : ℝ≥0∞) /
            ((doubleMiddleLower n : ℕ) : ℝ≥0∞))
          (phase1RungBase
            (doubleMiddleLower n) (doubleMiddleLowerD n)) ^
              doubleMiddleResolutions n) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  let g := n / 20
  let start := doubleMiddleLower n + doubleMiddleStartGap n
  let hi := doubleMiddleHi n
  let M := doubleMiddleResolutions n
  have hgLe : g ≤ n := by
    dsimp only [g]
    exact Nat.div_le_self _ _
  have h20g : 20 * g ≤ n := by
    dsimp only [g]
    exact Nat.mul_div_le n 20
  have h20u : n < 20 * g + 20 := by
    dsimp only [g]
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have hng : n ≤ 21 * g := by omega
  have hLower : doubleMiddleLower n = n + g := by rfl
  have hLowerD : doubleMiddleLowerD n = n - g := by
    unfold doubleMiddleLowerD doubleMiddleLower
    dsimp only [g]
    omega
  have hstartHi : start ≤ hi - 1 := by
    dsimp only [start, hi, doubleMiddleLower, doubleMiddleStartGap,
      doubleMiddleHi, doubleMiddleTarget, g]
    have h2 := Nat.mul_div_le n 2
    have h32 := Nat.mul_div_le n 32
    omega
  have hraw :=
    doubleDirectionError_le_exp n g start hi M
      hnPos hgLe hstartHi
  rw [← hLower, ← hLowerD] at hraw
  have hbound :
      ((((hi - 1 : ℕ) : ℝ) - (start : ℝ)) *
          Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) -
        (M : ℝ) * (g : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2)) ≤
        -(n : ℝ) / 1000 := by
    let D := (hi - 1) - start
    have hDcast :
        (((hi - 1 : ℕ) : ℝ) - (start : ℝ)) = (D : ℝ) := by
      dsimp only [D]
      rw [Nat.cast_sub hstartHi]
    have hDnat : D ≤ n / 2 := by
      dsimp only [D, start, hi, doubleMiddleLower,
        doubleMiddleStartGap, doubleMiddleHi, doubleMiddleTarget, g]
      omega
    have hDR : (D : ℝ) ≤ (n : ℝ) / 2 := by
      have hcast : (D : ℝ) ≤ (n / 2 : ℕ) := by exact_mod_cast hDnat
      have hfloor : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
        have hfloor' :
            ((n / 2 : ℕ) : ℝ) * 2 ≤ (n : ℝ) := by
          exact_mod_cast (Nat.div_mul_le_self n 2)
        nlinarith
      linarith
    have hratioPos :
        (0 : ℝ) < ((n + g : ℕ) : ℝ) / (n : ℝ) := by
      positivity
    have hlogBase := Real.log_le_sub_one_of_pos hratioPos
    have hratioSub :
        ((n + g : ℕ) : ℝ) / (n : ℝ) - 1 =
          (g : ℝ) / (n : ℝ) := by
      push_cast
      field_simp
      ring
    rw [hratioSub] at hlogBase
    have hratioOne :
        (1 : ℝ) ≤ ((n + g : ℕ) : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnR]
      push_cast
      linarith
    have hlog0 :
        0 ≤ Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) :=
      Real.log_nonneg hratioOne
    have hgUpper : (g : ℝ) / (n : ℝ) ≤ 1 / 20 := by
      rw [div_le_iff₀ hnR]
      have h20gR : (20 : ℝ) * g ≤ n := by exact_mod_cast h20g
      nlinarith
    have hlogUpper :
        Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) ≤ 1 / 20 :=
      hlogBase.trans hgUpper
    have hgrowth :
        (D : ℝ) *
            Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) ≤
          (n : ℝ) / 40 := by
      have hm := mul_le_mul hDR hlogUpper hlog0
        (show (0 : ℝ) ≤ (n : ℝ) / 2 by positivity)
      nlinarith
    have hgLower : (1 : ℝ) / 21 ≤ (g : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnR]
      have hngR : (n : ℝ) ≤ 21 * g := by exact_mod_cast hng
      nlinarith
    have hsq :
        ((1 : ℝ) / 21) ^ 2 ≤ ((g : ℝ) / (n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg ((g : ℝ) / (n : ℝ) - 1 / 21)]
    have hM : (M : ℝ) = 64 * (n : ℝ) := by
      dsimp only [M, doubleMiddleResolutions]
      norm_num
    have hcontract :
        32 * (n : ℝ) / 441 ≤
          (M : ℝ) * (g : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2) := by
      rw [hM]
      calc
        32 * (n : ℝ) / 441 =
            32 * (n : ℝ) * ((1 : ℝ) / 21) ^ 2 := by ring
        _ ≤ 32 * (n : ℝ) * ((g : ℝ) / (n : ℝ)) ^ 2 := by
          gcongr
        _ = 64 * (n : ℝ) * (g : ℝ) ^ 2 /
              (2 * (n : ℝ) ^ 2) := by
          field_simp
          ring
    rw [hDcast]
    nlinarith
  exact hraw.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hbound))

/-- The buffered upper-return term of the middle rung is exponentially
small in `n`. -/
theorem doubleMiddleReturnError_le
    (n : ℕ) (hlog : 12 ≤ Nat.log 2 n) :
    (((doubleMiddleReturnB n : ℕ) : ℝ≥0∞) /
        ((doubleMiddleReturnLo n : ℕ) : ℝ≥0∞)) ^
          doubleMiddleReturnGap n ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hretPos : 0 < doubleMiddleReturnLo n := by
    unfold doubleMiddleReturnLo doubleMiddleTarget
    omega
  have hretTop :
      ((doubleMiddleReturnLo n : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hcrossN :
      2 * doubleMiddleReturnB n ≤ doubleMiddleReturnLo n := by
    unfold doubleMiddleReturnB doubleMiddleReturnLo doubleMiddleTarget
    omega
  have hbase :
      (((doubleMiddleReturnB n : ℕ) : ℝ≥0∞) /
          ((doubleMiddleReturnLo n : ℕ) : ℝ≥0∞)) ≤
        (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.div_le_iff (by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega) hretTop]
    have hcross :
        (2 : ℝ≥0∞) * (doubleMiddleReturnB n : ℝ≥0∞) ≤
          (doubleMiddleReturnLo n : ℝ≥0∞) := by
      exact_mod_cast hcrossN
    calc
      (doubleMiddleReturnB n : ℝ≥0∞) =
          (1 / 2 : ℝ≥0∞) *
            (2 * (doubleMiddleReturnB n : ℝ≥0∞)) := by
        rw [← mul_assoc]
        rw [one_div, mul_comm (2 : ℝ≥0∞)⁻¹ 2,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ (1 / 2 : ℝ≥0∞) *
          (doubleMiddleReturnLo n : ℝ≥0∞) := by
        gcongr
  let k := doubleMiddleReturnGap n
  have hpow :
      (((doubleMiddleReturnB n : ℕ) : ℝ≥0∞) /
          ((doubleMiddleReturnLo n : ℕ) : ℝ≥0∞)) ^ k ≤
        ((1 : ℝ≥0∞) / 2) ^ k :=
    pow_le_pow_left' hbase k
  have hkR : (n : ℝ) / 32 ≤ (k : ℝ) := by
    dsimp only [k, doubleMiddleReturnGap]
    have hdiv : n < 32 * (n / 32 + 1) := by
      have hd := Nat.div_add_mod n 32
      have hm := Nat.mod_lt n (by norm_num : 0 < 32)
      omega
    have hdivR :
        (n : ℝ) < 32 * ((n / 32 + 1 : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    nlinarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 :=
    (by norm_num : (1 : ℝ) / 2 < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hreal :
      (1 / 2 : ℝ) ^ k ≤ Real.exp (-(n : ℝ) / 1000) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ k)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hlogHalf]
    have hprod :=
      mul_le_mul hkR hlog2
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by positivity : (0 : ℝ) ≤ (k : ℝ))
    nlinarith
  calc
    (((doubleMiddleReturnB n : ℕ) : ℝ≥0∞) /
          ((doubleMiddleReturnLo n : ℕ) : ℝ≥0∞)) ^
        doubleMiddleReturnGap n
        ≤ ((1 : ℝ≥0∞) / 2) ^ k := by
      simpa only [k] using hpow
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
      have hhalf :
          (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hhalf, ENNReal.ofReal_pow]
      positivity
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) :=
      ENNReal.ofReal_le_ofReal hreal

/-- The middle-band productivity floor is at least `1/64`. -/
theorem doubleMiddleProductivity_ge
    (n : ℕ) (hn : 2 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    2 * ENNReal.ofReal ((1 : ℝ) / 128) ≤
      doubleBandProductivity n (doubleMiddleLower n)
        (doubleMiddleHi n) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let g := n / 20
  let H := n / 2 - n / 32 + 1
  let A :=
    (doubleMiddleLower n + 1 - n) *
      (2 * n - (doubleMiddleHi n - 1))
  let B := 2 * Nat.choose n 2
  have h20g : 20 * g ≤ n := by
    dsimp only [g]
    exact Nat.mul_div_le n 20
  have h20u : n < 20 * g + 20 := by
    dsimp only [g]
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have hng : n ≤ 21 * g := by omega
  have hfactorLo :
      doubleMiddleLower n + 1 - n = g + 1 := by
    dsimp only [doubleMiddleLower, g]
    omega
  have hfactorHi :
      2 * n - (doubleMiddleHi n - 1) = H := by
    dsimp only [doubleMiddleHi, doubleMiddleTarget, H]
    omega
  have hA : A = (g + 1) * H := by
    dsimp only [A]
    rw [hfactorLo, hfactorHi]
  have hB : B = n * (n - 1) := by
    dsimp only [B]
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have h2u : n < 2 * (n / 2) + 2 := by
    have hd := Nat.div_add_mod n 2
    have hm := Nat.mod_lt n (by norm_num : 0 < 2)
    omega
  have h32 := Nat.mul_div_le n 32
  have hnH : n ≤ 3 * H := by
    dsimp only [H]
    omega
  have hn1 : n - 1 ≤ 21 * (g + 1) := by omega
  have hcross : B ≤ 64 * A := by
    rw [hA, hB]
    calc
      n * (n - 1) ≤ (3 * H) * (21 * (g + 1)) :=
        Nat.mul_le_mul hnH hn1
      _ = 63 * ((g + 1) * H) := by ring
      _ ≤ 64 * ((g + 1) * H) := by
        exact Nat.mul_le_mul_right ((g + 1) * H) (by norm_num)
  have hleftTop :
      2 * ENNReal.ofReal ((1 : ℝ) / 128) ≠ ⊤ := by
    finiteness
  have hrightTop :
      doubleBandProductivity n (doubleMiddleLower n)
        (doubleMiddleHi n) ≠ ⊤ := by
    unfold doubleBandProductivity
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]
      exact not_or_intro (by norm_num)
        (Nat.choose_pos hn).ne'
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  unfold doubleBandProductivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofNat, ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  change (1 : ℝ) / 64 ≤ (A : ℝ) / (B : ℝ)
  have hBR : (0 : ℝ) < B := by
    rw [hB]
    exact_mod_cast Nat.mul_pos hnPos (by omega : 0 < n - 1)
  have hcrossR : (B : ℝ) ≤ 64 * (A : ℝ) := by
    exact_mod_cast hcross
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 64) hBR]
  nlinarith

/-- The ordinary-productivity clock term of the middle rung is exponentially
small in `n`. -/
theorem doubleMiddleClockError_le
    (n : ℕ) (hn : 2 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    let pp :=
      doubleBandProductivity n (doubleMiddleLower n)
        (doubleMiddleHi n)
    let pp' := 1 - pp
    (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ doubleMiddleHorizon n /
        ((1 : ℝ≥0∞) / 2) ^
          ((2 * n -
              (doubleMiddleLower n + doubleMiddleStartGap n)) +
            3 * doubleMiddleResolutions n) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let pp :=
    doubleBandProductivity n (doubleMiddleLower n)
      (doubleMiddleHi n)
  let pp' := 1 - pp
  let x := pp * ((1 : ℝ≥0∞) / 2)
  let δ : ℝ := 1 / 128
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  let T := doubleMiddleHorizon n
  let E :=
    (2 * n - (doubleMiddleLower n + doubleMiddleStartGap n)) +
      3 * doubleMiddleResolutions n
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    norm_num
  have hg := doubleMiddle_geometry hlog
  have hpp1 : pp ≤ 1 := by
    exact doubleBandProductivity_le_one n hn
      (doubleMiddleLower n) (doubleMiddleHi n)
      hg.2.2.2.2.2.2.2.2.2.1 hg.2.1 hg.2.2.2.2.2.2.2.2.1
  have hppsum : pp + pp' = 1 := by
    exact doubleBandProductivity_add_compl n hn
      (doubleMiddleLower n) (doubleMiddleHi n)
      hg.2.2.2.2.2.2.2.2.2.1 hg.2.1 hg.2.2.2.2.2.2.2.2.1
  have h2δ : 2 * δe ≤ pp := by
    simpa only [δe, δ, pp] using
      doubleMiddleProductivity_ge n hn hlog
  have hhalfCancel :
      (2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2) = 1 := by
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hδx : δe ≤ x := by
    calc
      δe = δe * 1 := by rw [mul_one]
      _ = δe * (2 * ((1 : ℝ≥0∞) / 2)) := by rw [hhalfCancel]
      _ = (2 * δe) * ((1 : ℝ≥0∞) / 2) := by ring
      _ ≤ pp * ((1 : ℝ≥0∞) / 2) := by gcongr
      _ = x := rfl
  have hhalfAdd :
      ((1 : ℝ≥0∞) / 2) + ((1 : ℝ≥0∞) / 2) = 1 := by
    calc
      ((1 : ℝ≥0∞) / 2) + ((1 : ℝ≥0∞) / 2) =
          2 * ((1 : ℝ≥0∞) / 2) := by ring
      _ = 1 := hhalfCancel
  have hxx : x + x = pp := by
    dsimp only [x]
    calc
      pp * ((1 : ℝ≥0∞) / 2) +
          pp * ((1 : ℝ≥0∞) / 2) =
          pp * (((1 : ℝ≥0∞) / 2) + (1 / 2)) := by ring
      _ = pp := by rw [hhalfAdd, mul_one]
  have hphiSum : (pp' + x) + δe ≤ 1 := by
    calc
      (pp' + x) + δe ≤ (pp' + x) + x := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hδx (pp' + x)
      _ = pp' + (x + x) := by ring
      _ = pp' + pp := by rw [hxx]
      _ = 1 := by rw [add_comm, hppsum]
  have hδtop : δe ≠ ⊤ := by
    dsimp only [δe]
    exact ENNReal.ofReal_ne_top
  have hphiSub : pp' + x ≤ 1 - δe :=
    ENNReal.le_sub_of_add_le_right hδtop hphiSum
  have hsub :
      1 - δe = ENNReal.ofReal (1 - δ) := by
    dsimp only [δe]
    rw [ENNReal.ofReal_sub 1 hδ0, ENNReal.ofReal_one]
  have hphi : pp' + x ≤ ENNReal.ofReal (1 - δ) := by
    rwa [← hsub]
  have hnum :
      (pp' + x) ^ T ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) :=
    enn_pow_le_ofReal_exp (pp' + x) δ T hδ0 hδ1 hphi
  let half : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  have hdiv :
      (pp' + x) ^ T / half ^ E ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ E :=
    ENNReal.div_le_div_right hnum _
  have hhalf :
      half = ENNReal.ofReal (1 / 2 : ℝ) := by
    dsimp only [half]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hquot :
      ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ E =
        ENNReal.ofReal
          (Real.exp
            (-(δ * (T : ℝ)) + (E : ℝ) * Real.log 2)) := by
    rw [hhalf, ← ENNReal.ofReal_pow
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← ENNReal.ofReal_div_of_pos
      (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ E)]
    congr 2
    have hhalfReal :
        (1 / 2 : ℝ) ^ E =
          Real.exp (-(E : ℝ) * Real.log 2) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ E),
        Real.log_pow]
      have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hlogHalf]
      congr 1
      ring
    rw [hhalfReal, ← Real.exp_sub]
    congr 1
    ring
  have hT : (T : ℝ) = 65536 * (n : ℝ) := by
    dsimp only [T, doubleMiddleHorizon]
    norm_num
  have hδT : δ * (T : ℝ) = 512 * (n : ℝ) := by
    rw [hT]
    dsimp only [δ]
    ring
  have hENat : E ≤ 194 * n := by
    dsimp only [E, doubleMiddleLower, doubleMiddleStartGap,
      doubleMiddleResolutions]
    omega
  have hER : (E : ℝ) ≤ 194 * (n : ℝ) := by
    exact_mod_cast hENat
  have hlog2 : Real.log 2 ≤ (0.6931471808 : ℝ) :=
    Real.log_two_lt_d9.le
  have hE0 : (0 : ℝ) ≤ E := by positivity
  have hscaledE :
      (E : ℝ) * Real.log 2 ≤
        (194 * (n : ℝ)) * 0.6931471808 := by
    calc
      (E : ℝ) * Real.log 2 ≤ (E : ℝ) * 0.6931471808 :=
        mul_le_mul_of_nonneg_left hlog2 hE0
      _ ≤ (194 * (n : ℝ)) * 0.6931471808 := by gcongr
  have hexponent :
      -(δ * (T : ℝ)) + (E : ℝ) * Real.log 2 ≤ -(n : ℝ) := by
    rw [hδT]
    nlinarith
  change (pp' + x) ^ T / half ^ E ≤ _
  exact hdiv.trans (hquot.le.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)))

/-- All four terms of the middle rung fit one exponential envelope. -/
theorem doubleMiddleError_le
    (n : ℕ) (hn : 2 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    doubleMiddleError n ≤
      4 * ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) := by
  let e := ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000))
  have hsafety := doubleMiddleSafetyError_le n hlog
  have hdirection := doubleMiddleDirectionError_le n hlog
  have hclock := doubleMiddleClockError_le n hn hlog
  have hreturn := doubleMiddleReturnError_le n hlog
  have hclockEnvelope :
      (let pp :=
          doubleBandProductivity n (doubleMiddleLower n)
            (doubleMiddleHi n)
        let pp' := 1 - pp
        (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ doubleMiddleHorizon n /
            ((1 : ℝ≥0∞) / 2) ^
              ((2 * n -
                  (doubleMiddleLower n + doubleMiddleStartGap n)) +
                3 * doubleMiddleResolutions n)) ≤ e := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hexp : -(n : ℝ) ≤ -(n : ℝ) / 1000 := by
      nlinarith
    exact hclock.trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))
  change
    (((((doubleMiddleLowerR n : ℕ) : ℝ≥0∞) /
          ((doubleMiddleLower n : ℕ) : ℝ≥0∞)) ^
            doubleMiddleStartGap n +
        phase1RungBase (doubleMiddleLower n) (doubleMiddleLowerD n) ^
              (doubleMiddleLower n + doubleMiddleStartGap n) /
            (phase1RungBase
                (doubleMiddleLower n) (doubleMiddleLowerD n) ^
                  (doubleMiddleHi n - 1) *
              doubleDirectionEta
                (((doubleMiddleLowerD n : ℕ) : ℝ≥0∞) /
                  ((doubleMiddleLower n : ℕ) : ℝ≥0∞))
                (phase1RungBase
                  (doubleMiddleLower n) (doubleMiddleLowerD n)) ^
                    doubleMiddleResolutions n) +
        ((1 -
              doubleBandProductivity n (doubleMiddleLower n)
                (doubleMiddleHi n)) +
            doubleBandProductivity n (doubleMiddleLower n)
                (doubleMiddleHi n) * ((1 : ℝ≥0∞) / 2)) ^
              doubleMiddleHorizon n /
            ((1 : ℝ≥0∞) / 2) ^
              ((2 * n -
                  (doubleMiddleLower n + doubleMiddleStartGap n)) +
                3 * doubleMiddleResolutions n)) +
      (((doubleMiddleReturnB n : ℕ) : ℝ≥0∞) /
          ((doubleMiddleReturnLo n : ℕ) : ℝ≥0∞)) ^
            doubleMiddleReturnGap n) ≤ 4 * e
  calc
    _ ≤ ((e + e) + e) + e := by
      dsimp only [e] at hsafety hdirection hclockEnvelope hreturn ⊢
      gcongr
    _ = 4 * e := by ring

/-- The exponentially small middle-rung error fits the headline power law. -/
theorem doubleMiddleError_le_power
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    doubleMiddleError n ≤
      4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) := by
  have hnPos : 0 < n := by omega
  have hmiddle :=
    doubleMiddleError_le n hn (hlog.trans' (by norm_num))
  refine hmiddle.trans ?_
  gcongr
  have hrpow :
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) =
        ENNReal.ofReal
          ((n : ℝ) ^ (-((1 / 200 : ℝ) * (γ : ℝ)))) := by
    rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
      ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hnPos),
      ← ENNReal.ofReal_inv_of_pos (by positivity),
      Real.rpow_neg (by positivity)]
  rw [hrpow]
  apply ENNReal.ofReal_le_ofReal
  have hpExp : (0 : ℝ) < Real.exp (-(n : ℝ) / 1000) :=
    Real.exp_pos _
  have hpPow :
      (0 : ℝ) <
        (n : ℝ) ^ (-((1 / 200 : ℝ) * (γ : ℝ))) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hnPos) _
  have hlogIneq :
      Real.log (Real.exp (-(n : ℝ) / 1000)) ≤
        Real.log
          ((n : ℝ) ^ (-((1 / 200 : ℝ) * (γ : ℝ)))) := by
    rw [Real.log_exp, Real.log_rpow (by exact_mod_cast hnPos)]
    have hlog2 : Real.log 2 < (0.6931471808 : ℝ) :=
      Real.log_two_lt_d9
    have hlogn :
        Real.log n ≤
          ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
      have hup : n < 2 ^ (Nat.log 2 n + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) n
      have hlt :
          Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
        Real.log_lt_log (by exact_mod_cast hnPos)
          (by exact_mod_cast hup)
      rw [Real.log_pow] at hlt
      push_cast at hlt
      linarith
    have hL : (128 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hlog
    have hfactor :
        ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤
          (Nat.log 2 n : ℝ) := by
      have hlog2Nonneg : 0 ≤ Real.log 2 :=
        (Real.log_pos (by norm_num)).le
      nlinarith
    have hgammaLog :
        (γ : ℝ) * Real.log n ≤
          (γ : ℝ) * (Nat.log 2 n : ℝ) := by
      apply mul_le_mul_of_nonneg_left (hlogn.trans hfactor)
      positivity
    have hsizeR :
        6 * (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hsize
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogIneq
  rwa [Real.exp_log hpExp, Real.exp_log hpPow] at hexp

end Tri

#print axioms Tri.doubleMiddleSafetyError_le
#print axioms Tri.doubleMiddleDirectionError_le
#print axioms Tri.doubleMiddleReturnError_le
#print axioms Tri.doubleMiddleProductivity_ge
#print axioms Tri.doubleMiddleClockError_le
#print axioms Tri.doubleMiddleError_le
#print axioms Tri.doubleMiddleError_le_power
