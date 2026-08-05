/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBLateLadder

/-!
# Scalar constants for the ordinary-productivity Double-B ladder

This file bounds the four explicit terms exported by `doubleBandRungError`.
The fixed lower boundary has effective gap `⌊n/20⌋`; the dyadic rung at scale
`P` uses `64P` resolution events and a `65536n` raw block.
-/

namespace Tri

open scoped ENNReal

/-- The event-indexed direction term of a dyadic late rung decays
exponentially in its current co-level scale. -/
theorem doubleLateDirectionError_le
    (n s : ℕ) (hlog : 12 ≤ Nat.log 2 n)
    (hq : 32 ≤ phase2Scale n (s + 1)) :
    phase1RungBase (doubleMiddleLower n) (doubleMiddleLowerD n) ^
        doubleLateCheckpointLevel n s /
      (phase1RungBase (doubleMiddleLower n) (doubleMiddleLowerD n) ^
          (doubleLateHi n s - 1) *
        doubleDirectionEta
          (((doubleMiddleLowerD n : ℕ) : ℝ≥0∞) /
            ((doubleMiddleLower n : ℕ) : ℝ≥0∞))
          (phase1RungBase
            (doubleMiddleLower n) (doubleMiddleLowerD n)) ^
              doubleLateResolutions n s) ≤
      ENNReal.ofReal
        (Real.exp
          (-((phase2Scale n s : ℕ) : ℝ) / 80)) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  let g := n / 20
  let P := phase2Scale n s
  let Q := phase2Scale n (s + 1)
  let start := doubleLateCheckpointLevel n s
  let hi := doubleLateHi n s
  let M := doubleLateResolutions n s
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have hP64 : 64 ≤ P := by omega
  have hgLe : g ≤ n := by
    dsimp only [g]
    exact Nat.div_le_self _ _
  have h20g : 20 * g ≤ n := by
    dsimp only [g]
    exact Nat.mul_div_le n 20
  have hgLe : g ≤ n := by omega
  have h20u : n < 20 * g + 20 := by
    dsimp only [g]
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have hng : n ≤ 21 * g := by omega
  have hLower : doubleMiddleLower n = n + g := by
    rfl
  have hLowerD : doubleMiddleLowerD n = n - g := by
    unfold doubleMiddleLowerD doubleMiddleLower
    dsimp only [g]
    omega
  have hstartHi : start ≤ hi - 1 := by
    dsimp only [start, hi, doubleLateCheckpointLevel,
      doubleLateHi]
    dsimp only [P, Q] at hQP
    omega
  have hraw :=
    doubleDirectionError_le_exp n g start hi M
      hnPos hgLe hstartHi
  rw [← hLower, ← hLowerD] at hraw
  have hbound :
      ((((hi - 1 : ℕ) : ℝ) - (start : ℝ)) *
          Real.log (((n + g : ℕ) : ℝ) / (n : ℝ)) -
        (M : ℝ) * (g : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2)) ≤
        -(P : ℝ) / 80 := by
    let D := (hi - 1) - start
    have hDcast :
        (((hi - 1 : ℕ) : ℝ) - (start : ℝ)) = (D : ℝ) := by
      dsimp only [D]
      rw [Nat.cast_sub hstartHi]
    have hDnat : 5 * D ≤ 3 * P := by
      dsimp only [D, start, hi, doubleLateCheckpointLevel,
        doubleLateHi]
      dsimp only [P, Q] at hQP ⊢
      have hQ16 := Nat.div_mul_le_self Q 16
      omega
    have hDR : (D : ℝ) ≤ 3 * (P : ℝ) / 5 := by
      have : (5 : ℝ) * D ≤ 3 * P := by exact_mod_cast hDnat
      nlinarith
    have hratioPos :
        (0 : ℝ) < ((n + g : ℕ) : ℝ) / (n : ℝ) := by
      positivity
    have hlogBase :=
      Real.log_le_sub_one_of_pos hratioPos
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
          3 * (P : ℝ) / 100 := by
      have hm := mul_le_mul hDR hlogUpper hlog0
        (show (0 : ℝ) ≤ 3 * (P : ℝ) / 5 by positivity)
      nlinarith
    have hgLower : (1 : ℝ) / 21 ≤ (g : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnR]
      have hngR : (n : ℝ) ≤ 21 * g := by exact_mod_cast hng
      nlinarith
    have hratioNonneg : (0 : ℝ) ≤ (g : ℝ) / (n : ℝ) := by
      positivity
    have hsq :
        ((1 : ℝ) / 21) ^ 2 ≤ ((g : ℝ) / (n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg ((g : ℝ) / (n : ℝ) - 1 / 21)]
    have hM : (M : ℝ) = 64 * (P : ℝ) := by
      dsimp only [M, doubleLateResolutions, P]
      norm_num
    have hcontract :
        32 * (P : ℝ) / 441 ≤
          (M : ℝ) * (g : ℝ) ^ 2 / (2 * (n : ℝ) ^ 2) := by
      rw [hM]
      calc
        32 * (P : ℝ) / 441 =
            32 * (P : ℝ) * ((1 : ℝ) / 21) ^ 2 := by ring
        _ ≤ 32 * (P : ℝ) * ((g : ℝ) / (n : ℝ)) ^ 2 := by
          gcongr
        _ = 64 * (P : ℝ) * (g : ℝ) ^ 2 /
              (2 * (n : ℝ) ^ 2) := by
          field_simp
          ring
    rw [hDcast]
    have hP0 : (0 : ℝ) ≤ P := by positivity
    nlinarith
  exact hraw.trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr hbound))

/-- The fixed lower-boundary ruin term is exponentially small in the current
dyadic co-level scale. -/
theorem doubleLateSafetyError_le
    (n s : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 1)) :
    (((doubleMiddleLowerR n : ℕ) : ℝ≥0∞) /
        ((doubleMiddleLower n : ℕ) : ℝ≥0∞)) ^
          doubleLateStartGap n s ≤
      ENNReal.ofReal
        (Real.exp
          (-((phase2Scale n s : ℕ) : ℝ) / 80)) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let g := n / 20
  let P := phase2Scale n s
  let Q := phase2Scale n (s + 1)
  let a := doubleMiddleLower n
  let b := doubleMiddleLowerR n
  let k := doubleLateStartGap n s
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have hP_le : P ≤ n / 2 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    · norm_num
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
  have hk : k = 2 * n - P - (n + g) := by
    dsimp only [k, doubleLateStartGap,
      doubleLateCheckpointLevel, doubleMiddleLower, P, g]
  have hbPos : 0 < b := by rw [hb]; omega
  have hba : b ≤ a := by rw [ha, hb]; omega
  have hkLower : 20 * k ≥ 9 * n := by
    rw [hk]
    omega
  have hPk : 11 * P ≤ 80 * k := by omega
  have hdiff : a ≤ 11 * (a - b) := by
    rw [ha, hb]
    omega
  have hcross : P * a ≤ 80 * k * (a - b) := by
    calc
      P * a ≤ P * (11 * (a - b)) :=
        Nat.mul_le_mul_left P hdiff
      _ = (11 * P) * (a - b) := by ring
      _ ≤ (80 * k) * (a - b) :=
        Nat.mul_le_mul_right (a - b) hPk
      _ = 80 * k * (a - b) := by ring
  change ((b : ℝ≥0∞) / (a : ℝ≥0∞)) ^ k ≤
    ENNReal.ofReal (Real.exp (-(P : ℝ) / 80))
  have hE :
      (P : ℝ) / 80 ≤
        (k : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ) := by
    have haR : (0 : ℝ) < a := by
      exact_mod_cast (lt_of_lt_of_le hbPos hba)
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 80) haR]
    have hcross' : P * a ≤ k * (a - b) * 80 := by
      calc
        P * a ≤ 80 * k * (a - b) := hcross
        _ = k * (a - b) * 80 := by ring
    exact_mod_cast hcross'
  have hr := ratio_pow_le_ofReal_exp a b k ((P : ℝ) / 80)
    hbPos hba hE
  simpa only [show (-((P : ℝ) / 80)) = -(P : ℝ) / 80 by ring]
    using hr

/-- The buffered upper-return term of a dyadic late rung is exponentially
small in its next co-level scale. -/
theorem doubleLateReturnError_le
    (n s : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 1)) :
    (((doubleLateReturnB n s : ℕ) : ℝ≥0∞) /
        ((doubleLateReturnLo n s : ℕ) : ℝ≥0∞)) ^
          doubleLateReturnGap n s ≤
      ENNReal.ofReal
        (Real.exp
          (-((phase2Scale n (s + 1) : ℕ) : ℝ) / 32)) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  let P := phase2Scale n s
  let Q := phase2Scale n (s + 1)
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have hP_le : P ≤ n / 2 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    · norm_num
  have h2QP : 2 * Q ≤ P := by
    rw [hQP]
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self P 2
  have h4Q : 4 * Q ≤ n := by
    have h2n : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    omega
  have hQn : Q + 1 ≤ n := by omega
  have hretPos : 0 < doubleLateReturnLo n s := by
    unfold doubleLateReturnLo doubleLateCheckpointLevel
    dsimp only [Q, phase2Scale] at hQP ⊢
    omega
  have hretTop :
      ((doubleLateReturnLo n s : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hretB : doubleLateReturnB n s = Q - 1 := by rfl
  have hretLo : doubleLateReturnLo n s = 2 * n - Q - 1 := by rfl
  have hcrossN : 2 * (Q - 1) ≤ 2 * n - Q - 1 := by omega
  have hbase :
      (((doubleLateReturnB n s : ℕ) : ℝ≥0∞) /
          ((doubleLateReturnLo n s : ℕ) : ℝ≥0∞)) ≤
        (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.div_le_iff (by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega) hretTop]
    rw [hretB, hretLo]
    have hcross :
        (2 : ℝ≥0∞) * (((Q - 1 : ℕ) : ℝ≥0∞)) ≤
          (((2 * n - Q - 1 : ℕ) : ℝ≥0∞)) := by
      exact_mod_cast hcrossN
    calc
      (((Q - 1 : ℕ) : ℝ≥0∞)) =
          (1 / 2 : ℝ≥0∞) *
            (2 * (((Q - 1 : ℕ) : ℝ≥0∞))) := by
        rw [← mul_assoc]
        rw [one_div, mul_comm (2 : ℝ≥0∞)⁻¹ 2,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ (1 / 2 : ℝ≥0∞) *
          (((2 * n - Q - 1 : ℕ) : ℝ≥0∞)) := by
        gcongr
  let k := doubleLateReturnGap n s
  have hpow :
      (((doubleLateReturnB n s : ℕ) : ℝ≥0∞) /
          ((doubleLateReturnLo n s : ℕ) : ℝ≥0∞)) ^ k ≤
        ((1 : ℝ≥0∞) / 2) ^ k :=
    pow_le_pow_left' hbase k
  have hk : Q / 16 + 1 = k := by
    rfl
  have hkR : (Q : ℝ) / 16 ≤ (k : ℝ) := by
    have hdiv : Q < 16 * (Q / 16 + 1) := by
      have hd := Nat.div_add_mod Q 16
      have hm := Nat.mod_lt Q (by norm_num : 0 < 16)
      omega
    have hdivR :
        (Q : ℝ) < 16 * ((Q / 16 + 1 : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    rw [← hk]
    nlinarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 :=
    (by norm_num : (1 : ℝ) / 2 < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hreal :
      (1 / 2 : ℝ) ^ k ≤ Real.exp (-(Q : ℝ) / 32) := by
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
    (((doubleLateReturnB n s : ℕ) : ℝ≥0∞) /
          ((doubleLateReturnLo n s : ℕ) : ℝ≥0∞)) ^
        doubleLateReturnGap n s
        ≤ ((1 : ℝ≥0∞) / 2) ^ k := by
      simpa only [k] using hpow
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
      have hhalf :
          (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hhalf, ENNReal.ofReal_pow]
      positivity
    _ ≤ ENNReal.ofReal (Real.exp (-(Q : ℝ) / 32)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal
        (Real.exp
          (-((phase2Scale n (s + 1) : ℕ) : ℝ) / 32)) := by
      rfl

/-- The level-productivity floor of a late rung dominates
`2 · (Q/(128n))`, where `Q` is its next co-level scale. -/
theorem doubleLateProductivity_ge
    (n s : ℕ) (hn : 2 ≤ n)
    (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 1)) :
    2 * ENNReal.ofReal
        (((phase2Scale n (s + 1) : ℕ) : ℝ) /
          (128 * (n : ℝ))) ≤
      doubleBandProductivity n (doubleMiddleLower n)
        (doubleLateHi n s) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let g := n / 20
  let P := phase2Scale n s
  let Q := phase2Scale n (s + 1)
  let A :=
    (doubleMiddleLower n + 1 - n) *
      (2 * n - (doubleLateHi n s - 1))
  let B := 2 * Nat.choose n 2
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have hP_le : P ≤ n / 2 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    · norm_num
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
      2 * n - (doubleLateHi n s - 1) =
        Q - Q / 16 + 1 := by
    dsimp only [doubleLateHi, doubleLateCheckpointLevel]
    dsimp only [Q]
    omega
  have hA :
      A = (g + 1) * (Q - Q / 16 + 1) := by
    dsimp only [A]
    rw [hfactorLo, hfactorHi]
  have hB : B = n * (n - 1) := by
    dsimp only [B]
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hco : Q ≤ 2 * (Q - Q / 16 + 1) := by
    have hdiv := Nat.div_mul_le_self Q 16
    omega
  have hn1 : n - 1 ≤ 21 * (g + 1) := by omega
  have hcrossSmall :
      Q * (n - 1) ≤
        64 * ((g + 1) * (Q - Q / 16 + 1)) := by
    calc
      Q * (n - 1) ≤ Q * (21 * (g + 1)) :=
        Nat.mul_le_mul_left Q hn1
      _ = 21 * (Q * (g + 1)) := by ring
      _ ≤ 32 * (Q * (g + 1)) := by
        exact Nat.mul_le_mul_right (Q * (g + 1)) (by norm_num)
      _ = (32 * Q) * (g + 1) := by ring
      _ ≤ (64 * (Q - Q / 16 + 1)) * (g + 1) := by
        apply Nat.mul_le_mul_right
        have := Nat.mul_le_mul_left 32 hco
        omega
      _ = 64 * ((g + 1) * (Q - Q / 16 + 1)) := by ring
  have hcross :
      Q * B ≤ (64 * n) * A := by
    rw [hA, hB]
    calc
      Q * (n * (n - 1)) = n * (Q * (n - 1)) := by ring
      _ ≤ n * (64 * ((g + 1) * (Q - Q / 16 + 1))) :=
        Nat.mul_le_mul_left n hcrossSmall
      _ = (64 * n) * ((g + 1) * (Q - Q / 16 + 1)) := by ring
  have hleftTop :
      2 * ENNReal.ofReal
        ((Q : ℝ) / (128 * (n : ℝ))) ≠ ⊤ := by
    finiteness
  have hrightTop :
      doubleBandProductivity n (doubleMiddleLower n)
        (doubleLateHi n s) ≠ ⊤ := by
    unfold doubleBandProductivity
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]
      exact not_or_intro (by norm_num)
        (Nat.choose_pos hn).ne'
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  unfold doubleBandProductivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofNat, ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  change
    2 * ((Q : ℝ) / (128 * (n : ℝ))) ≤
      (A : ℝ) / (B : ℝ)
  have hBR : (0 : ℝ) < B := by
    rw [hB]
    exact_mod_cast
      (Nat.mul_pos hnPos (by omega : 0 < n - 1))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hleftEq :
      2 * ((Q : ℝ) / (128 * (n : ℝ))) =
        (Q : ℝ) / (64 * (n : ℝ)) := by
    field_simp
    ring
  rw [hleftEq]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 64 * n) hBR]
  have hcrossR : (Q : ℝ) * B ≤ (64 * n : ℕ) * A := by
    exact_mod_cast hcross
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcrossR ⊢
  calc
    (Q : ℝ) * B ≤ (64 * n : ℝ) * A := hcrossR
    _ = A * (64 * n : ℝ) := by ring

/-- The ordinary-productivity clock term of a late rung is exponentially
small in its current co-level scale. -/
theorem doubleLateClockError_le
    (n : ℕ) (hn : 2 ≤ n) (s : ℕ)
    (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 1)) :
    let pp :=
      doubleBandProductivity n (doubleMiddleLower n)
        (doubleLateHi n s)
    let pp' := 1 - pp
    (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ doubleLateHorizon n /
        ((1 : ℝ≥0∞) / 2) ^
          ((2 * n - doubleLateCheckpointLevel n s) +
            3 * doubleLateResolutions n s) ≤
      ENNReal.ofReal
        (Real.exp (-((phase2Scale n s : ℕ) : ℝ))) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  let P := phase2Scale n s
  let Q := phase2Scale n (s + 1)
  let pp :=
    doubleBandProductivity n (doubleMiddleLower n)
      (doubleLateHi n s)
  let pp' := 1 - pp
  let x := pp * ((1 : ℝ≥0∞) / 2)
  let δ : ℝ := (Q : ℝ) / (128 * (n : ℝ))
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  let T := doubleLateHorizon n
  let E :=
    (2 * n - doubleLateCheckpointLevel n s) +
      3 * doubleLateResolutions n s
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have hP64 : 64 ≤ P := by omega
  have hP_le : P ≤ n / 2 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    · norm_num
  have hQn : Q ≤ n := by omega
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by positivity : (0 : ℝ) < 128 * n)]
    exact_mod_cast (show Q ≤ 128 * n by omega)
  have hwidth :
      doubleMiddleLower n + 2 ≤ doubleLateHi n s := by
    unfold doubleMiddleLower doubleLateHi doubleLateCheckpointLevel
    omega
  have hhi : doubleLateHi n s ≤ 2 * n := by
    unfold doubleLateHi doubleLateCheckpointLevel
    have := Nat.div_le_self Q 16
    omega
  have hnLo : n ≤ doubleMiddleLower n + 1 := by
    unfold doubleMiddleLower
    omega
  have hpp1 : pp ≤ 1 := by
    exact doubleBandProductivity_le_one n hn
      (doubleMiddleLower n) (doubleLateHi n s)
      hnLo hwidth hhi
  have hppsum : pp + pp' = 1 := by
    exact doubleBandProductivity_add_compl n hn
      (doubleMiddleLower n) (doubleLateHi n s)
      hnLo hwidth hhi
  have h2δ : 2 * δe ≤ pp := by
    simpa only [δe, δ, Q, pp] using
      doubleLateProductivity_ge n s hn hlog hs hq
  have hhalfCancel :
      (2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2) = 1 := by
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hδx : δe ≤ x := by
    calc
      δe = δe * 1 := by rw [mul_one]
      _ = δe * (2 * ((1 : ℝ≥0∞) / 2)) := by rw [hhalfCancel]
      _ = (2 * δe) * ((1 : ℝ≥0∞) / 2) := by ring
      _ ≤ pp * ((1 : ℝ≥0∞) / 2) := by
        gcongr
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
      _ = pp := by
        rw [hhalfAdd, mul_one]
  have hphiSum : (pp' + x) + δe ≤ 1 := by
    calc
      (pp' + x) + δe ≤ (pp' + x) + x :=
        by
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
    rw [hhalf, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
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
  have hE : E = 193 * P := by
    dsimp only [E, doubleLateCheckpointLevel,
      doubleLateResolutions, P]
    omega
  have hT : (T : ℝ) = 65536 * (n : ℝ) := by
    dsimp only [T, doubleLateHorizon]
    norm_num
  have hδT : δ * (T : ℝ) = 512 * (Q : ℝ) := by
    rw [hT]
    dsimp only [δ]
    field_simp
    ring
  have hlog2 : Real.log 2 ≤ (0.6931471808 : ℝ) :=
    Real.log_two_lt_d9.le
  have hPQR : (P : ℝ) ≤ 2 * (Q : ℝ) + 1 := by
    have : P ≤ 2 * Q + 1 := by
      rw [hQP]
      omega
    exact_mod_cast this
  have hP64R : (64 : ℝ) ≤ P := by exact_mod_cast hP64
  have hexponent :
      -(δ * (T : ℝ)) + (E : ℝ) * Real.log 2 ≤ -(P : ℝ) := by
    rw [hδT, hE]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hP0 : (0 : ℝ) ≤ P := by positivity
    have hscaledLog :
        (193 * (P : ℝ)) * Real.log 2 ≤
          (193 * (P : ℝ)) * 0.6931471808 :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    nlinarith
  change (pp' + x) ^ T / half ^ E ≤ _
  exact hdiv.trans (hquot.le.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)))

/-- The upper-return term also fits the current-scale exponential envelope. -/
theorem doubleLateReturnError_le_current
    (n s : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 1)) :
    (((doubleLateReturnB n s : ℕ) : ℝ≥0∞) /
        ((doubleLateReturnLo n s : ℕ) : ℝ≥0∞)) ^
          doubleLateReturnGap n s ≤
      ENNReal.ofReal
        (Real.exp
          (-((phase2Scale n s : ℕ) : ℝ) / 80)) := by
  let P := phase2Scale n s
  let Q := phase2Scale n (s + 1)
  have hret := doubleLateReturnError_le n s hlog hs hq
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have hPQ : P ≤ 2 * Q + 1 := by
    rw [hQP]
    omega
  have hcompare : -(Q : ℝ) / 32 ≤ -(P : ℝ) / 80 := by
    have hPQR : (P : ℝ) ≤ 2 * Q + 1 := by exact_mod_cast hPQ
    have hQR : (32 : ℝ) ≤ Q := by exact_mod_cast hq
    nlinarith
  exact hret.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hcompare))

/-- All four terms of a late rung fit one current-scale envelope. -/
theorem doubleLateRungError_le
    (n : ℕ) (hn : 2 ≤ n) (s : ℕ)
    (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 1)) :
    doubleLateRungError n s ≤
      4 * ENNReal.ofReal
        (Real.exp
          (-((phase2Scale n s : ℕ) : ℝ) / 80)) := by
  let e :=
    ENNReal.ofReal
      (Real.exp (-((phase2Scale n s : ℕ) : ℝ) / 80))
  have hsafety := doubleLateSafetyError_le n s hlog hs hq
  have hdirection := doubleLateDirectionError_le n s hlog hq
  have hclock := doubleLateClockError_le n hn s hlog hs hq
  have hreturn := doubleLateReturnError_le_current n s hlog hs hq
  have hclockEnvelope :
      (let pp :=
          doubleBandProductivity n (doubleMiddleLower n)
            (doubleLateHi n s)
        let pp' := 1 - pp
        (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ doubleLateHorizon n /
            ((1 : ℝ≥0∞) / 2) ^
              ((2 * n - doubleLateCheckpointLevel n s) +
                3 * doubleLateResolutions n s)) ≤ e := by
    have hP0 : (0 : ℝ) ≤ phase2Scale n s := by positivity
    have hexp :
        -((phase2Scale n s : ℕ) : ℝ) ≤
          -((phase2Scale n s : ℕ) : ℝ) / 80 := by
      nlinarith
    exact hclock.trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))
  have hstart :
      doubleMiddleLower n + doubleLateStartGap n s =
        doubleLateCheckpointLevel n s := by
    have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
    have hP_le : phase2Scale n s ≤ n / 2 := by
      unfold phase2Scale
      apply Nat.div_le_div_left
      · calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
      · norm_num
    unfold doubleLateStartGap doubleLateCheckpointLevel doubleMiddleLower
    omega
  change
    (((((doubleMiddleLowerR n : ℕ) : ℝ≥0∞) /
          ((doubleMiddleLower n : ℕ) : ℝ≥0∞)) ^
            doubleLateStartGap n s +
        phase1RungBase (doubleMiddleLower n) (doubleMiddleLowerD n) ^
              (doubleMiddleLower n + doubleLateStartGap n s) /
            (phase1RungBase
                (doubleMiddleLower n) (doubleMiddleLowerD n) ^
                  (doubleLateHi n s - 1) *
              doubleDirectionEta
                (((doubleMiddleLowerD n : ℕ) : ℝ≥0∞) /
                  ((doubleMiddleLower n : ℕ) : ℝ≥0∞))
                (phase1RungBase
                  (doubleMiddleLower n) (doubleMiddleLowerD n)) ^
                    doubleLateResolutions n s) +
        ((1 -
              doubleBandProductivity n (doubleMiddleLower n)
                (doubleLateHi n s)) +
            doubleBandProductivity n (doubleMiddleLower n)
                (doubleLateHi n s) * ((1 : ℝ≥0∞) / 2)) ^
              doubleLateHorizon n /
            ((1 : ℝ≥0∞) / 2) ^
              ((2 * n -
                  (doubleMiddleLower n + doubleLateStartGap n s)) +
                3 * doubleLateResolutions n s)) +
      (((doubleLateReturnB n s : ℕ) : ℝ≥0∞) /
          ((doubleLateReturnLo n s : ℕ) : ℝ≥0∞)) ^
            doubleLateReturnGap n s) ≤ 4 * e
  rw [hstart]
  calc
    _ ≤ ((e + e) + e) + e := by
      dsimp only [e] at hsafety hdirection hclockEnvelope hreturn ⊢
      gcongr
    _ = 4 * e := by ring

end Tri

#print axioms Tri.doubleLateDirectionError_le
#print axioms Tri.doubleLateSafetyError_le
#print axioms Tri.doubleLateReturnError_le
#print axioms Tri.doubleLateProductivity_ge
#print axioms Tri.doubleLateClockError_le
#print axioms Tri.doubleLateReturnError_le_current
#print axioms Tri.doubleLateRungError_le
