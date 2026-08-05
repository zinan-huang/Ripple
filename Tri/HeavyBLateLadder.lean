/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBMiddleConstants
import Tri.Phase2AdditiveBudget

/-!
# The Heavy-B late ladder

Late rungs reuse the fixed Heavy-B direction boundary from
`HeavyBMiddleConstants`.  The public checkpoints are additive co-level
checkpoints; each concrete rung converts them to the level lower bounds
required by `heavyBandRung`.
-/

namespace Tri

open scoped ENNReal

def heavyLateStartLevel (n s : ℕ) : ℕ :=
  n - phase2Scale n (s + 1)

def heavyLateStartK (n s : ℕ) : ℕ :=
  heavyLateStartLevel n s - heavyMiddleLower n

def heavyLateReturnLo (n s : ℕ) : ℕ :=
  n - phase2Scale n (s + 2) - 1

def heavyLateReturnBHi (n s : ℕ) : ℕ :=
  phase2Scale n (s + 2) - 1

def heavyLateReturnK (n s : ℕ) : ℕ :=
  phase2Scale n (s + 2) / 16 + 1

def heavyLateHi (n s : ℕ) : ℕ :=
  n - phase2Scale n (s + 2) + phase2Scale n (s + 2) / 16

def heavyLateThr (n s : ℕ) : ℕ := heavyLateHi n s - 1

def heavyLateResolutions (n s : ℕ) : ℕ :=
  64 * phase2Scale n (s + 1)

def heavyLateHorizon (n : ℕ) : ℕ := 65536 * n

def heavyLateKClock (n s : ℕ) : ℕ :=
  193 * phase2Scale n (s + 1)

def heavyLateProdCo (n s : ℕ) : ℕ :=
  n - heavyLateThr n s

noncomputable def heavyLateRungError (n s : ℕ) : ℝ≥0∞ :=
  heavyBandRungError n (heavyDirA n) (heavyDirB n)
    (heavyMiddleLower n) (heavyMiddleLowerBHi n)
    (heavyLateThr n s) (heavyLateStartK n s)
    (heavyLateResolutions n s) (heavyLateKClock n s)
    (heavyLateHorizon n)
    (heavyLateReturnLo n s) (heavyLateReturnBHi n s)
    (heavyLateReturnK n s)
    (heavyMiddleProdGap n) (heavyLateProdCo n s)

/-! ## Scalar bounds for one late rung -/

theorem heavyLateSafetyError_le
    (n s : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (_hq : 32 ≤ phase2Scale n (s + 2)) :
    (((heavyMiddleLowerBHi n : ℕ) : ℝ≥0∞) /
        ((heavyMiddleLower n : ℕ) : ℝ≥0∞)) ^
          heavyLateStartK n s ≤
      ENNReal.ofReal
        (Real.exp (-((phase2Scale n (s + 1) : ℕ) : ℝ) / 80)) := by
  rcases heavyMiddle_geometry hlog with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hbHiR0, hmajR0,
      _, _, _, _, _, _, _, _, _⟩
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  let P := phase2Scale n (s + 1)
  let Q := phase2Scale n (s + 2)
  let a := heavyMiddleLower n
  let b := heavyMiddleLowerBHi n
  let k := heavyLateStartK n s
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ,
      Nat.div_div_eq_div_mul]
  have hP_le_quarter : P ≤ n / 4 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · norm_num
  have hbPos : 0 < b := by simpa only [b] using hbHiR0
  have hba : b ≤ a := by simpa only [a, b] using hmajR0
  have hstartEq : a + k = n - P := by
    dsimp only [a, k, P, heavyLateStartK, heavyLateStartLevel,
      heavyMiddleLower]
    omega
  have hkLarge : 13 * P ≤ 80 * k := by
    dsimp only [k, P, heavyLateStartK, heavyLateStartLevel,
      heavyMiddleLower]
    omega
  have hdiff : a ≤ 13 * (a - b) := by
    dsimp only [a, b, heavyMiddleLower, heavyMiddleLowerBHi]
    omega
  have hcross : P * a ≤ 80 * k * (a - b) := by
    calc
      P * a ≤ P * (13 * (a - b)) :=
        Nat.mul_le_mul_left P hdiff
      _ = (13 * P) * (a - b) := by ring
      _ ≤ (80 * k) * (a - b) :=
        Nat.mul_le_mul_right (a - b) hkLarge
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
  simpa only [show (-((P : ℝ) / 80)) = -(P : ℝ) / 80 by ring]
    using ratio_pow_le_ofReal_exp a b k ((P : ℝ) / 80)
      hbPos hba hE

theorem heavyLateReturnError_le
    (n s : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 2)) :
    (((heavyLateReturnBHi n s : ℕ) : ℝ≥0∞) /
        ((heavyLateReturnLo n s : ℕ) : ℝ≥0∞)) ^
          heavyLateReturnK n s ≤
      ENNReal.ofReal
        (Real.exp (-((phase2Scale n (s + 1) : ℕ) : ℝ) / 80)) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  let P := phase2Scale n (s + 1)
  let Q := phase2Scale n (s + 2)
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ,
      Nat.div_div_eq_div_mul]
  have hP_le_quarter : P ≤ n / 4 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · norm_num
  have hQn : Q + 1 ≤ n := by omega
  have hretPos : 0 < heavyLateReturnLo n s := by
    unfold heavyLateReturnLo
    dsimp only [Q] at hQn ⊢
    omega
  have hretTop :
      ((heavyLateReturnLo n s : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hcrossN :
      2 * heavyLateReturnBHi n s ≤ heavyLateReturnLo n s := by
    unfold heavyLateReturnBHi heavyLateReturnLo
    dsimp only [Q] at hQn ⊢
    omega
  have hbase :
      (((heavyLateReturnBHi n s : ℕ) : ℝ≥0∞) /
          ((heavyLateReturnLo n s : ℕ) : ℝ≥0∞)) ≤
        (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.div_le_iff (by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact hretPos.ne') hretTop]
    have hcross :
        (2 : ℝ≥0∞) * (heavyLateReturnBHi n s : ℝ≥0∞) ≤
          (heavyLateReturnLo n s : ℝ≥0∞) := by
      exact_mod_cast hcrossN
    calc
      (heavyLateReturnBHi n s : ℝ≥0∞) =
          (1 / 2 : ℝ≥0∞) *
            (2 * (heavyLateReturnBHi n s : ℝ≥0∞)) := by
        rw [← mul_assoc]
        rw [one_div, mul_comm (2 : ℝ≥0∞)⁻¹ 2,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ (1 / 2 : ℝ≥0∞) *
          (heavyLateReturnLo n s : ℝ≥0∞) := by
        gcongr
  let k := heavyLateReturnK n s
  have hpow :
      (((heavyLateReturnBHi n s : ℕ) : ℝ≥0∞) /
          ((heavyLateReturnLo n s : ℕ) : ℝ≥0∞)) ^ k ≤
        ((1 : ℝ≥0∞) / 2) ^ k :=
    pow_le_pow_left' hbase k
  have hkR : (Q : ℝ) / 16 ≤ (k : ℝ) := by
    have hdiv : Q < 16 * (Q / 16 + 1) := by
      have hd := Nat.div_add_mod Q 16
      have hm := Nat.mod_lt Q (by norm_num : 0 < 16)
      omega
    have hdivR : (Q : ℝ) < 16 * ((Q / 16 + 1 : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    dsimp only [k, heavyLateReturnK]
    dsimp only [Q]
    nlinarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 :=
    (by norm_num : (1 : ℝ) / 2 < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hreal :
      (1 / 2 : ℝ) ^ k ≤ Real.exp (-(P : ℝ) / 80) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ k)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hlogHalf]
    have hPQ : P ≤ 2 * Q + 1 := by
      rw [hQP]
      omega
    have hprod :=
      mul_le_mul hkR hlog2
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by positivity : (0 : ℝ) ≤ (k : ℝ))
    have hQR : (32 : ℝ) ≤ Q := by exact_mod_cast hq
    have hPQR : (P : ℝ) ≤ 2 * Q + 1 := by exact_mod_cast hPQ
    nlinarith
  calc
    (((heavyLateReturnBHi n s : ℕ) : ℝ≥0∞) /
          ((heavyLateReturnLo n s : ℕ) : ℝ≥0∞)) ^
        heavyLateReturnK n s
        ≤ ((1 : ℝ≥0∞) / 2) ^ k := by
      simpa only [k] using hpow
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
      have hhalf :
          (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hhalf, ENNReal.ofReal_pow]
      positivity
    _ ≤ ENNReal.ofReal (Real.exp (-(P : ℝ) / 80)) :=
      ENNReal.ofReal_le_ofReal hreal

theorem heavyLateProductivity_ge
    (n s : ℕ) (hn : 3 ≤ n) (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 2)) :
    2 * ENNReal.ofReal
        (((phase2Scale n (s + 2) : ℕ) : ℝ) /
          (128 * (n : ℝ))) ≤
      heavyBandProductivity n (heavyMiddleProdGap n)
        (heavyLateProdCo n s) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let Q := phase2Scale n (s + 2)
  let d := heavyMiddleProdGap n
  let c := heavyLateProdCo n s
  let A := d * c
  let Bc := Nat.choose n 2
  have h2 := Nat.mul_div_le n 2
  have h2u : n < 2 * (n / 2) + 2 := by
    have hd := Nat.div_add_mod n 2
    have hm := Nat.mod_lt n (by norm_num : 0 < 2)
    omega
  have h48 := Nat.mul_div_le n 48
  have h48u : n < 48 * (n / 48) + 48 := by
    have hd := Nat.div_add_mod n 48
    have hm := Nat.mod_lt n (by norm_num : 0 < 48)
    omega
  have hQ16 : Q / 16 ≤ Q := Nat.div_le_self Q 16
  have hdLower : n ≤ 25 * d := by
    change n ≤ 25 * (2 * (n / 2 + n / 48 + 1) - n)
    omega
  have hcLower : Q ≤ 2 * c := by
    have hQ_le_eighth : Q ≤ n / 8 := by
      dsimp only [Q, phase2Scale]
      apply Nat.div_le_div_left
      · calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (s + 2) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      · norm_num
    have hQn : Q + 1 ≤ n := by
      omega
    have hcEq : c = Q - Q / 16 + 1 := by
      dsimp only [c, Q, heavyLateProdCo, heavyLateThr, heavyLateHi]
      omega
    rw [hcEq]
    omega
  have hchoose : 2 * Bc = n * (n - 1) := by
    dsimp only [Bc]
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hcross : Q * Bc ≤ (64 * n) * A := by
    have hsmall : Q * (n - 1) ≤ 64 * A := by
      calc
        Q * (n - 1) ≤ Q * n := Nat.mul_le_mul_left Q (by omega : n - 1 ≤ n)
        _ ≤ (2 * c) * (25 * d) := Nat.mul_le_mul hcLower hdLower
        _ = 50 * (d * c) := by ring
        _ ≤ 64 * A := by
          dsimp only [A]
          exact Nat.mul_le_mul_right (d * c) (by norm_num : 50 ≤ 64)
    have h2cross : 2 * (Q * Bc) ≤ 2 * ((64 * n) * A) := by
      calc
        2 * (Q * Bc) = Q * (2 * Bc) := by ring
        _ = Q * (n * (n - 1)) := by rw [hchoose]
        _ = n * (Q * (n - 1)) := by ring
        _ ≤ n * (64 * A) := Nat.mul_le_mul_left n hsmall
        _ = (64 * n) * A := by ring
        _ ≤ 2 * ((64 * n) * A) := by omega
    exact Nat.le_of_mul_le_mul_left h2cross (by norm_num : 0 < 2)
  have hleftTop :
      2 * ENNReal.ofReal ((Q : ℝ) / (128 * (n : ℝ))) ≠ ⊤ := by
    finiteness
  have hrightTop :
      heavyBandProductivity n d c ≠ ⊤ := by
    unfold heavyBandProductivity
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · simp only [ne_eq, Nat.cast_eq_zero]
      exact (Nat.choose_pos (by omega : 2 ≤ n)).ne'
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  unfold heavyBandProductivity
  dsimp only [Q, d, c, A, Bc]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofNat, ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  change
    2 * ((phase2Scale n (s + 2) : ℝ) / (128 * (n : ℝ))) ≤
      ((heavyMiddleProdGap n * heavyLateProdCo n s : ℕ) : ℝ) /
        ((Nat.choose n 2 : ℕ) : ℝ)
  have hBR : (0 : ℝ) < (Nat.choose n 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hleftEq :
      2 * ((phase2Scale n (s + 2) : ℝ) / (128 * (n : ℝ))) =
        (phase2Scale n (s + 2) : ℝ) / (64 * (n : ℝ)) := by
    field_simp
    ring
  rw [hleftEq]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 64 * n) hBR]
  have hcrossR :
      ((phase2Scale n (s + 2) * Nat.choose n 2 : ℕ) : ℝ) ≤
        (((64 * n) * (heavyMiddleProdGap n * heavyLateProdCo n s) : ℕ) : ℝ) := by
    exact_mod_cast hcross
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcrossR ⊢
  calc
    (phase2Scale n (s + 2) : ℝ) * Nat.choose n 2
        ≤ (64 * n : ℝ) *
            (heavyMiddleProdGap n * heavyLateProdCo n s) := hcrossR
    _ = (heavyMiddleProdGap n * heavyLateProdCo n s : ℝ) *
          (64 * n : ℝ) := by ring

/-- The ordinary-productivity clock term of a Heavy-B late rung is exponentially
small in the current dyadic co-level scale. -/
theorem heavyLateClockError_le
    (n : ℕ) (hn : 3 ≤ n) (s : ℕ)
    (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 2)) :
    let pp := heavyBandProductivity n (heavyMiddleProdGap n)
      (heavyLateProdCo n s)
    let pp' := 1 - pp
    (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ heavyLateHorizon n /
        ((1 : ℝ≥0∞) / 2) ^ heavyLateKClock n s ≤
      ENNReal.ofReal
        (Real.exp (-((phase2Scale n (s + 1) : ℕ) : ℝ))) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let P := phase2Scale n (s + 1)
  let Q := phase2Scale n (s + 2)
  let pp := heavyBandProductivity n (heavyMiddleProdGap n)
    (heavyLateProdCo n s)
  let pp' := 1 - pp
  let x := pp * ((1 : ℝ≥0∞) / 2)
  let δ : ℝ := (Q : ℝ) / (128 * (n : ℝ))
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  let T := heavyLateHorizon n
  let E := heavyLateKClock n s
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ,
      Nat.div_div_eq_div_mul]
  have hqQ : 32 ≤ Q := by simpa only [Q] using hq
  have hP64 : 64 ≤ P := by
    rw [hQP] at hqQ
    omega
  have hP_le_quarter : P ≤ n / 4 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · norm_num
  have hQn : Q + 1 ≤ n := by
    omega
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by positivity : (0 : ℝ) < 128 * n)]
    exact_mod_cast (show Q ≤ 128 * n by omega)
  rcases heavyMiddle_geometry hlog with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hgapProd,
      _, _, _, _, _, _, _, _⟩
  have hwidth :
      heavyMiddleLower n + 1 ≤ heavyLateThr n s := by
    unfold heavyMiddleLower heavyLateThr heavyLateHi
    dsimp only [Q] at hQP hP_le_quarter hq hQn ⊢
    omega
  have hcoProd :
      heavyLateThr n s + heavyLateProdCo n s = n := by
    unfold heavyLateProdCo heavyLateThr heavyLateHi
    dsimp only [Q] at hQn ⊢
    omega
  have hpp1 : pp ≤ 1 := by
    exact heavyBandProductivity_le_one n hn
      (heavyMiddleLower n) (heavyLateThr n s)
      (heavyMiddleProdGap n) (heavyLateProdCo n s)
      hgapProd hcoProd hwidth
  have hppsum : pp + pp' = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hpp1
  have h2δ : 2 * δe ≤ pp := by
    simpa only [δe, δ, Q, pp] using
      heavyLateProductivity_ge n s hn hlog hs hq
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
    dsimp only [E, heavyLateKClock, P]
  have hT : (T : ℝ) = 65536 * (n : ℝ) := by
    dsimp only [T, heavyLateHorizon]
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

set_option maxHeartbeats 2000000 in
-- The Padé direction bound combines fixed Heavy-B floor witnesses with the
-- dyadic-scale deadline algebra, which exceeds the default heartbeat budget.
/-- The Heavy-B late direction term is exponentially small in the current
dyadic co-level scale. -/
theorem heavyLateDirectionError_le
    (n s : ℕ) (hlog : 128 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 2)) :
    let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW (heavyDirA n) (heavyDirB n))
    let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta (heavyDirA n) (heavyDirB n))
    w ^ (heavyMiddleLower n + heavyLateStartK n s) /
      (w ^ heavyLateThr n s * η ^ heavyLateResolutions n s) ≤
      ENNReal.ofReal
        (Real.exp (-((phase2Scale n (s + 1) : ℕ) : ℝ) / 80)) := by
  have hlog12 : 12 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  rcases heavyMiddle_geometry hlog12 with
    ⟨ha, hB, hparam, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _⟩
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog12
  have hnPos : 0 < n := by omega
  let a := heavyDirA n
  let B := heavyDirB n
  let wR := heavyBandW a B
  let ηR := heavyBandEta a B
  let P := phase2Scale n (s + 1)
  let Q := phase2Scale n (s + 2)
  let start := heavyMiddleLower n + heavyLateStartK n s
  let thr := heavyLateThr n s
  let M := heavyLateResolutions n s
  let D := thr - start
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ,
      Nat.div_div_eq_div_mul]
  have hP64 : 64 ≤ P := by
    have hqQ : 32 ≤ Q := by simpa only [Q] using hq
    rw [hQP] at hqQ
    omega
  have hP_le_quarter : P ≤ n / 4 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · norm_num
  have hQn : Q + 1 ≤ n := by
    omega
  have hstartThr : start ≤ thr := by
    have h2 := Nat.mul_div_le n 2
    have h48 := Nat.mul_div_le n 48
    have hstartEq : start = n - P := by
      dsimp only [start, heavyLateStartK, heavyLateStartLevel,
        heavyMiddleLower]
      omega
    have hthrEq : thr = n - Q + Q / 16 - 1 := by
      dsimp only [thr, heavyLateThr, heavyLateHi]
    rw [hstartEq, hthrEq]
    omega
  have hDadd : start + D = thr := by
    dsimp only [D]
    omega
  have hwpos : 0 < wR := by
    obtain ⟨hu, huw, _⟩ := heavyBand_tail_regime (a := a) (B := B)
      (by simpa only [a, B] using ha) (by simpa only [a, B] using hB)
    exact hu.trans huw
  have hw0 : 0 ≤ wR := hwpos.le
  have hηpos : 0 < ηR := heavyBandEta_pos
    (by simpa only [a, B] using ha) (by simpa only [a, B] using hB)
  have hη0 : 0 ≤ ηR := hηpos.le
  have hdenpos : 0 < wR ^ thr * ηR ^ M :=
    mul_pos (pow_pos hwpos _) (pow_pos hηpos _)
  change
    ENNReal.ofReal wR ^ start /
      (ENNReal.ofReal wR ^ thr * ENNReal.ofReal ηR ^ M) ≤
      ENNReal.ofReal (Real.exp (-(P : ℝ) / 80))
  rw [← ENNReal.ofReal_pow hw0, ← ENNReal.ofReal_pow hw0,
    ← ENNReal.ofReal_pow hη0,
    ← ENNReal.ofReal_mul (pow_nonneg hw0 thr),
    ← ENNReal.ofReal_div_of_pos hdenpos]
  apply ENNReal.ofReal_le_ofReal
  let x : ℝ := (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hparamR : (a : ℝ) + 2 * (B : ℝ) = n := by
    exact_mod_cast (by simpa only [a, B] using hparam)
  have hxN : x = (B : ℝ) / (n : ℝ) := by
    dsimp only [x]
    rw [hparamR]
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have h1x : 0 < 1 + x := by positivity
  have hw_eq : wR = 1 / (1 + x) := by
    dsimp only [wR, x, a, B]
    exact heavyBandW_eq_one_div ha hB
  have hlogTerm :
      Real.log (wR ^ start / (wR ^ thr * ηR ^ M)) =
        (D : ℝ) * Real.log (1 + x) - (M : ℝ) * Real.log ηR := by
    rw [Real.log_div (pow_ne_zero _ (ne_of_gt hwpos))
        (ne_of_gt hdenpos),
      Real.log_mul (pow_ne_zero _ (ne_of_gt hwpos))
        (pow_ne_zero _ (ne_of_gt hηpos)),
      Real.log_pow, Real.log_pow, Real.log_pow, hw_eq, one_div,
      Real.log_inv]
    rw [Nat.cast_sub hstartThr]
    ring
  have hlog1x0 : 0 ≤ Real.log (1 + x) :=
    Real.log_nonneg (by
      rw [hxN]
      have hxnonneg : (0 : ℝ) ≤ (B : ℝ) / (n : ℝ) := by positivity
      nlinarith)
  have hDnat : D * n ≤ M * B := by
    have hDle : D ≤ P := by
      dsimp only [D, start, thr, heavyLateStartK, heavyLateStartLevel,
        heavyLateThr, heavyLateHi]
      dsimp only [P, Q] at hQP hP_le_quarter hq hQn ⊢
      omega
    have h50u : n < 50 * (n / 50) + 50 := by
      have hd := Nat.div_add_mod n 50
      have hm := Nat.mod_lt n (by norm_num : 0 < 50)
      omega
    have hnB : n ≤ 64 * B := by
      dsimp only [B, heavyDirB]
      omega
    calc
      D * n ≤ P * n := Nat.mul_le_mul_right n hDle
      _ ≤ P * (64 * B) := Nat.mul_le_mul_left P hnB
      _ = (64 * P) * B := by ring
      _ = M * B := by
        dsimp only [M, heavyLateResolutions, P]
  have hDreal : (D : ℝ) ≤ (M : ℝ) * x := by
    rw [hxN]
    have hDnatR : ((D * n : ℕ) : ℝ) ≤ ((M * B : ℕ) : ℝ) := by
      exact_mod_cast hDnat
    norm_num only [Nat.cast_mul] at hDnatR
    calc
      (D : ℝ) ≤ ((M : ℝ) * (B : ℝ)) / (n : ℝ) := by
        rw [le_div_iff₀ hnR]
        nlinarith
      _ = (M : ℝ) * ((B : ℝ) / (n : ℝ)) := by ring
  have hsharp := heavyBand_deadline_exponent_sharp
    (a := a) (B := B) (by simpa only [a, B] using ha)
    (by simpa only [a, B] using hB)
  change x ^ 2 / 2 ≤ Real.log ηR - x * Real.log (1 + x) at hsharp
  have hgrowth :
      (D : ℝ) * Real.log (1 + x) ≤
        ((M : ℝ) * x) * Real.log (1 + x) :=
    mul_le_mul_of_nonneg_right hDreal hlog1x0
  have hmain :
      (D : ℝ) * Real.log (1 + x) - (M : ℝ) * Real.log ηR ≤
        -((M : ℝ) * (x ^ 2 / 2)) := by
    nlinarith
  have hnHuge : 2 ^ 128 ≤ n := by
    have hpow : 2 ^ 128 ≤ 2 ^ Nat.log 2 n :=
      Nat.pow_le_pow_right (by norm_num) hlog
    exact hpow.trans (Nat.pow_log_le_self 2 hnPos.ne')
  have hn4900 : 4900 ≤ n :=
    (by norm_num : 4900 ≤ 2 ^ 128).trans hnHuge
  have hBsq : n * n ≤ 2560 * (B * B) := by
    have h50u : n < 50 * (n / 50) + 50 := by
      have hd := Nat.div_add_mod n 50
      have hm := Nat.mod_lt n (by norm_num : 0 < 50)
      omega
    have hBbig : 98 ≤ B := by
      dsimp only [B, heavyDirB]
      omega
    have h2nB : 2 * n ≤ 101 * B := by
      dsimp only [B, heavyDirB] at hBbig ⊢
      omega
    have h4sq : 4 * (n * n) ≤ 4 * (2560 * (B * B)) := by
      calc
        4 * (n * n) = (2 * n) * (2 * n) := by ring
        _ ≤ (101 * B) * (101 * B) :=
          Nat.mul_le_mul h2nB h2nB
        _ = 10201 * (B * B) := by ring
        _ ≤ 10240 * (B * B) := by
          exact Nat.mul_le_mul_right (B * B) (by norm_num : 10201 ≤ 10240)
        _ = 4 * (2560 * (B * B)) := by ring
    exact Nat.le_of_mul_le_mul_left h4sq (by norm_num : 0 < 4)
  have hE :
      (P : ℝ) / 80 ≤ (M : ℝ) * (x ^ 2 / 2) := by
    have hBsqR : (n : ℝ) ^ 2 ≤ 2560 * (B : ℝ) ^ 2 := by
      have hBsq' : n ^ 2 ≤ 2560 * B ^ 2 := by
        simpa [pow_two] using hBsq
      exact_mod_cast hBsq'
    have hright :
        (M : ℝ) * (x ^ 2 / 2) =
          32 * (P : ℝ) * (B : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
      dsimp only [M, heavyLateResolutions]
      rw [hxN]
      dsimp only [P]
      field_simp [hnR.ne']
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      ring_nf
    rw [hright]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 80)
      (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
    have hmul :=
      mul_le_mul_of_nonneg_left hBsqR
        (by positivity : (0 : ℝ) ≤ (P : ℝ))
    nlinarith
  have hlogBound :
      Real.log (wR ^ start / (wR ^ thr * ηR ^ M)) ≤
        -(P : ℝ) / 80 := by
    rw [hlogTerm]
    nlinarith
  calc
    wR ^ start / (wR ^ thr * ηR ^ M) =
        Real.exp (Real.log (wR ^ start / (wR ^ thr * ηR ^ M))) := by
      rw [Real.exp_log]
      positivity
    _ ≤ Real.exp (-(P : ℝ) / 80) :=
      Real.exp_le_exp.mpr hlogBound

/-- All four explicit terms of a Heavy-B late rung fit one current-scale
exponential envelope. -/
theorem heavyLateRungError_le
    (n : ℕ) (hn : 3 ≤ n) (s : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 2)) :
    heavyLateRungError n s ≤
      4 * ENNReal.ofReal
        (Real.exp
          (-((phase2Scale n (s + 1) : ℕ) : ℝ) / 80)) := by
  let e :=
    ENNReal.ofReal
      (Real.exp (-((phase2Scale n (s + 1) : ℕ) : ℝ) / 80))
  have hlog12 : 12 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
  have hsafety := heavyLateSafetyError_le n s hlog12 hs hq
  have hdirection := heavyLateDirectionError_le n s hlog hs hq
  have hclock := heavyLateClockError_le n hn s hlog12 hs hq
  have hreturn := heavyLateReturnError_le n s hlog12 hs hq
  have hclockEnvelope :
      (let pp := heavyBandProductivity n (heavyMiddleProdGap n)
          (heavyLateProdCo n s)
        let pp' := 1 - pp
        (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ heavyLateHorizon n /
            ((1 : ℝ≥0∞) / 2) ^ heavyLateKClock n s) ≤ e := by
    have hexp :
        -((phase2Scale n (s + 1) : ℕ) : ℝ) ≤
          -((phase2Scale n (s + 1) : ℕ) : ℝ) / 80 := by
      have hP0 : (0 : ℝ) ≤ phase2Scale n (s + 1) := by positivity
      nlinarith
    exact hclock.trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))
  change
    (((((heavyMiddleLowerBHi n : ℕ) : ℝ≥0∞) /
          ((heavyMiddleLower n : ℕ) : ℝ≥0∞)) ^
            heavyLateStartK n s +
        ENNReal.ofReal (heavyBandW (heavyDirA n) (heavyDirB n)) ^
              (heavyMiddleLower n + heavyLateStartK n s) /
            (ENNReal.ofReal (heavyBandW (heavyDirA n) (heavyDirB n)) ^
                  heavyLateThr n s *
              ENNReal.ofReal (heavyBandEta (heavyDirA n) (heavyDirB n)) ^
                    heavyLateResolutions n s) +
        ((1 -
              heavyBandProductivity n (heavyMiddleProdGap n)
                (heavyLateProdCo n s)) +
            heavyBandProductivity n (heavyMiddleProdGap n)
                (heavyLateProdCo n s) * ((1 : ℝ≥0∞) / 2)) ^
              heavyLateHorizon n /
            ((1 : ℝ≥0∞) / 2) ^ heavyLateKClock n s) +
      (((heavyLateReturnBHi n s : ℕ) : ℝ≥0∞) /
          ((heavyLateReturnLo n s : ℕ) : ℝ≥0∞)) ^
            heavyLateReturnK n s) ≤ 4 * e
  calc
    _ ≤ ((e + e) + e) + e := by
      dsimp only [e] at hsafety hdirection hclockEnvelope hreturn ⊢
      gcongr
    _ = 4 * e := by ring

set_option maxHeartbeats 4000000 in
-- Instantiating `heavyBandRung` generates many integer side goals for the late
-- parameter table; the higher limit is only for that contract inhabitance.
/-- One Heavy-B late rung halves the public dyadic co-level scale.  The proof
inhabits the full `heavyBandRung` contract, whose generated side conditions
need more than the default heartbeat budget. -/
theorem heavyLate_rung
    (n : ℕ) (hn : 3 ≤ n) (s : ℕ)
    (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 2)) :
    Reaches (heavyStateStep n) (heavyLateHorizon n)
      (HeavyLateCheckpoint n s)
      (HeavyLateCheckpoint n (s + 1))
      (heavyLateRungError n s) := by
  rcases heavyMiddle_geometry hlog with
    ⟨ha, hB, hparam, hquarter, hguard, _hm_lohi, _hm_thr, _hm_width,
      _hm_startEq, _hm_startCo, _hm_K, hpopR, haLo, hbHiR, hmajR,
      hgapProd, _hm_coProd, _hm_popRet, _hm_returnLo, _hm_bHiRet,
      _hm_majRet, _hm_lowerTarget, _hm_targetHi, _hm_returnGap⟩
  let P := phase2Scale n (s + 1)
  let Q := phase2Scale n (s + 2)
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hPdef : P = phase2Scale n (s + 1) := rfl
  have hQdef : Q = phase2Scale n (s + 2) := rfl
  have hQP : Q = P / 2 := by
    dsimp only [Q, P, phase2Scale]
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ,
      Nat.div_div_eq_div_mul]
  have hP_le : P ≤ n / 2 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · norm_num
  have hP_le_quarter : P ≤ n / 4 := by
    dsimp only [P, phase2Scale]
    apply Nat.div_le_div_left
    · calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · norm_num
  have hQpos : 0 < Q := by omega
  have hQn : Q + 1 ≤ n := by omega
  have hQ16 : Q / 16 ≤ Q := Nat.div_le_self Q 16
  have hstartEq :
      heavyMiddleLower n + heavyLateStartK n s =
        heavyLateStartLevel n s := by
    simp only [heavyLateStartK, heavyLateStartLevel, heavyMiddleLower]
    change n / 2 + n / 48 + ((n - P) - (n / 2 + n / 48)) = n - P
    omega
  have hstartCo :
      heavyMiddleLower n + heavyLateStartK n s + P = n := by
    rw [hstartEq]
    unfold heavyLateStartLevel
    dsimp only [P] at hPdef ⊢
    omega
  have hreturnEq :
      heavyLateReturnLo n s + 1 =
        n - phase2Scale n (s + 2) := by
    unfold heavyLateReturnLo
    dsimp only [Q] at hQdef hQn ⊢
    omega
  have hretTarget :
      heavyLateReturnLo n s + 1 + Q = n := by
    rw [hreturnEq]
    dsimp only [Q] at hQdef ⊢
    omega
  have hthr :
      heavyLateThr n s + 1 = heavyLateHi n s := by
    unfold heavyLateThr heavyLateHi
    dsimp only [Q] at hQdef hQn ⊢
    omega
  have hcoProd :
      heavyLateThr n s + heavyLateProdCo n s = n := by
    unfold heavyLateProdCo heavyLateThr heavyLateHi
    dsimp only [Q] at hQdef hQn ⊢
    omega
  have hK :
      heavyLateKClock n s =
        P + 3 * heavyLateResolutions n s := by
    unfold heavyLateKClock heavyLateResolutions
    dsimp only [P] at hPdef ⊢
    omega
  have hretPop :
      heavyLateReturnLo n s + heavyLateReturnBHi n s + 2 = n := by
    unfold heavyLateReturnLo heavyLateReturnBHi
    dsimp only [Q] at hQdef hQn ⊢
    omega
  have hr :=
    heavyBandRung n hn
      (heavyDirA n) (heavyDirB n)
      ha hB hparam
      (heavyMiddleLower n) (heavyMiddleLowerBHi n)
      (heavyLateHi n s) (heavyLateThr n s)
      (heavyLateStartK n s) (heavyLateResolutions n s)
      (heavyLateKClock n s) (heavyLateHorizon n)
      P (heavyMiddleProdGap n) (heavyLateProdCo n s)
      hquarter hguard
      (by
        unfold heavyMiddleLower heavyLateHi
        dsimp only [Q] at hQdef hQP hP_le hP_le_quarter hq ⊢
        omega)
      hthr
      (by
        unfold heavyMiddleLower heavyLateThr heavyLateHi
        dsimp only [Q] at hQdef hQP hP_le hP_le_quarter hq ⊢
        omega)
      hstartCo hK hpopR haLo hbHiR hmajR hgapProd hcoProd
      (heavyLateReturnLo n s) (heavyLateReturnBHi n s)
      (heavyLateReturnK n s)
      hretPop
      (by
        unfold heavyLateReturnLo
        dsimp only [Q] at hQdef hQn ⊢
        omega)
      (by
        unfold heavyLateReturnBHi
        dsimp only [Q] at hQdef hq ⊢
        omega)
      (by
        unfold heavyLateReturnBHi heavyLateReturnLo
        dsimp only [Q] at hQdef hQn ⊢
        omega)
      (by
        unfold heavyMiddleLower heavyLateReturnLo
        dsimp only [Q] at hQdef hQP hP_le hP_le_quarter hq ⊢
        omega)
      (by
        rw [hreturnEq]
        unfold heavyLateHi
        dsimp only [Q] at hQdef ⊢
        omega)
      (by
        unfold heavyLateReturnLo heavyLateReturnK heavyLateHi
        dsimp only [Q] at hQdef hQn ⊢
        omega)
  have hr' :
      Reaches (heavyStateStep n) (heavyLateHorizon n)
        (HeavyLateCheckpoint n s)
        (fun z => heavyLateReturnLo n s + 1 ≤
          BiCfg.heavyLevel z.1)
        (heavyLateRungError n s) := by
    intro z hz
    unfold HeavyLateCheckpoint at hz
    have hpre :
        heavyMiddleLower n + heavyLateStartK n s ≤
          BiCfg.heavyLevel z.1 := by
      rw [hstartEq]
      dsimp only [P] at hPdef
      omega
    exact hr z hpre
  exact hr'.mono_post (by
    intro z hz
    unfold HeavyLateCheckpoint
    have hgoal : n ≤ BiCfg.heavyLevel z.1 + Q := by
      omega
    simpa only [Q] using hgoal)

/-! ## Composition of the late ladder -/

def heavyLateLadderHorizon (n γ : ℕ) : ℕ :=
  phase2StageCount n γ * heavyLateHorizon n

noncomputable def heavyLateLadderError (n γ : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (phase2StageCount n γ),
    heavyLateRungError n (1 + i)

/-- Existing additive-stage activity gives the Heavy-B late rung guard. -/
theorem heavyLate_active_nextScale_ge_32
    {n γ i : ℕ} (hγ : 1 ≤ γ)
    (hlog : 128 ≤ Nat.log 2 n)
    (hi : i < phase2StageCount n γ) :
    32 ≤ phase2Scale n (1 + i + 2) := by
  have hq := phase2_active_nextScale_ge_32 hγ hlog hi
  simpa [phase2NextScale, phase2Scale, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hq

/-- The symbolic Heavy-B late ladder, before scalar error summation. -/
theorem heavyLate_ladder_symbolic
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Reaches (heavyStateStep n) (heavyLateLadderHorizon n γ)
      (HeavyLateCheckpoint n 1)
      (HeavyLateCheckpoint n (1 + phase2StageCount n γ))
      (heavyLateLadderError n γ) := by
  let P : ℕ → HeavyState n → Prop :=
    fun i => HeavyLateCheckpoint n (1 + i)
  let T : ℕ → ℕ := fun _ => heavyLateHorizon n
  let ε : ℕ → ℝ≥0∞ := fun i => heavyLateRungError n (1 + i)
  have hrungs : ∀ i < phase2StageCount n γ,
      Reaches (heavyStateStep n) (T i) (P i) (P (i + 1)) (ε i) := by
    intro i hi
    have hq := heavyLate_active_nextScale_ge_32 hγ hlog hi
    have hr := heavyLate_rung n hn (1 + i)
      (hlog.trans' (by norm_num)) (by omega) hq
    simpa only [P, T, ε, Nat.add_assoc] using hr
  have hchain :=
    Reaches.chain
      (K := heavyStateStep n) (P := P) (T := T) (ε := ε) hrungs
  have hsum :
      (∑ i ∈ Finset.range (phase2StageCount n γ), T i) =
        heavyLateLadderHorizon n γ := by
    rw [heavyLateLadderHorizon]
    simp [T, Finset.sum_const, Finset.card_range]
  rw [hsum] at hchain
  simpa only [P, ε, heavyLateLadderError, Nat.add_assoc] using hchain

/-- The composed Heavy-B late ladder has a geometric exponential error budget. -/
theorem heavyLateLadderError_le_exp
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    heavyLateLadderError n γ ≤
      8 * ENNReal.ofReal
        (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 160))) := by
  let K := phase2StageCount n γ
  have hKPos : 0 < K :=
    phase2StageCount_pos n γ (hlog.trans' (by norm_num)) hsize hγ
  let g : ℕ → ℝ≥0∞ := fun i =>
    ENNReal.ofReal
      (Real.exp
        (-(((n / 2 ^ (2 + i) : ℕ) : ℝ)) / 80))
  have hsum :
      (∑ i ∈ Finset.range K, heavyLateRungError n (1 + i)) ≤
        ∑ i ∈ Finset.range K, 4 * g i := by
    apply Finset.sum_le_sum
    intro i hi
    have hiK : i < K := Finset.mem_range.1 hi
    have hq := heavyLate_active_nextScale_ge_32 hγ hlog
      (by simpa only [K] using hiK)
    have hr := heavyLateRungError_le n hn (1 + i)
      hlog (by omega) hq
    have hidx : (1 + i) + 1 = 2 + i := by omega
    simpa only [g, phase2Scale, hidx] using hr
  have hdouble :
      ∀ i, i + 1 < K → 2 * g i ≤ g (i + 1) := by
    intro i hi
    have hq :=
      heavyLate_active_nextScale_ge_32 hγ hlog
        (by simpa only [K] using hi)
    have hsucc :
        n / 2 ^ (2 + (i + 1)) =
          n / 2 ^ (2 + i) / 2 := by
      rw [show 2 + (i + 1) = (2 + i) + 1 by omega,
        pow_succ, Nat.div_div_eq_div_mul]
    have htwice :
        (n / 2 ^ (2 + i) / 2) * 2 ≤ n / 2 ^ (2 + i) :=
      Nat.div_mul_le_self _ 2
    have hgap :
        64 ≤ n / 2 ^ (2 + i) - n / 2 ^ (2 + (i + 1)) := by
      change 32 ≤ n / 2 ^ (1 + (i + 1) + 2) at hq
      have hnextNext :
          n / 2 ^ (1 + (i + 1) + 2) =
            n / 2 ^ (2 + (i + 1)) / 2 := by
        rw [show 1 + (i + 1) + 2 = (2 + (i + 1)) + 1 by omega,
          pow_succ, Nat.div_div_eq_div_mul]
      rw [hnextNext] at hq
      have hnextTwice :
          (n / 2 ^ (2 + (i + 1)) / 2) * 2 ≤
            n / 2 ^ (2 + (i + 1)) :=
        Nat.div_mul_le_self _ 2
      rw [hsucc]
      omega
    simp only [g]
    rw [← ENNReal.ofReal_ofNat (n := 2),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [show
        (2 : ℝ) *
            Real.exp (-((n / 2 ^ (2 + i) : ℕ) : ℝ) / 80) =
          Real.exp (Real.log 2) *
            Real.exp (-((n / 2 ^ (2 + i) : ℕ) : ℝ) / 80) by
      rw [Real.exp_log (by norm_num)], ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog2 : Real.log 2 < (0.6931471808 : ℝ) :=
      Real.log_two_lt_d9
    have hnextLe :
        n / 2 ^ (2 + (i + 1)) ≤ n / 2 ^ (2 + i) := by
      rw [hsucc]
      exact Nat.div_le_self _ _
    have hgapR :
        (64 : ℝ) ≤
          ((n / 2 ^ (2 + i) : ℕ) : ℝ) -
            ((n / 2 ^ (2 + (i + 1)) : ℕ) : ℝ) := by
      rw [← Nat.cast_sub hnextLe]
      exact_mod_cast hgap
    nlinarith
  have hgeom := enn_sum_le_two_last_of_double g K hKPos hdouble
  have hlast :
      g (K - 1) ≤
        ENNReal.ofReal
          (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 160))) := by
    have hmin :=
      phase2StageCount_minimal (n := n) (γ := γ)
        (show K - 1 < phase2StageCount n γ by
          dsimp only [K]
          omega)
    let P := n / 2 ^ (2 + (K - 1))
    have hPmin : γ * Nat.log 2 n < 2 * P := by
      dsimp only [P]
      simpa only [K] using hmin
    simp only [g]
    change
      ENNReal.ofReal (Real.exp (-(P : ℝ) / 80)) ≤
        ENNReal.ofReal
          (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 160)))
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hPminR :
        ((γ * Nat.log 2 n : ℕ) : ℝ) < 2 * (P : ℝ) := by
      exact_mod_cast hPmin
    nlinarith
  change
    (∑ i ∈ Finset.range K, heavyLateRungError n (1 + i)) ≤ _
  calc
    (∑ i ∈ Finset.range K, heavyLateRungError n (1 + i))
        ≤ ∑ i ∈ Finset.range K, 4 * g i := hsum
    _ = 4 * (∑ i ∈ Finset.range K, g i) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (2 * g (K - 1)) := by gcongr
    _ ≤ 8 * ENNReal.ofReal
          (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 160))) := by
      calc
        4 * (2 * g (K - 1)) = 8 * g (K - 1) := by ring
        _ ≤ _ := by gcongr

/-- The Heavy-B late ladder with the scalar exponential envelope. -/
theorem heavyLate_reaches
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (heavyStateStep n)
      (phase2StageCount n γ * 65536 * n)
      (HeavyLateCheckpoint n 1)
      (HeavyLateCheckpoint n (1 + phase2StageCount n γ))
      (8 * ENNReal.ofReal
        (Real.exp (-(((γ * Nat.log 2 n : ℕ) : ℝ) / 160)))) := by
  have hsym := heavyLate_ladder_symbolic n hn γ hlog hγ
  have herr := heavyLateLadderError_le_exp n hn γ hlog hγ hsize
  simpa [heavyLateLadderHorizon, heavyLateHorizon, Nat.mul_assoc] using
    hsym.mono_error herr

/-! ## Inhabitation gate for one late rung contract -/

example :
    Reaches (heavyStateStep 65536) (heavyLateHorizon 65536)
      (HeavyLateCheckpoint 65536 1)
      (HeavyLateCheckpoint 65536 2)
      (heavyLateRungError 65536 1) := by
  exact heavyLate_rung 65536 (by norm_num) 1
    (by decide) (by norm_num) (by norm_num [phase2Scale])

end Tri

#print axioms Tri.heavyLateSafetyError_le
#print axioms Tri.heavyLateReturnError_le
#print axioms Tri.heavyLateProductivity_ge
#print axioms Tri.heavyLateClockError_le
#print axioms Tri.heavyLateDirectionError_le
#print axioms Tri.heavyLateRungError_le
#print axioms Tri.heavyLate_rung
#print axioms Tri.heavyLate_active_nextScale_ge_32
#print axioms Tri.heavyLate_ladder_symbolic
#print axioms Tri.heavyLateLadderError_le_exp
#print axioms Tri.heavyLate_reaches
