/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivationBand
import Tri.ProdBound
import Tri.RatioExp

/-!
# Concrete activation-stage parameters for infection-initiated Tri

Before one quarter of the population is active, a stage from `a` active
molecules to `2a` has a raw activation probability at least `a / (8n)`.
This deliberately slack floor is convenient for a uniform linear-time
doubling stage.
-/

namespace Tri

open scoped ENNReal

/-- The inactive-population corner for the doubling stage `a → 2a`. -/
def infectionDoublingInactiveFloor (n a : ℕ) : ℕ :=
  n - 2 * a + 1

/-- A simple analytic lower bound for the exact rectangular activation floor.
The constant `1/8` is deliberately loose. -/
theorem infectionActivationFloor_ge_eighth
    (n a : ℕ) (h3 : 3 ≤ n) (hquarter : 4 * a ≤ n) :
    (a : ℝ≥0∞) / ((8 * n : ℕ) : ℝ≥0∞) ≤
      infectionActivationFloor n a
        (infectionDoublingInactiveFloor n a) := by
  let i := infectionDoublingInactiveFloor n a
  let A := Nat.choose a 2 * i + a * Nat.choose i 2
  let B := Nat.choose n 3
  have htwoI : 2 * Nat.choose i 2 = i * (i - 1) :=
    two_mul_choose_two i
  have hni : n ≤ 2 * i := by
    dsimp only [i, infectionDoublingInactiveFloor]
    omega
  have hniPred : n ≤ 2 * (i - 1) := by
    dsimp only [i, infectionDoublingInactiveFloor]
    omega
  have hsq : n * n ≤ 8 * Nat.choose i 2 := by
    calc
      n * n ≤ (2 * i) * (2 * (i - 1)) :=
        Nat.mul_le_mul hni hniPred
      _ = 4 * (i * (i - 1)) := by ring
      _ = 4 * (2 * Nat.choose i 2) := by rw [htwoI]
      _ = 8 * Nat.choose i 2 := by ring
  have hchoose : 6 * B = n * (n - 1) * (n - 2) := by
    dsimp only [B]
    have h := six_mul_choose_three_add_two (n - 2)
    simpa only [Nat.sub_add_cancel (by omega : 2 ≤ n),
      show n - 2 + 1 = n - 1 by omega] using h
  have hB : B ≤ 8 * n * Nat.choose i 2 := by
    calc
      B ≤ 6 * B := by omega
      _ = n * (n - 1) * (n - 2) := hchoose
      _ ≤ n * n * n := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left n (Nat.sub_le n 1))
          (Nat.sub_le n 2)
      _ ≤ (8 * Nat.choose i 2) * n :=
        Nat.mul_le_mul_right n hsq
      _ = n * (8 * Nat.choose i 2) := by ring
      _ = 8 * n * Nat.choose i 2 := by ring
  have hcross : B * a ≤ (8 * n) * A := by
    calc
      B * a ≤ (8 * n * Nat.choose i 2) * a :=
        Nat.mul_le_mul_right a hB
      _ = (8 * n) * (a * Nat.choose i 2) := by ring
      _ ≤ (8 * n) * A := by
        apply Nat.mul_le_mul_left
        dsimp only [A]
        omega
  have hnPos : 0 < n := by omega
  have hBPos : 0 < B := by
    dsimp only [B]
    exact Nat.choose_pos h3
  have hleftTop :
      (a : ℝ≥0∞) / ((8 * n : ℕ) : ℝ≥0∞) ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · exact_mod_cast Nat.mul_ne_zero (by norm_num) hnPos.ne'
  have hrightTop :
      infectionActivationFloor n a i ≠ ⊤ := by
    unfold infectionActivationFloor
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · exact_mod_cast hBPos.ne'
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  unfold infectionActivationFloor
  rw [ENNReal.toReal_div, ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_ofNat]
  change (a : ℝ) / (8 * (n : ℝ)) ≤ (A : ℝ) / (B : ℝ)
  have hnR : (0 : ℝ) < 8 * n := by positivity
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBPos
  rw [div_le_div_iff₀ hnR hBR]
  simpa [mul_comm] using (by exact_mod_cast hcross :
    (B : ℝ) * (a : ℝ) ≤ ((8 * n : ℕ) : ℝ) * (A : ℝ))

/-- The concrete Bernoulli activation floor for a doubling stage. -/
noncomputable def infectionDoublingP (n a : ℕ) : ℝ≥0∞ :=
  (a : ℝ≥0∞) / ((8 * n : ℕ) : ℝ≥0∞)

/-- The doubling-stage floor is a subprobability. -/
theorem infectionDoublingP_le_one
    (n a : ℕ) (h3 : 3 ≤ n) (hquarter : 4 * a ≤ n) :
    infectionDoublingP n a ≤ 1 := by
  have hnPos : 0 < n := by omega
  have ha8n : a ≤ 8 * n := by omega
  have hden0 : ((8 * n : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) hnPos.ne'
  have hdenTop : ((8 * n : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    infectionDoublingP n a ≤
        ((8 * n : ℕ) : ℝ≥0∞) / ((8 * n : ℕ) : ℝ≥0∞) := by
      unfold infectionDoublingP
      exact ENNReal.div_le_div_right (by exact_mod_cast ha8n) _
    _ = 1 := ENNReal.div_self hden0 hdenTop

/-- Complementing the concrete floor gives the Bernoulli split used by the
adapted activation clock. -/
theorem infectionDoublingP_add_compl
    (n a : ℕ) (h3 : 3 ≤ n) (hquarter : 4 * a ≤ n) :
    infectionDoublingP n a + (1 - infectionDoublingP n a) = 1 := by
  rw [add_comm]
  exact tsub_add_cancel_of_le
    (infectionDoublingP_le_one n a h3 hquarter)

/-- A concrete raw-interaction tail for one early doubling stage of the
original physical infection chain. -/
theorem infectionActivation_doubling_stage
    (n a T : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a)
    (hquarter : 4 * a ≤ n)
    (s0 : InfectionState n) (hstart : a ≤ s0.1.active) :
    (∑' s, if 2 * a ≤ s.1.active then 0 else
        iter (infectionStateStep n h3) T s0 s) ≤
      ((1 - infectionDoublingP n a) +
          infectionDoublingP n a * ((1 : ℝ≥0∞) / 2)) ^ T /
        ((1 : ℝ≥0∞) / 2) ^ (a - 1) := by
  have hhalf1 : ((1 : ℝ≥0∞) / 2) ≤ 1 := by norm_num
  have hhalf0 : ((1 : ℝ≥0∞) / 2) ≠ 0 := by norm_num
  have hi :
      infectionDoublingInactiveFloor n a + 2 * a ≤ n + 1 := by
    unfold infectionDoublingInactiveFloor
    omega
  have hpFloor :
      infectionDoublingP n a ≤
        infectionActivationFloor n a
          (infectionDoublingInactiveFloor n a) := by
    exact infectionActivationFloor_ge_eighth n a h3 hquarter
  have hthreshold :
      2 * a + 0 ≤ s0.1.active + ((a - 1) + 1) := by
    omega
  simpa only [pow_zero, mul_one] using
    (infectionActivation_failure_tail
      n h3 a (2 * a) (infectionDoublingInactiveFloor n a)
      ((1 : ℝ≥0∞) / 2)
      (infectionDoublingP n a) (1 - infectionDoublingP n a)
      hhalf1 hhalf0
      (infectionDoublingP_add_compl n a h3 hquarter)
      hi hpFloor T (a - 1) 0 s0 hstart hthreshold)

/-- Repeating the linear raw horizon by a factor `q` makes one early
doubling-stage error exponentially small in `a*q`. -/
theorem infectionActivation_doubling_error_scaled
    (n a q : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a) (hq : 1 ≤ q)
    (hquarter : 4 * a ≤ n) :
    ((1 - infectionDoublingP n a) +
          infectionDoublingP n a * ((1 : ℝ≥0∞) / 2)) ^
          (128 * n * q) /
        ((1 : ℝ≥0∞) / 2) ^ (a - 1) ≤
      ENNReal.ofReal (Real.exp (-((a * q : ℕ) : ℝ))) := by
  let p := infectionDoublingP n a
  let p' := 1 - p
  let half : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  let x := p * half
  let δ : ℝ := (a : ℝ) / (16 * (n : ℝ))
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  let T := 128 * n * q
  let E := a - 1
  have hnPos : 0 < n := by omega
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by positivity : (0 : ℝ) < 16 * n)]
    exact_mod_cast (by omega : a ≤ 16 * n)
  have hppsum : p + p' = 1 := by
    dsimp only [p, p']
    exact infectionDoublingP_add_compl n a h3 hquarter
  have hhalfCancel : (2 : ℝ≥0∞) * half = 1 := by
    dsimp only [half]
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hhalfAdd : half + half = 1 := by
    calc
      half + half = 2 * half := by ring
      _ = 1 := hhalfCancel
  have hxx : x + x = p := by
    dsimp only [x]
    calc
      p * half + p * half = p * (half + half) := by ring
      _ = p := by rw [hhalfAdd, mul_one]
  have hxδ : x = δe := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by unfold x p infectionDoublingP half; finiteness)
      (by unfold δe; exact ENNReal.ofReal_ne_top)).mp
    dsimp only [x, p, infectionDoublingP, half, δe, δ]
    rw [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_div, ENNReal.toReal_ofReal hδ0]
    norm_num only [ENNReal.toReal_natCast, Nat.cast_mul,
      Nat.cast_ofNat, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    dsimp only [δ]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat]
    field_simp
    ring
  have hphiSum : (p' + x) + δe ≤ 1 := by
    rw [← hxδ]
    calc
      (p' + x) + x = p' + (x + x) := by ring
      _ = p' + p := by rw [hxx]
      _ = 1 := by rw [add_comm, hppsum]
      _ ≤ 1 := le_rfl
  have hδtop : δe ≠ ⊤ := by
    dsimp only [δe]
    exact ENNReal.ofReal_ne_top
  have hphiSub : p' + x ≤ 1 - δe :=
    ENNReal.le_sub_of_add_le_right hδtop hphiSum
  have hsub : 1 - δe = ENNReal.ofReal (1 - δ) := by
    dsimp only [δe]
    rw [ENNReal.ofReal_sub 1 hδ0, ENNReal.ofReal_one]
  have hphi : p' + x ≤ ENNReal.ofReal (1 - δ) := by
    rwa [← hsub]
  have hnum :
      (p' + x) ^ T ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) :=
    enn_pow_le_ofReal_exp (p' + x) δ T hδ0 hδ1 hphi
  have hdiv :
      (p' + x) ^ T / half ^ E ≤
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
      rw [← Real.exp_log
        (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ E),
        Real.log_pow]
      have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hlogHalf]
      congr 1
      ring
    rw [hhalfReal, ← Real.exp_sub]
    congr 1
    ring
  have hT : (T : ℝ) = 128 * (n : ℝ) * (q : ℝ) := by
    dsimp only [T]
    push_cast
    ring
  have hδT : δ * (T : ℝ) = 8 * (a : ℝ) * (q : ℝ) := by
    rw [hT]
    dsimp only [δ]
    field_simp
    ring
  have hER : (E : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast (Nat.sub_le a 1)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hE0 : (0 : ℝ) ≤ E := by positivity
  have hscaledE : (E : ℝ) * Real.log 2 ≤ (a : ℝ) := by
    calc
      (E : ℝ) * Real.log 2 ≤ (E : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2 hE0
      _ ≤ (a : ℝ) := by simpa using hER
  have hexponent :
      -(δ * (T : ℝ)) + (E : ℝ) * Real.log 2 ≤
        -((a * q : ℕ) : ℝ) := by
    rw [hδT]
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    nlinarith
  change (p' + x) ^ T / half ^ E ≤ _
  exact hdiv.trans (hquot.le.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)))

/-- A fixed linear raw horizon makes one early doubling-stage error
exponentially small in its lower active count. -/
theorem infectionActivation_doubling_error
    (n a : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a)
    (hquarter : 4 * a ≤ n) :
    ((1 - infectionDoublingP n a) +
          infectionDoublingP n a * ((1 : ℝ≥0∞) / 2)) ^ (128 * n) /
        ((1 : ℝ≥0∞) / 2) ^ (a - 1) ≤
      ENNReal.ofReal (Real.exp (-(a : ℝ))) := by
  simpa using
    (infectionActivation_doubling_error_scaled
      n a 1 h3 ha (by omega) hquarter)

/-- Scaled early doubling rung with error `exp(-a*q)`. -/
theorem infectionActivation_doubling_reaches_scaled
    (n a q : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a) (hq : 1 ≤ q)
    (hquarter : 4 * a ≤ n)
    (s0 : InfectionState n) (hstart : a ≤ s0.1.active) :
    (∑' s, if 2 * a ≤ s.1.active then 0 else
        iter (infectionStateStep n h3) (128 * n * q) s0 s) ≤
      ENNReal.ofReal (Real.exp (-((a * q : ℕ) : ℝ))) := by
  exact (infectionActivation_doubling_stage
    n a (128 * n * q) h3 ha hquarter s0 hstart).trans
      (infectionActivation_doubling_error_scaled
        n a q h3 ha hq hquarter)

/-- One early activation doubling succeeds within `128n` raw interactions
except with probability `exp(-a)`. -/
theorem infectionActivation_doubling_reaches
    (n a : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a)
    (hquarter : 4 * a ≤ n)
    (s0 : InfectionState n) (hstart : a ≤ s0.1.active) :
    (∑' s, if 2 * a ≤ s.1.active then 0 else
        iter (infectionStateStep n h3) (128 * n) s0 s) ≤
      ENNReal.ofReal (Real.exp (-(a : ℝ))) := by
  exact (infectionActivation_doubling_stage
    n a (128 * n) h3 ha hquarter s0 hstart).trans
      (infectionActivation_doubling_error n a h3 ha hquarter)

/-- Predicate-form early doubling rung, ready for deterministic composition. -/
theorem infectionActivation_doubling_Reaches
    (n a : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a)
    (hquarter : 4 * a ≤ n) :
    Reaches (infectionStateStep n h3) (128 * n)
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => 2 * a ≤ s.1.active)
      (ENNReal.ofReal (Real.exp (-(a : ℝ)))) := by
  intro s hs
  exact infectionActivation_doubling_reaches
    n a h3 ha hquarter s hs

/-! ## Late stages: halve the inactive population -/

/-- Concrete Bernoulli floor for a late stage that activates `i` more
molecules. -/
noncomputable def infectionLateP (n i : ℕ) : ℝ≥0∞ :=
  infectionDoublingP (8 * n) i

/-- Once at least one quarter of the population is active, the rectangular
activation floor is at least `i/(64n)` whenever at least `i` inactive
molecules remain. -/
theorem infectionActivationFloor_ge_late
    (n a i : ℕ) (h3 : 3 ≤ n) (ha : 2 ≤ a)
    (hquarter : n ≤ 4 * a) :
    infectionLateP n i ≤
      infectionActivationFloor n a i := by
  let A := Nat.choose a 2 * i + a * Nat.choose i 2
  let B := Nat.choose n 3
  have htwoA : 2 * Nat.choose a 2 = a * (a - 1) :=
    two_mul_choose_two a
  have hna : n ≤ 4 * a := hquarter
  have hnaPred : n ≤ 8 * (a - 1) := by omega
  have hsq : n * n ≤ 64 * Nat.choose a 2 := by
    calc
      n * n ≤ (4 * a) * (8 * (a - 1)) :=
        Nat.mul_le_mul hna hnaPred
      _ = 32 * (a * (a - 1)) := by ring
      _ = 32 * (2 * Nat.choose a 2) := by rw [htwoA]
      _ = 64 * Nat.choose a 2 := by ring
  have hchoose : 6 * B = n * (n - 1) * (n - 2) := by
    dsimp only [B]
    have h := six_mul_choose_three_add_two (n - 2)
    simpa only [Nat.sub_add_cancel (by omega : 2 ≤ n),
      show n - 2 + 1 = n - 1 by omega] using h
  have hB : B ≤ 64 * n * Nat.choose a 2 := by
    calc
      B ≤ 6 * B := by omega
      _ = n * (n - 1) * (n - 2) := hchoose
      _ ≤ n * n * n := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left n (Nat.sub_le n 1))
          (Nat.sub_le n 2)
      _ ≤ (64 * Nat.choose a 2) * n :=
        Nat.mul_le_mul_right n hsq
      _ = 64 * n * Nat.choose a 2 := by ring
  have hcross : B * i ≤ (64 * n) * A := by
    calc
      B * i ≤ (64 * n * Nat.choose a 2) * i :=
        Nat.mul_le_mul_right i hB
      _ = (64 * n) * (Nat.choose a 2 * i) := by ring
      _ ≤ (64 * n) * A := by
        apply Nat.mul_le_mul_left
        dsimp only [A]
        exact le_add_right le_rfl
  have hnPos : 0 < n := by omega
  have hBPos : 0 < B := by
    dsimp only [B]
    exact Nat.choose_pos h3
  have hleftTop : infectionLateP n i ≠ ⊤ := by
    unfold infectionLateP infectionDoublingP
    finiteness
  have hrightTop :
      infectionActivationFloor n a i ≠ ⊤ := by
    unfold infectionActivationFloor
    apply ENNReal.div_ne_top
    · exact ENNReal.natCast_ne_top _
    · exact_mod_cast hBPos.ne'
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  unfold infectionLateP infectionDoublingP infectionActivationFloor
  rw [ENNReal.toReal_div, ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_ofNat]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  rw [show (8 : ℝ) * (8 * (n : ℝ)) = 64 * n by ring]
  have hnR : (0 : ℝ) < 64 * n := by positivity
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBPos
  rw [div_le_div_iff₀ hnR hBR]
  dsimp only [A, B] at hcross
  simpa [mul_comm] using (by exact_mod_cast hcross :
    (Nat.choose n 3 : ℝ) * (i : ℝ) ≤
      ((64 * n : ℕ) : ℝ) *
        ((Nat.choose a 2 * i +
          a * Nat.choose i 2 : ℕ) : ℝ))

/-- The late-stage floor and its complement form a Bernoulli split. -/
theorem infectionLateP_add_compl
    (n i : ℕ) (h3 : 3 ≤ n) (hi : i ≤ n) :
    infectionLateP n i + (1 - infectionLateP n i) = 1 := by
  unfold infectionLateP
  apply infectionDoublingP_add_compl
  · omega
  · omega

/-- Concrete raw-interaction tail for a stage that advances active count from
`a` to `a+i`, while `a+2i ≤ n+1` guarantees at least `i` inactive molecules
at every live state. -/
theorem infectionActivation_late_stage
    (n a i T : ℕ) (h3 : 3 ≤ n) (ha : 2 ≤ a) (hi : 1 ≤ i)
    (hquarter : n ≤ 4 * a) (hroom : a + 2 * i ≤ n + 1)
    (s0 : InfectionState n) (hstart : a ≤ s0.1.active) :
    (∑' s, if a + i ≤ s.1.active then 0 else
        iter (infectionStateStep n h3) T s0 s) ≤
      ((1 - infectionLateP n i) +
          infectionLateP n i * ((1 : ℝ≥0∞) / 2)) ^ T /
        ((1 : ℝ≥0∞) / 2) ^ (i - 1) := by
  have hhalf1 : ((1 : ℝ≥0∞) / 2) ≤ 1 := by norm_num
  have hhalf0 : ((1 : ℝ≥0∞) / 2) ≠ 0 := by norm_num
  have hpFloor :
      infectionLateP n i ≤
        infectionActivationFloor n a i :=
    infectionActivationFloor_ge_late n a i h3 ha hquarter
  have hthreshold :
      a + i + 0 ≤ s0.1.active + ((i - 1) + 1) := by
    omega
  simpa only [pow_zero, mul_one] using
    (infectionActivation_failure_tail
      n h3 a (a + i) i
      ((1 : ℝ≥0∞) / 2)
      (infectionLateP n i) (1 - infectionLateP n i)
      hhalf1 hhalf0
      (infectionLateP_add_compl n i h3 (by omega))
      (by omega) hpFloor T (i - 1) 0 s0 hstart hthreshold)

/-- The fixed `1024n` late-stage horizon gives error at most `exp(-i)`. -/
theorem infectionActivation_late_error
    (n i : ℕ) (h3 : 3 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) :
    ((1 - infectionLateP n i) +
          infectionLateP n i * ((1 : ℝ≥0∞) / 2)) ^ (1024 * n) /
        ((1 : ℝ≥0∞) / 2) ^ (i - 1) ≤
      ENNReal.ofReal (Real.exp (-(i : ℝ))) := by
  simpa only [infectionLateP, show 128 * (8 * n) = 1024 * n by ring] using
    (infectionActivation_doubling_error
      (8 * n) i (by omega) hi (by omega))

/-- Scaled late-stage horizon with error `exp(-i*q)`. -/
theorem infectionActivation_late_error_scaled
    (n i q : ℕ) (h3 : 3 ≤ n) (hi : 1 ≤ i) (hq : 1 ≤ q)
    (hin : i ≤ n) :
    ((1 - infectionLateP n i) +
          infectionLateP n i * ((1 : ℝ≥0∞) / 2)) ^
          (1024 * n * q) /
        ((1 : ℝ≥0∞) / 2) ^ (i - 1) ≤
      ENNReal.ofReal (Real.exp (-((i * q : ℕ) : ℝ))) := by
  simpa only [infectionLateP,
    show 128 * (8 * n) * q = 1024 * n * q by ring] using
      (infectionActivation_doubling_error_scaled
        (8 * n) i q (by omega) hi hq (by omega))

/-- Scaled late activation rung with error `exp(-i*q)`. -/
theorem infectionActivation_late_reaches_scaled
    (n a i q : ℕ) (h3 : 3 ≤ n) (ha : 2 ≤ a)
    (hi : 1 ≤ i) (hq : 1 ≤ q)
    (hquarter : n ≤ 4 * a) (hroom : a + 2 * i ≤ n + 1)
    (s0 : InfectionState n) (hstart : a ≤ s0.1.active) :
    (∑' s, if a + i ≤ s.1.active then 0 else
        iter (infectionStateStep n h3) (1024 * n * q) s0 s) ≤
      ENNReal.ofReal (Real.exp (-((i * q : ℕ) : ℝ))) := by
  exact (infectionActivation_late_stage
    n a i (1024 * n * q) h3 ha hi hquarter hroom s0 hstart).trans
      (infectionActivation_late_error_scaled n i q h3 hi hq (by omega))

/-- Horizon multiplier that assigns longer raw time to smaller activation
scales. -/
def infectionStageMultiplier (L scale : ℕ) : ℕ :=
  L / scale + 1

theorem infectionStageMultiplier_pos
    (L scale : ℕ) :
    1 ≤ infectionStageMultiplier L scale := by
  simp [infectionStageMultiplier]

/-- The scale times its horizon multiplier covers the requested error
exponent. -/
theorem infectionStageScale_mul_multiplier
    (L scale : ℕ) (hscale : 1 ≤ scale) :
    L ≤ scale * infectionStageMultiplier L scale := by
  unfold infectionStageMultiplier
  have hd := Nat.div_add_mod L scale
  have hm := Nat.mod_lt L (by omega : 0 < scale)
  rw [Nat.mul_add]
  omega

/-- Converting the scaled-stage exponent to one common requested budget. -/
theorem infectionStageError_le
    (L scale : ℕ) (hscale : 1 ≤ scale) :
    ENNReal.ofReal
        (Real.exp
          (-((scale * infectionStageMultiplier L scale : ℕ) : ℝ))) ≤
      ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (by
    exact_mod_cast infectionStageScale_mul_multiplier L scale hscale)

/-- Early doubling with a common error target `exp(-L)`. -/
theorem infectionActivation_doubling_reaches_budget
    (n a L : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a)
    (hquarter : 4 * a ≤ n)
    (s0 : InfectionState n) (hstart : a ≤ s0.1.active) :
    (∑' s, if 2 * a ≤ s.1.active then 0 else
        iter (infectionStateStep n h3)
          (128 * n * infectionStageMultiplier L a) s0 s) ≤
      ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  exact (infectionActivation_doubling_reaches_scaled
    n a (infectionStageMultiplier L a) h3 ha
      (infectionStageMultiplier_pos L a)
      hquarter s0 hstart).trans
    (infectionStageError_le L a ha)

/-- Late inactive-halving with a common error target `exp(-L)`. -/
theorem infectionActivation_late_reaches_budget
    (n a i L : ℕ) (h3 : 3 ≤ n) (ha : 2 ≤ a) (hi : 1 ≤ i)
    (hquarter : n ≤ 4 * a) (hroom : a + 2 * i ≤ n + 1)
    (s0 : InfectionState n) (hstart : a ≤ s0.1.active) :
    (∑' s, if a + i ≤ s.1.active then 0 else
        iter (infectionStateStep n h3)
          (1024 * n * infectionStageMultiplier L i) s0 s) ≤
      ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  exact (infectionActivation_late_reaches_scaled
    n a i (infectionStageMultiplier L i) h3 ha hi
      (infectionStageMultiplier_pos L i)
      hquarter hroom s0 hstart).trans
    (infectionStageError_le L i hi)

/-- One late activation stage succeeds within `1024n` raw interactions except
with probability `exp(-i)`. -/
theorem infectionActivation_late_reaches
    (n a i : ℕ) (h3 : 3 ≤ n) (ha : 2 ≤ a) (hi : 1 ≤ i)
    (hquarter : n ≤ 4 * a) (hroom : a + 2 * i ≤ n + 1)
    (s0 : InfectionState n) (hstart : a ≤ s0.1.active) :
    (∑' s, if a + i ≤ s.1.active then 0 else
        iter (infectionStateStep n h3) (1024 * n) s0 s) ≤
      ENNReal.ofReal (Real.exp (-(i : ℝ))) := by
  exact (infectionActivation_late_stage
    n a i (1024 * n) h3 ha hi hquarter hroom s0 hstart).trans
      (infectionActivation_late_error n i h3 hi (by omega))

/-- Predicate-form late rung, ready for deterministic composition. -/
theorem infectionActivation_late_Reaches
    (n a i : ℕ) (h3 : 3 ≤ n) (ha : 2 ≤ a) (hi : 1 ≤ i)
    (hquarter : n ≤ 4 * a) (hroom : a + 2 * i ≤ n + 1) :
    Reaches (infectionStateStep n h3) (1024 * n)
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => a + i ≤ s.1.active)
      (ENNReal.ofReal (Real.exp (-(i : ℝ)))) := by
  intro s hs
  exact infectionActivation_late_reaches
    n a i h3 ha hi hquarter hroom s hs

/-- Number of late inactive-halving stages. -/
def infectionLateStages : ℕ → ℕ
  | 0 => 0
  | r + 1 => 1 + infectionLateStages ((r + 1) / 2)
termination_by r => r
decreasing_by omega

/-- Union-bound error accumulated by the late inactive-halving schedule. -/
noncomputable def infectionLateError : ℕ → ℝ≥0∞
  | 0 => 0
  | r + 1 =>
      ENNReal.ofReal
          (Real.exp (-((((r + 1) + 1) / 2 : ℕ) : ℝ))) +
        infectionLateError ((r + 1) / 2)
termination_by r => r
decreasing_by omega

/-- The late rungs recursively halve the number of remaining inactive
molecules and reach full activation. -/
theorem infectionActivation_late_to_all
    (n r : ℕ) (h3 : 3 ≤ n) (hrn : r ≤ n)
    (ha : 2 ≤ n - r) (hquarter : n ≤ 4 * (n - r)) :
    Reaches (infectionStateStep n h3)
      (infectionLateStages r * (1024 * n))
      (fun s : InfectionState n => n - r ≤ s.1.active)
      (fun s => n ≤ s.1.active)
      (infectionLateError r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      cases r with
      | zero =>
          intro s hs
          simp only [infectionLateStages, zero_mul, infectionLateError, iter]
          rw [tsum_eq_single s (by
            intro z hzs
            simp [PMF.pure_apply, hzs])]
          simpa using hs
      | succ r =>
          let R := r + 1
          let i := (R + 1) / 2
          let r' := R / 2
          let a := n - R
          have hRPos : 0 < R := by omega
          have hr'lt : r' < R := by
            dsimp only [r', R]
            omega
          have hiPos : 1 ≤ i := by
            dsimp only [i, R]
            omega
          have hr'R : r' ≤ R := hr'lt.le
          have hr'n : r' ≤ n := hr'R.trans hrn
          have hlevel : a + i = n - r' := by
            dsimp only [a, i, r', R]
            omega
          have haDef : a = n - R := rfl
          have ha2 : 2 ≤ a := by
            rw [haDef]
            exact ha
          have haQuarter : n ≤ 4 * a := by
            rw [haDef]
            exact hquarter
          have hroom : a + 2 * i ≤ n + 1 := by
            dsimp only [a, i, R]
            omega
          have hr'a : 2 ≤ n - r' := by
            rw [← hlevel]
            omega
          have hr'quarter : n ≤ 4 * (n - r') := by
            have har' : a ≤ n - r' := by rw [← hlevel]; omega
            exact haQuarter.trans (Nat.mul_le_mul_left 4 har')
          have hstage :
              Reaches (infectionStateStep n h3) (1024 * n)
                (fun s : InfectionState n => a ≤ s.1.active)
                (fun s => n - r' ≤ s.1.active)
                (ENNReal.ofReal (Real.exp (-(i : ℝ)))) := by
            simpa only [hlevel] using
              (infectionActivation_late_Reaches
                n a i h3 ha2 hiPos haQuarter hroom)
          have hrest :=
            ih r' hr'lt hr'n hr'a hr'quarter
          have hcomp := hstage.comp hrest
          simpa only [R, a, i, r', infectionLateStages,
            infectionLateError, Nat.add_mul, one_mul] using hcomp

end Tri

#print axioms Tri.infectionActivationFloor_ge_eighth
#print axioms Tri.infectionActivation_doubling_stage
#print axioms Tri.infectionActivation_doubling_error
#print axioms Tri.infectionActivation_doubling_reaches
#print axioms Tri.infectionActivationFloor_ge_late
#print axioms Tri.infectionActivation_late_reaches
#print axioms Tri.infectionActivation_late_to_all
