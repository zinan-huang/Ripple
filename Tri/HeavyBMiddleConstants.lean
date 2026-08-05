/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBBandRung
import Tri.DoubleBMiddleConstants

/-!
# Scalar constants for the Heavy-B middle rung

The public Heavy-B checkpoints are stated in gap/co-level form.  Internally the
single-branch `heavyBandRung` consumes level lower bounds, so this file carries
the additive witnesses converting between the two descriptions.
-/

namespace Tri

open scoped ENNReal

/-! ## Shared fixed boundary -/

def heavyMiddleLower (n : ℕ) : ℕ := n / 2 + n / 48
def heavyDirB (n : ℕ) : ℕ := n / 50
def heavyDirA (n : ℕ) : ℕ := n - 2 * heavyDirB n

/-- The Heavy-B direction parameters partition the population. -/
theorem heavyDirA_add_two_heavyDirB
    (n : ℕ) :
    heavyDirA n + 2 * heavyDirB n = n := by
  unfold heavyDirA heavyDirB
  have h := Nat.mul_div_le n 50
  omega

/-- The direction band lies in the first quarter. -/
theorem heavyDirB_quarter (n : ℕ) :
    4 * heavyDirB n ≤ n := by
  unfold heavyDirB
  calc
    4 * (n / 50) ≤ 50 * (n / 50) := by
      exact Nat.mul_le_mul_right (n / 50) (by norm_num)
    _ ≤ n := Nat.mul_div_le n 50

/-- The fixed lower boundary implies the Heavy-B window guard. -/
theorem heavyMiddle_floorGuard
    (n : ℕ) :
    n + 2 * heavyDirB n ≤ 2 * (heavyMiddleLower n + 1) := by
  unfold heavyDirB heavyMiddleLower
  have h2 := Nat.mul_div_le n 2
  have h2u : n < 2 * (n / 2) + 2 := by
    have hd := Nat.div_add_mod n 2
    have hm := Nat.mod_lt n (by norm_num : 0 < 2)
    omega
  have h50_48 : n / 50 ≤ n / 48 :=
    Nat.div_le_div_left (by norm_num : 48 ≤ 50) (by norm_num : 0 < 48)
  omega

/-- The constant-gap handoff's exported gap dominates the middle entry gap. -/
theorem heavyMiddle_entry_gap_le_handoff_gap
    {n : ℕ} (hn : 1920 ≤ n) :
    n / 12 ≤ 32 * (n / 320) := by
  have h12 := Nat.div_add_mod n 12
  have h320 := Nat.div_add_mod n 320
  have h12m := Nat.mod_lt n (by norm_num : 0 < 12)
  have h320m := Nat.mod_lt n (by norm_num : 0 < 320)
  omega

/-! ## Public checkpoints -/

def HeavyMiddleStart (n : ℕ) (s : HeavyState n) : Prop :=
  n + n / 12 ≤ 2 * BiCfg.heavyLevel s.1

instance (n : ℕ) : DecidablePred (HeavyMiddleStart n) := by
  intro s
  unfold HeavyMiddleStart
  infer_instance

/-- Public late checkpoint with additive co-level scale. -/
def HeavyLateCheckpoint (n s : ℕ) (q : HeavyState n) : Prop :=
  n ≤ BiCfg.heavyLevel q.1 + phase2Scale n (s + 1)

instance (n s : ℕ) : DecidablePred (HeavyLateCheckpoint n s) := by
  intro q
  unfold HeavyLateCheckpoint
  infer_instance

/-! ## Middle rung constants -/

def heavyMiddleStartLevel (n : ℕ) : ℕ := n / 2 + n / 24
def heavyMiddleStartK (n : ℕ) : ℕ :=
  heavyMiddleStartLevel n - heavyMiddleLower n
def heavyMiddleStartCo (n : ℕ) : ℕ :=
  n - heavyMiddleStartLevel n

def heavyMiddleReturnLo (n : ℕ) : ℕ := n - n / 4 - 1
def heavyMiddleReturnBHi (n : ℕ) : ℕ := n / 4 - 1
def heavyMiddleReturnK (n : ℕ) : ℕ := n / 64 + 1
def heavyMiddleHi (n : ℕ) : ℕ := n - n / 4 + n / 64
def heavyMiddleThr (n : ℕ) : ℕ := heavyMiddleHi n - 1

def heavyMiddleResolutions (n : ℕ) : ℕ := 64 * n
def heavyMiddleHorizon (n : ℕ) : ℕ := 65536 * n
def heavyMiddleKClock (n : ℕ) : ℕ :=
  heavyMiddleStartCo n + 3 * heavyMiddleResolutions n

def heavyMiddleLowerBHi (n : ℕ) : ℕ :=
  n - heavyMiddleLower n - 2
def heavyMiddleProdGap (n : ℕ) : ℕ :=
  2 * (heavyMiddleLower n + 1) - n
def heavyMiddleProdCo (n : ℕ) : ℕ :=
  n - heavyMiddleThr n

noncomputable def heavyMiddleError (n : ℕ) : ℝ≥0∞ :=
  heavyBandRungError n (heavyDirA n) (heavyDirB n)
    (heavyMiddleLower n) (heavyMiddleLowerBHi n)
    (heavyMiddleThr n) (heavyMiddleStartK n)
    (heavyMiddleResolutions n) (heavyMiddleKClock n)
    (heavyMiddleHorizon n)
    (heavyMiddleReturnLo n) (heavyMiddleReturnBHi n)
    (heavyMiddleReturnK n)
    (heavyMiddleProdGap n) (heavyMiddleProdCo n)

/-- The integer geometry of the Heavy-B middle rung. -/
theorem heavyMiddle_geometry
    {n : ℕ} (hlog : 12 ≤ Nat.log 2 n) :
    0 < heavyDirA n ∧
    0 < heavyDirB n ∧
    heavyDirA n + 2 * heavyDirB n = n ∧
    4 * heavyDirB n ≤ n ∧
    n + 2 * heavyDirB n ≤ 2 * (heavyMiddleLower n + 1) ∧
    heavyMiddleLower n < heavyMiddleHi n ∧
    heavyMiddleThr n + 1 = heavyMiddleHi n ∧
    heavyMiddleLower n + 1 ≤ heavyMiddleThr n ∧
    heavyMiddleLower n + heavyMiddleStartK n =
      heavyMiddleStartLevel n ∧
    heavyMiddleStartLevel n + heavyMiddleStartCo n = n ∧
    heavyMiddleKClock n =
      heavyMiddleStartCo n + 3 * heavyMiddleResolutions n ∧
    heavyMiddleLower n + heavyMiddleLowerBHi n + 2 = n ∧
    0 < heavyMiddleLower n ∧
    0 < heavyMiddleLowerBHi n ∧
    heavyMiddleLowerBHi n ≤ heavyMiddleLower n ∧
    n + heavyMiddleProdGap n = 2 * (heavyMiddleLower n + 1) ∧
    heavyMiddleThr n + heavyMiddleProdCo n = n ∧
    heavyMiddleReturnLo n + heavyMiddleReturnBHi n + 2 = n ∧
    0 < heavyMiddleReturnLo n ∧
    0 < heavyMiddleReturnBHi n ∧
    heavyMiddleReturnBHi n ≤ heavyMiddleReturnLo n ∧
    heavyMiddleLower n < heavyMiddleReturnLo n + 1 ∧
    heavyMiddleReturnLo n + 1 ≤ heavyMiddleHi n ∧
    heavyMiddleReturnLo n + heavyMiddleReturnK n ≤ heavyMiddleHi n := by
  have hn : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have h2 := Nat.mul_div_le n 2
  have h2u : n < 2 * (n / 2) + 2 := by
    have hd := Nat.div_add_mod n 2
    have hm := Nat.mod_lt n (by norm_num : 0 < 2)
    omega
  have h4 := Nat.mul_div_le n 4
  have h4u : n < 4 * (n / 4) + 4 := by
    have hd := Nat.div_add_mod n 4
    have hm := Nat.mod_lt n (by norm_num : 0 < 4)
    omega
  have h24 := Nat.mul_div_le n 24
  have h24u : n < 24 * (n / 24) + 24 := by
    have hd := Nat.div_add_mod n 24
    have hm := Nat.mod_lt n (by norm_num : 0 < 24)
    omega
  have h48 := Nat.mul_div_le n 48
  have h48u : n < 48 * (n / 48) + 48 := by
    have hd := Nat.div_add_mod n 48
    have hm := Nat.mod_lt n (by norm_num : 0 < 48)
    omega
  have h50 := Nat.mul_div_le n 50
  have h50u : n < 50 * (n / 50) + 50 := by
    have hd := Nat.div_add_mod n 50
    have hm := Nat.mod_lt n (by norm_num : 0 < 50)
    omega
  have h64 := Nat.mul_div_le n 64
  have h64u : n < 64 * (n / 64) + 64 := by
    have hd := Nat.div_add_mod n 64
    have hm := Nat.mod_lt n (by norm_num : 0 < 64)
    omega
  have h50_48 : n / 50 ≤ n / 48 :=
    Nat.div_le_div_left (by norm_num : 48 ≤ 50) (by norm_num : 0 < 48)
  have h48_24 : n / 48 ≤ n / 24 :=
    Nat.div_le_div_left (by norm_num : 24 ≤ 48) (by norm_num : 0 < 24)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold heavyDirA heavyDirB
    omega
  · unfold heavyDirB
    omega
  · exact heavyDirA_add_two_heavyDirB n
  · exact heavyDirB_quarter n
  · exact heavyMiddle_floorGuard n
  · unfold heavyMiddleLower heavyMiddleHi
    omega
  · unfold heavyMiddleThr heavyMiddleHi
    omega
  · unfold heavyMiddleLower heavyMiddleThr heavyMiddleHi
    omega
  · simp only [heavyMiddleLower, heavyMiddleStartK, heavyMiddleStartLevel]
    omega
  · simp only [heavyMiddleStartLevel, heavyMiddleStartCo]
    omega
  · unfold heavyMiddleKClock
    rfl
  · simp only [heavyMiddleLower, heavyMiddleLowerBHi]
    omega
  · unfold heavyMiddleLower
    omega
  · unfold heavyMiddleLowerBHi heavyMiddleLower
    omega
  · unfold heavyMiddleLowerBHi heavyMiddleLower
    omega
  · simp only [heavyMiddleProdGap, heavyMiddleLower]
    omega
  · simp only [heavyMiddleProdCo, heavyMiddleThr, heavyMiddleHi]
    omega
  · unfold heavyMiddleReturnLo heavyMiddleReturnBHi
    omega
  · unfold heavyMiddleReturnLo
    omega
  · unfold heavyMiddleReturnBHi
    omega
  · unfold heavyMiddleReturnBHi heavyMiddleReturnLo
    omega
  · unfold heavyMiddleLower heavyMiddleReturnLo
    omega
  · unfold heavyMiddleReturnLo heavyMiddleHi
    omega
  · unfold heavyMiddleReturnLo heavyMiddleReturnK heavyMiddleHi
    omega

/-- The public gap-form start implies the level lower bound consumed by the rung. -/
theorem heavyMiddleStart_to_level
    {n : ℕ} {s : HeavyState n}
    (hs : HeavyMiddleStart n s) :
    heavyMiddleLower n + heavyMiddleStartK n ≤
      BiCfg.heavyLevel s.1 := by
  have h2 := Nat.mul_div_le n 2
  have h24_12 : 2 * (n / 24) ≤ n / 12 := by
    have h12 := Nat.mul_div_le n 12
    have h12u : n < 12 * (n / 12) + 12 := by
      have hd := Nat.div_add_mod n 12
      have hm := Nat.mod_lt n (by norm_num : 0 < 12)
      omega
    have h24 := Nat.mul_div_le n 24
    have h24u : n < 24 * (n / 24) + 24 := by
      have hd := Nat.div_add_mod n 24
      have hm := Nat.mod_lt n (by norm_num : 0 < 24)
      omega
    omega
  have htwice :
      2 * (heavyMiddleStartLevel n) ≤ n + n / 12 := by
    unfold heavyMiddleStartLevel
    omega
  have hstart :
      heavyMiddleLower n + heavyMiddleStartK n ≤
        heavyMiddleStartLevel n := by
    have h48_24 : n / 48 ≤ n / 24 :=
      Nat.div_le_div_left (by norm_num : 24 ≤ 48) (by norm_num : 0 < 24)
    unfold heavyMiddleStartK heavyMiddleLower heavyMiddleStartLevel
    omega
  unfold HeavyMiddleStart at hs
  have hmain :
      2 * (heavyMiddleLower n + heavyMiddleStartK n) ≤
        2 * BiCfg.heavyLevel s.1 := by
    omega
  omega

/-! ## Middle scalar bounds -/

/-- The fixed lower-boundary ruin term of the Heavy-B middle rung is
exponentially small.  This uses the approved slack exponent `1/2000`. -/
theorem heavyMiddleSafetyError_le
    (n : ℕ) (hlog : 12 ≤ Nat.log 2 n) :
    (((heavyMiddleLowerBHi n : ℕ) : ℝ≥0∞) /
        ((heavyMiddleLower n : ℕ) : ℝ≥0∞)) ^
          heavyMiddleStartK n ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000)) := by
  rcases heavyMiddle_geometry hlog with
    ⟨_, _, _, _, _, _, _, _, hstartEq0, _, _, _, _, hbHiR0,
      hmajR0, _, _, _, _, _, _, _, _, _⟩
  let a := heavyMiddleLower n
  let b := heavyMiddleLowerBHi n
  let k := heavyMiddleStartK n
  have hbPos : 0 < b := by simpa only [b] using
    hbHiR0
  have hba : b ≤ a := by simpa only [a, b] using
    hmajR0
  have hstartEq : a + k = heavyMiddleStartLevel n := by
    simpa only [a, k] using
      hstartEq0
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have h2 := Nat.mul_div_le n 2
  have h2u : n < 2 * (n / 2) + 2 := by
    have hd := Nat.div_add_mod n 2
    have hm := Nat.mod_lt n (by norm_num : 0 < 2)
    omega
  have h24 := Nat.mul_div_le n 24
  have h24u : n < 24 * (n / 24) + 24 := by
    have hd := Nat.div_add_mod n 24
    have hm := Nat.mod_lt n (by norm_num : 0 < 24)
    omega
  have h48 := Nat.mul_div_le n 48
  have h48u : n < 48 * (n / 48) + 48 := by
    have hd := Nat.div_add_mod n 48
    have hm := Nat.mod_lt n (by norm_num : 0 < 48)
    omega
  have hkLower : n ≤ 100 * k := by
    dsimp only [k, heavyMiddleStartK, heavyMiddleStartLevel,
      heavyMiddleLower]
    omega
  have hdiff : a ≤ 13 * (a - b) := by
    dsimp only [a, b, heavyMiddleLower, heavyMiddleLowerBHi]
    omega
  have hcross : n * a ≤ 2000 * k * (a - b) := by
    calc
      n * a ≤ (100 * k) * a := Nat.mul_le_mul_right a hkLower
      _ ≤ (100 * k) * (13 * (a - b)) :=
        Nat.mul_le_mul_left (100 * k) hdiff
      _ = 1300 * k * (a - b) := by ring
      _ = 1300 * (k * (a - b)) := by ring
      _ ≤ 2000 * (k * (a - b)) :=
        Nat.mul_le_mul_right (k * (a - b)) (by norm_num : 1300 ≤ 2000)
      _ = 2000 * k * (a - b) := by ring
  change ((b : ℝ≥0∞) / (a : ℝ≥0∞)) ^ k ≤
    ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000))
  have hE :
      (n : ℝ) / 2000 ≤
        (k : ℝ) * ((a : ℝ) - (b : ℝ)) / (a : ℝ) := by
    have haR : (0 : ℝ) < a := by
      exact_mod_cast (lt_of_lt_of_le hbPos hba)
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2000) haR]
    have hcross' : n * a ≤ k * (a - b) * 2000 := by
      calc
        n * a ≤ 2000 * k * (a - b) := hcross
        _ = k * (a - b) * 2000 := by ring
    exact_mod_cast hcross'
  simpa only [show (-((n : ℝ) / 2000)) = -(n : ℝ) / 2000 by ring]
    using ratio_pow_le_ofReal_exp a b k ((n : ℝ) / 2000)
      hbPos hba hE

/-- The buffered upper-return term of the Heavy-B middle rung is exponentially
small, again with slack exponent `1/2000`. -/
theorem heavyMiddleReturnError_le
    (n : ℕ) (hlog : 12 ≤ Nat.log 2 n) :
    (((heavyMiddleReturnBHi n : ℕ) : ℝ≥0∞) /
        ((heavyMiddleReturnLo n : ℕ) : ℝ≥0∞)) ^
          heavyMiddleReturnK n ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000)) := by
  rcases heavyMiddle_geometry hlog with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hretLo0,
      _, _, _, _, _⟩
  have hretPos : 0 < heavyMiddleReturnLo n := by
    simpa using hretLo0
  have hretTop :
      ((heavyMiddleReturnLo n : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hcrossN :
      2 * heavyMiddleReturnBHi n ≤ heavyMiddleReturnLo n := by
    have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
    unfold heavyMiddleReturnBHi heavyMiddleReturnLo
    omega
  have hbase :
      (((heavyMiddleReturnBHi n : ℕ) : ℝ≥0∞) /
          ((heavyMiddleReturnLo n : ℕ) : ℝ≥0∞)) ≤
        (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.div_le_iff (by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact hretPos.ne') hretTop]
    have hcross :
        (2 : ℝ≥0∞) * (heavyMiddleReturnBHi n : ℝ≥0∞) ≤
          (heavyMiddleReturnLo n : ℝ≥0∞) := by
      exact_mod_cast hcrossN
    calc
      (heavyMiddleReturnBHi n : ℝ≥0∞) =
          (1 / 2 : ℝ≥0∞) *
            (2 * (heavyMiddleReturnBHi n : ℝ≥0∞)) := by
        rw [← mul_assoc]
        rw [one_div, mul_comm (2 : ℝ≥0∞)⁻¹ 2,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ (1 / 2 : ℝ≥0∞) *
          (heavyMiddleReturnLo n : ℝ≥0∞) := by
        gcongr
  let k := heavyMiddleReturnK n
  have hpow :
      (((heavyMiddleReturnBHi n : ℕ) : ℝ≥0∞) /
          ((heavyMiddleReturnLo n : ℕ) : ℝ≥0∞)) ^ k ≤
        ((1 : ℝ≥0∞) / 2) ^ k :=
    pow_le_pow_left' hbase k
  have hkR : (n : ℝ) / 64 ≤ (k : ℝ) := by
    dsimp only [k, heavyMiddleReturnK]
    have hdiv : n < 64 * (n / 64 + 1) := by
      have hd := Nat.div_add_mod n 64
      have hm := Nat.mod_lt n (by norm_num : 0 < 64)
      omega
    have hdivR :
        (n : ℝ) < 64 * ((n / 64 + 1 : ℕ) : ℝ) := by
      exact_mod_cast hdiv
    nlinarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 :=
    (by norm_num : (1 : ℝ) / 2 < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hreal :
      (1 / 2 : ℝ) ^ k ≤ Real.exp (-(n : ℝ) / 2000) := by
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
    (((heavyMiddleReturnBHi n : ℕ) : ℝ≥0∞) /
          ((heavyMiddleReturnLo n : ℕ) : ℝ≥0∞)) ^
        heavyMiddleReturnK n
        ≤ ((1 : ℝ≥0∞) / 2) ^ k := by
      simpa only [k] using hpow
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
      have hhalf :
          (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hhalf, ENNReal.ofReal_pow]
      positivity
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000)) :=
      ENNReal.ofReal_le_ofReal hreal

/-- The middle-band Heavy-B productivity floor is at least `1/64`. -/
theorem heavyMiddleProductivity_ge
    (n : ℕ) (_hn : 3 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    2 * ENNReal.ofReal ((1 : ℝ) / 128) ≤
      heavyBandProductivity n (heavyMiddleProdGap n)
        (heavyMiddleProdCo n) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let d := heavyMiddleProdGap n
  let c := heavyMiddleProdCo n
  let A := d * c
  let B := Nat.choose n 2
  have h2 := Nat.mul_div_le n 2
  have h2u : n < 2 * (n / 2) + 2 := by
    have hd := Nat.div_add_mod n 2
    have hm := Nat.mod_lt n (by norm_num : 0 < 2)
    omega
  have h4 := Nat.mul_div_le n 4
  have h4u : n < 4 * (n / 4) + 4 := by
    have hd := Nat.div_add_mod n 4
    have hm := Nat.mod_lt n (by norm_num : 0 < 4)
    omega
  have h48 := Nat.mul_div_le n 48
  have h48u : n < 48 * (n / 48) + 48 := by
    have hd := Nat.div_add_mod n 48
    have hm := Nat.mod_lt n (by norm_num : 0 < 48)
    omega
  have h64 := Nat.mul_div_le n 64
  have h64u : n < 64 * (n / 64) + 64 := by
    have hd := Nat.div_add_mod n 64
    have hm := Nat.mod_lt n (by norm_num : 0 < 64)
    omega
  have hdLower : n ≤ 25 * d := by
    dsimp only [d, heavyMiddleProdGap, heavyMiddleLower]
    omega
  have hcLower : n ≤ 5 * c := by
    dsimp only [c, heavyMiddleProdCo, heavyMiddleThr, heavyMiddleHi]
    omega
  have hchoose : 2 * B = n * (n - 1) := by
    dsimp only [B]
    have h := two_mul_choose_two_succ (n - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h
  have hcross : B ≤ 64 * A := by
    have hn_sq : n * (n - 1) ≤ n * n := by
      exact Nat.mul_le_mul_left n (by omega : n - 1 ≤ n)
    have hprod : n * n ≤ 125 * (d * c) := by
      calc
        n * n ≤ (25 * d) * (5 * c) := Nat.mul_le_mul hdLower hcLower
        _ = 125 * (d * c) := by ring
    have hB2 : 2 * B ≤ 128 * A := by
      rw [hchoose]
      calc
        n * (n - 1) ≤ n * n := hn_sq
        _ ≤ 125 * (d * c) := hprod
        _ ≤ 128 * A := by
          dsimp only [A]
          exact Nat.mul_le_mul_right (d * c) (by norm_num)
    omega
  have hleftTop :
      2 * ENNReal.ofReal ((1 : ℝ) / 128) ≠ ⊤ := by
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
  dsimp only [d, c, A, B]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofNat, ENNReal.toReal_div]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  change (1 : ℝ) / 64 ≤
    ((heavyMiddleProdGap n * heavyMiddleProdCo n : ℕ) : ℝ) /
      ((Nat.choose n 2 : ℕ) : ℝ)
  have hBR : (0 : ℝ) < (Nat.choose n 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
  have hcrossR :
      ((Nat.choose n 2 : ℕ) : ℝ) ≤
        64 * ((heavyMiddleProdGap n * heavyMiddleProdCo n : ℕ) : ℝ) := by
    exact_mod_cast hcross
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 64) hBR]
  nlinarith

/-- The ordinary-productivity clock term of the Heavy-B middle rung is
exponentially small in `n`. -/
theorem heavyMiddleClockError_le
    (n : ℕ) (hn : 3 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    let pp := heavyBandProductivity n (heavyMiddleProdGap n)
      (heavyMiddleProdCo n)
    let pp' := 1 - pp
    (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ heavyMiddleHorizon n /
        ((1 : ℝ≥0∞) / 2) ^ heavyMiddleKClock n ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let pp := heavyBandProductivity n (heavyMiddleProdGap n)
    (heavyMiddleProdCo n)
  let pp' := 1 - pp
  let x := pp * ((1 : ℝ≥0∞) / 2)
  let δ : ℝ := 1 / 128
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  let T := heavyMiddleHorizon n
  let E := heavyMiddleKClock n
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    norm_num
  rcases heavyMiddle_geometry hlog with
    ⟨_, _, _, _, _, _, _, hwidth, _, _, _, _, _, _, _, hgapProd,
      hcoProd, _, _, _, _, _, _, _⟩
  have hpp1 : pp ≤ 1 := by
    exact heavyBandProductivity_le_one n hn
      (heavyMiddleLower n) (heavyMiddleThr n)
      (heavyMiddleProdGap n) (heavyMiddleProdCo n)
      hgapProd hcoProd hwidth
  have hppsum : pp + pp' = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hpp1
  have h2δ : 2 * δe ≤ pp := by
    simpa only [δe, δ, pp] using
      heavyMiddleProductivity_ge n hn hlog
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
  have hT : (T : ℝ) = 65536 * (n : ℝ) := by
    dsimp only [T, heavyMiddleHorizon]
    norm_num
  have hδT : δ * (T : ℝ) = 512 * (n : ℝ) := by
    rw [hT]
    dsimp only [δ]
    ring
  have hENat : E ≤ 194 * n := by
    dsimp only [E, heavyMiddleKClock, heavyMiddleStartCo,
      heavyMiddleStartLevel, heavyMiddleResolutions]
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

set_option maxHeartbeats 2000000 in
-- The Padé direction bound unfolds the Heavy-B window algebra and several
-- floor witnesses; the default heartbeat limit is too small for that chain.
/-- The Heavy-B middle direction term is exponentially small. -/
theorem heavyMiddleDirectionError_le
    (n : ℕ) (hlog : 12 ≤ Nat.log 2 n) :
    let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW (heavyDirA n) (heavyDirB n))
    let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta (heavyDirA n) (heavyDirB n))
    w ^ (heavyMiddleLower n + heavyMiddleStartK n) /
      (w ^ heavyMiddleThr n * η ^ heavyMiddleResolutions n) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000)) := by
  rcases heavyMiddle_geometry hlog with
    ⟨ha, hB, hparam, _, _, _, _, _, hstartEq, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, hreturnGap⟩
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hnPos : 0 < n := by omega
  let a := heavyDirA n
  let B := heavyDirB n
  let wR := heavyBandW a B
  let ηR := heavyBandEta a B
  let start := heavyMiddleLower n + heavyMiddleStartK n
  let thr := heavyMiddleThr n
  let M := heavyMiddleResolutions n
  let D := thr - start
  have hstartThr : start ≤ thr := by
    have h2 := Nat.mul_div_le n 2
    have h4 := Nat.mul_div_le n 4
    have h24 := Nat.mul_div_le n 24
    have h48 := Nat.mul_div_le n 48
    have h64 := Nat.mul_div_le n 64
    simp only [start, thr, heavyMiddleThr, heavyMiddleHi,
      heavyMiddleLower, heavyMiddleStartK, heavyMiddleStartLevel]
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
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000))
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
    have hDle : D ≤ n := by
      dsimp only [D, start, thr, heavyMiddleThr, heavyMiddleHi,
        heavyMiddleLower, heavyMiddleStartK, heavyMiddleStartLevel]
      omega
    have h50u : n < 50 * (n / 50) + 50 := by
      have hd := Nat.div_add_mod n 50
      have hm := Nat.mod_lt n (by norm_num : 0 < 50)
      omega
    have hnB : n ≤ 64 * B := by
      dsimp only [B, heavyDirB]
      omega
    dsimp only [M, heavyMiddleResolutions]
    calc
      D * n ≤ n * n := Nat.mul_le_mul_right n hDle
      _ ≤ n * (64 * B) := Nat.mul_le_mul_left n hnB
      _ = (64 * n) * B := by ring
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
        ((M : ℝ) * x) * Real.log (1 + x) := by
    exact mul_le_mul_of_nonneg_right hDreal hlog1x0
  have hmain :
      (D : ℝ) * Real.log (1 + x) - (M : ℝ) * Real.log ηR ≤
        -((M : ℝ) * (x ^ 2 / 2)) := by
    nlinarith
  have hBsq : n * n ≤ 64000 * (B * B) := by
    have h50u : n < 50 * (n / 50) + 50 := by
      have hd := Nat.div_add_mod n 50
      have hm := Nat.mod_lt n (by norm_num : 0 < 50)
      omega
    have hnB : n ≤ 64 * B := by
      dsimp only [B, heavyDirB]
      omega
    calc
      n * n ≤ (64 * B) * (64 * B) := Nat.mul_le_mul hnB hnB
      _ = 4096 * (B * B) := by ring
      _ ≤ 64000 * (B * B) := by
        exact Nat.mul_le_mul_right (B * B) (by norm_num : 4096 ≤ 64000)
  have hE :
      (n : ℝ) / 2000 ≤ (M : ℝ) * (x ^ 2 / 2) := by
    have hBsqR : (n : ℝ) ^ 2 ≤ 64000 * (B : ℝ) ^ 2 := by
      have hBsq' : n ^ 2 ≤ 64000 * B ^ 2 := by
        simpa [pow_two] using hBsq
      exact_mod_cast hBsq'
    have hright :
        (M : ℝ) * (x ^ 2 / 2) =
          32 * (B : ℝ) ^ 2 / (n : ℝ) := by
      dsimp only [M, heavyMiddleResolutions]
      rw [hxN]
      field_simp [hnR.ne']
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      ring_nf
    rw [hright]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2000) hnR]
    nlinarith
  have hlogBound :
      Real.log (wR ^ start / (wR ^ thr * ηR ^ M)) ≤
        -(n : ℝ) / 2000 := by
    rw [hlogTerm]
    nlinarith
  calc
    wR ^ start / (wR ^ thr * ηR ^ M) =
        Real.exp (Real.log (wR ^ start / (wR ^ thr * ηR ^ M))) := by
      rw [Real.exp_log]
      positivity
    _ ≤ Real.exp (-(n : ℝ) / 2000) :=
      Real.exp_le_exp.mpr hlogBound

/-- All four explicit middle-rung terms fit one exponential envelope.

This uses the spec-approved middle slack exponent `1/2000`. -/
theorem heavyMiddleError_le
    (n : ℕ) (hn : 3 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    heavyMiddleError n ≤
      4 * ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000)) := by
  let e := ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000))
  have hsafety := heavyMiddleSafetyError_le n hlog
  have hdirection := heavyMiddleDirectionError_le n hlog
  have hclock := heavyMiddleClockError_le n hn hlog
  have hreturn := heavyMiddleReturnError_le n hlog
  have hclockEnvelope :
      (let pp := heavyBandProductivity n (heavyMiddleProdGap n)
          (heavyMiddleProdCo n)
        let pp' := 1 - pp
        (pp' + pp * ((1 : ℝ≥0∞) / 2)) ^ heavyMiddleHorizon n /
            ((1 : ℝ≥0∞) / 2) ^ heavyMiddleKClock n) ≤ e := by
    have hexp : -(n : ℝ) ≤ -(n : ℝ) / 2000 := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    exact hclock.trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp))
  change
    (((((heavyMiddleLowerBHi n : ℕ) : ℝ≥0∞) /
          ((heavyMiddleLower n : ℕ) : ℝ≥0∞)) ^
            heavyMiddleStartK n +
        ENNReal.ofReal (heavyBandW (heavyDirA n) (heavyDirB n)) ^
              (heavyMiddleLower n + heavyMiddleStartK n) /
            (ENNReal.ofReal (heavyBandW (heavyDirA n) (heavyDirB n)) ^
                  heavyMiddleThr n *
              ENNReal.ofReal (heavyBandEta (heavyDirA n) (heavyDirB n)) ^
                    heavyMiddleResolutions n) +
        ((1 -
              heavyBandProductivity n (heavyMiddleProdGap n)
                (heavyMiddleProdCo n)) +
            heavyBandProductivity n (heavyMiddleProdGap n)
                (heavyMiddleProdCo n) * ((1 : ℝ≥0∞) / 2)) ^
              heavyMiddleHorizon n /
            ((1 : ℝ≥0∞) / 2) ^ heavyMiddleKClock n) +
      (((heavyMiddleReturnBHi n : ℕ) : ℝ≥0∞) /
          ((heavyMiddleReturnLo n : ℕ) : ℝ≥0∞)) ^
            heavyMiddleReturnK n) ≤ 4 * e
  calc
    _ ≤ ((e + e) + e) + e := by
      dsimp only [e] at hsafety hdirection hclockEnvelope hreturn ⊢
      gcongr
    _ = 4 * e := by ring

theorem heavyMiddle_reaches_symbolic
    (n : ℕ) (hn : 3 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    Reaches (heavyStateStep n) (heavyMiddleHorizon n)
      (HeavyMiddleStart n) (HeavyLateCheckpoint n 1)
      (heavyMiddleError n) := by
  rcases heavyMiddle_geometry hlog with
    ⟨ha, hB, hparam, hquarter, hguard, hlohi, hthr, hwidth,
      hstartEq, hstartCo, hK, hpopR, haLo, hbHiR, hmajR,
      hgapProd, hcoProd, hpopRet, hreturnLo, hbHiRet,
      hmajRet, hlowerTarget, htargetHi, hreturnGap⟩
  have hr :=
    heavyBandRung n hn
      (heavyDirA n) (heavyDirB n)
      ha hB hparam
      (heavyMiddleLower n) (heavyMiddleLowerBHi n)
      (heavyMiddleHi n) (heavyMiddleThr n)
      (heavyMiddleStartK n) (heavyMiddleResolutions n)
      (heavyMiddleKClock n) (heavyMiddleHorizon n)
      (heavyMiddleStartCo n)
      (heavyMiddleProdGap n) (heavyMiddleProdCo n)
      hquarter hguard hlohi hthr hwidth
      (by rw [hstartEq]; exact hstartCo) hK hpopR haLo hbHiR
      hmajR hgapProd hcoProd
      (heavyMiddleReturnLo n) (heavyMiddleReturnBHi n)
      (heavyMiddleReturnK n)
      hpopRet hreturnLo hbHiRet hmajRet hlowerTarget htargetHi
      hreturnGap
  have hr' :
      Reaches (heavyStateStep n) (heavyMiddleHorizon n)
        (HeavyMiddleStart n)
        (fun s => heavyMiddleReturnLo n + 1 ≤
          BiCfg.heavyLevel s.1)
        (heavyMiddleError n) := by
    intro s hs
    exact hr s (heavyMiddleStart_to_level hs)
  exact hr'.mono_post (by
    intro q hq
    unfold HeavyLateCheckpoint
    have htarget :
        heavyMiddleReturnLo n + 1 + n / 4 = n := by
      have hnlarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
      unfold heavyMiddleReturnLo
      omega
    have hscale : phase2Scale n 2 = n / 4 := by
      unfold phase2Scale
      norm_num
    rw [hscale]
    omega)

/-- The Heavy-B middle rung with the scalar envelope. -/
theorem heavyMiddle_reaches
    (n : ℕ) (hn : 3 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    Reaches (heavyStateStep n) (heavyMiddleHorizon n)
      (HeavyMiddleStart n) (HeavyLateCheckpoint n 1)
      (4 * ENNReal.ofReal (Real.exp (-(n : ℝ) / 2000))) := by
  exact (heavyMiddle_reaches_symbolic n hn hlog).mono_error
    (heavyMiddleError_le n hn hlog)

/-! ## Inhabitation gate for the middle rung contract -/

example :
    Reaches (heavyStateStep 4800) (heavyMiddleHorizon 4800)
      (fun s => heavyMiddleLower 4800 + heavyMiddleStartK 4800 ≤
        BiCfg.heavyLevel s.1)
      (fun s => heavyMiddleReturnLo 4800 + 1 ≤
        BiCfg.heavyLevel s.1)
      (heavyMiddleError 4800) := by
  exact heavyBandRung 4800 (by norm_num)
    (heavyDirA 4800) (heavyDirB 4800)
    (by norm_num [heavyDirA, heavyDirB])
    (by norm_num [heavyDirB])
    (by norm_num [heavyDirA, heavyDirB])
    (heavyMiddleLower 4800) (heavyMiddleLowerBHi 4800)
    (heavyMiddleHi 4800) (heavyMiddleThr 4800)
    (heavyMiddleStartK 4800) (heavyMiddleResolutions 4800)
    (heavyMiddleKClock 4800) (heavyMiddleHorizon 4800)
    (heavyMiddleStartCo 4800)
    (heavyMiddleProdGap 4800) (heavyMiddleProdCo 4800)
    (by norm_num [heavyDirB])
    (by norm_num [heavyDirB, heavyMiddleLower])
    (by norm_num [heavyMiddleLower, heavyMiddleHi])
    (by norm_num [heavyMiddleThr, heavyMiddleHi])
    (by norm_num [heavyMiddleLower, heavyMiddleThr, heavyMiddleHi])
    (by norm_num [heavyMiddleLower, heavyMiddleStartK,
      heavyMiddleStartLevel, heavyMiddleStartCo])
    (by norm_num [heavyMiddleKClock])
    (by norm_num [heavyMiddleLower, heavyMiddleLowerBHi])
    (by norm_num [heavyMiddleLower])
    (by norm_num [heavyMiddleLowerBHi, heavyMiddleLower])
    (by norm_num [heavyMiddleLowerBHi, heavyMiddleLower])
    (by norm_num [heavyMiddleLower, heavyMiddleProdGap])
    (by norm_num [heavyMiddleThr, heavyMiddleHi, heavyMiddleProdCo])
    (heavyMiddleReturnLo 4800) (heavyMiddleReturnBHi 4800)
    (heavyMiddleReturnK 4800)
    (by norm_num [heavyMiddleReturnLo, heavyMiddleReturnBHi])
    (by norm_num [heavyMiddleReturnLo])
    (by norm_num [heavyMiddleReturnBHi])
    (by norm_num [heavyMiddleReturnBHi, heavyMiddleReturnLo])
    (by norm_num [heavyMiddleLower, heavyMiddleReturnLo])
    (by norm_num [heavyMiddleReturnLo, heavyMiddleHi])
    (by norm_num [heavyMiddleReturnLo, heavyMiddleReturnK,
      heavyMiddleHi])

end Tri

#print axioms Tri.heavyDirA_add_two_heavyDirB
#print axioms Tri.heavyDirB_quarter
#print axioms Tri.heavyMiddle_floorGuard
#print axioms Tri.heavyMiddle_entry_gap_le_handoff_gap
#print axioms Tri.heavyMiddle_geometry
#print axioms Tri.heavyMiddleStart_to_level
#print axioms Tri.heavyMiddleSafetyError_le
#print axioms Tri.heavyMiddleReturnError_le
#print axioms Tri.heavyMiddleProductivity_ge
#print axioms Tri.heavyMiddleClockError_le
#print axioms Tri.heavyMiddleDirectionError_le
#print axioms Tri.heavyMiddleError_le
#print axioms Tri.heavyMiddle_reaches_symbolic
#print axioms Tri.heavyMiddle_reaches
