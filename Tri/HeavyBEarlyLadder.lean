/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBClockRung
import Tri.HeavyBMiddleConstants
import Tri.Phase1Refactored

/-!
# Heavy-B early gap ladder

The public checkpoints are stated in doubled-level gap form:

```
n + (8 + 2t)q <= 2 * heavyLevel.
```

The concrete rung witnesses use ordinary level lower bounds.  They are chosen
with a floor-half convention so the public predicates remain free of natural
subtraction and parity cases.
-/

namespace Tri

open scoped BigOperators ENNReal

/-- Public gap of subcheckpoint `t` in one early Heavy-B stage. -/
def heavyEarlyGap (q t : ℕ) : ℕ :=
  8 * q + 2 * (t * q)

/-- Public Heavy-B early checkpoint in gap form. -/
def HeavyEarlyCheckpoint (n q t : ℕ) (s : HeavyState n) : Prop :=
  n + heavyEarlyGap q t ≤ 2 * BiCfg.heavyLevel s.1

instance (n q t : ℕ) :
    DecidablePred (HeavyEarlyCheckpoint n q t) := by
  intro s
  unfold HeavyEarlyCheckpoint
  infer_instance

/-! ## Concrete subrung witnesses -/

def heavyEarlyDirB (q : ℕ) : ℕ := 2 * q
def heavyEarlyDirA (n q : ℕ) : ℕ := n - 4 * q
def heavyEarlyClockGap (q : ℕ) : ℕ := 4 * q

def heavyEarlyBandLo (n q : ℕ) : ℕ := n / 2 + 2 * q
def heavyEarlyBHiR (n q : ℕ) : ℕ :=
  n - heavyEarlyBandLo n q - 2

def heavyEarlyStartK (q t : ℕ) : ℕ := 2 * q + t * q
def heavyEarlyStartLevel (n q t : ℕ) : ℕ :=
  n / 2 + 4 * q + t * q
def heavyEarlyStartCo (n q t : ℕ) : ℕ :=
  n - heavyEarlyStartLevel n q t

def heavyEarlyHi (n q t : ℕ) : ℕ :=
  n / 2 + 6 * q + t * q + 1
def heavyEarlyThr (n q t : ℕ) : ℕ :=
  heavyEarlyHi n q t - 1

def heavyEarlyReturnLo (n q t : ℕ) : ℕ :=
  n / 2 + 5 * q + t * q
def heavyEarlyBHiRet (n q t : ℕ) : ℕ :=
  n - heavyEarlyReturnLo n q t - 2
def heavyEarlyReturnK (q : ℕ) : ℕ := q + 1

/-- Resolution quota used by the early Heavy-B direction branch. -/
def heavyEarlyResolutions (n : ℕ) : ℕ := 4 * n

/-- Fuel budget large enough for the resolution quota at the current start. -/
def heavyEarlyKClock (n q t : ℕ) : ℕ :=
  heavyEarlyStartCo n q t + 3 * heavyEarlyResolutions n

def heavyEarlyHalfHorizon (n q t : ℕ) : ℕ :=
  32 * heavyEarlyKClock n q t

def heavyEarlySubrungHorizon (n q t : ℕ) : ℕ :=
  64 * heavyEarlyKClock n q t

/-- Exact public error assigned to one early Heavy-B subrung. -/
noncomputable def heavyEarlySubrungError
    (n q t : ℕ) : ℝ≥0∞ :=
  heavyBandJointRungError
    n (heavyEarlyClockGap q) (heavyEarlyDirA n q) (heavyEarlyDirB q)
    (heavyEarlyBandLo n q) (heavyEarlyBHiR n q)
    (heavyEarlyHi n q t) (heavyEarlyThr n q t)
    (heavyEarlyStartK q t) (heavyEarlyResolutions n)
    (heavyEarlyReturnLo n q t) (heavyEarlyBHiRet n q t)
    (heavyEarlyReturnK q)

/-- Sum of the four subrung errors in one dyadic Heavy-B stage. -/
noncomputable def heavyEarlyStageError (n q : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range 4, heavyEarlySubrungError n q t

/-- Raw horizon of one four-subrung Heavy-B stage. -/
def heavyEarlyStageHorizon (n q : ℕ) : ℕ :=
  ∑ t ∈ Finset.range 4, heavyEarlySubrungHorizon n q t

/-! ## Elementary checkpoint arithmetic -/

theorem heavyEarlyGap_four_eq_next (q : ℕ) :
    heavyEarlyGap q 4 = heavyEarlyGap (2 * q) 0 := by
  unfold heavyEarlyGap
  ring

theorem heavyEarlyGap_succ (q t : ℕ) :
    heavyEarlyGap q (t + 1) = 10 * q + 2 * (t * q) := by
  unfold heavyEarlyGap
  ring

theorem heavyEarlyCheckpoint_to_start
    {n q t : ℕ} {s : HeavyState n}
    (hs : HeavyEarlyCheckpoint n q t s) :
    heavyEarlyStartLevel n q t ≤ BiCfg.heavyLevel s.1 := by
  unfold HeavyEarlyCheckpoint heavyEarlyGap at hs
  unfold heavyEarlyStartLevel
  have hhalf := Nat.mul_div_le n 2
  omega

theorem heavyEarly_return_to_checkpoint
    {n q t : ℕ} {s : HeavyState n}
    (hs : heavyEarlyReturnLo n q t + 1 ≤ BiCfg.heavyLevel s.1) :
    HeavyEarlyCheckpoint n q (t + 1) s := by
  unfold heavyEarlyReturnLo at hs
  unfold HeavyEarlyCheckpoint
  rw [heavyEarlyGap_succ]
  have hhalfUpper : n < 2 * (n / 2) + 2 := by
    have hd := Nat.div_add_mod n 2
    have hm := Nat.mod_lt n (by norm_num : 0 < 2)
    omega
  omega

/-! ## Scalar bounds for one subrung -/

theorem heavyEarly_ruin_le
    (n q t : ℕ) (hq : 0 < q) (_ht : t < 4)
    (hqSmall : 160 * q ≤ n) :
    (((heavyEarlyBHiR n q : ℕ) : ℝ≥0∞) /
        ((heavyEarlyBandLo n q : ℕ) : ℝ≥0∞)) ^
          heavyEarlyStartK q t ≤
      ENNReal.ofReal
        (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ))))) := by
  let aLo := heavyEarlyBandLo n q
  let bHi := heavyEarlyBHiR n q
  let k := heavyEarlyStartK q t
  have hn : 0 < n := by omega
  have hbPos : 0 < bHi := by
    dsimp only [bHi, heavyEarlyBHiR, aLo, heavyEarlyBandLo]
    omega
  have hba : bHi ≤ aLo := by
    dsimp only [bHi, heavyEarlyBHiR, aLo, heavyEarlyBandLo]
    omega
  apply ratio_pow_le_ofReal_exp aLo bHi k
    (((q : ℝ) ^ 2) / (4 * (n : ℝ))) hbPos hba
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqSmallR : (160 : ℝ) * q ≤ n := by exact_mod_cast hqSmall
  have hkLower : q ≤ k := by
    dsimp only [k, heavyEarlyStartK]
    omega
  have hkR : (q : ℝ) ≤ k := by exact_mod_cast hkLower
  have hdiff : 4 * q ≤ aLo - bHi := by
    dsimp only [aLo, bHi, heavyEarlyBandLo, heavyEarlyBHiR]
    omega
  have hdiffR : (4 : ℝ) * q ≤ (aLo : ℝ) - (bHi : ℝ) := by
    have hsub : ((aLo - bHi : ℕ) : ℝ) = (aLo : ℝ) - (bHi : ℝ) := by
      rw [Nat.cast_sub hba]
    rw [← hsub]
    exact_mod_cast hdiff
  have haUpper : (aLo : ℝ) ≤ n := by
    dsimp only [aLo, heavyEarlyBandLo]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hhalfR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast Nat.mul_div_le n 2
    have h4qR : (4 : ℝ) * q ≤ n := by
      nlinarith
    have htwice :
        (2 : ℝ) * (((n / 2 : ℕ) : ℝ) + 2 * (q : ℝ)) ≤
          2 * (n : ℝ) := by
      nlinarith
    nlinarith
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ))
    (by exact_mod_cast (lt_of_lt_of_le hbPos hba))]
  have hprod :
      (4 : ℝ) * (q : ℝ) ^ 2 ≤
        (k : ℝ) * ((aLo : ℝ) - (bHi : ℝ)) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ q by positivity)
      (show (0 : ℝ) ≤ (aLo : ℝ) - (bHi : ℝ) by exact sub_nonneg.mpr (by exact_mod_cast hba))]
  nlinarith [sq_nonneg (q : ℝ), mul_pos (by norm_num : (0 : ℝ) < 4) hnR]

theorem heavyEarly_return_le
    (n q t : ℕ) (hq : 0 < q) (ht : t < 4)
    (hqSmall : 160 * q ≤ n) :
    (((heavyEarlyBHiRet n q t : ℕ) : ℝ≥0∞) /
        ((heavyEarlyReturnLo n q t : ℕ) : ℝ≥0∞)) ^
          heavyEarlyReturnK q ≤
      ENNReal.ofReal
        (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ))))) := by
  let a := heavyEarlyReturnLo n q t
  let b := heavyEarlyBHiRet n q t
  let k := heavyEarlyReturnK q
  have hn : 0 < n := by omega
  have hbPos : 0 < b := by
    have htq : t * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
    dsimp only [b, heavyEarlyBHiRet, a, heavyEarlyReturnLo]
    omega
  have hba : b ≤ a := by
    have htq : t * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
    dsimp only [b, heavyEarlyBHiRet, a, heavyEarlyReturnLo]
    omega
  apply ratio_pow_le_ofReal_exp a b k
    (((q : ℝ) ^ 2) / (4 * (n : ℝ))) hbPos hba
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hkR : (q : ℝ) ≤ k := by
    dsimp only [k, heavyEarlyReturnK]
    exact_mod_cast (Nat.le_add_right q 1)
  have hdiff : 8 * q ≤ a - b := by
    have htq : t * q ≤ 3 * q := Nat.mul_le_mul_right q (by omega)
    dsimp only [a, b, heavyEarlyReturnLo, heavyEarlyBHiRet]
    omega
  have hdiffR : (8 : ℝ) * q ≤ (a : ℝ) - (b : ℝ) := by
    have hsub : ((a - b : ℕ) : ℝ) = (a : ℝ) - (b : ℝ) := by
      rw [Nat.cast_sub hba]
    rw [← hsub]
    exact_mod_cast hdiff
  have haUpper : (a : ℝ) ≤ n := by
    dsimp only [a, heavyEarlyReturnLo]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hsmallR : (160 : ℝ) * q ≤ n := by exact_mod_cast hqSmall
    have htqR : (t : ℝ) * (q : ℝ) ≤ 3 * q := by
      exact_mod_cast (Nat.mul_le_mul_right q (by omega : t ≤ 3))
    have hhalfR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast Nat.mul_div_le n 2
    have h16qR : (16 : ℝ) * q ≤ n := by
      nlinarith
    have htwice :
        (2 : ℝ) *
            (((n / 2 : ℕ) : ℝ) + 5 * (q : ℝ) +
              (t : ℝ) * (q : ℝ)) ≤
          2 * (n : ℝ) := by
      nlinarith
    nlinarith
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ))
    (by exact_mod_cast (lt_of_lt_of_le hbPos hba))]
  have hprod :
      (8 : ℝ) * (q : ℝ) ^ 2 ≤
        (k : ℝ) * ((a : ℝ) - (b : ℝ)) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ q by positivity)
      (show (0 : ℝ) ≤ (a : ℝ) - (b : ℝ) by exact sub_nonneg.mpr (by exact_mod_cast hba))]
  nlinarith [sq_nonneg (q : ℝ), mul_pos (by norm_num : (0 : ℝ) < 4) hnR]

theorem heavyEarly_normalClock_le
    (n q t : ℕ) (hq : 0 < q) (_ht : t < 4)
    (hqSmall : 160 * q ≤ n) :
    ((3 : ℝ≥0∞) / 4) ^ heavyClockBudget n (heavyEarlyResolutions n) ≤
      ENNReal.ofReal
        (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ))))) := by
  have hn : 0 < n := by omega
  apply ratio_pow_le_ofReal_exp 4 3
    (heavyClockBudget n (heavyEarlyResolutions n))
    (((q : ℝ) ^ 2) / (4 * (n : ℝ)))
    (by norm_num) (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqSmallNat : q ≤ n := by omega
  have hqSq : q ^ 2 ≤ n * n := by
    have hp := Nat.pow_le_pow_left hqSmallNat 2
    simpa [pow_two] using hp
  have hbudget : n ≤ heavyClockBudget n (heavyEarlyResolutions n) := by
    unfold heavyClockBudget
    omega
  have hqSqR : (q : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) := by
    exact_mod_cast hqSq
  have hbudgetR : (n : ℝ) ≤ heavyClockBudget n (heavyEarlyResolutions n) := by
    exact_mod_cast hbudget
  norm_num
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ))
    (by norm_num : (0 : ℝ) < 4)]
  nlinarith

theorem heavyEarly_blankClock_le
    (n q : ℕ) :
    ENNReal.ofReal
        (Real.exp (-(((heavyEarlyClockGap q : ℕ) : ℝ) ^ 2 / (n : ℝ)))) ≤
      ENNReal.ofReal
        (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ))))) := by
  by_cases hn : n = 0
  · subst n
    simp
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold heavyEarlyClockGap
    push_cast
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ)) hnR]
    nlinarith [sq_nonneg (q : ℝ)]

theorem heavyEarly_direction_le
    (n q t : ℕ) (hq : 0 < q) (_ht : t < 4)
    (hqSmall : 160 * q ≤ n) :
    let w : ℝ≥0∞ :=
      ENNReal.ofReal (heavyBandW (heavyEarlyDirA n q) (heavyEarlyDirB q))
    let η : ℝ≥0∞ :=
      ENNReal.ofReal (heavyBandEta (heavyEarlyDirA n q) (heavyEarlyDirB q))
    w ^ (heavyEarlyBandLo n q + heavyEarlyStartK q t) /
        (w ^ heavyEarlyThr n q t * η ^ heavyEarlyResolutions n) ≤
      ENNReal.ofReal
        (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ))))) := by
  dsimp only
  let a := heavyEarlyDirA n q
  let B := heavyEarlyDirB q
  let start := heavyEarlyBandLo n q + heavyEarlyStartK q t
  let thr := heavyEarlyThr n q t
  let M := heavyEarlyResolutions n
  let wR := heavyBandW a B
  let ηR := heavyBandEta a B
  have ha : 0 < a := by
    dsimp only [a, heavyEarlyDirA]
    omega
  have hB : 0 < B := by
    dsimp only [B, heavyEarlyDirB]
    omega
  have hparam : a + 2 * B = n := by
    dsimp only [a, B, heavyEarlyDirA, heavyEarlyDirB]
    omega
  have hquarter : 4 * B ≤ n := by
    dsimp only [B, heavyEarlyDirB]
    omega
  have hwpos : 0 < wR := by
    obtain ⟨hu, huw, _⟩ := heavyBand_tail_regime ha hB
    exact hu.trans huw
  have hw0 : 0 ≤ wR := hwpos.le
  have hw1 : wR ≤ 1 := (heavyBandW_lt_one (a := a) hB).le
  have hηpos : 0 < ηR := heavyBandEta_pos ha hB
  have hη0 : 0 ≤ ηR := hηpos.le
  have hη1 : 1 ≤ ηR := heavyBandEta_ge_one ha hB
  have hthr : thr = start + B := by
    dsimp only [thr, start, B, heavyEarlyThr, heavyEarlyHi,
      heavyEarlyBandLo, heavyEarlyStartK, heavyEarlyDirB]
    omega
  have hdenpos :
      0 < wR ^ thr * ηR ^ M :=
    mul_pos (pow_pos hwpos _) (pow_pos hηpos _)
  change
    ENNReal.ofReal wR ^ start /
        (ENNReal.ofReal wR ^ thr * ENNReal.ofReal ηR ^ M) ≤
      ENNReal.ofReal
        (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ)))))
  rw [← ENNReal.ofReal_pow hw0, ← ENNReal.ofReal_pow hw0,
    ← ENNReal.ofReal_pow hη0,
    ← ENNReal.ofReal_mul (pow_nonneg hw0 thr),
    ← ENNReal.ofReal_div_of_pos hdenpos]
  apply ENNReal.ofReal_le_ofReal
  have hterm :
      wR ^ start / (wR ^ thr * ηR ^ M) ≤
        1 / (wR ^ (2 * B) * ηR ^ (2 * n)) := by
    rw [hthr, pow_add]
    have hstartPow :
        wR ^ heavyEarlyBandLo n q * wR ^ heavyEarlyStartK q t =
          wR ^ start := by
      dsimp only [start]
      rw [← pow_add]
    have hleftpos : 0 < wR ^ start := pow_pos hwpos _
    have hBpos : 0 < wR ^ B := pow_pos hwpos _
    have hηMpos : 0 < ηR ^ M := pow_pos hηpos _
    have hη2pos : 0 < ηR ^ (2 * n) := pow_pos hηpos _
    have hsplit :
        wR ^ start / (wR ^ start * (wR ^ B * ηR ^ M)) =
          1 / (wR ^ B * ηR ^ M) := by
      field_simp
    rw [hstartPow]
    rw [show wR ^ (start + B) = wR ^ start * wR ^ B by
      rw [pow_add]]
    have hwB_le_one : wR ^ B ≤ 1 := by
      simpa using pow_le_one₀ (n := B) (by positivity) hw1
    have hη_pow : 1 ≤ ηR ^ (2 * n) := by
      simpa using one_le_pow₀ (n := 2 * n) hη1
    have hM : 2 * n ≤ M := by
      dsimp only [M, heavyEarlyResolutions]
      omega
    have hηM_ge : ηR ^ (2 * n) ≤ ηR ^ M :=
      pow_le_pow_right₀ hη1 hM
    have hdenLe :
        wR ^ (2 * B) * ηR ^ (2 * n) ≤
          wR ^ B * ηR ^ M := by
      calc
        wR ^ (2 * B) * ηR ^ (2 * n)
            = (wR ^ B) * (wR ^ B * ηR ^ (2 * n)) := by
              rw [show 2 * B = B + B by omega, pow_add]
              ring
        _ ≤ wR ^ B * (1 * ηR ^ M) := by
          gcongr
        _ = wR ^ B * ηR ^ M := by
          ring
    rw [mul_assoc, hsplit]
    exact one_div_le_one_div_of_le
      (mul_pos (pow_pos hwpos _) (pow_pos hηpos _)) hdenLe
  have hdeadline :=
    heavyBand_deadline_term ha hB hparam
  have hexp :
      Real.exp (-((B : ℝ) ^ 2 / (n : ℝ))) ≤
        Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ)))) := by
    apply Real.exp_le_exp.mpr
    have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp only [B, heavyEarlyDirB]
    push_cast
    rw [neg_le_neg_iff]
    field_simp [hnR.ne']
    nlinarith [sq_nonneg (q : ℝ)]
  exact hterm.trans (hdeadline.trans hexp)

/-- The exact joint-clock error produced by the larger early budget is below
the public `heavyBandJointRungError` envelope. -/
theorem heavyEarlyJointClockError_le_rungError
    (n q t : ℕ) (hq : 0 < q) (_ht : t < 4)
    (hqSmall : 160 * q ≤ n) :
    let a := heavyEarlyDirA n q
    let B := heavyEarlyDirB q
    let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
    let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
    heavyBandJointClockError
        n (heavyEarlyClockGap q)
        (heavyEarlyBandLo n q) (heavyEarlyBHiR n q)
        (heavyEarlyHi n q t) (heavyEarlyThr n q t)
        (heavyEarlyStartK q t) (heavyEarlyResolutions n)
        (heavyEarlyKClock n q t) (heavyEarlyHalfHorizon n q t)
        w η (heavyEarlyReturnLo n q t) (heavyEarlyBHiRet n q t)
        (heavyEarlyReturnK q) ≤
      heavyEarlySubrungError n q t := by
  dsimp only
  unfold heavyEarlySubrungError heavyBandJointRungError
  let a := heavyEarlyDirA n q
  let B := heavyEarlyDirB q
  let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
  let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
  let K := heavyEarlyKClock n q t
  let H := heavyEarlyHalfHorizon n q t
  let M := heavyEarlyResolutions n
  let start := heavyEarlyBandLo n q + heavyEarlyStartK q t
  let hi := heavyEarlyHi n q t
  have hn : 0 < n := by omega
  have hg : heavyEarlyClockGap q ≤ n := by
    unfold heavyEarlyClockGap
    omega
  have hstart : start ≤ hi := by
    dsimp only [start, hi, heavyEarlyBandLo, heavyEarlyStartK,
      heavyEarlyHi]
    omega
  have hwidth : hi ≤ start + heavyEarlyClockGap q := by
    dsimp only [start, hi, heavyEarlyClockGap, heavyEarlyBandLo,
      heavyEarlyStartK, heavyEarlyHi]
    omega
  have hnormal₀ :=
    heavyNormalClockError_le K
  have hnormal :
      1 / (((32 : ℝ≥0∞) / 31) ^ H * (1 / 2) ^ K) ≤
        ((3 : ℝ≥0∞) / 4) ^ heavyClockBudget n M := by
    have hH : H = 32 * K := by
      dsimp only [H, K, heavyEarlyHalfHorizon]
    have hbudget : heavyClockBudget n M ≤ K := by
      dsimp only [K, M, heavyEarlyKClock, heavyEarlyResolutions,
        heavyClockBudget]
      omega
    have hbase : ((3 : ℝ≥0∞) / 4) ≤ 1 := by
      rw [ENNReal.div_le_iff (by norm_num : (4 : ℝ≥0∞) ≠ 0)
        (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
      norm_num
    rw [hH]
    exact hnormal₀.trans
      (pow_le_pow_right_of_le_one' hbase hbudget)
  have hblank :
      heavyBlankW n (heavyEarlyClockGap q) ^ start /
          (heavyBlankW n (heavyEarlyClockGap q) ^ hi *
            heavyBlankEta n (heavyEarlyClockGap q) ^ H) ≤
        ENNReal.ofReal
          (Real.exp
            (-(((heavyEarlyClockGap q : ℕ) : ℝ) ^ 2 / (n : ℝ)))) := by
    apply heavyBlankClockError_le_exp_neg
      n (heavyEarlyClockGap q) start hi H hn hg hstart hwidth
    have hKge : n ≤ K := by
      dsimp only [K, heavyEarlyKClock, heavyEarlyResolutions]
      omega
    dsimp only [H, heavyEarlyHalfHorizon]
    exact Nat.mul_le_mul_left 32 hKge
  unfold heavyBandJointClockError heavyJointClockEnvelope
  exact add_le_add
    (add_le_add (add_le_add le_rfl le_rfl)
      (add_le_add hnormal hblank)) le_rfl

set_option maxHeartbeats 800000 in
-- Instantiating the joint-clock early parameter table generates many
-- arithmetic side conditions.
/-- One narrow early Heavy-B subrung. -/
theorem heavyEarly_subrung
    (n : ℕ) (hn : 3 ≤ n) (q t : ℕ)
    (hq : 0 < q) (ht : t < 4) (hqSmall : 160 * q ≤ n) :
    Reaches (heavyStateStep n) (heavyEarlySubrungHorizon n q t)
      (HeavyEarlyCheckpoint n q t)
      (HeavyEarlyCheckpoint n q (t + 1))
      (heavyEarlySubrungError n q t) := by
  let a := heavyEarlyDirA n q
  let B := heavyEarlyDirB q
  let g := heavyEarlyClockGap q
  let aLo := heavyEarlyBandLo n q
  let bHiR := heavyEarlyBHiR n q
  let hi := heavyEarlyHi n q t
  let thr := heavyEarlyThr n q t
  let k := heavyEarlyStartK q t
  let M := heavyEarlyResolutions n
  let K := heavyEarlyKClock n q t
  let H := heavyEarlyHalfHorizon n q t
  let T := heavyEarlySubrungHorizon n q t
  let cL := heavyEarlyStartCo n q t
  let returnLo := heavyEarlyReturnLo n q t
  let bHiRet := heavyEarlyBHiRet n q t
  let kRet := heavyEarlyReturnK q
  have htq : t * q ≤ 3 * q :=
    Nat.mul_le_mul_right q (by omega : t ≤ 3)
  have hbandLe : aLo + 2 ≤ n := by
    dsimp only [aLo, heavyEarlyBandLo]
    omega
  have hstartLevelLe : heavyEarlyStartLevel n q t ≤ n := by
    dsimp only [heavyEarlyStartLevel]
    omega
  have hreturnLe : returnLo + 2 ≤ n := by
    dsimp only [returnLo, heavyEarlyReturnLo]
    omega
  have ha : 0 < a := by
    dsimp only [a, heavyEarlyDirA]
    omega
  have hB : 0 < B := by
    dsimp only [B, heavyEarlyDirB]
    omega
  have hparam : a + 2 * B = n := by
    dsimp only [a, B, heavyEarlyDirA, heavyEarlyDirB]
    omega
  have hquarter : 4 * B ≤ n := by
    dsimp only [B, heavyEarlyDirB]
    omega
  have hg : g ≤ n := by
    dsimp only [g, heavyEarlyClockGap]
    omega
  have hfloorClock : n + g ≤ 2 * (aLo + 1) := by
    dsimp only [g, aLo, heavyEarlyClockGap, heavyEarlyBandLo]
    have hhalfUpper : n < 2 * (n / 2) + 2 := by
      have hd := Nat.div_add_mod n 2
      have hm := Nat.mod_lt n (by norm_num : 0 < 2)
      omega
    omega
  have hsmall : 16 * hi ≤ 9 * n := by
    dsimp only [hi, heavyEarlyHi]
    have hhalf := Nat.mul_div_le n 2
    omega
  have hfloorGuard : n + 2 * B ≤ 2 * (aLo + 1) := by
    dsimp only [B, aLo, heavyEarlyDirB, heavyEarlyBandLo]
    have hhalfUpper : n < 2 * (n / 2) + 2 := by
      have hd := Nat.div_add_mod n 2
      have hm := Nat.mod_lt n (by norm_num : 0 < 2)
      omega
    omega
  have haLohi : aLo < hi := by
    dsimp only [aLo, hi, heavyEarlyBandLo, heavyEarlyHi]
    omega
  have hthr : thr + 1 = hi := by
    dsimp only [thr, hi, heavyEarlyThr, heavyEarlyHi]
    omega
  have hstartClock : aLo + k ≤ hi := by
    dsimp only [aLo, k, hi, heavyEarlyBandLo, heavyEarlyStartK,
      heavyEarlyHi]
    omega
  have hwidthClock : hi ≤ aLo + k + g := by
    dsimp only [aLo, k, g, hi, heavyEarlyBandLo, heavyEarlyStartK,
      heavyEarlyClockGap, heavyEarlyHi]
    omega
  have hstartCo : aLo + k + cL = n := by
    dsimp only [aLo, k, cL, heavyEarlyBandLo, heavyEarlyStartK,
      heavyEarlyStartCo, heavyEarlyStartLevel]
    omega
  have hK : cL + 3 * M ≤ K := by
    dsimp only [K, cL, M, heavyEarlyKClock]
    exact le_rfl
  have hH : 2 * H ≤ T := by
    dsimp only [H, T, heavyEarlyHalfHorizon, heavyEarlySubrungHorizon]
    omega
  have hpopR : aLo + bHiR + 2 = n := by
    dsimp only [aLo, bHiR, heavyEarlyBandLo, heavyEarlyBHiR]
    omega
  have haLo : 0 < aLo := by
    dsimp only [aLo, heavyEarlyBandLo]
    omega
  have hbHiR : 0 < bHiR := by
    dsimp only [bHiR, heavyEarlyBHiR, aLo, heavyEarlyBandLo]
    omega
  have hmajR : bHiR ≤ aLo := by
    dsimp only [bHiR, aLo, heavyEarlyBHiR, heavyEarlyBandLo]
    omega
  have hpopRet : returnLo + bHiRet + 2 = n := by
    dsimp only [returnLo, bHiRet, heavyEarlyReturnLo,
      heavyEarlyBHiRet]
    omega
  have hreturnLo : 0 < returnLo := by
    dsimp only [returnLo, heavyEarlyReturnLo]
    omega
  have hbHiRet : 0 < bHiRet := by
    dsimp only [returnLo, bHiRet, heavyEarlyReturnLo,
      heavyEarlyBHiRet]
    omega
  have hmajRet : bHiRet ≤ returnLo := by
    dsimp only [returnLo, bHiRet, heavyEarlyReturnLo,
      heavyEarlyBHiRet]
    omega
  have hlowerTarget : aLo < returnLo + 1 := by
    dsimp only [aLo, returnLo, heavyEarlyBandLo, heavyEarlyReturnLo]
    omega
  have htargetHi : returnLo + 1 ≤ hi := by
    dsimp only [returnLo, hi, heavyEarlyReturnLo, heavyEarlyHi]
    omega
  have hreturnGap : returnLo + kRet ≤ hi := by
    dsimp only [returnLo, kRet, hi, heavyEarlyReturnLo,
      heavyEarlyReturnK, heavyEarlyHi]
    omega
  let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
  let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
  let u : ℝ≥0∞ := (a : ℝ≥0∞) / ((a + 4 * B : ℕ) : ℝ≥0∞)
  have hparams := heavyBand_params_enn ha hB hparam
  dsimp only at hparams
  rcases hparams with ⟨hrel, hwη, hw1, hw0, hη1, hηt, _hwt⟩
  have hqDen : a + 4 * B ≠ 0 := by omega
  have hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      (a + 4 * B) * s.cfg.1.y ≤ a * s.cfg.1.x := by
    intro s hlive _
    exact heavyBand_window_guard_params hparam hfloorGuard s hlive
  have hr :=
    heavyState_band_phase_reaches_joint_clock_mono
      n hn g aLo bHiR hi thr k M K T H cL
      hfloorClock hsmall hH haLohi hthr hstartCo hK hpopR
      haLo hbHiR hmajR
      a (a + 4 * B) hqDen hguard
      w η u rfl hrel hwη hw1 hw0 hη1 hηt
      returnLo bHiRet kRet hpopRet hreturnLo hbHiRet hmajRet
      hlowerTarget htargetHi hreturnGap
  have herr :
      heavyBandJointClockError
        n g aLo bHiR hi thr k M K H w η returnLo bHiRet kRet ≤
        heavyEarlySubrungError n q t := by
    simpa only [a, B, g, aLo, bHiR, hi, thr, k, M, K, H, w, η,
      returnLo, bHiRet, kRet] using
      heavyEarlyJointClockError_le_rungError n q t hq ht hqSmall
  have hrPublic :=
    (hr.mono_error herr).mono_post (by
      intro s hs
      exact heavyEarly_return_to_checkpoint (n := n) (q := q) (t := t) hs)
  intro s hs
  exact hrPublic s (by
    have hstart := heavyEarlyCheckpoint_to_start (n := n) (q := q)
      (t := t) (s := s) hs
    have heq : aLo + k = heavyEarlyStartLevel n q t := by
      dsimp only [aLo, k, heavyEarlyBandLo, heavyEarlyStartK,
        heavyEarlyStartLevel]
      ring
    rw [heq]
    exact hstart)

/-- One subrung costs at most five copies of its common Gaussian envelope. -/
theorem heavyEarlySubrungError_le
    (n q t : ℕ) (hq : 0 < q) (ht : t < 4)
    (hqSmall : 160 * q ≤ n) :
    heavyEarlySubrungError n q t ≤
      5 * ENNReal.ofReal
        (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ))))) := by
  let E : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ)))))
  have hsafety := heavyEarly_ruin_le n q t hq ht hqSmall
  have hdirection := heavyEarly_direction_le n q t hq ht hqSmall
  have hnormal := heavyEarly_normalClock_le n q t hq ht hqSmall
  have hblank := heavyEarly_blankClock_le n q
  have hreturn := heavyEarly_return_le n q t hq ht hqSmall
  calc
    heavyEarlySubrungError n q t ≤ (((E + E) + (E + E)) + E) := by
      unfold heavyEarlySubrungError heavyBandJointRungError
        heavyJointClockEnvelope
      dsimp only [E] at hsafety hdirection hnormal hblank hreturn ⊢
      gcongr
    _ = 5 * E := by ring

/-! ## Stage and dyadic ladder composition -/

theorem heavyEarly_stage
    (n : ℕ) (hn : 3 ≤ n) (q : ℕ)
    (hq : 0 < q) (hqSmall : 160 * q ≤ n) :
    Reaches (heavyStateStep n) (heavyEarlyStageHorizon n q)
      (HeavyEarlyCheckpoint n q 0)
      (HeavyEarlyCheckpoint n (2 * q) 0)
      (heavyEarlyStageError n q) := by
  let P : ℕ → HeavyState n → Prop :=
    fun t => HeavyEarlyCheckpoint n q t
  let T : ℕ → ℕ := fun t => heavyEarlySubrungHorizon n q t
  let ε : ℕ → ℝ≥0∞ := fun t => heavyEarlySubrungError n q t
  have hrungs : ∀ t < 4,
      Reaches (heavyStateStep n) (T t) (P t) (P (t + 1)) (ε t) := by
    intro t ht
    exact heavyEarly_subrung n hn q t hq ht hqSmall
  have hchain :=
    Reaches.chain
      (K := heavyStateStep n) (P := P) (T := T) (ε := ε) hrungs
  have hpost := hchain.mono_post (by
    intro s hs
    change HeavyEarlyCheckpoint n q 4 s at hs
    change HeavyEarlyCheckpoint n (2 * q) 0 s
    unfold HeavyEarlyCheckpoint at hs ⊢
    rwa [heavyEarlyGap_four_eq_next] at hs)
  simpa [P, T, ε, heavyEarlyStageHorizon, heavyEarlyStageError] using hpost

theorem heavyEarlyStageError_le
    (n q : ℕ) (hq : 0 < q) (hqSmall : 160 * q ≤ n) :
    heavyEarlyStageError n q ≤
      20 * ENNReal.ofReal
        (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ))))) := by
  unfold heavyEarlyStageError
  calc
    (∑ t ∈ Finset.range 4, heavyEarlySubrungError n q t)
        ≤ ∑ _t ∈ Finset.range 4,
            5 * ENNReal.ofReal
              (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ))))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact heavyEarlySubrungError_le n q t hq
        (Finset.mem_range.mp ht) hqSmall
    _ = 20 * ENNReal.ofReal
          (Real.exp (-((q : ℝ) ^ 2 / (4 * (n : ℝ))))) := by
      simp
      ring

/-- Initial dyadic scale for the Heavy-B early ladder. -/
def heavyEarlySeedUnit (n γ : ℕ) : ℕ :=
  max 1 (phase1SeedR n γ / 8)

def heavyEarlyScale (n γ j : ℕ) : ℕ :=
  2 ^ j * heavyEarlySeedUnit n γ

noncomputable def heavyEarlyEnvelopeScale (n γ : ℕ) : ℝ :=
  (heavyEarlySeedUnit n γ : ℝ) ^ 2 / (4 * (n : ℝ))

def HeavyEarlyTarget (n : ℕ) (s : HeavyState n) : Prop :=
  n + 8 * (n / 320) ≤ 2 * BiCfg.heavyLevel s.1

instance (n : ℕ) : DecidablePred (HeavyEarlyTarget n) := by
  intro s
  unfold HeavyEarlyTarget
  infer_instance

theorem heavyEarlyScale_succ (n γ j : ℕ) :
    heavyEarlyScale n γ (j + 1) = 2 * heavyEarlyScale n γ j := by
  unfold heavyEarlyScale
  rw [pow_succ]
  ring

theorem heavyEarlyScale_pos (n γ j : ℕ) :
    0 < heavyEarlyScale n γ j := by
  unfold heavyEarlyScale heavyEarlySeedUnit
  positivity

theorem heavyEarlyEnvelope_eq
    (n γ j : ℕ) :
    (heavyEarlyScale n γ j : ℝ) ^ 2 / (4 * (n : ℝ)) =
      (4 : ℝ) ^ j * heavyEarlyEnvelopeScale n γ := by
  unfold heavyEarlyScale heavyEarlyEnvelopeScale
  push_cast
  have hpow : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul]
    calc
      (2 : ℝ) ^ (j * 2) = ((2 : ℝ) ^ 2) ^ j := by
        rw [← pow_mul, Nat.mul_comm]
      _ = (4 : ℝ) ^ j := by norm_num
  rw [mul_pow, hpow]
  ring

theorem heavyEarlyScale_at_log (n γ : ℕ) :
    n / 320 ≤ heavyEarlyScale n γ (Nat.log 2 n) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hpow :
        n < 2 ^ (Nat.log 2 n + 1) := by
      simpa using Nat.lt_pow_succ_log_self
        (by norm_num : 1 < (2 : ℕ)) n
    have hhalf : n / 320 ≤ 2 ^ Nat.log 2 n := by
      rw [pow_succ] at hpow
      omega
    exact hhalf.trans (by
      unfold heavyEarlyScale heavyEarlySeedUnit
      calc
        2 ^ Nat.log 2 n = 2 ^ Nat.log 2 n * 1 := by simp
        _ ≤ 2 ^ Nat.log 2 n * max 1 (phase1SeedR n γ / 8) :=
          Nat.mul_le_mul_left (2 ^ Nat.log 2 n)
            (le_max_left 1 (phase1SeedR n γ / 8)))

theorem heavyEarlyScale_hits (n γ : ℕ) :
    ∃ j, n / 320 ≤ heavyEarlyScale n γ j := by
  exact ⟨Nat.log 2 n, heavyEarlyScale_at_log n γ⟩

def heavyEarlyStages (n γ : ℕ) : ℕ :=
  Nat.find (heavyEarlyScale_hits n γ)

theorem heavyEarlyScale_final (n γ : ℕ) :
    n / 320 ≤ heavyEarlyScale n γ (heavyEarlyStages n γ) := by
  exact Nat.find_spec (heavyEarlyScale_hits n γ)

theorem heavyEarlyScale_lt_final
    (n γ i : ℕ) (hi : i < heavyEarlyStages n γ) :
    heavyEarlyScale n γ i < n / 320 := by
  exact Nat.lt_of_not_ge
    (Nat.find_min (heavyEarlyScale_hits n γ) hi)

theorem heavyEarlyStages_le_log (n γ : ℕ) :
    heavyEarlyStages n γ ≤ Nat.log 2 n := by
  exact Nat.find_min' (heavyEarlyScale_hits n γ)
    (heavyEarlyScale_at_log n γ)

theorem heavyEarlyScale_small
    (n γ i : ℕ) (hi : i < heavyEarlyStages n γ) :
    160 * heavyEarlyScale n γ i ≤ n := by
  have hlt := heavyEarlyScale_lt_final n γ i hi
  calc
    160 * heavyEarlyScale n γ i ≤
        320 * heavyEarlyScale n γ i := by
      exact Nat.mul_le_mul_right _ (by norm_num : 160 ≤ 320)
    _ ≤ 320 * (n / 320) :=
      Nat.mul_le_mul_left 320 hlt.le
    _ ≤ n := Nat.mul_div_le _ _

def heavyEarlyLadderHorizon (n γ : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (heavyEarlyStages n γ),
    heavyEarlyStageHorizon n (heavyEarlyScale n γ j)

noncomputable def heavyEarlyLadderError
    (n γ : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (heavyEarlyStages n γ),
    heavyEarlyStageError n (heavyEarlyScale n γ j)

theorem heavyEarly_ladder
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ) :
    Reaches (heavyStateStep n) (heavyEarlyLadderHorizon n γ)
      (HeavyEarlyCheckpoint n (heavyEarlySeedUnit n γ) 0)
      (HeavyEarlyTarget n)
      (heavyEarlyLadderError n γ) := by
  let P : ℕ → HeavyState n → Prop :=
    fun j => HeavyEarlyCheckpoint n (heavyEarlyScale n γ j) 0
  let T : ℕ → ℕ :=
    fun j => heavyEarlyStageHorizon n (heavyEarlyScale n γ j)
  let ε : ℕ → ℝ≥0∞ :=
    fun j => heavyEarlyStageError n (heavyEarlyScale n γ j)
  have hrungs : ∀ j < heavyEarlyStages n γ,
      Reaches (heavyStateStep n) (T j) (P j) (P (j + 1)) (ε j) := by
    intro j hj
    have hr := heavyEarly_stage n hn (heavyEarlyScale n γ j)
      (heavyEarlyScale_pos n γ j) (heavyEarlyScale_small n γ j hj)
    have hscale := heavyEarlyScale_succ n γ j
    simpa only [P, T, ε, hscale] using hr
  have hchain :=
    Reaches.chain
      (K := heavyStateStep n) (P := P) (T := T) (ε := ε) hrungs
  have hpost := hchain.mono_post (by
    intro s hs
    change HeavyEarlyCheckpoint n
      (heavyEarlyScale n γ (heavyEarlyStages n γ)) 0 s at hs
    change HeavyEarlyTarget n s
    unfold HeavyEarlyCheckpoint heavyEarlyGap at hs
    unfold HeavyEarlyTarget
    have hfinal := heavyEarlyScale_final n γ
    omega)
  have hscaleZero :
      heavyEarlyScale n γ 0 = heavyEarlySeedUnit n γ := by
    simp [heavyEarlyScale]
  simpa [P, T, ε, hscaleZero, heavyEarlyLadderHorizon,
    heavyEarlyLadderError] using hpost

/-! ## Initial entry and error summation -/

theorem phase1SeedR_ge_eight
    {n γ : ℕ} (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    8 ≤ phase1SeedR n γ := by
  have hn : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have hrad : 8 ^ 2 ≤ phase1SeedRadicand n γ := by
    unfold phase1SeedRadicand
    calc
      8 ^ 2 ≤ 1 * 4096 * 12 := by norm_num
      _ ≤ γ * n * Nat.log 2 n :=
        Nat.mul_le_mul (Nat.mul_le_mul hγ hn) hlog
  have hsqrt : 8 ≤ Nat.sqrt (phase1SeedRadicand n γ) :=
    (Nat.le_sqrt').mpr hrad
  unfold phase1SeedR
  dsimp only
  split_ifs <;> omega

/-- Paper-style Heavy-B initial gap in physical coordinates. -/
def HeavyBEarlyInitial (n γ : ℕ) (s : HeavyState n) : Prop :=
  ∃ gap : ℕ,
    s.1.y + gap ≤ s.1.x ∧
      γ * n * Nat.log 2 n ≤ gap ^ 2

theorem heavyEarlyCheckpoint_zero_of_gap
    (n γ : ℕ) (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (s : HeavyState n) (gap : ℕ)
    (hxy : s.1.y + gap ≤ s.1.x)
    (hgapSq : γ * n * Nat.log 2 n ≤ gap ^ 2) :
    HeavyEarlyCheckpoint n (heavyEarlySeedUnit n γ) 0 s := by
  have hseedGap : phase1SeedR n γ ≤ gap :=
    phase1SeedR_le_of_sq
      (by simpa [phase1SeedRadicand] using hgapSq)
  have hseedEight := phase1SeedR_ge_eight hlog hγ
  have hunit :
      heavyEarlySeedUnit n γ = phase1SeedR n γ / 8 := by
    unfold heavyEarlySeedUnit
    rw [max_eq_right]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
    simpa using hseedEight
  have height :
      8 * heavyEarlySeedUnit n γ ≤ phase1SeedR n γ := by
    rw [hunit]
    exact Nat.mul_div_le _ _
  have hlevelGap : n + gap ≤ 2 * BiCfg.heavyLevel s.1 := by
    have hinv := s.2
    simp only [BiCfg.HeavyInv, BiCfg.heavyLevel] at hinv ⊢
    omega
  unfold HeavyEarlyCheckpoint heavyEarlyGap
  omega

theorem heavyEarly_reaches
    (n : ℕ) (hn : 3 ≤ n) (γ : ℕ)
    (hlog : 12 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Reaches (heavyStateStep n) (heavyEarlyLadderHorizon n γ)
      (HeavyBEarlyInitial n γ)
      (HeavyEarlyTarget n)
      (heavyEarlyLadderError n γ) := by
  have hl := heavyEarly_ladder n hn γ
  intro s hs
  obtain ⟨gap, hxy, hgapSq⟩ := hs
  exact hl s
    (heavyEarlyCheckpoint_zero_of_gap
      n γ hlog hγ s gap hxy hgapSq)

theorem heavyEarlyLadderError_le_first
    (n γ : ℕ) (_hlog : 128 ≤ Nat.log 2 n) :
    heavyEarlyLadderError n γ ≤
      ENNReal.ofReal
        (20 * (Nat.log 2 n : ℝ) *
          Real.exp (-heavyEarlyEnvelopeScale n γ)) := by
  unfold heavyEarlyLadderError
  calc
    (∑ j ∈ Finset.range (heavyEarlyStages n γ),
        heavyEarlyStageError n (heavyEarlyScale n γ j))
        ≤ ∑ j ∈ Finset.range (heavyEarlyStages n γ),
            ENNReal.ofReal
              (20 * Real.exp
                (-((4 : ℝ) ^ j * heavyEarlyEnvelopeScale n γ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hstage :=
        heavyEarlyStageError_le n (heavyEarlyScale n γ j)
          (heavyEarlyScale_pos n γ j)
          (heavyEarlyScale_small n γ j (Finset.mem_range.mp hj))
      rw [heavyEarlyEnvelope_eq n γ j] at hstage
      simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20)] using hstage
    _ = ENNReal.ofReal
          (∑ j ∈ Finset.range (heavyEarlyStages n γ),
            20 * Real.exp
              (-((4 : ℝ) ^ j * heavyEarlyEnvelopeScale n γ))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j hj
      positivity
    _ ≤ ENNReal.ofReal
          (20 * (Nat.log 2 n : ℝ) *
            Real.exp (-heavyEarlyEnvelopeScale n γ)) := by
      apply ENNReal.ofReal_le_ofReal
      have hstages := heavyEarlyStages_le_log n γ
      have hterms : ∀ j ∈ Finset.range (heavyEarlyStages n γ),
          20 * Real.exp
              (-((4 : ℝ) ^ j * heavyEarlyEnvelopeScale n γ)) ≤
            20 * Real.exp (-heavyEarlyEnvelopeScale n γ) := by
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff]
        have hpow : (1 : ℝ) ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
        have hscaleNonneg : 0 ≤ heavyEarlyEnvelopeScale n γ := by
          unfold heavyEarlyEnvelopeScale
          positivity
        nlinarith
      calc
        (∑ j ∈ Finset.range (heavyEarlyStages n γ),
            20 * Real.exp
              (-((4 : ℝ) ^ j * heavyEarlyEnvelopeScale n γ)))
            ≤ ∑ _j ∈ Finset.range (heavyEarlyStages n γ),
                20 * Real.exp (-heavyEarlyEnvelopeScale n γ) := by
          exact Finset.sum_le_sum hterms
        _ = (heavyEarlyStages n γ : ℝ) *
              (20 * Real.exp (-heavyEarlyEnvelopeScale n γ)) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ (Nat.log 2 n : ℝ) *
              (20 * Real.exp (-heavyEarlyEnvelopeScale n γ)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hstages
          · positivity
        _ = 20 * (Nat.log 2 n : ℝ) *
              Real.exp (-heavyEarlyEnvelopeScale n γ) := by ring

/-! ## Inhabitation gate -/

example :
    Reaches (heavyStateStep 3200) (heavyEarlySubrungHorizon 3200 20 0)
      (HeavyEarlyCheckpoint 3200 20 0)
      (HeavyEarlyCheckpoint 3200 20 1)
      (heavyEarlySubrungError 3200 20 0) := by
  exact heavyEarly_subrung 3200 (by norm_num) 20 0
    (by norm_num) (by norm_num) (by norm_num)

end Tri

#print axioms Tri.heavyEarlyCheckpoint_to_start
#print axioms Tri.heavyEarly_return_to_checkpoint
#print axioms Tri.heavyEarly_ruin_le
#print axioms Tri.heavyEarly_return_le
#print axioms Tri.heavyEarly_normalClock_le
#print axioms Tri.heavyEarly_blankClock_le
#print axioms Tri.heavyEarly_direction_le
#print axioms Tri.heavyEarlyJointClockError_le_rungError
#print axioms Tri.heavyEarly_subrung
#print axioms Tri.heavyEarlySubrungError_le
#print axioms Tri.heavyEarly_stage
#print axioms Tri.heavyEarlyStageError_le
#print axioms Tri.heavyEarly_ladder
#print axioms Tri.phase1SeedR_ge_eight
#print axioms Tri.heavyEarlyCheckpoint_zero_of_gap
#print axioms Tri.heavyEarly_reaches
#print axioms Tri.heavyEarlyLadderError_le_first
