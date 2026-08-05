/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBConstantGap
import Tri.DoubleBBandRung
import Tri.Phase2Additive

/-!
# The ordinary-productivity Double-B late ladder

Once the effective gap is a fixed fraction of `n`, the level-only productive
mass no longer loses the early-band cancellation.  This file first builds the
middle rung from gap `n/10` to level `n+n/2`; subsequent rungs will halve the
remaining co-level geometrically.
-/

namespace Tri

open scoped ENNReal

/-! ## Middle rung: constant gap to half co-level -/

def doubleMiddleLower (n : ℕ) : ℕ := n + n / 20
def doubleMiddleLowerR (n : ℕ) : ℕ := 2 * n - doubleMiddleLower n - 2
def doubleMiddleLowerD (n : ℕ) : ℕ := 2 * n - doubleMiddleLower n
def doubleMiddleStartGap (n : ℕ) : ℕ := n / 20

def doubleMiddleTarget (n : ℕ) : ℕ := 2 * n - n / 2
def doubleMiddleReturnLo (n : ℕ) : ℕ := doubleMiddleTarget n - 1
def doubleMiddleReturnB (n : ℕ) : ℕ :=
  2 * n - doubleMiddleReturnLo n - 2
def doubleMiddleReturnGap (n : ℕ) : ℕ := n / 32 + 1
def doubleMiddleHi (n : ℕ) : ℕ :=
  doubleMiddleTarget n + n / 32

def doubleMiddleResolutions (n : ℕ) : ℕ := 64 * n
def doubleMiddleHorizon (n : ℕ) : ℕ := 65536 * n

noncomputable def doubleMiddleError (n : ℕ) : ℝ≥0∞ :=
  doubleBandRungError n
    (doubleMiddleLower n) (doubleMiddleLowerR n)
    (doubleMiddleLowerD n) (doubleMiddleHi n)
    (doubleMiddleStartGap n) (doubleMiddleResolutions n)
    (doubleMiddleHorizon n)
    (doubleMiddleReturnLo n) (doubleMiddleReturnB n)
    (doubleMiddleReturnGap n)

/-- All integer geometry for the middle rung. -/
theorem doubleMiddle_geometry
    {n : ℕ} (hlog : 12 ≤ Nat.log 2 n) :
    doubleMiddleLower n < doubleMiddleHi n ∧
    doubleMiddleLower n + 2 ≤ doubleMiddleHi n ∧
    doubleMiddleLower n + doubleMiddleLowerR n + 2 = 2 * n ∧
    0 < doubleMiddleLower n ∧
    0 < doubleMiddleLowerR n ∧
    doubleMiddleLowerR n ≤ doubleMiddleLower n ∧
    doubleMiddleLower n + doubleMiddleLowerD n = 2 * n ∧
    doubleMiddleLowerD n < doubleMiddleLower n ∧
    doubleMiddleHi n ≤ 2 * n ∧
    n ≤ doubleMiddleLower n + 1 ∧
    doubleMiddleReturnLo n + doubleMiddleReturnB n + 2 = 2 * n ∧
    0 < doubleMiddleReturnLo n ∧
    0 < doubleMiddleReturnB n ∧
    doubleMiddleReturnB n ≤ doubleMiddleReturnLo n ∧
    doubleMiddleLower n < doubleMiddleReturnLo n + 1 ∧
    doubleMiddleReturnLo n + 1 ≤ doubleMiddleHi n ∧
    doubleMiddleReturnLo n + doubleMiddleReturnGap n ≤ doubleMiddleHi n := by
  have hn : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have h20 : 20 * (n / 20) ≤ n := Nat.mul_div_le n 20
  have h20u : n < 20 * (n / 20) + 20 := by
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have h2 : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have h2u : n < 2 * (n / 2) + 2 := by
    have hd := Nat.div_add_mod n 2
    have hm := Nat.mod_lt n (by norm_num : 0 < 2)
    omega
  have h32 : 32 * (n / 32) ≤ n := Nat.mul_div_le n 32
  simp only [doubleMiddleLower, doubleMiddleLowerR, doubleMiddleLowerD,
    doubleMiddleHi, doubleMiddleTarget, doubleMiddleReturnLo,
    doubleMiddleReturnB, doubleMiddleReturnGap]
  omega

/-- The public one-tenth-gap checkpoint lies above the nominal middle-rung
start. -/
theorem doubleMiddle_start_le
    {n : ℕ} (hlog : 12 ≤ Nat.log 2 n) :
    doubleMiddleLower n + doubleMiddleStartGap n ≤ n + n / 10 := by
  have hn : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  have h10 : 10 * (n / 10) ≤ n := Nat.mul_div_le n 10
  have h10u : n < 10 * (n / 10) + 10 := by
    have hd := Nat.div_add_mod n 10
    have hm := Nat.mod_lt n (by norm_num : 0 < 10)
    omega
  have h20 : 20 * (n / 20) ≤ n := Nat.mul_div_le n 20
  have h20u : n < 20 * (n / 20) + 20 := by
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  unfold doubleMiddleLower doubleMiddleStartGap
  omega

/-- An explicit ordinary-productivity rung reaches half co-level from the
constant-gap checkpoint. -/
theorem doubleMiddle_reaches
    (n : ℕ) (hn : 2 ≤ n) (hlog : 12 ≤ Nat.log 2 n) :
    Reaches (doubleStateStep n hn) (doubleMiddleHorizon n)
      (fun s => n + n / 10 ≤ s.1.doubleLevel)
      (fun s => doubleMiddleTarget n ≤ s.1.doubleLevel)
      (doubleMiddleError n) := by
  have hg := doubleMiddle_geometry hlog
  have hr :=
    doubleBandRung n hn
      (doubleMiddleLower n) (doubleMiddleLowerR n)
      (doubleMiddleLowerD n) (doubleMiddleHi n)
      (doubleMiddleStartGap n) (doubleMiddleResolutions n)
      (doubleMiddleHorizon n)
      hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1
      hg.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.1
      hg.2.2.2.2.2.2.2.2.2.1
      (doubleMiddleReturnLo n) (doubleMiddleReturnB n)
      (doubleMiddleReturnGap n)
      hg.2.2.2.2.2.2.2.2.2.2.1
      hg.2.2.2.2.2.2.2.2.2.2.2.1
      hg.2.2.2.2.2.2.2.2.2.2.2.2.1
      hg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hretEq :
      doubleMiddleReturnLo n + 1 = doubleMiddleTarget n := by
    unfold doubleMiddleReturnLo doubleMiddleTarget
    omega
  intro s hs
  have hpre :
      doubleMiddleLower n + doubleMiddleStartGap n ≤
        s.1.doubleLevel :=
    (doubleMiddle_start_le hlog).trans hs
  simpa only [hretEq, doubleMiddleError] using hr s hpre

/-! ## Dyadic co-level halving rungs -/

/-- Public checkpoint with remaining co-level `⌊n/2^s⌋`. -/
def doubleLateCheckpointLevel (n s : ℕ) : ℕ :=
  2 * n - phase2Scale n s

def DoubleLateCheckpoint (n s : ℕ) (z : DoubleState n) : Prop :=
  doubleLateCheckpointLevel n s ≤ z.1.doubleLevel

instance (n s : ℕ) : DecidablePred (DoubleLateCheckpoint n s) := by
  intro z
  unfold DoubleLateCheckpoint
  infer_instance

def doubleLateStartGap (n s : ℕ) : ℕ :=
  doubleLateCheckpointLevel n s - doubleMiddleLower n

def doubleLateReturnLo (n s : ℕ) : ℕ :=
  doubleLateCheckpointLevel n (s + 1) - 1

def doubleLateReturnB (n s : ℕ) : ℕ :=
  phase2Scale n (s + 1) - 1

def doubleLateReturnGap (n s : ℕ) : ℕ :=
  phase2Scale n (s + 1) / 16 + 1

def doubleLateHi (n s : ℕ) : ℕ :=
  doubleLateCheckpointLevel n (s + 1) +
    phase2Scale n (s + 1) / 16

def doubleLateResolutions (n s : ℕ) : ℕ :=
  64 * phase2Scale n s

def doubleLateHorizon (n : ℕ) : ℕ :=
  65536 * n

noncomputable def doubleLateRungError (n s : ℕ) : ℝ≥0∞ :=
  doubleBandRungError n
    (doubleMiddleLower n) (doubleMiddleLowerR n)
    (doubleMiddleLowerD n) (doubleLateHi n s)
    (doubleLateStartGap n s) (doubleLateResolutions n s)
    (doubleLateHorizon n)
    (doubleLateReturnLo n s) (doubleLateReturnB n s)
    (doubleLateReturnGap n s)

/-- One ordinary-productivity rung halves the dyadic co-level scale. -/
theorem doubleLate_rung
    (n : ℕ) (hn : 2 ≤ n) (s : ℕ)
    (hlog : 12 ≤ Nat.log 2 n) (hs : 1 ≤ s)
    (hq : 32 ≤ phase2Scale n (s + 1)) :
    Reaches (doubleStateStep n hn) (doubleLateHorizon n)
      (DoubleLateCheckpoint n s)
      (DoubleLateCheckpoint n (s + 1))
      (doubleLateRungError n s) := by
  have hnLarge : 4096 ≤ n := phase1_log_twelve_implies_size hlog
  let P := phase2Scale n s
  let Q := phase2Scale n (s + 1)
  have hP :
      P = n / 2 ^ s := by rfl
  have hQ :
      Q = n / 2 ^ (s + 1) := by rfl
  have hQP : Q = P / 2 := by
    rw [hQ, hP, pow_succ, Nat.div_div_eq_div_mul]
  have hP_le : P ≤ n / 2 := by
    rw [hP]
    apply Nat.div_le_div_left
    · calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    · norm_num
  have hQpos : 0 < Q := by omega
  have hQn : Q + 1 ≤ n := by omega
  have hQ16 : Q / 16 ≤ Q := Nat.div_le_self Q 16
  have h20 : 20 * (n / 20) ≤ n := Nat.mul_div_le n 20
  have h20u : n < 20 * (n / 20) + 20 := by
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have hstartEq :
      doubleMiddleLower n + doubleLateStartGap n s =
        doubleLateCheckpointLevel n s := by
    unfold doubleLateStartGap doubleLateCheckpointLevel
      doubleMiddleLower
    omega
  have hreturnEq :
      doubleLateReturnLo n s + 1 =
        doubleLateCheckpointLevel n (s + 1) := by
    unfold doubleLateReturnLo doubleLateCheckpointLevel
    omega
  have hreturnPop :
      doubleLateReturnLo n s + doubleLateReturnB n s + 2 =
        2 * n := by
    unfold doubleLateReturnLo doubleLateReturnB
      doubleLateCheckpointLevel
    dsimp only [phase2Scale] at hQ ⊢
    omega
  have hr :=
    doubleBandRung n hn
      (doubleMiddleLower n) (doubleMiddleLowerR n)
      (doubleMiddleLowerD n) (doubleLateHi n s)
      (doubleLateStartGap n s) (doubleLateResolutions n s)
      (doubleLateHorizon n)
      (by
        simp only [doubleMiddleLower, doubleLateHi,
          doubleLateCheckpointLevel]
        dsimp only [phase2Scale] at hP hQ ⊢
        omega)
      (by
        simp only [doubleMiddleLower, doubleLateHi,
          doubleLateCheckpointLevel]
        dsimp only [phase2Scale] at hP hQ ⊢
        omega)
      (by
        simp only [doubleMiddleLower, doubleMiddleLowerR]
        omega)
      (by unfold doubleMiddleLower; omega)
      (by simp only [doubleMiddleLowerR, doubleMiddleLower]; omega)
      (by
        simp only [doubleMiddleLowerR, doubleMiddleLower]
        omega)
      (by
        simp only [doubleMiddleLowerD, doubleMiddleLower]
        omega)
      (by
        simp only [doubleMiddleLowerD, doubleMiddleLower]
        omega)
      (by
        unfold doubleLateHi doubleLateCheckpointLevel
        dsimp only [phase2Scale] at hQ ⊢
        omega)
      (by unfold doubleMiddleLower; omega)
      (doubleLateReturnLo n s) (doubleLateReturnB n s)
      (doubleLateReturnGap n s)
      hreturnPop
      (by
        unfold doubleLateReturnLo doubleLateCheckpointLevel
        dsimp only [phase2Scale] at hQ ⊢
        omega)
      (by
        unfold doubleLateReturnB
        dsimp only [phase2Scale] at hQ ⊢
        omega)
      (by
        unfold doubleLateReturnB doubleLateReturnLo
          doubleLateCheckpointLevel
        dsimp only [phase2Scale] at hQ ⊢
        omega)
      (by
        unfold doubleMiddleLower doubleLateReturnLo
          doubleLateCheckpointLevel
        dsimp only [phase2Scale] at hQ ⊢
        omega)
      (by
        rw [hreturnEq]
        unfold doubleLateHi
        omega)
      (by
        unfold doubleLateReturnLo doubleLateReturnGap
          doubleLateHi doubleLateCheckpointLevel
        dsimp only [phase2Scale] at hQ ⊢
        omega)
  simpa only [DoubleLateCheckpoint, hstartEq, hreturnEq,
    doubleLateRungError] using hr

/-! ## Composition of the dyadic late ladder -/

def doubleLateStages (n γ : ℕ) : ℕ :=
  phase2StageCount n γ + 1

def doubleLateLadderHorizon (n γ : ℕ) : ℕ :=
  doubleLateStages n γ * doubleLateHorizon n

noncomputable def doubleLateLadderError (n γ : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (doubleLateStages n γ),
    doubleLateRungError n (1 + i)

/-- The late ladder contains at most `lg n + 1` rungs. -/
theorem doubleLateStages_le_log_add_one (n γ : ℕ) :
    doubleLateStages n γ ≤ Nat.log 2 n + 1 := by
  have hk := phase2StageCount_le_log n γ
  unfold doubleLateStages
  omega

/-- Every selected late rung retains a co-level scale of at least `32`. -/
theorem doubleLate_active_nextScale_ge_32
    {n γ i : ℕ} (hγ : 1 ≤ γ)
    (hlog : 128 ≤ Nat.log 2 n) (hi : i < doubleLateStages n γ) :
    32 ≤ phase2Scale n (1 + i + 1) := by
  rcases i with _ | j
  · have hnLarge : 4096 ≤ n :=
      phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    unfold phase2Scale
    norm_num only [zero_add, one_add_one_eq_two]
    omega
  · have hj : j < phase2StageCount n γ := by
      unfold doubleLateStages at hi
      omega
    have hq := phase2_active_nextScale_ge_32 hγ hlog hj
    change 32 ≤ n / 2 ^ (2 + j + 1) at hq
    change 32 ≤ n / 2 ^ (1 + (j + 1) + 1)
    rw [show 1 + (j + 1) + 1 = 2 + j + 1 by omega]
    exact hq

/-- The ordinary-productivity rungs compose from half co-level down to the
phase-3 logarithmic co-level threshold. -/
theorem doubleLate_ladder
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Reaches (doubleStateStep n hn) (doubleLateLadderHorizon n γ)
      (DoubleLateCheckpoint n 1)
      (DoubleLateCheckpoint n (2 + phase2StageCount n γ))
      (doubleLateLadderError n γ) := by
  let P : ℕ → DoubleState n → Prop :=
    fun i => DoubleLateCheckpoint n (1 + i)
  let T : ℕ → ℕ := fun _ => doubleLateHorizon n
  let ε : ℕ → ℝ≥0∞ := fun i => doubleLateRungError n (1 + i)
  have hrungs : ∀ i < doubleLateStages n γ,
      Reaches (doubleStateStep n hn) (T i) (P i) (P (i + 1)) (ε i) := by
    intro i hi
    have hq := doubleLate_active_nextScale_ge_32 hγ hlog hi
    have hr := doubleLate_rung n hn (1 + i)
      (hlog.trans' (by norm_num)) (by omega) hq
    simpa only [P, T, ε, Nat.add_assoc] using hr
  have hchain :=
    Reaches.chain
      (K := doubleStateStep n hn) (P := P) (T := T) (ε := ε) hrungs
  have hsum :
      (∑ i ∈ Finset.range (doubleLateStages n γ), T i) =
        doubleLateLadderHorizon n γ := by
    simp only [T, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rfl
  rw [hsum] at hchain
  have hidx :
      (phase2StageCount n γ + 1).succ =
        2 + phase2StageCount n γ := by omega
  simpa only [P, ε, doubleLateStages, doubleLateLadderError,
    Nat.add_assoc, Nat.one_add, hidx] using hchain

/-- The middle rung followed by the dyadic late ladder reaches the
logarithmic co-level checkpoint. -/
theorem doubleMiddleLate_reaches
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    Reaches (doubleStateStep n hn)
      (doubleMiddleHorizon n + doubleLateLadderHorizon n γ)
      (fun s => n + n / 10 ≤ s.1.doubleLevel)
      (DoubleLateCheckpoint n (2 + phase2StageCount n γ))
      (doubleMiddleError n + doubleLateLadderError n γ) := by
  have hm := doubleMiddle_reaches n hn (hlog.trans' (by norm_num))
  have hl := doubleLate_ladder n hn γ hlog hγ
  have htarget :
      (fun s : DoubleState n =>
        doubleMiddleTarget n ≤ s.1.doubleLevel) =
        DoubleLateCheckpoint n 1 := by
    funext s
    unfold doubleMiddleTarget DoubleLateCheckpoint
      doubleLateCheckpointLevel phase2Scale
    apply propext
    rfl
  simpa only [htarget] using hm.comp hl

/-- The middle rung and all dyadic late rungs fit in an explicit
`131072 n lg n` raw-interaction horizon. -/
theorem doubleMiddleLateHorizon_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) :
    doubleMiddleHorizon n + doubleLateLadderHorizon n γ ≤
      131072 * n * Nat.log 2 n := by
  have hk := doubleLateStages_le_log_add_one n γ
  unfold doubleMiddleHorizon doubleLateLadderHorizon doubleLateHorizon
  calc
    65536 * n + doubleLateStages n γ * (65536 * n)
        ≤ 65536 * n + (Nat.log 2 n + 1) * (65536 * n) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right (65536 * n) hk) _
    _ = (Nat.log 2 n + 2) * (65536 * n) := by ring
    _ ≤ (2 * Nat.log 2 n) * (65536 * n) := by
      apply Nat.mul_le_mul_right
      omega
    _ = 131072 * n * Nat.log 2 n := by ring

/-! ## Logarithmic co-level endgame -/

def doubleEndScale (n γ : ℕ) : ℕ :=
  phase2Scale n (2 + phase2StageCount n γ)

def doubleEndStartGap (n γ : ℕ) : ℕ :=
  doubleLateCheckpointLevel n (2 + phase2StageCount n γ) -
    doubleMiddleLower n

def doubleEndHi (n : ℕ) : ℕ := 2 * n - 1
def doubleEndReturnLo (n : ℕ) : ℕ := 2 * n - 3
def doubleEndReturnB (_n : ℕ) : ℕ := 1
def doubleEndReturnGap (_n : ℕ) : ℕ := 2

def doubleEndResolutions (n γ : ℕ) : ℕ :=
  64 * (γ * Nat.log 2 n + 1)

def doubleEndHorizon (n γ : ℕ) : ℕ :=
  65536 * n * (γ * Nat.log 2 n + 1)

noncomputable def doubleEndError (n γ : ℕ) : ℝ≥0∞ :=
  doubleBandRungError n
    (doubleMiddleLower n) (doubleMiddleLowerR n)
    (doubleMiddleLowerD n) (doubleEndHi n)
    (doubleEndStartGap n γ) (doubleEndResolutions n γ)
    (doubleEndHorizon n γ)
    (doubleEndReturnLo n) (doubleEndReturnB n)
    (doubleEndReturnGap n)

/-- The selected logarithmic co-level scale remains nontrivial. -/
theorem doubleEndScale_ge_32
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n)
    (hγ : 1 ≤ γ) (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    32 ≤ doubleEndScale n γ := by
  have hkpos := phase2StageCount_pos n γ
    (hlog.trans' (by norm_num)) hsize hγ
  let k := phase2StageCount n γ
  have hj : k - 1 < phase2StageCount n γ := by
    dsimp only [k]
    omega
  have hq := phase2_active_nextScale_ge_32 hγ hlog hj
  change 32 ≤ n / 2 ^ (2 + (k - 1) + 1) at hq
  unfold doubleEndScale phase2Scale
  rw [show 2 + (k - 1) + 1 = 2 + phase2StageCount n γ by
    dsimp only [k]
    omega] at hq
  exact hq

/-- The selected final dyadic co-level is at most half the logarithmic
threshold. -/
theorem doubleEndScale_le
    (n γ : ℕ) :
    2 * doubleEndScale n γ ≤ γ * Nat.log 2 n := by
  exact phase2StageCount_spec n γ

/-- The ordinary-productivity endgame reaches co-level at most two. -/
theorem doubleEnd_reaches
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (doubleStateStep n hn) (doubleEndHorizon n γ)
      (DoubleLateCheckpoint n (2 + phase2StageCount n γ))
      (fun z => 2 * n - 2 ≤ z.1.doubleLevel)
      (doubleEndError n γ) := by
  have hnLarge : 4096 ≤ n :=
    phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
  let Q := doubleEndScale n γ
  have hQ32 : 32 ≤ Q := by
    simpa only [Q] using doubleEndScale_ge_32 n γ hlog hγ hsize
  have hQsmall : 2 * Q ≤ γ * Nat.log 2 n := by
    simpa only [Q] using doubleEndScale_le n γ
  have hscaleSmall :
      2 * phase2Scale n (2 + phase2StageCount n γ) ≤
        γ * Nat.log 2 n := by
    simpa only [Q, doubleEndScale] using hQsmall
  have hγlog : 128 ≤ γ * Nat.log 2 n :=
    hlog.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hsize' : 6 * (γ * Nat.log 2 n) ≤ n := by
    simpa only [Nat.mul_assoc] using hsize
  have h20 : 20 * (n / 20) ≤ n := Nat.mul_div_le n 20
  have h20u : n < 20 * (n / 20) + 20 := by
    have hd := Nat.div_add_mod n 20
    have hm := Nat.mod_lt n (by norm_num : 0 < 20)
    omega
  have hstartEq :
      doubleMiddleLower n + doubleEndStartGap n γ =
        doubleLateCheckpointLevel n
          (2 + phase2StageCount n γ) := by
    simp only [doubleEndStartGap, doubleLateCheckpointLevel,
      doubleMiddleLower]
    omega
  have hr :=
    doubleBandRung n hn
      (doubleMiddleLower n) (doubleMiddleLowerR n)
      (doubleMiddleLowerD n) (doubleEndHi n)
      (doubleEndStartGap n γ) (doubleEndResolutions n γ)
      (doubleEndHorizon n γ)
      (by
        simp only [doubleMiddleLower, doubleEndHi]
        omega)
      (by
        simp only [doubleMiddleLower, doubleEndHi]
        omega)
      (by
        simp only [doubleMiddleLower, doubleMiddleLowerR]
        omega)
      (by unfold doubleMiddleLower; omega)
      (by simp only [doubleMiddleLowerR, doubleMiddleLower]; omega)
      (by simp only [doubleMiddleLowerR, doubleMiddleLower]; omega)
      (by simp only [doubleMiddleLowerD, doubleMiddleLower]; omega)
      (by simp only [doubleMiddleLowerD, doubleMiddleLower]; omega)
      (by unfold doubleEndHi; omega)
      (by unfold doubleMiddleLower; omega)
      (doubleEndReturnLo n) (doubleEndReturnB n)
      (doubleEndReturnGap n)
      (by
        unfold doubleEndReturnLo doubleEndReturnB
        omega)
      (by unfold doubleEndReturnLo; omega)
      (by unfold doubleEndReturnB; omega)
      (by unfold doubleEndReturnB doubleEndReturnLo; omega)
      (by unfold doubleMiddleLower doubleEndReturnLo; omega)
      (by unfold doubleEndReturnLo doubleEndHi; omega)
      (by
        unfold doubleEndReturnLo doubleEndReturnGap doubleEndHi
        omega)
  have hretEq : 2 * n - 3 + 1 = 2 * n - 2 := by omega
  simpa only [DoubleLateCheckpoint, hstartEq, doubleEndReturnLo,
    hretEq, doubleEndError] using hr

/-- The logarithmic endgame still has the required
`O(γ n lg n)` horizon. -/
theorem doubleEndHorizon_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    doubleEndHorizon n γ ≤ 131072 * γ * n * Nat.log 2 n := by
  have hpos : 1 ≤ γ * Nat.log 2 n :=
    Nat.mul_pos (by omega) (by omega)
  unfold doubleEndHorizon
  calc
    65536 * n * (γ * Nat.log 2 n + 1)
        ≤ 65536 * n * (2 * (γ * Nat.log 2 n)) := by
      gcongr
      omega
    _ = 131072 * γ * n * Nat.log 2 n := by ring

/-! ## Assembly through the near-consensus checkpoint -/

def doubleNearConsensusHorizon (n γ : ℕ) : ℕ :=
  doubleEarlyLadderHorizon n γ +
    doubleConstantGapHorizon n +
    (doubleMiddleHorizon n + doubleLateLadderHorizon n γ) +
    doubleEndHorizon n γ

noncomputable def doubleNearConsensusError (n γ : ℕ) : ℝ≥0∞ :=
  doubleEarlyLadderError n γ +
    doubleConstantGapError n +
    (doubleMiddleError n + doubleLateLadderError n γ) +
    doubleEndError n γ

/-- All proved Double-B ladders compose from the paper's initial square gap
to co-level at most two. -/
theorem doubleNearConsensus_reaches
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (doubleStateStep n hn) (doubleNearConsensusHorizon n γ)
      (DoubleBEarlyInitial n γ)
      (fun z => 2 * n - 2 ≤ z.1.doubleLevel)
      (doubleNearConsensusError n γ) := by
  have he := doubleEarly_reaches n hn γ
    (hlog.trans' (by norm_num)) hγ
  have hc := doubleConstantGap_reaches n hn
    (hlog.trans' (by norm_num))
  have hl := doubleMiddleLate_reaches n hn γ hlog hγ
  have hend := doubleEnd_reaches n hn γ hlog hγ hsize
  have h := ((he.comp hc).comp hl).comp hend
  simpa only [doubleNearConsensusHorizon, doubleNearConsensusError,
    Nat.add_assoc, add_assoc] using h

/-- The early joint-clock ladder costs at most `2304 n lg n`
interactions. -/
theorem doubleEarlyLadderHorizon_le
    (n γ : ℕ) :
    doubleEarlyLadderHorizon n γ ≤
      2304 * n * Nat.log 2 n := by
  have hk := doubleEarlyStages_le_log n γ
  unfold doubleEarlyLadderHorizon doubleEarlyStageHorizon
    doubleClockHorizon doubleClockBudget
  calc
    doubleEarlyStages n γ * (4 * (64 * (n + 2 * (4 * n))))
        ≤ Nat.log 2 n * (4 * (64 * (n + 2 * (4 * n)))) :=
      Nat.mul_le_mul_right _ hk
    _ = 2304 * n * Nat.log 2 n := by ring

/-- The two-stage constant-gap handoff costs at most `4608 n lg n`
interactions in the large-log regime. -/
theorem doubleConstantGapHorizon_le
    (n : ℕ) (hlog : 128 ≤ Nat.log 2 n) :
    doubleConstantGapHorizon n ≤
      4608 * n * Nat.log 2 n := by
  unfold doubleConstantGapHorizon doubleEarlyStageHorizon
    doubleClockHorizon doubleClockBudget
  calc
    2 * (4 * (64 * (n + 2 * (4 * n))))
        = 4608 * n := by ring
    _ ≤ 4608 * n * Nat.log 2 n := by
      nth_rewrite 1 [← mul_one (4608 * n)]
      exact Nat.mul_le_mul_left _ (by omega)

/-- The complete proved route to co-level two fits under a single
`270000 γ n lg n` horizon. -/
theorem doubleNearConsensusHorizon_le
    (n γ : ℕ) (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ) :
    doubleNearConsensusHorizon n γ ≤
      270000 * γ * n * Nat.log 2 n := by
  have he := doubleEarlyLadderHorizon_le n γ
  have hc := doubleConstantGapHorizon_le n hlog
  have hl := doubleMiddleLateHorizon_le n γ hlog
  have hend := doubleEndHorizon_le n γ hlog hγ
  unfold doubleNearConsensusHorizon
  calc
    doubleEarlyLadderHorizon n γ +
          doubleConstantGapHorizon n +
          (doubleMiddleHorizon n + doubleLateLadderHorizon n γ) +
          doubleEndHorizon n γ
        ≤ 2304 * n * Nat.log 2 n +
          4608 * n * Nat.log 2 n +
          131072 * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by omega
    _ = 137984 * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by ring
    _ ≤ 137984 * γ * n * Nat.log 2 n +
          131072 * γ * n * Nat.log 2 n := by
      gcongr
      exact Nat.mul_le_mul_left 137984 hγ
    _ = 269056 * γ * n * Nat.log 2 n := by ring
    _ ≤ 270000 * γ * n * Nat.log 2 n := by
      gcongr
      norm_num

end Tri

#print axioms Tri.doubleMiddle_geometry
#print axioms Tri.doubleMiddle_start_le
#print axioms Tri.doubleMiddle_reaches
#print axioms Tri.doubleLate_rung
#print axioms Tri.doubleLate_active_nextScale_ge_32
#print axioms Tri.doubleLate_ladder
#print axioms Tri.doubleMiddleLate_reaches
#print axioms Tri.doubleMiddleLateHorizon_le
#print axioms Tri.doubleEndScale_ge_32
#print axioms Tri.doubleEndScale_le
#print axioms Tri.doubleEnd_reaches
#print axioms Tri.doubleEndHorizon_le
#print axioms Tri.doubleNearConsensus_reaches
#print axioms Tri.doubleEarlyLadderHorizon_le
#print axioms Tri.doubleConstantGapHorizon_le
#print axioms Tri.doubleNearConsensusHorizon_le
