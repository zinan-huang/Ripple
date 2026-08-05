/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem4EntryUnconditional
import Tri.BudgetArith
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The unconditional paper-facing Theorem 4 entry clause

This module compresses the exact Phase-I/Phase-II horizon and error sums to
the public `C γ n lg n` and `n^{-cγ}` envelopes.
-/

namespace Tri.Byzantine

open scoped ENNReal NNReal

noncomputable section

/-! ## Phase-II schedule and deadline compression -/

/-- Fixed Phase-II scalar certificate, independent of the population and the
confidence parameter. -/
noncomputable def theorem4Phase2Scalars :
    RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal) :=
  Classical.choice
    (exists_relaxedScheduleScalars
      phase2HalfRate (6 / 5 : NNReal)
      (by norm_num [phase2HalfRate])
      (by
        rw [← NNReal.coe_lt_coe]
        norm_num))

/-- The Phase-II stage count is exactly the ordinary dyadic stage count
starting from minority scale `⌊n/4⌋`. -/
theorem phase2BufferedStageCount_eq_relaxed
    {n : ℕ} (hlog : 4 ≤ Nat.log 2 n) :
    phase2BufferedStageCount n =
      relaxedDyadicStageCount (n / 4) := by
  unfold phase2BufferedStageCount relaxedDyadicStageCount
  have hfour : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [hfour, Nat.log_div_base_pow]
  omega

/-- On every active Phase-II rung, the paper's floor minority scale is the
active dyadic scale generated from `⌊n/4⌋`. -/
theorem phase2DyadicMinorityScale_eq_relaxed
    {n j : ℕ}
    (hn4 : 1 ≤ n / 4)
    (hj : j < phase2BufferedStageCount n)
    (hlog : 4 ≤ Nat.log 2 n) :
    phase2DyadicMinorityScale n j =
      relaxedDyadicActiveScale (n / 4) j := by
  have hstage :
      j < relaxedDyadicStageCount (n / 4) := by
    rwa [← phase2BufferedStageCount_eq_relaxed hlog]
  rw [relaxedDyadicActiveScale_eq
    (n / 4) j (Nat.ne_of_gt hn4) hstage]
  unfold phase2DyadicMinorityScale phase2DyadicK
    relaxedDyadicScale
  rw [Nat.div_div_eq_div_mul]
  congr 1
  ring

/-- The sum of all adaptive Phase-II rung multipliers has only an additive
`2g` overhead over the dyadic stage count. -/
theorem phase2BufferedRungMultiplier_sum_le
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    {g n : ℕ}
    (hg : 1 ≤ g)
    (hlarge : 68 * g ≤ 3 * n) :
    (∑ j ∈ Finset.range (phase2BufferedStageCount n),
        phase2BufferedRungMultiplier S g n j) ≤
      S.R₀ * (phase2BufferedStageCount n + 2 * g) := by
  have hlog :=
    phase2BufferedStageCount_log_lower g n hg hlarge
  have hn4 : 1 ≤ n / 4 := by omega
  rw [phase2BufferedStageCount_eq_relaxed hlog]
  calc
    (∑ j ∈ Finset.range (relaxedDyadicStageCount (n / 4)),
        phase2BufferedRungMultiplier S g n j) =
        ∑ j ∈ Finset.range (relaxedDyadicStageCount (n / 4)),
          relaxedDyadicAdaptiveMultiplier S.R₀ g
            (relaxedDyadicActiveScale (n / 4) j) := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold phase2BufferedRungMultiplier
      rw [phase2DyadicMinorityScale_eq_relaxed
        hn4 (by
          rw [phase2BufferedStageCount_eq_relaxed hlog]
          exact Finset.mem_range.mp hj) hlog]
    _ ≤ S.R₀ * (relaxedDyadicStageCount (n / 4) + 2 * g) :=
      relaxedDyadicAdaptiveMultiplier_sum_le S.R₀ g (n / 4) hn4

/-- Exact Phase-II time is bounded linearly in the buffered scale `g`. -/
theorem phase2BufferedLadderHorizon_le_linear
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    {g n : ℕ}
    (hg : 1 ≤ g)
    (hlarge : 68 * g ≤ 3 * n)
    (hlogle : Nat.log 2 n ≤ g) :
    phase2BufferedLadderHorizon S g n
        (phase2BufferedStageCount n) ≤
      12288 * S.C * S.R₀ * g * n := by
  have hsum :=
    phase2BufferedRungMultiplier_sum_le S hg hlarge
  have hJ : phase2BufferedStageCount n ≤ g := by
    unfold phase2BufferedStageCount
    omega
  unfold phase2BufferedLadderHorizon
    phase2BufferedRungHorizon relaxedDyadicHorizon
  calc
    (∑ j ∈ Finset.range (phase2BufferedStageCount n),
        4096 * (S.C *
          phase2BufferedRungMultiplier S g n j) * n) =
        4096 * S.C * n *
          ∑ j ∈ Finset.range (phase2BufferedStageCount n),
            phase2BufferedRungMultiplier S g n j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 4096 * S.C * n *
        (S.R₀ * (phase2BufferedStageCount n + 2 * g)) :=
      Nat.mul_le_mul_left _ hsum
    _ ≤ 4096 * S.C * n * (S.R₀ * (3 * g)) := by
      gcongr
      omega
    _ = 12288 * S.C * S.R₀ * g * n := by ring

/-- The exact two-phase deadline fits one fixed multiple of `g n`. -/
theorem phase12Horizon_le_linear
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    {g n : ℕ}
    (hg : 1 ≤ g)
    (hlarge : 68 * g ≤ 3 * n)
    (hlogle : Nat.log 2 n ≤ g) :
    phase1RawDyadicLadderHorizon n (Nat.log 2 n) +
        phase2BufferedLadderHorizon S g n
          (phase2BufferedStageCount n) ≤
      (40 + 12288 * S.C * S.R₀) * g * n := by
  have hphase1 :
      phase1RawDyadicLadderHorizon n (Nat.log 2 n) ≤
        40 * g * n := by
    unfold phase1RawDyadicLadderHorizon
    nlinarith [Nat.mul_le_mul_right (40 * n) hlogle]
  have hphase2 :=
    phase2BufferedLadderHorizon_le_linear S hg hlarge hlogle
  calc
    phase1RawDyadicLadderHorizon n (Nat.log 2 n) +
          phase2BufferedLadderHorizon S g n
            (phase2BufferedStageCount n) ≤
        40 * g * n + 12288 * S.C * S.R₀ * g * n :=
      Nat.add_le_add hphase1 hphase2
    _ = (40 + 12288 * S.C * S.R₀) * g * n := by ring

/-! ## Logarithmic coefficients and real-power conversion -/

/-- An eighth power of every sufficiently large binary logarithm fits under
the corresponding power of two. -/
theorem pow_eight_le_two_pow :
    ∀ L : ℕ, 64 ≤ L → L ^ 8 ≤ 2 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
      norm_num
  | succ L hbase ih =>
      have hlin : 16 * (L + 1) ≤ 17 * L := by omega
      have hp := Nat.pow_le_pow_left hlin 8
      have hconst : (17 : ℕ) ^ 8 ≤ 2 * 16 ^ 8 := by norm_num
      have hstep : (L + 1) ^ 8 ≤ 2 * L ^ 8 := by
        have hmul :
            16 ^ 8 * (L + 1) ^ 8 ≤
              16 ^ 8 * (2 * L ^ 8) := by
          calc
            16 ^ 8 * (L + 1) ^ 8 =
                (16 * (L + 1)) ^ 8 := by ring
            _ ≤ (17 * L) ^ 8 := hp
            _ = 17 ^ 8 * L ^ 8 := by ring
            _ ≤ (2 * 16 ^ 8) * L ^ 8 :=
              Nat.mul_le_mul_right _ hconst
            _ = 16 ^ 8 * (2 * L ^ 8) := by ring
        exact Nat.le_of_mul_le_mul_left hmul (by positivity)
      calc
        (L + 1) ^ 8 ≤ 2 * L ^ 8 := hstep
        _ ≤ 2 * 2 ^ L := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (L + 1) := by rw [pow_succ]; ring

/-- The logarithmic stage coefficient is at most an eighth power of the
population once `lg n ≥ 64`. -/
theorem phase2BufferedStageCount_le_rpow
    {n : ℕ} (hlog : 64 ≤ Nat.log 2 n) :
    (phase2BufferedStageCount n : ℝ≥0∞) ≤
      (n : ℝ≥0∞) ^ (1 / 8 : ℝ) := by
  let L := Nat.log 2 n
  let J := phase2BufferedStageCount n
  have hJL : J ≤ L := by
    dsimp only [J, L]
    unfold phase2BufferedStageCount
    exact Nat.sub_le _ _
  have hn : n ≠ 0 := by
    intro hn
    subst n
    norm_num at hlog
  have hnat : J ^ 8 ≤ n := by
    calc
      J ^ 8 ≤ L ^ 8 := Nat.pow_le_pow_left hJL 8
      _ ≤ 2 ^ L := pow_eight_le_two_pow L hlog
      _ ≤ n := Nat.pow_log_le_self 2 hn
  have hcast :
      ((J : ℝ≥0∞) ^ (8 : ℕ)) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hnat
  have hroot :=
    ENNReal.rpow_le_rpow hcast (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hleft :
      (((J : ℝ≥0∞) ^ (8 : ℕ)) ^ (1 / 8 : ℝ)) =
        (J : ℝ≥0∞) := by
    rw [← ENNReal.rpow_natCast (J : ℝ≥0∞) 8,
      ← ENNReal.rpow_mul]
    norm_num
  rw [hleft] at hroot
  exact hroot

/-- Above a fixed binary-log threshold, the natural floor logarithm dominates
the real natural logarithm. -/
theorem theorem4RealLog_le_natLog
    {n : ℕ} (hlog : 128 ≤ Nat.log 2 n) :
    Real.log (n : ℝ) ≤ (Nat.log 2 n : ℝ) := by
  have hn : 0 < n := by
    have hnLarge : 4096 ≤ n :=
      phase1_log_twelve_implies_size (hlog.trans' (by norm_num))
    omega
  have hlogn :
      Real.log n ≤
        ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
    have hup : n < 2 ^ (Nat.log 2 n + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) n
    have hlt :
        Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
      Real.log_lt_log (by exact_mod_cast hn)
        (by exact_mod_cast hup)
    rw [Real.log_pow] at hlt
    push_cast at hlt
    linarith
  have hL : (128 : ℝ) ≤ Nat.log 2 n := by
    exact_mod_cast hlog
  have hfactor :
      ((Nat.log 2 n : ℝ) + 1) * Real.log 2 ≤
        (Nat.log 2 n : ℝ) := by
    have hlog2 : Real.log 2 < (0.6931471808 : ℝ) :=
      Real.log_two_lt_d9
    have hlog2Nonneg : 0 ≤ Real.log 2 :=
      (Real.log_pos (by norm_num)).le
    nlinarith
  exact hlogn.trans hfactor

/-- Convert a real exponential estimate to an inverse `ENNReal` power. -/
theorem theorem4_ofReal_exp_neg_le_inv_rpow
    (n : ℕ) (hn : 0 < n) (S a : ℝ)
    (hS : Real.log (n : ℝ) * a ≤ S) :
    ENNReal.ofReal (Real.exp (-S)) ≤
      (n : ℝ≥0∞)⁻¹ ^ a := by
  have hrpow :
      (n : ℝ≥0∞)⁻¹ ^ a =
        ENNReal.ofReal ((n : ℝ) ^ (-a)) := by
    rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
      ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hn),
      ← ENNReal.ofReal_inv_of_pos (by positivity),
      Real.rpow_neg (by positivity)]
  rw [hrpow]
  apply ENNReal.ofReal_le_ofReal
  have hpExp : (0 : ℝ) < Real.exp (-S) := Real.exp_pos _
  have hpPow : (0 : ℝ) < (n : ℝ) ^ (-a) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hlogIneq :
      Real.log (Real.exp (-S)) ≤
        Real.log ((n : ℝ) ^ (-a)) := by
    rw [Real.log_exp, Real.log_rpow (by exact_mod_cast hn)]
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogIneq
  rwa [Real.exp_log hpExp, Real.exp_log hpPow] at hexp

/-- The elementary rational lower bound used for the directional
`log(6/5)` exponent. -/
theorem one_sixth_le_log_six_fifths :
    (1 / 6 : ℝ) ≤ Real.log (6 / 5 : ℝ) := by
  have h :=
    Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 5 / 6 by norm_num)
  have hinv : (5 / 6 : ℝ) = (6 / 5 : ℝ)⁻¹ := by norm_num
  rw [hinv, Real.log_inv] at h
  norm_num at h ⊢
  linarith

/-- A positive population power can absorb a coefficient power while leaving
a shallower inverse-power tail. -/
theorem rpow_mul_inv_rpow_le
    (n : ℕ) (hn : 1 ≤ n)
    (u a b : ℝ)
    (hu : 0 ≤ u)
    (hub : u + b ≤ a) :
    (n : ℝ≥0∞) ^ u * (n : ℝ≥0∞)⁻¹ ^ a ≤
      (n : ℝ≥0∞)⁻¹ ^ b := by
  have hn1 : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le one_pos hn1)
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hinv0 : (n : ℝ≥0∞)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr hntop
  have hinvtop : (n : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hn0
  have hab : b ≤ a := by linarith
  have hsplit :
      (n : ℝ≥0∞)⁻¹ ^ a =
        (n : ℝ≥0∞)⁻¹ ^ (a - b) *
          (n : ℝ≥0∞)⁻¹ ^ b := by
    rw [← ENNReal.rpow_add _ _ hinv0 hinvtop]
    congr 1
    ring
  have hcoeff :
      (n : ℝ≥0∞) ^ u ≤
        (n : ℝ≥0∞) ^ (a - b) := by
    exact ENNReal.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpow0 :
      (n : ℝ≥0∞) ^ (a - b) ≠ 0 := by
    exact ne_of_gt
      (ENNReal.rpow_pos
        (lt_of_lt_of_le one_pos hn1) hntop)
  have hpowtop :
      (n : ℝ≥0∞) ^ (a - b) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) hntop
  have hclear :
      (n : ℝ≥0∞)⁻¹ ^ (a - b) =
        ((n : ℝ≥0∞) ^ (a - b))⁻¹ := by
    rw [ENNReal.inv_rpow]
  rw [hsplit, hclear]
  calc
    (n : ℝ≥0∞) ^ u *
          (((n : ℝ≥0∞) ^ (a - b))⁻¹ *
            (n : ℝ≥0∞)⁻¹ ^ b) =
        ((n : ℝ≥0∞) ^ u *
          ((n : ℝ≥0∞) ^ (a - b))⁻¹) *
            (n : ℝ≥0∞)⁻¹ ^ b := by rw [mul_assoc]
    _ ≤ ((n : ℝ≥0∞) ^ (a - b) *
          ((n : ℝ≥0∞) ^ (a - b))⁻¹) *
            (n : ℝ≥0∞)⁻¹ ^ b := by
      exact mul_le_mul_left
        (mul_le_mul_left hcoeff _) _
    _ = (n : ℝ≥0∞)⁻¹ ^ b := by
      rw [ENNReal.mul_inv_cancel hpow0 hpowtop, one_mul]

/-! ## Phase-II error compression -/

/-- One buffered Phase-II envelope is at most three copies of the
`n^{-γ/6}` tail. -/
theorem phase2BufferedRungEnvelope_le_power
    (n γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n)
    (hγ : 1 ≤ γ) :
    phase2BufferedRungEnvelope (γ * Nat.log 2 n) ≤
      3 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 6 : ℝ) * (γ : ℝ)) := by
  let L := Nat.log 2 n
  let g := γ * L
  let p := (n : ℝ≥0∞)⁻¹ ^ ((1 / 6 : ℝ) * (γ : ℝ))
  have hn : 0 < n := by
    have := phase1_log_twelve_implies_size
      (hlog.trans' (by norm_num))
    omega
  have hlogle := theorem4RealLog_le_natLog hlog
  have hdirS :
      Real.log (n : ℝ) * ((1 / 6 : ℝ) * (γ : ℝ)) ≤
        (g : ℝ) * Real.log (6 / 5 : ℝ) := by
    calc
      Real.log (n : ℝ) * ((1 / 6 : ℝ) * (γ : ℝ)) ≤
          (L : ℝ) * ((1 / 6 : ℝ) * (γ : ℝ)) :=
        mul_le_mul_of_nonneg_right hlogle (by positivity)
      _ ≤ (L : ℝ) * ((γ : ℝ) * Real.log (6 / 5 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          (1 / 6 : ℝ) * (γ : ℝ) =
              (γ : ℝ) * (1 / 6 : ℝ) := by ring
          _ ≤ (γ : ℝ) * Real.log (6 / 5 : ℝ) :=
            mul_le_mul_of_nonneg_left
              one_sixth_le_log_six_fifths (by positivity)
      _ = (g : ℝ) * Real.log (6 / 5 : ℝ) := by
        dsimp only [g, L]
        push_cast
        ring
  have hdir :
      ENNReal.ofReal
          (Real.exp
            (-((g : ℝ) * Real.log (6 / 5 : ℝ)))) ≤ p :=
    theorem4_ofReal_exp_neg_le_inv_rpow
      n hn ((g : ℝ) * Real.log (6 / 5 : ℝ))
      ((1 / 6 : ℝ) * (γ : ℝ)) hdirS
  have hfastS :
      Real.log (n : ℝ) * (γ : ℝ) ≤ (g : ℝ) := by
    calc
      Real.log (n : ℝ) * (γ : ℝ) ≤
          (L : ℝ) * (γ : ℝ) :=
        mul_le_mul_of_nonneg_right hlogle (by positivity)
      _ = (g : ℝ) := by
        dsimp only [g, L]
        push_cast
        ring
  have hfast :
      ENNReal.ofReal (Real.exp (-(g : ℝ))) ≤
        (n : ℝ≥0∞)⁻¹ ^ (γ : ℝ) :=
    theorem4_ofReal_exp_neg_le_inv_rpow
      n hn (g : ℝ) (γ : ℝ) hfastS
  have hinvle : (n : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]
    exact_mod_cast (show 1 ≤ n by omega)
  have hfast' :
      ENNReal.ofReal (Real.exp (-(g : ℝ))) ≤ p := by
    exact hfast.trans
      (ENNReal.rpow_le_rpow_of_exponent_ge
        hinvle (by
          have : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
          nlinarith))
  change
    ENNReal.ofReal
          (Real.exp
            (-((g : ℝ) * Real.log (6 / 5 : ℝ)))) +
        ENNReal.ofReal (Real.exp (-(g : ℝ))) +
        ENNReal.ofReal (Real.exp (-(g : ℝ))) ≤
      3 * p
  calc
    _ ≤ p + p + p := add_le_add (add_le_add hdir hfast') hfast'
    _ = 3 * p := by ring

/-- The complete buffered Phase-II error is at most
`3 n^{-γ/24}` after absorbing its logarithmic stage count. -/
theorem phase2BufferedLadderError_le_power
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (n γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n)
    (hγ : 1 ≤ γ)
    (hlarge : 68 * (γ * Nat.log 2 n) ≤ 3 * n) :
    phase2BufferedLadderError S (γ * Nat.log 2 n) n
        (phase2BufferedStageCount n) ≤
      3 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 24 : ℝ) * (γ : ℝ)) := by
  let J := phase2BufferedStageCount n
  let p₆ := (n : ℝ≥0∞)⁻¹ ^ ((1 / 6 : ℝ) * (γ : ℝ))
  let p₂₄ := (n : ℝ≥0∞)⁻¹ ^ ((1 / 24 : ℝ) * (γ : ℝ))
  have hg : 1 ≤ γ * Nat.log 2 n := by
    have hL : 1 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
    nlinarith
  have hbase :=
    phase2BufferedLadderError_le
      S (γ * Nat.log 2 n) n J
      hg
      hlarge
      (fun j hj =>
        phase2BufferedStageCount_rung_le
          (d := γ * Nat.log 2 n) (n := n) (j := j)
          hg hlarge hj)
  have henvelope :=
    phase2BufferedRungEnvelope_le_power n γ hlog hγ
  have hJ :=
    phase2BufferedStageCount_le_rpow
      (hlog.trans' (by norm_num))
  have hn1 : 1 ≤ n := by
    have := phase1_log_twelve_implies_size
      (hlog.trans' (by norm_num))
    omega
  have hproduct :
      (J : ℝ≥0∞) * p₆ ≤ p₂₄ := by
    calc
      (J : ℝ≥0∞) * p₆ ≤
          (n : ℝ≥0∞) ^ (1 / 8 : ℝ) * p₆ :=
        mul_le_mul_left hJ p₆
      _ ≤ p₂₄ := by
        exact rpow_mul_inv_rpow_le n hn1
          (1 / 8 : ℝ)
          ((1 / 6 : ℝ) * (γ : ℝ))
          ((1 / 24 : ℝ) * (γ : ℝ))
          (by norm_num)
          (by
            have : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
            nlinarith)
  calc
    phase2BufferedLadderError S (γ * Nat.log 2 n) n J ≤
        (J : ℝ≥0∞) *
          phase2BufferedRungEnvelope (γ * Nat.log 2 n) :=
      hbase
    _ ≤ (J : ℝ≥0∞) * (3 * p₆) :=
      mul_le_mul_right henvelope _
    _ = 3 * ((J : ℝ≥0∞) * p₆) := by ring
    _ ≤ 3 * p₂₄ := mul_le_mul_right hproduct 3

/-! ## Phase-I error compression -/

/-- The corrected raw Phase-I error splits into the dyadic-square envelope
and the repeated productive-clock tail. -/
theorem phase1RawDyadicLadderError_eq
    (n d J : ℕ) :
    phase1RawDyadicLadderError n d J =
      phase1DyadicEnvelopeError n d J +
        (J : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2) ^ n := by
  simp [phase1RawDyadicLadderError,
    phase1RawDyadicRungError,
    phase1DyadicEnvelopeError,
    Finset.sum_add_distrib, nsmul_eq_mul]

/-- The repeated Phase-I productive-clock error is already at most
`n^{-γ}` under the paper's time guard. -/
theorem phase1RawClockError_le_power
    (n γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n)
    (hγ : 1 ≤ γ)
    (hguard : 6 * γ * Nat.log 2 n ≤ n) :
    (Nat.log 2 n : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2) ^ n ≤
      (n : ℝ≥0∞)⁻¹ ^ (γ : ℝ) := by
  let L := Nat.log 2 n
  have hn : 0 < n := by
    have := phase1_log_twelve_implies_size
      (hlog.trans' (by norm_num))
    omega
  have hn1 : 1 ≤ n := by omega
  have hlogle := theorem4RealLog_le_natLog hlog
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hS :
      Real.log (n : ℝ) * (2 * (γ : ℝ) + 1) ≤
        (n : ℝ) * Real.log 2 := by
    have hγR : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
    have hguardR :
        6 * (γ : ℝ) * (L : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hguard
    calc
      Real.log (n : ℝ) * (2 * (γ : ℝ) + 1) ≤
          (L : ℝ) * (2 * (γ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hlogle (by positivity)
      _ ≤ (L : ℝ) * (3 * (γ : ℝ)) := by
        gcongr
        linarith
      _ ≤ (n : ℝ) * (1 / 2 : ℝ) := by
        nlinarith
      _ ≤ (n : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hlog2 (by positivity)
  have hhalfReal :
      (1 / 2 : ℝ) ^ n =
        Real.exp (-((n : ℝ) * Real.log 2)) := by
    rw [← Real.exp_log
      (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ n)]
    rw [Real.log_pow]
    have hlogHalf :
        Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hlogHalf]
    congr 1
    ring
  have hhalfENN :
      ((1 : ℝ≥0∞) / 2) ^ n =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    have hhalf :
        (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos
        (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hhalf, ENNReal.ofReal_pow]
    positivity
  have hhalf :
      ((1 : ℝ≥0∞) / 2) ^ n ≤
        (n : ℝ≥0∞)⁻¹ ^ (2 * (γ : ℝ) + 1) := by
    rw [hhalfENN, hhalfReal]
    exact theorem4_ofReal_exp_neg_le_inv_rpow
      n hn ((n : ℝ) * Real.log 2)
      (2 * (γ : ℝ) + 1) hS
  have hL :
      (L : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast Nat.log_le_self 2 n
  calc
    (L : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2) ^ n ≤
        (n : ℝ≥0∞) *
          (n : ℝ≥0∞)⁻¹ ^ (2 * (γ : ℝ) + 1) :=
      mul_le_mul hL hhalf bot_le bot_le
    _ = (n : ℝ≥0∞) ^ (1 : ℝ) *
          (n : ℝ≥0∞)⁻¹ ^ (2 * (γ : ℝ) + 1) := by
      rw [ENNReal.rpow_one]
    _ ≤ (n : ℝ≥0∞)⁻¹ ^ (γ : ℝ) := by
      exact rpow_mul_inv_rpow_le n hn1
        1 (2 * (γ : ℝ) + 1) (γ : ℝ)
        (by norm_num)
        (by
          have : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
          linarith)

/-- The complete corrected raw Phase-I error is the dyadic-square power tail
plus one faster clock tail. -/
theorem phase1RawDyadicLadderError_le_power
    (n γ d : ℕ)
    (hlog : 128 ≤ Nat.log 2 n)
    (hγ : 1 ≤ γ)
    (hguard : 6 * γ * Nat.log 2 n ≤ n)
    (hseed : γ * n * Nat.log 2 n ≤ d ^ 2) :
    phase1RawDyadicLadderError n d (Nat.log 2 n) ≤
      4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 68 : ℝ) * (γ : ℝ)) +
        (n : ℝ≥0∞)⁻¹ ^ (γ : ℝ) := by
  rw [phase1RawDyadicLadderError_eq]
  exact add_le_add
    (phase1DyadicEnvelopeError_le_power_of_log_ge_fortysix
      n γ d (Nat.log 2 n)
      (hlog.trans' (by norm_num)) hγ hseed)
    (phase1RawClockError_le_power n γ hlog hγ hguard)

/-- A natural constant clears a real population power once an integral power
of that constant fits below the chosen global binary threshold. -/
theorem theorem4_constant_le_rpow
    (A k N n : ℕ) (e : ℝ)
    (hk : 1 ≤ k)
    (hAk : A ^ k ≤ 2 ^ N)
    (hn : 2 ^ N ≤ n)
    (he : (1 / (k : ℝ)) ≤ e) :
    (A : ℝ≥0∞) ≤ (n : ℝ≥0∞) ^ e := by
  have hn1 : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    have hpow : 1 ≤ 2 ^ N := Nat.one_le_two_pow
    exact_mod_cast hpow.trans hn
  have hbase :
      ((A : ℝ≥0∞) ^ (k : ℕ)) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hAk.trans hn
  have hroot :
      (((A : ℝ≥0∞) ^ (k : ℕ)) ^ (1 / (k : ℝ))) =
        (A : ℝ≥0∞) := by
    rw [← ENNReal.rpow_natCast (A : ℝ≥0∞) k,
      ← ENNReal.rpow_mul]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hkprod : (k : ℝ) * (1 / (k : ℝ)) = 1 := by
      field_simp
    rw [hkprod, ENNReal.rpow_one]
  calc
    (A : ℝ≥0∞) =
        ((A : ℝ≥0∞) ^ (k : ℕ)) ^ (1 / (k : ℝ)) :=
      hroot.symm
    _ ≤ (n : ℝ≥0∞) ^ (1 / (k : ℝ)) :=
      ENNReal.rpow_le_rpow hbase (by positivity)
    _ ≤ (n : ℝ≥0∞) ^ e :=
      ENNReal.rpow_le_rpow_of_exponent_le hn1 he

/-! ## Absorbing constant coefficients into the final envelope -/

set_option exponentiation.threshold 1100 in
/-- Numerical certificate used to absorb the coefficient four in the
Phase-I tail into one third of the final error envelope. -/
lemma twelve_pow_136_le_two_pow_1000 :
    (12 : ℕ) ^ 136 ≤ 2 ^ 1000 := by
  norm_num

set_option exponentiation.threshold 1100 in
/-- Numerical certificate used to absorb the coefficient three in the
Phase-II tail into one third of the final error envelope. -/
lemma nine_pow_30_le_two_pow_1000 :
    (9 : ℕ) ^ 30 ≤ 2 ^ 1000 := by
  norm_num

set_option exponentiation.threshold 1100 in
/-- Numerical certificate placing the remaining Phase-I clock tail below
one third of the final error envelope. -/
lemma three_pow_two_le_two_pow_1000 :
    (3 : ℕ) ^ 2 ≤ 2 ^ 1000 := by
  norm_num

set_option exponentiation.threshold 1100 in
/-- The global population threshold is large enough for the physical
three-molecule transition rule. -/
lemma three_le_two_pow_1000 :
    (3 : ℕ) ≤ 2 ^ 1000 := by
  calc
    3 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ 1000 :=
      Nat.pow_le_pow_right
        (by decide : (1 : ℕ) ≤ 2)
        (show 2 ≤ 1000 by omega)

/-! ## Final two-phase assembly -/

set_option exponentiation.threshold 1100 in
/-- The sum of the exact corrected Phase-I and buffered Phase-II errors fits
the single public `n^{-γ/136}` envelope above the global threshold. -/
theorem phase12Error_le_headline
    (S : RelaxedScheduleScalars phase2HalfRate (6 / 5 : NNReal))
    (n γ d : ℕ)
    (hn : 2 ^ 1000 ≤ n)
    (hγ : 1 ≤ γ)
    (hguard : 6 * γ * Nat.log 2 n ≤ n)
    (hlarge : 68 * (γ * Nat.log 2 n) ≤ 3 * n)
    (hseed : γ * n * Nat.log 2 n ≤ d ^ 2) :
    phase1RawDyadicLadderError n d (Nat.log 2 n) +
        phase2BufferedLadderError S (γ * Nat.log 2 n) n
          (phase2BufferedStageCount n) ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 136 : ℝ) * (γ : ℝ)) := by
  have hlog : 128 ≤ Nat.log 2 n := by
    have hlog1000 : 1000 ≤ Nat.log 2 n :=
      Nat.le_log_of_pow_le (by decide) hn
    omega
  let e₁ :=
    4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 68 : ℝ) * (γ : ℝ))
  let ec := (n : ℝ≥0∞)⁻¹ ^ (γ : ℝ)
  let e₂ :=
    3 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 24 : ℝ) * (γ : ℝ))
  let w :=
    (n : ℝ≥0∞)⁻¹ ^ ((1 / 136 : ℝ) * (γ : ℝ))
  have hphase1 :=
    phase1RawDyadicLadderError_le_power
      n γ d hlog hγ hguard hseed
  have hphase2 :=
    phase2BufferedLadderError_le_power
      S n γ hlog hγ hlarge
  have h12 :
      (12 : ℝ≥0∞) ≤
        (n : ℝ≥0∞) ^
          (((1 / 68 : ℝ) * (γ : ℝ)) -
            ((1 / 136 : ℝ) * (γ : ℝ))) := by
    apply theorem4_constant_le_rpow 12 136 1000 n
    · norm_num
    · exact twelve_pow_136_le_two_pow_1000
    · exact hn
    · have : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
      nlinarith
  have h9 :
      (9 : ℝ≥0∞) ≤
        (n : ℝ≥0∞) ^
          (((1 / 24 : ℝ) * (γ : ℝ)) -
            ((1 / 136 : ℝ) * (γ : ℝ))) := by
    apply theorem4_constant_le_rpow 9 30 1000 n
    · norm_num
    · exact nine_pow_30_le_two_pow_1000
    · exact hn
    · have : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
      nlinarith
  have h3 :
      (3 : ℝ≥0∞) ≤
        (n : ℝ≥0∞) ^
          ((γ : ℝ) -
            ((1 / 136 : ℝ) * (γ : ℝ))) := by
    apply theorem4_constant_le_rpow 3 2 1000 n
    · norm_num
    · exact three_pow_two_le_two_pow_1000
    · exact hn
    · have : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
      nlinarith
  have he₁ : e₁ ≤ (1 / 3 : ℝ≥0∞) * w := by
    exact inv_rpow_third 4
      ((1 / 68 : ℝ) * (γ : ℝ))
      ((1 / 136 : ℝ) * (γ : ℝ))
      n (by
        have : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
        nlinarith)
      (by
        have hpow : 1 ≤ 2 ^ 1000 := Nat.one_le_two_pow
        exact hpow.trans hn)
      (by
        have hm : (3 : ℝ≥0∞) * 4 = 12 := by norm_num
        rw [hm]
        exact h12)
  have hec : ec ≤ (1 / 3 : ℝ≥0∞) * w := by
    have h :=
      inv_rpow_third 1
        (γ : ℝ)
        ((1 / 136 : ℝ) * (γ : ℝ))
        n (by
          have : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
          nlinarith)
        (by
          have hpow : 1 ≤ 2 ^ 1000 := Nat.one_le_two_pow
          exact hpow.trans hn)
        (by
          have hm : (3 : ℝ≥0∞) * 1 = 3 := by norm_num
          rw [hm]
          exact h3)
    simpa [ec, w] using h
  have he₂ : e₂ ≤ (1 / 3 : ℝ≥0∞) * w := by
    exact inv_rpow_third 3
      ((1 / 24 : ℝ) * (γ : ℝ))
      ((1 / 136 : ℝ) * (γ : ℝ))
      n (by
        have : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
        nlinarith)
      (by
        have hpow : 1 ≤ 2 ^ 1000 := Nat.one_le_two_pow
        exact hpow.trans hn)
      (by
        have hm : (3 : ℝ≥0∞) * 3 = 9 := by norm_num
        rw [hm]
        exact h9)
  calc
    phase1RawDyadicLadderError n d (Nat.log 2 n) +
          phase2BufferedLadderError S (γ * Nat.log 2 n) n
            (phase2BufferedStageCount n) ≤
        (e₁ + ec) + e₂ :=
      add_le_add hphase1 hphase2
    _ ≤ w := three_thirds_le he₁ hec he₂

set_option exponentiation.threshold 1100 in
/-- The entry clause of paper Theorem 4, corrected to the reached-by-deadline
event and carrying the necessary Phase-II large-population side condition, is
fully unconditional. -/
theorem theorem4_entry :
    Theorem4_entry_statement := by
  let S := theorem4Phase2Scalars
  let C := 40 + 12288 * S.C * S.R₀
  refine
    ⟨C, 2 ^ 1000, (1 / 136 : ℝ),
      (by
        dsimp only [C]
        omega),
      (by norm_num),
      (by
        exact three_le_two_pow_1000), ?_⟩
  intro n γ hn hγ hguard hstrict x₀ y₀ B d hinit σ
  let g := γ * Nat.log 2 n
  let s₀ := theorem4InitialState n x₀ y₀ B hinit.1
  let T :=
    phase1RawDyadicLadderHorizon n (Nat.log 2 n) +
      phase2BufferedLadderHorizon S g n
        (phase2BufferedStageCount n)
  have h3 : 3 ≤ n := by
    exact three_le_two_pow_1000.trans hn
  have hlog : 1000 ≤ Nat.log 2 n := by
    exact Nat.le_log_of_pow_le (by decide) hn
  have hg : 1 ≤ g := by
    dsimp only [g]
    have hL : 1 ≤ Nat.log 2 n := hlog.trans' (by norm_num)
    nlinarith
  have hlarge : 68 * g ≤ 3 * n := by
    dsimp only [g]
    calc
      68 * (γ * Nat.log 2 n) =
          68 * γ * Nat.log 2 n := by ring
      _ ≤ 3 * n := by omega
  have hlogle : Nat.log 2 n ≤ g := by
    dsimp only [g]
    nlinarith
  have hT :
      T ≤ C * γ * n * Nat.log 2 n := by
    have hbound :=
      phase12Horizon_le_linear S hg hlarge hlogle
    dsimp only [T, C, g] at *
    calc
      phase1RawDyadicLadderHorizon n (Nat.log 2 n) +
            phase2BufferedLadderHorizon S
              (γ * Nat.log 2 n) n
              (phase2BufferedStageCount n) ≤
          (40 + 12288 * S.C * S.R₀) *
            (γ * Nat.log 2 n) * n :=
        hbound
      _ = (40 + 12288 * S.C * S.R₀) *
          γ * n * Nat.log 2 n := by ring
  have hfinite :=
    theorem4EntryHittingFailureMass_le_finite
      (n := n) (B := B)
      σ h3 S γ g x₀ y₀ d hg hlarge hinit
  have herror :=
    phase12Error_le_headline S n γ d hn hγ hguard
      hlarge hinit.2.2.1
  change
    theorem4EntryHittingFailureMass σ
        (C * γ * n * Nat.log 2 n) [] s₀ ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 136 : ℝ) * (γ : ℝ))
  calc
    theorem4EntryHittingFailureMass σ
          (C * γ * n * Nat.log 2 n) [] s₀ ≤
        theorem4EntryHittingFailureMass σ T [] s₀ := by
      rw [theorem4EntryHittingFailureMass_eq_joint σ h3,
        theorem4EntryHittingFailureMass_eq_joint σ h3]
      exact
        terminalFailureMass_iter_freeze_antitone_of_subset
          (fun q : ControlledJointState n B =>
            RelaxedXConsensus q.2)
          (fun q : ControlledJointState n B =>
            RelaxedXConsensus q.2)
          (controlledJointStep σ h3)
          (fun _ h => h) T (C * γ * n * Nat.log 2 n)
          hT ([], s₀)
    _ ≤ phase1RawDyadicLadderError n d (Nat.log 2 n) +
          phase2BufferedLadderError S g n
            (phase2BufferedStageCount n) :=
      hfinite
    _ ≤ (n : ℝ≥0∞)⁻¹ ^
          ((1 / 136 : ℝ) * (γ : ℝ)) :=
      herror

end

end Tri.Byzantine

#print axioms Tri.Byzantine.phase2BufferedLadderHorizon_le_linear
#print axioms Tri.Byzantine.phase12Horizon_le_linear
#print axioms Tri.Byzantine.phase2BufferedStageCount_le_rpow
#print axioms Tri.Byzantine.phase2BufferedLadderError_le_power
#print axioms Tri.Byzantine.phase1RawDyadicLadderError_le_power
#print axioms Tri.Byzantine.phase12Error_le_headline
#print axioms Tri.Byzantine.theorem4_entry
