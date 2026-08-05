/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase2Additive
import Tri.Phase3Feller
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The phase-2 additive error budget

`phase2_reaches_additive` exports the failure mass
`∑ i < phase2StageCount n γ, phase2AdditiveRungError n (2 + i)`, a sum of the
three additive terms `live + lowerRuin + upperReturn`.  This module works toward
bounding that sum by `6 · n⁻¹ ^ (γ / 50)`.

The base-ratio bounds here show both Feller bases are at most `1/2` (the lower
guard gives `2·bHi ≤ lo`, the upper buffer `2·bHi ≤ lo` under `q ≤ n/8`), so each
Feller term is at most `(1/2)^width` with `width = Θ(n)` (lower) or `Θ(q)`
(upper).
-/

namespace Tri

open scoped ENNReal

/-- A natural-number ratio with `c a ≤ b` is at most `1/c` in `ℝ≥0∞`. -/
theorem enn_natCast_ratio_le (c : ℕ) (hc : 0 < c) {a b : ℕ} (hb : 0 < b)
    (hab : c * a ≤ b) : (a : ℝ≥0∞) / (b : ℝ≥0∞) ≤ (1 : ℝ≥0∞) / (c : ℝ≥0∞) := by
  have hcne : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have h1c : (1 / (c : ℝ≥0∞)) * (c : ℝ≥0∞) = 1 := by
    rw [one_div]; exact ENNReal.inv_mul_cancel hcne (ENNReal.natCast_ne_top c)
  have hle : (a : ℝ≥0∞) ≤ (1 / (c : ℝ≥0∞)) * (b : ℝ≥0∞) := by
    have hcab : (c : ℝ≥0∞) * (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast hab
    calc (a : ℝ≥0∞) = (1 / (c : ℝ≥0∞)) * ((c : ℝ≥0∞) * (a : ℝ≥0∞)) := by
          rw [← mul_assoc, h1c, one_mul]
      _ ≤ (1 / (c : ℝ≥0∞)) * (b : ℝ≥0∞) := by gcongr
  exact ENNReal.div_le_of_le_mul hle

/-- The lower-ruin Feller term is at most `(1/2)^(n/16)`. -/
theorem phase2LowerRuinError_le (n : ℕ) (hn : 96 ≤ n) :
    phase2LowerRuinError n ≤ ((1 : ℝ≥0∞) / 2) ^ (n / 16) := by
  unfold phase2LowerRuinError
  have hquarter : 4 * (n / 4) ≤ n := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self n 4
  have hquartermod : n < 4 * (n / 4) + 4 := by
    have := Nat.div_add_mod n 4; have : n % 4 < 4 := Nat.mod_lt n (by norm_num); omega
  have hbase : (phase2LowerBHi n : ℝ≥0∞) / (phase2LowerLo n : ℝ≥0∞) ≤ (1 : ℝ≥0∞) / 2 :=
    enn_natCast_ratio_le 2 (by norm_num) (by unfold phase2LowerLo; omega)
      (by unfold phase2LowerLo phase2LowerBHi; omega)
  exact pow_le_pow_left' hbase _

/-- The upper-return Feller term is at most `(1/2)^phase2UpperGap`. -/
theorem phase2UpperReturnError_le (n s : ℕ) (h3 : 3 ≤ n) (hs : 2 ≤ s)
    (hq : 32 ≤ phase2NextScale n s) :
    phase2UpperReturnError n s ≤ ((1 : ℝ≥0∞) / 7) ^ phase2UpperGap n s := by
  unfold phase2UpperReturnError
  have hq8 : phase2NextScale n s ≤ n / 8 := by
    show n / 2 ^ (s + 1) ≤ n / 8
    exact Nat.div_le_div_left
      (by calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num)
  have hn8 : n / 8 ≤ n := Nat.div_le_self _ _
  have h3q : 3 * phase2NextScale n s ≤ n := by omega
  have h7q : 7 * phase2NextScale n s ≤ n := by omega
  have hbase : (phase2ReturnBHi n s : ℝ≥0∞) / (phase2ReturnLo n s : ℝ≥0∞) ≤ (1 : ℝ≥0∞) / 7 :=
    enn_natCast_ratio_le 7 (by norm_num) (by unfold phase2ReturnLo; omega)
      (by unfold phase2ReturnLo phase2ReturnBHi; omega)
  exact pow_le_pow_left' hbase _

/-! ## Nat-power scaffolding -/

/-- `32 L ≤ 2^L` for `L ≥ 8`, by induction (`32 ≤ 2^L` past the base). -/
theorem thirtytwo_mul_le_two_pow : ∀ L : ℕ, 8 ≤ L → 32 * L ≤ 2 ^ L := by
  intro L
  induction L with
  | zero => intro h; omega
  | succ m ih =>
    intro hL
    rcases Nat.lt_or_ge m 8 with hm | hm
    · have hm7 : m = 7 := by omega
      subst hm7; norm_num
    · have hih := ih hm
      have h32 : 32 ≤ 2 ^ m := le_trans (by omega) hih
      calc 32 * (m + 1) = 32 * m + 32 := by ring
        _ ≤ 2 ^ m + 2 ^ m := by omega
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- `lg n ≤ n/16` whenever `lg n ≥ 8` (so the `lg n` prefactor is dwarfed). -/
theorem log_le_div_sixteen {n : ℕ} (hlog : 8 ≤ Nat.log 2 n) :
    Nat.log 2 n ≤ n / 16 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hlog
  have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have h32 : 32 * Nat.log 2 n ≤ 2 ^ Nat.log 2 n := thirtytwo_mul_le_two_pow _ hlog
  have : 16 * Nat.log 2 n ≤ n := by omega
  omega

/-! ## The lower-ruin sum -/

set_option maxHeartbeats 400000 in
-- Comparing the geometric stage count with the exponential tail needs extended log arithmetic.
/-- The constant lower-ruin term, summed over all stages, fits `n⁻¹^(γ/50)`.
`phase2StageCount ≤ lg n` copies of `(1/2)^(n/16)` are dwarfed because the
Feller exponent `n/16` is enormous next to `lg n` and `(γ/50) lg n`. -/
theorem phase2_lowerRuin_sum_le (n γ : ℕ) (hγ : 1 ≤ γ) (hn : 96 ≤ n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hlog : 8 ≤ Nat.log 2 n) :
    (∑ _i ∈ Finset.range (phase2StageCount n γ), phase2LowerRuinError n)
      ≤ (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by
  have hnpos : 0 < n := by omega
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have h32 : 32 * Nat.log 2 n ≤ n := by
    have := thirtytwo_mul_le_two_pow (Nat.log 2 n) hlog
    have hp := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    omega
  -- the sum is `k • lowerRuin ≤ k • (1/2)^(n/16)`.
  have hkle : phase2StageCount n γ ≤ Nat.log 2 n := phase2StageCount_le_log n γ
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- reduce to a real inequality.
  have hbaseR : phase2LowerRuinError n ≤ ((1 : ℝ≥0∞) / 2) ^ (n / 16) :=
    phase2LowerRuinError_le n hn
  have hstep : (phase2StageCount n γ : ℝ≥0∞) * phase2LowerRuinError n ≤
      ((Nat.log 2 n : ℝ≥0∞)) * ((1 : ℝ≥0∞) / 2) ^ (n / 16) := by
    apply mul_le_mul' (by exact_mod_cast hkle) hbaseR
  refine hstep.trans ?_
  -- Now: (lg n) * (1/2)^(n/16) ≤ n⁻¹^((1/50)γ), via ofReal + logs.
  have hrpow : (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ))
      = ENNReal.ofReal ((n : ℝ) ^ (-((1 / 50 : ℝ) * (γ : ℝ)))) := by
    rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
      ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hnpos),
      ← ENNReal.ofReal_inv_of_pos (by positivity), Real.rpow_neg (by positivity)]
  have hlhs : ((Nat.log 2 n : ℝ≥0∞)) * ((1 : ℝ≥0∞) / 2) ^ (n / 16)
      = ENNReal.ofReal ((Nat.log 2 n : ℝ) * (1 / 2 : ℝ) ^ (n / 16)) := by
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast (Nat.log 2 n)]
    congr 1
    rw [show ((1 : ℝ≥0∞) / 2) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
      ← ENNReal.ofReal_pow (by norm_num)]
  rw [hlhs, hrpow]
  apply ENNReal.ofReal_le_ofReal
  -- Real inequality: (lg n)·(1/2)^(n/16) ≤ n^(-(1/50)γ).
  rw [Real.rpow_neg (by positivity)]
  rw [show (n : ℝ) ^ ((1 / 50 : ℝ) * (γ : ℝ))
      = Real.exp (((1 / 50 : ℝ) * (γ : ℝ)) * Real.log n) by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hnpos)]; ring_nf]
  rw [show (1 / 2 : ℝ) ^ (n / 16) = Real.exp (((n / 16 : ℕ) : ℝ) * Real.log (1 / 2)) by
    rw [← Real.exp_log (show (0:ℝ) < (1/2)^(n/16) by positivity), Real.log_pow]]
  rw [← Real.exp_neg, ← Real.exp_log (show (0:ℝ) < (Nat.log 2 n : ℝ) by
        have : 0 < Nat.log 2 n := by omega
        exact_mod_cast this), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- ln(lg n) + (n/16)·ln(1/2) ≤ -(1/50)γ·ln n
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlgN : 1 ≤ Nat.log 2 n := by omega
  have hlogn : Real.log n ≤ ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
    have hup : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hlt : Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
      Real.log_lt_log (by exact_mod_cast hnpos) (by exact_mod_cast hup)
    rw [Real.log_pow] at hlt; push_cast at hlt; linarith
  have hloglg : Real.log (Nat.log 2 n : ℝ) ≤ (Nat.log 2 n : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (Nat.log 2 n : ℝ) by exact_mod_cast hlgN)
    linarith
  have hlgle : (Nat.log 2 n : ℝ) ≤ (n : ℝ) / 32 := by
    have : (32 : ℝ) * (Nat.log 2 n : ℝ) ≤ (n : ℝ) := by exact_mod_cast h32
    linarith
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hgammaR : (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ (n : ℝ) / 6 := by
    have h6R : ((6 * γ * Nat.log 2 n : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hsize
    push_cast at h6R
    nlinarith [h6R]
  have hgammaU : (γ : ℝ) ≤ (n : ℝ) / 6 := by
    have hgn : (γ : ℝ) ≤ (γ : ℝ) * (Nat.log 2 n : ℝ) :=
      le_mul_of_one_le_right (by positivity) (by exact_mod_cast hlgN)
    linarith [hgammaR]
  have hgln : (γ : ℝ) * Real.log n ≤ ((n : ℝ) / 3) * Real.log 2 := by
    have hstep1 : (γ : ℝ) * Real.log n ≤ (γ : ℝ) * (((Nat.log 2 n : ℝ) + 1) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogn (by positivity)
    have hA : (γ : ℝ) * (Nat.log 2 n : ℝ) * Real.log 2 ≤ ((n : ℝ) / 6) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hgammaR hlog2pos.le
    have hB : (γ : ℝ) * Real.log 2 ≤ ((n : ℝ) / 6) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hgammaU hlog2pos.le
    nlinarith [hstep1, hA, hB]
  have hndiv2 : (n : ℝ) / 16 - 1 ≤ ((n / 16 : ℕ) : ℝ) := by
    have hh : n < (n / 16 + 1) * 16 := by
      have := Nat.div_add_mod n 16; have : n % 16 < 16 := Nat.mod_lt n (by norm_num); omega
    have hhR : (n : ℝ) < (((n / 16 : ℕ) : ℝ) + 1) * 16 := by exact_mod_cast hh
    linarith
  rw [hhalf]
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hmulLo : ((n : ℝ) / 16 - 1) * Real.log 2 ≤ ((n / 16 : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hndiv2 hlog2pos.le
  have hmulN : (n : ℝ) * 0.6931471803 ≤ (n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2lo.le hnn
  nlinarith [hloglg, hlgle, hgln, hlog2, hlog2pos, hmulLo, hmulN,
    show (0:ℝ) ≤ (Nat.log 2 n : ℝ) by positivity, hnn,
    show (96:ℝ) ≤ (n:ℝ) by exact_mod_cast hn]

/-! ## ENNReal half-decay sum -/

/-- Half-decay in `ℝ≥0∞`: if each term is at least twice the previous one up to
`k`, the whole finite sum is at most twice its last term.  (No `k` prefactor —
this is what the `γ`-scaled Feller terms need.) -/
theorem enn_sum_le_two_last_of_double (f : ℕ → ℝ≥0∞) :
    ∀ k, 0 < k → (∀ i, i + 1 < k → 2 * f i ≤ f (i + 1)) →
      (∑ i ∈ Finset.range k, f i) ≤ 2 * f (k - 1) := by
  intro k
  induction k with
  | zero => intro h _; omega
  | succ m ih =>
    intro _ hstep
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [Finset.sum_range_one, show (0 + 1) - 1 = 0 from rfl]
      calc f 0 = 1 * f 0 := (one_mul _).symm
        _ ≤ 2 * f 0 := by gcongr <;> norm_num
    · rw [Finset.sum_range_succ]
      have hIH : (∑ i ∈ Finset.range m, f i) ≤ 2 * f (m - 1) :=
        ih hmpos (fun i hi => hstep i (by omega))
      have hlast : 2 * f (m - 1) ≤ f m := by
        have := hstep (m - 1) (by omega)
        rwa [Nat.sub_add_cancel hmpos] at this
      have hidx : (m + 1) - 1 = m := by omega
      rw [hidx]
      calc (∑ i ∈ Finset.range m, f i) + f m ≤ 2 * f (m - 1) + f m :=
            add_le_add hIH (le_refl _)
        _ ≤ f m + f m := add_le_add hlast (le_refl _)
        _ = 2 * f m := by rw [two_mul]

/-! ## The upper-return sum -/

/-- Consecutive next-scales halve. -/
theorem phase2NextScale_succ (n i : ℕ) :
    phase2NextScale n (2 + (i + 1)) = phase2NextScale n (2 + i) / 2 := by
  unfold phase2NextScale
  rw [show 2 + (i + 1) + 1 = (2 + i + 1) + 1 by omega, pow_succ,
    Nat.div_div_eq_div_mul]

/-- `γ lg n ≤ 64 · gap` at the last active stage (buffer availability). -/
theorem phase2_lastGap_lower {n γ : ℕ} (hγ : 1 ≤ γ) (hlog : 128 ≤ Nat.log 2 n)
    (hkpos : 0 < phase2StageCount n γ) :
    γ * Nat.log 2 n ≤ 64 * phase2UpperGap n (2 + (phase2StageCount n γ - 1)) := by
  set k := phase2StageCount n γ with hk
  have hmin := phase2StageCount_minimal (n := n) (γ := γ)
    (show k - 1 < k by omega)
  -- γ lg n < 2 (n/2^(2+(k-1))), and next-scale = (n/2^(2+(k-1)))/2.
  have hns : phase2NextScale n (2 + (k - 1)) = (n / 2 ^ (2 + (k - 1))) / 2 := by
    unfold phase2NextScale
    rw [show 2 + (k - 1) + 1 = (2 + (k - 1)) + 1 by omega, pow_succ,
      Nat.div_div_eq_div_mul]
  unfold phase2UpperGap
  rw [hns]
  have hd16 : (n / 2 ^ (2 + (k - 1)) / 2) / 16 * 16 ≤ n / 2 ^ (2 + (k - 1)) / 2 :=
    Nat.div_mul_le_self _ 16
  have hd2 : n / 2 ^ (2 + (k - 1)) / 2 * 2 ≤ n / 2 ^ (2 + (k - 1)) :=
    Nat.div_mul_le_self _ 2
  omega

set_option maxHeartbeats 400000 in
-- The dyadic floor bounds and the geometric return envelope create a large nonlinear context.
/-- The upper-return terms sum to at most `2 · n⁻¹^(γ/50)`.  Envelope
`(1/7)^gap`, half-decay to the last stage, then `(1/7)^gap_last ≤ n^(-γ/50)`
because `γ lg n ≤ 64 gap_last` and `50 log 7 ≥ 128 log 2`. -/
theorem phase2_upperReturn_sum_le (n γ : ℕ) (hγ : 1 ≤ γ) (h3 : 3 ≤ n) (hn : 96 ≤ n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hlog : 128 ≤ Nat.log 2 n) :
    (∑ i ∈ Finset.range (phase2StageCount n γ), phase2UpperReturnError n (2 + i))
      ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by
  have hnpos : 0 < n := by omega
  set k := phase2StageCount n γ with hk
  have hkpos : 0 < k := phase2StageCount_pos n γ (by omega) hsize hγ
  set g : ℕ → ℝ≥0∞ := fun i => ((1 : ℝ≥0∞) / 7) ^ phase2UpperGap n (2 + i) with hg
  -- 1. each term ≤ envelope.
  have hsum1 : (∑ i ∈ Finset.range k, phase2UpperReturnError n (2 + i)) ≤
      ∑ i ∈ Finset.range k, g i := by
    apply Finset.sum_le_sum
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    exact phase2UpperReturnError_le n (2 + i) h3 (by omega)
      (phase2_active_nextScale_ge_32 hγ (by omega) hik)
  -- 2. half-decay.
  have hdouble : ∀ i, i + 1 < k → 2 * g i ≤ g (i + 1) := by
    intro i hi
    have hq32 : 32 ≤ phase2NextScale n (2 + (i + 1)) :=
      phase2_active_nextScale_ge_32 hγ (by omega) hi
    have hsucc := phase2NextScale_succ n i
    have hW : phase2UpperGap n (2 + (i + 1)) + 1 ≤ phase2UpperGap n (2 + i) := by
      unfold phase2UpperGap
      rw [hsucc] at hq32 ⊢
      have hd16a : phase2NextScale n (2 + i) / 2 / 16 * 16 ≤
        phase2NextScale n (2 + i) / 2 := Nat.div_mul_le_self _ 16
      have hd2 : phase2NextScale n (2 + i) / 2 * 2 ≤ phase2NextScale n (2 + i) :=
        Nat.div_mul_le_self _ 2
      have hd16b : phase2NextScale n (2 + i) / 16 * 16 ≤ phase2NextScale n (2 + i) :=
        Nat.div_mul_le_self _ 16
      omega
    have hWpos : 1 ≤ phase2UpperGap n (2 + i) := by unfold phase2UpperGap; omega
    have hgeom : ((1 : ℝ≥0∞) / 7) ^ (phase2UpperGap n (2 + i) - 1) =
        7 * ((1 : ℝ≥0∞) / 7) ^ phase2UpperGap n (2 + i) := by
      have hpS : ((1 : ℝ≥0∞) / 7) ^ phase2UpperGap n (2 + i) =
          ((1 : ℝ≥0∞) / 7) ^ (phase2UpperGap n (2 + i) - 1) * ((1 : ℝ≥0∞) / 7) := by
        rw [← pow_succ, Nat.sub_add_cancel hWpos]
      rw [hpS]
      rw [show (7 : ℝ≥0∞) * (((1 : ℝ≥0∞) / 7) ^ (phase2UpperGap n (2 + i) - 1) * (1 / 7))
        = ((1 : ℝ≥0∞) / 7) ^ (phase2UpperGap n (2 + i) - 1) * (7 * (1 / 7)) by ring,
        show (7 : ℝ≥0∞) * (1 / 7) = 1 by
          rw [mul_one_div, ENNReal.div_self (by norm_num) (by norm_num)], mul_one]
    calc 2 * g i ≤ 7 * g i := by gcongr <;> norm_num
      _ = ((1 : ℝ≥0∞) / 7) ^ (phase2UpperGap n (2 + i) - 1) := by
          simp only [hg]; exact hgeom.symm
      _ ≤ ((1 : ℝ≥0∞) / 7) ^ phase2UpperGap n (2 + (i + 1)) :=
          pow_le_pow_right_of_le_one' (by norm_num) (by omega)
      _ = g (i + 1) := by simp only [hg]
  have hhd := enn_sum_le_two_last_of_double g k hkpos hdouble
  refine (hsum1.trans hhd).trans ?_
  -- 3. g (k-1) ≤ n⁻¹^(γ/50).
  have hlast : g (k - 1) ≤ (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by
    simp only [hg]
    set W := phase2UpperGap n (2 + (k - 1)) with hW
    have hgap : γ * Nat.log 2 n ≤ 64 * W := phase2_lastGap_lower hγ hlog hkpos
    -- convert to reals.
    have hrpow : (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ))
        = ENNReal.ofReal ((n : ℝ) ^ (-((1 / 50 : ℝ) * (γ : ℝ)))) := by
      rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
        ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hnpos),
        ← ENNReal.ofReal_inv_of_pos (by positivity), Real.rpow_neg (by positivity)]
    have hlhs : ((1 : ℝ≥0∞) / 7) ^ W = ENNReal.ofReal ((1 / 7 : ℝ) ^ W) := by
      rw [show ((1 : ℝ≥0∞) / 7) = ENNReal.ofReal (1 / 7) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
        ← ENNReal.ofReal_pow (by norm_num)]
    rw [hlhs, hrpow]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg (by positivity),
      show (n : ℝ) ^ ((1 / 50 : ℝ) * (γ : ℝ))
        = Real.exp (((1 / 50 : ℝ) * (γ : ℝ)) * Real.log n) by
        rw [Real.rpow_def_of_pos (by exact_mod_cast hnpos)]; ring_nf,
      show (1 / 7 : ℝ) ^ W = Real.exp ((W : ℝ) * Real.log (1 / 7)) by
        rw [← Real.exp_log (show (0:ℝ) < (1/7)^W by positivity), Real.log_pow],
      ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    -- (W)·log(1/7) ≤ -(1/50)γ·log n, i.e. (1/50)γ log n ≤ W log7.
    have hhalf7 : Real.log (1 / 7 : ℝ) = -Real.log 7 := by rw [one_div, Real.log_inv]
    rw [hhalf7]
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog7 : (128 : ℝ) * Real.log 2 ≤ 50 * Real.log 7 := by
      have hpow : (2 : ℝ) ^ 13 ≤ (7 : ℝ) ^ 5 := by norm_num
      have hll : Real.log ((2:ℝ)^13) ≤ Real.log ((7:ℝ)^5) :=
        Real.log_le_log (by positivity) hpow
      rw [Real.log_pow, Real.log_pow] at hll
      push_cast at hll
      nlinarith [hll, hlog2pos]
    have hlogn : Real.log n ≤ ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
      have hup : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have hlt : Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
        Real.log_lt_log (by exact_mod_cast hnpos) (by exact_mod_cast hup)
      rw [Real.log_pow] at hlt; push_cast at hlt; linarith
    have hgammaR : (γ : ℝ) * (Nat.log 2 n : ℝ) ≤ 64 * (W : ℝ) := by
      have : ((γ * Nat.log 2 n : ℕ) : ℝ) ≤ ((64 * W : ℕ) : ℝ) := by exact_mod_cast hgap
      push_cast at this; linarith
    have hgammaU : (γ : ℝ) ≤ 64 * (W : ℝ) := by
      have h1 : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by
        have : 1 ≤ Nat.log 2 n := by omega
        exact_mod_cast this
      nlinarith [hgammaR, h1, show (0:ℝ) ≤ (γ:ℝ) by positivity]
    have hlog7pos : (0 : ℝ) < Real.log 7 := Real.log_pos (by norm_num)
    -- (1/50)γ log n ≤ (1/50)γ(lgn+1)log2 ≤ (1/50)(128W)log2 ≤ W log7.
    have hA : (γ : ℝ) * Real.log n ≤ (γ : ℝ) * (((Nat.log 2 n : ℝ) + 1) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogn (by positivity)
    have hB : (γ : ℝ) * (Nat.log 2 n : ℝ) * Real.log 2 ≤ 64 * (W : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hgammaR hlog2pos.le
    have hC : (γ : ℝ) * Real.log 2 ≤ 64 * (W : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hgammaU hlog2pos.le
    have hWlog7 : (W : ℝ) * (128 * Real.log 2) ≤ (W : ℝ) * (50 * Real.log 7) :=
      mul_le_mul_of_nonneg_left hlog7 (by positivity)
    have hcomb : (γ : ℝ) * Real.log n ≤ 128 * (W : ℝ) * Real.log 2 := by
      have hAe : (γ : ℝ) * Real.log n ≤
          (γ : ℝ) * (Nat.log 2 n : ℝ) * Real.log 2 + (γ : ℝ) * Real.log 2 := by
        nlinarith [hA]
      linarith [hAe, hB, hC]
    have hWL7 : 128 * (W : ℝ) * Real.log 2 ≤ 50 * (W : ℝ) * Real.log 7 := by
      nlinarith [hWlog7]
    linarith [hcomb, hWL7]
  calc (2 : ℝ≥0∞) * g (k - 1) ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by
        gcongr

/-! ## The live term envelope -/

set_option maxHeartbeats 800000 in
-- Expanding the buffered decay and floor estimates produces the main exponential calculation.
/-- The buffered live term decays like `exp(-(1/8)·⌊n/2^s⌋)`.  The raw growth
`2^E` (`E = phase2UpperHi - (n - n/2^s) ≤ 17P/32 + 1`, `P = ⌊n/2^s⌋`) is beaten
by the 8n-block contraction `phase2BufferedDecay^(8n) ≤ exp(-168 n/2^(s+8))`,
which is `≈ 0.656 P`. -/
theorem phase2BufferedLiveError_le_exp (n s : ℕ) (h3 : 3 ≤ n) (hs : 2 ≤ s)
    (hq : 32 ≤ phase2NextScale n s) :
    phase2BufferedLiveError n s ≤
      ENNReal.ofReal (Real.exp (-(1 / 8 : ℝ) * ((n / 2 ^ s : ℕ) : ℝ))) := by
  set P : ℕ := n / 2 ^ s with hP
  set q : ℕ := phase2NextScale n s with hqdef
  have hqP : q = P / 2 := by rw [hqdef, hP, phase2NextScale, pow_succ, Nat.div_div_eq_div_mul]
  have hqn : q + 1 ≤ n := by
    have hd : P ≤ n := by rw [hP]; exact Nat.div_le_self _ _
    have : q ≤ P := by rw [hqP]; exact Nat.div_le_self _ _
    omega
  have hUeq : phase2UpperHi n s = n - q + q / 16 := phase2_upper_hi_eq n s hqn
  have hd0 : 0 < phase2BufferedDecay s := by
    unfold phase2BufferedDecay
    have h1 : (21 : ℝ) / 2 ^ (s + 8) ≤ 21 / 2 ^ 8 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (21 : ℝ) / 2 ^ 8 < 1 := by norm_num
    linarith
  -- E := phase2UpperHi - (n - P), and its bound E ≤ P - q + q/16.
  have hPle : q ≤ P := by rw [hqP]; exact Nat.div_le_self _ _
  have hUge : n - P ≤ phase2UpperHi n s := by
    rw [hUeq]; have hqd : q / 16 ≤ q := Nat.div_le_self _ _; omega
  set E : ℕ := phase2UpperHi n s - (n - P) with hE
  have hEeq : E = P - q + q / 16 := by
    rw [hE, hUeq]
    have hqd : q / 16 ≤ q := Nat.div_le_self _ _
    have hPn : P ≤ n := by rw [hP]; exact Nat.div_le_self _ _
    omega
  -- Convert to a real value R and its log.
  have hpe : phase2BufferedLiveError n s =
      ENNReal.ofReal (phase2BufferedDecay s ^ (8 * n) *
        (1 / 2 : ℝ) ^ (n - P) / (1 / 2 : ℝ) ^ phase2UpperHi n s) := by
    unfold phase2BufferedLiveError phase2BufferedDecayENN
    rw [← ENNReal.ofReal_pow (phase2BufferedDecay_nonneg s),
      show ((1 : ℝ≥0∞) / 2) = ENNReal.ofReal (1 / 2) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp,
      ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_div_of_pos (by positivity), hP]
  rw [hpe]
  apply ENNReal.ofReal_le_ofReal
  set R : ℝ := phase2BufferedDecay s ^ (8 * n) * (1 / 2 : ℝ) ^ (n - P) /
    (1 / 2 : ℝ) ^ phase2UpperHi n s with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hval : R ≤ Real.exp (-(1 / 8 : ℝ) * (P : ℝ)) := by
    rw [← Real.exp_log hRpos]
    apply Real.exp_le_exp.mpr
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hlogR : Real.log R =
        (8 * n : ℕ) * Real.log (phase2BufferedDecay s)
          + ((phase2UpperHi n s : ℝ) - (n - P : ℕ)) * Real.log 2 := by
      rw [hR, Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]
      have h12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
      rw [h12]; push_cast; ring
    rw [hlogR]
    -- decay term ≤ -168 n / 2^(s+8).
    have hlogd : Real.log (phase2BufferedDecay s) ≤ -(21 / 2 ^ (s + 8) : ℝ) := by
      have := Real.log_le_sub_one_of_pos hd0
      unfold phase2BufferedDecay at this ⊢; linarith
    have hdecay : (8 * n : ℕ) * Real.log (phase2BufferedDecay s) ≤
        -(168 / 2 ^ (s + 8) : ℝ) * (n : ℝ) := by
      have hstep : (8 * n : ℕ) * Real.log (phase2BufferedDecay s) ≤
          (8 * n : ℕ) * (-(21 / 2 ^ (s + 8) : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogd (by positivity)
      have hcoef : ((8 * n : ℕ) : ℝ) * (-(21 / 2 ^ (s + 8) : ℝ))
          = -(168 / 2 ^ (s + 8) : ℝ) * (n : ℝ) := by push_cast; ring
      linarith [hstep, hcoef.le, hcoef.ge]
    -- 168 n / 2^(s+8) ≥ (168/256)·P  (P ≤ n/2^s).
    have hPle_real : (P : ℝ) ≤ (n : ℝ) / 2 ^ s := by rw [hP]; exact_mod_cast Nat.cast_div_le
    have hdecayP : (8 * n : ℕ) * Real.log (phase2BufferedDecay s) ≤
        -(168 / 256 : ℝ) * (P : ℝ) := by
      have hpow8 : (2 : ℝ) ^ (s + 8) = 2 ^ s * 256 := by rw [pow_add]; norm_num
      have h1 : -(168 / 2 ^ (s + 8) : ℝ) * (n : ℝ) = -(168 / 256 : ℝ) * ((n : ℝ) / 2 ^ s) := by
        rw [hpow8]; field_simp
      have h2 : -(168 / 256 : ℝ) * ((n : ℝ) / 2 ^ s) ≤ -(168 / 256 : ℝ) * (P : ℝ) :=
        mul_le_mul_of_nonpos_left hPle_real (by norm_num)
      linarith [hdecay, h1.le, h1.ge, h2]
    -- E ≤ P - q + q/16 ≤ 17P/32 + 1  (as reals).
    have hEr : ((phase2UpperHi n s : ℝ) - (n - P : ℕ)) = (E : ℝ) := by
      have : (phase2UpperHi n s : ℝ) - ((n - P : ℕ) : ℝ) = ((phase2UpperHi n s - (n - P) : ℕ) : ℝ) := by
        rw [Nat.cast_sub hUge]
      rw [this, ← hE]
    have hEbound : (E : ℝ) ≤ (17 / 32 : ℝ) * (P : ℝ) + 2 := by
      have hqd16 : q / 16 * 16 ≤ q := Nat.div_mul_le_self q 16
      have hq2 : 2 * (P / 2) ≤ P := by have := Nat.div_mul_le_self P 2; omega
      have hEn : E ≤ P - P / 2 + P / 32 + 1 := by
        rw [hEeq, hqP]
        have h1 : P / 2 / 16 = P / 32 := by
          rw [Nat.div_div_eq_div_mul]
        have h2 : q / 16 = P / 2 / 16 := by rw [hqP]
        omega
      have : ((E : ℕ) : ℝ) ≤ ((P - P / 2 + P / 32 + 1 : ℕ) : ℝ) := by exact_mod_cast hEn
      have hb : ((P - P / 2 + P / 32 + 1 : ℕ) : ℝ) ≤ (17 / 32 : ℝ) * (P : ℝ) + 2 := by
        have hP2 : (P : ℝ) / 2 - 1 ≤ ((P / 2 : ℕ) : ℝ) := by
          have := Nat.div_add_mod P 2; have : P % 2 < 2 := Nat.mod_lt P (by norm_num)
          have hh : (P : ℝ) < ((P / 2 : ℕ) : ℝ) * 2 + 2 := by
            have : P < (P / 2) * 2 + 2 := by omega
            exact_mod_cast this
          linarith
        have hP32 : ((P / 32 : ℕ) : ℝ) ≤ (P : ℝ) / 32 := by exact_mod_cast Nat.cast_div_le
        have hsub : ((P - P / 2 : ℕ) : ℝ) = (P : ℝ) - ((P / 2 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega : P / 2 ≤ P)]
        push_cast [hsub]
        nlinarith [hP2, hP32]
      linarith [this, hb]
    have hEterm : ((phase2UpperHi n s : ℝ) - (n - P : ℕ)) * Real.log 2 ≤
        ((17 / 32 : ℝ) * (P : ℝ) + 2) * Real.log 2 := by
      rw [hEr]; apply mul_le_mul_of_nonneg_right hEbound hlog2pos.le
    have hPnn : (0 : ℝ) ≤ (P : ℝ) := by positivity
    have hP32 : (32 : ℝ) ≤ (P : ℝ) := by
      have : 32 ≤ P := by rw [hP, ← hqdef.symm] at *; omega
      exact_mod_cast this
    nlinarith [hdecayP, hEterm, hlog2, hlog2pos, hPnn, hP32,
      mul_nonneg hPnn hlog2pos.le]
  rw [hP] at hval ⊢
  exact hval

set_option maxHeartbeats 800000 in
-- Summing the live envelopes combines dyadic minimality with repeated real-log normalization.
/-- The live terms sum to at most `2 · n⁻¹^(γ/50)`.  Envelope
`exp(-(1/8)⌊n/2^(2+i)⌋)`, half-decay to the last stage, then
`exp(-(1/8)P_last) ≤ n^(-γ/50)` since `γ lg n < 2 P_last` (minimality). -/
theorem phase2_live_sum_le (n γ : ℕ) (hγ : 1 ≤ γ) (h3 : 3 ≤ n) (hn : 96 ≤ n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hlog : 128 ≤ Nat.log 2 n) :
    (∑ i ∈ Finset.range (phase2StageCount n γ), phase2BufferedLiveError n (2 + i))
      ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by
  have hnpos : 0 < n := by omega
  set k := phase2StageCount n γ with hk
  have hkpos : 0 < k := phase2StageCount_pos n γ (by omega) hsize hγ
  set g : ℕ → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (Real.exp (-(1 / 8 : ℝ) * ((n / 2 ^ (2 + i) : ℕ) : ℝ))) with hg
  -- P i ≥ 64 for active stages.
  have hPactive : ∀ i, i < k → 64 ≤ n / 2 ^ (2 + i) := by
    intro i hik
    have hns := phase2_active_nextScale_ge_32 hγ (by omega) hik
    have hnseq : phase2NextScale n (2 + i) = n / 2 ^ (2 + i) / 2 := by
      unfold phase2NextScale
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [hnseq] at hns
    have hd2 : n / 2 ^ (2 + i) / 2 * 2 ≤ n / 2 ^ (2 + i) := Nat.div_mul_le_self _ 2
    omega
  -- 1. each term ≤ envelope.
  have hsum1 : (∑ i ∈ Finset.range k, phase2BufferedLiveError n (2 + i)) ≤
      ∑ i ∈ Finset.range k, g i := by
    apply Finset.sum_le_sum
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    exact phase2BufferedLiveError_le_exp n (2 + i) h3 (by omega)
      (phase2_active_nextScale_ge_32 hγ (by omega) hik)
  -- 2. half-decay.
  have hdouble : ∀ i, i + 1 < k → 2 * g i ≤ g (i + 1) := by
    intro i hi
    have hP1 : 64 ≤ n / 2 ^ (2 + (i + 1)) := hPactive (i + 1) hi
    have hsucc : n / 2 ^ (2 + (i + 1)) = n / 2 ^ (2 + i) / 2 := by
      rw [show 2 + (i + 1) = (2 + i) + 1 by omega, pow_succ, Nat.div_div_eq_div_mul]
    have hd2 : n / 2 ^ (2 + i) / 2 * 2 ≤ n / 2 ^ (2 + i) := Nat.div_mul_le_self _ 2
    have hPgap : 32 ≤ n / 2 ^ (2 + i) - n / 2 ^ (2 + (i + 1)) := by omega
    simp only [hg]
    rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (2 : ℝ) * Real.exp (-(1 / 8) * ((n / 2 ^ (2 + i) : ℕ) : ℝ))
        = Real.exp (Real.log 2) * Real.exp (-(1 / 8) * ((n / 2 ^ (2 + i) : ℕ) : ℝ)) by
      rw [Real.exp_log (by norm_num)], ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hPgapR : (32 : ℝ) ≤ ((n / 2 ^ (2 + i) : ℕ) : ℝ) - ((n / 2 ^ (2 + (i + 1)) : ℕ) : ℝ) := by
      have := hPgap
      have hle : n / 2 ^ (2 + (i + 1)) ≤ n / 2 ^ (2 + i) := by omega
      rw [← Nat.cast_sub hle]; exact_mod_cast this
    nlinarith [hlog2, hPgapR]
  have hhd := enn_sum_le_two_last_of_double g k hkpos hdouble
  refine (hsum1.trans hhd).trans ?_
  -- 3. g (k-1) ≤ n⁻¹^(γ/50).
  have hlast : g (k - 1) ≤ (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by
    simp only [hg]
    have hmin := phase2StageCount_minimal (n := n) (γ := γ) (show k - 1 < k by omega)
    set Plast : ℕ := n / 2 ^ (2 + (k - 1)) with hPl
    have hrpow : (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ))
        = ENNReal.ofReal ((n : ℝ) ^ (-((1 / 50 : ℝ) * (γ : ℝ)))) := by
      rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
        ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hnpos),
        ← ENNReal.ofReal_inv_of_pos (by positivity), Real.rpow_neg (by positivity)]
    rw [hrpow]
    apply ENNReal.ofReal_le_ofReal
    have hp1 : (0 : ℝ) < Real.exp (-(1 / 8 : ℝ) * (Plast : ℝ)) := Real.exp_pos _
    have hp2 : (0 : ℝ) < (n : ℝ) ^ (-((1 / 50 : ℝ) * (γ : ℝ))) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _
    have hli : Real.log (Real.exp (-(1 / 8 : ℝ) * (Plast : ℝ))) ≤
        Real.log ((n : ℝ) ^ (-((1 / 50 : ℝ) * (γ : ℝ)))) := by
      rw [Real.log_exp, Real.log_rpow (by exact_mod_cast hnpos)]
      -- -(1/8)Plast ≤ -(1/50)γ log n, i.e. (1/50)γ log n ≤ (1/8)Plast.
      have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have hlogn : Real.log n ≤ ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
        have hup : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
        have hlt : Real.log n < Real.log (2 ^ (Nat.log 2 n + 1)) :=
          Real.log_lt_log (by exact_mod_cast hnpos) (by exact_mod_cast hup)
        rw [Real.log_pow] at hlt; push_cast at hlt; linarith
      have hPlR : (γ : ℝ) * (Nat.log 2 n : ℝ) < 2 * (Plast : ℝ) := by
        have : ((γ * Nat.log 2 n : ℕ) : ℝ) < ((2 * Plast : ℕ) : ℝ) := by exact_mod_cast hmin
        push_cast at this; linarith
      have hgammaU : (γ : ℝ) ≤ 2 * (Plast : ℝ) := by
        have h1 : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by
          have : 1 ≤ Nat.log 2 n := by omega
          exact_mod_cast this
        nlinarith [hPlR, h1, show (0:ℝ) ≤ (γ:ℝ) by positivity]
      -- (1/50)γ log n ≤ (1/50)γ(lgn+1)log2 ≤ (1/50)(4 Plast)log2 ≤ (1/8)Plast.
      have hA : (γ : ℝ) * Real.log n ≤ (γ : ℝ) * (((Nat.log 2 n : ℝ) + 1) * Real.log 2) :=
        mul_le_mul_of_nonneg_left hlogn (by positivity)
      have hB : (γ : ℝ) * (Nat.log 2 n : ℝ) * Real.log 2 ≤ 2 * (Plast : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (le_of_lt hPlR) hlog2pos.le
      have hC : (γ : ℝ) * Real.log 2 ≤ 2 * (Plast : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hgammaU hlog2pos.le
      nlinarith [hA, hB, hC, hlog2, hlog2pos, show (0:ℝ) ≤ (Plast:ℝ) by positivity]
    have := Real.exp_le_exp.mpr hli
    rwa [Real.exp_log hp1, Real.exp_log hp2] at this
  calc (2 : ℝ≥0∞) * g (k - 1) ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by gcongr

/-! ## The full phase-2 additive error bound -/

/-- **The phase-2 additive error budget.**  The buffered ladder's total failure
mass fits `6 · n⁻¹^(γ/50)` (live ≤2, lowerRuin ≤1, upperReturn ≤2). -/
theorem phase2_additive_error_le (n γ : ℕ) (hγ : 1 ≤ γ) (h3 : 3 ≤ n) (hn : 96 ≤ n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hlog : 128 ≤ Nat.log 2 n) :
    (∑ i ∈ Finset.range (phase2StageCount n γ), phase2AdditiveRungError n (2 + i))
      ≤ 6 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) := by
  set X : ℝ≥0∞ := (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) with hX
  have hsplit : (∑ i ∈ Finset.range (phase2StageCount n γ),
      phase2AdditiveRungError n (2 + i)) =
      (∑ i ∈ Finset.range (phase2StageCount n γ), phase2BufferedLiveError n (2 + i))
        + (∑ _i ∈ Finset.range (phase2StageCount n γ), phase2LowerRuinError n)
        + (∑ i ∈ Finset.range (phase2StageCount n γ), phase2UpperReturnError n (2 + i)) := by
    unfold phase2AdditiveRungError
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit]
  have hl : (∑ i ∈ Finset.range (phase2StageCount n γ), phase2BufferedLiveError n (2 + i))
      ≤ 2 * X := phase2_live_sum_le n γ hγ h3 hn hsize hlog
  have hlr : (∑ _i ∈ Finset.range (phase2StageCount n γ), phase2LowerRuinError n)
      ≤ X := phase2_lowerRuin_sum_le n γ hγ hn hsize (by omega)
  have hur : (∑ i ∈ Finset.range (phase2StageCount n γ), phase2UpperReturnError n (2 + i))
      ≤ 2 * X := phase2_upperReturn_sum_le n γ hγ h3 hn hsize hlog
  calc _ ≤ 2 * X + X + 2 * X := add_le_add (add_le_add hl hlr) hur
    _ = 5 * X := by ring
    _ ≤ 6 * X := by gcongr <;> norm_num

end Tri

#print axioms Tri.phase2_additive_error_le

#print axioms Tri.enn_natCast_ratio_le
#print axioms Tri.phase2LowerRuinError_le
#print axioms Tri.phase2UpperReturnError_le
