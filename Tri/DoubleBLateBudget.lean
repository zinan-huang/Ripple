/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBLateConstants
import Tri.Phase2AdditiveBudget

/-!
# Summing the ordinary-productivity Double-B late ladder

The strengthened `exp(-P/80)` rung envelope doubles as the dyadic co-level
scale halves.  Hence the whole late ladder is controlled by twice its last
envelope, with no logarithmic prefactor.
-/

namespace Tri

open scoped ENNReal

/-- The errors of all dyadic late rungs fit a single power-law budget. -/
theorem doubleLateLadderError_le
    (n : ℕ) (hn : 2 ≤ n) (γ : ℕ)
    (hlog : 128 ≤ Nat.log 2 n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    doubleLateLadderError n γ ≤
      8 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) := by
  have hnPos : 0 < n := by omega
  let k := phase2StageCount n γ
  let K := doubleLateStages n γ
  have hkPos : 0 < k :=
    phase2StageCount_pos n γ (hlog.trans' (by norm_num)) hsize hγ
  have hKPos : 0 < K := by
    dsimp only [K, doubleLateStages]
    omega
  let g : ℕ → ℝ≥0∞ := fun i =>
    ENNReal.ofReal
      (Real.exp
        (-(((n / 2 ^ (1 + i) : ℕ) : ℝ)) / 80))
  have hsum :
      (∑ i ∈ Finset.range K, doubleLateRungError n (1 + i)) ≤
        ∑ i ∈ Finset.range K, 4 * g i := by
    apply Finset.sum_le_sum
    intro i hi
    have hiK : i < K := Finset.mem_range.1 hi
    have hq := doubleLate_active_nextScale_ge_32 hγ hlog hiK
    have hr := doubleLateRungError_le n hn (1 + i)
      (hlog.trans' (by norm_num)) (by omega) hq
    simpa only [g, phase2Scale] using hr
  have hdouble :
      ∀ i, i + 1 < K → 2 * g i ≤ g (i + 1) := by
    intro i hi
    have hq :=
      doubleLate_active_nextScale_ge_32 hγ hlog
        (show i + 1 < K by omega)
    have hsucc :
        n / 2 ^ (1 + (i + 1)) =
          n / 2 ^ (1 + i) / 2 := by
      rw [show 1 + (i + 1) = (1 + i) + 1 by omega,
        pow_succ, Nat.div_div_eq_div_mul]
    have htwice :
        (n / 2 ^ (1 + i) / 2) * 2 ≤ n / 2 ^ (1 + i) :=
      Nat.div_mul_le_self _ 2
    have hgap :
        64 ≤ n / 2 ^ (1 + i) - n / 2 ^ (1 + (i + 1)) := by
      change 32 ≤ n / 2 ^ (1 + (i + 1) + 1) at hq
      have hnextNext :
          n / 2 ^ (1 + (i + 1) + 1) =
            n / 2 ^ (1 + (i + 1)) / 2 := by
        rw [show 1 + (i + 1) + 1 = (1 + (i + 1)) + 1 by omega,
          pow_succ, Nat.div_div_eq_div_mul]
      rw [hnextNext] at hq
      have hnextTwice :
          (n / 2 ^ (1 + (i + 1)) / 2) * 2 ≤
            n / 2 ^ (1 + (i + 1)) :=
        Nat.div_mul_le_self _ 2
      rw [hsucc]
      omega
    simp only [g]
    rw [← ENNReal.ofReal_ofNat (n := 2),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [show
        (2 : ℝ) *
            Real.exp (-((n / 2 ^ (1 + i) : ℕ) : ℝ) / 80) =
          Real.exp (Real.log 2) *
            Real.exp (-((n / 2 ^ (1 + i) : ℕ) : ℝ) / 80) by
      rw [Real.exp_log (by norm_num)], ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog2 : Real.log 2 < (0.6931471808 : ℝ) :=
      Real.log_two_lt_d9
    have hnextLe :
        n / 2 ^ (1 + (i + 1)) ≤ n / 2 ^ (1 + i) := by
      rw [hsucc]
      exact Nat.div_le_self _ _
    have hgapR :
        (64 : ℝ) ≤
          ((n / 2 ^ (1 + i) : ℕ) : ℝ) -
            ((n / 2 ^ (1 + (i + 1)) : ℕ) : ℝ) := by
      rw [← Nat.cast_sub hnextLe]
      exact_mod_cast hgap
    nlinarith
  have hgeom := enn_sum_le_two_last_of_double g K hKPos hdouble
  have hlast :
      g (K - 1) ≤
        (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) := by
    have hK : K = k + 1 := by
      dsimp only [K, k, doubleLateStages]
    have hidx : 1 + (K - 1) = 2 + (k - 1) := by omega
    have hmin :=
      phase2StageCount_minimal (n := n) (γ := γ)
        (show k - 1 < k by omega)
    let P := n / 2 ^ (1 + (K - 1))
    have hPmin : γ * Nat.log 2 n < 2 * P := by
      dsimp only [P]
      rw [hidx]
      exact hmin
    have hrpow :
        (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) =
          ENNReal.ofReal
            ((n : ℝ) ^ (-((1 / 200 : ℝ) * (γ : ℝ)))) := by
      rw [ENNReal.inv_rpow, ← ENNReal.ofReal_natCast n,
        ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hnPos),
        ← ENNReal.ofReal_inv_of_pos (by positivity),
        Real.rpow_neg (by positivity)]
    simp only [g]
    change
      ENNReal.ofReal (Real.exp (-(P : ℝ) / 80)) ≤
        (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ))
    rw [hrpow]
    apply ENNReal.ofReal_le_ofReal
    have hpExp :
        (0 : ℝ) < Real.exp (-(P : ℝ) / 80) :=
      Real.exp_pos _
    have hpPow :
        (0 : ℝ) <
          (n : ℝ) ^ (-((1 / 200 : ℝ) * (γ : ℝ))) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hnPos) _
    have hlogIneq :
        Real.log (Real.exp (-(P : ℝ) / 80)) ≤
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
            Real.log n <
              Real.log (2 ^ (Nat.log 2 n + 1)) :=
          Real.log_lt_log (by exact_mod_cast hnPos)
            (by exact_mod_cast hup)
        rw [Real.log_pow] at hlt
        push_cast at hlt
        linarith
      have hL :
          (128 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hlog
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
      have hPminR :
          (γ : ℝ) * (Nat.log 2 n : ℝ) < 2 * (P : ℝ) := by
        exact_mod_cast hPmin
      nlinarith
    have hexp := Real.exp_le_exp.mpr hlogIneq
    rwa [Real.exp_log hpExp, Real.exp_log hpPow] at hexp
  change
    (∑ i ∈ Finset.range K, doubleLateRungError n (1 + i)) ≤ _
  calc
    (∑ i ∈ Finset.range K, doubleLateRungError n (1 + i))
        ≤ ∑ i ∈ Finset.range K, 4 * g i := hsum
    _ = 4 * (∑ i ∈ Finset.range K, g i) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (2 * g (K - 1)) := by gcongr
    _ ≤ 8 * (n : ℝ≥0∞)⁻¹ ^
          ((1 / 200 : ℝ) * (γ : ℝ)) := by
      calc
        4 * (2 * g (K - 1)) = 8 * g (K - 1) := by ring
        _ ≤ _ := by gcongr

end Tri

#print axioms Tri.doubleLateLadderError_le
