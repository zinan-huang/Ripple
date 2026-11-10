/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Burman et al. Lemma 3.3 for the paper instance, with constants

`Rmax = ⌈60 ln n⌉`, `Dmax = 32 n`, window `t₃₃ = ⌈(3n/2)(2 ln n + Rmax ln 3)⌉`, `n ≥ 1600`: from a
fully propagating configuration with resetcounts at most `Rmax`, the configuration after `t₃₃`
interactions is fully dormant except with probability at most `1/(3n) + 1/n²`
(`P_EM_paper_dormancy_bound`; P2 Lemma 3.2).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.Dormancy
import Ripple.PopulationProtocol.SSEM.UpperBound.PropagationPaper

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- The dormancy window `⌈(3n/2)(2 ln n + Rmax ln 3)⌉`. -/
noncomputable def dormWindow (n : ℕ) : ℕ :=
  ⌈(3 * (n : ℝ) / 2) * (2 * Real.log n + (rmaxPaper n : ℝ) * Real.log 3)⌉₊

theorem dormRho_eq (hn : 2 ≤ n) :
    dormRho n = ENNReal.ofReal (1 - 2 / (3 * (n : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold dormRho
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  congr 1
  rw [div_eq_mul_inv, mul_inv, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
  norm_num
  ring

theorem PhiN_le_of_le (y : Fin n → ℕ) (R : ℕ) (hy : ∀ v, y v ≤ R) : PhiN y ≤ n * 3 ^ R := by
  unfold PhiN
  calc ∑ w, phiN (y w) ≤ ∑ _w : Fin n, 3 ^ R := Finset.sum_le_sum fun w _ => by
        unfold phiN
        split_ifs
        · exact Nat.zero_le _
        · exact Nat.pow_le_pow_right (by norm_num) (hy w)
    _ = n * 3 ^ R := by simp

/-- **Potential part of B33.** -/
theorem phi_term_le (hn : 2 ≤ n) (y₀ : Fin n → ℕ) (R : ℕ) (hy : ∀ v, y₀ v ≤ R) (K : ℕ)
    (hK : (3 * (n : ℝ) / 2) * (2 * Real.log n + (R : ℝ) * Real.log 3) ≤ K) :
    3 * (schedulerPrefixPMF n hn K).toOuterMeasure {σ | 3 ≤ PhiN (maxFrom y₀ K σ)} ≤
      ENNReal.ofReal (1 / n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM := schedulerPrefix_markov hn K (fun σ => (PhiN (maxFrom y₀ K σ) : ℝ≥0∞)) 3
  have hE := PhiN_expect_le hn y₀ K
  have hsub : {σ : SchedulerPrefix n K | 3 ≤ PhiN (maxFrom y₀ K σ)} ⊆
      {σ | (3 : ℝ≥0∞) ≤ (PhiN (maxFrom y₀ K σ) : ℝ≥0∞)} := by
    intro σ h
    show (3 : ℝ≥0∞) ≤ _
    exact_mod_cast h
  refine (mul_le_mul_left' (MeasureTheory.measure_mono hsub) 3).trans (hM.trans (hE.trans ?_))
  have hΦ : (PhiN y₀ : ℝ≥0∞) ≤ ENNReal.ofReal ((n : ℝ) * 3 ^ R) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num)]
    have := PhiN_le_of_le y₀ R hy
    have h3 : ENNReal.ofReal 3 = 3 := by norm_num
    rw [h3]
    exact_mod_cast this
  have hρ0 : (0 : ℝ) ≤ 1 - 2 / (3 * (n : ℝ)) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  rw [dormRho_eq hn, ← ENNReal.ofReal_pow hρ0]
  refine (mul_le_mul_left' hΦ _).trans ?_
  rw [← ENNReal.ofReal_mul (pow_nonneg hρ0 _)]
  apply ENNReal.ofReal_le_ofReal
  have hpow : (1 - 2 / (3 * (n : ℝ))) ^ K ≤ Real.exp (-(2 * K / (3 * n))) := by
    calc (1 - 2 / (3 * (n : ℝ))) ^ K ≤ (Real.exp (-(2 / (3 * n)))) ^ K := by
          apply pow_le_pow_left₀ hρ0
          have := Real.add_one_le_exp (-(2 / (3 * (n : ℝ))))
          linarith
      _ = Real.exp (-(2 * K / (3 * n))) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp : Real.exp (-(2 * K / (3 * n))) ≤
      Real.exp (-(2 * Real.log n + (R : ℝ) * Real.log 3)) := by
    apply Real.exp_le_exp.mpr
    have : 2 * Real.log n + (R : ℝ) * Real.log 3 ≤ 2 * K / (3 * n) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hval : Real.exp (-(2 * Real.log n + (R : ℝ) * Real.log 3)) * ((n : ℝ) * 3 ^ R) = 1 / n := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3),
      show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
    field_simp
  calc (1 - 2 / (3 * (n : ℝ))) ^ K * ((n : ℝ) * 3 ^ R)
      ≤ Real.exp (-(2 * Real.log n + (R : ℝ) * Real.log 3)) * ((n : ℝ) * 3 ^ R) :=
        mul_le_mul_of_nonneg_right (hpow.trans hexp) (by positivity)
    _ = 1 / n := hval

/-- `log n ≤ 2 √n`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  linarith

/-- **Count part of B33** at `Dmax = 32 n`. -/
theorem count_term_le (hn : 1600 ≤ n) (K : ℕ)
    (hK : (K : ℝ) ≤ (3 * (n : ℝ) / 2) * (2 * Real.log n + (rmaxPaper n : ℝ) * Real.log 3) + 1) :
    (schedulerPrefixPMF n (by omega) K).toOuterMeasure
        {σ | ∃ v, 32 * n ≤ cntIter K σ v + 1} ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  have hn2 : 2 ≤ n := by omega
  have hn' : (1600 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hT := count_tail_some_le hn2 K (32 * n - 1)
  have hsub : {σ : SchedulerPrefix n K | ∃ v, 32 * n ≤ cntIter K σ v + 1} ⊆
      {σ | ∃ v, 32 * n - 1 ≤ cntIter K σ v} := by
    rintro σ ⟨v, hv⟩; exact ⟨v, by omega⟩
  have h4 : (4 : ℝ≥0∞) ^ (32 * n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4' : (4 : ℝ≥0∞) ^ (32 * n - 1) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  refine (MeasureTheory.measure_mono hsub).trans ?_
  rw [← ENNReal.mul_le_mul_iff_right h4 h4']
  refine hT.trans ?_
  -- real inequality: n (1 + 6/n)^K ≤ 4^(32n-1) / n^2
  have hbase : (1 + 3 * (2 * (n : ℝ≥0∞)⁻¹)) = ENNReal.ofReal (1 + 6 / n) := by
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, div_eq_mul_inv,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
    congr 1
    rw [← mul_assoc]
    congr 1
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  have h4r : (4 : ℝ≥0∞) ^ (32 * n - 1) = ENNReal.ofReal (4 ^ (32 * n - 1)) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
  rw [hbase, ← ENNReal.ofReal_pow (by positivity), h4r, ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- bounds
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hR : (rmaxPaper n : ℝ) ≤ 60 * Real.log n + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hs := log_le_two_sqrt hn0.le
  have hsq : (40 : ℝ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by norm_num) hn0.le]; linarith
  have hsqsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  -- (1 + 6/n)^K ≤ exp(6K/n)
  have h1 : (1 + 6 / (n : ℝ)) ^ K ≤ Real.exp (6 * K / n) := by
    calc (1 + 6 / (n : ℝ)) ^ K ≤ (Real.exp (6 / n)) ^ K := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp (6 / (n : ℝ)); linarith
      _ = Real.exp (6 * K / n) := by rw [← Real.exp_nat_mul]; congr 1; ring
  -- 6K/n ≤ 790 log n + 14
  have h2 : 6 * (K : ℝ) / n ≤ 790 * Real.log n + 14 := by
    rw [div_le_iff₀ hn0]
    have hRl : (rmaxPaper n : ℝ) * Real.log 3 ≤ (60 * Real.log n + 1) * (2 * Real.log 2) :=
      mul_le_mul hR hl3 (Real.log_nonneg (by norm_num)) (by positivity)
    nlinarith
  -- 4^(32n-1) = exp((32n-1) log 4)
  have h4e : (4 : ℝ) ^ (32 * n - 1) = Real.exp (((32 * n - 1 : ℕ) : ℝ) * (2 * Real.log 2)) := by
    rw [Real.exp_nat_mul, show 2 * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num, Real.exp_log (by norm_num)]
  have hcast : ((32 * n - 1 : ℕ) : ℝ) = 32 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [h4e, hcast]
  have hnexp : (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
  have hn2exp : ((n : ℝ) ^ 2) = Real.exp (2 * Real.log n) := by
    rw [show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  calc (n : ℝ) * (1 + 6 / (n : ℝ)) ^ K
      ≤ Real.exp (Real.log n) * Real.exp (790 * Real.log n + 14) := by
        rw [← hnexp]
        exact mul_le_mul_of_nonneg_left (h1.trans (Real.exp_le_exp.mpr h2)) hn0.le
    _ = Real.exp ((32 * (n : ℝ) - 1) * (2 * Real.log 2) - 2 * Real.log n) *
          Real.exp (791 * Real.log n + 14 - (32 * (n : ℝ) - 1) * (2 * Real.log 2) +
            2 * Real.log n) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((32 * (n : ℝ) - 1) * (2 * Real.log 2) - 2 * Real.log n) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [Real.exp_le_one_iff]
        nlinarith
    _ = Real.exp ((32 * (n : ℝ) - 1) * (2 * Real.log 2)) * (1 / (n : ℝ) ^ 2) := by
        rw [mul_one, Real.exp_sub, hn2exp, div_eq_mul_one_div]

/-- **Burman et al. Lemma 3.3 for the paper instance** (`Dmax = 32 n`). -/
theorem P_EM_paper_dormancy_bound {trank e : ℕ} {hn : 0 < n} (hn2 : 2 ≤ n) (hN : 1600 ≤ n)
    (X : Config (AgentState n) Opinion n) (hX : FullyPropagating X)
    (hR : ∀ v, (X v).1.resetcount ≤ rmaxPaper n) :
    probNotHitBy (protocolPEMPaper n trank e 32 hn) hn2 X FullyDormant (dormWindow n) ≤
      ENNReal.ofReal (1 / (3 * n)) + ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine (P_EM_paper_dormancy (trank := trank) (e := e) (d := 32) hn2 X hX (dormWindow n)).trans ?_
  rw [add_comm]
  apply add_le_add
  · have hp := phi_term_le hn2 (fun w => (X w).1.resetcount) (rmaxPaper n) hR (dormWindow n)
      (Nat.le_ceil _)
    have h3 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
    have h3' : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num
    rw [← ENNReal.mul_le_mul_iff_right h3 h3']
    refine hp.trans (le_of_eq ?_)
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    field_simp
  · exact count_term_le hN (dormWindow n) (Nat.ceil_lt_add_one (by
      have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      positivity)).le

/-- Non-vacuity at `n = 1608`: an all-propagating configuration with resetcount 1 satisfies the
hypotheses of `P_EM_paper_dormancy_bound`. -/
example : ∃ X : Config (AgentState 1608) Opinion 1608,
    FullyPropagating X ∧ ∀ v, (X v).1.resetcount ≤ rmaxPaper 1608 :=
  ⟨fun _ => (AgentState.mk .Resetting 0 .L 1 .phi 0 0 0 0, Opinion.A),
    fun _ => by simp [effRc], fun _ => one_le_rmaxPaper (by norm_num)⟩

end Ripple.PopulationProtocol.SSEM
