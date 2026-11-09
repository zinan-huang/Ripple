/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Burman et al. Lemma 3.2 for P_EM with the paper's parameters

`Rmax = ⌈60 ln n⌉` (`rmaxPaper`), `K = ⌈4 n ln n⌉` interactions: from any configuration with an
agent that is Resetting with resetcount at least `Rmax`, the configuration after `K` interactions
is fully propagating except with probability at most `2/n` (`P_EM_paper_propagation`). Paper phase
`docs/audit/FIX2-BURMAN.md` §B.1; walk weights with `L = 3`.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.EpidemicTail
import Ripple.PopulationProtocol.SSEM.UpperBound.PaperInstance

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- The propagation window `⌈4 n ln n⌉`. -/
noncomputable def propWindow (n : ℕ) : ℕ := ⌈4 * (n : ℝ) * Real.log n⌉₊

theorem epidemic_term_le (hn : 2 ≤ n) (K : ℕ) (hK : 4 * (n : ℝ) * Real.log n ≤ K) :
    ENNReal.ofReal (((n : ℝ) - 2) / ((n : ℝ) - 1)) ^ K * ENNReal.ofReal ((n : ℝ) - 1) ≤
      ENNReal.ofReal (1 / n) * ENNReal.ofReal (1 / n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hρ0 : (0 : ℝ) ≤ ((n : ℝ) - 2) / ((n : ℝ) - 1) := div_nonneg (by linarith) hn1.le
  rw [← ENNReal.ofReal_pow hρ0, ← ENNReal.ofReal_mul (pow_nonneg hρ0 _),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- ρ ≤ exp (-1/(n-1))
  have hρ : ((n : ℝ) - 2) / ((n : ℝ) - 1) ≤ Real.exp (-(1 / ((n : ℝ) - 1))) := by
    have h := Real.add_one_le_exp (-(1 / ((n : ℝ) - 1)))
    have : ((n : ℝ) - 2) / ((n : ℝ) - 1) = -(1 / ((n : ℝ) - 1)) + 1 := by
      field_simp
      ring
    rw [this]
    exact h
  have hpow : (((n : ℝ) - 2) / ((n : ℝ) - 1)) ^ K ≤ Real.exp (-(K / ((n : ℝ) - 1))) := by
    calc (((n : ℝ) - 2) / ((n : ℝ) - 1)) ^ K ≤ (Real.exp (-(1 / ((n : ℝ) - 1)))) ^ K :=
          pow_le_pow_left₀ hρ0 hρ K
      _ = Real.exp (-(K / ((n : ℝ) - 1))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hexp : Real.exp (-(K / ((n : ℝ) - 1))) ≤ Real.exp (-(4 * Real.log n)) := by
    apply Real.exp_le_exp.mpr
    have : 4 * Real.log n ≤ K / ((n : ℝ) - 1) := by
      rw [le_div_iff₀ hn1]
      nlinarith
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow4 : Real.exp (-(4 * Real.log n)) = ((n : ℝ) ^ 4)⁻¹ := by
    rw [Real.exp_neg, show (4 : ℝ) * Real.log n = Real.log ((n : ℝ) ^ 4) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  calc (((n : ℝ) - 2) / ((n : ℝ) - 1)) ^ K * ((n : ℝ) - 1)
      ≤ ((n : ℝ) ^ 4)⁻¹ * ((n : ℝ) - 1) := by
        apply mul_le_mul_of_nonneg_right _ hn1.le
        rw [← hpow4]; exact hpow.trans hexp
    _ ≤ 1 / n * (1 / n) := by
        rw [div_mul_div_comm, one_mul, inv_mul_le_iff₀ (by positivity)]
        rw [show (n : ℝ) ^ 4 * (1 / (n * n)) = n * n by field_simp]
        nlinarith

theorem walk_term_le (hn : 2 ≤ n) (K R : ℕ) (hK : (K : ℝ) ≤ 4 * (n : ℝ) * Real.log n + 1)
    (hR : 60 * Real.log n ≤ R) :
    (1 + 4 * (3 : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) ^ K / 3 ^ R ≤ ENNReal.ofReal (1 / n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hbase : (1 + 4 * (3 : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 + 12 / n) := by
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, div_eq_mul_inv,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
    congr 1
    congr 1
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  have h3 : (3 : ℝ≥0∞) ^ R = ENNReal.ofReal (3 ^ R) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hbase, h3, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  -- (1 + 12/n)^K ≤ exp (12 K / n) ≤ exp (48 log n + 6)
  have h1 : (1 + 12 / (n : ℝ)) ^ K ≤ Real.exp (48 * Real.log n + 6) := by
    calc (1 + 12 / (n : ℝ)) ^ K ≤ (Real.exp (12 / n)) ^ K := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp (12 / (n : ℝ))
          linarith
      _ = Real.exp (K * (12 / n)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (48 * Real.log n + 6) := by
          apply Real.exp_le_exp.mpr
          have : (K : ℝ) * (12 / n) ≤ (4 * n * Real.log n + 1) * (12 / n) :=
            mul_le_mul_of_nonneg_right hK (by positivity)
          have h2 : (4 * (n : ℝ) * Real.log n + 1) * (12 / n) = 48 * Real.log n + 12 / n := by
            field_simp
            ring
          have h3 : 12 / (n : ℝ) ≤ 6 := by
            rw [div_le_iff₀ hn0]; linarith
          linarith
  -- 3^R ≥ exp (60 log n)
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have h2 : Real.exp (60 * Real.log n) ≤ (3 : ℝ) ^ R := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have : 60 * Real.log n ≤ Real.log 3 * (60 * Real.log n) := by nlinarith
    calc 60 * Real.log n ≤ Real.log 3 * (60 * Real.log n) := this
      _ ≤ Real.log 3 * R := by
          apply mul_le_mul_of_nonneg_left hR (by linarith)
  have hpos : 0 < Real.exp (60 * Real.log n) := Real.exp_pos _
  rw [div_le_iff₀ (by positivity)]
  calc (1 + 12 / (n : ℝ)) ^ K ≤ Real.exp (48 * Real.log n + 6) := h1
    _ ≤ 1 / n * Real.exp (60 * Real.log n) := by
        rw [show 48 * Real.log n + 6 = (60 * Real.log n) + (6 - 12 * Real.log n) by ring,
          Real.exp_add, mul_comm (1 / (n : ℝ))]
        apply mul_le_mul_of_nonneg_left _ hpos.le
        -- exp (6 - 12 log n) ≤ 1/n  ⟸  e^6 ≤ n^11
        rw [Real.exp_sub, div_le_div_iff₀ (Real.exp_pos _) hn0, one_mul]
        have hpow : Real.exp (12 * Real.log n) = (n : ℝ) ^ 12 := by
          rw [show (12 : ℝ) * Real.log n = Real.log ((n : ℝ) ^ 12) by
            rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
        rw [hpow]
        have he6 : Real.exp 6 < 404 := by
          have := Real.exp_one_lt_d9
          have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
          rw [h6]
          calc Real.exp 1 ^ 6 < (2.7182818286 : ℝ) ^ 6 :=
                pow_lt_pow_left₀ this (Real.exp_pos 1).le (by norm_num)
            _ < 404 := by norm_num
        have hn11 : (2 : ℝ) ^ 11 ≤ (n : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) hn' 11
        have : (n : ℝ) ^ 12 = (n : ℝ) ^ 11 * n := by ring
        rw [this]
        nlinarith
    _ = Real.exp (60 * Real.log n) * (1 / n) := by ring
    _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Burman et al. Lemma 3.2 for the paper instance of P_EM** (flat state space). -/
theorem P_EM_paper_propagation {trank e d : ℕ} {hn : 0 < n} (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n) (s : Fin n)
    (hs : rmaxPaper n ≤ effRc (C₀ s).1) :
    probNotHitBy (protocolPEMPaper n trank e d hn) hn2 C₀ FullyPropagating (propWindow n) ≤
      ENNReal.ofReal (2 / n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hK1 : 4 * (n : ℝ) * Real.log n ≤ propWindow n := Nat.le_ceil _
  have hK2 : (propWindow n : ℝ) ≤ 4 * (n : ℝ) * Real.log n + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hR : 60 * Real.log n ≤ rmaxPaper n := Nat.le_ceil _
  have hmain := propagation_not_full_le (protocolPEMPaper n trank e d hn) (rmaxPaper n)
    (fun s₀ s₁ x₀ x₁ => transitionPEM_effRc (trank := trank) (Emax := e * n) (Dmax := d * n)
      (hn := hn) s₀ s₁ x₀ x₁) hn2 C₀ s hs 3 (by norm_num) (by norm_num) (propWindow n)
  refine hmain.trans ?_
  have hepi := (epidemic_incomplete_le hn2 s (propWindow n)).trans
    (epidemic_term_le hn2 (propWindow n) hK1)
  have hinv : ENNReal.ofReal (1 / n) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hepi' := (ENNReal.mul_le_mul_iff_right hinv ENNReal.ofReal_ne_top).mp hepi
  have hwalk := walk_term_le hn2 (propWindow n) (rmaxPaper n) hK2 hR
  calc _ ≤ ENNReal.ofReal (1 / n) + ENNReal.ofReal (1 / n) := add_le_add hepi' hwalk
    _ = ENNReal.ofReal (2 / n) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Non-vacuity: at `n = 4` the hypothesis holds for the configuration in which every agent is
Resetting with resetcount `⌈60 ln 4⌉`. -/
example : probNotHitBy (protocolPEMPaper 4 1 1 1 (by norm_num)) (by norm_num)
      (fun _ => (⟨.Resetting, 0, .L, rmaxPaper 4, .phi, 0, 0, 0, 0⟩, .A)) FullyPropagating
      (propWindow 4) ≤ ENNReal.ofReal (2 / 4) := by
  have := P_EM_paper_propagation (n := 4) (trank := 1) (e := 1) (d := 1) (hn := by norm_num)
    (by norm_num) (fun _ => (⟨.Resetting, 0, .L, rmaxPaper 4, .phi, 0, 0, 0, 0⟩, .A)) 0
    (by simp [effRc])
  simpa using this

end Ripple.PopulationProtocol.SSEM
