/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage B1: from a triggered configuration with a leader to `FD_L^{½}` (P3 Lemma 10 (B1))

P2 Lemma 4.1 = 7.1 for the paper instance, in two hitting stages:

* `stageB1a`: from `PT_L`, a fully propagating configuration with a leader is hit within
  `K₃₂ = ⌈4 n ln n⌉` interactions with probability `≥ 0.9987` (B32, `P_EM_paper_propagation`,
  and leader invariance `exists_leader_step`);
* `stageB1b`: from a fully propagating configuration with a leader, `FD_L^{½}` (fully dormant,
  a leader, every delay timer `≥ 16 n + 1`) is hit within `t₃₃` interactions with probability
  `≥ 0.9997` (B33, `dormancy_run`: while every agent has fewer than `16 n` interactions, the
  delay timers stay `≥ 32 n - 16 n + 1`).

`stageB1 : StageB1` composes them (`0.9987 · 0.9997 ≥ 0.998`, window `t₁ = K₃₂ + t₃₃`).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.EpochCompose
import Ripple.PopulationProtocol.SSEM.UpperBound.LeaderInvariant
import Ripple.PopulationProtocol.SSEM.Probability.PrefixTools

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped ENNReal

variable {n : ℕ}

/-! ### Numerics -/

theorem log_le_lin (hN : 1608 ≤ n) : Real.log n ≤ 6.5 + n / 1608 := by
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have he := Real.exp_one_gt_d9
  have hl1608 : Real.log 1608 ≤ 7.5 := by
    have h : (1608 : ℝ) ^ 2 ≤ Real.exp 15 := by
      rw [show (15 : ℝ) = (15 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      calc (1608 : ℝ) ^ 2 ≤ 2.7182818283 ^ 15 := by norm_num
        _ ≤ Real.exp 1 ^ 15 := by gcongr
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_exp] at this
    push_cast at this
    linarith
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / 1608 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  linarith

/-- From a not-hit bound to a hit bound. -/
theorem ofReal_le_probHitBy_of_probNotHitBy_le {Q X Y : Type*} (P : Protocol Q X Y)
    (hn : 2 ≤ n) (C₀ : Config Q X n) (Goal : Config Q X n → Prop) (t : ℕ) (q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε) (hqε : q + ε ≤ 1)
    (h : probNotHitBy P hn C₀ Goal t ≤ ENNReal.ofReal ε) :
    ENNReal.ofReal q ≤ probHitBy P hn C₀ Goal t := by
  have hs := probHitBy_add_probNotHitBy P hn C₀ Goal t
  have hne : probNotHitBy P hn C₀ Goal t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  apply (ENNReal.add_le_add_iff_right hne).mp
  calc ENNReal.ofReal q + probNotHitBy P hn C₀ Goal t
      ≤ ENNReal.ofReal q + ENNReal.ofReal ε := add_le_add le_rfl h
    _ = ENNReal.ofReal (q + ε) := (ENNReal.ofReal_add hq hε).symm
    _ ≤ 1 := ENNReal.ofReal_le_one.mpr hqε
    _ = probHitBy P hn C₀ Goal t + probNotHitBy P hn C₀ Goal t := hs.symm

/-- **Count tail at `16 n`** over a B33 window. -/
theorem count_term16_le (hN : 1608 ≤ n) (K : ℕ)
    (hK : (K : ℝ) ≤ (3 * (n : ℝ) / 2) * (2 * Real.log n + (rmaxPaper n : ℝ) * Real.log 3) + 1) :
    (schedulerPrefixPMF n (by omega) K).toOuterMeasure
        {σ | ∃ v, 16 * n ≤ cntIter K σ v} ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  have hn2 : 2 ≤ n := by omega
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  have hT := count_tail_some_le hn2 K (16 * n)
  have h4 : (4 : ℝ≥0∞) ^ (16 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4' : (4 : ℝ≥0∞) ^ (16 * n) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [← ENNReal.mul_le_mul_iff_right h4 h4']
  refine hT.trans ?_
  have hbase : (1 + 3 * (2 * (n : ℝ≥0∞)⁻¹)) = ENNReal.ofReal (1 + 6 / n) := by
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, div_eq_mul_inv,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
    congr 1
    rw [← mul_assoc]
    congr 1
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  have h4r : (4 : ℝ≥0∞) ^ (16 * n) = ENNReal.ofReal (4 ^ (16 * n)) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
  rw [hbase, ← ENNReal.ofReal_pow (by positivity), h4r, ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hl3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hR : (rmaxPaper n : ℝ) ≤ 60 * Real.log n + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hLn := log_le_lin hN
  have h1 : (1 + 6 / (n : ℝ)) ^ K ≤ Real.exp (6 * K / n) := by
    calc (1 + 6 / (n : ℝ)) ^ K ≤ (Real.exp (6 / n)) ^ K := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp (6 / (n : ℝ)); linarith
      _ = Real.exp (6 * K / n) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h2 : 6 * (K : ℝ) / n ≤ 790 * Real.log n + 14 := by
    rw [div_le_iff₀ hn0]
    have hRl : (rmaxPaper n : ℝ) * Real.log 3 ≤ (60 * Real.log n + 1) * (2 * Real.log 2) :=
      mul_le_mul hR hl3 (Real.log_nonneg (by norm_num)) (by positivity)
    have hl2' := Real.log_two_lt_d9
    nlinarith
  have h4e : (4 : ℝ) ^ (16 * n) = Real.exp (((16 * n : ℕ) : ℝ) * (2 * Real.log 2)) := by
    rw [Real.exp_nat_mul, show 2 * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num, Real.exp_log (by norm_num)]
  rw [h4e]
  push_cast
  have hnexp : (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
  have hn2exp : ((n : ℝ) ^ 2) = Real.exp (2 * Real.log n) := by
    rw [show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  calc (n : ℝ) * (1 + 6 / (n : ℝ)) ^ K
      ≤ Real.exp (Real.log n) * Real.exp (790 * Real.log n + 14) := by
        rw [← hnexp]
        exact mul_le_mul_of_nonneg_left (h1.trans (Real.exp_le_exp.mpr h2)) hn0.le
    _ = Real.exp (16 * (n : ℝ) * (2 * Real.log 2) - 2 * Real.log n) *
          Real.exp (791 * Real.log n + 14 - 16 * (n : ℝ) * (2 * Real.log 2) +
            2 * Real.log n) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (16 * (n : ℝ) * (2 * Real.log 2) - 2 * Real.log n) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [Real.exp_le_one_iff]
        nlinarith
    _ = Real.exp (16 * (n : ℝ) * (2 * Real.log 2)) * (1 / (n : ℝ) ^ 2) := by
        rw [mul_one, Real.exp_sub, hn2exp, div_eq_mul_one_div]

/-! ### The stages -/

/-- Fully propagating, with a leader. -/
def FPL (C : Config (AgentState n) Opinion n) : Prop :=
  FullyPropagating C ∧ ∃ v, (C v).1.leader = .L

theorem exists_leader_step_PEM40 {hn : 0 < n} (C : Config (AgentState n) Opinion n)
    (h : ∃ v, (C v).1.leader = .L) (i j : Fin n) :
    ∃ v, ((C.step (PEM40 n hn) i j) v).1.leader = .L :=
  exists_leader_step C h i j

/-- **Stage B1a** (B32 with a leader). -/
theorem stageB1a : StageBound PTL FPL propWindow 0.9987 := by
  intro n hN hn hn2 X _ hA
  obtain ⟨⟨s, hsr, hsc⟩, hL⟩ := hA
  have hprop := P_EM_paper_propagation (trank := 40) (e := 208) (d := 32) (hn := hn) hn2 X s
    (by rw [effRc_of_resetting hsr, hsc])
  have he := probHitBy_eq_and_inv_of_invariant (PEM40 n hn) hn2 X FullyPropagating
    (fun C => ∃ v, (C v).1.leader = .L) hL (fun C hC i j => exists_leader_step_PEM40 C hC i j)
    (propWindow n)
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have h2 : ENNReal.ofReal 0.9987 ≤ probHitBy (PEM40 n hn) hn2 X FullyPropagating (propWindow n) :=
    ofReal_le_probHitBy_of_probNotHitBy_le _ hn2 X _ _ 0.9987 (2 / n) (by norm_num)
      (by positivity) (by
        have : (2 : ℝ) / n ≤ 2 / 1608 := by gcongr
        linarith) hprop
  exact h2.trans_eq he.symm

/-- **Stage B1b** (B33 with delay timers and a leader). -/
theorem stageB1b : StageBound FPL FDLHalf dormWindow 0.9997 := by
  classical
  intro n hN hn hn2 Y hY hA
  obtain ⟨hFP, hL⟩ := hA
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  set P := PEM40 n hn
  set K := dormWindow n
  set y₀ : Fin n → ℕ := fun w => (Y w).1.resetcount
  have hY' : ∀ v, (Y v).1.role = .Resetting ∧ 1 ≤ (Y v).1.resetcount := by
    intro v
    have h := hFP v
    by_cases hr : (Y v).1.role = .Resetting
    · exact ⟨hr, by rw [effRc_of_resetting hr] at h; exact h⟩
    · rw [effRc_of_not_resetting hr] at h; omega
  -- deterministic part
  have hdet : ∀ σ : SchedulerPrefix n K, ¬ (∃ v, 16 * n ≤ cntIter K σ v) →
      ¬ (3 ≤ PhiN (maxFrom y₀ K σ)) → FDLHalf (runPrefix P Y K σ) := by
    intro σ hc hphi
    push Not at hc hphi
    have hrun := dormancy_run (trank := 40) (e := 208) (d := 32) (hn := hn) Y hY' K σ
      (fun v => by have := hc v; omega)
    have hzero : ∀ v, maxFrom y₀ K σ v = 0 := by
      intro v
      by_contra hne
      have h3 := three_le_phiN hne
      have hle : phiN (maxFrom y₀ K σ v) ≤ PhiN (maxFrom y₀ K σ) :=
        Finset.single_le_sum (f := fun w => phiN (maxFrom y₀ K σ w))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
      omega
    have hrc : ∀ v, (runPrefix P Y K σ v).1.resetcount = 0 := fun v => by
      rw [(hrun v).2.1]; exact hzero v
    refine ⟨fun v => ⟨(hrun v).1, hrc v⟩, ?_, fun v => ?_⟩
    · exact runPrefix_inv P Y (fun C => ∃ v, (C v).1.leader = .L) hL
        (fun C hC i j => exists_leader_step_PEM40 C hC i j) K σ
    · have h1 : 32 * n ≤ (runPrefix P Y K σ v).1.delaytimer + cntIter K σ v :=
        (hrun v).2.2 (hrc v)
      have h2 := hc v
      omega
  -- probability part
  have hnot : probNotHitBy P hn2 Y FDLHalf K ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) + ENNReal.ofReal (1 / (3 * n)) := by
    refine (probNotHitBy_le_prefixMass P hn2 Y FDLHalf K).trans ?_
    refine (MeasureTheory.measure_mono (t := {σ | ∃ v, 16 * n ≤ cntIter K σ v} ∪
      {σ | 3 ≤ PhiN (maxFrom y₀ K σ)}) ?_).trans
      ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_))
    · intro σ hσ
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
      exact hσ (hdet σ hcon.1 hcon.2)
    · exact count_term16_le hN K (Nat.ceil_lt_add_one (by
        have : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
        have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        positivity)).le
    · have hp := phi_term_le hn2 y₀ (rmaxPaper n) (fun v => (hY v).2.1) K (Nat.le_ceil _)
      have h3 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
      have h3' : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num
      rw [← ENNReal.mul_le_mul_iff_right h3 h3']
      refine hp.trans (le_of_eq ?_)
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      field_simp
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hnot
  apply ofReal_le_probHitBy_of_probNotHitBy_le P hn2 Y FDLHalf K 0.9997 _ (by norm_num)
    (by positivity) _ hnot
  have : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 1608 ^ 2 := by gcongr
  have : (1 : ℝ) / (3 * n) ≤ 1 / (3 * 1608) := by gcongr
  norm_num at *
  linarith

/-- **Stage B1** (P3 Lemma 10 (B1), P2 Lemma 4.1). -/
theorem stageB1 : StageB1 :=
  (stageB1a.comp stageB1b (by norm_num)).mono (fun _ _ => le_rfl) (by norm_num)

end Ripple.PopulationProtocol.SSEM
