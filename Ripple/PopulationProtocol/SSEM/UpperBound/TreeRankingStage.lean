/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# P3 Lemma 11 (with the R3 fix F1): `FD_1 → R(99)` within `52 n²` interactions

P3 Lemma 11 composes P2 Lemma 7.3 (stage B3, the wake phase) and P2 Lemma 7.4 (stage B4, the
tree ranking) for `P_EM` at the paper constants (`T₀ = 308`, `Emax = 208 n`, `Dmax = 32 n`).
The R3 fix F1 (a tick when the median meets the rank `n - 1` agent created in the same
interaction) is the `[rank n-1 unassigned]` term of `tExp`.

* `stageB3_gen`: `FD_1 ∧ E → MidE E` within `32 n²`, probability `≥ 0.98`;
* `stageB4_gen`: `MidE E → R(99)` within `20 n²`, probability `≥ 0.77`;
* `stageB34`: their composition, `0.98 · 0.77 = 0.7546 ≥ 0.753` and `32 + 20 = 52`.

`MidE E` is a valid tree with every agent computing, Unsettled errorcounts `≥ 80n + 1` and
median timer `≥ 180`, together with the extra invariant `E` (used for the answer version).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingB3

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-! ### Numerical tools -/

theorem exp_le_one_div_pow {y : ℝ} (k : ℕ) (hy : y ≤ -k) :
    Real.exp y ≤ 1 / (2.7 : ℝ) ^ k := by
  calc Real.exp y ≤ Real.exp (-k) := Real.exp_le_exp.mpr hy
    _ = 1 / Real.exp 1 ^ k := by rw [Real.exp_neg, ← Real.exp_nat_mul, mul_one, one_div]
    _ ≤ 1 / (2.7 : ℝ) ^ k :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) k)

theorem ofReal_exp_mul (a b : ℝ) :
    ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) =
      ENNReal.ofReal (Real.exp (a + b)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos a).le, Real.exp_add]

theorem one_add_two_inv_pow_le (m W : ℕ) (hm : 0 < m) :
    (1 + 2 * (m : ℝ≥0∞)⁻¹) ^ W ≤ ENNReal.ofReal (Real.exp (2 * W / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : (1 + 2 * (m : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 + 2 / m) := by
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, div_eq_mul_inv,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos hm', ENNReal.ofReal_natCast]
    norm_num
  rw [hb, ← ENNReal.ofReal_pow (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc (1 + 2 / (m : ℝ)) ^ W ≤ (Real.exp (2 / m)) ^ W :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 / (m : ℝ))]) W
    _ = Real.exp (2 * W / m) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem one_sub_inv_pow_le (m W : ℕ) (hm : 0 < m) :
    (1 - (m : ℝ≥0∞)⁻¹) ^ W ≤ ENNReal.ofReal (Real.exp (-(W / m))) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (1 : ℝ) / m ≤ 1 := by
    rw [div_le_one hm']; exact_mod_cast (show 1 ≤ m by omega)
  have hb : (1 - (m : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 - 1 / m) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, one_div,
      ENNReal.ofReal_inv_of_pos hm', ENNReal.ofReal_natCast]
  rw [hb, ← ENNReal.ofReal_pow (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  calc (1 - 1 / (m : ℝ)) ^ W ≤ (Real.exp (-(1 / m))) ^ W :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-(1 / (m : ℝ)))]) W
    _ = Real.exp (-(W / m)) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem tr_two_pow_eq_ofReal (k : ℕ) :
    (2 : ℝ≥0∞) ^ k = ENNReal.ofReal (Real.exp (k * Real.log 2)) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num), ENNReal.ofReal_pow (by norm_num)]
  norm_num

theorem inv_two_pow_eq_ofReal (k : ℕ) :
    (2⁻¹ : ℝ≥0∞) ^ k = ENNReal.ofReal (Real.exp (-(k * Real.log 2))) := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), ← inv_pow,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

theorem natCast_le_ofReal_exp (m : ℕ) : (m : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp m) := by
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (m : ℝ)])

/-- From a not-hit bound to a hit bound. -/
theorem ofReal_le_probHitBy {P : Protocol (AgentState n) Opinion Output} {hn2 : 2 ≤ n}
    {X : Config (AgentState n) Opinion n} {G : Config (AgentState n) Opinion n → Prop} {W : ℕ}
    {q ε : ℝ} (hqε : q ≤ 1 - ε) (hε : 0 ≤ ε)
    (h : probNotHitBy P hn2 X G W ≤ ENNReal.ofReal ε) :
    ENNReal.ofReal q ≤ probHitBy P hn2 X G W := by
  have hsum := probHitBy_add_probNotHitBy P hn2 X G W
  have hne : probNotHitBy P hn2 X G W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  rw [ENNReal.eq_sub_of_add_eq hne hsum]
  calc ENNReal.ofReal q ≤ ENNReal.ofReal (1 - ε) := ENNReal.ofReal_le_ofReal hqε
    _ = 1 - ENNReal.ofReal ε := by rw [ENNReal.ofReal_sub _ hε, ENNReal.ofReal_one]
    _ ≤ 1 - probNotHitBy P hn2 X G W := tsub_le_tsub_left h 1

theorem log_two_bounds : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

/-! ### The classes -/

/-- The class between the two stages: a valid tree with every agent computing, Unsettled
errorcounts `≥ 80 n + 1`, median timer `≥ 180`, and the extra invariant `E`. -/
def MidE (E : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop) {n : ℕ}
    (C : Config (AgentState n) Opinion n) : Prop :=
  TreeOK3 (fun C => E C) (80 * n + 1) 180 C ∧ AllCompK (kC C)

/-- A fully dormant configuration with one leader is a valid (empty) tree. -/
theorem treeCore_fdOne {X : Config (AgentState n) Opinion n} (h : FDOne X) : TreeCore (kC X) := by
  have hR : ∀ v, (kC X v).role = .Resetting := fun v => (h.1 v).1
  have hS : ∀ v, ¬ (kC X v).role = .Settled := fun v => by rw [hR v]; decide
  refine ⟨fun v _ => (h.1 v).2, fun v w hv hw => h.2.unique hv hw,
    fun v _ hv _ => absurd hv (hS v), ?_, fun v _ hv _ _ => absurd hv (hS v),
    fun v hv _ => absurd hv (hS v), fun v hv => absurd hv (hS v)⟩
  obtain ⟨v, hv, -⟩ := h.2
  exact Or.inr ⟨v, hR v, hv⟩

/-! ### Stage B4 at the paper constants -/

/-- **Stage B4** (P2 Lemma 7.4 for P_EM): `MidE E → R(99)` within `20 n²`, probability
`≥ 0.77`. -/
theorem stageB4_gen (E : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop)
    (G : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop)
    (hE : ∀ {n : ℕ} (hn : 0 < n), 3 ≤ n → ∀ (C : Config (AgentState n) Opinion n),
      TreeStepHyp C → E C → ∀ u v, u ≠ v → E (C.step (PEM40 n hn) u v))
    (hG : ∀ {n : ℕ} (C : Config (AgentState n) Opinion n), RTheta 99 C → E C → G C) :
    StageBound (MidE E) G (fun n => 20 * n ^ 2) 0.77 := by
  intro n hN hn hn2 X _ hM
  obtain ⟨h3, hcomp⟩ := hM
  have hn3 : 3 ≤ n := by omega
  have hX4 : TreeOK4 (fun C => E C) 99 X :=
    ⟨h3.core, hcomp, fun w hw => by have := h3.ec w hw; omega,
      fun w hw => by have := h3.med w hw; omega, h3.extra⟩
  have hb := b4_notHit (trank := 40) (Rmax := rmaxPaper n) (Emax := 208 * n) (Dmax := 32 * n)
    (hn := hn) hn2 hn3 (by norm_num) (θ := 99) (by norm_num) (by norm_num) (fun C => E C)
    (fun C => G C) (fun C hC u v huv => hE hn hn3 C (hC.hyp (by norm_num)) hC.extra u v huv)
    (fun C hC hS => hG C ⟨⟨hS, fun v w hvw => hC.core.inj v w (hS v) (hS w) hvw⟩,
      fun v hv => hC.med v ⟨hS v, hv⟩⟩ hC.extra) X hX4 (20 * n ^ 2) (by
        have hWpos : 0 < 20 * n ^ 2 := by positivity
        exact hWpos)
  refine ofReal_le_probHitBy (ε := 0.23) (by norm_num) (by norm_num) (hb.trans ?_)
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl1, -⟩ := log_two_bounds
  have hnl : (n : ℝ) * 0.6931471803 ≤ n * Real.log 2 := mul_le_mul_of_nonneg_left hl1.le hn0.le
  -- the drift term
  have t1 : phiE X / ((20 * n ^ 2 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (55 / 240) := by
    apply ENNReal.div_le_of_le_mul
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
    unfold phiE
    apply ENNReal.ofReal_le_ofReal
    have hp := phiT_le (kC X)
    have hp0 := phiT_nonneg (kC X)
    have hN' : ((n * (n - 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : n * (n - 1) ≤ n ^ 2 := by
        rw [sq]; exact Nat.mul_le_mul_left n (Nat.sub_le n 1)
      exact_mod_cast this
    have hW : ((20 * n ^ 2 : ℕ) : ℝ) = 20 * (n : ℝ) ^ 2 := by push_cast; ring
    rw [hW]
    have := mul_le_mul hN' hp hp0 (by positivity)
    linarith
  -- the errorcount term
  have hec : ecV 2 X ≤ (n : ℝ≥0∞) * 2⁻¹ ^ (80 * n) := by
    unfold ecV
    calc ∑ w, (if (X w).1.role = .Unsettled then (2 : ℝ≥0∞) * 2⁻¹ ^ (X w).1.errorcount else 0)
        ≤ ∑ _w : Fin n, (2⁻¹ : ℝ≥0∞) ^ (80 * n) := Finset.sum_le_sum fun w _ => by
          split_ifs with hw
          · have hle := h3.ec w hw
            calc (2 : ℝ≥0∞) * 2⁻¹ ^ (X w).1.errorcount ≤ 2 * 2⁻¹ ^ (80 * n + 1) :=
                  mul_le_mul_right (pow_le_pow_right_of_le_one' (by norm_num) hle) _
              _ = 2⁻¹ ^ (80 * n) := by
                  rw [pow_succ, mul_comm (2 : ℝ≥0∞), mul_assoc,
                    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
          · exact zero_le
      _ = (n : ℝ≥0∞) * 2⁻¹ ^ (80 * n) := by simp [Finset.sum_const, nsmul_eq_mul]
  have t2 : (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ (20 * n ^ 2) * ecV 2 X ≤
      ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
    calc (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ (20 * n ^ 2) * ecV 2 X
        ≤ ENNReal.ofReal (Real.exp (2 * ((20 * n ^ 2 : ℕ) : ℝ) / n)) *
            (ENNReal.ofReal (Real.exp n) *
              ENNReal.ofReal (Real.exp (-(((80 * n : ℕ) : ℝ) * Real.log 2)))) := by
          refine mul_le_mul' (one_add_two_inv_pow_le n _ (by omega)) (hec.trans ?_)
          rw [inv_two_pow_eq_ofReal]
          exact mul_le_mul_left (natCast_le_ofReal_exp n) _
      _ = ENNReal.ofReal (Real.exp (2 * ((20 * n ^ 2 : ℕ) : ℝ) / n +
            (n + -(((80 * n : ℕ) : ℝ) * Real.log 2)))) := by
          rw [ofReal_exp_mul, ofReal_exp_mul]
      _ ≤ ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
          apply ENNReal.ofReal_le_ofReal
          apply exp_le_one_div_pow
          have e1 : 2 * ((20 * n ^ 2 : ℕ) : ℝ) / n = 40 * n := by
            rw [div_eq_iff hn0.ne']; push_cast; ring
          rw [e1]
          push_cast
          nlinarith
  -- the median-timer term
  have htExp : tExp (7 * (40 + 4)) X ≤ 129 := by
    unfold tExp medTimer
    by_cases h1 : ∃ w, MedAt (X w).1
    · rw [dif_pos h1]
      have := h3.med _ h1.choose_spec
      split_ifs <;> omega
    · rw [dif_neg h1]
      split_ifs <;> omega
  have hNpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have hNr : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hWN : 2 * (20 * n ^ 2) ≤ 41 * (n * (n - 1)) := by
    have hlin : 40 * n ≤ 41 * (n - 1) := by omega
    calc
      2 * (20 * n ^ 2) = n * (40 * n) := by ring
      _ ≤ n * (41 * (n - 1)) := Nat.mul_le_mul_left n hlin
      _ = 41 * (n * (n - 1)) := by ring
  have hr41 : 2 * ((20 * n ^ 2 : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ) ≤ 41 := by
    rw [div_le_iff₀ hNr]; exact_mod_cast hWN
  have t3 : (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) ^ (20 * n ^ 2) *
      (2 ^ tExp (7 * (40 + 4)) X * (2 ^ (7 * (40 + 4) - 99 + 1))⁻¹) ≤
      ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
    have e210 : 7 * (40 + 4) - 99 + 1 = 210 := by norm_num
    calc (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) ^ (20 * n ^ 2) *
          (2 ^ tExp (7 * (40 + 4)) X * (2 ^ (7 * (40 + 4) - 99 + 1))⁻¹)
        ≤ ENNReal.ofReal (Real.exp (2 * ((20 * n ^ 2 : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ))) *
            (ENNReal.ofReal (Real.exp (((129 : ℕ) : ℝ) * Real.log 2)) *
              ENNReal.ofReal (Real.exp (-(((210 : ℕ) : ℝ) * Real.log 2)))) := by
          rw [e210, ENNReal.inv_pow]
          refine mul_le_mul' (one_add_two_inv_pow_le _ _ hNpos)
            (mul_le_mul' ?_ (inv_two_pow_eq_ofReal 210).le)
          rw [← tr_two_pow_eq_ofReal]
          exact pow_le_pow_right₀ (by norm_num) htExp
      _ = ENNReal.ofReal (Real.exp (2 * ((20 * n ^ 2 : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ) +
            (((129 : ℕ) : ℝ) * Real.log 2 + -(((210 : ℕ) : ℝ) * Real.log 2)))) := by
          rw [ofReal_exp_mul, ofReal_exp_mul]
      _ ≤ ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
          apply ENNReal.ofReal_le_ofReal
          apply exp_le_one_div_pow
          simp only [Nat.cast_ofNat]
          linarith
  calc phiE X / ((20 * n ^ 2 : ℕ) : ℝ≥0∞) + (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ (20 * n ^ 2) * ecV 2 X +
        (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) ^ (20 * n ^ 2) *
          (2 ^ tExp (7 * (40 + 4)) X * (2 ^ (7 * (40 + 4) - 99 + 1))⁻¹)
      ≤ ENNReal.ofReal (55 / 240) + ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) +
          ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := add_le_add (add_le_add t1 t2) t3
    _ = ENNReal.ofReal (55 / 240 + 1 / (2.7 : ℝ) ^ 10 + 1 / (2.7 : ℝ) ^ 10) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal 0.23 := ENNReal.ofReal_le_ofReal (by norm_num)

/-! ### Stage B3 at the paper constants -/

/-- **Stage B3** (P2 Lemma 7.3 for P_EM): `FD_1 ∧ E → MidE E` within `32 n²`, probability
`≥ 0.98`. -/
theorem stageB3_gen (E : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop)
    (hE : ∀ {n : ℕ} (hn : 0 < n), 3 ≤ n → ∀ (C : Config (AgentState n) Opinion n),
      TreeStepHyp C → E C → ∀ u v, u ≠ v → E (C.step (PEM40 n hn) u v)) :
    StageBound (fun C => FDOne C ∧ E C) (MidE E) (fun n => 32 * n ^ 2) 0.98 := by
  intro n hN hn hn2 X hgood hA
  obtain ⟨hFD, hEX⟩ := hA
  have hn3 : 3 ≤ n := by omega
  have hR : ∀ v, (X v).1.role = .Resetting := fun v => (hFD.1 v).1
  have hX3 : TreeOK3 (fun C => E C) (80 * n + 1) 180 X :=
    ⟨treeCore_fdOne hFD, fun w hw => absurd hw (by rw [hR w]; decide),
      fun w hw => absurd hw.1 (by rw [hR w]; decide), hEX⟩
  have hb := b3_notHit (trank := 40) (Rmax := rmaxPaper n) (Emax := 208 * n) (Dmax := 32 * n)
    (hn := hn) hn2 hn3 (by norm_num) (B := 80 * n + 1) (θ := 180) (by omega) (by norm_num)
    (by norm_num) (fun C => E C) (fun C => MidE E C)
    (fun C hC u v huv => hE hn hn3 C (hC.hyp (by omega) (by norm_num)) hC.extra u v huv)
    (fun C hC hc => ⟨hC, hc⟩) X hX3 (32 * n ^ 2)
  refine ofReal_le_probHitBy (ε := 0.02) (by norm_num) (by norm_num) (hb.trans ?_)
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl1, hl2⟩ := log_two_bounds
  have hnl : (n : ℝ) * 0.6931471803 ≤ n * Real.log 2 := mul_le_mul_of_nonneg_left hl1.le hn0.le
  have hnl' : (n : ℝ) * Real.log 2 ≤ n * 0.6931471808 := mul_le_mul_of_nonneg_left hl2.le hn0.le
  -- the dormancy term
  have hdorm : dormV X ≤ (n : ℝ≥0∞) * 2 ^ (32 * n) := by
    unfold dormV
    calc ∑ w, (if (X w).1.role = .Resetting then (2 : ℝ≥0∞) ^ (X w).1.delaytimer else 0)
        ≤ ∑ _w : Fin n, (2 : ℝ≥0∞) ^ (32 * n) := Finset.sum_le_sum fun w _ => by
          split_ifs
          · exact pow_le_pow_right₀ (by norm_num) (hgood w).2.2.2.1
          · exact zero_le
      _ = (n : ℝ≥0∞) * 2 ^ (32 * n) := by simp [Finset.sum_const, nsmul_eq_mul]
  have t1 : (1 - (n : ℝ≥0∞)⁻¹) ^ (32 * n ^ 2) * dormV X ≤
      ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
    calc (1 - (n : ℝ≥0∞)⁻¹) ^ (32 * n ^ 2) * dormV X
        ≤ ENNReal.ofReal (Real.exp (-(((32 * n ^ 2 : ℕ) : ℝ) / n))) *
            (ENNReal.ofReal (Real.exp n) *
              ENNReal.ofReal (Real.exp (((32 * n : ℕ) : ℝ) * Real.log 2))) := by
          refine mul_le_mul' (one_sub_inv_pow_le n _ (by omega)) (hdorm.trans ?_)
          rw [tr_two_pow_eq_ofReal]
          exact mul_le_mul_left (natCast_le_ofReal_exp n) _
      _ = ENNReal.ofReal (Real.exp (-(((32 * n ^ 2 : ℕ) : ℝ) / n) +
            (n + ((32 * n : ℕ) : ℝ) * Real.log 2))) := by
          rw [ofReal_exp_mul, ofReal_exp_mul]
      _ ≤ ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
          apply ENNReal.ofReal_le_ofReal
          apply exp_le_one_div_pow
          have e1 : ((32 * n ^ 2 : ℕ) : ℝ) / n = 32 * n := by
            rw [div_eq_iff hn0.ne']; push_cast; ring
          rw [e1]
          push_cast
          nlinarith
  -- the errorcount term
  have hB : 80 * n + 1 - 1 = 80 * n := Nat.add_sub_cancel _ _
  have hec : ecV3 (2 ^ (80 * n + 1 - 1)) (208 * n) X ≤
      (n : ℝ≥0∞) * (2 ^ (80 * n) * 2⁻¹ ^ (208 * n)) := by
    rw [hB]
    unfold ecV3
    refine le_of_eq ?_
    calc ∑ w, ecTerm (2 ^ (80 * n)) (208 * n) (X w).1
        = ∑ _w : Fin n, ((2 : ℝ≥0∞) ^ (80 * n) * 2⁻¹ ^ (208 * n)) :=
          Finset.sum_congr rfl fun w _ => by
            simp [ecTerm, hR w]
      _ = (n : ℝ≥0∞) * (2 ^ (80 * n) * 2⁻¹ ^ (208 * n)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have t2 : (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ (32 * n ^ 2) * ecV3 (2 ^ (80 * n + 1 - 1)) (208 * n) X ≤
      ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
    calc (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ (32 * n ^ 2) * ecV3 (2 ^ (80 * n + 1 - 1)) (208 * n) X
        ≤ ENNReal.ofReal (Real.exp (2 * ((32 * n ^ 2 : ℕ) : ℝ) / n)) *
            (ENNReal.ofReal (Real.exp n) *
              (ENNReal.ofReal (Real.exp (((80 * n : ℕ) : ℝ) * Real.log 2)) *
                ENNReal.ofReal (Real.exp (-(((208 * n : ℕ) : ℝ) * Real.log 2))))) := by
          refine mul_le_mul' (one_add_two_inv_pow_le n _ (by omega)) (hec.trans ?_)
          rw [tr_two_pow_eq_ofReal, inv_two_pow_eq_ofReal]
          exact mul_le_mul_left (natCast_le_ofReal_exp n) _
      _ = ENNReal.ofReal (Real.exp (2 * ((32 * n ^ 2 : ℕ) : ℝ) / n +
            (n + (((80 * n : ℕ) : ℝ) * Real.log 2 + -(((208 * n : ℕ) : ℝ) * Real.log 2))))) := by
          rw [ofReal_exp_mul, ofReal_exp_mul, ofReal_exp_mul]
      _ ≤ ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
          apply ENNReal.ofReal_le_ofReal
          apply exp_le_one_div_pow
          have e1 : 2 * ((32 * n ^ 2 : ℕ) : ℝ) / n = 64 * n := by
            rw [div_eq_iff hn0.ne']; push_cast; ring
          rw [e1]
          push_cast
          nlinarith
  -- the median-timer term
  have htExp : tExp (7 * (40 + 4)) X ≤ 1 := by
    have hnone : ∀ w, ¬ MedAt (X w).1 := fun w hw => absurd hw.1 (by rw [hR w]; decide)
    unfold tExp
    rw [medTimer_none hnone]
    split_ifs <;> omega
  have hNpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have hNr : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hWN : 2 * (32 * n ^ 2) ≤ 65 * (n * (n - 1)) := by
    have hlin : 64 * n ≤ 65 * (n - 1) := by omega
    calc
      2 * (32 * n ^ 2) = n * (64 * n) := by ring
      _ ≤ n * (65 * (n - 1)) := Nat.mul_le_mul_left n hlin
      _ = 65 * (n * (n - 1)) := by ring
  have hr65 : 2 * ((32 * n ^ 2 : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ) ≤ 65 := by
    rw [div_le_iff₀ hNr]; exact_mod_cast hWN
  have t3 : (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) ^ (32 * n ^ 2) *
      (2 ^ tExp (7 * (40 + 4)) X * (2 ^ (7 * (40 + 4) - 180 + 1))⁻¹) ≤
      ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
    have e129 : 7 * (40 + 4) - 180 + 1 = 129 := by norm_num
    calc (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) ^ (32 * n ^ 2) *
          (2 ^ tExp (7 * (40 + 4)) X * (2 ^ (7 * (40 + 4) - 180 + 1))⁻¹)
        ≤ ENNReal.ofReal (Real.exp (2 * ((32 * n ^ 2 : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ))) *
            (ENNReal.ofReal (Real.exp (((1 : ℕ) : ℝ) * Real.log 2)) *
              ENNReal.ofReal (Real.exp (-(((129 : ℕ) : ℝ) * Real.log 2)))) := by
          rw [e129, ENNReal.inv_pow]
          refine mul_le_mul' (one_add_two_inv_pow_le _ _ hNpos)
            (mul_le_mul' ?_ (inv_two_pow_eq_ofReal 129).le)
          rw [← tr_two_pow_eq_ofReal]
          exact pow_le_pow_right₀ (by norm_num) htExp
      _ = ENNReal.ofReal (Real.exp (2 * ((32 * n ^ 2 : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ) +
            (((1 : ℕ) : ℝ) * Real.log 2 + -(((129 : ℕ) : ℝ) * Real.log 2)))) := by
          rw [ofReal_exp_mul, ofReal_exp_mul]
      _ ≤ ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := by
          apply ENNReal.ofReal_le_ofReal
          apply exp_le_one_div_pow
          simp only [Nat.cast_ofNat, Nat.cast_one]
          linarith
  calc (1 - (n : ℝ≥0∞)⁻¹) ^ (32 * n ^ 2) * dormV X +
        (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ (32 * n ^ 2) * ecV3 (2 ^ (80 * n + 1 - 1)) (208 * n) X +
        (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) ^ (32 * n ^ 2) *
          (2 ^ tExp (7 * (40 + 4)) X * (2 ^ (7 * (40 + 4) - 180 + 1))⁻¹)
      ≤ ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) + ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) +
          ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10) := add_le_add (add_le_add t1 t2) t3
    _ = ENNReal.ofReal (1 / (2.7 : ℝ) ^ 10 + 1 / (2.7 : ℝ) ^ 10 + 1 / (2.7 : ℝ) ^ 10) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal 0.02 := ENNReal.ofReal_le_ofReal (by norm_num)

/-! ### P3 Lemma 11 -/

/-- **P3 Lemma 11** (with the R3 fix F1): `FD_1 → R(99)` within `52 n²` interactions with
probability `≥ 0.753`. -/
theorem stageB34 : StageB34 := by
  have h3 := stageB3_gen (fun _ => True) (by intros; trivial)
  have h4 := stageB4_gen (fun _ => True) (fun C => RTheta 99 C) (by intros; trivial)
    (fun _ h _ => h)
  have h := (h3.comp h4 (by norm_num)).mono (W' := fun n => 52 * n ^ 2)
    (fun _ _ => le_of_eq (by ring))
    (by norm_num : (0.753 : ℝ) ≤ 0.98 * 0.77)
  intro n hN hn hn2 X hX hA
  exact h n hN hn hn2 X hX ⟨hA, trivial⟩

/-! ### The answer version -/

/-- The answer invariant of the tree phase: every agent has the majority answer, except Settled
agents of median-type rank. -/
def AnsInvC (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ w, (C w).1.answer = majorityAnswer C ∨
    ((C w).1.role = .Settled ∧ IsMedType n (C w).1.rank.val)

/-- The answer invariant survives a tree-phase step: answers move only with their states
(possibly exchanged by a Phase-4 swap), and change only at median-type ranks. -/
theorem ansInv_step {hn : 0 < n} (hn3 : 3 ≤ n) (C : Config (AgentState n) Opinion n)
    (h : TreeStepHyp C) (hA : AnsInvC C) (u v : Fin n) (huv : u ≠ v) :
    AnsInvC (C.step (PEM40 n hn) u v) := by
  change AnsInvC (C.step (protocolPEM n 40 (rmaxPaper n)
    (rankDeltaOSSR (rmaxPaper n) (208 * n) (32 * n) hn)) u v)
  obtain ⟨-, hsu, hsv, π, hπ, -, -, hans⟩ := pem_tree_step (trank := 40) (Rmax := rmaxPaper n)
    (Emax := 208 * n) (Dmax := 32 * n) (hn := hn) C h huv (by norm_num) hn3
  have hpers : ∀ x, (C x).1.role = .Settled →
      (kstep (rankDeltaOSSR (rmaxPaper n) (208 * n) (32 * n) hn) (kC C) u v x).role =
        .Settled ∧
      (kstep (rankDeltaOSSR (rmaxPaper n) (208 * n) (32 * n) hn) (kC C) u v x).rank =
        (C x).1.rank := by
    intro x hx
    by_cases hxu : x = u
    · subst hxu; exact hsu.settled hx
    · by_cases hxv : x = v
      · subst hxv; exact hsv.settled hx
      · rw [kstep_other _ _ hxu hxv]; exact ⟨hx, rfl⟩
  intro w
  rw [majorityAnswer_step_eq]
  have eb := rhoS_eq_iff.mp (hπ w)
  rcases hans w with h1 | h2 | ⟨hR, hphi⟩
  · rcases hA (π w) with h3 | ⟨hS, hmed⟩
    · exact Or.inl (h1.trans h3)
    · obtain ⟨hS', hr'⟩ := hpers (π w) hS
      exact Or.inr ⟨eb.1.trans hS', by rw [eb.2.1, hr']; exact hmed⟩
  · exact Or.inr h2
  · exfalso
    rcases hA (π w) with h3 | ⟨hS, -⟩
    · exact majorityAnswer_ne_phi C (h3.symm.trans hphi)
    · rw [hR] at hS; exact absurd hS (by decide)

/-- **P3 Lemma 11, answer version**: `FD_1 ∧ AllMaj → R(99) ∧ AnsOK` within `52 n²`
interactions with probability `≥ 0.753`. -/
theorem stageB34M : StageB34M := by
  have hE : ∀ {n : ℕ} (hn : 0 < n), 3 ≤ n → ∀ (C : Config (AgentState n) Opinion n),
      TreeStepHyp C → AnsInvC C → ∀ u v, u ≠ v → AnsInvC (C.step (PEM40 n hn) u v) :=
    fun _ hn3 C h hA u v huv => ansInv_step hn3 C h hA u v huv
  have h3 := stageB3_gen (fun C => AnsInvC C) hE
  have h4 := stageB4_gen (fun C => AnsInvC C) (fun C => RTheta 99 C ∧ AnsOK C) hE
    (fun C hR hA => ⟨hR, fun v _ hnm => (hA v).resolve_right (fun h => hnm h.2)⟩)
  have h := (h3.comp h4 (by norm_num)).mono (W' := fun n => 52 * n ^ 2)
    (fun _ _ => le_of_eq (by ring))
    (by norm_num : (0.753 : ℝ) ≤ 0.98 * 0.77)
  intro n hN hn hn2 X hX hA
  exact h n hN hn hn2 X hX ⟨hA.1, fun w => Or.inl (hA.2 w)⟩

/-! ### Non-vacuity: the start classes are inhabited -/

/-- The all-dormant configuration with agent `0` the leader. -/
def fdOneWitness (n : ℕ) (hn : 0 < n) (x : Fin n → Opinion) : Config (AgentState n) Opinion n :=
  fun w =>
    ({ role := .Resetting
       rank := ⟨0, hn⟩
       leader := if w = ⟨0, hn⟩ then .L else .F
       resetcount := 0
       answer := .outT
       timer := 0
       children := 0
       errorcount := 0
       delaytimer := 0 }, x w)

theorem fdOneWitness_good {hn : 0 < n} (x : Fin n → Opinion) :
    GoodPaper (fdOneWitness n hn x) := fun _ => by
  simp only [GoodPEM, fdOneWitness]
  omega

theorem fdOneWitness_fdOne {hn : 0 < n} (x : Fin n → Opinion) :
    FDOne (fdOneWitness n hn x) := by
  refine ⟨fun _ => ⟨rfl, rfl⟩,
    ⟨⟨0, hn⟩, by simp [fdOneWitness], fun w hw => ?_⟩⟩
  by_contra hne
  simp [fdOneWitness, hne] at hw

private theorem majorityAnswer_eq_of_input_eq
    (C D : Config (AgentState n) Opinion n)
    (h : ∀ w, (C w).2 = (D w).2) :
    majorityAnswer C = majorityAnswer D := by
  have hAgents (x : Opinion) : C.agentsWithInput x = D.agentsWithInput x := by
    unfold Config.agentsWithInput Config.inputOf
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h w]
  unfold majorityAnswer nAOf nBOf
  rw [hAgents Opinion.A, hAgents Opinion.B]

/-- With every opinion `A` the majority answer is `outA`, so the all-dormant configuration with
answers `outA` lies in `FD_1 ∧ AllMaj`. -/
example (hn : 0 < n) : ∃ X : Config (AgentState n) Opinion n,
    GoodPaper X ∧ FDOne X ∧ AllMaj X := by
  let X : Config (AgentState n) Opinion n := fun w =>
    ({ (fdOneWitness n hn (fun _ => .A) w).1 with
       answer := majorityAnswer (fdOneWitness n hn (fun _ => .A)) }, .A)
  refine ⟨X, ?_, ?_, ?_⟩
  · intro w
    simp [GoodPEM, X, fdOneWitness]
  · obtain ⟨hFD, hleader⟩ :=
      fdOneWitness_fdOne (hn := hn) (fun _ : Fin n => Opinion.A)
    refine ⟨?_, ?_⟩
    · intro w
      simpa [X] using hFD w
    · obtain ⟨w, hw, huniq⟩ := hleader
      refine ⟨w, ?_, ?_⟩
      · simpa [X] using hw
      · intro v hv
        apply huniq v
        simpa [X] using hv
  · intro w
    have hmaj :
        majorityAnswer (fdOneWitness n hn (fun _ => .A)) = majorityAnswer X :=
      majorityAnswer_eq_of_input_eq
        (fdOneWitness n hn (fun _ => .A)) X
        (fun v => by simp [X, fdOneWitness])
    simpa [X] using hmaj

end Ripple.PopulationProtocol.SSEM
