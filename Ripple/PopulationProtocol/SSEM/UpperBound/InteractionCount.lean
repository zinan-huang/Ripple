/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Interaction counts along a scheduler prefix

`cntIter K σ v` is the number of interactions of agent `v` among the first `K` pairs of `σ`.
Upper tail (`count_tail_le`): `4 ^ D · P[cnt ≥ D] ≤ (1 + 6/n) ^ K` (exponential Markov with
base 4); a union bound over agents gives `count_tail_some_le`. (P2 Lemma 1.5 (b) and Corollary
1.6 in exponential-moment form.)
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.PropagationTail

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- Count step: both endpoints of an off-diagonal pair gain one interaction. -/
def cntStep (c : Fin n → ℕ) (p : Fin n × Fin n) : Fin n → ℕ :=
  fun w => if p ∈ PairsInvolving n w then c w + 1 else c w

/-- Interaction counts along a prefix. -/
def cntIter : (K : ℕ) → SchedulerPrefix n K → Fin n → ℕ :=
  prefixIter (fun _ => 0) cntStep

theorem cntIter_succ_ge (K : ℕ) (σ : SchedulerPrefix n (K + 1)) (v : Fin n) :
    cntIter K (Fin.init σ) v ≤ cntIter (K + 1) σ v := by
  simp only [cntIter, prefixIter_succ, cntStep]
  split_ifs <;> omega

theorem uniformPair_sum_four_pow (hn : 2 ≤ n) (v : Fin n) :
    ∑ p : Fin n × Fin n, uniformPair n hn p * (if p ∈ PairsInvolving n v then 4 else 1) =
      1 + 3 * (2 * (n : ℝ≥0∞)⁻¹) := by
  classical
  have h1 : ∀ p : Fin n × Fin n, uniformPair n hn p * (if p ∈ PairsInvolving n v then 4 else 1) =
      uniformPair n hn p + (if p ∈ PairsInvolving n v then uniformPair n hn p * 3 else 0) := by
    intro p
    split_ifs
    · rw [show (4 : ℝ≥0∞) = 1 + 3 by norm_num, mul_add, mul_one]
    · rw [mul_one, add_zero]
  rw [Finset.sum_congr rfl (fun p _ => h1 p), Finset.sum_add_distrib]
  have hsum : ∑ p : Fin n × Fin n, uniformPair n hn p = 1 := by
    simpa [tsum_fintype] using (uniformPair n hn).tsum_coe
  rw [hsum, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.sum_mul]
  have := pairSetMass_pairsInvolving n hn v
  unfold pairSetMass at this
  rw [this, mul_comm]

/-- **Upper tail of an interaction count.** -/
theorem count_tail_le (hn : 2 ≤ n) (v : Fin n) (K D : ℕ) :
    4 ^ D * (schedulerPrefixPMF n hn K).toOuterMeasure {σ | D ≤ cntIter K σ v} ≤
      (1 + 3 * (2 * (n : ℝ≥0∞)⁻¹)) ^ K := by
  classical
  have hE := schedulerPrefix_expect_le_pow hn (fun K σ => (4 : ℝ≥0∞) ^ cntIter K σ v)
    (1 + 3 * (2 * (n : ℝ≥0∞)⁻¹)) (by
      intro K σ
      simp only [cntIter, prefixIter_snoc, cntStep]
      have h2 : ∀ p : Fin n × Fin n, uniformPair n hn p *
          (4 : ℝ≥0∞) ^ (if p ∈ PairsInvolving n v then
            prefixIter (fun _ => 0) cntStep K σ v + 1
            else prefixIter (fun _ => 0) cntStep K σ v) =
          (4 : ℝ≥0∞) ^ prefixIter (fun _ => 0) cntStep K σ v *
            (uniformPair n hn p * (if p ∈ PairsInvolving n v then 4 else 1)) := by
        intro p
        split_ifs
        · rw [pow_succ]; ring
        · ring
      rw [Finset.sum_congr rfl (fun p _ => h2 p), ← Finset.mul_sum,
        uniformPair_sum_four_pow hn v, mul_comm]) K
  simp only [cntIter, prefixIter, pow_zero, mul_one] at hE
  refine le_trans ?_ hE
  have hM := schedulerPrefix_markov hn K (fun σ => (4 : ℝ≥0∞) ^ cntIter K σ v) (4 ^ D)
  refine le_trans (mul_le_mul_left' (MeasureTheory.measure_mono ?_) _) hM
  intro σ hσ
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 4) hσ

/-- **Some agent reaches `D` interactions** (union bound). -/
theorem count_tail_some_le (hn : 2 ≤ n) (K D : ℕ) :
    4 ^ D * (schedulerPrefixPMF n hn K).toOuterMeasure {σ | ∃ v, D ≤ cntIter K σ v} ≤
      n * (1 + 3 * (2 * (n : ℝ≥0∞)⁻¹)) ^ K := by
  classical
  have hU : {σ : SchedulerPrefix n K | ∃ v, D ≤ cntIter K σ v} =
      ⋃ v, {σ | D ≤ cntIter K σ v} := by
    ext σ; simp
  rw [hU]
  calc 4 ^ D * (schedulerPrefixPMF n hn K).toOuterMeasure (⋃ v, {σ | D ≤ cntIter K σ v})
      ≤ 4 ^ D * ∑ v : Fin n, (schedulerPrefixPMF n hn K).toOuterMeasure
          {σ | D ≤ cntIter K σ v} :=
        mul_le_mul_left' (MeasureTheory.measure_iUnion_fintype_le _ _) _
    _ = ∑ v : Fin n, 4 ^ D * (schedulerPrefixPMF n hn K).toOuterMeasure
          {σ | D ≤ cntIter K σ v} := Finset.mul_sum _ _ _
    _ ≤ ∑ _v : Fin n, (1 + 3 * (2 * (n : ℝ≥0∞)⁻¹)) ^ K :=
        Finset.sum_le_sum fun v _ => count_tail_le hn v K D
    _ = n * (1 + 3 * (2 * (n : ℝ≥0∞)⁻¹)) ^ K := by
        simp [Finset.sum_const, nsmul_eq_mul]

end Ripple.PopulationProtocol.SSEM
