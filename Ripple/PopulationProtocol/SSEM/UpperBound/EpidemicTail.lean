/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tail of the two-way epidemic

Paper phase `docs/audit/FIX2-BURMAN.md`, §B.1 (P2'). With `k` reached agents the potential
`Ψ = (n - k)/k` satisfies `E[Ψ'] ≤ (1 - 1/(n-1)) Ψ` under one uniform scheduler pair
(`epiPot_step`), so after `K` interactions
`P[some agent unreached] ≤ n (n - 1) ((n - 2)/(n - 1)) ^ K` (`epidemic_incomplete_le`).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.PropagationTail

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- Number of reached agents. -/
def reachCount (r : Fin n → Bool) : ℕ := (Finset.univ.filter fun w => r w = true).card

/-- Ordered pairs with exactly one reached endpoint. -/
def crossSet (r : Fin n → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => (r p.1 = true ∧ r p.2 = false) ∨ (r p.1 = false ∧ r p.2 = true)

theorem crossSet_subset_offDiagonal (r : Fin n → Bool) : crossSet r ⊆ OffDiagonalPairs n := by
  intro p hp
  rw [mem_offDiagonalPairs]
  simp only [crossSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  intro h
  rw [h] at hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

theorem reachCount_le (r : Fin n → Bool) : reachCount r ≤ n := by
  unfold reachCount
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem crossSet_card (r : Fin n → Bool) :
    (crossSet r).card = 2 * (reachCount r * (n - reachCount r)) := by
  classical
  set A := Finset.univ.filter fun w : Fin n => r w = true
  set B := Finset.univ.filter fun w : Fin n => r w = false
  have hAB : A.card + B.card = n := by
    have := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin n)))
      (fun w => r w = true)
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
    exact this
  have hset : crossSet r = A ×ˢ B ∪ B ×ˢ A := by
    ext p
    simp [crossSet, A, B, Finset.mem_product]
  have hdisj : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_product, A, B, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1.1] at h2
    exact absurd h2.1 (by decide)
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product]
  have : reachCount r = A.card := rfl
  rw [this]
  have hB : B.card = n - A.card := by omega
  rw [hB]
  ring

theorem reachStep_reachCount (r : Fin n → Bool) (p : Fin n × Fin n) :
    reachCount (reachStep r p) = if p ∈ crossSet r then reachCount r + 1 else reachCount r := by
  classical
  obtain ⟨a, b⟩ := p
  unfold reachCount reachStep pairUpd
  by_cases hc : (a, b) ∈ crossSet r
  · rw [if_pos hc]
    have hab : a ≠ b := (mem_offDiagonalPairs n (a, b)).mp (crossSet_subset_offDiagonal r hc)
    simp only [crossSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hset : (Finset.univ.filter fun w =>
          (if a ≠ b ∧ (w = a ∨ w = b) then (r a || r b) else r w) = true) =
          insert b (Finset.univ.filter fun w => r w = true) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hwa : w = a
        · subst hwa; simp [hab, ha]
        · by_cases hwb : w = b
          · subst hwb; simp [hab, ha]
          · simp [hwa, hwb]
      rw [hset, Finset.card_insert_of_notMem (by simp [hb])]
    · have hset : (Finset.univ.filter fun w =>
          (if a ≠ b ∧ (w = a ∨ w = b) then (r a || r b) else r w) = true) =
          insert a (Finset.univ.filter fun w => r w = true) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hwa : w = a
        · subst hwa; simp [hab, hb]
        · by_cases hwb : w = b
          · subst hwb; simp [hab, hb, hwa]
          · simp [hwa, hwb]
      rw [hset, Finset.card_insert_of_notMem (by simp [ha])]
  · rw [if_neg hc]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [crossSet, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and] at hc
    by_cases hw : a ≠ b ∧ (w = a ∨ w = b)
    · rw [if_pos hw]
      rcases hw.2 with rfl | rfl
      · cases hra : r w <;> cases hrb : r b <;> simp_all
      · cases hra : r a <;> cases hrb : r w <;> simp_all
    · rw [if_neg hw]

/-- The epidemic potential `(n - k)/k`. -/
noncomputable def epiPot (n k : ℕ) : ℝ := ((n : ℝ) - k) / k

theorem epiPot_nonneg {k : ℕ} (hk : k ≤ n) : 0 ≤ epiPot n k := by
  unfold epiPot
  apply div_nonneg _ (Nat.cast_nonneg _)
  have : (k : ℝ) ≤ n := by exact_mod_cast hk
  linarith

/-- The real inequality behind the one-step bound:
`RHS - LHS = (n - k)(k - 1) / ((n - 1) k (k + 1)) ≥ 0`. -/
theorem epiPot_step_real (n k : ℝ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    2 * (k * (n - k)) / (n * (n - 1)) * ((n - (k + 1)) / (k + 1)) +
        (1 - 2 * (k * (n - k)) / (n * (n - 1))) * ((n - k) / k) ≤
      (n - 2) / (n - 1) * ((n - k) / k) := by
  have hk0 : k ≠ 0 := by intro h; rw [h] at hk; norm_num at hk
  have hk1 : k + 1 ≠ 0 := by intro h; linarith
  have hn0 : n ≠ 0 := by intro h; rw [h] at hkn; linarith
  have hn1 : n - 1 ≠ 0 := by intro h; linarith
  have key : (n - 2) / (n - 1) * ((n - k) / k) -
      (2 * (k * (n - k)) / (n * (n - 1)) * ((n - (k + 1)) / (k + 1)) +
        (1 - 2 * (k * (n - k)) / (n * (n - 1))) * ((n - k) / k)) =
      (n - k) * (k - 1) / ((n - 1) * k * (k + 1)) := by
    field_simp
    ring
  have hnn : 0 ≤ (n - k) * (k - 1) / ((n - 1) * k * (k + 1)) := by
    apply div_nonneg
    · apply mul_nonneg <;> linarith
    · apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
  linarith

theorem epiPot_nonneg' {k : ℕ} (hk : k ≤ n) : 0 ≤ epiPot n k := epiPot_nonneg hk

theorem reachIter_source (s : Fin n) : ∀ K (σ : SchedulerPrefix n K), reachIter s K σ s = true
  | 0, _ => by simp [reachIter, prefixIter]
  | K + 1, σ => by
      have ih := reachIter_source s K (Fin.init σ)
      simp only [reachIter] at ih ⊢
      rw [prefixIter_succ]
      simp only [reachStep, pairUpd]
      split_ifs with h
      · rcases h.2 with h' | h'
        · rw [← h', ih]; simp
        · rw [← h', ih]; simp
      · exact ih

theorem one_le_reachCount_iter (s : Fin n) (K : ℕ) (σ : SchedulerPrefix n K) :
    1 ≤ reachCount (reachIter s K σ) := by
  unfold reachCount
  exact Finset.card_pos.mpr ⟨s, by simp [reachIter_source]⟩

/-- **One step of the epidemic potential.** -/
theorem epiPot_step (hn : 2 ≤ n) (r : Fin n → Bool) (hk : 1 ≤ reachCount r) :
    ∑ p : Fin n × Fin n, uniformPair n hn p *
        ENNReal.ofReal (epiPot n (reachCount (reachStep r p))) ≤
      ENNReal.ofReal (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
        ENNReal.ofReal (epiPot n (reachCount r)) := by
  classical
  set k := reachCount r with hkdef
  have hkn := reachCount_le r
  have hpt : ∀ p : Fin n × Fin n,
      uniformPair n hn p * ENNReal.ofReal (epiPot n (reachCount (reachStep r p))) =
        if p ∈ crossSet r then uniformPair n hn p * ENNReal.ofReal (epiPot n (k + 1))
        else uniformPair n hn p * ENNReal.ofReal (epiPot n k) := by
    intro p
    rw [reachStep_reachCount]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_ite, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hmc : ∑ p ∈ crossSet r, uniformPair n hn p =
      ENNReal.ofReal ((2 * (k * (n - k)) : ℕ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    have := pairSetMass_eq_card_mul_inv_of_subset n hn (crossSet r)
      (crossSet_subset_offDiagonal r)
    unfold pairSetMass at this
    rw [this, crossSet_card, ← hkdef, div_eq_mul_inv, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_inv_of_pos (by
        have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
        exact_mod_cast this), ENNReal.ofReal_natCast]
  have htot : ∑ p ∈ crossSet r, uniformPair n hn p +
      ∑ p ∈ Finset.univ.filter (fun p => p ∉ crossSet r), uniformPair n hn p = 1 := by
    have h1 : ∑ p : Fin n × Fin n, uniformPair n hn p = 1 := by
      simpa [tsum_fintype] using (uniformPair n hn).tsum_coe
    rw [← h1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p ∈ crossSet r),
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  set x : ℝ := ((2 * (k * (n - k)) : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    have h := hmc ▸ (le_self_add.trans htot.le :
      ∑ p ∈ crossSet r, uniformPair n hn p ≤ 1)
    have := (ENNReal.ofReal_le_one).mp h
    exact this
  have hmn : ∑ p ∈ Finset.univ.filter (fun p => p ∉ crossSet r), uniformPair n hn p =
      ENNReal.ofReal (1 - x) := by
    rw [ENNReal.ofReal_sub _ hx0, ENNReal.ofReal_one, ← hmc]
    rw [← htot, ENNReal.add_sub_cancel_left (by
      rw [hmc]; exact ENNReal.ofReal_ne_top)]
  rw [hmc, hmn]
  by_cases hkn' : k < n
  · have hb : 0 ≤ epiPot n (k + 1) := epiPot_nonneg (by omega)
    have ha : 0 ≤ epiPot n k := epiPot_nonneg hkn
    rw [← ENNReal.ofReal_mul hx0, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (mul_nonneg hx0 hb) (mul_nonneg (by linarith) ha),
      ← ENNReal.ofReal_mul (by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn
        apply div_nonneg <;> linarith)]
    apply ENNReal.ofReal_le_ofReal
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkn'' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn'
    have hreal := epiPot_step_real n k hk' hkn''
    have hxe : x = 2 * ((k : ℝ) * (n - k)) / (n * (n - 1)) := by
      rw [hx]
      push_cast [Nat.cast_sub (show k ≤ n from hkn), Nat.cast_sub (show 1 ≤ n by omega)]
      ring
    unfold epiPot
    rw [hxe]
    push_cast
    exact hreal
  · have hkeq : k = n := by omega
    have hz : x = 0 := by rw [hx, hkeq, Nat.sub_self]; simp
    have ha : epiPot n k = 0 := by unfold epiPot; rw [hkeq]; simp
    rw [hz, ha]
    simp

/-- **Epidemic tail.** -/
theorem epidemic_incomplete_le (hn : 2 ≤ n) (s : Fin n) (K : ℕ) :
    ENNReal.ofReal (1 / n) *
        (schedulerPrefixPMF n hn K).toOuterMeasure {σ | ∃ w, reachIter s K σ w = false} ≤
      ENNReal.ofReal (((n : ℝ) - 2) / ((n : ℝ) - 1)) ^ K * ENNReal.ofReal ((n : ℝ) - 1) := by
  classical
  set F : ∀ K, SchedulerPrefix n K → ℝ≥0∞ :=
    fun K σ => ENNReal.ofReal (epiPot n (reachCount (reachIter s K σ))) with hF
  have hE := schedulerPrefix_expect_le_pow hn F (ENNReal.ofReal (((n : ℝ) - 2) / ((n : ℝ) - 1)))
    (by
      intro K σ
      simp only [hF, reachIter, prefixIter_snoc]
      exact epiPot_step hn _ (one_le_reachCount_iter s K σ)) K
  have h0 : F 0 (fun t => Fin.elim0 t) = ENNReal.ofReal ((n : ℝ) - 1) := by
    simp only [hF, reachIter, prefixIter]
    have : reachCount (fun w : Fin n => decide (w = s)) = 1 := by
      unfold reachCount
      rw [Finset.card_eq_one]
      exact ⟨s, by ext w; simp⟩
    rw [this]
    unfold epiPot
    simp
  rw [h0] at hE
  refine le_trans ?_ hE
  refine le_trans ?_ (schedulerPrefix_markov hn K (F K) (ENNReal.ofReal (1 / n)))
  apply mul_le_mul_left'
  apply MeasureTheory.measure_mono
  intro σ hσ
  obtain ⟨w, hw⟩ := hσ
  change ENNReal.ofReal (1 / n) ≤ F K σ
  simp only [hF]
  apply ENNReal.ofReal_le_ofReal
  have hk1 := one_le_reachCount_iter s K σ
  have hklt : reachCount (reachIter s K σ) < n := by
    unfold reachCount
    calc (Finset.univ.filter fun w => reachIter s K σ w = true).card
        < (Finset.univ : Finset (Fin n)).card := by
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr ⟨w, by simp, ?_⟩
          simp [hw]
      _ = n := by simp
  set k := reachCount (reachIter s K σ)
  unfold epiPot
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hklt
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end Ripple.PopulationProtocol.SSEM
