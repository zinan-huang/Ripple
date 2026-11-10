/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stages E and C (P3 Lemmas 16, 17, 21)

* `stageE : StageE` (P3 Lemma 21): from `Cons`, the silent consensus `S_em` is hit within
  `308 n²` interactions with probability at least `0.999`. On `Cons` a step only ticks the median
  timer, which drops by one exactly at the two ordered pairs {median, last} (`srank_step_medT`).
  The potential `2 ^ medT` has one-step mean at most `(1 - 1/(n(n-1))) 2 ^ medT`
  (`srank_tick_expect`), so the failure probability is at most
  `2^308 (1 - 1/(n(n-1)))^(308 n²) ≤ (2/e)^308` (`countdown_numeric`).
* `stageC : StageC` (P3 Lemma 17): from `D`, `S_em ∪ Z` is hit within `311 n²` interactions with
  probability at least `0.997`. First `308 n²` steps: countdown to `D ∩ {medT = 0}` (or `Z`, or
  `S_em`) as in Lemma 16, with `D` kept by non-reset steps and a reset from `D` landing in `Z`
  (P3 Lemma 2). Next `3 n²` steps: from `D ∩ {medT = 0}` outside `S_em`, some agent `w` has a
  wrong answer, and the two ordered pairs {median, `w`} reset into `Z`
  (`decided_step_reset`); failure at most `(1 - 2/(n(n-1)))^(3 n²) ≤ e^{-6}`.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.SRankStep

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-! ### Common tools -/

/-- The number `n (n - 1)` of ordered pairs of distinct agents, as a real number. -/
noncomputable def npairs (n : ℕ) : ℝ := ((n * (n - 1) : ℕ) : ℝ)

theorem npairs_eq (hn2 : 2 ≤ n) : npairs n = (n : ℝ) * ((n : ℝ) - 1) := by
  unfold npairs
  rw [Nat.cast_mul, Nat.cast_sub (by omega)]
  simp

theorem two_le_npairs (hn2 : 2 ≤ n) : 2 ≤ npairs n := by
  rw [npairs_eq hn2]
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  nlinarith

theorem npairs_le_sq (hn2 : 2 ≤ n) : npairs n ≤ (n : ℝ) ^ 2 := by
  rw [npairs_eq hn2]
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

theorem step_self' {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n) (i : Fin n) :
    C.step P i i = C := by
  simp [Config.step]

theorem two_pow_eq_ofReal (k : ℕ) : (2 : ℝ≥0∞) ^ k = ENNReal.ofReal ((2 : ℝ) ^ k) := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- From a not-hit bound to a hit bound. -/
theorem probHitBy_ge_of_probNotHitBy_le {Q X Y : Type*} (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) (t : ℕ) (f q : ℝ) (hf : 0 ≤ f)
    (hq : q ≤ 1 - f) (h : probNotHitBy P hn C₀ Goal t ≤ ENNReal.ofReal f) :
    ENNReal.ofReal q ≤ probHitBy P hn C₀ Goal t := by
  have hne : probNotHitBy P hn C₀ Goal t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have e : probHitBy P hn C₀ Goal t = 1 - probNotHitBy P hn C₀ Goal t :=
    ENNReal.eq_sub_of_add_eq hne (probHitBy_add_probNotHitBy P hn C₀ Goal t)
  rw [e]
  calc ENNReal.ofReal q ≤ ENNReal.ofReal (1 - f) := ENNReal.ofReal_le_ofReal hq
    _ = 1 - ENNReal.ofReal f := by rw [ENNReal.ofReal_sub _ hf, ENNReal.ofReal_one]
    _ ≤ 1 - probNotHitBy P hn C₀ Goal t := tsub_le_tsub_left h 1

/-- Two ordered pairs `{(a, b), (b, a)}` have mass `2 / (n (n - 1))`. -/
theorem mass_two (hn2 : 2 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    ∑ p ∈ ({(a, b), (b, a)} : Finset (Fin n × Fin n)), uniformPair n hn2 p =
      ENNReal.ofReal (2 / npairs n) := by
  have hne : ((a, b) : Fin n × Fin n) ≠ (b, a) := fun h => hab (Prod.mk.inj h).1
  rw [uniformPair_mass_card hn2 _ (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hab
    · exact Ne.symm hab), Finset.card_pair hne]
  unfold npairs
  norm_num

/-- `(1 - c/(n(n-1)))^(m n²) ≤ e^{-c m}`. -/
theorem pow_pairs_le (hn2 : 2 ≤ n) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 2) (m : ℕ) :
    ENNReal.ofReal (1 - c / npairs n) ^ (m * n ^ 2) ≤ ENNReal.ofReal (Real.exp (-(c * m))) := by
  have hN := two_le_npairs hn2
  have hNsq := npairs_le_sq hn2
  have hN0 : 0 < npairs n := by linarith
  have hc1 : c / npairs n ≤ 1 := by rw [div_le_one hN0]; linarith
  rw [← ENNReal.ofReal_pow (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  refine (one_sub_pow_le_exp (by positivity) hc1 _).trans (Real.exp_le_exp.mpr ?_)
  have key : c * m ≤ c / npairs n * ((m * n ^ 2 : ℕ) : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hN0]
    push_cast
    have hm : (0 : ℝ) ≤ m := by positivity
    have := mul_le_mul_of_nonneg_left hNsq (mul_nonneg hc0 hm)
    nlinarith
  linarith

/-- `e^{-k} 2^k ≤ (20/27)^k`. -/
theorem exp_neg_mul_two_pow (k : ℕ) : Real.exp (-(k : ℝ)) * 2 ^ k ≤ (20 / 27 : ℝ) ^ k := by
  have he : (2.7 : ℝ) ^ k ≤ Real.exp k := by
    rw [show (k : ℝ) = k * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) k
  have h27 : (0 : ℝ) < 2.7 ^ k := by positivity
  rw [Real.exp_neg]
  calc (Real.exp k)⁻¹ * 2 ^ k ≤ ((2.7 : ℝ) ^ k)⁻¹ * 2 ^ k := by
        gcongr
    _ = ((2.7 : ℝ)⁻¹ * 2) ^ k := by rw [mul_pow, inv_pow]
    _ = (20 / 27 : ℝ) ^ k := by norm_num

/-- The countdown failure bound: `(1 - 1/(n(n-1)))^(308 n²) 2^x ≤ 10⁻⁴` for `x ≤ 308`. -/
theorem countdown_numeric (hN : 1608 ≤ n) (x : ℕ) (hx : x ≤ 308) :
    ENNReal.ofReal (1 - 1 / npairs n) ^ (308 * n ^ 2) * 2 ^ x ≤ ENNReal.ofReal 0.0001 := by
  have hn2 : 2 ≤ n := by omega
  refine (mul_le_mul' (pow_pairs_le hn2 1 zero_le_one (by norm_num) 308)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hx)).trans ?_
  rw [two_pow_eq_ofReal, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  calc Real.exp (-(1 * ((308 : ℕ) : ℝ))) * 2 ^ 308
        = Real.exp (-((308 : ℕ) : ℝ)) * 2 ^ 308 := by rw [one_mul]
    _ ≤ (20 / 27 : ℝ) ^ 308 := exp_neg_mul_two_pow 308
    _ ≤ (20 / 27 : ℝ) ^ 40 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
    _ ≤ 0.0001 := by norm_num

/-- **One step of the countdown** (P3 Lemmas 4, 16): on `S_rank` with median timer `x ≥ 1`, the
mean of `2 ^ medT` after one step is at most `(1 - 1/(n(n-1))) 2^x`. -/
theorem srank_tick_expect {hn : 0 < n} (hn2 : 2 ≤ n) {C : Config (AgentState n) Opinion n}
    (hC : SRank C) (h1 : 1 ≤ medT C) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p * (2 : ℝ≥0∞) ^ medT (C.step (PEM40 n hn) p.1 p.2) ≤
      ENNReal.ofReal (1 - 1 / npairs n) * 2 ^ medT C := by
  obtain ⟨μ, hμ⟩ := srank_exists_median hC hn2
  obtain ⟨ν, hν⟩ := srank_exists_last hC hn2
  have hμν : μ ≠ ν := by
    intro h; rw [h] at hμ; unfold ceilHalf at hμ; omega
  have hlow : ∀ p ∈ ({(μ, ν), (ν, μ)} : Finset (Fin n × Fin n)),
      (2 : ℝ≥0∞) ^ medT (C.step (PEM40 n hn) p.1 p.2) ≤ ENNReal.ofReal (2 ^ (medT C - 1)) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [← two_pow_eq_ofReal]
    rcases hp with rfl | rfl
    · rw [srank_step_medT hC hμν, if_pos (show tickS n (C μ).1 (C ν).1 from Or.inl ⟨hμ, hν⟩)]
    · rw [srank_step_medT hC (Ne.symm hμν),
        if_pos (show tickS n (C ν).1 (C μ).1 from Or.inr ⟨hμ, hν⟩)]
  have hall : ∀ p : Fin n × Fin n,
      (2 : ℝ≥0∞) ^ medT (C.step (PEM40 n hn) p.1 p.2) ≤ ENNReal.ofReal (2 ^ medT C) := by
    intro p
    rw [← two_pow_eq_ofReal]
    apply pow_le_pow_right₀ (by norm_num)
    by_cases h : p.1 = p.2
    · have e : C.step (PEM40 n hn) p.1 p.2 = C := by rw [h]; exact step_self' _ _ _
      exact le_of_eq (by rw [e])
    · rw [srank_step_medT hC h]; omega
  have hs := sum_uniformPair_split hn2
    (fun p => (2 : ℝ≥0∞) ^ medT (C.step (PEM40 n hn) p.1 p.2))
    {(μ, ν), (ν, μ)} (2 ^ (medT C - 1)) (2 ^ medT C) (by positivity) (by positivity) hlow
    (fun p _ => hall p)
  have hN := two_le_npairs hn2
  rw [mass_two hn2 hμν, ENNReal.toReal_ofReal (by positivity)] at hs
  refine hs.trans (le_of_eq ?_)
  have hq : 0 ≤ 1 - 1 / npairs n := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  rw [two_pow_eq_ofReal, ← ENNReal.ofReal_mul hq]
  congr 1
  have e : (2 : ℝ) ^ medT C = 2 * 2 ^ (medT C - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [e]
  ring

theorem cons_srank {C : Config (AgentState n) Opinion n} (h : IsConsensusConfig C) : SRank C :=
  ⟨h.allSettled, h.ranks_inj⟩

theorem cons_step40 {hn : 0 < n} {C : Config (AgentState n) Opinion n}
    (h : IsConsensusConfig C) (i j : Fin n) : IsConsensusConfig (C.step (PEM40 n hn) i j) :=
  step_preserves_consensus rankDeltaOSSR_satisfies_fix h i j

theorem medT_le_of_good {C : Config (AgentState n) Opinion n} (hG : GoodPaper C) (hC : SRank C)
    (hn2 : 2 ≤ n) : medT C ≤ 308 := by
  obtain ⟨μ, hμ⟩ := srank_exists_median hC hn2
  rw [medT_eq hC hμ]
  have := (hG μ).1
  omega

theorem one_le_medT_of_not_silent {C : Config (AgentState n) Opinion n}
    (hC : IsConsensusConfig C) (hG : ¬ IsSilentConsensus C) : 1 ≤ medT C := by
  by_contra h
  apply hG
  refine ⟨hC, fun v hv => ?_⟩
  rw [← medT_eq (cons_srank hC) hv]
  omega

/-! ### Stage E -/

/-- **Stage E** (P3 Lemma 21): `Cons → S_em` within `308 n²`, probability `0.999`. -/
theorem stageE : StageE := by
  intro n hN hn hn2 X hX hA
  have h := probNotHitBy_le_potential_avoid (PEM40 n hn) hn2 X IsSilentConsensus
    IsConsensusConfig (fun C => (2 : ℝ≥0∞) ^ medT C) (ENNReal.ofReal (1 - 1 / npairs n)) 1 hA
    (fun C hC _ i j => Or.inl (cons_step40 hC i j))
    (fun C hC hG => srank_tick_expect hn2 (cons_srank hC) (one_le_medT_of_not_silent hC hG))
    (fun C _ _ => one_le_pow₀ (by norm_num)) (308 * n ^ 2)
  rw [one_mul] at h
  have hx := medT_le_of_good hX (cons_srank hA) hn2
  exact probHitBy_ge_of_probNotHitBy_le _ hn2 X _ _ 0.0001 0.999 (by norm_num) (by norm_num)
    (h.trans (countdown_numeric hN _ hx))

/-! ### Stage C -/

/-- **Stage C** (P3 Lemma 17): `D → S_em ∪ Z` within `311 n²`, probability `0.997`. -/
theorem stageC : StageC := by
  intro n hN hn hn2 X hX hA
  let Mid : Config (AgentState n) Opinion n → Prop :=
    fun C => (Decided C ∧ medT C = 0) ∨ IsSilentConsensus C ∨ ZTwo C
  let Goal : Config (AgentState n) Opinion n → Prop := fun C => IsSilentConsensus C ∨ ZTwo C
  -- phase 1: countdown
  have hInv1 : ∀ C, Decided C → ¬ Mid C → ∀ i j : Fin n,
      Decided (C.step (PEM40 n hn) i j) ∨ Mid (C.step (PEM40 n hn) i j) := by
    intro C hC _ i j
    by_cases hij : i = j
    · subst hij; rw [step_self']; exact Or.inl hC
    · by_cases hS : SRank (C.step (PEM40 n hn) i j)
      · exact Or.inl (decided_step hC hij hS)
      · exact Or.inr (Or.inr (Or.inr (decided_step_zTwo hC hij hS)))
  have h1 : probNotHitBy (PEM40 n hn) hn2 X Mid (308 * n ^ 2) ≤ ENNReal.ofReal 0.0001 := by
    have h := probNotHitBy_le_potential_avoid (PEM40 n hn) hn2 X Mid Decided
      (fun C => (2 : ℝ≥0∞) ^ medT C) (ENNReal.ofReal (1 - 1 / npairs n)) 1 hA hInv1
      (fun C hC hG => srank_tick_expect hn2 hC.1.1 (by
        by_contra h0
        exact hG (Or.inl ⟨hC, by omega⟩)))
      (fun C _ _ => one_le_pow₀ (by norm_num)) (308 * n ^ 2)
    rw [one_mul] at h
    exact h.trans (countdown_numeric hN _ (medT_le_of_good hX hA.1.1 hn2))
  -- phase 2: the median meets a wrong answer
  have hD : ∀ C, Mid C → ¬ Goal C → Decided C ∧ medT C = 0 := by
    intro C hI hG
    rcases hI with h | h | h
    · exact h
    · exact absurd (Or.inl h) hG
    · exact absurd (Or.inr h) hG
  have hInv2 : ∀ C, Mid C → ¬ Goal C → ∀ i j : Fin n,
      Mid (C.step (PEM40 n hn) i j) ∨ Goal (C.step (PEM40 n hn) i j) := by
    intro C hI hG i j
    have hC := hD C hI hG
    by_cases hij : i = j
    · subst hij; rw [step_self']; exact Or.inl hI
    · by_cases hS : SRank (C.step (PEM40 n hn) i j)
      · refine Or.inl (Or.inl ⟨decided_step hC.1 hij hS, ?_⟩)
        rw [srank_step_medT hC.1.1.1 hij, hC.2]
        simp
      · exact Or.inr (Or.inr (decided_step_zTwo hC.1 hij hS))
  have hstep2 : ∀ C, Mid C → ¬ Goal C → ∃ S : Finset (Fin n × Fin n),
      (∀ p ∈ S, Goal (C.step (PEM40 n hn) p.1 p.2)) ∧
        ENNReal.ofReal (2 / npairs n) ≤ ∑ p ∈ S, uniformPair n hn2 p := by
    intro C hI hG
    have hC := hD C hI hG
    obtain ⟨μ, hμ⟩ := srank_exists_median hC.1.1.1 hn2
    have hw : ∃ w, (C w).1.answer ≠ majorityAnswer C := by
      by_contra hw
      simp only [not_exists, not_not] at hw
      apply hG
      left
      refine ⟨⟨hC.1.1.1.1, hC.1.1.1.2, hC.1.1.2, hw⟩, fun v hv => ?_⟩
      rw [← medT_eq hC.1.1.1 hv]
      exact hC.2
    obtain ⟨w, hw⟩ := hw
    have hμw : μ ≠ w := by
      rintro rfl
      exact hw (hC.1.2 μ (Or.inl hμ))
    refine ⟨{(μ, w), (w, μ)}, ?_, (mass_two hn2 hμw).ge⟩
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Or.inr (decided_step_zTwo hC.1 hμw
        (decided_step_reset hC.1 hμw hC.2 (Or.inl ⟨hμ, hw⟩)))
    · exact Or.inr (decided_step_zTwo hC.1 (Ne.symm hμw)
        (decided_step_reset hC.1 (Ne.symm hμw) hC.2 (Or.inr ⟨hμ, hw⟩)))
  have h2 : ∀ C, Mid C → probNotHitBy (PEM40 n hn) hn2 C Goal (3 * n ^ 2) ≤
      ENNReal.ofReal 0.002479 := by
    intro C hC
    refine (probNotHitBy_le_geom (PEM40 n hn) hn2 C Goal Mid (2 / npairs n)
      (by have := two_le_npairs hn2; positivity) hC hInv2 hstep2 (3 * n ^ 2)).trans ?_
    refine (pow_pairs_le hn2 2 (by norm_num) le_rfl 3).trans (ENNReal.ofReal_le_ofReal ?_)
    have := exp_neg_six_lt
    have e : -(2 * ((3 : ℕ) : ℝ)) = -6 := by norm_num
    rw [e]
    exact this.le
  have h := probNotHitBy_compose_le (PEM40 n hn) hn2 X Mid Goal _ _ _ _ h1 h2
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    show 308 * n ^ 2 + 3 * n ^ 2 = 311 * n ^ 2 by ring] at h
  exact probHitBy_ge_of_probNotHitBy_le _ hn2 X _ _ _ 0.997 (by norm_num) (by norm_num) h

end Ripple.PopulationProtocol.SSEM
