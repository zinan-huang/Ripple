/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Probability tools for the stage bounds on `S_rank`

Variants of the prefix tools of `Probability/PrefixTools.lean` in which the one-step conditions
are required only outside the goal (P3 Lemma 3 with first-hit stopping; P2 Lemmas 1.4, 1.5):

* `pathAvoids_inv`: along a run that has not yet hit `Goal`, an invariant `Inv` holds as soon
  as every step from `Inv \ Goal` lands in `Inv ∪ Goal`;
* `probNotHitBy_le_potential_avoid`: multiplicative potential, `a · P[not hit] ≤ ρ ^ K V(C₀)`;
* `probNotHitBy_le_geom`: if from every configuration of `Inv \ Goal` a set of scheduler pairs of
  mass at least `m` leads into `Goal`, then `P[not hit within K] ≤ (1 - m) ^ K` (P3 Lemma 4(ii));
* `probNotHitBy_window_le_drift_avoid`: additive drift, `W · P[not hit within W] ≤ Φ(C₀)`
  (P2 Lemma 1.4);
* `probHitBy_le_potential_grow`: a growing potential stopped at the first visit to `Goal` bounds
  the probability of hitting `Goal` (exponential Markov inequality, P2 Lemma 1.5(a));
* `sum_uniformPair_split`, `uniformPair_mass_card`: one-step expectations over the uniform pair;
* `sum_step_add`: an agent sum changes only at the two interacting agents.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.EpochCompose
import Ripple.PopulationProtocol.SSEM.Probability.PrefixTools

namespace Ripple.PopulationProtocol.SSEM
namespace Probability

open scoped BigOperators ENNReal

variable {Q X Y : Type*} {n : ℕ}

/-! ### Invariants until the goal is hit -/

/-- Along a run that avoids `Goal`, `Inv` holds, provided every step from `Inv \ Goal` lands in
`Inv ∪ Goal`. -/
theorem pathAvoids_inv (P : Protocol Q X Y) (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop)
    (h₀ : Inv C₀)
    (hInv : ∀ C, Inv C → ¬ Goal C → ∀ i j : Fin n, Inv (C.step P i j) ∨ Goal (C.step P i j)) :
    ∀ (K : ℕ) (σ : SchedulerPrefix n K), PathAvoids P C₀ Goal K σ → Inv (runPrefix P C₀ K σ)
  | 0, _, _ => h₀
  | K + 1, σ, h => by
      have hK : PathAvoids P C₀ Goal K (Fin.init σ) := h.1
      have hI := pathAvoids_inv P C₀ Goal Inv h₀ hInv K (Fin.init σ) hK
      have hG := pathAvoids_final P C₀ Goal K (Fin.init σ) hK
      have hlast : ¬ Goal (runPrefix P C₀ (K + 1) σ) := h.2
      rw [runPrefix_succ] at hlast ⊢
      rcases hInv _ hI hG (σ (Fin.last K)).1 (σ (Fin.last K)).2 with h' | h'
      · exact h'
      · exact absurd h' hlast

/-! ### Multiplicative potential outside the goal -/

/-- **Not-hit bound from a potential, step condition outside the goal only.** -/
theorem probNotHitBy_le_potential_avoid (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞)
    (ρ a : ℝ≥0∞) (h₀ : Inv C₀)
    (hInv : ∀ C, Inv C → ¬ Goal C → ∀ i j : Fin n, Inv (C.step P i j) ∨ Goal (C.step P i j))
    (hstep : ∀ C, Inv C → ¬ Goal C →
      ∑ p : Fin n × Fin n, uniformPair n hn p * V (C.step P p.1 p.2) ≤ ρ * V C)
    (hlow : ∀ C, Inv C → ¬ Goal C → a ≤ V C) (K : ℕ) :
    a * probNotHitBy P hn C₀ Goal K ≤ ρ ^ K * V C₀ := by
  classical
  let F : ∀ K, SchedulerPrefix n K → ℝ≥0∞ := fun K σ =>
    if PathAvoids P C₀ Goal K σ then V (runPrefix P C₀ K σ) else 0
  have hF : ∀ K (σ : SchedulerPrefix n K),
      ∑ p : Fin n × Fin n, uniformPair n hn p * F (K + 1) (Fin.snoc σ p) ≤ ρ * F K σ := by
    intro K σ
    by_cases hA : PathAvoids P C₀ Goal K σ
    · have hG := pathAvoids_final P C₀ Goal K σ hA
      have hI := pathAvoids_inv P C₀ Goal Inv h₀ hInv K σ hA
      simp only [F, if_pos hA]
      refine le_trans ?_ (hstep _ hI hG)
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_right
      by_cases hA' : PathAvoids P C₀ Goal (K + 1) (Fin.snoc σ p)
      · rw [if_pos hA', runPrefix_snoc]
      · rw [if_neg hA']; exact zero_le
    · have hA' : ∀ p, ¬ PathAvoids P C₀ Goal (K + 1) (Fin.snoc σ p) := fun p h =>
        hA ((pathAvoids_snoc P C₀ Goal K σ p).mp h).1
      simp [F, hA, hA']
  have hE := schedulerPrefix_expect_le_pow hn F ρ hF K
  have hF0 : F 0 (fun t => Fin.elim0 t) ≤ V C₀ := by
    simp only [F]
    split_ifs
    · rfl
    · exact zero_le
  have hM := schedulerPrefix_markov hn K (F K) a
  refine (mul_le_mul_right (probNotHitBy_le_prefixMass_avoid P hn C₀ Goal K) a).trans ?_
  refine le_trans ?_ (hM.trans (hE.trans (mul_le_mul_right hF0 _)))
  apply mul_le_mul_right
  apply MeasureTheory.measure_mono
  intro σ hσ
  have hσ' : PathAvoids P C₀ Goal K σ := hσ
  change a ≤ F K σ
  simp only [F, if_pos hσ']
  exact hlow _ (pathAvoids_inv P C₀ Goal Inv h₀ hInv K σ hσ') (pathAvoids_final P C₀ Goal K σ hσ')

/-! ### One-step expectations over the uniform pair -/

theorem uniformPair_mass_le_one (hn : 2 ≤ n) (S : Finset (Fin n × Fin n)) :
    ∑ p ∈ S, uniformPair n hn p ≤ 1 := by
  rw [← uniformPair_sum_one hn]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)

/-- **Two-level bound**: if `f ≤ x` on `S` and `f ≤ y` off `S`, the mean of `f` under the
uniform pair is at most `M x + (1 - M) y` with `M` the mass of `S`. -/
theorem sum_uniformPair_split (hn : 2 ≤ n) (f : Fin n × Fin n → ℝ≥0∞)
    (S : Finset (Fin n × Fin n)) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hS : ∀ p ∈ S, f p ≤ ENNReal.ofReal x) (hT : ∀ p ∉ S, f p ≤ ENNReal.ofReal y) :
    ∑ p, uniformPair n hn p * f p ≤
      ENNReal.ofReal ((∑ p ∈ S, uniformPair n hn p).toReal * x +
        (1 - (∑ p ∈ S, uniformPair n hn p).toReal) * y) := by
  classical
  set M := ∑ p ∈ S, uniformPair n hn p with hMdef
  have hM1 : M ≤ 1 := uniformPair_mass_le_one hn S
  have hMt : M ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hM1
  have hMr : M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hMt).symm
  have hMr1 : M.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hM1
    simpa using this
  have hMr0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  have hcompl : ∑ p ∈ Sᶜ, uniformPair n hn p = 1 - M := by
    have h := Finset.sum_add_sum_compl S (fun p => uniformPair n hn p)
    rw [uniformPair_sum_one hn] at h
    exact ENNReal.eq_sub_of_add_eq hMt (by rw [add_comm]; exact h)
  rw [← Finset.sum_add_sum_compl S]
  have h1 : ∑ p ∈ S, uniformPair n hn p * f p ≤ M * ENNReal.ofReal x := by
    rw [hMdef, Finset.sum_mul]
    exact Finset.sum_le_sum fun p hp => mul_le_mul_right (hS p hp) _
  have h2 : ∑ p ∈ Sᶜ, uniformPair n hn p * f p ≤ (1 - M) * ENNReal.ofReal y := by
    rw [← hcompl, Finset.sum_mul]
    exact Finset.sum_le_sum fun p hp =>
      mul_le_mul_right (hT p (Finset.mem_compl.mp hp)) _
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [hMr, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hMr0, ← ENNReal.ofReal_mul hMr0,
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by linarith) hy), ENNReal.toReal_ofReal hMr0]

/-- The mass of a set of off-diagonal pairs: `|S| / (n (n - 1))`. -/
theorem uniformPair_mass_card (hn : 2 ≤ n) (S : Finset (Fin n × Fin n))
    (hS : ∀ p ∈ S, p.1 ≠ p.2) :
    ∑ p ∈ S, uniformPair n hn p =
      ENNReal.ofReal ((S.card : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
  have hpos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  rw [Finset.sum_congr rfl (fun p hp => uniformPair_apply_of_ne n hn (hS p hp)),
    Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]

/-! ### Geometric bound from good pairs -/

/-- **Geometric bound** (P3 Lemma 4(ii)): if from every configuration of `Inv \ Goal` a set of
scheduler pairs of mass at least `m` leads into `Goal`, then `P[not hit within K] ≤ (1-m)^K`. -/
theorem probNotHitBy_le_geom (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop) (m : ℝ) (hm : 0 ≤ m) (h₀ : Inv C₀)
    (hInv : ∀ C, Inv C → ¬ Goal C → ∀ i j : Fin n, Inv (C.step P i j) ∨ Goal (C.step P i j))
    (hstep : ∀ C, Inv C → ¬ Goal C → ∃ S : Finset (Fin n × Fin n),
      (∀ p ∈ S, Goal (C.step P p.1 p.2)) ∧ ENNReal.ofReal m ≤ ∑ p ∈ S, uniformPair n hn p)
    (K : ℕ) :
    probNotHitBy P hn C₀ Goal K ≤ ENNReal.ofReal (1 - m) ^ K := by
  classical
  let V : Config Q X n → ℝ≥0∞ := fun C => if Goal C then 0 else 1
  have h := probNotHitBy_le_potential_avoid P hn C₀ Goal Inv V (ENNReal.ofReal (1 - m)) 1 h₀
    hInv ?_ (fun C _ hG => by simp [V, hG]) K
  · rw [one_mul] at h
    refine h.trans ?_
    calc ENNReal.ofReal (1 - m) ^ K * V C₀ ≤ ENNReal.ofReal (1 - m) ^ K * 1 := by
          apply mul_le_mul_right
          simp only [V]
          split_ifs <;> simp
      _ = ENNReal.ofReal (1 - m) ^ K := mul_one _
  · intro C hI hG
    obtain ⟨S, hSg, hSm⟩ := hstep C hI hG
    simp only [V, if_neg hG, mul_one]
    have hsplit := sum_uniformPair_split hn (fun p => if Goal (C.step P p.1 p.2) then 0 else 1)
      S 0 1 le_rfl zero_le_one
      (fun p hp => by simp [hSg p hp])
      (fun p _ => by dsimp only; split_ifs <;> simp)
    refine hsplit.trans (ENNReal.ofReal_le_ofReal ?_)
    have hM := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
      (uniformPair_mass_le_one hn S)) hSm
    rw [ENNReal.toReal_ofReal hm] at hM
    linarith

/-! ### Additive drift outside the goal -/

/-- **Hitting window from additive drift, step condition outside the goal only** (P2 Lemma
1.4): `W · P[Goal not hit within W] ≤ Φ(C₀)`. -/
theorem probNotHitBy_window_le_drift_avoid (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop) (Φ : Config Q X n → ℝ≥0∞)
    (h₀ : Inv C₀)
    (hInv : ∀ C, Inv C → ¬ Goal C → ∀ i j : Fin n, Inv (C.step P i j) ∨ Goal (C.step P i j))
    (hstep : ∀ C, Inv C → ¬ Goal C →
      ∑ p : Fin n × Fin n, uniformPair n hn p * Φ (C.step P p.1 p.2) + 1 ≤ Φ C) (W : ℕ) :
    (W : ℝ≥0∞) * probNotHitBy P hn C₀ Goal W ≤ Φ C₀ := by
  classical
  let c : ∀ K, SchedulerPrefix n K → ℝ≥0∞ := fun K σ =>
    if PathAvoids P C₀ Goal K σ then 1 else 0
  let F : ∀ K, SchedulerPrefix n K → ℝ≥0∞ := fun K σ =>
    if PathAvoids P C₀ Goal K σ then Φ (runPrefix P C₀ K σ) else 0
  have hstepF : ∀ K (σ : SchedulerPrefix n K),
      ∑ p : Fin n × Fin n, uniformPair n hn p * F (K + 1) (Fin.snoc σ p) + c K σ ≤ F K σ := by
    intro K σ
    by_cases hA : PathAvoids P C₀ Goal K σ
    · have hG := pathAvoids_final P C₀ Goal K σ hA
      simp only [F, c, if_pos hA]
      refine le_trans ?_ (hstep _ (pathAvoids_inv P C₀ Goal Inv h₀ hInv K σ hA) hG)
      refine add_le_add ?_ le_rfl
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_right
      by_cases hA' : PathAvoids P C₀ Goal (K + 1) (Fin.snoc σ p)
      · rw [if_pos hA', runPrefix_snoc]
      · rw [if_neg hA']; exact zero_le
    · have hA' : ∀ p, ¬ PathAvoids P C₀ Goal (K + 1) (Fin.snoc σ p) := fun p h =>
        hA ((pathAvoids_snoc P C₀ Goal K σ p).mp h).1
      simp [F, c, hA, hA']
  have hmono : ∀ K (σ : SchedulerPrefix n K) p, c (K + 1) (Fin.snoc σ p) ≤ c K σ := by
    intro K σ p
    by_cases hA' : PathAvoids P C₀ Goal (K + 1) (Fin.snoc σ p)
    · have hA := ((pathAvoids_snoc P C₀ Goal K σ p).mp hA').1
      simp [c, hA, hA']
    · simp only [c, if_neg hA']; exact zero_le
  have h := schedulerPrefix_window_le_drift hn F c hstepF hmono W
  have hF0 : F 0 (fun t => Fin.elim0 t) ≤ Φ C₀ := by
    simp only [F]
    split_ifs
    · rfl
    · exact zero_le
  refine le_trans ?_ (h.trans hF0)
  apply mul_le_mul_right
  refine (probNotHitBy_le_prefixMass_avoid P hn C₀ Goal W).trans (le_of_eq ?_)
  rw [schedulerPrefix_toOuterMeasure_eq_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [c, Set.mem_setOf_eq]
  split_ifs <;> simp

/-! ### Hitting probability from a growing potential -/

/-- On the support of the coupled trace, a run that avoids `Goal` has a false hit flag. -/
theorem schedulerTraceDist_support_flag_of_avoid (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ∀ (K : ℕ) (S : SchedulerTraceState Q X n K),
      S ∈ (schedulerTraceDist P hn C₀ Goal K).support →
        PathAvoids P C₀ Goal K S.2 → S.1.2 = false
  | 0, S, hS, hA => by
      classical
      rw [schedulerTraceDist, PMF.support_pure, Set.mem_singleton_iff] at hS
      subst hS
      have hA' : ¬ Goal C₀ := hA
      simpa using hA'
  | K + 1, S, hS, hA => by
      classical
      rw [schedulerTraceDist, PMF.mem_support_bind_iff] at hS
      obtain ⟨S', hS', hS⟩ := hS
      unfold schedulerTraceStepDist at hS
      rw [PMF.support_map] at hS
      obtain ⟨p, -, rfl⟩ := hS
      obtain ⟨hrun, -⟩ := schedulerTraceDist_support_run P hn C₀ Goal K S' hS'
      have hA' := (pathAvoids_snoc P C₀ Goal K S'.2 p).mp hA
      have ih := schedulerTraceDist_support_flag_of_avoid P hn C₀ Goal K S' hS' hA'.1
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨ih, ?_⟩
      rw [hrun]
      exact hA'.2

/-- **Prefix bound for the hit probability**: hitting `Goal` within `K` steps needs a prefix
whose run does not avoid `Goal`. -/
theorem probHitBy_le_prefixMass_not_avoid (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) (K : ℕ) :
    probHitBy P hn C₀ Goal K ≤
      (schedulerPrefixPMF n hn K).toOuterMeasure {σ | ¬ PathAvoids P C₀ Goal K σ} := by
  classical
  rw [probHitBy_eq_hitFlagDist_toOuterMeasure, ← schedulerTraceDist_map_hitFlag,
    ← schedulerTraceDist_map_prefix P hn C₀ Goal K, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_mono
  rintro S ⟨hS, hsupp⟩
  have hS' : S.1.2 = true := hS
  change ¬ PathAvoids P C₀ Goal K S.2
  intro hA
  have h := schedulerTraceDist_support_flag_of_avoid P hn C₀ Goal K S hsupp hA
  rw [h] at hS'
  exact Bool.false_ne_true hS'

open Classical in
/-- The potential `V` along the run of a prefix, stopped at the first visit to `Goal`. -/
noncomputable def stoppedPot (P : Protocol Q X Y) (C₀ : Config Q X n)
    (Goal : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞) :
    (K : ℕ) → SchedulerPrefix n K → ℝ≥0∞
  | 0, _ => V C₀
  | K + 1, σ => if PathAvoids P C₀ Goal K (Fin.init σ) then V (runPrefix P C₀ (K + 1) σ)
      else stoppedPot P C₀ Goal V K (Fin.init σ)

theorem stoppedPot_of_avoid (P : Protocol Q X Y) (C₀ : Config Q X n)
    (Goal : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞) :
    ∀ (K : ℕ) (σ : SchedulerPrefix n K), PathAvoids P C₀ Goal K σ →
      stoppedPot P C₀ Goal V K σ = V (runPrefix P C₀ K σ)
  | 0, _, _ => rfl
  | K + 1, σ, h => by
      classical
      have h1 : PathAvoids P C₀ Goal K (Fin.init σ) := h.1
      simp only [stoppedPot, if_pos h1]

theorem stoppedPot_snoc_of_not_avoid (P : Protocol Q X Y) (C₀ : Config Q X n)
    (Goal : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞) (K : ℕ)
    (σ : SchedulerPrefix n K) (p : Fin n × Fin n) (h : ¬ PathAvoids P C₀ Goal K σ) :
    stoppedPot P C₀ Goal V (K + 1) (Fin.snoc σ p) = stoppedPot P C₀ Goal V K σ := by
  classical
  simp only [stoppedPot, Fin.init_snoc, if_neg h]

theorem stoppedPot_snoc_of_avoid (P : Protocol Q X Y) (C₀ : Config Q X n)
    (Goal : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞) (K : ℕ)
    (σ : SchedulerPrefix n K) (p : Fin n × Fin n) (h : PathAvoids P C₀ Goal K σ) :
    stoppedPot P C₀ Goal V (K + 1) (Fin.snoc σ p) = V ((runPrefix P C₀ K σ).step P p.1 p.2) := by
  classical
  simp only [stoppedPot, Fin.init_snoc, if_pos h, runPrefix_snoc]

/-- **Hit bound from a growing potential** (exponential Markov inequality): if `V` grows by at
most `ρ ≥ 1` in mean per step outside `Goal`, `Inv` is kept by every step from `Inv \ Goal`,
and `V ≥ a` on `Inv ∩ Goal`, then `a · P[hit Goal within K] ≤ ρ ^ K V(C₀)`. -/
theorem probHitBy_le_potential_grow (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞)
    (ρ a : ℝ≥0∞) (hρ : 1 ≤ ρ) (h₀ : Inv C₀)
    (hInv : ∀ C, Inv C → ¬ Goal C → ∀ i j : Fin n, Inv (C.step P i j))
    (hstep : ∀ C, Inv C → ¬ Goal C →
      ∑ p : Fin n × Fin n, uniformPair n hn p * V (C.step P p.1 p.2) ≤ ρ * V C)
    (hlow : ∀ C, Inv C → Goal C → a ≤ V C) (K : ℕ) :
    a * probHitBy P hn C₀ Goal K ≤ ρ ^ K * V C₀ := by
  classical
  have hInv' : ∀ C, Inv C → ¬ Goal C → ∀ i j : Fin n,
      Inv (C.step P i j) ∨ Goal (C.step P i j) := fun C h1 h2 i j => Or.inl (hInv C h1 h2 i j)
  let F := stoppedPot P C₀ Goal V
  have hF : ∀ K (σ : SchedulerPrefix n K),
      ∑ p : Fin n × Fin n, uniformPair n hn p * F (K + 1) (Fin.snoc σ p) ≤ ρ * F K σ := by
    intro K σ
    by_cases hA : PathAvoids P C₀ Goal K σ
    · simp only [F, stoppedPot_snoc_of_avoid P C₀ Goal V K σ _ hA,
        stoppedPot_of_avoid P C₀ Goal V K σ hA]
      exact hstep _ (pathAvoids_inv P C₀ Goal Inv h₀ hInv' K σ hA)
        (pathAvoids_final P C₀ Goal K σ hA)
    · simp only [F, stoppedPot_snoc_of_not_avoid P C₀ Goal V K σ _ hA]
      rw [← Finset.sum_mul, uniformPair_sum_one hn, one_mul]
      exact le_mul_of_one_le_left zero_le hρ
  -- the stopped potential is at least `a` once `Goal` has been visited
  have hge : ∀ (K : ℕ) (σ : SchedulerPrefix n K), ¬ PathAvoids P C₀ Goal K σ → a ≤ F K σ := by
    intro K
    induction K with
    | zero =>
        intro σ h
        have hG : Goal C₀ := by
          by_contra hG
          exact h hG
        exact hlow C₀ h₀ hG
    | succ K ih =>
        intro σ h
        by_cases hA : PathAvoids P C₀ Goal K (Fin.init σ)
        · have hG : Goal (runPrefix P C₀ (K + 1) σ) := by
            by_contra hG
            exact h ⟨hA, hG⟩
          have hI : Inv (runPrefix P C₀ (K + 1) σ) := by
            rw [runPrefix_succ]
            exact hInv _ (pathAvoids_inv P C₀ Goal Inv h₀ hInv' K _ hA)
              (pathAvoids_final P C₀ Goal K _ hA) _ _
          change a ≤ stoppedPot P C₀ Goal V (K + 1) σ
          simp only [stoppedPot, if_pos hA]
          exact hlow _ hI hG
        · change a ≤ stoppedPot P C₀ Goal V (K + 1) σ
          simp only [stoppedPot, if_neg hA]
          exact ih _ hA
  have hE := schedulerPrefix_expect_le_pow hn F ρ hF K
  have hM := schedulerPrefix_markov hn K (F K) a
  refine (mul_le_mul_right (probHitBy_le_prefixMass_not_avoid P hn C₀ Goal K) a).trans ?_
  refine le_trans ?_ (hM.trans hE)
  apply mul_le_mul_right
  apply MeasureTheory.measure_mono
  intro σ hσ
  exact hge K σ hσ

/-! ### Sums over agents -/

/-- An agent sum changes only at the two interacting agents. -/
theorem sum_step_add (P : Protocol Q X Y) (C : Config Q X n) (u v : Fin n) (huv : u ≠ v)
    (f : Q × X → ℕ) :
    ∑ w, f ((C.step P u v) w) + (f (C u) + f (C v)) =
      ∑ w, f (C w) + (f ((C.step P u v) u) + f ((C.step P u v) v)) := by
  classical
  have key : ∀ D : Config Q X n, ∑ w, f (D w) =
      f (D u) + f (D v) + ∑ w ∈ (Finset.univ.erase u).erase v, f (D w) := by
    intro D
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩),
      add_assoc]
  have hrest : ∑ w ∈ (Finset.univ.erase u).erase v, f ((C.step P u v) w) =
      ∑ w ∈ (Finset.univ.erase u).erase v, f (C w) := by
    apply Finset.sum_congr rfl
    intro w hw
    have hwv := Finset.ne_of_mem_erase hw
    have hwu := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hw)
    simp only [Config.step, if_neg huv, if_neg hwu, if_neg hwv]
  rw [key (C.step P u v), key C, hrest]
  ring

end Probability

/-! ### Elementary numerics -/

theorem one_sub_pow_le_exp {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (K : ℕ) :
    (1 - x) ^ K ≤ Real.exp (-(x * K)) := by
  calc (1 - x) ^ K ≤ (Real.exp (-x)) ^ K := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (-x)
        linarith
    _ = Real.exp (-(x * K)) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem one_add_pow_le_exp {x : ℝ} (hx0 : 0 ≤ x) (K : ℕ) :
    (1 + x) ^ K ≤ Real.exp (x * K) := by
  calc (1 + x) ^ K ≤ (Real.exp x) ^ K := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp x
        linarith
    _ = Real.exp (x * K) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- `e^{-6} < 0.002479`. -/
theorem exp_neg_six_lt : Real.exp (-6) < 0.002479 := by
  have he := Real.exp_one_gt_d9
  have h6 : (2.7182818283 : ℝ) ^ 6 < Real.exp 6 := by
    rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  rw [Real.exp_neg]
  rw [inv_lt_comm₀ (Real.exp_pos 6) (by norm_num)]
  calc (0.002479 : ℝ)⁻¹ < 2.7182818283 ^ 6 := by norm_num
    _ < Real.exp 6 := h6

end Ripple.PopulationProtocol.SSEM
