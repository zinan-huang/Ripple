/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tools for window bounds on scheduler prefixes

* `PathAvoids P C₀ Goal K σ`: no configuration of the run of `σ` (times `0, …, K`) is in `Goal`;
  `probNotHitBy_le_prefixMass_avoid` bounds the not-hit probability by the mass of these
  prefixes, so whole-path arguments ("until `Goal` is hit, `Inv` holds") become deterministic.
* `runPrefix_inv`: an invariant of the protocol holds along every run.
* `schedulerPrefix_expect_run_le_pow`, `probNotHitBy_le_potential`: a multiplicative potential
  (supermartingale) on configurations gives an exponential tail (P2 Lemma 1.5 style).
* `schedulerPrefix_additive_drift`, `schedulerPrefix_window_le_drift`: additive drift. If
  `E[F_{K+1}] + c_K ≤ F_K` one step at a time, then `Σ_{k<K} E[c_k] ≤ F_0`; with `c` the
  indicator of "not done" and "done" closed along runs, `W · P[not done at W] ≤ F_0` (P2 Lemma
  1.4, in potential form).
-/

import Ripple.PopulationProtocol.SSEM.Probability.PrefixRun

namespace Ripple.PopulationProtocol.SSEM
namespace Probability

open scoped BigOperators ENNReal

variable {Q X Y : Type*} {n : ℕ}

/-! ### Avoiding a goal along the whole run -/

/-- No configuration of the run of `σ` at times `0, …, K` is in `Goal`. -/
def PathAvoids (P : Protocol Q X Y) (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    (K : ℕ) → SchedulerPrefix n K → Prop
  | 0, _ => ¬ Goal C₀
  | K + 1, σ => PathAvoids P C₀ Goal K (Fin.init σ) ∧ ¬ Goal (runPrefix P C₀ (K + 1) σ)

theorem pathAvoids_snoc (P : Protocol Q X Y) (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K : ℕ) (σ : SchedulerPrefix n K) (p : Fin n × Fin n) :
    PathAvoids P C₀ Goal (K + 1) (Fin.snoc σ p) ↔
      PathAvoids P C₀ Goal K σ ∧ ¬ Goal ((runPrefix P C₀ K σ).step P p.1 p.2) := by
  simp only [PathAvoids, Fin.init_snoc, runPrefix_snoc]

theorem pathAvoids_final (P : Protocol Q X Y) (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ∀ (K : ℕ) (σ : SchedulerPrefix n K), PathAvoids P C₀ Goal K σ →
      ¬ Goal (runPrefix P C₀ K σ)
  | 0, _, h => h
  | _ + 1, _, h => h.2

theorem schedulerTraceDist_support_avoid (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ∀ (K : ℕ) (S : SchedulerTraceState Q X n K),
      S ∈ (schedulerTraceDist P hn C₀ Goal K).support →
        S.1.2 = false → PathAvoids P C₀ Goal K S.2
  | 0, S, hS, hf => by
      classical
      rw [schedulerTraceDist, PMF.support_pure, Set.mem_singleton_iff] at hS
      subst hS
      simpa [PathAvoids] using hf
  | K + 1, S, hS, hf => by
      classical
      have hS0 := hS
      rw [schedulerTraceDist, PMF.mem_support_bind_iff] at hS
      obtain ⟨S', hS', hS⟩ := hS
      unfold schedulerTraceStepDist at hS
      rw [PMF.support_map] at hS
      obtain ⟨p, -, rfl⟩ := hS
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
      have ih := schedulerTraceDist_support_avoid P hn C₀ Goal K S' hS' hf.1
      obtain ⟨hrun, -⟩ := schedulerTraceDist_support_run P hn C₀ Goal K S' hS'
      refine (pathAvoids_snoc P C₀ Goal K S'.2 p).mpr ⟨ih, ?_⟩
      rw [← hrun]
      exact hf.2

/-- **Prefix bound for the not-hit probability, whole path.** -/
theorem probNotHitBy_le_prefixMass_avoid (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) (K : ℕ) :
    probNotHitBy P hn C₀ Goal K ≤
      (schedulerPrefixPMF n hn K).toOuterMeasure {σ | PathAvoids P C₀ Goal K σ} := by
  classical
  rw [probNotHitBy_eq_hitFlagDist_toOuterMeasure, ← schedulerTraceDist_map_hitFlag,
    ← schedulerTraceDist_map_prefix P hn C₀ Goal K, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply]
  apply PMF.toOuterMeasure_mono
  rintro S ⟨hS, hsupp⟩
  exact schedulerTraceDist_support_avoid P hn C₀ Goal K S hsupp hS

/-! ### Invariants along runs -/

theorem runPrefix_inv (P : Protocol Q X Y) (C₀ : Config Q X n) (Inv : Config Q X n → Prop)
    (h₀ : Inv C₀) (hstep : ∀ C, Inv C → ∀ i j : Fin n, Inv (C.step P i j)) :
    ∀ (K : ℕ) (σ : SchedulerPrefix n K), Inv (runPrefix P C₀ K σ)
  | 0, _ => h₀
  | K + 1, σ => by
      rw [runPrefix_succ]
      exact hstep _ (runPrefix_inv P C₀ Inv h₀ hstep K _) _ _

/-! ### Multiplicative potentials -/

/-- **Potential bound along runs.** -/
theorem schedulerPrefix_expect_run_le_pow (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Inv : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞) (ρ : ℝ≥0∞)
    (h₀ : Inv C₀) (hInv : ∀ C, Inv C → ∀ i j : Fin n, Inv (C.step P i j))
    (hstep : ∀ C, Inv C → ∑ p : Fin n × Fin n, uniformPair n hn p * V (C.step P p.1 p.2) ≤
      ρ * V C) (K : ℕ) :
    ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ * V (runPrefix P C₀ K σ) ≤
      ρ ^ K * V C₀ := by
  have h := schedulerPrefix_expect_le_pow hn (fun K σ => V (runPrefix P C₀ K σ)) ρ (by
    intro K σ
    simp only [runPrefix_snoc]
    exact hstep _ (runPrefix_inv P C₀ Inv h₀ hInv K σ)) K
  simpa using h

/-- **Not-hit bound from a potential**: if `a ≤ V C` on every invariant configuration outside
`Goal`, then `a · P[Goal not hit within K] ≤ ρ ^ K · V C₀`. -/
theorem probNotHitBy_le_potential (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞)
    (ρ a : ℝ≥0∞) (h₀ : Inv C₀) (hInv : ∀ C, Inv C → ∀ i j : Fin n, Inv (C.step P i j))
    (hstep : ∀ C, Inv C → ∑ p : Fin n × Fin n, uniformPair n hn p * V (C.step P p.1 p.2) ≤
      ρ * V C)
    (hlow : ∀ C, Inv C → ¬ Goal C → a ≤ V C) (K : ℕ) :
    a * probNotHitBy P hn C₀ Goal K ≤ ρ ^ K * V C₀ := by
  refine (mul_le_mul_left' (probNotHitBy_le_prefixMass P hn C₀ Goal K) a).trans ?_
  refine le_trans ?_ ((schedulerPrefix_markov hn K (fun σ => V (runPrefix P C₀ K σ)) a).trans
    (schedulerPrefix_expect_run_le_pow P hn C₀ Inv V ρ h₀ hInv hstep K))
  apply mul_le_mul_left'
  apply PMF.toOuterMeasure_mono
  intro σ hσ
  exact hlow _ (runPrefix_inv P C₀ Inv h₀ hInv K σ) hσ.1

/-! ### Additive drift -/

theorem uniformPair_sum_one (hn : 2 ≤ n) : ∑ p : Fin n × Fin n, uniformPair n hn p = 1 := by
  simpa [tsum_fintype] using (uniformPair n hn).tsum_coe

/-- **Additive drift on prefixes.** -/
theorem schedulerPrefix_additive_drift (hn : 2 ≤ n) (F c : ∀ K, SchedulerPrefix n K → ℝ≥0∞)
    (hstep : ∀ K (σ : SchedulerPrefix n K),
      ∑ p : Fin n × Fin n, uniformPair n hn p * F (K + 1) (Fin.snoc σ p) + c K σ ≤ F K σ) :
    ∀ K, ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ * F K σ +
        ∑ k ∈ Finset.range K, ∑ σ : SchedulerPrefix n k, schedulerPrefixPMF n hn k σ * c k σ ≤
      F 0 (fun t => Fin.elim0 t)
  | 0 => by
      rw [Finset.sum_range_zero, add_zero, Fintype.sum_unique, schedulerPrefixPMF_apply,
        schedulerPrefixWeight, Fin.prod_univ_zero, one_mul]
      rw [Subsingleton.elim (default : SchedulerPrefix n 0) (fun t => Fin.elim0 t)]
  | K + 1 => by
      refine le_trans ?_ (schedulerPrefix_additive_drift hn F c hstep K)
      rw [schedulerPrefix_sum_succ, Finset.sum_range_succ, ← add_assoc, add_right_comm]
      refine add_le_add ?_ le_rfl
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro σ _
      rw [← mul_add]
      exact mul_le_mul_left' (hstep K σ) _

/-- The expectation of a quantity that does not increase along prefixes does not increase. -/
theorem schedulerPrefix_expect_succ_le (hn : 2 ≤ n) (c : ∀ K, SchedulerPrefix n K → ℝ≥0∞)
    (hmono : ∀ K (σ : SchedulerPrefix n K) p, c (K + 1) (Fin.snoc σ p) ≤ c K σ) (K : ℕ) :
    ∑ τ : SchedulerPrefix n (K + 1), schedulerPrefixPMF n hn (K + 1) τ * c (K + 1) τ ≤
      ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ * c K σ := by
  rw [schedulerPrefix_sum_succ]
  apply Finset.sum_le_sum
  intro σ _
  apply mul_le_mul_left'
  calc ∑ p : Fin n × Fin n, uniformPair n hn p * c (K + 1) (Fin.snoc σ p)
      ≤ ∑ p : Fin n × Fin n, uniformPair n hn p * c K σ :=
        Finset.sum_le_sum fun p _ => mul_le_mul_left' (hmono K σ p) _
    _ = c K σ := by rw [← Finset.sum_mul, uniformPair_sum_one hn, one_mul]

theorem schedulerPrefix_expect_le_of_le (hn : 2 ≤ n) (c : ∀ K, SchedulerPrefix n K → ℝ≥0∞)
    (hmono : ∀ K (σ : SchedulerPrefix n K) p, c (K + 1) (Fin.snoc σ p) ≤ c K σ) {k K : ℕ}
    (hk : k ≤ K) :
    ∑ τ : SchedulerPrefix n K, schedulerPrefixPMF n hn K τ * c K τ ≤
      ∑ σ : SchedulerPrefix n k, schedulerPrefixPMF n hn k σ * c k σ := by
  induction K, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ K _ ih => exact (schedulerPrefix_expect_succ_le hn c hmono K).trans ih

/-- **Window bound from additive drift**: if `c` does not increase along prefixes, then
`W · E[c_W] ≤ F_0`. With `c` the indicator of "not done", this is `W · P[not done at W] ≤ F_0`
(Markov's inequality for the hitting time, P2 Lemma 1.4). -/
theorem schedulerPrefix_window_le_drift (hn : 2 ≤ n) (F c : ∀ K, SchedulerPrefix n K → ℝ≥0∞)
    (hstep : ∀ K (σ : SchedulerPrefix n K),
      ∑ p : Fin n × Fin n, uniformPair n hn p * F (K + 1) (Fin.snoc σ p) + c K σ ≤ F K σ)
    (hmono : ∀ K (σ : SchedulerPrefix n K) p, c (K + 1) (Fin.snoc σ p) ≤ c K σ) (W : ℕ) :
    (W : ℝ≥0∞) * ∑ τ : SchedulerPrefix n W, schedulerPrefixPMF n hn W τ * c W τ ≤
      F 0 (fun t => Fin.elim0 t) := by
  have hd := schedulerPrefix_additive_drift hn F c hstep W
  refine le_trans ?_ (le_trans le_add_self hd)
  calc (W : ℝ≥0∞) * ∑ τ : SchedulerPrefix n W, schedulerPrefixPMF n hn W τ * c W τ
      = ∑ _k ∈ Finset.range W,
          ∑ τ : SchedulerPrefix n W, schedulerPrefixPMF n hn W τ * c W τ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.range W,
          ∑ σ : SchedulerPrefix n k, schedulerPrefixPMF n hn k σ * c k σ :=
        Finset.sum_le_sum fun k hk =>
          schedulerPrefix_expect_le_of_le hn c hmono (Finset.mem_range.mp hk).le

/-- **Hitting window from additive drift along runs**: let `Φ ≥ 0` be a potential on
configurations with `E[Φ(next)] + 1 ≤ Φ(C)` from every invariant configuration outside `Goal`.
Then `W · P[Goal not hit within W] ≤ Φ(C₀)` (the drift is used only before the first hit). -/
theorem probNotHitBy_window_le_drift (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal Inv : Config Q X n → Prop) (Φ : Config Q X n → ℝ≥0∞)
    (h₀ : Inv C₀) (hInv : ∀ C, Inv C → ∀ i j : Fin n, Inv (C.step P i j))
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
      refine le_trans ?_ (hstep _ (runPrefix_inv P C₀ Inv h₀ hInv K σ) hG)
      refine add_le_add ?_ le_rfl
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_left'
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
  apply mul_le_mul_left'
  refine (probNotHitBy_le_prefixMass_avoid P hn C₀ Goal W).trans (le_of_eq ?_)
  rw [schedulerPrefix_toOuterMeasure_eq_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [c, Set.mem_setOf_eq]
  split_ifs <;> simp

end Probability
end Ripple.PopulationProtocol.SSEM
