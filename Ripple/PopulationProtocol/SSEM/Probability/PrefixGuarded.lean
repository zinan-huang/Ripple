/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Additive drift on a guarded set of prefixes

`probNotHitBy_window_le_drift_guarded`: the additive-drift window bound of `PrefixTools` when the
drift is only known on a prefix-closed "good" set of scheduler prefixes `G` (for example: every
agent has had fewer than `D` interactions, so that a deterministic description of the run is
available). The bad prefixes are paid for separately:
`W · P[Goal not hit within W] ≤ Φ(C₀) + W · P[¬ G at W]`.
-/

import Ripple.PopulationProtocol.SSEM.Probability.PrefixTools

namespace Ripple.PopulationProtocol.SSEM
namespace Probability

open scoped BigOperators ENNReal

variable {Q X Y : Type*} {n : ℕ}

/-- **Guarded additive drift.** -/
theorem probNotHitBy_window_le_drift_guarded (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) (Φ : Config Q X n → ℝ≥0∞)
    (G : ∀ K, SchedulerPrefix n K → Prop)
    (hG : ∀ K (σ : SchedulerPrefix n K) p, G (K + 1) (Fin.snoc σ p) → G K σ)
    (hstep : ∀ K (σ : SchedulerPrefix n K), G K σ → PathAvoids P C₀ Goal K σ →
      ∑ p : Fin n × Fin n, uniformPair n hn p *
          Φ ((runPrefix P C₀ K σ).step P p.1 p.2) + 1 ≤ Φ (runPrefix P C₀ K σ))
    (W : ℕ) :
    (W : ℝ≥0∞) * probNotHitBy P hn C₀ Goal W ≤
      Φ C₀ + (W : ℝ≥0∞) * (schedulerPrefixPMF n hn W).toOuterMeasure {σ | ¬ G W σ} := by
  classical
  let A : ∀ K, SchedulerPrefix n K → Prop := fun K σ => G K σ ∧ PathAvoids P C₀ Goal K σ
  have hA : ∀ K (σ : SchedulerPrefix n K) p, A (K + 1) (Fin.snoc σ p) → A K σ := fun K σ p h =>
    ⟨hG K σ p h.1, ((pathAvoids_snoc P C₀ Goal K σ p).mp h.2).1⟩
  let c : ∀ K, SchedulerPrefix n K → ℝ≥0∞ := fun K σ => if A K σ then 1 else 0
  let F : ∀ K, SchedulerPrefix n K → ℝ≥0∞ := fun K σ =>
    if A K σ then Φ (runPrefix P C₀ K σ) else 0
  have hstepF : ∀ K (σ : SchedulerPrefix n K),
      ∑ p : Fin n × Fin n, uniformPair n hn p * F (K + 1) (Fin.snoc σ p) + c K σ ≤ F K σ := by
    intro K σ
    by_cases hAσ : A K σ
    · simp only [F, c, if_pos hAσ]
      refine le_trans ?_ (hstep K σ hAσ.1 hAσ.2)
      refine add_le_add ?_ le_rfl
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_left'
      split_ifs
      · rw [runPrefix_snoc]
      · exact zero_le
    · have hA' : ∀ p, ¬ A (K + 1) (Fin.snoc σ p) := fun p h => hAσ (hA K σ p h)
      simp [F, c, hAσ, hA']
  have hmono : ∀ K (σ : SchedulerPrefix n K) p, c (K + 1) (Fin.snoc σ p) ≤ c K σ := by
    intro K σ p
    by_cases hA' : A (K + 1) (Fin.snoc σ p)
    · simp [c, hA', hA K σ p hA']
    · simp only [c, if_neg hA']; exact zero_le
  have h := schedulerPrefix_window_le_drift hn F c hstepF hmono W
  have hF0 : F 0 (fun t => Fin.elim0 t) ≤ Φ C₀ := by
    simp only [F]
    split_ifs
    · rfl
    · exact zero_le
  -- split the not-hit event into `A` and `¬ G`
  have hsplit : probNotHitBy P hn C₀ Goal W ≤
      (∑ τ : SchedulerPrefix n W, schedulerPrefixPMF n hn W τ * c W τ) +
        (schedulerPrefixPMF n hn W).toOuterMeasure {σ | ¬ G W σ} := by
    refine (probNotHitBy_le_prefixMass_avoid P hn C₀ Goal W).trans ?_
    have hsub : {σ : SchedulerPrefix n W | PathAvoids P C₀ Goal W σ} ⊆
        {σ | A W σ} ∪ {σ | ¬ G W σ} := by
      intro σ hσ
      by_cases hg : G W σ
      · exact Or.inl ⟨hg, hσ⟩
      · exact Or.inr hg
    refine (MeasureTheory.measure_mono hsub).trans
      ((MeasureTheory.measure_union_le _ _).trans (add_le_add (le_of_eq ?_) le_rfl))
    rw [schedulerPrefix_toOuterMeasure_eq_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [c, Set.mem_setOf_eq]
    split_ifs <;> simp
  calc (W : ℝ≥0∞) * probNotHitBy P hn C₀ Goal W
      ≤ (W : ℝ≥0∞) * ((∑ τ : SchedulerPrefix n W, schedulerPrefixPMF n hn W τ * c W τ) +
          (schedulerPrefixPMF n hn W).toOuterMeasure {σ | ¬ G W σ}) :=
        mul_le_mul_left' hsplit _
    _ = (W : ℝ≥0∞) * (∑ τ : SchedulerPrefix n W, schedulerPrefixPMF n hn W τ * c W τ) +
          (W : ℝ≥0∞) * (schedulerPrefixPMF n hn W).toOuterMeasure {σ | ¬ G W σ} := mul_add _ _ _
    _ ≤ Φ C₀ + (W : ℝ≥0∞) * (schedulerPrefixPMF n hn W).toOuterMeasure {σ | ¬ G W σ} :=
        add_le_add (h.trans hF0) le_rfl

end Probability
end Ripple.PopulationProtocol.SSEM
