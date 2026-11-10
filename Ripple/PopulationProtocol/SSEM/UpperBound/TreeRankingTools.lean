/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stopped potentials on scheduler prefixes (tools for P3 Lemma 11)

Window bounds of P3 Lemma 11 (stage B34) split a "not hit" event into three parts: the run
avoids a stopping set `S` for the whole window, or the first configuration of the run in `S` is
of one of two "bad" kinds `T₁`, `T₂` (`pathAvoids_split`, `probNotHitBy_le_three`). Each part is
bounded by a potential stopped at `S`:

* `prefixMass_avoid_le_drift`: additive drift (`E[Φ(next)] + 1 ≤ Φ` before `S`) gives
  `W · P[S not hit within W] ≤ Φ(C₀)` (P2 Lemma 1.4 with Markov's inequality);
* `prefixMass_avoid_le_potential`: a multiplicative potential with `V ≥ 1` outside `S` gives
  `P[S not hit within K] ≤ ρ^K V(C₀)` (any `ρ`, also `ρ < 1`);
* `prefixMass_hitFirst_le`: a multiplicative potential with `V ≥ 1` on `T ⊆ S` gives
  `P[the first hit of S is in T] ≤ ρ^K V(C₀)` for `ρ ≥ 1` (exponential Markov for a stopped
  supermartingale, P2 Lemma 1.5 style).

All three only use the potential before the stopping time, so the potentials may be defined
arbitrarily (for example `0` or `1`) on configurations in `S`.
-/

import Ripple.PopulationProtocol.SSEM.Probability.PrefixTools

namespace Ripple.PopulationProtocol.SSEM
namespace Probability

open scoped BigOperators ENNReal

variable {Q X Y : Type*} {n : ℕ}

/-! ### The first hit of a stopping set -/

/-- The first configuration of the run of `σ` (times `0, …, K`) that lies in `S` lies in `T`.
(Used with `T ⊆ S`.) -/
def HitFirst (P : Protocol Q X Y) (C₀ : Config Q X n) (S T : Config Q X n → Prop) :
    (K : ℕ) → SchedulerPrefix n K → Prop
  | 0, _ => T C₀
  | K + 1, σ => HitFirst P C₀ S T K (Fin.init σ) ∨
      (PathAvoids P C₀ S K (Fin.init σ) ∧ T (runPrefix P C₀ (K + 1) σ))

theorem hitFirst_snoc (P : Protocol Q X Y) (C₀ : Config Q X n) (S T : Config Q X n → Prop)
    (K : ℕ) (σ : SchedulerPrefix n K) (p : Fin n × Fin n) :
    HitFirst P C₀ S T (K + 1) (Fin.snoc σ p) ↔
      HitFirst P C₀ S T K σ ∨
        (PathAvoids P C₀ S K σ ∧ T ((runPrefix P C₀ K σ).step P p.1 p.2)) := by
  simp only [HitFirst, Fin.init_snoc, runPrefix_snoc]

theorem hitFirst_not_avoids (P : Protocol Q X Y) (C₀ : Config Q X n)
    (S T : Config Q X n → Prop) (hTS : ∀ C, T C → S C) :
    ∀ (K : ℕ) (σ : SchedulerPrefix n K), HitFirst P C₀ S T K σ → ¬ PathAvoids P C₀ S K σ
  | 0, _, h => fun hA => hA (hTS _ h)
  | K + 1, σ, h => by
      rintro ⟨hA, hn⟩
      rcases h with h | ⟨_, hT⟩
      · exact hitFirst_not_avoids P C₀ S T hTS K _ h hA
      · exact hn (hTS _ hT)

/-- Avoiding `G` means: avoiding `S`, or the first hit of `S` is in `T₁` or in `T₂`, provided
`S ⊆ G ∪ T₁ ∪ T₂`. -/
theorem pathAvoids_split (P : Protocol Q X Y) (C₀ : Config Q X n)
    (G S T₁ T₂ : Config Q X n → Prop) (hS : ∀ C, S C → G C ∨ T₁ C ∨ T₂ C) :
    ∀ (K : ℕ) (σ : SchedulerPrefix n K), PathAvoids P C₀ G K σ →
      PathAvoids P C₀ S K σ ∨ HitFirst P C₀ S T₁ K σ ∨ HitFirst P C₀ S T₂ K σ
  | 0, _, h => by
      by_cases hs : S C₀
      · rcases hS _ hs with hg | h1 | h2
        · exact absurd hg h
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h2)
      · exact Or.inl hs
  | K + 1, σ, h => by
      obtain ⟨hK, hg⟩ := h
      rcases pathAvoids_split P C₀ G S T₁ T₂ hS K (Fin.init σ) hK with hA | h1 | h2
      · by_cases hs : S (runPrefix P C₀ (K + 1) σ)
        · rcases hS _ hs with hg' | h1 | h2
          · exact absurd hg' hg
          · exact Or.inr (Or.inl (Or.inr ⟨hA, h1⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨hA, h2⟩))
        · exact Or.inl ⟨hA, hs⟩
      · exact Or.inr (Or.inl (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inl h2))

/-- **Three-way split of the not-hit probability.** -/
theorem probNotHitBy_le_three (P : Protocol Q X Y) (hn : 2 ≤ n) (C₀ : Config Q X n)
    (G S T₁ T₂ : Config Q X n → Prop) (hS : ∀ C, S C → G C ∨ T₁ C ∨ T₂ C) (K : ℕ) :
    probNotHitBy P hn C₀ G K ≤
      (schedulerPrefixPMF n hn K).toOuterMeasure {σ | PathAvoids P C₀ S K σ} +
      (schedulerPrefixPMF n hn K).toOuterMeasure {σ | HitFirst P C₀ S T₁ K σ} +
      (schedulerPrefixPMF n hn K).toOuterMeasure {σ | HitFirst P C₀ S T₂ K σ} := by
  refine (probNotHitBy_le_prefixMass_avoid P hn C₀ G K).trans ?_
  have hsub : {σ | PathAvoids P C₀ G K σ} ⊆
      ({σ | PathAvoids P C₀ S K σ} ∪ {σ | HitFirst P C₀ S T₁ K σ}) ∪
        {σ | HitFirst P C₀ S T₂ K σ} := by
    intro σ hσ
    rcases pathAvoids_split P C₀ G S T₁ T₂ hS K σ hσ with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine (MeasureTheory.measure_union_le _ _).trans ?_
  exact add_le_add (MeasureTheory.measure_union_le _ _) le_rfl

/-! ### Stopped potentials -/

/-- **Stopped multiplicative potential, avoidance form.** If `E[V(next)] ≤ ρ V(C)` and
`1 ≤ V(C)` on invariant configurations outside `S`, then `P[S not hit within K] ≤ ρ^K V(C₀)`. -/
theorem prefixMass_avoid_le_potential (P : Protocol Q X Y) (hn : 2 ≤ n) (C₀ : Config Q X n)
    (S Inv : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞) (ρ : ℝ≥0∞) (h₀ : Inv C₀)
    (hInv : ∀ C, Inv C → ∀ i j : Fin n, Inv (C.step P i j))
    (hstep : ∀ C, Inv C → ¬ S C →
      ∑ p : Fin n × Fin n, uniformPair n hn p * V (C.step P p.1 p.2) ≤ ρ * V C)
    (hlow : ∀ C, Inv C → ¬ S C → 1 ≤ V C) (K : ℕ) :
    (schedulerPrefixPMF n hn K).toOuterMeasure {σ | PathAvoids P C₀ S K σ} ≤ ρ ^ K * V C₀ := by
  classical
  let F : ∀ K, SchedulerPrefix n K → ℝ≥0∞ := fun K σ =>
    if PathAvoids P C₀ S K σ then V (runPrefix P C₀ K σ) else 0
  have hE := schedulerPrefix_expect_le_pow hn F ρ (by
    intro K σ
    by_cases hA : PathAvoids P C₀ S K σ
    · have hF : F K σ = V (runPrefix P C₀ K σ) := if_pos hA
      rw [hF]
      refine le_trans ?_ (hstep _ (runPrefix_inv P C₀ Inv h₀ hInv K σ)
        (pathAvoids_final P C₀ S K σ hA))
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_left'
      simp only [F]
      split_ifs
      · rw [runPrefix_snoc]
      · exact zero_le
    · have hA' : ∀ p, ¬ PathAvoids P C₀ S (K + 1) (Fin.snoc σ p) := fun p h =>
        hA ((pathAvoids_snoc P C₀ S K σ p).mp h).1
      simp [F, hA']) K
  have hF0 : F 0 (fun t => Fin.elim0 t) ≤ V C₀ := by
    simp only [F]
    split_ifs
    · rfl
    · exact zero_le
  have hM := schedulerPrefix_markov hn K (F K) 1
  rw [one_mul] at hM
  refine le_trans ?_ (hM.trans (hE.trans (mul_le_mul_left' hF0 _)))
  apply MeasureTheory.measure_mono
  intro σ hσ
  show 1 ≤ F K σ
  simp only [F, if_pos (show PathAvoids P C₀ S K σ from hσ)]
  exact hlow _ (runPrefix_inv P C₀ Inv h₀ hInv K σ) (pathAvoids_final P C₀ S K σ hσ)

/-- **Stopped multiplicative potential, first-hit form.** Let `T ⊆ S`, `ρ ≥ 1`. If
`E[V(next)] ≤ ρ V(C)` on invariant configurations outside `S` and `1 ≤ V` on invariant
configurations in `T`, then `P[the first hit of S within K is in T] ≤ ρ^K V(C₀)`. -/
theorem prefixMass_hitFirst_le (P : Protocol Q X Y) (hn : 2 ≤ n) (C₀ : Config Q X n)
    (S T Inv : Config Q X n → Prop) (V : Config Q X n → ℝ≥0∞) (ρ : ℝ≥0∞) (hρ : 1 ≤ ρ)
    (hTS : ∀ C, T C → S C) (h₀ : Inv C₀)
    (hInv : ∀ C, Inv C → ∀ i j : Fin n, Inv (C.step P i j))
    (hstep : ∀ C, Inv C → ¬ S C →
      ∑ p : Fin n × Fin n, uniformPair n hn p * V (C.step P p.1 p.2) ≤ ρ * V C)
    (hlow : ∀ C, Inv C → T C → 1 ≤ V C) (K : ℕ) :
    (schedulerPrefixPMF n hn K).toOuterMeasure {σ | HitFirst P C₀ S T K σ} ≤
      ρ ^ K * V C₀ := by
  classical
  let F : ∀ K, SchedulerPrefix n K → ℝ≥0∞ := fun K σ =>
    if PathAvoids P C₀ S K σ then V (runPrefix P C₀ K σ)
    else if HitFirst P C₀ S T K σ then 1 else 0
  have hE := schedulerPrefix_expect_le_pow hn F ρ (by
    intro K σ
    by_cases hA : PathAvoids P C₀ S K σ
    · have hF : F K σ = V (runPrefix P C₀ K σ) := if_pos hA
      rw [hF]
      have hInvK := runPrefix_inv P C₀ Inv h₀ hInv K σ
      refine le_trans ?_ (hstep _ hInvK (pathAvoids_final P C₀ S K σ hA))
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_left'
      have hHK : ¬ HitFirst P C₀ S T K σ := fun h =>
        hitFirst_not_avoids P C₀ S T hTS K σ h hA
      simp only [F]
      split_ifs with h1 h2
      · rw [runPrefix_snoc]
      · rcases (hitFirst_snoc P C₀ S T K σ p).mp h2 with h | ⟨-, hT⟩
        · exact absurd h hHK
        · exact hlow _ (hInv _ hInvK _ _) hT
      · exact zero_le
    · have hA' : ∀ p, ¬ PathAvoids P C₀ S (K + 1) (Fin.snoc σ p) := fun p h =>
        hA ((pathAvoids_snoc P C₀ S K σ p).mp h).1
      have hH : ∀ p, HitFirst P C₀ S T (K + 1) (Fin.snoc σ p) ↔ HitFirst P C₀ S T K σ := by
        intro p
        rw [hitFirst_snoc]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact h
          · exact absurd h hA
        · exact Or.inl
      have hF : ∀ p, F (K + 1) (Fin.snoc σ p) = F K σ := by
        intro p
        simp only [F, if_neg (hA' p), if_neg hA, hH p]
      simp only [hF]
      rw [← Finset.sum_mul, uniformPair_sum_one hn, one_mul]
      calc F K σ = 1 * F K σ := (one_mul _).symm
        _ ≤ ρ * F K σ := mul_le_mul_right' hρ _) K
  have hF0 : F 0 (fun t => Fin.elim0 t) ≤ V C₀ := by
    simp only [F]
    split_ifs with h1 h2
    · rfl
    · exact hlow _ h₀ h2
    · exact zero_le
  have hM := schedulerPrefix_markov hn K (F K) 1
  rw [one_mul] at hM
  refine le_trans ?_ (hM.trans (hE.trans (mul_le_mul_left' hF0 _)))
  apply MeasureTheory.measure_mono
  intro σ hσ
  show 1 ≤ F K σ
  have hσ' : HitFirst P C₀ S T K σ := hσ
  simp only [F, if_neg (hitFirst_not_avoids P C₀ S T hTS K σ hσ'), if_pos hσ', le_refl]

/-- **Additive drift, avoidance form**: `W · P[S not hit within W] ≤ Φ(C₀)` when
`E[Φ(next)] + 1 ≤ Φ(C)` on invariant configurations outside `S`. -/
theorem prefixMass_avoid_le_drift (P : Protocol Q X Y) (hn : 2 ≤ n) (C₀ : Config Q X n)
    (S Inv : Config Q X n → Prop) (Φ : Config Q X n → ℝ≥0∞) (h₀ : Inv C₀)
    (hInv : ∀ C, Inv C → ∀ i j : Fin n, Inv (C.step P i j))
    (hstep : ∀ C, Inv C → ¬ S C →
      ∑ p : Fin n × Fin n, uniformPair n hn p * Φ (C.step P p.1 p.2) + 1 ≤ Φ C) (W : ℕ) :
    (W : ℝ≥0∞) * (schedulerPrefixPMF n hn W).toOuterMeasure {σ | PathAvoids P C₀ S W σ} ≤
      Φ C₀ := by
  classical
  let c : ∀ K, SchedulerPrefix n K → ℝ≥0∞ := fun K σ =>
    if PathAvoids P C₀ S K σ then 1 else 0
  let F : ∀ K, SchedulerPrefix n K → ℝ≥0∞ := fun K σ =>
    if PathAvoids P C₀ S K σ then Φ (runPrefix P C₀ K σ) else 0
  have hstepF : ∀ K (σ : SchedulerPrefix n K),
      ∑ p : Fin n × Fin n, uniformPair n hn p * F (K + 1) (Fin.snoc σ p) + c K σ ≤ F K σ := by
    intro K σ
    by_cases hA : PathAvoids P C₀ S K σ
    · have hG := pathAvoids_final P C₀ S K σ hA
      simp only [F, c, if_pos hA]
      refine le_trans ?_ (hstep _ (runPrefix_inv P C₀ Inv h₀ hInv K σ) hG)
      refine add_le_add ?_ le_rfl
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_left'
      by_cases hA' : PathAvoids P C₀ S (K + 1) (Fin.snoc σ p)
      · rw [if_pos hA', runPrefix_snoc]
      · rw [if_neg hA']; exact zero_le
    · have hA' : ∀ p, ¬ PathAvoids P C₀ S (K + 1) (Fin.snoc σ p) := fun p h =>
        hA ((pathAvoids_snoc P C₀ S K σ p).mp h).1
      simp [F, c, hA, hA']
  have hmono : ∀ K (σ : SchedulerPrefix n K) p, c (K + 1) (Fin.snoc σ p) ≤ c K σ := by
    intro K σ p
    by_cases hA' : PathAvoids P C₀ S (K + 1) (Fin.snoc σ p)
    · have hA := ((pathAvoids_snoc P C₀ S K σ p).mp hA').1
      simp [c, hA, hA']
    · simp only [c, if_neg hA']; exact zero_le
  have h := schedulerPrefix_window_le_drift hn F c hstepF hmono W
  have hF0 : F 0 (fun t => Fin.elim0 t) ≤ Φ C₀ := by
    simp only [F]
    split_ifs
    · rfl
    · exact zero_le
  refine le_trans (le_of_eq ?_) (h.trans hF0)
  congr 1
  rw [schedulerPrefix_toOuterMeasure_eq_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [c, Set.mem_setOf_eq]
  split_ifs <;> simp

end Probability
end Ripple.PopulationProtocol.SSEM
