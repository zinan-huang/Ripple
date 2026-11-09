/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Propagation of a reset outruns the decay of the resetcount (Burman et al. Lemma 3.2)

Paper phase `docs/audit/FIX2-BURMAN.md`, §B.1 (the potential form of P1 Theorem A). Along a
scheduler prefix we run three deterministic processes next to the protocol:

* `reachIter`: the two-way epidemic from the source `s`;
* `maxIter`: the pure max-minus-one process started at `R` on `s` (P1 Lemma 2: it is dominated by
  the effective resetcount of any protocol satisfying P1 Lemma 1, `effRc_runPrefix_ge`);
* `wtIter`: walk weights `N`, updated by `N(a), N(b) ← L (N(a) + N(b))`.

Invariant (`wt_invariant`): a reached agent `w` has `L ^ (R - x w) ≤ N w`. Hence a reached agent
whose max-process value is `0` forces `L ^ R ≤ Σ N`, and `E[Σ N] ≤ (1 + 4L/n) ^ K`
(`expect_wtSum_le`). Result (`propagation_not_full_le`): the probability that the configuration
after `K` interactions is not fully propagating is at most the probability that the epidemic has
not reached everyone plus `(1 + 4L/n) ^ K / L ^ R`.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.Propagation
import Ripple.PopulationProtocol.SSEM.Probability.PrefixRun

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- Update both endpoints of a pair to `v` (no change on a diagonal pair). -/
def pairUpd {α : Type*} (f : Fin n → α) (a b : Fin n) (v : α) : Fin n → α :=
  fun w => if a ≠ b ∧ (w = a ∨ w = b) then v else f w

/-- Iterate a pair-driven update along a scheduler prefix. -/
def prefixIter {α : Type*} (init : Fin n → α)
    (step : (Fin n → α) → Fin n × Fin n → Fin n → α) :
    (K : ℕ) → SchedulerPrefix n K → Fin n → α
  | 0, _ => init
  | K + 1, σ => step (prefixIter init step K (Fin.init σ)) (σ (Fin.last K))

theorem prefixIter_succ {α : Type*} (init : Fin n → α)
    (step : (Fin n → α) → Fin n × Fin n → Fin n → α) (K : ℕ) (σ : SchedulerPrefix n (K + 1)) :
    prefixIter init step (K + 1) σ = step (prefixIter init step K (Fin.init σ)) (σ (Fin.last K)) :=
  rfl

@[simp] theorem prefixIter_snoc {α : Type*} (init : Fin n → α)
    (step : (Fin n → α) → Fin n × Fin n → Fin n → α) (K : ℕ) (σ : SchedulerPrefix n K)
    (p : Fin n × Fin n) :
    prefixIter init step (K + 1) (Fin.snoc σ p) = step (prefixIter init step K σ) p := by
  rw [prefixIter_succ, Fin.init_snoc, Fin.snoc_last]

/-- Max-minus-one step. -/
def maxStep (x : Fin n → ℕ) (p : Fin n × Fin n) : Fin n → ℕ :=
  pairUpd x p.1 p.2 (max (x p.1 - 1) (x p.2 - 1))

/-- Epidemic step. -/
def reachStep (r : Fin n → Bool) (p : Fin n × Fin n) : Fin n → Bool :=
  pairUpd r p.1 p.2 (r p.1 || r p.2)

/-- Walk-weight step. -/
noncomputable def wtStep (L : ℝ≥0∞) (N : Fin n → ℝ≥0∞) (p : Fin n × Fin n) : Fin n → ℝ≥0∞ :=
  pairUpd N p.1 p.2 (L * (N p.1 + N p.2))

/-- The max-minus-one process from `R` at `s`. -/
def maxIter (R : ℕ) (s : Fin n) : (K : ℕ) → SchedulerPrefix n K → Fin n → ℕ :=
  prefixIter (fun w => if w = s then R else 0) maxStep

/-- The two-way epidemic from `s`. -/
def reachIter (s : Fin n) : (K : ℕ) → SchedulerPrefix n K → Fin n → Bool :=
  prefixIter (fun w => decide (w = s)) reachStep

/-- Walk weights from `s`. -/
noncomputable def wtIter (L : ℝ≥0∞) (s : Fin n) : (K : ℕ) → SchedulerPrefix n K → Fin n → ℝ≥0∞ :=
  prefixIter (fun w => if w = s then 1 else 0) (wtStep L)

theorem maxIter_le (R : ℕ) (s : Fin n) : ∀ K (σ : SchedulerPrefix n K) w, maxIter R s K σ w ≤ R
  | 0, _, w => by
      simp only [maxIter, prefixIter]
      split_ifs <;> omega
  | K + 1, σ, w => by
      simp only [maxIter, prefixIter_succ, maxStep, pairUpd]
      have h1 := maxIter_le R s K (Fin.init σ) (σ (Fin.last K)).1
      have h2 := maxIter_le R s K (Fin.init σ) (σ (Fin.last K)).2
      have h3 := maxIter_le R s K (Fin.init σ) w
      simp only [maxIter] at h1 h2 h3
      split_ifs <;> omega

/-- **Domination (P1 Lemma 2).** For a protocol whose transition satisfies P1 Lemma 1 with
reset value `R`, the effective resetcount dominates the max-minus-one process from a source
with effective resetcount at least `R`. -/
theorem effRc_runPrefix_ge {X Y : Type*} (P : Protocol (AgentState n) X Y) (R : ℕ)
    (hδ : ∀ (s₀ s₁ : AgentState n) (x₀ x₁ : X),
      RcOutcome (max (effRc s₀ - 1) (effRc s₁ - 1)) R
        (effRc (P.δ ((s₀, x₀), (s₁, x₁))).1) (effRc (P.δ ((s₀, x₀), (s₁, x₁))).2))
    (C₀ : Config (AgentState n) X n) (s : Fin n) (hs : R ≤ effRc (C₀ s).1) :
    ∀ K (σ : SchedulerPrefix n K) w, maxIter R s K σ w ≤ effRc (runPrefix P C₀ K σ w).1
  | 0, _, w => by
      simp only [maxIter, prefixIter, runPrefix_zero]
      split_ifs with h
      · rw [h]; exact hs
      · exact Nat.zero_le _
  | K + 1, σ, w => by
      have ih := effRc_runPrefix_ge P R hδ C₀ s hs K (Fin.init σ)
      have hle := maxIter_le R s K (Fin.init σ)
      simp only [maxIter] at ih hle
      simp only [maxIter, prefixIter_succ, maxStep, pairUpd, runPrefix_succ]
      generalize σ (Fin.last K) = p
      obtain ⟨a, b⟩ := p
      generalize prefixIter (fun w => if w = s then R else 0) maxStep K (Fin.init σ) = x at ih hle
      generalize runPrefix P C₀ K (Fin.init σ) = C at ih
      simp only
      by_cases hab : a = b
      · subst hab
        have hC : C.step P a a = C := by simp [Config.step]
        rw [hC, if_neg (fun h => h.1 rfl)]
        exact ih w
      · have hstep : ∀ v, (C.step P a b) v =
            if v = a then ((P.δ (C a, C b)).1, (C a).2)
            else if v = b then ((P.δ (C a, C b)).2, (C b).2) else C v := by
          intro v
          simp only [Config.step, hab, if_false]
        rw [hstep]
        have hO := hδ (C a).1 (C b).1 (C a).2 (C b).2
        have hm : max (x a - 1) (x b - 1) ≤ max (effRc (C a).1 - 1) (effRc (C b).1 - 1) :=
          max_le_max (Nat.sub_le_sub_right (ih a) 1) (Nat.sub_le_sub_right (ih b) 1)
        have hR : max (x a - 1) (x b - 1) ≤ R := by
          have := hle a; have := hle b; omega
        by_cases hwa : w = a
        · rw [if_pos ⟨hab, Or.inl hwa⟩, if_pos hwa]
          dsimp only
          rcases hO with ⟨h1, -⟩ | ⟨h1, -⟩
          · have h1' : effRc (P.δ (C a, C b)).1 = max (effRc (C a).1 - 1) (effRc (C b).1 - 1) := h1
            omega
          · have h1' : effRc (P.δ (C a, C b)).1 = R := h1
            omega
        · by_cases hwb : w = b
          · rw [if_pos ⟨hab, Or.inr hwb⟩, if_neg hwa, if_pos hwb]
            dsimp only
            rcases hO with ⟨-, h2⟩ | ⟨-, h2⟩
            · have h2' : effRc (P.δ (C a, C b)).2 = max (effRc (C a).1 - 1) (effRc (C b).1 - 1) :=
                h2
              omega
            · have h2' : effRc (P.δ (C a, C b)).2 = R := h2
              omega
          · rw [if_neg (by tauto), if_neg hwa, if_neg hwb]
            exact ih w

/-- **Walk-weight invariant** (§B.1 (D2)). -/
theorem wt_invariant (R : ℕ) (s : Fin n) (L : ℝ≥0∞) (hL : 1 ≤ L) :
    ∀ K (σ : SchedulerPrefix n K) w,
      (1 ≤ maxIter R s K σ w → reachIter s K σ w = true) ∧
        (reachIter s K σ w = true → L ^ (R - maxIter R s K σ w) ≤ wtIter L s K σ w)
  | 0, _, w => by
      simp only [maxIter, reachIter, wtIter, prefixIter]
      by_cases h : w = s
      · simp [h]
      · simp [h]
  | K + 1, σ, w => by
      have ih := wt_invariant R s L hL K (Fin.init σ)
      have hle := maxIter_le R s K (Fin.init σ)
      simp only [maxIter, reachIter, wtIter] at ih hle
      simp only [maxIter, reachIter, wtIter, prefixIter_succ, maxStep, reachStep, wtStep, pairUpd]
      generalize σ (Fin.last K) = p
      obtain ⟨a, b⟩ := p
      generalize prefixIter (fun w => if w = s then R else 0) maxStep K (Fin.init σ) = x at ih hle
      generalize prefixIter (fun w => decide (w = s)) reachStep K (Fin.init σ) = r at ih
      generalize prefixIter (fun w => if w = s then 1 else 0) (wtStep L) K (Fin.init σ) = N at ih
      simp only
      by_cases hc : a ≠ b ∧ (w = a ∨ w = b)
      · simp only [if_pos hc]
        constructor
        · intro h1
          have : 2 ≤ x a ∨ 2 ≤ x b := by omega
          rcases this with h | h
          · have := (ih a).1 (by omega); simp [this]
          · have := (ih b).1 (by omega); simp [this]
        · intro hr
          have hNab : N a + N b ≤ L * (N a + N b) := le_mul_of_one_le_left' hL
          have hmax : ∃ c, (c = a ∨ c = b) ∧ x c = max (x a) (x b) := by
            rcases le_total (x a) (x b) with h | h
            · exact ⟨b, Or.inr rfl, (max_eq_right h).symm⟩
            · exact ⟨a, Or.inl rfl, (max_eq_left h).symm⟩
          obtain ⟨c, hc', hxc⟩ := hmax
          have hNc : N c ≤ N a + N b := by
            rcases hc' with rfl | rfl
            · exact le_self_add
            · exact le_add_self
          by_cases hpos : 1 ≤ x c
          · have hw := (ih c).2 ((ih c).1 hpos)
            have hle_c := hle c
            have heq : R - max (x a - 1) (x b - 1) = (R - x c) + 1 := by omega
            rw [heq, pow_succ, mul_comm]
            exact mul_le_mul_left' (hw.trans hNc) L
          · have hz : max (x a - 1) (x b - 1) = 0 := by omega
            rw [hz, Nat.sub_zero]
            have hrab : r a = true ∨ r b = true := by simpa using hr
            have hx0 : x a = 0 ∧ x b = 0 := by omega
            rcases hrab with h | h
            · have := (ih a).2 h
              rw [hx0.1, Nat.sub_zero] at this
              exact this.trans (le_self_add.trans hNab)
            · have := (ih b).2 h
              rw [hx0.2, Nat.sub_zero] at this
              exact this.trans (le_add_self.trans hNab)
      · simp only [if_neg hc]
        exact ih w

theorem sum_pairUpd_le (N : Fin n → ℝ≥0∞) (a b : Fin n) (v : ℝ≥0∞) :
    ∑ w, pairUpd N a b v w ≤ ∑ w, N w + 2 * v := by
  classical
  unfold pairUpd
  calc ∑ w, (if a ≠ b ∧ (w = a ∨ w = b) then v else N w)
      ≤ ∑ w, (N w + ((if w = a then v else 0) + (if w = b then v else 0))) := by
        apply Finset.sum_le_sum
        intro w _
        by_cases hc : a ≠ b ∧ (w = a ∨ w = b)
        · rw [if_pos hc]
          rcases hc.2 with rfl | rfl
          · rw [if_pos rfl]; exact le_add_left le_self_add
          · rw [if_pos (rfl : w = w)]; exact le_add_left le_add_self
        · rw [if_neg hc]; exact le_self_add
    _ = ∑ w, N w + 2 * v := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
          Finset.sum_ite_eq']
        simp [two_mul]

theorem wtSum_step (hn : 2 ≤ n) (L : ℝ≥0∞) (N : Fin n → ℝ≥0∞) :
    ∑ p : Fin n × Fin n, uniformPair n hn p * ∑ w, wtStep L N p w ≤
      (1 + 4 * L * (n : ℝ≥0∞)⁻¹) * ∑ w, N w := by
  have hsum : ∑ p : Fin n × Fin n, uniformPair n hn p = 1 := by
    simpa [tsum_fintype] using (uniformPair n hn).tsum_coe
  calc ∑ p : Fin n × Fin n, uniformPair n hn p * ∑ w, wtStep L N p w
      ≤ ∑ p : Fin n × Fin n, uniformPair n hn p *
          (∑ w, N w + 2 * L * (N p.1 + N p.2)) := by
        apply Finset.sum_le_sum
        intro p _
        apply mul_le_mul_left'
        have := sum_pairUpd_le N p.1 p.2 (L * (N p.1 + N p.2))
        simpa [wtStep, mul_assoc] using this
    _ = (∑ p : Fin n × Fin n, uniformPair n hn p) * ∑ w, N w +
          2 * L * ∑ p : Fin n × Fin n, uniformPair n hn p * (N p.1 + N p.2) := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ = (1 + 4 * L * (n : ℝ≥0∞)⁻¹) * ∑ w, N w := by
        rw [hsum, uniformPair_sum_endpoints]
        ring

/-- **Expected walk weight** after `K` interactions. -/
theorem expect_wtSum_le (hn : 2 ≤ n) (L : ℝ≥0∞) (s : Fin n) (K : ℕ) :
    ∑ σ : SchedulerPrefix n K, schedulerPrefixPMF n hn K σ * ∑ w, wtIter L s K σ w ≤
      (1 + 4 * L * (n : ℝ≥0∞)⁻¹) ^ K := by
  have h := schedulerPrefix_expect_le_pow hn (fun K σ => ∑ w, wtIter L s K σ w)
    (1 + 4 * L * (n : ℝ≥0∞)⁻¹) (by
      intro K σ
      simp only [wtIter, prefixIter_snoc]
      exact wtSum_step hn L _) K
  have h0 : ∑ w : Fin n, wtIter L s 0 (fun t => Fin.elim0 t) w = 1 := by
    simp [wtIter, prefixIter]
  rw [h0, mul_one] at h
  exact h

/-- Fully propagating: every agent is Resetting with resetcount at least `1`. -/
def FullyPropagating {X : Type*} (C : Config (AgentState n) X n) : Prop :=
  ∀ w, 1 ≤ effRc (C w).1

/-- **Propagation (Burman et al. Lemma 3.2), potential form.** -/
theorem propagation_not_full_le {X Y : Type*} (P : Protocol (AgentState n) X Y) (R : ℕ)
    (hδ : ∀ (s₀ s₁ : AgentState n) (x₀ x₁ : X),
      RcOutcome (max (effRc s₀ - 1) (effRc s₁ - 1)) R
        (effRc (P.δ ((s₀, x₀), (s₁, x₁))).1) (effRc (P.δ ((s₀, x₀), (s₁, x₁))).2))
    (hn : 2 ≤ n) (C₀ : Config (AgentState n) X n) (s : Fin n) (hs : R ≤ effRc (C₀ s).1)
    (L : ℝ≥0∞) (hL : 1 ≤ L) (hLt : L ≠ ⊤) (K : ℕ) :
    probNotHitBy P hn C₀ FullyPropagating K ≤
      (schedulerPrefixPMF n hn K).toOuterMeasure {σ | ∃ w, reachIter s K σ w = false} +
        (1 + 4 * L * (n : ℝ≥0∞)⁻¹) ^ K / L ^ R := by
  classical
  refine (probNotHitBy_le_prefixMass P hn C₀ FullyPropagating K).trans ?_
  set B : Set (SchedulerPrefix n K) := {σ | L ^ R ≤ ∑ w, wtIter L s K σ w}
  have hsub : {σ | ¬ FullyPropagating (runPrefix P C₀ K σ)} ⊆
      {σ | ∃ w, reachIter s K σ w = false} ∪ B := by
    intro σ hσ
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, Bool.not_eq_false,
      not_le, B] at hcon
    apply hσ
    intro w
    refine le_trans ?_ (effRc_runPrefix_ge P R hδ C₀ s hs K σ w)
    by_contra h0
    have hx : maxIter R s K σ w = 0 := by omega
    have := (wt_invariant R s L hL K σ w).2 (hcon.1 w)
    rw [hx, Nat.sub_zero] at this
    exact absurd (this.trans (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ w)))
      (not_le.mpr hcon.2)
  refine (MeasureTheory.measure_mono hsub).trans ((MeasureTheory.measure_union_le _ _).trans ?_)
  refine add_le_add le_rfl ?_
  have hM := (schedulerPrefix_markov hn K (fun σ => ∑ w, wtIter L s K σ w) (L ^ R)).trans
    (expect_wtSum_le hn L s K)
  have hL0 : L ^ R ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hL))
  have hLT : L ^ R ≠ ⊤ := ENNReal.pow_ne_top hLt
  rw [ENNReal.le_div_iff_mul_le (Or.inl hL0) (Or.inl hLT), mul_comm]
  exact hM

end Ripple.PopulationProtocol.SSEM
