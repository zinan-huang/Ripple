/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform Random Scheduler for ExactMajority Protocols

This file gives the generic population-protocol scheduler used by the
ExactMajority development.  It samples an ordered pair of distinct agents
uniformly and then applies the deterministic chosen-pair update from
`Basic.PopulationProtocol`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Basic.PopulationProtocol
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace ExactMajority

open scoped BigOperators

namespace Config

variable {Λ : Type*}

/-- The total number of ordered pairs of distinct agents in `c`. -/
def totalPairs (c : Config Λ) : ℕ :=
  c.card * (c.card - 1)

/-- `totalPairs c > 0` when `c` has at least two agents. -/
theorem totalPairs_pos {c : Config Λ} (hc : 2 ≤ c.card) : 0 < c.totalPairs := by
  unfold totalPairs
  exact Nat.mul_pos (by omega : 0 < c.card) (by omega : 0 < c.card - 1)

theorem totalPairs_ne_zero_ennreal {c : Config Λ} (hc : 2 ≤ c.card) :
    (c.totalPairs : ENNReal) ≠ 0 := by
  exact_mod_cast (totalPairs_pos hc).ne'

theorem totalPairs_ne_top (c : Config Λ) : (c.totalPairs : ENNReal) ≠ ⊤ :=
  ENNReal.natCast_ne_top c.totalPairs

variable [Fintype Λ] [DecidableEq Λ]

/-- The number of ordered pairs of distinct agents with states `(s₁, s₂)`. -/
def interactionCount (c : Config Λ) (s₁ s₂ : Λ) : ℕ :=
  if s₁ = s₂ then
    c.count s₁ * (c.count s₁ - 1)
  else
    c.count s₁ * c.count s₂

/-- The scheduler probability of selecting an ordered state pair `(s₁, s₂)`. -/
noncomputable def interactionProb (c : Config Λ) (s₁ s₂ : Λ) : ENNReal :=
  (c.interactionCount s₁ s₂ : ENNReal) / (c.totalPairs : ENNReal)

private theorem sum_count_univ (c : Config Λ) :
    (Finset.univ.sum fun s : Λ => c.count s) = c.card := by
  have h :
      (∑ s ∈ (Finset.univ : Finset Λ), c.count s) = c.card :=
    Multiset.sum_count_eq_card (s := (Finset.univ : Finset Λ)) (m := c)
      (by intro a _; exact Finset.mem_univ a)
  rw [← h]

private theorem sum_count_erase (c : Config Λ) (s : Λ) :
    ((Finset.univ.erase s).sum fun t : Λ => c.count t) = c.card - c.count s := by
  have hsum :
      c.count s + ((Finset.univ.erase s).sum fun t : Λ => c.count t) = c.card := by
    calc
      c.count s + ((Finset.univ.erase s).sum fun t : Λ => c.count t)
          = (Finset.univ.sum fun t : Λ => c.count t) := by
            exact Finset.add_sum_erase Finset.univ (fun t : Λ => c.count t)
              (Finset.mem_univ s)
      _ = c.card := sum_count_univ c
  omega

/-- For a fixed initiator state, summing over responder states gives the
number of agents in that initiator state times the number of possible distinct
partners. -/
theorem sum_interactionCount_right (c : Config Λ) (s₁ : Λ) :
    (Finset.univ.sum fun s₂ : Λ => c.interactionCount s₁ s₂) =
      c.count s₁ * (c.card - 1) := by
  classical
  by_cases hzero : c.count s₁ = 0
  · simp [interactionCount, hzero]
  have hpos : 0 < c.count s₁ := Nat.pos_of_ne_zero hzero
  have hpoint :
      (fun s₂ : Λ => c.interactionCount s₁ s₂) =
        fun s₂ : Λ =>
          c.count s₁ * if s₁ = s₂ then c.count s₁ - 1 else c.count s₂ := by
    funext s₂
    by_cases h : s₁ = s₂
    · simp [interactionCount, h]
    · simp [interactionCount, h]
  rw [hpoint, ← Finset.mul_sum]
  congr 1
  have hsplit :
      (Finset.univ.sum fun s₂ : Λ =>
          if s₁ = s₂ then c.count s₁ - 1 else c.count s₂) =
        (c.count s₁ - 1) + ((Finset.univ.erase s₁).sum fun s₂ : Λ => c.count s₂) := by
    calc
      (Finset.univ.sum fun s₂ : Λ =>
          if s₁ = s₂ then c.count s₁ - 1 else c.count s₂)
          = (Finset.univ.sum fun s₂ : Λ =>
              if s₂ = s₁ then c.count s₁ - 1 else c.count s₂) := by
                refine Finset.sum_congr rfl ?_
                intro s₂ _
                by_cases h : s₁ = s₂ <;> simp [h, eq_comm]
      _ = (c.count s₁ - 1) + ((Finset.univ.erase s₁).sum fun s₂ : Λ => c.count s₂) := by
            rw [← Finset.add_sum_erase Finset.univ
              (fun s₂ : Λ => if s₂ = s₁ then c.count s₁ - 1 else c.count s₂)
              (Finset.mem_univ s₁)]
            simp only [if_true]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro s₂ hs₂
            have hs₂_ne : s₂ ≠ s₁ := (Finset.mem_erase.mp hs₂).1
            simp [hs₂_ne]
  rw [hsplit, sum_count_erase]
  have hle : c.count s₁ ≤ c.card := Multiset.count_le_card s₁ c
  omega

/-- The interaction counts over all ordered state pairs sum to the number of
ordered pairs of distinct agents. -/
theorem sum_interactionCount (c : Config Λ) :
    (Finset.univ.sum fun s₁ : Λ =>
      Finset.univ.sum fun s₂ : Λ =>
        c.interactionCount s₁ s₂) = c.totalPairs := by
  rw [show (Finset.univ.sum fun s₁ : Λ =>
      Finset.univ.sum fun s₂ : Λ => c.interactionCount s₁ s₂) =
        Finset.univ.sum fun s₁ : Λ => c.count s₁ * (c.card - 1) by
    refine Finset.sum_congr rfl ?_
    intro s₁ _
    exact sum_interactionCount_right c s₁]
  rw [← Finset.sum_mul, sum_count_univ]
  rfl

/-- Uniform random scheduler over ordered state pairs. -/
noncomputable def interactionPMF (c : Config Λ) (hc : 2 ≤ c.card) :
    PMF (Λ × Λ) := by
  refine ⟨fun p => c.interactionProb p.1 p.2, ?_⟩
  have hfin := hasSum_fintype (fun p : Λ × Λ => c.interactionProb p.1 p.2)
  suffices hgoal :
      Finset.univ.sum (fun p : Λ × Λ => c.interactionProb p.1 p.2) = 1 by
    rwa [hgoal] at hfin
  simp only [interactionProb]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [show (Finset.univ : Finset (Λ × Λ)) = Finset.univ ×ˢ Finset.univ
    from (Finset.univ_product_univ).symm]
  simp_rw [Finset.sum_product]
  have hkey :
      (∑ s₁ : Λ, ∑ s₂ : Λ, (c.interactionCount s₁ s₂ : ENNReal)) =
        (c.totalPairs : ENNReal) := by
    exact_mod_cast sum_interactionCount c
  rw [hkey]
  exact ENNReal.mul_inv_cancel (totalPairs_ne_zero_ennreal hc) (totalPairs_ne_top c)

end Config

namespace Protocol

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Deterministic update associated with a scheduled ordered state pair. -/
noncomputable def scheduledStep (P : Protocol Λ) (c : Config Λ) (pair : Λ × Λ) :
    Config Λ :=
  stepOrSelf P c pair.1 pair.2

/-- The one-step distribution induced by the uniform random scheduler. -/
noncomputable def stepDist (P : Protocol Λ) (c : Config Λ) (hc : 2 ≤ c.card) :
    PMF (Config Λ) :=
  PMF.map (scheduledStep P c) (c.interactionPMF hc)

/-- Every support point of the one-step distribution is obtained from one
scheduled ordered pair. -/
theorem stepDist_support (P : Protocol Λ) (c : Config Λ) (hc : 2 ≤ c.card)
    (c' : Config Λ) :
    c' ∈ (P.stepDist c hc).support →
      ∃ pair : Λ × Λ, scheduledStep P c pair = c' := by
  intro h
  simp only [stepDist, PMF.support_map, Set.mem_image] at h
  obtain ⟨pair, _, heq⟩ := h
  exact ⟨pair, heq⟩

/-- Every support point of the one-step distribution is reachable from the
current configuration. -/
theorem stepDist_support_reachable (P : Protocol Λ) (c : Config Λ)
    (hc : 2 ≤ c.card) (c' : Config Λ) :
    c' ∈ (P.stepDist c hc).support → P.Reachable c c' := by
  intro h
  obtain ⟨⟨r₁, r₂⟩, hr⟩ := stepDist_support P c hc c' h
  rw [← hr]
  exact reachable_stepOrSelf c r₁ r₂

/-- One stochastic scheduler step preserves population size on every support
point. -/
theorem stepDist_support_card_eq (P : Protocol Λ) (c : Config Λ)
    (hc : 2 ≤ c.card) (c' : Config Λ) :
    c' ∈ (P.stepDist c hc).support → c'.card = c.card := by
  intro h
  exact reachable_card_eq (stepDist_support_reachable P c hc c' h)

end Protocol

end ExactMajority
