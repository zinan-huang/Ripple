/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform Random Scheduler

The probabilistic scheduler selects an ordered pair `(i, r)` of *distinct*
agents uniformly at random.  Given a configuration `c` with population size
`n ≥ 2`, the probability of selecting an interaction between an agent of
state `s₁` (initiator) and an agent of state `s₂` (responder) is:

  - If `s₁ ≠ s₂`: `c.countOf(s₁) * c.countOf(s₂) / (n * (n - 1))`
  - If `s₁ = s₂`: `c.countOf(s₁) * (c.countOf(s₁) - 1) / (n * (n - 1))`

This file defines the interaction probability function and constructs a
`PMF` (probability mass function) over `State × State` interactions.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Config
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace PopProto

open State

namespace Config

variable {n : ℕ}

/-- The number of ordered pairs of distinct agents with states `(s₁, s₂)`. -/
def interactionCount (c : Config n) (s₁ s₂ : State) : ℕ :=
  if s₁ = s₂ then
    c.countOf s₁ * (c.countOf s₁ - 1)
  else
    c.countOf s₁ * c.countOf s₂

/-- The total number of ordered pairs of distinct agents: `n * (n - 1)`. -/
def totalPairs (n : ℕ) : ℕ := n * (n - 1)

/-- The probability of interaction `(s₁, s₂)` as a rational number in `ℝ≥0∞`. -/
noncomputable def interactionProb (c : Config n) (_hn : n ≥ 2) (s₁ s₂ : State) :
    ENNReal :=
  (c.interactionCount s₁ s₂ : ENNReal) / (totalPairs n : ENNReal)

/-! ### Expanding finite sums over `State`

Since `State` has exactly three elements `{x, b, y}`, any `Finset.univ.sum f`
can be expanded to `f .x + f .b + f .y`. -/

private lemma sum_state_eq {α : Type*} [AddCommMonoid α] (f : State → α) :
    Finset.univ.sum f = f .x + f .b + f .y := by
  rw [show (Finset.univ : Finset State) = {.x, .b, .y} from by
    ext s; simp [Finset.mem_univ]; cases s <;> simp]
  rw [Finset.sum_insert (show State.x ∉ ({.b, .y} : Finset State) from by decide)]
  rw [Finset.sum_insert (show State.b ∉ ({.y} : Finset State) from by decide)]
  rw [Finset.sum_singleton, ← add_assoc]

/-! ### Row-sum identity

For any row `s₁`, the sum `∑_{s₂} interactionCount(s₁, s₂)` equals
`countOf(s₁) * (n - 1)`.  The key insight is factoring out `countOf(s₁)`:
  `a*(a-1) + a*b + a*c = a * ((a-1) + b + c) = a * (n-1)`
when `a + b + c = n`.
-/

private lemma row_sum_eq_mul (a b c s : ℕ) (h : a + b + c = s) :
    a * (a - 1) + a * b + a * c = a * (s - 1) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · simp [ha]
  · -- Factor out `a`: a*(a-1) + a*b + a*c = a*((a-1) + b + c)
    have hfactor : a * (a - 1) + a * b + a * c = a * ((a - 1) + b + c) := by ring
    rw [hfactor]
    congr 1
    omega

/-- Each inner sum equals `countOf(s₁) * (n - 1)`. -/
private lemma inner_sum_x (c : Config n) :
    (Finset.univ.sum fun s₂ => c.interactionCount .x s₂) = c.x_count * (n - 1) := by
  rw [sum_state_eq]
  change c.x_count * (c.x_count - 1) + c.x_count * c.b_count +
      c.x_count * c.y_count = c.x_count * (n - 1)
  exact row_sum_eq_mul c.x_count c.b_count c.y_count n c.sum_eq

private lemma inner_sum_b (c : Config n) :
    (Finset.univ.sum fun s₂ => c.interactionCount .b s₂) = c.b_count * (n - 1) := by
  rw [sum_state_eq]; simp [interactionCount, countOf]
  have := c.sum_eq
  have := row_sum_eq_mul c.b_count c.x_count c.y_count n (by omega)
  omega

private lemma inner_sum_y (c : Config n) :
    (Finset.univ.sum fun s₂ => c.interactionCount .y s₂) = c.y_count * (n - 1) := by
  rw [sum_state_eq]; simp [interactionCount, countOf]
  have := c.sum_eq
  have := row_sum_eq_mul c.y_count c.x_count c.b_count n (by omega)
  omega

/-- The sum of all interaction counts equals `n * (n - 1)`.
    This is the key identity: `∑ᵢ ∑ⱼ count(i,j) = n(n-1)`.
    Proof strategy: factor each row sum, then sum the rows. -/
theorem sum_interactionCount (c : Config n) :
    (Finset.univ.sum fun s₁ : State =>
      Finset.univ.sum fun s₂ : State =>
        c.interactionCount s₁ s₂) = totalPairs n := by
  -- Expand outer sum and apply row-sum lemmas
  rw [sum_state_eq, inner_sum_x, inner_sum_b, inner_sum_y]
  -- Goal: x*(n-1) + b*(n-1) + y*(n-1) = n*(n-1)
  -- Factor out (n-1): (x + b + y) * (n-1) = n * (n-1)
  unfold totalPairs
  rw [← add_mul, ← add_mul, c.sum_eq]

/-- `totalPairs n > 0` when `n ≥ 2`. -/
theorem totalPairs_pos (hn : n ≥ 2) : 0 < totalPairs n := by
  unfold totalPairs
  exact Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)

/-- `totalPairs n ≠ 0` when `n ≥ 2`, as `ENNReal`. -/
theorem totalPairs_ne_zero_ennreal (hn : n ≥ 2) :
    (totalPairs n : ENNReal) ≠ 0 := by
  exact_mod_cast (totalPairs_pos hn).ne'

/-- `totalPairs n ≠ ⊤` as `ENNReal` (it's a natural number). -/
theorem totalPairs_ne_top : (totalPairs n : ENNReal) ≠ ⊤ :=
  ENNReal.natCast_ne_top (totalPairs n)

/-- Construct the PMF for the uniform random scheduler.
    This requires `n ≥ 2` so that the denominator `n * (n-1) > 0`. -/
noncomputable def interactionPMF (c : Config n) (hn : n ≥ 2) :
    PMF (State × State) := by
  refine ⟨fun p => c.interactionProb hn p.1 p.2, ?_⟩
  -- Goal: HasSum (fun p => interactionProb c hn p.1 p.2) 1
  -- Use hasSum_fintype to reduce to a Finset.sum equality
  have hfin := hasSum_fintype (fun p : State × State => c.interactionProb hn p.1 p.2)
  suffices hgoal : Finset.univ.sum
      (fun p : State × State => c.interactionProb hn p.1 p.2) = 1 by
    rwa [hgoal] at hfin
  -- Unfold interactionProb to (count / total)
  simp only [interactionProb]
  -- Factor the constant denominator: ∑ (a/d) = (∑ a) * d⁻¹
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  -- Convert single sum over State × State to double sum
  rw [show (Finset.univ : Finset (State × State)) = Finset.univ ×ˢ Finset.univ
    from (Finset.univ_product_univ).symm]
  simp_rw [Finset.sum_product]
  -- Push Nat.cast through the double sum and apply sum_interactionCount
  have hkey : (∑ s₁ : State, ∑ s₂ : State, (c.interactionCount s₁ s₂ : ENNReal)) =
      (totalPairs n : ENNReal) := by
    exact_mod_cast sum_interactionCount c
  rw [hkey]
  -- Goal: (totalPairs n : ENNReal) * (totalPairs n : ENNReal)⁻¹ = 1
  exact ENNReal.mul_inv_cancel (totalPairs_ne_zero_ennreal hn) totalPairs_ne_top

end Config
end PopProto
