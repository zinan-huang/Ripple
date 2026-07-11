/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Population Configuration

A configuration records how many agents hold each of the three opinions
in a population of size `n`.  The constraint `x_count + b_count + y_count = n`
is enforced by the type itself.
-/

import Ripple.PopulationProtocol.Majority.PopProto.State

namespace PopProto

open State

/-- A configuration of a population of size `n`.
    Stores the counts of agents in each state with a proof that they sum to `n`. -/
structure Config (n : ℕ) where
  x_count : ℕ
  b_count : ℕ
  y_count : ℕ
  sum_eq : x_count + b_count + y_count = n

namespace Config

variable {n : ℕ}

/-- The gap `x_count - y_count` as an integer (can be negative). -/
def gap (c : Config n) : ℤ :=
  (c.x_count : ℤ) - (c.y_count : ℤ)

/-- Number of opinionated agents (non-blank). -/
def opinionated (c : Config n) : ℕ :=
  c.x_count + c.y_count

/-- Number of agents in a given state. -/
def countOf (c : Config n) : State → ℕ
  | .x => c.x_count
  | .b => c.b_count
  | .y => c.y_count

/-- All agents hold opinion X. -/
def allX (c : Config n) : Prop :=
  c.x_count = n ∧ c.b_count = 0 ∧ c.y_count = 0

/-- All agents hold opinion Y. -/
def allY (c : Config n) : Prop :=
  c.x_count = 0 ∧ c.b_count = 0 ∧ c.y_count = n

/-- All agents are blank. -/
def allB (c : Config n) : Prop :=
  c.x_count = 0 ∧ c.b_count = n ∧ c.y_count = 0

instance (c : Config n) : Decidable c.allX :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (c : Config n) : Decidable c.allY :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (c : Config n) : Decidable c.allB :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The initial configuration with `a` agents holding X and `n - a` holding Y. -/
def initial (n a : ℕ) (h : a ≤ n) : Config n where
  x_count := a
  b_count := 0
  y_count := n - a
  sum_eq := by omega

/-- Initial configurations are never all-blank when the population is
nonempty. -/
theorem initial_not_allB {n a : ℕ} (h : a ≤ n) (hn : 0 < n) :
    ¬(initial n a h).allB := by
  intro hb
  unfold initial allB at hb
  simp at hb
  omega

/-- A configuration is *consensus* if all agents agree on one opinion. -/
def isConsensus (c : Config n) : Prop :=
  c.allX ∨ c.allY

instance (c : Config n) : Decidable c.isConsensus :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A configuration has *positive opinion* when there exists at least one
    non-blank agent. -/
def hasOpinion (c : Config n) : Prop :=
  c.opinionated > 0

instance (c : Config n) : Decidable c.hasOpinion :=
  inferInstanceAs (Decidable (_ > _))

/-- A positive-size initial configuration always has at least one
opinionated agent. -/
theorem initial_hasOpinion {n a : ℕ} (h : a ≤ n) (hn : 0 < n) :
    (initial n a h).hasOpinion := by
  unfold initial hasOpinion opinionated
  simp
  omega

/-- An initial configuration is consensus exactly when all agents start with X
or all agents start with Y. -/
theorem initial_isConsensus_iff {n a : ℕ} (h : a ≤ n) :
    (initial n a h).isConsensus ↔ a = n ∨ a = 0 := by
  constructor
  · intro hc
    rcases hc with hx | hy
    · left
      unfold initial allX at hx
      exact hx.1
    · right
      unfold initial allY at hy
      exact hy.1
  · intro hcases
    rcases hcases with ha | ha
    · left
      unfold initial allX
      simp [ha]
    · right
      unfold initial allY
      simp [ha]

/-- If both initial opinions are present, the initial configuration is not a
consensus. -/
theorem initial_not_isConsensus_of_pos_lt {n a : ℕ} (h : a ≤ n)
    (ha_pos : 0 < a) (ha_lt : a < n) :
    ¬(initial n a h).isConsensus := by
  rw [initial_isConsensus_iff h]
  omega

/-- The blank count is determined by the population size and opinionated count. -/
theorem b_count_eq (c : Config n) : c.b_count = n - c.opinionated := by
  unfold opinionated; have := c.sum_eq; omega

/-- Each count is bounded by the population size. -/
theorem x_count_le (c : Config n) : c.x_count ≤ n := by have := c.sum_eq; omega
theorem b_count_le (c : Config n) : c.b_count ≤ n := by have := c.sum_eq; omega
theorem y_count_le (c : Config n) : c.y_count ≤ n := by have := c.sum_eq; omega

end Config
end PopProto
