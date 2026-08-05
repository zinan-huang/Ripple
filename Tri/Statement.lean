/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Tri.Chain
import Tri.Compose

/-!
# A formal statement of Theorem 1(b)

This file records a faithful, explicit-constant formulation of Theorem 1(b) of
Condon--Hajiaghayi--Kirkpatrick--Mañuch, *Approximate Majority Analyses using
Tri-molecular Chemical Reaction Networks*.  The proposition is recorded as a
definition and is **not proved** here.

The structural facts needed to read its terminal-time marginal as a hitting
claim are proved: consensus is absorbing, and freezing an already absorbing
target does not change its time-`T` marginal.
-/

namespace Tri

open scoped ENNReal

/-- A population state is at consensus when every molecule is `Y` or every
molecule is `X`. -/
def IsConsensus (n x : ℕ) :
    Prop :=
  x = 0 ∨ x = n

/-- Membership in a consensus state is decidable. -/
instance (n : ℕ) : DecidablePred (IsConsensus n) := by
  intro x
  unfold IsConsensus
  infer_instance

/-- A population state is an `X`-majority consensus when every molecule is
`X`. -/
def IsXMajority (n x : ℕ) :
    Prop :=
  x = n

/-- Membership in the all-`X` state is decidable. -/
instance (n : ℕ) : DecidablePred (IsXMajority n) := by
  intro x
  unfold IsXMajority
  infer_instance

/-- `HasXInitialGap n γ x₀` is the subtraction-free form of saying that the
initial `X` count exceeds the initial `Y` count by at least
`√(γ n lg n)`.  The witness `gap` is no larger than the actual count gap,
and its square is at least the required threshold. -/
def HasXInitialGap (n γ x₀ : ℕ) :
    Prop :=
  ∃ gap : ℕ, n + gap ≤ 2 * x₀ ∧ γ * n * Nat.log 2 n ≤ gap ^ 2

/-- **The formal statement of Theorem 1(b).**  Proved unconditionally as
`Tri.theorem1b` in `Tri/Theorem1bFinal.lean`.

The witnesses `C` and `c` replace the paper's hidden constants in, respectively,
`O(γ n lg n)` and `exp(-Ω(γ lg n))`; `n₀` makes the absolute part of "for
sufficiently large `n`" explicit.  The further condition `6 * γ * lg n ≤ n`
is the size assumption used in the paper's proof.  The remaining assumptions say
that `γ ≥ 1`, the initial count is a physical state, and the initial `X`--`Y`
gap is at least `√(γ n lg n)`.

After `C * γ * n * lg n` interactions, the displayed sum is exactly the
probability of not being at the all-`X` state.  Its upper bound
`(n⁻¹)^(c * γ)` is the explicit power-law form of `exp(-Ω(γ lg n))`.  Since
all-`X` is absorbing, `x = n` at that time is equivalent to having reached the
paper's `X`-majority consensus by that time; this equivalence is proved below.

The base-two logarithm `Nat.log 2 n` fixes the paper's `lg n`
convention. -/
def Theorem1b_statement
    : Prop :=
  ∃ C n₀ : ℕ, ∃ c : ℝ,
    0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ x₀ : ℕ,
        n₀ ≤ n →
        1 ≤ γ →
        6 * γ * Nat.log 2 n ≤ n →
        x₀ ≤ n →
        HasXInitialGap n γ x₀ →
        ∑' z, (if IsXMajority n z then 0
          else iter (triChain n) (C * γ * n * Nat.log 2 n) x₀ z)
            ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))

/-- **Theorem 1(a).**  From *any* initial configuration `x₀ ≤ n`, the
tri-molecular CRN reaches a consensus (`x = 0` or `x = n`) within
`C * γ * n * lg n` interaction events, except for a failure mass at most
`(n⁻¹)^(c * γ) = exp(-Ω(γ lg n))`.  Unlike Theorem 1(b), there is no initial-gap
precondition and the target is either consensus, not specifically `X`-majority. -/
def Theorem1a_statement
    : Prop :=
  ∃ C n₀ : ℕ, ∃ c : ℝ,
    0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ x₀ : ℕ,
        n₀ ≤ n →
        1 ≤ γ →
        6 * γ * Nat.log 2 n ≤ n →
        x₀ ≤ n →
        ∑' z, (if IsConsensus n z then 0
          else iter (triChain n) (C * γ * n * Nat.log 2 n) x₀ z)
            ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))

/-- Consensus states are absorbing for the `X`-count chain. -/
theorem consensus_absorbing (n x : ℕ) (hx : IsConsensus n x) :
    triChain n x = PMF.pure x := by
  rcases hx with hx | hx
  · unfold triChain
    subst x
    by_cases h3 : 3 ≤ n
    · rw [dif_pos ⟨h3, Nat.zero_le n⟩]
      simpa using triStep_consensus_Y n (by omega)
    · rw [dif_neg]
      exact fun h => h3 h.1
  · subst x
    by_cases h3 : 3 ≤ n
    · exact triChain_consensus h3
    · unfold triChain
      rw [dif_neg]
      exact fun h => h3 h.1

/-- For an absorbing target, the probability of having reached the target by
time `T` equals the ordinary time-`T` marginal at that target.

`hitProb` computes reachability by freezing the target.  If the target was
already absorbing, freezing leaves the kernel unchanged, and the singleton
indicator sum reduces to its one marginal. -/
theorem hitProb_eq_iter_of_absorbing (K : ℕ → PMF ℕ) (target T start : ℕ)
    (hTarget : K target = PMF.pure target) :
    hitProb (fun z => z = target) K T start = iter K T start target := by
  have hfreeze : freeze (fun z => z = target) K = K := by
    funext z
    by_cases hz : z = target
    · subst z
      simp [freeze, hTarget]
    · simp [freeze, hz]
  unfold hitProb expect ind
  rw [hfreeze, tsum_eq_single target]
  · simp
  · intro z hz
    simp [hz]

/-- For the Tri chain specifically, reaching all-`X` by time `T` and being at
all-`X` at time `T` have the same probability. -/
theorem xMajority_reached_eq_at_time (n T x₀ : ℕ) :
    hitProb (IsXMajority n) (triChain n) T x₀ = iter (triChain n) T x₀ n := by
  change hitProb (fun z => z = n) (triChain n) T x₀ = iter (triChain n) T x₀ n
  apply hitProb_eq_iter_of_absorbing
  exact consensus_absorbing n n (Or.inr rfl)

end Tri
