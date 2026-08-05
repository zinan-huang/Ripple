/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem1bFinal

/-!
# Phase-0 interface for Theorem 1(a)

This module contains only the seed predicate, error budget, and abstract
reachability interface.  Keeping these declarations below both the phase-0
proof and the final Theorem 1(a) assembly avoids an import cycle.
-/

namespace Tri

open scoped ENNReal

/-- A gap of the required size in the `Y` direction, written without natural
subtraction. -/
def HasYInitialGap (n γ x₀ : ℕ) : Prop :=
  ∃ gap : ℕ, 2 * x₀ + gap ≤ n ∧ γ * n * Nat.log 2 n ≤ gap ^ 2

/-- A physical state with a square-root gap in either direction. -/
def Phase0Seed (n γ x : ℕ) : Prop :=
  x ≤ n ∧ (HasXInitialGap n γ x ∨ HasYInitialGap n γ x)

noncomputable instance (n γ : ℕ) : DecidablePred (Phase0Seed n γ) :=
  Classical.decPred _

/-- The phase-0 error budget used by its abstract interface. -/
noncomputable def phase0Error (n γ : ℕ) : ℝ≥0∞ :=
  (n : ℝ≥0∞)⁻¹ ^ ((1 / 100 : ℝ) * (γ : ℝ))

/-- The sole new probabilistic interface for Theorem 1(a).

From every physical start, phase 0 reaches a square-root gap in either species
direction in `C₀ * γ * n * lg n` interactions.  The existing headline regime
is included so the result composes directly with phases 1--3. -/
structure Phase0Hyp (C₀ : ℕ) : Prop where
  hC₀ : 0 < C₀
  reaches : ∀ n γ : ℕ, 2 ^ 420 ≤ n → 1 ≤ γ →
    6 * γ * Nat.log 2 n ≤ n →
    Reaches (triChain n) (C₀ * γ * n * Nat.log 2 n)
      (fun x => x ≤ n) (Phase0Seed n γ) (phase0Error n γ)

end Tri
