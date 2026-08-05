/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Assembly

/-!
# The buffered phase-2/phase-3 handoff region

This module records the phase-3 entry predicate produced by the reconciled
phase-2 ladder.  Its half-threshold leaves a factor-two minority buffer.  Under
the unchanged headline size guard, that buffer places the minority below
`n / 12`, without strengthening the universally quantified guard on `gamma`.
-/

namespace Tri

/-- Entry to phase 3: the state is physical and twice its minority count is at
most `gamma * lg n`, written without natural subtraction. -/
def Phase3Entry (n γ x : ℕ) : Prop :=
  x ≤ n ∧ 2 * n ≤ 2 * x + γ * Nat.log 2 n

/-- Membership in the buffered phase-3 entry region is decidable. -/
instance (n γ : ℕ) : DecidablePred (Phase3Entry n γ) := by
  intro x
  unfold Phase3Entry
  infer_instance

/-- A phase-3 entry has minority at most half of `gamma * lg n`; under the
headline guard its minority is consequently at most `n / 12`.  The population
identity `x + y = n` keeps both conclusions free of natural subtraction. -/
theorem phase3Entry_buffered {n γ x y : ℕ} (hpop : x + y = n)
    (hentry : Phase3Entry n γ x)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    2 * y ≤ γ * Nat.log 2 n ∧ 12 * y ≤ n := by
  rcases hentry with ⟨_hxn, hentry⟩
  simp only [mul_assoc] at hsize
  constructor <;> omega

#print axioms phase3Entry_buffered

end Tri
