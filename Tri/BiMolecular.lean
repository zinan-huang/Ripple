/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Data.Nat.Basic

/-!
# Bi-molecular Approximate-Majority CRNs (Theorem 2 foundation)

Theorem 2 of Condon–Hajiaghayi–Kirkpatrick–Mañuch concerns three *bi-molecular*
CRNs — Heavy-B, Double-B, Single-B — that emulate the tri-molecular reactions
using an auxiliary *blank* species `B`.  This file sets up the shared state
space and the effective-level projections, following the design in
`data/theorem2_design_Q300.md`.

The central modelling fact (proved downstream, not here) is that the effective
level is **not** a Markov projection: the next level's law depends on `x, y, b`
separately, not on the level alone.  So the reduction to the tri-molecular
analysis is by *stochastic domination at resolution events*, reusing the
phase-1--3 biased-walk engine in resolution-event time — never a one-step kernel
equality.

This file records only the deterministic, subtraction-free scaffolding: the
configuration, the two population invariants, the effective levels, and the
consensus characterisations.
-/

namespace Tri

/-- A bi-molecular configuration: `x` species-`X`, `y` species-`Y`, and `b`
blank (`B`) molecules. -/
structure BiCfg where
  x : ℕ
  y : ℕ
  b : ℕ
deriving DecidableEq

namespace BiCfg

/-- **Heavy-B invariant** `x + y + 2b = n`: each blank stands for a consumed
`X`--`Y` pair, so the blanks are double-counted in the population. -/
def HeavyInv (n : ℕ) (s : BiCfg) : Prop := s.x + s.y + 2 * s.b = n

/-- **Double-B / Single-B invariant** `x + y + b = n`: blanks are ordinary
molecules. -/
def DoubleInv (n : ℕ) (s : BiCfg) : Prop := s.x + s.y + s.b = n

/-- Effective `X`-level for Heavy-B: `x + b`.  Consensus is `heavyLevel = n`. -/
def heavyLevel (s : BiCfg) : ℕ := s.x + s.b

/-- Doubled effective `X`-level for Double-B / Single-B: `2x + b`.  This avoids
half-integers and instantiates the tri engine at effective population `2n`. -/
def doubleLevel (s : BiCfg) : ℕ := 2 * s.x + s.b

/-- Under the Heavy-B invariant the level and its co-level partition `n`. -/
theorem heavyLevel_add_coLevel {n : ℕ} {s : BiCfg} (h : HeavyInv n s) :
    heavyLevel s + (s.y + s.b) = n := by
  unfold heavyLevel HeavyInv at *; omega

/-- Heavy-B all-`X` consensus: `heavyLevel = n` forces `y = b = 0`. -/
theorem heavyLevel_eq_iff {n : ℕ} {s : BiCfg} (h : HeavyInv n s) :
    heavyLevel s = n ↔ s.y = 0 ∧ s.b = 0 := by
  unfold heavyLevel HeavyInv at *; omega

/-- Under the Double-B invariant the doubled level and its co-level sum to `2n`. -/
theorem doubleLevel_add_coLevel {n : ℕ} {s : BiCfg} (h : DoubleInv n s) :
    doubleLevel s + (2 * s.y + s.b) = 2 * n := by
  unfold doubleLevel DoubleInv at *; omega

/-- Double-B all-`X` consensus: `doubleLevel = 2n` forces `y = b = 0`. -/
theorem doubleLevel_eq_iff {n : ℕ} {s : BiCfg} (h : DoubleInv n s) :
    doubleLevel s = 2 * n ↔ s.y = 0 ∧ s.b = 0 := by
  unfold doubleLevel DoubleInv at *; omega

end BiCfg

end Tri
