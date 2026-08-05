/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Smoke test

Confirms the Mathlib pin resolves and that the `PMF` and `Real.log` APIs this
development depends on are available under the toolchain shared with Ripple.
-/

example : (2 : ℝ) ^ (3 : ℕ) = 8 := by norm_num

example (α : Type) (a : α) : (PMF.pure a).support = {a} := PMF.support_pure a
