/-
Copyright (c) 2026 Xuanji Li and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li, Lean Pool contributors
-/

/- Modified for Ripple (2026-11-08): ported from LeanPool/lean-pool
`LeanPool/Chudnovsky/BernoulliValues.lean` at commit 6b28d23e (Apache-2.0, see NOTICE); module-system
syntax removed, namespace `Chudnovsky` renamed `Ripple.Number.Milla`, adapted to Mathlib
v4.30.0. -/

import Mathlib.NumberTheory.Bernoulli

/-!
# Bernoulli values used in the Chudnovsky formula

Evaluate the two small Bernoulli numbers once, without unfolding their recursive definitions
inside the analytic developments that use them.
-/

namespace Ripple.Number.Milla

/-- The fourth Bernoulli number, using the known value of `bernoulli'`. -/
lemma bernoulli_four_value : bernoulli 4 = -1 / 30 := by
  rw [bernoulli, bernoulli'_four]
  norm_num

/-- The sixth Bernoulli number, evaluated from the preceding values. -/
lemma bernoulli_six_value : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5]
    norm_num [Nat.choose]
  rw [bernoulli, h6]
  norm_num

end Ripple.Number.Milla
