/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# SeamDischargeCore — lightweight core of SeamDischarge for Capstone.

Extracted from `SeamDischarge.lean` to break the transitive `Assembly` import.
`SeamDischarge` imports `Assembly`, which pulls in the entire V2-V7 chain;
`Capstone` only needs `drift_budget_nonvacuous` (a pure arithmetic lemma),
so this file provides it WITHOUT importing Assembly or any chain file.

`SeamDischarge.lean` re-exports this via its own import of SeamDischargeCore.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace ExactMajority
namespace SeamDischarge

open scoped ENNReal NNReal

/-- **Non-vacuity of the drift budget.**  The discharged epidemic budget
`(1/n²).toNNReal` is `≤ 1/n² ≤ 1` for `n ≥ 1` (and strictly `< 1` for `n ≥ 2`), i.e. a
genuine sub-unit per-phase failure probability, NOT a vacuous `≥ 1`. -/
theorem drift_budget_nonvacuous (n : ℕ) (hn : 2 ≤ n) :
    ((Real.toNNReal (1 / (n : ℝ) ^ 2) : ℝ≥0) : ℝ≥0∞) < 1 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlt : (1 : ℝ) / (n : ℝ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  rw [show (((Real.toNNReal (1 / (n : ℝ) ^ 2)) : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal (1 / (n : ℝ) ^ 2) from by rw [ENNReal.ofReal]]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr hlt

end SeamDischarge
end ExactMajority
