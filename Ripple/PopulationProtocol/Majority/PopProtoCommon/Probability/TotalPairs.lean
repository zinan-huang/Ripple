/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Total Pairs Counting (Generic)

The number of ordered pairs of distinct agents in a population of size `n`,
i.e. `n * (n - 1)`. This appears as the denominator of the uniform random
scheduler's interaction probability, and is independent of any particular
state-set or transition structure.

Extracted from PP-Proof's `PopProto/Probability/Scheduler.lean`.
-/

import Mathlib.Data.ENNReal.Basic

namespace PopProtoCommon

/-- The total number of ordered pairs of distinct agents in a population
    of size `n`: `n * (n - 1)`. -/
def totalPairs (n : ℕ) : ℕ := n * (n - 1)

/-- `totalPairs n > 0` when `n ≥ 2`. -/
theorem totalPairs_pos {n : ℕ} (hn : n ≥ 2) : 0 < totalPairs n := by
  unfold totalPairs
  exact Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)

/-- `totalPairs n ≠ 0` when `n ≥ 2`, as `ENNReal`. -/
theorem totalPairs_ne_zero_ennreal {n : ℕ} (hn : n ≥ 2) :
    (totalPairs n : ENNReal) ≠ 0 := by
  exact_mod_cast (totalPairs_pos hn).ne'

/-- `totalPairs n ≠ ⊤` as `ENNReal` (it's a natural number). -/
theorem totalPairs_ne_top {n : ℕ} : (totalPairs n : ENNReal) ≠ ⊤ :=
  ENNReal.natCast_ne_top (totalPairs n)

end PopProtoCommon
