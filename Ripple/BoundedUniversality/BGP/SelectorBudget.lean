import Ripple.BoundedUniversality.BGP.SelectorGateApprox

/-!
Ripple.BoundedUniversality.BGP.SelectorBudget
-------------------------
The DepthBudget `Wbound` construction that discharges the carried `hWstep` admissibility
hypothesis of `selector_MU_flag_read_of_tracking_concrete`.

ChatGPT (channel `life`, 2026-06-15, Q2) — KEY: the weighted step
`Wbound j i + k^(dep(j+1) i)·η j i ≤ Wbound(j+1) i` is an INCREASING-budget recurrence, so
`Wbound` must be a PREFIX SUM (not a tail, which decreases with `j`).  With the prefix budget
`Wbound j = W0 + Σ_{m<j} weightedDefect m`, the step is exactly `Finset.sum_range_succ` (an
equality, hence `≤`).  Boundedness below the tube margin is `WboundPrefix_le_cap` (prefix ≤
`W0 + tsum`), which needs the weighted defect to be summable — by geometric comparison once each
`η`-component decays geometrically faster than the depth growth `k^(dep(j+1))`.

This budget layer is COMPLETELY INDEPENDENT of how `η` is split (odds/reset/write/hold): it only
needs `Summable (weightedDefect)`, which the concrete selector discharges from the gain-driven
geometric decays.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Finset

variable {d : ℕ}

/-- The precision-weighted per-cycle defect `k^(dep(j+1) i)·η j i` — the increment the budget
must absorb at cycle `j` (matches the `mu_weighted_step` weighted term). -/
def weightedDefect (k : ℝ) (dep : ℕ → Fin d → ℤ) (η : ℕ → Fin d → ℝ) (j : ℕ) (i : Fin d) : ℝ :=
  k ^ dep (j + 1) i * η j i

/-- The PREFIX budget: `W0 + Σ_{m<j} weightedDefect m`.  Increasing in `j` (for nonnegative
defects), which is the correct orientation for the `mu_weighted_step` recurrence. -/
def WboundPrefix (W0 : Fin d → ℝ) (k : ℝ) (dep : ℕ → Fin d → ℤ) (η : ℕ → Fin d → ℝ)
    (j : ℕ) (i : Fin d) : ℝ :=
  W0 i + ∑ m ∈ Finset.range j, weightedDefect k dep η m i

/-- **The `hWstep` admissibility, DISCHARGED.**  For the prefix budget the weighted step is an
EQUALITY (`Finset.sum_range_succ`), hence the required `≤` holds.  This is exactly the
`hWstep : ∀ j i, Wbound j i + k^(dep(j+1) i)·η j i ≤ Wbound(j+1) i` that
`selector_MU_flag_read_of_tracking_concrete` carries. -/
theorem WboundPrefix_step (W0 : Fin d → ℝ) (k : ℝ) (dep : ℕ → Fin d → ℤ) (η : ℕ → Fin d → ℝ) :
    ∀ j i, WboundPrefix W0 k dep η j i + k ^ dep (j + 1) i * η j i
      ≤ WboundPrefix W0 k dep η (j + 1) i := by
  intro j i
  apply le_of_eq
  unfold WboundPrefix weightedDefect
  rw [Finset.sum_range_succ]
  ring

/-- **The prefix budget stays below its cap.**  `WboundPrefix j ≤ W0 + Σ'_m weightedDefect m`
whenever the weighted defects are nonnegative and summable.  This bounds the all-time budget by a
finite cap (which the tube-margin admissibility `cap ≤ r_LE_U`-style condition then closes). -/
theorem WboundPrefix_le_cap (W0 : Fin d → ℝ) (k : ℝ) (dep : ℕ → Fin d → ℤ) (η : ℕ → Fin d → ℝ)
    (i : Fin d) (hTnonneg : ∀ m, 0 ≤ weightedDefect k dep η m i)
    (hTsum : Summable (fun m => weightedDefect k dep η m i)) (j : ℕ) :
    WboundPrefix W0 k dep η j i ≤ W0 i + ∑' m, weightedDefect k dep η m i := by
  unfold WboundPrefix
  have h := Summable.sum_le_tsum (Finset.range j) (fun m _ => hTnonneg m) hTsum
  linarith [h]

/-- **Geometric summability of the weighted defect.**  If `‖weightedDefect j i‖ ≤ C·q^j` with
`0 ≤ q < 1` (each `η`-component decays geometrically faster than the depth growth `k^(dep(j+1))`),
the weighted defect is summable — so `WboundPrefix_le_cap` applies and the all-time budget is
finite.  Comparison test (`Summable.of_norm_bounded`) against a geometric series. -/
theorem weightedDefect_summable_of_geometric (k : ℝ) (dep : ℕ → Fin d → ℤ) (η : ℕ → Fin d → ℝ)
    (i : Fin d) {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ j, ‖weightedDefect k dep η j i‖ ≤ C * q ^ j) :
    Summable (fun j => weightedDefect k dep η j i) := by
  have hgeom : Summable (fun j : ℕ => C * q ^ j) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left C
  exact Summable.of_norm_bounded hgeom hbound

end Ripple.BoundedUniversality.BGP
