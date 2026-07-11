import Mathlib

/-!
Ripple.BoundedUniversality.GPAC.ThresholdReadout
----------------------------

Generic threshold-readout helpers for the halt coordinate.  If the analog halt
coordinate is within `ε < 1/4` of a Boolean flag value, then the fixed threshold
`1/2` separates the halted and non-halted cases.  The final lemma packages the
standard discrete absorbing-halt argument for iterates.
-/

namespace Ripple.BoundedUniversality.GPAC.ThresholdReadout

/-- If a real value is within `ε < 1/4` of the halt flag `1`, then it lies above
threshold `1/2`. -/
theorem halt_threshold_high {x ε : ℝ}
    (hx : |x - 1| ≤ ε) (hε : ε < 1 / 4) :
    1 / 2 < x := by
  have hlo : -ε ≤ x - 1 := (abs_le.mp hx).1
  linarith

/-- If a real value is within `ε < 1/4` of the halt flag `0`, then it lies below
threshold `1/2`. -/
theorem halt_threshold_low {x ε : ℝ}
    (hx : |x - 0| ≤ ε) (hε : ε < 1 / 4) :
    x < 1 / 2 := by
  have hhi : x - 0 ≤ ε := (abs_le.mp hx).2
  linarith

/-- Eventual high threshold from an eventual flag value `1` and an eventual tube
around that flag. -/
theorem eventual_high_of_flag_eventually_one
    {v flag : ℝ → ℝ} {ε T0 : ℝ} (hε : ε < 1 / 4)
    (htube : ∀ t, T0 ≤ t → |v t - flag t| ≤ ε)
    (hflag1 : ∀ t, T0 ≤ t → flag t = 1) :
    ∀ t, T0 ≤ t → 1 / 2 < v t := by
  intro t ht
  have hx : |v t - 1| ≤ ε := by
    simpa [hflag1 t ht] using htube t ht
  exact halt_threshold_high hx hε

/-- Always-low threshold from a flag value `0` and a tube around that flag on all
nonnegative times. -/
theorem always_low_of_flag_zero
    {v flag : ℝ → ℝ} {ε : ℝ} (hε : ε < 1 / 4)
    (htube : ∀ t, 0 ≤ t → |v t - flag t| ≤ ε)
    (hflag0 : ∀ t, 0 ≤ t → flag t = 0) :
    ∀ t, 0 ≤ t → v t < 1 / 2 := by
  intro t ht
  have hx : |v t - 0| ≤ ε := by
    simpa [hflag0 t ht] using htube t ht
  exact halt_threshold_low hx hε

/-- Generic absorbing-halt helper for iterates: if a configuration at time `j`
is halted and the step function fixes halted configurations, then every later
iterate is halted. -/
theorem halted_iterate_absorbing {Conf : Type} (step : Conf → Conf) (halts : Conf → Prop)
    (habs : ∀ c, halts c → step c = c) {c0 : Conf} {j : ℕ}
    (hj : halts (step^[j] c0)) :
    ∀ n, j ≤ n → halts (step^[n] c0) := by
  intro n hn
  refine Nat.le_induction hj ?_ n hn
  intro n _hn ih
  rw [Function.iterate_succ_apply']
  rw [habs _ ih]
  exact ih

end Ripple.BoundedUniversality.GPAC.ThresholdReadout
