/-
Ripple.BoundedUniversality.GPAC.RationalClock
-------------------------
A periodic clock realized by a polynomial ODE with RATIONAL (indeed
integer) coefficients — no π anywhere in the system.

The literature states the BGP clock over Q(π) as
    u' = 2π v,   v' = -2π u      (solution sin(2πt), cos(2πt), period 1)
where the coefficient 2π ∈ Q(π) is present ONLY to normalize the period
to 1. Dropping that cosmetic normalization, the bare rational clock
    u' = v,   v' = -u            (solution sin t, cos t, period 2π)
has coefficients ±1 ∈ ℚ. π appears only as the PERIOD of the solution,
never as data of the system. Thus the coefficient field can be taken to
be ℚ: π is inessential to the construction.

This file proves the rational clock has genuine strong (HasDerivAt)
semantics and is 2π-periodic.
-/

import Ripple.BoundedUniversality.GPAC.PIVP
import Ripple.BoundedUniversality.GPAC.StrongSemantics
import Mathlib

namespace Ripple.BoundedUniversality.GPAC

open Ripple.BoundedUniversality.Core

/-- The bare rational clock ODE: `u' = v`, `v' = -u`, with `u(0)=0`,
`v(0)=1`.  All coefficients are in `ℚ` (in fact `±1`). -/
noncomputable def ratClockPIVP : PIVP ℚ where
  n := 2
  vf := fun i =>
    if i = 0 then MvPolynomial.X ⟨1, by omega⟩
    else -(MvPolynomial.X ⟨0, by show 0 < 2; omega⟩)
  init := fun _ i => if i = 0 then 0 else 1

/-- Strong semantics for the rational clock: the genuine ODE solution is
`(sin t, cos t)`, with the derivative given by the rational vector field
`(v, -u)`.  No π enters the system. -/
noncomputable def ratClockSemantics : StrongPIVPSemantics ratClockPIVP where
  traj := fun _ t i => if (i : ℕ) = 0 then Real.sin t else Real.cos t
  init_at_zero := by
    intro w; ext i
    refine Fin.cases ?_ ?_ i <;>
      simp [ratClockPIVP, PIVP.realInit, Real.sin_zero, Real.cos_zero]
  solves_ode := by
    intro w t _
    refine hasDerivAt_pi.mpr (fun i => ?_)
    refine Fin.cases ?_ ?_ i
    · -- u' = v : d/dt sin t = cos t
      show HasDerivAt (fun t => Real.sin t) _ t
      convert Real.hasDerivAt_sin t using 1
      simp [ratClockPIVP, PIVP.evalVF]
    · -- v' = -u : d/dt cos t = -sin t
      intro _
      show HasDerivAt (fun t => Real.cos t) _ t
      convert Real.hasDerivAt_cos t using 1
      simp [ratClockPIVP, PIVP.evalVF]
  traj_continuous := by
    intro w; apply continuous_pi; intro i
    refine Fin.cases ?_ ?_ i
    · exact Real.continuous_sin
    · intro j; refine Fin.cases ?_ ?_ j
      · exact Real.continuous_cos
      · intro k; exact k.elim0

/-- The rational clock is `2π`-periodic. -/
theorem ratClock_periodic (w : ℕ) (t : ℝ) (i : Fin ratClockPIVP.n) :
    ratClockSemantics.traj w (t + 2 * Real.pi) i = ratClockSemantics.traj w t i := by
  simp only [ratClockSemantics]
  split
  · exact Real.sin_add_two_pi t
  · exact Real.cos_add_two_pi t

/-- The rational clock is nonconstant (it genuinely oscillates). -/
theorem ratClock_nonconstant :
    ∃ t : ℝ, ratClockSemantics.traj 0 t ⟨0, by show 0 < 2; omega⟩
           ≠ ratClockSemantics.traj 0 0 ⟨0, by show 0 < 2; omega⟩ := by
  refine ⟨Real.pi / 2, ?_⟩
  simp only [ratClockSemantics, show ((⟨0, by show 0 < 2; omega⟩ : Fin ratClockPIVP.n) : ℕ) = 0 from rfl,
    if_pos, Real.sin_pi_div_two, Real.sin_zero]
  norm_num

/-- A periodic clock with RATIONAL coefficients exists: the system
`u' = v, v' = -u` over `ℚ` has a genuine (HasDerivAt) periodic,
nonconstant solution.  π enters only as the period of the solution,
never as a coefficient. -/
theorem exists_rational_periodic_clock :
    ∃ (P : PIVP ℚ) (S : StrongPIVPSemantics P),
      (∃ (period : ℝ), 0 < period ∧
        ∀ w t i, S.traj w (t + period) i = S.traj w t i) ∧
      (∃ w t i, S.traj w t i ≠ S.traj w 0 i) := by
  refine ⟨ratClockPIVP, ratClockSemantics,
    ⟨2 * Real.pi, by positivity, ratClock_periodic⟩, ?_⟩
  obtain ⟨t, ht⟩ := ratClock_nonconstant
  exact ⟨0, t, ⟨0, by show 0 < 2; omega⟩, ht⟩

end Ripple.BoundedUniversality.GPAC
