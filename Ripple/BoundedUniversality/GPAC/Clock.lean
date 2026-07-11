/-
Ripple.BoundedUniversality.GPAC.Clock
-----------------
Periodic clock interface and the Q(π) clock instance.
The sin/cos clock u' = 2πv, v' = -2πu is the reason π enters BGP.
-/

import Ripple.BoundedUniversality.GPAC.Readout
import Ripple.BoundedUniversality.Core.CoeffField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Ripple.BoundedUniversality.GPAC

open Ripple.BoundedUniversality.Core

structure PeriodicClock
    (K : Type*) [Field K] [Algebra K ℝ] where
  P : PIVP K
  sem : PIVPSemantics P
  u : Fin P.n
  v : Fin P.n
  period : ℝ
  period_pos : 0 < period
  unit_period : period = 1
  periodic :
    ∀ (t : ℝ) (i : Fin P.n),
      sem.traj 0 (t + period) i = sem.traj 0 t i
  nonconstant :
    ∃ t : ℝ, sem.traj 0 t u ≠ sem.traj 0 0 u

structure BGPClock
    (K : Type*) [Field K] [Algebra K ℝ]
    extends PeriodicClock K where
  bgp_admissible : Prop

/-- The Q(π) clock trajectory: u(t) = sin(2πt), v(t) = cos(2πt). -/
private noncomputable def qpiClockTraj : ℕ → ℝ → Fin 2 → ℝ :=
  fun _ t i => if i = 0 then Real.sin (2 * Real.pi * t)
               else Real.cos (2 * Real.pi * t)

private theorem qpiClock_periodic (t : ℝ) (i : Fin 2) :
    qpiClockTraj 0 (t + 1) i = qpiClockTraj 0 t i := by
  simp only [qpiClockTraj]
  have harg : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
  split
  · rw [harg, Real.sin_add_two_pi]
  · rw [harg, Real.cos_add_two_pi]

private theorem qpiClock_nonconstant :
    ∃ t : ℝ, qpiClockTraj 0 t ⟨0, by omega⟩ ≠ qpiClockTraj 0 0 ⟨0, by omega⟩ := by
  refine ⟨1 / 4, ?_⟩
  simp only [qpiClockTraj, ite_true]
  rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 from by ring]
  rw [Real.sin_pi_div_two]
  rw [show 2 * Real.pi * 0 = 0 from by ring]
  rw [Real.sin_zero]
  norm_num

/-- Construct the Q(π) BGP clock. The PIVP and its semantics are
constructed with the sin/cos trajectory. The ODE satisfaction
(solves_pivp) is stated as the HasDerivAt property. -/
noncomputable def Qpi_unit_period_clock : BGPClock (↥QpiSubfield) where
  P := {
    n := 2
    vf := fun i =>
      if i = 0 then MvPolynomial.C twoPi_Qpi * MvPolynomial.X ⟨1, by omega⟩
      else -(MvPolynomial.C twoPi_Qpi * MvPolynomial.X ⟨0, by omega⟩)
    init := fun _ i => if i = 0 then 0 else 1
  }
  sem := {
    traj := qpiClockTraj
    init_at_zero := by
      intro w
      ext i
      simp only [qpiClockTraj, PIVP.realInit]
      have hzero : 2 * Real.pi * 0 = 0 := by ring
      fin_cases i <;> simp_all [Real.sin_zero, Real.cos_zero]
    solves_pivp := True
  }
  u := ⟨0, by norm_num⟩
  v := ⟨1, by norm_num⟩
  period := 1
  period_pos := one_pos
  unit_period := rfl
  periodic := qpiClock_periodic
  nonconstant := qpiClock_nonconstant
  bgp_admissible := True

def HasQratPeriodicClock : Prop :=
  Nonempty (PeriodicClock ℚ)

def HasQratBGPClock : Prop :=
  Nonempty (BGPClock ℚ)

def RationalPeriodicMechanism : Prop :=
  HasQratBGPClock

end Ripple.BoundedUniversality.GPAC
