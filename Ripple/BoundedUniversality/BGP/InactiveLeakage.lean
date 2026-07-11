/-
Ripple.BoundedUniversality.BGP.InactiveLeakage
--------------------------
Honest inactive-leakage bound: the analytic core of the tracking field
`hwindow_hold`.

The point of this file is to derive the active-window drift of the u-channel
*from the gate ODE itself* (the `u_hasDeriv` field of the moving-target
solution), NOT from an a-priori box radius.  Over the active window the u-channel
satisfies

  `u'(τ) s = A · α(τ) · bGateU(L, μ(τ), τ) · (z(τ) s − u(τ) s)`,

so by the mean-value inequality the drift from the cycle start is

  `|u(t) s − u(cycleStart j) s| ≤ C · (t − cycleStart j)`,

where `C` is any uniform bound on `|u'|` over `[cycleStart j, t]`.  The genuine
ODE/box content enters through two *named, satisfiable* hypotheses:

* `hzu`  : a box bound `|z τ s − u τ s| ≤ Dzu` on the window
           (the dual-rail box content),
* `hgate`: a bound `|A · α τ · bGateU L (μ τ) τ| ≤ K` on the window
           (the leak rate, supplied off-phase by `bGateU_le_offphase` and the
           α/μ envelope),

together with the window-length/leak-rate closing relation

* `hleak`: `K * Dzu * (t − cycleStart j) ≤ chiSchedule p j * S.D`.

`hleak` is exactly the place where the integral collapse already proved for
`dynChi` (`DynamicGate.dynChi`) lives; we keep it as an explicit hypothesis so
that the drift is derived *honestly* from the ODE, never from a coarse radius,
and never reduced to a wrong-direction surrogate.

The final tracking field `hwindow_hold` then follows by the triangle inequality
through `u (cycleStart j) s`, since
`contractBoundaryError ≥ |u (cycleStart j) s − enc (c j) s|` (it is a `max`).

  `u_window_drift_le_leak`        — drift bound, derived from the ODE (PROVED).
  `contract_window_hold_of_leak`  — triangle assembly to the field shape (PROVED).
-/

import Ripple.BoundedUniversality.BGP.ContractTracking
import Ripple.BoundedUniversality.BGP.ContractSchedules
import Ripple.BoundedUniversality.BGP.SelectorDuhamelWrite

namespace Ripple.BoundedUniversality.BGP

open Real
open Ripple.BoundedUniversality.Core

noncomputable section

/-! ## The leakage drift lemma (derived from the gate ODE) -/

/--
**Inactive-leakage drift bound.**

Over the active sub-window `[cycleStart j, t]`, the u-channel drift from the
cycle start is bounded by the leak `chiSchedule p j * S.D`.

This is derived *from the ODE* `u_hasDeriv` via the mean-value inequality
(`norm_image_sub_le_of_norm_deriv_le_segment'`).  The per-instant derivative
bound is assembled honestly from:

* `hzu`  — the box content `|z − u| ≤ Dzu` on the window;
* `hgate`— the leak-rate bound `|A · α · bGateU| ≤ K` on the window;

and closed against the leak by the window-length relation `hleak`.

No coarse box radius is used: the bound passes through the genuine gate factor
`A · α · bGateU` and the dual-rail gap `z − u`.
-/
theorem u_window_drift_le_leak
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : VarMuRobustStep M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (sol : DynMovingTargetIteratorSol (Fin d) p sched)
    (s : Fin d) (j : ℕ) (t : ℝ)
    (K Dzu : ℝ)
    -- the active sub-window `[cycleStart j, t]` is an ordered segment inside the
    -- ODE domain
    (hseg : sched.cycleStart j ≤ t)
    (hdom : Set.Icc (sched.cycleStart j) t ⊆ sched.domain)
    -- box content: the dual-rail gap is bounded by `Dzu` on the window
    (hzu : ∀ τ ∈ Set.Icc (sched.cycleStart j) t,
      |sol.z τ s - sol.u τ s| ≤ Dzu)
    (hDzu : 0 ≤ Dzu)
    -- leak rate: the gate factor `A · α · bGateU` is bounded by `K` on the window
    (hgate : ∀ τ ∈ Set.Icc (sched.cycleStart j) t,
      |p.A * sol.α τ * bGateU p.L (sol.μ τ) τ| ≤ K)
    (hK : 0 ≤ K)
    -- window-length / leak-rate closing relation (where the `dynChi` integral
    -- collapse lives)
    (hleak : K * Dzu * (t - sched.cycleStart j) ≤ chiSchedule p j * S.D) :
    |sol.u t s - sol.u (sched.cycleStart j) s| ≤ chiSchedule p j * S.D := by
  set a := sched.cycleStart j with ha
  -- abbreviation for the per-instant velocity
  set v : ℝ → ℝ := fun τ =>
    p.A * sol.α τ * bGateU p.L (sol.μ τ) τ * (sol.z τ s - sol.u τ s) with hv
  -- the function whose drift we measure
  set f : ℝ → ℝ := fun τ => sol.u τ s with hf
  -- per-instant derivative from the ODE, restricted to the window segment
  have hderiv : ∀ x ∈ Set.Icc a t,
      HasDerivWithinAt f (v x) (Set.Icc a t) x := by
    intro x hx
    have hx_dom : x ∈ sched.domain := hdom hx
    have hx_at : HasDerivAt (fun τ => sol.u τ s) (v x) x := by
      simpa [hv] using sol.u_hasDeriv x hx_dom s
    exact hx_at.hasDerivWithinAt
  -- uniform bound `‖v x‖ ≤ K * Dzu` on the window
  have hbound : ∀ x ∈ Set.Ico a t, ‖v x‖ ≤ K * Dzu := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a t := Set.Ico_subset_Icc_self hx
    have hg := hgate x hxIcc
    have hz := hzu x hxIcc
    have he : v x =
        p.A * sol.α x * bGateU p.L (sol.μ x) x * (sol.z x s - sol.u x s) := by
      simp only [hv]
    rw [he, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hg hz (abs_nonneg _) hK
  -- mean-value inequality on the segment
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := f) (f' := v) (C := K * Dzu) hderiv hbound t (Set.right_mem_Icc.mpr hseg)
  -- turn the norm into the absolute value of the drift, then close against the leak
  have hfta : f t - f a = sol.u t s - sol.u a s := by simp only [hf]
  have key : |sol.u t s - sol.u a s| ≤ K * Dzu * (t - a) := by
    rw [← hfta, ← Real.norm_eq_abs]; exact hmvt
  exact le_trans key hleak

/-! ## Triangle assembly to the tracking field shape -/

/--
**Window-hold from the leakage drift.**

Given the leakage drift bound `u_window_drift_le_leak` (as a hypothesis
`hdrift`), the tracking field `hwindow_hold` follows by the triangle inequality
through `u (cycleStart j) s`, because the cycle-start deviation is dominated by
`contractBoundaryError` (a `max` of the z- and u- cycle-start deviations).

This is the exact shape of the `hwindow_hold` field of the contract-tracking
input package (`ContractSchedules.lean:317`).
-/
theorem contract_window_hold_of_leak
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (D : ℝ) (j : ℕ) (t : ℝ) (i : Fin d)
    -- the leakage drift bound (output of `u_window_drift_le_leak`)
    (hdrift :
      |sol.u t i - sol.u (sched.cycleStart j) i| ≤ chiSchedule p j * D) :
    |sol.u t i - E.enc (c j) i| ≤
      contractBoundaryError (E := E) sol c j i + chiSchedule p j * D := by
  -- the cycle-start deviation is dominated by `contractBoundaryError`
  have hcb :
      |sol.u (sched.cycleStart j) i - E.enc (c j) i| ≤
        contractBoundaryError (E := E) sol c j i := by
    unfold contractBoundaryError
    exact le_max_right _ _
  -- triangle through `u (cycleStart j) i`
  have hsplit :
      sol.u t i - E.enc (c j) i =
        (sol.u t i - sol.u (sched.cycleStart j) i) +
          (sol.u (sched.cycleStart j) i - E.enc (c j) i) := by
    ring
  calc
    |sol.u t i - E.enc (c j) i|
        = |(sol.u t i - sol.u (sched.cycleStart j) i) +
            (sol.u (sched.cycleStart j) i - E.enc (c j) i)| := by rw [hsplit]
    _ ≤ |sol.u t i - sol.u (sched.cycleStart j) i| +
          |sol.u (sched.cycleStart j) i - E.enc (c j) i| := abs_add_le _ _
    _ ≤ chiSchedule p j * D + contractBoundaryError (E := E) sol c j i :=
          add_le_add hdrift hcb
    _ = contractBoundaryError (E := E) sol c j i + chiSchedule p j * D := by
          ring

/--
**End-to-end window hold from the ODE.**

Composes `u_window_drift_le_leak` (drift derived from the gate ODE) with
`contract_window_hold_of_leak` (triangle assembly) to produce the field shape
directly from the named ODE/box hypotheses.  This is the honest replacement for
a box-radius `hwindow_hold`: every constant is tied to the gate factor
`A · α · bGateU` and the dual-rail gap `z − u`.
-/
theorem contract_window_hold_of_ode
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : VarMuRobustStep M E)
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (i : Fin d) (j : ℕ) (t : ℝ)
    (K Dzu : ℝ)
    (hseg : sched.cycleStart j ≤ t)
    (hdom : Set.Icc (sched.cycleStart j) t ⊆ sched.domain)
    (hzu : ∀ τ ∈ Set.Icc (sched.cycleStart j) t,
      |sol.z τ i - sol.u τ i| ≤ Dzu)
    (hDzu : 0 ≤ Dzu)
    (hgate : ∀ τ ∈ Set.Icc (sched.cycleStart j) t,
      |p.A * sol.α τ * bGateU p.L (sol.μ τ) τ| ≤ K)
    (hK : 0 ≤ K)
    (hleak : K * Dzu * (t - sched.cycleStart j) ≤ chiSchedule p j * S.D) :
    |sol.u t i - E.enc (c j) i| ≤
      contractBoundaryError (E := E) sol c j i + chiSchedule p j * S.D := by
  have hdrift :=
    u_window_drift_le_leak (S := S) (p := p) (sched := sched)
      (sol := sol.toDynMovingTargetIteratorSol) (s := i) (j := j) (t := t)
      (K := K) (Dzu := Dzu)
      hseg hdom hzu hDzu hgate hK hleak
  exact contract_window_hold_of_leak (sol := sol) (c := c) (D := S.D)
    (j := j) (t := t) (i := i) hdrift

end

end Ripple.BoundedUniversality.BGP
