/-
Ripple.BoundedUniversality.BGP.InactiveLeakageZ
---------------------------
Honest inactive-leakage bound for the **z-channel**: the analytic core of the
tracking field `hz_window_hold`.

This file is the z-channel mirror of `Ripple.BoundedUniversality.BGP.InactiveLeakage`.  Whereas the
u-channel relaxes toward `z` via `bGateU` and the dual-rail gap `z − u`, the
z-channel relaxes toward the **moving target** `w` via `bGateZ` and the gap
`w − z`.  Over the active window the z-channel satisfies (from `z_hasDeriv`)

  `z'(τ) s = A · α(τ) · bGateZ(L, μ(τ), τ) · (w(τ) s − z(τ) s)`,

so by the mean-value inequality the drift from the cycle start is

  `|z(t) s − z(cycleStart j) s| ≤ C · (t − cycleStart j)`,

where `C` is any uniform bound on `|z'|` over `[cycleStart j, t]`.  The genuine
ODE/box content enters through two *named, satisfiable* hypotheses:

* `hwz`  : a box bound `|w τ s − z τ s| ≤ Dwz` on the window
           (the moving-target gap content),
* `hgate`: a bound `|A · α τ · bGateZ L (μ τ) τ| ≤ K` on the window
           (the leak rate, supplied off-phase by the `bGateZ` envelope and the
           α/μ envelope),

together with the window-length/leak-rate closing relation

* `hleak`: `K * Dwz * (t − cycleStart j) ≤ chiSchedule p j * S.D`.

`hleak` is exactly the place where the integral collapse already proved for
`dynChi` lives; we keep it as an explicit hypothesis so that the drift is derived
*honestly* from the ODE, never from a coarse radius, and never reduced to a
wrong-direction surrogate.

The final tracking field `hz_window_hold` then follows by the triangle
inequality through `z (cycleStart j) s`, since
`contractBoundaryError ≥ |z (cycleStart j) s − enc (c j) s|` (it is a `max` whose
*left* argument is the z-deviation).

  `z_window_drift_le_leak`          — drift bound, derived from the ODE (PROVED).
  `contract_z_window_hold_of_leak`  — triangle assembly to the field shape (PROVED).
  `contract_z_window_hold_of_ode`   — end-to-end composition (PROVED).
-/

import Ripple.BoundedUniversality.BGP.InactiveLeakage

namespace Ripple.BoundedUniversality.BGP

open Real
open Ripple.BoundedUniversality.Core

noncomputable section

/-! ## The z-channel leakage drift lemma (derived from the gate ODE) -/

/--
**Inactive-leakage drift bound (z-channel).**

Over the active sub-window `[cycleStart j, t]`, the z-channel drift from the
cycle start is bounded by the leak `chiSchedule p j * S.D`.

This is derived *from the ODE* `z_hasDeriv` via the mean-value inequality
(`norm_image_sub_le_of_norm_deriv_le_segment'`).  The per-instant derivative
bound is assembled honestly from:

* `hwz`  — the moving-target gap content `|w − z| ≤ Dwz` on the window;
* `hgate`— the leak-rate bound `|A · α · bGateZ| ≤ K` on the window;

and closed against the leak by the window-length relation `hleak`.

No coarse box radius is used: the bound passes through the genuine gate factor
`A · α · bGateZ` and the moving-target gap `w − z`.
-/
theorem z_window_drift_le_leak
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : VarMuRobustStep M E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (sol : DynMovingTargetIteratorSol (Fin d) p sched)
    (s : Fin d) (j : ℕ) (t : ℝ)
    (K Dwz : ℝ)
    -- the active sub-window `[cycleStart j, t]` is an ordered segment inside the
    -- ODE domain
    (hseg : sched.cycleStart j ≤ t)
    (hdom : Set.Icc (sched.cycleStart j) t ⊆ sched.domain)
    -- box content: the moving-target gap is bounded by `Dwz` on the window
    (hwz : ∀ τ ∈ Set.Icc (sched.cycleStart j) t,
      |sol.w τ s - sol.z τ s| ≤ Dwz)
    (hDwz : 0 ≤ Dwz)
    -- leak rate: the gate factor `A · α · bGateZ` is bounded by `K` on the window
    (hgate : ∀ τ ∈ Set.Icc (sched.cycleStart j) t,
      |p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ| ≤ K)
    (hK : 0 ≤ K)
    -- window-length / leak-rate closing relation (where the `dynChi` integral
    -- collapse lives)
    (hleak : K * Dwz * (t - sched.cycleStart j) ≤ chiSchedule p j * S.D) :
    |sol.z t s - sol.z (sched.cycleStart j) s| ≤ chiSchedule p j * S.D := by
  set a := sched.cycleStart j with ha
  -- abbreviation for the per-instant velocity
  set v : ℝ → ℝ := fun τ =>
    p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ * (sol.w τ s - sol.z τ s) with hv
  -- the function whose drift we measure
  set f : ℝ → ℝ := fun τ => sol.z τ s with hf
  -- per-instant derivative from the ODE, restricted to the window segment
  have hderiv : ∀ x ∈ Set.Icc a t,
      HasDerivWithinAt f (v x) (Set.Icc a t) x := by
    intro x hx
    have hx_dom : x ∈ sched.domain := hdom hx
    have hx_at : HasDerivAt (fun τ => sol.z τ s) (v x) x := by
      simpa [hv] using sol.z_hasDeriv x hx_dom s
    exact hx_at.hasDerivWithinAt
  -- uniform bound `‖v x‖ ≤ K * Dwz` on the window
  have hbound : ∀ x ∈ Set.Ico a t, ‖v x‖ ≤ K * Dwz := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a t := Set.Ico_subset_Icc_self hx
    have hg := hgate x hxIcc
    have hz := hwz x hxIcc
    have he : v x =
        p.A * sol.α x * bGateZ p.L (sol.μ x) x * (sol.w x s - sol.z x s) := by
      simp only [hv]
    rw [he, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hg hz (abs_nonneg _) hK
  -- mean-value inequality on the segment
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := f) (f' := v) (C := K * Dwz) hderiv hbound t (Set.right_mem_Icc.mpr hseg)
  -- turn the norm into the absolute value of the drift, then close against the leak
  have hfta : f t - f a = sol.z t s - sol.z a s := by simp only [hf]
  have key : |sol.z t s - sol.z a s| ≤ K * Dwz * (t - a) := by
    rw [← hfta, ← Real.norm_eq_abs]; exact hmvt
  exact le_trans key hleak

/-! ## Triangle assembly to the tracking field shape -/

/--
**z-channel window-hold from the leakage drift.**

Given the z-channel leakage drift bound `z_window_drift_le_leak` (as a hypothesis
`hdrift`), the tracking field `hz_window_hold` follows by the triangle inequality
through `z (cycleStart j) s`, because the cycle-start deviation is dominated by
`contractBoundaryError` (a `max` whose *left* argument is the z-cycle-start
deviation).

This is the exact shape of the `hz_window_hold` field of the contract-tracking
input package (`ContractSchedules.lean:323`).
-/
theorem contract_z_window_hold_of_leak
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (D : ℝ) (j : ℕ) (t : ℝ) (i : Fin d)
    -- the leakage drift bound (output of `z_window_drift_le_leak`)
    (hdrift :
      |sol.z t i - sol.z (sched.cycleStart j) i| ≤ chiSchedule p j * D) :
    |sol.z t i - E.enc (c j) i| ≤
      contractBoundaryError (E := E) sol c j i + chiSchedule p j * D := by
  -- the cycle-start deviation is dominated by `contractBoundaryError`
  -- (z-deviation is the LEFT argument of the `max`, hence `le_max_left`)
  have hcb :
      |sol.z (sched.cycleStart j) i - E.enc (c j) i| ≤
        contractBoundaryError (E := E) sol c j i := by
    unfold contractBoundaryError
    exact le_max_left _ _
  -- triangle through `z (cycleStart j) i`
  have hsplit :
      sol.z t i - E.enc (c j) i =
        (sol.z t i - sol.z (sched.cycleStart j) i) +
          (sol.z (sched.cycleStart j) i - E.enc (c j) i) := by
    ring
  calc
    |sol.z t i - E.enc (c j) i|
        = |(sol.z t i - sol.z (sched.cycleStart j) i) +
            (sol.z (sched.cycleStart j) i - E.enc (c j) i)| := by rw [hsplit]
    _ ≤ |sol.z t i - sol.z (sched.cycleStart j) i| +
          |sol.z (sched.cycleStart j) i - E.enc (c j) i| := abs_add_le _ _
    _ ≤ chiSchedule p j * D + contractBoundaryError (E := E) sol c j i :=
          add_le_add hdrift hcb
    _ = contractBoundaryError (E := E) sol c j i + chiSchedule p j * D := by
          ring

/--
**End-to-end z-channel window hold from the ODE.**

Composes `z_window_drift_le_leak` (drift derived from the gate ODE) with
`contract_z_window_hold_of_leak` (triangle assembly) to produce the
`hz_window_hold` field shape directly from the named ODE/box hypotheses.  This is
the honest replacement for a box-radius `hz_window_hold`: every constant is tied
to the gate factor `A · α · bGateZ` and the moving-target gap `w − z`.
-/
theorem contract_z_window_hold_of_ode
    {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {d nS : ℕ} {E : StackMachineEncoding d nS M}
    (S : VarMuRobustStep M E)
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (i : Fin d) (j : ℕ) (t : ℝ)
    (K Dwz : ℝ)
    (hseg : sched.cycleStart j ≤ t)
    (hdom : Set.Icc (sched.cycleStart j) t ⊆ sched.domain)
    (hwz : ∀ τ ∈ Set.Icc (sched.cycleStart j) t,
      |sol.w τ i - sol.z τ i| ≤ Dwz)
    (hDwz : 0 ≤ Dwz)
    (hgate : ∀ τ ∈ Set.Icc (sched.cycleStart j) t,
      |p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ| ≤ K)
    (hK : 0 ≤ K)
    (hleak : K * Dwz * (t - sched.cycleStart j) ≤ chiSchedule p j * S.D) :
    |sol.z t i - E.enc (c j) i| ≤
      contractBoundaryError (E := E) sol c j i + chiSchedule p j * S.D := by
  have hdrift :=
    z_window_drift_le_leak (S := S) (p := p) (sched := sched)
      (sol := sol.toDynMovingTargetIteratorSol) (s := i) (j := j) (t := t)
      (K := K) (Dwz := Dwz)
      hseg hdom hwz hDwz hgate hK hleak
  exact contract_z_window_hold_of_leak (sol := sol) (c := c) (D := S.D)
    (j := j) (t := t) (i := i) hdrift

end

end Ripple.BoundedUniversality.BGP
