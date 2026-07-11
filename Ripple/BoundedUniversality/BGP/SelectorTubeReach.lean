import Ripple.BoundedUniversality.BGP.SelectorGateApprox

/-!
Ripple.BoundedUniversality.BGP.SelectorTubeReach
----------------------------
The config-tube Reach facts that discharge the carried `hwin_of_weighted` / `hztube_of_utube`
hypotheses of `selector_MU_flag_read_of_tracking_concrete` from the solution dynamics.

ChatGPT (channel `ac`, 2026-06-15) Q1: the boundary-point → whole-window `UTube` step is PURE
ALGEBRA — triangle inequality + the hold drift, no Grönwall — with one pitfall: from the
WEIGHTED bound `k^dep·boundaryError ≤ Wbound` one must DIVIDE by the positive `k^dep` (which can
be `< 1` when `dep < 0`, `k > 1`), never silently drop it.

This file builds the analytic foundation: `u_hold_window_bound`, the "for all `t ∈ [a,b]`"
version of `u_hold_drift` (which only bounds the endpoint gap `|u b − u a|`).  It follows by
applying `u_hold_drift` on the sub-window `[a,t] ⊆ [a,b]`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set

variable {d B : ℕ} {V : Type} [Fintype V] {p : DynGateParams} {sched : PhaseSchedule}
  {branch : V → BranchData d B} {chiReset chiGate kappa gain : ℝ → ℝ}
  {readoutP : V → (Fin d → ℝ) → ℝ}

/-- **Whole-window hold drift.**  `u_hold_drift` bounds only the endpoint gap
`|u b − u a| ≤ η·(b−a)`.  This upgrades it to a bound at EVERY `t ∈ [a,b]`:
`|u t − u a| ≤ η·(b−a)`, by applying `u_hold_drift` on the sub-window `[a,t]` (whose drift
bound `η·(t−a) ≤ η·(b−a)`).  This is the analytic input for the boundary-point → whole-window
`UTube` step (ChatGPT Q1, step 1). -/
theorem u_hold_window_bound
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b η : ℝ} (hη0 : 0 ≤ η)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hη : ∀ t ∈ Icc a b,
      |p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t s - sol.u t s)| ≤ η) :
    ∀ t ∈ Icc a b, |sol.u t s - sol.u a s| ≤ η * (b - a) := by
  intro t ht
  have htb : t ≤ b := ht.2
  have hdrift : |sol.u t s - sol.u a s| ≤ η * (t - a) :=
    sol.u_hold_drift s ht.1
      (fun u hu => hdom u ⟨hu.1, le_trans hu.2 htb⟩)
      (fun u hu => hη u ⟨hu.1, le_trans hu.2 htb⟩)
  calc |sol.u t s - sol.u a s| ≤ η * (t - a) := hdrift
    _ ≤ η * (b - a) := by
        apply mul_le_mul_of_nonneg_left _ hη0
        linarith [ht.1]

/-- **Weighted boundary error → radius (the `UTube` algebraic core).**  From the WEIGHTED
boundary bound `k^(dep i)·|u_a − enc| ≤ Wbound i` (one coordinate of `MUWeighted`), the hold
drift `|u_t − u_a| ≤ εhold`, and the radius budget `Wbound i / k^(dep i) + εhold ≤ ρ`, conclude
`|u_t − enc| ≤ ρ` (the `UTube` shape).  ChatGPT (ac) Q1 PITFALL: one must DIVIDE the weighted
bound by the POSITIVE `k^(dep i)` (which is `< 1` when `dep i < 0`, `k > 1`), never silently drop
it.  Pure algebra: explicit division + triangle inequality.  Fully abstract (no `MUWeighted`/
`UTube` dependence); the M_U instantiation plugs in `a = 2πj+π/6`, `MUWeighted j`, and the drift
from `u_hold_window_bound`. -/
theorem weighted_boundary_to_radius
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (enc : Fin d → ℝ) {k : ℝ} (hk1 : 1 < k) (dep : Fin d → ℤ) (Wbound : Fin d → ℝ)
    {a t εhold ρ : ℝ}
    (hhold : ∀ i, |sol.u t i - sol.u a i| ≤ εhold)
    (hradius : ∀ i, Wbound i / k ^ dep i + εhold ≤ ρ)
    (hw : ∀ i, k ^ dep i * |sol.u a i - enc i| ≤ Wbound i) :
    ∀ i, |sol.u t i - enc i| ≤ ρ := by
  intro i
  have hkpos : 0 < k ^ dep i := zpow_pos (by linarith : (0 : ℝ) < k) _
  -- divide the weighted bound by the positive `k^(dep i)` (the pitfall)
  have hbd : |sol.u a i - enc i| ≤ Wbound i / k ^ dep i := by
    rw [le_div_iff₀ hkpos]
    calc |sol.u a i - enc i| * k ^ dep i = k ^ dep i * |sol.u a i - enc i| := by ring
      _ ≤ Wbound i := hw i
  have htri : |sol.u t i - enc i| ≤ |sol.u a i - enc i| + |sol.u t i - sol.u a i| := by
    have heq : sol.u t i - enc i = (sol.u a i - enc i) + (sol.u t i - sol.u a i) := by ring
    rw [heq]; exact abs_add_le _ _
  calc |sol.u t i - enc i| ≤ |sol.u a i - enc i| + |sol.u t i - sol.u a i| := htri
    _ ≤ Wbound i / k ^ dep i + εhold := add_le_add hbd (hhold i)
    _ ≤ ρ := hradius i

end Ripple.BoundedUniversality.BGP
