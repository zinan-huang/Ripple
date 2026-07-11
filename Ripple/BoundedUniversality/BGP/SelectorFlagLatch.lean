import Ripple.BoundedUniversality.BGP.SelectorZRead

/-!
Ripple.BoundedUniversality.BGP.SelectorFlagLatch
----------------------------
Gap E of the flag-coordinate route: the between-window LATCH.

Past the flag-constancy point `N` the flag target is CONSTANT (`= 1` after halting, `= 0` on a
nonhalting run), so the latch is a z-HOLD toward a constant, not a moving-target tracking problem.
`moving_target_bound` (the Grönwall core, `z' = g·(mixTarget − z)`, `g = A·α·bGateZ ≥ 0`) gives, on
ANY sub-interval `[a,t]`, `|z(t) − b| ≤ exp(−∫g)·|z(a) − b| + δmix ≤ |z(a) − b| + δmix` (since the
gate integral is nonneg, `exp(−∫g) ≤ 1`).  So if `z` starts within `ρ` of the constant flag value `b`
and the mixture stays within `δmix` of `b`, then `z[haltCoord]` stays within `ρ + δmix` of `b` across
the whole interval — the latch.  With `ρ` (the flag-read radius) and `δmix` both `→ 0`, `ρ + δmix < 1/4`
eventually, closing the between-window gap of the eventual-threshold region.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set

/-- **The flag-coordinate hold (latch).**  For the halt coordinate, if `z` starts within `ρ` of a
constant `bc` at `a` and the mixture target stays within `δmix` of `bc` on `[a,b]`, then `z[haltCoord]`
stays within `ρ + δmix` of `bc` on all of `[a,b]`.  (`moving_target_bound` on `[a,t]`, with
`exp(−∫g) ≤ 1` from the nonneg gate integral.)  This extends the per-window flag proximity to the
between-window gap. -/
theorem flag_hold_on_interval
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b bc ρ δmix : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hmix : ∀ t ∈ Icc a b, |selectorMixTarget branch sol.u sol.lam t s - bc| ≤ δmix)
    (hstart : |sol.z a s - bc| ≤ ρ) :
    ∀ t ∈ Icc a b, |sol.z t s - bc| ≤ ρ + δmix := by
  intro t ht
  have hat : a ≤ t := ht.1
  have hsub : ∀ u ∈ Icc a t, u ∈ Icc a b := fun u hu => ⟨hu.1, le_trans hu.2 ht.2⟩
  have hbnd := moving_target_bound
    (fun u => p.A * sol.α u * bGateZ p.L (sol.μ u) u)
    (fun u => selectorMixTarget branch sol.u sol.lam u s)
    (fun u => sol.z u s) a t hat hg_cont
    (fun u hu => hg0 u (hsub u hu))
    (sol.cont_mixTarget s) bc δmix
    (fun u hu => hmix u (hsub u hu))
    (fun u hu => sol.z_hasDeriv u (hdom u (hsub u hu)) s)
  have hint_nonneg : 0 ≤ ∫ u in a..t, p.A * sol.α u * bGateZ p.L (sol.μ u) u :=
    intervalIntegral.integral_nonneg hat (fun u hu => hg0 u (hsub u hu))
  have hexp : Real.exp (-(∫ u in a..t, p.A * sol.α u * bGateZ p.L (sol.μ u) u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hmul : Real.exp (-(∫ u in a..t, p.A * sol.α u * bGateZ p.L (sol.μ u) u)) * |sol.z a s - bc|
      ≤ 1 * ρ :=
    mul_le_mul hexp hstart (abs_nonneg _) zero_le_one
  calc |sol.z t s - bc|
      ≤ Real.exp (-(∫ u in a..t, p.A * sol.α u * bGateZ p.L (sol.μ u) u)) * |sol.z a s - bc| + δmix :=
        hbnd
    _ ≤ 1 * ρ + δmix := by linarith
    _ = ρ + δmix := by ring

/-- **Latch ⟹ region radius on the interval.**  If additionally `ρ + δmix ≤ 1/4`, the held coordinate
is within `1/4` of `bc` on the whole interval — the form the eventual-threshold region assembly
consumes (with `bc` the constant flag value). -/
theorem flag_within_quarter_on_interval
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b bc ρ δmix : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hmix : ∀ t ∈ Icc a b, |selectorMixTarget branch sol.u sol.lam t s - bc| ≤ δmix)
    (hstart : |sol.z a s - bc| ≤ ρ) (hsmall : ρ + δmix ≤ 1 / 4) :
    ∀ t ∈ Icc a b, |sol.z t s - bc| ≤ 1 / 4 := by
  intro t ht
  exact le_trans (flag_hold_on_interval sol s hab hdom hg_cont hg0 hmix hstart t ht) hsmall

end Ripple.BoundedUniversality.BGP
