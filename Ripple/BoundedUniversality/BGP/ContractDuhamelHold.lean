/-
Ripple.BoundedUniversality.BGP.ContractDuhamelHold
------------------------------
The CLEAN box-free window-hold reduction via the Duhamel relaxation sup-bound
(`SelectorDuhamelWrite.stack_write_gronwall_sup_bound`), replacing the
leak/gap/off-phase-split apparatus entirely for the dual-rail U-channel.

The `u`-rail solves the relaxation ODE `u' = (A·α·bGateU)·(z − u)`, with rate
`k = A·α·bGateU ≥ 0` (no off-phase needed — `k ≥ 0` always).  The Duhamel
sup-bound gives
  `|u(b) − M| ≤ exp(−∫k)·|u(a) − M| + δsup·(1 − exp(−∫k))`
where `δsup` bounds `|z − M|` over the window.  Since the RHS is a convex
combination of `|u(a) − M|` and `δsup` (both `≤ δsup` when `u` starts inside the
tube), it collapses to `|u(b) − M| ≤ δsup`:

  **the U-window-hold is just the Z-window-hold** (same radius), given `u` starts
  within it.  No dynChi leak, no dual-rail gap `Dzu`, no U-off/Z-off window split.
-/

import Ripple.BoundedUniversality.BGP.SelectorDuhamelWrite
import Ripple.BoundedUniversality.BGP.ContractTracking

namespace Ripple.BoundedUniversality.BGP

open Real
open Ripple.BoundedUniversality.Core

noncomputable section

variable {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
  {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}

/-- The U-channel gate rate `k(τ) = A·α(τ)·bGateU(L, μ(τ), τ)`. -/
def uRate (sol : DynContractIteratorSol (Fin d) p sched F) (τ : ℝ) : ℝ :=
  p.A * sol.α τ * bGateU p.L (sol.μ τ) τ

/-- **Duhamel relaxation sup-bound for the `u`-rail.**  Direct application of
`stack_write_gronwall_sup_bound` to `u' = (A·α·bGateU)·(z − u)`. -/
theorem contract_u_duhamel_bound
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (i : Fin d) (M a b : ℝ) (hab : a ≤ b)
    (hk_cont : Continuous (uRate sol))
    (hA : 0 ≤ p.A) (hαnn : ∀ τ ∈ Set.Icc a b, 0 ≤ sol.α τ)
    (hdom : Set.Icc a b ⊆ sched.domain)
    {δsup : ℝ} (hzsup : ∀ τ ∈ Set.Icc a b, |sol.z τ i - M| ≤ δsup) :
    |sol.u b i - M| ≤
      Real.exp (-(∫ τ in a..b, uRate sol τ)) * |sol.u a i - M| +
        δsup * (1 - Real.exp (-(∫ τ in a..b, uRate sol τ))) := by
  refine stack_write_gronwall_sup_bound
    (fun τ => sol.u τ i) (fun τ => sol.z τ i) (uRate sol) M a b hab
    hk_cont ?_ (sol.cont_z i) ?_ hzsup
  · intro τ hτ
    exact mul_nonneg (mul_nonneg hA (hαnn τ hτ)) (bGateU_pos p.L (sol.μ τ) τ).le
  · intro τ hτ
    have h := sol.u_hasDeriv τ (hdom hτ) i
    have hrw : p.A * sol.α τ * bGateU p.L (sol.μ τ) τ * (sol.z τ i - sol.u τ i)
        = uRate sol τ * (sol.z τ i - sol.u τ i) := by rw [uRate]
    rw [hrw] at h
    exact h

/-- **The U-window-hold IS the Z-window-hold.**  If `u` starts within `δsup` of
the fixed target `M` and `z` stays within `δsup` of `M` over `[a,b]`, then `u`
stays within `δsup` of `M` at `b` — the relaxation cannot push `u` outside the
tube its target lives in.  (No leak, no gap, no off/on-phase split.) -/
theorem contract_u_hold_le
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (i : Fin d) (M a b : ℝ) (hab : a ≤ b)
    (hk_cont : Continuous (uRate sol))
    (hA : 0 ≤ p.A) (hαnn : ∀ τ ∈ Set.Icc a b, 0 ≤ sol.α τ)
    (hdom : Set.Icc a b ⊆ sched.domain)
    {δsup : ℝ}
    (hustart : |sol.u a i - M| ≤ δsup)
    (hzsup : ∀ τ ∈ Set.Icc a b, |sol.z τ i - M| ≤ δsup) :
    |sol.u b i - M| ≤ δsup := by
  have hbound := contract_u_duhamel_bound sol i M a b hab hk_cont hA hαnn hdom hzsup
  have hexp_nonneg : 0 ≤ Real.exp (-(∫ τ in a..b, uRate sol τ)) := (Real.exp_pos _).le
  -- convex combination: exp·|u a−M| + δsup·(1−exp) ≤ exp·δsup + δsup·(1−exp) = δsup
  nlinarith [hbound, hustart, hexp_nonneg]

/-! ## Z-channel mirror: `z` relaxes to the moving target `w = F(μ, u)`. -/

/-- The Z-channel gate rate `k(τ) = A·α(τ)·bGateZ(L, μ(τ), τ)`. -/
def zRate (sol : DynContractIteratorSol (Fin d) p sched F) (τ : ℝ) : ℝ :=
  p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ

/-- **Duhamel relaxation sup-bound for the `z`-rail** (`z' = (A·α·bGateZ)·(w − z)`,
moving target `w`). -/
theorem contract_z_duhamel_bound
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (i : Fin d) (M a b : ℝ) (hab : a ≤ b)
    (hk_cont : Continuous (zRate sol))
    (hA : 0 ≤ p.A) (hαnn : ∀ τ ∈ Set.Icc a b, 0 ≤ sol.α τ)
    (hdom : Set.Icc a b ⊆ sched.domain)
    {δsup : ℝ} (hwsup : ∀ τ ∈ Set.Icc a b, |sol.w τ i - M| ≤ δsup) :
    |sol.z b i - M| ≤
      Real.exp (-(∫ τ in a..b, zRate sol τ)) * |sol.z a i - M| +
        δsup * (1 - Real.exp (-(∫ τ in a..b, zRate sol τ))) := by
  refine stack_write_gronwall_sup_bound
    (fun τ => sol.z τ i) (fun τ => sol.w τ i) (zRate sol) M a b hab
    hk_cont ?_ (sol.cont_w i) ?_ hwsup
  · intro τ hτ
    exact mul_nonneg (mul_nonneg hA (hαnn τ hτ)) (bGateZ_pos p.L (sol.μ τ) τ).le
  · intro τ hτ
    have h := sol.z_hasDeriv τ (hdom hτ) i
    have hrw : p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ * (sol.w τ i - sol.z τ i)
        = zRate sol τ * (sol.w τ i - sol.z τ i) := by rw [zRate]
    rw [hrw] at h
    exact h

/-- **The Z-window-hold IS the field-target hold.**  If `z` starts within `δsup`
of `M` and the moving target `w = F(μ,u)` stays within `δsup` of `M` over
`[a,b]`, then `z` stays within `δsup` of `M` at `b`. -/
theorem contract_z_hold_le
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (i : Fin d) (M a b : ℝ) (hab : a ≤ b)
    (hk_cont : Continuous (zRate sol))
    (hA : 0 ≤ p.A) (hαnn : ∀ τ ∈ Set.Icc a b, 0 ≤ sol.α τ)
    (hdom : Set.Icc a b ⊆ sched.domain)
    {δsup : ℝ}
    (hzstart : |sol.z a i - M| ≤ δsup)
    (hwsup : ∀ τ ∈ Set.Icc a b, |sol.w τ i - M| ≤ δsup) :
    |sol.z b i - M| ≤ δsup := by
  have hbound := contract_z_duhamel_bound sol i M a b hab hk_cont hA hαnn hdom hwsup
  have hexp_nonneg : 0 ≤ Real.exp (-(∫ τ in a..b, zRate sol τ)) := (Real.exp_pos _).le
  nlinarith [hbound, hzstart, hexp_nonneg]

/-! ## Gate-rate continuity (`hk_cont`), from continuity of `α` and `μ`.

For the supply solution these come from `hycont : Continuous y`
(`ContractSupply`): `sol.α = y·(contractAlpha)`, `sol.μ = y·(contractMu)`. -/

theorem uRate_continuous (sol : DynContractIteratorSol (Fin d) p sched F)
    (hcα : Continuous sol.α) (hcμ : Continuous sol.μ) :
    Continuous (uRate sol) := by
  have hq : Continuous (fun t : ℝ => qPulse p.L t) := by
    simp only [qPulse]
    exact ((continuous_const.add Real.continuous_sin).div_const 2).pow p.L
  have hg : Continuous (fun τ => bGateU p.L (sol.μ τ) τ) := by
    simp only [bGateU]
    exact Real.continuous_exp.comp ((hcμ.mul hq).neg)
  unfold uRate
  exact (continuous_const.mul hcα).mul hg

theorem zRate_continuous (sol : DynContractIteratorSol (Fin d) p sched F)
    (hcα : Continuous sol.α) (hcμ : Continuous sol.μ) :
    Continuous (zRate sol) := by
  have hr : Continuous (fun t : ℝ => rPulse p.L t) := by
    simp only [rPulse]
    exact ((continuous_const.sub Real.continuous_sin).div_const 2).pow p.L
  have hg : Continuous (fun τ => bGateZ p.L (sol.μ τ) τ) := by
    simp only [bGateZ]
    exact Real.continuous_exp.comp ((hcμ.mul hr).neg)
  unfold zRate
  exact (continuous_const.mul hcα).mul hg

end

end Ripple.BoundedUniversality.BGP
