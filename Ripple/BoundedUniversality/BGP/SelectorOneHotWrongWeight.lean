import Ripple.BoundedUniversality.BGP.SelectorGateApprox

/-!
Ripple.BoundedUniversality.BGP.SelectorOneHotWrongWeight
-----------------------------------

One-hot wrong-view discharge for the selector gate weights.

The dynamic hypotheses kept here have the same provenance as the gate-approximation
contract: `readout_neg_of_sharp` comes from gate sharpness, `reset_odds` from the reset
window, the unit/box hypotheses from the lambda barriers, and `ΔG → ∞` from the growing
gate integral.  The actual logistic step is discharged by
`logistic_false_bound_perturbed`, not restated.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Filter
open Set
open scoped Topology BigOperators

/-- The per-cycle wrong-view lambda budget:
`ε_λ(j) = (Qa0 + ρb/(1-Lmax)^2*Kint) * exp(-α*ΔG_j)`. -/
def selectorOneHotWrongEps
    (Qa0 ρb Lmax Kint α : ℝ) (ΔG : ℕ → ℝ) : ℕ → ℝ :=
  fun j => (Qa0 + ρb / (1 - Lmax) ^ 2 * Kint) * Real.exp (-α * ΔG j)

theorem selectorOneHotWrongEps_nonneg
    {Qa0 ρb Lmax Kint α : ℝ} {ΔG : ℕ → ℝ}
    (hQa0 : 0 ≤ Qa0) (hρb : 0 ≤ ρb) (hKint : 0 ≤ Kint) :
    ∀ j, 0 ≤ selectorOneHotWrongEps Qa0 ρb Lmax Kint α ΔG j := by
  intro j
  unfold selectorOneHotWrongEps
  apply mul_nonneg
  · exact add_nonneg hQa0 (mul_nonneg (div_nonneg hρb (sq_nonneg _)) hKint)
  · exact (Real.exp_pos _).le

/-- If the accumulated gate gain diverges and the readout margin is positive, then the
wrong-view lambda budget tends to zero. -/
theorem selectorOneHotWrongEps_tendsto_zero
    {Qa0 ρb Lmax Kint α : ℝ} {ΔG : ℕ → ℝ}
    (hα : 0 < α) (hΔG : Tendsto ΔG atTop atTop) :
    Tendsto (selectorOneHotWrongEps Qa0 ρb Lmax Kint α ΔG) atTop (𝓝 0) := by
  have hscaled : Tendsto (fun j : ℕ => α * ΔG j) atTop atTop :=
    hΔG.const_mul_atTop hα
  have hneg : Tendsto (fun j : ℕ => -(α * ΔG j)) atTop atBot :=
    Filter.tendsto_neg_atBot_iff.mpr hscaled
  have hexp : Tendsto (fun j : ℕ => Real.exp (-(α * ΔG j))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hmul : Tendsto
      (fun j : ℕ =>
        (Qa0 + ρb / (1 - Lmax) ^ 2 * Kint) * Real.exp (-(α * ΔG j)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hexp
  change Tendsto
    (fun j : ℕ => (Qa0 + ρb / (1 - Lmax) ^ 2 * Kint) * Real.exp (-α * ΔG j))
    atTop (𝓝 0)
  simpa [neg_mul] using hmul

/-- A linear lower bound on the gate gain is enough to make `ΔG_j` diverge. -/
theorem selectorOneHotDeltaG_tendsto_atTop_of_linear
    {c : ℝ} {ΔG : ℕ → ℝ} (hc : 0 < c)
    (hΔG_linear : ∀ j : ℕ, c * (j : ℝ) ≤ ΔG j) :
    Tendsto ΔG atTop atTop := by
  have hlin : Tendsto (fun j : ℕ => c * (j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hev : (fun j : ℕ => c * (j : ℝ)) ≤ᶠ[atTop] ΔG := by
    filter_upwards with j
    exact hΔG_linear j
  exact Filter.tendsto_atTop_mono' atTop hev hlin

theorem selectorOneHotWrongEps_tendsto_zero_of_linear
    {Qa0 ρb Lmax Kint α c : ℝ} {ΔG : ℕ → ℝ}
    (hα : 0 < α) (hc : 0 < c)
    (hΔG_linear : ∀ j : ℕ, c * (j : ℝ) ≤ ΔG j) :
    Tendsto (selectorOneHotWrongEps Qa0 ρb Lmax Kint α ΔG) atTop (𝓝 0) :=
  selectorOneHotWrongEps_tendsto_zero hα
    (selectorOneHotDeltaG_tendsto_atTop_of_linear hc hΔG_linear)

/-- One gate window, carried ODE form.  This is the direct application of
`logistic_false_bound_perturbed` for a wrong view `v ≠ vstar`. -/
theorem selector_oneHot_wrong_weight_bound_window
    {V : Type*} [Fintype V] [DecidableEq V]
    {a b α Lmax ρb Kint Qa0 : ℝ}
    {r G : ℝ → ℝ} {lam P ρ : V → ℝ → ℝ}
    (vstar v : V) (hv : v ≠ vstar)
    (hab : a ≤ b) (hLmax1 : Lmax < 1)
    (hGcontglob : Continuous G)
    (lam_ode_window : ∀ t ∈ Ico a b,
      HasDerivWithinAt (lam v)
        (r t * P v t * (lam v t * (1 - lam v t)) + ρ v t) (Ici t) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hlamcont : ContinuousOn (lam v) (Icc a b))
    (hr0 : ∀ t ∈ Ico a b, 0 ≤ r t)
    (readout_neg_of_sharp :
      ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, P v t ≤ -α)
    (hunit : ∀ t ∈ Icc a b, 0 < lam v t ∧ lam v t < 1)
    (reset_odds : lam v a / (1 - lam v a) ≤ Qa0)
    (hLub : ∀ t ∈ Icc a b, lam v t ≤ Lmax)
    (hρ_ge : ∀ t ∈ Ico a b, -ρb ≤ ρ v t)
    (hρ_le : ∀ t ∈ Ico a b, ρ v t ≤ ρb)
    (hρb : 0 ≤ ρb)
    (hint : (∫ t in a..b, Real.exp (α * (G t - G a))) ≤ Kint)
    (hKint : 0 ≤ Kint) :
    lam v b ≤ (Qa0 + ρb / (1 - Lmax) ^ 2 * Kint)
      * Real.exp (-α * (G b - G a)) := by
  exact logistic_false_bound_perturbed hab hLmax1 hGcontglob lam_ode_window hGder
    hlamcont hr0 (readout_neg_of_sharp v hv) hunit reset_odds hLub hρ_ge hρ_le
    hρb hint hKint

/-- Per-cycle carried wrapper: a wrong view stays below `ε_λ(j)` on every gate window. -/
theorem selector_oneHot_wrong_weight_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {a b : ℕ → ℝ} {α Lmax ρb Kint Qa0 : ℝ}
    {r G : ℝ → ℝ} {lam P ρ : V → ℝ → ℝ}
    (vstar v : V) (hv : v ≠ vstar)
    (hab : ∀ j, a j ≤ b j) (hLmax1 : Lmax < 1)
    (hGcontglob : Continuous G)
    (lam_ode_window : ∀ j, ∀ t ∈ Ico (a j) (b j),
      HasDerivWithinAt (lam v)
        (r t * P v t * (lam v t * (1 - lam v t)) + ρ v t) (Ici t) t)
    (hGder : ∀ j, ∀ t ∈ Ico (a j) (b j),
      HasDerivWithinAt G (r t) (Ici t) t)
    (hlamcont : ∀ j, ContinuousOn (lam v) (Icc (a j) (b j)))
    (hr0 : ∀ j, ∀ t ∈ Ico (a j) (b j), 0 ≤ r t)
    (readout_neg_of_sharp :
      ∀ j, ∀ v, v ≠ vstar → ∀ t ∈ Ico (a j) (b j), P v t ≤ -α)
    (hunit : ∀ j, ∀ t ∈ Icc (a j) (b j), 0 < lam v t ∧ lam v t < 1)
    (reset_odds : ∀ j, lam v (a j) / (1 - lam v (a j)) ≤ Qa0)
    (hLub : ∀ j, ∀ t ∈ Icc (a j) (b j), lam v t ≤ Lmax)
    (hρ_ge : ∀ j, ∀ t ∈ Ico (a j) (b j), -ρb ≤ ρ v t)
    (hρ_le : ∀ j, ∀ t ∈ Ico (a j) (b j), ρ v t ≤ ρb)
    (hρb : 0 ≤ ρb)
    (hint : ∀ j, (∫ t in a j..b j, Real.exp (α * (G t - G (a j)))) ≤ Kint)
    (hKint : 0 ≤ Kint) :
    ∀ j, lam v (b j) ≤ selectorOneHotWrongEps Qa0 ρb Lmax Kint α
      (fun j => G (b j) - G (a j)) j := by
  intro j
  simpa [selectorOneHotWrongEps] using
    selector_oneHot_wrong_weight_bound_window (vstar := vstar) (v := v) hv
      (hab j) hLmax1 hGcontglob (lam_ode_window j) (hGder j) (hlamcont j)
      (hr0 j) (readout_neg_of_sharp j) (hunit j) (reset_odds j) (hLub j)
      (hρ_ge j) (hρ_le j) hρb (hint j) hKint

/-- `SelectorDynSol` version: the lambda and gain derivative hypotheses are wired from
`sol.lam_hasDeriv` and `sol.G_hasDeriv`; sharpness, reset odds, boxes, and residual bounds
remain explicit contract hypotheses. -/
theorem selectorDyn_oneHot_wrong_weight_bound
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (vstar v : V) (hv : v ≠ vstar)
    {a b : ℕ → ℝ} {α Lmax ρb Kint Qa0 : ℝ}
    (hab : ∀ j, a j ≤ b j) (hLmax1 : Lmax < 1)
    (hdom : ∀ j, ∀ t ∈ Ico (a j) (b j), t ∈ sched.domain)
    (hr0 : ∀ j, ∀ t ∈ Ico (a j) (b j), 0 ≤ chiGate t * gain t)
    (readout_neg_of_sharp :
      ∀ j, ∀ v, v ≠ vstar → ∀ t ∈ Ico (a j) (b j), sol.Pval v t ≤ -α)
    (hunit : ∀ j, ∀ t ∈ Icc (a j) (b j), 0 < sol.lam v t ∧ sol.lam v t < 1)
    (reset_odds : ∀ j, sol.lam v (a j) / (1 - sol.lam v (a j)) ≤ Qa0)
    (hLub : ∀ j, ∀ t ∈ Icc (a j) (b j), sol.lam v t ≤ Lmax)
    (hρ_ge : ∀ j, ∀ t ∈ Ico (a j) (b j),
      -ρb ≤ chiReset t * kappa t * (1 / 2 - sol.lam v t))
    (hρ_le : ∀ j, ∀ t ∈ Ico (a j) (b j),
      chiReset t * kappa t * (1 / 2 - sol.lam v t) ≤ ρb)
    (hρb : 0 ≤ ρb)
    (hint : ∀ j,
      (∫ t in a j..b j, Real.exp (α * (sol.G t - sol.G (a j)))) ≤ Kint)
    (hKint : 0 ≤ Kint) :
    ∀ j, sol.lam v (b j) ≤ selectorOneHotWrongEps Qa0 ρb Lmax Kint α
      (fun j => sol.G (b j) - sol.G (a j)) j := by
  refine selector_oneHot_wrong_weight_bound (vstar := vstar) (v := v)
    (a := a) (b := b) (r := fun t => chiGate t * gain t) (G := sol.G)
    (lam := fun v t => sol.lam v t) (P := sol.Pval)
    (ρ := fun v t => chiReset t * kappa t * (1 / 2 - sol.lam v t))
    hv hab hLmax1 sol.cont_G ?_ ?_ ?_ hr0 readout_neg_of_sharp hunit reset_odds
    hLub hρ_ge hρ_le hρb hint hKint
  · intro j t ht
    have h := (sol.lam_hasDeriv v t (hdom j t ht)).hasDerivWithinAt (s := Ici t)
    convert h using 1
    simp only [SelectorDynSol.Pval]
    ring
  · intro j t ht
    have h := (sol.G_hasDeriv t (hdom j t ht)).hasDerivWithinAt (s := Ici t)
    simpa using h
  · intro _j
    exact (sol.cont_lam v).continuousOn

/-- Packaged endpoint theorem: per-cycle wrong-view bound plus `ε_λ → 0`.  The only
asymptotic input carried here is `ΔG_j → ∞`, supplied upstream by the growing gate integral. -/
theorem selectorDyn_oneHot_wrong_weight_bound_and_tendsto
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (vstar v : V) (hv : v ≠ vstar)
    {a b : ℕ → ℝ} {α Lmax ρb Kint Qa0 : ℝ}
    (hab : ∀ j, a j ≤ b j) (hLmax1 : Lmax < 1)
    (hdom : ∀ j, ∀ t ∈ Ico (a j) (b j), t ∈ sched.domain)
    (hr0 : ∀ j, ∀ t ∈ Ico (a j) (b j), 0 ≤ chiGate t * gain t)
    (readout_neg_of_sharp :
      ∀ j, ∀ v, v ≠ vstar → ∀ t ∈ Ico (a j) (b j), sol.Pval v t ≤ -α)
    (hunit : ∀ j, ∀ t ∈ Icc (a j) (b j), 0 < sol.lam v t ∧ sol.lam v t < 1)
    (reset_odds : ∀ j, sol.lam v (a j) / (1 - sol.lam v (a j)) ≤ Qa0)
    (hLub : ∀ j, ∀ t ∈ Icc (a j) (b j), sol.lam v t ≤ Lmax)
    (hρ_ge : ∀ j, ∀ t ∈ Ico (a j) (b j),
      -ρb ≤ chiReset t * kappa t * (1 / 2 - sol.lam v t))
    (hρ_le : ∀ j, ∀ t ∈ Ico (a j) (b j),
      chiReset t * kappa t * (1 / 2 - sol.lam v t) ≤ ρb)
    (hρb : 0 ≤ ρb)
    (hint : ∀ j,
      (∫ t in a j..b j, Real.exp (α * (sol.G t - sol.G (a j)))) ≤ Kint)
    (hKint : 0 ≤ Kint)
    (hα : 0 < α)
    (hΔG : Tendsto (fun j => sol.G (b j) - sol.G (a j)) atTop atTop) :
    (∀ j, sol.lam v (b j) ≤ selectorOneHotWrongEps Qa0 ρb Lmax Kint α
        (fun j => sol.G (b j) - sol.G (a j)) j) ∧
      Tendsto (selectorOneHotWrongEps Qa0 ρb Lmax Kint α
        (fun j => sol.G (b j) - sol.G (a j))) atTop (𝓝 0) := by
  exact ⟨selectorDyn_oneHot_wrong_weight_bound sol vstar v hv hab hLmax1 hdom hr0
      readout_neg_of_sharp hunit reset_odds hLub hρ_ge hρ_le hρb hint hKint,
    selectorOneHotWrongEps_tendsto_zero hα hΔG⟩

end Ripple.BoundedUniversality.BGP
