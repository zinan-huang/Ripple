import Ripple.BoundedUniversality.BGP.SelectorReplicatorExistence
import Ripple.BoundedUniversality.BGP.SelectorReplicatorBox
import Ripple.BoundedUniversality.BGP.SelectorReplicatorConc
import Ripple.BoundedUniversality.BGP.SelectorCorrectedAssembly
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorHeadline
--------------------------------------
Final integration layer for the simplex-replicator selector solution.

This file is deliberately additive: the original logistic `SelectorDynSol`
headline remains unchanged, while the corrected direct-z readout headline is
restated for the sibling `SelectorReplicatorDynSol`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set MachineInstance

/-! ## Replicator core helpers used by the corrected headline path -/

namespace SelectorReplicatorDynSol

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}

theorem alpha_eq_exp
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain) {t : ℝ} (ht : 0 ≤ t) :
    sol.α t = Real.exp (p.cα * t) := by
  rcases eq_or_lt_of_le ht with h0 | h0
  · rw [← h0]; simp [sol.α_at_zero]
  · set g : ℝ → ℝ := fun s => sol.α s * Real.exp (-(p.cα * s)) with hgdef
    have hgder : ∀ s : ℝ, 0 ≤ s → HasDerivAt g 0 s := by
      intro s hs
      have hα := sol.α_hasDeriv s (hdom s hs)
      have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-(p.cα * τ)))
          (-(p.cα) * Real.exp (-(p.cα * s))) s := by
        have hlin : HasDerivAt (fun τ : ℝ => -(p.cα * τ)) (-(p.cα)) s := by
          simpa using ((hasDerivAt_id s).const_mul (-(p.cα)))
        simpa [mul_comm] using hlin.exp
      have hmul := hα.mul hexp
      rw [hgdef]
      convert hmul using 1
      ring
    have hdiff : DifferentiableOn ℝ g (Icc 0 t) :=
      fun x hx => (hgder x hx.1).differentiableAt.differentiableWithinAt
    have hderivW : ∀ x ∈ Ico 0 t, derivWithin g (Icc 0 t) x = 0 := by
      intro x hx
      have huniq : UniqueDiffWithinAt ℝ (Icc 0 t) x :=
        (uniqueDiffOn_Icc h0) x (Ico_subset_Icc_self hx)
      exact (hgder x hx.1).hasDerivWithinAt.derivWithin huniq
    have hcst := constant_of_derivWithin_zero hdiff hderivW t (right_mem_Icc.mpr ht)
    have hg0 : g 0 = 1 := by simp [hgdef, sol.α_at_zero]
    have hgt : sol.α t * Real.exp (-(p.cα * t)) = 1 := by
      have h := hcst
      rw [hg0] at h
      exact h
    rw [Real.exp_neg, mul_inv_eq_one₀ (Real.exp_ne_zero _)] at hgt
    exact hgt

theorem cont_mixTarget
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) :
    Continuous fun t => selectorMixTarget branch sol.u sol.lam t s := by
  simp only [selectorMixTarget, selectorF]
  refine continuous_finset_sum _ (fun v _ => ?_)
  refine (sol.cont_lam v).mul ?_
  simp only [BranchData.evalBranch, BranchAction.evalReal]
  exact (continuous_const.mul (sol.cont_u s)).add continuous_const

theorem mu_eq_linear
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain) {t : ℝ} (ht : 0 ≤ t) :
    sol.μ t = sol.μ 0 + p.cμ * t := by
  rcases eq_or_lt_of_le ht with h0 | h0
  · rw [← h0]; simp
  · set g : ℝ → ℝ := fun s => sol.μ s - p.cμ * s with hgdef
    have hgder : ∀ s : ℝ, 0 ≤ s → HasDerivAt g 0 s := by
      intro s hs
      have hμ := sol.μ_hasDeriv s (hdom s hs)
      have hlin : HasDerivAt (fun τ : ℝ => p.cμ * τ) p.cμ s := by
        simpa using ((hasDerivAt_id s).const_mul p.cμ)
      have hsub := hμ.sub hlin
      rw [hgdef]
      convert hsub using 1
      ring
    have hdiff : DifferentiableOn ℝ g (Icc 0 t) :=
      fun x hx => (hgder x hx.1).differentiableAt.differentiableWithinAt
    have hderivW : ∀ x ∈ Ico 0 t, derivWithin g (Icc 0 t) x = 0 := by
      intro x hx
      have huniq : UniqueDiffWithinAt ℝ (Icc 0 t) x :=
        (uniqueDiffOn_Icc h0) x (Ico_subset_Icc_self hx)
      exact (hgder x hx.1).hasDerivWithinAt.derivWithin huniq
    have hcst := constant_of_derivWithin_zero hdiff hderivW t (right_mem_Icc.mpr ht)
    have hg0 : g 0 = sol.μ 0 := by simp [hgdef]
    have hgt : sol.μ t - p.cμ * t = sol.μ 0 := by
      have h := hcst
      rw [hg0] at h
      exact h
    linarith [hgt]

end SelectorReplicatorDynSol

/-! ## Replicator versions of the flag-latch/end-to-end path -/

private theorem abs_sub_le_one_of_mem_Icc_zero_one {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |x - y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Replicator z-flag drift from an integral bound on the ODE vector field.

This is the direct `hold_bound_integral` port for `SelectorReplicatorDynSol.z`:
the only analytic input is the interval integral of `|z'|`, with `z'` supplied by
`sol.z_hasDeriv`. -/
theorem flag_drift_bound_on_interval_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b δhold : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hfieldInt : ∀ t ∈ Icc a b,
      (∫ τ in a..t, |p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ *
        (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)|) ≤ δhold) :
    ∀ t ∈ Icc a b, |sol.z t s - sol.z a s| ≤ δhold := by
  intro t ht
  have hat : a ≤ t := ht.1
  let g : ℝ → ℝ := fun τ =>
    p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ *
      (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)
  have hgc : Continuous g := by
    dsimp [g]
    exact hg_cont.mul ((sol.cont_mixTarget s).sub (sol.cont_z s))
  have hderiv : ∀ τ ∈ Icc a t, HasDerivAt (fun ξ => sol.z ξ s) (g τ) τ := by
    intro τ hτ
    have hτab : τ ∈ Icc a b := ⟨hτ.1, le_trans hτ.2 ht.2⟩
    dsimp [g]
    exact sol.z_hasDeriv τ (hdom τ hτab) s
  have hhold := hold_bound_integral (fun τ => sol.z τ s) g a t hat hgc hderiv
  exact le_trans (by simpa [g] using hhold) (hfieldInt t ht)

/-- Sufficient drift producer from the flag box and a bound on the z-gate
integral.  Since both the live mixture target and `z` lie in `[0,1]`, the
forcing gap has absolute value at most `1`, so `∫ |z'|` is bounded by
`∫ A·α·bGateZ`. -/
theorem flag_drift_bound_of_gate_integral_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b δhold : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hmix_box : ∀ t ∈ Icc a b,
      selectorMixTarget branch sol.u sol.lam t s ∈ Icc (0 : ℝ) 1)
    (hz_box : ∀ t ∈ Icc a b, sol.z t s ∈ Icc (0 : ℝ) 1)
    (hgateInt : ∀ t ∈ Icc a b,
      (∫ τ in a..t, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) ≤ δhold) :
    ∀ t ∈ Icc a b, |sol.z t s - sol.z a s| ≤ δhold := by
  refine flag_drift_bound_on_interval_repl sol s hab hdom hg_cont ?_
  intro t ht
  have hat : a ≤ t := ht.1
  have hsub : ∀ τ ∈ Icc a t, τ ∈ Icc a b :=
    fun τ hτ => ⟨hτ.1, le_trans hτ.2 ht.2⟩
  let g : ℝ → ℝ := fun τ =>
    p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ *
      (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)
  have hgc : Continuous g := by
    dsimp [g]
    exact hg_cont.mul ((sol.cont_mixTarget s).sub (sol.cont_z s))
  have hmono :
      (∫ τ in a..t, |g τ|)
        ≤ ∫ τ in a..t, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ := by
    apply intervalIntegral.integral_mono_on hat
    · exact hgc.abs.intervalIntegrable a t
    · exact hg_cont.intervalIntegrable a t
    · intro τ hτ
      have hτab : τ ∈ Icc a b := hsub τ hτ
      have hcoef0 : 0 ≤ p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ := hg0 τ hτab
      have hgap :
          |selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s| ≤ 1 :=
        abs_sub_le_one_of_mem_Icc_zero_one (hmix_box τ hτab) (hz_box τ hτab)
      calc
        |g τ| =
            (p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) *
              |selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s| := by
          dsimp [g]
          rw [abs_mul, abs_of_nonneg hcoef0]
        _ ≤ (p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) * 1 :=
          mul_le_mul_of_nonneg_left hgap hcoef0
        _ = p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ := by ring
  exact le_trans (by simpa [g] using hmono) (hgateInt t ht)

/-- Integral-form drift producer from the flag box and a bound on the z-gate
integral.

This is the field-integral counterpart of
`flag_drift_bound_of_gate_integral_repl`: downstream residuals that already
target the `flag_drift_bound_on_interval_repl` input can consume this directly. -/
theorem flag_fieldIntegral_bound_of_gate_integral_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b δhold : ℝ}
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hmix_box : ∀ t ∈ Icc a b,
      selectorMixTarget branch sol.u sol.lam t s ∈ Icc (0 : ℝ) 1)
    (hz_box : ∀ t ∈ Icc a b, sol.z t s ∈ Icc (0 : ℝ) 1)
    (hgateInt : ∀ t ∈ Icc a b,
      (∫ τ in a..t, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) ≤ δhold) :
    ∀ t ∈ Icc a b,
      (∫ τ in a..t,
        |p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ *
          (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)|) ≤ δhold := by
  intro t ht
  have hsub : ∀ τ ∈ Icc a t, τ ∈ Icc a b :=
    fun τ hτ => ⟨hτ.1, le_trans hτ.2 ht.2⟩
  let g : ℝ → ℝ := fun τ =>
    p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ *
      (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)
  have hgc : Continuous g := by
    dsimp [g]
    exact hg_cont.mul ((sol.cont_mixTarget s).sub (sol.cont_z s))
  have hmono :
      (∫ τ in a..t, |g τ|)
        ≤ ∫ τ in a..t, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ := by
    apply intervalIntegral.integral_mono_on ht.1
    · exact hgc.abs.intervalIntegrable a t
    · exact hg_cont.intervalIntegrable a t
    · intro τ hτ
      have hτab : τ ∈ Icc a b := hsub τ hτ
      have hcoef0 : 0 ≤ p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ := hg0 τ hτab
      have hgap :
          |selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s| ≤ 1 :=
        abs_sub_le_one_of_mem_Icc_zero_one (hmix_box τ hτab) (hz_box τ hτab)
      calc
        |g τ| =
            (p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) *
              |selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s| := by
          dsimp [g]
          rw [abs_mul, abs_of_nonneg hcoef0]
        _ ≤ (p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) * 1 :=
          mul_le_mul_of_nonneg_left hgap hcoef0
        _ = p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ := by ring
  exact le_trans (by simpa [g] using hmono) (hgateInt t ht)

/-- Pointwise offphase envelope for the replicator z-gate integrand.

This is the precise `bGateZ_le_offphase` bridge: on subwindows with
`sin t ≤ 0`, `bGateZ ≤ exp(-(cμ·t·2^{-L}))`, hence
`A·exp(cα t)·bGateZ ≤ A·exp(-((cμ·2^{-L} - cα)t))`. -/
theorem gateZ_integrand_le_offphase_exp_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    {A cμ cα t : ℝ} (ht0 : 0 ≤ t) (hA0 : 0 ≤ A) (hcμ0 : 0 ≤ cμ)
    (hpA : p.A = A)
    (hα : sol.α t = Real.exp (cα * t))
    (hμ : sol.μ t = cμ * t)
    (hsin : Real.sin t ≤ 0) :
    p.A * sol.α t * bGateZ p.L (sol.μ t) t
      ≤ A * Real.exp (-((cμ * (1 / 2) ^ p.L - cα) * t)) := by
  rw [hpA, hα]
  have hgate :
      bGateZ p.L (sol.μ t) t ≤ Real.exp (-(cμ * t * (1 / 2) ^ p.L)) := by
    rw [hμ]
    simpa [mul_assoc] using bGateZ_le_offphase p.L (mul_nonneg hcμ0 ht0) hsin
  have hmul :
      Real.exp (cα * t) * bGateZ p.L (sol.μ t) t
        ≤ Real.exp (cα * t) * Real.exp (-(cμ * t * (1 / 2) ^ p.L)) :=
    mul_le_mul_of_nonneg_left hgate (Real.exp_pos _).le
  have hA_mul := mul_le_mul_of_nonneg_left hmul hA0
  calc
    A * Real.exp (cα * t) * bGateZ p.L (sol.μ t) t
        = A * (Real.exp (cα * t) * bGateZ p.L (sol.μ t) t) := by ring
    _ ≤ A * (Real.exp (cα * t) * Real.exp (-(cμ * t * (1 / 2) ^ p.L))) := hA_mul
    _ = A * Real.exp (-((cμ * (1 / 2) ^ p.L - cα) * t)) := by
      rw [← Real.exp_add]
      ring

/-- Integral offphase envelope for the z-gate on any subinterval where
`sin t ≤ 0`.  This is the reusable producer for the post-write hold subwindows. -/
theorem gateZ_integral_le_offphase_exp_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    {a b A cμ cα : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hA0 : 0 ≤ A) (hcμ0 : 0 ≤ cμ)
    (hpA : p.A = A)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hα : ∀ t ∈ Icc a b, sol.α t = Real.exp (cα * t))
    (hμ : ∀ t ∈ Icc a b, sol.μ t = cμ * t)
    (hsin : ∀ t ∈ Icc a b, Real.sin t ≤ 0) :
    (∫ t in a..b, p.A * sol.α t * bGateZ p.L (sol.μ t) t)
      ≤ ∫ t in a..b, A * Real.exp (-((cμ * (1 / 2) ^ p.L - cα) * t)) := by
  have henv_cont :
      Continuous fun t : ℝ => A * Real.exp (-((cμ * (1 / 2) ^ p.L - cα) * t)) := by
    fun_prop
  apply intervalIntegral.integral_mono_on hab
  · exact hg_cont.intervalIntegrable a b
  · exact henv_cont.intervalIntegrable a b
  · intro t ht
    exact gateZ_integrand_le_offphase_exp_repl sol
      (le_trans ha0 ht.1) hA0 hcμ0 hpA (hα t ht) (hμ t ht) (hsin t ht)

/-- Offphase field-integral producer.

This is the integral-level version of
`flag_drift_bound_of_offphase_envelope_repl`.  It is useful when a downstream
residual already wants the field integral consumed by
`flag_drift_bound_on_interval_repl`. -/
theorem flag_fieldIntegral_bound_of_offphase_envelope_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b A cμ cα δhold : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hA0 : 0 ≤ A) (hcμ0 : 0 ≤ cμ)
    (hpA : p.A = A)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hα : ∀ t ∈ Icc a b, sol.α t = Real.exp (cα * t))
    (hμ : ∀ t ∈ Icc a b, sol.μ t = cμ * t)
    (hsin : ∀ t ∈ Icc a b, Real.sin t ≤ 0)
    (hmix_box : ∀ t ∈ Icc a b,
      selectorMixTarget branch sol.u sol.lam t s ∈ Icc (0 : ℝ) 1)
    (hz_box : ∀ t ∈ Icc a b, sol.z t s ∈ Icc (0 : ℝ) 1)
    (henvInt : ∀ t ∈ Icc a b,
      (∫ τ in a..t, A * Real.exp (-((cμ * (1 / 2) ^ p.L - cα) * τ))) ≤
        δhold) :
    ∀ t ∈ Icc a b,
      (∫ τ in a..t,
        |p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ *
          (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)|) ≤ δhold := by
  intro t ht
  have hat : a ≤ t := ht.1
  have hsub : ∀ τ ∈ Icc a t, τ ∈ Icc a b :=
    fun τ hτ => ⟨hτ.1, le_trans hτ.2 ht.2⟩
  let g : ℝ → ℝ := fun τ =>
    p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ *
      (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)
  have hgc : Continuous g := by
    dsimp [g]
    exact hg_cont.mul ((sol.cont_mixTarget s).sub (sol.cont_z s))
  have hmono :
      (∫ τ in a..t, |g τ|)
        ≤ ∫ τ in a..t, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ := by
    apply intervalIntegral.integral_mono_on hat
    · exact hgc.abs.intervalIntegrable a t
    · exact hg_cont.intervalIntegrable a t
    · intro τ hτ
      have hτab : τ ∈ Icc a b := hsub τ hτ
      have hcoef0 : 0 ≤ p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ := hg0 τ hτab
      have hgap :
          |selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s| ≤ 1 :=
        abs_sub_le_one_of_mem_Icc_zero_one (hmix_box τ hτab) (hz_box τ hτab)
      calc
        |g τ| =
            (p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) *
              |selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s| := by
          dsimp [g]
          rw [abs_mul, abs_of_nonneg hcoef0]
        _ ≤ (p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) * 1 :=
          mul_le_mul_of_nonneg_left hgap hcoef0
        _ = p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ := by ring
  have hgate_le := gateZ_integral_le_offphase_exp_repl sol ht.1 ha0 hA0 hcμ0 hpA
    hg_cont
    (fun τ hτ => hα τ ⟨hτ.1, le_trans hτ.2 ht.2⟩)
    (fun τ hτ => hμ τ ⟨hτ.1, le_trans hτ.2 ht.2⟩)
    (fun τ hτ => hsin τ ⟨hτ.1, le_trans hτ.2 ht.2⟩)
  exact le_trans (by simpa [g] using hmono) (le_trans hgate_le (henvInt t ht))

/-- Offphase drift producer: combine the `[0,1]` flag box, the offphase
`bGateZ_le_offphase` envelope, and a final scalar envelope integral budget. -/
theorem flag_drift_bound_of_offphase_envelope_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b A cμ cα δhold : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hA0 : 0 ≤ A) (hcμ0 : 0 ≤ cμ)
    (hpA : p.A = A)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hα : ∀ t ∈ Icc a b, sol.α t = Real.exp (cα * t))
    (hμ : ∀ t ∈ Icc a b, sol.μ t = cμ * t)
    (hsin : ∀ t ∈ Icc a b, Real.sin t ≤ 0)
    (hmix_box : ∀ t ∈ Icc a b,
      selectorMixTarget branch sol.u sol.lam t s ∈ Icc (0 : ℝ) 1)
    (hz_box : ∀ t ∈ Icc a b, sol.z t s ∈ Icc (0 : ℝ) 1)
    (henvInt : ∀ t ∈ Icc a b,
      (∫ τ in a..t, A * Real.exp (-((cμ * (1 / 2) ^ p.L - cα) * τ))) ≤ δhold) :
    ∀ t ∈ Icc a b, |sol.z t s - sol.z a s| ≤ δhold := by
  refine flag_drift_bound_of_gate_integral_repl sol s hab hdom hg_cont hg0
    hmix_box hz_box ?_
  intro t ht
  have hgate_le := gateZ_integral_le_offphase_exp_repl sol ht.1 ha0 hA0 hcμ0 hpA hg_cont
    (fun τ hτ => hα τ ⟨hτ.1, le_trans hτ.2 ht.2⟩)
    (fun τ hτ => hμ τ ⟨hτ.1, le_trans hτ.2 ht.2⟩)
    (fun τ hτ => hsin τ ⟨hτ.1, le_trans hτ.2 ht.2⟩)
  exact le_trans hgate_le (henvInt t ht)

theorem flag_hold_on_interval_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
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
  have hmul : Real.exp (-(∫ u in a..t, p.A * sol.α u * bGateZ p.L (sol.μ u) u)) *
        |sol.z a s - bc| ≤ 1 * ρ :=
    mul_le_mul hexp hstart (abs_nonneg _) zero_le_one
  calc |sol.z t s - bc|
      ≤ Real.exp (-(∫ u in a..t, p.A * sol.α u * bGateZ p.L (sol.μ u) u)) *
            |sol.z a s - bc| + δmix := hbnd
    _ ≤ 1 * ρ + δmix := by linarith
    _ = ρ + δmix := by ring

/-- Moving-target field-integral producer.

If the mixture target stays within `δmix` of a constant baseline and `z` starts
within `ρ` of the same baseline, then the actual z-field integral is bounded by
`(ρ + 2δmix)` times the z-gate integral budget. -/
theorem flag_fieldIntegral_bound_of_moving_target_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b bc ρ δmix gateCap : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hmix : ∀ t ∈ Icc a b,
      |selectorMixTarget branch sol.u sol.lam t s - bc| ≤ δmix)
    (hstart : |sol.z a s - bc| ≤ ρ)
    (hgateInt : ∀ t ∈ Icc a b,
      (∫ τ in a..t, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) ≤ gateCap) :
    ∀ t ∈ Icc a b,
      (∫ τ in a..t,
        |p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ *
          (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)|) ≤
        (ρ + 2 * δmix) * gateCap := by
  have hhold :=
    flag_hold_on_interval_repl sol s hab hdom hg_cont hg0 hmix hstart
  have hρ0 : 0 ≤ ρ := le_trans (abs_nonneg _) hstart
  have hδ0 : 0 ≤ δmix := by
    exact le_trans (abs_nonneg _) (hmix a ⟨le_rfl, hab⟩)
  have hgap0 : 0 ≤ ρ + 2 * δmix := by linarith
  intro t ht
  have hsub : ∀ τ ∈ Icc a t, τ ∈ Icc a b :=
    fun τ hτ => ⟨hτ.1, le_trans hτ.2 ht.2⟩
  let coef : ℝ → ℝ := fun τ => p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ
  let g : ℝ → ℝ := fun τ =>
    coef τ * (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)
  have hcoef_cont : Continuous coef := by
    simpa [coef] using hg_cont
  have hgc : Continuous g := by
    dsimp [g, coef]
    exact hg_cont.mul ((sol.cont_mixTarget s).sub (sol.cont_z s))
  have hupper_cont : Continuous fun τ => (ρ + 2 * δmix) * coef τ :=
    continuous_const.mul hcoef_cont
  have hmono :
      (∫ τ in a..t, |g τ|)
        ≤ ∫ τ in a..t, (ρ + 2 * δmix) * coef τ := by
    apply intervalIntegral.integral_mono_on ht.1
    · exact hgc.abs.intervalIntegrable a t
    · exact hupper_cont.intervalIntegrable a t
    · intro τ hτ
      have hτab : τ ∈ Icc a b := hsub τ hτ
      have hcoef0 : 0 ≤ coef τ := by
        simpa [coef] using hg0 τ hτab
      have htri :
          |selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s| ≤
            |selectorMixTarget branch sol.u sol.lam τ s - bc| +
              |sol.z τ s - bc| := by
        have htri' :=
          abs_sub_le (selectorMixTarget branch sol.u sol.lam τ s) bc (sol.z τ s)
        simpa [abs_sub_comm (a := bc) (b := sol.z τ s)] using htri'
      have hgap :
          |selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s| ≤
            ρ + 2 * δmix := by
        have hmixτ := hmix τ hτab
        have hzτ := hhold τ hτab
        linarith
      calc
        |g τ| =
            coef τ *
              |selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s| := by
          dsimp [g]
          rw [abs_mul, abs_of_nonneg hcoef0]
        _ ≤ coef τ * (ρ + 2 * δmix) :=
          mul_le_mul_of_nonneg_left hgap hcoef0
        _ = (ρ + 2 * δmix) * coef τ := by ring
  calc
    (∫ τ in a..t,
        |p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ *
          (selectorMixTarget branch sol.u sol.lam τ s - sol.z τ s)|)
        = ∫ τ in a..t, |g τ| := by
          apply intervalIntegral.integral_congr
          intro τ _hτ
          simp [g, coef]
    _ ≤ ∫ τ in a..t, (ρ + 2 * δmix) * coef τ := hmono
    _ = (ρ + 2 * δmix) * ∫ τ in a..t, coef τ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (ρ + 2 * δmix) * gateCap :=
      mul_le_mul_of_nonneg_left (by simpa [coef] using hgateInt t ht) hgap0

theorem flag_within_quarter_on_interval_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b bc ρ δmix : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hmix : ∀ t ∈ Icc a b, |selectorMixTarget branch sol.u sol.lam t s - bc| ≤ δmix)
    (hstart : |sol.z a s - bc| ≤ ρ) (hsmall : ρ + δmix ≤ 1 / 4) :
    ∀ t ∈ Icc a b, |sol.z t s - bc| ≤ 1 / 4 := by
  intro t ht
  exact le_trans (flag_hold_on_interval_repl sol s hab hdom hg_cont hg0 hmix hstart t ht) hsmall

/-- Replicator sibling of `z_after_write_bound`.

This is the honest write-window endpoint form: it controls `z` after a write
against the mixture target frozen at the hold time.  It does not assert that the
mixture itself remains close to the encoded flag over the later reset part. -/
theorem z_after_write_bound_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a m b M δw δzh : ℝ} (ham : a ≤ m)
    (hdom1 : ∀ t ∈ Icc a m, t ∈ sched.domain)
    (hgZ_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hgZ0 : ∀ t ∈ Icc a m, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hstab : ∀ t ∈ Icc a m, |selectorMixTarget branch sol.u sol.lam t s - M| ≤ δw)
    (hzh : ∀ t ∈ Icc m b, |sol.z t s - sol.z m s| ≤ δzh) :
    ∀ t ∈ Icc m b, |sol.z t s - M| ≤
      δzh + (Real.exp (-(∫ τ in a..m, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ))
        * |sol.z a s - M| + δw) := by
  intro t ht
  have hzm := moving_target_bound
    (fun τ => p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ)
    (fun τ => selectorMixTarget branch sol.u sol.lam τ s)
    (fun τ => sol.z τ s) a m ham hgZ_cont hgZ0
    (sol.cont_mixTarget s) M δw hstab
    (fun τ hτ => sol.z_hasDeriv τ (hdom1 τ hτ) s)
  calc |sol.z t s - M| ≤ |sol.z t s - sol.z m s| + |sol.z m s - M| :=
        abs_sub_le _ _ _
    _ ≤ δzh + (Real.exp (-(∫ τ in a..m, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ))
          * |sol.z a s - M| + δw) := add_le_add (hzh t ht) hzm

/-- Hold-only flag transfer for the corrected replicator endpoint.

After the z-write has put the flag coordinate within `ρ` of the constant Boolean
target, it is enough to bound the subsequent drift of `z`; no full-tile mixture
premise is used. -/
theorem flag_within_quarter_on_interval_hold_repl
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b bc ρ δhold : ℝ}
    (hstart : |sol.z a s - bc| ≤ ρ)
    (hhold : ∀ t ∈ Icc a b, |sol.z t s - sol.z a s| ≤ δhold)
    (hsmall : ρ + δhold ≤ 1 / 4) :
    ∀ t ∈ Icc a b, |sol.z t s - bc| ≤ 1 / 4 := by
  intro t ht
  calc |sol.z t s - bc|
      ≤ |sol.z t s - sol.z a s| + |sol.z a s - bc| := abs_sub_le _ _ _
    _ ≤ δhold + ρ := add_le_add (hhold t ht) hstart
    _ = ρ + δhold := by ring
    _ ≤ 1 / 4 := hsmall

theorem selector_correct_halt_endtoend_repl
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δmix : ℕ → ℝ)
    (hdom : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6), t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => pp.A * sol.α t * bGateZ pp.L (sol.μ t) t))
    (hg0 : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      0 ≤ pp.A * sol.α t * bGateZ pp.L (sol.μ t) t)
    (hmix : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |selectorMixTarget branch sol.u sol.lam t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ δmix j)
    (hstart : ∀ (j : ℕ),
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hsmall : ∀ j, ρ j + δmix j ≤ 1 / 4)
    (hbox : ∀ t, 0 ≤ t → sol.z t MachineInstance.haltCoordU ≤ 1) :
    ∃ T : ℝ, ∀ t ≥ T,
      3 / 4 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 := by
  obtain ⟨N, hN⟩ := flag_target_eventually_one_of_halts hw
  apply eventual_region_of_tiled (N := N)
  intro j hjN t ht
  have hab : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6
      ≤ 2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6 := by
    have := Real.pi_pos
    nlinarith
  have hlatch := flag_within_quarter_on_interval_repl sol MachineInstance.haltCoordU
    hab (hdom j) hg_cont (hg0 j) (hmix j) (hstart j) (hsmall j) t ht
  have hone : MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU
      = (1 : ℝ) := by
    rw [hcfg (j + 1)]
    exact hN j hjN
  have ht0 : 0 ≤ t := by
    have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by positivity
    exact le_trans hleft ht.1
  rw [hone] at hlatch
  exact mem_haltRegion_of_flag_one hlatch (hbox t ht0)

theorem selector_correct_nonhalt_endtoend_repl
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : ¬ M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δmix : ℕ → ℝ)
    (hdom : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6), t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => pp.A * sol.α t * bGateZ pp.L (sol.μ t) t))
    (hg0 : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      0 ≤ pp.A * sol.α t * bGateZ pp.L (sol.μ t) t)
    (hmix : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |selectorMixTarget branch sol.u sol.lam t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ δmix j)
    (hstart : ∀ (j : ℕ),
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hsmall : ∀ j, ρ j + δmix j ≤ 1 / 4)
    (hbox : ∀ t, 0 ≤ t → 0 ≤ sol.z t MachineInstance.haltCoordU) :
    ∃ T : ℝ, ∀ t ≥ T,
      0 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 / 4 := by
  apply eventual_region_of_tiled (N := 0)
  intro j _hjN t ht
  have hab : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6
      ≤ 2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6 := by
    have := Real.pi_pos
    nlinarith
  have hlatch := flag_within_quarter_on_interval_repl sol MachineInstance.haltCoordU
    hab (hdom j) hg_cont (hg0 j) (hmix j) (hstart j) (hsmall j) t ht
  have hzero : MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU
      = (0 : ℝ) := by
    rw [hcfg (j + 1)]
    exact flag_target_zero_of_not_halts hw j
  have ht0 : 0 ≤ t := by
    have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by positivity
    exact le_trans hleft ht.1
  rw [hzero] at hlatch
  exact mem_nonhaltRegion_of_flag_zero hlatch (hbox t ht0)

/-- Hold-form halting endpoint for the replicator sibling.

This is the corrected replacement when the mixture estimate is only known at the
z-write/hold time: the full tile is covered by a direct `z`-drift bound. -/
theorem selector_correct_halt_endtoend_hold_repl
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δhold : ℕ → ℝ)
    (hstart : ∀ (j : ℕ),
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hhold : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |sol.z t MachineInstance.haltCoordU
        - sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
            MachineInstance.haltCoordU| ≤ δhold j)
    (hsmall : ∀ j, ρ j + δhold j ≤ 1 / 4)
    (hbox : ∀ t, 0 ≤ t → sol.z t MachineInstance.haltCoordU ≤ 1) :
    ∃ T : ℝ, ∀ t ≥ T,
      3 / 4 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 := by
  obtain ⟨N, hN⟩ := flag_target_eventually_one_of_halts hw
  apply eventual_region_of_tiled (N := N)
  intro j hjN t ht
  have hlatch := flag_within_quarter_on_interval_hold_repl sol MachineInstance.haltCoordU
    (hstart j) (hhold j) (hsmall j) t ht
  have hone : MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU
      = (1 : ℝ) := by
    rw [hcfg (j + 1)]
    exact hN j hjN
  have ht0 : 0 ≤ t := by
    have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by positivity
    exact le_trans hleft ht.1
  rw [hone] at hlatch
  exact mem_haltRegion_of_flag_one hlatch (hbox t ht0)

/-- Hold-form nonhalting endpoint for the replicator sibling. -/
theorem selector_correct_nonhalt_endtoend_hold_repl
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : ¬ M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δhold : ℕ → ℝ)
    (hstart : ∀ (j : ℕ),
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hhold : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      |sol.z t MachineInstance.haltCoordU
        - sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
            MachineInstance.haltCoordU| ≤ δhold j)
    (hsmall : ∀ j, ρ j + δhold j ≤ 1 / 4)
    (hbox : ∀ t, 0 ≤ t → 0 ≤ sol.z t MachineInstance.haltCoordU) :
    ∃ T : ℝ, ∀ t ≥ T,
      0 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 / 4 := by
  apply eventual_region_of_tiled (N := 0)
  intro j _hjN t ht
  have hlatch := flag_within_quarter_on_interval_hold_repl sol MachineInstance.haltCoordU
    (hstart j) (hhold j) (hsmall j) t ht
  have hzero : MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU
      = (0 : ℝ) := by
    rw [hcfg (j + 1)]
    exact flag_target_zero_of_not_halts hw j
  have ht0 : 0 ≤ t := by
    have hleft : 0 ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 := by positivity
    exact le_trans hleft ht.1
  rw [hzero] at hlatch
  exact mem_nonhaltRegion_of_flag_zero hlatch (hbox t ht0)

/-- Hold-form halting endpoint with the `δhold` premise produced from the z-gate
integral and the halt-flag `[0,1]` box.  This discharges the old `hhold`
argument of `selector_correct_halt_endtoend_hold_repl`. -/
theorem selector_correct_halt_endtoend_hold_gate_repl
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δhold : ℕ → ℝ)
    (hdom : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6), t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => pp.A * sol.α t * bGateZ pp.L (sol.μ t) t))
    (hg0 : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      0 ≤ pp.A * sol.α t * bGateZ pp.L (sol.μ t) t)
    (hmix_box : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      selectorMixTarget branch sol.u sol.lam t MachineInstance.haltCoordU ∈ Icc (0 : ℝ) 1)
    (hz_box : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      sol.z t MachineInstance.haltCoordU ∈ Icc (0 : ℝ) 1)
    (hgateInt : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      (∫ τ in (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)..t,
        pp.A * sol.α τ * bGateZ pp.L (sol.μ τ) τ) ≤ δhold j)
    (hstart : ∀ (j : ℕ),
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hsmall : ∀ j, ρ j + δhold j ≤ 1 / 4)
    (hbox : ∀ t, 0 ≤ t → sol.z t MachineInstance.haltCoordU ≤ 1) :
    ∃ T : ℝ, ∀ t ≥ T,
      3 / 4 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 := by
  refine selector_correct_halt_endtoend_hold_repl sol w hw cfg hcfg ρ δhold
    hstart ?_ hsmall hbox
  intro j t ht
  have hab : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6
      ≤ 2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6 := by
    have := Real.pi_pos
    nlinarith
  exact flag_drift_bound_of_gate_integral_repl sol MachineInstance.haltCoordU
    hab (hdom j) hg_cont (hg0 j) (hmix_box j) (hz_box j) (hgateInt j) t ht

/-- Nonhalting sibling of `selector_correct_halt_endtoend_hold_gate_repl`. -/
theorem selector_correct_nonhalt_endtoend_hold_gate_repl
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {pp : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U V pp
      selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (w : ℕ) (hw : ¬ M_U.haltsOn w)
    (cfg : ℕ → MachineInstance.UConf) (hcfg : ∀ j, cfg j = M_U.step^[j] (M_U.init w))
    (ρ δhold : ℕ → ℝ)
    (hdom : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6), t ∈ selectorSchedule.domain)
    (hg_cont : Continuous (fun t => pp.A * sol.α t * bGateZ pp.L (sol.μ t) t))
    (hg0 : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      0 ≤ pp.A * sol.α t * bGateZ pp.L (sol.μ t) t)
    (hmix_box : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      selectorMixTarget branch sol.u sol.lam t MachineInstance.haltCoordU ∈ Icc (0 : ℝ) 1)
    (hz_box : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      sol.z t MachineInstance.haltCoordU ∈ Icc (0 : ℝ) 1)
    (hgateInt : ∀ (j : ℕ), ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6),
      (∫ τ in (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)..t,
        pp.A * sol.α τ * bGateZ pp.L (sol.μ τ) τ) ≤ δhold j)
    (hstart : ∀ (j : ℕ),
      |sol.z (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1))
            MachineInstance.haltCoordU| ≤ ρ j)
    (hsmall : ∀ j, ρ j + δhold j ≤ 1 / 4)
    (hbox : ∀ t, 0 ≤ t → 0 ≤ sol.z t MachineInstance.haltCoordU) :
    ∃ T : ℝ, ∀ t ≥ T,
      0 ≤ sol.z t MachineInstance.haltCoordU ∧
        sol.z t MachineInstance.haltCoordU ≤ 1 / 4 := by
  refine selector_correct_nonhalt_endtoend_hold_repl sol w hw cfg hcfg ρ δhold
    hstart ?_ hsmall hbox
  intro j t ht
  have hab : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6
      ≤ 2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6 := by
    have := Real.pi_pos
    nlinarith
  exact flag_drift_bound_of_gate_integral_repl sol MachineInstance.haltCoordU
    hab (hdom j) hg_cont (hg0 j) (hmix_box j) (hz_box j) (hgateInt j) t ht

/-! ## Forward flag box for `SelectorReplicatorDynSol` -/

/- The exterior z-barrier proof is independent of the selector-weight ODE.  This
replicator sibling is the same argument as
`selectorDynSol_flag_box_of_mixTarget_haltCoord_mem_Icc`, with the solution type
changed. -/
theorem selectorDynSol_flag_box_of_mixTarget_haltCoord_mem_Icc_repl
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
      MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M)
      (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hz0 : sol.z 0 MachineInstance.haltCoordU ∈ Icc (0 : ℝ) 1)
    (hmix : ∀ t : ℝ, 0 ≤ t →
      selectorMixTarget MachineInstance.branchU sol.u sol.lam t
          MachineInstance.haltCoordU ∈ Icc (0 : ℝ) 1) :
    (∀ t : ℝ, 0 ≤ t → sol.z t MachineInstance.haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ sol.z t MachineInstance.haltCoordU) := by
  constructor
  · intro T hT
    have hupper := Ripple.scalar_upper_barrier_exterior_on_Icc
      (T := T) (b := (1 : ℝ)) hT
      (fun t : ℝ => sol.z t MachineInstance.haltCoordU)
      (fun t : ℝ =>
        bgpParams38.A * sol.α t *
          bGateZ bgpParams38.L (sol.μ t) t *
            (selectorMixTarget MachineInstance.branchU sol.u sol.lam t
              MachineInstance.haltCoordU - sol.z t MachineInstance.haltCoordU))
      hz0.2
      ((sol.cont_z MachineInstance.haltCoordU).continuousOn)
      (fun t ht =>
        (sol.z_hasDeriv t
          (selectorSchedule_domain_of_nonneg_box t ht.1)
          MachineInstance.haltCoordU).hasDerivWithinAt)
      (fun t ht _hwall => by
        have hcoef :
            0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
          have halpha :
              sol.α t = Real.exp (bgpParams38.cα * t) :=
            sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_box ht.1
          rw [halpha]
          exact mul_nonneg (mul_nonneg (by norm_num [bgpParams38])
            (Real.exp_pos _).le) (bGateZ_pos bgpParams38.L (sol.μ t) t).le
        have hdiff :
            selectorMixTarget MachineInstance.branchU sol.u sol.lam t
                MachineInstance.haltCoordU -
              sol.z t MachineInstance.haltCoordU ≤ 0 := by
          linarith [(hmix t ht.1).2]
        exact mul_nonpos_of_nonneg_of_nonpos hcoef hdiff)
    exact hupper T (right_mem_Icc.mpr hT)
  · intro T hT
    have hlower := Ripple.scalar_lower_barrier_exterior_on_Icc
      (T := T) (a := (0 : ℝ)) hT
      (fun t : ℝ => sol.z t MachineInstance.haltCoordU)
      (fun t : ℝ =>
        bgpParams38.A * sol.α t *
          bGateZ bgpParams38.L (sol.μ t) t *
            (selectorMixTarget MachineInstance.branchU sol.u sol.lam t
              MachineInstance.haltCoordU - sol.z t MachineInstance.haltCoordU))
      hz0.1
      ((sol.cont_z MachineInstance.haltCoordU).continuousOn)
      (fun t ht =>
        (sol.z_hasDeriv t
          (selectorSchedule_domain_of_nonneg_box t ht.1)
          MachineInstance.haltCoordU).hasDerivWithinAt)
      (fun t ht _hwall => by
        have hcoef :
            0 ≤ bgpParams38.A * sol.α t * bGateZ bgpParams38.L (sol.μ t) t := by
          have halpha :
              sol.α t = Real.exp (bgpParams38.cα * t) :=
            sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_box ht.1
          rw [halpha]
          exact mul_nonneg (mul_nonneg (by norm_num [bgpParams38])
            (Real.exp_pos _).le) (bGateZ_pos bgpParams38.L (sol.μ t) t).le
        have hdiff :
            0 ≤ selectorMixTarget MachineInstance.branchU sol.u sol.lam t
                MachineInstance.haltCoordU -
              sol.z t MachineInstance.haltCoordU := by
          linarith [(hmix t ht.1).1]
        exact mul_nonneg hcoef hdiff)
    exact hlower T (right_mem_Icc.mpr hT)

theorem selector_replicator_flag_box_on_nonneg_repl
    {eta : ℚ} {heta : 0 < eta} {M : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
      MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M)
      (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hcr_cont :
      Continuous fun t : ℝ => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
    (hcg_cont :
      Continuous fun t : ℝ =>
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
    (hP_cont : ∀ v : MachineInstance.UniversalLocalView,
      Continuous fun t : ℝ => universalPval eta heta v (sol.u t))
    (hcr_nonneg :
      ∀ t : ℝ, 0 ≤ ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
    (hlam_sum0 : (∑ v : MachineInstance.UniversalLocalView, sol.lam v 0) = 1)
    (hlam_init_nonneg :
      ∀ v : MachineInstance.UniversalLocalView, 0 ≤ sol.lam v 0)
    (hz0 : sol.z 0 MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1) :
    (∀ t : ℝ, 0 ≤ t → sol.z t MachineInstance.haltCoordU ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ sol.z t MachineInstance.haltCoordU) := by
  classical
  haveI : Nonempty MachineInstance.UniversalLocalView := ⟨MachineInstance.defaultLocalViewU⟩
  have hode : ∀ v : MachineInstance.UniversalLocalView, ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (sol.lam v)
          ((((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ)) *
              (1 / (Fintype.card MachineInstance.UniversalLocalView : ℝ) - sol.lam v t)
            + (((1 + Real.sin t) / 2) ^ M *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t))) *
              sol.lam v t *
                (universalPval eta heta v (sol.u t)
                  - ∑ w : MachineInstance.UniversalLocalView,
                      sol.lam w t * universalPval eta heta w (sol.u t))) t := by
    intro v t ht
    simpa [selectorSchedule] using sol.lam_hasDeriv v t (by simpa [selectorSchedule] using ht)
  have hsum :
      ∀ t : ℝ, 0 ≤ t →
        (∑ v : MachineInstance.UniversalLocalView, sol.lam v t) = 1 :=
    replicator_sum_lam_eq_one
      (lam := fun v t => sol.lam v t)
      (P := fun v t => universalPval eta heta v (sol.u t))
      (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      hcr_cont hcg_cont
      (fun v => sol.cont_lam v)
      hP_cont hode hlam_sum0
  have hlam_nonneg_forward :
      ∀ v : MachineInstance.UniversalLocalView, ∀ t : ℝ, 0 ≤ t → 0 ≤ sol.lam v t :=
    replicator_lam_nonneg
      (lam := fun v t => sol.lam v t)
      (P := fun v t => universalPval eta heta v (sol.u t))
      (cr := fun t => ((1 + Real.cos t) / 2) ^ M * (κ₀ : ℝ))
      (cg := fun t =>
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * t)))
      hcr_cont hcg_cont
      (fun v => sol.cont_lam v)
      hP_cont hcr_nonneg hode hlam_init_nonneg
  have hmix : ∀ t : ℝ, 0 ≤ t →
      selectorMixTarget MachineInstance.branchU sol.u sol.lam t
          MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
      sol.u sol.lam t
      (fun v => hlam_nonneg_forward v t ht)
      (hsum t ht)
  exact selectorDynSol_flag_box_of_mixTarget_haltCoord_mem_Icc_repl sol hz0 hmix

#print axioms selector_correct_halt_endtoend_repl
#print axioms selector_correct_nonhalt_endtoend_repl
#print axioms SelectorReplicatorDynSol.mu_eq_linear
#print axioms flag_drift_bound_on_interval_repl
#print axioms flag_drift_bound_of_gate_integral_repl
#print axioms flag_fieldIntegral_bound_of_gate_integral_repl
#print axioms flag_fieldIntegral_bound_of_moving_target_repl
#print axioms gateZ_integrand_le_offphase_exp_repl
#print axioms gateZ_integral_le_offphase_exp_repl
#print axioms flag_fieldIntegral_bound_of_offphase_envelope_repl
#print axioms flag_drift_bound_of_offphase_envelope_repl
#print axioms z_after_write_bound_repl
#print axioms selector_correct_halt_endtoend_hold_repl
#print axioms selector_correct_nonhalt_endtoend_hold_repl
#print axioms selector_correct_halt_endtoend_hold_gate_repl
#print axioms selector_correct_nonhalt_endtoend_hold_gate_repl
#print axioms selector_replicator_flag_box_on_nonneg_repl

end Ripple.BoundedUniversality.BGP
