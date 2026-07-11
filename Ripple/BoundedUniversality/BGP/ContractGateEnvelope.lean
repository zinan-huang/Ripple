/-
Ripple.BoundedUniversality.BGP.ContractGateEnvelope
-------------------------------
Reusable closed forms + gate envelope for the BOX-FREE contract iterator
solution `DynContractIteratorSol`, extracted from the inline derivation inside
`DynamicGate.dyn_perturbation_recurrence` (which is locked to the BOXED
`DynIteratorSol`).  These are the foundation sub-producers for the box-free
window-hold discharge over `bgpSchedulePhys`:

* `contractSol_mu_eq`   : `μ t = init_μ + cμ·t`  (general warm init `init_μ`),
* `contractSol_alpha_eq`: `α t = init_α·exp(cα·t)`,
* `gate_envelope_U/Z`   : on the off-phase half (`sin ≥ 0` for U, `sin ≤ 0` for
  Z) the gate factor `|A·α·bGate|` is bounded by the DECAYING envelope
  `A·init_α·exp(−leakLambda·t)·exp(−init_μ·(1/2)^L)` — the `hgate` witness the
  leak lemma `contract_window_hold_of_ode` needs, with the gate growth of `α`
  fully absorbed by the gate decay.

The warm init enters HERE: a large `init_μ` pre-decays the gate, shrinking the
envelope constant `exp(−init_μ·(1/2)^L)` so it fits the leak budget.
-/

import Ripple.BoundedUniversality.BGP.DynChiLeak
import Ripple.BoundedUniversality.BGP.ContractTracking

namespace Ripple.BoundedUniversality.BGP

open Real
open Ripple.BoundedUniversality.Core

noncomputable section

/-- Local copy of the forward-constancy helper (`DynamicGate`'s is `private`):
if `f' = 0` on `[0,∞)` then `f` is constant there. -/
private theorem fwd_const_of_deriv_zero
    (f : ℝ → ℝ) (hderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt f 0 s)
    (t : ℝ) (ht : 0 ≤ t) : f t = f 0 := by
  have hmono : ∀ (g : ℝ → ℝ), (∀ s : ℝ, 0 ≤ s → HasDerivAt g 0 s) →
      0 ≤ g 0 → 0 ≤ g t := by
    intro g hg h0
    have hm : MonotoneOn g (Set.Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · intro x hx; exact (hg x hx.1).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact ((hg x hx.1.le).differentiableAt).differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hg x hx.1.le).deriv]
    have := hm (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
    linarith
  have h1 : 0 ≤ (fun s => f s - f 0) t := by
    apply hmono (fun s => f s - f 0)
    · intro s hs; simpa using (hderiv s hs).sub_const (f 0)
    · simp
  have h2 : 0 ≤ (fun s => f 0 - f s) t := by
    apply hmono (fun s => f 0 - f s)
    · intro s hs; have := (hderiv s hs).const_sub (f 0); simpa using this
    · simp
  simp only at h1 h2
  linarith

variable {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
  {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}

/-- `μ` is affine on `[0,∞)`: `μ t = init_μ + cμ·t`. -/
theorem contractSol_mu_eq (sol : DynContractIteratorSol (Fin d) p sched F)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    {t : ℝ} (ht : 0 ≤ t) :
    sol.μ t = sol.init_μ + p.cμ * t := by
  have key := fwd_const_of_deriv_zero
    (fun s => sol.μ s - (sol.init_μ + p.cμ * s))
    (fun s hs => by
      have h1 := sol.μ_hasDeriv s (hdom s hs)
      have hb : HasDerivAt (fun τ : ℝ => p.cμ * τ) p.cμ s := by
        simpa using (hasDerivAt_id s).const_mul p.cμ
      have h2 : HasDerivAt (fun τ : ℝ => sol.init_μ + p.cμ * τ) p.cμ s :=
        hb.const_add sol.init_μ
      simpa using h1.sub h2)
    t ht
  have h0 : sol.μ 0 = sol.init_μ := sol.μ_at_zero
  simp only [h0, mul_zero, add_zero, sub_self] at key
  linarith [key]

/-- `α` is exponential on `[0,∞)`: `α t = init_α·exp(cα·t)`. -/
theorem contractSol_alpha_eq (sol : DynContractIteratorSol (Fin d) p sched F)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    {t : ℝ} (ht : 0 ≤ t) :
    sol.α t = sol.init_α * Real.exp (p.cα * t) := by
  have key := fwd_const_of_deriv_zero
    (fun s => sol.α s * Real.exp (-(p.cα * s)))
    (fun s hs => by
      have h1 := sol.α_hasDeriv s (hdom s hs)
      have h2 : HasDerivAt (fun τ : ℝ => Real.exp (-(p.cα * τ)))
          (-(p.cα) * Real.exp (-(p.cα * s))) s := by
        have hin : HasDerivAt (fun τ : ℝ => -(p.cα * τ)) (-(p.cα)) s := by
          simpa using ((hasDerivAt_id s).const_mul p.cα).neg
        have := hin.exp
        convert this using 1; ring
      have h3 := h1.mul h2
      convert h3 using 1; ring)
    t ht
  have h0 : sol.α 0 = sol.init_α := sol.α_at_zero
  simp only [h0, mul_zero, neg_zero, Real.exp_zero, mul_one] at key
  -- key : sol.α t * Real.exp (-(p.cα * t)) = sol.init_α
  have hexp : Real.exp (-(p.cα * t)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hmul : sol.α t * Real.exp (-(p.cα * t)) = sol.init_α := key
  have : sol.α t = sol.init_α * (Real.exp (-(p.cα * t)))⁻¹ := by
    field_simp at hmul ⊢; linarith [hmul]
  rw [this, ← Real.exp_neg]; ring_nf

/-- **U-channel gate envelope.** On the off-phase half (`sin t ≥ 0`), with
`0 ≤ A`, `0 ≤ init_μ`, `0 ≤ init_α`, the gate factor is bounded by the decaying
envelope: `α`'s exponential growth is fully absorbed by `bGateU`'s decay, leaving
`leakLambda = cμ·(1/2)^L − cα`. -/
theorem gate_envelope_U (sol : DynContractIteratorSol (Fin d) p sched F)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hαinit : 0 ≤ sol.init_α)
    (hμinit : 0 ≤ sol.init_μ)
    {t : ℝ} (ht : 0 ≤ t) (hsin : 0 ≤ Real.sin t) :
    |p.A * sol.α t * bGateU p.L (sol.μ t) t| ≤
      p.A * sol.init_α
        * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * t))
        * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L)) := by
  have hα := contractSol_alpha_eq sol hdom ht
  have hμ := contractSol_mu_eq sol hdom ht
  have hμnonneg : 0 ≤ sol.μ t := by
    rw [hμ]; have := mul_nonneg hcμ ht; linarith
  have hgate : bGateU p.L (sol.μ t) t ≤ Real.exp (-(sol.μ t * (1 / 2 : ℝ) ^ p.L)) :=
    bGateU_le_offphase p.L hμnonneg hsin
  have hαpos : 0 ≤ sol.α t := by
    rw [hα]; exact mul_nonneg hαinit (Real.exp_pos _).le
  have hAα : 0 ≤ p.A * sol.α t := mul_nonneg hA hαpos
  have hgate_nonneg : 0 ≤ bGateU p.L (sol.μ t) t := (bGateU_pos p.L (sol.μ t) t).le
  rw [abs_of_nonneg (mul_nonneg hAα hgate_nonneg)]
  calc
    p.A * sol.α t * bGateU p.L (sol.μ t) t
        ≤ p.A * sol.α t * Real.exp (-(sol.μ t * (1 / 2 : ℝ) ^ p.L)) :=
          mul_le_mul_of_nonneg_left hgate hAα
    _ = p.A * sol.init_α
          * (Real.exp (p.cα * t)
              * Real.exp (-((sol.init_μ + p.cμ * t) * (1 / 2 : ℝ) ^ p.L))) := by
          rw [hα, hμ]; ring
    _ = p.A * sol.init_α
          * (Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * t))
              * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))) := by
          congr 1
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          unfold DynChiLeak.leakLambda
          ring
    _ = p.A * sol.init_α
          * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * t))
          * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L)) := by ring

/-- **Z-channel gate envelope.** Mirror of `gate_envelope_U` on the Z-off half
(`sin t ≤ 0`), via `bGateZ_le_offphase`. -/
theorem gate_envelope_Z (sol : DynContractIteratorSol (Fin d) p sched F)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hαinit : 0 ≤ sol.init_α)
    (hμinit : 0 ≤ sol.init_μ)
    {t : ℝ} (ht : 0 ≤ t) (hsin : Real.sin t ≤ 0) :
    |p.A * sol.α t * bGateZ p.L (sol.μ t) t| ≤
      p.A * sol.init_α
        * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * t))
        * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L)) := by
  have hα := contractSol_alpha_eq sol hdom ht
  have hμ := contractSol_mu_eq sol hdom ht
  have hμnonneg : 0 ≤ sol.μ t := by
    rw [hμ]; have := mul_nonneg hcμ ht; linarith
  have hgate : bGateZ p.L (sol.μ t) t ≤ Real.exp (-(sol.μ t * (1 / 2 : ℝ) ^ p.L)) :=
    bGateZ_le_offphase p.L hμnonneg hsin
  have hαpos : 0 ≤ sol.α t := by
    rw [hα]; exact mul_nonneg hαinit (Real.exp_pos _).le
  have hAα : 0 ≤ p.A * sol.α t := mul_nonneg hA hαpos
  have hgate_nonneg : 0 ≤ bGateZ p.L (sol.μ t) t := (bGateZ_pos p.L (sol.μ t) t).le
  rw [abs_of_nonneg (mul_nonneg hAα hgate_nonneg)]
  calc
    p.A * sol.α t * bGateZ p.L (sol.μ t) t
        ≤ p.A * sol.α t * Real.exp (-(sol.μ t * (1 / 2 : ℝ) ^ p.L)) :=
          mul_le_mul_of_nonneg_left hgate hAα
    _ = p.A * sol.init_α
          * (Real.exp (p.cα * t)
              * Real.exp (-((sol.init_μ + p.cμ * t) * (1 / 2 : ℝ) ^ p.L))) := by
          rw [hα, hμ]; ring
    _ = p.A * sol.init_α
          * (Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * t))
              * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))) := by
          congr 1
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          unfold DynChiLeak.leakLambda
          ring
    _ = p.A * sol.init_α
          * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * t))
          * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L)) := by ring

/-- **Off-phase Z-gate integral (leak) bound.**  On a Z-off window (`sin ≤ 0`),
the gate-rate integral `∫ A·α·bGateZ` is bounded by the dynChi-type quantity
`C·exp(−λ·a)/λ` (`C = A·init_α·exp(−init_μ(1/2)^L)`, `λ = leakLambda`) — the decay
that makes the Duhamel moving-target term `δsup·(1−exp(−∫k)) ≤ δsup·∫k` small. -/
theorem gate_integral_offphase_Z
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hαinit : 0 ≤ sol.init_α)
    (hμinit : 0 ≤ sol.init_μ)
    (hlam_pos : 0 < DynChiLeak.leakLambda p.cμ p.cα p.L)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hsin : ∀ τ ∈ Set.Icc a b, Real.sin τ ≤ 0)
    (hcont : Continuous (fun τ => p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ)) :
    (∫ τ in a..b, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ)
      ≤ p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
          * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * a))
          / DynChiLeak.leakLambda p.cμ p.cα p.L := by
  set lam := DynChiLeak.leakLambda p.cμ p.cα p.L with hlamdef
  set C := p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L)) with hCdef
  have hlam0 : lam ≠ 0 := ne_of_gt hlam_pos
  have hCnn : 0 ≤ C := by
    rw [hCdef]; exact mul_nonneg (mul_nonneg hA hαinit) (Real.exp_pos _).le
  -- pointwise envelope: integrand ≤ C·exp(−lam·τ)
  have henv : ∀ τ ∈ Set.Icc a b,
      p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ ≤ C * Real.exp (-(lam * τ)) := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha hτ.1
    have hev := gate_envelope_Z sol hdom hA hcμ hαinit hμinit hτ0 (hsin τ hτ)
    have habs : p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ
        ≤ |p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ| := le_abs_self _
    refine le_trans habs (le_trans hev (le_of_eq ?_))
    rw [hCdef, hlamdef]; ring
  have hexp_cont : Continuous (fun τ : ℝ => C * Real.exp (-(lam * τ))) :=
    continuous_const.mul (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))
  have hint1 : (∫ τ in a..b, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ)
      ≤ ∫ τ in a..b, C * Real.exp (-(lam * τ)) :=
    intervalIntegral.integral_mono_on hab
      (hcont.intervalIntegrable a b) (hexp_cont.intervalIntegrable a b) henv
  -- closed form: ∫ C·exp(−lam·τ) = C·(exp(−lam·a) − exp(−lam·b))/lam
  have hG : ∀ τ : ℝ, HasDerivAt (fun s => -(C / lam) * Real.exp (-(lam * s)))
      (C * Real.exp (-(lam * τ))) τ := by
    intro τ
    have h1 : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) τ := by
      simpa using ((hasDerivAt_id τ).const_mul lam).neg
    have h2 := (h1.exp).const_mul (-(C / lam))
    convert h2 using 1
    field_simp
  have hclosed : (∫ τ in a..b, C * Real.exp (-(lam * τ)))
      = (-(C / lam) * Real.exp (-(lam * b))) - (-(C / lam) * Real.exp (-(lam * a))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hG τ)
      (hexp_cont.intervalIntegrable a b)
  rw [hclosed] at hint1
  refine le_trans hint1 ?_
  have hb0 : 0 ≤ C / lam * Real.exp (-(lam * b)) :=
    mul_nonneg (div_nonneg hCnn hlam_pos.le) (Real.exp_pos _).le
  have heq : C * Real.exp (-(lam * a)) / lam = C / lam * Real.exp (-(lam * a)) := by ring
  rw [heq]
  linarith [hb0]

/-- **Off-phase U-gate integral (leak) bound.**  Mirror of `gate_integral_offphase_Z`
on a U-off window (`0 ≤ sin`), via `gate_envelope_U`. -/
theorem gate_integral_offphase_U
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hαinit : 0 ≤ sol.init_α)
    (hμinit : 0 ≤ sol.init_μ)
    (hlam_pos : 0 < DynChiLeak.leakLambda p.cμ p.cα p.L)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hsin : ∀ τ ∈ Set.Icc a b, 0 ≤ Real.sin τ)
    (hcont : Continuous (fun τ => p.A * sol.α τ * bGateU p.L (sol.μ τ) τ)) :
    (∫ τ in a..b, p.A * sol.α τ * bGateU p.L (sol.μ τ) τ)
      ≤ p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
          * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * a))
          / DynChiLeak.leakLambda p.cμ p.cα p.L := by
  set lam := DynChiLeak.leakLambda p.cμ p.cα p.L with hlamdef
  set C := p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L)) with hCdef
  have hlam0 : lam ≠ 0 := ne_of_gt hlam_pos
  have hCnn : 0 ≤ C := by
    rw [hCdef]; exact mul_nonneg (mul_nonneg hA hαinit) (Real.exp_pos _).le
  have henv : ∀ τ ∈ Set.Icc a b,
      p.A * sol.α τ * bGateU p.L (sol.μ τ) τ ≤ C * Real.exp (-(lam * τ)) := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha hτ.1
    have hev := gate_envelope_U sol hdom hA hcμ hαinit hμinit hτ0 (hsin τ hτ)
    have habs : p.A * sol.α τ * bGateU p.L (sol.μ τ) τ
        ≤ |p.A * sol.α τ * bGateU p.L (sol.μ τ) τ| := le_abs_self _
    refine le_trans habs (le_trans hev (le_of_eq ?_))
    rw [hCdef, hlamdef]; ring
  have hexp_cont : Continuous (fun τ : ℝ => C * Real.exp (-(lam * τ))) :=
    continuous_const.mul (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))
  have hint1 : (∫ τ in a..b, p.A * sol.α τ * bGateU p.L (sol.μ τ) τ)
      ≤ ∫ τ in a..b, C * Real.exp (-(lam * τ)) :=
    intervalIntegral.integral_mono_on hab
      (hcont.intervalIntegrable a b) (hexp_cont.intervalIntegrable a b) henv
  have hG : ∀ τ : ℝ, HasDerivAt (fun s => -(C / lam) * Real.exp (-(lam * s)))
      (C * Real.exp (-(lam * τ))) τ := by
    intro τ
    have h1 : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) τ := by
      simpa using ((hasDerivAt_id τ).const_mul lam).neg
    have h2 := (h1.exp).const_mul (-(C / lam))
    convert h2 using 1
    field_simp
  have hclosed : (∫ τ in a..b, C * Real.exp (-(lam * τ)))
      = (-(C / lam) * Real.exp (-(lam * b))) - (-(C / lam) * Real.exp (-(lam * a))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hG τ)
      (hexp_cont.intervalIntegrable a b)
  rw [hclosed] at hint1
  refine le_trans hint1 ?_
  have hb0 : 0 ≤ C / lam * Real.exp (-(lam * b)) :=
    mul_nonneg (div_nonneg hCnn hlam_pos.le) (Real.exp_pos _).le
  have heq : C * Real.exp (-(lam * a)) / lam = C / lam * Real.exp (-(lam * a)) := by ring
  rw [heq]
  linarith [hb0]

end

end Ripple.BoundedUniversality.BGP
