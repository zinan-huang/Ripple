import Ripple.BoundedUniversality.BGP.SelectorCycle
import Ripple.BoundedUniversality.BGP.ContractTracking

/-!
Ripple.BoundedUniversality.BGP.SelectorDyn
----------------------
Heterogeneous iterator solution for the clock-driven selector cycle (W1).

Design source: `notes/gpt-clock-driven-selector-r2.md` §6 and
`HANDOFF/fin3-f-wiring-spec.md`.  The companion route does not compose, so the
config and selector dynamics live in ONE solution object with per-group ODEs:

* config `z` reaches the DYNAMIC branch mixture `∑_v λ_v · A_v(u)` (Reach),
* config `u` holds `z`,
* selector weights `λ_v` follow the reset+gate logistic field,
* integrated gain `G' = χ_gate · gain`.

The mixture target reads BOTH the held config `u` (branch values) and the
selector state `λ_v` (weights) — this coupling is exactly what `DynContractIteratorSol`'s
`F(μ,u)` signature cannot express, forcing this dedicated structure.

This file defines the solution structure (W1) and the readout helpers.  The
per-cycle bounds (gate-window mix error via `selector_mix_error_reset`,
reset-window error via `reset_to_half_bound`, config Reach, then
`selector_cycle_step_error`) are the next assembly layer.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set

/-- The dynamic branch mixture target for the config Reach: weighted by the live
selector state `λ_v(t)`, with branch values read off the held config `u(t)`. -/
def selectorMixTarget {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) (u : ℝ → Fin d → ℝ) (lam : V → ℝ → ℝ)
    (t : ℝ) (s : Fin d) : ℝ :=
  selectorF branch (u t) (fun v => lam v t) s

/-- Heterogeneous iterator solution: config (`z`,`u`) + selector weights `λ_v` +
integrated gain `G`, over a shared phase clock `μ`,`α`.  Phase envelopes
`χ_reset`,`χ_gate` (functions of time, realised by clock polynomials) select the
reset vs gate behaviour of the `λ_v` field; `Pval v` is the coarse-margin readout
`Λ_N(v) - 1/2` evaluated along the held config. -/
structure SelectorDynSol
    (d B : ℕ) (V : Type) [Fintype V]
    (p : DynGateParams) (sched : PhaseSchedule)
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gain : ℝ → ℝ) (readoutP : V → (Fin d → ℝ) → ℝ) where
  z : ℝ → Fin d → ℝ
  u : ℝ → Fin d → ℝ
  lam : V → ℝ → ℝ
  G : ℝ → ℝ
  μ : ℝ → ℝ
  α : ℝ → ℝ
  init_z : Fin d → ℝ
  init_u : Fin d → ℝ
  z_at_zero : z 0 = init_z
  u_at_zero : u 0 = init_u
  /-- The precision coordinate starts at `1` (input-independent), so it solves
  `α' = cα·α`, `α 0 = 1` deterministically — pinning `α t = exp(cα·t)` for all sols of
  this type (see `SelectorDynSol.alpha_eq_exp`).  This makes the gate gain
  `gainF = g₀·α` an input-independent function, as the field package requires. -/
  α_at_zero : α 0 = 1
  /-- The dynamic-gate phase starts at `0`, so with `μ' = cμ` it is linear. -/
  μ_at_zero : μ 0 = 0
  cont_z : ∀ s, Continuous fun t => z t s
  cont_u : ∀ s, Continuous fun t => u t s
  cont_lam : ∀ v, Continuous (lam v)
  cont_G : Continuous G
  /-- Config Reach toward the dynamic mixture `∑_v λ_v · A_v(u)`. -/
  z_hasDeriv : ∀ t ∈ sched.domain, ∀ s : Fin d,
    HasDerivAt (fun τ => z τ s)
      (p.A * α t * bGateZ p.L (μ t) t *
        (selectorMixTarget branch u lam t s - z t s)) t
  /-- Config hold: `u` tracks `z`. -/
  u_hasDeriv : ∀ t ∈ sched.domain, ∀ s : Fin d,
    HasDerivAt (fun τ => u τ s)
      (p.A * α t * bGateU p.L (μ t) t * (z t s - u t s)) t
  /-- Selector weight `λ_v` follows the reset+gate logistic field. -/
  lam_hasDeriv : ∀ v, ∀ t ∈ sched.domain,
    HasDerivAt (lam v)
      (chiReset t * kappa t * (1 / 2 - lam v t)
        + chiGate t * (gain t * readoutP v (u t) * (lam v t * (1 - lam v t)))) t
  /-- Integrated gain accumulates only during the gate phase. -/
  G_hasDeriv : ∀ t ∈ sched.domain,
    HasDerivAt G (chiGate t * gain t) t
  μ_hasDeriv : ∀ t ∈ sched.domain, HasDerivAt μ p.cμ t
  α_hasDeriv : ∀ t ∈ sched.domain, HasDerivAt α (p.cα * α t) t

/-- Derived margin readout as a time-function: `readoutP` evaluated along the held
config `u`.  Defeq to `readoutP v (sol.u t)`, so `sol.Pval v t = readoutP v (sol.u t)`
holds by `rfl`.  Downstream code keeps using `sol.Pval v t`. -/
def SelectorDynSol.Pval {d B : ℕ} {V : Type} [Fintype V]
    {p sched branch chiReset chiGate kappa gain readoutP}
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (v : V) (t : ℝ) : ℝ :=
  readoutP v (sol.u t)

namespace SelectorDynSol

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}

/-- Finite-horizon, coordinatewise bound for the selector config registers. -/
def ZUFiniteCoordBound
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ M : ℝ, 0 < M ∧
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin d,
      |sol.z t i| ≤ M ∧ |sol.u t i| ≤ M

/-- **The precision coordinate is the deterministic exponential.**  From `α 0 = 1`
(`α_at_zero`) and the autonomous ODE `α' = cα·α` (`α_hasDeriv` on the domain),
`α t = exp(cα·t)` for every `t ≥ 0` — input-independent.  Proof: the integrating
factor `g s = α s · exp(−cα·s)` has derivative `0` on `[0,t]`, so it is constant
`= g 0 = 1`.  This pins the gate gain `gainF = g₀·α` to the fixed function
`g₀·exp(cα·t)`, which the field package's realization requires. -/
theorem alpha_eq_exp
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain) {t : ℝ} (ht : 0 ≤ t) :
    sol.α t = Real.exp (p.cα * t) := by
  rcases eq_or_lt_of_le ht with h0 | h0
  · rw [← h0]; simp [sol.α_at_zero]
  · set g : ℝ → ℝ := fun s => sol.α s * Real.exp (-(p.cα * s)) with hgdef
    have hgder : ∀ s : ℝ, 0 ≤ s → HasDerivAt g 0 s := by
      intro s hs
      have hα := sol.α_hasDeriv s (hdom s hs)
      have hneg : HasDerivAt (fun τ : ℝ => -(p.cα * τ)) (-(p.cα)) s := by
        simpa using (((hasDerivAt_id s).const_mul p.cα).neg)
      have hprod := hα.mul hneg.exp
      rw [hgdef]
      convert hprod using 1
      ring
    have hdiff : DifferentiableOn ℝ g (Set.Icc 0 t) :=
      fun x hx => (hgder x hx.1).differentiableAt.differentiableWithinAt
    have hderivW : ∀ x ∈ Set.Ico 0 t, derivWithin g (Set.Icc 0 t) x = 0 := by
      intro x hx
      have huniq : UniqueDiffWithinAt ℝ (Set.Icc 0 t) x :=
        (uniqueDiffOn_Icc h0) x (Set.Ico_subset_Icc_self hx)
      exact (hgder x hx.1).hasDerivWithinAt.derivWithin huniq
    have hcst := constant_of_derivWithin_zero hdiff hderivW t (Set.right_mem_Icc.mpr ht)
    have hg0 : g 0 = 1 := by simp [hgdef, sol.α_at_zero]
    have hgt : sol.α t * Real.exp (-(p.cα * t)) = 1 := by
      have h := hcst; rw [hg0] at h; exact h
    rw [Real.exp_neg, mul_inv_eq_one₀ (Real.exp_ne_zero _)] at hgt
    exact hgt

/-- **The clock phase is linear in time.**  From `μ' = cμ` (`μ_hasDeriv`), `μ t = μ 0 + cμ·t`
for `t ≥ 0` (integrating the constant derivative; integrating-factor `g s = μ s − cμ·s` has
derivative `0`).  With the clock init `μ 0 = 0` (carried as a solution fact) this gives `μ t = cμ·t`
— used to bound the config gates `bGateZ/bGateU = exp(−μ·{r,q}Pulse)` (the u-channel is suppressed
on the gate window since `cμ·qPulse > cα`). -/
theorem mu_eq_linear
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
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
    have hdiff : DifferentiableOn ℝ g (Set.Icc 0 t) :=
      fun x hx => (hgder x hx.1).differentiableAt.differentiableWithinAt
    have hderivW : ∀ x ∈ Set.Ico 0 t, derivWithin g (Set.Icc 0 t) x = 0 := by
      intro x hx
      have huniq : UniqueDiffWithinAt ℝ (Set.Icc 0 t) x :=
        (uniqueDiffOn_Icc h0) x (Set.Ico_subset_Icc_self hx)
      exact (hgder x hx.1).hasDerivWithinAt.derivWithin huniq
    have hcst := constant_of_derivWithin_zero hdiff hderivW t (Set.right_mem_Icc.mpr ht)
    have hg0 : g 0 = sol.μ 0 := by simp [hgdef]
    have hgt : sol.μ t - p.cμ * t = sol.μ 0 := by
      have h := hcst; rw [hg0] at h; exact h
    linarith [hgt]

/-- On the gate window (`χ_reset = 0`, `χ_gate = 1`) the `λ_v` ODE is the pure
logistic gate field `gain · P_v · λ_v(1 - λ_v)` — the hypothesis form consumed by
`selector_mix_error_reset`. -/
theorem lam_gate_hasDeriv
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (v : V) {t : ℝ} (ht : t ∈ sched.domain)
    (hreset0 : chiReset t = 0) (hgate1 : chiGate t = 1) :
    HasDerivAt (sol.lam v)
      (gain t * sol.Pval v t * (sol.lam v t * (1 - sol.lam v t))) t := by
  have h := sol.lam_hasDeriv v t ht
  rw [hreset0, hgate1] at h
  convert h using 1
  simp only [SelectorDynSol.Pval]
  ring

/-- On the reset window (`χ_reset = 1`, `χ_gate = 0`) the `λ_v` ODE is the Reach
field `κ · (1/2 - λ_v)` — the hypothesis form consumed by `reset_to_half_bound`. -/
theorem lam_reset_hasDeriv
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (v : V) {t : ℝ} (ht : t ∈ sched.domain)
    (hreset1 : chiReset t = 1) (hgate0 : chiGate t = 0) :
    HasDerivAt (sol.lam v) (kappa t * (1 / 2 - sol.lam v t)) t := by
  have h := sol.lam_hasDeriv v t ht
  rw [hreset1, hgate0] at h
  convert h using 1
  ring

/-- On the gate window the gain ODE is `G' = gain`. -/
theorem G_gate_hasDeriv
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    {t : ℝ} (ht : t ∈ sched.domain) (hgate1 : chiGate t = 1) :
    HasDerivAt sol.G (gain t) t := by
  have h := sol.G_hasDeriv t ht
  rw [hgate1] at h
  simpa using h

/-- **(W3) reset-window error.** Over a reset window `[a,b]` (`χ_reset = 1`,
`χ_gate = 0`) the weight `λ_v` contracts toward `1/2`:
`|λ_v(b) - 1/2| ≤ (1/2)·exp(-∫_a^b κ)`.  This is the reset error `δ_reset` fed to
the gate-window mix error. -/
theorem reset_error
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (v : V) {a b : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hreset1 : ∀ t ∈ Icc a b, chiReset t = 1)
    (hgate0 : ∀ t ∈ Icc a b, chiGate t = 0)
    (hkappa_cont : Continuous kappa) (hkappa0 : ∀ t ∈ Icc a b, 0 ≤ kappa t)
    (hunit0 : 0 ≤ sol.lam v a ∧ sol.lam v a ≤ 1) :
    |sol.lam v b - 1 / 2| ≤ Real.exp (-(∫ t in a..b, kappa t)) * (1 / 2) :=
  reset_to_half_bound_unit (sol.lam v) kappa a b hab hkappa_cont hkappa0
    (fun t ht => sol.lam_reset_hasDeriv v (hdom t ht) (hreset1 t ht) (hgate0 t ht)) hunit0

/-- **(W3) gate-window selector error.**  Over a gate window `[a,b]`
(`χ_reset = 0`, `χ_gate = 1`, in the domain), with reset error `δ` carried in,
coarse margins `αmar`, branch values bounded by `R` and weights in `(0,1)`, the
dynamic mixture at the window end is within
`card·R·C_reset(δ)·e^{-αmar·(G b - G a)}` of the true branch value
`A_vstar(u b)`.  Combines the iterator's gate-window ODEs with
`selector_mix_error_reset`. -/
theorem gate_mix_error
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    [DecidableEq V] (vstar : V) (i : Fin d) {a b αmar δ R : ℝ}
    (hab : a ≤ b) (hαmar : 0 < αmar) (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2) (hR : 0 ≤ R)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hreset0 : ∀ t ∈ Icc a b, chiReset t = 0)
    (hgate1 : ∀ t ∈ Icc a b, chiGate t = 1)
    (hgain_nonneg : ∀ t ∈ Ico a b, 0 ≤ gain t)
    (hunit : ∀ v, ∀ t ∈ Icc a b, 0 < sol.lam v t ∧ sol.lam v t < 1)
    (hlama : ∀ v, |sol.lam v a - 1 / 2| ≤ δ)
    (hPtrue : ∀ t ∈ Ico a b, αmar ≤ sol.Pval vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, sol.Pval v t ≤ -αmar)
    (hA : ∀ v, |BranchData.evalBranch (branch v) (sol.u b) i| ≤ R) :
    |selectorMixTarget branch sol.u sol.lam b i
        - BranchData.evalBranch (branch vstar) (sol.u b) i|
      ≤ (Fintype.card V : ℝ) * R *
          (Creset δ * Real.exp (-αmar * (sol.G b - sol.G a))) := by
  have hmix := selector_mix_error_reset (V := V) vstar
    (fun v => BranchData.evalBranch (branch v) (sol.u b) i)
    hab hαmar hδ hδhalf hR hgain_nonneg
    (fun t ht => (sol.G_gate_hasDeriv (hdom t (Ico_subset_Icc_self ht))
      (hgate1 t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
    sol.cont_G.continuousOn
    (fun v t ht => (sol.lam_gate_hasDeriv v (hdom t (Ico_subset_Icc_self ht))
      (hreset0 t (Ico_subset_Icc_self ht))
      (hgate1 t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
    (fun v => (sol.cont_lam v).continuousOn)
    hunit hlama hPtrue hPfalse hA
  simpa only [selectorMixTarget, selectorF] using hmix

/-- **(W4a) per-cycle step for the iterator.**  Lifts `selector_cycle_step_error`
to the iterator's held config `u` at the cycle timepoints `tStart` (cycle start),
`tHold` (gate-window end, where the mixture is read), `tEnd` (cycle end): the
written config is within `mult·|u(tStart) - E(c)| + ε_F` of `E(step c)`, with
`ε_F = ε_mix + ε_write + mult·ε_hold`.  `ε_mix` is supplied by `gate_mix_error`. -/
theorem cycle_step
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (vstar : V) (i : Fin d) (tStart tHold tEnd : ℝ)
    (encC encStepC : Fin d → ℝ) {εmix εwrite εhold mult : ℝ}
    (hmult : 0 ≤ mult)
    (hmix : |selectorMixTarget branch sol.u sol.lam tHold i
              - BranchData.evalBranch (branch vstar) (sol.u tHold) i| ≤ εmix)
    (hdiag : |BranchData.evalBranch (branch vstar) (sol.u tHold) i - encStepC i|
              ≤ mult * |sol.u tHold i - encC i|)
    (hhold : |sol.u tHold i - encC i| ≤ |sol.u tStart i - encC i| + εhold)
    (hwrite : |sol.u tEnd i
                - selectorMixTarget branch sol.u sol.lam tHold i| ≤ εwrite) :
    |sol.u tEnd i - encStepC i|
      ≤ mult * |sol.u tStart i - encC i| + (εmix + εwrite + mult * εhold) :=
  selector_cycle_step_error branch (sol.u tStart) (sol.u tHold) (sol.u tEnd)
    (fun v => sol.lam v tHold) encC encStepC vstar i hmult hmix hdiag hhold hwrite

/-- Continuity of the dynamic mixture target (in time), from continuity of the
held config `u` and the selector weights `λ_v`.  Needed as the moving-target
continuity hypothesis of `moving_target_bound`. -/
theorem cont_mixTarget
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) :
  Continuous (fun t => selectorMixTarget branch sol.u sol.lam t s) := by
  simp only [selectorMixTarget, selectorF]
  refine continuous_finsetSum _ (fun v _ => ?_)
  refine (sol.cont_lam v).mul ?_
  simp only [BranchData.evalBranch, BranchAction.evalReal]
  exact (continuous_const.mul (sol.cont_u s)).add continuous_const

/-- Derivative of the dynamic branch mixture target.

The branch maps are affine coordinatewise, so the derivative is the finite sum
of the selector-weight derivative term plus the held-coordinate derivative term. -/
theorem selectorMixTarget_hasDerivAt
    {u : ℝ → Fin d → ℝ} {lam : V → ℝ → ℝ}
    {u' : Fin d → ℝ} {lam' : V → ℝ} {t : ℝ} (s : Fin d)
    (hu : ∀ i : Fin d, HasDerivAt (fun τ => u τ i) (u' i) t)
    (hlam : ∀ v : V, HasDerivAt (lam v) (lam' v) t) :
    HasDerivAt (fun τ => selectorMixTarget branch u lam τ s)
      ((∑ v : V,
          (lam' v * BranchData.evalBranch (branch v) (u t) s +
            lam v t * (((branch v).action s).scale : ℝ) * u' s))) t := by
  have hterm : ∀ v : V,
      HasDerivAt
        (fun τ => lam v τ * BranchData.evalBranch (branch v) (u τ) s)
        (lam' v * BranchData.evalBranch (branch v) (u t) s +
          lam v t * (((branch v).action s).scale : ℝ) * u' s) t := by
    intro v
    have hbranch :
        HasDerivAt (fun τ => BranchData.evalBranch (branch v) (u τ) s)
          ((((branch v).action s).scale : ℝ) * u' s) t := by
      have hmul :=
        (hasDerivAt_const t (((branch v).action s).scale : ℝ)).mul (hu s)
      have h := hmul.add_const (((branch v).action s).shift : ℝ)
      simpa [BranchData.evalBranch, BranchAction.evalReal] using h
    have hprod := (hlam v).mul hbranch
    convert hprod using 1
    ring
  simpa [selectorMixTarget, selectorF] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun v _hv => hterm v)

/-- Center a weighted finite sum around a distinguished value when the weights
sum to one. The `v = c` summand in the residual sum is zero by algebra. -/
theorem sum_mul_eq_centered_of_sum_eq_one
    (lam A : V → ℝ) (c : V)
    (hsum : (∑ v : V, lam v) = 1) :
    (∑ v : V, lam v * A v) =
      A c + ∑ v : V, lam v * (A v - A c) := by
  calc
    (∑ v : V, lam v * A v)
        = ∑ v : V, (lam v * A c + lam v * (A v - A c)) := by
            refine Finset.sum_congr rfl ?_
            intro v _hv
            ring
    _ = A c + ∑ v : V, lam v * (A v - A c) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
            ring

/-- Center a weighted finite sum around a distinguished value when the weights
sum to zero. -/
theorem sum_mul_eq_centered_of_sum_eq_zero
    (lam A : V → ℝ) (c : V)
    (hsum : (∑ v : V, lam v) = 0) :
    (∑ v : V, lam v * A v) =
      ∑ v : V, lam v * (A v - A c) := by
  symm
  calc
    (∑ v : V, lam v * (A v - A c))
        = ∑ v : V, (lam v * A v - lam v * A c) := by
            refine Finset.sum_congr rfl ?_
            intro v _hv
            ring
    _ = (∑ v : V, lam v * A v) - ∑ v : V, lam v * A c := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ v : V, lam v * A v) := by
            rw [← Finset.sum_mul, hsum]
            ring

/-- Pure finite-sum centered derivative identity for a mixture target. -/
theorem finite_mix_deriv_centered
    (B σ lam lam' : V → ℝ) (u_s' : ℝ) (c : V)
    (h_lam : (∑ v : V, lam v) = 1)
    (h_lam' : (∑ v : V, lam' v) = 0) :
    (∑ v : V, (lam' v * B v + lam v * σ v * u_s')) =
      σ c * u_s' +
        (∑ v : V, lam' v * (B v - B c)) +
        (∑ v : V, lam v * (σ v - σ c) * u_s') := by
  have hB := sum_mul_eq_centered_of_sum_eq_zero
    (V := V) (lam := lam') (A := B) c h_lam'
  have hσ := sum_mul_eq_centered_of_sum_eq_one
    (V := V) (lam := lam) (A := σ) c h_lam
  have htransport :
      (∑ v : V, lam v * σ v * u_s') =
        σ c * u_s' + ∑ v : V, lam v * (σ v - σ c) * u_s' := by
    calc
      (∑ v : V, lam v * σ v * u_s')
          = (∑ v : V, lam v * σ v) * u_s' := by
              rw [Finset.sum_mul]
      _ = (σ c + ∑ v : V, lam v * (σ v - σ c)) * u_s' := by
              rw [hσ]
      _ = σ c * u_s' + ∑ v : V, lam v * (σ v - σ c) * u_s' := by
              rw [add_mul, Finset.sum_mul]
  calc
    (∑ v : V, (lam' v * B v + lam v * σ v * u_s'))
        = (∑ v : V, lam' v * B v) +
            ∑ v : V, lam v * σ v * u_s' := by
              rw [Finset.sum_add_distrib]
    _ = (∑ v : V, lam' v * (B v - B c)) +
          (σ c * u_s' + ∑ v : V, lam v * (σ v - σ c) * u_s') := by
              rw [hB, htransport]
    _ = σ c * u_s' +
        (∑ v : V, lam' v * (B v - B c)) +
        (∑ v : V, lam v * (σ v - σ c) * u_s') := by
              ring

/-- Subtract the active-branch transport term from the centered derivative
identity. -/
theorem finite_mix_deriv_sub_active_centered
    (B σ lam lam' : V → ℝ) (u_s' : ℝ) (c : V)
    (h_lam : (∑ v : V, lam v) = 1)
    (h_lam' : (∑ v : V, lam' v) = 0) :
    (∑ v : V, (lam' v * B v + lam v * σ v * u_s')) - σ c * u_s' =
      (∑ v : V, lam' v * (B v - B c)) +
      (∑ v : V, lam v * (σ v - σ c) * u_s') := by
  rw [finite_mix_deriv_centered B σ lam lam' u_s' c h_lam h_lam']
  ring

/-- Centered replicator RHS for an observable, rewritten as reset drift plus
the centered payoff/observable covariance.  This is pure finite-sum algebra;
no dynamics or estimates are hidden here. -/
theorem replicator_centered_rhs_eq_reset_add_covariance
    (lam P B : V → ℝ) (cr cg : ℝ) (c : V)
    (hmass : (∑ v : V, lam v) = 1) :
    (∑ v : V,
      (cr * ((Fintype.card V : ℝ)⁻¹ - lam v) +
        cg * lam v * (P v - ∑ w : V, lam w * P w)) * (B v - B c)) =
      cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B v - B c)) -
        ∑ v : V, lam v * (B v - B c)) +
      cg * (∑ v : V,
        lam v * (P v - P c) *
          ((B v - B c) - ∑ w : V, lam w * (B w - B c))) := by
  classical
  let ΔB : V → ℝ := fun v => B v - B c
  let ΔP : V → ℝ := fun v => P v - P c
  let qB : ℝ := ∑ v : V, lam v * ΔB v
  let qP : ℝ := ∑ v : V, lam v * ΔP v
  have hPcenter : (∑ w : V, lam w * P w) = P c + qP := by
    simpa [qP, ΔP] using
      sum_mul_eq_centered_of_sum_eq_one (V := V) (lam := lam) (A := P) c hmass
  have hreset :
      (∑ v : V, cr * ((Fintype.card V : ℝ)⁻¹ - lam v) * ΔB v) =
        cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, ΔB v) - qB) := by
    calc
      (∑ v : V, cr * ((Fintype.card V : ℝ)⁻¹ - lam v) * ΔB v)
          = cr * (∑ v : V, ((Fintype.card V : ℝ)⁻¹ - lam v) * ΔB v) := by
              simp_rw [mul_assoc]
              rw [Finset.mul_sum]
      _ = cr * ((∑ v : V, (Fintype.card V : ℝ)⁻¹ * ΔB v) -
            ∑ v : V, lam v * ΔB v) := by
              rw [← Finset.sum_sub_distrib]
              refine congrArg (fun x => cr * x) ?_
              refine Finset.sum_congr rfl ?_
              intro v _hv
              ring
      _ = cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, ΔB v) - qB) := by
              rw [Finset.mul_sum]
  have hgate :
      (∑ v : V, cg * lam v * (P v - ∑ w : V, lam w * P w) * ΔB v) =
        cg * (∑ v : V, lam v * ΔP v * (ΔB v - qB)) := by
    calc
      (∑ v : V, cg * lam v * (P v - ∑ w : V, lam w * P w) * ΔB v)
          = cg * (∑ v : V, lam v * ((P v - P c) - qP) * ΔB v) := by
              simp_rw [hPcenter]
              simp_rw [sub_add_eq_sub_sub]
              simp_rw [mul_assoc]
              rw [Finset.mul_sum]
      _ = cg * (∑ v : V, (lam v * ΔP v * ΔB v - lam v * ΔB v * qP)) := by
              refine congrArg (fun x => cg * x) ?_
              refine Finset.sum_congr rfl ?_
              intro v _hv
              simp [ΔP]
              ring
      _ = cg * ((∑ v : V, lam v * ΔP v * ΔB v) -
            (∑ v : V, lam v * ΔB v) * qP) := by
              rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = cg * ((∑ v : V, lam v * ΔP v * ΔB v) - qB * qP) := by
              rfl
      _ = cg * (∑ v : V, lam v * ΔP v * (ΔB v - qB)) := by
              congr 1
              symm
              calc
                (∑ v : V, lam v * ΔP v * (ΔB v - qB))
                    = ∑ v : V, (lam v * ΔP v * ΔB v -
                        lam v * ΔP v * qB) := by
                        refine Finset.sum_congr rfl ?_
                        intro v _hv
                        ring
                _ = (∑ v : V, lam v * ΔP v * ΔB v) -
                      (∑ v : V, lam v * ΔP v) * qB := by
                        rw [Finset.sum_sub_distrib, Finset.sum_mul]
                _ = (∑ v : V, lam v * ΔP v * ΔB v) - qB * qP := by
                        simp [qP, mul_comm]
  calc
    (∑ v : V,
      (cr * ((Fintype.card V : ℝ)⁻¹ - lam v) +
        cg * lam v * (P v - ∑ w : V, lam w * P w)) * (B v - B c))
        = ∑ v : V,
            (cr * ((Fintype.card V : ℝ)⁻¹ - lam v) * ΔB v +
              cg * lam v * (P v - ∑ w : V, lam w * P w) * ΔB v) := by
              refine Finset.sum_congr rfl ?_
              intro v _hv
              simp [ΔB]
              ring
    _ = (∑ v : V, cr * ((Fintype.card V : ℝ)⁻¹ - lam v) * ΔB v) +
          ∑ v : V, cg * lam v *
            (P v - ∑ w : V, lam w * P w) * ΔB v := by
              rw [Finset.sum_add_distrib]
    _ = cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, ΔB v) - qB) +
          cg * (∑ v : V, lam v * ΔP v * (ΔB v - qB)) := by
            rw [hreset, hgate]
    _ = cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B v - B c)) -
          ∑ v : V, lam v * (B v - B c)) +
        cg * (∑ v : V,
          lam v * (P v - P c) *
            ((B v - B c) - ∑ w : V, lam w * (B w - B c))) := by
            simp [ΔB, ΔP, qB]

/-- The same centered replicator RHS in nonnegative-defect coordinates
`D v = B c - B v` and `δ v = P c - P v`.

This is the algebraic surface for the active halt-coordinate residual:
`cg * gap_covariance - cr * reset_defect`. -/
theorem replicator_centered_rhs_eq_gap_covariance_sub_reset_defect
    (lam P B : V → ℝ) (cr cg : ℝ) (c : V)
    (hmass : (∑ v : V, lam v) = 1) :
    (∑ v : V,
      (cr * ((Fintype.card V : ℝ)⁻¹ - lam v) +
        cg * lam v * (P v - ∑ w : V, lam w * P w)) * (B v - B c)) =
      cg * (∑ v : V,
        lam v * (P c - P v) *
          ((B c - B v) - ∑ w : V, lam w * (B c - B w))) -
      cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B c - B v)) -
        ∑ v : V, lam v * (B c - B v)) := by
  classical
  let qB : ℝ := ∑ v : V, lam v * (B v - B c)
  let qD : ℝ := ∑ v : V, lam v * (B c - B v)
  have hDsum :
      (∑ v : V, (B c - B v)) = -(∑ v : V, (B v - B c)) := by
    calc
      (∑ v : V, (B c - B v))
          = ∑ v : V, -(B v - B c) := by
              refine Finset.sum_congr rfl ?_
              intro v _hv
              ring
      _ = -(∑ v : V, (B v - B c)) := by
              rw [Finset.sum_neg_distrib]
  have hqD : qD = -qB := by
    calc
      qD = ∑ v : V, -(lam v * (B v - B c)) := by
              refine Finset.sum_congr rfl ?_
              intro v _hv
              ring
      _ = -qB := by
              simp [qB, Finset.sum_neg_distrib]
  have hcov :
      (∑ v : V,
        lam v * (P c - P v) *
          ((B c - B v) - ∑ w : V, lam w * (B c - B w))) =
      (∑ v : V,
        lam v * (P v - P c) *
          ((B v - B c) - ∑ w : V, lam w * (B w - B c))) := by
    refine Finset.sum_congr rfl ?_
    intro v _hv
    have hqD' :
        (∑ w : V, lam w * (B c - B w)) =
          -(∑ w : V, lam w * (B w - B c)) := by
      calc
        (∑ w : V, lam w * (B c - B w))
            = ∑ w : V, -(lam w * (B w - B c)) := by
                refine Finset.sum_congr rfl ?_
                intro w _hw
                ring
        _ = -(∑ w : V, lam w * (B w - B c)) := by
                rw [Finset.sum_neg_distrib]
    rw [hqD']
    ring
  have hbase :=
    replicator_centered_rhs_eq_reset_add_covariance
      (V := V) lam P B cr cg c hmass
  calc
    (∑ v : V,
      (cr * ((Fintype.card V : ℝ)⁻¹ - lam v) +
        cg * lam v * (P v - ∑ w : V, lam w * P w)) * (B v - B c))
        = cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B v - B c)) -
            ∑ v : V, lam v * (B v - B c)) +
          cg * (∑ v : V,
            lam v * (P v - P c) *
              ((B v - B c) - ∑ w : V, lam w * (B w - B c))) := hbase
    _ = cg * (∑ v : V,
          lam v * (P c - P v) *
            ((B c - B v) - ∑ w : V, lam w * (B c - B w))) -
        cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B c - B v)) -
          ∑ v : V, lam v * (B c - B v)) := by
          rw [hcov, hDsum]
          have hqD' :
              (∑ v : V, lam v * (B c - B v)) =
                -(∑ v : V, lam v * (B v - B c)) := by
            simpa [qB, qD] using hqD
          rw [hqD']
          ring

/-- Per-branch reset/selection cancellation: the replicator RHS is a
branch-local tracking residual toward the reset/selection equilibrium, plus the
mean-gap forcing term. -/
theorem replicatorLamRHS_eq_gapTrackingResidual_add_meanGap
    (lam P : V → ℝ) (cr cg : ℝ) (c v : V)
    (hmass : (∑ x : V, lam x) = 1) :
    cr * ((Fintype.card V : ℝ)⁻¹ - lam v) +
        cg * lam v * (P v - ∑ x : V, lam x * P x)
      =
    (cr * (Fintype.card V : ℝ)⁻¹ -
        (cr + cg * (P c - P v)) * lam v) +
      cg * (∑ x : V, lam x * (P c - P x)) * lam v := by
  classical
  have hmeanGap :
      (∑ x : V, lam x * (P c - P x)) =
        P c - ∑ x : V, lam x * P x := by
    calc
      (∑ x : V, lam x * (P c - P x))
          = ∑ x : V, (lam x * P c - lam x * P x) := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              ring
      _ = (∑ x : V, lam x * P c) - ∑ x : V, lam x * P x := by
              rw [Finset.sum_sub_distrib]
      _ = (∑ x : V, lam x) * P c - ∑ x : V, lam x * P x := by
              rw [Finset.sum_mul]
      _ = P c - ∑ x : V, lam x * P x := by
              rw [hmass]
              ring
  rw [hmeanGap]
  ring

/-- Exact branch-residual form of the active centered covariance/reset expression. -/
theorem activeCenteredVariation_eq_neg_branchResiduals_sub_meanGapProduct
    (lam P B : V → ℝ) (cr cg : ℝ) (c : V)
    (hmass : (∑ v : V, lam v) = 1) :
    (cg * (∑ v : V,
        lam v * (P c - P v) *
          ((B c - B v) - ∑ w : V, lam w * (B c - B w)))
      - cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B c - B v)) -
          ∑ v : V, lam v * (B c - B v)))
    =
      - (∑ v : V,
        (B c - B v) *
          (cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v))
      - cg * (∑ v : V, lam v * (P c - P v)) *
          (∑ v : V, lam v * (B c - B v)) := by
  classical
  have hcenter :
      (∑ v : V,
        (cr * ((Fintype.card V : ℝ)⁻¹ - lam v) +
          cg * lam v * (P v - ∑ x : V, lam x * P x)) * (B v - B c))
      =
      (cg * (∑ v : V,
          lam v * (P c - P v) *
            ((B c - B v) - ∑ w : V, lam w * (B c - B w)))
        - cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B c - B v)) -
            ∑ v : V, lam v * (B c - B v))) := by
    simpa using
      (replicator_centered_rhs_eq_gap_covariance_sub_reset_defect
        (lam := lam) (P := P) (B := B) (cr := cr) (cg := cg) (c := c) hmass)
  have hpoint : ∀ v : V,
      cr * ((Fintype.card V : ℝ)⁻¹ - lam v) +
          cg * lam v * (P v - ∑ x : V, lam x * P x)
        =
      (cr * (Fintype.card V : ℝ)⁻¹ -
          (cr + cg * (P c - P v)) * lam v) +
        cg * (∑ x : V, lam x * (P c - P x)) * lam v := by
    intro v
    exact replicatorLamRHS_eq_gapTrackingResidual_add_meanGap
      (lam := lam) (P := P) (cr := cr) (cg := cg) (c := c) (v := v) hmass
  calc
    (cg * (∑ v : V,
        lam v * (P c - P v) *
          ((B c - B v) - ∑ w : V, lam w * (B c - B w)))
      - cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B c - B v)) -
          ∑ v : V, lam v * (B c - B v)))
        =
      (∑ v : V,
        (cr * ((Fintype.card V : ℝ)⁻¹ - lam v) +
          cg * lam v * (P v - ∑ x : V, lam x * P x)) * (B v - B c)) := by
          exact hcenter.symm
    _ =
      (∑ v : V,
        (((cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v) +
          cg * (∑ x : V, lam x * (P c - P x)) * lam v) *
          (B v - B c))) := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [hpoint v]
    _ =
      (∑ v : V,
        (-((B c - B v) *
            (cr * (Fintype.card V : ℝ)⁻¹ -
              (cr + cg * (P c - P v)) * lam v)) -
          (cg * (∑ x : V, lam x * (P c - P x))) *
            (lam v * (B c - B v)))) := by
          apply Finset.sum_congr rfl
          intro v _hv
          ring
    _ =
      - (∑ v : V,
        (B c - B v) *
          (cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v))
      - cg * (∑ v : V, lam v * (P c - P v)) *
          (∑ v : V, lam v * (B c - B v)) := by
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_neg_distrib]
          rw [← Finset.mul_sum]

/-- Cancellation-preserving pointwise bound for the active centered variation.

The reset term is not separated from selection.  Instead the cancellation is
localized into the branch tracking residual
`cr / N - (cr + cg * (P c - P v)) * lam v`, with the mean-gap forcing paid as a
quadratic product. -/
theorem activeCenteredVariation_abs_le_branchResiduals_add_meanGapProduct
    (lam P B : V → ℝ) (cr cg : ℝ) (c : V)
    (hmass : (∑ v : V, lam v) = 1)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v)
    (hcg_nonneg : 0 ≤ cg)
    (hD_nonneg : ∀ v : V, 0 ≤ B c - B v)
    (hdelta_nonneg : ∀ v : V, 0 ≤ P c - P v) :
    |(cg * (∑ v : V,
        lam v * (P c - P v) *
          ((B c - B v) - ∑ w : V, lam w * (B c - B w)))
      - cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B c - B v)) -
          ∑ v : V, lam v * (B c - B v)))|
    ≤
      (∑ v : V,
        (B c - B v) *
          |cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v|)
      +
      cg * (∑ v : V, lam v * (P c - P v)) *
        (∑ v : V, lam v * (B c - B v)) := by
  classical
  have hEq :=
    activeCenteredVariation_eq_neg_branchResiduals_sub_meanGapProduct
      (lam := lam) (P := P) (B := B) (cr := cr) (cg := cg) (c := c) hmass
  rw [hEq]
  have hmean_nonneg : 0 ≤ ∑ v : V, lam v * (P c - P v) := by
    exact Finset.sum_nonneg (fun v _hv =>
      mul_nonneg (hlam_nonneg v) (hdelta_nonneg v))
  have hDmean_nonneg : 0 ≤ ∑ v : V, lam v * (B c - B v) := by
    exact Finset.sum_nonneg (fun v _hv =>
      mul_nonneg (hlam_nonneg v) (hD_nonneg v))
  have hT_nonneg :
      0 ≤ cg * (∑ v : V, lam v * (P c - P v)) *
          (∑ v : V, lam v * (B c - B v)) := by
    exact mul_nonneg (mul_nonneg hcg_nonneg hmean_nonneg) hDmean_nonneg
  have hsum_abs :
      |∑ v : V,
        (B c - B v) *
          (cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v)|
      ≤
      ∑ v : V,
        (B c - B v) *
          |cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v| := by
    calc
      |∑ v : V,
        (B c - B v) *
          (cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v)|
          ≤
        ∑ v : V,
          |(B c - B v) *
            (cr * (Fintype.card V : ℝ)⁻¹ -
              (cr + cg * (P c - P v)) * lam v)| := by
              exact Finset.abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun v : V =>
                  (B c - B v) *
                    (cr * (Fintype.card V : ℝ)⁻¹ -
                      (cr + cg * (P c - P v)) * lam v))
      _ = ∑ v : V,
          (B c - B v) *
            |cr * (Fintype.card V : ℝ)⁻¹ -
              (cr + cg * (P c - P v)) * lam v| := by
              refine Finset.sum_congr rfl ?_
              intro v _hv
              rw [abs_mul, abs_of_nonneg (hD_nonneg v)]
  have hmain :
      |-(∑ v : V,
          (B c - B v) *
            (cr * (Fintype.card V : ℝ)⁻¹ -
              (cr + cg * (P c - P v)) * lam v))
        - cg * (∑ v : V, lam v * (P c - P v)) *
            (∑ v : V, lam v * (B c - B v))|
      ≤
      |∑ v : V,
          (B c - B v) *
            (cr * (Fintype.card V : ℝ)⁻¹ -
              (cr + cg * (P c - P v)) * lam v)|
      + cg * (∑ v : V, lam v * (P c - P v)) *
          (∑ v : V, lam v * (B c - B v)) := by
    calc
      |-(∑ v : V,
          (B c - B v) *
            (cr * (Fintype.card V : ℝ)⁻¹ -
              (cr + cg * (P c - P v)) * lam v))
        - cg * (∑ v : V, lam v * (P c - P v)) *
            (∑ v : V, lam v * (B c - B v))|
          =
        |(∑ v : V,
          (B c - B v) *
            (cr * (Fintype.card V : ℝ)⁻¹ -
              (cr + cg * (P c - P v)) * lam v))
        + cg * (∑ v : V, lam v * (P c - P v)) *
            (∑ v : V, lam v * (B c - B v))| := by
            have hneg :
                -(∑ v : V,
                    (B c - B v) *
                      (cr * (Fintype.card V : ℝ)⁻¹ -
                        (cr + cg * (P c - P v)) * lam v))
                  - cg * (∑ v : V, lam v * (P c - P v)) *
                      (∑ v : V, lam v * (B c - B v))
                =
                -((∑ v : V,
                    (B c - B v) *
                      (cr * (Fintype.card V : ℝ)⁻¹ -
                        (cr + cg * (P c - P v)) * lam v))
                  + cg * (∑ v : V, lam v * (P c - P v)) *
                      (∑ v : V, lam v * (B c - B v))) := by
              ring
            rw [hneg, abs_neg]
      _ ≤
        |∑ v : V,
          (B c - B v) *
            (cr * (Fintype.card V : ℝ)⁻¹ -
              (cr + cg * (P c - P v)) * lam v)|
        + |cg * (∑ v : V, lam v * (P c - P v)) *
            (∑ v : V, lam v * (B c - B v))| := by
            exact abs_add_le _ _
      _ =
        |∑ v : V,
          (B c - B v) *
            (cr * (Fintype.card V : ℝ)⁻¹ -
              (cr + cg * (P c - P v)) * lam v)|
        + cg * (∑ v : V, lam v * (P c - P v)) *
            (∑ v : V, lam v * (B c - B v)) := by
            rw [abs_of_nonneg hT_nonneg]
  exact le_trans hmain (add_le_add hsum_abs le_rfl)

/-- Flipped-orientation version of
`activeCenteredVariation_abs_le_branchResiduals_add_meanGapProduct`.

This is the same cancellation-preserving estimate, with branch gaps measured as
`B v - B c`.  It is useful when the active halt branch has target `0` rather
than `1`. -/
theorem activeCenteredVariation_abs_le_branchResiduals_add_meanGapProduct_flip
    (lam P B : V → ℝ) (cr cg : ℝ) (c : V)
    (hmass : (∑ v : V, lam v) = 1)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v)
    (hcg_nonneg : 0 ≤ cg)
    (hD_nonneg : ∀ v : V, 0 ≤ B v - B c)
    (hdelta_nonneg : ∀ v : V, 0 ≤ P c - P v) :
    |(cg * (∑ v : V,
        lam v * (P c - P v) *
          ((B v - B c) - ∑ w : V, lam w * (B w - B c)))
      - cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B v - B c)) -
          ∑ v : V, lam v * (B v - B c)))|
    ≤
      (∑ v : V,
        (B v - B c) *
          |cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v|)
      +
      cg * (∑ v : V, lam v * (P c - P v)) *
        (∑ v : V, lam v * (B v - B c)) := by
  classical
  have h :=
    activeCenteredVariation_abs_le_branchResiduals_add_meanGapProduct
      (lam := lam) (P := P) (B := fun v : V => -B v)
      (cr := cr) (cg := cg) (c := c)
      hmass hlam_nonneg hcg_nonneg
      (by
        intro v
        simpa using hD_nonneg v)
      hdelta_nonneg
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc,
    mul_left_comm, mul_comm] using h

/-- Flipped residual bound for the original centered variation orientation.

The active cap estimates are written with branch differences `B c - B v`.
When the active halt target is `0`, the nonnegative residual coordinate is
`B v - B c`; the two centered variations differ by a sign, so their absolute
values agree. -/
theorem activeCenteredVariation_abs_le_branchResiduals_add_meanGapProduct_flip_original
    (lam P B : V → ℝ) (cr cg : ℝ) (c : V)
    (hmass : (∑ v : V, lam v) = 1)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v)
    (hcg_nonneg : 0 ≤ cg)
    (hD_nonneg : ∀ v : V, 0 ≤ B v - B c)
    (hdelta_nonneg : ∀ v : V, 0 ≤ P c - P v) :
    |(cg * (∑ v : V,
        lam v * (P c - P v) *
          ((B c - B v) - ∑ w : V, lam w * (B c - B w)))
      - cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B c - B v)) -
          ∑ v : V, lam v * (B c - B v)))|
    ≤
      (∑ v : V,
        (B v - B c) *
          |cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v|)
      +
      cg * (∑ v : V, lam v * (P c - P v)) *
        (∑ v : V, lam v * (B v - B c)) := by
  classical
  have h :=
    activeCenteredVariation_abs_le_branchResiduals_add_meanGapProduct_flip
      (lam := lam) (P := P) (B := B) (cr := cr) (cg := cg) (c := c)
      hmass hlam_nonneg hcg_nonneg hD_nonneg hdelta_nonneg
  let orig : ℝ :=
    cg * (∑ v : V,
        lam v * (P c - P v) *
          ((B c - B v) - ∑ w : V, lam w * (B c - B w)))
      - cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B c - B v)) -
          ∑ v : V, lam v * (B c - B v))
  let flip : ℝ :=
    cg * (∑ v : V,
        lam v * (P c - P v) *
          ((B v - B c) - ∑ w : V, lam w * (B w - B c)))
      - cr * (((Fintype.card V : ℝ)⁻¹ * ∑ v : V, (B v - B c)) -
          ∑ v : V, lam v * (B v - B c))
  let rhs : ℝ :=
    (∑ v : V,
        (B v - B c) *
          |cr * (Fintype.card V : ℝ)⁻¹ -
            (cr + cg * (P c - P v)) * lam v|)
      +
      cg * (∑ v : V, lam v * (P c - P v)) *
        (∑ v : V, lam v * (B v - B c))
  change |orig| ≤ rhs
  have hflip : |flip| ≤ rhs := by
    simpa [flip, rhs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hsumD :
      (∑ v : V, (B v - B c)) = -∑ v : V, (B c - B v) := by
    rw [← Finset.sum_neg_distrib
      (s := Finset.univ) (f := fun v : V => B c - B v)]
    refine Finset.sum_congr rfl ?_
    intro v _hv
    ring
  have hmeanD :
      (∑ v : V, lam v * (B v - B c)) =
        -∑ v : V, lam v * (B c - B v) := by
    rw [← Finset.sum_neg_distrib
      (s := Finset.univ) (f := fun v : V => lam v * (B c - B v))]
    refine Finset.sum_congr rfl ?_
    intro v _hv
    ring
  have hcov :
      (∑ v : V,
        lam v * (P c - P v) *
          ((B v - B c) - ∑ w : V, lam w * (B w - B c))) =
        -∑ v : V,
          lam v * (P c - P v) *
            ((B c - B v) - ∑ w : V, lam w * (B c - B w)) := by
    have hcenter : ∀ v : V,
        ((B v - B c) - ∑ w : V, lam w * (B w - B c)) =
          -((B c - B v) - ∑ w : V, lam w * (B c - B w)) := by
      intro v
      rw [hmeanD]
      ring
    calc
      (∑ v : V,
        lam v * (P c - P v) *
          ((B v - B c) - ∑ w : V, lam w * (B w - B c))) =
        ∑ v : V,
          -(lam v * (P c - P v) *
            ((B c - B v) - ∑ w : V, lam w * (B c - B w))) := by
          refine Finset.sum_congr rfl ?_
          intro v _hv
          rw [hcenter v]
          ring
      _ = -∑ v : V,
          lam v * (P c - P v) *
            ((B c - B v) - ∑ w : V, lam w * (B c - B w)) := by
          rw [Finset.sum_neg_distrib]
  have horig : orig = -flip := by
    dsimp [orig, flip]
    rw [hcov, hsumD, hmeanD]
    ring
  calc
    |orig| = |flip| := by rw [horig, abs_neg]
    _ ≤ rhs := hflip

/-- Centered algebraic form of the selector-mixture derivative sum. This is the
structural identity needed before estimating total variation: the dangerous
`lam' * branch` source is rewritten against branch differences. -/
theorem selectorMixTarget_deriv_sum_eq_centered
    {u : ℝ → Fin d → ℝ} {lam : V → ℝ → ℝ}
    (u' : Fin d → ℝ) (lam' : V → ℝ) (t : ℝ) (s : Fin d) (c : V)
    (hlam : (∑ v : V, lam v t) = 1)
    (hlam' : (∑ v : V, lam' v) = 0) :
    (∑ v : V,
        (lam' v * BranchData.evalBranch (branch v) (u t) s +
          lam v t * (((branch v).action s).scale : ℝ) * u' s)) =
      (((branch c).action s).scale : ℝ) * u' s +
        ∑ v : V,
          (lam' v *
              (BranchData.evalBranch (branch v) (u t) s -
                BranchData.evalBranch (branch c) (u t) s) +
            lam v t *
              ((((branch v).action s).scale : ℝ) * u' s -
                (((branch c).action s).scale : ℝ) * u' s)) := by
  let A : V → ℝ := fun v => BranchData.evalBranch (branch v) (u t) s
  let D : V → ℝ := fun v => (((branch v).action s).scale : ℝ) * u' s
  have hA := sum_mul_eq_centered_of_sum_eq_zero (V := V) (lam := lam') (A := A) c hlam'
  have hD := sum_mul_eq_centered_of_sum_eq_one
    (V := V) (lam := fun v => lam v t) (A := D) c hlam
  calc
    (∑ v : V,
        (lam' v * BranchData.evalBranch (branch v) (u t) s +
          lam v t * (((branch v).action s).scale : ℝ) * u' s))
        = (∑ v : V, lam' v * A v) + ∑ v : V, lam v t * D v := by
            rw [Finset.sum_add_distrib]
            simp [A, D, mul_assoc]
    _ = (∑ v : V, lam' v * (A v - A c)) +
          (D c + ∑ v : V, lam v t * (D v - D c)) := by
            rw [hA, hD]
    _ = D c +
          ∑ v : V, (lam' v * (A v - A c) + lam v t * (D v - D c)) := by
            rw [Finset.sum_add_distrib]
            ring
    _ = (((branch c).action s).scale : ℝ) * u' s +
        ∑ v : V,
          (lam' v *
              (BranchData.evalBranch (branch v) (u t) s -
                BranchData.evalBranch (branch c) (u t) s) +
            lam v t *
              ((((branch v).action s).scale : ℝ) * u' s -
                (((branch c).action s).scale : ℝ) * u' s)) := rfl

theorem selectorMixTarget_deriv_sum_sub_active_centered
    {u : ℝ → Fin d → ℝ} {lam : V → ℝ → ℝ}
    (u' : Fin d → ℝ) (lam' : V → ℝ) (t : ℝ) (s : Fin d) (c : V)
    (hlam : (∑ v : V, lam v t) = 1)
    (hlam' : (∑ v : V, lam' v) = 0) :
    (∑ v : V,
        (lam' v * BranchData.evalBranch (branch v) (u t) s +
          lam v t * (((branch v).action s).scale : ℝ) * u' s)) -
        (((branch c).action s).scale : ℝ) * u' s =
      ∑ v : V,
        (lam' v *
            (BranchData.evalBranch (branch v) (u t) s -
              BranchData.evalBranch (branch c) (u t) s) +
          lam v t *
            ((((branch v).action s).scale : ℝ) * u' s -
              (((branch c).action s).scale : ℝ) * u' s)) := by
  rw [selectorMixTarget_deriv_sum_eq_centered
    (branch := branch) (u' := u') (lam' := lam') t s c hlam hlam']
  ring

/-- ODE right-hand side for the derivative of `selectorMixTarget`. -/
def mixTargetDerivRHS
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (t : ℝ) (s : Fin d) : ℝ :=
  (Finset.univ : Finset V).sum (fun v =>
    ((chiReset t * kappa t * (1 / 2 - sol.lam v t) +
        chiGate t * (gain t * readoutP v (sol.u t) *
          (sol.lam v t * (1 - sol.lam v t)))) *
      BranchData.evalBranch (branch v) (sol.u t) s +
    sol.lam v t * (((branch v).action s).scale : ℝ) *
      (p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t s - sol.u t s))))

/-- Solution-level derivative of the dynamic branch mixture target.

This packages the `u`-field and `λ`-field ODEs into the finite-sum derivative
of `selectorMixTarget`. -/
theorem mixTarget_hasDerivAt_ode
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    {t : ℝ} (ht : t ∈ sched.domain) (s : Fin d) :
    HasDerivAt (fun τ => selectorMixTarget branch sol.u sol.lam τ s)
      (mixTargetDerivRHS sol t s) t := by
  simpa [mixTargetDerivRHS] using selectorMixTarget_hasDerivAt
    (branch := branch) (s := s) (u := sol.u) (lam := sol.lam)
    (u' := fun i =>
      p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t i - sol.u t i))
    (lam' := fun v =>
      chiReset t * kappa t * (1 / 2 - sol.lam v t) +
        chiGate t * (gain t * readoutP v (sol.u t) *
          (sol.lam v t * (1 - sol.lam v t))))
    (fun i => sol.u_hasDeriv t ht i)
    (fun v => sol.lam_hasDeriv v t ht)

/-- **(W4a) config z-Reach toward the dynamic mixture.**  Over a window `[a,b]`
the config register `z` (Reach ODE `z' = A·α·bGateZ·(mixture - z)`) contracts
toward any constant `c` that the moving mixture target stays within `δ` of:
`|z(b) - c| ≤ exp(-∫ A·α·bGateZ)·|z(a) - c| + δ`.  Direct instance of
`moving_target_bound`; the gate-envelope continuity is supplied as a hypothesis
(matching `variable_mu_cycle_recurrence`'s style). -/
theorem z_reach_bound
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b c δ : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hδ : ∀ t ∈ Icc a b, |selectorMixTarget branch sol.u sol.lam t s - c| ≤ δ) :
    |sol.z b s - c| ≤
      Real.exp (-(∫ t in a..b, p.A * sol.α t * bGateZ p.L (sol.μ t) t)) *
          |sol.z a s - c| + δ :=
  moving_target_bound (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (fun t => selectorMixTarget branch sol.u sol.lam t s) (fun t => sol.z t s)
    a b hab hg_cont hg0 (sol.cont_mixTarget s) c δ hδ
    (fun t ht => sol.z_hasDeriv t (hdom t ht) s)

/-- **(W4a) config u-hold toward z.**  Over a window `[a,b]` the held register `u`
(hold ODE `u' = A·α·bGateU·(z - u)`) contracts toward any constant `c` that `z`
stays within `δ` of: `|u(b) - c| ≤ exp(-∫ A·α·bGateU)·|u(a) - c| + δ`. -/
theorem u_hold_bound
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b c δ : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hg_cont : Continuous (fun t => p.A * sol.α t * bGateU p.L (sol.μ t) t))
    (hg0 : ∀ t ∈ Icc a b, 0 ≤ p.A * sol.α t * bGateU p.L (sol.μ t) t)
    (hδ : ∀ t ∈ Icc a b, |sol.z t s - c| ≤ δ) :
    |sol.u b s - c| ≤
      Real.exp (-(∫ t in a..b, p.A * sol.α t * bGateU p.L (sol.μ t) t)) *
          |sol.u a s - c| + δ :=
  moving_target_bound (fun t => p.A * sol.α t * bGateU p.L (sol.μ t) t)
    (fun t => sol.z t s) (fun t => sol.u t s)
    a b hab hg_cont hg0 (sol.cont_z s) c δ hδ
    (fun t ht => sol.u_hasDeriv t (hdom t ht) s)

/-- **(W4a) two-half write Reach.**  The config write of one cycle: `z` reaches the
held mixture value `M` on the z-active half `[a,m]` (mixture stable within `δw` of
`M`), holds within `δzh` of `z(m)` on the u-active half `[m,b]`, while `u` reaches
`z` on `[m,b]`.  Combined, the written config `u(b)` lands within `εwrite` of `M`:

  `εwrite = δzh + κz·|z(a) - M| + δw`,  `κz = exp(-∫_a^m A·α·bGateZ)`.

This is the heterogeneous analogue of `variable_mu_cycle_recurrence`'s two-half
composition, built from the iterator's Reach primitives. -/
theorem write_reach
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a m b M δw δzh : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hdom1 : ∀ t ∈ Icc a m, t ∈ sched.domain)
    (hdom2 : ∀ t ∈ Icc m b, t ∈ sched.domain)
    (hgZ_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hgZ0 : ∀ t ∈ Icc a m, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hgU_cont : Continuous (fun t => p.A * sol.α t * bGateU p.L (sol.μ t) t))
    (hgU0 : ∀ t ∈ Icc m b, 0 ≤ p.A * sol.α t * bGateU p.L (sol.μ t) t)
    (hstab : ∀ t ∈ Icc a m, |selectorMixTarget branch sol.u sol.lam t s - M| ≤ δw)
    (hzh : ∀ t ∈ Icc m b, |sol.z t s - sol.z m s| ≤ δzh) :
    |sol.u b s - M| ≤
      Real.exp (-(∫ t in m..b, p.A * sol.α t * bGateU p.L (sol.μ t) t)) *
          |sol.u m s - M|
        + (δzh + (Real.exp (-(∫ t in a..m, p.A * sol.α t * bGateZ p.L (sol.μ t) t)) *
            |sol.z a s - M| + δw)) := by
  have hzm := sol.z_reach_bound s ham hdom1 hgZ_cont hgZ0 hstab
  have hzdrift : ∀ t ∈ Icc m b, |sol.z t s - M| ≤
      δzh + (Real.exp (-(∫ t in a..m, p.A * sol.α t * bGateZ p.L (sol.μ t) t)) *
        |sol.z a s - M| + δw) := by
    intro t ht
    calc |sol.z t s - M| ≤ |sol.z t s - sol.z m s| + |sol.z m s - M| :=
          abs_sub_le _ _ _
      _ ≤ δzh + (Real.exp (-(∫ t in a..m, p.A * sol.α t * bGateZ p.L (sol.μ t) t)) *
            |sol.z a s - M| + δw) := add_le_add (hzh t ht) hzm
  exact sol.u_hold_bound s hmb hdom2 hgU_cont hgU0 hzdrift

/-- **(W4a) hold drift.**  Over the z-active window `[a,b]` (where the `u`-channel
gate `bGateU` is small) the held config `u` drifts little: `|u(b) - u(a)| ≤ η·(b-a)`
when the hold field magnitude is bounded by `η`.  This is the `ε_hold` of
`cycle_step` (combined with a triangle step to `E(c)`). -/
theorem u_hold_drift
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a b η : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hη : ∀ t ∈ Icc a b,
      |p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t s - sol.u t s)| ≤ η) :
    |sol.u b s - sol.u a s| ≤ η * (b - a) :=
  hold_bound (fun t => sol.u t s)
    (fun t => p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t s - sol.u t s))
    η a b hab (fun t ht => sol.u_hasDeriv t (hdom t ht) s) hη

/-- The `hhold` shape `cycle_step` wants, from the hold drift: the held config at
the gate-readout point is within `ε_hold` of where it started, hence within
`|u(tStart) - E(c)| + ε_hold` of `E(c)`. -/
theorem hold_to_enc
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {tStart tHold : ℝ} {encC : Fin d → ℝ} {εhold : ℝ}
    (hdrift : |sol.u tHold s - sol.u tStart s| ≤ εhold) :
    |sol.u tHold s - encC s| ≤ |sol.u tStart s - encC s| + εhold := by
  calc |sol.u tHold s - encC s|
      ≤ |sol.u tHold s - sol.u tStart s| + |sol.u tStart s - encC s| := abs_sub_le _ _ _
    _ ≤ εhold + |sol.u tStart s - encC s| := by linarith [hdrift]
    _ = |sol.u tStart s - encC s| + εhold := by ring

/-- **(W4) coarse margins for the iterator from SEL1 bounds.**  When the iterator's
margin readout `Pval v` is the fixed Bernstein SEL1 weight `Λ v` shifted by `1/2`,
the separation `errSel < 1/2` supplies the gate-phase margins that `gate_mix_error`
consumes: `Pval vstar ≥ αmar` and `Pval v ≤ -αmar` with `αmar = 1/2 - errSel`.  The
instance discharges `htrue`/`hoff` via the tube chain
`EncodingTube → universalGateAtoms_sharpness → gate_view_selectorsN_SEL1_hypotheses`
(errSel = Σ_k atom error). -/
theorem margins_of_sel1
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (vstar : V) {a b : ℝ} {Λ : V → ℝ → ℝ} {errSel : ℝ}
    (herr : errSel < 1 / 2)
    (hPdef : ∀ v t, sol.Pval v t = Λ v t - 1 / 2)
    (htrue : ∀ t ∈ Ico a b, 1 - errSel ≤ Λ vstar t)
    (hoff : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, Λ v t ≤ errSel) :
    (∀ t ∈ Ico a b, 1 / 2 - errSel ≤ sol.Pval vstar t) ∧
      (∀ v, v ≠ vstar → ∀ t ∈ Ico a b, sol.Pval v t ≤ -(1 / 2 - errSel)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    have hm := (coarse_margin_of_sel1 vstar (fun v => Λ v t) herr (htrue t ht)
      (fun v hv => hoff v hv t ht)).2.1
    rw [hPdef]; linarith
  · intro v hv t ht
    have hm := (coarse_margin_of_sel1 vstar (fun v => Λ v t) herr (htrue t ht)
      (fun v hv => hoff v hv t ht)).2.2 v hv
    rw [hPdef]; linarith

end SelectorDynSol

end Ripple.BoundedUniversality.BGP
