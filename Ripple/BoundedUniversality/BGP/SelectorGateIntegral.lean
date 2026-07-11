import Ripple.BoundedUniversality.BGP.SelectorGateApprox

/-!
Ripple.BoundedUniversality.BGP.SelectorGateIntegral
-------------------------------
The gate-integral asymptotics for the εmix reset-residual term (#8, the `hint` integral).

ChatGPT (channel `ac`, 2026-06-15) surfaced a hidden-premise trap: the carried
`hint : ∫ exp(α(G−Ga)) ≤ Kint` with a SINGLE FIXED `Kint` across all cycles `j` is
UNSATISFIABLE on the growing-gain gate window — the integral grows like
`(exp(αΔG_j)−1)/(α·gmin_j) ~ exp(αΔG_j)`, so no `j`-independent `Kint` bounds it.

The genuine decaying object is the PRODUCT `exp(−αΔG)·∫ exp(α(G−Ga))`, which is bounded
by `1/(α·gmin) → 0` as the gain grows.  This is the clean cancellation that suppresses the
reset residual `ρb·Cb·Kint·exp(−αΔG)` in `gate_mix_error_approx` WITHOUT a fixed `Kint`.

`gate_perturb_integral_times_decay` is the abstract product-cancellation corollary of
`gate_perturbation_integral_bound` (with `ρ ≡ 1`, `c = 1`).
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set

/-- **Gate-integral × decay cancellation (the #8 product form).**  With the integrated gain
`G` growing at rate `r ≥ gmin > 0` on `[a,b]`, the gate integral `∫ exp(α(G−Ga))` weighted
by the decay `exp(−αΔG)` (`ΔG = G b − G a`) is bounded by `1/(α·gmin)` — INDEPENDENT of the
window position, and `→ 0` as `gmin → ∞`.  This is the correct statement of the reset-residual
suppression: the integral itself grows like `exp(αΔG)`, but the product with `exp(−αΔG)` does
not.  Corollary of `gate_perturbation_integral_bound` (`ρ ≡ 1`, `c = 1`) multiplied by
`exp(−αΔG) ≥ 0`. -/
theorem gate_perturb_integral_times_decay
    {a b α gmin : ℝ} {G r : ℝ → ℝ}
    (hab : a ≤ b) (hα : 0 < α) (hgmin : 0 < gmin)
    (hGder : ∀ t, HasDerivAt G (r t) t)
    (hr_cont : Continuous r)
    (hr : ∀ t ∈ Set.Icc a b, gmin ≤ r t) :
    Real.exp (-α * (G b - G a)) * (∫ t in a..b, Real.exp (α * (G t - G a)))
      ≤ 1 / (α * gmin) := by
  have hden : 0 < α * gmin := mul_pos hα hgmin
  set Δ : ℝ := G b - G a with hΔ
  have hexp_nonneg : 0 ≤ Real.exp (-α * Δ) := (Real.exp_pos _).le
  -- the bare-integral bound from `gate_perturbation_integral_bound` with `ρ ≡ 1`, `c = 1`
  have hbase : (∫ t in a..b, Real.exp (α * (G t - G a)))
      ≤ (1 / (α * gmin)) * (Real.exp (α * Δ) - 1) := by
    have h := gate_perturbation_integral_bound (a := a) (b := b) (α := α) (gmin := gmin)
      (c := 1) (G := G) (r := r) (ρ := fun _ => 1)
      hab hα hgmin hGder hr_cont continuous_const hr
      (fun _ _ => zero_le_one) (fun _ _ => le_refl 1)
    simpa [hΔ] using h
  calc Real.exp (-α * Δ) * (∫ t in a..b, Real.exp (α * (G t - G a)))
      ≤ Real.exp (-α * Δ) * ((1 / (α * gmin)) * (Real.exp (α * Δ) - 1)) :=
        mul_le_mul_of_nonneg_left hbase hexp_nonneg
    _ = (1 / (α * gmin)) * (1 - Real.exp (-α * Δ)) := by
        have hcancel : Real.exp (-α * Δ) * Real.exp (α * Δ) = 1 := by
          rw [← Real.exp_add, show -α * Δ + α * Δ = 0 by ring, Real.exp_zero]
        linear_combination (1 / (α * gmin)) * hcancel
    _ ≤ 1 / (α * gmin) := by
        have hpos : 0 ≤ 1 / (α * gmin) := by positivity
        nlinarith [mul_nonneg hpos hexp_nonneg]

/-- **Localized gate-integral × decay cancellation.**  The `SelectorDynSol`-usable variant:
the solution's integrated gain `G` only has its derivative `G' = χ_gate·gain` on the schedule
domain `[0,∞)` (`G_hasDeriv`), NOT globally — but it IS globally continuous (`cont_G`).  So
this takes `HasDerivAt G (r t) t` only for `t ∈ [a,b]` (the gate window, always `⊆ [0,∞)`),
plus global continuity, and concludes the same product bound `exp(−αΔG)·∫ ≤ 1/(α·gmin)`.
Re-derives the FTC chain of `gate_perturbation_integral_bound` with interval-local
derivatives. -/
theorem gate_perturb_integral_times_decay_local
    {a b α gmin : ℝ} {G r : ℝ → ℝ}
    (hab : a ≤ b) (hα : 0 < α) (hgmin : 0 < gmin)
    (hGcont : Continuous G)
    (hGder : ∀ t ∈ Set.Icc a b, HasDerivAt G (r t) t)
    (hr_cont : Continuous r)
    (hr : ∀ t ∈ Set.Icc a b, gmin ≤ r t) :
    Real.exp (-α * (G b - G a)) * (∫ t in a..b, Real.exp (α * (G t - G a)))
      ≤ 1 / (α * gmin) := by
  have hden : 0 < α * gmin := mul_pos hα hgmin
  set Δ : ℝ := G b - G a with hΔ
  have hexp_nonneg : 0 ≤ Real.exp (-α * Δ) := (Real.exp_pos _).le
  set F : ℝ → ℝ := fun t => Real.exp (α * (G t - G a)) with hFdef
  have hFcont : Continuous F := by
    simpa [hFdef] using
      Real.continuous_exp.comp (continuous_const.mul (hGcont.sub continuous_const))
  -- local FTC for `∫ α·r·F = F b − F a`
  have hFder : ∀ t ∈ Set.uIcc a b, HasDerivAt F (α * r t * F t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at ht
    have h := (((hGder t htIcc).sub_const (G a)).const_mul α).exp
    convert h using 1
    simp only [hFdef]; ring
  have hcont' : Continuous (fun t => α * r t * F t) :=
    (continuous_const.mul hr_cont).mul hFcont
  have hint_arF : (∫ t in a..b, α * r t * F t) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFder (hcont'.intervalIntegrable a b)
  -- pointwise `F ≤ (1/(α·gmin))·(α·r·F)` on the window (`F·1`, the bare integrand)
  have hptwise : ∀ t ∈ Set.Icc a b, F t ≤ (1 / (α * gmin)) * (α * r t * F t) := by
    intro t ht
    have hFpos : 0 < F t := Real.exp_pos _
    have hrt : gmin ≤ r t := hr t ht
    have eq1 : (1 / (α * gmin)) * (α * r t * F t) = r t * F t / gmin := by
      field_simp
    rw [eq1, le_div_iff₀ hgmin]
    nlinarith [mul_nonneg hFpos.le (sub_nonneg.mpr hrt), hFpos]
  have hf_int : IntervalIntegrable F MeasureTheory.volume a b :=
    hFcont.intervalIntegrable a b
  have hg_int : IntervalIntegrable (fun t => (1 / (α * gmin)) * (α * r t * F t))
      MeasureTheory.volume a b := (continuous_const.mul hcont').intervalIntegrable a b
  have hbase : (∫ t in a..b, Real.exp (α * (G t - G a)))
      ≤ (1 / (α * gmin)) * (Real.exp (α * Δ) - 1) := by
    calc (∫ t in a..b, F t)
        ≤ ∫ t in a..b, (1 / (α * gmin)) * (α * r t * F t) :=
          intervalIntegral.integral_mono_on hab hf_int hg_int hptwise
      _ = (1 / (α * gmin)) * ∫ t in a..b, α * r t * F t := by
          rw [intervalIntegral.integral_const_mul]
      _ = (1 / (α * gmin)) * (F b - F a) := by rw [hint_arF]
      _ = (1 / (α * gmin)) * (Real.exp (α * Δ) - 1) := by
          simp only [hFdef, hΔ, sub_self, mul_zero, Real.exp_zero]
  calc Real.exp (-α * Δ) * (∫ t in a..b, Real.exp (α * (G t - G a)))
      ≤ Real.exp (-α * Δ) * ((1 / (α * gmin)) * (Real.exp (α * Δ) - 1)) :=
        mul_le_mul_of_nonneg_left hbase hexp_nonneg
    _ = (1 / (α * gmin)) * (1 - Real.exp (-α * Δ)) := by
        have hcancel : Real.exp (-α * Δ) * Real.exp (α * Δ) = 1 := by
          rw [← Real.exp_add, show -α * Δ + α * Δ = 0 by ring, Real.exp_zero]
        linear_combination (1 / (α * gmin)) * hcancel
    _ ≤ 1 / (α * gmin) := by
        have hpos : 0 ≤ 1 / (α * gmin) := by positivity
        nlinarith [mul_nonneg hpos hexp_nonneg]

/-- **Concrete gate-integral decay for the M_U selector sol on the gate window.**  Applies
`gate_perturb_integral_times_decay_local` to the sol with `χ_gate = ((1+sin t)/2)^M`,
`gain = g₀·exp(cα·t)` over the rising gate sub-window `[2πj+π/6, 2πj+π/2]`.  The window-uniform
gain lower bound is `gmin_j = (3/4)^M·g₀·exp(cα·(2πj+π/6))` (from `sin t ≥ ½` ⇒ `((1+sin)/2)^M ≥
(3/4)^M` via `chiGate_lb`, and `exp(cα·a) ≤ exp(cα·t)`).  CONCLUSION: the εmix reset-residual
gate factor `exp(−αΔG_j)·∫ exp(α(G−Ga)) ≤ 1/(α·gmin_j)`, which `→ 0` as `j → ∞`
(`gmin_j → ∞`).  This is the concrete #8 fact: NO fixed `Kint` — the decay is in the product. -/
theorem selector_gate_integral_decay_window
    {d B : ℕ} {V : Type} [Fintype V] {branch : V → BranchData d B}
    {Pv : V → (Fin d → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF kappaF : ℝ → ℝ} (M : ℕ) {g₀ cα α : ℝ}
    (hα : 0 < α) (hcα : 0 < cα) (hg₀ : 0 < g₀)
    (sol : SelectorDynSol d B V p selectorSchedule branch
      chiResetF (fun t => ((1 + Real.sin t) / 2) ^ M) kappaF
      (fun t => g₀ * Real.exp (cα * t)) Pv) (j : ℕ) :
    Real.exp (-α * (sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 2)
            - sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 6)))
        * (∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ) + Real.pi / 2),
            Real.exp (α * (sol.G t - sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 6))))
      ≤ 1 / (α * ((3 / 4 : ℝ) ^ M * g₀
          * Real.exp (cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6)))) := by
  have hpi := Real.pi_pos
  set a : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi / 6 with ha
  set b : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi / 2 with hb
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; positivity
  have hab : a ≤ b := by rw [ha, hb]; linarith
  refine gate_perturb_integral_times_decay_local (G := sol.G)
    (r := fun t => ((1 + Real.sin t) / 2) ^ M * (g₀ * Real.exp (cα * t)))
    hab hα (by positivity) sol.cont_G ?_ (by fun_prop) ?_
  · -- `HasDerivAt sol.G (χ_gate·gain) t` on the window (⊆ domain `[0,∞)`)
    intro t ht
    have htdom : t ∈ selectorSchedule.domain := by
      show t ∈ Set.Ici (0 : ℝ)
      exact Set.mem_Ici.mpr (le_trans ha0 ht.1)
    exact sol.G_hasDeriv t htdom
  · -- window-uniform gain lower bound `gmin_j ≤ χ_gate t · gain t`
    intro t ht
    have hsin : (1 : ℝ) / 2 ≤ Real.sin t :=
      sin_ge_half_of_gate_window j (by rw [ha, hb] at ht; exact ht)
    have hchi : (3 / 4 : ℝ) ^ M ≤ ((1 + Real.sin t) / 2) ^ M := by
      have h := chiGate_lb M hsin (by norm_num : (-1 : ℝ) ≤ 1 / 2)
      have heq : ((1 + (1 / 2 : ℝ)) / 2) ^ M = (3 / 4 : ℝ) ^ M := by norm_num
      rwa [heq] at h
    have hgain : Real.exp (cα * a) ≤ Real.exp (cα * t) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.1, hcα.le])
    have hg0e : (0 : ℝ) ≤ g₀ * Real.exp (cα * t) := by positivity
    calc (3 / 4 : ℝ) ^ M * g₀ * Real.exp (cα * a)
        = (3 / 4 : ℝ) ^ M * (g₀ * Real.exp (cα * a)) := by ring
      _ ≤ (3 / 4 : ℝ) ^ M * (g₀ * Real.exp (cα * t)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hgain hg₀.le
      _ ≤ ((1 + Real.sin t) / 2) ^ M * (g₀ * Real.exp (cα * t)) :=
          mul_le_mul_of_nonneg_right hchi hg0e

open Filter in
/-- **The gate-factor bound vanishes as `j → ∞`.**  `1/(α·gmin_j) → 0` because
`gmin_j = (3/4)^M·g₀·exp(cα·(2πj+π/6))` grows to `+∞` (the exponential clock gain).  Together
with `selector_gate_integral_decay_window` this is the asymptotic statement that the εmix
reset-residual gate factor `exp(−αΔG_j)·∫ exp(α(G−Ga))` vanishes — the no-floor advantage,
with NO fixed `Kint`. -/
theorem selector_gate_decay_tendsto_zero
    (M : ℕ) {g₀ cα α : ℝ} (hα : 0 < α) (hcα : 0 < cα) (hg₀ : 0 < g₀) :
    Tendsto
      (fun j : ℕ => 1 / (α * ((3 / 4 : ℝ) ^ M * g₀
        * Real.exp (cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6)))))
      atTop (nhds 0) := by
  have hE : Tendsto
      (fun j : ℕ => Real.exp (cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6))) atTop atTop := by
    apply Real.tendsto_exp_atTop.comp
    apply Filter.Tendsto.const_mul_atTop hcα
    apply Filter.tendsto_atTop_add_const_right atTop (Real.pi / 6)
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      tendsto_natCast_atTop_atTop
  have hD : Tendsto
      (fun j : ℕ => α * ((3 / 4 : ℝ) ^ M * g₀
        * Real.exp (cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6)))) atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hα
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < (3 / 4 : ℝ) ^ M * g₀) hE
  have hinv : Tendsto
      (fun j : ℕ => (α * ((3 / 4 : ℝ) ^ M * g₀
        * Real.exp (cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6))))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hD
  simpa only [one_div] using hinv

/-- **εmix split (the Kprod refactor core).**  Any bound `X ≤ (Qa0 + ρb·Cb·Kint)·Edecay` splits
into `X ≤ Qa0·Edecay + ρb·Cb·Kprod` once the reset slot is replaced by the PRODUCT bound
`Kint·Edecay ≤ Kprod` (with `Edecay = exp(−αΔG)`).  This is the clean algebraic core of ChatGPT's
(life Q1) split refactor — it avoids re-threading the ~24 hypotheses of
`selector_phase_onehot_perturbed`: apply it directly to that lemma's two conclusions, and to the
`card·R·(…)` form at the recurrence level.  For the M_U gate window, `Kprod = 1/(α·gmin_j)`
discharged by `selector_gate_integral_decay_window` (so the unsatisfiable fixed `Kint` is gone:
the reset term becomes `ρb·Cb/(α·gmin_j) → 0`). -/
theorem epsmix_split_bound {Qa0 ρb Cb Kint Kprod Edecay X : ℝ}
    (hscale : 0 ≤ ρb * Cb) (hKprod : Kint * Edecay ≤ Kprod)
    (hbase : X ≤ (Qa0 + ρb * Cb * Kint) * Edecay) :
    X ≤ Qa0 * Edecay + ρb * Cb * Kprod := by
  have hstep : ρb * Cb * (Kint * Edecay) ≤ ρb * Cb * Kprod :=
    mul_le_mul_of_nonneg_left hKprod hscale
  have hid : (Qa0 + ρb * Cb * Kint) * Edecay
      = Qa0 * Edecay + ρb * Cb * (Kint * Edecay) := by ring
  calc X ≤ (Qa0 + ρb * Cb * Kint) * Edecay := hbase
    _ = Qa0 * Edecay + ρb * Cb * (Kint * Edecay) := hid
    _ ≤ Qa0 * Edecay + ρb * Cb * Kprod := by linarith [hstep]

/-- **The reset gate-factor bound is GEOMETRIC in `j`.**  `1/(α·gmin_j) = Creset·exp(−(2π·cα)·j)`
with `Creset = 1/(α·(3/4)^M·g₀·exp(cα·π/6))` — the closed form behind `selector_gate_decay_tendsto_zero`,
exposing the geometric decay rate `λ_reset = 2π·cα` needed for budget summability
(`weightedDefect_summable_of_geometric`).  Pure algebra: `exp(cα(2πj+π/6)) = exp(cα·π/6)·exp(2π·cα·j)`. -/
theorem inv_alpha_gmin_eq_const_mul_exp (M : ℕ) {g₀ cα α : ℝ} (hα : α ≠ 0) (hg₀ : g₀ ≠ 0) (j : ℕ) :
    1 / (α * ((3 / 4 : ℝ) ^ M * g₀
        * Real.exp (cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6))))
      = (1 / (α * ((3 / 4 : ℝ) ^ M * g₀ * Real.exp (cα * (Real.pi / 6)))))
          * Real.exp (-(2 * Real.pi * cα) * (j : ℝ)) := by
  have hAj : Real.exp ((2 * Real.pi * cα) * (j : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have hB : Real.exp (cα * (Real.pi / 6)) ≠ 0 := (Real.exp_pos _).ne'
  have hpow : ((3 / 4 : ℝ) ^ M) ≠ 0 := by positivity
  rw [show cα * (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        = (2 * Real.pi * cα) * (j : ℝ) + cα * (Real.pi / 6) by ring,
      Real.exp_add,
      show (-(2 * Real.pi * cα) * (j : ℝ)) = -((2 * Real.pi * cα) * (j : ℝ)) by ring,
      Real.exp_neg]
  field_simp

end Ripple.BoundedUniversality.BGP
