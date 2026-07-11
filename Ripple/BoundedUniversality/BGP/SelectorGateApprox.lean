import Ripple.BoundedUniversality.BGP.SelectorField

/-!
Ripple.BoundedUniversality.BGP.SelectorGateApprox
-----------------------------
Approximate-gate relaxation of the selector gate-phase logistic bound (option (a),
approved 2026-06-14).  The selector math layer's `gate_mix_error` assumes EXACT gate
conditions `χ_reset = 0` / `χ_gate = 1` on the gate window, which no analytic/polynomial
gate can satisfy on a non-degenerate interval.  This file relaxes the analysis to
approximate gates, where the per-cycle defect picks up a residual that the GROWING gate
gain suppresses (floor `~ ρ_b/(α·g_min) → 0`).

Entry lemma: the key integral estimate — the perturbation, weighted by the growing
`exp(α(G−Ga))`, integrates to `O(1/g_min)·exp(αΔG)` because `G' = r ≥ g_min`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set

/-- General quotient derivative for the low-odds `L/(1−L)` — unlike
`hasDerivWithinAt_oddsLo`, this takes an ARBITRARY derivative `d` for `L` (not the pure
logistic form), needed for the perturbed ODE `L' = r·P·L(1−L) + ρ`. -/
theorem hasDerivWithinAt_oddsLo_general {L : ℝ → ℝ} {t d : ℝ} {s : Set ℝ}
    (hL : HasDerivWithinAt L d s t) (hL1 : 1 - L t ≠ 0) :
    HasDerivWithinAt (fun u => L u / (1 - L u)) (d / (1 - L t) ^ 2) s t := by
  have hden : HasDerivWithinAt (fun u => 1 - L u) (-d) s t := by
    simpa using (hasDerivWithinAt_const t s (1 : ℝ)).sub hL
  have hquot := hL.div hden hL1
  convert hquot using 1
  field_simp
  ring

/-- General quotient derivative for the high-odds `(1−L)/L` (arbitrary `L'`). -/
theorem hasDerivWithinAt_oddsHi_general {L : ℝ → ℝ} {t d : ℝ} {s : Set ℝ}
    (hL : HasDerivWithinAt L d s t) (hL0 : L t ≠ 0) :
    HasDerivWithinAt (fun u => (1 - L u) / L u) (-d / L t ^ 2) s t := by
  have hnum : HasDerivWithinAt (fun u => 1 - L u) (-d) s t := by
    simpa using (hasDerivWithinAt_const t s (1 : ℝ)).sub hL
  have hquot := hnum.div hL hL0
  convert hquot using 1
  field_simp
  ring

/-- **Gate perturbation integral estimate.**  With the integrated gain `G` growing at rate
`r ≥ g_min > 0`, a nonnegative perturbation `ρ ≤ c` weighted by `exp(α(G−Ga))` integrates to
at most `(c/(α·g_min))·(exp(αΔG)−1)`.  Mechanism: `d/dt exp(α(G−Ga)) = α·r·exp ≥ α·g_min·exp`,
so `exp ≤ (1/(α·g_min))·d/dt exp`, and the integral telescopes by the FTC.  This is why the
fixed reset residual is suppressed by the growing gain (no Gronwall needed). -/
theorem gate_perturbation_integral_bound
    {a b α gmin c : ℝ} {G r ρ : ℝ → ℝ}
    (hab : a ≤ b) (hα : 0 < α) (hgmin : 0 < gmin)
    (hGder : ∀ t, HasDerivAt G (r t) t)
    (hr_cont : Continuous r) (hρ_cont : Continuous ρ)
    (hr : ∀ t ∈ Icc a b, gmin ≤ r t)
    (hρ_nonneg : ∀ t ∈ Icc a b, 0 ≤ ρ t) (hρ_le : ∀ t ∈ Icc a b, ρ t ≤ c) :
    (∫ t in a..b, Real.exp (α * (G t - G a)) * ρ t)
      ≤ (c / (α * gmin)) * (Real.exp (α * (G b - G a)) - 1) := by
  have hGcont : Continuous G :=
    continuous_iff_continuousAt.mpr (fun t => (hGder t).continuousAt)
  set F : ℝ → ℝ := fun t => Real.exp (α * (G t - G a)) with hFdef
  have hFder : ∀ t, HasDerivAt F (α * r t * F t) t := by
    intro t
    have h := (((hGder t).sub_const (G a)).const_mul α).exp
    convert h using 1
    simp only [hFdef]; ring
  have hFcont : Continuous F := by
    simpa [hFdef] using
      Real.continuous_exp.comp (continuous_const.mul (hGcont.sub continuous_const))
  have hint_arF : (∫ t in a..b, α * r t * F t) = F b - F a := by
    have hcont' : Continuous (fun t => α * r t * F t) :=
      (continuous_const.mul hr_cont).mul hFcont
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hFder t)
      (hcont'.intervalIntegrable a b)
  have hptwise : ∀ t ∈ Icc a b, F t * ρ t ≤ (c / (α * gmin)) * (α * r t * F t) := by
    intro t ht
    have hFpos : 0 < F t := Real.exp_pos _
    have hrt : gmin ≤ r t := hr t ht
    have hρt : ρ t ≤ c := hρ_le t ht
    have hc0 : 0 ≤ c := le_trans (hρ_nonneg t ht) hρt
    have eq1 : (c / (α * gmin)) * (α * r t * F t) = c * r t * F t / gmin := by
      field_simp
    rw [eq1, le_div_iff₀ hgmin]
    nlinarith [mul_nonneg (mul_nonneg hFpos.le hc0) (sub_nonneg.mpr hrt),
      mul_nonneg (mul_nonneg hFpos.le hgmin.le) (sub_nonneg.mpr hρt)]
  have hf_int : IntervalIntegrable (fun t => F t * ρ t) MeasureTheory.volume a b :=
    (hFcont.mul hρ_cont).intervalIntegrable a b
  have hg_int : IntervalIntegrable (fun t => (c / (α * gmin)) * (α * r t * F t))
      MeasureTheory.volume a b :=
    (continuous_const.mul ((continuous_const.mul hr_cont).mul hFcont)).intervalIntegrable a b
  calc (∫ t in a..b, F t * ρ t)
      ≤ ∫ t in a..b, (c / (α * gmin)) * (α * r t * F t) :=
        intervalIntegral.integral_mono_on hab hf_int hg_int hptwise
    _ = (c / (α * gmin)) * ∫ t in a..b, α * r t * F t := by
        rw [intervalIntegral.integral_const_mul]
    _ = (c / (α * gmin)) * (F b - F a) := by rw [hint_arF]
    _ = (c / (α * gmin)) * (Real.exp (α * (G b - G a)) - 1) := by
        simp only [hFdef, sub_self, mul_zero, Real.exp_zero]

/-- **Perturbed false-view logistic bound (approximate gates).**  The false view's gate ODE
with the reset residual `ρ ≥ −ρb` (`L' = r·P·L(1−L) + ρ`, `P ≤ −α`).  The bound `L b ≤ …`
only needs the UPPER bound `ρ ≤ ρb` (the residual pushing `L` up is the bad direction); the
lower bound on `ρ` is irrelevant here, so `ρ ≥ −ρb` (matching the true view, satisfiable from
the δ-relaxed barrier `λ_v ≤ ½+δ`) suffices.  The bound degrades only by
`(ρb/(1−Lmax)²)·∫exp(α(G−Ga))` — and that integral is
`O(1/g_min)·exp(αΔG)` (`gate_perturbation_integral_bound`), so the false-view floor is
`~ ρb/(g_min) → 0`.  The integral bound `Kint` is taken as a hypothesis (discharged by
`gate_perturbation_integral_bound`), decoupling the deriv settings.  `Continuous G` (the
solution's `cont_G`) gives the FTC boundary. -/
theorem logistic_false_bound_perturbed
    {a b α Lmax ρb Kint Qa0 : ℝ} {L r P G ρ : ℝ → ℝ}
    (hab : a ≤ b) (hLmax1 : Lmax < 1)
    (hGcontglob : Continuous G)
    (hLder : ∀ t ∈ Ico a b,
      HasDerivWithinAt L (r t * P t * (L t * (1 - L t)) + ρ t) (Ici t) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hLcont : ContinuousOn L (Icc a b))
    (hr0 : ∀ t ∈ Ico a b, 0 ≤ r t) (hP : ∀ t ∈ Ico a b, P t ≤ -α)
    (hunit : ∀ t ∈ Icc a b, 0 < L t ∧ L t < 1) (hLa_le : L a / (1 - L a) ≤ Qa0)
    (hLub : ∀ t ∈ Icc a b, L t ≤ Lmax)
    (hρ_ge : ∀ t ∈ Ico a b, -ρb ≤ ρ t) (hρ_le : ∀ t ∈ Ico a b, ρ t ≤ ρb) (hρb : 0 ≤ ρb)
    (hint : (∫ t in a..b, Real.exp (α * (G t - G a))) ≤ Kint) (hKint : 0 ≤ Kint) :
    L b ≤ (Qa0 + ρb / (1 - Lmax) ^ 2 * Kint) * Real.exp (-α * (G b - G a)) := by
  have hLmax0 : (0 : ℝ) < 1 - Lmax := by linarith
  set c : ℝ := ρb / (1 - Lmax) ^ 2 with hcdef
  have hc0 : 0 ≤ c := by
    apply div_nonneg hρb; positivity
  set E : ℝ → ℝ := fun t => Real.exp (α * (G t - G a)) with hEdef
  have hEcont : Continuous E := by
    simpa [hEdef] using
      Real.continuous_exp.comp (continuous_const.mul (hGcontglob.sub continuous_const))
  set Q : ℝ → ℝ := fun t => (L t / (1 - L t)) * E t with hQdef
  -- Q derivative (raw product-rule form)
  have hQder : ∀ t ∈ Ico a b,
      HasDerivWithinAt Q
        ((r t * P t * (L t * (1 - L t)) + ρ t) / (1 - L t) ^ 2 * E t
          + L t / (1 - L t) * (E t * (α * r t))) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hL1 : 1 - L t ≠ 0 := by have := (hunit t htc).2; linarith
    have hodds := hasDerivWithinAt_oddsLo_general (hLder t ht) hL1
    have hE : HasDerivWithinAt E (E t * (α * r t)) (Ici t) t := by
      have := (((hGder t ht).sub_const (G a)).const_mul α).exp
      simpa [hEdef, mul_comm] using this
    exact hodds.mul hE
  -- boundary B(t) = Qa0 + c * ∫_a^t E
  set B : ℝ → ℝ := fun t => Qa0 + c * ∫ s in a..t, E s with hBdef
  have hBder : ∀ t ∈ Ico a b, HasDerivWithinAt B (c * E t) (Ici t) t := by
    intro t ht
    have hftc : HasDerivAt (fun u => ∫ s in a..u, E s) (E t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hEcont.intervalIntegrable a t)
        (hEcont.stronglyMeasurableAtFilter _ _) hEcont.continuousAt
    have := (hftc.const_mul c).const_add 1
    simpa [hBdef] using this.hasDerivWithinAt
  have hBcont : ContinuousOn B (Icc a b) := by
    have hprim : Continuous (fun u => ∫ s in a..u, E s) :=
      continuous_iff_continuousAt.mpr (fun t =>
        (intervalIntegral.integral_hasDerivAt_right (hEcont.intervalIntegrable a t)
          (hEcont.stronglyMeasurableAtFilter _ _) hEcont.continuousAt).continuousAt)
    simp only [hBdef]
    exact (continuous_const.add (continuous_const.mul hprim)).continuousOn
  have hQcont : ContinuousOn Q (Icc a b) := by
    apply ContinuousOn.mul
    · exact hLcont.div (continuousOn_const.sub hLcont)
        (fun t ht => by have := (hunit t ht).2; intro h; linarith [sub_eq_zero.mp h])
    · exact hEcont.continuousOn
  have hQa : Q a = L a / (1 - L a) := by
    simp only [hQdef, hEdef, sub_self, mul_zero, Real.exp_zero, mul_one]
  have hBa : B a = Qa0 := by simp [hBdef]
  -- Q' ≤ B' pointwise
  have hcomp : ∀ t ∈ Ico a b,
      (r t * P t * (L t * (1 - L t)) + ρ t) / (1 - L t) ^ 2 * E t
        + L t / (1 - L t) * (E t * (α * r t)) ≤ c * E t := by
    intro t ht
    have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hLpos : 0 < L t := (hunit t htc).1
    have hL1 : 0 < 1 - L t := by have := (hunit t htc).2; linarith
    have hEpos : 0 < E t := Real.exp_pos _
    have hLubt : L t ≤ Lmax := hLub t htc
    have hPt : P t ≤ -α := hP t ht
    have hrt : 0 ≤ r t := hr0 t ht
    have hρt : ρ t ≤ ρb := hρ_le t ht
    have hsq : (1 - Lmax) ^ 2 ≤ (1 - L t) ^ 2 := by nlinarith [hLubt, hLmax0, hL1]
    have hcsq : ρb ≤ c * (1 - L t) ^ 2 := by
      rw [hcdef, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hsq hρb
    have hfield :
        (r t * P t * (L t * (1 - L t)) + ρ t) / (1 - L t) ^ 2 * E t
            + L t / (1 - L t) * (E t * (α * r t))
          = ((r t * P t * (L t * (1 - L t)) + ρ t) * E t
              + L t * (E t * (α * r t)) * (1 - L t)) / (1 - L t) ^ 2 := by
      field_simp
    rw [hfield, div_le_iff₀ (by positivity : (0:ℝ) < (1 - L t) ^ 2)]
    have hterm1 : (E t * L t * (1 - L t) * r t) * (P t + α) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (mul_nonneg hEpos.le hLpos.le) hL1.le) hrt)
        (by linarith [hPt])
    nlinarith [hterm1, mul_nonneg hEpos.le (sub_nonneg.mpr hρt),
      mul_nonneg hEpos.le (sub_nonneg.mpr hcsq)]
  -- image_le
  have hbound : ∀ ⦃x⦄, x ∈ Icc a b → Q x ≤ B x :=
    image_le_of_deriv_right_le_deriv_boundary hQcont hQder
      (by rw [hQa, hBa]; exact hLa_le) hBcont hBder hcomp
  have hQb : Q b ≤ B b := hbound (right_mem_Icc.mpr hab)
  -- conclude
  have hLb := hunit b (right_mem_Icc.mpr hab)
  have hBb_le : B b ≤ Qa0 + c * Kint := by
    rw [hBdef]
    have : c * (∫ s in a..b, E s) ≤ c * Kint := mul_le_mul_of_nonneg_left hint hc0
    linarith
  have hEbpos : 0 < E b := Real.exp_pos _
  have hodds_le : L b / (1 - L b) ≤ (Qa0 + c * Kint) * Real.exp (-α * (G b - G a)) := by
    have hQble : Q b ≤ Qa0 + c * Kint := le_trans hQb hBb_le
    have hEb : E b = Real.exp (α * (G b - G a)) := rfl
    have hexpinv : Real.exp (-α * (G b - G a)) = (E b)⁻¹ := by
      rw [hEb, show (-α * (G b - G a)) = -(α * (G b - G a)) by ring, Real.exp_neg]
    rw [hexpinv]
    have : L b / (1 - L b) = Q b * (E b)⁻¹ := by
      rw [hQdef]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hQble (by positivity)
  have hstep : L b ≤ L b / (1 - L b) := by
    rw [le_div_iff₀ (by linarith [hLb.2] : (0:ℝ) < 1 - L b)]
    nlinarith [hLb.1, hLb.2]
  calc L b ≤ L b / (1 - L b) := hstep
    _ ≤ (Qa0 + c * Kint) * Real.exp (-α * (G b - G a)) := hodds_le
    _ = (Qa0 + ρb / (1 - Lmax) ^ 2 * Kint) * Real.exp (-α * (G b - G a)) := by rw [hcdef]

/-- **Perturbed true-view logistic bound (approximate gates).**  Symmetric to the false-view
bound: the true view's gate ODE with reset residual (`L' = r·P·L(1−L) + ρ`, `P ≥ α`, `ρ ≥ −ρb`,
`L ≥ Lmin > 0`).  The residual pushes `L` down (away from 1), but the growing gain suppresses it:
`1 − L b ≤ (1 + (ρb/Lmin²)·Kint)·exp(−αΔG)`, floor `~ ρb/(Lmin²·α·gmin) → 0`. -/
theorem logistic_true_bound_perturbed
    {a b α Lmin ρb Kint Qa0 : ℝ} {L r P G ρ : ℝ → ℝ}
    (hab : a ≤ b) (hLmin0 : 0 < Lmin)
    (hGcontglob : Continuous G)
    (hLder : ∀ t ∈ Ico a b,
      HasDerivWithinAt L (r t * P t * (L t * (1 - L t)) + ρ t) (Ici t) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hLcont : ContinuousOn L (Icc a b))
    (hr0 : ∀ t ∈ Ico a b, 0 ≤ r t) (hP : ∀ t ∈ Ico a b, α ≤ P t)
    (hunit : ∀ t ∈ Icc a b, 0 < L t ∧ L t < 1) (hLa_le : (1 - L a) / L a ≤ Qa0)
    (hLlb : ∀ t ∈ Icc a b, Lmin ≤ L t)
    (hρ_ge : ∀ t ∈ Ico a b, -ρb ≤ ρ t) (hρb : 0 ≤ ρb)
    (hint : (∫ t in a..b, Real.exp (α * (G t - G a))) ≤ Kint) (hKint : 0 ≤ Kint) :
    1 - L b ≤ (Qa0 + ρb / Lmin ^ 2 * Kint) * Real.exp (-α * (G b - G a)) := by
  set c : ℝ := ρb / Lmin ^ 2 with hcdef
  have hc0 : 0 ≤ c := by apply div_nonneg hρb; positivity
  set E : ℝ → ℝ := fun t => Real.exp (α * (G t - G a)) with hEdef
  have hEcont : Continuous E := by
    simpa [hEdef] using
      Real.continuous_exp.comp (continuous_const.mul (hGcontglob.sub continuous_const))
  set Q : ℝ → ℝ := fun t => ((1 - L t) / L t) * E t with hQdef
  have hQder : ∀ t ∈ Ico a b,
      HasDerivWithinAt Q
        (-(r t * P t * (L t * (1 - L t)) + ρ t) / L t ^ 2 * E t
          + (1 - L t) / L t * (E t * (α * r t))) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hL0 : L t ≠ 0 := (hunit t htc).1.ne'
    have hodds := hasDerivWithinAt_oddsHi_general (hLder t ht) hL0
    have hE : HasDerivWithinAt E (E t * (α * r t)) (Ici t) t := by
      have := (((hGder t ht).sub_const (G a)).const_mul α).exp
      simpa [hEdef, mul_comm] using this
    exact hodds.mul hE
  set B : ℝ → ℝ := fun t => Qa0 + c * ∫ s in a..t, E s with hBdef
  have hBder : ∀ t ∈ Ico a b, HasDerivWithinAt B (c * E t) (Ici t) t := by
    intro t ht
    have hftc : HasDerivAt (fun u => ∫ s in a..u, E s) (E t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hEcont.intervalIntegrable a t)
        (hEcont.stronglyMeasurableAtFilter _ _) hEcont.continuousAt
    have := (hftc.const_mul c).const_add Qa0
    simpa [hBdef] using this.hasDerivWithinAt
  have hBcont : ContinuousOn B (Icc a b) := by
    have hprim : Continuous (fun u => ∫ s in a..u, E s) :=
      continuous_iff_continuousAt.mpr (fun t =>
        (intervalIntegral.integral_hasDerivAt_right (hEcont.intervalIntegrable a t)
          (hEcont.stronglyMeasurableAtFilter _ _) hEcont.continuousAt).continuousAt)
    simp only [hBdef]
    exact (continuous_const.add (continuous_const.mul hprim)).continuousOn
  have hQcont : ContinuousOn Q (Icc a b) := by
    apply ContinuousOn.mul
    · exact (continuousOn_const.sub hLcont).div hLcont (fun t ht => (hunit t ht).1.ne')
    · exact hEcont.continuousOn
  have hQa : Q a = (1 - L a) / L a := by
    simp only [hQdef, hEdef, sub_self, mul_zero, Real.exp_zero, mul_one]
  have hBa : B a = Qa0 := by simp [hBdef]
  have hcomp : ∀ t ∈ Ico a b,
      -(r t * P t * (L t * (1 - L t)) + ρ t) / L t ^ 2 * E t
          + (1 - L t) / L t * (E t * (α * r t)) ≤ c * E t := by
    intro t ht
    have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hLpos : 0 < L t := (hunit t htc).1
    have hL1 : 0 < 1 - L t := by have := (hunit t htc).2; linarith
    have hEpos : 0 < E t := Real.exp_pos _
    have hLlbt : Lmin ≤ L t := hLlb t htc
    have hPt : α ≤ P t := hP t ht
    have hrt : 0 ≤ r t := hr0 t ht
    have hρt : -ρb ≤ ρ t := hρ_ge t ht
    have hsq : Lmin ^ 2 ≤ L t ^ 2 := by nlinarith [hLlbt, hLmin0, hLpos]
    have hcsq : ρb ≤ c * L t ^ 2 := by
      rw [hcdef, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hsq hρb
    have hfield :
        -(r t * P t * (L t * (1 - L t)) + ρ t) / L t ^ 2 * E t
            + (1 - L t) / L t * (E t * (α * r t))
          = (-(r t * P t * (L t * (1 - L t)) + ρ t) * E t
              + (1 - L t) * (E t * (α * r t)) * L t) / L t ^ 2 := by
      field_simp
    rw [hfield, div_le_iff₀ (by positivity : (0:ℝ) < L t ^ 2)]
    have hterm1 : (E t * L t * (1 - L t) * r t) * (α - P t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (mul_nonneg hEpos.le hLpos.le) hL1.le) hrt)
        (by linarith [hPt])
    nlinarith [hterm1, mul_nonneg hEpos.le (sub_nonneg.mpr hρt),
      mul_nonneg hEpos.le (sub_nonneg.mpr hcsq), hEpos.le, hρb]
  have hbound : ∀ ⦃x⦄, x ∈ Icc a b → Q x ≤ B x :=
    image_le_of_deriv_right_le_deriv_boundary hQcont hQder
      (by rw [hQa, hBa]; exact hLa_le) hBcont hBder hcomp
  have hQb : Q b ≤ B b := hbound (right_mem_Icc.mpr hab)
  have hLb := hunit b (right_mem_Icc.mpr hab)
  have hBb_le : B b ≤ Qa0 + c * Kint := by
    rw [hBdef]
    have : c * (∫ s in a..b, E s) ≤ c * Kint := mul_le_mul_of_nonneg_left hint hc0
    linarith
  have hodds_le : (1 - L b) / L b ≤ (Qa0 + c * Kint) * Real.exp (-α * (G b - G a)) := by
    have hQble : Q b ≤ Qa0 + c * Kint := le_trans hQb hBb_le
    have hexpinv : Real.exp (-α * (G b - G a)) = (E b)⁻¹ := by
      rw [hEdef, show (-α * (G b - G a)) = -(α * (G b - G a)) by ring, Real.exp_neg]
    rw [hexpinv]
    have hEbpos : 0 < E b := Real.exp_pos _
    have : (1 - L b) / L b = Q b * (E b)⁻¹ := by
      rw [hQdef]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hQble (by positivity)
  have hstep : 1 - L b ≤ (1 - L b) / L b := by
    rw [le_div_iff₀ hLb.1]
    nlinarith [hLb.1, hLb.2]
  calc 1 - L b ≤ (1 - L b) / L b := hstep
    _ ≤ (Qa0 + c * Kint) * Real.exp (-α * (G b - G a)) := hodds_le
    _ = (Qa0 + ρb / Lmin ^ 2 * Kint) * Real.exp (-α * (G b - G a)) := by rw [hcdef]

open scoped BigOperators

/-- **Approximate-gate one-hot phase.**  The analog of `selector_phase_onehot_reset` for
approximate gates: with the gate ODE `lam_v' = r·P_v·lam_v(1−lam_v) + ρ_v` (effective rate
`r = χ_gate·gain ≥ 0`, `G' = r`), the true view saturates to `1 − ε` and the false views
collapse to `ε` with the common bound `ε = (1 + ρb·Cb·Kint)·exp(−αΔG)`, `Cb` dominating both
`1/Lmin²` and `1/(1−Lmax)²`.  Combines `logistic_true_bound_perturbed` and
`logistic_false_bound_perturbed`; `ε → 0` as the gain grows (`Kint·exp(−αΔG) ~ 1/gmin`). -/
theorem selector_phase_onehot_perturbed {V : Type*} (vstar : V)
    {a b α Lmin Lmax ρb Kint Cb δ : ℝ} {r G : ℝ → ℝ} {lam P ρ : V → ℝ → ℝ}
    (hab : a ≤ b) (hLmin0 : 0 < Lmin) (hLmax1 : Lmax < 1) (hρb : 0 ≤ ρb) (hKint : 0 ≤ Kint)
    (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hGcontglob : Continuous G)
    (hCb_lo : 1 / Lmin ^ 2 ≤ Cb) (hCb_hi : 1 / (1 - Lmax) ^ 2 ≤ Cb)
    (hlamder : ∀ v, ∀ t ∈ Ico a b,
      HasDerivWithinAt (lam v) (r t * P v t * (lam v t * (1 - lam v t)) + ρ v t) (Ici t) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hlamcont : ∀ v, ContinuousOn (lam v) (Icc a b))
    (hr0 : ∀ t ∈ Ico a b, 0 ≤ r t)
    (hunit : ∀ v, ∀ t ∈ Icc a b, 0 < lam v t ∧ lam v t < 1)
    (hlama : ∀ v, |lam v a - 1 / 2| ≤ δ)
    (hPtrue : ∀ t ∈ Ico a b, α ≤ P vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, P v t ≤ -α)
    (hLlb_vstar : ∀ t ∈ Icc a b, Lmin ≤ lam vstar t)
    (hLub_false : ∀ v, v ≠ vstar → ∀ t ∈ Icc a b, lam v t ≤ Lmax)
    (hρ_vstar : ∀ t ∈ Ico a b, -ρb ≤ ρ vstar t)
    (hρ_false : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, -ρb ≤ ρ v t)
    (hρ_false_le : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, ρ v t ≤ ρb)
    (hint : (∫ t in a..b, Real.exp (α * (G t - G a))) ≤ Kint) :
    1 - lam vstar b ≤ ((1 / 2 + δ) / (1 / 2 - δ) + ρb * Cb * Kint) * Real.exp (-α * (G b - G a)) ∧
      ∀ v, v ≠ vstar →
        lam v b ≤ ((1 / 2 + δ) / (1 / 2 - δ) + ρb * Cb * Kint) * Real.exp (-α * (G b - G a)) := by
  have hexp0 : 0 ≤ Real.exp (-α * (G b - G a)) := (Real.exp_pos _).le
  have hhalfδ : 0 < 1 / 2 - δ := by linarith
  set Qa0 : ℝ := (1 / 2 + δ) / (1 / 2 - δ) with hQa0def
  -- odds bound at `a` (false view): `lam v a / (1 - lam v a) ≤ Qa0`
  have hQa0_false : ∀ v, lam v a / (1 - lam v a) ≤ Qa0 := by
    intro v
    have ha := hunit v a (left_mem_Icc.mpr hab)
    have habs := abs_le.mp (hlama v)
    rw [hQa0def, div_le_div_iff₀ (by linarith [ha.2]) hhalfδ]
    nlinarith [habs.1, habs.2]
  -- odds bound at `a` (true view): `(1 - lam v a) / lam v a ≤ Qa0`
  have hQa0_true : ∀ v, (1 - lam v a) / lam v a ≤ Qa0 := by
    intro v
    have ha := hunit v a (left_mem_Icc.mpr hab)
    have habs := abs_le.mp (hlama v)
    rw [hQa0def, div_le_div_iff₀ ha.1 hhalfδ]
    nlinarith [habs.1, habs.2]
  have hweaken_t : (Qa0 + ρb / Lmin ^ 2 * Kint) * Real.exp (-α * (G b - G a))
      ≤ (Qa0 + ρb * Cb * Kint) * Real.exp (-α * (G b - G a)) := by
    apply mul_le_mul_of_nonneg_right _ hexp0
    have : ρb / Lmin ^ 2 ≤ ρb * Cb := by
      rw [div_eq_mul_inv, ← one_div]
      exact mul_le_mul_of_nonneg_left hCb_lo hρb
    nlinarith [this, hKint]
  have hweaken_f : (Qa0 + ρb / (1 - Lmax) ^ 2 * Kint) * Real.exp (-α * (G b - G a))
      ≤ (Qa0 + ρb * Cb * Kint) * Real.exp (-α * (G b - G a)) := by
    apply mul_le_mul_of_nonneg_right _ hexp0
    have : ρb / (1 - Lmax) ^ 2 ≤ ρb * Cb := by
      rw [div_eq_mul_inv, ← one_div]
      exact mul_le_mul_of_nonneg_left hCb_hi hρb
    nlinarith [this, hKint]
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hweaken_t
    exact logistic_true_bound_perturbed hab hLmin0 hGcontglob (hlamder vstar) hGder
      (hlamcont vstar) hr0 hPtrue (hunit vstar) (hQa0_true vstar) hLlb_vstar hρ_vstar hρb hint hKint
  · intro v hv
    refine le_trans ?_ hweaken_f
    exact logistic_false_bound_perturbed hab hLmax1 hGcontglob (hlamder v) hGder
      (hlamcont v) hr0 (hPfalse v hv) (hunit v) (hQa0_false v) (hLub_false v hv)
      (hρ_false v hv) (hρ_false_le v hv) hρb hint hKint

/-- **Approximate-gate selector mixture error.**  The full clock-driven selector error with
approximate gates: the weighted branch mixture is within `card·R·ε` of the true branch value,
`ε = (1 + ρb·Cb·Kint)·exp(−αΔG) → 0`.  Combines `selector_phase_onehot_perturbed` with
`branch_mix_error`. -/
theorem selector_mix_error_perturbed {V : Type*} [Fintype V] [DecidableEq V] (vstar : V)
    {a b α Lmin Lmax ρb Kint Cb R δ : ℝ} {r G : ℝ → ℝ} {lam P ρ : V → ℝ → ℝ} (A : V → ℝ)
    (hab : a ≤ b) (hLmin0 : 0 < Lmin) (hLmax1 : Lmax < 1) (hρb : 0 ≤ ρb) (hKint : 0 ≤ Kint)
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hGcontglob : Continuous G)
    (hCb_lo : 1 / Lmin ^ 2 ≤ Cb) (hCb_hi : 1 / (1 - Lmax) ^ 2 ≤ Cb)
    (hlamder : ∀ v, ∀ t ∈ Ico a b,
      HasDerivWithinAt (lam v) (r t * P v t * (lam v t * (1 - lam v t)) + ρ v t) (Ici t) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (r t) (Ici t) t)
    (hlamcont : ∀ v, ContinuousOn (lam v) (Icc a b))
    (hr0 : ∀ t ∈ Ico a b, 0 ≤ r t)
    (hunit : ∀ v, ∀ t ∈ Icc a b, 0 < lam v t ∧ lam v t < 1)
    (hlama : ∀ v, |lam v a - 1 / 2| ≤ δ)
    (hPtrue : ∀ t ∈ Ico a b, α ≤ P vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, P v t ≤ -α)
    (hLlb_vstar : ∀ t ∈ Icc a b, Lmin ≤ lam vstar t)
    (hLub_false : ∀ v, v ≠ vstar → ∀ t ∈ Icc a b, lam v t ≤ Lmax)
    (hρ_vstar : ∀ t ∈ Ico a b, -ρb ≤ ρ vstar t)
    (hρ_false : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, -ρb ≤ ρ v t)
    (hρ_false_le : ∀ v, v ≠ vstar → ∀ t ∈ Ico a b, ρ v t ≤ ρb)
    (hint : (∫ t in a..b, Real.exp (α * (G t - G a))) ≤ Kint)
    (hA : ∀ v, |A v| ≤ R) :
    |(∑ v, lam v b * A v) - A vstar| ≤
      (Fintype.card V : ℝ) * R *
        (((1 / 2 + δ) / (1 / 2 - δ) + ρb * Cb * Kint) * Real.exp (-α * (G b - G a))) := by
  obtain ⟨htrue, hfalse⟩ := selector_phase_onehot_perturbed vstar hab hLmin0 hLmax1 hρb hKint
    hδ hδhalf hGcontglob hCb_lo hCb_hi hlamder hGder hlamcont hr0 hunit hlama hPtrue hPfalse
    hLlb_vstar hLub_false hρ_vstar hρ_false hρ_false_le hint
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hhalfδ : 0 < 1 / 2 - δ := by linarith
  have hεnn : 0 ≤ ((1 / 2 + δ) / (1 / 2 - δ) + ρb * Cb * Kint) * Real.exp (-α * (G b - G a)) := by
    apply mul_nonneg _ (Real.exp_pos _).le
    have hodds0 : 0 ≤ (1 / 2 + δ) / (1 / 2 - δ) := by positivity
    have : 0 ≤ ρb * Cb * Kint := by
      have hCb0 : 0 ≤ Cb := le_trans (by positivity) hCb_lo
      positivity
    linarith
  exact branch_mix_error vstar (fun v => lam v b) A hεnn hR
    (fun v => (hunit v b hb).1.le)
    (by linarith [htrue]) (hunit vstar b hb).2.le hfalse hA

/-- **(A2) SelectorDynSol-level approximate-gate mixture error.**  Regroups the iterator's
`lam_hasDeriv` (full field `χ_reset·κ·(½−λ) + χ_gate·gain·P·λ(1−λ)`) into the perturbed form
`r·P·λ(1−λ) + ρ` with `r = χ_gate·gain` (= `G'`) and `ρ = χ_reset·κ·(½−λ)`, then applies
`selector_mix_error_perturbed`.  The dynamic mixture at the gate-window end is within
`card·R·ε` of the true branch value, `ε = (1 + ρb·Cb·Kint)·exp(−α(G b − G a)) → 0`. -/
theorem gate_mix_error_approx
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF readoutP)
    (vstar : V) (i : Fin d)
    {a b α Lmin Lmax ρb Kint Cb R δ : ℝ}
    (hab : a ≤ b) (hLmin0 : 0 < Lmin) (hLmax1 : Lmax < 1) (hρb : 0 ≤ ρb) (hKint : 0 ≤ Kint)
    (hR : 0 ≤ R) (hCb_lo : 1 / Lmin ^ 2 ≤ Cb) (hCb_hi : 1 / (1 - Lmax) ^ 2 ≤ Cb)
    (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hdom : ∀ t ∈ Set.Ico a b, t ∈ sched.domain)
    (hr0 : ∀ t ∈ Set.Ico a b, 0 ≤ chiGateF t * gainF t)
    (hunit : ∀ v, ∀ t ∈ Set.Icc a b, 0 < sol.lam v t ∧ sol.lam v t < 1)
    (hlama : ∀ v, |sol.lam v a - 1 / 2| ≤ δ)
    (hPtrue : ∀ t ∈ Set.Ico a b, α ≤ sol.Pval vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico a b, sol.Pval v t ≤ -α)
    (hLlb_vstar : ∀ t ∈ Set.Icc a b, Lmin ≤ sol.lam vstar t)
    (hLub_false : ∀ v, v ≠ vstar → ∀ t ∈ Set.Icc a b, sol.lam v t ≤ Lmax)
    (hρ_vstar : ∀ t ∈ Set.Ico a b, -ρb ≤ chiResetF t * kappaF t * (1 / 2 - sol.lam vstar t))
    (hρ_false : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico a b,
      -ρb ≤ chiResetF t * kappaF t * (1 / 2 - sol.lam v t))
    (hρ_false_le : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico a b,
      chiResetF t * kappaF t * (1 / 2 - sol.lam v t) ≤ ρb)
    (hint : (∫ t in a..b, Real.exp (α * (sol.G t - sol.G a))) ≤ Kint)
    (hA : ∀ v, |BranchData.evalBranch (branch v) (sol.u b) i| ≤ R) :
    |selectorMixTarget branch sol.u sol.lam b i
        - BranchData.evalBranch (branch vstar) (sol.u b) i|
      ≤ (Fintype.card V : ℝ) * R *
          (((1 / 2 + δ) / (1 / 2 - δ) + ρb * Cb * Kint)
            * Real.exp (-α * (sol.G b - sol.G a))) := by
  have hmix := selector_mix_error_perturbed (V := V) vstar
    (r := fun t => chiGateF t * gainF t) (G := sol.G)
    (lam := fun v t => sol.lam v t) (P := sol.Pval)
    (ρ := fun v t => chiResetF t * kappaF t * (1 / 2 - sol.lam v t))
    (fun v => BranchData.evalBranch (branch v) (sol.u b) i)
    hab hLmin0 hLmax1 hρb hKint hR hδ hδhalf sol.cont_G hCb_lo hCb_hi
    (fun v t ht => by
      have h := (sol.lam_hasDeriv v t (hdom t ht)).hasDerivWithinAt (s := Set.Ici t)
      convert h using 1
      simp only [SelectorDynSol.Pval]
      ring)
    (fun t ht => by
      have h := (sol.G_hasDeriv t (hdom t ht)).hasDerivWithinAt (s := Set.Ici t)
      simpa using h)
    (fun v => (sol.cont_lam v).continuousOn)
    hr0 hunit hlama hPtrue hPfalse hLlb_vstar hLub_false hρ_vstar hρ_false hρ_false_le hint hA
  simpa only [selectorMixTarget, selectorF] using hmix

/-- **Per-cycle step with APPROXIMATE gate-phase precision.**  The realizable analog of
`selector_cycle_step_gate`: one cycle of the iterator where the gate window `[a, tHold]`
uses APPROXIMATE gates (`χ_reset ≤ η`, `χ_gate ≥ 1−η` — no exact `χ=0/1`), driving the
mixture error to `card·R·(1+ρb·Cb·Kint)·e^{−α·ΔG}` (`gate_mix_error_approx`), and
`cycle_step` composes this with the branch contraction, the hold drift, and the write
Reach to give the boundary-error recurrence.  This is `cycle_step ∘ gate_mix_error_approx`
— the per-cycle bound whose `εmix→0` (via the growing gain `ΔG`, with the residual floor
`ρb·Cb·Kint·e^{−αΔG}` ALSO suppressed by the gain) closes the all-time tube WITHOUT any
exact-gate assumption.  This is the realizable replacement for the exact
`selector_cycle_step_gate` in the M_U tube-closing. -/
theorem selector_cycle_step_gate_approx
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF readoutP)
    (vstar : V) (i : Fin d) (tStart a tHold tEnd : ℝ)
    (encC encStepC : Fin d → ℝ)
    {α Lmin Lmax ρb Kint Cb R εwrite εhold mult δ : ℝ}
    (hmult : 0 ≤ mult)
    (hab : a ≤ tHold) (hLmin0 : 0 < Lmin) (hLmax1 : Lmax < 1) (hρb : 0 ≤ ρb) (hKint : 0 ≤ Kint)
    (hR : 0 ≤ R) (hCb_lo : 1 / Lmin ^ 2 ≤ Cb) (hCb_hi : 1 / (1 - Lmax) ^ 2 ≤ Cb)
    (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    (hdom : ∀ t ∈ Set.Ico a tHold, t ∈ sched.domain)
    (hr0 : ∀ t ∈ Set.Ico a tHold, 0 ≤ chiGateF t * gainF t)
    (hunit : ∀ v, ∀ t ∈ Set.Icc a tHold, 0 < sol.lam v t ∧ sol.lam v t < 1)
    (hlama : ∀ v, |sol.lam v a - 1 / 2| ≤ δ)
    (hPtrue : ∀ t ∈ Set.Ico a tHold, α ≤ sol.Pval vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico a tHold, sol.Pval v t ≤ -α)
    (hLlb_vstar : ∀ t ∈ Set.Icc a tHold, Lmin ≤ sol.lam vstar t)
    (hLub_false : ∀ v, v ≠ vstar → ∀ t ∈ Set.Icc a tHold, sol.lam v t ≤ Lmax)
    (hρ_vstar : ∀ t ∈ Set.Ico a tHold, -ρb ≤ chiResetF t * kappaF t * (1 / 2 - sol.lam vstar t))
    (hρ_false : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico a tHold,
      -ρb ≤ chiResetF t * kappaF t * (1 / 2 - sol.lam v t))
    (hρ_false_le : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico a tHold,
      chiResetF t * kappaF t * (1 / 2 - sol.lam v t) ≤ ρb)
    (hint : (∫ t in a..tHold, Real.exp (α * (sol.G t - sol.G a))) ≤ Kint)
    (hA : ∀ v, |BranchData.evalBranch (branch v) (sol.u tHold) i| ≤ R)
    (hdiag : |BranchData.evalBranch (branch vstar) (sol.u tHold) i - encStepC i|
              ≤ mult * |sol.u tHold i - encC i|)
    (hhold : |sol.u tHold i - encC i| ≤ |sol.u tStart i - encC i| + εhold)
    (hwrite : |sol.u tEnd i - selectorMixTarget branch sol.u sol.lam tHold i| ≤ εwrite) :
    |sol.u tEnd i - encStepC i| ≤
      mult * |sol.u tStart i - encC i| +
        ((Fintype.card V : ℝ) * R *
            (((1 / 2 + δ) / (1 / 2 - δ) + ρb * Cb * Kint)
              * Real.exp (-α * (sol.G tHold - sol.G a)))
          + εwrite + mult * εhold) :=
  sol.cycle_step vstar i tStart tHold tEnd encC encStepC hmult
    (gate_mix_error_approx sol vstar i hab hLmin0 hLmax1 hρb hKint hR hCb_lo hCb_hi hδ hδhalf
      hdom hr0 hunit hlama hPtrue hPfalse hLlb_vstar hLub_false hρ_vstar hρ_false hρ_false_le
      hint hA)
    hdiag hhold hwrite

/-! ## Cos-gate window bounds (B2): the realizable gates are sharp on `{cos ≤ c0}` -/

/-- On the gate window `{sin t ≥ s0}` the (sin-based) gate envelope `((1+sin t)/2)^M` is bounded
below by `((1+s0)/2)^M` (`= 1 − η`).  With `s0 = 1/2, M = 1`: `χ_gate ≥ 3/4`.  The gate peaks at
`sin t = 1` (`t ≈ 2πj+π/2`), completing by the z-write so the selection is captured. -/
theorem chiGate_lb {s0 : ℝ} (M : ℕ) {t : ℝ} (ht : s0 ≤ Real.sin t) (hs0 : -1 ≤ s0) :
    ((1 + s0) / 2) ^ M ≤ ((1 + Real.sin t) / 2) ^ M := by
  gcongr <;> linarith [Real.neg_one_le_sin t]

/-- **Gate-window sin bound.**  On the rising gate sub-window `[2πj+π/6, 2πj+π/2]` of the
`selectorSchedule` cycle, `sin t ≥ 1/2` (sin is increasing on `[−π/2, π/2]`, `sin(π/6)=1/2`, plus
`2π`-periodicity).  Combined with `chiGate_lb (s0:=1/2)` this gives `χ_gate ≥ (3/4)^M` on the gate
window — the `hchi` hypothesis of `selector_gain_linear_growth` (with `a₀ = π/6`) and the gate
sharpness `gate_mix_error_approx` consumes. -/
theorem sin_ge_half_of_gate_window (j : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + Real.pi / 2)) :
    (1 : ℝ) / 2 ≤ Real.sin t := by
  obtain ⟨hl, hr⟩ := ht
  have hpi := Real.pi_pos
  set s := t - 2 * Real.pi * (j : ℝ) with hs
  have hsin : Real.sin t = Real.sin s := by
    have ht_eq : t = s + (j : ℝ) * (2 * Real.pi) := by rw [hs]; ring
    rw [ht_eq, Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  have hs1 : Real.pi / 6 ≤ s := by rw [hs]; linarith
  have hs2 : s ≤ Real.pi / 2 := by rw [hs]; linarith
  have hmem1 : Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmem2 : s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmono := Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 hs1
  rwa [Real.sin_pi_div_six] at hmono

theorem sin_ge_half_of_write_window (j : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)) :
    (1 : ℝ) / 2 ≤ Real.sin t := by
  obtain ⟨hl, hr⟩ := ht
  have hpi := Real.pi_pos
  set s := t - 2 * Real.pi * (j : ℝ) with hs_def
  have hsin : Real.sin t = Real.sin s := by
    have ht_eq : t = s + (j : ℝ) * (2 * Real.pi) := by rw [hs_def]; ring
    rw [ht_eq, Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  have hs1 : Real.pi / 6 ≤ s := by rw [hs_def]; linarith
  have hs2 : s ≤ 5 * Real.pi / 6 := by rw [hs_def]; linarith
  by_cases hle : s ≤ Real.pi / 2
  · have hmem1 : Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have hmem2 : s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have hmono := Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 hs1
    rwa [Real.sin_pi_div_six] at hmono
  · push_neg at hle
    have hsym : Real.sin s = Real.sin (Real.pi - s) := by
      rw [Real.sin_pi_sub]
    rw [hsym]
    have hps1 : Real.pi / 6 ≤ Real.pi - s := by linarith
    have hps2 : Real.pi - s ≤ Real.pi / 2 := by linarith
    have hmem1 : Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have hmem2 : Real.pi - s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have hmono := Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 hps1
    rwa [Real.sin_pi_div_six] at hmono

/-- **(Config-Reach item #1) The u-drift on the gate window decays — εhold → 0.**  On the gate
window `[2πj+π/6, 2πj+π/2]` the u-channel field magnitude is `A·α·bGateU = exp(t·cα − μ·qPulse)`.
With the M_U parameters (`A=1, cα=1/4, cμ=1, L=1`), `α t = exp(t/4)` (`alpha_eq_exp`), `μ t = t`
(`mu_eq_linear` + `μ 0 = 0`), and `qPulse t = (1+sin t)/2 ≥ 3/4` on the window (`sin ≥ 1/2`), so the
field `≤ exp(t/4 − 3t/4) = exp(−t/2) ≤ exp(−(2πj+π/6)/2)`.  Hence the held config `u` drifts by at
most `exp(−(2πj+π/6)/2)·M·(π/3) → 0` (`u_hold_drift`), `M` a bound on `|z−u|`.  This is the `εhold`
the per-cycle recurrence needs, proven to vanish — the u-channel is suppressed during the gate. -/
theorem selector_uhold_decays
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p selectorSchedule branch chiResetF chiGateF kappaF gainF Pv)
    (hA : p.A = 1) (hcμ : p.cμ = 1) (hcα : p.cα = 1 / 4) (hL : p.L = 1)
    (s : Fin d) (j : ℕ) {Mbnd : ℝ} (hMbnd : 0 ≤ Mbnd)
    (hμ0 : sol.μ 0 = 0)
    (hbox : ∀ t, |sol.z t s - sol.u t s| ≤ Mbnd) :
    |sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 2) s
        - sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 6) s|
      ≤ Real.exp (-(2 * Real.pi * (j : ℝ) + Real.pi / 6) / 2) * Mbnd * (Real.pi / 3) := by
  have hpi := Real.pi_pos
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  set a := 2 * Real.pi * (j : ℝ) + Real.pi / 6 with ha
  set b := 2 * Real.pi * (j : ℝ) + Real.pi / 2 with hb
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; positivity
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hbw : b - a = Real.pi / 3 := by rw [ha, hb]; ring
  have hdomU : ∀ x : ℝ, 0 ≤ x → x ∈ selectorSchedule.domain := fun x hx => by
    simpa [selectorSchedule] using hx
  set η := Real.exp (-a / 2) * Mbnd with hη
  have hηnn : 0 ≤ η := mul_nonneg (Real.exp_pos _).le hMbnd
  have hfield : ∀ t ∈ Set.Icc a b,
      |p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t s - sol.u t s)| ≤ η := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans ha0 ht.1
    have hαt : sol.α t = Real.exp (t / 4) := by
      rw [sol.alpha_eq_exp hdomU ht0, hcα]; congr 1; ring
    have hμt : sol.μ t = t := by rw [sol.mu_eq_linear hdomU ht0, hμ0, hcμ]; ring
    have hsin : (1 : ℝ) / 2 ≤ Real.sin t := sin_ge_half_of_gate_window j ht
    -- the field magnitude = exp(t/4 − t·(1+sin t)/2) · |z−u|
    have hgate : p.A * sol.α t * bGateU p.L (sol.μ t) t
        = Real.exp (t / 4 - t * ((1 + Real.sin t) / 2)) := by
      rw [hA, hαt, hμt, hL]
      simp only [bGateU, qPulse, pow_one, one_mul]
      rw [← Real.exp_add]
      congr 1
    rw [hgate, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp_le : Real.exp (t / 4 - t * ((1 + Real.sin t) / 2)) ≤ Real.exp (-a / 2) := by
      apply Real.exp_le_exp.mpr
      have h1 : t * ((1 + Real.sin t) / 2) ≥ t * (3 / 4) := by
        apply mul_le_mul_of_nonneg_left _ ht0; linarith
      have h2 : -t / 2 ≤ -a / 2 := by linarith [ht.1]
      linarith
    calc Real.exp (t / 4 - t * ((1 + Real.sin t) / 2)) * |sol.z t s - sol.u t s|
        ≤ Real.exp (-a / 2) * Mbnd := by
          apply mul_le_mul hexp_le (hbox t) (abs_nonneg _) (Real.exp_pos _).le
      _ = η := by rw [hη]
  have hdrift := sol.u_hold_drift s hab (fun t ht => hdomU t (le_trans ha0 ht.1)) hfield
  rw [hbw] at hdrift
  calc |sol.u b s - sol.u a s| ≤ η * (Real.pi / 3) := hdrift
    _ = Real.exp (-a / 2) * Mbnd * (Real.pi / 3) := by rw [hη]
    _ = Real.exp (-(2 * Real.pi * (j : ℝ) + Real.pi / 6) / 2) * Mbnd * (Real.pi / 3) := by rw [ha]

/-- On the gate window `{cos t ≤ c0}` the reset envelope `((1+cos t)/2)^M` is bounded above by
`((1+c0)/2)^M` (`= η`).  With `c0 = −1/2, M = 1`: `χ_reset ≤ 1/4`. -/
theorem chiReset_ub {c0 : ℝ} (M : ℕ) {t : ℝ} (ht : Real.cos t ≤ c0) :
    ((1 + Real.cos t) / 2) ^ M ≤ ((1 + c0) / 2) ^ M := by
  gcongr <;> linarith [Real.neg_one_le_cos t]

end Ripple.BoundedUniversality.BGP
