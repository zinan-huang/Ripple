/-
Ripple.BoundedUniversality.BGP.RelaxationToolkit
----------------------------

Public generic scalar toolkit for the 38→NW migration (repair classes R1–R3):
interval-anchored box invariance and absolute-tube trapping for relaxation
ODEs `y' = k (m − y)`, plus the exponential-integral caps used by the S2/S4
edge estimates.

The kernel-mass identities are already public in `SelectorDuhamelWrite`
(`forward_kernel_integral_eq_one_sub_exp`, `write_forward_kernel_mass_le_one`,
`stack_write_tracking_total_variation_le`); this file adds only the missing
pieces, as interval-anchored wrappers of `scalar_relaxation_trapping_invariant`
and elementary integral comparisons.
-/
import Ripple.BoundedUniversality.BGP.ContractTrappingInvariant
import Ripple.BoundedUniversality.BGP.SelectorDuhamelWrite
import Ripple.BoundedUniversality.BGP.PhaseClock

namespace Ripple.BoundedUniversality.BGP

open Set Real intervalIntegral

/-- Box forward-invariance for the relaxation ODE `y' = k (m − y)` on an
interval `[a, b]`: if the moving target `m` stays in `[lo, hi]` and `y`
starts in `[lo, hi]`, then `y` stays in `[lo, hi]` — independently of the
size of the (nonnegative) rate `k`.  Interval-anchored wrapper of
`scalar_relaxation_trapping_invariant`. -/
theorem relaxation_box_invariant
    (y m k : ℝ → ℝ) {lo hi a b : ℝ}
    (_hab : a ≤ b)
    (hk_cont : Continuous k) (hm_cont : Continuous m)
    (hy_ode : ∀ t ∈ Set.Icc a b, HasDerivAt y (k t * (m t - y t)) t)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hm_range : ∀ t ∈ Set.Icc a b, m t ∈ Set.Icc lo hi)
    (hya : y a ∈ Set.Icc lo hi) :
    ∀ t ∈ Set.Icc a b, y t ∈ Set.Icc lo hi := by
  intro t ht
  have hode' : ∀ σ ∈ Set.Icc (0 : ℝ) (t - a),
      HasDerivAt (fun σ' : ℝ => y (a + σ'))
        (k (a + σ) * (m (a + σ) - y (a + σ))) σ := by
    intro σ hσ
    have hmem : a + σ ∈ Set.Icc a b :=
      ⟨by linarith [hσ.1], by linarith [hσ.2, ht.2]⟩
    have h1 : HasDerivAt (fun σ' : ℝ => a + σ') 1 σ := by
      simpa using (hasDerivAt_id σ).const_add a
    have h2 := (hy_ode (a + σ) hmem).comp σ h1
    simpa [Function.comp] using h2
  have hknn' : ∀ σ ∈ Set.Icc (0 : ℝ) (t - a), 0 ≤ k (a + σ) := by
    intro σ hσ
    exact hk_nonneg (a + σ) ⟨by linarith [hσ.1], by linarith [hσ.2, ht.2]⟩
  have hmr' : ∀ σ ∈ Set.Icc (0 : ℝ) (t - a), m (a + σ) ∈ Set.Icc lo hi := by
    intro σ hσ
    exact hm_range (a + σ) ⟨by linarith [hσ.1], by linarith [hσ.2, ht.2]⟩
  have hy0' : y (a + 0) ∈ Set.Icc lo hi := by simpa using hya
  have hshift := scalar_relaxation_trapping_invariant
    (fun σ => y (a + σ)) (fun σ => m (a + σ)) (fun σ => k (a + σ))
    (lo := lo) (hi := hi) (T := t - a)
    (by linarith [ht.1])
    (hk_cont.comp (continuous_const.add continuous_id))
    (hm_cont.comp (continuous_const.add continuous_id))
    hode' hknn' hmr' hy0'
  simpa [show a + (t - a) = t from by ring] using hshift

/-- Absolute-tube trapping for the relaxation ODE on `[a, b]`: if the entry
error and the moving-target error are both `≤ δ` around a center `M`, the
state error stays `≤ δ` — rate-independent (repair class R2). -/
theorem relax_abs_trap
    (y m k : ℝ → ℝ) {M δ a b : ℝ}
    (hab : a ≤ b)
    (hk_cont : Continuous k) (hm_cont : Continuous m)
    (hy_ode : ∀ t ∈ Set.Icc a b, HasDerivAt y (k t * (m t - y t)) t)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hya : |y a - M| ≤ δ)
    (hm : ∀ t ∈ Set.Icc a b, |m t - M| ≤ δ) :
    ∀ t ∈ Set.Icc a b, |y t - M| ≤ δ := by
  have hbox := relaxation_box_invariant y m k
    (lo := M - δ) (hi := M + δ) hab hk_cont hm_cont hy_ode hk_nonneg
    (fun t ht => by
      have hmt := hm t ht
      rw [abs_le] at hmt
      exact ⟨by linarith [hmt.1], by linarith [hmt.2]⟩)
    (by
      rw [abs_le] at hya
      exact ⟨by linarith [hya.1], by linarith [hya.2]⟩)
  intro t ht
  have hyt := hbox t ht
  rw [abs_le]
  exact ⟨by linarith [hyt.1], by linarith [hyt.2]⟩

/-- Elementary left-anchored cap for a decaying exponential integral:
`∫_a^b C e^{−r τ} dτ ≤ (C / r) e^{−r a}`. -/
theorem integral_const_mul_exp_neg_le_left
    {r C a b : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (_hab : a ≤ b) :
    (∫ τ in a..b, C * Real.exp (-(r * τ))) ≤
      (C / r) * Real.exp (-(r * a)) := by
  have hderiv : ∀ τ : ℝ,
      HasDerivAt (fun τ' : ℝ => -Real.exp (-(r * τ')) / r)
        (Real.exp (-(r * τ))) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ' : ℝ => -(r * τ')) (-r) τ := by
      simpa using ((hasDerivAt_id τ).const_mul r).neg
    have h2 := (Real.hasDerivAt_exp (-(r * τ))).comp τ h1
    have h3 := h2.neg.div_const r
    convert h3 using 1
    field_simp
  have hint : (∫ τ in a..b, Real.exp (-(r * τ))) =
      (-Real.exp (-(r * b)) / r) - (-Real.exp (-(r * a)) / r) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun τ _ => hderiv τ)
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg).intervalIntegrable a b
  have hb0 : 0 ≤ Real.exp (-(r * b)) / r :=
    div_nonneg (Real.exp_pos _).le hr.le
  calc (∫ τ in a..b, C * Real.exp (-(r * τ)))
      = C * ∫ τ in a..b, Real.exp (-(r * τ)) := by
        rw [intervalIntegral.integral_const_mul]
    _ = C * ((-Real.exp (-(r * b)) / r) - (-Real.exp (-(r * a)) / r)) := by
        rw [hint]
    _ ≤ C * (Real.exp (-(r * a)) / r) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have hring : (-Real.exp (-(r * b)) / r) - (-Real.exp (-(r * a)) / r) =
            Real.exp (-(r * a)) / r - Real.exp (-(r * b)) / r := by ring
        linarith [hb0, hring.le, hring.ge]
    _ = (C / r) * Real.exp (-(r * a)) := by ring

/-- Weighted product-mass cap (S4 forcing shape): a bad mass decaying at rate
`r₁` times a bounded multiplier times a speed decaying at rate `r₂` has
integral at most `(Cλ L Cu / (r₁ + r₂)) e^{−(r₁+r₂) a}`. -/
theorem weighted_product_exp_integral_le
    {a b L Cl Cu r₁ r₂ : ℝ} {badMass uSpeed : ℝ → ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L) (hCl : 0 ≤ Cl) (hCu : 0 ≤ Cu)
    (hr : 0 < r₁ + r₂)
    (hbad_cont : Continuous badMass) (hu_cont : Continuous uSpeed)
    (hbad : ∀ τ ∈ Set.Icc a b,
      0 ≤ badMass τ ∧ badMass τ ≤ Cl * Real.exp (-(r₁ * τ)))
    (hu : ∀ τ ∈ Set.Icc a b,
      0 ≤ uSpeed τ ∧ uSpeed τ ≤ Cu * Real.exp (-(r₂ * τ))) :
    (∫ τ in a..b, badMass τ * L * uSpeed τ) ≤
      (Cl * L * Cu / (r₁ + r₂)) * Real.exp (-((r₁ + r₂) * a)) := by
  have hexp : ∀ τ : ℝ,
      Real.exp (-(r₁ * τ)) * Real.exp (-(r₂ * τ)) =
        Real.exp (-((r₁ + r₂) * τ)) := by
    intro τ
    rw [← Real.exp_add]
    congr 1
    ring
  have hpoint : ∀ τ ∈ Set.Icc a b,
      badMass τ * L * uSpeed τ ≤
        (Cl * L * Cu) * Real.exp (-((r₁ + r₂) * τ)) := by
    intro τ hτ
    obtain ⟨hb0, hbB⟩ := hbad τ hτ
    obtain ⟨hu0, huB⟩ := hu τ hτ
    have hmul : badMass τ * uSpeed τ ≤
        (Cl * Real.exp (-(r₁ * τ))) * (Cu * Real.exp (-(r₂ * τ)))  :=
      mul_le_mul hbB huB hu0 (by positivity)
    calc badMass τ * L * uSpeed τ = L * (badMass τ * uSpeed τ) := by ring
      _ ≤ L * ((Cl * Real.exp (-(r₁ * τ))) * (Cu * Real.exp (-(r₂ * τ)))) :=
          mul_le_mul_of_nonneg_left hmul hL
      _ = (Cl * L * Cu) *
            (Real.exp (-(r₁ * τ)) * Real.exp (-(r₂ * τ))) := by ring
      _ = (Cl * L * Cu) * Real.exp (-((r₁ + r₂) * τ)) := by rw [hexp τ]
  have hcont_rhs : Continuous fun τ : ℝ =>
      (Cl * L * Cu) * Real.exp (-((r₁ + r₂) * τ)) :=
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg)
  have hint1 : IntervalIntegrable
      (fun τ => badMass τ * L * uSpeed τ) MeasureTheory.volume a b :=
    ((hbad_cont.mul continuous_const).mul hu_cont).intervalIntegrable a b
  have hint2 : IntervalIntegrable
      (fun τ => (Cl * L * Cu) * Real.exp (-((r₁ + r₂) * τ)))
      MeasureTheory.volume a b :=
    hcont_rhs.intervalIntegrable a b
  calc (∫ τ in a..b, badMass τ * L * uSpeed τ)
      ≤ ∫ τ in a..b, (Cl * L * Cu) * Real.exp (-((r₁ + r₂) * τ)) :=
        intervalIntegral.integral_mono_on hab hint1 hint2 hpoint
    _ ≤ ((Cl * L * Cu) / (r₁ + r₂)) * Real.exp (-((r₁ + r₂) * a)) :=
        integral_const_mul_exp_neg_le_left hr (by positivity) hab

/-- On the middle third `[π/3, 2π/3]` of the upper half-period, `sin`
stays above `√3/2`. -/
theorem sqrt3_div_two_le_sin_middle_third {s : ℝ}
    (hs1 : Real.pi / 3 ≤ s) (hs2 : s ≤ 2 * Real.pi / 3) :
    Real.sqrt 3 / 2 ≤ Real.sin s := by
  have hπ := Real.pi_pos
  rcases le_total s (Real.pi / 2) with hsplit | hsplit
  · have hmem1 : Real.pi / 3 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, by linarith⟩
    have hmem2 : s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, hsplit⟩
    have hmono := Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 hs1
    rw [Real.sin_pi_div_three] at hmono
    exact hmono
  · have hmem1 : Real.pi / 3 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, by linarith⟩
    have hmem2 : Real.pi - s ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, by linarith⟩
    have hle : Real.pi / 3 ≤ Real.pi - s := by linarith
    have hmono := Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 hle
    rw [Real.sin_pi_div_three, Real.sin_pi_sub] at hmono
    exact hmono

/-- `sin ≤ −√3/2` on the copy window `[2πj + 4π/3, 2πj + 5π/3]` — the
trigonometric core of the S2 copy-mass bound (`qPulse ≤ 67/1000`). -/
theorem sin_le_neg_sqrt3_div_two_on_copy_window (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + 4 * Real.pi / 3 ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 3) :
    Real.sin t ≤ -(Real.sqrt 3 / 2) := by
  set x : ℝ := t - 2 * Real.pi * (j : ℝ) with hx
  have hsin : Real.sin t = Real.sin x := by
    have hrw : t = x + (j : ℕ) * (2 * Real.pi) := by
      rw [hx]; ring
    conv_lhs => rw [hrw]
    rw [Real.sin_add_nat_mul_two_pi]
  have hxl : 4 * Real.pi / 3 ≤ x := by rw [hx]; linarith
  have hxr : x ≤ 5 * Real.pi / 3 := by rw [hx]; linarith
  have hπ := Real.pi_pos
  have hkey : Real.sqrt 3 / 2 ≤ Real.sin (x - Real.pi) :=
    sqrt3_div_two_le_sin_middle_third (by linarith) (by linarith)
  have hsub : Real.sin (x - Real.pi) = -Real.sin x := Real.sin_sub_pi x
  rw [hsin]
  linarith [hsub ▸ hkey]

/-- Numeric form of the copy-window pulse bound:
`(1 + sin t)/2 ≤ 67/1000` on `[2πj + 4π/3, 2πj + 5π/3]`
(since `(2 − √3)/4 < 67/1000`). -/
theorem one_add_sin_div_two_le_67_div_1000_on_copy_window (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + 4 * Real.pi / 3 ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 3) :
    (1 + Real.sin t) / 2 ≤ 67 / 1000 := by
  have hsin := sin_le_neg_sqrt3_div_two_on_copy_window j h1 h2
  have hsqrt : (1.732 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1.732 : ℝ) = Real.sqrt (1.732 ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- `sin ≥ 0` on the handoff piece-1 window `[2πj + 5π/6, 2πj + π]`. -/
theorem sin_nonneg_on_handoff_piece1 (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6 ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + Real.pi) :
    0 ≤ Real.sin t := by
  set x : ℝ := t - 2 * Real.pi * (j : ℝ) with hx
  have hsin : Real.sin t = Real.sin x := by
    have hrw : t = x + (j : ℕ) * (2 * Real.pi) := by rw [hx]; ring
    conv_lhs => rw [hrw]
    rw [Real.sin_add_nat_mul_two_pi]
  have hπ := Real.pi_pos
  rw [hsin]
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (by rw [hx]; linarith) (by rw [hx]; linarith)

/-- `sin ≤ 0` on the handoff piece-2 window `[2πj + π, 2πj + 7π/6]`. -/
theorem sin_nonpos_on_handoff_piece2 (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + Real.pi ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) :
    Real.sin t ≤ 0 := by
  set x : ℝ := t - 2 * Real.pi * (j : ℝ) with hx
  have hsin : Real.sin t = Real.sin x := by
    have hrw : t = x + (j : ℕ) * (2 * Real.pi) := by rw [hx]; ring
    conv_lhs => rw [hrw]
    rw [Real.sin_add_nat_mul_two_pi]
  have hπ := Real.pi_pos
  have hshift : Real.sin (x - Real.pi) = -Real.sin x := Real.sin_sub_pi x
  have hnn : 0 ≤ Real.sin (x - Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by rw [hx]; linarith) (by rw [hx]; linarith)
  rw [hsin]
  linarith [hshift ▸ hnn]

/-- `sin ≤ 0` on the whole lower half-period `[2πj + π, 2πj + 2π]`
(generalizes the handoff piece-2 window; also covers the post-copy
freeze window `[2πj + 5π/3, 2π(j+1)]`). -/
theorem sin_nonpos_on_lower_half (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + Real.pi ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + 2 * Real.pi) :
    Real.sin t ≤ 0 := by
  set x : ℝ := t - 2 * Real.pi * (j : ℝ) with hx
  have hsin : Real.sin t = Real.sin x := by
    have hrw : t = x + (j : ℕ) * (2 * Real.pi) := by rw [hx]; ring
    conv_lhs => rw [hrw]
    rw [Real.sin_add_nat_mul_two_pi]
  have hπ := Real.pi_pos
  have hshift : Real.sin (x - Real.pi) = -Real.sin x := Real.sin_sub_pi x
  have hnn : 0 ≤ Real.sin (x - Real.pi) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by rw [hx]; linarith) (by rw [hx]; linarith)
  rw [hsin]
  linarith [hshift ▸ hnn]

/-- The `L = 1` u-gate pulse is at most `67/1000` on the copy window
`[2πj + 4π/3, 2πj + 5π/3]` — the sharp S2 copy-rate input
(rate `300 − 67 = 233` survives). -/
theorem qPulse_one_le_67_div_1000_on_copy_window (j : ℕ) {t : ℝ}
    (h1 : 2 * Real.pi * (j : ℝ) + 4 * Real.pi / 3 ≤ t)
    (h2 : t ≤ 2 * Real.pi * (j : ℝ) + 5 * Real.pi / 3) :
    qPulse 1 t ≤ 67 / 1000 := by
  rw [qPulse, pow_one]
  exact one_add_sin_div_two_le_67_div_1000_on_copy_window j h1 h2

/-- Tube persistence by entry slack plus drift (S4 edge-tube shape, generic):
if the state starts `ε`-inside the radius-`r` tube around `enc` and drifts by
at most `ε` on `[a, b]`, it stays in the tube. -/
theorem tube_of_entry_slack_and_drift {d : ℕ}
    (u : ℝ → Fin d → ℝ) (enc : Fin d → ℝ) {a b r ε : ℝ}
    (hstart : ∀ i, |u a i - enc i| ≤ r - ε)
    (hdrift : ∀ τ ∈ Set.Icc a b, ∀ i, |u τ i - u a i| ≤ ε) :
    ∀ τ ∈ Set.Icc a b, ∀ i, |u τ i - enc i| ≤ r := by
  intro τ hτ i
  calc |u τ i - enc i|
      ≤ |u τ i - u a i| + |u a i - enc i| := abs_sub_le _ _ _
    _ ≤ ε + (r - ε) := add_le_add (hdrift τ hτ i) (hstart i)
    _ = r := by ring

/-- Endpoint contraction for the relaxation ODE with a mass lower bound
(S2 copy-phase shape): `|y b − M| ≤ e^{−Mass}·D₀ + δ` whenever the entry
error is `≤ D₀`, the target error is `≤ δ`, and the accumulated rate mass
is `≥ Mass`.  Wrapper of `stack_write_gronwall_sup_bound`. -/
theorem relax_endpoint_contract_of_mass_lower
    (y m k : ℝ → ℝ) {M a b D0 δ Mass : ℝ}
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hm_cont : Continuous m)
    (hy_ode : ∀ t ∈ Set.Icc a b, HasDerivAt y (k t * (m t - y t)) t)
    (hya : |y a - M| ≤ D0)
    (hδ : ∀ t ∈ Set.Icc a b, |m t - M| ≤ δ) (hδ0 : 0 ≤ δ)
    (hmass : Mass ≤ ∫ t in a..b, k t) :
    |y b - M| ≤ Real.exp (-Mass) * D0 + δ := by
  have h := stack_write_gronwall_sup_bound y m k M a b hab
    hk_cont hk_nonneg hm_cont hy_ode hδ
  have hexp1 : Real.exp (-(∫ t in a..b, k t)) ≤ Real.exp (-Mass) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexp2 : 1 - Real.exp (-(∫ t in a..b, k t)) ≤ 1 := by
    linarith [(Real.exp_pos (-(∫ t in a..b, k t))).le]
  calc |y b - M|
      ≤ Real.exp (-(∫ t in a..b, k t)) * |y a - M| +
          δ * (1 - Real.exp (-(∫ t in a..b, k t))) := h
    _ ≤ Real.exp (-Mass) * D0 + δ * 1 := by
        apply add_le_add
        · exact mul_le_mul hexp1 hya (abs_nonneg _) (Real.exp_pos _).le
        · exact mul_le_mul_of_nonneg_left hexp2 hδ0
    _ = Real.exp (-Mass) * D0 + δ := by ring

/-- Endpoint drift of a relaxation state is at most the target-error sup
times the rate mass: `|y b − y a| ≤ B · ∫ k`. -/
theorem relax_drift_le_sup_mul_mass
    (y m k : ℝ → ℝ) {a b B : ℝ}
    (hab : a ≤ b)
    (hk_cont : Continuous k) (hm_cont : Continuous m)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hy_ode : ∀ t ∈ Set.Icc a b, HasDerivAt y (k t * (m t - y t)) t)
    (_hB0 : 0 ≤ B)
    (hmy : ∀ t ∈ Set.Icc a b, |m t - y t| ≤ B) :
    |y b - y a| ≤ B * ∫ t in a..b, k t := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hy_cont : ContinuousOn y (Set.Icc a b) := fun t ht =>
    (hy_ode t ht).continuousAt.continuousWithinAt
  have hf'_cont : ContinuousOn (fun t => k t * (m t - y t)) (Set.Icc a b) :=
    (hk_cont.continuousOn).mul (hm_cont.continuousOn.sub hy_cont)
  have hf'_int : IntervalIntegrable
      (fun t => k t * (m t - y t)) MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hf'_cont.integrableOn_Icc
  have hftc : (∫ t in a..b, k t * (m t - y t)) = y b - y a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      exact hy_ode t (huIcc ▸ ht)
    · exact hf'_int
  have habs_int : IntervalIntegrable
      (fun t => |k t * (m t - y t)|) MeasureTheory.volume a b := hf'_int.abs
  have hkB_int : IntervalIntegrable
      (fun t => k t * B) MeasureTheory.volume a b :=
    (hk_cont.mul continuous_const).intervalIntegrable a b
  have hpoint : ∀ t ∈ Set.Icc a b, |k t * (m t - y t)| ≤ k t * B := by
    intro t ht
    rw [abs_mul, abs_of_nonneg (hk_nonneg t ht)]
    exact mul_le_mul_of_nonneg_left (hmy t ht) (hk_nonneg t ht)
  calc |y b - y a| = |∫ t in a..b, k t * (m t - y t)| := by rw [hftc]
    _ ≤ ∫ t in a..b, |k t * (m t - y t)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, k t * B :=
        intervalIntegral.integral_mono_on hab habs_int hkB_int hpoint
    _ = B * ∫ t in a..b, k t := by
        rw [intervalIntegral.integral_mul_const]
        ring

/-- Two-phase handoff core (S2 shape, Q4132): on `[b, T]` the state is
trapped in the `δs + M₁` tube around `E` because the target `mix` stays
`M₁`-close to `E`; on `[T, aE]` the state drifts by at most `Bmz` times the
(externally capped) rate mass.  Conclusion:
`|z(aE) − E| ≤ δs + M₁ + Bmz · KM`. -/
theorem relax_two_phase_handoff
    (z mix kZ : ℝ → ℝ) {E δs M1 Bmz KM b T aE : ℝ}
    (hbT : b ≤ T) (hTa : T ≤ aE)
    (hkZ_cont : Continuous kZ) (hmix_cont : Continuous mix)
    (hkZ_nonneg : ∀ t ∈ Set.Icc b aE, 0 ≤ kZ t)
    (hz_ode : ∀ t ∈ Set.Icc b aE, HasDerivAt z (kZ t * (mix t - z t)) t)
    (hδs0 : 0 ≤ δs) (hM10 : 0 ≤ M1)
    (hz_b : |z b - E| ≤ δs)
    (hmix1 : ∀ t ∈ Set.Icc b T, |mix t - E| ≤ M1)
    (hBmz0 : 0 ≤ Bmz)
    (hmixz2 : ∀ t ∈ Set.Icc T aE, |mix t - z t| ≤ Bmz)
    (hKM : (∫ t in T..aE, kZ t) ≤ KM) :
    |z aE - E| ≤ δs + M1 + Bmz * KM := by
  have h1 : ∀ t ∈ Set.Icc b T, |z t - E| ≤ δs + M1 :=
    relax_abs_trap z mix kZ hbT hkZ_cont hmix_cont
      (fun t ht => hz_ode t ⟨ht.1, le_trans ht.2 hTa⟩)
      (fun t ht => hkZ_nonneg t ⟨ht.1, le_trans ht.2 hTa⟩)
      (le_trans hz_b (by linarith))
      (fun t ht => le_trans (hmix1 t ht) (by linarith))
  have h2 : |z aE - z T| ≤ Bmz * ∫ t in T..aE, kZ t :=
    relax_drift_le_sup_mul_mass z mix kZ hTa hkZ_cont hmix_cont
      (fun t ht => hkZ_nonneg t ⟨le_trans hbT ht.1, ht.2⟩)
      (fun t ht => hz_ode t ⟨le_trans hbT ht.1, ht.2⟩)
      hBmz0 hmixz2
  have hzT := h1 T ⟨hbT, le_refl T⟩
  have hmass : Bmz * (∫ t in T..aE, kZ t) ≤ Bmz * KM :=
    mul_le_mul_of_nonneg_left hKM hBmz0
  calc |z aE - E| ≤ |z aE - z T| + |z T - E| := abs_sub_le _ _ _
    _ ≤ Bmz * KM + (δs + M1) := add_le_add (le_trans h2 hmass) hzT
    _ = δs + M1 + Bmz * KM := by ring

end Ripple.BoundedUniversality.BGP
