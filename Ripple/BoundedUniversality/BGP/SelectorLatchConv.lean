import Ripple.BoundedUniversality.BGP.SelectorField

/-!
# Selector latch convergence (analytic core)

This file discharges the analytic latch-convergence facts for the clock-driven
selector latch `SelectorHaltLatchSol`.  Its scalar ODE
`a' = K · gPulse R t · (Hval(z t) − a t)`, `a 0 = 0`
is identical to the contract latch `ContractHaltLatchSol` and the dynamic latch
`DynLatchSol`.  The contract/dynamic flavors discharge convergence through a
private integrating-factor engine (`latch_eventual_upper` in
`Ripple.BoundedUniversality.BGP.LatchAssembly` / `Ripple.BoundedUniversality.BGP.DynamicAssembly`); that engine is
`private`, so — following the established per-flavor pattern in this codebase —
we re-derive a self-contained generic engine here over abstract `y w : ℝ → ℝ`
and apply it to the selector latch with driving signal `t ↦ I.Hval (sol.z t)`.

The two public results are:

* `selector_latch_high` — eventually-`1`-indicator ⇒ latch eventually in `[3/4,1]`.
* `selector_latch_low`  — always-`0`-indicator   ⇒ latch eventually in `[0,1/4]`.

Both require, as honest extra hypotheses (beyond the kernel's window
hypotheses), the global flag-domain fact `∀ t ≥ 0, sol.z t flagCoord ∈ [0,1]`
(needed to invoke `I.in_unit` along the whole trajectory) and the parameter
feasibility facts for `K, R` (matching the constants chosen by
`latch_parameter_exists`).  These are exactly the hypotheses the generic engine
consumes; nothing is `sorry`'d.
-/

namespace Ripple.BoundedUniversality.BGP

open Real

/-! ## Generic gPulse cosine / integral bounds (re-derived, `sel_`-prefixed) -/

private theorem sel_sqrt_three_le_87_div_50 : Real.sqrt 3 ≤ (87 : ℝ) / 50 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    Real.sqrt_nonneg (3 : ℝ)]

private theorem sel_sqrt_three_ge_43_div_25 : (43 : ℝ) / 25 ≤ Real.sqrt 3 := by
  rw [Real.le_sqrt' (by norm_num)]
  norm_num

private theorem sel_cos_pi_div_twelve_ge_24_div_25 :
    (24 : ℝ) / 25 ≤ Real.cos (π / 12) := by
  have hhalf := Real.cos_half (x := π / 6)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsqrt : (24 : ℝ) / 25 ≤ Real.sqrt (((1 + Real.cos (π / 6)) / 2)) := by
    rw [Real.le_sqrt' (by norm_num)]
    rw [Real.cos_pi_div_six]
    nlinarith [sel_sqrt_three_ge_43_div_25]
  rw [show π / 12 = π / 6 / 2 by ring]
  rw [hhalf]
  exact hsqrt

private theorem sel_cos_shift_eq_neg_cos_center (j : ℕ) (t : ℝ) :
    Real.cos t = -Real.cos (t - 2 * π * (j : ℝ) - π) := by
  have hteq : t =
      ((t - 2 * π * (j : ℝ) - π) + π) + (j : ℕ) * (2 * π) := by
    push_cast
    ring
  conv_lhs => rw [hteq]
  rw [Real.cos_add_nat_mul_two_pi, Real.cos_add_pi]

private theorem sel_cos_stable_inner_le (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j + 11 * π / 12 ≤ t)
    (h2 : t ≤ 2 * π * j + 13 * π / 12) :
    Real.cos t ≤ -(24 : ℝ) / 25 := by
  have hπ := Real.pi_pos
  set x := t - 2 * π * (j : ℝ) - π with hx
  have hxabs : |x| ≤ π / 12 := by
    rw [abs_le]
    constructor <;> simp only [hx] <;> linarith
  have hcosx : (24 : ℝ) / 25 ≤ Real.cos x := by
    rw [← Real.cos_abs x]
    calc
      (24 : ℝ) / 25 ≤ Real.cos (π / 12) := sel_cos_pi_div_twelve_ge_24_div_25
      _ ≤ Real.cos |x| :=
          Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
            (by linarith) hxabs
  rw [sel_cos_shift_eq_neg_cos_center j t]
  linarith

private theorem sel_cos_off_left_ge (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j ≤ t)
    (h2 : t ≤ 2 * π * j + 5 * π / 6) :
    -(87 : ℝ) / 100 ≤ Real.cos t := by
  have hπ := Real.pi_pos
  set x := t - 2 * π * (j : ℝ) - π with hx
  have hxlo : π / 6 ≤ |x| := by
    rw [le_abs]
    right
    simp only [hx]
    linarith
  have hxhi : |x| ≤ π := by
    rw [abs_le]
    constructor <;> simp only [hx] <;> linarith
  have hcosx : Real.cos x ≤ (87 : ℝ) / 100 := by
    rw [← Real.cos_abs x]
    calc
      Real.cos |x| ≤ Real.cos (π / 6) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
            hxhi hxlo
      _ = Real.sqrt 3 / 2 := Real.cos_pi_div_six
      _ ≤ (87 : ℝ) / 100 := by
          nlinarith [sel_sqrt_three_le_87_div_50]
  rw [sel_cos_shift_eq_neg_cos_center j t]
  linarith

private theorem sel_cos_off_right_ge (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j + 7 * π / 6 ≤ t)
    (h2 : t ≤ 2 * π * (j + 1)) :
    -(87 : ℝ) / 100 ≤ Real.cos t := by
  have hπ := Real.pi_pos
  set x := t - 2 * π * (j : ℝ) - π with hx
  have hxlo : π / 6 ≤ |x| := by
    rw [le_abs]
    left
    simp only [hx]
    linarith
  have hxhi : |x| ≤ π := by
    rw [abs_le]
    constructor <;> simp only [hx] <;> nlinarith [hπ, h1, h2]
  have hcosx : Real.cos x ≤ (87 : ℝ) / 100 := by
    rw [← Real.cos_abs x]
    calc
      Real.cos |x| ≤ Real.cos (π / 6) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
            hxhi hxlo
      _ = Real.sqrt 3 / 2 := Real.cos_pi_div_six
      _ ≤ (87 : ℝ) / 100 := by
          nlinarith [sel_sqrt_three_le_87_div_50]
  rw [sel_cos_shift_eq_neg_cos_center j t]
  linarith

private theorem sel_gPulse_ge_stable_inner {R j : ℕ} {t : ℝ}
    (h1 : 2 * π * j + 11 * π / 12 ≤ t)
    (h2 : t ≤ 2 * π * j + 13 * π / 12) :
    ((49 : ℝ) / 50) ^ R ≤ gPulse R t := by
  unfold gPulse
  apply pow_le_pow_left₀ (by norm_num)
  have hcos := sel_cos_stable_inner_le j h1 h2
  linarith

private theorem sel_gPulse_le_off_left {R j : ℕ} {t : ℝ}
    (h1 : 2 * π * j ≤ t)
    (h2 : t ≤ 2 * π * j + 5 * π / 6) :
    gPulse R t ≤ ((187 : ℝ) / 200) ^ R := by
  unfold gPulse
  apply pow_le_pow_left₀
  · nlinarith [Real.cos_le_one t]
  · have hcos := sel_cos_off_left_ge j h1 h2
    linarith

private theorem sel_gPulse_le_off_right {R j : ℕ} {t : ℝ}
    (h1 : 2 * π * j + 7 * π / 6 ≤ t)
    (h2 : t ≤ 2 * π * (j + 1)) :
    gPulse R t ≤ ((187 : ℝ) / 200) ^ R := by
  unfold gPulse
  apply pow_le_pow_left₀
  · nlinarith [Real.cos_le_one t]
  · have hcos := sel_cos_off_right_ge j h1 h2
    linarith

private theorem sel_latch_intInt (f : ℝ → ℝ) (hf : Continuous f) (u v : ℝ) :
    IntervalIntegrable f MeasureTheory.volume u v :=
  hf.intervalIntegrable u v

private theorem sel_latch_intConst (c u v : ℝ) :
    IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume u v :=
  _root_.intervalIntegrable_const

private theorem sel_gPulse_stable_inner_integral_lower (R j : ℕ) :
    (π / 6) * ((49 : ℝ) / 50) ^ R ≤
      ∫ t in (2 * π * j + 11 * π / 12)..(2 * π * j + 13 * π / 12),
        gPulse R t := by
  have hπ := Real.pi_pos
  have hab : 2 * π * (j : ℝ) + 11 * π / 12 ≤
      2 * π * (j : ℝ) + 13 * π / 12 := by linarith
  have hint := sel_latch_intInt (gPulse R) (gPulse_continuous R)
  have hconst :
      (∫ _t in (2 * π * (j : ℝ) + 11 * π / 12)..
          (2 * π * (j : ℝ) + 13 * π / 12), ((49 : ℝ) / 50) ^ R)
        = (π / 6) * ((49 : ℝ) / 50) ^ R := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab (sel_latch_intConst _ _ _)
    (hint _ _)
  intro t ht
  exact sel_gPulse_ge_stable_inner ht.1 ht.2

private theorem sel_gPulse_stable_integral_lower (R j : ℕ) :
    (π / 6) * ((49 : ℝ) / 50) ^ R ≤
      ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
        gPulse R t := by
  have hπ := Real.pi_pos
  have hinner :=
    sel_gPulse_stable_inner_integral_lower R j
  have hmono :
      (∫ t in (2 * π * j + 11 * π / 12)..(2 * π * j + 13 * π / 12),
        gPulse R t)
        ≤ ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
          gPulse R t := by
    apply intervalIntegral.integral_mono_interval
    · linarith
    · linarith
    · linarith
    · exact Filter.Eventually.of_forall fun t => gPulse_nonneg R t
    · exact sel_latch_intInt (gPulse R) (gPulse_continuous R) _ _
  exact le_trans hinner hmono

private theorem sel_exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have h2exp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h ⊢
    exact h
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr h2exp

/-! ## Latch parameter feasibility (re-derived) -/

private theorem sel_latch_parameter_exists :
    ∃ (K : ℚ) (R : ℕ), 0 < K ∧
      (∀ j : ℕ,
        Real.exp (-((K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t)) ≤ (1 / 2 : ℝ)) ∧
      (K : ℝ) * ((187 : ℝ) / 200) ^ R * (5 * π / 6) ≤ (1 / 100 : ℝ) := by
  let q : ℝ := (187 : ℝ) / 196
  have hq0 : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  obtain ⟨R, hR⟩ : ∃ R : ℕ, q ^ R < (3 : ℝ) / 2500 :=
    exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 3 / 2500) hq1
  let Glo : ℝ := (π / 6) * ((49 : ℝ) / 50) ^ R
  have hGlo_pos : 0 < Glo := by
    dsimp [Glo]
    positivity
  let N : ℕ := Nat.ceil (1 / Glo)
  let K : ℚ := (N : ℚ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.ceil_pos.mpr (by positivity)
  have hKpos : 0 < K := by
    dsimp [K]
    exact_mod_cast hNpos
  refine ⟨K, R, hKpos, ?_, ?_⟩
  · intro j
    have hceil : (1 / Glo : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
    have hKGlo : 1 ≤ (K : ℝ) * Glo := by
      have := mul_le_mul_of_nonneg_right hceil hGlo_pos.le
      have hcast : (K : ℝ) = (N : ℝ) := by norm_num [K]
      rw [hcast]
      rwa [one_div_mul_cancel hGlo_pos.ne'] at this
    have hint :=
      sel_gPulse_stable_integral_lower R j
    have hKnonneg : 0 ≤ (K : ℝ) := by exact_mod_cast hKpos.le
    have hprod :
        1 ≤ (K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t := by
      calc
        1 ≤ (K : ℝ) * Glo := hKGlo
        _ ≤ (K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t := by
              apply mul_le_mul_of_nonneg_left
              · simpa [Glo] using hint
              · exact hKnonneg
    calc
      Real.exp (-((K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t))
          ≤ Real.exp (-1) := by
            apply Real.exp_le_exp.mpr
            linarith
      _ ≤ (1 / 2 : ℝ) := sel_exp_neg_one_le_half
  · have hceil_lt : (N : ℝ) < 1 / Glo + 1 := by
      dsimp [N]
      exact Nat.ceil_lt_add_one (by positivity)
    have hKle : (K : ℝ) ≤ 1 / Glo + 1 := by
      have hcast : (K : ℝ) = (N : ℝ) := by norm_num [K]
      rw [hcast]
      exact hceil_lt.le
    have hoff_le_q : ((187 : ℝ) / 200) ^ R ≤ q ^ R := by
      apply pow_le_pow_left₀
      · norm_num
      · norm_num [q]
    have hπ4 : π ≤ (4 : ℝ) := Real.pi_le_four
    have hleak_bound :
        (1 / Glo + 1) * ((187 : ℝ) / 200) ^ R * (5 * π / 6)
          ≤ ((25 : ℝ) / 3) * q ^ R := by
      have hstable_pos : 0 < ((49 : ℝ) / 50) ^ R := by positivity
      have hoff_nonneg : 0 ≤ ((187 : ℝ) / 200) ^ R := by positivity
      have hqpow_nonneg : 0 ≤ q ^ R := by positivity
      calc
        (1 / Glo + 1) * ((187 : ℝ) / 200) ^ R * (5 * π / 6)
            = (5 * (((187 : ℝ) / 200) ^ R / (((49 : ℝ) / 50) ^ R)) +
                (5 * π / 6) * ((187 : ℝ) / 200) ^ R) := by
                field_simp [Glo, hGlo_pos.ne', Real.pi_ne_zero, hstable_pos.ne']
                ring
        _ ≤ 5 * q ^ R + (5 * π / 6) * q ^ R := by
              have hratio :
                  ((187 : ℝ) / 200) ^ R / (((49 : ℝ) / 50) ^ R) = q ^ R := by
                rw [← div_pow]
                congr 1
                norm_num [q]
              rw [hratio]
              gcongr
        _ ≤ 5 * q ^ R + (10 / 3 : ℝ) * q ^ R := by
              have hcoef : 5 * π / 6 ≤ (10 / 3 : ℝ) := by
                nlinarith [hπ4]
              have hterm :
                  (5 * π / 6) * q ^ R ≤ (10 / 3 : ℝ) * q ^ R :=
                mul_le_mul_of_nonneg_right hcoef hqpow_nonneg
              linarith
        _ = ((25 : ℝ) / 3) * q ^ R := by ring
    calc
      (K : ℝ) * ((187 : ℝ) / 200) ^ R * (5 * π / 6)
          ≤ (1 / Glo + 1) * ((187 : ℝ) / 200) ^ R * (5 * π / 6) := by
            gcongr
      _ ≤ ((25 : ℝ) / 3) * q ^ R := hleak_bound
      _ ≤ (1 / 100 : ℝ) := by
            nlinarith [hR]

/-! ## Generic unit-interval invariance and integrating-factor engine -/

private theorem sel_nonneg_of_hasDerivAt_nonneg
    (f : ℝ → ℝ) (f' : ℝ → ℝ)
    (hderiv : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hpos : ∀ s : ℝ, 0 ≤ s → 0 ≤ f' s)
    (h0 : 0 ≤ f 0) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · exact (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
    · intro s hs
      exact ((hderiv s).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hderiv s).deriv]
      exact hpos s hs.1.le
  have := hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
  linarith

/-- Forward invariance of `[0,1]` for the abstract latch coordinate `a`, given
its ODE shape and `Hval`-along-trajectory in `[0,1]`. -/
private theorem sel_latch_mem_unitInterval
    (Hdrive : ℝ → ℝ) (a : ℝ → ℝ) (K : ℝ) (hK : 0 < K) (R : ℕ)
    (ha0 : a 0 = 0)
    (hode : ∀ t : ℝ, HasDerivAt a (K * gPulse R t * (Hdrive t - a t)) t)
    (hH : ∀ t : ℝ, 0 ≤ t → 0 ≤ Hdrive t ∧ Hdrive t ≤ 1) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ a t ∧ a t ≤ 1 := by
  intro t ht
  set φ : ℝ → ℝ := fun s => K * gPulse R s with hφdef
  have hφcont : Continuous φ := by
    have : Continuous (gPulse R) := gPulse_continuous R
    fun_prop
  set Φ : ℝ → ℝ := fun s => ∫ τ in (0:ℝ)..s, φ τ with hΦdef
  have hΦderiv : ∀ s : ℝ, HasDerivAt Φ (φ s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right
      (hφcont.intervalIntegrable 0 s)
      (hφcont.stronglyMeasurableAtFilter _ _)
      hφcont.continuousAt
  set E : ℝ → ℝ := fun s => Real.exp (Φ s) with hEdef
  have hEderiv : ∀ s : ℝ, HasDerivAt E (φ s * E s) s := by
    intro s
    have := (hΦderiv s).exp
    convert this using 1
    simp only [hEdef]
    ring
  have hEpos : ∀ s, 0 < E s := fun s => Real.exp_pos _
  have hE0 : E 0 = 1 := by simp [hEdef, hΦdef]
  constructor
  · have hfderiv : ∀ s : ℝ, HasDerivAt (fun τ => a τ * E τ)
        (K * gPulse R s * Hdrive s * E s) s := by
      intro s
      have h1 := (hode s).mul (hEderiv s)
      convert h1 using 1
      simp only [hφdef, hEdef]
      ring
    have h := sel_nonneg_of_hasDerivAt_nonneg (fun τ => a τ * E τ) _
      hfderiv
      (fun s hs => by
        have hHs := (hH s hs).1
        have := (hEpos s).le
        have := gPulse_nonneg R s
        positivity)
      (by simp [ha0]) t ht
    nlinarith [hEpos t, h]
  · have hfderiv : ∀ s : ℝ, HasDerivAt (fun τ => (1 - a τ) * E τ)
        (K * gPulse R s * (1 - Hdrive s) * E s) s := by
      intro s
      have h0 : HasDerivAt (fun τ => 1 - a τ)
          (-(K * gPulse R s * (Hdrive s - a s))) s :=
        (hode s).const_sub 1
      have h1 := h0.mul (hEderiv s)
      convert h1 using 1
      simp only [hφdef, hEdef]
      ring
    have h := sel_nonneg_of_hasDerivAt_nonneg (fun τ => (1 - a τ) * E τ) _
      hfderiv
      (fun s hs => by
        have hHs := (hH s hs).2
        have h1 : 0 ≤ 1 - Hdrive s := by linarith
        have := (hEpos s).le
        have := gPulse_nonneg R s
        positivity)
      (by simp [ha0, hE0]) t ht
    nlinarith [hEpos t, h]

private theorem sel_latch_one_sided_target_upper
    (A : ℝ) (hA : 0 < A) (φ w y : ℝ → ℝ)
    (a b η : ℝ) (hab : a ≤ b)
    (hφ_cont : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc a b, 0 ≤ φ t)
    (hwη : ∀ t ∈ Set.Icc a b, w t ≤ η)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (A * φ t * (w t - y t)) t) :
    y b ≤
      Real.exp (-(A * ∫ t in a..b, φ t)) * y a +
        (1 - Real.exp (-(A * ∫ t in a..b, φ t))) * η := by
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, φ s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (φ t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hφ_cont.intervalIntegrable a t)
      (hφ_cont.stronglyMeasurableAtFilter _ _)
      hφ_cont.continuousAt
  have hΦa : Φ a = 0 := by simp [hΦdef]
  have hΦcont : Continuous Φ := by
    exact continuous_iff_continuousAt.mpr fun t => (hΦderiv t).continuousAt
  set Efun : ℝ → ℝ := fun t => Real.exp (A * Φ t) with hEdef
  have hEderiv : ∀ t : ℝ,
      HasDerivAt Efun (A * φ t * Efun t) t := by
    intro t
    have h1 : HasDerivAt (fun τ => A * Φ τ) (A * φ t) t :=
      (hΦderiv t).const_mul A
    have h2 := h1.exp
    convert h2 using 1
    simp [hEdef]
    ring
  have hEpos : ∀ t, 0 < Efun t := fun t => Real.exp_pos _
  have hEa : Efun a = 1 := by simp [hEdef, hΦa]
  set v : ℝ → ℝ := fun t => (y t - η) * Efun t with hvdef
  have hvderiv : ∀ t ∈ Set.Icc a b,
      HasDerivAt v (A * φ t * (w t - η) * Efun t) t := by
    intro t ht
    have h1 : HasDerivAt (fun τ => y τ - η)
        (A * φ t * (w t - y t)) t := (hy t ht).sub_const η
    have h2 := h1.mul (hEderiv t)
    convert h2 using 1
    simp [hvdef, hEdef]
    ring
  have hvanti : AntitoneOn v (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · intro t ht
      exact (hvderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact ((hvderiv t (interior_subset ht)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [(hvderiv t (interior_subset ht)).deriv]
      have hφt := hφ0 t (interior_subset ht)
      have hwt := hwη t (interior_subset ht)
      have hEt : 0 ≤ Efun t := (hEpos t).le
      have hwsub : w t - η ≤ 0 := by linarith
      have hcoef : 0 ≤ A * φ t * Efun t := by positivity
      have hnonpos : A * φ t * (w t - η) * Efun t ≤ 0 := by
        calc
          A * φ t * (w t - η) * Efun t =
              (A * φ t * Efun t) * (w t - η) := by ring
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcoef hwsub
      simpa using hnonpos
  have hvle : v b ≤ v a :=
    hvanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  have hEbpos := hEpos b
  have hmain : y b - η ≤ (y a - η) / Efun b := by
    have hvle' : (y b - η) * Efun b ≤ (y a - η) * Efun a := by
      simpa [hvdef] using hvle
    rw [hEa] at hvle'
    rw [le_div_iff₀ hEbpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hvle'
  have hEinv :
      (y a - η) / Efun b =
        Real.exp (-(A * ∫ t in a..b, φ t)) * (y a - η) := by
    simp [hEdef, hΦdef, div_eq_mul_inv, Real.exp_neg, mul_comm, mul_left_comm,
      mul_assoc]
  rw [hEinv] at hmain
  have hfinal :
      y b ≤ Real.exp (-(A * ∫ t in a..b, φ t)) * (y a - η) + η := by
    linarith
  calc
    y b ≤ Real.exp (-(A * ∫ t in a..b, φ t)) * (y a - η) + η := hfinal
    _ = Real.exp (-(A * ∫ t in a..b, φ t)) * y a +
        (1 - Real.exp (-(A * ∫ t in a..b, φ t))) * η := by ring

private noncomputable def selLatchSample (j : ℕ) : ℝ :=
  2 * π * (j : ℝ) + 7 * π / 6

private noncomputable def selLatchStableStart (j : ℕ) : ℝ :=
  2 * π * (j : ℝ) + 5 * π / 6

private theorem selLatchSample_add (j n : ℕ) :
    selLatchSample (j + n) = selLatchSample j + 2 * π * (n : ℝ) := by
  unfold selLatchSample
  push_cast
  ring

private theorem selLatchSample_nonneg (j : ℕ) : 0 ≤ selLatchSample j := by
  unfold selLatchSample
  positivity

private theorem selLatchStableStart_nonneg (j : ℕ) : 0 ≤ selLatchStableStart j := by
  unfold selLatchStableStart
  positivity

private theorem sel_latch_cycle_cover {base t : ℝ} (hbase : base ≤ t) :
    ∃ n : ℕ, base + 2 * π * (n : ℝ) ≤ t ∧
      t ≤ base + 2 * π * ((n : ℝ) + 1) := by
  let p : ℝ := 2 * π
  have hp : 0 < p := by
    dsimp [p]
    positivity
  let x : ℝ := (t - base) / p
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (sub_nonneg.mpr hbase) hp.le
  refine ⟨Nat.floor x, ?_, ?_⟩
  · have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hmul := mul_le_mul_of_nonneg_left hfloor hp.le
    have hpx : p * x = t - base := by
      dsimp [x]
      field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith
  · have hlt : x < ((Nat.floor x : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmul := mul_lt_mul_of_pos_left hlt hp
    have hpx : p * x = t - base := by
      dsimp [x]
      field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith

private theorem sel_convex_combo_le_max {θ x η : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * x + (1 - θ) * η ≤ max x η := by
  by_cases hx : x ≤ η
  · have hmax : max x η = η := max_eq_right hx
    rw [hmax]
    nlinarith
  · have hx' : η ≤ x := le_of_lt (lt_of_not_ge hx)
    have hmax : max x η = x := max_eq_left hx'
    rw [hmax]
    nlinarith

private theorem sel_latch_drift_upper
    (K : ℝ) (hK0 : 0 ≤ K) (R : ℕ)
    (y w : ℝ → ℝ) (a b C ε : ℝ)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hC0 : 0 ≤ C)
    (hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1)
    (hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ w t ∧ w t ≤ 1)
    (hy : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (K * gPulse R t * (w t - y t)) t)
    (hg : ∀ t ∈ Set.Icc a b, gPulse R t ≤ C)
    (hε : K * C * (b - a) ≤ ε) :
    y b ≤ y a + ε := by
  have hbound : ∀ t ∈ Set.Icc a b,
      |K * gPulse R t * (w t - y t)| ≤ K * C := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans ha0 ht.1
    have hyt := hy01 t ht0
    have hwt := hw01 t ht0
    have hwy : |w t - y t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hg0 := gPulse_nonneg R t
    have hgC := hg t ht
    calc
      |K * gPulse R t * (w t - y t)|
          = K * gPulse R t * |w t - y t| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hK0, abs_of_nonneg hg0]
      _ ≤ K * C * 1 := by
            gcongr
      _ = K * C := by ring
  have hhold := hold_bound y
    (fun t => K * gPulse R t * (w t - y t)) (K * C) a b hab hy hbound
  have hdiff : y b - y a ≤ ε := by
    calc
      y b - y a ≤ |y b - y a| := le_abs_self _
      _ ≤ K * C * (b - a) := hhold
      _ ≤ ε := hε
  linarith

private theorem sel_latch_stable_max_upper
    (K : ℝ) (hK : 0 < K) (R : ℕ)
    (y w : ℝ → ℝ) (η a b : ℝ)
    (hab : a ≤ b)
    (hwη : ∀ t ∈ Set.Icc a b, w t ≤ η)
    (hy : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (K * gPulse R t * (w t - y t)) t) :
    y b ≤ max (y a) η := by
  have hmain := sel_latch_one_sided_target_upper K hK (gPulse R) w y a b η hab
    (gPulse_continuous R)
    (fun t ht => gPulse_nonneg R t)
    hwη hy
  set θ : ℝ := Real.exp (-(K * ∫ t in a..b, gPulse R t)) with hθ
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    exact (Real.exp_pos _).le
  have hint0 : 0 ≤ ∫ t in a..b, gPulse R t :=
    intervalIntegral.integral_nonneg hab (fun t _ => gPulse_nonneg R t)
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    apply Real.exp_le_one_iff.mpr
    nlinarith [hK.le, hint0]
  exact le_trans (by simpa [hθ] using hmain) (sel_convex_combo_le_max hθ0 hθ1)

private theorem sel_latch_eventual_upper
    (K : ℝ) (hK : 0 < K) (R : ℕ)
    (hθ : ∀ j : ℕ,
      Real.exp (-(K *
        ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
          gPulse R t)) ≤ (1 / 2 : ℝ))
    (hℓ : K * ((187 : ℝ) / 200) ^ R * (5 * π / 6) ≤ (1 / 100 : ℝ))
    (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 8)
    (j₀ : ℕ) (y w : ℝ → ℝ)
    (hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1)
    (hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ w t ∧ w t ≤ 1)
    (hy : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y (K * gPulse R t * (w t - y t)) t)
    (hwStable : ∀ j : ℕ, j₀ ≤ j →
      ∀ t ∈ Set.Icc (2 * π * j + 5 * π / 6) (2 * π * j + 7 * π / 6),
        w t ≤ η) :
    ∃ T : ℝ, ∀ t ≥ T, 0 ≤ y t ∧ y t ≤ 1 / 4 := by
  let C : ℝ := ((187 : ℝ) / 200) ^ R
  let ℓ : ℝ := (1 / 100 : ℝ)
  let B : ℝ := η + 4 * ℓ
  have hK0 : 0 ≤ K := hK.le
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hℓ0 : 0 ≤ ℓ := by norm_num [ℓ]
  have hleak : K * C * (5 * π / 6) ≤ ℓ := by
    simpa [C, ℓ] using hℓ
  have hoff_right :
      ∀ j : ℕ, ∀ t ∈ Set.Icc (selLatchSample j) (2 * π * ((j : ℝ) + 1)),
        y t ≤ y (selLatchSample j) + ℓ := by
    intro j t ht
    have hab : selLatchSample j ≤ t := ht.1
    have ha0 : 0 ≤ selLatchSample j := selLatchSample_nonneg j
    apply sel_latch_drift_upper K hK0 R y w (selLatchSample j) t C ℓ hab ha0 hC0
      hy01 hw01
    · intro s hs
      exact hy s (le_trans ha0 hs.1)
    · intro s hs
      apply sel_gPulse_le_off_right (j := j)
      · simpa [selLatchSample] using hs.1
      · exact le_trans hs.2 ht.2
    · have hlen : t - selLatchSample j ≤ 5 * π / 6 := by
        unfold selLatchSample at ht ⊢
        nlinarith [ht.2]
      calc
        K * C * (t - selLatchSample j) ≤ K * C * (5 * π / 6) := by
          gcongr
        _ ≤ ℓ := hleak
  have hoff_left :
      ∀ j : ℕ, ∀ t ∈ Set.Icc (2 * π * (j : ℝ)) (selLatchStableStart j),
        y t ≤ y (2 * π * (j : ℝ)) + ℓ := by
    intro j t ht
    have hab : 2 * π * (j : ℝ) ≤ t := ht.1
    have ha0 : 0 ≤ 2 * π * (j : ℝ) := by positivity
    apply sel_latch_drift_upper K hK0 R y w (2 * π * (j : ℝ)) t C ℓ hab ha0 hC0
      hy01 hw01
    · intro s hs
      exact hy s (le_trans ha0 hs.1)
    · intro s hs
      apply sel_gPulse_le_off_left (j := j)
      · exact hs.1
      · exact le_trans hs.2 ht.2
    · have hlen : t - 2 * π * (j : ℝ) ≤ 5 * π / 6 := by
        unfold selLatchStableStart at ht
        nlinarith [ht.2]
      calc
        K * C * (t - 2 * π * (j : ℝ)) ≤ K * C * (5 * π / 6) := by
          gcongr
        _ ≤ ℓ := hleak
  have hstable :
      ∀ j : ℕ, j₀ ≤ j → ∀ t ∈ Set.Icc (selLatchStableStart j) (selLatchSample j),
        y t ≤ max (y (selLatchStableStart j)) η := by
    intro j hj t ht
    have hab : selLatchStableStart j ≤ t := ht.1
    apply sel_latch_stable_max_upper K hK R y w η (selLatchStableStart j) t hab
    · intro s hs
      apply hwStable j hj s
      constructor
      · simpa [selLatchStableStart] using hs.1
      · exact le_trans hs.2 ht.2
    · intro s hs
      exact hy s (le_trans (selLatchStableStart_nonneg j) hs.1)
  have hcycle :
      ∀ j : ℕ, j₀ ≤ j →
        y (selLatchSample (j + 1)) ≤
          Real.exp (-(K *
            ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
              (2 * π * (j + 1) + 7 * π / 6), gPulse R t)) *
              y (selLatchSample j) + 2 * ℓ +
            (1 - Real.exp (-(K *
              ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
                (2 * π * (j + 1) + 7 * π / 6), gPulse R t))) * η := by
    intro j hj
    let m : ℝ := 2 * π * ((j : ℝ) + 1)
    let s : ℝ := 2 * π * ((j : ℝ) + 1) + 5 * π / 6
    let e : ℝ := selLatchSample (j + 1)
    have hsam_m : selLatchSample j ≤ m := by
      dsimp [m, selLatchSample]
      nlinarith [Real.pi_pos]
    have hm_s : m ≤ s := by
      dsimp [m, s]
      nlinarith [Real.pi_pos]
    have hs_e : s ≤ e := by
      dsimp [s, e, selLatchSample]
      push_cast
      nlinarith [Real.pi_pos]
    have hm_bound : y m ≤ y (selLatchSample j) + ℓ := by
      apply hoff_right j m
      constructor
      · exact hsam_m
      · rfl
    have hs_bound : y s ≤ y (selLatchSample j) + 2 * ℓ := by
      have hs1 : y s ≤ y m + ℓ := by
        have := hoff_left (j + 1) s
        have hmem : s ∈ Set.Icc (2 * π * ((j + 1 : ℕ) : ℝ)) (selLatchStableStart (j + 1)) := by
          constructor
          · dsimp [s]
            push_cast
            nlinarith [Real.pi_pos]
          · dsimp [s, selLatchStableStart]
            push_cast
            exact le_rfl
        have hthis := this hmem
        simpa [m, s, Nat.cast_add, Nat.cast_one] using hthis
      linarith
    have hmain := sel_latch_one_sided_target_upper K hK (gPulse R) w y s e η hs_e
      (gPulse_continuous R)
      (fun t ht => gPulse_nonneg R t)
      (by
        intro t ht
        apply hwStable (j + 1) (le_trans hj (Nat.le_succ j)) t
        constructor
        · simpa [s, selLatchStableStart, Nat.cast_add, Nat.cast_one] using ht.1
        · simpa [e, selLatchSample, Nat.cast_add, Nat.cast_one] using ht.2)
      (by
        intro t ht
        exact hy t (le_trans (by dsimp [s]; positivity) ht.1))
    have hθnonneg :
        0 ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) :=
      (Real.exp_pos _).le
    calc
      y (selLatchSample (j + 1)) = y e := rfl
      _ ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) * y s +
          (1 - Real.exp (-(K * ∫ t in s..e, gPulse R t))) * η := hmain
      _ ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) *
            (y (selLatchSample j) + 2 * ℓ) +
          (1 - Real.exp (-(K * ∫ t in s..e, gPulse R t))) * η := by
            gcongr
      _ ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) * y (selLatchSample j) +
            2 * ℓ +
          (1 - Real.exp (-(K * ∫ t in s..e, gPulse R t))) * η := by
            have hθle : Real.exp (-(K * ∫ t in s..e, gPulse R t)) ≤ 1 := by
              apply Real.exp_le_one_iff.mpr
              have hint0 : 0 ≤ ∫ t in s..e, gPulse R t :=
                intervalIntegral.integral_nonneg hs_e (fun t _ => gPulse_nonneg R t)
              nlinarith [hK.le, hint0]
            nlinarith [hℓ0, hθnonneg, hθle]
      _ = Real.exp (-(K *
            ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
              (2 * π * (j + 1) + 7 * π / 6), gPulse R t)) *
              y (selLatchSample j) + 2 * ℓ +
            (1 - Real.exp (-(K *
              ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
                (2 * π * (j + 1) + 7 * π / 6), gPulse R t))) * η := by
            congr 3 <;> simp [s, e, selLatchSample, Nat.cast_add, Nat.cast_one]
  have hsample :
      ∀ n : ℕ, y (selLatchSample (j₀ + n)) ≤ B + (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
        have hyb := (hy01 (selLatchSample j₀) (selLatchSample_nonneg j₀)).2
        dsimp [B]
        norm_num
        nlinarith [hη0, hℓ0, hyb]
    | succ n ih =>
        have hjle : j₀ ≤ j₀ + n := Nat.le_add_right _ _
        have hrec := hcycle (j₀ + n) hjle
        have htheta := hθ (j₀ + n + 1)
        have htheta0 :
            0 ≤ Real.exp (-(K *
              ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t)) :=
          (Real.exp_pos _).le
        have hstep :
            y (selLatchSample (j₀ + (n + 1))) ≤
              B + (1 / 2 : ℝ) ^ (n + 1) := by
          have hrec' :
              y (selLatchSample (j₀ + (n + 1))) ≤
                Real.exp (-(K *
                  ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                    (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t)) *
                    y (selLatchSample (j₀ + n)) + 2 * ℓ +
                  (1 - Real.exp (-(K *
                    ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                      (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t))) * η := by
            simpa [Nat.add_assoc] using hrec
          calc
            y (selLatchSample (j₀ + (n + 1))) ≤
                Real.exp (-(K *
                  ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                    (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t)) *
                    y (selLatchSample (j₀ + n)) + 2 * ℓ +
                  (1 - Real.exp (-(K *
                    ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                      (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t))) * η := hrec'
            _ ≤ B + (1 / 2 : ℝ) ^ (n + 1) := by
              have hpownonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
              have hpowstep : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) * (1 / 2) ^ n := by
                rw [pow_succ]
                ring
              set θv : ℝ := Real.exp (-(K *
                  ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                    (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t))
              have hθv0 : 0 ≤ θv := by simpa [θv] using htheta0
              have hθv : θv ≤ 1 / 2 := by simpa [θv, Nat.cast_add, Nat.cast_one] using htheta
              have hfirst :
                  θv * y (selLatchSample (j₀ + n)) + 2 * ℓ + (1 - θv) * η
                    ≤ θv * (B + (1 / 2 : ℝ) ^ n) + 2 * ℓ + (1 - θv) * η := by
                gcongr
              have hsecond :
                  θv * (B + (1 / 2 : ℝ) ^ n) + 2 * ℓ + (1 - θv) * η
                    ≤ B + (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
                dsimp [B]
                nlinarith [hθv, hθv0, hpownonneg, hℓ0]
              dsimp [B]
              rw [hpowstep]
              exact le_trans (by simpa [θv] using hfirst) hsecond
        exact hstep
  refine ⟨selLatchSample (j₀ + 4), ?_⟩
  intro t htT
  have hy_nonneg := (hy01 t (le_trans (selLatchSample_nonneg (j₀ + 4)) htT)).1
  refine ⟨hy_nonneg, ?_⟩
  obtain ⟨n, hnlo, hnhi⟩ := sel_latch_cycle_cover htT
  let j : ℕ := j₀ + 4 + n
  have hj_ge : j₀ ≤ j := by
    dsimp [j]
    omega
  have hj4 : ∃ m : ℕ, j = j₀ + m ∧ 4 ≤ m := by
    refine ⟨4 + n, ?_, ?_⟩
    · dsimp [j]
      omega
    · omega
  have hsamp_eq : selLatchSample j = selLatchSample (j₀ + 4) + 2 * π * (n : ℝ) := by
    simpa [j, Nat.add_assoc] using selLatchSample_add (j₀ + 4) n
  have hnext_eq : selLatchSample (j + 1) =
      selLatchSample (j₀ + 4) + 2 * π * ((n : ℝ) + 1) := by
    simpa [j, Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
      selLatchSample_add (j₀ + 4) (n + 1)
  have htcycle : t ∈ Set.Icc (selLatchSample j) (selLatchSample (j + 1)) := by
    constructor
    · simpa [hsamp_eq] using hnlo
    · simpa [hnext_eq, Nat.cast_add, Nat.cast_one] using hnhi
  obtain ⟨m, hjm, hm4⟩ := hj4
  have hsample_j : y (selLatchSample j) ≤ B + (1 / 2 : ℝ) ^ m := by
    simpa [hjm] using hsample m
  have hpow_le : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (4 : ℕ) := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hm4
  have hsample_j' : y (selLatchSample j) ≤ B + (1 / 16 : ℝ) := by
    norm_num at hpow_le
    nlinarith
  have hcycle_bound : y t ≤ max (y (selLatchSample j) + 2 * ℓ) η := by
    let mpt : ℝ := 2 * π * ((j : ℝ) + 1)
    have hmpt_eq : 2 * π * ((j + 1 : ℕ) : ℝ) = mpt := by
      dsimp [mpt]
      rw [Nat.cast_add, Nat.cast_one]
    have hsample_mpt : selLatchSample j ≤ mpt := by
      change 2 * π * (j : ℝ) + 7 * π / 6 ≤ 2 * π * ((j : ℝ) + 1)
      nlinarith [Real.pi_pos]
    have hm_bound : y mpt ≤ y (selLatchSample j) + ℓ := by
      apply hoff_right j mpt
      exact ⟨hsample_mpt, le_rfl⟩
    have hstable_left :
        2 * π * ((j + 1 : ℕ) : ℝ) ≤ selLatchStableStart (j + 1) := by
      change 2 * π * ((j + 1 : ℕ) : ℝ) ≤
        2 * π * ((j + 1 : ℕ) : ℝ) + 5 * π / 6
      exact le_add_of_nonneg_right (by positivity)
    by_cases ht_m : t ≤ mpt
    · have hmem : t ∈ Set.Icc (selLatchSample j) mpt := ⟨htcycle.1, ht_m⟩
      have h1 := hoff_right j t hmem
      exact le_trans (by nlinarith [hℓ0]) (le_max_left _ _)
    · have hm_t : mpt ≤ t := le_of_lt (lt_of_not_ge ht_m)
      by_cases ht_s : t ≤ selLatchStableStart (j + 1)
      ·
        have hleft : y t ≤ y mpt + ℓ := by
          have hmem : t ∈ Set.Icc (2 * π * ((j + 1 : ℕ) : ℝ))
              (selLatchStableStart (j + 1)) := by
            constructor
            · rw [hmpt_eq]
              exact hm_t
            · exact ht_s
          have := hoff_left (j + 1) t hmem
          rw [hmpt_eq] at this
          exact this
        exact le_trans (by nlinarith) (le_max_left _ _)
      · have hs_t : selLatchStableStart (j + 1) ≤ t := le_of_lt (lt_of_not_ge ht_s)
        have hs_bound :
            y (selLatchStableStart (j + 1)) ≤ y (selLatchSample j) + 2 * ℓ := by
          have hleft : y (selLatchStableStart (j + 1)) ≤ y mpt + ℓ := by
            have hmem :
                selLatchStableStart (j + 1) ∈ Set.Icc (2 * π * ((j + 1 : ℕ) : ℝ))
                (selLatchStableStart (j + 1)) := by
              constructor
              · exact hstable_left
              · exact le_rfl
            have := hoff_left (j + 1) (selLatchStableStart (j + 1)) hmem
            rw [hmpt_eq] at this
            exact this
          linarith [hm_bound]
        have hstab : y t ≤ max (y (selLatchStableStart (j + 1))) η := by
          have hmem : t ∈ Set.Icc (selLatchStableStart (j + 1)) (selLatchSample (j + 1)) := by
            constructor
            · exact hs_t
            · exact htcycle.2
          exact hstable (j + 1) (le_trans hj_ge (Nat.le_succ j)) t hmem
        have hstab_bound :
            max (y (selLatchStableStart (j + 1))) η ≤ max (y (selLatchSample j) + 2 * ℓ) η := by
          apply max_le
          · exact le_trans hs_bound (le_max_left _ _)
          · exact le_max_right _ _
        exact le_trans hstab hstab_bound
  have harith : B + (1 / 16 : ℝ) + 2 * ℓ < 1 / 4 := by
    calc
      B + (1 / 16 : ℝ) + 2 * ℓ = η + (49 / 400 : ℝ) := by
        dsimp [B, ℓ]
        ring
      _ < 1 / 8 + (49 / 400 : ℝ) := by
        linarith [hη]
      _ < 1 / 4 := by
        norm_num
  have hmax_bound : max (y (selLatchSample j) + 2 * ℓ) η ≤ B + (1 / 16 : ℝ) + 2 * ℓ := by
    apply max_le
    · calc
        y (selLatchSample j) + 2 * ℓ = 2 * ℓ + y (selLatchSample j) := by ring
        _ ≤ 2 * ℓ + (B + (1 / 16 : ℝ)) := add_le_add_right hsample_j' (2 * ℓ)
        _ = B + (1 / 16 : ℝ) + 2 * ℓ := by ring
    · dsimp [B]
      linarith [hℓ0]
  exact le_of_lt (lt_of_le_of_lt (le_trans hcycle_bound hmax_bound) harith)

/-! ## Public selector latch convergence -/

section SelectorConv

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- **Selector latch high (analytic).**  If the indicator is eventually
`≥ 1 − eta` on the active windows, and the flag coordinate stays in `[0,1]`
along the whole trajectory, then the selector latch `La.a` eventually sits in
`[3/4, 1]`.  The parameter hypotheses `hθ`/`hℓ` are the feasibility facts that
`sel_latch_parameter_exists` chooses; `hη` is `eta < 1/8` (already a field of
`I`).  Proved by the integrating-factor engine `sel_latch_eventual_upper`. -/
theorem selector_latch_high
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {flagCoord : Fin d} (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (La : SelectorHaltLatchSol sol I.Hval K R)
    (hK : 0 < K)
    (hθ : ∀ j : ℕ,
      Real.exp (-(K *
        ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
          gPulse R t)) ≤ (1 / 2 : ℝ))
    (hℓ : K * ((187 : ℝ) / 200) ^ R * (5 * π / 6) ≤ (1 / 100 : ℝ))
    (hflagDom : ∀ t : ℝ, 0 ≤ t → sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1)
    (hhigh : ∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ sched.zActiveWindow j,
      1 - I.eta ≤ I.Hval (sol.z t)) :
    ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1 := by
  obtain ⟨J, hJ⟩ := hhigh
  have hHunit : ∀ t : ℝ, 0 ≤ t →
      0 ≤ I.Hval (sol.z t) ∧ I.Hval (sol.z t) ≤ 1 := by
    intro t ht
    exact I.in_unit (sol.z t) (hflagDom t ht)
  have haUnit : ∀ t : ℝ, 0 ≤ t → 0 ≤ La.a t ∧ La.a t ≤ 1 :=
    sel_latch_mem_unitInterval (fun t => I.Hval (sol.z t)) La.a K hK R
      La.init_a La.ode_a hHunit
  -- complementary coordinate `y = 1 − a`, target `w = 1 − Hval`
  let y : ℝ → ℝ := fun t => 1 - La.a t
  let wtar : ℝ → ℝ := fun t => 1 - I.Hval (sol.z t)
  have hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1 := by
    intro t ht
    have ht' := haUnit t ht
    dsimp [y]
    constructor <;> linarith
  have hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ wtar t ∧ wtar t ≤ 1 := by
    intro t ht
    have ht' := hHunit t ht
    dsimp [wtar]
    constructor <;> linarith
  have hyderiv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y (K * gPulse R t * (wtar t - y t)) t := by
    intro t _ht
    have h0 : HasDerivAt (fun τ => 1 - La.a τ)
        (-(K * gPulse R t * (I.Hval (sol.z t) - La.a t))) t :=
      (La.ode_a t).const_sub 1
    convert h0 using 1 <;> dsimp [y, wtar] <;> ring
  have hwStable : ∀ j : ℕ, J ≤ j →
      ∀ t ∈ Set.Icc (2 * π * j + 5 * π / 6) (2 * π * j + 7 * π / 6),
        wtar t ≤ I.eta := by
    intro j hj t ht
    have hmem : t ∈ sched.zActiveWindow j :=
      sched.stableWindow_subset_zActiveWindow j ht
    have hH := hJ j hj t hmem
    dsimp [wtar]
    linarith
  obtain ⟨T, hT⟩ := sel_latch_eventual_upper K hK R hθ hℓ
    I.eta I.eta_nonneg I.eta_lt J y wtar hy01 hw01 hyderiv hwStable
  refine ⟨T, ?_⟩
  intro t ht
  have hyT := hT t ht
  dsimp [y] at hyT
  refine ⟨by linarith, by linarith⟩

/-- **Selector latch low (analytic).**  If the indicator is everywhere `≤ eta`
on the active windows, and the flag coordinate stays in `[0,1]` along the whole
trajectory, then the selector latch `La.a` eventually sits in `[0, 1/4]`.
Proved by the integrating-factor engine `sel_latch_eventual_upper`. -/
theorem selector_latch_low
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {flagCoord : Fin d} (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (La : SelectorHaltLatchSol sol I.Hval K R)
    (hK : 0 < K)
    (hθ : ∀ j : ℕ,
      Real.exp (-(K *
        ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
          gPulse R t)) ≤ (1 / 2 : ℝ))
    (hℓ : K * ((187 : ℝ) / 200) ^ R * (5 * π / 6) ≤ (1 / 100 : ℝ))
    (hflagDom : ∀ t : ℝ, 0 ≤ t → sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1)
    (hlow : ∀ j : ℕ, ∀ t ∈ sched.zActiveWindow j,
      I.Hval (sol.z t) ≤ I.eta) :
    ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4 := by
  have hHunit : ∀ t : ℝ, 0 ≤ t →
      0 ≤ I.Hval (sol.z t) ∧ I.Hval (sol.z t) ≤ 1 := by
    intro t ht
    exact I.in_unit (sol.z t) (hflagDom t ht)
  have haUnit : ∀ t : ℝ, 0 ≤ t → 0 ≤ La.a t ∧ La.a t ≤ 1 :=
    sel_latch_mem_unitInterval (fun t => I.Hval (sol.z t)) La.a K hK R
      La.init_a La.ode_a hHunit
  let y : ℝ → ℝ := La.a
  let wtar : ℝ → ℝ := fun t => I.Hval (sol.z t)
  have hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1 := fun t ht => haUnit t ht
  have hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ wtar t ∧ wtar t ≤ 1 := fun t ht => hHunit t ht
  have hyderiv : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y (K * gPulse R t * (wtar t - y t)) t := by
    intro t _ht
    simpa [y, wtar] using La.ode_a t
  have hwStable : ∀ j : ℕ, 0 ≤ j →
      ∀ t ∈ Set.Icc (2 * π * j + 5 * π / 6) (2 * π * j + 7 * π / 6),
        wtar t ≤ I.eta := by
    intro j _hj t ht
    have hmem : t ∈ sched.zActiveWindow j :=
      sched.stableWindow_subset_zActiveWindow j ht
    exact hlow j t hmem
  obtain ⟨T, hT⟩ := sel_latch_eventual_upper K hK R hθ hℓ
    I.eta I.eta_nonneg I.eta_lt 0 y wtar hy01 hw01 hyderiv hwStable
  exact ⟨T, hT⟩

end SelectorConv

end Ripple.BoundedUniversality.BGP
