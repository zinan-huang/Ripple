import Ripple.BoundedUniversality.BGP.SelectorExistence
import Ripple.Core.ODEBox

/-!
Ripple.BoundedUniversality.BGP.SelectorAprioriBound
-------------------------------
Stage B of the 3rd-vacuity fix: discharge
`Ripple.FiniteHorizonBound (selectorAssembledVectorField …) y₀`
outright, making `selector_sol_exists` fully unconditional.

We build the per-coordinate a-priori bound for an ARBITRARY solution `y` of the autonomous selector
field on `[0,T)` with `y 0 = y₀` (the selector init).  Each coordinate's scalar ODE is
extracted via
`hasDerivAt_pi` + the field per-coordinate evaluation, then bounded:
- clocks `α` (`α'=cα·α`), `μ` (`μ'=cμ`): exact linear-ODE values;
- trig `s,c` (`s'=c, c'=-s`): `s²+c²` conserved;
- gates: linear-homogeneous, finite-time;
- fiber `z,u`: coupled contraction box;
- `λ`: logistic interval `[0,1]`;
- `G`, `contractA`: integral / contraction.

This file is additive.  We re-derive the (private) per-coordinate field-eval lemmas locally.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial Set

/-- A function with constant derivative `c` on `[0,T)` is affine: `g t = g 0 + c·t`. -/
theorem affine_of_const_deriv {T c : ℝ} (g : ℝ → ℝ)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt g c t) :
    ∀ t ∈ Ico (0 : ℝ) T, g t = g 0 + c * t := by
  intro t ht
  have key : ∀ s ∈ Icc (0 : ℝ) t, (fun r => g r - c * r) s = (fun r => g r - c * r) 0 := by
    apply constant_of_has_deriv_right_zero
    · refine ContinuousOn.sub ?_ (continuous_const.mul continuous_id).continuousOn
      intro s hs
      have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      exact (hderiv s hsT).continuousAt.continuousWithinAt
    · intro s hs
      have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
      have hg := hderiv s hsT
      have hcr : HasDerivAt (fun r : ℝ => c * r) c s := by
        simpa using (hasDerivAt_id s).const_mul c
      have : HasDerivAt (fun r => g r - c * r) (c - c) s := hg.sub hcr
      simpa using this.hasDerivWithinAt
  have ht0 : t ∈ Icc (0 : ℝ) t := ⟨ht.1, le_refl t⟩
  have := key t ht0
  simp only at this
  linarith [this]

/-- A function solving the scalar linear ODE `g' = c·g` on `[0,T)` is `g t = g 0 · exp(c·t)`. -/
theorem scalar_linear_ode_eq {T c : ℝ} (g : ℝ → ℝ)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt g (c * g t) t) :
    ∀ t ∈ Ico (0 : ℝ) T, g t = g 0 * Real.exp (c * t) := by
  intro t ht
  have key : ∀ s ∈ Icc (0 : ℝ) t,
      (fun r => g r * Real.exp (-c * r)) s = (fun r => g r * Real.exp (-c * r)) 0 := by
    apply constant_of_has_deriv_right_zero
    · refine ContinuousOn.mul ?_
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      intro s hs
      have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      exact (hderiv s hsT).continuousAt.continuousWithinAt
    · intro s hs
      have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
      have hg := hderiv s hsT
      have hexp : HasDerivAt (fun r => Real.exp (-c * r)) (Real.exp (-c * s) * (-c * 1)) s :=
        ((hasDerivAt_id s).const_mul (-c)).exp
      have hp := hg.mul hexp
      have hz : c * g s * Real.exp (-c * s) + g s * (Real.exp (-c * s) * (-c * 1)) = 0 := by ring
      rw [hz] at hp
      exact hp.hasDerivWithinAt
  have ht0 : t ∈ Icc (0 : ℝ) t := ⟨ht.1, le_refl t⟩
  have hk := key t ht0
  simp only [neg_mul, mul_zero, Real.exp_zero, mul_one] at hk
  have hk2 : g 0 = g t * Real.exp (-(c * t)) := hk.symm
  rw [hk2, mul_assoc, ← Real.exp_add]
  have h2 : -(c * t) + c * t = 0 := by ring
  rw [h2, Real.exp_zero, mul_one]

/-- The Grönwall closed-form bound is nonnegative at nonnegative times when
the initial and forcing bounds are nonnegative. -/
theorem gronwallBound_nonneg_of_nonneg {δ K ε x : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    0 ≤ gronwallBound δ K ε x := by
  by_cases hK : K = 0
  · simp [gronwallBound, hK, add_nonneg hδ (mul_nonneg hε hx)]
  · rw [gronwallBound_of_K_ne_0 hK]
    have hδexp : 0 ≤ δ * Real.exp (K * x) :=
      mul_nonneg hδ (le_of_lt (Real.exp_pos _))
    have hforce : 0 ≤ ε / K * (Real.exp (K * x) - 1) := by
      by_cases hKpos : 0 < K
      · have hKx : 0 ≤ K * x := mul_nonneg hKpos.le hx
        have hexp : 0 ≤ Real.exp (K * x) - 1 :=
          sub_nonneg.mpr (Real.one_le_exp_iff.mpr hKx)
        exact mul_nonneg (div_nonneg hε hKpos.le) hexp
      · have hKle : K ≤ 0 := le_of_not_gt hKpos
        have hKneg : K < 0 := lt_of_le_of_ne hKle hK
        have hKx : K * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hKneg.le hx
        have hexp : Real.exp (K * x) - 1 ≤ 0 :=
          sub_nonpos.mpr (Real.exp_le_one_iff.mpr hKx)
        exact mul_nonneg_of_nonpos_of_nonpos
          (div_nonpos_of_nonneg_of_nonpos hε hKneg.le) hexp
    exact add_nonneg hδexp hforce

/-- The Grönwall bound is monotone in the forcing bound `ε`. -/
theorem gronwallBound_mono_epsilon {δ K x : ℝ} (hx : 0 ≤ x) :
    Monotone (fun ε : ℝ => gronwallBound δ K ε x) := by
  intro ε₁ ε₂ hε
  let f : ℝ → ℝ := fun s => gronwallBound δ K ε₁ s
  let f' : ℝ → ℝ := fun s => K * f s + ε₁
  have hf : ContinuousOn f (Icc (0 : ℝ) x) := by
    intro s hs
    exact (hasDerivAt_gronwallBound δ K ε₁ s).continuousAt.continuousWithinAt
  have hfderiv : ∀ s ∈ Ico (0 : ℝ) x,
      HasDerivWithinAt f (f' s) (Ici s) s := by
    intro s hs
    exact (hasDerivAt_gronwallBound δ K ε₁ s).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) x, f' s ≤ K * f s + ε₂ := by
    intro s hs
    dsimp [f']
    linarith
  have hgr := le_gronwallBound_of_liminf_deriv_right_le
    (f := f) (f' := f') (δ := δ) (K := K) (ε := ε₂)
    (a := (0 : ℝ)) (b := x) hf
    (fun s hs _r hr => (hfderiv s hs).liminf_right_slope_le hr)
    (by dsimp [f]; rw [gronwallBound_x0]) hbound x ⟨hx, le_rfl⟩
  simpa [f, sub_zero] using hgr

/-- The Grönwall bound is monotone in the growth coefficient `K`. -/
theorem gronwallBound_mono_K {δ ε x : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    Monotone (fun K : ℝ => gronwallBound δ K ε x) := by
  intro K₁ K₂ hK
  let f : ℝ → ℝ := fun s => gronwallBound δ K₁ ε s
  let f' : ℝ → ℝ := fun s => K₁ * f s + ε
  have hf : ContinuousOn f (Icc (0 : ℝ) x) := by
    intro s hs
    exact (hasDerivAt_gronwallBound δ K₁ ε s).continuousAt.continuousWithinAt
  have hfderiv : ∀ s ∈ Ico (0 : ℝ) x,
      HasDerivWithinAt f (f' s) (Ici s) s := by
    intro s hs
    exact (hasDerivAt_gronwallBound δ K₁ ε s).hasDerivWithinAt
  have hnonneg : ∀ s ∈ Ico (0 : ℝ) x, 0 ≤ f s := by
    intro s hs
    exact gronwallBound_nonneg_of_nonneg hδ hε hs.1
  have hbound : ∀ s ∈ Ico (0 : ℝ) x, f' s ≤ K₂ * f s + ε := by
    intro s hs
    have hmul : K₁ * f s ≤ K₂ * f s :=
      mul_le_mul_of_nonneg_right hK (hnonneg s hs)
    dsimp [f']
    linarith
  have hgr := le_gronwallBound_of_liminf_deriv_right_le
    (f := f) (f' := f') (δ := δ) (K := K₂) (ε := ε)
    (a := (0 : ℝ)) (b := x) hf
    (fun s hs _r hr => (hfderiv s hs).liminf_right_slope_le hr)
    (by dsimp [f]; rw [gronwallBound_x0]) hbound x ⟨hx, le_rfl⟩
  simpa [f, sub_zero] using hgr

variable {d B : ℕ} {V : Type} [Fintype V]
  (branch : V → BranchData d B)
  (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
  (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
  (HP : MvPolynomial (Fin d) ℚ)
  (Aq Kq cμq cαq : ℚ) (L R : ℕ)
  (y : Fin (selectorDim d V) → ℝ)

/-- Local (non-private) copy: the assembled field at the `μ` coordinate is the constant `cμ`. -/
theorem aprioriField_mu_eq :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractMu d)) = (cμq : ℝ) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selOfContract V (contractMu d)) = C cμq from by
    simp [selectorAssembledField, selOfContract, contractMu, contractS]]
  simp

/-- Local copy: the assembled field at the `α` coordinate is `cα · α`. -/
theorem aprioriField_alpha_eq :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractAlpha d)) =
      (cαq : ℝ) * y (selOfContract V (contractAlpha d)) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selOfContract V (contractAlpha d)) =
        C cαq * X (selOfContract V (contractAlpha d)) from by
    simp [selectorAssembledField, selOfContract, contractAlpha, contractS]]
  simp

/-- The `μ` coordinate of any solution is affine: `μ(t) = μ(0) + cμ·t`. -/
theorem mu_coord_affine
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      yt t (selOfContract V (contractMu d))
        = yt 0 (selOfContract V (contractMu d)) + (cμq : ℝ) * t := by
  have h := affine_of_const_deriv (T := T) (c := (cμq : ℝ))
    (fun s => yt s (selOfContract V (contractMu d))) ?_
  · exact h
  · intro t ht
    have hpi := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractMu d))
    rw [aprioriField_mu_eq] at hpi
    exact hpi

/-- The `α` coordinate of any solution is `α(t) = α(0)·exp(cα·t)`. -/
theorem alpha_coord_eq
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      yt t (selOfContract V (contractAlpha d))
        = yt 0 (selOfContract V (contractAlpha d)) * Real.exp ((cαq : ℝ) * t) := by
  have h := scalar_linear_ode_eq (T := T) (c := (cαq : ℝ))
    (fun s => yt s (selOfContract V (contractAlpha d))) ?_
  · exact h
  · intro t ht
    have hpi := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractAlpha d))
    rw [aprioriField_alpha_eq] at hpi
    exact hpi

/-- Local copy: field at the `s` coordinate is the `c` coordinate (`s' = c`). -/
theorem aprioriField_s_eq :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractS d)) = y (selOfContract V (contractC d)) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selOfContract V (contractS d)) =
        X (selOfContract V (contractC d)) from by
    simp [selectorAssembledField, selOfContract, contractS]]
  simp

/-- Local copy: field at the `c` coordinate is `-s` (`c' = -s`). -/
theorem aprioriField_c_eq :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractC d)) = -y (selOfContract V (contractS d)) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selOfContract V (contractC d)) =
        -X (selOfContract V (contractS d)) from by
    simp [selectorAssembledField, selOfContract, contractC, contractS]]
  simp

theorem aprioriField_warmGain_eq :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selWarmGainCoord d V) = 0 := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selWarmGainCoord d V) = 0 from by
    simp [selectorAssembledField, selWarmGainCoord, Fin.append_right, Fin.append, Fin.addCases]]
  simp

theorem warmGain_coord_const
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      yt t (selWarmGainCoord d V) = yt 0 (selWarmGainCoord d V) := by
  intro t ht
  have h0T : (0 : ℝ) ≤ t := ht.1
  have hdiff : DifferentiableOn ℝ (fun s => yt s (selWarmGainCoord d V)) (Set.Icc 0 t) := by
    intro x hx
    have hxIco : x ∈ Ico (0 : ℝ) T := ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩
    exact ((hasDerivAt_pi.mp (hderiv x hxIco)) (selWarmGainCoord d V)).differentiableAt.differentiableWithinAt
  have hderivW : ∀ x ∈ Set.Ico (0 : ℝ) t,
      derivWithin (fun s => yt s (selWarmGainCoord d V)) (Set.Icc 0 t) x = 0 := by
    intro x hx
    have hxIco : x ∈ Ico (0 : ℝ) T := ⟨hx.1, lt_trans hx.2 ht.2⟩
    have huniq : UniqueDiffWithinAt ℝ (Set.Icc 0 t) x :=
      (uniqueDiffOn_Icc (lt_of_le_of_lt hx.1 hx.2)) x (Set.Ico_subset_Icc_self hx)
    have hpi := (hasDerivAt_pi.mp (hderiv x hxIco)) (selWarmGainCoord d V)
    rw [aprioriField_warmGain_eq] at hpi
    exact hpi.hasDerivWithinAt.derivWithin huniq
  exact constant_of_derivWithin_zero hdiff hderivW t (Set.right_mem_Icc.mpr h0T)

/-- The trig pair conserves `s²+c²`: it stays at its initial value. -/
theorem sc_conservation
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      (yt t (selOfContract V (contractS d))) ^ 2 + (yt t (selOfContract V (contractC d))) ^ 2
        = (yt 0 (selOfContract V (contractS d))) ^ 2
          + (yt 0 (selOfContract V (contractC d))) ^ 2 := by
  have h := affine_of_const_deriv (T := T) (c := (0 : ℝ))
    (fun s => (yt s (selOfContract V (contractS d))) ^ 2
      + (yt s (selOfContract V (contractC d))) ^ 2) ?_
  · intro t ht; have := h t ht; simpa using this
  · intro t ht
    have hs := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractS d))
    have hc := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractC d))
    rw [aprioriField_s_eq] at hs
    rw [aprioriField_c_eq] at hc
    have hs2 := hs.pow 2
    have hc2 := hc.pow 2
    have hsum := hs2.add hc2
    have hz : (2 : ℕ) * yt t (selOfContract V (contractS d)) ^ (2 - 1)
          * yt t (selOfContract V (contractC d))
        + (2 : ℕ) * yt t (selOfContract V (contractC d)) ^ (2 - 1)
          * (-yt t (selOfContract V (contractS d))) = 0 := by
      push_cast; ring
    rw [hz] at hsum
    exact hsum

/-- Trig realization: any solution with `s(0)=0, c(0)=1` has clock coords
`s t = sin t`, `c t = cos t` (via the conserved
`E = (s−sin)²+(c−cos)²`, `E'=0`, `E(0)=0`). -/
theorem sc_realize
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hs0 : yt 0 (selOfContract V (contractS d)) = 0)
    (hc0 : yt 0 (selOfContract V (contractC d)) = 1) :
    ∀ t ∈ Ico (0 : ℝ) T,
      yt t (selOfContract V (contractS d)) = Real.sin t
        ∧ yt t (selOfContract V (contractC d)) = Real.cos t := by
  have hE : ∀ t ∈ Ico (0 : ℝ) T,
      (yt t (selOfContract V (contractS d)) - Real.sin t) ^ 2
        + (yt t (selOfContract V (contractC d)) - Real.cos t) ^ 2 = 0 := by
    have key := affine_of_const_deriv (T := T) (c := (0 : ℝ))
      (fun r => (yt r (selOfContract V (contractS d)) - Real.sin r) ^ 2
        + (yt r (selOfContract V (contractC d)) - Real.cos r) ^ 2) ?_
    · intro t ht
      have h := key t ht
      simp only [mul_zero, add_zero] at h
      rw [h, hs0, hc0]; norm_num
    · intro t ht
      have hsd := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractS d))
      have hcd := (hasDerivAt_pi.mp (hderiv t ht)) (selOfContract V (contractC d))
      rw [aprioriField_s_eq] at hsd
      rw [aprioriField_c_eq] at hcd
      have e1 : HasDerivAt (fun r => (yt r (selOfContract V (contractS d)) - Real.sin r) ^ 2)
          (2 * (yt t (selOfContract V (contractS d)) - Real.sin t)
            * (yt t (selOfContract V (contractC d)) - Real.cos t)) t := by
        simpa using (hsd.sub (Real.hasDerivAt_sin t)).pow 2
      have e2 : HasDerivAt (fun r => (yt r (selOfContract V (contractC d)) - Real.cos r) ^ 2)
          (2 * (yt t (selOfContract V (contractC d)) - Real.cos t)
            * (-(yt t (selOfContract V (contractS d))) + Real.sin t)) t := by
        simpa using (hcd.sub (Real.hasDerivAt_cos t)).pow 2
      have hsum0 := e1.add e2
      have hval : 2 * (yt t (selOfContract V (contractS d)) - Real.sin t)
            * (yt t (selOfContract V (contractC d)) - Real.cos t)
          + 2 * (yt t (selOfContract V (contractC d)) - Real.cos t)
            * (-(yt t (selOfContract V (contractS d))) + Real.sin t) = 0 := by ring
      rw [hval] at hsum0
      exact hsum0
  intro t ht
  have h := hE t ht
  have hs2 : (yt t (selOfContract V (contractS d)) - Real.sin t) ^ 2 = 0 := by
    nlinarith [sq_nonneg (yt t (selOfContract V (contractS d)) - Real.sin t),
      sq_nonneg (yt t (selOfContract V (contractC d)) - Real.cos t)]
  have hc2 : (yt t (selOfContract V (contractC d)) - Real.cos t) ^ 2 = 0 := by
    nlinarith [sq_nonneg (yt t (selOfContract V (contractS d)) - Real.sin t),
      sq_nonneg (yt t (selOfContract V (contractC d)) - Real.cos t)]
  refine ⟨?_, ?_⟩
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs2; linarith
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc2; linarith

/-- Local copy: field at the `z_i` coordinate is `A·α·gateZ·(mix_i − z_i)`. -/
theorem aprioriField_z_eq (i : Fin d) :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selZ V i) =
      (Aq : ℝ) * y (selOfContract V (contractAlpha d)) * y (selOfContract V (contractGateZ d))
        * (MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selectorMixField branch i)
          - y (selZ V i)) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selZ V i) =
        C Aq * X (selOfContract V (contractAlpha d)) * X (selOfContract V (contractGateZ d))
          * (selectorMixField branch i - X (selZ V i)) from by
    simp [selectorAssembledField, selZ, selOfContract, contractZ, contractTailZ]]
  simp [eval₂_mul, eval₂_C, eval₂_X, eval₂_sub]

/-- Local copy: field at the `u_i` coordinate is `A·α·gateU·(z_i − u_i)`. -/
theorem aprioriField_u_eq (i : Fin d) :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selU V i) =
      (Aq : ℝ) * y (selOfContract V (contractAlpha d)) * y (selOfContract V (contractGateU d))
        * (y (selZ V i) - y (selU V i)) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selU V i) =
        C Aq * X (selOfContract V (contractAlpha d)) * X (selOfContract V (contractGateU d))
          * (X (selZ V i) - X (selU V i)) from by
    simp [selectorAssembledField, selU, selZ, selOfContract, contractU, contractTailU]]
  simp [eval₂_mul, eval₂_C, eval₂_X, eval₂_sub]

/-- Local copy: field at the `G` coordinate is `eval(chiGate)·eval(gain)`. -/
theorem aprioriField_G_eq :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selGCoord d V) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) y chiGateP
        * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y gainP := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selGCoord d V) = selectorGainFieldPoly chiGateP gainP from by
    simp [selectorAssembledField, selGCoord, Fin.append_right]; rfl]
  rw [eval₂_selectorGainFieldPoly]

theorem aprioriField_gateZ_eq :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractGateZ d)) =
      -((cμq : ℝ) * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selRP d V L)
        + y (selOfContract V (contractMu d))
          * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selRPderiv d V L))
        * y (selOfContract V (contractGateZ d)) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selOfContract V (contractGateZ d)) =
        -((C cμq * selRP d V L
          + X (selOfContract V (contractMu d)) * selRPderiv d V L) *
          X (selOfContract V (contractGateZ d))) from by
    simp [selectorAssembledField, selOfContract, contractGateZ]]
  simp only [eval₂_neg, eval₂_mul, eval₂_add, eval₂_C, eval₂_X, eq_ratCast]; ring

theorem aprioriField_gateU_eq :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractGateU d)) =
      -((cμq : ℝ) * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selQP d V L)
        + y (selOfContract V (contractMu d))
          * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selQPderiv d V L))
        * y (selOfContract V (contractGateU d)) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selOfContract V (contractGateU d)) =
        -((C cμq * selQP d V L
          + X (selOfContract V (contractMu d)) * selQPderiv d V L) *
          X (selOfContract V (contractGateU d))) from by
    simp [selectorAssembledField, selOfContract, contractGateU]]
  simp only [eval₂_neg, eval₂_mul, eval₂_add, eval₂_C, eval₂_X, eq_ratCast]; ring

theorem scalar_linear_homog_abs_bound {T : ℝ} (g k : ℝ → ℝ) (Kbd : ℝ)
    (hKbd : ∀ t ∈ Ico (0 : ℝ) T, |k t| ≤ Kbd)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt g (-(k t) * g t) t) :
    ∀ t ∈ Ico (0 : ℝ) T, |g t| ≤ |g 0| * Real.exp (Kbd * T) := by
  intro t ht
  have hcont : ContinuousOn g (Icc (0 : ℝ) t) := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    exact (hderiv s hsT).continuousAt.continuousWithinAt
  have hderivWithin : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt g (-(k s) * g s) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    exact (hderiv s hsT).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t,
      ‖-(k s) * g s‖ ≤ Kbd * ‖g s‖ + 0 := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    calc
      ‖-(k s) * g s‖ = |k s| * ‖g s‖ := by
        simp [Real.norm_eq_abs, abs_mul]
      _ ≤ Kbd * ‖g s‖ :=
        mul_le_mul_of_nonneg_right (hKbd s hsT) (norm_nonneg _)
      _ = Kbd * ‖g s‖ + 0 := by ring
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := g) (f' := fun s => -(k s) * g s) (δ := |g 0|)
    (K := Kbd) (ε := 0) (a := (0 : ℝ)) (b := t)
    hcont hderivWithin (by simp [Real.norm_eq_abs]) hbound t ⟨ht.1, le_rfl⟩
  have hgr' : |g t| ≤ |g 0| * Real.exp (Kbd * t) := by
    simpa [Real.norm_eq_abs, gronwallBound_ε0, sub_zero] using hgr
  have h0T : (0 : ℝ) < T := lt_of_le_of_lt ht.1 ht.2
  have hKbd_nonneg : 0 ≤ Kbd :=
    le_trans (abs_nonneg (k 0)) (hKbd 0 ⟨le_rfl, h0T⟩)
  have hexp : Real.exp (Kbd * t) ≤ Real.exp (Kbd * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt ht.2) hKbd_nonneg)
  exact hgr'.trans (mul_le_mul_of_nonneg_left hexp (abs_nonneg (g 0)))

theorem gateZ_coord_abs_bound
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hSelRP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1)
    (hSelRPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ)) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateZ d))| ≤
        |yt 0 (selOfContract V (contractGateZ d))| *
          Real.exp ((|(cμq : ℝ)|
            + (|yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T)
              * (L : ℝ)) * T) := by
  let k : ℝ → ℝ := fun t =>
    (cμq : ℝ) * MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)
      + yt t (selOfContract V (contractMu d))
        * MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)
  let Kbd : ℝ := |(cμq : ℝ)|
    + (|yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T) * (L : ℝ)
  have hlin := scalar_linear_homog_abs_bound (T := T)
    (g := fun t => yt t (selOfContract V (contractGateZ d))) (k := k)
    (Kbd := Kbd) ?_ ?_
  · simpa [k, Kbd] using hlin
  · intro τ hτ
    let rp := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt τ) (selRP d V L)
    let rpd := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt τ) (selRPderiv d V L)
    let mu := yt τ (selOfContract V (contractMu d))
    let muBd := |yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T
    have hT_nonneg : 0 ≤ T := le_trans hτ.1 (le_of_lt hτ.2)
    have hmuBd_nonneg : 0 ≤ muBd := by
      dsimp [muBd]
      exact add_nonneg (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) hT_nonneg)
    have hmu : |mu| ≤ muBd := by
      dsimp [mu, muBd]
      rw [mu_coord_affine (branch := branch) (chiResetP := chiResetP)
        (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
        (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
        (cμq := cμq) (cαq := cαq) (L := L) (R := R)
        (yt := yt) (T := T) hderiv τ hτ]
      have h1 := abs_add_le (yt 0 (selOfContract V (contractMu d))) ((cμq : ℝ) * τ)
      rw [abs_mul, abs_of_nonneg hτ.1] at h1
      have h2 : |(cμq : ℝ)| * τ ≤ |(cμq : ℝ)| * T :=
        mul_le_mul_of_nonneg_left (le_of_lt hτ.2) (abs_nonneg _)
      linarith
    have hRp : |rp| ≤ 1 := by simpa [rp] using hSelRP τ hτ
    have hRpd : |rpd| ≤ (L : ℝ) := by simpa [rpd] using hSelRPderiv τ hτ
    have hterm1 : |(cμq : ℝ) * rp| ≤ |(cμq : ℝ)| * 1 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hRp (abs_nonneg _)
    have hterm2 : |mu * rpd| ≤ muBd * (L : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hmu hRpd (abs_nonneg _) hmuBd_nonneg
    have hsum : |(cμq : ℝ) * rp + mu * rpd| ≤ |(cμq : ℝ)| + muBd * (L : ℝ) := by
      calc
        |(cμq : ℝ) * rp + mu * rpd| ≤ |(cμq : ℝ) * rp| + |mu * rpd| :=
          abs_add_le _ _
        _ ≤ |(cμq : ℝ)| * 1 + muBd * (L : ℝ) :=
          add_le_add hterm1 hterm2
        _ = |(cμq : ℝ)| + muBd * (L : ℝ) := by ring
    simpa [k, Kbd, rp, rpd, mu, muBd] using hsum
  · intro τ hτ
    have hpi := (hasDerivAt_pi.mp (hderiv τ hτ))
      (selOfContract V (contractGateZ d))
    rw [aprioriField_gateZ_eq] at hpi
    simpa [k] using hpi

theorem gateU_coord_abs_bound
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hSelQP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1)
    (hSelQPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ)) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateU d))| ≤
        |yt 0 (selOfContract V (contractGateU d))| *
          Real.exp ((|(cμq : ℝ)|
            + (|yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T)
              * (L : ℝ)) * T) := by
  let k : ℝ → ℝ := fun t =>
    (cμq : ℝ) * MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)
      + yt t (selOfContract V (contractMu d))
        * MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)
  let Kbd : ℝ := |(cμq : ℝ)|
    + (|yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T) * (L : ℝ)
  have hlin := scalar_linear_homog_abs_bound (T := T)
    (g := fun t => yt t (selOfContract V (contractGateU d))) (k := k)
    (Kbd := Kbd) ?_ ?_
  · simpa [k, Kbd] using hlin
  · intro τ hτ
    let qp := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt τ) (selQP d V L)
    let qpd := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt τ) (selQPderiv d V L)
    let mu := yt τ (selOfContract V (contractMu d))
    let muBd := |yt 0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T
    have hT_nonneg : 0 ≤ T := le_trans hτ.1 (le_of_lt hτ.2)
    have hmuBd_nonneg : 0 ≤ muBd := by
      dsimp [muBd]
      exact add_nonneg (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) hT_nonneg)
    have hmu : |mu| ≤ muBd := by
      dsimp [mu, muBd]
      rw [mu_coord_affine (branch := branch) (chiResetP := chiResetP)
        (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
        (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
        (cμq := cμq) (cαq := cαq) (L := L) (R := R)
        (yt := yt) (T := T) hderiv τ hτ]
      have h1 := abs_add_le (yt 0 (selOfContract V (contractMu d))) ((cμq : ℝ) * τ)
      rw [abs_mul, abs_of_nonneg hτ.1] at h1
      have h2 : |(cμq : ℝ)| * τ ≤ |(cμq : ℝ)| * T :=
        mul_le_mul_of_nonneg_left (le_of_lt hτ.2) (abs_nonneg _)
      linarith
    have hQp : |qp| ≤ 1 := by simpa [qp] using hSelQP τ hτ
    have hQpd : |qpd| ≤ (L : ℝ) := by simpa [qpd] using hSelQPderiv τ hτ
    have hterm1 : |(cμq : ℝ) * qp| ≤ |(cμq : ℝ)| * 1 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hQp (abs_nonneg _)
    have hterm2 : |mu * qpd| ≤ muBd * (L : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hmu hQpd (abs_nonneg _) hmuBd_nonneg
    have hsum : |(cμq : ℝ) * qp + mu * qpd| ≤ |(cμq : ℝ)| + muBd * (L : ℝ) := by
      calc
        |(cμq : ℝ) * qp + mu * qpd| ≤ |(cμq : ℝ) * qp| + |mu * qpd| :=
          abs_add_le _ _
        _ ≤ |(cμq : ℝ)| * 1 + muBd * (L : ℝ) :=
          add_le_add hterm1 hterm2
        _ = |(cμq : ℝ)| + muBd * (L : ℝ) := by ring
    simpa [k, Kbd, qp, qpd, mu, muBd] using hsum
  · intro τ hτ
    have hpi := (hasDerivAt_pi.mp (hderiv τ hτ))
      (selOfContract V (contractGateU d))
    rw [aprioriField_gateU_eq] at hpi
    simpa [k] using hpi

theorem nonneg_of_linear_inhomogeneous_on_Ico
    (T : ℝ) (y a p : ℝ → ℝ)
    (hy_cont : Continuous y)
    (ha_cont : Continuous a)
    (hy0 : 0 ≤ y 0)
    (hp_nonneg : ∀ t ∈ Set.Ico (0 : ℝ) T, 0 ≤ p t)
    (hderiv :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt y (p t + a t * y t) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, 0 ≤ y t := by
  classical

  by_cases hT : 0 ≤ T
  ·
    let A : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, a u
    let E : ℝ → ℝ := fun s => Real.exp (-(A s))
    let H : ℝ → ℝ := fun s => -(y s * E s)
    let Hp : ℝ → ℝ :=
      fun s =>
        -(((p s + a s * y s) * E s) +
          y s * (E s * (-(a s))))

    have hA_deriv : ∀ s : ℝ, HasDerivAt A (a s) s := by
      intro s
      exact (ha_cont.integral_hasStrictDerivAt (0 : ℝ) s).hasDerivAt

    have hA_cont : Continuous A := by
      rw [continuous_iff_continuousAt]
      intro s
      exact (hA_deriv s).continuousAt

    have hE_cont : Continuous E := by
      dsimp [E]
      exact Real.continuous_exp.comp hA_cont.neg

    have hH_cont : Continuous H := by
      dsimp [H]
      exact (hy_cont.mul hE_cont).neg

    have hE_deriv :
        ∀ s : ℝ, HasDerivAt E (E s * (-(a s))) s := by
      intro s
      have hnegA : HasDerivAt (fun r : ℝ => -(A r)) (-(a s)) s :=
        (hA_deriv s).neg
      dsimp [E]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnegA.exp

    have hH_deriv :
        ∀ s ∈ Set.Ico (0 : ℝ) T,
          HasDerivWithinAt H (Hp s) (Set.Ici s) s := by
      intro s hs
      have hy' : HasDerivAt y (p s + a s * y s) s :=
        hderiv s hs
      have hE' : HasDerivAt E (E s * (-(a s))) s :=
        hE_deriv s
      have hmul :
          HasDerivAt
            (fun r : ℝ => y r * E r)
            ((p s + a s * y s) * E s +
              y s * (E s * (-(a s))))
            s :=
        hy'.mul hE'
      have hneg :
          HasDerivAt H (Hp s) s := by
        dsimp [H, Hp]
        simpa using hmul.neg
      exact hneg.hasDerivWithinAt

    have hH0 : H 0 ≤ (fun _ : ℝ => (0 : ℝ)) 0 := by
      have hA0 : A 0 = 0 := by
        simp [A]
      have hE0 : E 0 = 1 := by
        simp [E, hA0]
      dsimp [H]
      rw [hE0]
      linarith

    have hB_cont :
        ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc (0 : ℝ) T) := by
      exact continuous_const.continuousOn

    have hB_deriv :
        ∀ s ∈ Set.Ico (0 : ℝ) T,
          HasDerivWithinAt
            (fun _ : ℝ => (0 : ℝ))
            0
            (Set.Ici s)
            s := by
      intro s hs
      simpa using
        (hasDerivAt_const (x := s) (c := (0 : ℝ))).hasDerivWithinAt

    have hHp_nonpos :
        ∀ s ∈ Set.Ico (0 : ℝ) T, Hp s ≤ 0 := by
      intro s hs
      have hp_s : 0 ≤ p s := hp_nonneg s hs
      have hEpos : 0 < E s := by
        dsimp [E]
        exact Real.exp_pos _
      have hHp_eq : Hp s = -(E s * p s) := by
        dsimp [Hp]
        ring
      rw [hHp_eq]
      exact neg_nonpos.mpr (mul_nonneg (le_of_lt hEpos) hp_s)

    have hH_le_zero :
        ∀ s ∈ Set.Icc (0 : ℝ) T, H s ≤ 0 := by
      intro s hs
      exact
        image_le_of_deriv_right_le_deriv_boundary
          (f := H)
          (f' := Hp)
          (a := (0 : ℝ))
          (b := T)
          (B := fun _ : ℝ => (0 : ℝ))
          (B' := fun _ : ℝ => (0 : ℝ))
          hH_cont.continuousOn
          hH_deriv
          hH0
          hB_cont
          hB_deriv
          hHp_nonpos
          hs

    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
    have hHt : H t ≤ 0 := hH_le_zero t htIcc
    have hprod : 0 ≤ y t * E t := by
      dsimp [H] at hHt
      linarith
    have hEpos : 0 < E t := by
      dsimp [E]
      exact Real.exp_pos _
    exact (mul_nonneg_iff_of_pos_right hEpos).mp hprod

  ·
    intro t ht
    have hTpos : 0 < T := lt_of_le_of_lt ht.1 ht.2
    linarith


/-
The logistic lower-bound lemma.

The lower bound follows from the linear-in-lambda rewrite

  lam' = cr/2 + (-cr + cg*rho*(1-lam))*lam.

Only `cr ≥ 0` is needed for the inhomogeneous source term.
-/
theorem lambda_lower
    (T : ℝ) (lam cr cg rho : ℝ → ℝ)
    (hlam_cont : Continuous lam)
    (hcr_cont : Continuous cr)
    (hcg_cont : Continuous cg)
    (hrho_cont : Continuous rho)
    (hlam0 : 0 ≤ lam 0)
    (hcr : ∀ t ∈ Set.Ico (0 : ℝ) T, 0 ≤ cr t)
    (hup : ∀ t ∈ Set.Ico (0 : ℝ) T, lam t ≤ 1)
    (hderiv :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt lam
          (cr t * ((1 : ℝ) / 2 - lam t) +
            cg t * rho t * (lam t * (1 - lam t)))
          t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, 0 ≤ lam t := by
  classical

  let a : ℝ → ℝ :=
    fun t => -cr t + cg t * rho t * (1 - lam t)

  let p : ℝ → ℝ :=
    fun t => cr t / 2

  have ha_cont : Continuous a := by
    dsimp [a]
    fun_prop

  have hp_nonneg :
      ∀ t ∈ Set.Ico (0 : ℝ) T, 0 ≤ p t := by
    intro t ht
    dsimp [p]
    nlinarith [hcr t ht]

  have hlinear :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt lam (p t + a t * lam t) t := by
    intro t ht
    have h := hderiv t ht
    convert h using 1
    dsimp [a, p]
    ring

  exact
    nonneg_of_linear_inhomogeneous_on_Ico
      T lam a p
      hlam_cont
      ha_cont
      hlam0
      hp_nonneg
      hlinear

/-- Upper logistic bound: `lam ≤ 1` from `cr ≥ 0` ALONE (the readout sign is
NOT needed). Applies the integrating-factor lemma to `ν = 1 − lam`
(`ν' = cr/2 + a·ν`, `p = cr/2 ≥ 0`). -/
theorem lambda_upper
    (T : ℝ) (lam cr cg rho : ℝ → ℝ)
    (hlam_cont : Continuous lam) (hcr_cont : Continuous cr)
    (hcg_cont : Continuous cg) (hrho_cont : Continuous rho)
    (hlam1 : lam 0 ≤ 1)
    (hcr : ∀ t ∈ Set.Ico (0 : ℝ) T, 0 ≤ cr t)
    (hderiv :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt lam
          (cr t * ((1 : ℝ) / 2 - lam t) + cg t * rho t * (lam t * (1 - lam t))) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, lam t ≤ 1 := by
  classical
  have hnu := nonneg_of_linear_inhomogeneous_on_Ico
    T (fun t => 1 - lam t)
    (fun t => -cr t - cg t * rho t * lam t)
    (fun t => cr t / 2)
    (by fun_prop)
    ((hcr_cont.neg).sub ((hcg_cont.mul hrho_cont).mul hlam_cont))
    (by simpa using hlam1)
    (fun t ht => by dsimp; nlinarith [hcr t ht])
    (fun t ht => by
      have h := (hderiv t ht).const_sub (1 : ℝ)
      convert h using 1
      ring)
  intro t ht
  have h := hnu t ht
  linarith

/-- Local copy: field at the `λ_v` coordinate is the logistic reset/gate RHS. -/
theorem aprioriField_lam_eq (v : V) :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selLamCoord v) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) y chiResetP
          * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y kappaP * (1 / 2 - y (selLamCoord v))
        + MvPolynomial.eval₂ (algebraMap ℚ ℝ) y chiGateP
          * (MvPolynomial.eval₂ (algebraMap ℚ ℝ) y gainP
              * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (PpolyP v)
            * (y (selLamCoord v) * (1 - y (selLamCoord v)))) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R (selLamCoord v) =
        selectorResetGateFieldPoly chiResetP chiGateP kappaP gainP (PpolyP v)
          (selLamCoord v) from by
    simp only [selectorAssembledField, selLamCoord, Fin.append_right, Fin.append_left,
      Equiv.symm_apply_apply]]
  rw [eval₂_selectorResetGateFieldPoly]

theorem G_coord_abs_bound
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T Gbd : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hGbd : 0 ≤ Gbd)
    (hChiGain : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selGCoord d V)| ≤ |yt 0 (selGCoord d V)| + Gbd * T := by
  intro t ht
  let g : ℝ → ℝ := fun s => yt s (selGCoord d V)
  let g' : ℝ → ℝ := fun s =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) chiGateP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) gainP
  have hcont : ContinuousOn g (Icc (0 : ℝ) t) := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hpi := (hasDerivAt_pi.mp (hderiv s hsT)) (selGCoord d V)
    rw [aprioriField_G_eq] at hpi
    exact hpi.continuousAt.continuousWithinAt
  have hderivWithin : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt g (g' s) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hpi := (hasDerivAt_pi.mp (hderiv s hsT)) (selGCoord d V)
    rw [aprioriField_G_eq] at hpi
    exact hpi.hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖g' s‖ ≤ 0 * ‖g s‖ + Gbd := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    simpa [g', Real.norm_eq_abs] using hChiGain s hsT
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := g) (f' := g') (δ := |g 0|) (K := 0) (ε := Gbd)
    (a := (0 : ℝ)) (b := t) hcont hderivWithin
    (by simp [g, Real.norm_eq_abs]) hbound t ⟨ht.1, le_rfl⟩
  have ht_bound : |g t| ≤ |g 0| + Gbd * t := by
    simpa [g, Real.norm_eq_abs, gronwallBound_K0, sub_zero] using hgr
  have hGT : Gbd * t ≤ Gbd * T :=
    mul_le_mul_of_nonneg_left (le_of_lt ht.2) hGbd
  dsimp [g] at ht_bound ⊢
  linarith

theorem zu_coord_abs_bound (i : Fin d)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T Cbd Mbd : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hCbd : 0 ≤ Cbd) (hMbd : 0 ≤ Mbd)
    (hCoef : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd ∧
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd)
    (hMix : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selectorMixField branch i)| ≤ Mbd) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selZ V i)| ≤
        gronwallBound ‖(yt 0 (selZ V i), yt 0 (selU V i))‖
          (2 * Cbd) (Cbd * Mbd) T ∧
      |yt t (selU V i)| ≤
        gronwallBound ‖(yt 0 (selZ V i), yt 0 (selU V i))‖
          (2 * Cbd) (Cbd * Mbd) T := by
  intro t ht
  let f : ℝ → ℝ × ℝ := fun s => (yt s (selZ V i), yt s (selU V i))
  let f' : ℝ → ℝ × ℝ := fun s =>
    ((Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
        yt s (selOfContract V (contractGateZ d)) *
        (MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selectorMixField branch i)
          - yt s (selZ V i)),
      (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
        yt s (selOfContract V (contractGateU d)) *
        (yt s (selZ V i) - yt s (selU V i)))
  have hcont : ContinuousOn f (Icc (0 : ℝ) t) := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hz := (hasDerivAt_pi.mp (hderiv s hsT)) (selZ V i)
    have hu := (hasDerivAt_pi.mp (hderiv s hsT)) (selU V i)
    exact (hz.prodMk hu).continuousAt.continuousWithinAt
  have hderivWithin : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt f (f' s) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hz := (hasDerivAt_pi.mp (hderiv s hsT)) (selZ V i)
    have hu := (hasDerivAt_pi.mp (hderiv s hsT)) (selU V i)
    rw [aprioriField_z_eq] at hz
    rw [aprioriField_u_eq] at hu
    have hpair : HasDerivAt f (f' s) s := by simpa [f, f'] using (hz.prodMk hu)
    exact hpair.hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t,
      ‖f' s‖ ≤ (2 * Cbd) * ‖f s‖ + Cbd * Mbd := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    let z := yt s (selZ V i)
    let u := yt s (selU V i)
    let m := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selectorMixField branch i)
    let az := (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
      yt s (selOfContract V (contractGateZ d))
    let au := (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
      yt s (selOfContract V (contractGateU d))
    have haz : |az| ≤ Cbd := by simpa [az] using (hCoef s hsT).1
    have hau : |au| ≤ Cbd := by simpa [au] using (hCoef s hsT).2
    have hm : |m| ≤ Mbd := by simpa [m] using hMix s hsT
    have hzle : |z| ≤ ‖(z, u)‖ := by
      change |z| ≤ max ‖z‖ ‖u‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_left _ _
    have hule : |u| ≤ ‖(z, u)‖ := by
      change |u| ≤ max ‖z‖ ‖u‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_right _ _
    have hmz_abs : |m - z| ≤ |m| + |z| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le m (-z)
    have hzu_abs : |z - u| ≤ |z| + |u| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le z (-u)
    have hdz : |az * (m - z)| ≤ (2 * Cbd) * ‖(z, u)‖ + Cbd * Mbd := by
      calc
        |az * (m - z)| = |az| * |m - z| := abs_mul _ _
        _ ≤ Cbd * |m - z| :=
          mul_le_mul_of_nonneg_right haz (abs_nonneg _)
        _ ≤ Cbd * (|m| + |z|) :=
          mul_le_mul_of_nonneg_left hmz_abs hCbd
        _ ≤ Cbd * (Mbd + ‖(z, u)‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hm hzle) hCbd
        _ = Cbd * Mbd + Cbd * ‖(z, u)‖ := by ring
        _ ≤ (2 * Cbd) * ‖(z, u)‖ + Cbd * Mbd := by
          have hcn : 0 ≤ Cbd * ‖(z, u)‖ := mul_nonneg hCbd (norm_nonneg _)
          linarith
    have hdu : |au * (z - u)| ≤ (2 * Cbd) * ‖(z, u)‖ + Cbd * Mbd := by
      calc
        |au * (z - u)| = |au| * |z - u| := abs_mul _ _
        _ ≤ Cbd * |z - u| :=
          mul_le_mul_of_nonneg_right hau (abs_nonneg _)
        _ ≤ Cbd * (|z| + |u|) :=
          mul_le_mul_of_nonneg_left hzu_abs hCbd
        _ ≤ Cbd * (‖(z, u)‖ + ‖(z, u)‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hzle hule) hCbd
        _ ≤ (2 * Cbd) * ‖(z, u)‖ + Cbd * Mbd := by
          have hε : 0 ≤ Cbd * Mbd := mul_nonneg hCbd hMbd
          nlinarith
    simpa [f, f', z, u, m, az, au, Real.norm_eq_abs] using max_le hdz hdu
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (δ := ‖f 0‖) (K := 2 * Cbd)
    (ε := Cbd * Mbd) (a := (0 : ℝ)) (b := t)
    hcont hderivWithin (by simp [f]) hbound t ⟨ht.1, le_rfl⟩
  have hK : 0 ≤ 2 * Cbd := mul_nonneg (by norm_num) hCbd
  have hε : 0 ≤ Cbd * Mbd := mul_nonneg hCbd hMbd
  have hmono := gronwallBound_mono (δ := ‖f 0‖) (K := 2 * Cbd)
    (ε := Cbd * Mbd) (norm_nonneg _) hε hK
  have hpairT : ‖f t‖ ≤
      gronwallBound ‖f 0‖ (2 * Cbd) (Cbd * Mbd) T := by
    have hpairt : ‖f t‖ ≤ gronwallBound ‖f 0‖ (2 * Cbd) (Cbd * Mbd) t := by
      simpa [sub_zero] using hgr
    exact hpairt.trans (hmono (le_of_lt ht.2))
  have hz_abs : |yt t (selZ V i)| ≤ ‖f t‖ := by
    have := norm_fst_le (f t)
    simpa [f, Real.norm_eq_abs] using this
  have hu_abs : |yt t (selU V i)| ≤ ‖f t‖ := by
    have := norm_snd_le (f t)
    simpa [f, Real.norm_eq_abs] using this
  constructor
  · exact hz_abs.trans (by simpa [f] using hpairT)
  · exact hu_abs.trans (by simpa [f] using hpairT)

/-- The selector weight coordinate is nonnegative on `[0,T)` once the reset
factor has the expected sign. -/
theorem lam_coord_nonneg
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ} (v : V)
    (hcont : Continuous yt)
    (hlam0 : 0 ≤ yt 0 (selLamCoord v))
    (hCr_cont : Continuous
      (fun t : ℝ =>
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP))
    (hcg_cont : Continuous
      (fun t : ℝ =>
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP))
    (hrho_cont : Continuous
      (fun t : ℝ =>
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP v)))
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hup : ∀ t ∈ Ico (0 : ℝ) T, yt t (selLamCoord v) ≤ 1)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ yt t (selLamCoord v) := by
  let lam : ℝ → ℝ := fun t => yt t (selLamCoord v)
  let cr : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP
  let cg : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP
  let rho : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP v)
  have hlam_cont : Continuous lam := (continuous_apply (selLamCoord v)).comp hcont
  have hlow := lambda_lower T lam cr cg rho hlam_cont
    (by simpa [cr] using hCr_cont)
    (by simpa [cg] using hcg_cont)
    (by simpa [rho] using hrho_cont)
    (by simpa [lam] using hlam0)
    (by simpa [cr] using hCr)
    (by simpa [lam] using hup)
    ?_
  · simpa [lam] using hlow
  · intro t ht
    have hpi := (hasDerivAt_pi.mp (hderiv t ht)) (selLamCoord v)
    rw [aprioriField_lam_eq] at hpi
    convert hpi using 1 <;> simp [lam, cr, cg, rho] <;> ring

theorem eval₂_comp_continuous
    {yt : ℝ → Fin (selectorDim d V) → ℝ} (hyt : Continuous yt)
    (p : MvPolynomial (Fin (selectorDim d V)) ℚ) :
    Continuous (fun t => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) p) := by
  convert
    (MvPolynomial.continuous_eval
      (p := MvPolynomial.map (algebraMap ℚ ℝ) p)).comp hyt
    using 1
  ext t
  exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (yt t) p

private theorem selector_eval₂_continuous_along
    (yt : ℝ → Fin (selectorDim d V) → ℝ) (hytcont : Continuous yt)
    (p : MvPolynomial (Fin (selectorDim d V)) ℚ) :
    Continuous fun t => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) p := by
  exact eval₂_comp_continuous (yt := yt) hytcont p

theorem lam_coord_le_one
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ} (v : V)
    (hytcont : Continuous yt)
    (hlam0 : yt 0 (selLamCoord v) ≤ 1)
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, yt t (selLamCoord v) ≤ 1 := by
  let lam : ℝ → ℝ := fun t => yt t (selLamCoord v)
  let cr : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP
  let cg : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP
  let rho : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP v)
  apply lambda_upper T lam cr cg rho
    ((continuous_apply (selLamCoord v)).comp hytcont)
    ((eval₂_comp_continuous (yt := yt) hytcont chiResetP).mul
      (eval₂_comp_continuous (yt := yt) hytcont kappaP))
    ((eval₂_comp_continuous (yt := yt) hytcont chiGateP).mul
      (eval₂_comp_continuous (yt := yt) hytcont gainP))
    (eval₂_comp_continuous (yt := yt) hytcont (PpolyP v))
    (by simpa [lam] using hlam0)
    (fun t ht => by simpa [cr] using hCr t ht)
    (fun t ht => by
      have hpi := (hasDerivAt_pi.mp (hderiv t ht)) (selLamCoord v)
      rw [aprioriField_lam_eq] at hpi
      convert hpi using 1 <;> simp [lam, cr, cg, rho] <;> ring)

theorem lam_coord_abs_le_one
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ} (v : V)
    (hT : 0 < T) (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (hyt0 : yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hytcont : Continuous yt)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, |yt t (selLamCoord v)| ≤ 1 := by
  have hlam0 : yt 0 (selLamCoord v) = (1 / 2 : ℝ) := by
    rw [hyt0]
    simp [selectorEuclInitQ, selLamCoord]
  have hup := lam_coord_le_one (branch := branch) (chiResetP := chiResetP)
    (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
    (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
    (cμq := cμq) (cαq := cαq) (L := L) (R := R)
    (yt := yt) (T := T) v hytcont (by rw [hlam0]; norm_num)
    hCr hderiv
  have hlow := lam_coord_nonneg (branch := branch) (chiResetP := chiResetP)
    (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
    (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
    (cμq := cμq) (cαq := cαq) (L := L) (R := R)
    (yt := yt) (T := T) v hytcont (by rw [hlam0]; norm_num)
    ((selector_eval₂_continuous_along yt hytcont chiResetP).mul
      (selector_eval₂_continuous_along yt hytcont kappaP))
    ((selector_eval₂_continuous_along yt hytcont chiGateP).mul
      (selector_eval₂_continuous_along yt hytcont gainP))
    (selector_eval₂_continuous_along yt hytcont (PpolyP v))
    hCr hup hderiv
  intro t ht
  exact abs_le.mpr ⟨by linarith [hlow t ht], hup t ht⟩

private def selectorAprioriBnd
    {d : ℕ} {V : Type} [Fintype V]
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (cμq cαq : ℚ) (L : ℕ) (Cbd Mbd Gbd Abd : ℝ → ℝ) : ℝ → ℝ := by
  classical
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  exact fun τ =>
    let scBd : ℝ :=
      Real.sqrt (y0 (selOfContract V (contractS d)) ^ 2 +
        y0 (selOfContract V (contractC d)) ^ 2)
    let muBd : ℝ :=
      |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * τ
    let alphaBd : ℝ :=
      |y0 (selOfContract V (contractAlpha d))| * Real.exp (|(cαq : ℝ)| * τ)
    let gateZBd : ℝ :=
      |y0 (selOfContract V (contractGateZ d))| *
        Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * τ)
    let gateUBd : ℝ :=
      |y0 (selOfContract V (contractGateU d))| *
        Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * τ)
    let zuBd : ℝ :=
      ∑ i : Fin d,
        gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
          (2 * Cbd τ) (Cbd τ * Mbd τ) τ
    let GBd : ℝ := |y0 (selGCoord d V)| + Gbd τ * τ
    let warmBd : ℝ := |(warmGainInit : ℝ)|
    max 1 (max scBd (max muBd (max alphaBd
      (max gateZBd (max gateUBd (max zuBd (max GBd (max warmBd (Abd τ)))))))))

set_option maxHeartbeats 2000000

/-- Specific version of the coordinatewise selector a-priori bound, using the
explicit shared max-fold bound `selectorAprioriBnd`. -/
theorem selector_coordwise_bound_specific
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    {T : ℝ} (Cbd Mbd Gbd Abd : ℝ → ℝ) (hT : 0 < T)
    (hCbdmono : Monotone Cbd) (hMbdmono : Monotone Mbd)
    (hGbdmono : Monotone Gbd) (hAbdmono : Monotone Abd)
    (hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ) (hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ) (hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ)
    (hyt0 : yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hSelRP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1)
    (hSelRPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ))
    (hSelQP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1)
    (hSelQPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ))
    (hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd T)
    (hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd T)
    (hMix : ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selectorMixField branch i)| ≤ Mbd T)
    (hChiGain : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T)
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hytcont : Continuous yt)
    (hA : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractA d))| ≤ Abd T) :
    let Bnd := selectorAprioriBnd (V := V) x₀ w warmGainInit cμq cαq L Cbd Mbd Gbd Abd
    (∀ T' : ℝ, 0 < T' → 0 < Bnd T') ∧
    (∀ ⦃S T' : ℝ⦄, 0 < S → S ≤ T' → Bnd S ≤ Bnd T') ∧
    ∀ t ∈ Ico (0 : ℝ) T, ∀ i, |yt t i| ≤ Bnd T := by
  classical
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  let scBd : ℝ :=
    Real.sqrt (y0 (selOfContract V (contractS d)) ^ 2 +
      y0 (selOfContract V (contractC d)) ^ 2)
  let muBd : ℝ → ℝ := fun τ =>
    |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * τ
  let alphaBd : ℝ → ℝ := fun τ =>
    |y0 (selOfContract V (contractAlpha d))| * Real.exp (|(cαq : ℝ)| * τ)
  let gateZBd : ℝ → ℝ := fun τ =>
    |y0 (selOfContract V (contractGateZ d))| *
      Real.exp ((|(cμq : ℝ)| + muBd τ * (L : ℝ)) * τ)
  let gateUBd : ℝ → ℝ := fun τ =>
    |y0 (selOfContract V (contractGateU d))| *
      Real.exp ((|(cμq : ℝ)| + muBd τ * (L : ℝ)) * τ)
  let zuBd : ℝ → ℝ := fun τ =>
    (∑ i : Fin d,
      gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
        (2 * Cbd τ) (Cbd τ * Mbd τ) τ)
  let GBd : ℝ → ℝ := fun τ => |y0 (selGCoord d V)| + Gbd τ * τ
  let warmBd : ℝ := |(warmGainInit : ℝ)|
  let Bnd : ℝ → ℝ := fun τ =>
    max 1 (max scBd (max (muBd τ) (max (alphaBd τ)
      (max (gateZBd τ) (max (gateUBd τ)
        (max (zuBd τ) (max (GBd τ) (max warmBd (Abd τ)))))))))
  change (∀ T' : ℝ, 0 < T' → 0 < Bnd T') ∧
    (∀ ⦃S T' : ℝ⦄, 0 < S → S ≤ T' → Bnd S ≤ Bnd T') ∧
    ∀ t ∈ Ico (0 : ℝ) T, ∀ i, |yt t i| ≤ Bnd T
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    exact lt_of_lt_of_le zero_lt_one (by dsimp [Bnd]; aesop)
  · intro S T' hS hST
    have hSnn : 0 ≤ S := le_of_lt hS
    have hTnn : 0 ≤ T' := le_trans hSnn hST
    have hmu : muBd S ≤ muBd T' := by dsimp [muBd]; gcongr
    have halpha : alphaBd S ≤ alphaBd T' := by
      dsimp [alphaBd]
      gcongr
    have hgateZ : gateZBd S ≤ gateZBd T' := by
      dsimp [gateZBd]
      gcongr
    have hgateU : gateUBd S ≤ gateUBd T' := by
      dsimp [gateUBd]
      gcongr
    have hzu : zuBd S ≤ zuBd T' := by
      dsimp [zuBd]
      refine Finset.sum_le_sum ?_
      intro i hi
      let δi : ℝ := ‖(y0 (selZ V i), y0 (selU V i))‖
      have hδ : 0 ≤ δi := norm_nonneg _
      have hKS : 0 ≤ 2 * Cbd S := mul_nonneg (by norm_num) (hCbd0 S)
      have hεS : 0 ≤ Cbd S * Mbd S := mul_nonneg (hCbd0 S) (hMbd0 S)
      have htime :
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) S ≤
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) T' :=
        gronwallBound_mono (δ := δi) (K := 2 * Cbd S)
          (ε := Cbd S * Mbd S) hδ hεS hKS hST
      have hKST : 2 * Cbd S ≤ 2 * Cbd T' :=
        mul_le_mul_of_nonneg_left (hCbdmono hST) (by norm_num)
      have hKstep :
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) T' ≤
          gronwallBound δi (2 * Cbd T') (Cbd S * Mbd S) T' :=
        gronwallBound_mono_K (δ := δi) (ε := Cbd S * Mbd S)
          (x := T') hδ hεS hTnn hKST
      have hεST : Cbd S * Mbd S ≤ Cbd T' * Mbd T' :=
        mul_le_mul (hCbdmono hST) (hMbdmono hST) (hMbd0 S) (hCbd0 T')
      have hεstep :
          gronwallBound δi (2 * Cbd T') (Cbd S * Mbd S) T' ≤
          gronwallBound δi (2 * Cbd T') (Cbd T' * Mbd T') T' :=
        gronwallBound_mono_epsilon (δ := δi) (K := 2 * Cbd T')
          (x := T') hTnn hεST
      exact htime.trans (hKstep.trans hεstep)
    have hG : GBd S ≤ GBd T' := by
      dsimp [GBd]
      have hprod : Gbd S * S ≤ Gbd T' * T' :=
        mul_le_mul (hGbdmono hST) hST hSnn (hGbd0 T')
      linarith
    have hAbd : Abd S ≤ Abd T' := hAbdmono hST
    dsimp [Bnd]
    gcongr
  · intro t ht i
    have hyt0' : yt 0 = y0 := by simpa [y0] using hyt0
    have htoB {x : ℝ} (hx : x ≤ Bnd T) : x ≤ Bnd T := hx
    have hone_to_B : (1 : ℝ) ≤ Bnd T := by
      dsimp [Bnd]
      exact le_max_left _ _
    have hsc_to_B : scBd ≤ Bnd T := by
      dsimp [Bnd]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hmu_to_B : muBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        muBd T ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))) :=
          le_max_left _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))))) :=
          le_max_right _ _
    have halpha_to_B : alphaBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        alphaBd T ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))) :=
          le_max_left _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))))) :=
          le_max_right _ _
    have hgateZ_to_B : gateZBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        gateZBd T ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))) :=
          le_max_left _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))))) :=
          le_max_right _ _
    have hgateU_to_B : gateUBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        gateUBd T ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))) :=
          le_max_left _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))))) :=
          le_max_right _ _
    have hzu_to_B : zuBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        zuBd T ≤ max (zuBd T) (max (GBd T) (max warmBd (Abd T))) := le_max_left _ _
        _ ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))) :=
          le_max_right _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))))) :=
          le_max_right _ _
    have hG_to_B : GBd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        GBd T ≤ max (GBd T) (max warmBd (Abd T)) := le_max_left _ _
        _ ≤ max (zuBd T) (max (GBd T) (max warmBd (Abd T))) := le_max_right _ _
        _ ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))) :=
          le_max_right _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))))) :=
          le_max_right _ _
    have hA_to_B : Abd T ≤ Bnd T := by
      dsimp [Bnd]
      calc
        Abd T ≤ max warmBd (Abd T) := le_max_right _ _
        _ ≤ max (GBd T) (max warmBd (Abd T)) := le_max_right _ _
        _ ≤ max (zuBd T) (max (GBd T) (max warmBd (Abd T))) := le_max_right _ _
        _ ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))) :=
          le_max_right _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))))) :=
          le_max_right _ _
    have hwarmBd_to_B : warmBd ≤ Bnd T := by
      dsimp [Bnd]
      calc
        warmBd ≤ max warmBd (Abd T) := le_max_left _ _
        _ ≤ max (GBd T) (max warmBd (Abd T)) := le_max_right _ _
        _ ≤ max (zuBd T) (max (GBd T) (max warmBd (Abd T))) := le_max_right _ _
        _ ≤ max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))) :=
          le_max_right _ _
        _ ≤ max (gateZBd T)
            (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))) :=
          le_max_right _ _
        _ ≤ max (alphaBd T)
            (max (gateZBd T)
              (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))) :=
          le_max_right _ _
        _ ≤ max (muBd T)
            (max (alphaBd T)
              (max (gateZBd T)
                (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))) :=
          le_max_right _ _
        _ ≤ max scBd
            (max (muBd T)
              (max (alphaBd T)
                (max (gateZBd T)
                  (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T)))))))) :=
          le_max_right _ _
        _ ≤ max 1
            (max scBd
              (max (muBd T)
                (max (alphaBd T)
                  (max (gateZBd T)
                    (max (gateUBd T) (max (zuBd T) (max (GBd T) (max warmBd (Abd T))))))))) :=
          le_max_right _ _
    refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ i
    · intro j
      refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ j
      · intro a
        fin_cases a
        · have hsc := sc_conservation (branch := branch) (chiResetP := chiResetP)
            (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
            (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
            (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht
          have hs : |yt t (selOfContract V (contractS d))| ≤ scBd := by
            have hsq : (yt t (selOfContract V (contractS d))) ^ 2 ≤ scBd ^ 2 := by
              have hnn : 0 ≤ y0 (selOfContract V (contractS d)) ^ 2 +
                  y0 (selOfContract V (contractC d)) ^ 2 := by positivity
              dsimp [scBd]
              rw [Real.sq_sqrt hnn]
              rw [hyt0'] at hsc
              nlinarith [sq_nonneg (yt t (selOfContract V (contractC d)))]
            exact abs_le_of_sq_le_sq hsq (by positivity)
          exact hs.trans hsc_to_B
        · have hsc := sc_conservation (branch := branch) (chiResetP := chiResetP)
            (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
            (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
            (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht
          have hc : |yt t (selOfContract V (contractC d))| ≤ scBd := by
            have hsq : (yt t (selOfContract V (contractC d))) ^ 2 ≤ scBd ^ 2 := by
              have hnn : 0 ≤ y0 (selOfContract V (contractS d)) ^ 2 +
                  y0 (selOfContract V (contractC d)) ^ 2 := by positivity
              dsimp [scBd]
              rw [Real.sq_sqrt hnn]
              rw [hyt0'] at hsc
              nlinarith [sq_nonneg (yt t (selOfContract V (contractS d)))]
            exact abs_le_of_sq_le_sq hsq (by positivity)
          exact hc.trans hsc_to_B
        · change |yt t (selOfContract V (contractMu d))| ≤ Bnd T
          rw [mu_coord_affine (branch := branch) (chiResetP := chiResetP)
            (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
            (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
            (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht]
          rw [hyt0']
          have hle : |y0 (selOfContract V (contractMu d)) + (cμq : ℝ) * t| ≤
              muBd T := by
            have h1 := abs_add_le (y0 (selOfContract V (contractMu d))) ((cμq : ℝ) * t)
            rw [abs_mul, abs_of_nonneg ht.1] at h1
            have h2 : |(cμq : ℝ)| * t ≤ |(cμq : ℝ)| * T :=
              mul_le_mul_of_nonneg_left (le_of_lt ht.2) (abs_nonneg _)
            dsimp [muBd]
            linarith
          exact hle.trans hmu_to_B
        · change |yt t (selOfContract V (contractAlpha d))| ≤ Bnd T
          rw [alpha_coord_eq (branch := branch) (chiResetP := chiResetP)
            (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
            (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
            (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht]
          rw [hyt0']
          have hle : |y0 (selOfContract V (contractAlpha d)) *
              Real.exp ((cαq : ℝ) * t)| ≤ alphaBd T := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
            dsimp [alphaBd]
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr
              ((mul_le_mul_of_nonneg_right (le_abs_self _) ht.1).trans
                (mul_le_mul_of_nonneg_left (le_of_lt ht.2) (abs_nonneg _))))
              (abs_nonneg _)
          exact hle.trans halpha_to_B
      · intro b
        refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ b
        · intro g
          fin_cases g
          · have hb := gateZ_coord_abs_bound (branch := branch)
              (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
              (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
              (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
              (yt := yt) (T := T) hderiv hSelRP hSelRPderiv t ht
            rw [hyt0'] at hb
            exact hb.trans hgateZ_to_B
          · have hb := gateU_coord_abs_bound (branch := branch)
              (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
              (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
              (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
              (yt := yt) (T := T) hderiv hSelQP hSelQPderiv t ht
            rw [hyt0'] at hb
            exact hb.trans hgateU_to_B
        · intro r
          refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ r
          · intro z
            have hz := (zu_coord_abs_bound (branch := branch)
              (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
              (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
              (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
              z (yt := yt) (T := T) (Cbd := Cbd T) (Mbd := Mbd T) hderiv
              (hCbd0 T) (hMbd0 T) (fun s hs => ⟨hCoefZ s hs, hCoefU s hs⟩)
              (hMix z) t ht).1
            rw [hyt0'] at hz
            have hsum : gronwallBound ‖(y0 (selZ V z), y0 (selU V z))‖
                (2 * Cbd T) (Cbd T * Mbd T) T ≤ zuBd T := by
              dsimp [zuBd]
              refine Finset.single_le_sum
                (f := fun i : Fin d =>
                  gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
                    (2 * Cbd T) (Cbd T * Mbd T) T)
                ?_ (Finset.mem_univ z)
              intro i hi
              have hK : 0 ≤ 2 * Cbd T := mul_nonneg (by norm_num) (hCbd0 T)
              have hε : 0 ≤ Cbd T * Mbd T := mul_nonneg (hCbd0 T) (hMbd0 T)
              have hδ : 0 ≤ ‖(y0 (selZ V i), y0 (selU V i))‖ := norm_nonneg _
              have h0T := (gronwallBound_mono
                (δ := ‖(y0 (selZ V i), y0 (selU V i))‖)
                (K := 2 * Cbd T) (ε := Cbd T * Mbd T) hδ hε hK
                (le_of_lt hT))
              rw [gronwallBound_x0] at h0T
              exact hδ.trans h0T
            exact hz.trans (hsum.trans hzu_to_B)
          · intro s
            refine Fin.addCases (m := d) (n := 1) ?_ ?_ s
            · intro u
              have hu := (zu_coord_abs_bound (branch := branch)
                (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
                (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
                (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
                u (yt := yt) (T := T) (Cbd := Cbd T) (Mbd := Mbd T) hderiv
                (hCbd0 T) (hMbd0 T) (fun s hs => ⟨hCoefZ s hs, hCoefU s hs⟩)
                (hMix u) t ht).2
              rw [hyt0'] at hu
              have hsum : gronwallBound ‖(y0 (selZ V u), y0 (selU V u))‖
                  (2 * Cbd T) (Cbd T * Mbd T) T ≤ zuBd T := by
                dsimp [zuBd]
                refine Finset.single_le_sum
                  (f := fun i : Fin d =>
                    gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
                      (2 * Cbd T) (Cbd T * Mbd T) T)
                  ?_ (Finset.mem_univ u)
                intro i hi
                have hK : 0 ≤ 2 * Cbd T := mul_nonneg (by norm_num) (hCbd0 T)
                have hε : 0 ≤ Cbd T * Mbd T := mul_nonneg (hCbd0 T) (hMbd0 T)
                have hδ : 0 ≤ ‖(y0 (selZ V i), y0 (selU V i))‖ := norm_nonneg _
                have h0T := (gronwallBound_mono
                  (δ := ‖(y0 (selZ V i), y0 (selU V i))‖)
                  (K := 2 * Cbd T) (ε := Cbd T * Mbd T) hδ hε hK
                  (le_of_lt hT))
                rw [gronwallBound_x0] at h0T
                exact hδ.trans h0T
              exact hu.trans (hsum.trans hzu_to_B)
            · intro a1
              fin_cases a1
              exact (hA t ht).trans hA_to_B
    · intro k
      refine Fin.addCases (m := Fintype.card V) (n := 2) ?_ ?_ k
      · intro v
        have hlam := lam_coord_abs_le_one (branch := branch)
          (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
          (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
          (cμq := cμq) (cαq := cαq) (L := L) (R := R)
          (yt := yt) (T := T) ((Fintype.equivFin V).symm v)
          hT x₀ w warmGainInit hyt0 hCr hytcont hderiv t ht
        simpa [selLamCoord] using hlam.trans hone_to_B
      · intro g
        fin_cases g
        · have hG := G_coord_abs_bound (branch := branch) (chiResetP := chiResetP)
            (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
            (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
            (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) (Gbd := Gbd T) hderiv (hGbd0 T) hChiGain t ht
          rw [hyt0'] at hG
          exact hG.trans hG_to_B
        · change |yt t (selWarmGainCoord d V)| ≤ Bnd T
          have hconst := warmGain_coord_const (branch := branch)
            (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
            (gainP := gainP) (PpolyP := PpolyP) (HP := HP)
            (Aq := Aq) (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
            (yt := yt) (T := T) hderiv t ht
          rw [hconst, hyt0']
          have hy0wg : y0 (selWarmGainCoord d V) = (warmGainInit : ℝ) := by
            simp [y0, selectorEuclInitQ, selWarmGainCoord, Fin.append_right]
            rfl
          rw [hy0wg]
          exact hwarmBd_to_B

/-- Genuine coordinatewise selector a-priori bound, proved by decomposing the
selector coordinate layout and dispatching each leaf to the corresponding
per-coordinate scalar bound. -/
theorem selector_coordwise_bound
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    {T : ℝ} (Cbd Mbd Gbd Abd : ℝ → ℝ) (hT : 0 < T)
    (hCbdmono : Monotone Cbd) (hMbdmono : Monotone Mbd)
    (hGbdmono : Monotone Gbd) (hAbdmono : Monotone Abd)
    (hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ) (hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ) (hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ)
    (hyt0 : yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hSelRP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1)
    (hSelRPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ))
    (hSelQP : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1)
    (hSelQPderiv : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ))
    (hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd T)
    (hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd T)
    (hMix : ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selectorMixField branch i)| ≤ Mbd T)
    (hChiGain : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T)
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hytcont : Continuous yt)
    (hA : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractA d))| ≤ Abd T) :
    ∃ Bnd : ℝ → ℝ,
      (∀ T' : ℝ, 0 < T' → 0 < Bnd T') ∧
      (∀ ⦃S T' : ℝ⦄, 0 < S → S ≤ T' → Bnd S ≤ Bnd T') ∧
      ∀ t ∈ Ico (0 : ℝ) T, ∀ i, |yt t i| ≤ Bnd T := by
  refine ⟨selectorAprioriBnd (V := V) x₀ w warmGainInit cμq cαq L Cbd Mbd Gbd Abd, ?_⟩
  simpa using
    selector_coordwise_bound_specific branch chiResetP chiGateP kappaP gainP
      PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit Cbd Mbd Gbd Abd hT
      hCbdmono hMbdmono hGbdmono hAbdmono hCbd0 hMbd0 hGbd0 hAbd0
      yt hyt0 hderiv hSelRP hSelRPderiv hSelQP hSelQPderiv hCoefZ hCoefU
      hMix hChiGain hCr hytcont hA

/-- A prefix-uniform finite-horizon selector bound from the structural
per-coordinate hypotheses, packaged into Ripple's `FiniteHorizonBound`. -/
theorem selector_finiteHorizonBound
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (Cbd Mbd Gbd Abd : ℝ → ℝ)
    (hCbdmono : Monotone Cbd) (hMbdmono : Monotone Mbd)
    (hGbdmono : Monotone Gbd) (hAbdmono : Monotone Abd)
    (hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ) (hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ) (hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ)
    (hstruct : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ)) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ)) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
            yt t (selOfContract V (contractGateZ d))| ≤ Cbd T) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
            yt t (selOfContract V (contractGateU d))| ≤ Cbd T) ∧
        (∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selectorMixField branch i)| ≤ Mbd T) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP) ∧
        Continuous yt ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |yt t (selOfContract V (contractA d))| ≤ Abd T)) :
    Ripple.FiniteHorizonBound
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
      (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) := by
  let Bnd : ℝ → ℝ :=
    selectorAprioriBnd (V := V) x₀ w warmGainInit cμq cαq L Cbd Mbd Gbd Abd
  have hBpos : ∀ T : ℝ, 0 < T → 0 < Bnd T := by
    intro T hT
    dsimp [Bnd, selectorAprioriBnd]
    exact lt_of_lt_of_le zero_lt_one (by aesop)
  have hBmono : ∀ ⦃S T : ℝ⦄, 0 < S → S ≤ T → Bnd S ≤ Bnd T := by
    intro S T hS hST
    have hSnn : 0 ≤ S := le_of_lt hS
    have hTnn : 0 ≤ T := le_trans hSnn hST
    have hGprod : Gbd S * S ≤ Gbd T * T :=
      mul_le_mul (hGbdmono hST) hST hSnn (hGbd0 T)
    have hAbdST : Abd S ≤ Abd T := hAbdmono hST
    dsimp [Bnd, selectorAprioriBnd]
    gcongr
    · rename_i i hi
      let δi : ℝ :=
        max ‖((selectorEuclInitQ d V x₀ w warmGainInit (selZ V i) : ℚ) : ℝ)‖
          ‖((selectorEuclInitQ d V x₀ w warmGainInit (selU V i) : ℚ) : ℝ)‖
      have hδ : 0 ≤ δi := by
        dsimp [δi]
        exact le_trans (norm_nonneg _) (le_max_left _ _)
      have hKS : 0 ≤ 2 * Cbd S := mul_nonneg (by norm_num) (hCbd0 S)
      have hεS : 0 ≤ Cbd S * Mbd S := mul_nonneg (hCbd0 S) (hMbd0 S)
      have htime :
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) S ≤
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) T :=
        gronwallBound_mono (δ := δi) (K := 2 * Cbd S)
          (ε := Cbd S * Mbd S) hδ hεS hKS hST
      have hKST : 2 * Cbd S ≤ 2 * Cbd T :=
        mul_le_mul_of_nonneg_left (hCbdmono hST) (by norm_num)
      have hKstep :
          gronwallBound δi (2 * Cbd S) (Cbd S * Mbd S) T ≤
          gronwallBound δi (2 * Cbd T) (Cbd S * Mbd S) T :=
        gronwallBound_mono_K (δ := δi) (ε := Cbd S * Mbd S)
          (x := T) hδ hεS hTnn hKST
      have hεST : Cbd S * Mbd S ≤ Cbd T * Mbd T :=
        mul_le_mul (hCbdmono hST) (hMbdmono hST) (hMbd0 S) (hCbd0 T)
      have hεstep :
          gronwallBound δi (2 * Cbd T) (Cbd S * Mbd S) T ≤
          gronwallBound δi (2 * Cbd T) (Cbd T * Mbd T) T :=
        gronwallBound_mono_epsilon (δ := δi) (K := 2 * Cbd T)
          (x := T) hTnn hεST
      exact htime.trans (hKstep.trans hεstep)
  refine Ripple.finiteHorizonBound_of_monotone_bound
    (f := selectorAssembledVectorField d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    (y₀ := fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ))
    Bnd hBpos ?_ ?_
  · intro S T hS hST
    exact hBmono hS hST
  · intro T hT yt hyt0 hderiv t ht
    obtain ⟨hSelRP, hSelRPderiv, hSelQP, hSelQPderiv,
      hCoefZ, hCoefU, hMix, hChiGain, hCr, hytcont, hA⟩ :=
      hstruct T hT yt hyt0 hderiv
    have hspec := selector_coordwise_bound_specific
      (branch := branch) (chiResetP := chiResetP) (chiGateP := chiGateP)
      (kappaP := kappaP) (gainP := gainP) (PpolyP := PpolyP) (HP := HP)
      (Aq := Aq) (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (x₀ := x₀) (w := w) (warmGainInit := warmGainInit) (T := T) (Cbd := Cbd) (Mbd := Mbd)
      (Gbd := Gbd) (Abd := Abd) hT hCbdmono hMbdmono hGbdmono hAbdmono
      hCbd0 hMbd0 hGbd0 hAbd0 yt hyt0 hderiv hSelRP hSelRPderiv
      hSelQP hSelQPderiv hCoefZ hCoefU hMix hChiGain hCr hytcont hA
    have hcoordT :
        ∀ t ∈ Ico (0 : ℝ) T, ∀ i, |yt t i| ≤ Bnd T := by
      simpa [Bnd] using hspec.2.2
    have _hexists :=
      selector_coordwise_bound branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R x₀ w warmGainInit Cbd Mbd Gbd Abd hT hCbdmono hMbdmono
        hGbdmono hAbdmono hCbd0 hMbd0 hGbd0 hAbd0 yt hyt0 hderiv hSelRP
        hSelRPderiv hSelQP hSelQPderiv hCoefZ hCoefU hMix hChiGain hCr
        hytcont hA
    rw [pi_norm_le_iff_of_nonneg (le_of_lt (hBpos T hT))]
    intro i
    simpa [Real.norm_eq_abs] using hcoordT t ht i

/-- Selector solution existence with the finite-horizon hypothesis discharged by
the Stage-B coordinatewise a-priori bound package. -/
theorem selector_sol_exists_unconditional
    {d B : ℕ} {V : Type} [Fintype V]
    (p : DynGateParams) (sched : PhaseSchedule)
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ)) (hcμ : p.cμ = (cμq : ℝ))
    (hcα : p.cα = (cαq : ℝ)) (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (chiResetF chiGateF kappaF gainF : ℝ → ℝ)
    (readoutP : V → (Fin d → ℝ) → ℝ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (Cbd Mbd Gbd Abd : ℝ → ℝ)
    (hCbdmono : Monotone Cbd) (hMbdmono : Monotone Mbd)
    (hGbdmono : Monotone Gbd) (hAbdmono : Monotone Abd)
    (hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ) (hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ) (hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ)
    (hstruct : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ)) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ)) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
            yt t (selOfContract V (contractGateZ d))| ≤ Cbd T) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
            yt t (selOfContract V (contractGateU d))| ≤ Cbd T) ∧
        (∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selectorMixField branch i)| ≤ Mbd T) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP) ∧
        Continuous yt ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          |yt t (selOfContract V (contractA d))| ≤ Abd T))
    (hgateZ :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
              (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract V (contractGateZ d)) =
            bGateZ L (y t (selOfContract V (contractMu d))) t)
    (hgateU :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
              (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract V (contractGateU d)) =
            bGateU L (y t (selOfContract V (contractMu d))) t)
    (h_chiReset :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
              (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiResetP = chiResetF t)
    (h_chiGate :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
              (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiGateP = chiGateF t)
    (h_kappa :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
              (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) kappaP = kappaF t)
    (h_gain :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
              (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) gainP = gainF t)
    (h_P :
      ∀ y : ℝ → Fin (selectorDim d V) → ℝ,
        y 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (selectorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
              (y t)) t) →
        ∀ (v : V) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (PpolyP v) =
            readoutP v (fun i => y t (selU V i))) :
    ∃ sol : SelectorDynSol d B V p sched branch
        chiResetF chiGateF kappaF gainF readoutP,
      sol.z 0 = sol.init_z ∧ sol.u 0 = sol.init_u ∧
        (∀ i, sol.u 0 i = ((selectorEuclInitQ d V x₀ w warmGainInit (selU V i) : ℚ) : ℝ)) ∧
        sol.ZUFiniteCoordBound := by
  refine selector_sol_exists p sched branch chiResetP chiGateP kappaP gainP
    PpolyP HP hA hcμ hcα hL hdomain_nonneg
    chiResetF chiGateF kappaF gainF readoutP x₀ w warmGainInit ?_
    hgateZ hgateU h_chiReset h_chiGate h_kappa h_gain h_P
  exact selector_finiteHorizonBound branch chiResetP chiGateP kappaP gainP
    PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit Cbd Mbd Gbd Abd
    hCbdmono hMbdmono hGbdmono hAbdmono hCbd0 hMbd0 hGbd0 hAbd0 hstruct

/-
Discharge layer for the satisfiable structural package in
`selector_finiteHorizonBound`.

The clock pulse facts are proved here from `sc_conservation` and the selector
Euclidean initial vector.  The `Cbd` coefficient clauses are proved from
`alpha_coord_eq` plus the in-file gate bounds `gateZ_coord_abs_bound` and
`gateU_coord_abs_bound`.  The remaining carried assumptions are the honest
realization/contract-status layer:
* `hMixBound`: the affine-in-`u` branch-mixture bound, obtainable from
  `BranchData.coord_lipschitz` and the selector-weight simplex invariant;
* `hChiGain`, `hA`, `hCr`, `hytcont`: realization and sign facts.
-/

private theorem selector_sc_abs_le_one
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    {T : ℝ} (yt : ℝ → Fin (selectorDim d V) → ℝ)
    (hyt0 : yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractS d))| ≤ 1 ∧
      |yt t (selOfContract V (contractC d))| ≤ 1 := by
  intro t ht
  have hsc := sc_conservation (branch := branch) (chiResetP := chiResetP)
    (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
    (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
    (cμq := cμq) (cαq := cαq) (L := L) (R := R)
    (yt := yt) (T := T) hderiv t ht
  rw [hyt0] at hsc
  have hsc1 :
      (yt t (selOfContract V (contractS d))) ^ 2
        + (yt t (selOfContract V (contractC d))) ^ 2 = 1 := by
    rw [hsc]
    norm_num [selectorEuclInitQ, selOfContract, contractS, contractC, Fin.isValue]
  have hs_sq :
      (yt t (selOfContract V (contractS d))) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (yt t (selOfContract V (contractC d))), hsc1]
  have hc_sq :
      (yt t (selOfContract V (contractC d))) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (yt t (selOfContract V (contractS d))), hsc1]
  exact ⟨abs_le_of_sq_le_sq (b := (1:ℝ)) (by nlinarith [hs_sq]) (by norm_num),
    abs_le_of_sq_le_sq (b := (1:ℝ)) (by nlinarith [hc_sq]) (by norm_num)⟩

private theorem selector_pulse_bounds
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    {T : ℝ} (yt : ℝ → Fin (selectorDim d V) → ℝ)
    (hyt0 : yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    (∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRP d V L)| ≤ 1) ∧
    (∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRPderiv d V L)| ≤ (L : ℝ)) ∧
    (∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQP d V L)| ≤ 1) ∧
    (∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selQPderiv d V L)| ≤ (L : ℝ)) := by
  classical
  have hsc := selector_sc_abs_le_one branch chiResetP chiGateP kappaP gainP
    PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit yt hyt0 hderiv
  have hpulse :
      ∀ (σ : ℝ), |σ| ≤ 1 →
        |((1 / 2 : ℝ) * (1 - σ)) ^ L| ≤ 1 ∧
        |((1 / 2 : ℝ) * (1 + σ)) ^ L| ≤ 1 := by
    intro σ hσ
    have hσlo : -1 ≤ σ := (abs_le.mp hσ).1
    have hσhi : σ ≤ 1 := (abs_le.mp hσ).2
    have hr0 : 0 ≤ (1 / 2 : ℝ) * (1 - σ) := by nlinarith
    have hr1 : (1 / 2 : ℝ) * (1 - σ) ≤ 1 := by nlinarith
    have hq0 : 0 ≤ (1 / 2 : ℝ) * (1 + σ) := by nlinarith
    have hq1 : (1 / 2 : ℝ) * (1 + σ) ≤ 1 := by nlinarith
    exact ⟨by
      rw [abs_of_nonneg (pow_nonneg hr0 L)]
      exact pow_le_one₀ hr0 hr1, by
      rw [abs_of_nonneg (pow_nonneg hq0 L)]
      exact pow_le_one₀ hq0 hq1⟩
  have hpulseDeriv :
      ∀ (σ κ : ℝ), |σ| ≤ 1 → |κ| ≤ 1 →
        |(L : ℝ) * ((1 / 2 : ℝ) * (1 - σ)) ^ (L - 1) *
            (-(1 / 2 : ℝ) * κ)| ≤ (L : ℝ) ∧
        |(L : ℝ) * ((1 / 2 : ℝ) * (1 + σ)) ^ (L - 1) *
            ((1 / 2 : ℝ) * κ)| ≤ (L : ℝ) := by
    intro σ κ hσ hκ
    have hσlo : -1 ≤ σ := (abs_le.mp hσ).1
    have hσhi : σ ≤ 1 := (abs_le.mp hσ).2
    have hr0 : 0 ≤ (1 / 2 : ℝ) * (1 - σ) := by nlinarith
    have hr1 : (1 / 2 : ℝ) * (1 - σ) ≤ 1 := by nlinarith
    have hq0 : 0 ≤ (1 / 2 : ℝ) * (1 + σ) := by nlinarith
    have hq1 : (1 / 2 : ℝ) * (1 + σ) ≤ 1 := by nlinarith
    have hκhalf : |(1 / 2 : ℝ) * κ| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      nlinarith [hκ]
    constructor
    · calc
        |(L : ℝ) * ((1 / 2 : ℝ) * (1 - σ)) ^ (L - 1) *
            (-(1 / 2 : ℝ) * κ)|
            = (L : ℝ) *
              |((1 / 2 : ℝ) * (1 - σ)) ^ (L - 1)| *
              |-(1 / 2 : ℝ) * κ| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg L)]
        _ ≤ (L : ℝ) * 1 * 1 := by
          gcongr
          · rw [abs_of_nonneg (pow_nonneg hr0 (L - 1))]
            exact pow_le_one₀ hr0 hr1
          · simpa [abs_neg] using hκhalf
        _ = (L : ℝ) := by ring
    · calc
        |(L : ℝ) * ((1 / 2 : ℝ) * (1 + σ)) ^ (L - 1) *
            ((1 / 2 : ℝ) * κ)|
            = (L : ℝ) *
              |((1 / 2 : ℝ) * (1 + σ)) ^ (L - 1)| *
              |(1 / 2 : ℝ) * κ| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg L)]
        _ ≤ (L : ℝ) * 1 * 1 := by
          gcongr
          rw [abs_of_nonneg (pow_nonneg hq0 (L - 1))]
          exact pow_le_one₀ hq0 hq1
        _ = (L : ℝ) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    have hs := (hsc t ht).1
    simpa [selRP, eval₂_pow, eval₂_mul, eval₂_C, eval₂_sub, eval₂_one, eval₂_X]
      using (hpulse (yt t (selOfContract V (contractS d))) hs).1
  · intro t ht
    have hs := (hsc t ht).1
    have hc := (hsc t ht).2
    simpa [selRPderiv, eval₂_pow, eval₂_mul, eval₂_C, eval₂_sub, eval₂_one,
      eval₂_X] using (hpulseDeriv (yt t (selOfContract V (contractS d)))
        (yt t (selOfContract V (contractC d))) hs hc).1
  · intro t ht
    have hs := (hsc t ht).1
    simpa [selQP, eval₂_pow, eval₂_mul, eval₂_C, eval₂_add, eval₂_one, eval₂_X]
      using (hpulse (yt t (selOfContract V (contractS d))) hs).2
  · intro t ht
    have hs := (hsc t ht).1
    have hc := (hsc t ht).2
    simpa [selQPderiv, eval₂_pow, eval₂_mul, eval₂_C, eval₂_add, eval₂_one,
      eval₂_X] using (hpulseDeriv (yt t (selOfContract V (contractS d)))
        (yt t (selOfContract V (contractC d))) hs hc).2

/-- Finite-horizon bound with the clock-pulse and `Cbd` coefficient clauses
discharged from the in-file scalar lemmas.  `hCbd_ge` only says the chosen
monotone coefficient function dominates the explicit product of the alpha and
gate bounds; the actual per-solution coefficient clauses are proved below.

`hMixBound` is the remaining explicit satisfiable affine-mixture contract,
derived externally from `BranchData.coord_lipschitz`; `hChiGain`, `hA`, and
the reset sign hypothesis are the honest realization layer. -/
theorem selector_finiteHorizonBound_discharged
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (Cbd Mbd Gbd Abd : ℝ → ℝ)
    (hCbdmono : Monotone Cbd) (hMbdmono : Monotone Mbd)
    (hGbdmono : Monotone Gbd) (hAbdmono : Monotone Abd)
    (hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ) (hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ) (hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ)
    (hCbd_ge : ∀ T : ℝ, 0 < T →
      let y0 : Fin (selectorDim d V) → ℝ :=
        fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
      let muBd : ℝ :=
        |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T
      let alphaBd : ℝ :=
        |y0 (selOfContract V (contractAlpha d))| *
          Real.exp (|(cαq : ℝ)| * T)
      let gateZBd : ℝ :=
        |y0 (selOfContract V (contractGateZ d))| *
          Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * T)
      let gateUBd : ℝ :=
        |y0 (selOfContract V (contractGateU d))| *
          Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * T)
      |(Aq : ℝ)| * alphaBd * max gateZBd gateUBd ≤ Cbd T)
    (hMixBound : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selectorMixField branch i)| ≤ Mbd T)
    (hChiGain : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T)
    (hCr : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        Continuous yt)
    (hA : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |yt t (selOfContract V (contractA d))| ≤ Abd T) :
    Ripple.FiniteHorizonBound
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
      (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) := by
  refine selector_finiteHorizonBound branch chiResetP chiGateP kappaP gainP
    PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit Cbd Mbd Gbd Abd
    hCbdmono hMbdmono hGbdmono hAbdmono hCbd0 hMbd0 hGbd0 hAbd0 ?_
  intro T hT yt hyt0 hderiv
  have hpulse := selector_pulse_bounds branch chiResetP chiGateP kappaP gainP
    PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit yt hyt0 hderiv
  obtain ⟨hSelRP, hSelRPderiv, hSelQP, hSelQPderiv⟩ := hpulse
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  let muBd : ℝ :=
    |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T
  let alphaBd : ℝ :=
    |y0 (selOfContract V (contractAlpha d))| *
      Real.exp (|(cαq : ℝ)| * T)
  let gateZBd : ℝ :=
    |y0 (selOfContract V (contractGateZ d))| *
      Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * T)
  let gateUBd : ℝ :=
    |y0 (selOfContract V (contractGateU d))| *
      Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * T)
  have hyt0' : yt 0 = y0 := by simpa [y0] using hyt0
  have halpha : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractAlpha d))| ≤ alphaBd := by
    intro t ht
    rw [alpha_coord_eq (branch := branch) (chiResetP := chiResetP)
      (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
      (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
      (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv t ht]
    rw [hyt0']
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    dsimp [alphaBd]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        ((mul_le_mul_of_nonneg_right (le_abs_self _) ht.1).trans
          (mul_le_mul_of_nonneg_left (le_of_lt ht.2) (abs_nonneg _))))
      (abs_nonneg _)
  have hgateZ : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateZ d))| ≤ gateZBd := by
    intro t ht
    have hb := gateZ_coord_abs_bound (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
      (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv hSelRP hSelRPderiv t ht
    rw [hyt0'] at hb
    simpa [gateZBd, muBd] using hb
  have hgateU : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateU d))| ≤ gateUBd := by
    intro t ht
    have hb := gateU_coord_abs_bound (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
      (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv hSelQP hSelQPderiv t ht
    rw [hyt0'] at hb
    simpa [gateUBd, muBd] using hb
  have hCbdChoice :
      |(Aq : ℝ)| * alphaBd * max gateZBd gateUBd ≤ Cbd T := by
    simpa [y0, muBd, alphaBd, gateZBd, gateUBd] using hCbd_ge T hT
  have hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd T := by
    intro t ht
    calc
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
          yt t (selOfContract V (contractGateZ d))|
          = |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| *
            |yt t (selOfContract V (contractGateZ d))| := by
              rw [abs_mul, abs_mul]
      _ ≤ |(Aq : ℝ)| * alphaBd * gateZBd := by
        gcongr
        · exact halpha t ht
        · exact hgateZ t ht
      _ ≤ |(Aq : ℝ)| * alphaBd * max gateZBd gateUBd := by
        gcongr
        exact le_max_left _ _
      _ ≤ Cbd T := hCbdChoice
  have hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd T := by
    intro t ht
    calc
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
          yt t (selOfContract V (contractGateU d))|
          = |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| *
            |yt t (selOfContract V (contractGateU d))| := by
              rw [abs_mul, abs_mul]
      _ ≤ |(Aq : ℝ)| * alphaBd * gateUBd := by
        gcongr
        · exact halpha t ht
        · exact hgateU t ht
      _ ≤ |(Aq : ℝ)| * alphaBd * max gateZBd gateUBd := by
        gcongr
        exact le_max_right _ _
      _ ≤ Cbd T := hCbdChoice
  exact ⟨hSelRP, hSelRPderiv, hSelQP, hSelQPderiv, hCoefZ, hCoefU,
    hMixBound T hT yt hyt0 hderiv, hChiGain T hT yt hyt0 hderiv,
    hCr T hT yt hyt0 hderiv, hytcont T hT yt hyt0 hderiv,
    hA T hT yt hyt0 hderiv⟩

/-- The dynamic selector mixture is affine in the active `u_i` coordinate,
uniformly on a finite horizon, once the selector weights stay in `[0,1]`.
The constants are deliberately coarse finite sums over branches and output
coordinates; no tightness is needed for the a-priori box. -/
theorem selector_mix_affine_bound
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hBpos : 0 < B)
    (hLam01 : ∀ v : V, ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ yt t (selLamCoord v) ∧ yt t (selLamCoord v) ≤ 1) :
    ∃ Cmix kmix : ℝ, 0 ≤ Cmix ∧ 0 ≤ kmix ∧
      ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
        |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selectorMixField branch i)| ≤
        Cmix + kmix * |yt t (selU V i)| := by
  classical
  let Cmix : ℝ :=
    ∑ v : V, ∑ j : Fin d,
      |BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) j|
  let kmix : ℝ :=
    ∑ v : V, ∑ j : Fin d,
      BranchAction.multiplier B ((branch v).action j)
  have hCmix0 : 0 ≤ Cmix := by
    dsimp [Cmix]
    exact Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hkmix0 : 0 ≤ kmix := by
    dsimp [kmix]
    exact Finset.sum_nonneg (fun v _ =>
      Finset.sum_nonneg (fun j _ => by
        simpa [BranchAction.multiplier] using
          abs_nonneg (((branch v).action j).scale : ℝ)))
  refine ⟨Cmix, kmix, hCmix0, hkmix0, ?_⟩
  intro i t ht
  have heval :
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selectorMixField branch i) =
        ∑ v : V, yt t (selLamCoord v) *
          BranchData.evalBranch (branch v)
            (fun j => yt t (selU V j)) i := by
    rw [selectorMixField, eval₂_selectorMixFieldPoly]
  have hterm : ∀ v : V,
      |yt t (selLamCoord v) *
        BranchData.evalBranch (branch v) (fun j => yt t (selU V j)) i| ≤
      |BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) i| +
        BranchAction.multiplier B ((branch v).action i) *
          |yt t (selU V i)| := by
    intro v
    let a := BranchData.evalBranch (branch v) (fun j => yt t (selU V j)) i
    let b := BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) i
    let m := BranchAction.multiplier B ((branch v).action i)
    have hm_nonneg : 0 ≤ m := by
      simpa [m, BranchAction.multiplier] using
        abs_nonneg (((branch v).action i).scale : ℝ)
    have hlam : |yt t (selLamCoord v)| ≤ 1 := by
      rw [abs_of_nonneg (hLam01 v t ht).1]
      exact (hLam01 v t ht).2
    have hlip : |a - b| ≤ m * |yt t (selU V i)| := by
      simpa [a, b, m] using
        BranchData.coord_lipschitz hBpos (branch v)
          (fun j => yt t (selU V j)) (fun _ => (0 : ℝ)) i
    have hbranch : |a| ≤ |b| + m * |yt t (selU V i)| := by
      calc
        |a| = |(a - b) + b| := by congr 1; ring
        _ ≤ |a - b| + |b| := abs_add_le _ _
        _ ≤ m * |yt t (selU V i)| + |b| :=
          by linarith [hlip]
        _ = |b| + m * |yt t (selU V i)| := by ring
    have hrhs0 : 0 ≤ |b| + m * |yt t (selU V i)| := by
      exact add_nonneg (abs_nonneg _)
        (mul_nonneg hm_nonneg (abs_nonneg _))
    calc
      |yt t (selLamCoord v) * a| = |yt t (selLamCoord v)| * |a| := abs_mul _ _
      _ ≤ 1 * (|b| + m * |yt t (selU V i)|) :=
        mul_le_mul hlam hbranch (abs_nonneg _) zero_le_one
      _ = |b| + m * |yt t (selU V i)| := by ring
  have hsum :
      |∑ v : V, yt t (selLamCoord v) *
          BranchData.evalBranch (branch v)
            (fun j => yt t (selU V j)) i| ≤
      (∑ v : V, |BranchData.evalBranch (branch v)
          (fun _ => (0 : ℝ)) i|) +
        (∑ v : V, BranchAction.multiplier B ((branch v).action i)) *
          |yt t (selU V i)| := by
    calc
      |∑ v : V, yt t (selLamCoord v) *
          BranchData.evalBranch (branch v)
            (fun j => yt t (selU V j)) i|
          ≤ ∑ v : V, |yt t (selLamCoord v) *
              BranchData.evalBranch (branch v)
                (fun j => yt t (selU V j)) i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v : V, (|BranchData.evalBranch (branch v)
              (fun _ => (0 : ℝ)) i| +
            BranchAction.multiplier B ((branch v).action i) *
              |yt t (selU V i)|) :=
            Finset.sum_le_sum (fun v _ => hterm v)
      _ = (∑ v : V, |BranchData.evalBranch (branch v)
              (fun _ => (0 : ℝ)) i|) +
            (∑ v : V, BranchAction.multiplier B ((branch v).action i)) *
              |yt t (selU V i)| := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
  have hCcoord :
      (∑ v : V, |BranchData.evalBranch (branch v)
          (fun _ => (0 : ℝ)) i|) ≤ Cmix := by
    dsimp [Cmix]
    exact Finset.sum_le_sum (fun v _ =>
      Finset.single_le_sum
        (fun j _ => abs_nonneg
          (BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) j))
        (Finset.mem_univ i))
  have hKcoord :
      (∑ v : V, BranchAction.multiplier B ((branch v).action i)) ≤ kmix := by
    dsimp [kmix]
    exact Finset.sum_le_sum (fun v _ =>
      Finset.single_le_sum
        (f := fun j => BranchAction.multiplier B ((branch v).action j))
        (fun j _ => abs_nonneg _)
        (Finset.mem_univ i))
  calc
    |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)|
        = |∑ v : V, yt t (selLamCoord v) *
            BranchData.evalBranch (branch v)
              (fun j => yt t (selU V j)) i| := by rw [heval]
    _ ≤ (∑ v : V, |BranchData.evalBranch (branch v)
          (fun _ => (0 : ℝ)) i|) +
        (∑ v : V, BranchAction.multiplier B ((branch v).action i)) *
          |yt t (selU V i)| := hsum
    _ ≤ Cmix + kmix * |yt t (selU V i)| :=
      add_le_add hCcoord
        (mul_le_mul_of_nonneg_right hKcoord (abs_nonneg _))

/-- Coupled `z/u` a-priori bound with an affine-in-`u` mixture estimate in the
rate.  This removes the separate carried `Mbd` mixture box: the only rate data
are the coefficient bound `Cbd` and the affine constants `Cmix, kmix`. -/
theorem zu_coord_abs_bound_selfcontained (i : Fin d)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T Cbd Cmix kmix : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t)
    (hCbd : 0 ≤ Cbd) (hCmix : 0 ≤ Cmix) (hkmix : 0 ≤ kmix)
    (hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd)
    (hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd)
    (hMixAff : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)| ≤
        Cmix + kmix * |yt t (selU V i)|) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selZ V i)| ≤
        gronwallBound ‖(yt 0 (selZ V i), yt 0 (selU V i))‖
          (Cbd * (2 + kmix)) (Cbd * Cmix) T ∧
      |yt t (selU V i)| ≤
        gronwallBound ‖(yt 0 (selZ V i), yt 0 (selU V i))‖
          (Cbd * (2 + kmix)) (Cbd * Cmix) T := by
  intro t ht
  let f : ℝ → ℝ × ℝ := fun s => (yt s (selZ V i), yt s (selU V i))
  let f' : ℝ → ℝ × ℝ := fun s =>
    ((Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
        yt s (selOfContract V (contractGateZ d)) *
        (MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selectorMixField branch i)
          - yt s (selZ V i)),
      (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
        yt s (selOfContract V (contractGateU d)) *
        (yt s (selZ V i) - yt s (selU V i)))
  have hcont : ContinuousOn f (Icc (0 : ℝ) t) := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hz := (hasDerivAt_pi.mp (hderiv s hsT)) (selZ V i)
    have hu := (hasDerivAt_pi.mp (hderiv s hsT)) (selU V i)
    exact (hz.prodMk hu).continuousAt.continuousWithinAt
  have hderivWithin : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt f (f' s) (Ici s) s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have hz := (hasDerivAt_pi.mp (hderiv s hsT)) (selZ V i)
    have hu := (hasDerivAt_pi.mp (hderiv s hsT)) (selU V i)
    rw [aprioriField_z_eq] at hz
    rw [aprioriField_u_eq] at hu
    have hpair : HasDerivAt f (f' s) s := by simpa [f, f'] using (hz.prodMk hu)
    exact hpair.hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t,
      ‖f' s‖ ≤ (Cbd * (2 + kmix)) * ‖f s‖ + Cbd * Cmix := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
    let z := yt s (selZ V i)
    let u := yt s (selU V i)
    let m := MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selectorMixField branch i)
    let az := (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
      yt s (selOfContract V (contractGateZ d))
    let au := (Aq : ℝ) * yt s (selOfContract V (contractAlpha d)) *
      yt s (selOfContract V (contractGateU d))
    have haz : |az| ≤ Cbd := by simpa [az] using hCoefZ s hsT
    have hau : |au| ≤ Cbd := by simpa [au] using hCoefU s hsT
    have hm : |m| ≤ Cmix + kmix * |u| := by simpa [m, u] using hMixAff s hsT
    have hzle : |z| ≤ ‖(z, u)‖ := by
      change |z| ≤ max ‖z‖ ‖u‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_left _ _
    have hule : |u| ≤ ‖(z, u)‖ := by
      change |u| ≤ max ‖z‖ ‖u‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact le_max_right _ _
    have hmN : |m| ≤ Cmix + kmix * ‖(z, u)‖ :=
      hm.trans (by linarith [mul_le_mul_of_nonneg_left hule hkmix])
    have hmz_abs : |m - z| ≤ |m| + |z| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le m (-z)
    have hzu_abs : |z - u| ≤ |z| + |u| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le z (-u)
    have hdz :
        |az * (m - z)| ≤ (Cbd * (2 + kmix)) * ‖(z, u)‖ + Cbd * Cmix := by
      calc
        |az * (m - z)| = |az| * |m - z| := abs_mul _ _
        _ ≤ Cbd * |m - z| :=
          mul_le_mul_of_nonneg_right haz (abs_nonneg _)
        _ ≤ Cbd * (|m| + |z|) :=
          mul_le_mul_of_nonneg_left hmz_abs hCbd
        _ ≤ Cbd * ((Cmix + kmix * ‖(z, u)‖) + ‖(z, u)‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hmN hzle) hCbd
        _ ≤ (Cbd * (2 + kmix)) * ‖(z, u)‖ + Cbd * Cmix := by
          nlinarith [hCbd, hCmix, hkmix, norm_nonneg (z, u),
            mul_nonneg (mul_nonneg hCbd hkmix) (norm_nonneg (z, u)),
            mul_nonneg hCbd hCmix]
    have hdu :
        |au * (z - u)| ≤ (Cbd * (2 + kmix)) * ‖(z, u)‖ + Cbd * Cmix := by
      calc
        |au * (z - u)| = |au| * |z - u| := abs_mul _ _
        _ ≤ Cbd * |z - u| :=
          mul_le_mul_of_nonneg_right hau (abs_nonneg _)
        _ ≤ Cbd * (|z| + |u|) :=
          mul_le_mul_of_nonneg_left hzu_abs hCbd
        _ ≤ Cbd * (‖(z, u)‖ + ‖(z, u)‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hzle hule) hCbd
        _ ≤ (Cbd * (2 + kmix)) * ‖(z, u)‖ + Cbd * Cmix := by
          nlinarith [hCbd, hCmix, hkmix, norm_nonneg (z, u),
            mul_nonneg (mul_nonneg hCbd hkmix) (norm_nonneg (z, u)),
            mul_nonneg hCbd hCmix]
    simpa [f, f', z, u, m, az, au, Real.norm_eq_abs] using max_le hdz hdu
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (δ := ‖f 0‖) (K := Cbd * (2 + kmix))
    (ε := Cbd * Cmix) (a := (0 : ℝ)) (b := t)
    hcont hderivWithin (by simp [f]) hbound t ⟨ht.1, le_rfl⟩
  have hK : 0 ≤ Cbd * (2 + kmix) :=
    mul_nonneg hCbd (by nlinarith)
  have hε : 0 ≤ Cbd * Cmix := mul_nonneg hCbd hCmix
  have hmono := gronwallBound_mono (δ := ‖f 0‖) (K := Cbd * (2 + kmix))
    (ε := Cbd * Cmix) (norm_nonneg _) hε hK
  have hpairT : ‖f t‖ ≤
      gronwallBound ‖f 0‖ (Cbd * (2 + kmix)) (Cbd * Cmix) T := by
    have hpairt : ‖f t‖ ≤
        gronwallBound ‖f 0‖ (Cbd * (2 + kmix)) (Cbd * Cmix) t := by
      simpa [sub_zero] using hgr
    exact hpairt.trans (hmono (le_of_lt ht.2))
  have hz_abs : |yt t (selZ V i)| ≤ ‖f t‖ := by
    have := norm_fst_le (f t)
    simpa [f, Real.norm_eq_abs] using this
  have hu_abs : |yt t (selU V i)| ≤ ‖f t‖ := by
    have := norm_snd_le (f t)
    simpa [f, Real.norm_eq_abs] using this
  constructor
  · exact hz_abs.trans (by simpa [f] using hpairT)
  · exact hu_abs.trans (by simpa [f] using hpairT)

/-- Explicit constant term for the selector mixture affine estimate. -/
private def selectorMixConst
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) : ℝ :=
  ∑ v : V, ∑ j : Fin d,
    |BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) j|

/-- Explicit slope for the selector mixture affine estimate. -/
private def selectorMixSlope
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) : ℝ :=
  ∑ v : V, ∑ j : Fin d,
    BranchAction.multiplier B ((branch v).action j)

private theorem selectorMixConst_nonneg
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) :
    0 ≤ selectorMixConst branch := by
  dsimp [selectorMixConst]
  exact Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _))

private theorem selectorMixSlope_nonneg
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B) :
    0 ≤ selectorMixSlope branch := by
  dsimp [selectorMixSlope]
  exact Finset.sum_nonneg (fun v _ =>
    Finset.sum_nonneg (fun j _ => by
      simpa [BranchAction.multiplier] using
        abs_nonneg (((branch v).action j).scale : ℝ)))

/-- Explicit version of `selector_mix_affine_bound`, with constants independent
of the particular trajectory and horizon. -/
private theorem selector_mix_affine_bound_explicit
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hBpos : 0 < B)
    (hLam01 : ∀ v : V, ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ yt t (selLamCoord v) ∧ yt t (selLamCoord v) ≤ 1) :
    ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)| ≤
      selectorMixConst branch + selectorMixSlope branch *
        |yt t (selU V i)| := by
  classical
  intro i t ht
  have heval :
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selectorMixField branch i) =
        ∑ v : V, yt t (selLamCoord v) *
          BranchData.evalBranch (branch v)
            (fun j => yt t (selU V j)) i := by
    rw [selectorMixField, eval₂_selectorMixFieldPoly]
  have hterm : ∀ v : V,
      |yt t (selLamCoord v) *
        BranchData.evalBranch (branch v) (fun j => yt t (selU V j)) i| ≤
      |BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) i| +
        BranchAction.multiplier B ((branch v).action i) *
          |yt t (selU V i)| := by
    intro v
    let a := BranchData.evalBranch (branch v) (fun j => yt t (selU V j)) i
    let b := BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) i
    let m := BranchAction.multiplier B ((branch v).action i)
    have hm_nonneg : 0 ≤ m := by
      simpa [m, BranchAction.multiplier] using
        abs_nonneg (((branch v).action i).scale : ℝ)
    have hlam : |yt t (selLamCoord v)| ≤ 1 := by
      rw [abs_of_nonneg (hLam01 v t ht).1]
      exact (hLam01 v t ht).2
    have hlip : |a - b| ≤ m * |yt t (selU V i)| := by
      simpa [a, b, m] using
        BranchData.coord_lipschitz hBpos (branch v)
          (fun j => yt t (selU V j)) (fun _ => (0 : ℝ)) i
    have hbranch : |a| ≤ |b| + m * |yt t (selU V i)| := by
      calc
        |a| = |(a - b) + b| := by congr 1; ring
        _ ≤ |a - b| + |b| := abs_add_le _ _
        _ ≤ m * |yt t (selU V i)| + |b| := by linarith [hlip]
        _ = |b| + m * |yt t (selU V i)| := by ring
    calc
      |yt t (selLamCoord v) * a| =
          |yt t (selLamCoord v)| * |a| := abs_mul _ _
      _ ≤ 1 * (|b| + m * |yt t (selU V i)|) :=
        mul_le_mul hlam hbranch (abs_nonneg _) zero_le_one
      _ = |b| + m * |yt t (selU V i)| := by ring
  have hsum :
      |∑ v : V, yt t (selLamCoord v) *
          BranchData.evalBranch (branch v)
            (fun j => yt t (selU V j)) i| ≤
      (∑ v : V, |BranchData.evalBranch (branch v)
          (fun _ => (0 : ℝ)) i|) +
        (∑ v : V, BranchAction.multiplier B ((branch v).action i)) *
          |yt t (selU V i)| := by
    calc
      |∑ v : V, yt t (selLamCoord v) *
          BranchData.evalBranch (branch v)
            (fun j => yt t (selU V j)) i|
          ≤ ∑ v : V, |yt t (selLamCoord v) *
              BranchData.evalBranch (branch v)
                (fun j => yt t (selU V j)) i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v : V, (|BranchData.evalBranch (branch v)
              (fun _ => (0 : ℝ)) i| +
            BranchAction.multiplier B ((branch v).action i) *
              |yt t (selU V i)|) :=
            Finset.sum_le_sum (fun v _ => hterm v)
      _ = (∑ v : V, |BranchData.evalBranch (branch v)
              (fun _ => (0 : ℝ)) i|) +
            (∑ v : V, BranchAction.multiplier B ((branch v).action i)) *
              |yt t (selU V i)| := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
  have hCcoord :
      (∑ v : V, |BranchData.evalBranch (branch v)
          (fun _ => (0 : ℝ)) i|) ≤ selectorMixConst branch := by
    dsimp [selectorMixConst]
    exact Finset.sum_le_sum (fun v _ =>
      Finset.single_le_sum
        (fun j _ => abs_nonneg
          (BranchData.evalBranch (branch v) (fun _ => (0 : ℝ)) j))
        (Finset.mem_univ i))
  have hKcoord :
      (∑ v : V, BranchAction.multiplier B ((branch v).action i)) ≤
        selectorMixSlope branch := by
    dsimp [selectorMixSlope]
    exact Finset.sum_le_sum (fun v _ =>
      Finset.single_le_sum
        (f := fun j => BranchAction.multiplier B ((branch v).action j))
        (fun j _ => abs_nonneg _)
        (Finset.mem_univ i))
  calc
    |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)|
        = |∑ v : V, yt t (selLamCoord v) *
            BranchData.evalBranch (branch v)
              (fun j => yt t (selU V j)) i| := by rw [heval]
    _ ≤ (∑ v : V, |BranchData.evalBranch (branch v)
          (fun _ => (0 : ℝ)) i|) +
        (∑ v : V, BranchAction.multiplier B ((branch v).action i)) *
          |yt t (selU V i)| := hsum
    _ ≤ selectorMixConst branch + selectorMixSlope branch *
          |yt t (selU V i)| :=
      add_le_add hCcoord
        (mul_le_mul_of_nonneg_right hKcoord (abs_nonneg _))

/-- Explicit gate-coefficient bound used by
`selector_finiteHorizonBound_v2`.  The `max 0 τ` clamp only makes the function
globally monotone; on positive horizons it is exactly the intended bound. -/
private def selectorCoeffBdV2
    {d : ℕ} {V : Type} [Fintype V]
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ) (Aq cμq cαq : ℚ) (L : ℕ) :
    ℝ → ℝ := by
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  exact fun τ =>
    let θ : ℝ := max 0 τ
    let muBd : ℝ :=
      |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * θ
    let alphaBd : ℝ :=
      |y0 (selOfContract V (contractAlpha d))| *
        Real.exp (|(cαq : ℝ)| * θ)
    let gateBd : ℝ :=
      |y0 (selOfContract V (contractGateZ d))| *
        Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * θ)
    |(Aq : ℝ)| * alphaBd * gateBd

private def selectorMixMbdV2
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ) (Aq cμq cαq : ℚ) (L : ℕ) :
    ℝ → ℝ := by
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  let Cmix : ℝ := selectorMixConst branch
  let kmix : ℝ := selectorMixSlope branch
  let Cbd : ℝ → ℝ := selectorCoeffBdV2 (V := V) x₀ w warmGainInit Aq cμq cαq L
  exact fun τ =>
    let θ : ℝ := max 0 τ
    Cmix + kmix * ∑ i : Fin d,
      gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
        (Cbd τ * (2 + kmix)) (Cbd τ * Cmix) θ

/-- Finite-horizon selector bound carrying only the realization/sign facts.
The coefficient and mixture boxes are built internally from the self-contained
scalar, affine-mixture, and `z/u` Grönwall tools. -/
theorem selector_finiteHorizonBound_v2
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (Gbd Abd : ℝ → ℝ)
    (hBpos : 0 < B)
    (hGbdmono : Monotone Gbd) (hAbdmono : Monotone Abd)
    (hGbd0 : ∀ τ : ℝ, 0 ≤ Gbd τ) (hAbd0 : ∀ τ : ℝ, 0 ≤ Abd τ)
    (hChiGain : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP| ≤ Gbd T)
    (hCr : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        Continuous yt)
    (hA : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d V) → ℝ,
        yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) →
        Ripple.DerivOnIco
          (selectorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
          yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |yt t (selOfContract V (contractA d))| ≤ Abd T) :
    Ripple.FiniteHorizonBound
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
      (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)) := by
  classical
  let Cbd : ℝ → ℝ := selectorCoeffBdV2 (V := V) x₀ w warmGainInit Aq cμq cαq L
  let Mbd : ℝ → ℝ := selectorMixMbdV2 branch x₀ w warmGainInit Aq cμq cαq L
  have hCmix0 : 0 ≤ selectorMixConst branch := selectorMixConst_nonneg branch
  have hkmix0 : 0 ≤ selectorMixSlope branch := selectorMixSlope_nonneg branch
  have hCbd0 : ∀ τ : ℝ, 0 ≤ Cbd τ := by
    intro τ
    dsimp [Cbd, selectorCoeffBdV2]
    positivity
  have hCbdmono : Monotone Cbd := by
    intro S T hST
    let y0 : Fin (selectorDim d V) → ℝ :=
      fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
    let θS : ℝ := max (0 : ℝ) S
    let θT : ℝ := max (0 : ℝ) T
    let muBd : ℝ → ℝ :=
      fun θ => |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * θ
    let alphaBd : ℝ → ℝ :=
      fun θ => |y0 (selOfContract V (contractAlpha d))| *
        Real.exp (|(cαq : ℝ)| * θ)
    let gateBd : ℝ → ℝ :=
      fun θ => |y0 (selOfContract V (contractGateZ d))| *
        Real.exp ((|(cμq : ℝ)| + muBd θ * (L : ℝ)) * θ)
    have hθ : θS ≤ θT := by
      dsimp [θS, θT]
      exact max_le_max le_rfl hST
    have hθS0 : 0 ≤ θS := by dsimp [θS]; exact le_max_left _ _
    have hθT0 : 0 ≤ θT := by dsimp [θT]; exact le_max_left _ _
    have hmu : muBd θS ≤ muBd θT := by
      dsimp [muBd]
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hθ (abs_nonneg _)) _
    have hmuT0 : 0 ≤ muBd θT := by
      dsimp [muBd]
      exact add_nonneg (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) hθT0)
    have halpha : alphaBd θS ≤ alphaBd θT := by
      dsimp [alphaBd]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hθ (abs_nonneg _)))
        (abs_nonneg _)
    have hgate : gateBd θS ≤ gateBd θT := by
      have hcoef :
          |(cμq : ℝ)| + muBd θS * (L : ℝ) ≤
          |(cμq : ℝ)| + muBd θT * (L : ℝ) := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)) _
      have harg :
          (|(cμq : ℝ)| + muBd θS * (L : ℝ)) * θS ≤
          (|(cμq : ℝ)| + muBd θT * (L : ℝ)) * θT := by
        have hcoefT0 :
            0 ≤ |(cμq : ℝ)| + muBd θT * (L : ℝ) :=
          add_nonneg (abs_nonneg _)
            (mul_nonneg hmuT0 (Nat.cast_nonneg _))
        exact mul_le_mul hcoef hθ hθS0 hcoefT0
      dsimp [gateBd]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr harg) (abs_nonneg _)
    dsimp [Cbd, selectorCoeffBdV2]
    change |(Aq : ℝ)| * alphaBd θS * gateBd θS ≤
      |(Aq : ℝ)| * alphaBd θT * gateBd θT
    have hleft :
        |(Aq : ℝ)| * alphaBd θS ≤ |(Aq : ℝ)| * alphaBd θT :=
      mul_le_mul_of_nonneg_left halpha (abs_nonneg _)
    exact mul_le_mul hleft hgate (by positivity) (by positivity)
  have hMbd0 : ∀ τ : ℝ, 0 ≤ Mbd τ := by
    intro τ
    dsimp [Mbd, selectorMixMbdV2]
    refine add_nonneg hCmix0 (mul_nonneg hkmix0 ?_)
    exact Finset.sum_nonneg (fun i _ =>
      gronwallBound_nonneg_of_nonneg (by positivity)
        (mul_nonneg (hCbd0 τ) hCmix0) (le_max_left _ _))
  have hMbdmono : Monotone Mbd := by
    intro S T hST
    let θS : ℝ := max 0 S
    let θT : ℝ := max 0 T
    have hθ : θS ≤ θT := by
      dsimp [θS, θT]
      exact max_le_max le_rfl hST
    have hθT0 : 0 ≤ θT := by dsimp [θT]; exact le_max_left _ _
    have hθS0 : 0 ≤ θS := by dsimp [θS]; exact le_max_left _ _
    have hCST : Cbd S ≤ Cbd T := hCbdmono hST
    dsimp [Mbd, selectorMixMbdV2]
    refine add_le_add_right ?_ (selectorMixConst branch)
    refine mul_le_mul_of_nonneg_left ?_ hkmix0
    refine Finset.sum_le_sum ?_
    intro i _hi
    let δi : ℝ :=
      max ‖selectorEuclInitQ d V x₀ w warmGainInit (selZ V i)‖
        ‖selectorEuclInitQ d V x₀ w warmGainInit (selU V i)‖
    have hδ : 0 ≤ δi := by
      dsimp [δi]
      positivity
    have hεS : 0 ≤ Cbd S * selectorMixConst branch :=
      mul_nonneg (hCbd0 S) hCmix0
    have hKST :
        Cbd S * (2 + selectorMixSlope branch) ≤
        Cbd T * (2 + selectorMixSlope branch) := by
      exact mul_le_mul_of_nonneg_right hCST (by nlinarith)
    have hεST :
        Cbd S * selectorMixConst branch ≤
        Cbd T * selectorMixConst branch :=
      mul_le_mul_of_nonneg_right hCST hCmix0
    have htime :
        gronwallBound δi (Cbd S * (2 + selectorMixSlope branch))
          (Cbd S * selectorMixConst branch) θS ≤
        gronwallBound δi (Cbd S * (2 + selectorMixSlope branch))
          (Cbd S * selectorMixConst branch) θT := by
      have hK : 0 ≤ Cbd S * (2 + selectorMixSlope branch) :=
        mul_nonneg (hCbd0 S) (by nlinarith)
      exact gronwallBound_mono (δ := δi)
        (K := Cbd S * (2 + selectorMixSlope branch))
        (ε := Cbd S * selectorMixConst branch) hδ hεS hK hθ
    have hKstep :
        gronwallBound δi (Cbd S * (2 + selectorMixSlope branch))
          (Cbd S * selectorMixConst branch) θT ≤
        gronwallBound δi (Cbd T * (2 + selectorMixSlope branch))
          (Cbd S * selectorMixConst branch) θT := by
      exact gronwallBound_mono_K (δ := δi)
        (ε := Cbd S * selectorMixConst branch) (x := θT)
        hδ hεS hθT0 hKST
    have hεstep :
        gronwallBound δi (Cbd T * (2 + selectorMixSlope branch))
          (Cbd S * selectorMixConst branch) θT ≤
        gronwallBound δi (Cbd T * (2 + selectorMixSlope branch))
          (Cbd T * selectorMixConst branch) θT := by
      exact gronwallBound_mono_epsilon (δ := δi)
        (K := Cbd T * (2 + selectorMixSlope branch)) (x := θT) hθT0 hεST
    exact htime.trans (hKstep.trans hεstep)
  refine selector_finiteHorizonBound branch chiResetP chiGateP kappaP gainP
    PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit Cbd Mbd Gbd Abd
    hCbdmono hMbdmono hGbdmono hAbdmono hCbd0 hMbd0 hGbd0 hAbd0 ?_
  intro T hT yt hyt0 hderiv
  have hpulse := selector_pulse_bounds branch chiResetP chiGateP kappaP gainP
    PpolyP HP Aq Kq cμq cαq L R x₀ w warmGainInit yt hyt0 hderiv
  obtain ⟨hSelRP, hSelRPderiv, hSelQP, hSelQPderiv⟩ := hpulse
  let y0 : Fin (selectorDim d V) → ℝ :=
    fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)
  let muBd : ℝ :=
    |y0 (selOfContract V (contractMu d))| + |(cμq : ℝ)| * T
  let alphaBd : ℝ :=
    |y0 (selOfContract V (contractAlpha d))| *
      Real.exp (|(cαq : ℝ)| * T)
  let gateZBd : ℝ :=
    |y0 (selOfContract V (contractGateZ d))| *
      Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * T)
  let gateUBd : ℝ :=
    |y0 (selOfContract V (contractGateU d))| *
      Real.exp ((|(cμq : ℝ)| + muBd * (L : ℝ)) * T)
  have hyt0' : yt 0 = y0 := by simpa [y0] using hyt0
  have hθT : max 0 T = T := max_eq_right (le_of_lt hT)
  have hcontT : Continuous yt := hytcont T hT yt hyt0 hderiv
  have halpha : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractAlpha d))| ≤ alphaBd := by
    intro t ht
    rw [alpha_coord_eq (branch := branch) (chiResetP := chiResetP)
      (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
      (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
      (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv t ht]
    rw [hyt0']
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    dsimp [alphaBd]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        ((mul_le_mul_of_nonneg_right (le_abs_self _) ht.1).trans
          (mul_le_mul_of_nonneg_left (le_of_lt ht.2) (abs_nonneg _))))
      (abs_nonneg _)
  have hgateZ : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateZ d))| ≤ gateZBd := by
    intro t ht
    have hb := gateZ_coord_abs_bound (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
      (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv hSelRP hSelRPderiv t ht
    rw [hyt0'] at hb
    simpa [gateZBd, muBd] using hb
  have hgateU : ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractGateU d))| ≤ gateUBd := by
    intro t ht
    have hb := gateU_coord_abs_bound (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
      (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv hSelQP hSelQPderiv t ht
    rw [hyt0'] at hb
    simpa [gateUBd, muBd] using hb
  have hgateU_le_Z : gateUBd ≤ gateZBd := by
    dsimp [gateUBd, gateZBd]
    have hinit :
        |y0 (selOfContract V (contractGateU d))| ≤
        |y0 (selOfContract V (contractGateZ d))| := by
      simp [y0, selectorEuclInitQ, selOfContract, contractGateZ, contractGateU]
    exact mul_le_mul_of_nonneg_right hinit (le_of_lt (Real.exp_pos _))
  have hCbdChoice :
      |(Aq : ℝ)| * alphaBd * gateZBd = Cbd T := by
    dsimp [Cbd, selectorCoeffBdV2, alphaBd, gateZBd, muBd]
    simp [hθT, y0]
  have hCoefZ : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateZ d))| ≤ Cbd T := by
    intro t ht
    calc
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
          yt t (selOfContract V (contractGateZ d))|
          = |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| *
            |yt t (selOfContract V (contractGateZ d))| := by
              rw [abs_mul, abs_mul]
      _ ≤ |(Aq : ℝ)| * alphaBd * gateZBd := by
        have hleft :
            |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| ≤
            |(Aq : ℝ)| * alphaBd :=
          mul_le_mul_of_nonneg_left (halpha t ht) (abs_nonneg _)
        exact mul_le_mul hleft (hgateZ t ht)
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
      _ = Cbd T := hCbdChoice
  have hCoefU : ∀ t ∈ Ico (0 : ℝ) T,
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
        yt t (selOfContract V (contractGateU d))| ≤ Cbd T := by
    intro t ht
    calc
      |(Aq : ℝ) * yt t (selOfContract V (contractAlpha d)) *
          yt t (selOfContract V (contractGateU d))|
          = |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| *
            |yt t (selOfContract V (contractGateU d))| := by
              rw [abs_mul, abs_mul]
      _ ≤ |(Aq : ℝ)| * alphaBd * gateUBd := by
        have hleft :
            |(Aq : ℝ)| * |yt t (selOfContract V (contractAlpha d))| ≤
            |(Aq : ℝ)| * alphaBd :=
          mul_le_mul_of_nonneg_left (halpha t ht) (abs_nonneg _)
        exact mul_le_mul hleft (hgateU t ht)
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
      _ ≤ |(Aq : ℝ)| * alphaBd * gateZBd := by
        exact mul_le_mul_of_nonneg_left hgateU_le_Z
          (mul_nonneg (abs_nonneg _) (by positivity))
      _ = Cbd T := hCbdChoice
  have hLam01 : ∀ v : V, ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ yt t (selLamCoord v) ∧ yt t (selLamCoord v) ≤ 1 := by
    intro v t ht
    have hup := lam_coord_le_one (branch := branch) (chiResetP := chiResetP)
      (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
      (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
      (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) v hcontT (by
        rw [hyt0]
        norm_num [selectorEuclInitQ, selLamCoord])
      (hCr T hT yt hyt0 hderiv) hderiv
    have hlow := lam_coord_nonneg (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP)
      (Aq := Aq) (Kq := Kq) (cμq := cμq) (cαq := cαq)
      (L := L) (R := R) (yt := yt) (T := T) v hcontT (by
        rw [hyt0]
        norm_num [selectorEuclInitQ, selLamCoord])
      ((selector_eval₂_continuous_along yt hcontT chiResetP).mul
        (selector_eval₂_continuous_along yt hcontT kappaP))
      ((selector_eval₂_continuous_along yt hcontT chiGateP).mul
        (selector_eval₂_continuous_along yt hcontT gainP))
      (selector_eval₂_continuous_along yt hcontT (PpolyP v))
      (hCr T hT yt hyt0 hderiv) hup hderiv
    exact ⟨hlow t ht, hup t ht⟩
  have hMixAff := selector_mix_affine_bound_explicit
    (branch := branch) (yt := yt) (T := T) hBpos hLam01
  have hMixBound : ∀ i : Fin d, ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selectorMixField branch i)| ≤ Mbd T := by
    intro i t ht
    have hzu := (zu_coord_abs_bound_selfcontained (branch := branch)
      (chiResetP := chiResetP) (chiGateP := chiGateP) (kappaP := kappaP)
      (gainP := gainP) (PpolyP := PpolyP) (HP := HP) (Aq := Aq)
      (Kq := Kq) (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      i (yt := yt) (T := T) (Cbd := Cbd T)
      (Cmix := selectorMixConst branch) (kmix := selectorMixSlope branch)
      hderiv (hCbd0 T) hCmix0 hkmix0 hCoefZ hCoefU
      (hMixAff i) t ht).2
    rw [hyt0'] at hzu
    have hsum :
        gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
          (Cbd T * (2 + selectorMixSlope branch))
          (Cbd T * selectorMixConst branch) T ≤
        ∑ j : Fin d,
          gronwallBound ‖(y0 (selZ V j), y0 (selU V j))‖
            (Cbd T * (2 + selectorMixSlope branch))
            (Cbd T * selectorMixConst branch) T := by
      refine Finset.single_le_sum
        (f := fun j : Fin d =>
          gronwallBound ‖(y0 (selZ V j), y0 (selU V j))‖
            (Cbd T * (2 + selectorMixSlope branch))
            (Cbd T * selectorMixConst branch) T)
        ?_ (Finset.mem_univ i)
      intro j hj
      exact gronwallBound_nonneg_of_nonneg (norm_nonneg _)
        (mul_nonneg (hCbd0 T) hCmix0) (le_of_lt hT)
    calc
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selectorMixField branch i)|
          ≤ selectorMixConst branch + selectorMixSlope branch *
              |yt t (selU V i)| := hMixAff i t ht
      _ ≤ selectorMixConst branch + selectorMixSlope branch *
        gronwallBound ‖(y0 (selZ V i), y0 (selU V i))‖
          (Cbd T * (2 + selectorMixSlope branch))
          (Cbd T * selectorMixConst branch) T := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hzu hkmix0) (selectorMixConst branch)
      _ ≤ selectorMixConst branch + selectorMixSlope branch *
          ∑ j : Fin d,
            gronwallBound ‖(y0 (selZ V j), y0 (selU V j))‖
              (Cbd T * (2 + selectorMixSlope branch))
              (Cbd T * selectorMixConst branch) T := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hsum hkmix0) (selectorMixConst branch)
      _ = Mbd T := by
        dsimp [Mbd, selectorMixMbdV2]
        rw [hθT]
        congr 2
  exact ⟨hSelRP, hSelRPderiv, hSelQP, hSelQPderiv, hCoefZ, hCoefU,
    hMixBound, hChiGain T hT yt hyt0 hderiv,
    hCr T hT yt hyt0 hderiv, hcontT, hA T hT yt hyt0 hderiv⟩

theorem chiGate_eval_yt
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP :
      MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R M : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        (yt t)) t)
    (hs0 : yt 0 (selOfContract V (contractS d)) = 0)
    (hc0 : yt 0 (selOfContract V (contractC d)) = 1) :
    ∀ t ∈ Ico (0 : ℝ) T,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selChiGatePoly d V M) =
        ((1 + Real.sin t) / 2) ^ M := by
  intro t ht
  have hsc := sc_realize (branch := branch) (chiResetP := chiResetP)
    (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
    (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
    (cμq := cμq) (cαq := cαq) (L := L) (R := R)
    (yt := yt) (T := T) hderiv hs0 hc0 t ht
  simp only [selChiGatePoly, eval₂_pow, eval₂_mul, eval₂_add,
    eval₂_C, eval₂_X, eval₂_one, map_div₀, map_one, map_ofNat]
  rw [hsc.1]
  ring_nf

theorem chiReset_eval_yt
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP :
      MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R M : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        (yt t)) t)
    (hs0 : yt 0 (selOfContract V (contractS d)) = 0)
    (hc0 : yt 0 (selOfContract V (contractC d)) = 1) :
    ∀ t ∈ Ico (0 : ℝ) T,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
          (selChiResetPoly d V M) =
        ((1 + Real.cos t) / 2) ^ M := by
  intro t ht
  have hsc := sc_realize (branch := branch) (chiResetP := chiResetP)
    (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
    (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
    (cμq := cμq) (cαq := cαq) (L := L) (R := R)
    (yt := yt) (T := T) hderiv hs0 hc0 t ht
  simp only [selChiResetPoly, eval₂_pow, eval₂_mul, eval₂_add,
    eval₂_C, eval₂_X, eval₂_one, map_div₀, map_one, map_ofNat]
  rw [hsc.2]
  ring_nf

theorem kappa_eval_yt
    {d : ℕ} {V : Type} [Fintype V] (κ₀ : ℚ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) (t : ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selKappaPoly d V κ₀) =
      (κ₀ : ℝ) := by
  simp [selKappaPoly]

theorem gain_eval_yt
    {d : ℕ} {V : Type} [Fintype V]
    (yt : ℝ → Fin (selectorDim d V) → ℝ) (t : ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (selGainPoly d V) =
      yt t (selWarmGainCoord d V) * yt t (selOfContract V (contractAlpha d)) := by
  simp [selGainPoly]

open MachineInstance in
theorem muReadoutPoly_eval_yt (eta : ℚ) (heta : 0 < eta)
    (v : UniversalLocalView)
    (yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ) (t : ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
        (muReadoutPoly eta heta v) =
      universalPval eta heta v (fun i => yt t (selU UniversalLocalView i)) := by
  rw [muReadoutPoly, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_rename]
  rw [show ((yt t) ∘ (selU UniversalLocalView))
        = (fun i => yt t (selU UniversalLocalView i)) from rfl]
  rw [MvPolynomial.eval₂_C]
  rw [universalPval, LambdaN, evalPoly4]
  norm_num

open MachineInstance in
noncomputable abbrev selectorMUField
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ) :=
  selectorAssembledVectorField d_U B_U UniversalLocalView branchU
    (selChiResetPoly d_U UniversalLocalView M)
    (selChiGatePoly d_U UniversalLocalView M)
    (selKappaPoly d_U UniversalLocalView κ₀)
    (selGainPoly d_U UniversalLocalView)
    (muReadoutPoly eta heta) HP
    (1 : ℚ) Kq (1 : ℚ) (1 / 4 : ℚ) 1 R

open MachineInstance in
abbrev selectorMUInit
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) (warmGainInit : ℚ) :
    Fin (selectorDim d_U UniversalLocalView) → ℝ :=
  fun i => ((selectorEuclInitQ d_U UniversalLocalView x₀ w warmGainInit i : ℚ) : ℝ)

open MachineInstance in
theorem selector_finiteHorizonBound_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hA : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |yt t (selOfContract UniversalLocalView (contractA d_U))| ≤
            max 0 T + 1) :
    Ripple.FiniteHorizonBound (selectorMUField eta heta M κ₀ g₀ HP Kq R)
      (selectorMUInit x₀ w g₀) := by
  classical
  let Gbd : ℝ → ℝ := fun T => (g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * T)
  let Abd : ℝ → ℝ := fun T => max 0 T + 1
  have hGbdmono : Monotone Gbd := by
    intro S T hST
    dsimp [Gbd]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hST (by norm_num : (0 : ℝ) ≤ 1 / 4)))
      hg0
  have hAbdmono : Monotone Abd := by
    intro S T hST
    dsimp [Abd]
    gcongr
  have hGbd0 : ∀ T : ℝ, 0 ≤ Gbd T := by
    intro T
    exact mul_nonneg hg0 (le_of_lt (Real.exp_pos _))
  have hAbd0 : ∀ T : ℝ, 0 ≤ Abd T := by
    intro T
    dsimp [Abd]
    nlinarith [le_max_left (0 : ℝ) T]
  refine selector_finiteHorizonBound_v2
    (branch := branchU)
    (chiResetP := selChiResetPoly d_U UniversalLocalView M)
    (chiGateP := selChiGatePoly d_U UniversalLocalView M)
    (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
    (gainP := selGainPoly d_U UniversalLocalView)
    (PpolyP := muReadoutPoly eta heta) (HP := HP)
    (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
    (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
    (x₀ := x₀) (w := w) (warmGainInit := g₀) (Gbd := Gbd) (Abd := Abd)
    (hBpos := by norm_num [B_U])
    hGbdmono hAbdmono hGbd0 hAbd0 ?_ ?_ hytcont hA
  · intro T hT yt hyt0 hderiv t ht
    have hs0 : yt 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : yt 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hgate := chiGate_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := yt) (T := T) hderiv hs0 hc0 t ht
    have hgain := gain_eval_yt (d := d_U) (V := UniversalLocalView) yt t
    have halpha := alpha_coord_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
      (yt := yt) (T := T) hderiv t ht
    have hα0 : yt 0 (selOfContract UniversalLocalView (contractAlpha d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractAlpha]
    have hwg : yt t (selWarmGainCoord d_U UniversalLocalView) = (g₀ : ℝ) := by
      have hconst := warmGain_coord_const (branch := branchU)
        (chiResetP := selChiResetPoly d_U UniversalLocalView M)
        (chiGateP := selChiGatePoly d_U UniversalLocalView M)
        (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
        (gainP := selGainPoly d_U UniversalLocalView)
        (PpolyP := muReadoutPoly eta heta) (HP := HP)
        (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
        (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
        (yt := yt) (T := T) hderiv t ht
      rw [hconst, hyt0]
      simp [selectorEuclInitQ, selWarmGainCoord, Fin.append_right]
      rfl
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selChiGatePoly d_U UniversalLocalView M) *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selGainPoly d_U UniversalLocalView) =
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * t)) := by
      rw [hgate, hgain, hwg, halpha, hα0]
      norm_num
    have hq0 : 0 ≤ ((1 + Real.sin t) / 2) ^ M := by
      simpa [qPulse] using qPulse_nonneg M t
    have hq1 : ((1 + Real.sin t) / 2) ^ M ≤ 1 := by
      simpa [qPulse] using qPulse_le_one M t
    rw [heq, abs_of_nonneg
      (mul_nonneg hq0 (mul_nonneg hg0 (le_of_lt (Real.exp_pos _))))]
    calc
      ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * t))
          ≤ 1 * ((g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * t)) := by
            exact mul_le_mul_of_nonneg_right hq1
              (mul_nonneg hg0 (le_of_lt (Real.exp_pos _)))
      _ ≤ (g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * T) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (le_of_lt ht.2)
              (by norm_num : (0 : ℝ) ≤ 1 / 4)))
          hg0
      _ = Gbd T := rfl
  · intro T hT yt hyt0 hderiv t ht
    have hs0 : yt 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : yt 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hreset := chiReset_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := yt) (T := T) hderiv hs0 hc0 t ht
    have hkappa := kappa_eval_yt (d := d_U) (V := UniversalLocalView) κ₀ yt t
    rw [hreset, hkappa]
    exact mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) M) hκ0

/-- Local copy: field at the held contract value `A` is
`K·((1/2)·(1-c))^R·(renameZ - A)`. -/
theorem aprioriField_A_eq :
    selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selOfContract V (contractA d)) =
      (Kq : ℝ) *
        (((1 / 2 : ℝ) *
          (1 - y (selOfContract V (contractC d)))) ^ R) *
        (MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (selRenameZ V HP) -
          y (selOfContract V (contractA d))) := by
  unfold selectorAssembledVectorField
  rw [show selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP
        PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractA d)) =
        C Kq *
          ((C (1 / 2 : ℚ) *
            (1 - X (selOfContract V (contractC d)))) ^ R) *
          (selRenameZ V HP - X (selOfContract V (contractA d))) from by
    simp [selectorAssembledField, selOfContract, contractA, contractTailA]]
  simp [eval₂_mul, eval₂_pow, eval₂_C, eval₂_sub, eval₂_one, eval₂_X,
    eq_ratCast]

/-- The `contractA` coordinate is trapped between exterior barriers around the
bounded renamed target. -/
theorem contractA_coord_abs_bound
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T Rbd : ℝ}
    (hT : 0 < T) (hKq0 : 0 ≤ (Kq : ℝ)) (hytcont : Continuous yt)
    (hyt0 : yt 0 = (fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ)))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        (yt t)) t)
    (hRen : ∀ t ∈ Ico (0 : ℝ) T,
      |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (selRenameZ V HP)| ≤ Rbd) :
    ∀ t ∈ Ico (0 : ℝ) T,
      |yt t (selOfContract V (contractA d))| ≤
        max |yt 0 (selOfContract V (contractA d))| Rbd := by
  classical
  let Acoord := selOfContract V (contractA d)
  let Ccoord := selOfContract V (contractC d)
  let g : ℝ → ℝ := fun s => yt s Acoord
  let q : ℝ → ℝ :=
    fun s => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt s) (selRenameZ V HP)
  let gp : ℝ → ℝ := fun s =>
    (Kq : ℝ) * (((1 / 2 : ℝ) * (1 - yt s Ccoord)) ^ R) * (q s - g s)
  let b : ℝ := max |g 0| Rbd
  have hs0 : yt 0 (selOfContract V (contractS d)) = 0 := by
    rw [hyt0]
    simp [selectorEuclInitQ, selOfContract, contractS]
  have hc0 : yt 0 (selOfContract V (contractC d)) = 1 := by
    rw [hyt0]
    simp [selectorEuclInitQ, selOfContract, contractC]
  have hcont : ContinuousOn g (Icc (0 : ℝ) T) :=
    ((continuous_apply Acoord).comp hytcont).continuousOn
  have hderivWithin :
      ∀ s ∈ Ico (0 : ℝ) T, HasDerivWithinAt g (gp s) (Ici s) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hderiv s hs)) Acoord
    rw [aprioriField_A_eq] at hpi
    have hcoord : HasDerivAt g (gp s) s := by
      simpa [g, gp, q, Acoord, Ccoord] using hpi
    exact hcoord.hasDerivWithinAt
  have hcoef0 : ∀ s ∈ Ico (0 : ℝ) T,
      0 ≤ (Kq : ℝ) * (((1 / 2 : ℝ) * (1 - yt s Ccoord)) ^ R) := by
    intro s hs
    have hsc := sc_realize (branch := branch) (chiResetP := chiResetP)
      (chiGateP := chiGateP) (kappaP := kappaP) (gainP := gainP)
      (PpolyP := PpolyP) (HP := HP) (Aq := Aq) (Kq := Kq)
      (cμq := cμq) (cαq := cαq) (L := L) (R := R)
      (yt := yt) (T := T) hderiv hs0 hc0 s hs
    have hbase0 : 0 ≤ (1 / 2 : ℝ) * (1 - yt s Ccoord) := by
      dsimp [Ccoord]
      rw [hsc.2]
      nlinarith [Real.cos_le_one s]
    exact mul_nonneg hKq0 (pow_nonneg hbase0 R)
  have hg0ub : g 0 ≤ b := (abs_le.mp (le_max_left |g 0| Rbd)).2
  have hg0lb : -b ≤ g 0 := (abs_le.mp (le_max_left |g 0| Rbd)).1
  have hupper := Ripple.scalar_upper_barrier_exterior_on_Icc
    (T := T) (b := b) (le_of_lt hT) g gp hg0ub hcont hderivWithin
    (by
      intro s hs hbg
      have hqle : q s ≤ b :=
        (abs_le.mp (hRen s hs)).2.trans (le_max_right |g 0| Rbd)
      have hdiff : q s - g s ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (hcoef0 s hs) hdiff)
  have hlower := Ripple.scalar_lower_barrier_exterior_on_Icc
    (T := T) (a := -b) (le_of_lt hT) g gp hg0lb hcont hderivWithin
    (by
      intro s hs hgb
      have hqlo : -b ≤ q s := by
        have hq := (abs_le.mp (hRen s hs)).1
        have hbR : Rbd ≤ b := le_max_right |g 0| Rbd
        linarith
      have hdiff : 0 ≤ q s - g s := by linarith
      exact mul_nonneg (hcoef0 s hs) hdiff)
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
  exact abs_le.mpr ⟨by simpa [g, b, Acoord] using hlower t htIcc,
    by simpa [g, b, Acoord] using hupper t htIcc⟩

open MachineInstance in
theorem selector_finiteHorizonBound_MU'
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd) :
    Ripple.FiniteHorizonBound (selectorMUField eta heta M κ₀ g₀ HP Kq R)
      (selectorMUInit x₀ w g₀) := by
  classical
  let Gbd : ℝ → ℝ := fun T => (g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * T)
  let Abd : ℝ → ℝ :=
    fun _ => max |selectorMUInit x₀ w g₀
      (selOfContract UniversalLocalView (contractA d_U))| Rbd
  have hGbdmono : Monotone Gbd := by
    intro S T hST
    dsimp [Gbd]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hST (by norm_num : (0 : ℝ) ≤ 1 / 4)))
      hg0
  have hAbdmono : Monotone Abd := by
    intro S T hST
    dsimp [Abd]
    exact le_rfl
  have hGbd0 : ∀ T : ℝ, 0 ≤ Gbd T := by
    intro T
    exact mul_nonneg hg0 (le_of_lt (Real.exp_pos _))
  have hAbd0 : ∀ T : ℝ, 0 ≤ Abd T := by
    intro T
    dsimp [Abd]
    exact le_trans (abs_nonneg _)
      (le_max_left _ _)
  refine selector_finiteHorizonBound_v2
    (branch := branchU)
    (chiResetP := selChiResetPoly d_U UniversalLocalView M)
    (chiGateP := selChiGatePoly d_U UniversalLocalView M)
    (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
    (gainP := selGainPoly d_U UniversalLocalView)
    (PpolyP := muReadoutPoly eta heta) (HP := HP)
    (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
    (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
    (x₀ := x₀) (w := w) (warmGainInit := g₀) (Gbd := Gbd) (Abd := Abd)
    (hBpos := by norm_num [B_U])
    hGbdmono hAbdmono hGbd0 hAbd0 ?_ ?_ hytcont ?_
  · intro T hT yt hyt0 hderiv t ht
    have hs0 : yt 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : yt 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hgate := chiGate_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := yt) (T := T) hderiv hs0 hc0 t ht
    have hgain := gain_eval_yt (d := d_U) (V := UniversalLocalView) yt t
    have halpha := alpha_coord_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
      (yt := yt) (T := T) hderiv t ht
    have hα0 : yt 0 (selOfContract UniversalLocalView (contractAlpha d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractAlpha]
    have hwg : yt t (selWarmGainCoord d_U UniversalLocalView) = (g₀ : ℝ) := by
      have hconst := warmGain_coord_const (branch := branchU)
        (chiResetP := selChiResetPoly d_U UniversalLocalView M)
        (chiGateP := selChiGatePoly d_U UniversalLocalView M)
        (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
        (gainP := selGainPoly d_U UniversalLocalView)
        (PpolyP := muReadoutPoly eta heta) (HP := HP)
        (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
        (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
        (yt := yt) (T := T) hderiv t ht
      rw [hconst, hyt0]
      simp [selectorEuclInitQ, selWarmGainCoord, Fin.append_right]
      rfl
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selChiGatePoly d_U UniversalLocalView M) *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selGainPoly d_U UniversalLocalView) =
        ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * t)) := by
      rw [hgate, hgain, hwg, halpha, hα0]
      norm_num
    have hq0 : 0 ≤ ((1 + Real.sin t) / 2) ^ M := by
      simpa [qPulse] using qPulse_nonneg M t
    have hq1 : ((1 + Real.sin t) / 2) ^ M ≤ 1 := by
      simpa [qPulse] using qPulse_le_one M t
    rw [heq, abs_of_nonneg
      (mul_nonneg hq0 (mul_nonneg hg0 (le_of_lt (Real.exp_pos _))))]
    calc
      ((1 + Real.sin t) / 2) ^ M *
          ((g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * t))
          ≤ 1 * ((g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * t)) := by
            exact mul_le_mul_of_nonneg_right hq1
              (mul_nonneg hg0 (le_of_lt (Real.exp_pos _)))
      _ ≤ (g₀ : ℝ) * Real.exp ((1 / 4 : ℝ) * T) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (le_of_lt ht.2)
              (by norm_num : (0 : ℝ) ≤ 1 / 4)))
          hg0
      _ = Gbd T := rfl
  · intro T hT yt hyt0 hderiv t ht
    have hs0 : yt 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : yt 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hyt0]
      simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hreset := chiReset_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := yt) (T := T) hderiv hs0 hc0 t ht
    have hkappa := kappa_eval_yt (d := d_U) (V := UniversalLocalView) κ₀ yt t
    rw [hreset, hkappa]
    exact mul_nonneg (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) M) hκ0
  · intro T hT yt hyt0 hderiv t ht
    have hA := contractA_coord_abs_bound
      (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
      (x₀ := x₀) (w := w) (warmGainInit := g₀) (yt := yt) (T := T) (Rbd := Rbd)
      hT hKq0 (hytcont T hT yt hyt0 hderiv) hyt0 hderiv
      (hRen T hT yt hyt0 hderiv) t ht
    rw [hyt0] at hA
    simpa [Abd, selectorMUInit] using hA

open MachineInstance in
theorem selector_sol_exists_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd)
    (hgateZ :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t) :
    ∃ sol : SelectorDynSol d_U B_U UniversalLocalView bgpParams selectorSchedule
        branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (bgpParams.cα * t))
        (universalPval eta heta),
      sol.z 0 = sol.init_z ∧ sol.u 0 = sol.init_u ∧
        (∀ i,
          sol.u 0 i =
            ((selectorEuclInitQ d_U UniversalLocalView x₀ w g₀
              (selU UniversalLocalView i) : ℚ) : ℝ)) ∧
        sol.ZUFiniteCoordBound := by
  classical
  refine selector_sol_exists
    (p := bgpParams) (sched := selectorSchedule) (branch := branchU)
    (chiResetP := selChiResetPoly d_U UniversalLocalView M)
    (chiGateP := selChiGatePoly d_U UniversalLocalView M)
    (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
    (gainP := selGainPoly d_U UniversalLocalView)
    (PpolyP := muReadoutPoly eta heta) (HP := HP)
    (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
    (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
    (hA := by norm_num [bgpParams]) (hcμ := by norm_num [bgpParams])
    (hcα := by norm_num [bgpParams]) (hL := rfl)
    (hdomain_nonneg := by intro t ht; simpa [selectorSchedule] using ht)
    (chiResetF := fun t => ((1 + Real.cos t) / 2) ^ M)
    (chiGateF := fun t => ((1 + Real.sin t) / 2) ^ M)
    (kappaF := fun _ => (κ₀ : ℝ))
    (gainF := fun t => (g₀ : ℝ) * Real.exp (bgpParams.cα * t))
    (readoutP := universalPval eta heta) (x₀ := x₀) (w := w) (warmGainInit := g₀) ?_
    hgateZ hgateU ?_ ?_ ?_ ?_ ?_
  · exact selector_finiteHorizonBound_MU' eta heta M κ₀ g₀ HP Kq R x₀ w
      hκ0 hg0 hKq0 hytcont hRen
  · intro y hy0 hyode t ht
    have hT : 0 < t + 1 := by linarith
    have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    exact chiReset_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) hs0 hc0 t htIco
  · intro y hy0 hyode t ht
    have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    exact chiGate_eval_yt (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R) (M := M)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) hs0 hc0 t htIco
  · intro y _hy0 _hyode t _ht
    exact kappa_eval_yt (d := d_U) (V := UniversalLocalView) κ₀ y t
  · intro y hy0 hyode t ht
    have htIco : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hα0 : y 0 (selOfContract UniversalLocalView (contractAlpha d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractAlpha]
    rw [gain_eval_yt (d := d_U) (V := UniversalLocalView) y t]
    have hwg : y t (selWarmGainCoord d_U UniversalLocalView) = (g₀ : ℝ) := by
      have hconst := warmGain_coord_const (branch := branchU)
        (chiResetP := selChiResetPoly d_U UniversalLocalView M)
        (chiGateP := selChiGatePoly d_U UniversalLocalView M)
        (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
        (gainP := selGainPoly d_U UniversalLocalView)
        (PpolyP := muReadoutPoly eta heta) (HP := HP)
        (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
        (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
        (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) t htIco
      rw [hconst, hy0]
      simp [selectorMUInit, selectorEuclInitQ, selWarmGainCoord, Fin.append_right]
      rfl
    rw [hwg]
    rw [alpha_coord_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP)
      (Aq := (1 : ℚ)) (Kq := Kq) (cμq := (1 : ℚ))
      (cαq := (1 / 4 : ℚ)) (L := 1) (R := R)
      (yt := y) (T := t + 1) (fun s hs => hyode s hs.1) t htIco]
    rw [hα0]
    norm_num [bgpParams]
  · intro y _hy0 _hyode v t _ht
    exact muReadoutPoly_eval_yt eta heta v y t

private theorem selector_gate_exp_unique {n : ℕ}
    (y : ℝ → Fin n → ℝ) (gate μ : Fin n) (pulse pulseDeriv : ℝ → ℝ)
    (hgate0 : y 0 gate = 1) (hμ0 : y 0 μ = 0)
    (hgate : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun τ => y τ gate)
        (-(pulse s + y s μ * pulseDeriv s) * y s gate) s)
    (hμ : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => y τ μ) 1 s)
    (hpulse : ∀ s : ℝ, HasDerivAt pulse (pulseDeriv s) s) :
    ∀ t : ℝ, 0 ≤ t →
      y t gate = Real.exp (-(y t μ * pulse t)) := by
  intro t ht
  let G : ℝ → ℝ := fun s => y s gate * Real.exp (y s μ * pulse s)
  have hGconst := affine_of_const_deriv (T := t + 1) (c := (0 : ℝ)) G ?_
    t ⟨ht, by linarith⟩
  have hG0 : G 0 = 1 := by simp [G, hgate0, hμ0]
  have hGt : G t = 1 := by simpa [hG0] using hGconst
  have hEne : Real.exp (y t μ * pulse t) ≠ 0 := (Real.exp_pos _).ne'
  have hmul :
      y t gate * Real.exp (y t μ * pulse t) =
        Real.exp (-(y t μ * pulse t)) * Real.exp (y t μ * pulse t) := by
    calc
      y t gate * Real.exp (y t μ * pulse t) = 1 := by simpa [G] using hGt
      _ = Real.exp (-(y t μ * pulse t)) * Real.exp (y t μ * pulse t) := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    y t gate = (y t gate * Real.exp (y t μ * pulse t)) /
        Real.exp (y t μ * pulse t) := by field_simp [hEne]
    _ = (Real.exp (-(y t μ * pulse t)) * Real.exp (y t μ * pulse t)) /
        Real.exp (y t μ * pulse t) := by rw [hmul]
    _ = Real.exp (-(y t μ * pulse t)) := by field_simp [hEne]
  · intro s hs
    have hg := hgate s hs.1
    have hprod := (hμ s hs.1).mul (hpulse s)
    have hexp := hprod.exp
    have hG := hg.mul hexp
    convert hG using 1 <;> ring

open MachineInstance in
theorem selector_gateZ_realize
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ)
    (hy0 : y 0 = selectorMUInit x₀ w g₀)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y (selectorMUField eta heta M κ₀ g₀ HP Kq R (y t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
        bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t := by
  let gate := selOfContract UniversalLocalView (contractGateZ d_U)
  let μ := selOfContract UniversalLocalView (contractMu d_U)
  have hgate0 : y 0 gate = 1 := by
    rw [hy0]; simp [gate, selectorMUInit, selectorEuclInitQ, selOfContract, contractGateZ]
  have hμ0 : y 0 μ = 0 := by
    rw [hy0]; simp [μ, selectorMUInit, selectorEuclInitQ, selOfContract, contractMu]
  have hμder : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => y τ μ) 1 s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) μ
    simp only [selectorMUField] at hpi
    rw [aprioriField_mu_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1 : ℚ)) (cαq := (1 / 4 : ℚ))
      (L := 1) (R := R)] at hpi
    simpa [μ] using hpi
  have hpulse : ∀ s : ℝ, HasDerivAt (rPulse 1) (-(Real.cos s / 2)) s := by
    intro s
    unfold rPulse
    have hb : HasDerivAt (fun τ : ℝ => (1 - Real.sin τ) / 2)
        (-(Real.cos s / 2)) s := by
      convert ((hasDerivAt_const (x := s) (c := (1 : ℝ))).sub
        (Real.hasDerivAt_sin s)).div_const 2 using 1 <;> ring
    simpa using hb.pow 1
  have hgateDer : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun τ => y τ gate)
        (-(rPulse 1 s + y s μ * (-(Real.cos s / 2))) * y s gate) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) gate
    simp only [selectorMUField] at hpi
    rw [aprioriField_gateZ_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1 : ℚ)) (cαq := (1 / 4 : ℚ))
      (L := 1) (R := R)] at hpi
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hsc := sc_realize (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1 : ℚ)) (cαq := (1 / 4 : ℚ))
      (L := 1) (R := R) (yt := y) (T := s + 1)
      (fun r hr => hyode r hr.1) hs0 hc0 s ⟨hs, by linarith⟩
    have hrp : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selRP d_U UniversalLocalView 1) = rPulse 1 s := by
      simp [selRP, rPulse, hsc.1]; ring
    have hrpd : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selRPderiv d_U UniversalLocalView 1) = -(Real.cos s / 2) := by
      simp [selRPderiv, hsc.1, hsc.2]; ring
    rw [hrp, hrpd] at hpi
    convert hpi using 1 <;> simp [gate, μ] <;> ring
  intro t ht
  simpa [gate, μ, bGateZ] using
    selector_gate_exp_unique y gate μ (rPulse 1) (fun s => -(Real.cos s / 2))
      hgate0 hμ0 hgateDer hμder hpulse t ht

open MachineInstance in
theorem selector_gateU_realize
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ)
    (hy0 : y 0 = selectorMUInit x₀ w g₀)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y (selectorMUField eta heta M κ₀ g₀ HP Kq R (y t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract UniversalLocalView (contractGateU d_U)) =
        bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t := by
  let gate := selOfContract UniversalLocalView (contractGateU d_U)
  let μ := selOfContract UniversalLocalView (contractMu d_U)
  have hgate0 : y 0 gate = 1 := by
    rw [hy0]; simp [gate, selectorMUInit, selectorEuclInitQ, selOfContract, contractGateU]
  have hμ0 : y 0 μ = 0 := by
    rw [hy0]; simp [μ, selectorMUInit, selectorEuclInitQ, selOfContract, contractMu]
  have hμder : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => y τ μ) 1 s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) μ
    simp only [selectorMUField] at hpi
    rw [aprioriField_mu_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1 : ℚ)) (cαq := (1 / 4 : ℚ))
      (L := 1) (R := R)] at hpi
    simpa [μ] using hpi
  have hpulse : ∀ s : ℝ, HasDerivAt (qPulse 1) (Real.cos s / 2) s := by
    intro s
    unfold qPulse
    have hb : HasDerivAt (fun τ : ℝ => (1 + Real.sin τ) / 2)
        (Real.cos s / 2) s := by
      convert ((hasDerivAt_const (x := s) (c := (1 : ℝ))).add
        (Real.hasDerivAt_sin s)).div_const 2 using 1 <;> ring
    simpa using hb.pow 1
  have hgateDer : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun τ => y τ gate)
        (-(qPulse 1 s + y s μ * (Real.cos s / 2)) * y s gate) s := by
    intro s hs
    have hpi := (hasDerivAt_pi.mp (hyode s hs)) gate
    simp only [selectorMUField] at hpi
    rw [aprioriField_gateU_eq (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1 : ℚ)) (cαq := (1 / 4 : ℚ))
      (L := 1) (R := R)] at hpi
    have hs0 : y 0 (selOfContract UniversalLocalView (contractS d_U)) = 0 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractS]
    have hc0 : y 0 (selOfContract UniversalLocalView (contractC d_U)) = 1 := by
      rw [hy0]; simp [selectorMUInit, selectorEuclInitQ, selOfContract, contractC]
    have hsc := sc_realize (branch := branchU)
      (chiResetP := selChiResetPoly d_U UniversalLocalView M)
      (chiGateP := selChiGatePoly d_U UniversalLocalView M)
      (kappaP := selKappaPoly d_U UniversalLocalView κ₀)
      (gainP := selGainPoly d_U UniversalLocalView)
      (PpolyP := muReadoutPoly eta heta) (HP := HP) (Aq := (1 : ℚ))
      (Kq := Kq) (cμq := (1 : ℚ)) (cαq := (1 / 4 : ℚ))
      (L := 1) (R := R) (yt := y) (T := s + 1)
      (fun r hr => hyode r hr.1) hs0 hc0 s ⟨hs, by linarith⟩
    have hqp : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selQP d_U UniversalLocalView 1) = qPulse 1 s := by
      simp [selQP, qPulse, hsc.1]; ring
    have hqpd : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y s)
        (selQPderiv d_U UniversalLocalView 1) = Real.cos s / 2 := by
      simp [selQPderiv, hsc.1, hsc.2]; ring
    rw [hqp, hqpd] at hpi
    convert hpi using 1 <;> simp [gate, μ] <;> ring
  intro t ht
  simpa [gate, μ, bGateU] using
    selector_gate_exp_unique y gate μ (qPulse 1) (fun s => Real.cos s / 2)
      hgate0 hμ0 hgateDer hμder hpulse t ht

open MachineInstance in
/-- Tightened `selector_sol_exists_MU`: the gate-identification bridges `hgateZ`/`hgateU`
are DISCHARGED via `selector_gateZ_realize`/`selector_gateU_realize` (scalar gate-ODE
uniqueness with init match `contractMu`=0, gate=1, `bGateZ 1 0 0 = 1`), so the concrete
solution-existence carries only trivially-satisfiable residuals (`hκ0`, `hg0`, `hKq0`,
`hytcont`, `hRen`). -/
theorem selector_sol_exists_MU_clean
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ T : ℝ, 0 < T →
      ∀ yt : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        yt 0 = selectorMUInit x₀ w g₀ →
        Ripple.DerivOnIco (selectorMUField eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd) :
    ∃ sol : SelectorDynSol d_U B_U UniversalLocalView bgpParams selectorSchedule
        branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (bgpParams.cα * t))
        (universalPval eta heta),
      sol.z 0 = sol.init_z ∧ sol.u 0 = sol.init_u ∧
        (∀ i,
          sol.u 0 i =
            ((selectorEuclInitQ d_U UniversalLocalView x₀ w g₀
              (selU UniversalLocalView i) : ℚ) : ℝ)) ∧
        sol.ZUFiniteCoordBound :=
  selector_sol_exists_MU eta heta M κ₀ g₀ HP Kq R x₀ w hκ0 hg0 hKq0 hytcont hRen
    (fun y hy0 hyode =>
      selector_gateZ_realize eta heta M κ₀ g₀ HP Kq R x₀ w y hy0 hyode)
    (fun y hy0 hyode =>
      selector_gateU_realize eta heta M κ₀ g₀ HP Kq R x₀ w y hy0 hyode)

end Ripple.BoundedUniversality.BGP
