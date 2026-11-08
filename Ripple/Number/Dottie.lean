/-
  Ripple.Number.Dottie — Stage 1: PIVP + analytic convergence for the Dottie number.

  The Dottie number d ≈ 0.73908513 is the unique real fixed point of cos,
  i.e., the unique solution in [0, 1] of cos(d) = d.

  Stage 1 content (this file):
    - Existence of d via the intermediate value theorem on cos(x) − x.
    - A 3-dim syntactic `PolyPIVP` with state (x, Y, Z), semantically
      (x(t), cos(x(t)), sin(x(t))):
        x' = Y − x
        Y' = Z · (x − Y)                      [= −sin(x)·(Y−x)]
        Z' = Y · (Y − x)                      [=  cos(x)·(Y−x)]
      init x(0) = 0, Y(0) = 1, Z(0) = 0.
    - Scalar vector field `scalarField x = cos x − x` with Lipschitz
      constant 2 globally (via `lipschitzWith_of_nnnorm_deriv_le`).
    - The full analytic convergence theorem
      `dottie_convergence_of_solution`: any function `x : ℝ → ℝ` that
      satisfies the scalar ODE `x' = cos(x) − x`, has `x(0) = 0`, and is
      confined to `[0, d]`, obeys `|x(t) − d| ≤ d · e^{−t}`.
    - The upper-bound invariance `scalar_le_dottie` proved via ODE
      uniqueness (`ODE_solution_unique_of_mem_Icc_right`) against the
      constant solution `d̄`.
    - The lower-bound invariance `scalar_nonneg` proved via a last-zero
      MVT argument.
    - Global existence of the scalar solution on `[0, ∞)` via
      `Ripple.scalar_global_existence`, with the bound `|y(t)| ≤ 1`
      coming from `0 ≤ y(t) ≤ dottieNumber < 1`.
    - The lift of the scalar solution to a 3-dim trajectory
      `α(t) = (x(t), cos(x(t)), sin(x(t)))` of `dottiePolyPIVP`.
    - Packaging as `SemanticBTC 3 dottieNumber` backed by the
      ACTUAL non-constant trajectory of `dottiePolyPIVP` starting at
      `(0, 1, 0)`, with modulus `μ(r) = r + 1` from the convergence
      bound `|x(t) − d| ≤ d · e^{−t} ≤ e^{−t}`.
-/

import Ripple.Core.BoundedTime
import Ripple.Core.GlobalPicard
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real.Pi.Bounds

namespace Ripple.Number

open Real Set

/-! ## The Dottie number -/

/-- `cos(x) − x`, as a real-valued function. -/
private noncomputable def cosSubId : ℝ → ℝ := fun x => Real.cos x - x

private lemma cosSubId_continuous : Continuous cosSubId := by
  unfold cosSubId
  exact Real.continuous_cos.sub continuous_id

private lemma cosSubId_zero : cosSubId 0 = 1 := by
  simp [cosSubId]

private lemma cosSubId_one_neg : cosSubId 1 < 0 := by
  unfold cosSubId
  have h : Real.cos 1 ≤ 5 / 9 := Real.cos_one_le
  linarith

/-- `cos` has a fixed point in `(0, 1)`. -/
private lemma exists_cos_fixed :
    ∃ d ∈ Ioo (0 : ℝ) 1, Real.cos d = d := by
  have hcont : ContinuousOn cosSubId (Icc (0 : ℝ) 1) :=
    cosSubId_continuous.continuousOn
  obtain ⟨d, hd, hfd⟩ :=
    intermediate_value_Ioo' (le_of_lt zero_lt_one) hcont
      (show (0 : ℝ) ∈ Ioo (cosSubId 1) (cosSubId 0) by
        refine ⟨cosSubId_one_neg, ?_⟩
        simp [cosSubId_zero])
  refine ⟨d, hd, ?_⟩
  have : Real.cos d - d = 0 := hfd
  linarith

/-- The Dottie number: the unique real fixed point of cos in `(0, 1)`. -/
noncomputable def dottieNumber : ℝ := (exists_cos_fixed).choose

lemma dottieNumber_mem_Ioo : dottieNumber ∈ Ioo (0 : ℝ) 1 :=
  (exists_cos_fixed).choose_spec.1

lemma cos_dottieNumber : Real.cos dottieNumber = dottieNumber :=
  (exists_cos_fixed).choose_spec.2

lemma dottieNumber_pos : 0 < dottieNumber := dottieNumber_mem_Ioo.1

lemma dottieNumber_lt_one : dottieNumber < 1 := dottieNumber_mem_Ioo.2

lemma dottieNumber_nonneg : 0 ≤ dottieNumber := le_of_lt dottieNumber_pos

lemma dottieNumber_le_one : dottieNumber ≤ 1 := le_of_lt dottieNumber_lt_one

/-! ## The PIVP

  Dimension 3 with state `(x, Y, Z)`:
    x' = Y − x
    Y' = Z · (x − Y) = Z·x − Z·Y       -- −sin(x)·(Y−x)
    Z' = Y · (Y − x) = Y·Y − Y·x       --  cos(x)·(Y−x)
  Initial condition `x(0) = 0, Y(0) = 1, Z(0) = 0`.
-/

open MvPolynomial in
/-- The syntactic polynomial PIVP for the Dottie number. -/
noncomputable def dottiePolyPIVP : Ripple.PolyPIVP 3 where
  field := fun i =>
    match i with
    | ⟨0, _⟩ => X (1 : Fin 3) - X 0
    | ⟨1, _⟩ => X 2 * X 0 - X 2 * X 1
    | ⟨2, _⟩ => X 1 * X 1 - X 1 * X 0
    | ⟨n+3, hn⟩ => absurd hn (by omega)
  init := ![0, 1, 0]
  output := 0

/-- The semantic PIVP obtained from `dottiePolyPIVP`. -/
noncomputable def dottiePIVP : Ripple.PIVP 3 := dottiePolyPIVP.toPIVP

/-! ## The scalar ODE  x' = cos(x) − x , x(0) = 0 -/

/-- Scalar vector field `v(x) = cos(x) − x`. -/
noncomputable def scalarField : ℝ → ℝ := fun x => Real.cos x - x

lemma scalarField_zero : scalarField 0 = 1 := by
  simp [scalarField]

lemma scalarField_dottie : scalarField dottieNumber = 0 := by
  simp [scalarField, cos_dottieNumber, sub_self]

lemma scalarField_continuous : Continuous scalarField := by
  unfold scalarField
  exact Real.continuous_cos.sub continuous_id

lemma scalarField_hasDerivAt (x : ℝ) :
    HasDerivAt scalarField (-Real.sin x - 1) x := by
  unfold scalarField
  have hc : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
  have hi : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id x
  exact hc.sub hi

lemma differentiable_scalarField : Differentiable ℝ scalarField := by
  unfold scalarField
  exact Real.differentiable_cos.sub differentiable_id

/-- `scalarField` is globally Lipschitz with constant 2. -/
lemma lipschitzWith_scalarField :
    LipschitzWith 2 scalarField := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_scalarField
  intro x
  have hderiv : deriv scalarField x = -Real.sin x - 1 :=
    (scalarField_hasDerivAt x).deriv
  rw [hderiv]
  have hbound : ‖-Real.sin x - 1‖ ≤ (2 : ℝ) := by
    rw [Real.norm_eq_abs]
    have h1 : |-Real.sin x - 1| = |Real.sin x + 1| := by
      rw [abs_sub_comm]; ring_nf
    rw [h1]
    have h2 : |Real.sin x + 1| ≤ |Real.sin x| + 1 := by
      calc |Real.sin x + 1|
          ≤ |Real.sin x| + |(1 : ℝ)| := abs_add_le _ _
        _ = |Real.sin x| + 1 := by rw [abs_one]
    have h3 : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
    linarith
  have h2 : (‖-Real.sin x - 1‖₊ : ℝ) ≤ 2 := by
    rw [coe_nnnorm]; exact hbound
  have h3 : ‖-Real.sin x - 1‖₊ ≤ (2 : NNReal) := by exact_mod_cast h2
  exact h3

/-! ## Analytic convergence -/

/-- The key pointwise MVT bound: for `y ∈ [0, dottieNumber]`,
`cos y - y ≥ dottieNumber - y`. -/
lemma cos_sub_id_ge_dottie_sub (y : ℝ) (hy0 : 0 ≤ y) (hyd : y ≤ dottieNumber) :
    dottieNumber - y ≤ Real.cos y - y := by
  suffices h : dottieNumber ≤ Real.cos y by linarith
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hd1 : dottieNumber ≤ 1 := dottieNumber_le_one
  have hcos_mono : Real.cos dottieNumber ≤ Real.cos y := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi hy0 ?_ hyd
    linarith
  rw [cos_dottieNumber] at hcos_mono
  exact hcos_mono

/-- The analytic convergence theorem for the Dottie ODE. -/
theorem dottie_convergence_of_solution
    {x : ℝ → ℝ}
    (hx0 : x 0 = 0)
    (hxlo : ∀ t : ℝ, 0 ≤ t → 0 ≤ x t)
    (hxhi : ∀ t : ℝ, 0 ≤ t → x t ≤ dottieNumber)
    (hxdiff : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (Real.cos (x t) - x t) t)
    (t : ℝ) (ht : 0 ≤ t) :
    |x t - dottieNumber| ≤ dottieNumber * Real.exp (-t) := by
  set h : ℝ → ℝ := fun s => Real.exp s * (dottieNumber - x s) with hh_def
  have h_deriv : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt h
        (Real.exp s * ((dottieNumber - x s) - (Real.cos (x s) - x s))) s := by
    intro s hs
    have hexp : HasDerivAt Real.exp (Real.exp s) s := Real.hasDerivAt_exp s
    have hu : HasDerivAt (fun r : ℝ => dottieNumber - x r)
        (-(Real.cos (x s) - x s)) s := by
      have := (hxdiff s hs).const_sub dottieNumber
      simpa using this
    have := hexp.mul hu
    convert this using 1
    ring
  have h_deriv_nonpos : ∀ s : ℝ, 0 ≤ s →
      Real.exp s * ((dottieNumber - x s) - (Real.cos (x s) - x s)) ≤ 0 := by
    intro s hs
    have hxs_nn : 0 ≤ x s := hxlo s hs
    have hxs_le : x s ≤ dottieNumber := hxhi s hs
    have hmvt : dottieNumber - x s ≤ Real.cos (x s) - x s :=
      cos_sub_id_ge_dottie_sub (x s) hxs_nn hxs_le
    nlinarith [Real.exp_pos s]
  have h_mono : h t ≤ h 0 := by
    have hcont : ContinuousOn h (Icc 0 t) := by
      intro s hs
      exact (h_deriv s hs.1).continuousAt.continuousWithinAt
    have hint : interior (Icc (0 : ℝ) t) = Ioo 0 t := interior_Icc
    have hderiv_within : ∀ s ∈ interior (Icc (0 : ℝ) t),
        HasDerivWithinAt h
          (Real.exp s * ((dottieNumber - x s) - (Real.cos (x s) - x s)))
          (interior (Icc (0 : ℝ) t)) s := by
      intro s hs
      rw [hint] at hs
      exact (h_deriv s (le_of_lt hs.1)).hasDerivWithinAt
    have hle : ∀ s ∈ interior (Icc (0 : ℝ) t),
        Real.exp s * ((dottieNumber - x s) - (Real.cos (x s) - x s)) ≤ 0 := by
      intro s hs
      rw [hint] at hs
      exact h_deriv_nonpos s (le_of_lt hs.1)
    have hmono := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
      hcont hderiv_within hle
    exact hmono ⟨le_refl _, ht⟩ ⟨ht, le_refl _⟩ ht
  have h_zero : h 0 = dottieNumber := by
    simp [hh_def, hx0, Real.exp_zero]
  have hx_le : x t ≤ dottieNumber := hxhi t ht
  have hexp_pos : 0 < Real.exp t := Real.exp_pos t
  have h_bound : dottieNumber - x t ≤ dottieNumber * Real.exp (-t) := by
    have h1 : Real.exp t * (dottieNumber - x t) ≤ dottieNumber := by
      rw [h_zero] at h_mono; exact h_mono
    have h2 : dottieNumber - x t ≤ dottieNumber / Real.exp t := by
      rw [le_div_iff₀ hexp_pos]; linarith [mul_comm (Real.exp t) (dottieNumber - x t)]
    have h3 : dottieNumber / Real.exp t = dottieNumber * Real.exp (-t) := by
      rw [Real.exp_neg]; ring
    linarith
  have h_abs : |x t - dottieNumber| = dottieNumber - x t := by
    rw [abs_of_nonpos (by linarith : x t - dottieNumber ≤ 0)]
    ring
  rw [h_abs]; exact h_bound

/-! ## Scalar invariance via ODE uniqueness

  Upper bound:  any scalar solution of `y' = cos(y) - y` with `y(0) = 0`
  stays below `dottieNumber`, via ODE uniqueness against the constant
  solution `d̄(t) = dottieNumber`.
-/

/-- Upper bound invariance for the scalar Dottie ODE. -/
private lemma scalar_le_dottie
    {y : ℝ → ℝ} {T : ℝ}
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (Real.cos (y t) - y t) t) :
    ∀ t ∈ Ico (0 : ℝ) T, y t ≤ dottieNumber := by
  intro t ht
  by_contra hcontra
  push_neg at hcontra
  have hy_cont_Icc : ContinuousOn y (Icc 0 t) := by
    intro s hs
    have hsT : s < T := lt_of_le_of_lt hs.2 ht.2
    exact (hy_deriv s ⟨hs.1, hsT⟩).continuousAt.continuousWithinAt
  have h0_le_t : (0 : ℝ) ≤ t := ht.1
  have h_ivt : ∃ t₁ ∈ Icc (0 : ℝ) t, y t₁ = dottieNumber := by
    have hmem : dottieNumber ∈ Icc (y 0) (y t) := by
      rw [hy0]; exact ⟨dottieNumber_nonneg, le_of_lt hcontra⟩
    exact intermediate_value_Icc h0_le_t hy_cont_Icc hmem
  obtain ⟨t₁, ht₁_mem, ht₁_eq⟩ := h_ivt
  have ht₁_nn : 0 ≤ t₁ := ht₁_mem.1
  have ht₁_le : t₁ ≤ t := ht₁_mem.2
  set v : ℝ → ℝ → ℝ := fun _ y => Real.cos y - y
  have hv_lip : ∀ τ : ℝ, LipschitzWith 2 (v τ) := fun _ => lipschitzWith_scalarField
  have hy_ode : ∀ τ ∈ Ico t₁ t,
      HasDerivWithinAt y (v τ (y τ)) (Ici τ) τ := by
    intro τ hτ
    have hτ_mem : τ ∈ Ico (0 : ℝ) T :=
      ⟨le_trans ht₁_nn hτ.1, lt_of_lt_of_le hτ.2 (le_of_lt ht.2)⟩
    exact (hy_deriv τ hτ_mem).hasDerivWithinAt
  have hy_cont_Icc_t₁t : ContinuousOn y (Icc t₁ t) :=
    hy_cont_Icc.mono (Icc_subset_Icc ht₁_nn (le_refl _))
  let dBar : ℝ → ℝ := fun _ => dottieNumber
  have hdBar_cont : ContinuousOn dBar (Icc t₁ t) := continuousOn_const
  have hdBar_ode : ∀ τ ∈ Ico t₁ t,
      HasDerivWithinAt dBar (v τ (dBar τ)) (Ici τ) τ := by
    intro τ _
    have h1 : HasDerivAt dBar 0 τ := hasDerivAt_const τ dottieNumber
    have h2 : v τ (dBar τ) = 0 := by
      show Real.cos dottieNumber - dottieNumber = 0
      rw [cos_dottieNumber]; ring
    rw [h2]
    exact h1.hasDerivWithinAt
  have h_eq : EqOn y dBar (Icc t₁ t) :=
    ODE_solution_unique_of_mem_Icc_right
      (K := 2) (v := v) (s := fun _ => univ)
      (fun τ _ => (hv_lip τ).lipschitzOnWith)
      hy_cont_Icc_t₁t hy_ode (fun _ _ => trivial)
      hdBar_cont hdBar_ode (fun _ _ => trivial) ht₁_eq
  have : y t = dottieNumber := h_eq (right_mem_Icc.mpr ht₁_le)
  linarith

/-- Lower bound: any scalar solution of `y' = cos(y) - y` with `y(0) = 0`
stays above `0`.  Proof: consider the last zero of `y` in `[0, t₀]`;
at that point the derivative is `1 > 0`, forcing `y > 0` just afterwards,
contradicting the assumption that `y(t₀) < 0` (which would place the last
zero strictly before `t₀`). -/
private lemma scalar_nonneg
    {y : ℝ → ℝ} {T : ℝ}
    (hy0 : y 0 = 0)
    (hy_deriv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt y (Real.cos (y t) - y t) t) :
    ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ y t := by
  intro t₀ ht₀
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : y t₀ < 0
  have hy_cont_Icc : ContinuousOn y (Icc 0 t₀) := by
    intro s hs
    have hsT : s < T := lt_of_le_of_lt hs.2 ht₀.2
    exact (hy_deriv s ⟨hs.1, hsT⟩).continuousAt.continuousWithinAt
  -- The set Z := {s ∈ [0, t₀] | y s = 0} is closed, nonempty (contains 0), and bounded.
  -- Let t₁ := sup Z ≤ t₀; by continuity y t₁ = 0.
  -- Since y t₀ < 0, t₁ < t₀.  On (t₁, t₀], y ≠ 0 (by definition of sup Z), and by
  -- continuity + y t₀ < 0, y < 0 on (t₁, t₀].  But y'(t₁) = cos(0) - 0 = 1 > 0 and
  -- y(t₁) = 0, so for small s > t₁, y(s) > 0, contradiction.
  set Z : Set ℝ := {s | s ∈ Icc (0 : ℝ) t₀ ∧ y s = 0} with hZ_def
  have hZ_nonempty : (0 : ℝ) ∈ Z := ⟨⟨le_refl _, ht₀.1⟩, hy0⟩
  have hZ_bdd : BddAbove Z := ⟨t₀, fun s hs => hs.1.2⟩
  have hZ_closed : IsClosed Z := by
    have h1 : IsClosed (Icc (0 : ℝ) t₀) := isClosed_Icc
    have h_pre : IsClosed (Icc (0 : ℝ) t₀ ∩ y ⁻¹' {0}) :=
      hy_cont_Icc.preimage_isClosed_of_isClosed h1 isClosed_singleton
    have hset : Z = Icc (0 : ℝ) t₀ ∩ y ⁻¹' {0} := by
      ext s
      constructor
      · rintro ⟨hmem, heq⟩
        exact ⟨hmem, heq⟩
      · rintro ⟨hmem, heq⟩
        exact ⟨hmem, heq⟩
    rw [hset]; exact h_pre
  set t₁ := sSup Z with ht₁_def
  have ht₁_mem_Z : t₁ ∈ Z := by
    exact hZ_closed.csSup_mem ⟨0, hZ_nonempty⟩ hZ_bdd
  have ht₁_nn : 0 ≤ t₁ := ht₁_mem_Z.1.1
  have ht₁_le : t₁ ≤ t₀ := ht₁_mem_Z.1.2
  have ht₁_y_zero : y t₁ = 0 := ht₁_mem_Z.2
  -- t₁ < t₀ because y t₀ ≠ 0
  have ht₁_lt : t₁ < t₀ := by
    rcases lt_or_eq_of_le ht₁_le with h | h
    · exact h
    · exfalso; rw [← h] at hcontra; linarith [ht₁_y_zero]
  -- t₁ < T (since t₀ < T)
  have ht₁_lt_T : t₁ < T := lt_of_le_of_lt ht₁_le ht₀.2
  -- y'(t₁) = cos(0) - 0 = 1
  have hy_deriv_at_t₁ : HasDerivAt y 1 t₁ := by
    have := hy_deriv t₁ ⟨ht₁_nn, ht₁_lt_T⟩
    rw [ht₁_y_zero] at this
    simpa using this
  -- Use the IsLittleO characterization of HasDerivAt:
  -- y(t₁ + h) - y t₁ - h = o(h)  as  h → 0.
  -- So there exists δ > 0 s.t. for |h| < δ, |y(t₁+h) - h| ≤ h/2,
  -- hence for 0 < h < δ, y(t₁+h) ≥ h/2 > 0.
  have h_lilo : (fun h : ℝ => y (t₁ + h) - y t₁ - h • (1 : ℝ)) =o[nhds 0] (fun h => h) :=
    hasDerivAt_iff_isLittleO_nhds_zero.mp hy_deriv_at_t₁
  have h_lilo' : ∀ᶠ h : ℝ in nhds 0, ‖y (t₁ + h) - y t₁ - h • (1:ℝ)‖ ≤ (1/2 : ℝ) * ‖h‖ :=
    h_lilo.def (half_pos one_pos)
  -- Simplify to real-valued form
  have h_bound : ∀ᶠ h : ℝ in nhds 0, |y (t₁ + h) - h| ≤ (1/2 : ℝ) * |h| := by
    filter_upwards [h_lilo'] with h hh
    rw [ht₁_y_zero, sub_zero] at hh
    simp only [smul_eq_mul, mul_one, Real.norm_eq_abs] at hh
    exact hh
  -- Pick h ∈ (0, min δ (t₀ - t₁)), giving y(t₁ + h) ≥ h/2 > 0
  have h_pos_after : ∃ s ∈ Ioc t₁ t₀, 0 < y s := by
    -- Convert the eventually statement to an existence of δ > 0
    rw [Metric.eventually_nhds_iff_ball] at h_bound
    obtain ⟨δ, hδ_pos, hδ⟩ := h_bound
    -- Pick h = min(δ/2, (t₀ - t₁)/2)
    let h₀ : ℝ := min (δ / 2) ((t₀ - t₁) / 2)
    have hh₀_pos : 0 < h₀ := by
      apply lt_min (by linarith) (by linarith)
    have hh₀_lt_δ : h₀ < δ := by
      have := min_le_left (δ / 2) ((t₀ - t₁) / 2)
      linarith
    have hh₀_le_diff : h₀ ≤ t₀ - t₁ := by
      have := min_le_right (δ / 2) ((t₀ - t₁) / 2)
      linarith
    have hh₀_in_ball : h₀ ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hh₀_pos]
      exact hh₀_lt_δ
    have h_est : |y (t₁ + h₀) - h₀| ≤ (1/2) * |h₀| := hδ h₀ hh₀_in_ball
    rw [abs_of_pos hh₀_pos] at h_est
    have hy_lower : h₀ / 2 ≤ y (t₁ + h₀) := by
      have := abs_sub_abs_le_abs_sub (y (t₁ + h₀)) h₀
      -- |y(t₁+h₀) - h₀| ≤ h₀/2 ⇒ y(t₁+h₀) ≥ h₀ - h₀/2 = h₀/2
      have h1 : -(1/2 * h₀) ≤ y (t₁ + h₀) - h₀ ∧ y (t₁ + h₀) - h₀ ≤ 1/2 * h₀ := by
        constructor
        · linarith [abs_le.mp h_est |>.1]
        · linarith [abs_le.mp h_est |>.2]
      linarith [h1.1]
    have hy_pos : 0 < y (t₁ + h₀) := lt_of_lt_of_le (by linarith) hy_lower
    refine ⟨t₁ + h₀, ⟨by linarith, by linarith⟩, hy_pos⟩
  -- But y < 0 on (t₁, t₀] (from sup Z = t₁ and continuity + y t₀ < 0).
  obtain ⟨s, hs_mem, hs_pos⟩ := h_pos_after
  -- We need to show s ∈ (t₁, t₀] ⇒ y s ≤ 0, then contradict with y s > 0.
  -- Claim: ∀ s ∈ Ioc t₁ t₀, y s < 0.  Proof: by contradiction, suppose some s ∈ (t₁, t₀] has y s ≥ 0.
  -- Case y s = 0: then s ∈ Z and s > t₁ = sSup Z, contradiction.
  -- Case y s > 0: then by IVT on [s, t₀] (y(s) > 0, y(t₀) < 0) there's s' ∈ (s, t₀) with y s' = 0,
  -- so s' ∈ Z and s' > t₁ = sSup Z, contradiction.
  have hy_neg_after : ∀ s ∈ Ioc t₁ t₀, y s < 0 := by
    intro s hs
    by_contra h_nonneg
    push_neg at h_nonneg
    rcases lt_or_eq_of_le h_nonneg with h_pos | h_zero
    · -- y s > 0. IVT on [s, t₀] gives s' ∈ [s, t₀] with y s' = 0.
      have hs_nn : 0 ≤ s := le_trans ht₁_nn (le_of_lt hs.1)
      have hs_le : s ≤ t₀ := hs.2
      have hy_cont_s_t₀ : ContinuousOn y (Icc s t₀) :=
        hy_cont_Icc.mono (Icc_subset_Icc hs_nn (le_refl _))
      have h_mem : (0 : ℝ) ∈ Icc (y t₀) (y s) := ⟨le_of_lt hcontra, le_of_lt h_pos⟩
      obtain ⟨s', hs'_mem, hs'_eq⟩ := intermediate_value_Icc' hs_le hy_cont_s_t₀ h_mem
      have hs'_in_Z : s' ∈ Z :=
        ⟨⟨le_trans hs_nn hs'_mem.1, hs'_mem.2⟩, hs'_eq⟩
      have hs'_gt_t₁ : t₁ < s' := lt_of_lt_of_le hs.1 hs'_mem.1
      have : s' ≤ t₁ := le_csSup hZ_bdd hs'_in_Z
      linarith
    · -- y s = 0, so s ∈ Z but s > t₁ = sSup Z.
      have : s ∈ Z := ⟨⟨le_trans ht₁_nn (le_of_lt hs.1), hs.2⟩, h_zero.symm⟩
      have : s ≤ t₁ := le_csSup hZ_bdd this
      linarith [hs.1]
  have := hy_neg_after s hs_mem
  linarith

/-! ## Global existence of the scalar Dottie ODE solution

  We apply `scalar_global_existence` with `M = 1` and the invariance
  lemmas `scalar_le_dottie` and `scalar_nonneg` (combined with
  `dottieNumber < 1`) to produce a continuous global solution.
-/

/-- The scalar Dottie ODE has a continuous global solution starting at 0. -/
lemma exists_scalar_dottie_solution :
    ∃ x : ℝ → ℝ, x 0 = 0 ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt x (Real.cos (x t) - x t) t) ∧
      Continuous x := by
  have h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ a b : ℝ,
      |a| ≤ R → |b| ≤ R → |scalarField a - scalarField b| ≤ L * |a - b| := by
    intro R _hR
    refine ⟨2, ?_⟩
    intro a b _ha _hb
    have := lipschitzWith_scalarField.dist_le_mul a b
    simp only [Real.dist_eq] at this
    have h2 : (↑(2 : NNReal) : ℝ) = 2 := by norm_num
    rw [h2] at this
    linarith [this]
  have h_M : (0 : ℝ) < 1 := one_pos
  have h_invariant : ∀ (T : ℝ), 0 < T → ∀ (x : ℝ → ℝ),
      x 0 = 0 →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivAt x (scalarField (x t)) t) →
      ∀ t ∈ Ico (0 : ℝ) T, |x t| ≤ 1 := by
    intro T hT x hx0 hx_deriv t ht
    have hx_deriv' : ∀ s ∈ Ico (0 : ℝ) T, HasDerivAt x (Real.cos (x s) - x s) s :=
      hx_deriv
    have hx_lo : 0 ≤ x t := scalar_nonneg hx0 hx_deriv' t ht
    have hx_hi : x t ≤ dottieNumber := scalar_le_dottie hx0 hx_deriv' t ht
    have hx_hi1 : x t ≤ 1 := le_trans hx_hi dottieNumber_le_one
    rw [abs_of_nonneg hx_lo]
    exact hx_hi1
  obtain ⟨x, hx0, hx_deriv, hx_cont⟩ :=
    Ripple.scalar_global_existence scalarField 0 h_lip 1 h_M h_invariant
  refine ⟨x, hx0, ?_, hx_cont⟩
  intro t ht
  have := hx_deriv t ht
  show HasDerivAt x (Real.cos (x t) - x t) t
  exact this

/-! ## Lift to 3-dim trajectory and package `SemanticBTC` -/

noncomputable def dottieScalarSol : ℝ → ℝ :=
  (exists_scalar_dottie_solution).choose

lemma dottieScalarSol_zero : dottieScalarSol 0 = 0 :=
  (exists_scalar_dottie_solution).choose_spec.1

lemma dottieScalarSol_hasDerivAt : ∀ t : ℝ, 0 ≤ t →
    HasDerivAt dottieScalarSol
      (Real.cos (dottieScalarSol t) - dottieScalarSol t) t :=
  (exists_scalar_dottie_solution).choose_spec.2.1

lemma dottieScalarSol_continuous : Continuous dottieScalarSol :=
  (exists_scalar_dottie_solution).choose_spec.2.2

/-- For every `t ≥ 0`, the scalar Dottie solution stays in `[0, dottieNumber]`. -/
lemma dottieScalarSol_bounds (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ dottieScalarSol t ∧ dottieScalarSol t ≤ dottieNumber := by
  -- Apply invariance lemmas with T = t + 1
  have hT_pos : (0 : ℝ) < t + 1 := by linarith
  have ht_mem : t ∈ Ico (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hderiv_Ico : ∀ s ∈ Ico (0 : ℝ) (t + 1),
      HasDerivAt dottieScalarSol
        (Real.cos (dottieScalarSol s) - dottieScalarSol s) s := fun s hs =>
    dottieScalarSol_hasDerivAt s hs.1
  refine ⟨?_, ?_⟩
  · exact scalar_nonneg dottieScalarSol_zero hderiv_Ico t ht_mem
  · exact scalar_le_dottie dottieScalarSol_zero hderiv_Ico t ht_mem

/-- The 3-dim trajectory `α(t) = (x(t), cos(x(t)), sin(x(t)))`. -/
noncomputable def dottieTrajectory : ℝ → Fin 3 → ℝ := fun t =>
  ![dottieScalarSol t, Real.cos (dottieScalarSol t), Real.sin (dottieScalarSol t)]

lemma dottieTrajectory_zero :
    dottieTrajectory 0 = ![0, 1, 0] := by
  unfold dottieTrajectory
  rw [dottieScalarSol_zero, Real.cos_zero, Real.sin_zero]

/-- The 3-dim trajectory satisfies the `dottiePolyPIVP` ODE. -/
lemma dottieTrajectory_hasDerivAt (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt dottieTrajectory
      (dottiePIVP.field (dottieTrajectory t)) t := by
  -- Each coordinate: use hasDerivAt_pi.
  apply hasDerivAt_pi.mpr
  intro i
  -- Abbreviate
  have hx_deriv := dottieScalarSol_hasDerivAt t ht
  set x := dottieScalarSol t with hx_def
  -- The field values:
  -- field 0 = Y - x = cos(x) - x  (this matches x' by definition)
  -- field 1 = Z * x - Z * Y = sin(x) * x - sin(x) * cos(x)
  -- field 2 = Y * Y - Y * x = cos(x)² - cos(x) * x
  -- Coordinate 0: d/dt x = cos(x) - x ✓
  -- Coordinate 1: d/dt cos(x) = -sin(x) * x' = -sin(x) * (cos(x) - x) = sin(x)*x - sin(x)*cos(x) ✓
  -- Coordinate 2: d/dt sin(x) = cos(x) * x' = cos(x) * (cos(x) - x) = cos(x)² - cos(x)*x ✓
  fin_cases i
  · -- i = 0
    show HasDerivAt (fun s => dottieTrajectory s 0)
      (dottiePIVP.field (dottieTrajectory t) 0) t
    have hfield : dottiePIVP.field (dottieTrajectory t) 0 =
        Real.cos x - x := by
      show dottiePolyPIVP.evalField (dottieTrajectory t) 0 = Real.cos x - x
      unfold PolyPIVP.evalField
      simp [dottiePolyPIVP, dottieTrajectory, hx_def]
    rw [hfield]
    show HasDerivAt (fun s => dottieTrajectory s 0) (Real.cos x - x) t
    have : (fun s => dottieTrajectory s 0) = dottieScalarSol := by
      ext s; simp [dottieTrajectory]
    rw [this]
    exact hx_deriv
  · -- i = 1: d/dt cos(x) = -sin(x) * x'
    show HasDerivAt (fun s => dottieTrajectory s 1)
      (dottiePIVP.field (dottieTrajectory t) 1) t
    have hfield : dottiePIVP.field (dottieTrajectory t) 1 =
        Real.sin x * x - Real.sin x * Real.cos x := by
      show dottiePolyPIVP.evalField (dottieTrajectory t) 1 =
        Real.sin x * x - Real.sin x * Real.cos x
      unfold PolyPIVP.evalField
      simp [dottiePolyPIVP, dottieTrajectory, hx_def]
    rw [hfield]
    have h1 : HasDerivAt (fun s => Real.cos (dottieScalarSol s))
        (-Real.sin x * (Real.cos x - x)) t := by
      have hcos : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
      exact hcos.comp t hx_deriv
    have this_eq : (fun s => dottieTrajectory s 1) =
        (fun s => Real.cos (dottieScalarSol s)) := by
      ext s; simp [dottieTrajectory]
    rw [this_eq]
    convert h1 using 1
    ring
  · -- i = 2: d/dt sin(x) = cos(x) * x'
    show HasDerivAt (fun s => dottieTrajectory s 2)
      (dottiePIVP.field (dottieTrajectory t) 2) t
    have hfield : dottiePIVP.field (dottieTrajectory t) 2 =
        Real.cos x * Real.cos x - Real.cos x * x := by
      show dottiePolyPIVP.evalField (dottieTrajectory t) 2 =
        Real.cos x * Real.cos x - Real.cos x * x
      unfold PolyPIVP.evalField
      simp [dottiePolyPIVP, dottieTrajectory, hx_def]
    rw [hfield]
    have h1 : HasDerivAt (fun s => Real.sin (dottieScalarSol s))
        (Real.cos x * (Real.cos x - x)) t := by
      have hsin : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
      exact hsin.comp t hx_deriv
    have this_eq : (fun s => dottieTrajectory s 2) =
        (fun s => Real.sin (dottieScalarSol s)) := by
      ext s; simp [dottieTrajectory]
    rw [this_eq]
    convert h1 using 1
    ring

/-- The trajectory is bounded (by 1 in sup norm). -/
lemma dottieTrajectory_bounded :
    dottiePIVP.IsBounded dottieTrajectory := by
  refine ⟨2, by norm_num, ?_⟩
  intro t ht
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  intro i
  unfold dottieTrajectory
  fin_cases i
  · simp [Real.norm_eq_abs]
    have hbounds := dottieScalarSol_bounds t ht
    rw [abs_of_nonneg hbounds.1]
    linarith [dottieNumber_le_one]
  · simp [Real.norm_eq_abs]
    have : |Real.cos (dottieScalarSol t)| ≤ 1 := by
      rw [abs_le]; exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    linarith
  · simp [Real.norm_eq_abs]
    have : |Real.sin (dottieScalarSol t)| ≤ 1 := Real.abs_sin_le_one _
    linarith

/-- The `PIVP.Solution` bundle. -/
noncomputable def dottieSolution : Ripple.PIVP.Solution dottiePIVP where
  trajectory := dottieTrajectory
  init_cond := by
    show dottieTrajectory 0 = dottiePIVP.init
    rw [dottieTrajectory_zero]
    show _ = dottiePolyPIVP.toPIVP.init
    ext i
    fin_cases i <;> simp [dottiePolyPIVP, PolyPIVP.toPIVP]
  is_solution := dottieTrajectory_hasDerivAt

/-- Convergence: `|x(t) - dottieNumber| ≤ dottieNumber * exp(-t)`. -/
lemma dottieScalarSol_convergence (t : ℝ) (ht : 0 ≤ t) :
    |dottieScalarSol t - dottieNumber| ≤ dottieNumber * Real.exp (-t) := by
  apply dottie_convergence_of_solution (t := t)
  · exact dottieScalarSol_zero
  · intros s hs; exact (dottieScalarSol_bounds s hs).1
  · intros s hs; exact (dottieScalarSol_bounds s hs).2
  · exact dottieScalarSol_hasDerivAt
  · exact ht

/-- The `SemanticBTC` bundle for `dottieNumber`. -/
noncomputable def dottieBTC : Ripple.SemanticBTC 3 dottieNumber where
  pivp := dottiePIVP
  sol := dottieSolution
  modulus := fun r => (r : ℝ) + 1
  bounded := dottieTrajectory_bounded
  convergence := by
    intro r t ht
    -- Output coordinate is 0, which is the scalar solution.
    show |dottieSolution.trajectory t dottiePIVP.output - dottieNumber| < Real.exp (-(r : ℝ))
    have houtput : dottiePIVP.output = (0 : Fin 3) := by
      show dottiePolyPIVP.output = (0 : Fin 3)
      rfl
    rw [houtput]
    have hcoord : dottieSolution.trajectory t 0 = dottieScalarSol t := by
      show dottieTrajectory t 0 = dottieScalarSol t
      simp [dottieTrajectory]
    rw [hcoord]
    -- We have |dottieScalarSol t - d| ≤ d * exp(-t).  Need < exp(-r).
    have ht_nn : 0 ≤ t := by linarith [show (0 : ℝ) ≤ (r : ℝ) + 1 from by positivity]
    have hconv : |dottieScalarSol t - dottieNumber| ≤ dottieNumber * Real.exp (-t) :=
      dottieScalarSol_convergence t ht_nn
    -- dottieNumber * exp(-t) < exp(-r)  when t > r + 1
    -- dottieNumber < 1, so dottieNumber * exp(-t) < exp(-t) ≤ exp(-(r+1)) < exp(-r)
    have h1 : dottieNumber * Real.exp (-t) < 1 * Real.exp (-t) := by
      apply mul_lt_mul_of_pos_right dottieNumber_lt_one (Real.exp_pos _)
    have h2 : Real.exp (-t) < Real.exp (-(r : ℝ)) := by
      apply Real.exp_lt_exp.mpr
      linarith
    have h3 : 1 * Real.exp (-t) = Real.exp (-t) := by ring
    linarith

end Ripple.Number
