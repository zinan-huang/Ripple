 /-
   Ripple.Core.MinPolyConvergence — Convergence modulus for the
   min-polynomial single-species PIVP.

   This file discharges `minPolyPIVP_convergence_modulus_linear`.

   Strategy. The interface requires only the existence of **some** time modulus
   μ : ℕ → ℝ that bounds the convergence time per bit of precision.
   The pointwise statement `sol t 0 → α` (proven in `MinPolyMonotone` via
   monotone convergence to α) is classically sufficient: for each r, there
   exists T_r such that `|sol t 0 - α| < exp(-r)` for all `t > T_r`. Use
   `Classical.choice` to assemble the modulus.

   Rate note. While the paper claims a linear-in-r modulus (real-time
   class), that quantitative content requires a full Grönwall argument
   based on `P'(α) < 0` (hence `hα_simple`). That rate is not part of
   the current interface — it only demands existence of
   some modulus. A linear modulus is preserved by the hierarchical
   bookkeeping for the RTCRN1 Theorem 5.2 reduction, and is a target for
   a follow-up sharpening.

   Boundedness comes free from `minPolyPIVP_sol_in_interval`.
 -/

import Ripple.Core.MinPolyMonotone
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Topology.Algebra.Polynomial

 open Set Filter Topology

 namespace Ripple
 namespace Algebraic

 open MvPolynomial

/-- The min-poly PIVP's solution is bounded by `α`. -/
lemma minPolyPIVP_bounded
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hc0_pos : 0 < P.coeff 0)
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP) :
    (minPolyPIVP P).toPIVP.IsBounded sol.trajectory := by
  refine ⟨α + 1, by linarith, ?_⟩
  intro t ht
  rw [norm_fin_one]
  obtain ⟨h_low, h_high⟩ := minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol t ht
  rw [abs_of_nonneg h_low]
  linarith

/-- For the real-coefficient lift `f = P.map ℤ→ℝ`, the quotient by the
simple root factor `X - α` is nonzero at `α`. This is the algebraic core
behind the local linear lower bound needed for the real-time modulus. -/
lemma minPoly_lift_div_root_eval_ne_zero
    {α : ℝ} {P : Polynomial ℤ}
    (hα_simple : (Polynomial.aeval α P.derivative : ℝ) ≠ 0) :
    let f : Polynomial ℝ := P.map (Int.castRingHom ℝ)
    let q : Polynomial ℝ := f / (Polynomial.X - Polynomial.C α)
    q.eval α ≠ 0 := by
  dsimp
  have hderiv_map : (((Polynomial.derivative P).map (Int.castRingHom ℝ)).eval α) ≠ 0 := by
    simpa [Polynomial.eval_map] using hα_simple
  have hkey := Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
    (P.map (Int.castRingHom ℝ)) α
  have heval := congrArg (fun p : Polynomial ℝ => p.eval α) hkey
  simp [Polynomial.divByMonic_eq_div _ (Polynomial.monic_X_sub_C α)] at heval
  rw [heval]
  exact hderiv_map

/-- The quotient by the root factor `X - α` is negative at `α`.

Since `P(x) > 0` for `x < α` close to `α`, the sign of
`P(x) = (x - α) q(x)` forces `q(α) < 0` by continuity. -/
lemma minPoly_lift_div_root_eval_neg
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0)
    (hα_simple : (Polynomial.aeval α P.derivative : ℝ) ≠ 0) :
    let f : Polynomial ℝ := P.map (Int.castRingHom ℝ)
    let q : Polynomial ℝ := f / (Polynomial.X - Polynomial.C α)
    q.eval α < 0 := by
  dsimp
  have hq_ne := minPoly_lift_div_root_eval_ne_zero hα_simple
  by_contra hq_nonneg
  have hq_nn : 0 ≤ ((P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α)).eval α :=
    le_of_not_gt hq_nonneg
  have hq_pos : 0 < ((P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α)).eval α :=
    lt_of_le_of_ne hq_nn hq_ne.symm
  have hq_cont :
      Continuous fun x : ℝ =>
        ((P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α)).eval x :=
    ((P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α)).continuous
  have h_ev : ∀ᶠ x in 𝓝 α,
      0 < ((P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α)).eval x := by
    exact hq_cont.continuousAt.tendsto.eventually_const_lt hq_pos
  obtain ⟨ε, hε_pos, hεsub⟩ := Metric.mem_nhds_iff.mp h_ev
  let x : ℝ := α - min (ε / 2) (α / 2)
  have hx_pos : 0 < x := by
    dsimp [x]
    have hhalf : α / 2 < α := by linarith
    have hmin_lt : min (ε / 2) (α / 2) < α := lt_of_le_of_lt (min_le_right _ _) hhalf
    linarith
  have hx_lt : x < α := by
    dsimp [x]
    have hmin_pos : 0 < min (ε / 2) (α / 2) := by positivity
    linarith
  have hx_mem : x ∈ Metric.ball α ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hx_le : x ≤ α := by linarith [hx_lt]
    rw [abs_of_nonpos (by linarith)]
    dsimp [x]
    have hmin_lt_ε : min (ε / 2) (α / 2) < ε := by
      have hεhalf : ε / 2 < ε := by nlinarith [hε_pos]
      exact lt_of_le_of_lt (min_le_left _ _) hεhalf
    linarith
  have hqx_pos :
      0 < ((P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α)).eval x :=
    hεsub hx_mem
  have hPx_pos : 0 < (Polynomial.aeval x P : ℝ) :=
    minPolyPIVP_P_pos_on_Ico hα_pos hα_smallest hc0_pos x hx_pos.le hx_lt
  have hfac :
      (Polynomial.X - Polynomial.C α) * ((P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α))
        = P.map (Int.castRingHom ℝ) := by
    exact (show Polynomial.IsRoot (P.map (Int.castRingHom ℝ)) α from by
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using hα_root).mul_div_eq
  have hfacx := congrArg (fun p : Polynomial ℝ => p.eval x) hfac
  have h_eq :
      (x - α) * (((P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α)).eval x)
        = (Polynomial.aeval x P : ℝ) := by
    simpa [Polynomial.eval_map, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hfacx
  have hxα_neg : x - α < 0 := by linarith
  have : (x - α) * (((P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α)).eval x) < 0 :=
    mul_neg_of_neg_of_pos hxα_neg hqx_pos
  linarith [h_eq]

/-- Near `α`, the lifted polynomial is bounded below by a positive multiple
of the distance to `α`. -/
lemma minPoly_eventually_linear_lower_bound
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0)
    (hα_simple : (Polynomial.aeval α P.derivative : ℝ) ≠ 0) :
    ∃ k δ : ℝ, 0 < k ∧ 0 < δ ∧ δ ≤ α ∧
      ∀ x : ℝ, α - δ ≤ x → x ≤ α →
        k * (α - x) ≤ (Polynomial.aeval x P : ℝ) := by
  let q : Polynomial ℝ := (P.map (Int.castRingHom ℝ)) / (Polynomial.X - Polynomial.C α)
  have hq_neg : q.eval α < 0 := by
    simpa [q] using
      minPoly_lift_div_root_eval_neg hα_pos hα_root hα_smallest hc0_pos hα_simple
  let k : ℝ := -(q.eval α) / 2
  have hk_pos : 0 < k := by
    dsimp [k]
    linarith
  have hq_cont : Continuous fun x : ℝ => q.eval x := q.continuous
  have h_ev : ∀ᶠ x in 𝓝 α, q.eval x < -k := by
    have htarget : q.eval α < -k := by
      dsimp [k]
      linarith
    exact hq_cont.continuousAt.tendsto.eventually_lt_const htarget
  obtain ⟨δ0, hδ0_pos, hδ0sub⟩ := Metric.mem_nhds_iff.mp h_ev
  let δ : ℝ := min (δ0 / 2) α
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_le : δ ≤ α := by
    dsimp [δ]
    exact min_le_right _ _
  refine ⟨k, δ, hk_pos, hδ_pos, hδ_le, ?_⟩
  intro x hx1 hx2
  rcases eq_or_lt_of_le hx2 with rfl | hxlt
  · rw [hα_root]
    simp
  have hball : x ∈ Metric.ball α δ0 := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hxle : x ≤ α := hx2
    rw [abs_of_nonpos (by linarith)]
    have hx_dist : α - x < δ0 := by
      have hleδ : α - x ≤ δ := by linarith
      have hδ_lt : δ < δ0 := by
        dsimp [δ]
        have hhalf : δ0 / 2 < δ0 := by nlinarith [hδ0_pos]
        exact lt_of_le_of_lt (min_le_left _ _) hhalf
      exact lt_of_le_of_lt hleδ hδ_lt
    have hx_dist' : -(x - α) < δ0 := by
      linarith
    exact hx_dist'
  have hqx : q.eval x < -k := hδ0sub hball
  have hfac : (Polynomial.X - Polynomial.C α) * q = P.map (Int.castRingHom ℝ) := by
    exact (show Polynomial.IsRoot (P.map (Int.castRingHom ℝ)) α from by
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using hα_root).mul_div_eq
  have hfacx := congrArg (fun p : Polynomial ℝ => p.eval x) hfac
  have h_eq : (x - α) * q.eval x = (Polynomial.aeval x P : ℝ) := by
    simpa [q, Polynomial.eval_map, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hfacx
  have hxα_neg : x - α < 0 := by linarith
  have hmul : (x - α) * (-k) < (x - α) * q.eval x := by
    exact mul_lt_mul_of_neg_left hqx hxα_neg
  have hmain : k * (α - x) < (Polynomial.aeval x P : ℝ) := by
    linarith [hmul, h_eq]
  exact hmain.le

/-- **Linear convergence modulus for the min-poly PIVP.**

Once the solution has entered a small left-neighborhood of the simple root `α`,
the local factorization `P(x) = (x - α) q(x)` and `q(α) < 0` give a linear
one-sided bound `P(x) ≥ k (α - x)`. Grönwall then yields exponential decay of
the error `α - sol(t)`, hence a linear-in-`r` time modulus. -/
theorem minPolyPIVP_convergence_modulus_linear {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α → (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0)
    (hα_simple : (Polynomial.aeval α P.derivative : ℝ) ≠ 0)
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP) :
    ∃ (modulus : TimeModulus),
      (minPolyPIVP P).toPIVP.IsBounded sol.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus r →
        |sol.trajectory t (minPolyPIVP P).output - α| < Real.exp (-(r : ℝ))) := by
  have h_bdd : (minPolyPIVP P).toPIVP.IsBounded sol.trajectory :=
    minPolyPIVP_bounded hα_pos hα_root hc0_pos sol
  have h_tendsto : Filter.Tendsto (fun t => sol.trajectory t 0)
      Filter.atTop (nhds α) :=
    minPolyPIVP_tendsto_alpha hα_pos hα_root hα_smallest hc0_pos sol
  obtain ⟨k, δ, hk_pos, hδ_pos, hδ_le, hlinear⟩ :=
    minPoly_eventually_linear_lower_bound hα_pos hα_root hα_smallest hc0_pos hα_simple
  obtain ⟨Traw, hTraw⟩ := (Metric.tendsto_atTop.mp h_tendsto) δ hδ_pos
  let T : ℝ := max Traw 0
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact le_max_right _ _
  have hclose : ∀ s : ℝ, T ≤ s → |sol.trajectory s 0 - α| < δ := by
    intro s hs
    exact hTraw s (le_trans (by dsimp [T]; exact le_max_left _ _) hs)
  have hT_interval : 0 ≤ sol.trajectory T 0 ∧ sol.trajectory T 0 ≤ α :=
    minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol T hT_nonneg
  have hT_ge : α - δ < sol.trajectory T 0 := by
    have hT_close : |sol.trajectory T 0 - α| < δ := hclose T (le_rfl)
    have hT_nonpos : sol.trajectory T 0 - α ≤ 0 := by linarith [hT_interval.2]
    rw [abs_of_nonpos hT_nonpos] at hT_close
    linarith
  let A : ℝ := α + 1
  have hA_pos : 0 < A := by
    dsimp [A]
    linarith
  have hA_bound : α - sol.trajectory T 0 ≤ A := by
    dsimp [A]
    linarith [hT_interval.1]
  let modulus : TimeModulus := fun r => T + ((r : ℝ) + Real.log A) / k
  refine ⟨modulus, h_bdd, ?_⟩
  intro r t ht
  have hTt : T < t := by
    have hshift_nonneg : 0 ≤ ((r : ℝ) + Real.log A) / k := by
      have hlog_nonneg : 0 ≤ Real.log A := by
        have hA_ge_one : 1 ≤ A := by
          dsimp [A]
          linarith
        exact Real.log_nonneg hA_ge_one
      positivity
    have hmod_ge : T ≤ modulus r := by
      dsimp [modulus]
      linarith
    exact lt_of_le_of_lt hmod_ge ht
  have ht_nonneg : 0 ≤ t := le_trans hT_nonneg hTt.le
  have htraj_t : 0 ≤ sol.trajectory t 0 ∧ sol.trajectory t 0 ≤ α :=
    minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol t ht_nonneg
  set f : ℝ → ℝ := fun s => α - sol.trajectory s 0 with hf_def
  have hf_cont : ContinuousOn f (Set.Icc T t) := by
    intro s hs
    have hs_nonneg : 0 ≤ s := le_trans hT_nonneg hs.1
    exact ((hasDerivAt_const s α).sub (minPolyPIVP_scalar_deriv sol s hs_nonneg)).continuousAt.continuousWithinAt
  have hf_deriv :
      ∀ s ∈ Set.Ico T t,
        HasDerivWithinAt f (-(Polynomial.aeval (sol.trajectory s 0) P : ℝ)) (Set.Ici s) s := by
    intro s hs
    have hs_nonneg : 0 ≤ s := le_trans hT_nonneg hs.1
    simpa [hf_def] using
      ((hasDerivAt_const s α).sub (minPolyPIVP_scalar_deriv sol s hs_nonneg)).hasDerivWithinAt
  have hf_bound :
      ∀ s ∈ Set.Ico T t,
        -(Polynomial.aeval (sol.trajectory s 0) P : ℝ) ≤ (-k) * f s + 0 := by
    intro s hs
    have hs_nonneg : 0 ≤ s := le_trans hT_nonneg hs.1
    have hs_interval : 0 ≤ sol.trajectory s 0 ∧ sol.trajectory s 0 ≤ α :=
      minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol s hs_nonneg
    have hmono : sol.trajectory T 0 ≤ sol.trajectory s 0 :=
      minPolyPIVP_sol_monotone hα_pos hα_root hα_smallest hc0_pos sol T s hT_nonneg hs.1
    have hs_low : α - δ ≤ sol.trajectory s 0 := le_trans (le_of_lt hT_ge) hmono
    have hlin := hlinear (sol.trajectory s 0) hs_low hs_interval.2
    dsimp [f]
    linarith
  have hgw :=
    le_gronwallBound_of_liminf_deriv_right_le
      hf_cont
      (fun s hs r hr => (hf_deriv s hs).liminf_right_slope_le hr)
      (le_rfl : f T ≤ f T)
      hf_bound
      t
      (Set.right_mem_Icc.mpr hTt.le)
  have h_decay : f t ≤ f T * Real.exp ((-k) * (t - T)) := by
    simpa [gronwallBound_ε0] using hgw
  have h_error_eq : |sol.trajectory t 0 - α| = f t := by
    dsimp [f]
    rw [abs_of_nonpos (sub_nonpos.mpr htraj_t.2)]
    ring
  have h_init_nonneg : 0 ≤ f T := by
    dsimp [f]
    linarith [hT_interval.2]
  have h_decay' : |sol.trajectory t 0 - α| ≤ A * Real.exp ((-k) * (t - T)) := by
    rw [h_error_eq]
    calc
      f t ≤ f T * Real.exp ((-k) * (t - T)) := h_decay
      _ ≤ A * Real.exp ((-k) * (t - T)) := by
        apply mul_le_mul_of_nonneg_right hA_bound
        exact le_of_lt (Real.exp_pos _)
  have hrate_exp :
      A * Real.exp ((-k) * (t - T)) < Real.exp (-(r : ℝ)) := by
    have harg : (r : ℝ) + Real.log A < k * (t - T) := by
      have hdiv : (((r : ℝ) + Real.log A) / k) < t - T := by
        dsimp [modulus] at ht
        linarith
      have hmul : k * (((r : ℝ) + Real.log A) / k) < k * (t - T) :=
        mul_lt_mul_of_pos_left hdiv hk_pos
      have hk_ne : k ≠ 0 := ne_of_gt hk_pos
      have hleft : k * (((r : ℝ) + Real.log A) / k) = (r : ℝ) + Real.log A := by
        field_simp [hk_ne]
      rw [hleft] at hmul
      exact hmul
    have hexp_lt :
        Real.exp ((-k) * (t - T)) < Real.exp (-(r : ℝ) - Real.log A) := by
      apply Real.exp_lt_exp.mpr
      linarith
    calc
      A * Real.exp ((-k) * (t - T))
          < A * Real.exp (-(r : ℝ) - Real.log A) := by
            exact mul_lt_mul_of_pos_left hexp_lt hA_pos
      _ = Real.exp (-(r : ℝ)) := by
            have hsplit :
                Real.exp (-(r : ℝ) - Real.log A)
                  = Real.exp (-(r : ℝ)) * Real.exp (-Real.log A) := by
              rw [show (-(r : ℝ) - Real.log A) = (-(r : ℝ)) + (-Real.log A) by ring, Real.exp_add]
            rw [hsplit]
            have hA_ne : A ≠ 0 := ne_of_gt hA_pos
            have hA_inv : A * Real.exp (-Real.log A) = 1 := by
              rw [Real.exp_neg, Real.exp_log hA_pos]
              exact mul_inv_cancel₀ hA_ne
            rw [show A * (Real.exp (-(r : ℝ)) * Real.exp (-Real.log A))
                = Real.exp (-(r : ℝ)) * (A * Real.exp (-Real.log A)) by ring]
            rw [hA_inv, mul_one]
  have h_output : (minPolyPIVP P).output = 0 := rfl
  show |sol.trajectory t ((minPolyPIVP P).output) - α| < Real.exp (-(r : ℝ))
  rw [h_output]
  exact lt_of_le_of_lt h_decay' hrate_exp
