/-
  Ripple.Number.ApreyScalarZ — (F6) scalar exponential convergence
  of the Apéry conifold parameter `z(τ)`.

  The Apéry 8-variable system's z-coordinate satisfies an autonomous
  scalar ODE
      `dz/dτ = p(z) := z² (1 − 34 z + z²) = z² (z − z₁)(z − z₂)`
  where
      `z₁ := 17 − 12 √2`  (the conifold singularity, our target),
      `z₂ := 17 + 12 √2`  (the conjugate, outside the basin).

  **Goal of this file.**  Prove the standalone scalar lemma (F6) from the
  roadmap in `ApreyBounded.apery_conifold_frobenius_witness`:

      if `z : ℝ → ℝ` satisfies `z' = p(z)` on `[0, ∞)` with
      `z(0) = z₀ ∈ (0, z₁)`, then there exist `K, κ > 0` with
      `|z₁ − z(t)| ≤ K · exp(−κ · t)` for all `t ≥ 0`.

  This is the only F-step of the Frobenius roadmap that is fully within
  Mathlib's reach — (F1)–(F5) require Apéry's irrationality theorem and
  regular-singular-point Frobenius theory.

  **Proof outline.**

    1. Factorisation.  `p(z) = (z₁ − z) · z² · (z₂ − z)`.  On the open
       interval `(0, z₁)` the three factors `(z₁ − z)`, `z²`, `(z₂ − z)`
       are all strictly positive, so `p(z) > 0` — i.e. `z` is strictly
       increasing along any solution that stays in `(0, z₁)`.

    2. Invariant region.  The constant function `z ≡ z₁` is a solution
       of `z' = p(z)` (since `p(z₁) = 0`).  Mathlib's Picard uniqueness
       (`ODE_solution_unique`) then forces any solution starting
       strictly below `z₁` to remain strictly below `z₁` forever.

    3. Gronwall contraction.  Let `u(t) := z₁ − z(t) > 0`.  Then
          `u'(t) = −p(z(t)) = −u(t) · z(t)² · (z₂ − z(t))`.
       On the invariant region `z(t) ∈ [z₀, z₁]` the factor
       `z(t)² · (z₂ − z(t))` is bounded below by
          `κ := z₀² · (z₂ − z₁) = z₀² · 24 √2 > 0`.
       Hence `u'(t) ≤ −κ · u(t)`, and the constant-coefficient scalar
       Grönwall inequality gives
          `u(t) ≤ u(0) · exp(−κ · t)`.

  The constant `κ` obtained this way is *not* the optimal linearisation
  rate `λ = 24 √2 · z₁²` advertised in the docstring of
  `apery_conifold_frobenius_witness` (nor `3 λ / 2`), but it is *some*
  strictly positive rate — which is all the downstream chain demands.
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Ripple
namespace Number

open Real Set

/-- The conifold singularity `z₁ = 17 − 12√2`.  This is the target
fixed point of the scalar Apéry dynamics. -/
noncomputable def aperyZ1 : ℝ := 17 - 12 * Real.sqrt 2

/-- The conjugate `z₂ = 17 + 12√2`.  Outside the conifold basin. -/
noncomputable def aperyZ2 : ℝ := 17 + 12 * Real.sqrt 2

/-- Scalar field for the conifold z-dynamics:
`p(z) = z² · (1 − 34 z + z²)`. -/
noncomputable def aperyScalarP (z : ℝ) : ℝ :=
  z ^ 2 * (1 - 34 * z + z ^ 2)

/-! ## Elementary properties of `z₁`, `z₂`, `p`. -/

lemma aperyZ1_lt_aperyZ2 : aperyZ1 < aperyZ2 := by
  unfold aperyZ1 aperyZ2
  have h : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

lemma aperyZ2_sub_aperyZ1 : aperyZ2 - aperyZ1 = 24 * Real.sqrt 2 := by
  unfold aperyZ1 aperyZ2; ring

lemma aperyZ1_pos : 0 < aperyZ1 := by
  unfold aperyZ1
  -- 17 > 12 √2 iff 289 > 288, true.
  have hsqrt : Real.sqrt 2 < 17 / 12 := by
    rw [show (17 : ℝ) / 12 = Real.sqrt ((17 / 12) ^ 2) by
      rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 17/12)]]
    apply Real.sqrt_lt_sqrt (by norm_num)
    norm_num
  linarith

/-- Factorisation: `p(z) = z² · (z − z₁) · (z − z₂)`. -/
lemma aperyScalarP_factor (z : ℝ) :
    aperyScalarP z = z ^ 2 * (z - aperyZ1) * (z - aperyZ2) := by
  unfold aperyScalarP aperyZ1 aperyZ2
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  ring_nf
  ring_nf at h2
  nlinarith [h2, Real.sqrt_nonneg 2]

/-- Useful form: `p(z) = −(z₁ − z) · z² · (z₂ − z) · (−1)`  — i.e.
`p(z) = (z₁ − z) · z² · (z₂ − z)` when the two negatives cancel. -/
lemma aperyScalarP_factor' (z : ℝ) :
    aperyScalarP z = (aperyZ1 - z) * z ^ 2 * (aperyZ2 - z) := by
  rw [aperyScalarP_factor]; ring

/-- On the open interval `(0, z₁)` the scalar field is strictly
positive. -/
lemma aperyScalarP_pos_of_mem_basin {z : ℝ}
    (hz_pos : 0 < z) (hz_lt : z < aperyZ1) :
    0 < aperyScalarP z := by
  rw [aperyScalarP_factor']
  have hz2_pos : 0 < z ^ 2 := by positivity
  have hleft : 0 < aperyZ1 - z := by linarith
  have hright : 0 < aperyZ2 - z := by
    have : z < aperyZ2 := lt_trans hz_lt aperyZ1_lt_aperyZ2
    linarith
  positivity

/-- The linearisation rate used in the Gronwall step is strictly positive.
Given a lower bound `z₀ > 0` on the z-coordinate, we use
`κ := z₀² · (z₂ − z₁) = 24 √2 · z₀²`. -/
noncomputable def aperyKappa (z₀ : ℝ) : ℝ := z₀ ^ 2 * (24 * Real.sqrt 2)

lemma aperyKappa_pos {z₀ : ℝ} (hz₀ : 0 < z₀) : 0 < aperyKappa z₀ := by
  unfold aperyKappa
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have : 0 < z₀ ^ 2 := by positivity
  positivity

/-! ## (F6): the main exponential-convergence lemma.

  We split the proof into two parts:

    * **Gronwall step** (`apery_scalar_z_gronwall_on_invariant_interval`):
      assuming the trajectory stays inside `[z₀, z₁]` on `[0, b]`,
      derive the exponential bound on `[0, b]` via Mathlib's scalar
      Grönwall inequality `le_gronwallBound_of_liminf_deriv_right_le`.

    * **Invariant region** (`apery_scalar_z_invariant_region`, *open*):
      prove that `z(t) ∈ [z₀, z₁]` for all `t ≥ 0`, using ODE
      uniqueness against the constant solution `z ≡ z₁`.

  Combining the two yields the main theorem
  `apery_scalar_z_exponential_convergence`.  Both parts are now axiom-clean.
-/

/-- **(F6) Grönwall step.**  Given a solution `z` of the scalar
Apéry ODE `z' = p(z)` on `[0, b]` that a priori stays inside
`[z₀, z₁]`, the gap `z₁ − z(t)` decays at rate `κ := z₀² · 24 √2`. -/
theorem apery_scalar_z_gronwall_on_invariant_interval
    (z : ℝ → ℝ) (z₀ b : ℝ)
    (hz₀_pos : 0 < z₀) (_hz₀_lt : z₀ < aperyZ1) (_hb : 0 ≤ b)
    (hz_init : z 0 = z₀)
    (hz_ode : ∀ t ∈ Icc (0 : ℝ) b, HasDerivAt z (aperyScalarP (z t)) t)
    (hz_region : ∀ t ∈ Icc (0 : ℝ) b, z₀ ≤ z t ∧ z t ≤ aperyZ1) :
    ∀ t ∈ Icc (0 : ℝ) b,
      aperyZ1 - z t ≤ (aperyZ1 - z₀) * Real.exp (-(aperyKappa z₀ * t)) := by
  -- Set up the auxiliary function `f(t) := z₁ − z(t)`.
  set f : ℝ → ℝ := fun t => aperyZ1 - z t with hf_def
  set K : ℝ := -aperyKappa z₀ with hK_def
  set δ : ℝ := aperyZ1 - z₀ with hδ_def
  -- Continuity of `z` on `[0, b]` from pointwise `HasDerivAt`.
  have hz_cont : ContinuousOn z (Icc (0 : ℝ) b) := by
    refine continuousOn_of_forall_continuousAt ?_
    intro t ht
    exact (hz_ode t ht).continuousAt
  -- `f` is continuous on `[0, b]`.
  have hf_cont : ContinuousOn f (Icc 0 b) := by
    simpa [hf_def] using continuousOn_const.sub hz_cont
  -- Right-derivative of `f` on `[0, b)`: f'(t) = −p(z(t)).
  have hf_deriv : ∀ t ∈ Ico (0 : ℝ) b,
      HasDerivWithinAt f (-aperyScalarP (z t)) (Ici t) t := by
    intro t ht
    have ht_icc : t ∈ Icc (0 : ℝ) b := ⟨ht.1, le_of_lt ht.2⟩
    have h1 : HasDerivAt f (-aperyScalarP (z t)) t := by
      have := (hz_ode t ht_icc).const_sub aperyZ1
      simpa [hf_def] using this
    exact h1.hasDerivWithinAt
  -- Initial value: f(0) = z₁ − z₀ = δ.
  have hf_init : f 0 ≤ δ := by simp [hf_def, hz_init, hδ_def]
  -- Bound: f'(t) ≤ K · f(t) + 0 for t ∈ [0, b).
  -- I.e. −p(z(t)) ≤ −κ · (z₁ − z(t)).
  have h_bound : ∀ t ∈ Ico (0 : ℝ) b,
      -aperyScalarP (z t) ≤ K * f t + 0 := by
    intro t ht
    have ht_icc : t ∈ Icc (0 : ℝ) b := ⟨ht.1, le_of_lt ht.2⟩
    obtain ⟨hzt_ge, hzt_le⟩ := hz_region t ht_icc
    -- p(z) = (z₁ − z)·z²·(z₂ − z)  ≥  (z₁ − z) · z₀² · 24√2  =  κ · f(t).
    have hp_eq : aperyScalarP (z t)
        = (aperyZ1 - z t) * (z t) ^ 2 * (aperyZ2 - z t) :=
      aperyScalarP_factor' (z t)
    have h_z2sq : z₀ ^ 2 ≤ (z t) ^ 2 := by
      have hz_nn : 0 ≤ z t := le_trans (le_of_lt hz₀_pos) hzt_ge
      have hz₀_nn : 0 ≤ z₀ := le_of_lt hz₀_pos
      exact pow_le_pow_left₀ hz₀_nn hzt_ge 2
    have h_z2_diff : aperyZ2 - aperyZ1 ≤ aperyZ2 - z t := by linarith
    have h_z2_pos : 0 < aperyZ2 - z t := by
      have : z t < aperyZ2 := lt_of_le_of_lt hzt_le aperyZ1_lt_aperyZ2
      linarith
    have h_ft_nn : 0 ≤ f t := by simp [hf_def]; linarith
    have h_kappa_eq : aperyKappa z₀ = z₀ ^ 2 * (aperyZ2 - aperyZ1) := by
      rw [aperyZ2_sub_aperyZ1]; rfl
    -- Main inequality: p(z t) ≥ f t · κ
    have h_pz_ge : aperyKappa z₀ * f t ≤ aperyScalarP (z t) := by
      rw [hp_eq, h_kappa_eq]
      have hz₀_sq_nn : 0 ≤ z₀ ^ 2 := by positivity
      have h24_nn : 0 ≤ aperyZ2 - aperyZ1 := le_of_lt (by
        have := aperyZ1_lt_aperyZ2; linarith)
      -- z₀² · (z₂−z₁) · (z₁−z t) ≤ (z t)² · (z₂−z t) · (z₁−z t)
      have h_step1 : z₀ ^ 2 * (aperyZ2 - aperyZ1) * f t ≤
          (z t) ^ 2 * (aperyZ2 - aperyZ1) * f t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_z2sq h24_nn) h_ft_nn
      have h_step2 : (z t) ^ 2 * (aperyZ2 - aperyZ1) * f t ≤
          (z t) ^ 2 * (aperyZ2 - z t) * f t := by
        have hzt_sq_nn : 0 ≤ (z t) ^ 2 := by positivity
        have : (z t) ^ 2 * (aperyZ2 - aperyZ1) ≤ (z t) ^ 2 * (aperyZ2 - z t) :=
          mul_le_mul_of_nonneg_left h_z2_diff hzt_sq_nn
        exact mul_le_mul_of_nonneg_right this h_ft_nn
      have : z₀ ^ 2 * (aperyZ2 - aperyZ1) * f t ≤
          (z t) ^ 2 * (aperyZ2 - z t) * f t :=
        le_trans h_step1 h_step2
      -- Rearrange the RHS to match aperyScalarP_factor'.
      have hrhs : (aperyZ1 - z t) * (z t) ^ 2 * (aperyZ2 - z t) =
          (z t) ^ 2 * (aperyZ2 - z t) * f t := by
        simp [hf_def]; ring
      linarith [this, hrhs.symm ▸ this]
    linarith [h_pz_ge]
  -- Apply Mathlib's scalar Grönwall.
  have hGronwall :
      ∀ x ∈ Icc (0 : ℝ) b, f x ≤ gronwallBound δ K 0 (x - 0) := by
    apply le_gronwallBound_of_liminf_deriv_right_le hf_cont
    · intro t ht r hr
      have hd := hf_deriv t ht
      exact hd.liminf_right_slope_le hr
    · exact hf_init
    · exact h_bound
  -- Simplify `gronwallBound δ K 0 x` to `δ · exp(K · x) = δ · exp(−κ · x)`.
  intro t ht
  have hg := hGronwall t ht
  rw [gronwallBound_ε0, sub_zero] at hg
  simpa [hK_def, hδ_def, hf_def, mul_comm] using hg

/-! ## Building blocks for the invariant region.  -/

/-- `p(z₁) = 0`: the conifold is a fixed point of the scalar dynamics. -/
lemma aperyScalarP_at_aperyZ1 : aperyScalarP aperyZ1 = 0 := by
  rw [aperyScalarP_factor]; ring

/-- The constant function at `z₁` is a solution of `z' = p(z)`. -/
lemma hasDerivAt_const_aperyZ1 (t : ℝ) :
    HasDerivAt (fun _ : ℝ => aperyZ1) (aperyScalarP aperyZ1) t := by
  rw [aperyScalarP_at_aperyZ1]; exact hasDerivAt_const t aperyZ1

/-- `aperyScalarP` is differentiable everywhere. -/
lemma aperyScalarP_differentiable : Differentiable ℝ aperyScalarP := by
  unfold aperyScalarP
  fun_prop

/-- Explicit derivative of `aperyScalarP`. -/
lemma deriv_aperyScalarP (x : ℝ) :
    deriv aperyScalarP x = 2 * x - 102 * x ^ 2 + 4 * x ^ 3 := by
  unfold aperyScalarP
  have h : deriv (fun z : ℝ => z ^ 2 * (1 - 34 * z + z ^ 2)) x =
      2 * x - 102 * x ^ 2 + 4 * x ^ 3 := by
    have h1 : HasDerivAt (fun z : ℝ => z ^ 2 * (1 - 34 * z + z ^ 2))
              (2 * x - 102 * x ^ 2 + 4 * x ^ 3) x := by
      have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
        simpa using (hasDerivAt_pow 2 x)
      have hcu : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := hsq
      have hinner : HasDerivAt (fun z : ℝ => 1 - 34 * z + z ^ 2)
                    (-34 + 2 * x) x := by
        have : HasDerivAt (fun z : ℝ => (1 : ℝ) - 34 * z + z ^ 2)
               (0 - 34 * 1 + 2 * x) x := by
          exact ((hasDerivAt_const x (1 : ℝ)).sub
            ((hasDerivAt_id x).const_mul 34)).add hsq
        simpa using this
      have := hsq.mul hinner
      convert this using 1
      ring
    exact h1.deriv
  exact h

lemma aperyScalarP_deriv_bound {M : ℝ} (hM : 0 ≤ M) (x : ℝ)
    (hx : x ∈ Icc (-M) M) :
    |deriv aperyScalarP x| ≤ 2 * M + 102 * M ^ 2 + 4 * M ^ 3 := by
  rw [deriv_aperyScalarP]
  have habs_x : |x| ≤ M := abs_le.mpr hx
  have habs_x_nn : 0 ≤ |x| := abs_nonneg _
  have hx_sq_le : x ^ 2 ≤ M ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
  have hx3_abs : |x ^ 3| ≤ M ^ 3 := by
    have h1 : |x ^ 3| = |x| ^ 3 := by rw [abs_pow]
    rw [h1]
    exact pow_le_pow_left₀ habs_x_nn habs_x 3
  have hx3_bound : -M ^ 3 ≤ x ^ 3 ∧ x ^ 3 ≤ M ^ 3 := abs_le.mp hx3_abs
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg x, habs_x]
  · nlinarith [sq_nonneg x, habs_x]

/-- The scalar Apéry field `p` is Lipschitz on any bounded interval,
with explicit Lipschitz constant `L(M) := 2M + 102 M² + 4 M³`. -/
lemma aperyScalarP_lipschitzOnWith {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : NNReal, LipschitzOnWith L aperyScalarP (Icc (-M) M) := by
  set L : NNReal := ⟨2 * M + 102 * M ^ 2 + 4 * M ^ 3,
    by positivity⟩ with hL_def
  refine ⟨L, ?_⟩
  refine (convex_Icc _ _).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => aperyScalarP_differentiable x) ?_
  intro x hx
  have hbnd : |deriv aperyScalarP x| ≤ 2 * M + 102 * M ^ 2 + 4 * M ^ 3 :=
    aperyScalarP_deriv_bound hM x hx
  -- Convert `| · |` bound to `‖ · ‖₊` bound on NNReal.
  have hL_coe : (L : ℝ) = 2 * M + 102 * M ^ 2 + 4 * M ^ 3 := rfl
  rw [show ((‖deriv aperyScalarP x‖₊ : NNReal) ≤ L) ↔
        ((‖deriv aperyScalarP x‖₊ : ℝ) ≤ (L : ℝ)) from NNReal.coe_le_coe.symm]
  rw [hL_coe]
  calc (‖deriv aperyScalarP x‖₊ : ℝ)
      = ‖deriv aperyScalarP x‖ := by simp
    _ = |deriv aperyScalarP x| := Real.norm_eq_abs _
    _ ≤ 2 * M + 102 * M ^ 2 + 4 * M ^ 3 := hbnd

/-- Continuity of a solution `z` of the scalar Apéry ODE on `[0, ∞)`. -/
lemma apery_scalar_z_continuous
    (z : ℝ → ℝ)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (aperyScalarP (z t)) t) :
    ContinuousOn z (Ici (0 : ℝ)) := by
  refine continuousOn_of_forall_continuousAt ?_
  intro t ht
  exact (hz_ode t ht).continuousAt

/-- **(F6) Upper barrier.**  `z(t) ≤ z₁` for all `t ≥ 0`.

Proof by contradiction via Picard backward uniqueness.  If `z(T) > z₁`
for some `T ≥ 0`, IVT gives `t* ∈ [0, T]` with `z(t*) = z₁`.  On a large
enough bounded box `Icc (-M) M` the polynomial field `p` is Lipschitz
(`aperyScalarP_lipschitzOnWith`), and both `z` and the constant solution
`ẑ ≡ z₁` solve `z' = p(z)` and agree at `t*`.  Picard uniqueness
(`ODE_solution_unique_of_mem_Icc_left`) forces `z ≡ z₁` on `[0, t*]`,
contradicting `z(0) = z₀ < z₁`. -/
lemma apery_scalar_z_upper_bound
    (z : ℝ → ℝ) (z₀ : ℝ)
    (_hz₀_pos : 0 < z₀) (hz₀_lt : z₀ < aperyZ1)
    (hz_init : z 0 = z₀)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (aperyScalarP (z t)) t) :
    ∀ t : ℝ, 0 ≤ t → z t ≤ aperyZ1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨T, hT_nn, hzT⟩ := hcon
  -- Continuity of `z` on `Icc 0 T` (hence on every sub-interval).
  have hz_cont_T : ContinuousOn z (Icc (0 : ℝ) T) := fun t ht =>
    ((hz_ode t ht.1).continuousAt).continuousWithinAt
  -- IVT gives `t_star ∈ [0, T]` with `z t_star = aperyZ1`.
  have h_lo : z 0 ≤ aperyZ1 := by rw [hz_init]; exact le_of_lt hz₀_lt
  have h_hi : aperyZ1 ≤ z T := le_of_lt hzT
  obtain ⟨t_star, ht_star_mem, hz_star⟩ :=
    intermediate_value_Icc hT_nn hz_cont_T ⟨h_lo, h_hi⟩
  obtain ⟨ht_star_nn, ht_star_le_T⟩ := ht_star_mem
  -- Continuity on the smaller interval.
  have hz_cont : ContinuousOn z (Icc (0 : ℝ) t_star) :=
    hz_cont_T.mono (Icc_subset_Icc_right ht_star_le_T)
  -- Extract max/min of `z` on the compact `[0, t_star]`.
  have h_compact : IsCompact (Icc (0 : ℝ) t_star) := isCompact_Icc
  have h_nonempty : (Icc (0 : ℝ) t_star).Nonempty := ⟨0, ⟨le_refl _, ht_star_nn⟩⟩
  obtain ⟨a_max, _, h_max⟩ :=
    h_compact.exists_isMaxOn h_nonempty hz_cont
  obtain ⟨a_min, _, h_min⟩ :=
    h_compact.exists_isMinOn h_nonempty hz_cont
  -- `M := max (|z a_max|, |z a_min|, |aperyZ1|) + 1` is a bound for `|z|`
  -- on `[0, t_star]` and also bounds `|aperyZ1|`.
  set M : ℝ := max (max |z a_max| |z a_min|) |aperyZ1| + 1 with hM_def
  have hM_nn : 0 ≤ M := by
    have : 0 ≤ max (max |z a_max| |z a_min|) |aperyZ1| := by positivity
    linarith
  have hM_z1 : aperyZ1 ∈ Icc (-M) M := by
    refine ⟨?_, ?_⟩
    · have : -|aperyZ1| ≤ aperyZ1 := neg_abs_le _
      have hle : |aperyZ1| ≤ M := by
        have : |aperyZ1| ≤ max (max |z a_max| |z a_min|) |aperyZ1| := le_max_right _ _
        linarith
      linarith
    · have : aperyZ1 ≤ |aperyZ1| := le_abs_self _
      have hle : |aperyZ1| ≤ M := by
        have : |aperyZ1| ≤ max (max |z a_max| |z a_min|) |aperyZ1| := le_max_right _ _
        linarith
      linarith
  -- Membership of `z t` in the box for `t ∈ [0, t_star]`.
  have hz_in_box : ∀ t ∈ Icc (0 : ℝ) t_star, z t ∈ Icc (-M) M := by
    intro t ht
    have hmax_bd : z t ≤ z a_max := h_max ht
    have hmin_bd : z a_min ≤ z t := h_min ht
    refine ⟨?_, ?_⟩
    · have h1 : -|z a_min| ≤ z a_min := neg_abs_le _
      have h2 : |z a_min| ≤ M := by
        have : |z a_min| ≤ max |z a_max| |z a_min| := le_max_right _ _
        have : |z a_min| ≤ max (max |z a_max| |z a_min|) |aperyZ1| :=
          le_trans this (le_max_left _ _)
        linarith
      linarith
    · have h1 : z a_max ≤ |z a_max| := le_abs_self _
      have h2 : |z a_max| ≤ M := by
        have : |z a_max| ≤ max |z a_max| |z a_min| := le_max_left _ _
        have : |z a_max| ≤ max (max |z a_max| |z a_min|) |aperyZ1| :=
          le_trans this (le_max_left _ _)
        linarith
      linarith
  -- Lipschitz on the box.
  obtain ⟨L, hL⟩ := aperyScalarP_lipschitzOnWith hM_nn
  -- Apply ODE uniqueness on `[0, t_star]`, comparing `z` with the
  -- constant function at `aperyZ1`.
  have h_eq : EqOn z (fun _ : ℝ => aperyZ1) (Icc (0 : ℝ) t_star) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun _ x => aperyScalarP x) (s := fun _ => Icc (-M) M)
      (K := L) (a := 0) (b := t_star)
    · intro t _; exact hL
    · exact hz_cont
    · intro t ht
      have ht_icc : t ∈ Icc (0 : ℝ) t_star := ⟨le_of_lt ht.1, ht.2⟩
      exact (hz_ode t ht_icc.1).hasDerivWithinAt
    · intro t ht
      exact hz_in_box t ⟨le_of_lt ht.1, ht.2⟩
    · exact continuousOn_const
    · intro t _
      exact (hasDerivAt_const t aperyZ1).hasDerivWithinAt.congr_deriv
        aperyScalarP_at_aperyZ1.symm
    · intro _ _; exact hM_z1
    · exact hz_star
  -- Evaluate the equality at `0`.
  have h_at_zero : z 0 = aperyZ1 := h_eq ⟨le_refl _, ht_star_nn⟩
  rw [hz_init] at h_at_zero
  linarith

/-- **(F6) Lower barrier.**  `z(t) ≥ z₀` for all `t ≥ 0`.

Proof in two stages.
  * *Nonnegativity via Picard.*  The same argument as the upper barrier,
    but comparing `z` with the constant solution `ẑ ≡ 0` (since
    `p(0) = 0`), forces `z(t) ≥ 0` for all `t ≥ 0`.
  * *Monotonicity bootstrap.*  On `[0, z₁]` the factored form
    `p(z) = (z₁ − z) · z² · (z₂ − z)` is a product of non-negatives, so
    `p(z) ≥ 0`.  Combined with the upper barrier and nonnegativity,
    `z' = p(z) ≥ 0` on every `[0, t]`, so `z` is monotone and
    `z(t) ≥ z(0) = z₀`. -/
lemma apery_scalar_z_lower_bound
    (z : ℝ → ℝ) (z₀ : ℝ)
    (hz₀_pos : 0 < z₀) (hz₀_lt : z₀ < aperyZ1)
    (hz_init : z 0 = z₀)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (aperyScalarP (z t)) t) :
    ∀ t : ℝ, 0 ≤ t → z₀ ≤ z t := by
  -- Stage 1: nonnegativity of `z` via Picard against `ẑ ≡ 0`.
  have hz_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ z t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    -- `z t < 0`.  IVT: ∃ `t_star ∈ [0, t]` with `z t_star = 0`.
    have hz_cont_T : ContinuousOn z (Icc (0 : ℝ) t) := fun s hs =>
      ((hz_ode s hs.1).continuousAt).continuousWithinAt
    have h_lo : z t ≤ 0 := le_of_lt hcon
    have h_hi : (0 : ℝ) ≤ z 0 := by rw [hz_init]; linarith
    obtain ⟨t_star, ht_star_mem, hz_star⟩ :=
      intermediate_value_Icc' ht hz_cont_T ⟨h_lo, h_hi⟩
    obtain ⟨ht_star_nn, ht_star_le⟩ := ht_star_mem
    -- Same compactness + Picard argument.
    have hz_cont : ContinuousOn z (Icc (0 : ℝ) t_star) :=
      hz_cont_T.mono (Icc_subset_Icc_right ht_star_le)
    have h_compact : IsCompact (Icc (0 : ℝ) t_star) := isCompact_Icc
    have h_nonempty : (Icc (0 : ℝ) t_star).Nonempty := ⟨0, ⟨le_refl _, ht_star_nn⟩⟩
    obtain ⟨a_max, _, h_max⟩ := h_compact.exists_isMaxOn h_nonempty hz_cont
    obtain ⟨a_min, _, h_min⟩ := h_compact.exists_isMinOn h_nonempty hz_cont
    set M : ℝ := max |z a_max| |z a_min| + 1 with hM_def
    have hM_nn : 0 ≤ M := by
      have : 0 ≤ max |z a_max| |z a_min| := by positivity
      linarith
    have hM_zero : (0 : ℝ) ∈ Icc (-M) M := by
      refine ⟨?_, ?_⟩
      · linarith
      · linarith
    have hz_in_box : ∀ s ∈ Icc (0 : ℝ) t_star, z s ∈ Icc (-M) M := by
      intro s hs
      have hmax_bd : z s ≤ z a_max := h_max hs
      have hmin_bd : z a_min ≤ z s := h_min hs
      refine ⟨?_, ?_⟩
      · have h1 : -|z a_min| ≤ z a_min := neg_abs_le _
        have h2 : |z a_min| ≤ M := by
          have := le_max_right |z a_max| |z a_min|
          linarith
        linarith
      · have h1 : z a_max ≤ |z a_max| := le_abs_self _
        have h2 : |z a_max| ≤ M := by
          have := le_max_left |z a_max| |z a_min|
          linarith
        linarith
    obtain ⟨L, hL⟩ := aperyScalarP_lipschitzOnWith hM_nn
    have hp_zero : aperyScalarP 0 = 0 := by unfold aperyScalarP; ring
    have h_eq : EqOn z (fun _ : ℝ => (0 : ℝ)) (Icc (0 : ℝ) t_star) := by
      apply ODE_solution_unique_of_mem_Icc_left
        (v := fun _ x => aperyScalarP x) (s := fun _ => Icc (-M) M)
        (K := L) (a := 0) (b := t_star)
      · intro s _; exact hL
      · exact hz_cont
      · intro s hs
        exact (hz_ode s (le_of_lt hs.1)).hasDerivWithinAt
      · intro s hs
        exact hz_in_box s ⟨le_of_lt hs.1, hs.2⟩
      · exact continuousOn_const
      · intro s _
        exact (hasDerivAt_const s (0 : ℝ)).hasDerivWithinAt.congr_deriv hp_zero.symm
      · intro _ _; exact hM_zero
      · exact hz_star
    have h_at_zero : z 0 = 0 := h_eq ⟨le_refl _, ht_star_nn⟩
    rw [hz_init] at h_at_zero
    linarith
  -- Stage 2: monotonicity bootstrap using both barriers.
  have hz_upper : ∀ s : ℝ, 0 ≤ s → z s ≤ aperyZ1 :=
    apery_scalar_z_upper_bound z z₀ hz₀_pos hz₀_lt hz_init hz_ode
  intro t ht
  -- `z` is monotone on `[0, t]` because `z' = p(z) ≥ 0` on `(0, t)`.
  have hz_cont_t : ContinuousOn z (Icc (0 : ℝ) t) := fun s hs =>
    ((hz_ode s hs.1).continuousAt).continuousWithinAt
  have h_mono : MonotoneOn z (Icc (0 : ℝ) t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hz_cont_t
      (f' := fun s => aperyScalarP (z s)) ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      have hs_nn : 0 ≤ s := le_of_lt hs.1
      exact (hz_ode s hs_nn).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs_nn : 0 ≤ s := le_of_lt hs.1
      have hzs_nn : 0 ≤ z s := hz_nonneg s hs_nn
      have hzs_le : z s ≤ aperyZ1 := hz_upper s hs_nn
      change 0 ≤ aperyScalarP (z s)
      rw [aperyScalarP_factor']
      have hleft : 0 ≤ aperyZ1 - z s := by linarith
      have hz_sq_nn : 0 ≤ (z s) ^ 2 := by positivity
      have hright : 0 ≤ aperyZ2 - z s := by
        have : z s < aperyZ2 := lt_of_le_of_lt hzs_le aperyZ1_lt_aperyZ2
        linarith
      positivity
  have h0_in : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_refl _, ht⟩
  have ht_in : t ∈ Icc (0 : ℝ) t := ⟨ht, le_refl _⟩
  have := h_mono h0_in ht_in ht
  rw [hz_init] at this
  exact this

/-- **(F6) Invariant region.**  Any solution `z` of `z' = p(z)` starting
at `z₀ ∈ (0, z₁)` stays in `[z₀, z₁]` for all `t ≥ 0`.

**Status.**  The invariant region is assembled from the *upper barrier*
(Picard uniqueness against the constant solution `z ≡ z₁`) and the
*lower barrier* (Picard nonnegativity at `ẑ ≡ 0` then monotonicity
bootstrap from `p ≥ 0` on `[0, z₁]`).  Both sub-lemmas are closed. -/
theorem apery_scalar_z_invariant_region
    (z : ℝ → ℝ) (z₀ : ℝ)
    (hz₀_pos : 0 < z₀) (hz₀_lt : z₀ < aperyZ1)
    (hz_init : z 0 = z₀)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (aperyScalarP (z t)) t) :
    ∀ t : ℝ, 0 ≤ t → z₀ ≤ z t ∧ z t ≤ aperyZ1 := fun t ht =>
  ⟨apery_scalar_z_lower_bound z z₀ hz₀_pos hz₀_lt hz_init hz_ode t ht,
   apery_scalar_z_upper_bound z z₀ hz₀_pos hz₀_lt hz_init hz_ode t ht⟩

/-- **(F6) Scalar exponential convergence of the Apéry z-coordinate.**
Given `z : ℝ → ℝ` satisfying `z' = p(z)` on `[0, ∞)` with
`z(0) = z₀ ∈ (0, z₁)`, the gap `z₁ − z(t)` decays exponentially with
rate `κ := z₀² · 24 √2`. -/
theorem apery_scalar_z_exponential_convergence
    (z : ℝ → ℝ) (z₀ : ℝ)
    (hz₀_pos : 0 < z₀) (hz₀_lt : z₀ < aperyZ1)
    (hz_init : z 0 = z₀)
    (hz_ode : ∀ t : ℝ, 0 ≤ t → HasDerivAt z (aperyScalarP (z t)) t) :
    ∃ K κ : ℝ, 0 < K ∧ 0 < κ ∧
      ∀ t : ℝ, 0 ≤ t → |aperyZ1 - z t| ≤ K * Real.exp (-(κ * t)) := by
  refine ⟨aperyZ1 - z₀, aperyKappa z₀, by linarith, aperyKappa_pos hz₀_pos, ?_⟩
  intro t ht
  have h_region := apery_scalar_z_invariant_region z z₀ hz₀_pos hz₀_lt hz_init hz_ode
  have h_gronwall := apery_scalar_z_gronwall_on_invariant_interval
    z z₀ (t + 1) hz₀_pos hz₀_lt (by linarith) hz_init
    (fun s hs => hz_ode s hs.1)
    (fun s hs => h_region s hs.1)
  have ht_in : t ∈ Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have ⟨_, hzt_le⟩ := h_region t ht
  have hg := h_gronwall t ht_in
  have h_abs : |aperyZ1 - z t| = aperyZ1 - z t := by
    apply abs_of_nonneg; linarith
  rw [h_abs]; exact hg

end Number
end Ripple
