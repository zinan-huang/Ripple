/-
  Ripple.Core.MinPolyMonotone — Monotone convergence on [0, α] for the
  min-polynomial single-species PIVP.

  Under the hypotheses of `minPolyPIVP_convergence_modulus`:
    • 0 < α, P.aeval α = 0, α smallest positive root, P.coeff 0 > 0.

  This file establishes:
    • `minPolyPIVP_P_pos_on_Ico`  — P(x) > 0 for x ∈ [0, α).
    • `minPolyPIVP_sol_monotone`  — sol 0 is monotone on [0, ∞).
    • `minPolyPIVP_tendsto_alpha` — sol t 0 → α as t → ∞.

  These facts, combined with a quantitative exponential-rate argument
  (file `MinPolyConvergence.lean`), discharge the analytic axiom.
-/

import Ripple.Core.MinPolyBounded
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Filter Topology

namespace Ripple
namespace Algebraic

open MvPolynomial

/-! ## Polynomial positivity on `[0, α)` -/

/-- Evaluate `minPolyPIVP P`'s field at a state `(fun _ => x)` collapses
to the real polynomial evaluation `Polynomial.aeval x P`. -/
lemma minPolyPIVP_field_scalar (P : Polynomial ℤ) (x : ℝ) :
    (minPolyPIVP P).toPIVP.field (fun _ : Fin 1 => x) 0
      = (Polynomial.aeval x P : ℝ) :=
  minPolyPIVP_field_eq_aeval P (fun _ => x) 0

/-- `x ↦ (aeval x P : ℝ)` is continuous for `P : Polynomial ℤ`. -/
lemma aeval_int_continuous (P : Polynomial ℤ) :
    Continuous (fun x : ℝ => (Polynomial.aeval x P : ℝ)) := by
  show Continuous (fun x : ℝ => Polynomial.eval₂ (Int.castRingHom ℝ) x P)
  exact Polynomial.continuous_eval₂ P (Int.castRingHom ℝ)

/-- Under `P(0) > 0` and `α` the smallest positive root of `P`, we have
`P(x) > 0` on the interval `[0, α)` (via continuity + IVT). -/
lemma minPolyPIVP_P_pos_on_Ico {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α →
      (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0) :
    ∀ x : ℝ, 0 ≤ x → x < α → 0 < (Polynomial.aeval x P : ℝ) := by
  classical
  have hP_at_0 : (Polynomial.aeval (0 : ℝ) P : ℝ) = (P.coeff 0 : ℝ) := by
    show Polynomial.eval₂ (Int.castRingHom ℝ) (0 : ℝ) P = _
    rw [Polynomial.eval₂_at_zero]; rfl
  have hP_at_0_pos : 0 < (Polynomial.aeval (0 : ℝ) P : ℝ) := by
    rw [hP_at_0]; exact_mod_cast hc0_pos
  set f : ℝ → ℝ := fun x => (Polynomial.aeval x P : ℝ) with hf_def
  have hf_cont : Continuous f := aeval_int_continuous P
  intro x hx_nn hx_lt
  by_contra h_not_pos
  push_neg at h_not_pos
  rcases eq_or_lt_of_le hx_nn with hx_eq | hx_pos
  · subst hx_eq
    exact absurd hP_at_0_pos (not_lt.mpr h_not_pos)
  · have hf_contOn : ContinuousOn f (Set.Icc 0 x) := hf_cont.continuousOn
    have hIVT : Set.Icc (f x) (f 0) ⊆ f '' Set.Icc 0 x :=
      intermediate_value_Icc' (le_of_lt hx_pos) hf_contOn
    have h0_in : (0 : ℝ) ∈ Set.Icc (f x) (f 0) := ⟨h_not_pos, le_of_lt hP_at_0_pos⟩
    obtain ⟨ξ, hξ_Icc, hξ_eq⟩ := hIVT h0_in
    rcases eq_or_lt_of_le hξ_Icc.1 with hξ_0 | hξ_pos
    · -- ξ = 0 (as equality from `0 = ξ`). So f 0 = 0, but f 0 > 0, contradiction.
      have hξ_eq0 : ξ = 0 := hξ_0.symm
      rw [hξ_eq0] at hξ_eq
      linarith [hP_at_0_pos]
    · have hξ_lt_α : ξ < α := lt_of_le_of_lt hξ_Icc.2 hx_lt
      exact hα_smallest ξ hξ_pos hξ_lt_α hξ_eq

/-! ## Trajectory non-negativity and upper bound on [0, ∞) -/

/-- The solution stays in `[0, α]`. -/
lemma minPolyPIVP_sol_in_interval
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hc0_pos : 0 < P.coeff 0)
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ sol.trajectory t 0 ∧ sol.trajectory t 0 ≤ α := by
  set T : ℝ := t + 1 with hT_def
  have hT_pos : 0 < T := by linarith
  have hsol_init : sol.trajectory 0 = fun _ : Fin 1 => (0 : ℝ) := by
    have := sol.init_cond
    rw [this]
    funext i
    simp [minPolyPIVP, PolyPIVP.toPIVP]
  have hsol_ode : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt sol.trajectory ((minPolyPIVP P).toPIVP.field (sol.trajectory s)) s :=
    fun s hs => sol.is_solution s hs.1
  have hs_Ico : t ∈ Set.Ico (0 : ℝ) T := ⟨ht, by linarith⟩
  have h_nn := minPolyPIVP_local_nonneg P (le_of_lt hc0_pos) T hT_pos sol.trajectory
    hsol_init hsol_ode t hs_Ico 0
  have h_nn_all : ∀ s ∈ Set.Ico (0 : ℝ) T, 0 ≤ sol.trajectory s 0 := fun s hs =>
    minPolyPIVP_local_nonneg P (le_of_lt hc0_pos) T hT_pos sol.trajectory
      hsol_init hsol_ode s hs 0
  have h_ub := minPolyPIVP_local_upper_bound hα_pos hα_root T hT_pos sol.trajectory
    hsol_init hsol_ode h_nn_all t hs_Ico
  exact ⟨h_nn, h_ub⟩

/-! ## Scalar derivative of sol 0 -/

/-- The scalar ODE: `d/dt (sol t 0) = P(sol t 0)` at every `t ≥ 0`. -/
lemma minPolyPIVP_scalar_deriv
    {P : Polynomial ℤ}
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => sol.trajectory s 0)
      (Polynomial.aeval (sol.trajectory t 0) P : ℝ) t := by
  have h_ode : HasDerivAt sol.trajectory
      ((minPolyPIVP P).toPIVP.field (sol.trajectory t)) t :=
    sol.is_solution t ht
  have h_comp : HasDerivAt (fun s => sol.trajectory s 0)
      ((minPolyPIVP P).toPIVP.field (sol.trajectory t) 0) t :=
    hasDerivAt_pi.mp h_ode 0
  have h_field_eq : (minPolyPIVP P).toPIVP.field (sol.trajectory t) 0
      = (Polynomial.aeval (sol.trajectory t 0) P : ℝ) := by
    have h : (fun i : Fin 1 => sol.trajectory t i) = fun _ => sol.trajectory t 0 := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      rw [hi]
    have h2 : (minPolyPIVP P).toPIVP.field (sol.trajectory t) 0
        = (minPolyPIVP P).toPIVP.field (fun _ : Fin 1 => sol.trajectory t 0) 0 := by
      congr 1
    rw [h2]
    exact minPolyPIVP_field_scalar P (sol.trajectory t 0)
  rw [← h_field_eq]
  exact h_comp

/-! ## Monotonicity on `[0, ∞)` -/

/-- The trajectory's 0-component is monotone increasing on `[0, ∞)`. -/
lemma minPolyPIVP_sol_monotone
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α →
      (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0)
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP) :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      sol.trajectory a 0 ≤ sol.trajectory b 0 := by
  intro a b ha hab
  -- Use monotoneOn_of_hasDerivWithinAt_nonneg on [a, b] (convex), with f' = P(sol _ 0) ≥ 0.
  set D : Set ℝ := Set.Icc a b with hD_def
  have hD_conv : Convex ℝ D := convex_Icc a b
  set f : ℝ → ℝ := fun u => sol.trajectory u 0 with hf_def
  have hf_cont : ContinuousOn f D := by
    intro s hs
    have hs_nn : 0 ≤ s := le_trans ha hs.1
    exact ((minPolyPIVP_scalar_deriv sol s hs_nn).continuousAt).continuousWithinAt
  -- On interior D, sol has derivative, and derivative ≥ 0.
  have h_hasDeriv_within : ∀ s ∈ interior D,
      HasDerivWithinAt f (Polynomial.aeval (sol.trajectory s 0) P : ℝ) (interior D) s := by
    intro s hs
    have hs_D : s ∈ D := interior_subset hs
    have hs_nn : 0 ≤ s := le_trans ha hs_D.1
    exact (minPolyPIVP_scalar_deriv sol s hs_nn).hasDerivWithinAt
  have h_deriv_nn : ∀ s ∈ interior D, 0 ≤ (Polynomial.aeval (sol.trajectory s 0) P : ℝ) := by
    intro s hs
    have hs_D : s ∈ D := interior_subset hs
    have hs_nn : 0 ≤ s := le_trans ha hs_D.1
    obtain ⟨h_low, h_high⟩ := minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol s hs_nn
    rcases eq_or_lt_of_le h_high with h_eq | h_lt
    · rw [h_eq, hα_root]
    · exact le_of_lt
        (minPolyPIVP_P_pos_on_Ico hα_pos hα_smallest hc0_pos _ h_low h_lt)
  have h_mono := monotoneOn_of_hasDerivWithinAt_nonneg hD_conv hf_cont
    h_hasDeriv_within h_deriv_nn
  exact h_mono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

/-! ## Limit identification -/

/-- The trajectory converges to α as t → ∞. -/
lemma minPolyPIVP_tendsto_alpha
    {α : ℝ} {P : Polynomial ℤ}
    (hα_pos : 0 < α)
    (hα_root : (Polynomial.aeval α P : ℝ) = 0)
    (hα_smallest : ∀ β : ℝ, 0 < β → β < α →
      (Polynomial.aeval β P : ℝ) ≠ 0)
    (hc0_pos : 0 < P.coeff 0)
    (sol : PIVP.Solution (minPolyPIVP P).toPIVP) :
    Filter.Tendsto (fun t => sol.trajectory t 0) Filter.atTop (nhds α) := by
  classical
  set g : ℝ → ℝ := fun t => sol.trajectory (max t 0) 0 with hg_def
  have hg_mono : Monotone g := by
    intro x y hxy
    show sol.trajectory (max x 0) 0 ≤ sol.trajectory (max y 0) 0
    apply minPolyPIVP_sol_monotone hα_pos hα_root hα_smallest hc0_pos sol
    · exact le_max_right _ _
    · exact max_le_max hxy (le_refl 0)
  have hg_bdd : ∀ t, g t ≤ α := fun t =>
    (minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol (max t 0)
      (le_max_right _ _)).2
  have hg_nn : ∀ t, 0 ≤ g t := fun t =>
    (minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol (max t 0)
      (le_max_right _ _)).1
  set L : ℝ := ⨆ t : ℝ, g t with hL_def
  have hL_le_α : L ≤ α := ciSup_le hg_bdd
  have h_bdd_above : BddAbove (Set.range g) := ⟨α, fun _ ⟨t, ht⟩ => ht ▸ hg_bdd t⟩
  have hg_tendsto_L : Filter.Tendsto g Filter.atTop (nhds L) :=
    tendsto_atTop_ciSup hg_mono h_bdd_above
  have h_eventually : ∀ᶠ t in Filter.atTop, g t = sol.trajectory t 0 := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    show sol.trajectory (max t 0) 0 = sol.trajectory t 0
    rw [max_eq_left ht]
  have h_tendsto_L : Filter.Tendsto (fun t => sol.trajectory t 0) Filter.atTop (nhds L) :=
    hg_tendsto_L.congr' h_eventually
  -- Now identify L = α.
  -- Step A: L > 0.
  have h_L_pos : 0 < L := by
    -- If L = 0, then sol t 0 = 0 for all t ≥ 0 (since g(t) ≤ L = 0 and g(t) ≥ 0).
    -- But sol'(0) = P(0) > 0, contradiction.
    by_contra h_nonpos
    push_neg at h_nonpos
    -- hg_nn t ≤ L, L ≤ 0, hg_nn t ≥ 0 ⇒ L = 0 and g t = 0 for all t.
    have hL_ge : 0 ≤ L := by
      -- g 0 ≤ L, g 0 ≥ 0.
      have : g 0 ≤ L := le_ciSup h_bdd_above 0
      linarith [hg_nn 0]
    have hL_eq : L = 0 := le_antisymm h_nonpos hL_ge
    -- So sol t 0 = 0 for t ≥ 0.
    have h_sol_zero : ∀ t ≥ (0 : ℝ), sol.trajectory t 0 = 0 := by
      intro t ht
      have hg_le_0 : g t ≤ 0 := by
        rw [← hL_eq]; exact le_ciSup h_bdd_above t
      have hg_ge_0 : 0 ≤ g t := hg_nn t
      have hg_eq : g t = 0 := le_antisymm hg_le_0 hg_ge_0
      have : g t = sol.trajectory t 0 := by
        show sol.trajectory (max t 0) 0 = sol.trajectory t 0
        rw [max_eq_left ht]
      linarith [hg_eq, this]
    -- But sol'(0) = P(sol 0 0) = P(0) = P.coeff 0 > 0.
    have h_deriv_0 : HasDerivAt (fun s => sol.trajectory s 0)
        (Polynomial.aeval (sol.trajectory 0 0) P : ℝ) 0 :=
      minPolyPIVP_scalar_deriv sol 0 (le_refl _)
    have h_sol_0_eq : sol.trajectory 0 0 = 0 := h_sol_zero 0 (le_refl _)
    rw [h_sol_0_eq] at h_deriv_0
    have hP0 : (Polynomial.aeval (0 : ℝ) P : ℝ) = (P.coeff 0 : ℝ) := by
      show Polynomial.eval₂ (Int.castRingHom ℝ) (0 : ℝ) P = _
      rw [Polynomial.eval₂_at_zero]; rfl
    rw [hP0] at h_deriv_0
    have hP_pos : (0 : ℝ) < (P.coeff 0 : ℝ) := by exact_mod_cast hc0_pos
    -- sol 0 = 0 but sol t 0 = 0 for t ≥ 0, so sol has derivative 0 at 0.
    -- But h_deriv_0 says derivative is P.coeff 0 > 0. Contradict.
    -- Derivation: the function (fun s => sol s 0) is zero on [0, ∞), so its
    -- right-derivative at 0 is 0. But `HasDerivAt` demands two-sided; we can't
    -- directly conclude. We need the one-sided version via the filter.
    -- sol s 0 = 0 for s ≥ 0, so (sol s 0 - sol 0 0) / s = 0 for s ≥ 0.
    -- Thus lim sup s → 0⁺ (...) = 0, but HasDerivAt says lim = P.coeff 0 > 0. Contra.
    -- `HasDerivAt` at 0 along 𝓝[>] 0 gives t⁻¹ • (sol (0 + t) 0 - sol 0 0) → P.coeff 0.
    have h_lim_right : Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (sol.trajectory (0 + t) 0 - sol.trajectory 0 0))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (P.coeff 0 : ℝ)) :=
      h_deriv_0.tendsto_slope_zero_right
    -- On (0, ∞), sol t 0 = 0, so the slope function is identically 0.
    have h_ev_zero : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        s⁻¹ • (sol.trajectory (0 + s) 0 - sol.trajectory 0 0) = (0 : ℝ) := by
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨Set.Ioi 0, self_mem_nhdsWithin, ?_⟩
      intro s (hs : 0 < s)
      have hsol_s : sol.trajectory (0 + s) 0 = 0 := by
        have : (0 : ℝ) + s = s := by ring
        rw [this]; exact h_sol_zero s (le_of_lt hs)
      rw [hsol_s, h_sol_0_eq]
      simp
    have h_tendsto_zero : Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (sol.trajectory (0 + t) 0 - sol.trajectory 0 0))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      apply Filter.Tendsto.congr' (f₁ := fun _ => (0 : ℝ))
      · exact h_ev_zero.mono (fun s hs => hs.symm)
      · exact tendsto_const_nhds
    have h_nhds_ne_bot : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot :=
      nhdsGT_neBot 0
    have h_unique := tendsto_nhds_unique h_lim_right h_tendsto_zero
    linarith
  -- Step B: P(L) = 0 (by contradiction: if P(L) > 0 and L < α, sol → ∞ contradicting bound).
  have h_P_L_zero : (Polynomial.aeval L P : ℝ) = 0 := by
    by_contra h_ne
    rcases eq_or_lt_of_le hL_le_α with hL_eq_α | hL_lt_α
    · rw [hL_eq_α, hα_root] at h_ne; exact h_ne rfl
    · have h_L_pos_nn : 0 ≤ L := le_of_lt h_L_pos
      have h_P_L_pos : 0 < (Polynomial.aeval L P : ℝ) :=
        minPolyPIVP_P_pos_on_Ico hα_pos hα_smallest hc0_pos L h_L_pos_nn hL_lt_α
      have h_aeval_cont : Continuous (fun x : ℝ => (Polynomial.aeval x P : ℝ)) :=
        aeval_int_continuous P
      have h_P_tendsto : Filter.Tendsto
          (fun t => (Polynomial.aeval (sol.trajectory t 0) P : ℝ))
          Filter.atTop (nhds (Polynomial.aeval L P : ℝ)) :=
        h_aeval_cont.continuousAt.tendsto.comp h_tendsto_L
      -- Eventually P(sol t 0) > P(L)/2.
      have h_ev_P : ∀ᶠ t in Filter.atTop,
          (Polynomial.aeval L P : ℝ) / 2 < (Polynomial.aeval (sol.trajectory t 0) P : ℝ) := by
        apply h_P_tendsto.eventually_const_lt (u := (Polynomial.aeval L P : ℝ) / 2)
        linarith
      obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp h_ev_P
      set T' : ℝ := max T 0 with hT'_def
      have hT'_nn : 0 ≤ T' := le_max_right _ _
      have hT'_ge_T : T ≤ T' := le_max_left _ _
      -- For any N ≥ 0, sol (T' + N) 0 ≥ sol T' 0 + P(L)/2 * N.
      have h_big : ∀ N : ℝ, 0 ≤ N → sol.trajectory T' 0 +
          (Polynomial.aeval L P : ℝ) / 2 * N ≤ sol.trajectory (T' + N) 0 := by
        intro N hN
        set f : ℝ → ℝ := fun s => sol.trajectory s 0 -
          (Polynomial.aeval L P : ℝ) / 2 * s with hf_def
        set D : Set ℝ := Set.Icc T' (T' + N) with hD_def
        have hD_conv : Convex ℝ D := convex_Icc T' (T' + N)
        have hf_cont : ContinuousOn f D := by
          intro s hs
          have hs_nn : 0 ≤ s := le_trans hT'_nn hs.1
          have h1 : ContinuousAt (fun u => sol.trajectory u 0) s :=
            (minPolyPIVP_scalar_deriv sol s hs_nn).continuousAt
          have h2 : ContinuousAt (fun s : ℝ => (Polynomial.aeval L P : ℝ) / 2 * s) s :=
            (continuous_const.mul continuous_id).continuousAt
          exact (h1.sub h2).continuousWithinAt
        have hf_deriv_at : ∀ s, 0 ≤ s → HasDerivAt f
            ((Polynomial.aeval (sol.trajectory s 0) P : ℝ) -
              (Polynomial.aeval L P : ℝ) / 2) s := by
          intro s hs_nn
          have h1 := minPolyPIVP_scalar_deriv sol s hs_nn
          have h2 : HasDerivAt (fun s : ℝ => (Polynomial.aeval L P : ℝ) / 2 * s)
              ((Polynomial.aeval L P : ℝ) / 2) s := by
            simpa using (hasDerivAt_id s).const_mul ((Polynomial.aeval L P : ℝ) / 2)
          exact h1.sub h2
        have hf_deriv : ∀ s ∈ interior D,
            HasDerivWithinAt f
              ((Polynomial.aeval (sol.trajectory s 0) P : ℝ) -
                (Polynomial.aeval L P : ℝ) / 2) (interior D) s := by
          intro s hs
          have hs_D : s ∈ D := interior_subset hs
          have hs_nn : 0 ≤ s := le_trans hT'_nn hs_D.1
          exact (hf_deriv_at s hs_nn).hasDerivWithinAt
        have hf_nn : ∀ s ∈ interior D,
            0 ≤ (Polynomial.aeval (sol.trajectory s 0) P : ℝ) -
              (Polynomial.aeval L P : ℝ) / 2 := by
          intro s hs
          have hs_D : s ∈ D := interior_subset hs
          have hs_T : T ≤ s := le_trans hT'_ge_T hs_D.1
          have := hT s hs_T
          linarith
        have h_mono := monotoneOn_of_hasDerivWithinAt_nonneg hD_conv hf_cont hf_deriv hf_nn
        have h_le : f T' ≤ f (T' + N) :=
          h_mono (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith)
        show sol.trajectory T' 0 + (Polynomial.aeval L P : ℝ) / 2 * N ≤ sol.trajectory (T' + N) 0
        have hfT' : f T' = sol.trajectory T' 0 - (Polynomial.aeval L P : ℝ) / 2 * T' := rfl
        have hfTN : f (T' + N) =
            sol.trajectory (T' + N) 0 - (Polynomial.aeval L P : ℝ) / 2 * (T' + N) := rfl
        rw [hfT', hfTN] at h_le
        linarith
      have h_sol_le_α : ∀ N : ℝ, 0 ≤ N → sol.trajectory (T' + N) 0 ≤ α := fun N hN =>
        (minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol (T' + N)
          (by linarith)).2
      set N : ℝ := 2 * (α + 1) / (Polynomial.aeval L P : ℝ) with hN_def
      have hN_nn : 0 ≤ N := by
        rw [hN_def]
        apply div_nonneg
        · have : (0 : ℝ) ≤ α := le_of_lt hα_pos
          linarith
        · linarith
      have h_big_N := h_big N hN_nn
      have h_le_α_N := h_sol_le_α N hN_nn
      have h_sol_T' : 0 ≤ sol.trajectory T' 0 :=
        (minPolyPIVP_sol_in_interval hα_pos hα_root hc0_pos sol T' hT'_nn).1
      have h_eq : (Polynomial.aeval L P : ℝ) / 2 * N = α + 1 := by
        rw [hN_def]; field_simp
      linarith
  -- Step C: P(L) = 0, 0 < L ≤ α. If L < α, the smallest-root hypothesis contradicts P(L) = 0.
  -- Hence L = α.
  rcases eq_or_lt_of_le hL_le_α with hL_eq | hL_lt
  · rw [hL_eq] at h_tendsto_L; exact h_tendsto_L
  · exfalso
    exact hα_smallest L h_L_pos hL_lt h_P_L_zero

end Algebraic
end Ripple
