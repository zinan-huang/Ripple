/-
  Ripple.Core.ODEShifted — Time-shifted ODE uniqueness.

  Mathlib's `ODE_solution_unique_of_mem_Icc_right` establishes uniqueness of
  two right-sided solutions on `Icc a b` that agree at `t = a`. It requires
  the Lipschitz/existence hypotheses indexed by `t ∈ Ico a b`.

  The CRN-style `h_lip` hypothesis used throughout `Ripple.Core.ODEGlobal` is
  global-in-time (only Lipschitz in the state), so Mathlib's theorem applies
  directly at any `a`. But our consumer lemmas are written with `a = 0`. This
  file provides the shifted variant (initial time `s₀` instead of `0`).

  The file also re-exports a minimal time-translation helper to keep
  `AlgebraicConstruction`'s proof local.
-/

import Ripple.Core.ODEGlobal

open Set Filter Topology

namespace Ripple

/-- **Shifted ODE uniqueness on `Icc s₀ T`.** Two solutions on `Icc s₀ T`
that agree at `s₀` and are both bounded by `M` on the whole interval must
agree throughout. Time-shifted version of `solutions_agree_on_Icc`. -/
lemma solutions_agree_on_Icc_shifted {d : ℕ} {f : (Fin d → ℝ) → Fin d → ℝ}
    {M : ℝ} {s₀ T : ℝ} (_hsT : s₀ < T) (hM : 0 ≤ M)
    (h_lip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖)
    {α β : ℝ → Fin d → ℝ}
    (h_init : α s₀ = β s₀)
    (hα_deriv : ∀ t ∈ Icc s₀ T, HasDerivWithinAt α (f (α t)) (Icc s₀ T) t)
    (hβ_deriv : ∀ t ∈ Icc s₀ T, HasDerivWithinAt β (f (β t)) (Icc s₀ T) t)
    (hα_bound : ∀ t ∈ Icc s₀ T, ‖α t‖ ≤ M)
    (hβ_bound : ∀ t ∈ Icc s₀ T, ‖β t‖ ≤ M) :
    EqOn α β (Icc s₀ T) := by
  -- Pick Lipschitz constant on closedBall 0 (M+1) and construct LipschitzOnWith.
  have hMplus1 : (0 : ℝ) < M + 1 := by linarith
  obtain ⟨L, hL⟩ := h_lip (M + 1) hMplus1
  set L' : ℝ := max L 0 with hL'_def
  have hL'_nn : (0 : ℝ) ≤ L' := le_max_right _ _
  have hL'_ge : L ≤ L' := le_max_left _ _
  set K : NNReal := Real.toNNReal L' with hK_def
  have hK_coe : (K : ℝ) = L' := Real.coe_toNNReal L' hL'_nn
  have hL_on : ∀ x y : Fin d → ℝ, ‖x‖ ≤ M + 1 → ‖y‖ ≤ M + 1 →
      ‖f x - f y‖ ≤ L' * ‖x - y‖ := fun x y hx hy => by
    have h1 := hL x y hx hy
    have h2 : L * ‖x - y‖ ≤ L' * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right hL'_ge (norm_nonneg _)
    linarith
  set s0 : Set (Fin d → ℝ) := Metric.closedBall 0 M with hs0_def
  have h_s_bound : ∀ x ∈ s0, ‖x‖ ≤ M := fun x hx => by
    simpa [s0, Metric.mem_closedBall] using hx
  have h_s_bound' : ∀ x ∈ s0, ‖x‖ ≤ M + 1 := fun x hx => by
    have := h_s_bound x hx; linarith
  have h_lipOn : LipschitzOnWith K f s0 := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm, hK_coe]
    exact hL_on x y (h_s_bound' x hx) (h_s_bound' y hy)
  -- Package for Mathlib's uniqueness theorem.
  let v : ℝ → (Fin d → ℝ) → Fin d → ℝ := fun _ => f
  let s : ℝ → Set (Fin d → ℝ) := fun _ => s0
  have h_hv : ∀ t ∈ Ico s₀ T, LipschitzOnWith K (v t) (s t) :=
    fun t _ => h_lipOn
  have h_α_cont : ContinuousOn α (Icc s₀ T) :=
    fun t ht => (hα_deriv t ht).continuousWithinAt
  have h_β_cont : ContinuousOn β (Icc s₀ T) :=
    fun t ht => (hβ_deriv t ht).continuousWithinAt
  -- Convert Icc-derivatives to Ici-derivatives on Ico.
  have h_conv : ∀ (γ : ℝ → Fin d → ℝ) (v₀ : ℝ → Fin d → ℝ) (t : ℝ),
      t ∈ Ico s₀ T →
      HasDerivWithinAt γ (v₀ t) (Icc s₀ T) t →
      HasDerivWithinAt γ (v₀ t) (Ici t) t := by
    intro γ v₀ t ht h
    apply h.mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Iio T, Iio_mem_nhds ht.2, ?_⟩
    intro y hy
    obtain ⟨hy_iio, hy_ici⟩ := hy
    refine ⟨?_, le_of_lt hy_iio⟩
    exact le_trans ht.1 hy_ici
  have h_α_Ici : ∀ t ∈ Ico s₀ T,
      HasDerivWithinAt α (v t (α t)) (Ici t) t := fun t ht =>
    h_conv α (fun t => f (α t)) t ht (hα_deriv t ⟨ht.1, ht.2.le⟩)
  have h_β_Ici : ∀ t ∈ Ico s₀ T,
      HasDerivWithinAt β (v t (β t)) (Ici t) t := fun t ht =>
    h_conv β (fun t => f (β t)) t ht (hβ_deriv t ⟨ht.1, ht.2.le⟩)
  have h_αs : ∀ t ∈ Ico s₀ T, α t ∈ s t := fun t ht => by
    simpa [s, s0, Metric.mem_closedBall] using hα_bound t ⟨ht.1, ht.2.le⟩
  have h_βs : ∀ t ∈ Ico s₀ T, β t ∈ s t := fun t ht => by
    simpa [s, s0, Metric.mem_closedBall] using hβ_bound t ⟨ht.1, ht.2.le⟩
  exact ODE_solution_unique_of_mem_Icc_right h_hv h_α_cont h_α_Ici h_αs
    h_β_cont h_β_Ici h_βs h_init

end Ripple
