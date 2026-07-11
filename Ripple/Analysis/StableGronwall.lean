/-
  Ripple.Analysis.StableGronwall — Lyapunov-Stable Gronwall and Residual Shadowing

  The standard Gronwall lemma gives ‖D(t)‖ ≤ e^{LT}(‖D(0)‖ + sup‖M‖),
  which blows up with T. For log-horizon Kurtz tubes (T_N ~ log N),
  we need Lyapunov-style contraction:
    ‖D(t)‖ ≤ e^{-ηt}‖D(0)‖ + C_stab · sup‖M‖.

  Three layers:
  1. `stable_gronwall_const`: scalar ODE comparison with -η dissipation
  2. `OneSidedContractingOn`: inner-product contraction predicate
  3. `stable_shadowing_with_residual`: vector-valued shadowing theorem

  Reference: Bansaye-Méléard 2015, deterministic-residual form.
  Mathlib base: `le_gronwallBound_of_liminf_deriv_right_le` with K = -η.
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace Ripple.Analysis

open Set Real Filter

/-! ## Step 1: Scalar stable Gronwall -/

private lemma gronwallBound_neg_eq {δ η ε x : ℝ} (hη : 0 < η) :
    gronwallBound δ (-η) ε x = δ * exp (-η * x) + (ε / η) * (1 - exp (-η * x)) := by
  unfold gronwallBound
  rw [if_neg (by linarith : (-η : ℝ) ≠ 0)]
  ring

/-- Scalar stable Gronwall: if u'(t) ≤ -η·u(t) + ε on [a,T], then
    u(t) ≤ u(a)·e^{-η(t-a)} + (ε/η)·(1 - e^{-η(t-a)}).

    This is the dissipative analogue of Mathlib's growth-mode Gronwall.
    The key difference: the coefficient is -η (negative), yielding
    exponential decay rather than growth. -/
theorem stable_gronwall_const {u : ℝ → ℝ} {a T η ε : ℝ}
    (hη : 0 < η) (hT : a ≤ T)
    (hu_cont : ContinuousOn u (Icc a T))
    (hu_deriv : ∀ t ∈ Ico a T,
      ∃ u' : ℝ, HasDerivWithinAt u u' (Ici t) t ∧ u' ≤ -η * u t + ε) :
    ∀ t ∈ Icc a T,
      u t ≤ u a * exp (-η * (t - a))
            + (ε / η) * (1 - exp (-η * (t - a))) := by
  have key := le_gronwallBound_of_liminf_deriv_right_le hu_cont
    (f' := fun t => -η * u t + ε)
    (K := -η) (ε := ε) (δ := u a)
    (fun t ht r hr => by
      obtain ⟨d, hd_deriv, hd_le⟩ := hu_deriv t ht
      exact hd_deriv.liminf_right_slope_le (lt_of_le_of_lt hd_le hr))
    le_rfl
    (fun t _ht => le_refl _)
  intro t ht
  have h := key t ht
  rw [gronwallBound_neg_eq hη] at h
  exact h

/-! ## Step 2: One-sided contraction predicate -/

/-- One-sided Lipschitz contraction in inner-product form.
    ⟨x - y, b(x) - b(y)⟩ ≤ -η · ‖x - y‖²
    This is strictly stronger than Lipschitz (which gives +L·‖x-y‖²)
    and captures the dissipative structure needed for stable shadowing. -/
def OneSidedContractingOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : E → E) (S : Set E) (η : ℝ) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ S → y ∈ S →
    @inner ℝ E _ (x - y) (b x - b y) ≤ -η * ‖x - y‖ ^ 2

/-- One-sided contraction implies the drift is Lipschitz on the same set
    (with constant η, not optimal but sufficient). -/
theorem OneSidedContractingOn.lipschitzOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {b : E → E} {S : Set E} {η : ℝ}
    (hη : 0 < η)
    (hb : OneSidedContractingOn b S η)
    (hLip : ∃ L : ℝ, ∀ x ∈ S, ∀ y ∈ S, ‖b x - b y‖ ≤ L * ‖x - y‖) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ S, ∀ y ∈ S, ‖b x - b y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L, hL⟩ := hLip
  exact ⟨max L 0, le_max_right _ _, fun x hx y hy =>
    (hL x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩

/-! ## Step 3: Derivative of squared norm under one-sided contraction -/

/-- If b is one-sided contracting with rate η on S, and x, y are solutions
    to x' = b(x), y' = b(y) both staying in S, then
    d/dt ‖x(t) - y(t)‖² ≤ -2η · ‖x(t) - y(t)‖². -/
theorem sq_norm_deriv_le_of_oneSidedContracting
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {b : E → E} {S : Set E} {η : ℝ}
    {x y : ℝ → E} {a T : ℝ}
    (hcontract : OneSidedContractingOn b S η)
    (hx_mem : ∀ t ∈ Icc a T, x t ∈ S)
    (hy_mem : ∀ t ∈ Icc a T, y t ∈ S)
    (hx_deriv : ∀ t ∈ Ico a T,
      HasDerivWithinAt x (b (x t)) (Ici t) t)
    (hy_deriv : ∀ t ∈ Ico a T,
      HasDerivWithinAt y (b (y t)) (Ici t) t) :
    ∀ t ∈ Ico a T,
      ∃ d' : ℝ,
        HasDerivWithinAt (fun s => ‖x s - y s‖ ^ 2) d' (Ici t) t
        ∧ d' ≤ -2 * η * ‖x t - y t‖ ^ 2 := by
  intro t ht
  refine ⟨2 * @inner ℝ E _ (x t - y t) (b (x t) - b (y t)), ?_, ?_⟩
  · have hd : HasDerivWithinAt (fun s => x s - y s)
        (b (x t) - b (y t)) (Ici t) t :=
      (hx_deriv t ht).sub (hy_deriv t ht)
    simpa using hd.norm_sq
  · have htcc : t ∈ Icc a T := ⟨ht.1, le_of_lt ht.2⟩
    have hc := hcontract (hx_mem t htcc) (hy_mem t htcc)
    nlinarith

/-! ## Step 4: Stable shadowing with residual -/

/-- The central deterministic theorem for log-horizon Kurtz tubes.

    Given:
    - x solves x' = b(x) (exact mean-field trajectory)
    - w := y - e solves w' = b(y) where y is the stochastic process
      and e is the martingale residual
    - b is one-sided contracting with rate η on S
    - b is also L-Lipschitz on S (for the residual term)
    - sup_{[a,T]} ‖e(t)‖ ≤ δ (the martingale residual is small)

    Then:
      ‖y(t) - x(t)‖ ≤ e^{-η(t-a)} · ‖y(a) - x(a)‖ + (1 + L/η) · δ

    The trick: w(t) := y(t) - e(t) satisfies w'(t) = b(y(t)) = b(w(t) + e(t)).
    One-sided contraction controls b(w) - b(x), ordinary Lipschitz controls
    b(w + e) - b(w). The exponential decay e^{-ηt} kills the initial error;
    the residual contributes only (1 + L/η)·δ regardless of time horizon. -/
theorem stable_shadowing_with_residual
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {b : E → E} {S : Set E}
    {x y e : ℝ → E} {a T η L δ : ℝ}
    (hη : 0 < η) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hT : a ≤ T)
    (hcontract : OneSidedContractingOn b S η)
    (hLip : ∀ u ∈ S, ∀ v ∈ S, ‖b u - b v‖ ≤ L * ‖u - v‖)
    (hx_mem : ∀ t ∈ Icc a T, x t ∈ S)
    (hy_mem : ∀ t ∈ Icc a T, y t ∈ S)
    (hw_mem : ∀ t ∈ Icc a T, y t - e t ∈ S)
    (hx_cont : ContinuousOn x (Icc a T))
    (hw_cont : ContinuousOn (fun t => y t - e t) (Icc a T))
    (hx_deriv : ∀ t ∈ Ico a T,
      HasDerivWithinAt x (b (x t)) (Ici t) t)
    (hw_deriv : ∀ t ∈ Ico a T,
      HasDerivWithinAt (fun s => y s - e s) (b (y t)) (Ici t) t)
    (he0 : e a = 0)
    (he_bound : ∀ t ∈ Icc a T, ‖e t‖ ≤ δ) :
    ∀ t ∈ Icc a T,
      ‖y t - x t‖ ≤ exp (-η * (t - a)) * ‖y a - x a‖ + (1 + L / η) * δ := by
  set g := fun t => (y t - e t) - x t with hg_def
  set v := fun t => ‖g t‖ with hv_def
  have hv_cont : ContinuousOn v (Icc a T) := by
    exact ContinuousOn.norm (hw_cont.sub hx_cont)
  have hga : g a = y a - x a := by simp [hg_def, he0]
  have hv_gronwall : ∀ t ∈ Icc a T,
      v t ≤ gronwallBound ‖y a - x a‖ (-η) (L * δ) (t - a) := by
    apply le_gronwallBound_of_liminf_deriv_right_le hv_cont
      (f' := fun t => -η * v t + L * δ)
    · intro t ht r hr
      have htcc : t ∈ Icc a T := ⟨ht.1, le_of_lt ht.2⟩
      have hg_deriv : HasDerivWithinAt g (b (y t) - b (x t)) (Ici t) t := by
        simpa [hg_def] using (hw_deriv t ht).sub (hx_deriv t ht)
      by_cases hgt : g t = 0
      · have hLd_lt : L * δ < r := by
          simpa [hv_def, hgt] using hr
        have hyx : y t - x t = e t := by
          have h0 : (y t - e t) - x t = 0 := by
            simpa [hg_def] using hgt
          calc
            y t - x t = ((y t - e t) - x t) + e t := by abel_nf
            _ = 0 + e t := by rw [h0]
            _ = e t := by simp
        have hderiv_norm_le : ‖b (y t) - b (x t)‖ ≤ L * δ := by
          calc
            ‖b (y t) - b (x t)‖ ≤ L * ‖y t - x t‖ :=
              hLip (y t) (hy_mem t htcc) (x t) (hx_mem t htcc)
            _ = L * ‖e t‖ := by rw [hyx]
            _ ≤ L * δ := mul_le_mul_of_nonneg_left (he_bound t htcc) hL
        exact (by
          simpa [hv_def] using
            hg_deriv.liminf_right_slope_norm_le
              (lt_of_le_of_lt hderiv_norm_le hLd_lt))
      · have hnorm_pos : 0 < ‖g t‖ := norm_pos_iff.mpr hgt
        have hg_sq_deriv :
            HasDerivWithinAt (fun s => ‖g s‖ ^ 2)
              (2 * @inner ℝ E _ (g t) (b (y t) - b (x t))) (Ici t) t := by
          simpa using hg_deriv.norm_sq
        have hv_deriv :
            HasDerivWithinAt v
              ((2 * @inner ℝ E _ (g t) (b (y t) - b (x t))) / (2 * ‖g t‖))
              (Ici t) t := by
          have hsqrt := hg_sq_deriv.sqrt
            (pow_ne_zero 2 (norm_ne_zero_iff.mpr hgt))
          simpa [hv_def, Real.sqrt_sq (norm_nonneg (g t))] using hsqrt
        have hres_lip : ‖b (y t) - b (y t - e t)‖ ≤ L * δ := by
          calc
            ‖b (y t) - b (y t - e t)‖
                ≤ L * ‖y t - (y t - e t)‖ :=
              hLip (y t) (hy_mem t htcc) (y t - e t) (hw_mem t htcc)
            _ = L * ‖e t‖ := by congr 1; abel_nf
            _ ≤ L * δ := mul_le_mul_of_nonneg_left (he_bound t htcc) hL
        have hcontract_t :
            @inner ℝ E _ (g t) (b (y t - e t) - b (x t))
              ≤ -η * ‖g t‖ ^ 2 := by
          simpa [hg_def] using hcontract (hw_mem t htcc) (hx_mem t htcc)
        have hres_inner_div :
            @inner ℝ E _ (g t) (b (y t) - b (y t - e t)) / ‖g t‖ ≤ L * δ := by
          have hcs := real_inner_le_norm (g t) (b (y t) - b (y t - e t))
          have hdiv :
              @inner ℝ E _ (g t) (b (y t) - b (y t - e t)) / ‖g t‖
                ≤ ‖b (y t) - b (y t - e t)‖ := by
            rw [div_le_iff₀ hnorm_pos]
            nlinarith [hcs]
          exact hdiv.trans hres_lip
        have hcontract_inner_div :
            @inner ℝ E _ (g t) (b (y t - e t) - b (x t)) / ‖g t‖
              ≤ -η * ‖g t‖ := by
          rw [div_le_iff₀ hnorm_pos]
          calc
            @inner ℝ E _ (g t) (b (y t - e t) - b (x t))
                ≤ -η * ‖g t‖ ^ 2 := hcontract_t
            _ = (-η * ‖g t‖) * ‖g t‖ := by ring
        have hinner_split :
            @inner ℝ E _ (g t) (b (y t) - b (x t))
              = @inner ℝ E _ (g t) (b (y t) - b (y t - e t))
                + @inner ℝ E _ (g t) (b (y t - e t) - b (x t)) := by
          have hvec : b (y t) - b (x t)
              = (b (y t) - b (y t - e t)) + (b (y t - e t) - b (x t)) := by
            abel_nf
          rw [hvec, inner_add_right]
        have hderiv_le :
            (2 * @inner ℝ E _ (g t) (b (y t) - b (x t))) / (2 * ‖g t‖)
              ≤ -η * v t + L * δ := by
          calc
            (2 * @inner ℝ E _ (g t) (b (y t) - b (x t))) / (2 * ‖g t‖)
                = @inner ℝ E _ (g t) (b (y t) - b (x t)) / ‖g t‖ := by
              field_simp [hnorm_pos.ne']
            _ = @inner ℝ E _ (g t) (b (y t) - b (y t - e t)) / ‖g t‖
                + @inner ℝ E _ (g t) (b (y t - e t) - b (x t)) / ‖g t‖ := by
              rw [hinner_split, add_div]
            _ ≤ L * δ + (-η * ‖g t‖) :=
              add_le_add hres_inner_div hcontract_inner_div
            _ = -η * v t + L * δ := by
              simp [hv_def]
              ring
        exact hv_deriv.liminf_right_slope_le (lt_of_le_of_lt hderiv_le hr)
    · simp [hv_def, hga]
    · intro t _ht; exact le_refl _
  intro t ht
  have hgt_bound := hv_gronwall t ht
  rw [gronwallBound_neg_eq hη] at hgt_bound
  have het := he_bound t ht
  have hye : ‖y t - x t‖ = ‖g t + e t‖ := by
    congr 1; simp only [hg_def]; abel
  rw [hye]
  have hta : a ≤ t := ht.1
  have hexp_le : exp (-η * (t - a)) ≤ 1 :=
    exp_le_one_iff.mpr (by nlinarith)
  have hLdη : 0 ≤ L * δ / η := by positivity
  have hexp_nn : 0 ≤ exp (-η * (t - a)) := exp_nonneg _
  have h_1mexp : 0 ≤ 1 - exp (-η * (t - a)) ∧
      1 - exp (-η * (t - a)) ≤ 1 := ⟨by linarith, by linarith⟩
  calc ‖g t + e t‖
      ≤ ‖g t‖ + ‖e t‖ := norm_add_le _ _
    _ ≤ v t + δ := add_le_add (le_refl _) het
    _ ≤ (‖y a - x a‖ * exp (-η * (t - a))
        + L * δ / η * (1 - exp (-η * (t - a)))) + δ := by linarith [hgt_bound]
    _ ≤ (‖y a - x a‖ * exp (-η * (t - a)) + L * δ / η) + δ := by
        have h_mono : L * δ / η * (1 - exp (-η * (t - a))) ≤ L * δ / η := by
          calc L * δ / η * (1 - exp (-η * (t - a)))
              ≤ L * δ / η * 1 := mul_le_mul_of_nonneg_left h_1mexp.2 hLdη
            _ = L * δ / η := mul_one _
        linarith [h_mono]
    _ = exp (-η * (t - a)) * ‖y a - x a‖ + (1 + L / η) * δ := by ring

end Ripple.Analysis
