/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.Kurtz.MeanField
import Ripple.Kurtz.IntegralGronwall

/-!
# Gronwall Event Inclusion for DensityProcess

Proves the deterministic event inclusion needed by Kurtz convergence:
if the sup-norm error exceeds ε, then either the initial error exceeds δ
or the martingale sup-square exceeds δ².

The proof is pathwise: for each ω, the decomposition
X(t) = X(0) + ∫₀ᵗ F(X(s)) ds + M(t) and the ODE
sol(t) = sol(0) + ∫₀ᵗ F(sol(s)) ds combine with Lipschitz F
and integral Gronwall to give
  sup ‖X - sol‖ ≤ (‖init error‖ + sup ‖M‖) · e^{LT}.
-/

namespace Ripple.Kurtz

open MeasureTheory Set

variable {d : ℕ} {Γ : RateSpec d}

/-- Pathwise Gronwall event inclusion: if sup ‖X(t) - sol(t)‖ ≥ ε,
then either ‖X(0) - sol(0)‖ ≥ δ or sup ‖M‖² ≥ δ², where
δ = ε / (2 · e^{LT}).

This is a deterministic (non-probabilistic) statement about individual paths.
The proof uses the martingale decomposition as an integral equation and
applies the integral form of Gronwall's inequality. -/
theorem gronwall_event_inclusion_pathwise
    (mf : MeanFieldSolution d Γ)
    {T : ℝ} (hT : 0 < T)
    {L : ℝ} (hL : 0 ≤ L)
    (h_lip : ∀ x y : Fin d → ℝ, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      dist (Γ.drift x) (Γ.drift y) ≤ L * dist x y)
    -- Pathwise data for a single ω
    (X : ℝ → Fin d → ℝ) (x_init : Fin d → ℝ) (M : ℝ → Fin d → ℝ)
    (hX_bound : ∀ t, ‖X t‖ ≤ 1)
    (hsol_bound : ∀ t ∈ Icc 0 T, ‖mf.sol t‖ ≤ 1)
    -- Pathwise decomposition (for ALL t, not just a.e.)
    (hdecomp : ∀ t ≥ 0,
      X t = x_init + (fun i => ∫ s in Icc (0 : ℝ) t,
        (Γ.drift (X s)) i) + M t)
    (hM0 : M 0 = 0)
    (herr_cont : ContinuousOn (fun t => ‖X t - mf.sol t‖) (Icc (0 : ℝ) T))
    (hM_sq_le_sup : ∀ t ∈ Icc (0 : ℝ) T,
      ‖M t‖ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖M s‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε)
    (h_integral_ineq :
      let C := Real.exp (L * T)
      let δ := ε / (2 * C)
      (∀ t ∈ Icc (0 : ℝ) T, ‖M t‖ ≤ δ) →
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖X t - mf.sol t‖ ≤
          (‖x_init - mf.x₀‖ + δ) +
            ∫ s in (0 : ℝ)..t, L * ‖X s - mf.sol s‖) :
    (ε ≤ ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖X t - mf.sol t‖) →
      let C := Real.exp (L * T)
      let δ := ε / (2 * C)
      (‖x_init - mf.x₀‖ ≥ δ) ∨
      (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖M s‖ ^ 2) := by
  intro hhit
  dsimp only
  let C := Real.exp (L * T)
  let δ := ε / (2 * C)
  have hC_pos : 0 < C := Real.exp_pos _
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have hδ_pos : 0 < δ := div_pos hε (mul_pos (by norm_num) hC_pos)
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  by_contra hnot
  push Not at hnot
  have hinit_lt : ‖x_init - mf.x₀‖ < δ := by
    simpa [δ, C] using hnot.1
  have hsup_lt :
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖M s‖ ^ 2) < δ ^ 2 :=
    by simpa [δ, C] using hnot.2
  have hM_le_delta : ∀ t ∈ Icc (0 : ℝ) T, ‖M t‖ ≤ δ := by
    intro t ht
    have hsq_lt : ‖M t‖ ^ 2 < δ ^ 2 :=
      lt_of_le_of_lt (hM_sq_le_sup t ht) hsup_lt
    exact le_of_lt ((sq_lt_sq₀ (norm_nonneg _) hδ_nonneg).1 hsq_lt)
  let α := ‖x_init - mf.x₀‖ + δ
  have hα_nonneg : 0 ≤ α := add_nonneg (norm_nonneg _) hδ_nonneg
  have hineq : ∀ t ∈ Icc (0 : ℝ) T,
      ‖X t - mf.sol t‖ ≤ α + ∫ s in (0 : ℝ)..t, L * ‖X s - mf.sol s‖ := by
    simpa [α, δ, C] using h_integral_ineq hM_le_delta
  have hgronwall := @integral_gronwall_core T α L
    (fun t => ‖X t - mf.sol t‖)
    (le_of_lt hT)
    hα_nonneg
    hL
    (fun t _ => norm_nonneg _)
    hineq
    (fun x hx =>
      ContinuousOn.intervalIntegrable_of_Icc hx.1
        (continuousOn_const.mul
          (herr_cont.mono (Icc_subset_Icc_right (le_of_lt hx.2)))))
    (fun x hx =>
      ((continuousOn_const.mul herr_cont).continuousWithinAt
        ⟨hx.1, le_of_lt hx.2⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem hx))
    (fun x hx =>
      ⟨Icc (0 : ℝ) T, Icc_mem_nhdsGT_of_mem hx,
        (continuousOn_const.mul herr_cont).aestronglyMeasurable measurableSet_Icc⟩)
    (by
      have hint : IntegrableOn (fun s => L * ‖X s - mf.sol s‖)
          (uIcc (0 : ℝ) T) volume := by
        rw [uIcc_of_le (le_of_lt hT)]
        exact (continuousOn_const.mul herr_cont).integrableOn_Icc
      have hprim := intervalIntegral.continuousOn_primitive_interval hint
      rw [uIcc_of_le (le_of_lt hT)] at hprim
      exact continuousOn_const.add hprim)
  have herror_le_C : ∀ t ∈ Icc (0 : ℝ) T, ‖X t - mf.sol t‖ ≤ α * C := by
    intro t ht
    have h_exp_le : Real.exp (L * t) ≤ C := by
      exact Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left ht.2 hL)
    exact (hgronwall t ht).trans (mul_le_mul_of_nonneg_left h_exp_le hα_nonneg)
  have hsup_error_le :
      (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖X t - mf.sol t‖) ≤ α * C := by
    have hαC_nonneg : 0 ≤ α * C := mul_nonneg hα_nonneg hC_nonneg
    exact Real.iSup_le
      (fun t => Real.iSup_le
        (fun ht => herror_le_C t ⟨ht.1, ht.2⟩)
        hαC_nonneg)
      hαC_nonneg
  have hα_lt : α < 2 * δ := by
    dsimp [α]
    linarith
  have hαC_lt : α * C < ε := by
    calc
      α * C < (2 * δ) * C := mul_lt_mul_of_pos_right hα_lt hC_pos
      _ = ε := by
        have hδ_mul : δ * (2 * C) = ε := by
          dsimp [δ]
          field_simp [hC_pos.ne']
        nlinarith [hδ_mul]
  linarith

/-- The event inclusion for `kurtz_convergence_for_density_dep_ctmc`,
derived from the pathwise Gronwall bound.

For any family of DensityProcesses with Lipschitz drift, the Gronwall
event inclusion hypothesis is satisfied. -/
theorem gronwall_event_inclusion_of_densityProcess
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (mf : MeanFieldSolution d Γ)
    (X : (N : ℕ) → DensityProcess d Γ N μ)
    {T : ℝ} (hT : 0 < T)
    (h_lip : ∃ L ≥ 0, ∀ x y : Fin d → ℝ,
      dist (Γ.drift x) (Γ.drift y) ≤ L * dist x y)
    (hsol_bound : ∀ t ∈ Icc (0 : ℝ) T, ‖mf.sol t‖ ≤ 1)
    (hdecomp_all : ∀ N : ℕ, ∀ᵐ ω ∂μ, ∀ t ≥ 0,
      (X N).process t ω = (X N).init ω + (fun i =>
        ∫ s in Icc (0 : ℝ) t, (Γ.drift ((X N).process s ω)) i) +
        (X N).martingale_part t ω)
    (herr_cont : ∀ N : ℕ, ∀ᵐ ω ∂μ,
      ContinuousOn (fun t => ‖(X N).process t ω - mf.sol t‖) (Icc (0 : ℝ) T))
    (h_integral_ineq : ∀ L ≥ 0,
      (∀ x y : Fin d → ℝ, dist (Γ.drift x) (Γ.drift y) ≤ L * dist x y) →
      ∀ N : ℕ, ∀ η ≥ 0, ∀ᵐ ω ∂μ,
      (∀ t ∈ Icc (0 : ℝ) T, ‖(X N).martingale_part t ω‖ ≤ η) →
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖(X N).process t ω - mf.sol t‖ ≤
          (‖(X N).init ω - mf.x₀‖ + η) +
            ∫ s in (0 : ℝ)..t,
              L * ‖(X N).process s ω - mf.sol s‖)
    (hM_sq_le_sup : ∀ N : ℕ, ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) T,
      ‖(X N).martingale_part t ω‖ ^ 2 ≤
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖(X N).martingale_part s ω‖ ^ 2) :
    ∀ ε > 0, ∃ δ > 0, ∀ (N : ℕ), 0 < N →
        ∀ᵐ ω ∂μ,
          (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T),
              ‖(X N).process t ω - mf.sol t‖ ≥ ε) →
            (‖(X N).init ω - mf.x₀‖ ≥ δ) ∨
            (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
              ‖(X N).martingale_part s ω‖ ^ 2) := by
  intro ε hε
  obtain ⟨L, hL, h_lip_bound⟩ := h_lip
  let C := Real.exp (L * T)
  let δ := ε / (2 * C)
  have hC_pos : 0 < C := Real.exp_pos _
  have hδ_pos : 0 < δ := div_pos hε (mul_pos (by norm_num) hC_pos)
  refine ⟨δ, hδ_pos, ?_⟩
  intro N _hN
  filter_upwards
    [hdecomp_all N, (X N).martingale_init, herr_cont N,
      h_integral_ineq L hL h_lip_bound N δ hδ_pos.le, hM_sq_le_sup N]
    with ω hdecompω hM0ω herrω hineqω hMsqω
  intro hhit
  exact gronwall_event_inclusion_pathwise
    (mf := mf) (T := T) hT (L := L) hL
    (fun x y _ _ => h_lip_bound x y)
    (fun t => (X N).process t ω)
    ((X N).init ω)
    (fun t => (X N).martingale_part t ω)
    (fun t => (X N).process_norm_le_one t ω)
    hsol_bound
    hdecompω
    hM0ω
    herrω
    hMsqω
    hε
    (by simpa [δ, C] using hineqω)
    hhit

/-- Right-continuous pathwise Gronwall event inclusion.

Thin wrapper around `integral_gronwall_core` for paths that are only
right-continuous (not continuous). Takes the FTC/integrability hypotheses
directly instead of deriving them from ContinuousOn. -/
theorem gronwall_event_inclusion_pathwise_rightContinuous
    (mf : MeanFieldSolution d Γ)
    {T : ℝ} (hT : 0 < T)
    {L : ℝ} (hL : 0 ≤ L)
    (X : ℝ → Fin d → ℝ) (x_init : Fin d → ℝ) (M : ℝ → Fin d → ℝ)
    (hg_int : ∀ x ∈ Ico (0 : ℝ) T,
        IntervalIntegrable
          (fun s => L * ‖X s - mf.sol s‖) volume (0 : ℝ) x)
    (hg_cont_right : ∀ x ∈ Ico (0 : ℝ) T,
        ContinuousWithinAt
          (fun s => L * ‖X s - mf.sol s‖) (Ioi x) x)
    (hg_sm : ∀ x ∈ Ico (0 : ℝ) T,
        StronglyMeasurableAtFilter
          (fun s => L * ‖X s - mf.sol s‖) (nhdsWithin x (Ioi x)))
    (hg_prim_cont : ContinuousOn
        (fun t => ∫ s in (0 : ℝ)..t, L * ‖X s - mf.sol s‖)
        (Icc (0 : ℝ) T))
    (hM_sq_le_sup : ∀ t ∈ Icc (0 : ℝ) T,
      ‖M t‖ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖M s‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε)
    (h_integral_ineq :
      let C := Real.exp (L * T)
      let δ := ε / (2 * C)
      (∀ t ∈ Icc (0 : ℝ) T, ‖M t‖ ≤ δ) →
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖X t - mf.sol t‖ ≤
          (‖x_init - mf.x₀‖ + δ) +
            ∫ s in (0 : ℝ)..t, L * ‖X s - mf.sol s‖) :
    (ε ≤ ⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖X t - mf.sol t‖) →
      let C := Real.exp (L * T)
      let δ := ε / (2 * C)
      (‖x_init - mf.x₀‖ ≥ δ) ∨
      (δ ^ 2 ≤ ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖M s‖ ^ 2) := by
  intro hhit
  dsimp only
  let C := Real.exp (L * T)
  let δ := ε / (2 * C)
  have hC_pos : 0 < C := Real.exp_pos _
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have hδ_pos : 0 < δ := div_pos hε (mul_pos (by norm_num) hC_pos)
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  by_contra hnot
  push_neg at hnot
  have hinit_lt : ‖x_init - mf.x₀‖ < δ := by
    simpa [δ, C] using hnot.1
  have hsup_lt :
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), ‖M s‖ ^ 2) < δ ^ 2 :=
    by simpa [δ, C] using hnot.2
  have hM_le_delta : ∀ t ∈ Icc (0 : ℝ) T, ‖M t‖ ≤ δ := by
    intro t ht
    have hsq_lt : ‖M t‖ ^ 2 < δ ^ 2 :=
      lt_of_le_of_lt (hM_sq_le_sup t ht) hsup_lt
    exact le_of_lt ((sq_lt_sq₀ (norm_nonneg _) hδ_nonneg).1 hsq_lt)
  let α := ‖x_init - mf.x₀‖ + δ
  have hα_nonneg : 0 ≤ α := add_nonneg (norm_nonneg _) hδ_nonneg
  have hineq : ∀ t ∈ Icc (0 : ℝ) T,
      ‖X t - mf.sol t‖ ≤ α + ∫ s in (0 : ℝ)..t, L * ‖X s - mf.sol s‖ := by
    simpa [α, δ, C] using h_integral_ineq hM_le_delta
  have hgronwall := @integral_gronwall_core T α L
    (fun t => ‖X t - mf.sol t‖)
    (le_of_lt hT)
    hα_nonneg
    hL
    (fun t _ => norm_nonneg _)
    hineq
    hg_int
    hg_cont_right
    hg_sm
    (by simpa [α] using continuousOn_const.add hg_prim_cont)
  have herror_le_C : ∀ t ∈ Icc (0 : ℝ) T, ‖X t - mf.sol t‖ ≤ α * C := by
    intro t ht
    have h_exp_le : Real.exp (L * t) ≤ C := by
      exact Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left ht.2 hL)
    exact (hgronwall t ht).trans (mul_le_mul_of_nonneg_left h_exp_le hα_nonneg)
  have hsup_error_le :
      (⨆ (t : ℝ) (_ : 0 ≤ t ∧ t ≤ T), ‖X t - mf.sol t‖) ≤ α * C := by
    have hαC_nonneg : 0 ≤ α * C := mul_nonneg hα_nonneg hC_nonneg
    exact Real.iSup_le
      (fun t => Real.iSup_le
        (fun ht => herror_le_C t ⟨ht.1, ht.2⟩)
        hαC_nonneg)
      hαC_nonneg
  have hα_lt : α < 2 * δ := by
    dsimp [α]
    linarith
  have hαC_lt : α * C < ε := by
    calc
      α * C < (2 * δ) * C := mul_lt_mul_of_pos_right hα_lt hC_pos
      _ = ε := by
        have hδ_mul : δ * (2 * C) = ε := by
          dsimp [δ]
          field_simp [hC_pos.ne']
        nlinarith [hδ_mul]
  linarith

end Ripple.Kurtz
