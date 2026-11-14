/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Tactic

/-!
# Uniform square-moment control and martingale limits

This module proves the analytic passage used by bounded stochastic exponentials.
The second-moment bound yields uniform integrability by a direct tail estimate;
Vitali then passes the conditional-expectation identity to the limit.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace Ripple.Stochastic.ExponentialMartingaleLimit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Martingale identities are closed under slice-wise L¹ convergence. -/
lemma martingale_of_tendsto_eLpNorm_one
    {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {ι : Type*} [Preorder ι] {ℱ : MeasureTheory.Filtration ι m0}
    {M : ℕ → ι → Ω → ℝ} {F : ι → Ω → ℝ}
    (hM : ∀ n, MeasureTheory.Martingale (M n) ℱ μ)
    (hMint : ∀ n t, MeasureTheory.Integrable (M n t) μ)
    (hadapt : MeasureTheory.StronglyAdapted ℱ F)
    (hint : ∀ t, MeasureTheory.Integrable (F t) μ)
    (htend : ∀ t, Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ) Filter.atTop (nhds 0)) :
    MeasureTheory.Martingale F ℱ μ := by
  refine ⟨hadapt, fun s t hst => ?_⟩
  have haesmC : MeasureTheory.AEStronglyMeasurable (μ[F t | ℱ s]) μ :=
    MeasureTheory.integrable_condExp.aestronglyMeasurable
  have haesm : MeasureTheory.AEStronglyMeasurable (μ[F t | ℱ s] - F s) μ :=
    haesmC.sub (hint s).1
  -- The target seminorm is bounded by `‖Mₙt − Ft‖₁ + ‖Mₙs − Fs‖₁` for every `n`.
  have hbound : ∀ n, MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ
      ≤ MeasureTheory.eLpNorm (M n t - F t) 1 μ
        + MeasureTheory.eLpNorm (M n s - F s) 1 μ := by
    intro n
    have hdecomp : (μ[F t | ℱ s] - F s)
        = (μ[F t | ℱ s] - μ[M n t | ℱ s]) + (μ[M n t | ℱ s] - F s) := by ring
    calc MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ
        = MeasureTheory.eLpNorm
            ((μ[F t | ℱ s] - μ[M n t | ℱ s]) + (μ[M n t | ℱ s] - F s)) 1 μ := by
          rw [hdecomp]
      _ ≤ MeasureTheory.eLpNorm (μ[F t | ℱ s] - μ[M n t | ℱ s]) 1 μ
          + MeasureTheory.eLpNorm (μ[M n t | ℱ s] - F s) 1 μ :=
          MeasureTheory.eLpNorm_add_le
            (haesmC.sub MeasureTheory.integrable_condExp.aestronglyMeasurable)
            (MeasureTheory.integrable_condExp.aestronglyMeasurable.sub (hint s).1) (by norm_num)
      _ ≤ MeasureTheory.eLpNorm (M n t - F t) 1 μ
          + MeasureTheory.eLpNorm (M n s - F s) 1 μ := by
          gcongr
          · have h_sub : (μ[F t | ℱ s] - μ[M n t | ℱ s]) =ᵐ[μ] μ[F t - M n t | ℱ s] :=
              (MeasureTheory.condExp_sub (hint t) (hMint n t) (ℱ s)).symm
            rw [MeasureTheory.eLpNorm_congr_ae h_sub]
            calc MeasureTheory.eLpNorm (μ[F t - M n t | ℱ s]) 1 μ
                ≤ MeasureTheory.eLpNorm (F t - M n t) 1 μ :=
                  MeasureTheory.eLpNorm_one_condExp_le_eLpNorm (F t - M n t)
              _ = MeasureTheory.eLpNorm (M n t - F t) 1 μ := by
                  rw [show F t - M n t = -(M n t - F t) from by ring,
                      MeasureTheory.eLpNorm_neg]
          · refine le_of_eq (MeasureTheory.eLpNorm_congr_ae ?_)
            exact ((hM n).condExp_ae_eq hst).sub (Filter.EventuallyEq.refl _ (F s))
  -- Send `n → ∞`: the bound tends to `0`, so the (constant) target seminorm is `0`.
  have hzero : MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ = 0 := by
    have htend2 : Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ
          + MeasureTheory.eLpNorm (M n s - F s) 1 μ) Filter.atTop (nhds 0) := by
      simpa using (htend t).add (htend s)
    refine le_antisymm ?_ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend2
      (Filter.Eventually.of_forall hbound)
  rw [MeasureTheory.eLpNorm_eq_zero_iff haesm (by norm_num)] at hzero
  filter_upwards [hzero] with ω hω
  simpa [Pi.sub_apply, sub_eq_zero] using hω

/-- A uniform second-moment bound gives uniform integrability at exponent one.
The bound is on an actual integral, with integrability supplied explicitly. -/
theorem uniformIntegrable_of_sq_integral_le
    {P : Measure Ω} [IsFiniteMeasure P] {f : ℕ → Ω → ℝ} {C : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hsq : ∀ n, Integrable (fun ω => (f n ω) ^ 2) P)
    (hbound : ∀ n, (∫ ω, (f n ω) ^ 2 ∂P) ≤ C) :
    UniformIntegrable f 1 P := by
  apply uniformIntegrable_of (by norm_num) (by norm_num) hf
  intro ε hε
  let R : ℝ := (max C 0 + 1) / ε
  have hR : 0 < R := div_pos (by positivity) hε
  refine ⟨⟨R, hR.le⟩, fun n => ?_⟩
  let g : Ω → ℝ := {ω | (⟨R, hR.le⟩ : ℝ≥0) ≤ ‖f n ω‖₊}.indicator (f n)
  have hpoint : ∀ ω, ‖g ω‖ ≤ (f n ω) ^ 2 / R := by
    intro ω
    by_cases hω : (⟨R, hR.le⟩ : ℝ≥0) ≤ ‖f n ω‖₊
    · have hlarge : R ≤ |f n ω| := by exact_mod_cast hω
      simp only [g, mem_setOf_eq, hω, indicator_of_mem, Real.norm_eq_abs]
      apply (le_div_iff₀ hR).mpr
      nlinarith [abs_nonneg (f n ω), sq_abs (f n ω)]
    · simp only [g, mem_setOf_eq, hω, not_false_eq_true, indicator_of_notMem, norm_zero]
      exact div_nonneg (sq_nonneg _) hR.le
  have hnorm : eLpNorm g 1 P ≤ ENNReal.ofReal (C / R) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc
      ∫⁻ ω, ‖g ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ 2 / R) ∂P := by
        apply lintegral_mono
        intro ω
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hpoint ω)
      _ = ENNReal.ofReal (∫ ω, (f n ω) ^ 2 / R ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal ((hsq n).div_const R)
          (ae_of_all _ (fun ω => div_nonneg (sq_nonneg _) hR.le))).symm
      _ ≤ ENNReal.ofReal (C / R) := by
        rw [integral_div]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hbound n) hR.le)
  have hCR : C / R ≤ ε := by
    apply (div_le_iff₀ hR).mpr
    have hcancel : ε * R = max C 0 + 1 := by dsimp [R]; field_simp
    rw [hcancel]
    exact (le_max_left C 0).trans (by linarith)
  exact hnorm.trans (ENNReal.ofReal_le_ofReal hCR)

/-- A martingale limit with a uniform square-moment bound. The limit's
integrability is produced, rather than carried as a separate premise. -/
theorem martingale_of_ae_limit_of_sq_integral_le
    {P : Measure Ω} [IsFiniteMeasure P] {ι : Type*} [Preorder ι]
    (F : Filtration ι ‹MeasurableSpace Ω›)
    (Z : ℕ → ι → Ω → ℝ) (E : ι → Ω → ℝ)
    (hZ : ∀ n, Martingale (Z n) F P)
    (hE : StronglyAdapted F E)
    (hsq : ∀ n t, Integrable (fun ω => (Z n t ω) ^ 2) P)
    (hbound : ∀ t, ∃ C : ℝ, ∀ n, (∫ ω, (Z n t ω) ^ 2 ∂P) ≤ C)
    (hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Z n t ω) atTop (nhds (E t ω))) :
    Martingale E F P := by
  have hui : ∀ t, UniformIntegrable (fun n => Z n t) 1 P := by
    intro t
    obtain ⟨C, hC⟩ := hbound t
    exact uniformIntegrable_of_sq_integral_le
      (fun n => (hZ n).integrable t |>.aestronglyMeasurable) (fun n => hsq n t) hC
  have hint : ∀ t, Integrable (E t) P :=
    fun t => (hui t).integrable_of_ae_tendsto (hlim t)
  apply martingale_of_tendsto_eLpNorm_one hZ
    (fun n t => (hZ n).integrable t) hE hint
  intro t
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (hZ n).integrable t |>.aestronglyMeasurable)
    (memLp_one_iff_integrable.mpr (hint t)) (hui t).2.1 (hlim t)

/-- Uniform exponential moment control is supplied by the doubled-parameter
exponential, not by a Gaussian-law claim for a random stochastic integral. -/
theorem exponential_sq_bound {P : Measure Ω} [IsFiniteMeasure P]
    (M Q : Ω → ℝ) (lam b : ℝ)
    (hM : AEStronglyMeasurable M P) (hQ : AEStronglyMeasurable Q P)
    (hQle : ∀ᵐ ω ∂P, Q ω ≤ b)
    (hdouble : Integrable (fun ω => Real.exp ((2 * lam) * M ω - (2 * lam) ^ 2 * Q ω / 2)) P)
    (hmean : (∫ ω, Real.exp ((2 * lam) * M ω - (2 * lam) ^ 2 * Q ω / 2) ∂P) = 1) :
    Integrable (fun ω => (Real.exp (lam * M ω - lam ^ 2 * Q ω / 2)) ^ 2) P ∧
      (∫ ω, (Real.exp (lam * M ω - lam ^ 2 * Q ω / 2)) ^ 2 ∂P) ≤ Real.exp (lam ^ 2 * b) := by
  let E : Ω → ℝ := fun ω => (Real.exp (lam * M ω - lam ^ 2 * Q ω / 2)) ^ 2
  let D : Ω → ℝ := fun ω => Real.exp (lam ^ 2 * b) *
    Real.exp ((2 * lam) * M ω - (2 * lam) ^ 2 * Q ω / 2)
  have hD : Integrable D P := hdouble.const_mul _
  have hle : E ≤ᵐ[P] D := by
    filter_upwards [hQle] with ω hω
    dsimp [E, D]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hω (sq_nonneg lam)
    norm_num
    nlinarith
  have hinner : AEStronglyMeasurable
      (fun ω => lam * M ω - lam ^ 2 * Q ω / 2) P :=
    ((hM.aemeasurable.const_mul lam).sub
      ((hQ.aemeasurable.const_mul (lam ^ 2)).div_const 2)).aestronglyMeasurable
  have hE : Integrable E P := hD.mono'
    ((Real.continuous_exp.comp_aestronglyMeasurable hinner).pow 2)
    (by
      filter_upwards [hle] with ω hω
      rw [Real.norm_of_nonneg (show 0 ≤ E ω from sq_nonneg _)]
      exact hω)
  refine ⟨hE, (integral_mono_ae hE hD hle).trans_eq ?_⟩
  dsimp [D]
  rw [integral_const_mul, hmean, mul_one]

/-- A bounded bracket and a normalized exponential yield the sub-Gaussian
MGF bound. This is used only after normalization has been proved. -/
theorem exponential_moment_bound {P : Measure Ω} [IsFiniteMeasure P]
    (M Q : Ω → ℝ) (lam b : ℝ) (hM : AEStronglyMeasurable M P)
    (hQle : ∀ᵐ ω ∂P, Q ω ≤ b)
    (hZint : Integrable (fun ω => Real.exp (lam * M ω - lam ^ 2 * Q ω / 2)) P)
    (hZmean : (∫ ω, Real.exp (lam * M ω - lam ^ 2 * Q ω / 2) ∂P) = 1) :
    Integrable (fun ω => Real.exp (lam * M ω)) P ∧
      (∫ ω, Real.exp (lam * M ω) ∂P) ≤ Real.exp (lam ^ 2 * b / 2) := by
  let D : Ω → ℝ := fun ω => Real.exp (lam ^ 2 * b / 2) *
    Real.exp (lam * M ω - lam ^ 2 * Q ω / 2)
  have hD : Integrable D P := hZint.const_mul _
  have hle : (fun ω => Real.exp (lam * M ω)) ≤ᵐ[P] D := by
    filter_upwards [hQle] with ω hω
    dsimp [D]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hω (sq_nonneg lam)
    linarith
  have hint : Integrable (fun ω => Real.exp (lam * M ω)) P :=
    hD.mono' (Real.continuous_exp.comp_aestronglyMeasurable (hM.const_mul lam))
      (by filter_upwards [hle] with ω hω; simpa [Real.norm_of_nonneg (Real.exp_nonneg _)] using hω)
  refine ⟨hint, (integral_mono_ae hint hD hle).trans_eq ?_⟩
  dsimp [D]
  rw [integral_const_mul, hZmean, mul_one]

end Ripple.Stochastic.ExponentialMartingaleLimit
