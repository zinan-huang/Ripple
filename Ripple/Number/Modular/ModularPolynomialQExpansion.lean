import Ripple.Number.Modular.KleinJ
import Ripple.Number.Modular.ModularPoly41Data
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Data.List.GetD

/-!
# Formal q-expansion target for the level-41 modular-polynomial input

This file sets up the formal power-series expression obtained from
`Phi_41(E4^3 / Delta, E4^3 / Delta)` after clearing denominators and using
`Q = exp(2 pi i tau / 41)`.  In this variable the first point contributes
`q = Q^41`, while the second contributes `q = Q`.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open PowerSeries
open EisensteinSeries
open CongruenceSubgroup
open UpperHalfPlane
open Filter
open scoped UpperHalfPlane
open scoped MatrixGroups
open scoped Manifold
open scoped ModularForm
open scoped PowerSeries.WithPiTopology

/-! ### Compatibility shims for the Mathlib `v4.30.0` q-expansion API.

The `q`-expansion / cusp-function machinery was relocated from the
`ModularFormClass` / `SlashInvariantFormClass` namespaces to `UpperHalfPlane`,
and several lemmas were restated in terms of analyticity/periodicity hypotheses
rather than a `strictPeriods` membership.  The shims below restore the previous
interface for the level-one (`𝒮ℒ`) forms used in this file, so the downstream
proofs go through unchanged. -/

namespace ModularFormClass

/-- `1 ∈ (𝒮ℒ).strictPeriods`, the level-one strict period (compat alias for
`one_mem_strictPeriods_SL`). -/
theorem one_mem_strictPeriods_SL2Z :
    (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
  one_mem_strictPeriods_SL

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-- The `q`-expansion of a modular form (compat alias). -/
noncomputable def qExpansion (h : ℝ) (f : ℍ → ℂ) : PowerSeries ℂ :=
  UpperHalfPlane.qExpansion h f

@[simp] lemma qExpansion_eq (h : ℝ) (f : ℍ → ℂ) :
    qExpansion h f = UpperHalfPlane.qExpansion h f := rfl

/-- Zeroth `q`-coefficient equals the value at `∞` (compat form). -/
theorem qExpansion_coeff_zero [SlashInvariantFormClass F (𝒮ℒ) k]
    [ModularFormClass F (𝒮ℒ) k] (f : F) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods) :
    (qExpansion h (f : ℍ → ℂ)).coeff 0 = UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) :=
  UpperHalfPlane.qExpansion_coeff_zero hh
    (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)

/-- `hasSum` for the `q`-expansion (compat form). -/
theorem hasSum_qExpansion [SlashInvariantFormClass F (𝒮ℒ) k]
    [ModularFormClass F (𝒮ℒ) k] (f : F) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion h (f : ℍ → ℂ)).coeff m
        • Function.Periodic.qParam h τ ^ m) ((f : ℍ → ℂ) τ) :=
  UpperHalfPlane.hasSum_qExpansion hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

/-- The `q`-expansion as a `FormalMultilinearSeries` (compat alias).

The Mathlib `UpperHalfPlane.qExpansionFormalMultilinearSeries` is stated for a
general `FunLike F ℍ ℂ` argument, so we inline its definition (`ofScalars` of the
`q`-expansion coefficients) for the `ℍ → ℂ` interface used here. -/
noncomputable def qExpansionFormalMultilinearSeries (h : ℝ) (f : ℍ → ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ fun m ↦ (UpperHalfPlane.qExpansion h f).coeff m

/-- Coefficients of the compat `FormalMultilinearSeries` (compat alias). -/
@[simp] lemma qExpansionFormalMultilinearSeries_coeff (h : ℝ) (f : ℍ → ℂ) (m : ℕ) :
    (qExpansionFormalMultilinearSeries h f).coeff m = (qExpansion h f).coeff m := by
  simp [qExpansionFormalMultilinearSeries, qExpansion, FormalMultilinearSeries.coeff_ofScalars]

/-- Norm of the compat `FormalMultilinearSeries` applied to `m` arguments (compat alias). -/
lemma qExpansionFormalMultilinearSeries_apply_norm (h : ℝ) (f : ℍ → ℂ) (m : ℕ) :
    ‖qExpansionFormalMultilinearSeries h f m‖ = ‖(qExpansion h f).coeff m‖ := by
  rw [qExpansionFormalMultilinearSeries,
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
  simp [qExpansion]

/-- Radius lower bound for the compat `FormalMultilinearSeries` (compat alias). -/
lemma qExpansionFormalMultilinearSeries_radius {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) {h : ℝ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    1 ≤ (qExpansionFormalMultilinearSeries h (f : ℍ → ℂ)).radius := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  exact UpperHalfPlane.qExpansionFormalMultilinearSeries_radius (f := f) hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)

/-- The `hasFPowerSeriesOnBall` statement for the cusp function (compat form). -/
theorem hasFPowerSeries_cuspFunction [SlashInvariantFormClass F (𝒮ℒ) k]
    [ModularFormClass F (𝒮ℒ) k] (f : F) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods) :
    HasFPowerSeriesOnBall (UpperHalfPlane.cuspFunction h (f : ℍ → ℂ))
      (qExpansionFormalMultilinearSeries h (f : ℍ → ℂ)) 0 1 := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hanalytic := ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
  have hsum := hasSum_qExpansion f hh hΓ
  have hball := UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction (f := (f : ℍ → ℂ))
    (c := fun m ↦ (UpperHalfPlane.qExpansion h (f : ℍ → ℂ)).coeff m) hh hanalytic hsum
  exact hball

end ModularFormClass

namespace SlashInvariantFormClass

/-- The cusp function (compat alias). -/
noncomputable def cuspFunction (h : ℝ) (f : ℍ → ℂ) : ℂ → ℂ :=
  UpperHalfPlane.cuspFunction h f

@[simp] lemma cuspFunction_eq (h : ℝ) (f : ℍ → ℂ) :
    cuspFunction h f = UpperHalfPlane.cuspFunction h f := rfl

end SlashInvariantFormClass

theorem isZeroAtImInfty_of_exp_decay {E : Type*} [NormedAddCommGroup E] {f : ℍ → E}
    (hf : ∃ c > 0, f =O[UpperHalfPlane.atImInfty] fun τ ↦ Real.exp (-c * τ.im)) :
  UpperHalfPlane.IsZeroAtImInfty f := by
  obtain ⟨a, ha, ha'⟩ := hf
  refine ha'.trans_tendsto <| (Real.tendsto_exp_atBot.comp ?_).comp tendsto_comap
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha)

theorem levelOne_modularForm_slash_action_SL {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) :
    (f : ℍ → ℂ) ∣[k] γ = f :=
  SlashInvariantForm.slash_action_eqn f _ (by simpa using mem_Gamma_one γ)

theorem levelOne_modularForm_isZeroAtImInfty_of_valueAtInfty_eq_zero {k : ℤ}
    (f : ModularForm 𝒮ℒ k)
    (h : UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) = 0) :
    UpperHalfPlane.IsZeroAtImInfty (f : ℍ → ℂ) := by
  apply isZeroAtImInfty_of_exp_decay
  have hdec := ModularFormClass.exp_decay_sub_atImInfty' f
  simpa [h] using hdec

theorem levelOne_modularForm_tendsto_valueAtInfty {k : ℤ}
    (f : ModularForm 𝒮ℒ k) :
    Filter.Tendsto (f : ℍ → ℂ) UpperHalfPlane.atImInfty
      (nhds (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))) := by
  have hzero :
      UpperHalfPlane.IsZeroAtImInfty
        (fun z : ℍ => f z - UpperHalfPlane.valueAtInfty (f : ℍ → ℂ)) := by
    apply isZeroAtImInfty_of_exp_decay
    exact ModularFormClass.exp_decay_sub_atImInfty' f
  rw [UpperHalfPlane.IsZeroAtImInfty] at hzero
  simpa using hzero.add_const (UpperHalfPlane.valueAtInfty (f : ℍ → ℂ))

theorem E4_tendsto_one_atImInfty :
    Filter.Tendsto (E4 : ℍ → ℂ) UpperHalfPlane.atImInfty (nhds 1) := by
  have hval : UpperHalfPlane.valueAtInfty (E4 : ℍ → ℂ) = 1 := by
    rw [← ModularFormClass.qExpansion_coeff_zero E4 one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z]
    exact EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4)
      (by norm_num : Even 4)
  simpa [hval] using levelOne_modularForm_tendsto_valueAtInfty E4

theorem E6_tendsto_one_atImInfty :
    Filter.Tendsto (E6 : ℍ → ℂ) UpperHalfPlane.atImInfty (nhds 1) := by
  have hval : UpperHalfPlane.valueAtInfty (E6 : ℍ → ℂ) = 1 := by
    rw [← ModularFormClass.qExpansion_coeff_zero E6 one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z]
    simpa [E6] using EisensteinSeries.E_qExpansion_coeff_zero (k := 6)
      (by norm_num) (by norm_num)
  simpa [hval] using levelOne_modularForm_tendsto_valueAtInfty E6

private lemma norm_qParam_eq (z : ℍ) :
    ‖Function.Periodic.qParam 1 (z : ℂ)‖ = Real.exp (-2 * Real.pi * z.im) := by
  simp only [Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]

theorem E2_eq_one_sub_sigma_qExpansion (z : ℍ) :
    EisensteinSeries.E2 z =
      1 - 24 * ∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ) := by
  change (1 / (2 * riemannZeta 2)) * EisensteinSeries.G2 z = _
  rw [EisensteinSeries.G2_eq_tsum_cexp]
  simp_rw [show ∀ n : ℕ+,
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) ^ (n : ℕ) =
        Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ) by
    intro n
    congr 1
    simp [Function.Periodic.qParam]]
  rw [riemannZeta_two]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

theorem E2_sigma_qExpansion_summable (z : ℍ) :
    Summable fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℂ) *
      Function.Periodic.qParam 1 (z : ℂ) ^ n := by
  let q := Function.Periodic.qParam 1 (z : ℂ)
  have hq : ‖q‖ < 1 := by
    simpa [q] using UpperHalfPlane.norm_qParam_lt_one 1 z
  have hgeom : Summable fun n : ℕ => ‖((n : ℂ) ^ 2) * q ^ n‖ := by
    simpa using (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℂ) 2 hq)
  refine hgeom.of_norm_bounded ?_
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  have hsigma :
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
  gcongr

theorem E2_qExpansion_hasSum (z : ℍ) :
    HasSum (fun n : ℕ => (if n = 0 then (1 : ℂ)
        else (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ)) *
        Function.Periodic.qParam 1 (z : ℂ) ^ n)
      (EisensteinSeries.E2 z) := by
  let q := Function.Periodic.qParam 1 (z : ℂ)
  let aNat : ℕ → ℂ := fun n => (ArithmeticFunction.sigma 1 n : ℂ) * q ^ n
  let f : ℕ → ℂ := fun n => (if n = 0 then (1 : ℂ)
        else (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ)) * q ^ n
  let tailNat : ℕ → ℂ := fun n => (-24 : ℂ) * aNat (n + 1)
  have hsummNat : Summable aNat := by
    simpa [aNat, q] using E2_sigma_qExpansion_summable z
  have htail_summ : Summable tailNat := by
    have hs : Summable fun n : ℕ => aNat (n + 1) :=
      (summable_nat_add_iff 1).mpr hsummNat
    simpa [tailNat] using Summable.mul_left (-24 : ℂ) hs
  have htail_tsum :
      (∑' n : ℕ, tailNat n) = (-24 : ℂ) * ∑' n : ℕ+, aNat n := by
    calc
      (∑' n : ℕ, tailNat n) =
          ∑' n : ℕ, (-24 : ℂ) * aNat (n + 1) := by simp [tailNat]
      _ = (-24 : ℂ) * ∑' n : ℕ, aNat (n + 1) := by rw [tsum_mul_left]
      _ = (-24 : ℂ) * ∑' n : ℕ+, aNat n := by
          rw [← tsum_pnat_eq_tsum_succ (f := aNat)]
  have htail : HasSum tailNat (EisensteinSeries.E2 z - 1) := by
    have htsum : HasSum tailNat (∑' n : ℕ, tailNat n) := htail_summ.hasSum
    convert htsum using 1
    rw [E2_eq_one_sub_sigma_qExpansion z, htail_tsum]
    simp [aNat, q]
  have htail_f : HasSum (fun n => f (n + 1)) (EisensteinSeries.E2 z - 1) := by
    convert htail using 1
    ext n
    simp [f, tailNat, aNat, q]
    ring
  have hfull := (hasSum_nat_add_iff 1).mp htail_f
  have hfull' : HasSum f (EisensteinSeries.E2 z) := by
    convert hfull using 1
    simp [f]
  convert hfull' using 1

private lemma summable_pnat_sq_exp_neg_two_pi :
    Summable fun n : ℕ+ =>
      ((n : ℕ) : ℝ) ^ 2 * Real.exp (-(2 * Real.pi) * (n : ℕ)) := by
  let f : ℕ → ℝ := fun m => (m : ℝ) ^ 2 * Real.exp (-(2 * Real.pi) * m)
  change Summable fun n : ℕ+ => f n
  exact (summable_pnat_iff_summable_succ (f := f)).mpr <|
    (summable_nat_add_iff 1).mpr
      (Real.summable_pow_mul_exp_neg_nat_mul 2
        (by positivity : (0 : ℝ) < 2 * Real.pi))

private lemma E2_sigma_term_bound_of_one_le_im
    (z : ℍ) (hz : (1 : ℝ) ≤ z.im) (n : ℕ+) :
    ‖(ArithmeticFunction.sigma 1 n : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ)‖ ≤
      ((n : ℕ) : ℝ) ^ 2 * Real.exp (-(2 * Real.pi) * (n : ℕ)) := by
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  have hsigma :
      ((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 (n : ℕ)
  have hq :
      ‖Function.Periodic.qParam 1 (z : ℂ)‖ ≤ Real.exp (-(2 * Real.pi)) := by
    rw [norm_qParam_eq]
    apply Real.exp_le_exp_of_le
    nlinarith [hz, Real.pi_pos]
  calc ((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℝ) *
        ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ (n : ℕ)
      ≤ ((n : ℕ) : ℝ) ^ 2 * (Real.exp (-(2 * Real.pi))) ^ (n : ℕ) := by
        gcongr
    _ = ((n : ℕ) : ℝ) ^ 2 * Real.exp (-(2 * Real.pi) * (n : ℕ)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

theorem E2_isBoundedAtImInfty :
    UpperHalfPlane.IsBoundedAtImInfty EisensteinSeries.E2 := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  let B : ℝ :=
    ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ 2 * Real.exp (-(2 * Real.pi) * (n : ℕ))
  refine ⟨1 + 24 * B, 1, ?_⟩
  intro z hz
  rw [E2_eq_one_sub_sigma_qExpansion z]
  let S : ℂ :=
    ∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) *
      Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ)
  have hterm : ∀ n : ℕ+,
      ‖(ArithmeticFunction.sigma 1 n : ℂ) *
          Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ)‖ ≤
        ((n : ℕ) : ℝ) ^ 2 * Real.exp (-(2 * Real.pi) * (n : ℕ)) :=
    E2_sigma_term_bound_of_one_le_im z hz
  have hsumm_bound := summable_pnat_sq_exp_neg_two_pi
  have hsumm_terms :
      Summable fun n : ℕ+ => (ArithmeticFunction.sigma 1 n : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ) :=
    hsumm_bound.of_norm_bounded hterm
  have hS_bound : ‖S‖ ≤ B := by
    exact hsumm_terms.hasSum.norm_le_of_bounded hsumm_bound.hasSum hterm
  calc ‖1 - 24 * S‖
      ≤ ‖(1 : ℂ)‖ + ‖(24 : ℂ) * S‖ := norm_sub_le _ _
    _ = 1 + 24 * ‖S‖ := by norm_num [norm_mul]
    _ ≤ 1 + 24 * B := by gcongr

theorem E2_tendsto_one_atImInfty :
    Filter.Tendsto EisensteinSeries.E2 UpperHalfPlane.atImInfty (nhds 1) := by
  have hS0 : Filter.Tendsto
      (fun z : ℍ => ∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ))
      UpperHalfPlane.atImInfty (nhds 0) := by
    have hterm : ∀ n : ℕ+, Filter.Tendsto
        (fun z : ℍ => (ArithmeticFunction.sigma 1 n : ℂ) *
          Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ))
        UpperHalfPlane.atImInfty (nhds 0) := by
      intro n
      have hq0 : Filter.Tendsto
          (fun z : ℍ => Function.Periodic.qParam 1 (z : ℂ))
          UpperHalfPlane.atImInfty (nhds 0) :=
        UpperHalfPlane.qParam_tendsto_atImInfty one_pos
      have hpow := hq0.pow (n : ℕ)
      have hnpos : (n : ℕ) ≠ 0 := PNat.ne_zero n
      simpa [hnpos] using hpow.const_mul (ArithmeticFunction.sigma 1 n : ℂ)
    have hbound : ∀ᶠ (z : ℍ) in UpperHalfPlane.atImInfty, ∀ n : ℕ+,
        ‖(ArithmeticFunction.sigma 1 n : ℂ) *
          Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ)‖ ≤
        ((n : ℕ) : ℝ) ^ 2 * Real.exp (-(2 * Real.pi) * (n : ℕ)) := by
      exact (UpperHalfPlane.atImInfty_mem _).mpr
        ⟨1, fun z hz n => E2_sigma_term_bound_of_one_le_im z hz n⟩
    simpa using
      (tendsto_tsum_of_dominated_convergence
        (α := ℍ) (β := ℕ+) (G := ℂ) (𝓕 := UpperHalfPlane.atImInfty)
        (f := fun z : ℍ => fun n : ℕ+ => (ArithmeticFunction.sigma 1 n : ℂ) *
          Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ))
        (g := fun _ : ℕ+ => (0 : ℂ))
        (bound := fun n : ℕ+ =>
          ((n : ℕ) : ℝ) ^ 2 * Real.exp (-(2 * Real.pi) * (n : ℕ)))
        summable_pnat_sq_exp_neg_two_pi hterm hbound)
  have hmain : Filter.Tendsto
      (fun z : ℍ => 1 - 24 * (∑' n : ℕ+, (ArithmeticFunction.sigma 1 n : ℂ) *
        Function.Periodic.qParam 1 (z : ℂ) ^ (n : ℕ)))
      UpperHalfPlane.atImInfty (nhds 1) := by
    simpa using (tendsto_const_nhds.sub (hS0.const_mul (24 : ℂ)))
  exact hmain.congr'
    (Filter.Eventually.of_forall (fun z => by rw [E2_eq_one_sub_sigma_qExpansion z]))

theorem levelOne_isBoundedAt_of_slash_invariant_of_boundedAtInfty {k : ℤ}
    {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[k] γ = f)
    (hinfty : UpperHalfPlane.IsBoundedAtImInfty f)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsBoundedAt f k := by
  have hc' : IsCusp c 𝒮ℒ := hc
  rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc']
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc'
  exact ⟨γ, hγ.symm, by
    rw [hslash γ]
    exact hinfty⟩

theorem E2_slash_correction_eq_normalized_derivative_correction
    (γ : SL(2, ℤ)) (z : ℍ) :
    (12 : ℂ)⁻¹ * (1 / (2 * riemannZeta 2)) * EisensteinSeries.D2 γ z =
      - ((2 * Real.pi * Complex.I)⁻¹ *
          ((γ 1 0 : ℂ) / UpperHalfPlane.denom γ z)) := by
  rw [EisensteinSeries.D2]
  rw [riemannZeta_two]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.I_ne_zero,
    UpperHalfPlane.denom_ne_zero γ z]
  ring_nf
  rw [show Complex.I ^ 2 = -1 by simp]
  ring

private lemma deriv_denom_SL (γ : SL(2, ℤ)) (z : ℂ) :
    deriv (fun w => UpperHalfPlane.denom γ w) z =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  simp only [UpperHalfPlane.denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id]
  simp

private lemma differentiableAt_denom_SL (γ : SL(2, ℤ)) (z : ℂ) :
    DifferentiableAt ℂ (fun w => UpperHalfPlane.denom γ w) z := by
  simp only [UpperHalfPlane.denom]
  fun_prop

private lemma deriv_denom_zpow_SL (γ : SL(2, ℤ)) (k : ℤ) (z : ℍ) :
    deriv (fun w => (UpperHalfPlane.denom γ w) ^ (-k)) z =
      (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) *
        (UpperHalfPlane.denom γ z) ^ (-k - 1) := by
  have hz : UpperHalfPlane.denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdiff := differentiableAt_denom_SL γ (z : ℂ)
  have hderiv_zpow := hasDerivAt_zpow (-k) (UpperHalfPlane.denom γ z) (Or.inl hz)
  have hderiv_denom :
      HasDerivAt (fun w => UpperHalfPlane.denom γ w)
        ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) (z : ℂ) := by
    rw [← deriv_denom_SL]
    exact hdiff.hasDerivAt
  have hcomp := hderiv_zpow.comp (z : ℂ) hderiv_denom
  have heq :
      (fun w => w ^ (-k)) ∘ (fun w => UpperHalfPlane.denom γ w) =
        (fun w => (UpperHalfPlane.denom γ w) ^ (-k)) := rfl
  rw [← heq, hcomp.deriv]
  simp only [Int.cast_neg]
  ring

private lemma differentiableAt_denom_zpow_SL (γ : SL(2, ℤ)) (k : ℤ) (z : ℍ) :
    DifferentiableAt ℂ (fun w => (UpperHalfPlane.denom γ w) ^ (-k)) z :=
  DifferentiableAt.zpow (differentiableAt_denom_SL γ z)
    (Or.inl (UpperHalfPlane.denom_ne_zero γ z))

private lemma det_map_SL_complex (γ : SL(2, ℤ)) :
    (((γ : Matrix (Fin 2) (Fin 2) ℤ).map fun x => (x : ℝ)).det : ℂ) = 1 := by
  have hreal :
      (((γ : Matrix (Fin 2) (Fin 2) ℤ).map fun x => (x : ℝ)).det) = (1 : ℝ) := by
    rw [← Int.cast_det]
    exact_mod_cast Matrix.SpecialLinearGroup.det_coe γ
  exact_mod_cast hreal

theorem normalizedDeriv_slash_action_SL (k : ℤ) (F : ℍ → ℂ)
    (hF : MDiff F) (γ : SL(2, ℤ)) :
    Derivative.normalizedDerivOfComplex (F ∣[k] γ) =
      (Derivative.normalizedDerivOfComplex F ∣[k + 2] γ) -
        (fun z : ℍ => (k : ℂ) * (2 * Real.pi * Complex.I)⁻¹ *
          ((γ 1 0 : ℂ) / UpperHalfPlane.denom γ z) * (F ∣[k] γ) z) := by
  ext z
  let g : GL (Fin 2) ℝ :=
    Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)
  have hzof : UpperHalfPlane.ofComplex (z : ℂ) = z :=
    UpperHalfPlane.ofComplex_apply z
  have hgz : g • z = γ • z := by simp [g]
  have hgzof : g • UpperHalfPlane.ofComplex (z : ℂ) = γ • z := by
    simpa [hzof] using hgz
  have heqfun :
      (fun w : ℂ => F (g • UpperHalfPlane.ofComplex w)) =
        ((F ∘ UpperHalfPlane.ofComplex) ∘
          (fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ))) := by
    funext w
    simp [UpperHalfPlane.ofComplex_apply]
  unfold Derivative.normalizedDerivOfComplex
  simp only [Pi.sub_apply]
  have hz_denom_ne : UpperHalfPlane.denom γ z ≠ 0 :=
    UpperHalfPlane.denom_ne_zero γ z
  have hdet_pos : (0 : ℝ) < ((g : GL (Fin 2) ℝ).det).val := by
    simp [g]
  have hcomp :
      deriv (((F ∣[k] γ)) ∘ UpperHalfPlane.ofComplex) z =
        deriv
          (fun w =>
            F (g • (UpperHalfPlane.ofComplex w)) * (UpperHalfPlane.denom γ w) ^ (-k))
          z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    simp [g]
  rw [hcomp]
  have hdiff_smul :
      DifferentiableAt ℂ (fun w : ℂ => F (g • UpperHalfPlane.ofComplex w)) z := by
    rw [heqfun]
    have hFgz :
        DifferentiableAt ℂ (F ∘ UpperHalfPlane.ofComplex)
          (((g • UpperHalfPlane.ofComplex (z : ℂ)) : ℍ) : ℂ) :=
      UpperHalfPlane.mdifferentiableAt_iff.mp
        (hF (g • UpperHalfPlane.ofComplex (z : ℂ)))
    have hsmul :
        DifferentiableAt ℂ
          (fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) z :=
      (UpperHalfPlane.hasStrictDerivAt_smul hdet_pos z).hasDerivAt.differentiableAt
    exact hFgz.comp (z : ℂ) hsmul
  have hpowdiff := differentiableAt_denom_zpow_SL γ k z
  rw [show
      (fun w => F (g • UpperHalfPlane.ofComplex w) * UpperHalfPlane.denom γ w ^ (-k)) =
        (fun w => F (g • UpperHalfPlane.ofComplex w)) *
          (fun w => UpperHalfPlane.denom γ w ^ (-k)) from rfl]
  rw [deriv_mul hdiff_smul hpowdiff]
  have hderiv_smul :
      deriv (fun w : ℂ => F (g • UpperHalfPlane.ofComplex w)) z =
        deriv (F ∘ UpperHalfPlane.ofComplex)
          (((g • UpperHalfPlane.ofComplex (z : ℂ)) : ℍ) : ℂ) *
          (1 / (UpperHalfPlane.denom γ z) ^ 2) := by
    rw [heqfun]
    have hFgz :
        DifferentiableAt ℂ (F ∘ UpperHalfPlane.ofComplex)
          (((g • UpperHalfPlane.ofComplex (z : ℂ)) : ℍ) : ℂ) :=
      UpperHalfPlane.mdifferentiableAt_iff.mp
        (hF (g • UpperHalfPlane.ofComplex (z : ℂ)))
    have hder := (hFgz.hasDerivAt.comp (z : ℂ)
      (UpperHalfPlane.hasStrictDerivAt_smul hdet_pos z).hasDerivAt).deriv
    simpa [UpperHalfPlane.deriv_smul hdet_pos z, g, det_map_SL_complex γ, one_div]
      using hder
  rw [hderiv_smul, deriv_denom_zpow_SL γ k z]
  have hpow_combine :
      1 / (UpperHalfPlane.denom γ z) ^ 2 * (UpperHalfPlane.denom γ z) ^ (-k) =
        (UpperHalfPlane.denom γ z) ^ (-(k + 2)) := by
    rw [one_div, ← zpow_natCast (UpperHalfPlane.denom γ z) 2, ← zpow_neg,
      ← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  have hpow_m1 :
      (UpperHalfPlane.denom γ z) ^ (-k - 1) =
        (UpperHalfPlane.denom γ z) ^ (-1 : ℤ) *
          (UpperHalfPlane.denom γ z) ^ (-k) := by
    rw [← zpow_add₀ hz_denom_ne]
    congr 1
    ring
  simp only [ModularForm.SL_slash_apply]
  rw [hgzof]
  rw [hpow_m1]
  conv_lhs =>
    rw [mul_assoc (deriv (F ∘ UpperHalfPlane.ofComplex) ↑(γ • z))
      (1 / UpperHalfPlane.denom γ ↑z ^ 2) _]
    rw [hpow_combine]
  simp only [zpow_neg_one]
  ring

theorem serreDerivative_slash_action_SL (k : ℤ) (F : ℍ → ℂ)
    (hF : MDiff F) (γ : SL(2, ℤ)) :
    Derivative.serreDerivative (k : ℂ) F ∣[k + 2] γ =
      Derivative.serreDerivative (k : ℂ) (F ∣[k] γ) := by
  have hD := normalizedDeriv_slash_action_SL k F hF γ
  have hE2 := EisensteinSeries.E2_slash_action γ
  have hmul := ModularForm.mul_slash_SL2 (2 : ℤ) k γ EisensteinSeries.E2 F
  ext z
  simp only [Derivative.serreDerivative_apply]
  have hLHS :
      (Derivative.serreDerivative (k : ℂ) F ∣[k + 2] γ) z =
        (Derivative.normalizedDerivOfComplex F ∣[k + 2] γ) z -
          (k : ℂ) * 12⁻¹ *
            ((EisensteinSeries.E2 ∣[(2 : ℤ)] γ) z * (F ∣[k] γ) z) := by
    have h := congrFun hmul z
    simp only [Pi.mul_apply, show (2 : ℤ) + k = k + 2 from by omega] at h
    simp only [ModularForm.SL_slash_apply, Derivative.serreDerivative_apply,
      Pi.mul_apply] at h ⊢
    rw [← h]
    ring
  rw [hLHS]
  let alphaD : ℂ := (1 / (2 * riemannZeta 2)) * EisensteinSeries.D2 γ z
  let corr : ℂ :=
    (2 * Real.pi * Complex.I)⁻¹ * ((γ 1 0 : ℂ) / UpperHalfPlane.denom γ z)
  have hE2z :
      (EisensteinSeries.E2 ∣[(2 : ℤ)] γ) z = EisensteinSeries.E2 z - alphaD := by
    have h := congrFun hE2 z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    simpa [alphaD] using h
  have hDz :
      Derivative.normalizedDerivOfComplex (F ∣[k] γ) z =
        (Derivative.normalizedDerivOfComplex F ∣[k + 2] γ) z -
          (k : ℂ) * corr * (F ∣[k] γ) z := by
    have h := congrFun hD z
    simpa [corr, mul_assoc] using h
  have hcorr : (12 : ℂ)⁻¹ * alphaD = -corr := by
    simpa [alphaD, corr, mul_assoc] using
      E2_slash_correction_eq_normalized_derivative_correction γ z
  rw [hE2z, hDz]
  linear_combination (k : ℂ) * (F ∣[k] γ) z * hcorr

theorem serreDerivative_slash_invariant_SL (k : ℤ) (F : ℍ → ℂ)
    (hF : MDiff F) (γ : SL(2, ℤ)) (hslash : F ∣[k] γ = F) :
    Derivative.serreDerivative (k : ℂ) F ∣[k + 2] γ =
      Derivative.serreDerivative (k : ℂ) F := by
  rw [serreDerivative_slash_action_SL k F hF γ, hslash]

private lemma diffContOnCl_comp_ofComplex_of_mdifferentiable {f : ℍ → ℂ}
    (hf : MDiff f) {c : ℂ} {R : ℝ}
    (hclosed : Metric.closedBall c R ⊆ {z : ℂ | 0 < z.im}) :
    DiffContOnCl ℂ (f ∘ UpperHalfPlane.ofComplex) (Metric.ball c R) :=
  ⟨fun z hz => (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hf ⟨z, hclosed (Metric.ball_subset_closedBall hz)⟩)).differentiableWithinAt,
   fun z hz => (UpperHalfPlane.mdifferentiableAt_iff.mp
      (hf ⟨z, hclosed (Metric.closure_ball_subset_closedBall hz)⟩)).continuousAt.continuousWithinAt⟩

private lemma closedBall_center_subset_upperHalfPlane (z : ℍ) :
    Metric.closedBall (z : ℂ) (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hdist : dist w z ≤ z.im / 2 := Metric.mem_closedBall.mp hw
  have habs : |w.im - z.im| ≤ z.im / 2 := calc
    |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
    _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    _ = dist w z := (dist_eq_norm _ _).symm
    _ ≤ z.im / 2 := hdist
  have hlower : z.im / 2 ≤ w.im := by
    linarith [(abs_le.mp habs).1]
  exact lt_of_lt_of_le (by linarith [z.im_pos] : 0 < z.im / 2) hlower

private lemma norm_normalizedDeriv_le_of_sphere_bound {f : ℍ → ℂ} {z : ℍ}
    {r M : ℝ}
    (hr : 0 < r)
    (hDiff :
      DiffContOnCl ℂ (f ∘ UpperHalfPlane.ofComplex) (Metric.ball (z : ℂ) r))
    (hbdd : ∀ w ∈ Metric.sphere (z : ℂ) r,
      ‖(f ∘ UpperHalfPlane.ofComplex) w‖ ≤ M) :
    ‖Derivative.normalizedDerivOfComplex f z‖ ≤ M / (2 * Real.pi * r) := calc
  ‖Derivative.normalizedDerivOfComplex f z‖
      = ‖(2 * Real.pi * Complex.I)⁻¹‖ *
          ‖deriv (f ∘ UpperHalfPlane.ofComplex) z‖ := by
        simp [Derivative.normalizedDerivOfComplex]
  _ = (2 * Real.pi)⁻¹ * ‖deriv (f ∘ UpperHalfPlane.ofComplex) z‖ := by
        simp [abs_of_pos Real.pi_pos]
  _ ≤ (2 * Real.pi)⁻¹ * (M / r) := by
        gcongr
        exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hDiff hbdd
  _ = M / (2 * Real.pi * r) := by ring

theorem normalizedDeriv_isBoundedAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    UpperHalfPlane.IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex f) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hbdd ⊢
  obtain ⟨M, A, hMA⟩ := hbdd
  use M / Real.pi, 2 * max A 0 + 1
  intro z hz
  have hR_pos : 0 < z.im / 2 := by linarith [z.im_pos]
  have hclosed := closedBall_center_subset_upperHalfPlane z
  have hDiff :
      DiffContOnCl ℂ (f ∘ UpperHalfPlane.ofComplex)
        (Metric.ball (z : ℂ) (z.im / 2)) :=
    diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
  have hf_bdd_sphere :
      ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2),
        ‖(f ∘ UpperHalfPlane.ofComplex) w‖ ≤ M := by
    intro w hw
    have hw_im_pos : 0 < w.im :=
      hclosed (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 := Metric.mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := by
      calc |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
        _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
        _ = dist w z := (dist_eq_norm _ _).symm
        _ = z.im / 2 := hdist
    have hw_im_ge_A : A ≤ w.im := by
      linarith [(abs_le.mp habs).1, le_max_left A 0]
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hw_im_pos] using
      hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  have hz_im_ge_1 : 1 ≤ z.im := by
    linarith [le_max_right A 0]
  have hM_nonneg : 0 ≤ M :=
    le_trans (norm_nonneg _) (hMA z (by linarith [le_max_left A 0]))
  calc ‖Derivative.normalizedDerivOfComplex f z‖
      ≤ M / (2 * Real.pi * (z.im / 2)) :=
        norm_normalizedDeriv_le_of_sphere_bound hR_pos hDiff hf_bdd_sphere
    _ = M / (Real.pi * z.im) := by ring
    _ ≤ M / (Real.pi * 1) := by gcongr
    _ = M / Real.pi := by ring

theorem normalizedDeriv_isZeroAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    UpperHalfPlane.IsZeroAtImInfty (Derivative.normalizedDerivOfComplex f) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hbdd
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  obtain ⟨M, A, hMA⟩ := hbdd
  intro ε hε
  refine ⟨max (2 * max A 0 + 1) (M / (Real.pi * ε)), ?_⟩
  intro z hz
  have hzA0 : 2 * max A 0 + 1 ≤ z.im := le_trans (le_max_left _ _) hz
  have hzM : M / (Real.pi * ε) ≤ z.im := le_trans (le_max_right _ _) hz
  have hR_pos : 0 < z.im / 2 := by linarith [z.im_pos]
  have hclosed := closedBall_center_subset_upperHalfPlane z
  have hDiff :
      DiffContOnCl ℂ (f ∘ UpperHalfPlane.ofComplex)
        (Metric.ball (z : ℂ) (z.im / 2)) :=
    diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
  have hf_bdd_sphere :
      ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2),
        ‖(f ∘ UpperHalfPlane.ofComplex) w‖ ≤ M := by
    intro w hw
    have hw_im_pos : 0 < w.im :=
      hclosed (Metric.sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 := Metric.mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := by
      calc |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
        _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
        _ = dist w z := (dist_eq_norm _ _).symm
        _ = z.im / 2 := hdist
    have hw_im_ge_A : A ≤ w.im := by
      linarith [(abs_le.mp habs).1, le_max_left A 0]
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hw_im_pos] using
      hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  have hM_nonneg : 0 ≤ M :=
    le_trans (norm_nonneg _) (hMA z (by linarith [le_max_left A 0]))
  calc ‖Derivative.normalizedDerivOfComplex f z‖
      ≤ M / (2 * Real.pi * (z.im / 2)) :=
        norm_normalizedDeriv_le_of_sphere_bound hR_pos hDiff hf_bdd_sphere
    _ = M / (Real.pi * z.im) := by ring
    _ ≤ ε := by
        rw [div_le_iff₀]
        · have hmul : M / (Real.pi * ε) * (Real.pi * ε) ≤
              z.im * (Real.pi * ε) := by
            gcongr
          field_simp [Real.pi_pos.ne', hε.ne'] at hmul
          nlinarith [hmul, Real.pi_pos, hε, hM_nonneg]
        · positivity

theorem serreDerivative_E4_isBoundedAtImInfty :
    UpperHalfPlane.IsBoundedAtImInfty (Derivative.serreDerivative (4 : ℂ) (E4 : ℍ → ℂ)) := by
  rw [UpperHalfPlane.IsBoundedAtImInfty]
  have hD :
      UpperHalfPlane.IsBoundedAtImInfty
        (Derivative.normalizedDerivOfComplex (E4 : ℍ → ℂ)) :=
    normalizedDeriv_isBoundedAtImInfty_of_bounded (ModularFormClass.holo E4)
      (ModularFormClass.bdd_at_infty E4)
  have hE2 : UpperHalfPlane.IsBoundedAtImInfty EisensteinSeries.E2 := E2_isBoundedAtImInfty
  have hE4 : UpperHalfPlane.IsBoundedAtImInfty (E4 : ℍ → ℂ) :=
    ModularFormClass.bdd_at_infty E4
  rw [UpperHalfPlane.IsBoundedAtImInfty] at hD hE2 hE4
  simpa [Derivative.serreDerivative, Pi.sub_apply, Pi.mul_apply, mul_assoc] using
    hD.sub (BoundedAtFilter.smul ((4 : ℂ) * (12 : ℂ)⁻¹) (hE2.mul hE4))

noncomputable def serreDerivativeE4ModularForm : ModularForm 𝒮ℒ 6 where
  toFun := Derivative.serreDerivative (4 : ℂ) (E4 : ℍ → ℂ)
  slash_action_eq' γ hγ := by
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hγ
    simpa [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash] using
      serreDerivative_slash_invariant_SL 4 (E4 : ℍ → ℂ)
        (ModularFormClass.holo E4) A (levelOne_modularForm_slash_action_SL E4 A)
  holo' := Derivative.serreDerivative_mdifferentiable (4 : ℂ) (ModularFormClass.holo E4)
  bdd_at_cusps' := by
    intro c hc
    exact levelOne_isBoundedAt_of_slash_invariant_of_boundedAtInfty
      (fun A => serreDerivative_slash_invariant_SL 4 (E4 : ℍ → ℂ)
        (ModularFormClass.holo E4) A (levelOne_modularForm_slash_action_SL E4 A))
      serreDerivative_E4_isBoundedAtImInfty hc

theorem serreDerivative_E4_tendsto_neg_one_third_atImInfty :
    Filter.Tendsto (Derivative.serreDerivative (4 : ℂ) (E4 : ℍ → ℂ))
      UpperHalfPlane.atImInfty (nhds (-(1 / 3 : ℂ))) := by
  have hD0 : Filter.Tendsto (Derivative.normalizedDerivOfComplex (E4 : ℍ → ℂ))
      UpperHalfPlane.atImInfty (nhds 0) :=
    normalizedDeriv_isZeroAtImInfty_of_bounded (ModularFormClass.holo E4)
      (ModularFormClass.bdd_at_infty E4)
  have hprod : Filter.Tendsto (fun z : ℍ => EisensteinSeries.E2 z * E4 z)
      UpperHalfPlane.atImInfty (nhds (1 * 1)) :=
    E2_tendsto_one_atImInfty.mul E4_tendsto_one_atImInfty
  have hmain := hD0.sub (hprod.const_mul ((4 : ℂ) * (12 : ℂ)⁻¹))
  convert hmain using 1
  · ext z
    simp [Derivative.serreDerivative, mul_assoc]
  · norm_num

theorem serreDerivativeE4_valueAtInfty :
    UpperHalfPlane.valueAtInfty (serreDerivativeE4ModularForm : ℍ → ℂ) =
      -(1 / 3 : ℂ) := by
  simpa [UpperHalfPlane.valueAtInfty, serreDerivativeE4ModularForm] using
    serreDerivative_E4_tendsto_neg_one_third_atImInfty.limUnder_eq

noncomputable def levelOneCuspFormOfValueAtInftyZero {k : ℤ}
    (f : ModularForm 𝒮ℒ k)
    (h : UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) = 0) : CuspForm 𝒮ℒ k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  zero_at_cusps' := fun {c} hc => by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z (f := f.toFun) (k := k) hc]
    intro γ _
    have hslash : f.toFun ∣[k] γ = f.toFun := by
      simpa [ModularForm.toFun_eq_coe] using levelOne_modularForm_slash_action_SL f γ
    rw [hslash]
    exact levelOne_modularForm_isZeroAtImInfty_of_valueAtInfty_eq_zero f h

theorem levelOne_weight6_sub_valueAtInfty_smul_E6_valueAtInfty
    (f : ModularForm 𝒮ℒ 6) :
    UpperHalfPlane.valueAtInfty
        ((f - UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) • E6 : ModularForm 𝒮ℒ 6) : ℍ → ℂ) =
      0 := by
  set c := UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) with hc
  -- `f` tends to `c` and `E6` tends to `1` at the cusp, so `f - c • E6` tends to `c - c • 1 = 0`.
  have hf_tend : Filter.Tendsto (f : ℍ → ℂ) UpperHalfPlane.atImInfty (nhds c) :=
    levelOne_modularForm_tendsto_valueAtInfty f
  have hE6_tend : Filter.Tendsto (E6 : ℍ → ℂ) UpperHalfPlane.atImInfty (nhds 1) :=
    E6_tendsto_one_atImInfty
  have htend :
      Filter.Tendsto ((f - c • E6 : ModularForm 𝒮ℒ 6) : ℍ → ℂ)
        UpperHalfPlane.atImInfty (nhds 0) := by
    have h0 : c - c • (1 : ℂ) = 0 := by simp
    have := hf_tend.sub ((hE6_tend.const_smul c))
    refine (h0 ▸ this).congr fun z => ?_
    simp [ModularForm.sub_apply, ModularForm.smul_apply, smul_eq_mul]
  simpa [UpperHalfPlane.valueAtInfty] using htend.limUnder_eq

lemma delta_slash_action_level_one (γ : SL(2, ℤ)) :
    ModularForm.discriminant ∣[(12 : ℤ)] γ = ModularForm.discriminant := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | one => simp
  | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hS | hT
      · simpa [hS] using ModularForm.discriminant_S_invariant
      · simpa [hT] using ModularForm.discriminant_T_invariant
  | mul g h _ _ hg hh =>
      rw [SlashAction.slash_mul, hg, hh]
  | inv g _ hg =>
      have H :
          (ModularForm.discriminant ∣[(12 : ℤ)] g) ∣[(12 : ℤ)] g⁻¹ =
            ModularForm.discriminant ∣[(12 : ℤ)] g⁻¹ := by
        rw [hg]
      simpa [← SlashAction.slash_mul] using H.symm

lemma mdiff_delta :
    MDiff (fun z : ℍ => ModularForm.discriminant z) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  change DifferentiableWithinAt ℂ
    (fun x : ℂ => ModularForm.discriminant (UpperHalfPlane.ofComplex x)) {z | 0 < z.im} z
  simp only [ModularForm.discriminant]
  have hη : DifferentiableAt ℂ ModularForm.eta z :=
    ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz
  exact (hη.pow 24).differentiableWithinAt.congr
    (fun x hx => by simp [UpperHalfPlane.ofComplex_apply_of_im_pos hx])
    (by simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz])

private lemma norm_tprod_one_sub_sub_one_le {f : ℕ → ℂ}
    (hmult : Multipliable (fun n => 1 + (-f n)))
    (hsum : Summable (fun n => ‖f n‖)) :
    ‖∏' n, (1 - f n) - 1‖ ≤ Real.exp (∑' n, ‖f n‖) - 1 := by
  have heq : (fun n => (1 : ℂ) - f n) = (fun n => 1 + (-f n)) := funext (fun n => by ring)
  rw [heq]
  apply le_of_tendsto' ((continuous_norm.tendsto _).comp
    (hmult.tendsto_prod_tprod_nat.sub tendsto_const_nhds))
  intro N
  calc ‖∏ n ∈ Finset.range N, (1 + (-f n)) - 1‖
      ≤ Real.exp (∑ n ∈ Finset.range N, ‖-f n‖) - 1 :=
        Finset.norm_prod_one_add_sub_one_le _ _
    _ ≤ Real.exp (∑' n, ‖f n‖) - 1 := by
        apply sub_le_sub_right
        apply Real.exp_le_exp_of_le
        simp_rw [norm_neg]
        exact hsum.sum_le_tsum _ (fun _ _ => norm_nonneg _)

private lemma tendsto_rexp_neg_mul_im_for_deltaLevelOneMF {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun z : ℍ => Real.exp (-c * z.im))
      UpperHalfPlane.atImInfty (nhds 0) := by
  refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((Filter.tendsto_comap (f := UpperHalfPlane.im) :
        Filter.Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty Filter.atTop).const_mul_atTop
      hc)).congr ?_
  intro z
  simp only [Function.comp_apply, neg_mul]

private lemma tendsto_eta_tprod_one_for_deltaLevelOneMF :
    Filter.Tendsto (fun z : ℍ => ∏' n, (1 - ModularForm.eta_q n (z : ℂ)))
      UpperHalfPlane.atImInfty (nhds 1) := by
  suffices h0 : Filter.Tendsto
      (fun z : ℍ => ∏' n, (1 - ModularForm.eta_q n (z : ℂ)) - 1)
      UpperHalfPlane.atImInfty (nhds (0 : ℂ)) by
    have := h0.add (tendsto_const_nhds (x := (1 : ℂ)))
    simp only [sub_add_cancel, zero_add] at this
    exact this
  apply squeeze_zero_norm
  · intro z
    exact norm_tprod_one_sub_sub_one_le
      (ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2)
      (by simpa [norm_neg] using ModularForm.summable_eta_q z)
  · have h_sum_eq : ∀ z : ℍ, ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ =
        ‖Function.Periodic.qParam 1 (z : ℂ)‖ /
          (1 - ‖Function.Periodic.qParam 1 (z : ℂ)‖) := by
      intro z
      simp only [ModularForm.eta_q, norm_pow]
      rw [show (fun n : ℕ => ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ (n + 1)) =
          (fun n => ‖Function.Periodic.qParam 1 (z : ℂ)‖ *
            ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ n)
        from funext (fun n => by ring),
        tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg _) (by
          rw [norm_qParam_eq]
          exact Real.exp_lt_one_iff.mpr (by nlinarith [z.im_pos, Real.pi_pos])),
        div_eq_mul_inv]
    simp_rw [h_sum_eq, norm_qParam_eq]
    have key : ∀ z : ℍ, -2 * Real.pi * z.im = -(2 * Real.pi) * z.im := fun _ => by ring
    simp_rw [key]
    change Filter.Tendsto
      ((fun r => Real.exp (r / (1 - r)) - 1) ∘
        (fun z : ℍ => Real.exp (-(2 * Real.pi) * z.im)))
      UpperHalfPlane.atImInfty (nhds 0)
    apply Filter.Tendsto.comp _
      (tendsto_rexp_neg_mul_im_for_deltaLevelOneMF (by positivity : 0 < 2 * Real.pi))
    have hcont : Filter.Tendsto (fun r : ℝ => Real.exp (r / (1 - r)) - 1) (nhds 0)
        (nhds (Real.exp ((0 : ℝ) / (1 - 0)) - 1)) :=
      ContinuousAt.sub
        (Real.continuous_exp.continuousAt.comp
          (continuousAt_id.div (continuousAt_const.sub continuousAt_id)
            (by norm_num : (1 : ℝ) - 0 ≠ 0)))
        continuousAt_const
    simp only [zero_div, Real.exp_zero, sub_self] at hcont
    exact hcont

private lemma tendsto_delta_zero_for_deltaLevelOneMF :
    Filter.Tendsto (fun z : ℍ => ModularForm.discriminant z)
      UpperHalfPlane.atImInfty (nhds 0) := by
  have hq : Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 (z : ℂ))
      UpperHalfPlane.atImInfty (nhds 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have hprod : Filter.Tendsto
      (fun z : ℍ => (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) ^ 24)
      UpperHalfPlane.atImInfty (nhds (1 ^ 24)) :=
    tendsto_eta_tprod_one_for_deltaLevelOneMF.pow 24
  have hmul := hq.mul hprod
  simpa only [zero_mul, one_pow] using hmul.congr' (Filter.Eventually.of_forall fun z => by
    rw [ModularForm.discriminant_eq_q_prod z,
      (ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2).tprod_pow 24])

private lemma delta_isZeroAtImInfty_for_deltaLevelOneMF :
    UpperHalfPlane.IsZeroAtImInfty (fun z : ℍ => ModularForm.discriminant z) :=
  tendsto_delta_zero_for_deltaLevelOneMF

private lemma isBoundedAtImInfty_delta_for_deltaLevelOneMF :
    UpperHalfPlane.IsBoundedAtImInfty (fun z : ℍ => ModularForm.discriminant z) :=
  delta_isZeroAtImInfty_for_deltaLevelOneMF.isBoundedAtImInfty

private lemma bddAtCusp_delta_for_deltaLevelOneMF
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsBoundedAt (fun z : ℍ => ModularForm.discriminant z) 12 := by
  have hc' : IsCusp c 𝒮ℒ := hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
  intro γ _hγ
  rw [delta_slash_action_level_one γ]
  exact isBoundedAtImInfty_delta_for_deltaLevelOneMF

noncomputable def deltaLevelOneMF : ModularForm 𝒮ℒ 12 where
  toSlashInvariantForm :=
    { toFun := fun z => ModularForm.discriminant z
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
        exact delta_slash_action_level_one g }
  holo' := mdiff_delta
  bdd_at_cusps' hc := bddAtCusp_delta_for_deltaLevelOneMF hc

private lemma eta_product_norm_eventually_ge :
    ∀ᶠ z : ℍ in UpperHalfPlane.atImInfty,
      (1 / 2 : ℝ) ≤ ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖ := by
  refine (UpperHalfPlane.atImInfty_mem _).mpr ⟨1, fun z hz => ?_⟩
  change (1 / 2 : ℝ) ≤ ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖
  have hrq : ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 := by
    rw [norm_qParam_eq]; exact Real.exp_lt_one_iff.mpr (by nlinarith [z.2, Real.pi_pos])
  have hmult : Multipliable fun n => 1 - ModularForm.eta_q n (z : ℂ) :=
    ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2
  have hsumm : Summable (fun n => ‖ModularForm.eta_q n (z : ℂ)‖) := by
    simpa [norm_neg] using ModularForm.summable_eta_q z
  have hsum_bound : ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ ≤ 1 / 4 := by
    have : ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ =
        ‖Function.Periodic.qParam 1 (z : ℂ)‖ / (1 - ‖Function.Periodic.qParam 1 (z : ℂ)‖) := by
      simp only [ModularForm.eta_q, norm_pow]
      rw [show (fun n : ℕ => ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ (n + 1)) =
          (fun n => ‖Function.Periodic.qParam 1 (z : ℂ)‖ *
            ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ n)
        from funext (fun n => by ring),
        tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg _) hrq, div_eq_mul_inv]
    rw [this]
    have hq_le : ‖Function.Periodic.qParam 1 (z : ℂ)‖ ≤ 1 / 5 := by
      rw [norm_qParam_eq]
      calc Real.exp (-2 * Real.pi * z.im)
          ≤ Real.exp (-6) := by
            apply Real.exp_le_exp_of_le
            have := Real.pi_gt_three; nlinarith
        _ ≤ 1 / 5 := by
            rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
            have h5 : (1 / 5 : ℝ)⁻¹ = 5 := by norm_num
            rw [h5]
            calc (5 : ℝ) ≤ 2 ^ 6 := by norm_num
              _ ≤ Real.exp 1 ^ 6 := by
                  apply pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
                  linarith [Real.add_one_le_exp (1 : ℝ)]
              _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
    have h1mr : (0 : ℝ) < 1 - ‖Function.Periodic.qParam 1 (z : ℂ)‖ := by linarith
    calc ‖Function.Periodic.qParam 1 (z : ℂ)‖ /
        (1 - ‖Function.Periodic.qParam 1 (z : ℂ)‖)
        ≤ (1 / 5) / (4 / 5) := by
          rw [div_le_div_iff₀ h1mr (by norm_num : (0:ℝ) < 4 / 5)]
          nlinarith [norm_nonneg (Function.Periodic.qParam 1 (z : ℂ))]
      _ = 1 / 4 := by norm_num
  have hprod_close : ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ)) - 1‖ ≤ 1 / 2 := by
    calc ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ)) - 1‖
        ≤ Real.exp (∑' n, ‖ModularForm.eta_q n (z : ℂ)‖) - 1 :=
          norm_tprod_one_sub_sub_one_le hmult hsumm
      _ ≤ 2 * ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ := by
          set S := ∑' n, ‖ModularForm.eta_q n (z : ℂ)‖ with hS_def
          have hS_nn : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
          have hS_le1 : |S| ≤ 1 := by rw [abs_of_nonneg hS_nn]; linarith [hsum_bound]
          have hab := Real.abs_exp_sub_one_le hS_le1
          rw [abs_of_nonneg (by linarith [Real.add_one_le_exp S]),
            abs_of_nonneg hS_nn] at hab
          linarith
      _ ≤ 2 * (1 / 4) := by linarith [hsum_bound]
      _ = 1 / 2 := by norm_num
  have h_tri := abs_norm_sub_norm_le (∏' n, (1 - ModularForm.eta_q n (z : ℂ))) 1
  rw [norm_one] at h_tri
  have h_abs_le : |‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖ - 1| ≤ 1 / 2 :=
    h_tri.trans hprod_close
  linarith [(abs_le.mp h_abs_le).1]

private lemma norm_delta_eq (z : ℍ) :
    ‖ModularForm.discriminant z‖ = ‖Function.Periodic.qParam 1 (z : ℂ)‖ *
      ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖ ^ 24 := by
  have hmult : Multipliable fun n => 1 - ModularForm.eta_q n (z : ℂ) :=
    ModularForm.multipliableLocallyUniformlyOn_eta.multipliable z.2
  rw [ModularForm.discriminant_eq_q_prod, norm_mul, hmult.tprod_pow 24, norm_pow]

lemma delta_norm_lower_bound :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im) ≤ ‖ModularForm.discriminant z‖ := by
  filter_upwards [eta_product_norm_eventually_ge] with z hz
  rw [norm_delta_eq, norm_qParam_eq]
  have hpow : (1 / 2 : ℝ) ^ 24 ≤ ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖ ^ 24 :=
    pow_le_pow_left₀ (by positivity) hz 24
  calc (1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im)
      ≤ ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖ ^ 24 *
          Real.exp (-2 * Real.pi * z.im) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (-2 * Real.pi * z.im) *
          ‖∏' n, (1 - ModularForm.eta_q n (z : ℂ))‖ ^ 24 := by ring

private lemma cuspForm_square_div_delta_slash_action (f : CuspForm 𝒮ℒ 6) (γ : SL(2, ℤ)) :
    (fun z : ℍ => f z ^ 2 / ModularForm.discriminant z) ∣[(0 : ℤ)] γ =
      fun z : ℍ => f z ^ 2 / ModularForm.discriminant z := by
  ext z
  have hf := SlashInvariantForm.slash_action_eqn'' f
    (Γ := 𝒮ℒ) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) z
  have hd := congrFun (delta_slash_action_level_one γ) z
  rw [ModularForm.SL_slash_apply] at hd
  rw [← MulAction.compHom_smul_def] at hf
  rw [ModularForm.SL_slash_apply, hf]
  have hdne :
      UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
          z ≠ 0 :=
    UpperHalfPlane.denom_ne_zero _ _
  have hdelg : ModularForm.discriminant (γ • z) ≠ 0 := ModularForm.discriminant_ne_zero (γ • z)
  have hdel : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  field_simp [hdne, hdelg, hdel] at hd
  ring_nf at hd
  rw [hd]
  have hmapGL :
      (Matrix.SpecialLinearGroup.mapGL ℝ) γ =
        Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ) :=
    rfl
  field_simp [hdne, hdel]
  rw [hmapGL]
  simp only [neg_zero, zpow_zero, mul_one]
  ring

private lemma mdiff_cuspForm_square_div_delta (f : CuspForm 𝒮ℒ 6) :
    MDiff (fun z : ℍ => f z ^ 2 / ModularForm.discriminant z) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hf : MDiff (f : ℍ → ℂ) := ModularFormClass.holo f
  have hf' := (UpperHalfPlane.mdifferentiable_iff.mp hf) z hz
  have hd :
      DifferentiableWithinAt ℂ
        (fun x : ℂ => ModularForm.discriminant (UpperHalfPlane.ofComplex x)) {z | 0 < z.im} z :=
    (UpperHalfPlane.mdifferentiable_iff.mp mdiff_delta) z hz
  have hdn : ModularForm.discriminant (UpperHalfPlane.ofComplex z) ≠ 0 :=
    ModularForm.discriminant_ne_zero (UpperHalfPlane.ofComplex z)
  exact (hf'.pow 2).div hd hdn

private lemma isZeroAtImInfty_cuspFormSquareDivDelta (f : CuspForm 𝒮ℒ 6) :
    UpperHalfPlane.IsZeroAtImInfty (fun z : ℍ => f z ^ 2 / ModularForm.discriminant z) := by
  apply isZeroAtImInfty_of_exp_decay
  have hf_decay : ⇑f =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im / 1) :=
    CuspFormClass.exp_decay_atImInfty f one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z
  simp only [div_one] at hf_decay
  refine ⟨2 * Real.pi, by positivity, ?_⟩
  have hf2 : (fun z : ℍ => f z ^ 2) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (-4 * Real.pi * τ.im) := by
    have h := hf_decay.pow 2
    refine h.congr_right fun z => ?_
    rw [← Real.exp_nat_mul]; push_cast; congr 1; ring
  have hdelta_inv : (fun z : ℍ => (ModularForm.discriminant z)⁻¹) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (2 * Real.pi * τ.im) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨(2 : ℝ) ^ 24, ?_⟩
    filter_upwards [delta_norm_lower_bound] with z hz
    rw [norm_inv, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hpos : 0 < (1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im) := by positivity
    calc ‖ModularForm.discriminant z‖⁻¹
        ≤ ((1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im))⁻¹ :=
          inv_anti₀ hpos hz
      _ = (2 : ℝ) ^ 24 * (Real.exp (-2 * Real.pi * z.im))⁻¹ := by
          have : ((1 / 2 : ℝ) ^ 24)⁻¹ = (2 : ℝ) ^ 24 := by
            rw [one_div, inv_pow, inv_inv]
          rw [mul_inv_rev, mul_comm, this]
      _ = (2 : ℝ) ^ 24 * Real.exp (2 * Real.pi * z.im) := by
          congr 1; rw [← Real.exp_neg]; congr 1; ring
  exact ((hf2.mul hdelta_inv).congr_left (fun z => by simp [div_eq_mul_inv])).congr_right
    fun z => by rw [← Real.exp_add]; congr 1; ring

private lemma bddAtCusp_cuspFormSquareDivDelta (f : CuspForm 𝒮ℒ 6)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsBoundedAt (fun z : ℍ => f z ^ 2 / ModularForm.discriminant z) 0 := by
  have hc' : IsCusp c 𝒮ℒ := hc
  rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc']
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc'
  exact ⟨γ, hγ.symm, by
    rw [cuspForm_square_div_delta_slash_action f γ]
    exact (isZeroAtImInfty_cuspFormSquareDivDelta f).isBoundedAtImInfty⟩

private noncomputable def cuspFormSquareDivDeltaMF (f : CuspForm 𝒮ℒ 6) :
    ModularForm 𝒮ℒ 0 where
  toSlashInvariantForm :=
    { toFun := fun z => f z ^ 2 / ModularForm.discriminant z
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
        exact cuspForm_square_div_delta_slash_action f g }
  holo' := mdiff_cuspForm_square_div_delta f
  bdd_at_cusps' hc := bddAtCusp_cuspFormSquareDivDelta f hc

private lemma cuspFormSquareDivDelta_const (f : CuspForm 𝒮ℒ 6) :
    ∃ c : ℂ, ∀ z : ℍ, f z ^ 2 / ModularForm.discriminant z = c := by
  have ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const (cuspFormSquareDivDeltaMF f)
  exact ⟨c, fun z => congr_fun hc z⟩

private lemma cuspFormSquareDivDelta_eq_zero (f : CuspForm 𝒮ℒ 6) :
    ∀ z : ℍ, f z ^ 2 / ModularForm.discriminant z = 0 := by
  obtain ⟨c, hc⟩ := cuspFormSquareDivDelta_const f
  suffices c = 0 by intro z; rw [hc z, this]
  have hzero := isZeroAtImInfty_cuspFormSquareDivDelta f
  rw [UpperHalfPlane.IsZeroAtImInfty] at hzero
  have htend : Filter.Tendsto (fun _ : ℍ => c) UpperHalfPlane.atImInfty (nhds 0) :=
    hzero.congr (fun z => hc z)
  rwa [tendsto_const_nhds_iff] at htend

theorem levelOne_cuspForm_weight6_eq_zero (f : CuspForm 𝒮ℒ 6) : ⇑f = 0 := by
  ext z
  have h := cuspFormSquareDivDelta_eq_zero f z
  have hdel : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · rwa [pow_eq_zero_iff (by norm_num : 2 ≠ 0)] at h
  · exact absurd h hdel

theorem levelOne_weight6_eq_valueAtInfty_smul_E6 (f : ModularForm 𝒮ℒ 6) :
    (f : ℍ → ℂ) = UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) • (E6 : ℍ → ℂ) := by
  let c := UpperHalfPlane.valueAtInfty (f : ℍ → ℂ)
  let g : ModularForm 𝒮ℒ 6 := f - c • E6
  have hg0 : UpperHalfPlane.valueAtInfty (g : ℍ → ℂ) = 0 := by
    simpa [g, c] using levelOne_weight6_sub_valueAtInfty_smul_E6_valueAtInfty f
  have hzero := levelOne_cuspForm_weight6_eq_zero (levelOneCuspFormOfValueAtInftyZero g hg0)
  ext z
  have hz := congr_fun hzero z
  change g z = 0 at hz
  simp only [g, ModularForm.sub_apply, ModularForm.IsGLPos.smul_apply, smul_eq_mul] at hz
  exact sub_eq_zero.mp hz

theorem serreDerivative_E4_eq_neg_one_third_smul_E6 :
    (serreDerivativeE4ModularForm : ℍ → ℂ) = (-(1 / 3 : ℂ)) • (E6 : ℍ → ℂ) := by
  simpa [serreDerivativeE4_valueAtInfty] using
    levelOne_weight6_eq_valueAtInfty_smul_E6 serreDerivativeE4ModularForm

private lemma hasDerivAt_qParam_one (z : ℂ) :
    HasDerivAt (fun w : ℂ => Function.Periodic.qParam 1 w)
      (Function.Periodic.qParam 1 z * (2 * Real.pi * Complex.I)) z := by
  unfold Function.Periodic.qParam
  convert (((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I / (1 : ℝ))).cexp) using 1
  · ext w
    congr 1
    norm_num
  · norm_num

theorem normalizedDeriv_E4_eq_q_fderiv_cusp (τ : ℍ) :
    Derivative.normalizedDerivOfComplex (E4 : ℍ → ℂ) τ =
      (((ContinuousLinearMap.apply ℂ ℂ) (Function.Periodic.qParam 1 (τ : ℂ)))
        (fderiv ℂ (SlashInvariantFormClass.cuspFunction 1 (E4 : ℍ → ℂ))
          (Function.Periodic.qParam 1 (τ : ℂ)))) := by
  let C := SlashInvariantFormClass.cuspFunction 1 (E4 : ℍ → ℂ)
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hqnorm : ‖q‖ < 1 := by
    simpa [q] using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hCdiff : DifferentiableAt ℂ C q := by
    simpa [C, q] using ModularFormClass.differentiableAt_cuspFunction (f := E4)
      one_pos ModularFormClass.one_mem_strictPeriods_SL2Z hqnorm
  have hqderiv := hasDerivAt_qParam_one (τ : ℂ)
  have hderiv_q : deriv (fun z : ℂ => Function.Periodic.qParam 1 z) (τ : ℂ) =
      q * (2 * Real.pi * Complex.I) := hqderiv.deriv
  have hcomp_deriv : deriv (fun z : ℂ => C (Function.Periodic.qParam 1 z)) (τ : ℂ) =
      deriv C q * (q * (2 * Real.pi * Complex.I)) := by
    change deriv (C ∘ fun w : ℂ => Function.Periodic.qParam 1 w) (τ : ℂ) = _
    rw [deriv_comp (x := (τ : ℂ)) hCdiff hqderiv.differentiableAt]
    rw [hderiv_q]
  have hevent : (fun z : ℂ => C (Function.Periodic.qParam 1 z)) =ᶠ[nhds (τ : ℂ)]
      (fun z : ℂ => E4 (UpperHalfPlane.ofComplex z)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    have h := SlashInvariantFormClass.eq_cuspFunction (f := E4)
      (h := 1) ⟨z, hz⟩ ModularFormClass.one_mem_strictPeriods_SL2Z one_ne_zero
    simpa [C, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using h
  have hderiv_eq := hevent.deriv_eq
  have hfderiv_apply :
      (((ContinuousLinearMap.apply ℂ ℂ) q) (fderiv ℂ C q)) = deriv C q * q := by
    change (fderiv ℂ C q : ℂ → ℂ) q = deriv C q * q
    rw [fderiv_eq_deriv_mul]
  unfold Derivative.normalizedDerivOfComplex
  change (2 * Real.pi * Complex.I)⁻¹ *
      deriv (fun z : ℂ => E4 (UpperHalfPlane.ofComplex z)) (τ : ℂ) = _
  rw [← hderiv_eq]
  rw [hcomp_deriv]
  rw [show (((ContinuousLinearMap.apply ℂ ℂ) (Function.Periodic.qParam 1 (τ : ℂ)))
        (fderiv ℂ (SlashInvariantFormClass.cuspFunction 1 (E4 : ℍ → ℂ))
          (Function.Periodic.qParam 1 (τ : ℂ)))) = deriv C q * q by
      simpa [C, q] using hfderiv_apply]
  field_simp [Complex.two_pi_I_ne_zero]

/-- A Tannery-style upgrade from convergent finite certificate series to the
limit series.

This is tailored for q-expansion proofs: `fN N` is a polynomial/truncated
coefficient sequence, `aN N` is its evaluated finite product, and `f`/`a` are
their pointwise and analytic limits. -/
theorem hasSum_of_tendsto_hasSum_of_dominated
    {fN : ℕ → ℕ → ℂ} {f : ℕ → ℂ} {aN : ℕ → ℂ} {a : ℂ} {bound : ℕ → ℝ}
    (hseries : ∀ N : ℕ, HasSum (fN N) (aN N))
    (hpoint : ∀ d : ℕ, Filter.Tendsto (fun N : ℕ => fN N d) Filter.atTop (nhds (f d)))
    (hbound_sum : Summable bound)
    (hbound : ∀ᶠ N : ℕ in Filter.atTop, ∀ d : ℕ, ‖fN N d‖ ≤ bound d)
    (ha : Filter.Tendsto aN Filter.atTop (nhds a)) :
    HasSum f a := by
  have htsum :
      Filter.Tendsto (fun N : ℕ => ∑' d : ℕ, fN N d) Filter.atTop
        (nhds (∑' d : ℕ, f d)) :=
    tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
      hbound_sum hpoint hbound
  have heq : ∀ N : ℕ, (∑' d : ℕ, fN N d) = aN N :=
    fun N => (hseries N).tsum_eq
  have htsum_aN :
      Filter.Tendsto (fun N : ℕ => aN N) Filter.atTop
        (nhds (∑' d : ℕ, f d)) := by
    exact htsum.congr' (Filter.Eventually.of_forall fun N => heq N)
  have hsum_eq : (∑' d : ℕ, f d) = a :=
    tendsto_nhds_unique htsum_aN ha
  have hbound_f : ∀ d : ℕ, ‖f d‖ ≤ bound d := by
    intro d
    exact le_of_tendsto (tendsto_norm.comp (hpoint d))
      (hbound.mono fun N h => h d)
  have hsumm : Summable f :=
    hbound_sum.of_norm_bounded hbound_f
  simpa [hsum_eq] using hsumm.hasSum

/-- The formal `q`-expansion of the normalized level-one `E4`. -/
noncomputable def E4QExpansion : PowerSeries ℂ :=
  ModularFormClass.qExpansion 1 (E4 : ℍ → ℂ)

@[simp]
theorem coeff_E4QExpansion (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n E4QExpansion =
      if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℂ) := by
  unfold E4QExpansion E4
  rw [ModularFormClass.qExpansion_eq,
    EisensteinSeries.E_qExpansion_coeff (by norm_num : 3 ≤ 4)
    (by norm_num : Even 4) n]
  have hcoef : (-(2 * (4 : ℂ) / (bernoulli 4 : ℂ))) = 240 := by
    rw [show bernoulli 4 = -1 / 30 by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : 4 ≠ 1), bernoulli'_four]]
    norm_num
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte]
  · simp only [hn, ↓reduceIte, Nat.reduceSub]
    change (-(2 * (4 : ℂ) / (bernoulli 4 : ℂ))) *
        (ArithmeticFunction.sigma 3 n : ℂ) =
      240 * (ArithmeticFunction.sigma 3 n : ℂ)
    rw [hcoef]

@[simp]
theorem constantCoeff_E4QExpansion :
    PowerSeries.constantCoeff E4QExpansion = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

/-- Integer coefficients of the normalized `E4` q-expansion. -/
def E4CoeffZ (n : ℕ) : ℤ :=
  if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ)

/-- The normalized `E4` q-expansion as an integer power series. -/
def E4ZSeries : PowerSeries ℤ :=
  PowerSeries.mk E4CoeffZ

@[simp]
theorem coeff_E4ZSeries (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n E4ZSeries = E4CoeffZ n := by
  simp [E4ZSeries]

theorem map_E4ZSeries :
    PowerSeries.map (Int.castRingHom ℂ) E4ZSeries = E4QExpansion := by
  ext n
  rw [PowerSeries.coeff_map, coeff_E4ZSeries, coeff_E4QExpansion]
  unfold E4CoeffZ
  by_cases hn : n = 0 <;> simp [hn]

theorem E4QExpansion_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n E4QExpansion *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (E4 τ) := by
  unfold E4QExpansion
  simpa [smul_eq_mul] using
    (ModularFormClass.hasSum_qExpansion (f := E4)
      (h := 1) one_pos ModularFormClass.one_mem_strictPeriods_SL2Z τ)

theorem E4_normalizedDeriv_qExpansion_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ => (n : ℂ) *
        PowerSeries.coeff (R := ℂ) n E4QExpansion *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (Derivative.normalizedDerivOfComplex (E4 : ℍ → ℂ) τ) := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  let p := ModularFormClass.qExpansionFormalMultilinearSeries 1 E4
  have hF : HasFPowerSeriesOnBall (SlashInvariantFormClass.cuspFunction 1 (E4 : ℍ → ℂ)) p 0 1 := by
    simpa [p] using ModularFormClass.hasFPowerSeries_cuspFunction (f := E4) one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z
  have hfd := hF.fderiv
  have hqnorm : ‖q‖ < 1 := by
    simpa [q] using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hqeball : q ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff]
    exact_mod_cast hqnorm
  have hsumCLM := hfd.hasSum_sub hqeball
  have hsumq := ((ContinuousLinearMap.apply ℂ ℂ) q).hasSum hsumCLM
  have hsucc : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) *
        PowerSeries.coeff (R := ℂ) (n + 1) E4QExpansion *
        Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))
      (Derivative.normalizedDerivOfComplex (E4 : ℍ → ℂ) τ) := by
    rw [normalizedDeriv_E4_eq_q_fderiv_cusp τ]
    convert hsumq using 1
    ext n
    change ((n + 1 : ℕ) : ℂ) * PowerSeries.coeff (R := ℂ) (n + 1) E4QExpansion *
        Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1) =
      (p.derivSeries n (fun _ : Fin n => q - 0)) q
    simp only [sub_zero]
    rw [FormalMultilinearSeries.derivSeries_apply_diag]
    simp [p, q, E4QExpansion, ModularFormClass.qExpansionFormalMultilinearSeries_coeff,
      nsmul_eq_mul]
    ring
  let f : ℕ → ℂ := fun n => (n : ℂ) *
    PowerSeries.coeff (R := ℂ) n E4QExpansion *
      Function.Periodic.qParam 1 (τ : ℂ) ^ n
  have htail : HasSum (fun n => f (n + 1))
      (Derivative.normalizedDerivOfComplex (E4 : ℍ → ℂ) τ) := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hsucc
  have hfull := (hasSum_nat_add_iff 1).mp htail
  simpa [f] using hfull

theorem qExpansion_summable_norm_of_norm_lt_one
    {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (f : F) {h : ℝ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ =>
      ‖(ModularFormClass.qExpansion h f).coeff n * q ^ n‖ := by
  let r : NNReal := ‖q‖₊
  have hr1 : r < 1 := by
    rw [← NNReal.coe_lt_coe]
    simpa [r] using hq
  have hlt :
      (r : ENNReal) < (ModularFormClass.qExpansionFormalMultilinearSeries h f).radius := by
    exact (ENNReal.coe_lt_coe.mpr hr1).trans_le
      (ModularFormClass.qExpansionFormalMultilinearSeries_radius f hh hΓ)
  have hs :=
    (ModularFormClass.qExpansionFormalMultilinearSeries h f).summable_norm_mul_pow hlt
  simpa [ModularFormClass.qExpansionFormalMultilinearSeries_apply_norm,
    r, norm_mul, norm_pow] using hs

theorem E4QExpansion_summable_norm (τ : ℍ) :
    Summable fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n E4QExpansion *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n‖ := by
  unfold E4QExpansion
  exact qExpansion_summable_norm_of_norm_lt_one (f := E4)
    one_pos ModularFormClass.one_mem_strictPeriods_SL2Z
    (by simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ)

private theorem bernoulli'_six : bernoulli' 6 = (1 / 42 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by norm_num : 1 < 5)]
  norm_num [Nat.choose]

/-- The formal `q`-expansion of the normalized level-one `E6`. -/
noncomputable def E6QExpansion : PowerSeries ℂ :=
  ModularFormClass.qExpansion 1 (E6 : ℍ → ℂ)

@[simp]
theorem coeff_E6QExpansion (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n E6QExpansion =
      if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℂ) := by
  unfold E6QExpansion E6
  rw [ModularFormClass.qExpansion_eq,
    EisensteinSeries.E_qExpansion_coeff (by norm_num : 3 ≤ 6)
    (by norm_num : Even 6) n]
  have hcoef : (-(2 * (6 : ℂ) / (bernoulli 6 : ℂ))) = -504 := by
    rw [show bernoulli 6 = 1 / 42 by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : 6 ≠ 1), bernoulli'_six]]
    norm_num
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte]
  · simp only [hn, ↓reduceIte, Nat.reduceSub]
    change (-(2 * (6 : ℂ) / (bernoulli 6 : ℂ))) *
        (ArithmeticFunction.sigma 5 n : ℂ) =
      -504 * (ArithmeticFunction.sigma 5 n : ℂ)
    rw [hcoef]

theorem E6QExpansion_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n E6QExpansion *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (E6 τ) := by
  unfold E6QExpansion
  simpa [smul_eq_mul] using
    (ModularFormClass.hasSum_qExpansion (f := E6)
      (h := 1) one_pos ModularFormClass.one_mem_strictPeriods_SL2Z τ)

theorem E6QExpansion_summable_norm (τ : ℍ) :
    Summable fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n E6QExpansion *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n‖ := by
  unfold E6QExpansion
  exact qExpansion_summable_norm_of_norm_lt_one (f := E6)
    one_pos ModularFormClass.one_mem_strictPeriods_SL2Z
    (by simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ)

/-- The formal Euler factor `(1 - q^m)^24` appearing in the discriminant. -/
def deltaEulerFactor (m : ℕ) : PowerSeries ℂ :=
  (1 - (PowerSeries.X : PowerSeries ℂ) ^ m) ^ 24

/-- Integer-coefficient Euler factor `(1 - q^m)^24`. -/
def deltaEulerFactorZ (m : ℕ) : PowerSeries ℤ :=
  (1 - (PowerSeries.X : PowerSeries ℤ) ^ m) ^ 24

theorem map_deltaEulerFactorZ (m : ℕ) :
    PowerSeries.map (Int.castRingHom ℂ) (deltaEulerFactorZ m) =
      deltaEulerFactor m := by
  simp [deltaEulerFactorZ, deltaEulerFactor, PowerSeries.map_X]

/-- Binomial expansion of the integer Euler factor `(1 - q^m)^24`. -/
theorem deltaEulerFactorZ_binomial (m : ℕ) :
    deltaEulerFactorZ m =
      ∑ j ∈ Finset.range 25,
        PowerSeries.C (((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ))) *
          (PowerSeries.X : PowerSeries ℤ) ^ (j * m) := by
  rw [deltaEulerFactorZ, sub_eq_add_neg, add_comm, add_pow]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjle : j ≤ 24 := by
    have : j < 25 := Finset.mem_range.mp hj
    omega
  rw [pow_mul]
  simp only [one_pow]
  rw [neg_pow]
  rw [show ((-1 : PowerSeries ℤ) ^ j) = PowerSeries.C ((-1 : ℤ) ^ j) by simp]
  rw [show ((-1 : ℤ) ^ j) = if Even j then 1 else -1 by
    simpa using (neg_one_pow_eq_ite (R := ℤ) (n := j))]
  rw [← pow_mul]
  rw [Nat.mul_comm m j]
  rw [pow_mul]
  simp [mul_comm]

theorem coeff_deltaEulerFactorZ_sparse (m n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (deltaEulerFactorZ m) =
      ∑ j ∈ Finset.range 25,
        if n = j * m then
          ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ))
        else 0 := by
  rw [deltaEulerFactorZ_binomial]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hEven : Even j
  · simp only [hEven, ↓reduceIte, one_mul]
    rw [PowerSeries.coeff_C_mul_X_pow]
  · simp only [hEven, ↓reduceIte]
    rw [PowerSeries.coeff_C_mul_X_pow]

/-- The finite Euler product `q * prod_{m=1}^{N} (1 - q^m)^24`. -/
def deltaEulerProductTrunc (N : ℕ) : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) *
    ∏ m ∈ Finset.range N, deltaEulerFactor (m + 1)

/-- Integer-coefficient finite Euler product `q * prod_{m=1}^{N} (1 - q^m)^24`. -/
def deltaEulerProductTruncZ (N : ℕ) : PowerSeries ℤ :=
  (PowerSeries.X : PowerSeries ℤ) *
    ∏ m ∈ Finset.range N, deltaEulerFactorZ (m + 1)

/-- Polynomial Euler factor `(1 - q^m)^24`, used to evaluate finite truncations. -/
def deltaEulerPolyFactor (m : ℕ) : Polynomial ℂ :=
  (1 - (Polynomial.X : Polynomial ℂ) ^ m) ^ 24

/-- Polynomial finite Euler product `q * prod_{m=1}^{N} (1 - q^m)^24`. -/
def deltaEulerPolyTrunc (N : ℕ) : Polynomial ℂ :=
  (Polynomial.X : Polynomial ℂ) *
    ∏ m ∈ Finset.range N, deltaEulerPolyFactor (m + 1)

theorem coe_deltaEulerPolyFactor (m : ℕ) :
    ((deltaEulerPolyFactor m : Polynomial ℂ) : PowerSeries ℂ) =
      deltaEulerFactor m := by
  simp [deltaEulerPolyFactor, deltaEulerFactor]

theorem coe_deltaEulerPolyTrunc (N : ℕ) :
    ((deltaEulerPolyTrunc N : Polynomial ℂ) : PowerSeries ℂ) =
      deltaEulerProductTrunc N := by
  simp only [deltaEulerPolyTrunc, deltaEulerProductTrunc, Polynomial.coe_mul,
    Polynomial.coe_X]
  congr 1
  change Polynomial.coeToPowerSeries.ringHom
      (∏ m ∈ Finset.range N, deltaEulerPolyFactor (m + 1)) =
    ∏ m ∈ Finset.range N, deltaEulerFactor (m + 1)
  rw [map_prod Polynomial.coeToPowerSeries.ringHom]
  exact Finset.prod_congr rfl fun x _hx => coe_deltaEulerPolyFactor (x + 1)

theorem eval_deltaEulerPolyFactor (m : ℕ) (q : ℂ) :
    (deltaEulerPolyFactor m).eval q = (1 - q ^ m) ^ 24 := by
  simp [deltaEulerPolyFactor]

theorem eval_deltaEulerPolyTrunc (N : ℕ) (q : ℂ) :
    (deltaEulerPolyTrunc N).eval q =
      q * ∏ m ∈ Finset.range N, (1 - q ^ (m + 1)) ^ 24 := by
  simp only [deltaEulerPolyTrunc, Polynomial.eval_mul, Polynomial.eval_X]
  rw [Polynomial.eval_prod]
  apply congrArg (fun t => q * t)
  exact Finset.prod_congr rfl fun x _hx => eval_deltaEulerPolyFactor (x + 1) q

theorem Polynomial.hasSum_coeff_mul_pow (p : Polynomial ℂ) (q : ℂ) :
    HasSum (fun d : ℕ => p.coeff d * q ^ d) (p.eval q) := by
  rw [Polynomial.eval_eq_sum_range]
  exact hasSum_sum_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) (by
    intro d hd
    have hlt : p.natDegree < d := by
      rw [Finset.mem_range, not_lt] at hd
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul])

/-- Sum of absolute values of coefficients weighted by a real radius.  This is
the finite polynomial norm used to dominate a single coefficient. -/
noncomputable def Polynomial.absCoeffEval (p : Polynomial ℂ) (r : ℝ) : ℝ :=
  ∑ d ∈ p.support, ‖p.coeff d‖ * r ^ d

theorem Polynomial.absCoeffEval_nonneg (p : Polynomial ℂ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ Polynomial.absCoeffEval p r := by
  unfold Polynomial.absCoeffEval
  exact Finset.sum_nonneg fun d _hd =>
    mul_nonneg (norm_nonneg _) (pow_nonneg hr d)

theorem Polynomial.absCoeffEval_eq_sum_range (p : Polynomial ℂ) (r : ℝ) :
    Polynomial.absCoeffEval p r =
      ∑ d ∈ Finset.range (p.natDegree + 1), ‖p.coeff d‖ * r ^ d := by
  unfold Polynomial.absCoeffEval
  exact Finset.sum_subset
    (s₁ := p.support) (s₂ := Finset.range (p.natDegree + 1))
    (f := fun d => ‖p.coeff d‖ * r ^ d)
    (Polynomial.supp_subset_range_natDegree_succ (p := p))
    (fun d _hd hdp => by
      simp [Polynomial.notMem_support_iff.mp hdp])

theorem Polynomial.absCoeffEval_add_le
    (p q : Polynomial ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Polynomial.absCoeffEval (p + q) r ≤
      Polynomial.absCoeffEval p r + Polynomial.absCoeffEval q r := by
  classical
  unfold Polynomial.absCoeffEval
  calc
    ∑ d ∈ (p + q).support, ‖(p + q).coeff d‖ * r ^ d
        ≤ ∑ d ∈ (p + q).support,
            (‖p.coeff d‖ * r ^ d + ‖q.coeff d‖ * r ^ d) := by
          refine Finset.sum_le_sum fun d _hd => ?_
          calc
            ‖(p + q).coeff d‖ * r ^ d
                = ‖p.coeff d + q.coeff d‖ * r ^ d := by rw [Polynomial.coeff_add]
            _ ≤ (‖p.coeff d‖ + ‖q.coeff d‖) * r ^ d :=
                mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hr d)
            _ = ‖p.coeff d‖ * r ^ d + ‖q.coeff d‖ * r ^ d := by ring
    _ = (∑ d ∈ (p + q).support, ‖p.coeff d‖ * r ^ d) +
          ∑ d ∈ (p + q).support, ‖q.coeff d‖ * r ^ d := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ d ∈ p.support, ‖p.coeff d‖ * r ^ d) +
          ∑ d ∈ q.support, ‖q.coeff d‖ * r ^ d := by
          apply add_le_add
          · calc
              ∑ d ∈ (p + q).support, ‖p.coeff d‖ * r ^ d
                  ≤ ∑ d ∈ p.support ∪ q.support, ‖p.coeff d‖ * r ^ d :=
                    Finset.sum_le_sum_of_subset_of_nonneg
                      (Polynomial.support_add (p := p) (q := q))
                      (fun d _hd _hadd =>
                        mul_nonneg (norm_nonneg _) (pow_nonneg hr d))
              _ = ∑ d ∈ p.support, ‖p.coeff d‖ * r ^ d := by
                    exact (Finset.sum_subset Finset.subset_union_left
                      (fun d _hd hdp => by
                        rw [Polynomial.notMem_support_iff.mp hdp, norm_zero, zero_mul])).symm
          · calc
              ∑ d ∈ (p + q).support, ‖q.coeff d‖ * r ^ d
                  ≤ ∑ d ∈ p.support ∪ q.support, ‖q.coeff d‖ * r ^ d :=
                    Finset.sum_le_sum_of_subset_of_nonneg
                      (Polynomial.support_add (p := p) (q := q))
                      (fun d _hd _hadd =>
                        mul_nonneg (norm_nonneg _) (pow_nonneg hr d))
              _ = ∑ d ∈ q.support, ‖q.coeff d‖ * r ^ d := by
                    exact (Finset.sum_subset Finset.subset_union_right
                      (fun d _hd hdq => by
                        rw [Polynomial.notMem_support_iff.mp hdq, norm_zero, zero_mul])).symm

@[simp]
theorem Polynomial.absCoeffEval_zero (r : ℝ) :
    Polynomial.absCoeffEval (0 : Polynomial ℂ) r = 0 := by
  simp [Polynomial.absCoeffEval]

theorem Polynomial.absCoeffEval_neg (p : Polynomial ℂ) (r : ℝ) :
    Polynomial.absCoeffEval (-p) r = Polynomial.absCoeffEval p r := by
  simp [Polynomial.absCoeffEval, Polynomial.support_neg]

theorem Polynomial.absCoeffEval_C (a : ℂ) (r : ℝ) :
    Polynomial.absCoeffEval (Polynomial.C a) r = ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha, Polynomial.absCoeffEval]
  · simp [Polynomial.absCoeffEval, Polynomial.support_C ha]

theorem Polynomial.absCoeffEval_X_pow (n : ℕ) (r : ℝ) :
    Polynomial.absCoeffEval ((Polynomial.X : Polynomial ℂ) ^ n) r = r ^ n := by
  have hone : ¬(1 : ℂ) = 0 := one_ne_zero
  simp [Polynomial.absCoeffEval, Polynomial.support_X_pow hone n]

theorem Polynomial.absCoeffEval_mul_le
    (p q : Polynomial ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Polynomial.absCoeffEval (p * q) r ≤
      Polynomial.absCoeffEval p r * Polynomial.absCoeffEval q r := by
  classical
  let dp := p.natDegree
  let dq := q.natDegree
  let A : ℕ × ℕ → ℝ := fun ij =>
    (‖p.coeff ij.1‖ * r ^ ij.1) * (‖q.coeff ij.2‖ * r ^ ij.2)
  have hA_nonneg : ∀ ij : ℕ × ℕ, 0 ≤ A ij := by
    intro ij
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
      (mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
  have hprod_natDegree : (p * q).natDegree ≤ dp + dq := by
    simpa [dp, dq] using (Polynomial.natDegree_mul_le (p := p) (q := q))
  have hsupport_range :
      (p * q).support ⊆ Finset.range (dp + dq + 1) := by
    intro n hn
    exact Finset.mem_range.mpr
      ((Polynomial.le_natDegree_of_mem_supp n hn).trans_lt (Nat.lt_succ_of_le hprod_natDegree))
  have hdisj :
      Set.PairwiseDisjoint (↑(Finset.range (dp + dq + 1)))
        (fun n : ℕ => Finset.antidiagonal n) := by
    intro a _ha b _hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro ij hija hijb
    have haeq : ij.1 + ij.2 = a := Finset.mem_antidiagonal.mp hija
    have hbeq : ij.1 + ij.2 = b := Finset.mem_antidiagonal.mp hijb
    exact hab (haeq.symm.trans hbeq)
  have hrect_subset :
      (Finset.range (dp + 1)).product (Finset.range (dq + 1)) ⊆
        (Finset.range (dp + dq + 1)).biUnion (fun n : ℕ => Finset.antidiagonal n) := by
    intro ij hij
    rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
    rw [Finset.mem_biUnion]
    refine ⟨ij.1 + ij.2, ?_, ?_⟩
    · rw [Finset.mem_range] at hi hj ⊢
      omega
    · exact Finset.mem_antidiagonal.mpr rfl
  have hbig_eq_rect :
      ∑ ij ∈ (Finset.range (dp + dq + 1)).biUnion (fun n : ℕ => Finset.antidiagonal n), A ij =
        ∑ ij ∈ (Finset.range (dp + 1)).product (Finset.range (dq + 1)), A ij := by
    exact Finset.sum_subset
      (s₁ := (Finset.range (dp + 1)).product (Finset.range (dq + 1)))
      (s₂ := (Finset.range (dp + dq + 1)).biUnion (fun n : ℕ => Finset.antidiagonal n))
      (f := A) hrect_subset (fun ij _hij hrect => by
        by_cases hi : ij.1 ∈ Finset.range (dp + 1)
        · have hjnot : ij.2 ∉ Finset.range (dq + 1) := by
            intro hj
            exact hrect (Finset.mem_product.mpr ⟨hi, hj⟩)
          have hjq : q.coeff ij.2 = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            rw [Finset.mem_range, not_lt] at hjnot
            omega
          simp [A, hjq]
        · have hip : p.coeff ij.1 = 0 := by
            apply Polynomial.coeff_eq_zero_of_natDegree_lt
            rw [Finset.mem_range, not_lt] at hi
            omega
          simp [A, hip])
      |>.symm
  rw [Polynomial.absCoeffEval_eq_sum_range]
  calc
    ∑ n ∈ Finset.range ((p * q).natDegree + 1), ‖(p * q).coeff n‖ * r ^ n
        ≤ ∑ n ∈ Finset.range (dp + dq + 1), ‖(p * q).coeff n‖ * r ^ n :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (Nat.succ_le_succ hprod_natDegree))
            (fun n _hn _hsmall => mul_nonneg (norm_nonneg _) (pow_nonneg hr n))
    _ ≤ ∑ n ∈ Finset.range (dp + dq + 1),
          ∑ ij ∈ Finset.antidiagonal n, A ij := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Polynomial.coeff_mul]
        have hnorm :
            ‖∑ ij ∈ Finset.antidiagonal n, p.coeff ij.1 * q.coeff ij.2‖ ≤
              ∑ ij ∈ Finset.antidiagonal n, ‖p.coeff ij.1 * q.coeff ij.2‖ :=
          norm_sum_le _ _
        calc
          ‖∑ ij ∈ Finset.antidiagonal n, p.coeff ij.1 * q.coeff ij.2‖ * r ^ n
              ≤ (∑ ij ∈ Finset.antidiagonal n, ‖p.coeff ij.1 * q.coeff ij.2‖) * r ^ n :=
                mul_le_mul_of_nonneg_right hnorm (pow_nonneg hr n)
          _ = ∑ ij ∈ Finset.antidiagonal n, A ij := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun ij hij => ?_
              have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
              simp only [A, norm_mul]
              rw [← hsum, pow_add]
              ring
    _ = ∑ ij ∈ (Finset.range (dp + dq + 1)).biUnion
          (fun n : ℕ => Finset.antidiagonal n), A ij := by
        rw [Finset.sum_biUnion hdisj]
    _ = ∑ ij ∈ (Finset.range (dp + 1)).product (Finset.range (dq + 1)), A ij := hbig_eq_rect
    _ = (∑ i ∈ Finset.range (dp + 1), ‖p.coeff i‖ * r ^ i) *
          ∑ j ∈ Finset.range (dq + 1), ‖q.coeff j‖ * r ^ j := by
        calc
          ∑ ij ∈ (Finset.range (dp + 1)).product (Finset.range (dq + 1)), A ij
              = ∑ i ∈ Finset.range (dp + 1), ∑ j ∈ Finset.range (dq + 1),
                  (‖p.coeff i‖ * r ^ i) * (‖q.coeff j‖ * r ^ j) := by
                simpa [A] using
                  (Finset.sum_product' (Finset.range (dp + 1)) (Finset.range (dq + 1))
                    (fun i j => (‖p.coeff i‖ * r ^ i) * (‖q.coeff j‖ * r ^ j)))
          _ = (∑ i ∈ Finset.range (dp + 1), ‖p.coeff i‖ * r ^ i) *
                ∑ j ∈ Finset.range (dq + 1), ‖q.coeff j‖ * r ^ j := by
              exact (Finset.sum_mul_sum (Finset.range (dp + 1)) (Finset.range (dq + 1))
                (fun i => ‖p.coeff i‖ * r ^ i)
                (fun j => ‖q.coeff j‖ * r ^ j)).symm
    _ = Polynomial.absCoeffEval p r * Polynomial.absCoeffEval q r := by
        rw [Polynomial.absCoeffEval_eq_sum_range, Polynomial.absCoeffEval_eq_sum_range]

theorem Polynomial.absCoeffEval_pow_le
    (p : Polynomial ℂ) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    Polynomial.absCoeffEval (p ^ n) r ≤ Polynomial.absCoeffEval p r ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      change Polynomial.absCoeffEval (Polynomial.C (1 : ℂ)) r ≤ 1
      rw [Polynomial.absCoeffEval_C]
      norm_num
  | succ n ih =>
      calc
        Polynomial.absCoeffEval (p ^ (n + 1)) r
            = Polynomial.absCoeffEval (p ^ n * p) r := by rw [pow_succ]
        _ ≤ Polynomial.absCoeffEval (p ^ n) r * Polynomial.absCoeffEval p r :=
            Polynomial.absCoeffEval_mul_le (p ^ n) p hr
        _ ≤ Polynomial.absCoeffEval p r ^ n * Polynomial.absCoeffEval p r :=
            mul_le_mul_of_nonneg_right ih (Polynomial.absCoeffEval_nonneg p hr)
        _ = Polynomial.absCoeffEval p r ^ (n + 1) := by rw [pow_succ]

theorem Polynomial.absCoeffEval_prod_le
    {α : Type*} (s : Finset α) (f : α → Polynomial ℂ) (B : α → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (hB_nonneg : ∀ i ∈ s, 0 ≤ B i)
    (hB : ∀ i ∈ s, Polynomial.absCoeffEval (f i) r ≤ B i) :
    Polynomial.absCoeffEval (∏ i ∈ s, f i) r ≤ ∏ i ∈ s, B i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change Polynomial.absCoeffEval (Polynomial.C (1 : ℂ)) r ≤ 1
      rw [Polynomial.absCoeffEval_C]
      norm_num
  | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.prod_insert has]
      calc
        Polynomial.absCoeffEval (f a * ∏ i ∈ s, f i) r
            ≤ Polynomial.absCoeffEval (f a) r *
                Polynomial.absCoeffEval (∏ i ∈ s, f i) r :=
              Polynomial.absCoeffEval_mul_le (f a) (∏ i ∈ s, f i) hr
        _ ≤ B a * ∏ i ∈ s, B i := by
              exact mul_le_mul (hB a (Finset.mem_insert_self a s))
                (ih (fun i hi => hB_nonneg i (Finset.mem_insert_of_mem hi))
                  (fun i hi => hB i (Finset.mem_insert_of_mem hi)))
                (Polynomial.absCoeffEval_nonneg _ hr)
                (hB_nonneg a (Finset.mem_insert_self a s))

theorem absCoeffEval_one_sub_X_pow_le {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    Polynomial.absCoeffEval (1 - (Polynomial.X : Polynomial ℂ) ^ m) r ≤ 1 + r ^ m := by
  have h :=
    Polynomial.absCoeffEval_add_le
      (1 : Polynomial ℂ) (-((Polynomial.X : Polynomial ℂ) ^ m)) hr
  have h_one : Polynomial.absCoeffEval (1 : Polynomial ℂ) r = 1 := by
    change Polynomial.absCoeffEval (Polynomial.C (1 : ℂ)) r = 1
    rw [Polynomial.absCoeffEval_C]
    norm_num
  rw [h_one] at h
  simpa [sub_eq_add_neg, Polynomial.absCoeffEval_C, Polynomial.absCoeffEval_neg,
    Polynomial.absCoeffEval_X_pow] using h

theorem absCoeffEval_deltaEulerPolyFactor_le {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    Polynomial.absCoeffEval (deltaEulerPolyFactor m) r ≤ (1 + r ^ m) ^ 24 := by
  unfold deltaEulerPolyFactor
  calc
    Polynomial.absCoeffEval ((1 - (Polynomial.X : Polynomial ℂ) ^ m) ^ 24) r
        ≤ Polynomial.absCoeffEval (1 - (Polynomial.X : Polynomial ℂ) ^ m) r ^ 24 :=
          Polynomial.absCoeffEval_pow_le _ hr 24
    _ ≤ (1 + r ^ m) ^ 24 := by
          have hbase :
              Polynomial.absCoeffEval (1 - (Polynomial.X : Polynomial ℂ) ^ m) r ≤
                1 + r ^ m :=
            absCoeffEval_one_sub_X_pow_le hr m
          have hsource_nonneg :
              0 ≤ Polynomial.absCoeffEval (1 - (Polynomial.X : Polynomial ℂ) ^ m) r :=
            Polynomial.absCoeffEval_nonneg _ hr
          exact pow_le_pow_left₀ hsource_nonneg hbase 24

theorem absCoeffEval_deltaEulerPolyTrunc_le {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    Polynomial.absCoeffEval (deltaEulerPolyTrunc N) r ≤
      r * ∏ m ∈ Finset.range N, (1 + r ^ (m + 1)) ^ 24 := by
  unfold deltaEulerPolyTrunc
  calc
    Polynomial.absCoeffEval
        ((Polynomial.X : Polynomial ℂ) *
          ∏ m ∈ Finset.range N, deltaEulerPolyFactor (m + 1)) r
        ≤ Polynomial.absCoeffEval (Polynomial.X : Polynomial ℂ) r *
            Polynomial.absCoeffEval
              (∏ m ∈ Finset.range N, deltaEulerPolyFactor (m + 1)) r :=
          Polynomial.absCoeffEval_mul_le _ _ hr
    _ ≤ r * ∏ m ∈ Finset.range N, (1 + r ^ (m + 1)) ^ 24 := by
          rw [show Polynomial.absCoeffEval (Polynomial.X : Polynomial ℂ) r = r by
            simpa using Polynomial.absCoeffEval_X_pow 1 r]
          exact mul_le_mul_of_nonneg_left
            (Polynomial.absCoeffEval_prod_le (Finset.range N)
              (fun m => deltaEulerPolyFactor (m + 1))
              (fun m => (1 + r ^ (m + 1)) ^ 24) hr
              (fun m _hm => pow_nonneg (by positivity) 24)
              (fun m _hm => absCoeffEval_deltaEulerPolyFactor_le hr (m + 1)))
            hr

theorem Polynomial.norm_coeff_mul_pow_le_absCoeffEval_mul
    (p : Polynomial ℂ) {r s : ℝ} (hr_nonneg : 0 ≤ r) (hs_pos : 0 < s)
    (d : ℕ) :
    ‖p.coeff d‖ * r ^ d ≤ Polynomial.absCoeffEval p s * (r / s) ^ d := by
  classical
  have hratio_nonneg : 0 ≤ r / s := div_nonneg hr_nonneg hs_pos.le
  have habs_nonneg : 0 ≤ Polynomial.absCoeffEval p s := by
    unfold Polynomial.absCoeffEval
    exact Finset.sum_nonneg fun x _hx =>
      mul_nonneg (norm_nonneg _) (pow_nonneg hs_pos.le x)
  by_cases hcoeff : p.coeff d = 0
  · simp [hcoeff, mul_nonneg habs_nonneg (pow_nonneg hratio_nonneg d)]
  have hdmem : d ∈ p.support := by
    rw [Polynomial.mem_support_iff]
    exact hcoeff
  have hterm_nonneg :
      ∀ x ∈ p.support, 0 ≤ ‖p.coeff x‖ * s ^ x := by
    intro x _hx
    exact mul_nonneg (norm_nonneg _) (pow_nonneg hs_pos.le x)
  have hterm_le :
      ‖p.coeff d‖ * s ^ d ≤ Polynomial.absCoeffEval p s := by
    unfold Polynomial.absCoeffEval
    exact Finset.single_le_sum hterm_nonneg hdmem
  have hmul := mul_le_mul_of_nonneg_right hterm_le (pow_nonneg hratio_nonneg d)
  have hpow :
      s ^ d * (r / s) ^ d = r ^ d := by
    rw [← mul_pow, mul_div_cancel₀ r hs_pos.ne']
  calc
    ‖p.coeff d‖ * r ^ d
        = (‖p.coeff d‖ * s ^ d) * (r / s) ^ d := by
            rw [mul_assoc, hpow]
    _ ≤ Polynomial.absCoeffEval p s * (r / s) ^ d := hmul

theorem coeff_deltaEulerProductTrunc_eq_polyCoeff (N d : ℕ) :
    PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) =
      (deltaEulerPolyTrunc N).coeff d := by
  rw [← coe_deltaEulerPolyTrunc]
  simp

theorem hasSum_deltaEulerProductTrunc_coeff (N : ℕ) (q : ℂ) :
    HasSum
      (fun d : ℕ =>
        PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) * q ^ d)
      (q * ∏ m ∈ Finset.range N, (1 - q ^ (m + 1)) ^ 24) := by
  have hpoly := Polynomial.hasSum_coeff_mul_pow (deltaEulerPolyTrunc N) q
  rw [eval_deltaEulerPolyTrunc] at hpoly
  refine hpoly.congr ?_
  intro d
  rw [← coe_deltaEulerPolyTrunc]
  simp

theorem multipliable_one_sub_pow_succ_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) := by
  have hs : Summable (fun n : ℕ => -q ^ (n + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => -q ^ n) 1).mpr
      (summable_geometric_of_norm_lt_one hq).neg
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hs

theorem multipliable_delta_analytic_factor_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun n : ℕ => (1 - q ^ (n + 1)) ^ 24) :=
  (multipliable_one_sub_pow_succ_of_norm_lt_one hq).pow 24

theorem tendsto_deltaEulerProductTrunc_eval_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) :
    Filter.Tendsto
      (fun N : ℕ => q * ∏ m ∈ Finset.range N, (1 - q ^ (m + 1)) ^ 24)
      Filter.atTop
      (nhds (q * ∏' m : ℕ, (1 - q ^ (m + 1)) ^ 24)) := by
  exact tendsto_const_nhds.mul
    (multipliable_delta_analytic_factor_of_norm_lt_one hq).hasProd.tendsto_prod_nat

theorem map_deltaEulerProductTruncZ (N : ℕ) :
    PowerSeries.map (Int.castRingHom ℂ) (deltaEulerProductTruncZ N) =
      deltaEulerProductTrunc N := by
  simp [deltaEulerProductTruncZ, deltaEulerProductTrunc, map_deltaEulerFactorZ,
    PowerSeries.map_X]

private theorem trunc_one_sub_X_pow_eq_one_of_lt {d m : ℕ} (hdm : d < m) :
    PowerSeries.trunc (R := ℂ) (d + 1)
        (1 - (PowerSeries.X : PowerSeries ℂ) ^ m) = 1 := by
  ext i
  rw [PowerSeries.coeff_trunc]
  by_cases hi : i < d + 1
  · have him : i ≠ m := by omega
    rw [if_pos hi, Polynomial.coeff_one]
    simp [PowerSeries.coeff_X_pow, him]
  · have hi0 : i ≠ 0 := by omega
    rw [if_neg hi, Polynomial.coeff_one]
    simp [hi0]

private theorem trunc_deltaEulerFactor_eq_one_of_lt {d m : ℕ} (hdm : d < m) :
    PowerSeries.trunc (R := ℂ) (d + 1) (deltaEulerFactor m) = 1 := by
  unfold deltaEulerFactor
  induction 24 with
  | zero =>
      exact PowerSeries.trunc_one d
  | succ k ih =>
      rw [pow_succ, ← PowerSeries.trunc_trunc_mul_trunc]
      rw [trunc_one_sub_X_pow_eq_one_of_lt hdm, ih]
      simp

theorem coeff_mul_deltaEulerFactor_of_lt (f : PowerSeries ℂ) {d m : ℕ}
    (hdm : d < m) :
    PowerSeries.coeff (R := ℂ) d (f * deltaEulerFactor m) =
      PowerSeries.coeff (R := ℂ) d f := by
  rw [PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc
    (f := f) (g := deltaEulerFactor m) (n := d + 1) (d := d) (Nat.lt_succ_self d)]
  rw [trunc_deltaEulerFactor_eq_one_of_lt hdm]
  simp [PowerSeries.coeff_coe_trunc_of_lt (Nat.lt_succ_self d)]

theorem coeff_deltaEulerProductTrunc_succ_of_lt {N d : ℕ} (hdN : d < N + 1) :
    PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc (N + 1)) =
      PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) := by
  unfold deltaEulerProductTrunc
  rw [Finset.prod_range_succ]
  rw [← mul_assoc]
  exact coeff_mul_deltaEulerFactor_of_lt
    ((PowerSeries.X : PowerSeries ℂ) *
      ∏ m ∈ Finset.range N, deltaEulerFactor (m + 1)) hdN

theorem coeff_deltaEulerProductTrunc_eq_of_le {N M d : ℕ}
    (hdN : d < N) (hNM : N ≤ M) :
    PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc M) =
      PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, coeff_deltaEulerProductTrunc_succ_of_lt]
      · exact ih (Nat.le_add_right N k)
      · omega

/-- Coefficient of the formal Euler-product expansion of `Delta`.

The previous stability lemma shows that this does not depend on taking any
longer product. -/
def deltaEulerCoeff (d : ℕ) : ℂ :=
  PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc (d + 1))

/-- Integer coefficient of the formal Euler-product expansion of `Delta`. -/
def deltaEulerCoeffZ (d : ℕ) : ℤ :=
  PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ (d + 1))

theorem map_deltaEulerCoeffZ (d : ℕ) :
    (deltaEulerCoeffZ d : ℂ) = deltaEulerCoeff d := by
  unfold deltaEulerCoeffZ deltaEulerCoeff
  calc
    ((PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ (d + 1)) : ℤ) : ℂ)
        = PowerSeries.coeff (R := ℂ) d
            (PowerSeries.map (Int.castRingHom ℂ) (deltaEulerProductTruncZ (d + 1))) := by
          rw [PowerSeries.coeff_map]
          rfl
    _ = PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc (d + 1)) := by
          rw [map_deltaEulerProductTruncZ]

theorem coeff_deltaEulerProductTrunc_eq_deltaEulerCoeff_of_lt {N d : ℕ}
    (hdN : d < N) :
    PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) =
      deltaEulerCoeff d := by
  unfold deltaEulerCoeff
  exact coeff_deltaEulerProductTrunc_eq_of_le (Nat.lt_succ_self d) (by omega)

theorem hasSum_deltaEulerCoeff_mul_pow_of_norm_lt_one_of_dominated
    {q : ℂ} (hq : ‖q‖ < 1) {bound : ℕ → ℝ}
    (hbound_sum : Summable bound)
    (hbound : ∀ᶠ N : ℕ in Filter.atTop, ∀ d : ℕ,
      ‖PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) * q ^ d‖ ≤ bound d) :
    HasSum (fun d : ℕ => deltaEulerCoeff d * q ^ d)
      (q * ∏' m : ℕ, (1 - q ^ (m + 1)) ^ 24) := by
  refine hasSum_of_tendsto_hasSum_of_dominated
    (fN := fun N d => PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) * q ^ d)
    (f := fun d => deltaEulerCoeff d * q ^ d)
    (aN := fun N => q * ∏ m ∈ Finset.range N, (1 - q ^ (m + 1)) ^ 24)
    (a := q * ∏' m : ℕ, (1 - q ^ (m + 1)) ^ 24)
    (bound := bound) ?hseries ?hpoint hbound_sum hbound ?ha
  · intro N
    exact hasSum_deltaEulerProductTrunc_coeff N q
  · intro d
    refine tendsto_atTop_of_eventually_const (i₀ := d + 1) ?_
    intro N hN
    change PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) * q ^ d =
      deltaEulerCoeff d * q ^ d
    rw [coeff_deltaEulerProductTrunc_eq_deltaEulerCoeff_of_lt (N := N) (d := d) (by omega)]
  · exact tendsto_deltaEulerProductTrunc_eval_of_norm_lt_one hq

theorem hasSum_deltaEulerCoeff_mul_pow_of_absCoeffEval_bound
    {q : ℂ} {s C : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1) (hqs : ‖q‖ < s)
    (hC :
      ∀ᶠ N : ℕ in Filter.atTop,
        Polynomial.absCoeffEval (deltaEulerPolyTrunc N) s ≤ C) :
    HasSum (fun d : ℕ => deltaEulerCoeff d * q ^ d)
      (q * ∏' m : ℕ, (1 - q ^ (m + 1)) ^ 24) := by
  have hq : ‖q‖ < 1 := by
    exact hqs.trans hs_lt_one
  let ratio : ℝ := ‖q‖ / s
  have hratio_nonneg : 0 ≤ ratio := div_nonneg (norm_nonneg q) hs_pos.le
  have hratio_lt_one : ratio < 1 := by
    rw [show (1 : ℝ) = s / s by field_simp [hs_pos.ne']]
    exact div_lt_div_of_pos_right hqs hs_pos
  have hratio_norm_lt_one : ‖ratio‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hratio_nonneg]
  refine hasSum_deltaEulerCoeff_mul_pow_of_norm_lt_one_of_dominated
    (q := q) hq (bound := fun d : ℕ => C * ratio ^ d) ?_ ?_
  · exact (summable_geometric_of_norm_lt_one hratio_norm_lt_one).mul_left C
  · filter_upwards [hC] with N hCN d
    rw [coeff_deltaEulerProductTrunc_eq_polyCoeff]
    calc
      ‖(deltaEulerPolyTrunc N).coeff d * q ^ d‖
          = ‖(deltaEulerPolyTrunc N).coeff d‖ * ‖q‖ ^ d := by
              rw [norm_mul, norm_pow]
      _ ≤ Polynomial.absCoeffEval (deltaEulerPolyTrunc N) s * ratio ^ d :=
            Polynomial.norm_coeff_mul_pow_le_absCoeffEval_mul
              (deltaEulerPolyTrunc N) (norm_nonneg q) hs_pos d
      _ ≤ C * ratio ^ d :=
            mul_le_mul_of_nonneg_right hCN (pow_nonneg hratio_nonneg d)

theorem delta_hasSum_deltaEulerCoeff_of_dominated
    (τ : ℍ) {bound : ℕ → ℝ}
    (hbound_sum : Summable bound)
    (hbound : ∀ᶠ N : ℕ in Filter.atTop, ∀ d : ℕ,
      ‖PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ d‖ ≤ bound d) :
    HasSum
      (fun d : ℕ =>
        deltaEulerCoeff d • Function.Periodic.qParam 1 (τ : ℂ) ^ d)
      (ModularForm.discriminant τ) := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hq : ‖q‖ < 1 := by
    simpa [q] using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hs := hasSum_deltaEulerCoeff_mul_pow_of_norm_lt_one_of_dominated
    (q := q) hq hbound_sum (by simpa [q] using hbound)
  rw [ModularForm.discriminant_eq_q_prod τ]
  simpa [q, ModularForm.eta_q, smul_eq_mul] using hs

theorem delta_hasSum_deltaEulerCoeff_of_absCoeffEval_bound
    (τ : ℍ) {s C : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hqs : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < s)
    (hC :
      ∀ᶠ N : ℕ in Filter.atTop,
        Polynomial.absCoeffEval (deltaEulerPolyTrunc N) s ≤ C) :
    HasSum
      (fun d : ℕ =>
        deltaEulerCoeff d • Function.Periodic.qParam 1 (τ : ℂ) ^ d)
      (ModularForm.discriminant τ) := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hs := hasSum_deltaEulerCoeff_mul_pow_of_absCoeffEval_bound
    (q := q) hs_pos hs_lt_one (by simpa [q] using hqs) hC
  rw [ModularForm.discriminant_eq_q_prod τ]
  simpa [q, ModularForm.eta_q, smul_eq_mul] using hs

theorem exists_qParam_radius_between_norm_and_one (τ : ℍ) :
    ∃ s : ℝ, 0 < s ∧ ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < s ∧ s < 1 := by
  obtain ⟨s, hqs, hs1⟩ :=
    exists_between (UpperHalfPlane.norm_qParam_lt_one 1 τ)
  exact ⟨s, (norm_nonneg _).trans_lt hqs, by simpa using hqs, hs1⟩

theorem multipliable_delta_abs_majorant_of_lt_one {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    Multipliable (fun n : ℕ => (1 + r ^ (n + 1)) ^ 24) := by
  have hnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr_nonneg] using hr_lt_one
  have hs_geom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  have hs : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => r ^ n) 1).mpr hs_geom
  simpa using (Real.multipliable_one_add_of_summable hs).pow 24

theorem eventually_absCoeffEval_deltaEulerPolyTrunc_le_of_lt_one {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
      Polynomial.absCoeffEval (deltaEulerPolyTrunc N) r ≤ C := by
  let majorant : ℕ → ℝ := fun n => (1 + r ^ (n + 1)) ^ 24
  let P : ℝ := ∏' n : ℕ, majorant n
  have hmult : Multipliable majorant := by
    simpa [majorant] using multipliable_delta_abs_majorant_of_lt_one hr_nonneg hr_lt_one
  have htend :
      Filter.Tendsto (fun N : ℕ => ∏ m ∈ Finset.range N, majorant m)
        Filter.atTop (nhds P) := by
    simpa [P] using hmult.hasProd.tendsto_prod_nat
  refine ⟨r * (P + 1), ?_⟩
  have hevent :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∏ m ∈ Finset.range N, majorant m < P + 1 :=
    htend.eventually_lt_const (lt_add_one P)
  filter_upwards [hevent] with N hN
  calc
    Polynomial.absCoeffEval (deltaEulerPolyTrunc N) r
        ≤ r * ∏ m ∈ Finset.range N, (1 + r ^ (m + 1)) ^ 24 :=
          absCoeffEval_deltaEulerPolyTrunc_le hr_nonneg N
    _ = r * ∏ m ∈ Finset.range N, majorant m := by
          simp [majorant]
    _ ≤ r * (P + 1) :=
          mul_le_mul_of_nonneg_left hN.le hr_nonneg

theorem delta_hasSum_deltaEulerCoeff (τ : ℍ) :
    HasSum
      (fun d : ℕ =>
        deltaEulerCoeff d • Function.Periodic.qParam 1 (τ : ℂ) ^ d)
      (ModularForm.discriminant τ) := by
  rcases exists_qParam_radius_between_norm_and_one τ with ⟨s, hs_pos, hqs, hs_lt_one⟩
  rcases eventually_absCoeffEval_deltaEulerPolyTrunc_le_of_lt_one hs_pos.le hs_lt_one with
    ⟨C, hC⟩
  exact delta_hasSum_deltaEulerCoeff_of_absCoeffEval_bound τ hs_pos hs_lt_one hqs hC

theorem coeff_deltaEulerProductTruncZ_eq_deltaEulerCoeffZ_of_lt {N d : ℕ}
    (hdN : d < N) :
    PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ N) =
      deltaEulerCoeffZ d := by
  have hC :
      ((PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ N) : ℤ) : ℂ) =
        (deltaEulerCoeffZ d : ℂ) := by
    calc
      ((PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ N) : ℤ) : ℂ)
          = PowerSeries.coeff (R := ℂ) d
              (PowerSeries.map (Int.castRingHom ℂ) (deltaEulerProductTruncZ N)) := by
            rw [PowerSeries.coeff_map]
            rfl
      _ = PowerSeries.coeff (R := ℂ) d (deltaEulerProductTrunc N) := by
            rw [map_deltaEulerProductTruncZ]
      _ = deltaEulerCoeff d := coeff_deltaEulerProductTrunc_eq_deltaEulerCoeff_of_lt hdN
      _ = (deltaEulerCoeffZ d : ℂ) := by
            rw [← map_deltaEulerCoeffZ]
  exact_mod_cast hC

/-- The formal power series with coefficients supplied by the stable finite
Euler products. -/
def deltaEulerSeries : PowerSeries ℂ :=
  PowerSeries.mk deltaEulerCoeff

/-- Integer-coefficient Euler-product series for `Delta`. -/
def deltaEulerSeriesZ : PowerSeries ℤ :=
  PowerSeries.mk deltaEulerCoeffZ

@[simp]
theorem coeff_deltaEulerSeries (d : ℕ) :
    PowerSeries.coeff (R := ℂ) d deltaEulerSeries = deltaEulerCoeff d := by
  simp [deltaEulerSeries]

@[simp]
theorem coeff_deltaEulerSeriesZ (d : ℕ) :
    PowerSeries.coeff (R := ℤ) d deltaEulerSeriesZ = deltaEulerCoeffZ d := by
  simp [deltaEulerSeriesZ]

theorem deltaEulerSeries_hasSum (τ : ℍ) :
    HasSum (fun d : ℕ =>
      PowerSeries.coeff (R := ℂ) d deltaEulerSeries *
        Function.Periodic.qParam 1 (τ : ℂ) ^ d)
      (ModularForm.discriminant τ) := by
  simpa [smul_eq_mul] using delta_hasSum_deltaEulerCoeff τ

theorem map_deltaEulerSeriesZ :
    PowerSeries.map (Int.castRingHom ℂ) deltaEulerSeriesZ = deltaEulerSeries := by
  ext d
  rw [PowerSeries.coeff_map, coeff_deltaEulerSeriesZ, coeff_deltaEulerSeries]
  exact map_deltaEulerCoeffZ d

@[simp]
theorem deltaEulerCoeff_zero : deltaEulerCoeff 0 = 0 := by
  simp [deltaEulerCoeff, deltaEulerProductTrunc]

@[simp]
theorem deltaEulerCoeffZ_zero : deltaEulerCoeffZ 0 = 0 := by
  simp [deltaEulerCoeffZ, deltaEulerProductTruncZ]

@[simp]
theorem constantCoeff_deltaEulerSeries :
    PowerSeries.constantCoeff deltaEulerSeries = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

/-- The formal infinite Euler product for the discriminant, in the `q` variable. -/
noncomputable def deltaEulerProduct : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) *
    ∏' n : ℕ, deltaEulerFactor (n + 1)

theorem multipliable_deltaEulerFactor_succ :
    Multipliable (fun n : ℕ => deltaEulerFactor (n + 1)) := by
  simpa [deltaEulerFactor] using
    (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℂ).pow 24

theorem coeff_deltaEulerProduct_eq_deltaEulerCoeff (d : ℕ) :
    PowerSeries.coeff (R := ℂ) d deltaEulerProduct = deltaEulerCoeff d := by
  let f : ℕ → PowerSeries ℂ := fun n => deltaEulerFactor (n + 1)
  have hf : Multipliable f := by
    simpa [f] using multipliable_deltaEulerFactor_succ
  have ht :
      Filter.Tendsto
        (fun N => (PowerSeries.X : PowerSeries ℂ) * ∏ n ∈ Finset.range N, f n)
        Filter.atTop
        (nhds ((PowerSeries.X : PowerSeries ℂ) * ∏' n, f n)) := by
    exact tendsto_const_nhds.mul hf.hasProd.tendsto_prod_nat
  have hc :
      Filter.Tendsto
        (fun N =>
          PowerSeries.coeff (R := ℂ) d
            ((PowerSeries.X : PowerSeries ℂ) * ∏ n ∈ Finset.range N, f n))
        Filter.atTop
        (nhds
          (PowerSeries.coeff (R := ℂ) d
            ((PowerSeries.X : PowerSeries ℂ) * ∏' n, f n))) := by
    exact ((PowerSeries.WithPiTopology.continuous_coeff ℂ d).tendsto _).comp ht
  have hevent : ∀ᶠ N : ℕ in Filter.atTop,
      PowerSeries.coeff (R := ℂ) d
          ((PowerSeries.X : PowerSeries ℂ) * ∏ n ∈ Finset.range N, f n) =
        deltaEulerCoeff d := by
    exact Filter.eventually_atTop.mpr ⟨d + 1, fun N hN => by
      simpa [f, deltaEulerProductTrunc] using
        coeff_deltaEulerProductTrunc_eq_deltaEulerCoeff_of_lt
          (N := N) (d := d) (by omega)⟩
  have hconst :
      Filter.Tendsto (fun _N : ℕ => deltaEulerCoeff d) Filter.atTop
        (nhds (deltaEulerCoeff d)) :=
    tendsto_const_nhds
  have hc' :
      Filter.Tendsto (fun _N : ℕ => deltaEulerCoeff d) Filter.atTop
        (nhds
          (PowerSeries.coeff (R := ℂ) d
            ((PowerSeries.X : PowerSeries ℂ) * ∏' n, f n))) := by
    exact hc.congr' hevent
  have hlim := tendsto_nhds_unique hconst hc'
  simpa [deltaEulerProduct, f] using hlim.symm

theorem deltaEulerProduct_eq_deltaEulerSeries :
    deltaEulerProduct = deltaEulerSeries := by
  ext d
  rw [coeff_deltaEulerProduct_eq_deltaEulerCoeff, coeff_deltaEulerSeries]

/-- The formal `q`-expansion of the modular discriminant `Delta`. -/
noncomputable def deltaQExpansion : PowerSeries ℂ :=
  ModularFormClass.qExpansion 1 ModularForm.discriminant

theorem deltaQExpansion_eq_deltaEulerSeries_of_coeff
    (hcoeff :
      ∀ d : ℕ, PowerSeries.coeff (R := ℂ) d deltaQExpansion = deltaEulerCoeff d) :
    deltaQExpansion = deltaEulerSeries := by
  ext d
  rw [hcoeff d, coeff_deltaEulerSeries]

theorem deltaQExpansion_eq_deltaEulerSeries_of_hasSum
    (hcoeff :
      ∀ d : ℕ, PowerSeries.coeff (R := ℂ) d deltaQExpansion = deltaEulerCoeff d)
    (_hsum :
      ∀ τ : ℍ,
        HasSum (fun d : ℕ =>
          deltaEulerCoeff d • Function.Periodic.qParam 1 (τ : ℂ) ^ d)
          (ModularForm.discriminant τ)) :
    deltaQExpansion = deltaEulerSeries := by
  exact deltaQExpansion_eq_deltaEulerSeries_of_coeff hcoeff

/-- Substitute `q = Q^41` into a formal q-expansion. -/
noncomputable def qPullback41 (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.subst ((PowerSeries.X : PowerSeries ℂ) ^ 41) f

/-- Integer-coefficient version of substituting `q = Q^41`. -/
noncomputable def qPullback41Z (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.subst ((PowerSeries.X : PowerSeries ℤ) ^ 41) f

theorem qPullback41_add (f g : PowerSeries ℂ) :
    qPullback41 (f + g) = qPullback41 f + qPullback41 g := by
  unfold qPullback41
  exact PowerSeries.subst_add (PowerSeries.HasSubst.X_pow (R := ℂ)
    (by exact Nat.succ_ne_zero 40)) f g

theorem qPullback41_mul (f g : PowerSeries ℂ) :
    qPullback41 (f * g) = qPullback41 f * qPullback41 g := by
  unfold qPullback41
  exact PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow (R := ℂ)
    (by exact Nat.succ_ne_zero 40)) f g

theorem qPullback41_pow (f : PowerSeries ℂ) (n : ℕ) :
    qPullback41 (f ^ n) = qPullback41 f ^ n := by
  unfold qPullback41
  exact PowerSeries.subst_pow (PowerSeries.HasSubst.X_pow (R := ℂ)
    (by exact Nat.succ_ne_zero 40)) f n

theorem qPullback41Z_mul (f g : PowerSeries ℤ) :
    qPullback41Z (f * g) = qPullback41Z f * qPullback41Z g := by
  unfold qPullback41Z
  exact PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow (R := ℤ)
    (by exact Nat.succ_ne_zero 40)) f g

theorem qPullback41Z_pow (f : PowerSeries ℤ) (n : ℕ) :
    qPullback41Z (f ^ n) = qPullback41Z f ^ n := by
  unfold qPullback41Z
  exact PowerSeries.subst_pow (PowerSeries.HasSubst.X_pow (R := ℤ)
    (by exact Nat.succ_ne_zero 40)) f n

@[simp]
theorem coeff_qPullback41 (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (qPullback41 f) =
      if 41 ∣ n then PowerSeries.coeff (R := ℂ) (n / 41) f else 0 := by
  have h41 : (41 : ℕ) ≠ 0 := Nat.succ_ne_zero 40
  simp [qPullback41,
    (PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ)
      (k := 41) h41 f n)]

/-- Evaluating a pullback `q ↦ q^41` is the same as evaluating the original
series at `q^41`; the inserted coefficients away from multiples of `41` are
handled by extending the summation by zero. -/
theorem qPullback41_hasSum_eval
    {f : PowerSeries ℂ} {q value : ℂ}
    (hsum : HasSum (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n f * (q ^ 41) ^ n) value) :
    HasSum (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n (qPullback41 f) * q ^ n) value := by
  classical
  let g : ℕ → ℕ := fun n => 41 * n
  have hg : Function.Injective g := by
    intro a b h
    exact Nat.mul_left_cancel (by norm_num : 0 < 41) h
  have hbase : HasSum (Function.extend g
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f * (q ^ 41) ^ n)
      (fun _ : ℕ => (0 : ℂ))) value := by
    exact (hasSum_extend_zero hg).2 hsum
  convert hbase using 1
  funext m
  by_cases hm : 41 ∣ m
  · have hgimg : ∃ a, g a = m := by
      refine ⟨m / 41, ?_⟩
      dsimp [g]
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hm
    rw [Function.extend_def]
    simp only [hgimg, dif_pos]
    have hchoose : g (Classical.choose hgimg) = m :=
      Classical.choose_spec hgimg
    have hchoose_eq : Classical.choose hgimg = m / 41 := by
      apply hg
      rw [hchoose]
      dsimp [g]
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel hm).symm
    rw [coeff_qPullback41, if_pos hm, hchoose_eq]
    have hpow : q ^ m = (q ^ 41) ^ (m / 41) := by
      rw [← pow_mul, Nat.mul_comm, Nat.div_mul_cancel hm]
    rw [hpow]
  · have hnot : ¬ ∃ a, g a = m := by
      rintro ⟨a, ha⟩
      apply hm
      use a
      exact ha.symm
    rw [Function.extend_apply' _ _ _ hnot]
    rw [coeff_qPullback41, if_neg hm]
    simp

theorem qPullback41_summable_norm_eval
    {f : PowerSeries ℂ} {q : ℂ}
    (hsumm : Summable fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n f * (q ^ 41) ^ n‖) :
    Summable fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n (qPullback41 f) * q ^ n‖ := by
  classical
  let g : ℕ → ℕ := fun n => 41 * n
  have hg : Function.Injective g := by
    intro a b h
    exact Nat.mul_left_cancel (by norm_num : 0 < 41) h
  have hbase : Summable (Function.extend g
      (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n f * (q ^ 41) ^ n‖)
      (fun _ : ℕ => (0 : ℝ))) := by
    exact ((hasSum_extend_zero hg).2 hsumm.hasSum).summable
  convert hbase using 1
  funext m
  by_cases hm : 41 ∣ m
  · have hgimg : ∃ a, g a = m := by
      refine ⟨m / 41, ?_⟩
      dsimp [g]
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hm
    rw [Function.extend_def]
    simp only [hgimg, dif_pos]
    have hchoose : g (Classical.choose hgimg) = m :=
      Classical.choose_spec hgimg
    have hchoose_eq : Classical.choose hgimg = m / 41 := by
      apply hg
      rw [hchoose]
      dsimp [g]
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel hm).symm
    rw [coeff_qPullback41, if_pos hm, hchoose_eq]
    have hpow : q ^ m = (q ^ 41) ^ (m / 41) := by
      rw [← pow_mul, Nat.mul_comm, Nat.div_mul_cancel hm]
    rw [hpow]
  · have hnot : ¬ ∃ a, g a = m := by
      rintro ⟨a, ha⟩
      apply hm
      use a
      exact ha.symm
    rw [Function.extend_apply' _ _ _ hnot]
    rw [coeff_qPullback41, if_neg hm]
    simp

@[simp]
theorem coeff_qPullback41Z (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (qPullback41Z f) =
      if 41 ∣ n then PowerSeries.coeff (R := ℤ) (n / 41) f else 0 := by
  have h41 : (41 : ℕ) ≠ 0 := Nat.succ_ne_zero 40
  simp [qPullback41Z,
    (PowerSeries.coeff_subst_X_pow (R := ℤ) (S := ℤ)
      (k := 41) h41 f n)]

theorem map_qPullback41Z (f : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom ℂ) (qPullback41Z f) =
      qPullback41 (PowerSeries.map (Int.castRingHom ℂ) f) := by
  ext n
  by_cases hn : 41 ∣ n
  · rw [PowerSeries.coeff_map, coeff_qPullback41Z, coeff_qPullback41,
      if_pos hn, if_pos hn, PowerSeries.coeff_map]
  · rw [PowerSeries.coeff_map, coeff_qPullback41Z, coeff_qPullback41,
      if_neg hn, if_neg hn]
    simp

theorem coeff_qPullback41Z_deltaEulerSeriesZ_eq_trunc_of_dvd {N n : ℕ}
    (hn : 41 ∣ n) (hN : n / 41 < N) :
    PowerSeries.coeff (R := ℤ) n (qPullback41Z deltaEulerSeriesZ) =
      PowerSeries.coeff (R := ℤ) (n / 41) (deltaEulerProductTruncZ N) := by
  rw [coeff_qPullback41Z, if_pos hn, coeff_deltaEulerSeriesZ]
  exact (coeff_deltaEulerProductTruncZ_eq_deltaEulerCoeffZ_of_lt hN).symm

theorem coeff_qPullback41Z_deltaEulerSeriesZ_eq_zero_of_not_dvd {n : ℕ}
    (hn : ¬ 41 ∣ n) :
    PowerSeries.coeff (R := ℤ) n (qPullback41Z deltaEulerSeriesZ) = 0 := by
  rw [coeff_qPullback41Z, if_neg hn]

/-- The numerator series for `E4(tau)^3` in the variable
`Q = exp(2 pi i tau / 41)`. -/
noncomputable def E4CubedQExpansionAtTau : PowerSeries ℂ :=
  qPullback41 (E4QExpansion ^ 3)

/-- The denominator series for `Delta(tau)` in the variable
`Q = exp(2 pi i tau / 41)`. -/
noncomputable def deltaQExpansionAtTau : PowerSeries ℂ :=
  qPullback41 deltaQExpansion

/-- The numerator series for `E4(tau / 41)^3` in the same `Q` variable. -/
noncomputable def E4CubedQExpansionAtTauDiv41 : PowerSeries ℂ :=
  E4QExpansion ^ 3

/-- The denominator series for `Delta(tau / 41)` in the same `Q` variable. -/
noncomputable def deltaQExpansionAtTauDiv41 : PowerSeries ℂ :=
  deltaQExpansion

/-- Formal q-expansion of the denominator-cleared level-41 modular-polynomial
expression at `(tau, tau / 41)`.

The intended next theorem is that this series is zero, by identifying it as a
modular form on `Gamma_0(41)` and verifying enough initial coefficients. -/
noncomputable def phi41Level41ClearedQExpansion : PowerSeries ℂ :=
  evalSparseBivarCleared phi41SparseTerms 42 42
    E4CubedQExpansionAtTau deltaQExpansionAtTau
    E4CubedQExpansionAtTauDiv41 deltaQExpansionAtTauDiv41

/-- Fully formal Euler-product version of the cleared expression.  This is the
finite-coefficient verification target once `deltaQExpansion` has been
identified with `deltaEulerSeries`. -/
noncomputable def phi41Level41ClearedEulerQExpansion : PowerSeries ℂ :=
  evalSparseBivarCleared phi41SparseTerms 42 42
    (qPullback41 (E4QExpansion ^ 3)) (qPullback41 deltaEulerSeries)
    (E4QExpansion ^ 3) deltaEulerSeries

/-- Integer-coefficient version of the Euler-product cleared expression. -/
noncomputable def phi41Level41ClearedEulerQExpansionZ : PowerSeries ℤ :=
  evalSparseBivarCleared phi41SparseTerms 42 42
    (qPullback41Z (E4ZSeries ^ 3)) (qPullback41Z deltaEulerSeriesZ)
    (E4ZSeries ^ 3) deltaEulerSeriesZ

theorem map_phi41Level41ClearedEulerQExpansionZ :
    PowerSeries.map (Int.castRingHom ℂ) phi41Level41ClearedEulerQExpansionZ =
      phi41Level41ClearedEulerQExpansion := by
  unfold phi41Level41ClearedEulerQExpansionZ phi41Level41ClearedEulerQExpansion
  rw [map_evalSparseBivarCleared]
  simp [map_qPullback41Z, map_E4ZSeries, map_deltaEulerSeriesZ]

theorem coeff_phi41Level41ClearedEulerQExpansion_eq_map_coeffZ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n phi41Level41ClearedEulerQExpansion =
      (PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ : ℂ) := by
  rw [← map_phi41Level41ClearedEulerQExpansionZ, PowerSeries.coeff_map]
  rfl

theorem phi41Level41ClearedEulerQExpansion_eq_zero_of_coeffZ_eq_zero
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0) :
    phi41Level41ClearedEulerQExpansion = 0 := by
  ext n
  rw [coeff_phi41Level41ClearedEulerQExpansion_eq_map_coeffZ, hcoeff n]
  simp

theorem phi41Level41ClearedQExpansion_eq :
    phi41Level41ClearedQExpansion =
      evalSparseBivarCleared phi41SparseTerms 42 42
        (qPullback41 (E4QExpansion ^ 3)) (qPullback41 deltaQExpansion)
        (E4QExpansion ^ 3) deltaQExpansion := by
  rfl

theorem phi41Level41ClearedQExpansion_eq_euler
    (hdelta : deltaQExpansion = deltaEulerSeries) :
    phi41Level41ClearedQExpansion = phi41Level41ClearedEulerQExpansion := by
  simp [phi41Level41ClearedQExpansion, phi41Level41ClearedEulerQExpansion,
    E4CubedQExpansionAtTau, deltaQExpansionAtTau, E4CubedQExpansionAtTauDiv41,
    deltaQExpansionAtTauDiv41, hdelta]

theorem phi41Level41ClearedQExpansion_eq_zero_of_coeff_eq_zero
    (hcoeff :
      ∀ n : ℕ, PowerSeries.coeff (R := ℂ) n phi41Level41ClearedQExpansion = 0) :
    phi41Level41ClearedQExpansion = 0 := by
  ext n
  exact hcoeff n

theorem phi41Level41ClearedQExpansion_eq_zero_of_delta_euler
    (hdelta : deltaQExpansion = deltaEulerSeries)
    (hcoeff :
      ∀ n : ℕ, PowerSeries.coeff (R := ℂ) n phi41Level41ClearedEulerQExpansion = 0) :
    phi41Level41ClearedQExpansion = 0 := by
  rw [phi41Level41ClearedQExpansion_eq_euler hdelta]
  ext n
  exact hcoeff n

theorem phi41Level41ClearedQExpansion_eq_zero_of_delta_euler_and_coeffZ
    (hdelta : deltaQExpansion = deltaEulerSeries)
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0) :
    phi41Level41ClearedQExpansion = 0 := by
  rw [phi41Level41ClearedQExpansion_eq_euler hdelta]
  exact phi41Level41ClearedEulerQExpansion_eq_zero_of_coeffZ_eq_zero hcoeff

theorem phi41Level41ClearedQExpansion_eq_zero_of_delta_coeff_and_coeffZ
    (hdeltaCoeff :
      ∀ d : ℕ, PowerSeries.coeff (R := ℂ) d deltaQExpansion = deltaEulerCoeff d)
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0) :
    phi41Level41ClearedQExpansion = 0 := by
  exact phi41Level41ClearedQExpansion_eq_zero_of_delta_euler_and_coeffZ
    (deltaQExpansion_eq_deltaEulerSeries_of_coeff hdeltaCoeff) hcoeff

theorem powerSeries_coeff_hasSum_value_eq_zero_of_eq_zero
    {p : PowerSeries ℂ} {q value : ℂ}
    (hsum : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n p * q ^ n) value)
    (hp : p = 0) :
    value = 0 := by
  have hsum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) value := by
    simpa [hp] using hsum
  exact hsum_zero.unique hasSum_zero

theorem powerSeries_mul_hasSum_eval
    {p r : PowerSeries ℂ} {q pv rv : ℂ}
    (hp : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n p * q ^ n) pv)
    (hr : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n r * q ^ n) rv)
    (hpair : Summable fun x : ℕ × ℕ =>
      (PowerSeries.coeff (R := ℂ) x.1 p * q ^ x.1) *
        (PowerSeries.coeff (R := ℂ) x.2 r * q ^ x.2)) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (p * r) * q ^ n)
      (pv * rv) := by
  let f : ℕ → ℂ := fun n => PowerSeries.coeff (R := ℂ) n p * q ^ n
  let g : ℕ → ℂ := fun n => PowerSeries.coeff (R := ℂ) n r * q ^ n
  have hf : Summable f := hp.summable
  have hg : Summable g := hr.summable
  have hcauchy := hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hpair
  have hpv : (∑' n : ℕ, f n) = pv := hp.tsum_eq
  have hrv : (∑' n : ℕ, g n) = rv := hr.tsum_eq
  have hterm : (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n (p * r) * q ^ n) =
      fun n : ℕ => ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
    funext n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro kl hkl
    rw [Finset.mem_antidiagonal] at hkl
    dsimp [f, g]
    have hpow : q ^ kl.1 * q ^ kl.2 = q ^ n := by
      rw [← pow_add, hkl]
    rw [← hpow]
    ring
  have hprod_tsum :
      (∑' n : ℕ, PowerSeries.coeff (R := ℂ) n (p * r) * q ^ n) =
        pv * rv := by
    rw [hterm, ← hcauchy, hpv, hrv]
  have hprod_summ :
      Summable (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n (p * r) * q ^ n) := by
    rw [hterm]
    exact summable_sum_mul_antidiagonal_of_summable_mul hpair
  exact (hprod_summ.hasSum_iff).2 hprod_tsum

theorem powerSeries_mul_hasSum_eval_of_summable_norm
    {p r : PowerSeries ℂ} {q pv rv : ℂ}
    (hp : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n p * q ^ n) pv)
    (hr : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n r * q ^ n) rv)
    (hp_abs : Summable fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n p * q ^ n‖)
    (hr_abs : Summable fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n r * q ^ n‖) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (p * r) * q ^ n)
      (pv * rv) := by
  let f : ℕ → ℂ := fun n => PowerSeries.coeff (R := ℂ) n p * q ^ n
  let g : ℕ → ℂ := fun n => PowerSeries.coeff (R := ℂ) n r * q ^ n
  have hf_abs : Summable fun n : ℕ => ‖f n‖ := by
    simpa [f] using hp_abs
  have hg_abs : Summable fun n : ℕ => ‖g n‖ := by
    simpa [g] using hr_abs
  have hpair : Summable fun x : ℕ × ℕ => f x.1 * g x.2 :=
    summable_mul_of_summable_norm hf_abs hg_abs
  exact powerSeries_mul_hasSum_eval hp hr (by simpa [f, g] using hpair)

theorem powerSeries_mul_summable_norm_eval
    {p r : PowerSeries ℂ} {q : ℂ}
    (hp_abs : Summable fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n p * q ^ n‖)
    (hr_abs : Summable fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n r * q ^ n‖) :
    Summable fun n : ℕ =>
      ‖PowerSeries.coeff (R := ℂ) n (p * r) * q ^ n‖ := by
  let f : ℕ → ℂ := fun n => PowerSeries.coeff (R := ℂ) n p * q ^ n
  let g : ℕ → ℂ := fun n => PowerSeries.coeff (R := ℂ) n r * q ^ n
  have hf_abs : Summable fun n : ℕ => ‖f n‖ := by
    simpa [f] using hp_abs
  have hg_abs : Summable fun n : ℕ => ‖g n‖ := by
    simpa [g] using hr_abs
  have hterm : (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n (p * r) * q ^ n) =
      fun n : ℕ => ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
    funext n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro kl hkl
    rw [Finset.mem_antidiagonal] at hkl
    dsimp [f, g]
    have hpow : q ^ kl.1 * q ^ kl.2 = q ^ n := by
      rw [← pow_add, hkl]
    rw [← hpow]
    ring
  have hs : Summable fun n : ℕ =>
      ‖∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2‖ :=
    summable_norm_sum_mul_antidiagonal_of_summable_norm hf_abs hg_abs
  change Summable (fun n : ℕ =>
    ‖(fun n : ℕ => PowerSeries.coeff (R := ℂ) n (p * r) * q ^ n) n‖)
  rw [hterm]
  exact hs

/-- A q-evaluation certificate for a formal power series, carrying both the
evaluated sum and the absolute convergence needed for Cauchy products. -/
structure PowerSeriesEvalCertificate (p : PowerSeries ℂ) (q value : ℂ) : Prop where
  hasSum : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n p * q ^ n) value
  summable_norm : Summable fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n p * q ^ n‖

namespace PowerSeriesEvalCertificate

theorem one (q : ℂ) :
    PowerSeriesEvalCertificate (1 : PowerSeries ℂ) q 1 := by
  refine ⟨?_, ?_⟩
  · simpa using
      (hasSum_single
        (f := fun n : ℕ => PowerSeries.coeff (R := ℂ) n
          (1 : PowerSeries ℂ) * q ^ n)
        (0 : ℕ) (by intro b hb; simp [hb]))
  · exact (show HasSum
        (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n
          (1 : PowerSeries ℂ) * q ^ n‖) 1 from by
        simpa using
          (hasSum_single
            (f := fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n
              (1 : PowerSeries ℂ) * q ^ n‖)
            (0 : ℕ) (by intro b hb; simp [hb]))).summable

theorem const (c q : ℂ) :
    PowerSeriesEvalCertificate (PowerSeries.C c) q c := by
  refine ⟨?_, ?_⟩
  · simpa using
      (hasSum_single
        (f := fun n : ℕ => PowerSeries.coeff (R := ℂ) n
          (PowerSeries.C c) * q ^ n)
        (0 : ℕ) (by intro b hb; simp [PowerSeries.coeff_C, hb]))
  · exact (show HasSum
        (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n
          (PowerSeries.C c) * q ^ n‖) ‖c‖ from by
        simpa using
          (hasSum_single
            (f := fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n
              (PowerSeries.C c) * q ^ n‖)
            (0 : ℕ) (by intro b hb; simp [PowerSeries.coeff_C, hb]))).summable

theorem mul {p r : PowerSeries ℂ} {q pv rv : ℂ}
    (hp : PowerSeriesEvalCertificate p q pv)
    (hr : PowerSeriesEvalCertificate r q rv) :
    PowerSeriesEvalCertificate (p * r) q (pv * rv) := by
  exact ⟨powerSeries_mul_hasSum_eval_of_summable_norm hp.hasSum hr.hasSum
      hp.summable_norm hr.summable_norm,
    powerSeries_mul_summable_norm_eval hp.summable_norm hr.summable_norm⟩

theorem pow {p : PowerSeries ℂ} {q pv : ℂ}
    (hp : PowerSeriesEvalCertificate p q pv) (k : ℕ) :
    PowerSeriesEvalCertificate (p ^ k) q (pv ^ k) := by
  induction k with
  | zero => simpa using one q
  | succ k ih =>
      simpa [pow_succ] using mul ih hp

theorem qPullback41 {p : PowerSeries ℂ} {q pv : ℂ}
    (hp : PowerSeriesEvalCertificate p (q ^ 41) pv) :
    PowerSeriesEvalCertificate (Modular.qPullback41 p) q pv := by
  exact ⟨qPullback41_hasSum_eval hp.hasSum,
    qPullback41_summable_norm_eval hp.summable_norm⟩

end PowerSeriesEvalCertificate

theorem E4QExpansion_evalCertificate (τ : ℍ) :
    PowerSeriesEvalCertificate E4QExpansion
      (Function.Periodic.qParam 1 (τ : ℂ)) (E4 τ) := by
  exact ⟨E4QExpansion_hasSum τ, E4QExpansion_summable_norm τ⟩

/-- Finite sparse cleared expressions preserve termwise `HasSum` evaluation.

This isolates the only infinite work in q-expansion evaluation to the individual
monomial series.  The sparse polynomial layer is a finite sum. -/
theorem evalSparseBivarCleared_hasSum_of_term_hasSum
    (terms : List SparseBivarTerm) (xMax yMax : ℕ)
    (xNum xDen yNum yDen : PowerSeries ℂ)
    (xNumV xDenV yNumV yDenV q : ℂ)
    (hterms :
      ∀ t : SparseBivarTerm, t ∈ terms →
        HasSum (fun n : ℕ =>
          PowerSeries.coeff (R := ℂ) n
              ((t.coeff : PowerSeries ℂ) *
                xNum ^ t.xPow * xDen ^ (xMax - t.xPow) *
                yNum ^ t.yPow * yDen ^ (yMax - t.yPow)) * q ^ n)
          ((t.coeff : ℂ) * xNumV ^ t.xPow * xDenV ^ (xMax - t.xPow) *
            yNumV ^ t.yPow * yDenV ^ (yMax - t.yPow))) :
    HasSum (fun n : ℕ =>
      PowerSeries.coeff (R := ℂ) n
          (evalSparseBivarCleared terms xMax yMax xNum xDen yNum yDen) * q ^ n)
      (evalSparseBivarClearedC terms xMax yMax xNumV xDenV yNumV yDenV) := by
  induction terms with
  | nil =>
      simp [evalSparseBivarCleared, evalSparseBivarClearedC]
  | cons t ts ih =>
      have hhead := hterms t (by simp)
      have htail :
          HasSum (fun n : ℕ =>
            PowerSeries.coeff (R := ℂ) n
                (evalSparseBivarCleared ts xMax yMax xNum xDen yNum yDen) * q ^ n)
            (evalSparseBivarClearedC ts xMax yMax xNumV xDenV yNumV yDenV) := by
        refine ih ?_
        intro u hu
        exact hterms u (by simp [hu])
      have hsum := hhead.add htail
      simpa [evalSparseBivarCleared, evalSparseBivarClearedC, add_mul]
        using hsum

/-- The weight of the denominator-cleared level-41 expression:
each substituted numerator/denominator factor has weight `12`, and clearing
to bidegree `(42, 42)` gives `12 * (42 + 42) = 1008`. -/
def phi41Level41ClearedWeight : ℕ := 1008

theorem phi41SparseTerms_cleared_term_weight (t : SparseBivarTerm)
    (ht : t ∈ phi41SparseTerms) :
    12 * t.xPow + 12 * (42 - t.xPow) +
        (12 * t.yPow + 12 * (42 - t.yPow)) =
      phi41Level41ClearedWeight := by
  have hdeg := phi41SparseTerms_degree_le_42 t ht
  unfold phi41Level41ClearedWeight
  omega

/-- The Sturm bound expected for weight `1008` on `Gamma_0(41)`:
`⌊1008 / 12 * [SL_2(Z) : Gamma_0(41)]⌋ + 1 = 84 * 42 + 1 = 3529`.
The `+ 1` matches the classical level-`N` Sturm bound (Stein, Lemma 9.18,
via the valence formula): vanishing of the first
`⌊k·index/12⌋ + 1` `q`-coefficients implies the form is zero. -/
def phi41Level41SturmBound : ℕ := 3529

theorem phi41Level41SturmBound_eq :
    phi41Level41SturmBound = phi41Level41ClearedWeight / 12 * 42 + 1 := by
  rfl

/-- The finite integer q-expansion certificate needed for the level-41
Sturm check: all coefficients below the Sturm bound vanish. -/
def phi41Level41SturmCoefficientCertificate : Prop :=
  ∀ n : ℕ, n < phi41Level41SturmBound →
    PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0

/-- Finset-range form of the finite Sturm certificate, convenient for
machine-generated coefficient checks. -/
def phi41Level41SturmCoefficientRangeCertificate : Prop :=
  ∀ n : ℕ, n ∈ Finset.range phi41Level41SturmBound →
    PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0

def phi41Level41ComplexSturmCoefficientCertificate : Prop :=
  ∀ n : ℕ, n < phi41Level41SturmBound →
    PowerSeries.coeff (R := ℂ) n phi41Level41ClearedEulerQExpansion = 0

theorem phi41Level41SturmCoefficientCertificate_of_range
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    phi41Level41SturmCoefficientCertificate := by
  intro n hn
  exact hcert n (Finset.mem_range.mpr hn)

theorem phi41Level41ComplexSturmCoefficientCertificate_of_int
    (hcert : phi41Level41SturmCoefficientCertificate) :
    phi41Level41ComplexSturmCoefficientCertificate := by
  intro n hn
  rw [coeff_phi41Level41ClearedEulerQExpansion_eq_map_coeffZ, hcert n hn]
  simp

/-- A packaged Sturm principle for the denominator-cleared level-41
q-expansion.  The actual modular-form Sturm theorem should supply this
principle; this definition keeps that standard input separated from the
finite coefficient certificate. -/
def phi41Level41SturmPrinciple : Prop :=
  phi41Level41SturmCoefficientCertificate →
    ∀ n : ℕ,
      PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0

def phi41Level41ComplexSturmPrinciple : Prop :=
  phi41Level41ComplexSturmCoefficientCertificate →
    ∀ n : ℕ,
      PowerSeries.coeff (R := ℂ) n phi41Level41ClearedEulerQExpansion = 0

theorem gamma0_41_strictPeriod_one :
    (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem gamma0_41_qExpansion_eq_zero_iff {k : ℤ}
    (f : ModularForm
      (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularFormClass.qExpansion 1 f.toFun = 0 ↔ f = 0 := by
  simpa [ModularForm.toFun_eq_coe] using
    (ModularForm.qExpansion_eq_zero_iff (h := 1)
      (by norm_num : (0 : ℝ) < 1)
      gamma0_41_strictPeriod_one
      f)

theorem gamma0_41_modularForm_eq_zero_of_qExpansion_coeff_eq_zero {k : ℤ}
    (f : ModularForm
      (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)) k)
    (hcoeff :
      ∀ n : ℕ,
        PowerSeries.coeff (R := ℂ) n (ModularFormClass.qExpansion 1 f.toFun) = 0) :
    f = 0 := by
  apply (gamma0_41_qExpansion_eq_zero_iff f).mp
  ext n
  exact hcoeff n

theorem phi41Level41SturmPrinciple_of_complex
    (hsturm : phi41Level41ComplexSturmPrinciple) :
    phi41Level41SturmPrinciple := by
  intro hcert n
  have hcoeffC := hsturm
    (phi41Level41ComplexSturmCoefficientCertificate_of_int hcert) n
  have hcast :
      ((PowerSeries.coeff (R := ℤ) n
        phi41Level41ClearedEulerQExpansionZ : ℤ) : ℂ) = 0 := by
    simpa [coeff_phi41Level41ClearedEulerQExpansion_eq_map_coeffZ] using hcoeffC
  exact_mod_cast hcast

/-- Structural reduction of the phi41 Sturm principle to two clean
mathematical inputs:

1. A bundled `ModularForm (Gamma0 41) 1008` whose `q`-expansion equals
   `phi41Level41ClearedEulerQExpansion` (the modularity of the
   denominator-cleared expression — supplied by
   `phi41Level41ClearedAsModularForm` in `Phi41ModularFormAssembly.lean`).
2. The Sturm bound at level `Γ₀(41)` weight `1008`: for any such
   modular form, vanishing of the first `3529 = 1008 * 42 / 12 + 1`
   `q`-expansion coefficients implies the form is zero (norm trick to
   `ModularForm 𝒮ℒ 42336` + generic level-1 Sturm — supplied by
   `levelGamma0_41_sturm_weight_1008` in `Gamma0_41_SturmBound.lean`).

Once both inputs are supplied, `complex_sturm_bound_valence_formula_phi41Level41Cleared`
follows by pure formal manipulation. -/
theorem complex_sturm_bound_valence_formula_phi41Level41Cleared_of_inputs
    (f : ModularForm
      (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)) 1008)
    (hbridge : ModularFormClass.qExpansion (1 : ℝ) f.toFun =
      phi41Level41ClearedEulerQExpansion)
    (hSturm : (∀ n : ℕ, n < phi41Level41SturmBound →
        PowerSeries.coeff (R := ℂ) n
          (ModularFormClass.qExpansion (1 : ℝ) f.toFun) = 0) → f = 0) :
    phi41Level41ComplexSturmPrinciple := by
  intro hcert n
  -- The certificate transfers through the bridge.
  have hcert' : ∀ m : ℕ, m < phi41Level41SturmBound →
      PowerSeries.coeff (R := ℂ) m
        (ModularFormClass.qExpansion (1 : ℝ) f.toFun) = 0 := by
    intro m hm
    rw [hbridge]
    exact hcert m hm
  -- Apply Sturm to deduce f = 0.
  have hf_zero : f = 0 := hSturm hcert'
  -- All q-expansion coefficients of `f` then vanish, so do those of
  -- phi41Level41ClearedEulerQExpansion via the bridge.
  have hqExpf_zero : ModularFormClass.qExpansion (1 : ℝ) f.toFun = 0 := by
    rw [(gamma0_41_qExpansion_eq_zero_iff f).mpr hf_zero]
  have hqExp_zero : phi41Level41ClearedEulerQExpansion = 0 := by
    rw [← hbridge]; exact hqExpf_zero
  rw [hqExp_zero]
  simp

theorem phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_sturm
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate) :
    ∀ n : ℕ,
      PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0 :=
  hsturm hcert

theorem phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_sturm_range
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    ∀ n : ℕ,
      PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0 :=
  phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_sturm hsturm
    (phi41Level41SturmCoefficientCertificate_of_range hcert)

theorem phi41Level41ClearedEulerQExpansion_eq_zero_of_sturm
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate) :
    phi41Level41ClearedEulerQExpansion = 0 := by
  exact phi41Level41ClearedEulerQExpansion_eq_zero_of_coeffZ_eq_zero
    (phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_sturm hsturm hcert)

theorem phi41Level41ClearedEulerQExpansion_eq_zero_of_sturm_range
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    phi41Level41ClearedEulerQExpansion = 0 := by
  exact phi41Level41ClearedEulerQExpansion_eq_zero_of_sturm hsturm
    (phi41Level41SturmCoefficientCertificate_of_range hcert)

theorem phi41Level41ClearedQExpansion_eq_zero_of_euler_sturm
    (hdelta : deltaQExpansion = deltaEulerSeries)
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientCertificate) :
    phi41Level41ClearedQExpansion = 0 := by
  exact phi41Level41ClearedQExpansion_eq_zero_of_delta_euler_and_coeffZ
    hdelta
    (phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_sturm hsturm hcert)

theorem phi41Level41ClearedQExpansion_eq_zero_of_euler_sturm_range
    (hdelta : deltaQExpansion = deltaEulerSeries)
    (hsturm : phi41Level41SturmPrinciple)
    (hcert : phi41Level41SturmCoefficientRangeCertificate) :
    phi41Level41ClearedQExpansion = 0 := by
  exact phi41Level41ClearedQExpansion_eq_zero_of_euler_sturm hdelta hsturm
    (phi41Level41SturmCoefficientCertificate_of_range hcert)

end Modular
end Number
end Ripple
