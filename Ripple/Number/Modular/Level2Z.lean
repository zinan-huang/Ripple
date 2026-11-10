import Ripple.Number.Modular.Gamma0Level
import Ripple.Number.Milla.Ramanujan

/-!
# The weight-2 form `Z = 2E₂(2τ) − E₂(τ)` on `Γ₀(2)`

`E₂` is not modular, but its defect `E₂ ∣[2] γ − E₂ = −D₂ γ` (Mathlib `E2_slash_action`) cancels
in `Z(τ) = 2E₂(2τ) − E₂(τ)` for `γ ∈ Γ₀(2)`. Here `Z` is built as the modular form
`E₂ ∣[2] diag(2,1) − E₂` of weight 2 on `Γ₀(2)` (`level2Z`), with its `q`-expansion
`2 E₂(q²) − E₂(q)` (`level2Z_qExpansion`).

Main statements:
* `E2_SL_smul`: `E₂(γτ) = (cτ+d)² E₂(τ) − (2πi/(2ζ(2))) c (cτ+d)`;
* `level2Z_apply`: `level2Z τ = 2 E₂(2τ) − E₂(τ)`;
* `level2Z_qExpansion`.
-/

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Complex EisensteinSeries
open scoped MatrixGroups ModularForm
open Pointwise ConjAct

/-- The constant in the transformation law of `E₂`. -/
noncomputable def e2Defect : ℂ := 1 / (2 * riemannZeta 2) * (2 * (Real.pi : ℂ) * Complex.I)

/-- The transformation law of `E₂` under `SL(2, ℤ)`, pointwise. -/
theorem E2_SL_smul (g : SL(2, ℤ)) (τ : ℍ) :
    E2 (g • τ) = denom g τ ^ 2 * E2 τ - e2Defect * ((g 1 0 : ℤ) : ℂ) * denom g τ := by
  have h := congr_fun (E2_slash_action g) τ
  rw [SL_slash_apply] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, D2, zpow_neg, zpow_two] at h
  have hD : denom g τ ≠ 0 := denom_ne_zero _ _
  have h3 := congrArg (· * (denom g τ * denom g τ)) h
  simp only at h3
  rw [inv_mul_cancel_right₀ (mul_ne_zero hD hD)] at h3
  rw [h3, e2Defect]
  field_simp

/-- `D₂ γ` is bounded at `i∞`. -/
theorem D2_isBoundedAtImInfty (g : SL(2, ℤ)) : IsBoundedAtImInfty (D2 g) := by
  rw [isBoundedAtImInfty_iff]
  refine ⟨2 * Real.pi, 1, fun z hz => ?_⟩
  simp only [D2]
  have hD : denom g z ≠ 0 := denom_ne_zero _ _
  have hpos : 0 < ‖denom g z‖ := norm_pos_iff.mpr hD
  have him : (denom g z).im = ((g 1 0 : ℤ) : ℝ) * z.im := by
    simp [ModularGroup.denom_apply]
  have hden : |((g 1 0 : ℤ) : ℝ)| * z.im ≤ ‖denom g z‖ := by
    calc |((g 1 0 : ℤ) : ℝ)| * z.im = |(denom g z).im| := by
          rw [him, abs_mul, abs_of_pos z.im_pos]
      _ ≤ ‖denom g z‖ := Complex.abs_im_le_norm _
  have hnum : ‖(2 * (Real.pi : ℂ) * Complex.I * ((g 1 0 : ℤ) : ℂ))‖ =
      2 * Real.pi * |((g 1 0 : ℤ) : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast]
    ring
  rw [norm_div, hnum, div_le_iff₀ hpos]
  have hc : 0 ≤ |((g 1 0 : ℤ) : ℝ)| := abs_nonneg _
  have h1 : |((g 1 0 : ℤ) : ℝ)| ≤ ‖denom g z‖ := by nlinarith
  nlinarith [Real.pi_pos]

/-- `E₂` is bounded at every cusp of `SL(2, ℤ)`. -/
theorem E2_isBoundedAt {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt E2 2 := by
  obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc]
  refine ⟨γ, rfl, ?_⟩
  rw [E2_slash_action, sub_eq_add_neg]
  exact Milla.isBoundedAtImInfty_E2.add (by
    simpa using (D2_isBoundedAtImInfty γ).const_smul_left (-(1 / (2 * riemannZeta 2))))

/-! ## `Γ₀(2)` and `diag(2, 1)` -/

/-- For `γ ∈ Γ₀(2)` with lower-left entry `2q`: `δ = [[a, 2b], [q, d]]`. -/
def gamma0TwoConj (γ : SL(2, ℤ)) (q : ℤ) (hq : γ 1 0 = 2 * q) : SL(2, ℤ) :=
  ⟨!![γ 0 0, 2 * γ 0 1; q, γ 1 1], by
    have h := γ.property
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    rw [hq] at h
    linarith⟩

theorem scaleGL_two_smul_gamma0 (γ : SL(2, ℤ)) (q : ℤ) (hq : γ 1 0 = 2 * q) (τ : ℍ) :
    scaleGL 2 • (γ • τ) = gamma0TwoConj γ q hq • (scaleGL 2 • τ) := by
  have hcq : ((γ 1 0 : ℤ) : ℂ) = 2 * (q : ℂ) := by exact_mod_cast hq
  have hD : ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have h := denom_ne_zero γ τ
    rwa [ModularGroup.denom_apply] at h
  rw [hcq] at hD
  have hD' : (q : ℂ) * (2 * τ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    convert hD using 1
    ring
  apply UpperHalfPlane.ext
  rw [coe_scaleGL_smul, coe_specialLinearGroup_apply, coe_specialLinearGroup_apply,
    coe_scaleGL_smul]
  simp [gamma0TwoConj, hcq]
  field_simp

theorem denom_gamma0TwoConj (γ : SL(2, ℤ)) (q : ℤ) (hq : γ 1 0 = 2 * q) (τ : ℍ) :
    denom (gamma0TwoConj γ q hq) ((scaleGL 2 • τ : ℍ) : ℂ) = denom γ τ := by
  rw [ModularGroup.denom_apply, ModularGroup.denom_apply, coe_scaleGL_smul]
  have hcq : ((γ 1 0 : ℤ) : ℂ) = 2 * (q : ℂ) := by exact_mod_cast hq
  simp [gamma0TwoConj, hcq]
  ring

/-! ## The form `Z` -/

/-- `Z = E₂ ∣[2] diag(2,1) − E₂`, i.e. `Z(τ) = 2 E₂(2τ) − E₂(τ)`. -/
noncomputable def level2ZFun : ℍ → ℂ := (E2 ∣[(2 : ℤ)] scaleGL 2) - E2

theorem level2ZFun_apply (τ : ℍ) : level2ZFun τ = 2 * E2 (scaleGL 2 • τ) - E2 τ := by
  simp only [level2ZFun, Pi.sub_apply, ModularForm.slash_def]
  simp [UpperHalfPlane.σ, UpperHalfPlane.denom, scaleGL]
  try ring

theorem level2ZFun_SL_smul (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 2) (τ : ℍ) :
    level2ZFun (γ • τ) = denom γ τ ^ 2 * level2ZFun τ := by
  rw [Gamma0_mem] at hγ
  have h2 : (2 : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by exact_mod_cast hγ)
  obtain ⟨q, hq⟩ := h2
  rw [level2ZFun_apply, level2ZFun_apply, scaleGL_two_smul_gamma0 γ q hq, E2_SL_smul,
    E2_SL_smul, denom_gamma0TwoConj]
  have hcq : ((γ 1 0 : ℤ) : ℂ) = 2 * (q : ℂ) := by exact_mod_cast hq
  have hδ : ((gamma0TwoConj γ q hq 1 0 : ℤ) : ℂ) = (q : ℂ) := by
    simp [gamma0TwoConj]
  rw [hδ, hcq]
  ring

theorem level2ZFun_slash (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Gamma0GL 2) :
    level2ZFun ∣[(2 : ℤ)] γ = level2ZFun := by
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
  funext τ
  change (level2ZFun ∣[(2 : ℤ)] γ₀) τ = level2ZFun τ
  rw [SL_slash_apply, level2ZFun_SL_smul γ₀ hγ₀]
  have hD : denom γ₀ τ ≠ 0 := denom_ne_zero _ _
  rw [zpow_neg, zpow_two]
  field_simp

theorem scaleGL_two_conj_le_SL : toConjAct (scaleGL 2) • Gamma0GL 2 ≤ 𝒮ℒ := by
  have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff
    (a := toConjAct (scaleGL 2))).mpr (gamma0GL_le_scale_conj (N := 2) (d := 2) dvd_rfl)
  rwa [map_inv, smul_inv_smul] at h

theorem level2ZFun_isBoundedAt {c : OnePoint ℝ} (hc : IsCusp c (Gamma0GL 2)) :
    c.IsBoundedAt level2ZFun 2 := by
  have hc1 : IsCusp c 𝒮ℒ := hc.mono (gamma0GL_le_SL 2)
  have hc2 : IsCusp (scaleGL 2 • c) 𝒮ℒ := (hc.smul (scaleGL 2)).mono scaleGL_two_conj_le_SL
  have hA : c.IsBoundedAt (E2 ∣[(2 : ℤ)] scaleGL 2) 2 :=
    OnePoint.IsBoundedAt.smul_iff.mp (E2_isBoundedAt hc2)
  have hB : c.IsBoundedAt (-E2) 2 := fun g hg => by
    simpa [SlashAction.neg_slash] using (E2_isBoundedAt hc1 g hg).const_smul_left (-1 : ℂ)
  simpa [level2ZFun, sub_eq_add_neg] using hA.add hB

/-- `Z = 2E₂(2τ) − E₂(τ)` as a weight-2 modular form on `Γ₀(2)`. -/
noncomputable def level2Z : ModularForm (Gamma0GL 2) 2 where
  toFun := level2ZFun
  slash_action_eq' := level2ZFun_slash
  holo' := (E2_mdifferentiable.slash 2 (scaleGL 2)).sub E2_mdifferentiable
  bdd_at_cusps' := level2ZFun_isBoundedAt

theorem level2Z_apply (τ : ℍ) : level2Z τ = 2 * E2 (scaleGL 2 • τ) - E2 τ :=
  level2ZFun_apply τ

/-! ## `q`-expansion -/

/-- The `q`-expansion `1 − 24 Σ σ₁(n) qⁿ` of `E₂`. -/
noncomputable def E2QExpansion : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then (1 : ℂ) else (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ)

theorem coeff_E2QExpansion (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n E2QExpansion =
      if n = 0 then (1 : ℂ) else (-24 : ℂ) * (ArithmeticFunction.sigma 1 n : ℂ) := by
  simp [E2QExpansion]

theorem E2QExpansion_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n E2QExpansion *
      Function.Periodic.qParam 1 (τ : ℂ) ^ n) (E2 τ) := by
  simpa [coeff_E2QExpansion] using E2_qExpansion_hasSum τ

/-- The `q`-expansion of `Z`. -/
noncomputable def level2ZQExpansion : PowerSeries ℂ :=
  (2 : ℂ) • qPullbackBy 2 E2QExpansion - E2QExpansion

theorem level2Z_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ) (level2Z : ℍ → ℂ) = level2ZQExpansion := by
  ext n
  symm
  refine ModularFormClass.qExpansion_coeff_unique
    (c := fun n => PowerSeries.coeff (R := ℂ) n level2ZQExpansion)
    (F := ModularForm (Gamma0GL 2) 2) (f := level2Z)
    (k := 2) one_pos (gamma0GL_strictPeriod_one 2) ?_ n
  intro τ
  rw [level2Z_apply τ]
  have h1 : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (qPullbackBy 2 E2QExpansion) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ n) (E2 (scaleGL 2 • τ)) := by
    refine qPullbackBy_hasSum_eval 2 ?_
    simpa [qParam_scaleGL 2 τ] using E2QExpansion_hasSum (scaleGL 2 • τ)
  have h2 := E2QExpansion_hasSum τ
  have h := (h1.mul_left 2).sub h2
  convert h using 1
  funext n
  simp only [level2ZQExpansion, map_sub, map_smul, smul_eq_mul]
  ring

end Modular
end Number
end Ripple
