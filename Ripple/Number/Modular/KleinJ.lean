import Ripple.Number.Modular.CMReduction
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Minimal level-one modular objects for Ramanujan--Chudnovsky identities

Mathlib exposes level-one Eisenstein series as `ModularForm.E`; this file
names the weight `4` and `6` forms and the classical Klein invariant
`j = E₄^3 / Δ` as an unbundled function on the upper half-plane.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Modular

open ModularForm
open EisensteinSeries
open CongruenceSubgroup
open scoped UpperHalfPlane MatrixGroups

/-- The normalized level-one Eisenstein series of weight `4`. -/
noncomputable def E4 : ModularForm 𝒮ℒ 4 :=
  ModularForm.E (k := 4) (by norm_num)

/-- The normalized level-one Eisenstein series of weight `6`. -/
noncomputable def E6 : ModularForm 𝒮ℒ 6 :=
  ModularForm.E (k := 6) (by norm_num)

/-- The Klein invariant `j(τ) = E₄(τ)^3 / Δ(τ)`. -/
noncomputable def kleinJ (τ : ℍ) : ℂ :=
  (E4 τ) ^ 3 / ModularForm.discriminant τ

lemma kleinJ_eq_E4_cubed_div_delta (τ : ℍ) :
    kleinJ τ = (E4 τ) ^ 3 / ModularForm.discriminant τ := rfl

lemma kleinJ_den_ne_zero (τ : ℍ) :
    ModularForm.discriminant τ ≠ 0 :=
  ModularForm.discriminant_ne_zero τ

lemma E4_qExpansion (τ : ℍ) :
    E4 τ = 1 + 240 * ∑' n : ℕ+,
      (ArithmeticFunction.sigma 3 n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ (n : ℕ) := by
  unfold E4
  rw [EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) (by decide) τ]
  simp_rw [zpow_natCast]
  rw [show bernoulli 4 = -1 / 30 by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : 4 ≠ 1), bernoulli'_four]]
  ring_nf
  congr
  ext n
  ring

lemma E6_qExpansion (τ : ℍ) :
    E6 τ = 1 - 504 * ∑' n : ℕ+,
      (ArithmeticFunction.sigma 5 n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ (n : ℕ) := by
  unfold E6
  rw [EisensteinSeries.q_expansion_bernoulli (k := 6) (by norm_num) (by decide) τ]
  simp_rw [zpow_natCast]
  rw [show bernoulli 6 = 1 / 42 by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num : 6 ≠ 1)]
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four,
      bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by norm_num : 1 < 5), Nat.choose]]
  ring_nf
  congr
  ext n
  ring

/-- `T`-invariance of a level-`𝒮ℒ` Eisenstein series, weight `k`. -/
private lemma E_T_invariant {k : ℕ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    f (ModularGroup.T • τ) = f τ := by
  have h := SlashInvariantForm.slash_action_eqn f
    ((ModularGroup.T : SL(2,ℤ)) : GL (Fin 2) ℝ) ⟨ModularGroup.T, rfl⟩
  rw [← ModularForm.SL_slash] at h
  have h2 := congrFun h τ
  rw [ModularForm.SL_slash_apply] at h2
  simpa [ModularGroup.T, UpperHalfPlane.denom] using h2

/-- `S`-transformation of a level-`𝒮ℒ` Eisenstein series, weight `k`. -/
private lemma E_S_transform {k : ℕ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    f (ModularGroup.S • τ) = (τ : ℂ)^k * f τ := by
  have h := SlashInvariantForm.slash_action_eqn f
    ((ModularGroup.S : SL(2,ℤ)) : GL (Fin 2) ℝ) ⟨ModularGroup.S, rfl⟩
  rw [← ModularForm.SL_slash] at h
  have h2 := congrFun h τ
  rw [ModularForm.SL_slash_apply] at h2
  have hden : (UpperHalfPlane.denom (((ModularGroup.S : SL(2,ℤ)) : GL (Fin 2) ℝ)) τ) = (τ : ℂ) := by
    simp [ModularGroup.S, UpperHalfPlane.denom]
  rw [hden] at h2
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [zpow_neg, ← div_eq_mul_inv] at h2
  field_simp [hτ] at h2
  rw [zpow_natCast] at h2
  linear_combination h2

lemma E4_T_invariant (τ : ℍ) : E4 (ModularGroup.T • τ) = E4 τ := E_T_invariant E4 τ

lemma E4_S_transform (τ : ℍ) : E4 (ModularGroup.S • τ) = (τ : ℂ)^4 * E4 τ := E_S_transform E4 τ

lemma E6_T_invariant (τ : ℍ) : E6 (ModularGroup.T • τ) = E6 τ := E_T_invariant E6 τ

lemma E6_S_transform (τ : ℍ) : E6 (ModularGroup.S • τ) = (τ : ℂ)^6 * E6 τ := E_S_transform E6 τ

lemma delta_T_invariant_apply (τ : ℍ) :
    ModularForm.discriminant (ModularGroup.T • τ) = ModularForm.discriminant τ := by
  have h := congrFun ModularForm.discriminant_T_invariant τ
  rw [SL_slash_apply] at h
  simpa [ModularGroup.T, UpperHalfPlane.denom] using h

lemma delta_S_transform (τ : ℍ) :
    ModularForm.discriminant (ModularGroup.S • τ)
      = (τ : ℂ)^12 * ModularForm.discriminant τ := by
  have h := congrFun ModularForm.discriminant_S_invariant τ
  rw [SL_slash_apply] at h
  have hden : UpperHalfPlane.denom (↑ModularGroup.S : GL (Fin 2) ℝ) τ = (τ : ℂ) := by
    simp [ModularGroup.S, UpperHalfPlane.denom]
  rw [hden] at h
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp [hτ] at h ⊢
  exact h

lemma kleinJ_T_invariant (τ : ℍ) : kleinJ (ModularGroup.T • τ) = kleinJ τ := by
  unfold kleinJ
  rw [E4_T_invariant, delta_T_invariant_apply]

lemma kleinJ_S_invariant (τ : ℍ) : kleinJ (ModularGroup.S • τ) = kleinJ τ := by
  unfold kleinJ
  rw [E4_S_transform, delta_S_transform]
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp [hτ]

lemma kleinJ_S_inv_invariant (τ : ℍ) :
    kleinJ (ModularGroup.S⁻¹ • τ) = kleinJ τ := by
  have h := kleinJ_S_invariant (ModularGroup.S⁻¹ • τ)
  rw [← mul_smul, mul_inv_cancel, one_smul] at h
  exact h.symm

lemma kleinJ_TS_inv_invariant (τ : ℍ) :
    kleinJ ((ModularGroup.T * ModularGroup.S⁻¹) • τ) = kleinJ τ := by
  rw [mul_smul, kleinJ_T_invariant, kleinJ_S_inv_invariant]

/-- The Heegner CM point `(1 + √(-163)) / 2` in the upper half-plane. -/
noncomputable def heegnerTau163 : ℍ :=
  ⟨((1 : ℂ) + Real.sqrt 163 * Complex.I) / 2, by
    rw [Complex.div_im]
    simp⟩

/-- The algebraic target value of the Klein invariant at discriminant `-163`. -/
noncomputable def heegnerJ163Target : ℂ :=
  -((640320 : ℂ) ^ 3)

lemma heegnerJ163Target_eq :
    heegnerJ163Target = -(262537412640768000 : ℂ) := by
  norm_num [heegnerJ163Target]

lemma heegnerTau163_re :
    (heegnerTau163 : ℂ).re = 1 / 2 := by
  norm_num [heegnerTau163]

lemma heegnerTau163_im :
    (heegnerTau163 : ℂ).im = Real.sqrt 163 / 2 := by
  norm_num [heegnerTau163]

end Modular
end Number
end Ripple
