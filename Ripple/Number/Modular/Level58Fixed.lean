import Ripple.Number.Modular.Psi29Certificate
import Ripple.Number.Milla.Ramanujan

/-!
# The Fricke involution `W₂` and the fixing map of `τ₅₈`

`W₂ τ = −1/(2τ)` (`fricke2`) swaps `E₄(τ)` and `E₄(2τ)` up to the factors `(2τ)⁴` and `τ⁴`; the
quadratic forms `P`, `Q` both pick up `16τ⁸`, so the Hauptmodul `T = P/Q` is `W₂`-invariant
(`hauptT58_fricke2`). With `μ(τ) = 29 · W₂(τ) = −29/(2τ)` (`mu58`), the modular equation
`Ψ₂₉(T(29τ), T(τ)) = 0` at `W₂τ` becomes `Ψ₂₉(T(μτ), T(τ)) = 0` (`psi29_mu58_equation`).
-/

namespace Ripple.Number.Modular

open UpperHalfPlane

/-- The Fricke involution of level 2: `W₂ τ = −1/(2τ)`. -/
noncomputable def fricke2 (τ : ℍ) : ℍ := ModularGroup.S • (scaleGL 2 • τ)

theorem coe_fricke2 (τ : ℍ) : (fricke2 τ : ℂ) = -1 / (2 * τ) := by
  rw [fricke2, UpperHalfPlane.modular_S_smul, coe_mk, coe_scaleGL_smul]
  push_cast
  ring

theorem scaleGL_two_fricke2 (τ : ℍ) : scaleGL 2 • fricke2 τ = ModularGroup.S • τ := by
  apply UpperHalfPlane.ext
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [coe_scaleGL_smul, coe_fricke2]
  simp only [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
  push_cast
  field_simp

theorem E4_fricke2 (τ : ℍ) : E4 (fricke2 τ) = (2 * (τ : ℂ)) ^ 4 * E4 (scaleGL 2 • τ) := by
  rw [fricke2, Milla.modularForm_S_smul, coe_scaleGL_smul]
  simp [zpow_ofNat]

theorem E4_scale_fricke2 (τ : ℍ) : E4 (scaleGL 2 • fricke2 τ) = (τ : ℂ) ^ 4 * E4 τ := by
  rw [scaleGL_two_fricke2, Milla.modularForm_S_smul]
  simp [zpow_ofNat]

theorem level2P_fricke2 (τ : ℍ) :
    level2P (E4 (fricke2 τ)) (E4 (scaleGL 2 • fricke2 τ)) =
      16 * (τ : ℂ) ^ 8 * level2P (E4 τ) (E4 (scaleGL 2 • τ)) := by
  rw [E4_fricke2, E4_scale_fricke2]
  simp only [level2P, quadForm]
  push_cast
  ring

theorem level2Q_fricke2 (τ : ℍ) :
    level2Q (E4 (fricke2 τ)) (E4 (scaleGL 2 • fricke2 τ)) =
      16 * (τ : ℂ) ^ 8 * level2Q (E4 τ) (E4 (scaleGL 2 • τ)) := by
  rw [E4_fricke2, E4_scale_fricke2]
  simp only [level2Q, quadForm]
  push_cast
  ring

/-- `T ∘ W₂ = T`. -/
theorem hauptT58_fricke2 (τ : ℍ) : hauptT58 (fricke2 τ) = hauptT58 τ := by
  have hτ : (16 : ℂ) * (τ : ℂ) ^ 8 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (UpperHalfPlane.ne_zero τ))
  rw [hauptT58, hauptT58, level2P_fricke2, level2Q_fricke2, mul_div_mul_left _ _ hτ]

/-- The fixing map of `τ₅₈ = i√58/2`: `μ(τ) = −29/(2τ)`. -/
noncomputable def mu58 (τ : ℍ) : ℍ := scaleGL 29 • fricke2 τ

theorem coe_mu58 (τ : ℍ) : (mu58 τ : ℂ) = -29 / (2 * τ) := by
  rw [mu58, coe_scaleGL_smul, coe_fricke2]
  push_cast
  ring

/-- `Ψ₂₉(T(μτ), T(τ)) = 0` wherever `Q(τ)`, `Q(μτ)` do not vanish. -/
theorem psi29_mu58_equation (τ : ℍ)
    (hQ : level2Q (E4 τ) (E4 (scaleGL 2 • τ)) ≠ 0)
    (hQμ : level2Q (E4 (mu58 τ)) (E4 (scaleGL 2 • mu58 τ)) ≠ 0) :
    evalSparseBivarC psi29SparseTerms (hauptT58 (mu58 τ)) (hauptT58 τ) = 0 := by
  have hQ' : level2Q (E4 (fricke2 τ)) (E4 (scaleGL 2 • fricke2 τ)) ≠ 0 := by
    rw [level2Q_fricke2]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (UpperHalfPlane.ne_zero τ))) hQ
  have h := psi29_modular_equation (fricke2 τ) hQ' hQμ
  rwa [hauptT58_fricke2] at h

end Ripple.Number.Modular
