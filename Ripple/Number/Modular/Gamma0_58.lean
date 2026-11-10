import Ripple.Number.Modular.Gamma0Level
import Ripple.Number.Modular.Psi29Terms

/-!
# Level 58: the cleared form of `Ψ₂₉` in `M₄₈₀(Γ₀(58))`

With `e = E₄(τ)`, `f = E₄(2τ)`, put

  `P = 248 e² − 616 e f + 3968 f²`,  `Q = −e² + 17 e f − 16 f²`  (weight 8 on `Γ₀(2)`),

so that the `Γ₀(2)+` Hauptmodul is `T = P / Q` (`Q = 3600 Δ₂`, `P = 3600 T Δ₂`, proved in the
level-2 layer). The cleared modular equation

  `F(τ) = Σ c_{xy} P(29τ)^x Q(29τ)^{30−x} P(τ)^y Q(τ)^{30−y}`

(`Ψ₂₉ = Σ c_{xy} X^x Y^y`, `psi29SparseTerms`) is a modular form of weight `480` on `Γ₀(58)`
(`psi29ClearedForm`). The index of `Γ₀(58)` is at most `90` (`gamma0_index_58_le`), so by the
Sturm bound `F = 0` as soon as its first `480 · 90 / 12 + 1 = 3601` coefficients vanish
(`psi29ClearedForm_eq_zero_of_coeff`).
-/

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane
open scoped MatrixGroups ModularForm DirectSum

/-! ## The index of `Γ₀(58)` -/

theorem gamma0_58_eq_inf : Gamma0 58 = Gamma0 2 ⊓ Gamma0 29 := by
  ext γ
  simp only [Subgroup.mem_inf, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  omega

theorem gamma0_index_2 : (Gamma0 2).index = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Ripple.CosetIndex.gamma0_index_prime 2

theorem gamma0_index_29 : (Gamma0 29).index = 30 := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact Ripple.CosetIndex.gamma0_index_prime 29

/-- `[SL(2,ℤ) : Γ₀(58)] ≤ [SL(2,ℤ) : Γ₀(2)] · [SL(2,ℤ) : Γ₀(29)] = 90` (in fact `= 90`). -/
theorem gamma0_index_58_le : (Gamma0 58).index ≤ 90 := by
  rw [gamma0_58_eq_inf, ← Subgroup.relIndex_top_right]
  calc (Gamma0 2 ⊓ Gamma0 29).relIndex ⊤
      ≤ (Gamma0 2).relIndex ⊤ * (Gamma0 29).relIndex ⊤ := Subgroup.relIndex_inf_le
    _ = 90 := by
      rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, gamma0_index_2,
        gamma0_index_29]

/-! ## The four `E₄` forms on `Γ₀(58)` -/

/-- `E₄(2τ)` on `Γ₀(58)`. -/
noncomputable def E4at2 : ModularForm (Gamma0GL 58) 4 := E4Scaled (show 2 ∣ 58 by norm_num)

/-- `E₄(29τ)` on `Γ₀(58)`. -/
noncomputable def E4at29 : ModularForm (Gamma0GL 58) 4 := E4Scaled (show 29 ∣ 58 by norm_num)

/-- `E₄(58τ)` on `Γ₀(58)`. -/
noncomputable def E4at58 : ModularForm (Gamma0GL 58) 4 := E4Scaled (show 58 ∣ 58 by norm_num)

/-- `a x² + b x y + c y²` in a commutative ring. -/
def quadForm {R : Type*} [CommRing R] (a b c : ℤ) (x y : R) : R :=
  (a : R) * x ^ 2 + (b : R) * x * y + (c : R) * y ^ 2

theorem map_quadForm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b c : ℤ)
    (x y : R) : φ (quadForm a b c x y) = quadForm a b c (φ x) (φ y) := by
  simp [quadForm]

/-- `P(x, y) = 248 x² − 616 x y + 3968 y²` (with `x = E₄(τ)`, `y = E₄(2τ)`: `P = 3600 T Δ₂`). -/
def level2P {R : Type*} [CommRing R] (x y : R) : R := quadForm 248 (-616) 3968 x y

/-- `Q(x, y) = −x² + 17 x y − 16 y²` (with `x = E₄(τ)`, `y = E₄(2τ)`: `Q = 3600 Δ₂`). -/
def level2Q {R : Type*} [CommRing R] (x y : R) : R := quadForm (-1) 17 (-16) x y

local notation "G58" => ⨁ k : ℤ, ModularForm (Gamma0GL 58) k

theorem psi29SparseTerms_degree_le_30 :
    ∀ t ∈ psi29SparseTerms, t.xPow ≤ 30 ∧ t.yPow ≤ 30 := by
  decide +kernel

/-- The cleared `Ψ₂₉` in the graded ring of modular forms on `Γ₀(58)`. -/
noncomputable def psi29ClearedGraded : G58 :=
  evalSparseBivarCleared psi29SparseTerms 30 30
    (level2P (gradedOf 4 E4at29) (gradedOf 4 E4at58))
    (level2Q (gradedOf 4 E4at29) (gradedOf 4 E4at58))
    (level2P (gradedOf 4 (E4Level 58)) (gradedOf 4 E4at2))
    (level2Q (gradedOf 4 (E4Level 58)) (gradedOf 4 E4at2))

/-- The cleared `Ψ₂₉` as a modular form of weight `480` on `Γ₀(58)`. -/
noncomputable def psi29ClearedForm : ModularForm (Gamma0GL 58) 480 :=
  psi29ClearedGraded 480

theorem psi29ClearedGraded_homogeneous : IsHomogeneousOf 480 psi29ClearedGraded := by
  have h4 : ∀ f : ModularForm (Gamma0GL 58) 4, IsHomogeneousOf 4 (gradedOf 4 f) :=
    fun f => isHomogeneousOf_of 4 f
  have hP : ∀ f g : ModularForm (Gamma0GL 58) 4,
      IsHomogeneousOf 8 (level2P (gradedOf 4 f) (gradedOf 4 g)) := fun f g =>
    isHomogeneousOf_cast (by norm_num) (isHomogeneousOf_quad 248 (-616) 3968 (h4 f) (h4 g))
  have hQ : ∀ f g : ModularForm (Gamma0GL 58) 4,
      IsHomogeneousOf 8 (level2Q (gradedOf 4 f) (gradedOf 4 g)) := fun f g =>
    isHomogeneousOf_cast (by norm_num) (isHomogeneousOf_quad (-1) 17 (-16) (h4 f) (h4 g))
  exact isHomogeneousOf_cast (by norm_num)
    (evalSparseBivarCleared_isHomogeneousOf psi29SparseTerms 30 30
      psi29SparseTerms_degree_le_30 (hP _ _) (hQ _ _) (hP _ _) (hQ _ _))

theorem psi29ClearedGraded_eq_of :
    DirectSum.of (ModularForm (Gamma0GL 58)) 480 psi29ClearedForm = psi29ClearedGraded :=
  psi29ClearedGraded_homogeneous

/-- The `q`-expansion of the cleared form, in terms of `E₄`'s expansion and `q ↦ q^d`. -/
theorem psi29ClearedForm_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ) (psi29ClearedForm : ℍ → ℂ) =
      evalSparseBivarCleared psi29SparseTerms 30 30
        (level2P (qPullbackBy 29 E4QExpansion) (qPullbackBy 58 E4QExpansion))
        (level2Q (qPullbackBy 29 E4QExpansion) (qPullbackBy 58 E4QExpansion))
        (level2P E4QExpansion (qPullbackBy 2 E4QExpansion))
        (level2Q E4QExpansion (qPullbackBy 2 E4QExpansion)) := by
  have hmap := congrArg
    (qExpansionRingHom (Γ := Gamma0GL 58) (1 : ℝ) one_pos (gamma0GL_strictPeriod_one 58))
    psi29ClearedGraded_eq_of
  have hG : qExpansionRingHom (Γ := Gamma0GL 58) (1 : ℝ) one_pos
      (gamma0GL_strictPeriod_one 58) psi29ClearedGraded =
      evalSparseBivarCleared psi29SparseTerms 30 30
        (level2P (qPullbackBy 29 E4QExpansion) (qPullbackBy 58 E4QExpansion))
        (level2Q (qPullbackBy 29 E4QExpansion) (qPullbackBy 58 E4QExpansion))
        (level2P E4QExpansion (qPullbackBy 2 E4QExpansion))
        (level2Q E4QExpansion (qPullbackBy 2 E4QExpansion)) := by
    unfold psi29ClearedGraded
    rw [map_evalSparseBivarCleared]
    simp [level2P, level2Q, map_quadForm, gradedOf, ← ModularFormClass.qExpansion_eq,
      E4Level_qExpansion, E4at2, E4at29, E4at58, E4Scaled_qExpansion]
  simpa using hmap.trans hG

/-- The value of the cleared form at `τ`. -/
theorem psi29ClearedForm_apply (τ : ℍ) :
    psi29ClearedForm τ =
      evalSparseBivarCleared psi29SparseTerms 30 30
        (level2P (E4 (scaleGL 29 • τ)) (E4 (scaleGL 58 • τ)))
        (level2Q (E4 (scaleGL 29 • τ)) (E4 (scaleGL 58 • τ)))
        (level2P (E4 τ) (E4 (scaleGL 2 • τ)))
        (level2Q (E4 τ) (E4 (scaleGL 2 • τ))) := by
  have h := congrArg (gradedEvalAtOf τ) psi29ClearedGraded_eq_of
  rw [gradedEvalAtOf_of] at h
  rw [h, psi29ClearedGraded, map_evalSparseBivarCleared]
  simp only [level2P, level2Q, map_quadForm, gradedOf, gradedEvalAtOf_of, E4Level_apply,
    E4at2, E4at29, E4at58, E4Scaled_apply]

/-- Sturm bound for the cleared form: `3601` coefficients suffice. -/
theorem psi29ClearedForm_eq_zero_of_coeff
    (hcoeff : ∀ n : ℕ, n < 3601 →
      PowerSeries.coeff (R := ℂ) n
        (ModularFormClass.qExpansion (1 : ℝ) (psi29ClearedForm : ℍ → ℂ)) = 0) :
    psi29ClearedForm = 0 := by
  have h := gamma0_eq_zero_of_coeff (N := 58) (k := 480) (B := 90) (by norm_num)
    ⟨240, rfl⟩ gamma0_index_58_le
  exact h psi29ClearedForm (fun n hn => hcoeff n (by simpa using hn))

end Modular
end Number
end Ripple
