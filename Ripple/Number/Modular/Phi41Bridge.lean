/-
  Phi41 modular form bridge — construction stage 1.

  Goal: build `phi41Level41ClearedAsModularForm : ModularForm Γ₀(41) 1008`
  whose q-expansion equals `phi41Level41ClearedEulerQExpansion`, closing
  Input 1 of `complex_sturm_bound_valence_formula_phi41Level41Cleared_of_inputs`.

  This file provides the building blocks:
    * `restrictModularForm` — restrict `ModularForm Γ k` to a subgroup.
    * `E4_on_Gamma0_41` — E_4 viewed as a ModularForm on Γ₀(41) (via restriction).
    * `delta_on_Gamma0_41` — Δ viewed as a ModularForm on Γ₀(41).

  The pullback `f(z/41)` and the polynomial assembly remain to be built.
-/
import Ripple.Number.Modular.ModularPolynomialQExpansion

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm UpperHalfPlane

open scoped MatrixGroups

/-- Restrict a `ModularForm` along a subgroup inclusion `Γ' ≤ Γ`. -/
noncomputable def restrictModularForm
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) {k : ℤ} (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f.toFun
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[simp]
lemma restrictModularForm_coe
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) {k : ℤ} (f : ModularForm Γ k) :
    (restrictModularForm h f : ℍ → ℂ) = (f : ℍ → ℂ) :=
  rfl

/-- `Γ₀(41) ≤ Γ(1)` at the SL(2,ℤ) level, then via the Subgroup → GL coercion. -/
lemma gamma0_41_le_gamma1 :
    (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)) ≤
      𝒮ℒ :=
  Subgroup.map_le_range _ _

/-- `E_4` viewed as a modular form on `Γ₀(41)` of weight 4 via restriction. -/
noncomputable def E4_on_Gamma0_41 :
    ModularForm (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)) 4 :=
  restrictModularForm gamma0_41_le_gamma1 E4

@[simp]
lemma E4_on_Gamma0_41_apply (z : ℍ) :
    (E4_on_Gamma0_41 : ℍ → ℂ) z = (E4 : ℍ → ℂ) z :=
  rfl

/-- `Δ` viewed as a modular form on `Γ₀(41)` of weight 12 via restriction. -/
noncomputable def delta_on_Gamma0_41 :
    ModularForm (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictModularForm gamma0_41_le_gamma1 deltaLevelOneMF

lemma delta_on_Gamma0_41_apply (z : ℍ) :
    (delta_on_Gamma0_41 : ℍ → ℂ) z = ModularForm.discriminant z := by
  change deltaLevelOneMF.toFun z = ModularForm.discriminant z
  rfl

/-! ## Pullback by `z ↦ N·z` for `N > 0`

For `f : ModularForm Γ(1) k`, the function `g(z) := f(N·z)` is a modular
form on `Γ₀(N)`.  We build it via Mathlib's `ModularForm.translate` with
the matrix `g_N = [[N, 0], [0, 1]] ∈ GL(2, ℝ)`:

  translate f g_N : ModularForm (g_N⁻¹ Γ(1) g_N) k

A direct calculation shows `Γ₀(N) ≤ g_N⁻¹ Γ(1) g_N`: for
γ' = [[a,b],[c,d]] ∈ Γ₀(N), the conjugate g_N γ' g_N⁻¹ = [[a, Nb], [c/N, d]]
is in SL(2,ℤ) (using `N | c` for the integrality of `c/N`).

Restricting along this inclusion gives a form on Γ₀(N).  The
function-level identification `g(z) = f(Nz)` then follows from the
Möbius action of g_N on `z`. -/

private def pullback41Pos : {x : ℝ // 0 < x} := ⟨(41 : ℝ), by norm_num⟩

/-- The function `z ↦ f (41 z)` for `f` a level-1 modular form. -/
noncomputable def pullback41Function {k : ℤ}
    (f : ModularForm
      𝒮ℒ k) :
    ℍ → ℂ :=
  fun z => f (pullback41Pos • z)

/-- The diagonal matrix `[[41, 0], [0, 1]] ∈ GL(2, ℝ)` used as the
Atkin-Lehner pullback matrix.  Defined with an explicit inverse
`[[1/41, 0], [0, 1]]` to keep matrix entries reducible. -/
noncomputable def pullback41GL : GL (Fin 2) ℝ :=
  ⟨!![(41 : ℝ), 0; 0, 1], !![(1/41 : ℝ), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

open ConjAct Pointwise in
/-- The pullback of a level-1 modular form by the matrix
`pullback41GL = [[41, 0], [0, 1]]` is a modular form on the conjugate
group `pullback41GL⁻¹ Γ(1) pullback41GL`. -/
noncomputable def pullback41Translate {k : ℤ}
    (f : ModularForm
      𝒮ℒ k) :
    ModularForm
      (toConjAct pullback41GL⁻¹ •
        𝒮ℒ) k :=
  ModularForm.translate f pullback41GL

open ConjAct Pointwise in
/-- `E_4` pulled back via `[[41, 0], [0, 1]]`, viewed on the Atkin-Lehner
conjugate of `Γ(1)`. -/
noncomputable def E4_pullback41Conjugated :
    ModularForm
      (toConjAct pullback41GL⁻¹ •
        𝒮ℒ) 4 :=
  pullback41Translate E4

open ConjAct Pointwise in
/-- `Δ` pulled back via `[[41, 0], [0, 1]]`, viewed on the Atkin-Lehner
conjugate of `Γ(1)`. -/
noncomputable def delta_pullback41Conjugated :
    ModularForm
      (toConjAct pullback41GL⁻¹ •
        𝒮ℒ) 12 :=
  pullback41Translate deltaLevelOneMF

open ConjAct Pointwise in
/-- The Atkin-Lehner inclusion `Γ₀(41) ≤ pullback41GL⁻¹ Γ(1) pullback41GL`,
exposed as a `Prop` so downstream consumers can be defined now and the
inclusion can be filled in via Atkin-Lehner once the matrix algebra is
formalised. -/
def AtkinLehnerInclusion41 : Prop :=
  (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)) ≤
    toConjAct pullback41GL⁻¹ •
      𝒮ℒ

/-- Conditional `E_4(41 z)` as `ModularForm Γ₀(41) 4`, parameterised by
the Atkin-Lehner inclusion hypothesis. -/
noncomputable def E4_pullback41
    (h : AtkinLehnerInclusion41) :
    ModularForm (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)) 4 :=
  restrictModularForm h E4_pullback41Conjugated

/-- Conditional `Δ(41 z)` as `ModularForm Γ₀(41) 12`, parameterised by
the Atkin-Lehner inclusion hypothesis. -/
noncomputable def delta_pullback41
    (h : AtkinLehnerInclusion41) :
    ModularForm (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictModularForm h delta_pullback41Conjugated

open ConjAct Pointwise

set_option linter.flexible false in
set_option maxHeartbeats 800000 in
-- This proof unfolds the finite SL/GL coercions and the two diagonal
-- matrix products entrywise; the local heartbeat bump is confined here.
/-- The Atkin-Lehner inclusion `Γ₀(41) ≤ pullback41GL⁻¹ Γ(1) pullback41GL`. -/
theorem atkinLehnerInclusion41 : AtkinLehnerInclusion41 := by
  intro γ hγ
  obtain ⟨γ_int, hγ_int_mem, hγ_int_eq⟩ := Subgroup.mem_map.mp hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ_int_mem
  have h41dvd : (41 : ℤ) ∣ γ_int.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 41).mp (by exact_mod_cast hγ_int_mem)
  obtain ⟨q, hq⟩ := h41dvd
  have hdet_γ_int : γ_int.val.det = 1 := γ_int.property
  have hdet_expand :
      γ_int.val 0 0 * γ_int.val 1 1 -
        γ_int.val 0 1 * γ_int.val 1 0 = 1 := by
    have := hdet_γ_int
    rw [Matrix.det_fin_two] at this
    linarith
  let δ_matrix : Matrix (Fin 2) (Fin 2) ℤ :=
    !![γ_int.val 0 0, 41 * γ_int.val 0 1; q, γ_int.val 1 1]
  have hδ_det : δ_matrix.det = 1 := by
    have hdet_eq : δ_matrix.det =
        γ_int.val 0 0 * γ_int.val 1 1 - 41 * γ_int.val 0 1 * q := by
      simp [δ_matrix, Matrix.det_fin_two_of]
    rw [hdet_eq]
    have hc_expand : γ_int.val 0 1 * γ_int.val 1 0 = 41 * γ_int.val 0 1 * q := by
      rw [hq]
      ring
    linarith [hdet_expand, hc_expand]
  let δ_int : SL(2, ℤ) := ⟨δ_matrix, hδ_det⟩
  refine (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨(Matrix.SpecialLinearGroup.mapGL ℝ) δ_int,
     MonoidHom.mem_range.mpr ⟨δ_int, rfl⟩, ?_⟩
  rw [ConjAct.toConjAct_inv_smul, ← hγ_int_eq]
  apply Units.ext
  ext i j
  have hcr : (γ_int.val 1 0 : ℝ) = 41 * (q : ℝ) := by
    exact_mod_cast hq
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, pullback41GL, Units.inv_mk,
      Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL, δ_int,
      δ_matrix]
    rw [mul_assoc, mul_comm ((γ_int.val 0 0 : ℤ) : ℝ) (41 : ℝ)]
    rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (41 : ℝ) ≠ 0), one_mul]
  · simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, pullback41GL, Units.inv_mk,
      Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL, δ_int,
      δ_matrix]
  · simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, pullback41GL, Units.inv_mk,
      Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL, δ_int,
      δ_matrix]
    nlinarith [hcr]
  · simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, pullback41GL, Units.inv_mk,
      Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL, δ_int,
      δ_matrix]

end Modular
end Number
end Ripple
