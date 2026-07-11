import Ripple.Number.Modular.LevelOneSturmGeneric
import Ripple.Number.Modular.Phi41ModularFormAssembly
import Ripple.Number.Modular.CosetIndex
import Mathlib.NumberTheory.ModularForms.NormTrace

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm ModularFormClass
open UpperHalfPlane Filter Asymptotics
open scoped MatrixGroups ModularForm BigOperators
open Pointwise ConjAct

/-- The GL-subgroup underlying `Γ(1)` is Mathlib's `𝒮ℒ`. -/
lemma Gamma_one_GL_eq_SL :
    ((Γ(1) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  change (Gamma 1).map (Matrix.SpecialLinearGroup.mapGL ℝ) = 𝒮ℒ
  rw [Gamma_one_top]
  exact (MonoidHom.range_eq_map
    (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)).symm

/-- View a form on `𝒮ℒ` as a level-one form (identity; `𝒮ℒ` is the level-one
group in Mathlib `v4.30.0`). -/
noncomputable def asLevelOne {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ k :=
  f

@[simp]
lemma asLevelOne_coe {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ⇑(asLevelOne f) = ⇑f :=
  rfl

/-- The norm of a level-41 form, regarded as a level-one modular form. -/
noncomputable def gamma0_41_normLevelOne
    (f : ModularForm Gamma0_41_GL 1008) :
    ModularForm 𝒮ℒ
      ((1008 * Nat.card (𝒮ℒ ⧸ Gamma0_41_GL.subgroupOf 𝒮ℒ) : ℕ) : ℤ) :=
  ModularForm.mcast (by norm_num)
    (asLevelOne (ModularForm.norm 𝒮ℒ f))

@[simp]
lemma gamma0_41_normLevelOne_coe
    (f : ModularForm Gamma0_41_GL 1008) :
    ⇑(gamma0_41_normLevelOne f) =
      ⇑(ModularForm.norm 𝒮ℒ f) :=
  rfl

local notation "Gamma0_41NormQuot" =>
  𝒮ℒ ⧸ Gamma0_41_GL.subgroupOf 𝒮ℒ

theorem gamma0_41_GL_relIndex_SL :
    Gamma0_41_GL.relIndex 𝒮ℒ = 42 := by
  rw [← Gamma_one_GL_eq_SL]
  change ((CongruenceSubgroup.Gamma0 41).map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
      ((CongruenceSubgroup.Gamma 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) = 42
  rw [Subgroup.relIndex_map_map_of_injective]
  · rw [CongruenceSubgroup.Gamma_one_top, Subgroup.relIndex_top_right]
    exact Ripple.CosetIndex.gamma0_index_41
  · exact Matrix.SpecialLinearGroup.mapGL_injective (R := ℤ) (S := ℝ) (n := Fin 2)

theorem gamma0_41_normQuot_card :
    Nat.card Gamma0_41NormQuot = 42 := by
  rw [← gamma0_41_GL_relIndex_SL]
  rw [Subgroup.relIndex, Subgroup.index_eq_card]

private lemma gamma0_41_norm_quotientFunc_bounded_atImInfty
    (f : ModularForm Gamma0_41_GL 1008) (q : Gamma0_41NormQuot) :
    BoundedAtFilter UpperHalfPlane.atImInfty (SlashInvariantForm.quotientFunc f q) := by
  classical
  induction q using Quotient.inductionOn with
  | h r =>
      change BoundedAtFilter UpperHalfPlane.atImInfty ((f : ℍ → ℂ) ∣[(1008 : ℤ)] (r.val⁻¹))
      have hcusp : IsCusp OnePoint.infty
          (ConjAct.toConjAct r.val • Gamma0_41_GL) := by
        simpa using (Fact.out : IsCusp OnePoint.infty 𝒮ℒ).of_isFiniteRelIndex_conj
          (𝒢 := Gamma0_41_GL) (ℋ := 𝒮ℒ) r.property
      have hbd := (ModularForm.translate f r.val⁻¹).bdd_at_cusps' hcusp
        (1 : GL (Fin 2) ℝ) (by simp)
      simpa [OnePoint.isBoundedAt_infty_iff] using hbd

theorem gamma0_41_norm_decay_of_decay
    (f : ModularForm Gamma0_41_GL 1008) {n : ℕ}
    (hfdec : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * n * τ.im)) :
    (⇑(ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * n * τ.im) := by
  classical
  letI := Fintype.ofFinite Gamma0_41NormQuot
  let e : Gamma0_41NormQuot := QuotientGroup.mk (1 : 𝒮ℒ)
  let H : ℍ → ℂ :=
    ∏ q ∈ (Finset.univ \ {e}), SlashInvariantForm.quotientFunc f q
  have hHbdd : BoundedAtFilter UpperHalfPlane.atImInfty H := by
    dsimp [H]
    exact BoundedAtFilter.prod _ (fun q _hq =>
      gamma0_41_norm_quotientFunc_bounded_atImInfty f q)
  have hfac : (⇑(ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) = (f : ℍ → ℂ) * H := by
    funext z
    rw [Pi.mul_apply]
    change (SlashInvariantForm.norm 𝒮ℒ f) z = _
    rw [SlashInvariantForm.norm]
    simp only [SlashInvariantForm.coe_mk]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ e)]
    simp [H, e, Finset.prod_apply, SlashInvariantForm.quotientFunc_mk]
  rw [hfac]
  refine (hfdec.mul hHbdd).congr_right ?_
  intro τ
  simp

private theorem levelGamma0_41_zero_of_norm_zero
    (f : ModularForm Gamma0_41_GL 1008)
    (hnorm_zero : ModularForm.norm 𝒮ℒ f = 0) :
    f = 0 := by
  have hf_fun : ⇑f = 0 :=
    (ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ) (f := f)).mp hnorm_zero
  ext z
  exact congrFun hf_fun z

theorem levelGamma0_41_sturm_weight_1008
    (f : ModularForm Gamma0_41_GL 1008)
    (hcoeff : ∀ n : ℕ, n < phi41Level41SturmBound →
      PowerSeries.coeff (R := ℂ) n
        (ModularFormClass.qExpansion (1 : ℝ) f.toFun) = 0) :
    f = 0 := by
  let K : ℕ := 1008 * Nat.card Gamma0_41NormQuot
  have hK_val : K = 42336 := by
    dsimp [K]
    rw [gamma0_41_normQuot_card]
  have horder : K / 12 + 1 = phi41Level41SturmBound := by
    rw [hK_val]
    rfl
  have horderR : ((K / 12 + 1 : ℕ) : ℝ) = phi41Level41SturmBound := by
    exact_mod_cast horder
  have hfdec₀ : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * phi41Level41SturmBound * τ.im / 1) :=
    exp_decay_atImInfty_of_qExpansion_coeff_zero f one_pos
      gamma0_41_strictPeriod_one hcoeff
  have hfdec : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * phi41Level41SturmBound * τ.im) := by
    refine hfdec₀.congr_right fun τ => ?_
    congr 1
    ring
  have hnormdec₀ :
      (⇑(ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
        fun τ : ℍ => Real.exp (-2 * Real.pi * phi41Level41SturmBound * τ.im) :=
    gamma0_41_norm_decay_of_decay f hfdec
  have hnormdec :
      (gamma0_41_normLevelOne f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
        fun τ : ℍ => Real.exp (-(2 * ((K / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im) := by
    change (⇑(ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * ((K / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im)
    refine hnormdec₀.congr_right fun τ => ?_
    rw [horderR]
    congr 1
    ring
  have hK_pos : 4 ≤ K := by rw [hK_val]; norm_num
  have hK_even : Even K := by rw [hK_val]; norm_num
  have hnorm_zero :
      gamma0_41_normLevelOne f = 0 :=
    levelOne_modularForm_eq_zero_of_exp_decay hK_pos hK_even
      (gamma0_41_normLevelOne f) hnormdec
  have hnorm_zero' : ModularForm.norm 𝒮ℒ f = 0 := by
    ext z
    have hz := congrArg (fun g : ModularForm 𝒮ℒ (K : ℤ) => g z)
      hnorm_zero
    change (gamma0_41_normLevelOne f) z = 0 at hz
    change (ModularForm.norm 𝒮ℒ f) z = 0
    simpa [gamma0_41_normLevelOne, asLevelOne, ModularForm.mcast, restrictModularForm,
      ModularForm.norm, SlashInvariantForm.norm] using hz
  exact levelGamma0_41_zero_of_norm_zero f hnorm_zero'

theorem qExp_norm_coeff_zero_of_qExp_coeff_zero
    (f : ModularForm Gamma0_41_GL 1008)
    (hcoeff : ∀ n : ℕ, n < phi41Level41SturmBound →
      PowerSeries.coeff (R := ℂ) n
        (ModularFormClass.qExpansion (1 : ℝ) f.toFun) = 0) :
    ∀ n : ℕ,
      n ≤ (1008 * Nat.card Gamma0_41NormQuot) / 12 →
        PowerSeries.coeff (R := ℂ) n
          (ModularFormClass.qExpansion (1 : ℝ)
            ⇑(gamma0_41_normLevelOne f)) = 0 := by
  intro n _hn
  have hf_zero : f = 0 := levelGamma0_41_sturm_weight_1008 f hcoeff
  have hf_fun : ⇑f = 0 := by
    ext z
    rw [hf_zero]
    rfl
  have hnorm_zero' : ModularForm.norm 𝒮ℒ f = 0 :=
    (ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ) (f := f)).mpr hf_fun
  have hnorm_zero : gamma0_41_normLevelOne f = 0 := by
    ext z
    change (ModularForm.norm 𝒮ℒ f) z = 0
    rw [hnorm_zero']
    rfl
  rw [hnorm_zero]
  change PowerSeries.coeff (R := ℂ) n
      (ModularFormClass.qExpansion (1 : ℝ) (0 : ℍ → ℂ)) = 0
  rw [ModularFormClass.qExpansion_eq, qExpansion_zero]
  simp

/-- Norm reduction to the generic level-one Sturm theorem.

This is the clean norm-trick endpoint: after proving the required level-one
q-expansion vanishing for the norm, nonvanishing of the norm is equivalent to
nonvanishing of the original level-41 form. -/
theorem levelGamma0_41_zero_of_norm_low_coeffs_vanish
    (f : ModularForm Gamma0_41_GL 1008)
    (hcoeff :
      ∀ n : ℕ,
        n ≤ (1008 * Nat.card (𝒮ℒ ⧸ Gamma0_41_GL.subgroupOf 𝒮ℒ)) / 12 →
          PowerSeries.coeff (R := ℂ) n
            (ModularFormClass.qExpansion (1 : ℝ)
              ⇑(gamma0_41_normLevelOne f)) = 0) :
    f = 0 := by
  let K : ℕ := 1008 * Nat.card (𝒮ℒ ⧸ Gamma0_41_GL.subgroupOf 𝒮ℒ)
  have hK_pos : 4 ≤ K := by
    dsimp [K]
    have hcard_pos : 0 < Nat.card (𝒮ℒ ⧸ Gamma0_41_GL.subgroupOf 𝒮ℒ) :=
      Nat.card_pos
    omega
  have hK_even : Even K := by
    dsimp [K]
    refine ⟨504 * Nat.card (𝒮ℒ ⧸ Gamma0_41_GL.subgroupOf 𝒮ℒ), ?_⟩
    ring
  have hnorm_zero :
      gamma0_41_normLevelOne f = 0 :=
    levelOne_modularForm_eq_zero_of_low_coeffs_vanish hK_pos hK_even
      (gamma0_41_normLevelOne f) (by
        intro n hn
        exact hcoeff n (by
          dsimp [K] at hn
          exact hn))
  have hnorm_fun :
      ⇑(ModularForm.norm 𝒮ℒ f) = 0 := by
    ext z
    have hz := congrArg (fun g : ModularForm 𝒮ℒ (K : ℤ) => g z)
      hnorm_zero
    change (gamma0_41_normLevelOne f) z = 0 at hz
    change (ModularForm.norm 𝒮ℒ f) z = 0
    simpa [gamma0_41_normLevelOne, asLevelOne, ModularForm.mcast, restrictModularForm,
      ModularForm.norm, SlashInvariantForm.norm] using hz
  have hnorm_zero' : ModularForm.norm 𝒮ℒ f = 0 := by
    ext z
    exact congrFun hnorm_fun z
  have hf_fun : ⇑f = 0 :=
    (ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ) (f := f)).mp hnorm_zero'
  ext z
  exact congrFun hf_fun z

end Modular
end Number
end Ripple
