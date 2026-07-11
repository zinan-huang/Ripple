import Ripple.Number.Modular.Phi41Bridge

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm
open scoped DirectSum MatrixGroups ModularForm

/-- The level subgroup used throughout the level-41 modular-polynomial assembly. -/
abbrev Gamma0_41_GL : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 41 : Subgroup (GL (Fin 2) ℝ))

/-- `E₄(41τ)` as a weight-four form on `Γ₀(41)`.

Mathlib's `ModularForm.translate` uses the slash action, so translating by
`diag(41,1)` introduces the scalar `41^(k-1)`.  We normalize it away here. -/
noncomputable def E4_pullback41_normalized : ModularForm Gamma0_41_GL 4 :=
  ((41 : ℂ) ^ (-3 : ℤ)) • E4_pullback41 atkinLehnerInclusion41

/-- `Δ(41τ)` as a weight-twelve form on `Γ₀(41)`, normalized from the slash
translate by removing the `41^(12-1)` factor. -/
noncomputable def delta_pullback41_normalized : ModularForm Gamma0_41_GL 12 :=
  ((41 : ℂ) ^ (-11 : ℤ)) • delta_pullback41 atkinLehnerInclusion41

private lemma pullback41GL_det_pos : 0 < pullback41GL.det.val := by
  norm_num [pullback41GL, Matrix.det_fin_two]

lemma E4_pullback41_normalized_apply (τ : UpperHalfPlane) :
    E4_pullback41_normalized τ = E4 (pullback41GL • τ) := by
  change ((41 : ℂ) ^ (-3 : ℤ)) *
      (((E4 : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] pullback41GL) τ) =
    E4 (pullback41GL • τ)
  simp [ModularForm.slash_def, UpperHalfPlane.σ, UpperHalfPlane.denom,
    pullback41GL]
  field_simp

lemma delta_pullback41_normalized_apply (τ : UpperHalfPlane) :
    delta_pullback41_normalized τ = deltaLevelOneMF (pullback41GL • τ) := by
  change ((41 : ℂ) ^ (-11 : ℤ)) *
      (((deltaLevelOneMF : UpperHalfPlane → ℂ) ∣[(12 : ℤ)] pullback41GL) τ) =
    deltaLevelOneMF (pullback41GL • τ)
  simp [ModularForm.slash_def, UpperHalfPlane.σ, UpperHalfPlane.denom,
    pullback41GL]
  field_simp

set_option linter.flexible false in
lemma qParam_pullback41GL (τ : UpperHalfPlane) :
    Function.Periodic.qParam (1 : ℝ) ((pullback41GL • τ : UpperHalfPlane) : ℂ) =
      Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ 41 := by
  rw [UpperHalfPlane.coe_smul_of_det_pos pullback41GL_det_pos]
  simp [Function.Periodic.qParam, pullback41GL, UpperHalfPlane.num,
    UpperHalfPlane.denom]
  rw [← Complex.exp_nat_mul]
  ring_nf

theorem E4_pullback41_normalized_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ)
        (E4_pullback41_normalized : UpperHalfPlane → ℂ) =
      qPullback41 E4QExpansion := by
  ext n
  symm
  refine ModularFormClass.qExpansion_coeff_unique
    (c := fun n => PowerSeries.coeff (R := ℂ) n (qPullback41 E4QExpansion))
    (F := ModularForm Gamma0_41_GL 4) (f := E4_pullback41_normalized)
    (k := 4) one_pos gamma0_41_strictPeriod_one ?_ n
  intro τ
  rw [E4_pullback41_normalized_apply τ]
  refine qPullback41_hasSum_eval ?_
  simpa [qParam_pullback41GL τ, smul_eq_mul] using
    E4QExpansion_hasSum (pullback41GL • τ)

theorem delta_pullback41_normalized_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ)
        (delta_pullback41_normalized : UpperHalfPlane → ℂ) =
      qPullback41 deltaQExpansion := by
  ext n
  symm
  refine ModularFormClass.qExpansion_coeff_unique
    (c := fun n => PowerSeries.coeff (R := ℂ) n (qPullback41 deltaQExpansion))
    (F := ModularForm Gamma0_41_GL 12) (f := delta_pullback41_normalized)
    (k := 12) one_pos gamma0_41_strictPeriod_one ?_ n
  intro τ
  rw [delta_pullback41_normalized_apply τ]
  refine qPullback41_hasSum_eval ?_
  simpa [deltaQExpansion, qParam_pullback41GL τ, smul_eq_mul] using
    (ModularFormClass.hasSum_qExpansion (f := deltaLevelOneMF)
      one_pos ModularFormClass.one_mem_strictPeriods_SL2Z (pullback41GL • τ))

@[simp]
theorem E4_on_Gamma0_41_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ) (E4_on_Gamma0_41 : UpperHalfPlane → ℂ) =
      E4QExpansion := by
  rfl

@[simp]
theorem delta_on_Gamma0_41_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ)
        (delta_on_Gamma0_41 : UpperHalfPlane → ℂ) =
      deltaQExpansion := by
  rfl

private noncomputable def ofMF (k : ℤ) (f : ModularForm Gamma0_41_GL k) :
    ⨁ k : ℤ, ModularForm Gamma0_41_GL k :=
  DirectSum.of (ModularForm Gamma0_41_GL) k f

private def IsHomogeneous (d : ℤ)
    (x : ⨁ k : ℤ, ModularForm Gamma0_41_GL k) : Prop :=
  DirectSum.of (ModularForm Gamma0_41_GL) d (x d) = x

private lemma isHomogeneous_zero (d : ℤ) :
    IsHomogeneous d (0 : ⨁ k : ℤ, ModularForm Gamma0_41_GL k) := by
  simp [IsHomogeneous]

private lemma isHomogeneous_intCast (z : ℤ) :
    IsHomogeneous 0 (z : ⨁ k : ℤ, ModularForm Gamma0_41_GL k) := by
  dsimp [IsHomogeneous]
  change DirectSum.of (ModularForm Gamma0_41_GL) 0
      (z : ModularForm Gamma0_41_GL 0) =
    (z : ⨁ k : ℤ, ModularForm Gamma0_41_GL k)
  rw [DirectSum.of_intCast]

private lemma isHomogeneous_of (d : ℤ) (f : ModularForm Gamma0_41_GL d) :
    IsHomogeneous d (DirectSum.of (ModularForm Gamma0_41_GL) d f) := by
  simp [IsHomogeneous]

private lemma isHomogeneous_add {d : ℤ}
    {x y : ⨁ k : ℤ, ModularForm Gamma0_41_GL k}
    (hx : IsHomogeneous d x) (hy : IsHomogeneous d y) :
    IsHomogeneous d (x + y) := by
  dsimp [IsHomogeneous] at *
  rw [← hx, ← hy]
  simp

private lemma isHomogeneous_mul {a b : ℤ}
    {x y : ⨁ k : ℤ, ModularForm Gamma0_41_GL k}
    (hx : IsHomogeneous a x) (hy : IsHomogeneous b y) :
    IsHomogeneous (a + b) (x * y) := by
  dsimp [IsHomogeneous] at *
  rw [← hx, ← hy]
  simp [DirectSum.of_mul_of]

private lemma isHomogeneous_pow {a : ℤ}
    {x : ⨁ k : ℤ, ModularForm Gamma0_41_GL k}
    (hx : IsHomogeneous a x) (n : ℕ) :
    IsHomogeneous ((n : ℕ) * a) (x ^ n) := by
  dsimp [IsHomogeneous] at *
  rw [← hx]
  simp [DirectSum.ofPow]

private lemma isHomogeneous_cast {a b : ℤ}
    {x : ⨁ k : ℤ, ModularForm Gamma0_41_GL k}
    (h : a = b) (hx : IsHomogeneous a x) :
    IsHomogeneous b x := by
  subst h
  exact hx

private lemma three_mul_four_eq_twelve' : (3 : ℕ) * (4 : ℤ) = 12 := by
  norm_num

@[simp]
private lemma qExpansion_mcast {a b : ℤ} (h : a = b)
    (f : ModularForm Gamma0_41_GL a) :
    ModularFormClass.qExpansion (1 : ℝ)
        (ModularForm.mcast h f : UpperHalfPlane → ℂ) =
      ModularFormClass.qExpansion (1 : ℝ) (f : UpperHalfPlane → ℂ) := by
  rfl

/-- The normalized weight-12 numerator `E₄(41τ)^3`. -/
noncomputable def E4Cubed_pullback41_normalized :
    ModularForm Gamma0_41_GL 12 :=
  ModularForm.mcast three_mul_four_eq_twelve'
    (((ofMF 4 E4_pullback41_normalized) ^ 3) ((3 : ℕ) * (4 : ℤ)))

/-- The level-one numerator `E₄(τ)^3`, restricted to `Γ₀(41)`. -/
noncomputable def E4Cubed_on_Gamma0_41 :
    ModularForm Gamma0_41_GL 12 :=
  ModularForm.mcast three_mul_four_eq_twelve'
    (((ofMF 4 E4_on_Gamma0_41) ^ 3) ((3 : ℕ) * (4 : ℤ)))

theorem E4Cubed_pullback41_normalized_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ)
        (E4Cubed_pullback41_normalized : UpperHalfPlane → ℂ) =
      qPullback41 (E4QExpansion ^ 3) := by
  rw [E4Cubed_pullback41_normalized, qExpansion_mcast]
  unfold ofMF Gamma0_41_GL
  rw [ModularFormClass.qExpansion_eq,
    qExpansion_of_pow one_pos gamma0_41_strictPeriod_one
    E4_pullback41_normalized 3, ← ModularFormClass.qExpansion_eq]
  rw [E4_pullback41_normalized_qExpansion, qPullback41_pow]

theorem E4Cubed_on_Gamma0_41_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ)
        (E4Cubed_on_Gamma0_41 : UpperHalfPlane → ℂ) =
      E4QExpansion ^ 3 := by
  rw [E4Cubed_on_Gamma0_41, qExpansion_mcast]
  unfold ofMF Gamma0_41_GL
  rw [ModularFormClass.qExpansion_eq,
    qExpansion_of_pow one_pos gamma0_41_strictPeriod_one
    E4_on_Gamma0_41 3, ← ModularFormClass.qExpansion_eq]
  rw [E4_on_Gamma0_41_qExpansion]

/-- The denominator-cleared level-41 modular-polynomial expression in the
graded ring of modular forms on `Γ₀(41)`. -/
noncomputable def phi41Level41ClearedGraded :
    ⨁ k : ℤ, ModularForm Gamma0_41_GL k :=
  evalSparseBivarCleared phi41SparseTerms 42 42
    (ofMF 12 E4Cubed_pullback41_normalized)
    (ofMF 12 delta_pullback41_normalized)
    (ofMF 12 E4Cubed_on_Gamma0_41)
    (ofMF 12 delta_on_Gamma0_41)

/-- The bundled weight-1008 modular form obtained from the homogeneous
level-41 cleared expression. -/
noncomputable def phi41Level41ClearedAsModularForm :
    ModularForm Gamma0_41_GL 1008 :=
  phi41Level41ClearedGraded 1008

theorem phi41Level41ClearedGraded_qExpansion
    (hdelta : deltaQExpansion = deltaEulerSeries) :
    qExpansionRingHom (Γ := Gamma0_41_GL) (1 : ℝ)
        one_pos gamma0_41_strictPeriod_one phi41Level41ClearedGraded =
      phi41Level41ClearedEulerQExpansion := by
  unfold phi41Level41ClearedGraded phi41Level41ClearedEulerQExpansion
  rw [map_evalSparseBivarCleared]
  simp [ofMF, ← ModularFormClass.qExpansion_eq,
    E4Cubed_pullback41_normalized_qExpansion,
    delta_pullback41_normalized_qExpansion, E4Cubed_on_Gamma0_41_qExpansion,
    delta_on_Gamma0_41_qExpansion, hdelta]

private lemma evalSparseBivarCleared_term_homogeneous (t : SparseBivarTerm)
    (hxle : t.xPow ≤ 42) (hyle : t.yPow ≤ 42)
    (hwt : 12 * t.xPow + 12 * (42 - t.xPow) +
        (12 * t.yPow + 12 * (42 - t.yPow)) = 1008)
    (xNum xDen yNum yDen : ModularForm Gamma0_41_GL 12) :
    IsHomogeneous 1008
      ((t.coeff : (⨁ k : ℤ, ModularForm Gamma0_41_GL k)) *
          ofMF 12 xNum ^ t.xPow * ofMF 12 xDen ^ (42 - t.xPow) *
          ofMF 12 yNum ^ t.yPow * ofMF 12 yDen ^ (42 - t.yPow)) := by
  have hc := isHomogeneous_intCast t.coeff
  have hxNum := isHomogeneous_pow (isHomogeneous_of 12 xNum) t.xPow
  have hxDen := isHomogeneous_pow (isHomogeneous_of 12 xDen) (42 - t.xPow)
  have hyNum := isHomogeneous_pow (isHomogeneous_of 12 yNum) t.yPow
  have hyDen := isHomogeneous_pow (isHomogeneous_of 12 yDen) (42 - t.yPow)
  have h1 := isHomogeneous_mul hc hxNum
  have h2 := isHomogeneous_mul h1 hxDen
  have h3 := isHomogeneous_mul h2 hyNum
  have h4 := isHomogeneous_mul h3 hyDen
  refine isHomogeneous_cast ?_ h4
  have hwtZ : (12 * t.xPow + 12 * (42 - t.xPow) +
      (12 * t.yPow + 12 * (42 - t.yPow)) : ℤ) = 1008 := by
    exact_mod_cast hwt
  omega

private lemma evalSparseBivarCleared_homogeneous
    (terms : List SparseBivarTerm)
    (hdeg : ∀ t ∈ terms, t.xPow ≤ 42 ∧ t.yPow ≤ 42)
    (hwt : ∀ t ∈ terms,
      12 * t.xPow + 12 * (42 - t.xPow) +
          (12 * t.yPow + 12 * (42 - t.yPow)) = 1008)
    (xNum xDen yNum yDen : ModularForm Gamma0_41_GL 12) :
    IsHomogeneous 1008
      (evalSparseBivarCleared terms 42 42
        (ofMF 12 xNum) (ofMF 12 xDen) (ofMF 12 yNum) (ofMF 12 yDen)) := by
  induction terms with
  | nil =>
      simpa [evalSparseBivarCleared] using isHomogeneous_zero (1008 : ℤ)
  | cons t ts ih =>
      have htdeg := hdeg t (by simp)
      have hhead := evalSparseBivarCleared_term_homogeneous t
        htdeg.1 htdeg.2 (hwt t (by simp)) xNum xDen yNum yDen
      have htail : IsHomogeneous 1008
          (evalSparseBivarCleared ts 42 42
            (ofMF 12 xNum) (ofMF 12 xDen) (ofMF 12 yNum) (ofMF 12 yDen)) := by
        refine ih ?_ ?_
        · intro u hu
          exact hdeg u (by simp [hu])
        · intro u hu
          exact hwt u (by simp [hu])
      simpa [evalSparseBivarCleared] using isHomogeneous_add hhead htail

private theorem phi41Level41ClearedGraded_homogeneous :
    IsHomogeneous 1008 phi41Level41ClearedGraded := by
  unfold phi41Level41ClearedGraded
  refine evalSparseBivarCleared_homogeneous phi41SparseTerms
    phi41SparseTerms_degree_le_42 ?_
    E4Cubed_pullback41_normalized delta_pullback41_normalized
    E4Cubed_on_Gamma0_41 delta_on_Gamma0_41
  intro t ht
  simpa [phi41Level41ClearedWeight] using
    phi41SparseTerms_cleared_term_weight t ht

theorem phi41Level41ClearedAsModularForm_qExpansion
    (hdelta : deltaQExpansion = deltaEulerSeries) :
    ModularFormClass.qExpansion (1 : ℝ)
        (phi41Level41ClearedAsModularForm : UpperHalfPlane → ℂ) =
      phi41Level41ClearedEulerQExpansion := by
  have hhom :
      DirectSum.of (ModularForm Gamma0_41_GL) 1008
          phi41Level41ClearedAsModularForm =
        phi41Level41ClearedGraded := by
    simpa [phi41Level41ClearedAsModularForm]
      using phi41Level41ClearedGraded_homogeneous
  have hmap := congrArg
    (qExpansionRingHom (Γ := Gamma0_41_GL) (1 : ℝ)
      one_pos gamma0_41_strictPeriod_one) hhom
  simpa using hmap.trans (phi41Level41ClearedGraded_qExpansion hdelta)

end Modular
end Number
end Ripple
