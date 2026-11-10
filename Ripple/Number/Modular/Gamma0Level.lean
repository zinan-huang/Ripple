import Ripple.Number.Modular.Gamma0_41_SturmBound

/-!
# Modular forms on `Γ₀(N)`: pullbacks, `q`-expansions and a Sturm bound

Level-`N` versions of the level-41 tools (`Gamma0_41_ModularForms`, `Phi41ModularFormAssembly`,
`Gamma0_41_SturmBound`):

* `scaleGL d = diag(d, 1)` and the inclusion `Γ₀(N) ≤ scaleGL d⁻¹ · SL(2,ℤ) · scaleGL d` for
  `d ∣ N`, so that `τ ↦ E₄(dτ)` is a weight-4 form on `Γ₀(N)` (`E4Scaled`);
* the substitution `q ↦ q^d` on formal power series (`qPullbackBy`) and the `q`-expansion of
  `E4Scaled`;
* a Sturm bound for `Γ₀(N)` from any upper bound on the index (`gamma0_eq_zero_of_coeff`), by the
  norm down to level one;
* the graded-ring helpers used to assemble a cleared modular polynomial into one modular form.
-/

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter Asymptotics
open scoped MatrixGroups ModularForm DirectSum
open Pointwise ConjAct

/-- `Γ₀(N)` as a subgroup of `GL(2, ℝ)`. -/
abbrev Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

lemma gamma0GL_le_SL (N : ℕ) : Gamma0GL N ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

theorem gamma0GL_strictPeriod_one (N : ℕ) : (1 : ℝ) ∈ (Gamma0GL N).strictPeriods := by
  simp

/-! ## The matrix `diag(d, 1)` -/

/-- `diag(d, 1) ∈ GL(2, ℝ)`, with explicit inverse `diag(1/d, 1)`. -/
noncomputable def scaleGL (d : ℕ) [NeZero d] : GL (Fin 2) ℝ :=
  ⟨!![(d : ℝ), 0; 0, 1], !![(1 / d : ℝ), 0; 0, 1],
    by
      have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd],
    by
      have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd]⟩

lemma scaleGL_det_pos (d : ℕ) [NeZero d] : 0 < (scaleGL d).det.val := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  simpa [scaleGL, Matrix.det_fin_two] using hd

lemma coe_scaleGL_smul (d : ℕ) [NeZero d] (τ : ℍ) :
    ((scaleGL d • τ : ℍ) : ℂ) = (d : ℂ) * τ := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (scaleGL_det_pos d)]
  simp [scaleGL, UpperHalfPlane.num, UpperHalfPlane.denom]

set_option linter.flexible false in
lemma qParam_scaleGL (d : ℕ) [NeZero d] (τ : ℍ) :
    Function.Periodic.qParam (1 : ℝ) ((scaleGL d • τ : ℍ) : ℂ) =
      Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ d := by
  rw [coe_scaleGL_smul]
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

set_option linter.flexible false in
set_option maxHeartbeats 800000 in
-- Entrywise computation of `diag(d,1)⁻¹ δ diag(d,1)` over the SL/GL coercions.
/-- For `d ∣ N`: `Γ₀(N) ≤ diag(d,1)⁻¹ · SL(2,ℤ) · diag(d,1)`. For `γ = [[a, b], [c, e]]` with
`d ∣ c`, the conjugate is `δ = [[a, d b], [c/d, e]] ∈ SL(2, ℤ)`. -/
theorem gamma0GL_le_scale_conj {N d : ℕ} [NeZero d] (hd : d ∣ N) :
    Gamma0GL N ≤ toConjAct (scaleGL d)⁻¹ • 𝒮ℒ := by
  intro γ hγ
  obtain ⟨γ_int, hγ_int_mem, hγ_int_eq⟩ := Subgroup.mem_map.mp hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ_int_mem
  have hNdvd : (N : ℤ) ∣ γ_int.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (by exact_mod_cast hγ_int_mem)
  have hddvd : (d : ℤ) ∣ γ_int.val 1 0 :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hd) hNdvd
  obtain ⟨q, hq⟩ := hddvd
  have hdet_γ_int : γ_int.val.det = 1 := γ_int.property
  have hdet_expand :
      γ_int.val 0 0 * γ_int.val 1 1 - γ_int.val 0 1 * γ_int.val 1 0 = 1 := by
    have := hdet_γ_int
    rw [Matrix.det_fin_two] at this
    linarith
  let δ_matrix : Matrix (Fin 2) (Fin 2) ℤ :=
    !![γ_int.val 0 0, (d : ℤ) * γ_int.val 0 1; q, γ_int.val 1 1]
  have hδ_det : δ_matrix.det = 1 := by
    have hdet_eq : δ_matrix.det =
        γ_int.val 0 0 * γ_int.val 1 1 - (d : ℤ) * γ_int.val 0 1 * q := by
      simp [δ_matrix, Matrix.det_fin_two_of]
    rw [hdet_eq]
    have hc_expand : γ_int.val 0 1 * γ_int.val 1 0 = (d : ℤ) * γ_int.val 0 1 * q := by
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
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hcr : (γ_int.val 1 0 : ℝ) = (d : ℝ) * (q : ℝ) := by
    exact_mod_cast hq
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, scaleGL, Units.inv_mk,
      Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.toGL, δ_int,
      δ_matrix, hd0] <;>
    (try field_simp) <;>
    linarith [hcr]

/-! ## `E₄(dτ)` on `Γ₀(N)` -/

/-- `E₄` restricted to `Γ₀(N)`. -/
noncomputable def E4Level (N : ℕ) : ModularForm (Gamma0GL N) 4 :=
  restrictModularForm (gamma0GL_le_SL N) E4

@[simp]
lemma E4Level_apply (N : ℕ) (τ : ℍ) : E4Level N τ = E4 τ :=
  rfl

theorem E4Level_qExpansion (N : ℕ) :
    ModularFormClass.qExpansion (1 : ℝ) (E4Level N : ℍ → ℂ) = E4QExpansion :=
  rfl

/-- `τ ↦ E₄(dτ)` as a weight-4 form on `Γ₀(N)` for `d ∣ N`; the slash translate by `diag(d, 1)`
carries the factor `d³`, removed here. -/
noncomputable def E4Scaled {N d : ℕ} [NeZero d] (hd : d ∣ N) : ModularForm (Gamma0GL N) 4 :=
  ((d : ℂ) ^ (-3 : ℤ)) •
    restrictModularForm (gamma0GL_le_scale_conj hd) (ModularForm.translate E4 (scaleGL d))

set_option linter.flexible false in
lemma E4Scaled_apply {N d : ℕ} [NeZero d] (hd : d ∣ N) (τ : ℍ) :
    E4Scaled hd τ = E4 (scaleGL d • τ) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdpos : 0 < d := NeZero.pos d
  change ((d : ℂ) ^ (-3 : ℤ)) * (((E4 : ℍ → ℂ) ∣[(4 : ℤ)] scaleGL d) τ) = E4 (scaleGL d • τ)
  simp [ModularForm.slash_def, UpperHalfPlane.σ, UpperHalfPlane.denom, scaleGL, hdpos]
  field_simp

/-! ## Substitution `q ↦ q^d` -/

/-- Substitute `q = Q^d` into a formal `q`-expansion. -/
noncomputable def qPullbackBy (d : ℕ) (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.subst ((PowerSeries.X : PowerSeries ℂ) ^ d) f

theorem qPullbackBy_add (d : ℕ) [NeZero d] (f g : PowerSeries ℂ) :
    qPullbackBy d (f + g) = qPullbackBy d f + qPullbackBy d g :=
  PowerSeries.subst_add (PowerSeries.HasSubst.X_pow (R := ℂ) (NeZero.ne d)) f g

theorem qPullbackBy_mul (d : ℕ) [NeZero d] (f g : PowerSeries ℂ) :
    qPullbackBy d (f * g) = qPullbackBy d f * qPullbackBy d g :=
  PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow (R := ℂ) (NeZero.ne d)) f g

theorem qPullbackBy_pow (d : ℕ) [NeZero d] (f : PowerSeries ℂ) (n : ℕ) :
    qPullbackBy d (f ^ n) = qPullbackBy d f ^ n :=
  PowerSeries.subst_pow (PowerSeries.HasSubst.X_pow (R := ℂ) (NeZero.ne d)) f n

theorem coeff_qPullbackBy (d : ℕ) [NeZero d] (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (qPullbackBy d f) =
      if d ∣ n then PowerSeries.coeff (R := ℂ) (n / d) f else 0 := by
  simp [qPullbackBy, PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ) (NeZero.ne d) f n]

/-- Evaluating a pullback `q ↦ q^d` is evaluating the original series at `q^d`. -/
theorem qPullbackBy_hasSum_eval (d : ℕ) [NeZero d]
    {f : PowerSeries ℂ} {q value : ℂ}
    (hsum : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f * (q ^ d) ^ n) value) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n (qPullbackBy d f) * q ^ n) value := by
  classical
  have hdpos : 0 < d := NeZero.pos d
  let g : ℕ → ℕ := fun n => d * n
  have hg : Function.Injective g := by
    intro a b h
    exact Nat.mul_left_cancel hdpos h
  have hbase : HasSum (Function.extend g
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f * (q ^ d) ^ n)
      (fun _ : ℕ => (0 : ℂ))) value :=
    (hasSum_extend_zero hg).2 hsum
  convert hbase using 1
  funext m
  by_cases hm : d ∣ m
  · have hgimg : ∃ a, g a = m := by
      refine ⟨m / d, ?_⟩
      dsimp [g]
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hm
    rw [Function.extend_def]
    simp only [hgimg, dif_pos]
    have hchoose : g (Classical.choose hgimg) = m := Classical.choose_spec hgimg
    have hchoose_eq : Classical.choose hgimg = m / d := by
      apply hg
      rw [hchoose]
      dsimp [g]
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel hm).symm
    rw [coeff_qPullbackBy, if_pos hm, hchoose_eq]
    have hpow : q ^ m = (q ^ d) ^ (m / d) := by
      rw [← pow_mul, Nat.mul_comm, Nat.div_mul_cancel hm]
    rw [hpow]
  · have hnot : ¬ ∃ a, g a = m := by
      rintro ⟨a, ha⟩
      apply hm
      exact ⟨a, ha.symm⟩
    rw [Function.extend_apply' _ _ _ hnot, coeff_qPullbackBy, if_neg hm]
    simp

theorem E4Scaled_qExpansion {N d : ℕ} [NeZero d] (hd : d ∣ N) :
    ModularFormClass.qExpansion (1 : ℝ) (E4Scaled hd : ℍ → ℂ) =
      qPullbackBy d E4QExpansion := by
  ext n
  symm
  refine ModularFormClass.qExpansion_coeff_unique
    (c := fun n => PowerSeries.coeff (R := ℂ) n (qPullbackBy d E4QExpansion))
    (F := ModularForm (Gamma0GL N) 4) (f := E4Scaled hd)
    (k := 4) one_pos (gamma0GL_strictPeriod_one N) ?_ n
  intro τ
  rw [E4Scaled_apply hd τ]
  refine qPullbackBy_hasSum_eval d ?_
  simpa [qParam_scaleGL d τ, smul_eq_mul] using E4QExpansion_hasSum (scaleGL d • τ)

/-! ## Sturm bound on `Γ₀(N)` -/

theorem gamma0GL_normQuot_card (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) = (Gamma0 N).index := by
  have h : (Gamma0GL N).relIndex 𝒮ℒ = (Gamma0 N).index := by
    rw [← Gamma_one_GL_eq_SL]
    change ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
        ((CongruenceSubgroup.Gamma 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) = _
    rw [Subgroup.relIndex_map_map_of_injective]
    · rw [CongruenceSubgroup.Gamma_one_top, Subgroup.relIndex_top_right]
    · exact Matrix.SpecialLinearGroup.mapGL_injective (R := ℤ) (S := ℝ) (n := Fin 2)
  rw [← h, Subgroup.relIndex, Subgroup.index_eq_card]

private lemma gamma0GL_norm_quotientFunc_bounded_atImInfty {N : ℕ} [NeZero N] {k : ℤ}
    (f : ModularForm (Gamma0GL N) k) (q : 𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) :
    BoundedAtFilter UpperHalfPlane.atImInfty (SlashInvariantForm.quotientFunc f q) := by
  classical
  induction q using Quotient.inductionOn with
  | h r =>
      change BoundedAtFilter UpperHalfPlane.atImInfty ((f : ℍ → ℂ) ∣[k] (r.val⁻¹))
      have hcusp : IsCusp OnePoint.infty
          (ConjAct.toConjAct r.val • Gamma0GL N) := by
        simpa using (Fact.out : IsCusp OnePoint.infty 𝒮ℒ).of_isFiniteRelIndex_conj
          (𝒢 := Gamma0GL N) (ℋ := 𝒮ℒ) r.property
      have hbd := (ModularForm.translate f r.val⁻¹).bdd_at_cusps' hcusp
        (1 : GL (Fin 2) ℝ) (by simp)
      simpa [OnePoint.isBoundedAt_infty_iff] using hbd

theorem gamma0GL_norm_decay_of_decay {N : ℕ} [NeZero N] {k : ℤ}
    (f : ModularForm (Gamma0GL N) k) {n : ℕ}
    (hfdec : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * n * τ.im)) :
    (⇑(ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * n * τ.im) := by
  classical
  letI := Fintype.ofFinite (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ)
  let e : 𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ := QuotientGroup.mk (1 : 𝒮ℒ)
  let H : ℍ → ℂ :=
    ∏ q ∈ (Finset.univ \ {e}), SlashInvariantForm.quotientFunc f q
  have hHbdd : BoundedAtFilter UpperHalfPlane.atImInfty H := by
    dsimp [H]
    exact BoundedAtFilter.prod _ (fun q _hq =>
      gamma0GL_norm_quotientFunc_bounded_atImInfty f q)
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

/-- Exponential decay of order `n` implies decay of every order `m ≤ n`. -/
theorem exp_decay_mono {g : ℍ → ℂ} {m n : ℕ} (hmn : m ≤ n)
    (h : g =O[UpperHalfPlane.atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * n * τ.im)) :
    g =O[UpperHalfPlane.atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * m * τ.im) := by
  refine h.trans (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_))
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hpy : 0 ≤ Real.pi * τ.im := le_of_lt (mul_pos Real.pi_pos τ.im_pos)
  have hle : (m : ℝ) * (Real.pi * τ.im) ≤ n * (Real.pi * τ.im) :=
    mul_le_mul_of_nonneg_right hmnR hpy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), one_mul]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The norm of a form on `Γ₀(N)`, as a level-one form of weight `k · [SL(2,ℤ) : Γ₀(N)]`. -/
noncomputable def gamma0NormLevelOne {N : ℕ} [NeZero N] {k : ℕ}
    (f : ModularForm (Gamma0GL N) (k : ℤ)) :
    ModularForm 𝒮ℒ ((k * Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) : ℕ) : ℤ) :=
  ModularForm.mcast (by push_cast; ring) (asLevelOne (ModularForm.norm 𝒮ℒ f))

/-- **Sturm bound on `Γ₀(N)`.** If `[SL(2,ℤ) : Γ₀(N)] ≤ B`, `k ≥ 4` is even, and the first
`k B / 12 + 1` coefficients of the `q`-expansion of `f ∈ M_k(Γ₀(N))` vanish, then `f = 0`. -/
theorem gamma0_eq_zero_of_coeff {N : ℕ} [NeZero N] {k B : ℕ} (hk : 4 ≤ k) (hke : Even k)
    (hB : (Gamma0 N).index ≤ B) (f : ModularForm (Gamma0GL N) (k : ℤ))
    (hcoeff : ∀ n : ℕ, n < k * B / 12 + 1 →
      PowerSeries.coeff (R := ℂ) n (ModularFormClass.qExpansion (1 : ℝ) f.toFun) = 0) :
    f = 0 := by
  let c : ℕ := Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ)
  have hc : c = (Gamma0 N).index := gamma0GL_normQuot_card N
  have hc1 : 0 < c := Nat.card_pos
  let K : ℕ := k * c
  have hK4 : 4 ≤ K := le_trans hk (Nat.le_mul_of_pos_right k hc1)
  have hKe : Even K := hke.mul_right c
  have hKB : K / 12 + 1 ≤ k * B / 12 + 1 := by
    have h1 : K ≤ k * B := Nat.mul_le_mul_left k (hc ▸ hB)
    have h2 : K / 12 ≤ k * B / 12 := Nat.div_le_div_right h1
    omega
  have hfdec₀ : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * ((k * B / 12 + 1 : ℕ) : ℝ) * τ.im / 1) :=
    exp_decay_atImInfty_of_qExpansion_coeff_zero f one_pos
      (gamma0GL_strictPeriod_one N) hcoeff
  have hfdec : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * ((k * B / 12 + 1 : ℕ) : ℝ) * τ.im) := by
    refine hfdec₀.congr_right fun τ => ?_
    congr 1
    ring
  have hnormdec := exp_decay_mono hKB (gamma0GL_norm_decay_of_decay f hfdec)
  have hnormdec' :
      (gamma0NormLevelOne f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
        fun τ : ℍ => Real.exp (-(2 * ((K / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im) := by
    change (⇑(ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * ((K / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im)
    refine hnormdec.congr_right fun τ => ?_
    congr 1
    ring
  have hnorm_zero : gamma0NormLevelOne f = 0 :=
    levelOne_modularForm_eq_zero_of_exp_decay hK4 hKe (gamma0NormLevelOne f) hnormdec'
  have hnorm_zero' : ModularForm.norm 𝒮ℒ f = 0 := by
    ext z
    have hz := congrArg (fun g : ModularForm 𝒮ℒ (K : ℤ) => g z) hnorm_zero
    change (gamma0NormLevelOne f) z = 0 at hz
    change (ModularForm.norm 𝒮ℒ f) z = 0
    simpa [gamma0NormLevelOne, asLevelOne, ModularForm.mcast, restrictModularForm,
      ModularForm.norm, SlashInvariantForm.norm] using hz
  have hf_fun : ⇑f = 0 :=
    (ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ) (f := f)).mp hnorm_zero'
  ext z
  exact congrFun hf_fun z

/-! ## Graded-ring helpers -/

section Graded

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]

/-- A form as an element of the graded ring. -/
noncomputable def gradedOf (k : ℤ) (f : ModularForm Γ k) : ⨁ k : ℤ, ModularForm Γ k :=
  DirectSum.of (ModularForm Γ) k f

/-- `x` is concentrated in weight `d`. -/
def IsHomogeneousOf (d : ℤ) (x : ⨁ k : ℤ, ModularForm Γ k) : Prop :=
  DirectSum.of (ModularForm Γ) d (x d) = x

lemma isHomogeneousOf_zero (d : ℤ) : IsHomogeneousOf d (0 : ⨁ k : ℤ, ModularForm Γ k) := by
  simp [IsHomogeneousOf]

lemma isHomogeneousOf_intCast (z : ℤ) :
    IsHomogeneousOf 0 (z : ⨁ k : ℤ, ModularForm Γ k) := by
  dsimp [IsHomogeneousOf]
  change DirectSum.of (ModularForm Γ) 0 (z : ModularForm Γ 0) = (z : ⨁ k : ℤ, ModularForm Γ k)
  rw [DirectSum.of_intCast]

omit [Γ.HasDetPlusMinusOne] in
lemma isHomogeneousOf_of (d : ℤ) (f : ModularForm Γ d) :
    IsHomogeneousOf d (DirectSum.of (ModularForm Γ) d f) := by
  simp [IsHomogeneousOf]

lemma isHomogeneousOf_add {d : ℤ} {x y : ⨁ k : ℤ, ModularForm Γ k}
    (hx : IsHomogeneousOf d x) (hy : IsHomogeneousOf d y) : IsHomogeneousOf d (x + y) := by
  dsimp [IsHomogeneousOf] at *
  rw [← hx, ← hy]
  simp

lemma isHomogeneousOf_mul {a b : ℤ} {x y : ⨁ k : ℤ, ModularForm Γ k}
    (hx : IsHomogeneousOf a x) (hy : IsHomogeneousOf b y) : IsHomogeneousOf (a + b) (x * y) := by
  dsimp [IsHomogeneousOf] at *
  rw [← hx, ← hy]
  simp [DirectSum.of_mul_of]

lemma isHomogeneousOf_pow {a : ℤ} {x : ⨁ k : ℤ, ModularForm Γ k}
    (hx : IsHomogeneousOf a x) (n : ℕ) : IsHomogeneousOf ((n : ℕ) * a) (x ^ n) := by
  dsimp [IsHomogeneousOf] at *
  rw [← hx]
  simp [DirectSum.ofPow]

omit [Γ.HasDetPlusMinusOne] in
lemma isHomogeneousOf_cast {a b : ℤ} {x : ⨁ k : ℤ, ModularForm Γ k}
    (h : a = b) (hx : IsHomogeneousOf a x) : IsHomogeneousOf b x := by
  subst h
  exact hx

lemma isHomogeneousOf_sub {d : ℤ} {x y : ⨁ k : ℤ, ModularForm Γ k}
    (hx : IsHomogeneousOf d x) (hy : IsHomogeneousOf d y) : IsHomogeneousOf d (x - y) := by
  dsimp [IsHomogeneousOf] at *
  rw [← hx, ← hy]
  simp

/-- `a x² + b x y + c y²` for `x, y` of weight `w` has weight `2 w`. -/
theorem isHomogeneousOf_quad (a b c : ℤ) {w : ℤ} {x y : ⨁ k : ℤ, ModularForm Γ k}
    (hx : IsHomogeneousOf w x) (hy : IsHomogeneousOf w y) :
    IsHomogeneousOf (2 * w)
      ((a : ⨁ k : ℤ, ModularForm Γ k) * x ^ 2 + (b : ⨁ k : ℤ, ModularForm Γ k) * x * y +
        (c : ⨁ k : ℤ, ModularForm Γ k) * y ^ 2) := by
  have h1 := isHomogeneousOf_cast (b := 2 * w) (by push_cast; ring)
    (isHomogeneousOf_mul (isHomogeneousOf_intCast (Γ := Γ) a) (isHomogeneousOf_pow hx 2))
  have h2 := isHomogeneousOf_cast (b := 2 * w) (by ring)
    (isHomogeneousOf_mul (isHomogeneousOf_mul (isHomogeneousOf_intCast (Γ := Γ) b) hx) hy)
  have h3 := isHomogeneousOf_cast (b := 2 * w) (by push_cast; ring)
    (isHomogeneousOf_mul (isHomogeneousOf_intCast (Γ := Γ) c) (isHomogeneousOf_pow hy 2))
  exact isHomogeneousOf_add (isHomogeneousOf_add h1 h2) h3

/-- A cleared sparse bivariate polynomial in four elements of one weight `w` is homogeneous of
weight `(xMax + yMax) w`. -/
theorem evalSparseBivarCleared_isHomogeneousOf (terms : List SparseBivarTerm) (xMax yMax : ℕ)
    (hdeg : ∀ t ∈ terms, t.xPow ≤ xMax ∧ t.yPow ≤ yMax) {w : ℤ}
    {xNum xDen yNum yDen : ⨁ k : ℤ, ModularForm Γ k}
    (hxN : IsHomogeneousOf w xNum) (hxD : IsHomogeneousOf w xDen)
    (hyN : IsHomogeneousOf w yNum) (hyD : IsHomogeneousOf w yDen) :
    IsHomogeneousOf (((xMax + yMax : ℕ) : ℤ) * w)
      (evalSparseBivarCleared terms xMax yMax xNum xDen yNum yDen) := by
  induction terms with
  | nil =>
      simpa [evalSparseBivarCleared] using isHomogeneousOf_zero (Γ := Γ) _
  | cons t ts ih =>
      have ht := hdeg t (by simp)
      have hc := isHomogeneousOf_intCast (Γ := Γ) t.coeff
      have h1 := isHomogeneousOf_mul hc (isHomogeneousOf_pow hxN t.xPow)
      have h2 := isHomogeneousOf_mul h1 (isHomogeneousOf_pow hxD (xMax - t.xPow))
      have h3 := isHomogeneousOf_mul h2 (isHomogeneousOf_pow hyN t.yPow)
      have h4 := isHomogeneousOf_mul h3 (isHomogeneousOf_pow hyD (yMax - t.yPow))
      have hhead := isHomogeneousOf_cast (b := ((xMax + yMax : ℕ) : ℤ) * w) (by
        push_cast [Nat.cast_sub ht.1, Nat.cast_sub ht.2]
        ring) h4
      have htail := ih (fun u hu => hdeg u (by simp [hu]))
      simpa [evalSparseBivarCleared] using isHomogeneousOf_add hhead htail

/-- Evaluation at `τ` on the graded ring: the sum of the values of the components. -/
noncomputable def gradedEvalAtOf (τ : ℍ) : (⨁ k : ℤ, ModularForm Γ k) →+* ℂ :=
  DirectSum.toSemiring
    (fun k => (Pi.evalAddMonoidHom (fun _ : ℍ => ℂ) τ).comp
      (ModularForm.coeHom (Γ := Γ) (k := k)))
    (by
      change ((1 : ModularForm Γ 0) : ℍ → ℂ) τ = 1
      rw [ModularForm.one_coe_eq_one]
      rfl)
    (fun f g => by
      change ((f.mul g : ModularForm Γ _) : ℍ → ℂ) τ = f τ * g τ
      rw [ModularForm.coe_mul]
      rfl)

theorem gradedEvalAtOf_of (τ : ℍ) (k : ℤ) (f : ModularForm Γ k) :
    gradedEvalAtOf τ (DirectSum.of _ k f) = f τ := by
  rw [gradedEvalAtOf, DirectSum.toSemiring_of]
  rfl

end Graded

end Modular
end Number
end Ripple
