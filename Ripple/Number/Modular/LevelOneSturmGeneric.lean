/-
  Generic level-1 Sturm bound for cusp forms of arbitrary even weight.

  For `f : CuspForm 𝒮ℒ k` with `k ≥ 4` even, if every `q`-expansion
  coefficient `a_m` with `m ≤ k/12` vanishes, then `f = 0`.

  Recipe: pick `(a, b)` with `a · k = 12 · b`, `a, b > 0`, depending on
  `k mod 12 ∈ {0, 2, 4, 6, 8, 10}`:
    * `k ≡ 0 (mod 12)`: `(a, b) = (1, k/12)`.
    * `k ≡ 2, 10`:      `(a, b) = (6, k/2)`.
    * `k ≡ 4, 8`:       `(a, b) = (3, k/4)`.
    * `k ≡ 6`:          `(a, b) = (2, k/6)`.

  Then `f^a / Δ^b` is a level-1 weight-0 modular form that decays at `∞`,
  hence is zero.  Since `Δ ≠ 0` on `ℍ`, `f^a = 0`, hence `f = 0`.
-/
import Ripple.Number.Modular.ModularPolynomialQExpansion
import Ripple.Number.Modular.HigherOrderDecay
import Ripple.Number.Modular.LevelOneSturm

set_option maxHeartbeats 800000
set_option linter.style.setOption false

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane Filter
open scoped MatrixGroups Manifold ModularForm

/-! ## Internal generic helper: `f^a / Δ^b` machinery. -/

/-- Slash invariance of `f^a / Δ^b` at weight `0`, given `a · k = 12 · b`. -/
private lemma cuspForm_pow_div_delta_pow_slash_action
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) {a b : ℕ}
    (hwt : a * k = 12 * b) (γ : SL(2, ℤ)) :
    (fun z : ℍ => f z ^ a / ModularForm.discriminant z ^ b) ∣[(0 : ℤ)] γ =
      fun z : ℍ => f z ^ a / ModularForm.discriminant z ^ b := by
  ext z
  -- Slash equations for `f` at weight `k`.
  have hf := SlashInvariantForm.slash_action_eqn'' f
    (Γ := 𝒮ℒ) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) z
  rw [← MulAction.compHom_smul_def] at hf
  -- Slash equations for `Δ` at weight `12`, applied at `z`.
  have hd := congrFun (delta_slash_action_level_one γ) z
  rw [ModularForm.SL_slash_apply] at hd
  -- Rewrite left-hand side via `SL_slash_apply`.
  rw [ModularForm.SL_slash_apply]
  set d : ℂ := UpperHalfPlane.denom
        (Matrix.SpecialLinearGroup.toGL
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) z with hd_def
  have hdne : d ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hdelg : ModularForm.discriminant (γ • z) ≠ 0 := ModularForm.discriminant_ne_zero (γ • z)
  have hdel : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  -- From `hd : Δ(γ•z) * d^(-12) = Δ z`, derive `Δ(γ•z) = d^12 * Δ z`.
  have hdelta_gz : ModularForm.discriminant (γ • z) = d ^ (12 : ℕ) * ModularForm.discriminant z := by
    have hd' : ModularForm.discriminant (γ • z) * d ^ ((-12 : ℤ)) = ModularForm.discriminant z := hd
    -- Multiply both sides by `d ^ 12`.
    have hdne12 : d ^ ((-12 : ℤ)) ≠ 0 := zpow_ne_zero _ hdne
    have hzpow_eq : d ^ ((12 : ℤ)) = d ^ (12 : ℕ) := zpow_natCast d 12
    have hmul_inv : d ^ ((-12 : ℤ)) * d ^ ((12 : ℤ)) = 1 := by
      rw [← zpow_add₀ hdne]; norm_num
    have hgoal :
        ModularForm.discriminant (γ • z) * d ^ ((-12 : ℤ)) * d ^ ((12 : ℤ)) =
          ModularForm.discriminant z * d ^ ((12 : ℤ)) := by rw [hd']
    have hgoal' :
        ModularForm.discriminant (γ • z) = ModularForm.discriminant z * d ^ ((12 : ℤ)) := by
      have hL :
          ModularForm.discriminant (γ • z) * d ^ ((-12 : ℤ)) * d ^ ((12 : ℤ)) =
            ModularForm.discriminant (γ • z) * (d ^ ((-12 : ℤ)) * d ^ ((12 : ℤ))) := by ring
      rw [hL, hmul_inv, mul_one] at hgoal
      exact hgoal
    rw [hgoal', hzpow_eq, mul_comm]
  -- Slash for `f`: `f(γ•z) = d^k * f z`.
  have hf_gz : (f : ℍ → ℂ) (γ • z) = d ^ ((k : ℤ)) * (f : ℍ → ℂ) z := hf
  have hf_gz_nat : (f : ℍ → ℂ) (γ • z) = d ^ k * (f : ℍ → ℂ) z := by
    have hzp : d ^ ((k : ℤ)) = d ^ k := zpow_natCast d k
    rw [hf_gz, hzp]
  -- Now compute the LHS.
  show (fun z' : ℍ => (f : ℍ → ℂ) z' ^ a / ModularForm.discriminant z' ^ b) (γ • z)
        * d ^ ((-(0 : ℤ))) = (f : ℍ → ℂ) z ^ a / ModularForm.discriminant z ^ b
  simp only [neg_zero, zpow_zero, mul_one]
  rw [hf_gz_nat, hdelta_gz]
  rw [mul_pow, mul_pow]
  have hka : (d ^ k) ^ a = d ^ (12 * b) := by
    rw [← pow_mul]; congr 1; rw [Nat.mul_comm]; exact hwt
  have h12b : (d ^ (12 : ℕ)) ^ b = d ^ (12 * b) := by rw [← pow_mul]
  rw [hka, h12b]
  have hdpow_ne : d ^ (12 * b) ≠ 0 := pow_ne_zero _ hdne
  have hdelta_pow_ne : ModularForm.discriminant z ^ b ≠ 0 := pow_ne_zero _ hdel
  -- Goal: `d^(12*b) * f z^a / (d^(12*b) * Δ z^b) = f z^a / Δ z^b`. Cancel `d^(12*b)`.
  rw [mul_div_mul_left _ _ hdpow_ne]

/-- Differentiability of `f^a / Δ^b` on `ℍ`. -/
private lemma mdiff_cuspForm_pow_div_delta_pow
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b : ℕ) :
    MDiff (fun z : ℍ => f z ^ a / ModularForm.discriminant z ^ b) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hf : MDiff (f : ℍ → ℂ) := CuspFormClass.holo f
  have hf' := (UpperHalfPlane.mdifferentiable_iff.mp hf) z hz
  have hd :
      DifferentiableWithinAt ℂ
        (fun x : ℂ => ModularForm.discriminant (UpperHalfPlane.ofComplex x))
          {z | 0 < z.im} z :=
    (UpperHalfPlane.mdifferentiable_iff.mp mdiff_delta) z hz
  have hdn : ModularForm.discriminant (UpperHalfPlane.ofComplex z) ≠ 0 :=
    ModularForm.discriminant_ne_zero (UpperHalfPlane.ofComplex z)
  have hdnb : ModularForm.discriminant (UpperHalfPlane.ofComplex z) ^ b ≠ 0 := pow_ne_zero b hdn
  exact (hf'.pow a).div (hd.pow b) hdnb

/-- Bound on `1/Δ^b` at the cusp `∞`. -/
private lemma delta_pow_inv_bigO_atImInfty (b : ℕ) :
    (fun z : ℍ => (ModularForm.discriminant z ^ b)⁻¹) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (2 * b * Real.pi * τ.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨(2 : ℝ) ^ (24 * b), ?_⟩
  filter_upwards [delta_norm_lower_bound] with z hz
  rw [norm_inv, Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow]
  have hpos : 0 < (1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im) := by positivity
  have hbase :
      ‖ModularForm.discriminant z‖⁻¹ ≤ (2 : ℝ) ^ 24 * Real.exp (2 * Real.pi * z.im) := by
    calc ‖ModularForm.discriminant z‖⁻¹
        ≤ ((1 / 2 : ℝ) ^ 24 * Real.exp (-2 * Real.pi * z.im))⁻¹ :=
          inv_anti₀ hpos hz
      _ = (2 : ℝ) ^ 24 * (Real.exp (-2 * Real.pi * z.im))⁻¹ := by
          have hone : ((1 / 2 : ℝ) ^ 24)⁻¹ = (2 : ℝ) ^ 24 := by
            rw [one_div, inv_pow, inv_inv]
          rw [mul_inv_rev, mul_comm, hone]
      _ = (2 : ℝ) ^ 24 * Real.exp (2 * Real.pi * z.im) := by
          congr 1; rw [← Real.exp_neg]; congr 1; ring
  have hbase_pos : 0 ≤ ‖ModularForm.discriminant z‖⁻¹ := by positivity
  calc (‖ModularForm.discriminant z‖ ^ b)⁻¹
      = (‖ModularForm.discriminant z‖⁻¹) ^ b := by rw [inv_pow]
    _ ≤ ((2 : ℝ) ^ 24 * Real.exp (2 * Real.pi * z.im)) ^ b :=
        pow_le_pow_left₀ hbase_pos hbase b
    _ = (2 : ℝ) ^ (24 * b) * Real.exp (2 * b * Real.pi * z.im) := by
        have hpow : ((2 : ℝ) ^ 24) ^ b = (2 : ℝ) ^ (24 * b) := by
          rw [← pow_mul]
        have hexp : Real.exp (2 * Real.pi * z.im) ^ b
            = Real.exp (2 * b * Real.pi * z.im) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [mul_pow, hpow, hexp]

/-- Vanishing of `f^a / Δ^b` at `∞` when `f` vanishes to high enough order. -/
private lemma isZeroAtImInfty_cuspForm_pow_div_delta_pow
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ)
    (hn_decay : a * n ≥ b + 1)
    (hcoeff : ∀ m < n,
      (ModularFormClass.qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff m = 0) :
    UpperHalfPlane.IsZeroAtImInfty
      (fun z : ℍ => f z ^ a / ModularForm.discriminant z ^ b) := by
  apply isZeroAtImInfty_of_exp_decay
  -- Decay of `f` at rate `2π·n`.
  have hf_decay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * (n : ℕ) * τ.im / 1) :=
    exp_decay_atImInfty_of_qExpansion_coeff_zero f one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z hcoeff
  have hf_decay' : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * n) * Real.pi * τ.im) := by
    refine hf_decay.congr_right fun τ => ?_
    congr 1; ring
  have hfa : (fun z : ℍ => f z ^ a) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (-(2 * a * n) * Real.pi * τ.im) := by
    have h := hf_decay'.pow a
    refine h.congr_right fun τ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdelta_inv := delta_pow_inv_bigO_atImInfty b
  -- Net rate constant: `c = 2 (a*n - b)`. Strictly positive since `a*n ≥ b+1`.
  set c : ℝ := 2 * ((a : ℝ) * n - b) * Real.pi with hc_def
  have hc_pos : 0 < c := by
    have han : (b : ℝ) + 1 ≤ (a : ℝ) * n := by exact_mod_cast hn_decay
    have h_diff : (a : ℝ) * n - b ≥ 1 := by linarith
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have : 0 < (a : ℝ) * n - b := by linarith
    positivity
  refine ⟨c, hc_pos, ?_⟩
  refine ((hfa.mul hdelta_inv).congr_left (fun z => by simp [div_eq_mul_inv])).congr_right ?_
  intro τ
  rw [← Real.exp_add]
  congr 1
  simp only [hc_def]
  ring

/-- Vanishing of `f^a / Δ^b` at `∞` from an already-proved exponential
decay estimate for `f`. -/
private lemma isZeroAtImInfty_cuspForm_pow_div_delta_pow_of_exp_decay
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ)
    (hn_decay : a * n ≥ b + 1)
    (hf_decay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * n) * Real.pi * τ.im)) :
    UpperHalfPlane.IsZeroAtImInfty
      (fun z : ℍ => f z ^ a / ModularForm.discriminant z ^ b) := by
  apply isZeroAtImInfty_of_exp_decay
  have hfa : (fun z : ℍ => f z ^ a) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (-(2 * a * n) * Real.pi * τ.im) := by
    have h := hf_decay.pow a
    refine h.congr_right fun τ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdelta_inv := delta_pow_inv_bigO_atImInfty b
  set c : ℝ := 2 * ((a : ℝ) * n - b) * Real.pi with hc_def
  have hc_pos : 0 < c := by
    have han : (b : ℝ) + 1 ≤ (a : ℝ) * n := by exact_mod_cast hn_decay
    have h_diff : (a : ℝ) * n - b ≥ 1 := by linarith
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have : 0 < (a : ℝ) * n - b := by linarith
    positivity
  refine ⟨c, hc_pos, ?_⟩
  refine ((hfa.mul hdelta_inv).congr_left (fun z => by simp [div_eq_mul_inv])).congr_right ?_
  intro τ
  rw [← Real.exp_add]
  congr 1
  simp only [hc_def]
  ring

/-- Boundedness of `f^a / Δ^b` at every cusp of `Γ(1)`. -/
private lemma bddAtCusp_cuspForm_pow_div_delta_pow
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ)
    (hwt : a * k = 12 * b)
    (hn_decay : a * n ≥ b + 1)
    (hcoeff : ∀ m < n,
      (ModularFormClass.qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff m = 0)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsBoundedAt (fun z : ℍ => f z ^ a / ModularForm.discriminant z ^ b) 0 := by
  have hc' : IsCusp c 𝒮ℒ := hc
  rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc']
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc'
  exact ⟨γ, hγ.symm, by
    rw [cuspForm_pow_div_delta_pow_slash_action f hwt γ]
    exact (isZeroAtImInfty_cuspForm_pow_div_delta_pow f a b n hn_decay
      hcoeff).isBoundedAtImInfty⟩

/-- Boundedness at every cusp from an exponential decay estimate at `∞`. -/
private lemma bddAtCusp_cuspForm_pow_div_delta_pow_of_exp_decay
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ)
    (hwt : a * k = 12 * b)
    (hn_decay : a * n ≥ b + 1)
    (hf_decay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * n) * Real.pi * τ.im))
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsBoundedAt (fun z : ℍ => f z ^ a / ModularForm.discriminant z ^ b) 0 := by
  have hc' : IsCusp c 𝒮ℒ := hc
  rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc']
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc'
  exact ⟨γ, hγ.symm, by
    rw [cuspForm_pow_div_delta_pow_slash_action f hwt γ]
    exact (isZeroAtImInfty_cuspForm_pow_div_delta_pow_of_exp_decay
      f a b n hn_decay hf_decay).isBoundedAtImInfty⟩

/-- Bundle `f^a / Δ^b` as a level-1 weight-0 modular form. -/
private noncomputable def cuspFormPowDivDeltaPowMF
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ)
    (hwt : a * k = 12 * b)
    (hn_decay : a * n ≥ b + 1)
    (hcoeff : ∀ m < n,
      (ModularFormClass.qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff m = 0) :
    ModularForm 𝒮ℒ 0 where
  toSlashInvariantForm :=
    { toFun := fun z => f z ^ a / ModularForm.discriminant z ^ b
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
        exact cuspForm_pow_div_delta_pow_slash_action f hwt g }
  holo' := mdiff_cuspForm_pow_div_delta_pow f a b
  bdd_at_cusps' hc :=
    bddAtCusp_cuspForm_pow_div_delta_pow f a b n hwt hn_decay hcoeff hc

/-- Bundle `f^a / Δ^b` as a level-1 weight-0 modular form, using an
external exponential decay estimate for `f`. -/
private noncomputable def cuspFormPowDivDeltaPowMFOfExpDecay
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ)
    (hwt : a * k = 12 * b)
    (hn_decay : a * n ≥ b + 1)
    (hf_decay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * n) * Real.pi * τ.im)) :
    ModularForm 𝒮ℒ 0 where
  toSlashInvariantForm :=
    { toFun := fun z => f z ^ a / ModularForm.discriminant z ^ b
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
        exact cuspForm_pow_div_delta_pow_slash_action f hwt g }
  holo' := mdiff_cuspForm_pow_div_delta_pow f a b
  bdd_at_cusps' hc :=
    bddAtCusp_cuspForm_pow_div_delta_pow_of_exp_decay
      f a b n hwt hn_decay hf_decay hc

/-- Generic helper: `f^a / Δ^b = 0` on `ℍ`. -/
private lemma cuspForm_pow_div_delta_pow_eq_zero
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ)
    (hwt : a * k = 12 * b)
    (hn_decay : a * n ≥ b + 1)
    (hcoeff : ∀ m < n,
      (ModularFormClass.qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff m = 0) :
    ∀ z : ℍ, f z ^ a / ModularForm.discriminant z ^ b = 0 := by
  have ⟨c, hc⟩ :=
    ModularFormClass.levelOne_weight_zero_const
      (cuspFormPowDivDeltaPowMF f a b n hwt hn_decay hcoeff)
  have hzero := isZeroAtImInfty_cuspForm_pow_div_delta_pow f a b n hn_decay hcoeff
  rw [UpperHalfPlane.IsZeroAtImInfty] at hzero
  have hc_eq : ∀ z : ℍ, f z ^ a / ModularForm.discriminant z ^ b = c := fun z => congrFun hc z
  have htend : Filter.Tendsto (fun _ : ℍ => c) UpperHalfPlane.atImInfty (nhds 0) :=
    hzero.congr (fun z => hc_eq z)
  have hc_zero : c = 0 := tendsto_const_nhds_iff.mp htend
  intro z; rw [hc_eq z, hc_zero]

/-- Generic helper: `f^a / Δ^b = 0` on `ℍ`, using an external exponential
decay estimate for `f`. -/
private lemma cuspForm_pow_div_delta_pow_eq_zero_of_exp_decay
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ)
    (hwt : a * k = 12 * b)
    (hn_decay : a * n ≥ b + 1)
    (hf_decay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * n) * Real.pi * τ.im)) :
    ∀ z : ℍ, f z ^ a / ModularForm.discriminant z ^ b = 0 := by
  have ⟨c, hc⟩ :=
    ModularFormClass.levelOne_weight_zero_const
      (cuspFormPowDivDeltaPowMFOfExpDecay f a b n hwt hn_decay hf_decay)
  have hzero := isZeroAtImInfty_cuspForm_pow_div_delta_pow_of_exp_decay
    f a b n hn_decay hf_decay
  rw [UpperHalfPlane.IsZeroAtImInfty] at hzero
  have hc_eq : ∀ z : ℍ, f z ^ a / ModularForm.discriminant z ^ b = c := fun z => congrFun hc z
  have htend : Filter.Tendsto (fun _ : ℍ => c) UpperHalfPlane.atImInfty (nhds 0) :=
    hzero.congr (fun z => hc_eq z)
  have hc_zero : c = 0 := tendsto_const_nhds_iff.mp htend
  intro z; rw [hc_eq z, hc_zero]

/-- From `f^a / Δ^b = 0` and `Δ ≠ 0`, conclude `f = 0`. -/
private lemma cuspForm_eq_zero_of_pow_div_delta_pow_eq_zero
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b : ℕ) (hap : 0 < a)
    (hzero : ∀ z : ℍ, f z ^ a / ModularForm.discriminant z ^ b = 0) :
    ⇑f = 0 := by
  ext z
  have h := hzero z
  have hdel : ModularForm.discriminant z ≠ 0 := ModularForm.discriminant_ne_zero z
  have hdelb : ModularForm.discriminant z ^ b ≠ 0 := pow_ne_zero b hdel
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · have hane : a ≠ 0 := Nat.pos_iff_ne_zero.mp hap
    rwa [pow_eq_zero_iff hane] at h
  · exact absurd h hdelb

/-- Combined helper: pick `(a, b, n)`, dispatch to zero conclusion. -/
private lemma cuspForm_eq_zero_via
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ) (hap : 0 < a)
    (hwt : a * k = 12 * b)
    (hn_decay : a * n ≥ b + 1)
    (hcoeff : ∀ m < n,
      (ModularFormClass.qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff m = 0) :
    ⇑f = 0 :=
  cuspForm_eq_zero_of_pow_div_delta_pow_eq_zero f a b hap
    (cuspForm_pow_div_delta_pow_eq_zero f a b n hwt hn_decay hcoeff)

/-- Combined helper using an external exponential decay estimate. -/
private lemma cuspForm_eq_zero_via_exp_decay
    {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) (a b n : ℕ) (hap : 0 < a)
    (hwt : a * k = 12 * b)
    (hn_decay : a * n ≥ b + 1)
    (hf_decay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * n) * Real.pi * τ.im)) :
    ⇑f = 0 :=
  cuspForm_eq_zero_of_pow_div_delta_pow_eq_zero f a b hap
    (cuspForm_pow_div_delta_pow_eq_zero_of_exp_decay f a b n hwt hn_decay hf_decay)

/-! ## Main theorem: dispatch on `k mod 12`. -/

/-- Generic level-1 Sturm bound for cusp forms of arbitrary even weight `k ≥ 4`.

If `f : CuspForm 𝒮ℒ k` has every `q`-expansion coefficient `a_m` with
`m ≤ k/12` vanishing, then `f = 0`. -/
theorem levelOne_cuspForm_eq_zero_of_low_coeffs_vanish
    {k : ℕ} (_hk_pos : 4 ≤ k) (hk_even : Even k)
    (f : CuspForm 𝒮ℒ (k : ℤ))
    (hcoeff : ∀ m : ℕ, m ≤ k / 12 →
      (ModularFormClass.qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff m = 0) :
    ⇑f = 0 := by
  -- `n = k/12 + 1`. `m ≤ k/12 ↔ m < n`.
  set n : ℕ := k / 12 + 1 with hn_def
  have hcoeff' : ∀ m < n,
      (ModularFormClass.qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff m = 0 := by
    intro m hm; apply hcoeff; omega
  -- Even k → k % 12 ∈ {0, 2, 4, 6, 8, 10}.
  have hk_even2 : k % 2 = 0 := by
    rcases hk_even with ⟨c, hc⟩; omega
  have hmod_lt : k % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hmod_even : k % 12 % 2 = 0 := by omega
  -- Dispatch.
  rcases Nat.lt_iff_add_one_le.mp hmod_lt with hmod_le
  -- Just enumerate manually.
  have h_dispatch : k % 12 = 0 ∨ k % 12 = 2 ∨ k % 12 = 4 ∨ k % 12 = 6 ∨
      k % 12 = 8 ∨ k % 12 = 10 := by omega
  rcases h_dispatch with h0 | h2 | h4 | h6 | h8 | h10
  · -- k % 12 = 0: a = 1, b = k / 12.
    have hwt : 1 * k = 12 * (k / 12) := by omega
    have hn_decay : 1 * n ≥ (k / 12) + 1 := by
      simp only [hn_def, one_mul]; exact le_refl _
    exact cuspForm_eq_zero_via f 1 (k / 12) n one_pos hwt hn_decay hcoeff'
  · -- k % 12 = 2: a = 6, b = k / 2.
    have hwt : 6 * k = 12 * (k / 2) := by omega
    have hn_decay : 6 * n ≥ (k / 2) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via f 6 (k / 2) n (by norm_num) hwt hn_decay hcoeff'
  · -- k % 12 = 4: a = 3, b = k / 4.
    have hwt : 3 * k = 12 * (k / 4) := by omega
    have hn_decay : 3 * n ≥ (k / 4) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via f 3 (k / 4) n (by norm_num) hwt hn_decay hcoeff'
  · -- k % 12 = 6: a = 2, b = k / 6.
    have hwt : 2 * k = 12 * (k / 6) := by omega
    have hn_decay : 2 * n ≥ (k / 6) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via f 2 (k / 6) n (by norm_num) hwt hn_decay hcoeff'
  · -- k % 12 = 8: a = 3, b = k / 4.
    have hwt : 3 * k = 12 * (k / 4) := by omega
    have hn_decay : 3 * n ≥ (k / 4) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via f 3 (k / 4) n (by norm_num) hwt hn_decay hcoeff'
  · -- k % 12 = 10: a = 6, b = k / 2.
    have hwt : 6 * k = 12 * (k / 2) := by omega
    have hn_decay : 6 * n ≥ (k / 2) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via f 6 (k / 2) n (by norm_num) hwt hn_decay hcoeff'

/-- Generic level-1 zero theorem for cusp forms from an externally supplied
exponential decay estimate at the Sturm order `k / 12 + 1`. -/
theorem levelOne_cuspForm_eq_zero_of_exp_decay
    {k : ℕ} (_hk_pos : 4 ≤ k) (hk_even : Even k)
    (f : CuspForm 𝒮ℒ (k : ℤ))
    (hf_decay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * ((k / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im)) :
    ⇑f = 0 := by
  set n : ℕ := k / 12 + 1 with hn_def
  have hf_decay' : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * n) * Real.pi * τ.im) := by
    simpa [hn_def] using hf_decay
  have hk_even2 : k % 2 = 0 := by
    rcases hk_even with ⟨c, hc⟩
    omega
  have hmod_lt : k % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hmod_even : k % 12 % 2 = 0 := by omega
  rcases Nat.lt_iff_add_one_le.mp hmod_lt with hmod_le
  have h_dispatch : k % 12 = 0 ∨ k % 12 = 2 ∨ k % 12 = 4 ∨ k % 12 = 6 ∨
      k % 12 = 8 ∨ k % 12 = 10 := by omega
  rcases h_dispatch with h0 | h2 | h4 | h6 | h8 | h10
  · have hwt : 1 * k = 12 * (k / 12) := by omega
    have hn_decay : 1 * n ≥ (k / 12) + 1 := by
      simp only [hn_def, one_mul]; exact le_refl _
    exact cuspForm_eq_zero_via_exp_decay f 1 (k / 12) n one_pos hwt hn_decay hf_decay'
  · have hwt : 6 * k = 12 * (k / 2) := by omega
    have hn_decay : 6 * n ≥ (k / 2) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via_exp_decay f 6 (k / 2) n (by norm_num) hwt hn_decay
      hf_decay'
  · have hwt : 3 * k = 12 * (k / 4) := by omega
    have hn_decay : 3 * n ≥ (k / 4) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via_exp_decay f 3 (k / 4) n (by norm_num) hwt hn_decay
      hf_decay'
  · have hwt : 2 * k = 12 * (k / 6) := by omega
    have hn_decay : 2 * n ≥ (k / 6) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via_exp_decay f 2 (k / 6) n (by norm_num) hwt hn_decay
      hf_decay'
  · have hwt : 3 * k = 12 * (k / 4) := by omega
    have hn_decay : 3 * n ≥ (k / 4) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via_exp_decay f 3 (k / 4) n (by norm_num) hwt hn_decay
      hf_decay'
  · have hwt : 6 * k = 12 * (k / 2) := by omega
    have hn_decay : 6 * n ≥ (k / 2) + 1 := by
      simp only [hn_def]; omega
    exact cuspForm_eq_zero_via_exp_decay f 6 (k / 2) n (by norm_num) hwt hn_decay
      hf_decay'

/-- Generic level-1 Sturm bound for modular forms of arbitrary even weight
`k ≥ 4`.

The vanishing of the constant coefficient makes the modular form cuspidal;
then `levelOne_cuspForm_eq_zero_of_low_coeffs_vanish` applies. -/
theorem levelOne_modularForm_eq_zero_of_low_coeffs_vanish
    {k : ℕ} (hk_pos : 4 ≤ k) (hk_even : Even k)
    (f : ModularForm 𝒮ℒ (k : ℤ))
    (hcoeff : ∀ m : ℕ, m ≤ k / 12 →
      (ModularFormClass.qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff m = 0) :
    f = 0 := by
  have h0coeff :
      (ModularFormClass.qExpansion (1 : ℝ) (f : ℍ → ℂ)).coeff 0 = 0 :=
    hcoeff 0 (by omega)
  have hval : UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) = 0 := by
    rw [← ModularFormClass.qExpansion_coeff_zero (f := f)
      one_pos ModularFormClass.one_mem_strictPeriods_SL2Z]
    exact h0coeff
  let fcusp : CuspForm 𝒮ℒ (k : ℤ) :=
    levelOneCuspFormOfValueAtInftyZero f hval
  have hcusp : (fcusp : ℍ → ℂ) = 0 :=
    levelOne_cuspForm_eq_zero_of_low_coeffs_vanish hk_pos hk_even fcusp (by
      intro m hm
      simpa [fcusp, levelOneCuspFormOfValueAtInftyZero] using hcoeff m hm)
  ext z
  exact congrFun hcusp z

/-- Level-one vanishing for weights divisible by `12`, formulated directly
from the high-order exponential decay estimate used in the norm trick. -/
theorem levelOne_modularForm_eq_zero_of_exp_decay_of_dvd12
    {k : ℕ} (hk_mod : k % 12 = 0)
    (f : ModularForm 𝒮ℒ (k : ℤ))
    (hf_decay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * ((k / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im)) :
    f = 0 := by
  have hzero : UpperHalfPlane.IsZeroAtImInfty (f : ℍ → ℂ) := by
    apply isZeroAtImInfty_of_exp_decay
    refine ⟨2 * ((k / 12 + 1 : ℕ) : ℝ) * Real.pi, by positivity, ?_⟩
    refine hf_decay.congr_right fun τ => ?_
    congr 1
    ring
  have hval : UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) = 0 :=
    hzero.valueAtInfty_eq_zero
  let fcusp : CuspForm 𝒮ℒ (k : ℤ) :=
    levelOneCuspFormOfValueAtInftyZero f hval
  have hfcusp_decay : (fcusp : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * ((k / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im) := by
    simpa [fcusp, levelOneCuspFormOfValueAtInftyZero] using hf_decay
  have hcusp : (fcusp : ℍ → ℂ) = 0 := by
    have hwt : 1 * k = 12 * (k / 12) := by omega
    have hn_decay : 1 * (k / 12 + 1) ≥ (k / 12) + 1 := by omega
    exact cuspForm_eq_zero_via_exp_decay fcusp 1 (k / 12) (k / 12 + 1)
      one_pos hwt hn_decay hfcusp_decay
  ext z
  exact congrFun hcusp z

/-- Generic level-1 zero theorem for modular forms of arbitrary even weight
`k ≥ 4`, from an externally supplied exponential decay estimate at the
Sturm order `k / 12 + 1`. -/
theorem levelOne_modularForm_eq_zero_of_exp_decay
    {k : ℕ} (hk_pos : 4 ≤ k) (hk_even : Even k)
    (f : ModularForm 𝒮ℒ (k : ℤ))
    (hf_decay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-(2 * ((k / 12 + 1 : ℕ) : ℝ)) * Real.pi * τ.im)) :
    f = 0 := by
  have hzeroInf : UpperHalfPlane.IsZeroAtImInfty (f : ℍ → ℂ) := by
    apply isZeroAtImInfty_of_exp_decay
    refine ⟨2 * ((k / 12 + 1 : ℕ) : ℝ) * Real.pi, by positivity, ?_⟩
    refine hf_decay.congr_right fun τ => ?_
    congr 1
    ring
  have hval : UpperHalfPlane.valueAtInfty (f : ℍ → ℂ) = 0 :=
    hzeroInf.valueAtInfty_eq_zero
  let fcusp : CuspForm 𝒮ℒ (k : ℤ) :=
    levelOneCuspFormOfValueAtInftyZero f hval
  have hcusp : (fcusp : ℍ → ℂ) = 0 :=
    levelOne_cuspForm_eq_zero_of_exp_decay hk_pos hk_even fcusp (by
      simpa [fcusp, levelOneCuspFormOfValueAtInftyZero] using hf_decay)
  ext z
  exact congrFun hcusp z

end Modular
end Number
end Ripple
