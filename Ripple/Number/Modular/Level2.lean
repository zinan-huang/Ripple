import Ripple.Number.Modular.Level2Z
import Ripple.Number.Modular.Gamma0_58

/-!
# Level-2 identities

With `e = E₄(τ)`, `f = E₄(2τ)` and `Z = 2E₂(2τ) − E₂(τ)` (`level2Z`), the Sturm bound on `Γ₀(2)`
(index 3, two coefficients in weights 4 and 6) gives

* `e + 4f = 5Z²` (`level2_E4_sum`),
* `2E₆(τ) = 3Z(4f − e) − 7Z³` (`level2_E6`),
* `16E₆(2τ) = 7Z³ + 3Z(4f − e)` (`level2_E6_two`).
-/

namespace Ripple
namespace Number
namespace Modular

open CongruenceSubgroup ModularForm ModularFormClass UpperHalfPlane
open scoped MatrixGroups ModularForm DirectSum

/-! ## `E₆(dτ)` on `Γ₀(N)` -/

/-- `E₆` restricted to `Γ₀(N)`. -/
noncomputable def E6Level (N : ℕ) : ModularForm (Gamma0GL N) 6 :=
  restrictModularForm (gamma0GL_le_SL N) E6

@[simp]
lemma E6Level_apply (N : ℕ) (τ : ℍ) : E6Level N τ = E6 τ :=
  rfl

theorem E6Level_qExpansion (N : ℕ) :
    ModularFormClass.qExpansion (1 : ℝ) (E6Level N : ℍ → ℂ) = E6QExpansion :=
  rfl

/-- `τ ↦ E₆(dτ)` as a weight-6 form on `Γ₀(N)` for `d ∣ N`. -/
noncomputable def E6Scaled {N d : ℕ} [NeZero d] (hd : d ∣ N) : ModularForm (Gamma0GL N) 6 :=
  ((d : ℂ) ^ (-5 : ℤ)) •
    restrictModularForm (gamma0GL_le_scale_conj hd) (ModularForm.translate E6 (scaleGL d))

set_option linter.flexible false in
lemma E6Scaled_apply {N d : ℕ} [NeZero d] (hd : d ∣ N) (τ : ℍ) :
    E6Scaled hd τ = E6 (scaleGL d • τ) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdpos : 0 < d := NeZero.pos d
  change ((d : ℂ) ^ (-5 : ℤ)) * (((E6 : ℍ → ℂ) ∣[(6 : ℤ)] scaleGL d) τ) = E6 (scaleGL d • τ)
  simp [ModularForm.slash_def, UpperHalfPlane.σ, UpperHalfPlane.denom, scaleGL, hdpos]
  field_simp

theorem E6Scaled_qExpansion {N d : ℕ} [NeZero d] (hd : d ∣ N) :
    ModularFormClass.qExpansion (1 : ℝ) (E6Scaled hd : ℍ → ℂ) =
      qPullbackBy d E6QExpansion := by
  ext n
  symm
  refine ModularFormClass.qExpansion_coeff_unique
    (c := fun n => PowerSeries.coeff (R := ℂ) n (qPullbackBy d E6QExpansion))
    (F := ModularForm (Gamma0GL N) 6) (f := E6Scaled hd)
    (k := 6) one_pos (gamma0GL_strictPeriod_one N) ?_ n
  intro τ
  rw [E6Scaled_apply hd τ]
  refine qPullbackBy_hasSum_eval d ?_
  simpa [qParam_scaleGL d τ, smul_eq_mul] using E6QExpansion_hasSum (scaleGL d • τ)

/-! ## Sturm on `Γ₀(N)` for graded elements -/

/-- A homogeneous element of the graded ring whose `q`-expansion vanishes up to the Sturm bound
vanishes at every point. -/
theorem gradedEval_eq_zero_of_coeff {N : ℕ} [NeZero N] {k B : ℕ} (hk : 4 ≤ k) (hke : Even k)
    (hB : (Gamma0 N).index ≤ B) (x : ⨁ k : ℤ, ModularForm (Gamma0GL N) k)
    (hx : IsHomogeneousOf (k : ℤ) x)
    (hcoeff : ∀ n : ℕ, n < k * B / 12 + 1 → PowerSeries.coeff (R := ℂ) n
      (qExpansionRingHom (Γ := Gamma0GL N) (1 : ℝ) one_pos (gamma0GL_strictPeriod_one N) x) = 0)
    (τ : ℍ) : gradedEvalAtOf τ x = 0 := by
  have hf : x (k : ℤ) = 0 := by
    apply gamma0_eq_zero_of_coeff hk hke hB
    intro n hn
    have hmap := congrArg
      (qExpansionRingHom (Γ := Gamma0GL N) (1 : ℝ) one_pos (gamma0GL_strictPeriod_one N)) hx
    have hq : ModularFormClass.qExpansion (1 : ℝ) (x (k : ℤ) : ℍ → ℂ) =
        qExpansionRingHom (Γ := Gamma0GL N) (1 : ℝ) one_pos (gamma0GL_strictPeriod_one N) x := by
      simpa using hmap
    have h := hcoeff n hn
    rw [← hq] at h
    exact h
  rw [← hx, hf]
  simp

/-! ## Low coefficients -/

theorem coeff_zero_mul' (f g : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 0 (f * g) =
      PowerSeries.coeff (R := ℂ) 0 f * PowerSeries.coeff (R := ℂ) 0 g := by
  simp [PowerSeries.coeff_mul]

theorem coeff_one_mul' (f g : PowerSeries ℂ) :
    PowerSeries.coeff (R := ℂ) 1 (f * g) =
      PowerSeries.coeff (R := ℂ) 0 f * PowerSeries.coeff (R := ℂ) 1 g +
        PowerSeries.coeff (R := ℂ) 1 f * PowerSeries.coeff (R := ℂ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp

theorem coeff_ofNat' (m : ℕ) [m.AtLeastTwo] (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (OfNat.ofNat m : PowerSeries ℂ) =
      if n = 0 then (OfNat.ofNat m : ℂ) else 0 := by
  rw [← map_ofNat (PowerSeries.C (R := ℂ)), PowerSeries.coeff_C]

theorem coeff_intCast' (z : ℤ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (z : PowerSeries ℂ) = if n = 0 then (z : ℂ) else 0 := by
  rw [← map_intCast (PowerSeries.C (R := ℂ)), PowerSeries.coeff_C]

/-! ## The identities -/

local notation "G2" => ⨁ k : ℤ, ModularForm (Gamma0GL 2) k

private lemma hom_zmul {d : ℤ} (z : ℤ) {x : G2} (hx : IsHomogeneousOf d x) :
    IsHomogeneousOf d ((z : G2) * x) :=
  isHomogeneousOf_cast (by simp) (isHomogeneousOf_mul (isHomogeneousOf_intCast z) hx)

private lemma hom_of (d : ℤ) (f : ModularForm (Gamma0GL 2) d) :
    IsHomogeneousOf d (gradedOf d f) :=
  isHomogeneousOf_of d f

private noncomputable abbrev gE : G2 := gradedOf 4 (E4Level 2)
private noncomputable abbrev gF : G2 := gradedOf 4 (E4Scaled (show 2 ∣ 2 from dvd_rfl))
private noncomputable abbrev gZ : G2 := gradedOf 2 level2Z
private noncomputable abbrev gE6 : G2 := gradedOf 6 (E6Level 2)
private noncomputable abbrev gF6 : G2 := gradedOf 6 (E6Scaled (show 2 ∣ 2 from dvd_rfl))

private lemma hom_gZ2 : IsHomogeneousOf 4 (gZ ^ 2) :=
  isHomogeneousOf_cast (by norm_num) (isHomogeneousOf_pow (hom_of 2 level2Z) 2)

private lemma hom_gZ3 : IsHomogeneousOf 6 (gZ ^ 3) :=
  isHomogeneousOf_cast (by norm_num) (isHomogeneousOf_pow (hom_of 2 level2Z) 3)

private lemma hom_gZD : IsHomogeneousOf 6 (gZ * (((4 : ℤ) : G2) * gF - gE)) :=
  isHomogeneousOf_cast (by norm_num) (isHomogeneousOf_mul (hom_of 2 level2Z)
    (isHomogeneousOf_sub (hom_zmul 4 (hom_of 4 _)) (hom_of 4 _)))

/-- `e + 4f − 5Z² = 0` in the graded ring. -/
private noncomputable abbrev gJ1 : G2 := gE + ((4 : ℤ) : G2) * gF - ((5 : ℤ) : G2) * gZ ^ 2

/-- `2E₆ − 3Z(4f − e) + 7Z³ = 0`. -/
private noncomputable abbrev gJ2 : G2 :=
  ((2 : ℤ) : G2) * gE6 - ((3 : ℤ) : G2) * (gZ * (((4 : ℤ) : G2) * gF - gE)) +
    ((7 : ℤ) : G2) * gZ ^ 3

/-- `16E₆(2τ) − 7Z³ − 3Z(4f − e) = 0`. -/
private noncomputable abbrev gJ3 : G2 :=
  ((16 : ℤ) : G2) * gF6 - ((7 : ℤ) : G2) * gZ ^ 3 -
    ((3 : ℤ) : G2) * (gZ * (((4 : ℤ) : G2) * gF - gE))

private lemma qExp_simp :
    (qExpansionRingHom (Γ := Gamma0GL 2) (1 : ℝ) one_pos (gamma0GL_strictPeriod_one 2) gE =
      E4QExpansion) ∧
    (qExpansionRingHom (Γ := Gamma0GL 2) (1 : ℝ) one_pos (gamma0GL_strictPeriod_one 2) gF =
      qPullbackBy 2 E4QExpansion) ∧
    (qExpansionRingHom (Γ := Gamma0GL 2) (1 : ℝ) one_pos (gamma0GL_strictPeriod_one 2) gZ =
      level2ZQExpansion) ∧
    (qExpansionRingHom (Γ := Gamma0GL 2) (1 : ℝ) one_pos (gamma0GL_strictPeriod_one 2) gE6 =
      E6QExpansion) ∧
    (qExpansionRingHom (Γ := Gamma0GL 2) (1 : ℝ) one_pos (gamma0GL_strictPeriod_one 2) gF6 =
      qPullbackBy 2 E6QExpansion) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [gE, gF, gZ, gE6, gF6, gradedOf, ← ModularFormClass.qExpansion_eq, E4Level_qExpansion,
    E4Scaled_qExpansion, level2Z_qExpansion, E6Level_qExpansion, E6Scaled_qExpansion]

set_option maxHeartbeats 1000000 in
-- `norm_num` on the expanded low coefficients of five series.
private lemma low_coeffs (n : ℕ) (hn : n < 2) :
    PowerSeries.coeff (R := ℂ) n (qExpansionRingHom (Γ := Gamma0GL 2) (1 : ℝ) one_pos
      (gamma0GL_strictPeriod_one 2) gJ1) = 0 ∧
    PowerSeries.coeff (R := ℂ) n (qExpansionRingHom (Γ := Gamma0GL 2) (1 : ℝ) one_pos
      (gamma0GL_strictPeriod_one 2) gJ2) = 0 ∧
    PowerSeries.coeff (R := ℂ) n (qExpansionRingHom (Γ := Gamma0GL 2) (1 : ℝ) one_pos
      (gamma0GL_strictPeriod_one 2) gJ3) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := qExp_simp
  simp only [gJ1, gJ2, gJ3, map_add, map_sub, map_mul, map_pow, map_intCast, h1, h2, h3, h4, h5]
  interval_cases n <;>
  simp only [map_add, map_sub, pow_two, pow_three, coeff_zero_mul', coeff_one_mul',
    coeff_intCast', coeff_qPullbackBy, level2ZQExpansion, map_smul, smul_eq_mul,
    coeff_E2QExpansion, coeff_E4QExpansion, coeff_E6QExpansion] <;>
  norm_num [ArithmeticFunction.sigma_apply, Nat.divisors_one]

private lemma gJ_eval (τ : ℍ) :
    gradedEvalAtOf τ gJ1 = 0 ∧ gradedEvalAtOf τ gJ2 = 0 ∧ gradedEvalAtOf τ gJ3 = 0 := by
  have hB : (Gamma0 2).index ≤ 3 := gamma0_index_2.le
  refine ⟨?_, ?_, ?_⟩
  · refine gradedEval_eq_zero_of_coeff (k := 4) (by norm_num) ⟨2, rfl⟩ hB gJ1 ?_ ?_ τ
    · exact isHomogeneousOf_sub (isHomogeneousOf_add (hom_of 4 _) (hom_zmul 4 (hom_of 4 _)))
        (hom_zmul 5 hom_gZ2)
    · intro n hn
      exact (low_coeffs n (by omega)).1
  · refine gradedEval_eq_zero_of_coeff (k := 6) (by norm_num) ⟨3, rfl⟩ hB gJ2 ?_ ?_ τ
    · exact isHomogeneousOf_add (isHomogeneousOf_sub (hom_zmul 2 (hom_of 6 _))
        (hom_zmul 3 hom_gZD)) (hom_zmul 7 hom_gZ3)
    · intro n hn
      exact (low_coeffs n (by omega)).2.1
  · refine gradedEval_eq_zero_of_coeff (k := 6) (by norm_num) ⟨3, rfl⟩ hB gJ3 ?_ ?_ τ
    · exact isHomogeneousOf_sub (isHomogeneousOf_sub (hom_zmul 16 (hom_of 6 _))
        (hom_zmul 7 hom_gZ3)) (hom_zmul 3 hom_gZD)
    · intro n hn
      exact (low_coeffs n (by omega)).2.2

/-- `E₄(τ) + 4E₄(2τ) = 5Z(τ)²`. -/
theorem level2_E4_sum (τ : ℍ) :
    E4 τ + 4 * E4 (scaleGL 2 • τ) = 5 * level2Z τ ^ 2 := by
  have h := (gJ_eval τ).1
  simp only [gJ1, gE, gF, gZ, map_add, map_sub, map_mul, map_pow, map_intCast, gradedOf,
    gradedEvalAtOf_of, E4Level_apply, E4Scaled_apply] at h
  push_cast at h
  linear_combination h

/-- `2E₆(τ) = 3Z(4E₄(2τ) − E₄(τ)) − 7Z³`. -/
theorem level2_E6 (τ : ℍ) :
    2 * E6 τ = 3 * level2Z τ * (4 * E4 (scaleGL 2 • τ) - E4 τ) - 7 * level2Z τ ^ 3 := by
  have h := (gJ_eval τ).2.1
  simp only [gJ2, gE, gF, gZ, gE6, map_add, map_sub, map_mul, map_pow, map_intCast, gradedOf,
    gradedEvalAtOf_of, E4Level_apply, E4Scaled_apply, E6Level_apply] at h
  push_cast at h
  linear_combination h

/-- `16E₆(2τ) = 7Z³ + 3Z(4E₄(2τ) − E₄(τ))`. -/
theorem level2_E6_two (τ : ℍ) :
    16 * E6 (scaleGL 2 • τ) =
      7 * level2Z τ ^ 3 + 3 * level2Z τ * (4 * E4 (scaleGL 2 • τ) - E4 τ) := by
  have h := (gJ_eval τ).2.2
  simp only [gJ3, gE, gF, gZ, gF6, map_sub, map_mul, map_pow, map_intCast, gradedOf,
    gradedEvalAtOf_of, E4Level_apply, E4Scaled_apply, E6Scaled_apply] at h
  push_cast at h
  linear_combination h

end Modular
end Number
end Ripple
