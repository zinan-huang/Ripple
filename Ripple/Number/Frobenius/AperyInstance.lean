import Ripple.Number.Frobenius.Falling
import Ripple.Number.Frobenius.Substitution
import Ripple.Number.AperyConifoldIndicial
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Frobenius framework — validation against the Apéry conifold

The concrete indicial polynomial `aperyConifoldIndicial` defined in
`Ripple/Number/AperyConifoldIndicial.lean` was written by hand from the
Apéry-GF ODE. This file exhibits it as a specialisation of the general
`indicialPolyFalling` construction, with coefficient sequence

```
bs 0 = 0
bs 1 = 0
bs 2 = q(z₁)      -- y'' -coefficient at the conifold
bs 3 = p'(z₁)     -- derivative of p at the conifold
```

This serves as a sanity check that the abstract framework is faithful to
the concrete Apéry case, and as a stepping stone for refactoring
`AperyBounded.lean` to invoke the framework rather than the hand-written
polynomial.
-/

namespace Ripple
namespace Number.Frobenius

/-- Coefficient sequence extracted from the Apéry conifold-ODE
leading behaviour: `bs 2 = q(z₁)`, `bs 3 = p'(z₁)`, and all other
values zero. -/
noncomputable def aperyConifoldFallingCoeffs : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold
  | 3 => Polynomial.eval Number.aperyConifoldZ1Poly
           (Polynomial.derivative Number.aperyPconifold)
  | _ + 4 => 0

@[simp] lemma aperyConifoldFallingCoeffs_zero :
    aperyConifoldFallingCoeffs 0 = 0 := rfl

@[simp] lemma aperyConifoldFallingCoeffs_one :
    aperyConifoldFallingCoeffs 1 = 0 := rfl

@[simp] lemma aperyConifoldFallingCoeffs_two :
    aperyConifoldFallingCoeffs 2 =
      Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold := rfl

@[simp] lemma aperyConifoldFallingCoeffs_three :
    aperyConifoldFallingCoeffs 3 =
      Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold) := rfl

/-- **Validation.** The hand-written `aperyConifoldIndicial` coincides
with the general `indicialPolyFalling` specialised to the Apéry
coefficient sequence. -/
theorem aperyConifoldIndicial_eq_indicialPolyFalling (ρ : ℝ) :
    Number.aperyConifoldIndicial ρ =
      indicialPolyFalling aperyConifoldFallingCoeffs 3 ρ := by
  unfold Number.aperyConifoldIndicial indicialPolyFalling
  rw [show (3 + 1 : ℕ) = 4 from rfl]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
  simp [fallingFactorial, aperyConifoldFallingCoeffs]
  ring

/-- **Apéry ≡ `aperyPatternIndicialPoly`.** Running the abstract
Apéry-pattern indicial-polynomial formula from `Substitution.lean` on the
Apéry conifold polynomials `p(z) = z²−34z³+z⁴` and `q(z) = 3z−153z²+6z³`
returns exactly the hand-written `Number.aperyConifoldIndicial`. -/
theorem aperyConifoldIndicial_eq_aperyPatternIndicialPoly (ρ : ℝ) :
    Number.aperyConifoldIndicial ρ =
      aperyPatternIndicialPoly Number.aperyQconifold Number.aperyPconifold
        Number.aperyConifoldZ1Poly ρ := by
  rw [aperyPatternIndicialPoly_eq]
  unfold Number.aperyConifoldIndicial
  ring

/-- **Corollary — Apéry indicial classification via the general framework.**

If a formal series `g` has nonzero constant term and the falling-Euler
sum with the Apéry coefficient sequence vanishes at leading order, then
`ρ` is one of the three Apéry indicial exponents `{0, 1/2, 1}`.

This is the same classification as `Number.aperyConifold_indicial_exponents_are_roots`,
but now obtained by closing the general framework against the concrete
Apéry coefficients rather than by a hand-written proof. -/
theorem aperyConifold_indicial_roots_via_framework
    {ρ : ℝ} {g : PowerSeries ℝ}
    (hg : PowerSeries.coeff (R := ℝ) 0 g ≠ 0)
    (hvanish : PowerSeries.coeff (R := ℝ) 0
        (∑ j ∈ Finset.range 4,
          aperyConifoldFallingCoeffs j • fallingEulerOp ρ j g) = 0) :
    ρ = 0 ∨ ρ = (1 / 2 : ℝ) ∨ ρ = 1 := by
  have h1 : indicialPolyFalling aperyConifoldFallingCoeffs 3 ρ = 0 := by
    simpa using
      indicial_root_of_leading_vanish_falling
        aperyConifoldFallingCoeffs 3 ρ g hg hvanish
  have h2 : Number.aperyConifoldIndicial ρ = 0 := by
    rw [aperyConifoldIndicial_eq_indicialPolyFalling]; exact h1
  exact (Number.aperyConifoldIndicial_eq_zero_iff ρ).mp h2

/-- **Apéry-pattern indicial polynomial: root classification.** On the
concrete Apéry polynomials, `aperyPatternIndicialPoly` vanishes exactly
at the three Frobenius exponents `{0, 1/2, 1}`. -/
theorem aperyPatternIndicialPoly_apery_eq_zero_iff (ρ : ℝ) :
    aperyPatternIndicialPoly Number.aperyQconifold Number.aperyPconifold
        Number.aperyConifoldZ1Poly ρ = 0 ↔
      ρ = 0 ∨ ρ = (1 / 2 : ℝ) ∨ ρ = 1 := by
  rw [← aperyConifoldIndicial_eq_aperyPatternIndicialPoly]
  exact Number.aperyConifoldIndicial_eq_zero_iff ρ

/-- **Apéry substitution ⇒ indicial roots.** For Apéry's concrete
polynomials `p(z) = z² − 34z³ + z⁴` and `q(z) = 3z − 153z² + 6z³` at
`z₁ = 17 − 12√2`, if a formal series `g` with nonzero constant term
makes the `t^{ρ-2}` coefficient of the substituted ODE vanish, then
`ρ ∈ {0, 1/2, 1}`. This is the full Frobenius-framework closure of the
Apéry indicial classification: substitution bridge + root dictionary. -/
theorem apery_substLHS_vanish_forces_indicial_root
    (p0 p1 : Polynomial ℝ) {ρ : ℝ} {g : PowerSeries ℝ}
    (hg : PowerSeries.coeff (R := ℝ) 0 g ≠ 0)
    (hvanish : PowerSeries.coeff (R := ℝ) 1
        (substLHS p0 p1 Number.aperyQconifold Number.aperyPconifold
          Number.aperyConifoldZ1Poly ρ g) = 0) :
    ρ = 0 ∨ ρ = (1 / 2 : ℝ) ∨ ρ = 1 := by
  have hp3 : Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyPconifold = 0 :=
    Number.aperyPconifold_eval_z1
  have hbridge := coeff_one_substLHS p0 p1 Number.aperyQconifold Number.aperyPconifold
    Number.aperyConifoldZ1Poly ρ g hp3
  rw [hvanish] at hbridge
  have hind : aperyPatternIndicialPoly Number.aperyQconifold
      Number.aperyPconifold Number.aperyConifoldZ1Poly ρ = 0 :=
    (mul_eq_zero.mp hbridge.symm).resolve_right hg
  exact (aperyPatternIndicialPoly_apery_eq_zero_iff ρ).mp hind

/-! ## Non-resonance (no-integer-shift) for Apéry indicial roots

The Apéry conifold indicial polynomial vanishes exactly at the three
Frobenius exponents `{0, 1/2, 1}`. For the two irrational/half-integer
roots `ρ = 1/2` and `ρ = 1`, the shifted values `ρ + m` for positive
integers `m` are bounded away from this three-element set, so the
Frobenius recurrence is non-resonant at these exponents.

This unlocks `substLHSGen_solution_unique` for the `3/2`-order and
unit-order Frobenius branches at the Apéry conifold. -/

open PowerSeries in
/-- **Non-resonance at `ρ = 1/2`.** For every `m ≥ 1`, the simple-zero
indicial polynomial does not vanish at `1/2 + m`, because
`1/2 + m ≥ 3/2` is outside the root set `{0, 1/2, 1}`. -/
theorem apery_no_integer_shift_half :
    ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly Number.aperyQconifold Number.aperyPconifold
          Number.aperyConifoldZ1Poly 2 ((1 / 2 : ℝ) + m) ≠ 0 := by
  intro m hm
  rw [← aperyPatternIndicialPoly_eq_simpleZero]
  intro hzero
  rcases (aperyPatternIndicialPoly_apery_eq_zero_iff _).mp hzero with h | h | h
  · have : (m : ℝ) ≥ 1 := by exact_mod_cast hm
    linarith
  · have : (m : ℝ) ≥ 1 := by exact_mod_cast hm
    linarith
  · have : (m : ℝ) ≥ 1 := by exact_mod_cast hm
    linarith

open PowerSeries in
/-- **Non-resonance at `ρ = 1`.** For every `m ≥ 1`, the simple-zero
indicial polynomial does not vanish at `1 + m`, because `1 + m ≥ 2` is
outside the root set `{0, 1/2, 1}`. -/
theorem apery_no_integer_shift_one :
    ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly Number.aperyQconifold Number.aperyPconifold
          Number.aperyConifoldZ1Poly 2 ((1 : ℝ) + m) ≠ 0 := by
  intro m hm
  rw [← aperyPatternIndicialPoly_eq_simpleZero]
  intro hzero
  rcases (aperyPatternIndicialPoly_apery_eq_zero_iff _).mp hzero with h | h | h
  · have : (m : ℝ) ≥ 1 := by exact_mod_cast hm
    linarith
  · have : (m : ℝ) ≥ 1 := by exact_mod_cast hm
    linarith
  · have : (m : ℝ) ≥ 1 := by exact_mod_cast hm
    linarith

open PowerSeries in
/-- **Apéry Frobenius uniqueness at `ρ = 1/2`.** Two formal power
series that share a constant term and both annihilate every positive
coefficient of the Apéry substitution at exponent `ρ = 1/2` must
coincide. This is the non-resonant branch that carries the classical
`3/2`-order Apéry asymptotic. -/
theorem apery_frobenius_unique_half
    {g g' : PowerSeries ℝ}
    (hg : ∀ m : ℕ, coeff (R := ℝ) (m + 1)
        (substLHSGen (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
          3 Number.aperyConifoldZ1Poly (1 / 2 : ℝ) g) = 0)
    (hg' : ∀ m : ℕ, coeff (R := ℝ) (m + 1)
        (substLHSGen (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
          3 Number.aperyConifoldZ1Poly (1 / 2 : ℝ) g') = 0)
    (h0 : coeff (R := ℝ) 0 g = coeff (R := ℝ) 0 g') :
    g = g' := by
  have hpk : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold 3).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  exact substLHSGen_solution_unique _ 2 Number.aperyConifoldZ1Poly (1 / 2) g g'
    hpk apery_no_integer_shift_half hg hg' h0

open PowerSeries in
/-- **Apéry Frobenius uniqueness at `ρ = 1`.** The unit-order Frobenius
branch at the Apéry conifold is also non-resonant and therefore uniquely
determined by its constant term. -/
theorem apery_frobenius_unique_one
    {g g' : PowerSeries ℝ}
    (hg : ∀ m : ℕ, coeff (R := ℝ) (m + 1)
        (substLHSGen (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
          3 Number.aperyConifoldZ1Poly (1 : ℝ) g) = 0)
    (hg' : ∀ m : ℕ, coeff (R := ℝ) (m + 1)
        (substLHSGen (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
          3 Number.aperyConifoldZ1Poly (1 : ℝ) g') = 0)
    (h0 : coeff (R := ℝ) 0 g = coeff (R := ℝ) 0 g') :
    g = g' := by
  have hpk : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold 3).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  exact substLHSGen_solution_unique _ 2 Number.aperyConifoldZ1Poly 1 g g'
    hpk apery_no_integer_shift_one hg hg' h0

/-! ## Existence of the Apéry Frobenius branches

Using the general `frobeniusSolution_is_solution`, we now package
existence witnesses for the two non-resonant Apéry branches `ρ = 1/2`
and `ρ = 1`. Together with the uniqueness theorems above, the local
Frobenius theory at the Apéry conifold is complete for both
half-integer and unit-order branches.

The resonant branch `ρ = 0` requires the logarithmic case
(STRATEGY.md Step 4) and is not covered here. -/

private lemma apery_simpleZero_eq_half_zero :
    simpleZeroIndicialPoly Number.aperyQconifold Number.aperyPconifold
        Number.aperyConifoldZ1Poly 2 (1 / 2 : ℝ) = 0 := by
  rw [← aperyPatternIndicialPoly_eq_simpleZero]
  exact (aperyPatternIndicialPoly_apery_eq_zero_iff _).mpr (Or.inr (Or.inl rfl))

private lemma apery_simpleZero_eq_one_zero :
    simpleZeroIndicialPoly Number.aperyQconifold Number.aperyPconifold
        Number.aperyConifoldZ1Poly 2 (1 : ℝ) = 0 := by
  rw [← aperyPatternIndicialPoly_eq_simpleZero]
  exact (aperyPatternIndicialPoly_apery_eq_zero_iff _).mpr (Or.inr (Or.inr rfl))

open PowerSeries in
/-- **Apéry Frobenius existence at `ρ = 1/2`.** For every chosen
constant term `c₀`, there is a formal power series with that constant
term annihilating every coefficient of the Apéry substitution at
exponent `ρ = 1/2`. Witness: `frobeniusSolution`. -/
theorem apery_frobenius_exists_half (c₀ : ℝ) :
    ∃ g : PowerSeries ℝ,
      coeff (R := ℝ) 0 g = c₀ ∧
      ∀ k, coeff (R := ℝ) k
          (substLHSGen (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
            3 Number.aperyConifoldZ1Poly (1 / 2 : ℝ) g) = 0 := by
  refine ⟨frobeniusSolution
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly (1 / 2 : ℝ) c₀, ?_⟩
  exact frobeniusSolution_is_solution _ 2 _ _ c₀
    Number.aperyPconifold_eval_z1 apery_simpleZero_eq_half_zero
    apery_no_integer_shift_half

open PowerSeries in
/-- **Apéry Frobenius existence at `ρ = 1`.** For every chosen constant
term `c₀`, there is a formal power series with that constant term
annihilating every coefficient of the Apéry substitution at exponent
`ρ = 1`. Witness: `frobeniusSolution`. -/
theorem apery_frobenius_exists_one (c₀ : ℝ) :
    ∃ g : PowerSeries ℝ,
      coeff (R := ℝ) 0 g = c₀ ∧
      ∀ k, coeff (R := ℝ) k
          (substLHSGen (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
            3 Number.aperyConifoldZ1Poly (1 : ℝ) g) = 0 := by
  refine ⟨frobeniusSolution
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly (1 : ℝ) c₀, ?_⟩
  exact frobeniusSolution_is_solution _ 2 _ _ c₀
    Number.aperyPconifold_eval_z1 apery_simpleZero_eq_one_zero
    apery_no_integer_shift_one

/-! ## Pointwise analytic ODE at the Apéry conifold (ρ = 1 branch)

Instantiate `pointwise_substLHS_analytic_apery_shape` on the concrete
Apéry polynomials. Indicial and non-resonance hypotheses are discharged
by `apery_simpleZero_eq_one_zero` and `apery_no_integer_shift_one`; the
`p_0 = p_1 = 0` hypothesis is definitional on `aperyPsSeq 0 0 Q P`. The
only free hypothesis is the radius-of-convergence summability `hg_abs`,
which must be produced by a subsequent coefficient-growth estimate
(future work: concrete `s` bound from the general
`frobeniusCoeff_*_abs_mul_pow_summable` lemmas).

The conclusion is the Apéry conifold ODE on the closed disk `|t| ≤ s`:
  `t · Q(t+z₁) · I₂(t) = P(t+z₁) · I₃(t)`,
where `z₁ = 17 − 12√2` and `Iⱼ(t) := Σ' m, fallingFactorial (1+m) j ·
aₘ · tᵐ` with `aₘ = frobeniusCoeff … m`. -/

open PowerSeries in
theorem apery_conifold_pointwise_ODE_at_rho_one
    (c₀ : ℝ) (s : ℝ)
    (hg_abs : ∀ j ∈ Finset.range 4, Summable (fun m : ℕ =>
        |fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) j| *
          |frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ m| *
          s ^ m))
    (t : ℝ) (ht_abs : |t| ≤ s) :
    t * (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t *
        (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 2 *
          frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ m * t ^ m) =
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
        ∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 3 *
          frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ m * t ^ m := by
  have hps0 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 0 = 0 :=
    rfl
  have hps1 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 1 = 0 :=
    rfl
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3).eval
      Number.aperyConifoldZ1Poly = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hindicial :
      simpleZeroIndicialPoly
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2)
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3)
        Number.aperyConifoldZ1Poly 2 (1 : ℝ) = 0 := by
    rw [hps2, hps3]; exact apery_simpleZero_eq_one_zero
  have hnr : ∀ m : ℕ, 1 ≤ m →
      simpleZeroIndicialPoly
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2)
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3)
        Number.aperyConifoldZ1Poly 2 ((1 : ℝ) + (m : ℝ)) ≠ 0 := by
    intro m hm; rw [hps2, hps3]; exact apery_no_integer_shift_one m hm
  have hmain := pointwise_substLHS_analytic_apery_shape
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
    Number.aperyConifoldZ1Poly c₀ hps0 hps1 hpk hindicial hnr s hg_abs t ht_abs
  rw [hps2, hps3] at hmain
  exact hmain

open PowerSeries in
/-- **Apéry conifold ODE, no free summability** (ρ=1 branch). The
hypothesis `hg_abs` of `apery_conifold_pointwise_ODE_at_rho_one` is
discharged internally via the `_general` summability chain, which
accepts `Q(z₁) ≠ 0` through a threshold condition
(`2|Q(z₁)| ≤ |p'(z₁)|·(m+1 − |ρ| − n)` for all `m ≥ M₀`). For Apéry
(ρ=1, n=2) the threshold reduces to
`m + 1 ≥ 3 + 2|Q(z₁)|/|p'(z₁)|`, i.e.
`M₀ ≥ 3 + 2|Q(z₁)|/|p'(z₁)| − 1`. -/
theorem apery_conifold_pointwise_ODE_at_rho_one_of_threshold
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) :
    t * (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t *
        (∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 2 *
          frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ m * t ^ m) =
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
        ∑' m : ℕ, fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) 3 *
          frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ m * t ^ m := by
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk' : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3)).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3)).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B := by
    intro j' hj' ℓ
    exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3)).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]; exact hs_lt
  have hg_abs : ∀ j ∈ Finset.range 4, Summable (fun m : ℕ =>
      |fallingFactorial ((1 : ℝ) + ((m : ℕ) : ℝ)) j| *
        |frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ m| *
        s ^ m) := by
    intro j _
    exact frobeniusCoeff_fallingFactorial_shift_one_abs_mul_pow_summable_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
      2 Number.aperyConifoldZ1Poly 1 c₀ M₀ j
      hpk' hslope' hM0_small' hM0_large' hM0_thresh' B hB_nn hB' s hs_nn hs_lt'
  exact apery_conifold_pointwise_ODE_at_rho_one c₀ s hg_abs t ht_abs

open PowerSeries in
/-- **Apéry conifold pure ODE form at ρ = 1.**

Substituting the shift-one Euler bridges
`Σ' (1+m)(m)·a·tᵐ = t²·V'' + 2t·V'`,
`Σ' (1+m)(m)(m-1)·a·tᵐ = t³·V''' + 3t²·V''`
into the discharged tsum identity
`t·Q_sh(t)·I₂ = P_sh(t)·I₃`
gives `t²·(Q_sh·(t·V''+2·V') − P_sh·(t·V'''+3·V'')) = 0`. Cancelling `t²`
for `t ≠ 0` yields the pure ODE relation
`Q_sh(t)·(t·V''(t)+2·V'(t)) = P_sh(t)·(t·V'''(t)+3·V''(t))`.

Recognising `(t·V''+2·V') = (t·V)''` and `(t·V'''+3·V'') = (t·V)'''`,
this is the second/third-order ODE for the ρ=1 Frobenius local solution
`y(t) = t·V(t)`. -/
theorem apery_conifold_pure_ODE_at_rho_one
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_abs : |t| ≤ s) (ht_ne : t ≠ 0) :
    (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t *
        (t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + 2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t) =
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
        (t * frobeniusValueDeriv3 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + 3 * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t) := by
  -- Shorthands
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  set Q := Number.aperyQconifold with hQ_def
  set P := Number.aperyPconifold with hP_def
  -- Discharged tsum identity.
  have hraw := apery_conifold_pointwise_ODE_at_rho_one_of_threshold
    c₀ M₀ B hB_nn hM0_small hM0_large hM0_thresh hB s hs_nn hs_lt t ht_abs
  -- Recover the _general hypotheses for the shift-one bridges.
  have hps2 : ps 2 = Q := rfl
  have hps3 : ps 3 = P := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ
    exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]; exact hs_lt
  -- Apply shift-one bridges to the two tsums.
  have hI2 := frobeniusValueDeriv_tsum_euler_shift_one_two_general
    ps 2 z₁ 1 c₀ M₀ hpk' hslope' hM0_small' hM0_large' hM0_thresh'
    B hB_nn hB' s hs_nn hs_lt' t ht_abs
  have hI3 := frobeniusValueDeriv_tsum_euler_shift_one_three_general
    ps 2 z₁ 1 c₀ M₀ hpk' hslope' hM0_small' hM0_large' hM0_thresh'
    B hB_nn hB' s hs_nn hs_lt' t ht_abs
  -- Substitute and clear t².
  rw [hI2, hI3] at hraw
  -- hraw : t·Q·(t²V'' + 2tV') = P·(t³V''' + 3t²V'')
  -- Goal :   Q·(tV'' + 2V') = P·(tV''' + 3V'')
  have ht2_pos : (0 : ℝ) < t ^ 2 := by positivity
  have ht2_ne : (t ^ 2) ≠ 0 := ne_of_gt ht2_pos
  have hexpand :
      (taylorShift Q z₁).eval t *
          (t * frobeniusValueDeriv2 ps 2 z₁ 1 c₀ t
            + 2 * frobeniusValueDeriv ps 2 z₁ 1 c₀ t)
        - (taylorShift P z₁).eval t *
          (t * frobeniusValueDeriv3 ps 2 z₁ 1 c₀ t
            + 3 * frobeniusValueDeriv2 ps 2 z₁ 1 c₀ t) = 0 := by
    have key :
        t ^ 2 * ((taylorShift Q z₁).eval t *
          (t * frobeniusValueDeriv2 ps 2 z₁ 1 c₀ t
            + 2 * frobeniusValueDeriv ps 2 z₁ 1 c₀ t)
        - (taylorShift P z₁).eval t *
          (t * frobeniusValueDeriv3 ps 2 z₁ 1 c₀ t
            + 3 * frobeniusValueDeriv2 ps 2 z₁ 1 c₀ t)) = 0 := by
      have := hraw
      linarith [this, sq_nonneg t]
    exact (mul_left_cancel₀ ht2_ne (by linarith [key] : t ^ 2 * _ = t ^ 2 * 0))
  linarith [hexpand]

/-!
## Apéry ρ=1 local Frobenius solution `y(t) := t · V(t)`

The pure ODE
`Q_sh(t)·(t·V'' + 2·V') = P_sh(t)·(t·V''' + 3·V'')`
becomes, in terms of `y(t) := t · V(t)`, the cleaner statement
`Q_sh(t) · y''(t) = P_sh(t) · y'''(t)`,
once we prove `y'' = 2·V' + t·V''` and `y''' = 3·V'' + t·V'''`.

The first three derivatives of `y` are computed by `(hasDerivAt_id t).mul`
composed with the V→V', V'→V'', V''→V''' general HasDerivAt lifts.
-/

/-- The ρ=1 Apéry local Frobenius solution at the conifold:
`y(t) := t · V(t)` where `V(t)` is the formal Frobenius value. -/
noncomputable def yApery (c₀ : ℝ) (t : ℝ) : ℝ :=
  t * frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
    Number.aperyConifoldZ1Poly 1 c₀ t

/-- **Apéry Frobenius solution is ℝ-linear in the indicial leading term.**
Direct consequence of `frobeniusValue_smul_c₀` lifted through the `t·V`
factor. The simple-zero hypothesis is supplied by
`Number.aperyPconifold_eval_z1`. -/
lemma yApery_smul_c₀ (c c₀ t : ℝ) :
    yApery (c * c₀) t = c * yApery c₀ t := by
  unfold yApery
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  rw [frobeniusValue_smul_c₀ _ 2 _ 1 c c₀ hpk t]
  ring

/-- The ρ=0 Apéry local Frobenius solution at the conifold:
`y(t) := V(t)` with no leading `t^ρ` factor (since `t^0 = 1`).  Real-
valued for all `t` since the Frobenius series has real coefficients. -/
noncomputable def yAperyZero (c₀ : ℝ) (t : ℝ) : ℝ :=
  frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
    Number.aperyConifoldZ1Poly 0 c₀ t

/-- The ρ=0 branch is ℝ-linear in the indicial leading term. -/
lemma yAperyZero_smul_c₀ (c c₀ t : ℝ) :
    yAperyZero (c * c₀) t = c * yAperyZero c₀ t := by
  unfold yAperyZero
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  exact frobeniusValue_smul_c₀ _ 2 _ 0 c c₀ hpk t

/-- The ρ=1/2 Apéry local Frobenius solution at the conifold, evaluated
on the negative-`t` corridor. The leading factor `t^(1/2)` is interpreted
as `√(−t)` (the standard real-analytic continuation for `t < 0`).
For the Apéry boundary corridor `[z₁−1, −ε] ⊂ (−∞, 0)` this is real-
valued. -/
noncomputable def yAperyHalf (c₀ : ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (-t) * frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) c₀ t

/-- The ρ=1/2 branch is ℝ-linear in the indicial leading term. -/
lemma yAperyHalf_smul_c₀ (c c₀ t : ℝ) :
    yAperyHalf (c * c₀) t = c * yAperyHalf c₀ t := by
  unfold yAperyHalf
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  rw [frobeniusValue_smul_c₀ _ 2 _ (1 / 2) c c₀ hpk t]
  ring

/-- **Apéry y₂ functional is ℝ-linear in the indicial leading term.**
The functional `y₂(c₀, t) := 2·V'(c₀,t) + t·V''(c₀,t)` (the second-order
combination that participates in the linear ODE
`y₂'(t) = (Q_sh/P_sh)(t) · y₂(t)`) is ℝ-linear in `c₀`. Direct
consequence of `frobeniusValueDeriv_smul_c₀` and
`frobeniusValueDeriv2_smul_c₀`. -/
lemma yApery_y2_smul_c₀ (c c₀ t : ℝ) :
    2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 (c * c₀) t
        + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 (c * c₀) t =
      c * (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t) := by
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  rw [frobeniusValueDeriv_smul_c₀ _ 2 _ 1 c c₀ hpk t,
      frobeniusValueDeriv2_smul_c₀ _ 2 _ 1 c c₀ hpk t]
  ring

/-- **ρ=0 branch y₂ functional ℝ-linear in seed.** The same `2V' + t·V''`
combinator at indicial root `0`. Direct corollary of the smul lemmas on
`frobeniusValueDeriv` and `frobeniusValueDeriv2`. -/
lemma yAperyZero_y2_smul_c₀ (c c₀ t : ℝ) :
    2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 (c * c₀) t
        + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 (c * c₀) t =
      c * (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 c₀ t) := by
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  rw [frobeniusValueDeriv_smul_c₀ _ 2 _ 0 c c₀ hpk t,
      frobeniusValueDeriv2_smul_c₀ _ 2 _ 0 c c₀ hpk t]
  ring

/-! ## Three-branch superposition

The conifold ODE has three Frobenius branches indexed by the indicial roots
`{0, 1/2, 1}`. The natural object on the Apéry corridor is therefore the
*triple* `(c₀, c_half, c₁) ∈ ℝ³` of branch seeds, producing a superposed
solution

  `Y(c₀, c_half, c₁; t) = yAperyZero c₀ t + yAperyHalf c_half t + yApery c₁ t`.

Below we record the basic scalar linearity. Once specific connection
coefficients matching the analytic-at-`z=0` continuation are pinned down,
this packaging is what feeds into the Layer-4 RTCRN packaging. -/

/-- The three-branch superposed Frobenius solution on the Apéry corridor:
indexed by a seed triple `(c₀, c_half, c₁)`, returns the pointwise sum of
the three indicial-branch Frobenius solutions. -/
noncomputable def aperyBranchTriple
    (c₀ c_half c₁ t : ℝ) : ℝ :=
  yAperyZero c₀ t + yAperyHalf c_half t + yApery c₁ t

/-- Uniform scalar smul: scaling the entire seed triple by `c` scales the
combined solution by `c` at every `t`. Direct corollary of the three
branchwise `_smul_c₀` lemmas. -/
lemma aperyBranchTriple_smul (c c₀ c_half c₁ t : ℝ) :
    aperyBranchTriple (c * c₀) (c * c_half) (c * c₁) t =
      c * aperyBranchTriple c₀ c_half c₁ t := by
  unfold aperyBranchTriple
  rw [yAperyZero_smul_c₀ c c₀ t,
      yAperyHalf_smul_c₀ c c_half t,
      yApery_smul_c₀ c c₁ t]
  ring

/-- Componentwise additivity: sum of two seed triples gives the pointwise
sum of their branch superpositions. Direct from the additivity of `+` in
`ℝ` together with the definitional unfolding. -/
lemma aperyBranchTriple_add
    (c₀₁ c_half₁ c₁₁ c₀₂ c_half₂ c₁₂ t : ℝ) :
    aperyBranchTriple c₀₁ c_half₁ c₁₁ t +
        aperyBranchTriple c₀₂ c_half₂ c₁₂ t =
      (yAperyZero c₀₁ t + yAperyZero c₀₂ t) +
      (yAperyHalf c_half₁ t + yAperyHalf c_half₂ t) +
      (yApery c₁₁ t + yApery c₁₂ t) := by
  unfold aperyBranchTriple
  ring

/-- **Seed-linearity (single branch).** Each branch evaluation factors
through scalar multiplication by `c`. -/
private lemma yApery_eq_smul_one (c t : ℝ) :
    yApery c t = c * yApery 1 t := by
  have := yApery_smul_c₀ c 1 t
  simpa using this

private lemma yAperyZero_eq_smul_one (c t : ℝ) :
    yAperyZero c t = c * yAperyZero 1 t := by
  have := yAperyZero_smul_c₀ c 1 t
  simpa using this

private lemma yAperyHalf_eq_smul_one (c t : ℝ) :
    yAperyHalf c t = c * yAperyHalf 1 t := by
  have := yAperyHalf_smul_c₀ c 1 t
  simpa using this

/-- **Seed-additivity of the branch triple.** Adding seeds adds branch
evaluations: `aperyBranchTriple (a + b) t = aperyBranchTriple a t +
aperyBranchTriple b t`. -/
lemma aperyBranchTriple_add_seeds
    (a₀ a_h a₁ b₀ b_h b₁ t : ℝ) :
    aperyBranchTriple (a₀ + b₀) (a_h + b_h) (a₁ + b₁) t =
      aperyBranchTriple a₀ a_h a₁ t + aperyBranchTriple b₀ b_h b₁ t := by
  unfold aperyBranchTriple
  rw [yAperyZero_eq_smul_one a₀ t, yAperyZero_eq_smul_one b₀ t,
      yAperyZero_eq_smul_one (a₀ + b₀) t,
      yAperyHalf_eq_smul_one a_h t, yAperyHalf_eq_smul_one b_h t,
      yAperyHalf_eq_smul_one (a_h + b_h) t,
      yApery_eq_smul_one a₁ t, yApery_eq_smul_one b₁ t,
      yApery_eq_smul_one (a₁ + b₁) t]
  ring

/-- The all-zero seed triple gives the zero solution at every `t`. -/
@[simp] lemma aperyBranchTriple_zero (t : ℝ) :
    aperyBranchTriple 0 0 0 t = 0 := by
  unfold aperyBranchTriple
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  have h0 : yAperyZero 0 t = 0 := by
    unfold yAperyZero; exact frobeniusValue_zero_seed _ 2 _ 0 hpk t
  have h_half : yAperyHalf 0 t = 0 := by
    unfold yAperyHalf
    rw [frobeniusValue_zero_seed _ 2 _ (1/2) hpk t]; ring
  have h1 : yApery 0 t = 0 := by
    unfold yApery
    rw [frobeniusValue_zero_seed _ 2 _ 1 hpk t]; ring
  rw [h0, h_half, h1]; ring

/-- **Triple value at `t = 0` extracts the ρ=0 seed.** At the conifold
point itself only the regular branch survives:
* `yAperyZero c₀ 0 = c₀` (from `frobeniusValue_zero`).
* `yAperyHalf c_half 0 = √0 · V_{1/2}(0; c_half) = 0`.
* `yApery c₁ 0 = 0 · V_{1}(0; c₁) = 0`.
Hence `aperyBranchTriple c₀ c_half c₁ 0 = c₀`. This is the first
component of branch independence: any annihilating triple must have
`c₀ = 0`. -/
@[simp] lemma aperyBranchTriple_at_zero (c₀ c_half c₁ : ℝ) :
    aperyBranchTriple c₀ c_half c₁ 0 = c₀ := by
  unfold aperyBranchTriple yAperyZero yAperyHalf yApery
  rw [frobeniusValue_zero, neg_zero, Real.sqrt_zero, zero_mul, zero_mul]
  ring

/-- **First-component independence.** If a seed triple annihilates the
combined branch sum at `t = 0`, then the regular-branch seed `c₀` must
vanish. Direct from `aperyBranchTriple_at_zero`. -/
lemma aperyBranchTriple_zero_at_zero_implies_c₀
    (c₀ c_half c₁ : ℝ)
    (h : aperyBranchTriple c₀ c_half c₁ 0 = 0) :
    c₀ = 0 := by
  have := aperyBranchTriple_at_zero c₀ c_half c₁
  linarith

/-- **Regular-branch projection.** Subtracting the regular branch from
the combined sum leaves exactly the singular pair (ρ=1/2 and ρ=1).
Algebraic identity from the definition of `aperyBranchTriple`. -/
lemma aperyBranchTriple_sub_regular (c₀ c_half c₁ t : ℝ) :
    aperyBranchTriple c₀ c_half c₁ t - yAperyZero c₀ t =
      yAperyHalf c_half t + yApery c₁ t := by
  unfold aperyBranchTriple
  ring

/-- **ρ=1 branch vanishes at the conifold (t=0).** The leading factor
`t` forces this irrespective of the Frobenius series content. -/
@[simp] lemma yApery_at_zero (c₁ : ℝ) : yApery c₁ 0 = 0 := by
  unfold yApery; ring

/-- **ρ=1/2 branch vanishes at the conifold (t=0).** Comes from the
leading `√(-t)` factor: `√(-0) = √0 = 0`. -/
@[simp] lemma yAperyHalf_at_zero (c_half : ℝ) : yAperyHalf c_half 0 = 0 := by
  unfold yAperyHalf; rw [neg_zero, Real.sqrt_zero]; ring

/-- **ρ=0 branch at the conifold equals the seed.** From
`frobeniusValue_zero`. -/
@[simp] lemma yAperyZero_at_zero (c₀ : ℝ) : yAperyZero c₀ 0 = c₀ := by
  unfold yAperyZero; exact frobeniusValue_zero _ _ _ _ _

/-- **ρ=1 branch desingularised**: dividing by the explicit `t` factor
recovers the underlying Frobenius series at indicial root `1`. -/
lemma yApery_div_t (c₁ t : ℝ) (ht : t ≠ 0) :
    yApery c₁ t / t =
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₁ t := by
  unfold yApery
  field_simp

/-- **ρ=1/2 branch desingularised on the negative axis**: dividing by
the explicit `√(-t)` factor recovers the underlying Frobenius series at
indicial root `1/2`.  Requires `t < 0` so `√(-t) > 0`. -/
lemma yAperyHalf_div_sqrt (c_half t : ℝ) (ht : t < 0) :
    yAperyHalf c_half t / Real.sqrt (-t) =
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) c_half t := by
  unfold yAperyHalf
  have h_pos : 0 < Real.sqrt (-t) := Real.sqrt_pos.mpr (neg_pos.mpr ht)
  field_simp

/-- **Triple value off-conifold from the seeds.** For `t < 0`, the
combined value decomposes into three Frobenius pieces with explicit
prefactors `1`, `√(-t)`, `t`. -/
lemma aperyBranchTriple_eq_decomp (c₀ c_half c₁ t : ℝ) :
    aperyBranchTriple c₀ c_half c₁ t =
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 c₀ t +
      Real.sqrt (-t) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) c_half t +
      t *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₁ t := by
  unfold aperyBranchTriple yAperyZero yAperyHalf yApery
  ring

/-- **Vanishing only on regular branch.** If only `c₀ ≠ 0` (and the
other two seeds are zero), the triple equals the regular Frobenius
series everywhere. -/
@[simp] lemma aperyBranchTriple_only_zero_branch (c₀ t : ℝ) :
    aperyBranchTriple c₀ 0 0 t = yAperyZero c₀ t := by
  unfold aperyBranchTriple
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  have h_half : yAperyHalf 0 t = 0 := by
    unfold yAperyHalf
    rw [frobeniusValue_zero_seed _ 2 _ (1/2) hpk t]; ring
  have h1 : yApery 0 t = 0 := by
    unfold yApery
    rw [frobeniusValue_zero_seed _ 2 _ 1 hpk t]; ring
  rw [h_half, h1]; ring

/-- **Triple with only ρ=1/2 seed reduces to ρ=1/2 branch.** -/
@[simp] lemma aperyBranchTriple_only_half_branch (c_half t : ℝ) :
    aperyBranchTriple 0 c_half 0 t = yAperyHalf c_half t := by
  unfold aperyBranchTriple
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  have h0 : yAperyZero 0 t = 0 := by
    unfold yAperyZero
    exact frobeniusValue_zero_seed _ 2 _ 0 hpk t
  have h1 : yApery 0 t = 0 := by
    unfold yApery
    rw [frobeniusValue_zero_seed _ 2 _ 1 hpk t]; ring
  rw [h0, h1]; ring

/-- **Triple with only ρ=1 seed reduces to ρ=1 branch.** -/
@[simp] lemma aperyBranchTriple_only_one_branch (c₁ t : ℝ) :
    aperyBranchTriple 0 0 c₁ t = yApery c₁ t := by
  unfold aperyBranchTriple
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  have h0 : yAperyZero 0 t = 0 := by
    unfold yAperyZero
    exact frobeniusValue_zero_seed _ 2 _ 0 hpk t
  have h_half : yAperyHalf 0 t = 0 := by
    unfold yAperyHalf
    rw [frobeniusValue_zero_seed _ 2 _ (1/2) hpk t]; ring
  rw [h0, h_half]; ring

/-- **Triple as componentwise sum of single-branch triples.** Direct
algebraic identity from the definition. -/
lemma aperyBranchTriple_split (c₀ c_half c₁ t : ℝ) :
    aperyBranchTriple c₀ c_half c₁ t =
      aperyBranchTriple c₀ 0 0 t +
      aperyBranchTriple 0 c_half 0 t +
      aperyBranchTriple 0 0 c₁ t := by
  rw [aperyBranchTriple_only_zero_branch,
      aperyBranchTriple_only_half_branch,
      aperyBranchTriple_only_one_branch]
  unfold aperyBranchTriple
  ring

/-- **Singular-pair desingularised on the negative axis.** After
subtracting the regular branch and dividing by `√(-t)`, the remaining
combination reads
`V_{1/2}(c_half, t) − √(-t) · V_1(c₁, t)`,
giving the algebraic skeleton for extracting `c_half` as the
limit `t → 0⁻` (deferred continuity machinery). -/
lemma aperyBranchTriple_singular_div_sqrt (c₀ c_half c₁ t : ℝ) (ht : t < 0) :
    (aperyBranchTriple c₀ c_half c₁ t - yAperyZero c₀ t) / Real.sqrt (-t) =
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) c_half t -
      Real.sqrt (-t) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₁ t := by
  rw [aperyBranchTriple_sub_regular]
  unfold yAperyHalf yApery
  have h_neg_nn : 0 ≤ -t := le_of_lt (neg_pos.mpr ht)
  have h_pos : 0 < Real.sqrt (-t) := Real.sqrt_pos.mpr (neg_pos.mpr ht)
  have h_ne : Real.sqrt (-t) ≠ 0 := ne_of_gt h_pos
  have h_sq : Real.sqrt (-t) * Real.sqrt (-t) = -t :=
    Real.mul_self_sqrt h_neg_nn
  set V_h := frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) c_half t
  set V_1 := frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₁ t
  rw [div_eq_iff h_ne]
  linear_combination (V_1 : ℝ) * h_sq

/-- **Singular branch desingularised by `t`.** After subtracting the
regular branch and dividing by `t`, the remaining combination reads
`V_1(c₁, t) + V_{1/2}(c_half, t) / √(-t) · (1/(-1))` … packaged here as
the explicit form `V_1(c₁, t) − V_{1/2}(c_half, t) / √(-t)` on `t < 0`,
the algebraic skeleton for extracting `c₁`. -/
lemma aperyBranchTriple_singular_div_t (c₀ c_half c₁ t : ℝ) (ht : t < 0) :
    (aperyBranchTriple c₀ c_half c₁ t - yAperyZero c₀ t) / t =
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₁ t +
      Real.sqrt (-t) / t *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) c_half t := by
  rw [aperyBranchTriple_sub_regular]
  unfold yAperyHalf yApery
  have ht_ne : t ≠ 0 := ne_of_lt ht
  field_simp
  ring

/-- First derivative of `y = t·V` is `V + t·V'`. -/
theorem yApery_hasDerivAt
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (yApery c₀)
      (frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
            2 Number.aperyConifoldZ1Poly 1 c₀ t
        + t * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t) t := by
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := rfl
  have hps2 : ps 2 = Number.aperyQconifold := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by
    rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm; have := hM0_small m hm; push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm; have := hM0_large m hm; push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ; exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]; exact hs_lt
  have hV := frobeniusValue_hasDerivAt_std_general ps 2 z₁ 1 c₀ M₀
    hpk' hslope' hM0_small' hM0_large' hM0_thresh'
    B hB_nn hB' s hs_pos hs_lt' t ht_mem
  have hid : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id t
  have hmul := hid.mul hV
  unfold yApery
  convert hmul using 1
  ring

/-- Second derivative of `y = t·V` is `2·V' + t·V''`. -/
theorem yApery_hasDerivAt_second
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun u => frobeniusValue
          (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
          2 Number.aperyConifoldZ1Poly 1 c₀ u
        + u * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u)
      (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
        + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t) t := by
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := rfl
  have hps2 : ps 2 = Number.aperyQconifold := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm; have := hM0_small m hm; push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm; have := hM0_large m hm; push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'; rw [hps2, hps3]
    have := hM0_thresh m' hm'; push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ; exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]; exact hs_lt
  have hV := frobeniusValue_hasDerivAt_std_general ps 2 z₁ 1 c₀ M₀
    hpk' hslope' hM0_small' hM0_large' hM0_thresh'
    B hB_nn hB' s hs_pos hs_lt' t ht_mem
  have hVd := frobeniusValueDeriv_hasDerivAt_general ps 2 z₁ 1 c₀ M₀
    hpk' hslope' hM0_small' hM0_large' hM0_thresh'
    B hB_nn hB' s hs_pos hs_lt' t ht_mem
  have hid : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id t
  have hsum := hV.add (hid.mul hVd)
  convert hsum using 1
  ring

/-- Third derivative of `y = t·V` is `3·V'' + t·V'''`. -/
theorem yApery_hasDerivAt_third
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) :
    HasDerivAt (fun u => 2 * frobeniusValueDeriv
          (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
          2 Number.aperyConifoldZ1Poly 1 c₀ u
        + u * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u)
      (3 * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
        + t * frobeniusValueDeriv3 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t) t := by
  set ps := aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold with hps_def
  set z₁ := Number.aperyConifoldZ1Poly with hz_def
  have hps3 : ps 3 = Number.aperyPconifold := rfl
  have hps2 : ps 2 = Number.aperyQconifold := rfl
  have hpk' : (ps 3).eval z₁ = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope' : (Polynomial.derivative (ps 3)).eval z₁ ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm; have := hM0_small m hm; push_cast at this ⊢; linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm; have := hM0_large m hm; push_cast at this ⊢; linarith
  have hM0_thresh' : ∀ m', M₀ ≤ m' →
      2 * |(ps 2).eval z₁| ≤
        |(Polynomial.derivative (ps 3)).eval z₁| *
          (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'; rw [hps2, hps3]
    have := hM0_thresh m' hm'; push_cast at this ⊢; linarith
  have hB' : ∀ j' ∈ Finset.range (2 + 2), ∀ ℓ : ℕ,
      |Polynomial.coeff (taylorShift (ps j') z₁) ℓ| ≤ B := by
    intro j' hj' ℓ; exact hB j' (by simp at hj' ⊢; omega) ℓ
  have hs_lt' : s * (1 + 2 * ((2 + 2 : ℕ) : ℝ) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative (ps 3)).eval z₁|) < 1 := by
    have h4 : ((2 + 2 : ℕ) : ℝ) = 4 := by norm_num
    have h21 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h4, h21, hps3]; exact hs_lt
  have hVd := frobeniusValueDeriv_hasDerivAt_general ps 2 z₁ 1 c₀ M₀
    hpk' hslope' hM0_small' hM0_large' hM0_thresh'
    B hB_nn hB' s hs_pos hs_lt' t ht_mem
  have hVdd := frobeniusValueDeriv2_hasDerivAt_general ps 2 z₁ 1 c₀ M₀
    hpk' hslope' hM0_small' hM0_large' hM0_thresh'
    B hB_nn hB' s hs_pos hs_lt' t ht_mem
  have hid : HasDerivAt (fun y : ℝ => y) 1 t := hasDerivAt_id t
  have hsum := (hVd.const_mul 2).add (hid.mul hVdd)
  convert hsum using 1
  ring

/-- Boundary value at `t = 0`: `y(0) = 0`. -/
@[simp] lemma yApery_zero (c₀ : ℝ) : yApery c₀ 0 = 0 := by
  unfold yApery; simp

/-- The derivative value at `t = 0`: `y'(0) = c₀`. This is the Frobenius
seed: with `ρ = 1`, the leading behaviour `y ~ c₀ · t` gives
`y'(0) = c₀`. -/
lemma yApery_deriv_at_zero
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    HasDerivAt (yApery c₀) c₀ 0 := by
  have h0_mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) s := Metric.mem_ball_self hs_pos
  have h := yApery_hasDerivAt c₀ M₀ B hB_nn hM0_small hM0_large hM0_thresh hB
    s hs_pos hs_lt 0 h0_mem
  have hVeq :
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
        2 Number.aperyConifoldZ1Poly 1 c₀ 0 +
      0 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ 0 = c₀ := by
    simp
  rw [hVeq] at h
  exact h

/-!
## Apéry conifold ρ=1 local Frobenius solution — packaged

Bundles the three HasDerivAt witnesses, the boundary conditions, and
the pure-ODE relation into a single existence theorem. The output
witnesses three derivative functions `y₁ y₂ y₃` such that

* `y(t)` has derivative `y₁ t` for every `t` in the convergence ball,
* `y₁` has derivative `y₂ t`,
* `y₂` has derivative `y₃ t`,
* `y(0) = 0`, `y₁(0) = c₀`,
* `Q_sh(t) · y₂(t) = P_sh(t) · y₃(t)` for every `t ≠ 0` in the ball.

This is the clean formal interface for the connection-coefficient step:
later work just consumes these six properties.
-/

theorem yApery_isLocalFrobeniusSolution
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    ∃ y₁ y₂ y₃ : ℝ → ℝ,
      (∀ t ∈ Metric.ball (0 : ℝ) s, HasDerivAt (yApery c₀) (y₁ t) t) ∧
      (∀ t ∈ Metric.ball (0 : ℝ) s, HasDerivAt y₁ (y₂ t) t) ∧
      (∀ t ∈ Metric.ball (0 : ℝ) s, HasDerivAt y₂ (y₃ t) t) ∧
      yApery c₀ 0 = 0 ∧
      y₁ 0 = c₀ ∧
      (∀ t ∈ Metric.ball (0 : ℝ) s, t ≠ 0 →
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t *
            y₂ t =
          (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
            y₃ t) := by
  refine ⟨fun t => frobeniusValue
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
      2 Number.aperyConifoldZ1Poly 1 c₀ t
    + t * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t,
    fun t => 2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
    + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t,
    fun t => 3 * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
    + t * frobeniusValueDeriv3 (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht_mem
    exact yApery_hasDerivAt c₀ M₀ B hB_nn hM0_small hM0_large hM0_thresh hB
      s hs_pos hs_lt t ht_mem
  · intro t ht_mem
    exact yApery_hasDerivAt_second c₀ M₀ B hB_nn hM0_small hM0_large hM0_thresh hB
      s hs_pos hs_lt t ht_mem
  · intro t ht_mem
    exact yApery_hasDerivAt_third c₀ M₀ B hB_nn hM0_small hM0_large hM0_thresh hB
      s hs_pos hs_lt t ht_mem
  · exact yApery_zero c₀
  · simp
  · intro t ht_mem ht_ne
    have ht_abs : |t| ≤ s := by
      rw [Metric.mem_ball, dist_zero_right] at ht_mem
      exact le_of_lt ht_mem
    have hs_nn : 0 ≤ s := le_of_lt hs_pos
    have hraw := apery_conifold_pure_ODE_at_rho_one c₀ M₀ B hB_nn
      hM0_small hM0_large hM0_thresh hB s hs_nn hs_lt t ht_abs ht_ne
    linarith [hraw]

/-!
## Conifold polynomial factorisation

The leading polynomial `P(z) = z² − 34 z³ + z⁴` of the Apéry ODE
factors at the conifold root `z₁ = 17 − 12√2` as
`P(z) = (z − z₁) · L(z)` for `L := P /ₘ (X − C z₁)`. Translating to
the shifted variable `t = z − z₁`,
`(taylorShift P z₁)(t) = −t · (taylorShift L z₁)(t)`,
and `L(z₁) = P'(z₁)` so the cofactor is non-zero at the conifold.

This factorisation is the structural input for both:
* the punctured-ball uniqueness argument (Picard on `0 < t < s` requires
  `(taylorShift P z₁)(t) ≠ 0`, i.e. `(taylorShift L z₁)(t) ≠ 0`),
* the connection-coefficient analysis (the local exponent of `P_sh` at
  `t = 0` is exactly `1`, matching the simple-zero indicial structure).
-/

/-- The cofactor `L = P /ₘ (X − C z₁)` of `aperyPconifold` after
removing the simple `(X − C z₁)` root. -/
noncomputable def aperyPconifoldQuotZ1 : Polynomial ℝ :=
  Number.aperyPconifold /ₘ (Polynomial.X - Polynomial.C Number.aperyConifoldZ1Poly)

/-- `aperyPconifold = (X − C z₁) · aperyPconifoldQuotZ1`. -/
lemma aperyPconifold_factor_z1 :
    Number.aperyPconifold =
      (Polynomial.X - Polynomial.C Number.aperyConifoldZ1Poly) *
      aperyPconifoldQuotZ1 := by
  unfold aperyPconifoldQuotZ1
  exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
    Number.aperyPconifold_eval_z1).symm

/-- The cofactor evaluated at `z₁` is `P'(z₁)`. Standard product rule:
`P = (z − z₁) · L` ⇒ `P'(z) = L(z) + (z − z₁) · L'(z)`, so `P'(z₁) = L(z₁)`. -/
lemma aperyPconifoldQuotZ1_eval_z1 :
    Polynomial.eval Number.aperyConifoldZ1Poly aperyPconifoldQuotZ1 =
      Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold) := by
  have hfact := aperyPconifold_factor_z1
  have hderiv := congrArg Polynomial.derivative hfact
  rw [Polynomial.derivative_mul] at hderiv
  have heval := congrArg (Polynomial.eval Number.aperyConifoldZ1Poly) hderiv
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C, sub_self,
    sub_zero, zero_mul, one_mul] at heval
  linarith [heval]

/-- The cofactor is non-zero at the conifold root, since
`L(z₁) = P'(z₁) ≠ 0`. -/
lemma aperyPconifoldQuotZ1_eval_z1_ne_zero :
    Polynomial.eval Number.aperyConifoldZ1Poly aperyPconifoldQuotZ1 ≠ 0 := by
  rw [aperyPconifoldQuotZ1_eval_z1]
  exact Number.aperyPconifold_deriv_eval_z1_ne_zero

/-- `taylorShift P z₁ = -X · taylorShift L z₁`. The minus sign comes from
the Jacobian `dz/dt = −1` of the change of variable `z = z₁ − t`. -/
lemma taylorShift_aperyPconifold_factor :
    taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly =
      (-Polynomial.X) * taylorShift aperyPconifoldQuotZ1
        Number.aperyConifoldZ1Poly := by
  conv_lhs => rw [aperyPconifold_factor_z1]
  rw [taylorShift_mul]
  congr 1
  unfold taylorShift
  simp [Polynomial.sub_comp]

/-- Pointwise: `(taylorShift P z₁)(t) = -t · (taylorShift L z₁)(t)`. -/
lemma taylorShift_aperyPconifold_eval (t : ℝ) :
    (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t =
      -t * (taylorShift aperyPconifoldQuotZ1
        Number.aperyConifoldZ1Poly).eval t := by
  rw [taylorShift_aperyPconifold_factor]
  simp [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_X]

/-- `(taylorShift L z₁)(0) = P'(z₁)`. Useful for the small-`t`
non-vanishing bound on the cofactor. -/
@[simp] lemma taylorShift_aperyPconifoldQuotZ1_eval_zero :
    (taylorShift aperyPconifoldQuotZ1
      Number.aperyConifoldZ1Poly).eval 0 =
      Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold) := by
  rw [taylorShift_eval_zero]
  exact aperyPconifoldQuotZ1_eval_z1

/-- The cofactor `L_sh(t)` is non-zero in a neighbourhood of `t = 0`,
since `L_sh(0) = P'(z₁) ≠ 0` and `L_sh` is continuous. -/
lemma exists_radius_taylorShift_aperyPconifoldQuotZ1_eval_ne_zero :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ →
      (taylorShift aperyPconifoldQuotZ1
        Number.aperyConifoldZ1Poly).eval t ≠ 0 := by
  set L := taylorShift aperyPconifoldQuotZ1 Number.aperyConifoldZ1Poly
  have hL0_ne : L.eval 0 ≠ 0 := by
    rw [taylorShift_aperyPconifoldQuotZ1_eval_zero]
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hev : ∀ᶠ t in nhds (0 : ℝ), L.eval t ≠ 0 :=
    L.continuous.continuousAt.eventually_ne hL0_ne
  rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hh⟩
  refine ⟨δ, hδ, fun t ht => hh ?_⟩
  rw [Real.dist_eq, sub_zero]; exact ht

/-- Punctured-ball non-vanishing of `P_sh(t)`: there is `δ > 0` such that
`(taylorShift P z₁)(t) ≠ 0` for every `t ≠ 0` with `|t| < δ`. This is
the input that lets the punctured-ball linear-ODE form
`y₂'(t) = (Q_sh / P_sh)(t) · y₂(t)` make sense. -/
lemma exists_radius_taylorShift_aperyPconifold_eval_ne_zero :
    ∃ δ > 0, ∀ t : ℝ, t ≠ 0 → |t| < δ →
      (taylorShift Number.aperyPconifold
        Number.aperyConifoldZ1Poly).eval t ≠ 0 := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    exists_radius_taylorShift_aperyPconifoldQuotZ1_eval_ne_zero
  refine ⟨δ, hδ_pos, ?_⟩
  intro t ht_ne ht_lt
  rw [taylorShift_aperyPconifold_eval]
  exact mul_ne_zero (neg_ne_zero.mpr ht_ne) (hδ t ht_lt)

/-!
## Punctured-ball linear ODE for `y₂`

On the punctured ball `{t : |t| < s, t ≠ 0, P_sh(t) ≠ 0}`, the pure
ODE `Q_sh(t) · y₂(t) = P_sh(t) · y₃(t)` plus the HasDerivAt witness
`y₂' = y₃` collapse to the first-order linear ODE
`y₂'(t) = (Q_sh / P_sh)(t) · y₂(t)`.
This is the standard Picard-Lindelöf entry: the right-hand side is
linear in `y₂` with continuous coefficient, so ODE_solution_unique
applies on any closed sub-interval avoiding `t = 0`.
-/

theorem yApery_y2_linear_ODE
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) (ht_ne : t ≠ 0)
    (hP_ne : (taylorShift Number.aperyPconifold
      Number.aperyConifoldZ1Poly).eval t ≠ 0) :
    HasDerivAt (fun u =>
        2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
        + u * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u)
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
        (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t))
      t := by
  have h2 := yApery_hasDerivAt_third c₀ M₀ B hB_nn hM0_small hM0_large
    hM0_thresh hB s hs_pos hs_lt t ht_mem
  have ht_abs : |t| ≤ s := by
    rw [Metric.mem_ball, dist_zero_right] at ht_mem
    exact le_of_lt ht_mem
  have hs_nn : 0 ≤ s := le_of_lt hs_pos
  have hODE := apery_conifold_pure_ODE_at_rho_one c₀ M₀ B hB_nn
    hM0_small hM0_large hM0_thresh hB s hs_nn hs_lt t ht_abs ht_ne
  -- Rewrite y₃(t) = (Q/P)(t) · y₂(t).
  have hy3_eq :
      3 * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
        + t * frobeniusValueDeriv3 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t =
      (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
        (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t) := by
    field_simp
    linarith [hODE]
  rw [hy3_eq] at h2
  exact h2

/-!
## Picard uniqueness on a positive sub-interval

On any closed interval `[a, b] ⊂ (0, s)` where `P_sh` is non-vanishing,
the linear ODE `y₂' = (Q_sh / P_sh) · y₂` has at most one solution with a
prescribed value at `a` (Picard–Lindelöf via Grönwall).
-/

theorem yApery_y2_unique_on_subinterval_pos
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (a b : ℝ) (ha_pos : 0 < a) (hab : a ≤ b) (hb_lt : b < s)
    (hP_ne : ∀ t ∈ Set.Icc a b,
      (taylorShift Number.aperyPconifold
        Number.aperyConifoldZ1Poly).eval t ≠ 0)
    (g : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_deriv : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t
        * g t)
      (Set.Ici t) t)
    (hg_init : g a =
      2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ a
        + a * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ a) :
    Set.EqOn g (fun t =>
        2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t)
      (Set.Icc a b) := by
  set Q_sh := taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly
    with hQ_sh_def
  set P_sh := taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly
    with hP_sh_def
  set f : ℝ → ℝ := fun t =>
    2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
      + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
    with hf_def
  let φ : ℝ → ℝ := fun u => Q_sh.eval u / P_sh.eval u
  let v : ℝ → ℝ → ℝ := fun u z => φ u * z
  -- Continuity of `φ` on `[a, b]` (uses non-vanishing of `P_sh`).
  have hφ_cont : ContinuousOn φ (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ hP_ne
    · exact (Q_sh.continuous).continuousOn
    · exact (P_sh.continuous).continuousOn
  -- Compactness gives a bound `K_val` on `|φ|`.
  have h_ab_ne : (Set.Icc a b).Nonempty := ⟨a, ⟨le_refl _, hab⟩⟩
  obtain ⟨u_max, _, hu_max⟩ :=
    isCompact_Icc.exists_isMaxOn h_ab_ne hφ_cont.abs
  set K_val : ℝ := |φ u_max| + 1 with hK_val_def
  have hK_nn : 0 ≤ K_val := by
    have h_abs : 0 ≤ |φ u_max| := abs_nonneg _
    linarith
  set K : NNReal := Real.toNNReal K_val with hK_def
  have hK_coe : (K : ℝ) = K_val := Real.coe_toNNReal K_val hK_nn
  have hφ_bdd : ∀ u ∈ Set.Icc a b, |φ u| ≤ K_val := by
    intro u hu
    have h_le : |φ u| ≤ |φ u_max| := hu_max hu
    change |φ u| ≤ |φ u_max| + 1
    linarith
  -- The vector field `v u` is `K`-Lipschitz on `Set.univ` for each `u`.
  have hv_lip : ∀ u ∈ Set.Ico a b, LipschitzOnWith K (v u) (Set.univ : Set ℝ) := by
    intro u hu
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z _ z' _
    rw [Real.dist_eq, Real.dist_eq, hK_coe]
    have h_exp : v u z - v u z' = φ u * (z - z') := by
      simp only [v]; ring
    rw [h_exp, abs_mul]
    have hu_in : u ∈ Set.Icc a b := ⟨hu.1, hu.2.le⟩
    have h_bound : |φ u| ≤ K_val := hφ_bdd u hu_in
    have h_diff_nn : 0 ≤ |z - z'| := abs_nonneg _
    nlinarith
  -- Continuity of `f` on `[a, b]`. We use the general continuity theorems for
  -- `frobeniusValueDeriv` and `frobeniusValueDeriv2` on `Icc (-s) s` and
  -- restrict via monotonicity.
  have hsubset : Set.Icc a b ⊆ Set.Icc (-s) s := by
    intro u hu
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) ≤ u := le_trans ha_pos.le hu.1
      linarith [hs_pos]
    · linarith [hu.2]
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by
    change Number.aperyPconifold.eval Number.aperyConifoldZ1Poly = 0
    exact Number.aperyPconifold_eval_z1
  have hslope :
      (Polynomial.derivative
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    change (Polynomial.derivative Number.aperyPconifold).eval
      Number.aperyConifoldZ1Poly ≠ 0
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hs_nn : 0 ≤ s := hs_pos.le
  have hV'_cont :
      ContinuousOn (fun t => frobeniusValueDeriv
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc (-s) s) :=
    frobeniusValueDeriv_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ M₀ hpk hslope
      hM0_small hM0_large hM0_thresh B hB_nn hB s hs_nn hs_lt
  have hV''_cont :
      ContinuousOn (fun t => frobeniusValueDeriv2
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc (-s) s) :=
    frobeniusValueDeriv2_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ M₀ hpk hslope
      hM0_small hM0_large hM0_thresh B hB_nn hB s hs_nn hs_lt
  have hV'_cont_ab : ContinuousOn (fun t => frobeniusValueDeriv
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc a b) := hV'_cont.mono hsubset
  have hV''_cont_ab : ContinuousOn (fun t => frobeniusValueDeriv2
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc a b) := hV''_cont.mono hsubset
  have hf_cont : ContinuousOn f (Set.Icc a b) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.mul hV'_cont_ab
    · exact continuousOn_id.mul hV''_cont_ab
  -- Each `u ∈ [a, b]` lies in `Metric.ball 0 s` and is non-zero,
  -- so `yApery_y2_linear_ODE` applies pointwise.
  have hf_within : ∀ u ∈ Set.Ico a b,
      HasDerivWithinAt f (v u (f u)) (Set.Ici u) u := by
    intro u hu
    have hu_pos : 0 < u := lt_of_lt_of_le ha_pos hu.1
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    have hu_lt : u < s := lt_trans hu.2 hb_lt
    have hu_mem : u ∈ Metric.ball (0 : ℝ) s := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
        abs_of_pos hu_pos]
      exact hu_lt
    have hP_ne_u : P_sh.eval u ≠ 0 :=
      hP_ne u ⟨hu.1, hu.2.le⟩
    have h_lin := yApery_y2_linear_ODE c₀ M₀ B hB_nn hM0_small hM0_large
      hM0_thresh hB s hs_pos hs_lt u hu_mem hu_ne hP_ne_u
    -- `v u (f u) = φ u * f u = (Q_sh/P_sh)(u) * f u`.
    have h_v_eq : v u (f u) =
        Q_sh.eval u / P_sh.eval u *
          (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
            + u * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u) := by
      simp only [v, φ, f]
    rw [h_v_eq]
    exact h_lin.hasDerivWithinAt
  -- Wrap `g` in the same form: `(Q/P) · g u = v u (g u)`.
  have hg_within : ∀ u ∈ Set.Ico a b,
      HasDerivWithinAt g (v u (g u)) (Set.Ici u) u := by
    intro u hu
    have h_v_eq : v u (g u) =
        Q_sh.eval u / P_sh.eval u * g u := by
      simp only [v, φ]
    rw [h_v_eq]
    exact hg_deriv u hu
  -- Universal containment.
  have hf_in : ∀ u ∈ Set.Ico a b, f u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  have hg_in : ∀ u ∈ Set.Ico a b, g u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  have h_init_eq : f a = g a := hg_init.symm
  have h_eq : Set.EqOn f g (Set.Icc a b) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hf_cont hf_within hf_in
      hg_cont hg_within hg_in h_init_eq
  exact h_eq.symm

/-- Right-anchored Picard uniqueness on a positive sub-interval `[a, b] ⊂ (0, s)`.
Same hypotheses as `yApery_y2_unique_on_subinterval_pos` but the anchor is at
the right endpoint `b`, and the derivative hypothesis uses left half-intervals
`Set.Iic t` (flowing leftward), via `ODE_solution_unique_of_mem_Icc_left`.
This is a building block for cross-zero glue. -/
theorem yApery_y2_unique_on_subinterval_pos_right
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (a b : ℝ) (ha_pos : 0 < a) (hab : a ≤ b) (hb_lt : b < s)
    (hP_ne : ∀ t ∈ Set.Icc a b,
      (taylorShift Number.aperyPconifold
        Number.aperyConifoldZ1Poly).eval t ≠ 0)
    (g : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_deriv : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt g
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t
        * g t)
      (Set.Iic t) t)
    (hg_init : g b =
      2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ b
        + b * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ b) :
    Set.EqOn g (fun t =>
        2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t)
      (Set.Icc a b) := by
  set Q_sh := taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly
    with hQ_sh_def
  set P_sh := taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly
    with hP_sh_def
  set f : ℝ → ℝ := fun t =>
    2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
      + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
    with hf_def
  let φ : ℝ → ℝ := fun u => Q_sh.eval u / P_sh.eval u
  let v : ℝ → ℝ → ℝ := fun u z => φ u * z
  have hφ_cont : ContinuousOn φ (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ hP_ne
    · exact (Q_sh.continuous).continuousOn
    · exact (P_sh.continuous).continuousOn
  have h_ab_ne : (Set.Icc a b).Nonempty := ⟨a, ⟨le_refl _, hab⟩⟩
  obtain ⟨u_max, _, hu_max⟩ :=
    isCompact_Icc.exists_isMaxOn h_ab_ne hφ_cont.abs
  set K_val : ℝ := |φ u_max| + 1 with hK_val_def
  have hK_nn : 0 ≤ K_val := by
    have h_abs : 0 ≤ |φ u_max| := abs_nonneg _
    linarith
  set K : NNReal := Real.toNNReal K_val with hK_def
  have hK_coe : (K : ℝ) = K_val := Real.coe_toNNReal K_val hK_nn
  have hφ_bdd : ∀ u ∈ Set.Icc a b, |φ u| ≤ K_val := by
    intro u hu
    have h_le : |φ u| ≤ |φ u_max| := hu_max hu
    change |φ u| ≤ |φ u_max| + 1
    linarith
  have hv_lip : ∀ u ∈ Set.Ioc a b, LipschitzOnWith K (v u) (Set.univ : Set ℝ) := by
    intro u hu
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z _ z' _
    rw [Real.dist_eq, Real.dist_eq, hK_coe]
    have h_exp : v u z - v u z' = φ u * (z - z') := by
      simp only [v]; ring
    rw [h_exp, abs_mul]
    have hu_in : u ∈ Set.Icc a b := ⟨le_of_lt hu.1, hu.2⟩
    have h_bound : |φ u| ≤ K_val := hφ_bdd u hu_in
    have h_diff_nn : 0 ≤ |z - z'| := abs_nonneg _
    nlinarith
  have hsubset : Set.Icc a b ⊆ Set.Icc (-s) s := by
    intro u hu
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) ≤ u := le_trans ha_pos.le hu.1
      linarith [hs_pos]
    · linarith [hu.2]
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by
    change Number.aperyPconifold.eval Number.aperyConifoldZ1Poly = 0
    exact Number.aperyPconifold_eval_z1
  have hslope :
      (Polynomial.derivative
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    change (Polynomial.derivative Number.aperyPconifold).eval
      Number.aperyConifoldZ1Poly ≠ 0
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hs_nn : 0 ≤ s := hs_pos.le
  have hV'_cont :
      ContinuousOn (fun t => frobeniusValueDeriv
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc (-s) s) :=
    frobeniusValueDeriv_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ M₀ hpk hslope
      hM0_small hM0_large hM0_thresh B hB_nn hB s hs_nn hs_lt
  have hV''_cont :
      ContinuousOn (fun t => frobeniusValueDeriv2
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc (-s) s) :=
    frobeniusValueDeriv2_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ M₀ hpk hslope
      hM0_small hM0_large hM0_thresh B hB_nn hB s hs_nn hs_lt
  have hV'_cont_ab : ContinuousOn (fun t => frobeniusValueDeriv
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc a b) := hV'_cont.mono hsubset
  have hV''_cont_ab : ContinuousOn (fun t => frobeniusValueDeriv2
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc a b) := hV''_cont.mono hsubset
  have hf_cont : ContinuousOn f (Set.Icc a b) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.mul hV'_cont_ab
    · exact continuousOn_id.mul hV''_cont_ab
  have hf_within : ∀ u ∈ Set.Ioc a b,
      HasDerivWithinAt f (v u (f u)) (Set.Iic u) u := by
    intro u hu
    have hu_pos : 0 < u := lt_trans ha_pos hu.1
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    have hu_lt : u < s := lt_of_le_of_lt hu.2 hb_lt
    have hu_mem : u ∈ Metric.ball (0 : ℝ) s := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
        abs_of_pos hu_pos]
      exact hu_lt
    have hP_ne_u : P_sh.eval u ≠ 0 :=
      hP_ne u ⟨le_of_lt hu.1, hu.2⟩
    have h_lin := yApery_y2_linear_ODE c₀ M₀ B hB_nn hM0_small hM0_large
      hM0_thresh hB s hs_pos hs_lt u hu_mem hu_ne hP_ne_u
    have h_v_eq : v u (f u) =
        Q_sh.eval u / P_sh.eval u *
          (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
            + u * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u) := by
      simp only [v, φ, f]
    rw [h_v_eq]
    exact h_lin.hasDerivWithinAt
  have hg_within : ∀ u ∈ Set.Ioc a b,
      HasDerivWithinAt g (v u (g u)) (Set.Iic u) u := by
    intro u hu
    have h_v_eq : v u (g u) =
        Q_sh.eval u / P_sh.eval u * g u := by
      simp only [v, φ]
    rw [h_v_eq]
    exact hg_deriv u hu
  have hf_in : ∀ u ∈ Set.Ioc a b, f u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  have hg_in : ∀ u ∈ Set.Ioc a b, g u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  have h_init_eq : f b = g b := hg_init.symm
  have h_eq : Set.EqOn f g (Set.Icc a b) :=
    ODE_solution_unique_of_mem_Icc_left hv_lip hf_cont hf_within hf_in
      hg_cont hg_within hg_in h_init_eq
  exact h_eq.symm

/-- Symmetric Picard uniqueness on a negative sub-interval `[a, b] ⊂ (-s, 0)`.
The structure mirrors the positive case: every `u ∈ [a, b]` satisfies
`u ≤ b < 0`, so `u ≠ 0` and `|u| = -u ≤ -a < s`, putting it inside the
punctured ball where `yApery_y2_linear_ODE` applies. -/
theorem yApery_y2_unique_on_subinterval_neg
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (a b : ℝ) (ha_lt : -s < a) (hab : a ≤ b) (hb_neg : b < 0)
    (hP_ne : ∀ t ∈ Set.Icc a b,
      (taylorShift Number.aperyPconifold
        Number.aperyConifoldZ1Poly).eval t ≠ 0)
    (g : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_deriv : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t
        * g t)
      (Set.Ici t) t)
    (hg_init : g a =
      2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ a
        + a * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ a) :
    Set.EqOn g (fun t =>
        2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t)
      (Set.Icc a b) := by
  set Q_sh := taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly
    with hQ_sh_def
  set P_sh := taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly
    with hP_sh_def
  set f : ℝ → ℝ := fun t =>
    2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
      + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
    with hf_def
  let φ : ℝ → ℝ := fun u => Q_sh.eval u / P_sh.eval u
  let v : ℝ → ℝ → ℝ := fun u z => φ u * z
  have hφ_cont : ContinuousOn φ (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ hP_ne
    · exact (Q_sh.continuous).continuousOn
    · exact (P_sh.continuous).continuousOn
  have h_ab_ne : (Set.Icc a b).Nonempty := ⟨a, ⟨le_refl _, hab⟩⟩
  obtain ⟨u_max, _, hu_max⟩ :=
    isCompact_Icc.exists_isMaxOn h_ab_ne hφ_cont.abs
  set K_val : ℝ := |φ u_max| + 1 with hK_val_def
  have hK_nn : 0 ≤ K_val := by
    have h_abs : 0 ≤ |φ u_max| := abs_nonneg _
    linarith
  set K : NNReal := Real.toNNReal K_val with hK_def
  have hK_coe : (K : ℝ) = K_val := Real.coe_toNNReal K_val hK_nn
  have hφ_bdd : ∀ u ∈ Set.Icc a b, |φ u| ≤ K_val := by
    intro u hu
    have h_le : |φ u| ≤ |φ u_max| := hu_max hu
    change |φ u| ≤ |φ u_max| + 1
    linarith
  have hv_lip : ∀ u ∈ Set.Ico a b, LipschitzOnWith K (v u) (Set.univ : Set ℝ) := by
    intro u hu
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z _ z' _
    rw [Real.dist_eq, Real.dist_eq, hK_coe]
    have h_exp : v u z - v u z' = φ u * (z - z') := by
      simp only [v]; ring
    rw [h_exp, abs_mul]
    have hu_in : u ∈ Set.Icc a b := ⟨hu.1, hu.2.le⟩
    have h_bound : |φ u| ≤ K_val := hφ_bdd u hu_in
    have h_diff_nn : 0 ≤ |z - z'| := abs_nonneg _
    nlinarith
  -- `[a, b] ⊆ [-s, s]`: lower via `ha_lt`, upper via `b < 0 < s`.
  have hsubset : Set.Icc a b ⊆ Set.Icc (-s) s := by
    intro u hu
    refine ⟨?_, ?_⟩
    · linarith [hu.1]
    · have hu_le : u ≤ b := hu.2
      linarith [hb_neg, hs_pos]
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by
    change Number.aperyPconifold.eval Number.aperyConifoldZ1Poly = 0
    exact Number.aperyPconifold_eval_z1
  have hslope :
      (Polynomial.derivative
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    change (Polynomial.derivative Number.aperyPconifold).eval
      Number.aperyConifoldZ1Poly ≠ 0
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hs_nn : 0 ≤ s := hs_pos.le
  have hV'_cont :
      ContinuousOn (fun t => frobeniusValueDeriv
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc (-s) s) :=
    frobeniusValueDeriv_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ M₀ hpk hslope
      hM0_small hM0_large hM0_thresh B hB_nn hB s hs_nn hs_lt
  have hV''_cont :
      ContinuousOn (fun t => frobeniusValueDeriv2
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc (-s) s) :=
    frobeniusValueDeriv2_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ M₀ hpk hslope
      hM0_small hM0_large hM0_thresh B hB_nn hB s hs_nn hs_lt
  have hV'_cont_ab : ContinuousOn (fun t => frobeniusValueDeriv
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc a b) := hV'_cont.mono hsubset
  have hV''_cont_ab : ContinuousOn (fun t => frobeniusValueDeriv2
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc a b) := hV''_cont.mono hsubset
  have hf_cont : ContinuousOn f (Set.Icc a b) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.mul hV'_cont_ab
    · exact continuousOn_id.mul hV''_cont_ab
  have hf_within : ∀ u ∈ Set.Ico a b,
      HasDerivWithinAt f (v u (f u)) (Set.Ici u) u := by
    intro u hu
    have hu_neg : u < 0 := lt_trans hu.2 hb_neg
    have hu_ne : u ≠ 0 := ne_of_lt hu_neg
    have hu_gt : -s < u := lt_of_lt_of_le ha_lt hu.1
    have hu_mem : u ∈ Metric.ball (0 : ℝ) s := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
        abs_of_neg hu_neg]
      linarith
    have hP_ne_u : P_sh.eval u ≠ 0 :=
      hP_ne u ⟨hu.1, hu.2.le⟩
    have h_lin := yApery_y2_linear_ODE c₀ M₀ B hB_nn hM0_small hM0_large
      hM0_thresh hB s hs_pos hs_lt u hu_mem hu_ne hP_ne_u
    have h_v_eq : v u (f u) =
        Q_sh.eval u / P_sh.eval u *
          (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
            + u * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u) := by
      simp only [v, φ, f]
    rw [h_v_eq]
    exact h_lin.hasDerivWithinAt
  have hg_within : ∀ u ∈ Set.Ico a b,
      HasDerivWithinAt g (v u (g u)) (Set.Ici u) u := by
    intro u hu
    have h_v_eq : v u (g u) =
        Q_sh.eval u / P_sh.eval u * g u := by
      simp only [v, φ]
    rw [h_v_eq]
    exact hg_deriv u hu
  have hf_in : ∀ u ∈ Set.Ico a b, f u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  have hg_in : ∀ u ∈ Set.Ico a b, g u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  have h_init_eq : f a = g a := hg_init.symm
  have h_eq : Set.EqOn f g (Set.Icc a b) :=
    ODE_solution_unique_of_mem_Icc_right hv_lip hf_cont hf_within hf_in
      hg_cont hg_within hg_in h_init_eq
  exact h_eq.symm

/-!
## Anchor value at the regular singular point `t = 0`

The function `f(t) = 2 V'(t) + t V''(t)` (i.e., `y₂` in the y-chain
notation) is analytic at `t = 0` because the underlying series is
absolutely convergent on `(-s, s)`. Its value at `0` collapses to the
leading recurrence coefficient `2 · a₁`. This anchor is what a future
Frobenius cross-zero rigidity argument will pin both punctured
half-intervals against.
-/

@[simp] lemma yApery_y2_eval_zero (c₀ : ℝ) :
    (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ 0
      + (0 : ℝ) * frobeniusValueDeriv2 (aperyPsSeq 0 0
          Number.aperyQconifold Number.aperyPconifold) 2
          Number.aperyConifoldZ1Poly 1 c₀ 0)
    = 2 * frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ 1 := by
  simp

/-- Companion anchor: `y₂'(0) = y₃(0) = 6 · a₃ + 0 · a₄`. -/
@[simp] lemma yApery_y3_eval_zero (c₀ : ℝ) :
    (3 * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ 0
      + (0 : ℝ) * frobeniusValueDeriv3 (aperyPsSeq 0 0
          Number.aperyQconifold Number.aperyPconifold) 2
          Number.aperyConifoldZ1Poly 1 c₀ 0)
    = 6 * frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ 2 := by
  simp; ring

/-- The Frobenius `y₂` function is continuous on the **full** closed ball
`[-s, s]` (including `t = 0`). This is the cross-zero glue: combined
with the two-sided Picard uniqueness, any candidate solution
agreeing with `y₂` on `[a, b] ⊂ (0, s)` must also share `y₂(0)` by
continuity at the singular point. -/
theorem yApery_y2_continuousOn_closedBall
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    ContinuousOn (fun t =>
        2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t)
      (Set.Icc (-s) s) := by
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by
    change Number.aperyPconifold.eval Number.aperyConifoldZ1Poly = 0
    exact Number.aperyPconifold_eval_z1
  have hslope :
      (Polynomial.derivative
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    change (Polynomial.derivative Number.aperyPconifold).eval
      Number.aperyConifoldZ1Poly ≠ 0
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hV'_cont :
      ContinuousOn (fun t => frobeniusValueDeriv
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc (-s) s) :=
    frobeniusValueDeriv_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ M₀ hpk hslope
      hM0_small hM0_large hM0_thresh B hB_nn hB s hs_nn hs_lt
  have hV''_cont :
      ContinuousOn (fun t => frobeniusValueDeriv2
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 c₀ t) (Set.Icc (-s) s) :=
    frobeniusValueDeriv2_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ M₀ hpk hslope
      hM0_small hM0_large hM0_thresh B hB_nn hB s hs_nn hs_lt
  refine ContinuousOn.add ?_ ?_
  · exact continuousOn_const.mul hV'_cont
  · exact continuousOn_id.mul hV''_cont

/-!
## Two-sided Picard uniqueness across the regular singular point `t = 0`

Combining the negative left-anchored Picard, positive right-anchored Picard,
and continuity of both `g` and the Frobenius `y₂` at `0`, we close the
`t = 0` gap: any candidate `g` that satisfies the linear ODE on each side
of `0`, is continuous on `[a, b]`, and matches `y₂` at the two outer
anchors `a < 0 < b` must agree with `y₂` on the entire closed interval
`[a, b]`. This completes the Picard side of the Apéry `y₂` uniqueness
chain across the regular singular point.
-/

theorem yApery_y2_unique_on_two_sided
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (a b : ℝ) (ha_lt : -s < a) (ha_neg : a < 0) (hb_pos : 0 < b) (hb_lt : b < s)
    (hP_ne_neg : ∀ t ∈ Set.Ico a 0,
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0)
    (hP_ne_pos : ∀ t ∈ Set.Ioc 0 b,
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0)
    (g : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_deriv_neg : ∀ t ∈ Set.Ico a 0, HasDerivWithinAt g
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * g t)
      (Set.Ici t) t)
    (hg_deriv_pos : ∀ t ∈ Set.Ioc 0 b, HasDerivWithinAt g
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * g t)
      (Set.Iic t) t)
    (hg_init_a : g a =
      2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ a
        + a * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ a)
    (hg_init_b : g b =
      2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ b
        + b * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ b) :
    Set.EqOn g (fun t =>
        2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t)
      (Set.Icc a b) := by
  set f : ℝ → ℝ := fun t =>
    2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
      + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
    with hf_def
  -- `[a, b] ⊆ [-s, s]`
  have hsubset_full : Set.Icc a b ⊆ Set.Icc (-s) s := by
    intro u hu
    refine ⟨?_, ?_⟩
    · linarith [hu.1]
    · linarith [hu.2]
  -- `f` is continuous on the full closed ball, hence on `[a, b]`.
  have hf_cont_full : ContinuousOn f (Set.Icc (-s) s) :=
    yApery_y2_continuousOn_closedBall c₀ M₀ B hB_nn hM0_small hM0_large
      hM0_thresh hB s hs_pos.le hs_lt
  have hf_cont : ContinuousOn f (Set.Icc a b) := hf_cont_full.mono hsubset_full
  -- Step 1: g ≡ f on each `[a, -ε]` for `0 < ε ≤ -a`.
  have h_neg_step : ∀ ε : ℝ, 0 < ε → ε ≤ -a →
      Set.EqOn g f (Set.Icc a (-ε)) := by
    intro ε hε_pos hε_le
    have ha_le_negε : a ≤ -ε := by linarith
    have hnegε_neg : -ε < 0 := by linarith
    -- Build the hypotheses for `yApery_y2_unique_on_subinterval_neg`.
    have hP_ne' : ∀ t ∈ Set.Icc a (-ε),
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0 := by
      intro t ht
      have ht_neg : t < 0 := lt_of_le_of_lt ht.2 hnegε_neg
      exact hP_ne_neg t ⟨ht.1, ht_neg⟩
    have hsubset_neg : Set.Icc a (-ε) ⊆ Set.Icc a b := by
      intro u hu
      refine ⟨hu.1, ?_⟩
      have : u ≤ -ε := hu.2
      linarith
    have hg_cont' : ContinuousOn g (Set.Icc a (-ε)) := hg_cont.mono hsubset_neg
    have hg_deriv' : ∀ t ∈ Set.Ico a (-ε), HasDerivWithinAt g
        ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
         (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * g t)
        (Set.Ici t) t := by
      intro t ht
      have ht_neg : t < 0 := lt_of_lt_of_le ht.2 hnegε_neg.le
      exact hg_deriv_neg t ⟨ht.1, ht_neg⟩
    exact yApery_y2_unique_on_subinterval_neg c₀ M₀ B hB_nn hM0_small hM0_large
      hM0_thresh hB s hs_pos hs_lt a (-ε) ha_lt ha_le_negε hnegε_neg hP_ne'
      g hg_cont' hg_deriv' hg_init_a
  -- Step 1b: extend to `Ico a 0`.
  have h_neg_eq : Set.EqOn g f (Set.Ico a 0) := by
    intro t ht
    have ht_a : a ≤ t := ht.1
    have ht_neg : t < 0 := ht.2
    set ε : ℝ := -t / 2 with hε_def
    have hε_pos : 0 < ε := by
      have : 0 < -t := by linarith
      have : 0 < -t / 2 := by linarith
      exact this
    have hε_le : ε ≤ -a := by
      have ht_le_half : t ≤ t / 2 := by linarith
      -- ε = -t/2, want -t/2 ≤ -a, i.e. a ≤ t/2.
      have ha_le_half : a ≤ t / 2 := le_trans ht_a ht_le_half
      have hε_eq : ε = -t / 2 := hε_def
      rw [hε_eq]
      linarith
    have ht_le_negε : t ≤ -ε := by
      -- -ε = t/2, and t ≤ t/2 since t < 0.
      have h1 : t ≤ t / 2 := by linarith
      have hneg : -ε = t / 2 := by rw [hε_def]; ring
      linarith
    have ht_in : t ∈ Set.Icc a (-ε) := ⟨ht_a, ht_le_negε⟩
    exact h_neg_step ε hε_pos hε_le ht_in
  -- Step 2: g ≡ f on each `[ε, b]` for `0 < ε ≤ b`.
  have h_pos_step : ∀ ε : ℝ, 0 < ε → ε ≤ b →
      Set.EqOn g f (Set.Icc ε b) := by
    intro ε hε_pos hε_le
    have hP_ne' : ∀ t ∈ Set.Icc ε b,
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0 := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hε_pos ht.1
      exact hP_ne_pos t ⟨ht_pos, ht.2⟩
    have hsubset_pos : Set.Icc ε b ⊆ Set.Icc a b := by
      intro u hu
      refine ⟨?_, hu.2⟩
      have : ε ≤ u := hu.1
      linarith
    have hg_cont' : ContinuousOn g (Set.Icc ε b) := hg_cont.mono hsubset_pos
    have hg_deriv' : ∀ t ∈ Set.Ioc ε b, HasDerivWithinAt g
        ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
         (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * g t)
        (Set.Iic t) t := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hε_pos ht.1.le
      exact hg_deriv_pos t ⟨ht_pos, ht.2⟩
    exact yApery_y2_unique_on_subinterval_pos_right c₀ M₀ B hB_nn hM0_small hM0_large
      hM0_thresh hB s hs_pos hs_lt ε b hε_pos hε_le hb_lt hP_ne'
      g hg_cont' hg_deriv' hg_init_b
  -- Step 2b: extend to `Ioc 0 b`.
  have h_pos_eq : Set.EqOn g f (Set.Ioc 0 b) := by
    intro t ht
    have ht_pos : 0 < t := ht.1
    have ht_le : t ≤ b := ht.2
    set ε : ℝ := t / 2 with hε_def
    have hε_pos : 0 < ε := by
      have : 0 < t / 2 := by linarith
      exact this
    have hε_le : ε ≤ b := by
      have : t / 2 ≤ t := by linarith
      have : t / 2 ≤ b := le_trans this ht_le
      simpa [hε_def] using this
    have hε_le_t : ε ≤ t := by
      have : t / 2 ≤ t := by linarith
      simpa [hε_def] using this
    have ht_in : t ∈ Set.Icc ε b := ⟨hε_le_t, ht_le⟩
    exact h_pos_step ε hε_pos hε_le ht_in
  -- Step 3: glue at 0 via continuity. Use `Set.EqOn.of_subset_closure`.
  -- We have `g = f` on `Ico a 0`. Both are continuous on `Icc a 0`.
  -- `closure (Ico a 0) = Icc a 0` (since `a < 0`).
  have hsubset_left : Set.Icc a 0 ⊆ Set.Icc a b := by
    intro u hu
    exact ⟨hu.1, le_trans hu.2 hb_pos.le⟩
  have hg_cont_left : ContinuousOn g (Set.Icc a 0) := hg_cont.mono hsubset_left
  have hf_cont_left : ContinuousOn f (Set.Icc a 0) := hf_cont.mono hsubset_left
  have h_left_eq : Set.EqOn g f (Set.Icc a 0) := by
    have hclos : closure (Set.Ico a 0) = Set.Icc a 0 := closure_Ico ha_neg.ne
    have hsub1 : Set.Ico a 0 ⊆ Set.Icc a 0 := Set.Ico_subset_Icc_self
    have hsub2 : Set.Icc a 0 ⊆ closure (Set.Ico a 0) := by
      rw [hclos]
    exact h_neg_eq.of_subset_closure hg_cont_left hf_cont_left hsub1 hsub2
  -- Similarly for the right side.
  have hsubset_right : Set.Icc 0 b ⊆ Set.Icc a b := by
    intro u hu
    exact ⟨le_trans ha_neg.le hu.1, hu.2⟩
  have hg_cont_right : ContinuousOn g (Set.Icc 0 b) := hg_cont.mono hsubset_right
  have hf_cont_right : ContinuousOn f (Set.Icc 0 b) := hf_cont.mono hsubset_right
  have h_right_eq : Set.EqOn g f (Set.Icc 0 b) := by
    have hclos : closure (Set.Ioc 0 b) = Set.Icc 0 b := closure_Ioc hb_pos.ne
    have hsub1 : Set.Ioc 0 b ⊆ Set.Icc 0 b := Set.Ioc_subset_Icc_self
    have hsub2 : Set.Icc 0 b ⊆ closure (Set.Ioc 0 b) := by
      rw [hclos]
    exact h_pos_eq.of_subset_closure hg_cont_right hf_cont_right hsub1 hsub2
  -- Step 4: combine. Any t ∈ Icc a b is in Icc a 0 (if t ≤ 0) or Icc 0 b.
  intro t ht
  by_cases ht_sign : t ≤ 0
  · exact h_left_eq ⟨ht.1, ht_sign⟩
  · have ht_pos : 0 < t := lt_of_not_ge ht_sign
    exact h_right_eq ⟨ht_pos.le, ht.2⟩

/-!
## Apéry-side series rigidity

Specializes the abstract `frobeniusValue_eqOn_of_eventuallyEq_general`
to the Apéry conifold parameters: `ps = aperyPsSeq 0 0 Q P`, `n = 2`,
`z₁ = aperyConifoldZ1Poly`, `ρ = 1`. Discharges the two non-degeneracy
hypotheses (`hpk`, `hslope`) from the conifold polynomial properties
already established in `AperyConifoldIndicial`.
-/

/-- **Apéry series rigidity at the conifold.** Any analytic function
that agrees with the Apéry Frobenius value `V` in a neighbourhood of
`t = 0` must equal `V` throughout the entire convergence disk
`Metric.ball 0 s`.

This is the series-side companion of the Picard-side cross-zero glue
(`yApery_y2_unique_on_two_sided`). Together they pin candidate solutions
of the Apéry conifold ODE on both the analytic and the differential
side. -/
theorem aperyFrobeniusValue_eqOn_of_eventuallyEq
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (g : ℝ → ℝ)
    (hg_anal : AnalyticOnNhd ℝ g (Metric.ball (0 : ℝ) s))
    (hfg : Filter.EventuallyEq (nhds (0 : ℝ)) g
      (fun t => frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t)) :
    Set.EqOn g (fun t : ℝ => frobeniusValue (aperyPsSeq 0 0
      Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 c₀ t)
      (Metric.ball (0 : ℝ) s) := by
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold)
      (2 + 1)).eval Number.aperyConifoldZ1Poly = 0 := by
    change Number.aperyPconifold.eval Number.aperyConifoldZ1Poly = 0
    exact Number.aperyPconifold_eval_z1
  have hslope :
      (Polynomial.derivative
        ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    change (Polynomial.derivative Number.aperyPconifold).eval
      Number.aperyConifoldZ1Poly ≠ 0
    exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  exact frobeniusValue_eqOn_of_eventuallyEq_general
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
    Number.aperyConifoldZ1Poly 1 c₀ M₀ hpk hslope
    hM0_small hM0_large hM0_thresh B hB_nn hB s hs_pos hs_lt g hg_anal hfg

/-!
## Generic Picard uniqueness on closed t-intervals

The lemmas above pin candidate solutions to the **Frobenius series**
on the convergence disk `Metric.ball 0 s`. To continue past the disk
along `[0, 1 - z₁]` (toward the Apéry boundary at `z = 1`), we need
Picard uniqueness for two arbitrary smooth solutions of the linear
ODE `ż = (Q_sh / P_sh) · z` on a closed sub-interval where `P_sh` is
non-vanishing.

The two-solution form (no Frobenius hypotheses) is the right primitive:
analytic continuation will splice together a "from-disk" Frobenius
function with a "to-boundary" candidate, and Picard pins them on the
overlap.
-/

/-- **Generic Picard uniqueness, positive subinterval.** Two functions
satisfying the linear Apéry conifold ODE in t-space on a closed
interval `[a, b] ⊂ (0, ∞)` with `P_sh` non-vanishing throughout, and
matching at the left endpoint `a`, agree on `[a, b]`.

This decouples ODE uniqueness from the Frobenius convergence disk:
useful for analytic continuation past `s` along the positive ray. -/
theorem aperyConifoldODE_unique_two_solutions_pos
    (a b : ℝ) (hab : a ≤ b)
    (hP_ne : ∀ t ∈ Set.Icc a b,
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0)
    (f g : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hf_deriv : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * f t)
      (Set.Ici t) t)
    (hg_deriv : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * g t)
      (Set.Ici t) t)
    (h_init : f a = g a) :
    Set.EqOn f g (Set.Icc a b) := by
  set Q_sh := taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly
    with hQ_sh_def
  set P_sh := taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly
    with hP_sh_def
  let φ : ℝ → ℝ := fun u => Q_sh.eval u / P_sh.eval u
  let v : ℝ → ℝ → ℝ := fun u z => φ u * z
  have hφ_cont : ContinuousOn φ (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ hP_ne
    · exact (Q_sh.continuous).continuousOn
    · exact (P_sh.continuous).continuousOn
  have h_ab_ne : (Set.Icc a b).Nonempty := ⟨a, ⟨le_refl _, hab⟩⟩
  obtain ⟨u_max, _, hu_max⟩ :=
    isCompact_Icc.exists_isMaxOn h_ab_ne hφ_cont.abs
  set K_val : ℝ := |φ u_max| + 1 with hK_val_def
  have hK_nn : 0 ≤ K_val := by
    have h_abs : 0 ≤ |φ u_max| := abs_nonneg _
    linarith
  set K : NNReal := Real.toNNReal K_val with hK_def
  have hK_coe : (K : ℝ) = K_val := Real.coe_toNNReal K_val hK_nn
  have hφ_bdd : ∀ u ∈ Set.Icc a b, |φ u| ≤ K_val := by
    intro u hu
    have h_le : |φ u| ≤ |φ u_max| := hu_max hu
    change |φ u| ≤ |φ u_max| + 1
    linarith
  have hv_lip : ∀ u ∈ Set.Ico a b, LipschitzOnWith K (v u) (Set.univ : Set ℝ) := by
    intro u hu
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z _ z' _
    rw [Real.dist_eq, Real.dist_eq, hK_coe]
    have h_exp : v u z - v u z' = φ u * (z - z') := by
      simp only [v]; ring
    rw [h_exp, abs_mul]
    have hu_in : u ∈ Set.Icc a b := ⟨hu.1, hu.2.le⟩
    have h_bound : |φ u| ≤ K_val := hφ_bdd u hu_in
    have h_diff_nn : 0 ≤ |z - z'| := abs_nonneg _
    nlinarith
  have hf_within : ∀ u ∈ Set.Ico a b,
      HasDerivWithinAt f (v u (f u)) (Set.Ici u) u := by
    intro u hu
    have h_v_eq : v u (f u) =
        Q_sh.eval u / P_sh.eval u * f u := by
      simp only [v, φ]
    rw [h_v_eq]
    exact hf_deriv u hu
  have hg_within : ∀ u ∈ Set.Ico a b,
      HasDerivWithinAt g (v u (g u)) (Set.Ici u) u := by
    intro u hu
    have h_v_eq : v u (g u) =
        Q_sh.eval u / P_sh.eval u * g u := by
      simp only [v, φ]
    rw [h_v_eq]
    exact hg_deriv u hu
  have hf_in : ∀ u ∈ Set.Ico a b, f u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  have hg_in : ∀ u ∈ Set.Ico a b, g u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  exact ODE_solution_unique_of_mem_Icc_right hv_lip hf_cont hf_within hf_in
    hg_cont hg_within hg_in h_init

/-!
## Closed-form factorisation of the conifold-shifted leading polynomial

`P_sh(t) = aperyPconifold(z₁ - t)` factors as `t · (z₁ - t)² · (24√2 + t)`.
Roots in t: `t = 0` (the conifold itself), `t = z₁` (image of `z = 0`,
double), and `t = -24√2` (image of `z = z₂`, the second conifold).
-/

/-- Closed-form value of the conifold-shifted leading polynomial:
`(taylorShift aperyP z₁)(t) = (z₁ - t)² · t · (24√2 + t)`. -/
lemma aperyPconifold_taylorShift_eval (t : ℝ) :
    (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t =
      (Number.aperyConifoldZ1Poly - t) ^ 2 * t *
        (t + 24 * Real.sqrt 2) := by
  have hreduce :
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t =
        Number.aperyPconifold.eval (Number.aperyConifoldZ1Poly - t) := by
    unfold taylorShift
    rw [Polynomial.eval_comp]
    simp
  rw [hreduce]
  unfold Number.aperyPconifold
  simp only [Polynomial.eval_add, Polynomial.eval_monomial]
  have hsq : Number.aperyConifoldZ1Poly ^ 2 =
      34 * Number.aperyConifoldZ1Poly - 1 :=
    Number.aperyConifoldZ1Poly_sq
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  unfold Number.aperyConifoldZ1Poly at hsq ⊢
  nlinarith [hsq, hsqrt2, sq_nonneg (17 - 12 * Real.sqrt 2 - t)]

/-- The conifold-shifted leading polynomial is non-vanishing on the
left punctured neighbourhood `(-24√2, 0)`, i.e., for `z ∈ (z₁, z₁ + 24√2)`
in the original variable. In particular this covers the path from the
conifold toward `z = 1` since `1 < z₁ + 24√2` (because `z₁ > 0`). -/
lemma aperyPconifold_taylorShift_ne_zero_left
    {t : ℝ} (ht_lt : -(24 * Real.sqrt 2) < t) (ht_neg : t < 0) :
    (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0 := by
  rw [aperyPconifold_taylorShift_eval]
  -- (z₁ - t)² · t · (24√2 + t) ≠ 0 since each factor ≠ 0.
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly := by
    unfold Number.aperyConifoldZ1Poly
    have hsqrt2 : Real.sqrt 2 < 17 / 12 := by
      have : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2, this]
    linarith
  have h1 : Number.aperyConifoldZ1Poly - t > 0 := by linarith
  have h1ne : (Number.aperyConifoldZ1Poly - t) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt h1)
  have h2 : t ≠ 0 := ne_of_lt ht_neg
  have h3 : t + 24 * Real.sqrt 2 ≠ 0 := by
    have : t + 24 * Real.sqrt 2 > 0 := by linarith
    exact ne_of_gt this
  exact mul_ne_zero (mul_ne_zero h1ne h2) h3

/-- The conifold-shifted leading polynomial is non-vanishing on the
right punctured neighbourhood `(0, z₁)`. -/
lemma aperyPconifold_taylorShift_ne_zero_right
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < Number.aperyConifoldZ1Poly) :
    (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0 := by
  rw [aperyPconifold_taylorShift_eval]
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly := by
    unfold Number.aperyConifoldZ1Poly
    have hsqrt2 : Real.sqrt 2 < 17 / 12 := by
      have : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2, this]
    linarith
  have hsqrt2_pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h1 : Number.aperyConifoldZ1Poly - t > 0 := by linarith
  have h1ne : (Number.aperyConifoldZ1Poly - t) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt h1)
  have h2 : t ≠ 0 := ne_of_gt ht_pos
  have h3 : t + 24 * Real.sqrt 2 ≠ 0 := by
    have : t + 24 * Real.sqrt 2 > 0 := by positivity
    exact ne_of_gt this
  exact mul_ne_zero (mul_ne_zero h1ne h2) h3

/-- **Generic Picard uniqueness, negative subinterval.** Two functions
satisfying the linear Apéry conifold ODE in t-space on a closed
interval `[a, b] ⊂ (-∞, 0)` with `P_sh` non-vanishing throughout, and
matching at the **right** endpoint `b`, agree on `[a, b]`.

Mirror of `aperyConifoldODE_unique_two_solutions_pos`: needed because the
Apéry physical boundary `z = 1` corresponds to `t = z₁ - 1 < 0`, so the
analytic-continuation path from the conifold disk lives in negative t. -/
theorem aperyConifoldODE_unique_two_solutions_neg
    (a b : ℝ) (hab : a ≤ b)
    (hP_ne : ∀ t ∈ Set.Icc a b,
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0)
    (f g : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hf_deriv : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt f
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * f t)
      (Set.Iic t) t)
    (hg_deriv : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt g
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * g t)
      (Set.Iic t) t)
    (h_init : f b = g b) :
    Set.EqOn f g (Set.Icc a b) := by
  set Q_sh := taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly
    with hQ_sh_def
  set P_sh := taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly
    with hP_sh_def
  let φ : ℝ → ℝ := fun u => Q_sh.eval u / P_sh.eval u
  let v : ℝ → ℝ → ℝ := fun u z => φ u * z
  have hφ_cont : ContinuousOn φ (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ hP_ne
    · exact (Q_sh.continuous).continuousOn
    · exact (P_sh.continuous).continuousOn
  have h_ab_ne : (Set.Icc a b).Nonempty := ⟨a, ⟨le_refl _, hab⟩⟩
  obtain ⟨u_max, _, hu_max⟩ :=
    isCompact_Icc.exists_isMaxOn h_ab_ne hφ_cont.abs
  set K_val : ℝ := |φ u_max| + 1 with hK_val_def
  have hK_nn : 0 ≤ K_val := by
    have h_abs : 0 ≤ |φ u_max| := abs_nonneg _
    linarith
  set K : NNReal := Real.toNNReal K_val with hK_def
  have hK_coe : (K : ℝ) = K_val := Real.coe_toNNReal K_val hK_nn
  have hφ_bdd : ∀ u ∈ Set.Icc a b, |φ u| ≤ K_val := by
    intro u hu
    have h_le : |φ u| ≤ |φ u_max| := hu_max hu
    change |φ u| ≤ |φ u_max| + 1
    linarith
  have hv_lip : ∀ u ∈ Set.Ioc a b, LipschitzOnWith K (v u) (Set.univ : Set ℝ) := by
    intro u hu
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z _ z' _
    rw [Real.dist_eq, Real.dist_eq, hK_coe]
    have h_exp : v u z - v u z' = φ u * (z - z') := by
      simp only [v]; ring
    rw [h_exp, abs_mul]
    have hu_in : u ∈ Set.Icc a b := ⟨hu.1.le, hu.2⟩
    have h_bound : |φ u| ≤ K_val := hφ_bdd u hu_in
    have h_diff_nn : 0 ≤ |z - z'| := abs_nonneg _
    nlinarith
  have hf_within : ∀ u ∈ Set.Ioc a b,
      HasDerivWithinAt f (v u (f u)) (Set.Iic u) u := by
    intro u hu
    have h_v_eq : v u (f u) =
        Q_sh.eval u / P_sh.eval u * f u := by
      simp only [v, φ]
    rw [h_v_eq]
    exact hf_deriv u hu
  have hg_within : ∀ u ∈ Set.Ioc a b,
      HasDerivWithinAt g (v u (g u)) (Set.Iic u) u := by
    intro u hu
    have h_v_eq : v u (g u) =
        Q_sh.eval u / P_sh.eval u * g u := by
      simp only [v, φ]
    rw [h_v_eq]
    exact hg_deriv u hu
  have hf_in : ∀ u ∈ Set.Ioc a b, f u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  have hg_in : ∀ u ∈ Set.Ioc a b, g u ∈ (Set.univ : Set ℝ) :=
    fun _ _ => Set.mem_univ _
  exact ODE_solution_unique_of_mem_Icc_left hv_lip hf_cont hf_within hf_in
    hg_cont hg_within hg_in h_init

/-!
## Apéry boundary corridor: `[z₁ − 1, −ε]` is P_sh-clean

The Apéry physical boundary `z = 1` ↔ `t = z₁ − 1 ≈ −0.97` lies far from
the Frobenius disk `|t| < z₁ ≈ 0.029`. Picard transport from a small
left-of-zero interval `[z₁ − 1, −ε]` (any `ε ∈ (0, 1 − z₁)`) is the
canonical analytic-continuation step. The lemma below is the
non-vanishing input to `aperyConifoldODE_unique_two_solutions_neg`
on that interval.
-/

/-- Numerical bound: `1 < 24·√2`. Used to certify that `z₁ − 1 > −24·√2`,
i.e. that the Apéry boundary corridor avoids the second conifold. -/
lemma one_lt_twentyfour_sqrt_two : (1 : ℝ) < 24 * Real.sqrt 2 := by
  have hsqrt2_lb : (1 : ℝ) < Real.sqrt 2 := by
    have h2_pos : (0 : ℝ) ≤ 2 := by norm_num
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_pos
    have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [hsq, hnn]
  linarith [hsqrt2_lb, Real.sqrt_nonneg 2]

/-- Numerical bound: `0 < z₁ < 1` (where `z₁ = 17 − 12√2 ≈ 0.029`).
Both inequalities stated so callers can use `1 − z₁ > 0` for ε. -/
lemma aperyConifoldZ1Poly_lt_one : Number.aperyConifoldZ1Poly < 1 := by
  unfold Number.aperyConifoldZ1Poly
  have hsqrt2_lb : (4 : ℝ) / 3 < Real.sqrt 2 := by
    have h2_pos : (0 : ℝ) ≤ 2 := by norm_num
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_pos
    have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [hsq, hnn]
  linarith

lemma aperyConifoldZ1Poly_pos : 0 < Number.aperyConifoldZ1Poly := by
  unfold Number.aperyConifoldZ1Poly
  have hsqrt2_ub : Real.sqrt 2 < 17 / 12 := by
    have h2_pos : (0 : ℝ) ≤ 2 := by norm_num
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2_pos
    have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [hsq, hnn]
  linarith

/-- **Apéry boundary corridor.** For every `ε ∈ (0, 1 − z₁]`, the closed
interval `[z₁ − 1, −ε]` lies strictly inside `(−24√2, 0)`, so `P_sh`
(the conifold-shifted leading polynomial) is non-vanishing throughout.

This feeds `aperyConifoldODE_unique_two_solutions_neg` directly. -/
lemma aperyPconifold_taylorShift_ne_zero_on_boundary_corridor
    (ε : ℝ) (hε_pos : 0 < ε) (_hε_le : ε ≤ 1 - Number.aperyConifoldZ1Poly)
    {t : ℝ} (ht : t ∈ Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)) :
    (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0 := by
  obtain ⟨ht_left, ht_right⟩ := ht
  have h24 : (1 : ℝ) < 24 * Real.sqrt 2 := one_lt_twentyfour_sqrt_two
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly := aperyConifoldZ1Poly_pos
  -- t ≥ z₁ − 1 > −24·√2
  have h_left : -(24 * Real.sqrt 2) < t := by
    have : -(24 * Real.sqrt 2) < Number.aperyConifoldZ1Poly - 1 := by linarith
    linarith
  -- t ≤ −ε < 0
  have h_right : t < 0 := by linarith
  exact aperyPconifold_taylorShift_ne_zero_left h_left h_right

/-- **Apéry boundary uniqueness, packaged.** Two continuous solutions of
the linear conifold ODE on the boundary corridor `[z₁ − 1, −ε]` that
agree at the right endpoint `−ε` (where `ε ∈ (0, 1 − z₁]`) agree
throughout the corridor — including at the Apéry boundary `t = z₁ − 1`
itself.

This is `aperyConifoldODE_unique_two_solutions_neg` specialised to the
corridor, with `hP_ne` discharged via
`aperyPconifold_taylorShift_ne_zero_on_boundary_corridor`. -/
theorem aperyConifold_solution_unique_left_of_zero
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 - Number.aperyConifoldZ1Poly)
    (Y₁ Y₂ : ℝ → ℝ)
    (hY₁_cont : ContinuousOn Y₁ (Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)))
    (hY₂_cont : ContinuousOn Y₂ (Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)))
    (hY₁_deriv : ∀ t ∈ Set.Ioc (Number.aperyConifoldZ1Poly - 1) (-ε),
      HasDerivWithinAt Y₁
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * Y₁ t)
      (Set.Iic t) t)
    (hY₂_deriv : ∀ t ∈ Set.Ioc (Number.aperyConifoldZ1Poly - 1) (-ε),
      HasDerivWithinAt Y₂
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * Y₂ t)
      (Set.Iic t) t)
    (h_match : Y₁ (-ε) = Y₂ (-ε)) :
    Set.EqOn Y₁ Y₂ (Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)) := by
  have hab : Number.aperyConifoldZ1Poly - 1 ≤ -ε := by linarith
  have hP_ne : ∀ t ∈ Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε),
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0 :=
    fun t ht =>
      aperyPconifold_taylorShift_ne_zero_on_boundary_corridor ε hε_pos hε_le ht
  exact aperyConifoldODE_unique_two_solutions_neg
    (Number.aperyConifoldZ1Poly - 1) (-ε) hab hP_ne Y₁ Y₂
    hY₁_cont hY₂_cont hY₁_deriv hY₂_deriv h_match

/-!
## Linearity of the conifold ODE flow

The conifold ODE `ż = φ(t) · z` is R-linear in `z`, so any R-linear
combination of solutions is again a solution. This is the structural
basis for connection-coefficient analysis: the analytic continuation
of the Frobenius solution from the conifold disk to the boundary
`t = z₁ − 1` is an R-linear functional of the initial data.

We package this for the negative subinterval (Iic-derivative form).
-/

/-- **Linearity of the conifold ODE flow (negative side).** A linear
combination `α · Y₁ + β · Y₂` of two ODE solutions on `[a, b]` is again
an ODE solution. Continuity is preserved by `ContinuousOn` algebra;
the derivative is computed by the standard `HasDerivWithinAt` linear
combination, with the RHS reorganised via `φ · (α·Y₁ + β·Y₂) =
α · (φ·Y₁) + β · (φ·Y₂)`. -/
theorem aperyConifoldODE_linear_combination_neg
    (a b : ℝ) (Y₁ Y₂ : ℝ → ℝ) (α β : ℝ)
    (hY₁_cont : ContinuousOn Y₁ (Set.Icc a b))
    (hY₂_cont : ContinuousOn Y₂ (Set.Icc a b))
    (hY₁_deriv : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt Y₁
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * Y₁ t)
      (Set.Iic t) t)
    (hY₂_deriv : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt Y₂
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * Y₂ t)
      (Set.Iic t) t) :
    ContinuousOn (fun t => α * Y₁ t + β * Y₂ t) (Set.Icc a b) ∧
    ∀ t ∈ Set.Ioc a b, HasDerivWithinAt (fun t => α * Y₁ t + β * Y₂ t)
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
       (α * Y₁ t + β * Y₂ t))
      (Set.Iic t) t := by
  refine ⟨?_, ?_⟩
  · exact ((continuousOn_const.mul hY₁_cont).add (continuousOn_const.mul hY₂_cont))
  · intro t ht
    have h1 := (hY₁_deriv t ht).const_mul α
    have h2 := (hY₂_deriv t ht).const_mul β
    have h_sum := h1.add h2
    convert h_sum using 1
    ring

/-- **Linearity of the conifold ODE flow (positive side).** Mirror of the
negative-side linearity: `α · Y₁ + β · Y₂` solves the ODE on `[a, b]`
when `Y₁`, `Y₂` solve it. Used for connection-coefficient analysis
on the `(0, ∞)` ray. -/
theorem aperyConifoldODE_linear_combination_pos
    (a b : ℝ) (Y₁ Y₂ : ℝ → ℝ) (α β : ℝ)
    (hY₁_cont : ContinuousOn Y₁ (Set.Icc a b))
    (hY₂_cont : ContinuousOn Y₂ (Set.Icc a b))
    (hY₁_deriv : ∀ t ∈ Set.Ico a b, HasDerivWithinAt Y₁
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * Y₁ t)
      (Set.Ici t) t)
    (hY₂_deriv : ∀ t ∈ Set.Ico a b, HasDerivWithinAt Y₂
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * Y₂ t)
      (Set.Ici t) t) :
    ContinuousOn (fun t => α * Y₁ t + β * Y₂ t) (Set.Icc a b) ∧
    ∀ t ∈ Set.Ico a b, HasDerivWithinAt (fun t => α * Y₁ t + β * Y₂ t)
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
       (α * Y₁ t + β * Y₂ t))
      (Set.Ici t) t := by
  refine ⟨?_, ?_⟩
  · exact ((continuousOn_const.mul hY₁_cont).add (continuousOn_const.mul hY₂_cont))
  · intro t ht
    have h1 := (hY₁_deriv t ht).const_mul α
    have h2 := (hY₂_deriv t ht).const_mul β
    have h_sum := h1.add h2
    convert h_sum using 1
    ring

/-!
## Boundary value as a functional of right-endpoint initial data

If two solutions on the Apéry boundary corridor `[z₁−1, −ε]` agree at
the right endpoint `−ε`, they agree *in particular* at the left
endpoint `z₁−1`, the Apéry physical boundary. Combined with the
linearity of the ODE flow, the boundary value at `z₁−1` is therefore a
well-defined R-linear functional of the initial value at `−ε`.

These are the structural ingredients for connection-coefficient
analysis. Existence of the extension (so the functional is non-vacuous)
is the remaining analytical step.
-/

/-- If two ODE solutions on `[z₁−1, −ε]` agree at `−ε`, they agree at the
Apéry physical boundary `t = z₁−1` itself.

A direct point-evaluation corollary of
`aperyConifold_solution_unique_left_of_zero`. Useful as the abstract
statement that the boundary value `Y(z₁−1)` is determined by the
right-endpoint value `Y(−ε)`. -/
theorem aperyConifold_boundary_value_determined
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 - Number.aperyConifoldZ1Poly)
    (Y₁ Y₂ : ℝ → ℝ)
    (hY₁_cont : ContinuousOn Y₁ (Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)))
    (hY₂_cont : ContinuousOn Y₂ (Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)))
    (hY₁_deriv : ∀ t ∈ Set.Ioc (Number.aperyConifoldZ1Poly - 1) (-ε),
      HasDerivWithinAt Y₁
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * Y₁ t)
      (Set.Iic t) t)
    (hY₂_deriv : ∀ t ∈ Set.Ioc (Number.aperyConifoldZ1Poly - 1) (-ε),
      HasDerivWithinAt Y₂
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t * Y₂ t)
      (Set.Iic t) t)
    (h_match : Y₁ (-ε) = Y₂ (-ε)) :
    Y₁ (Number.aperyConifoldZ1Poly - 1) = Y₂ (Number.aperyConifoldZ1Poly - 1) := by
  have h_eqOn := aperyConifold_solution_unique_left_of_zero ε hε_pos hε_le
    Y₁ Y₂ hY₁_cont hY₂_cont hY₁_deriv hY₂_deriv h_match
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly := aperyConifoldZ1Poly_pos
  have h_mem : Number.aperyConifoldZ1Poly - 1 ∈
      Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε) := by
    refine ⟨le_refl _, ?_⟩
    linarith
  exact h_eqOn h_mem

/-!
## Frobenius candidate as `HasDerivWithinAt` solution

The Frobenius series candidate `2 V'(t) + t V''(t)` already satisfies
the conifold ODE pointwise on `Metric.ball 0 s \ {0}`
(via `yApery_y2_linear_ODE`). The negative Picard interface expects
`HasDerivWithinAt (Iic t)` rather than `HasDerivAt`. Converting via
`HasDerivAt.hasDerivWithinAt` packages the candidate so it can serve
directly as an existence witness on any subinterval of `(-s, 0)`.
-/

/-- Frobenius candidate satisfies the conifold ODE in `HasDerivWithinAt
(Iic t)` form on `Metric.ball 0 s \ {0}`. -/
theorem yApery_y2_linear_ODE_within_Iic
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) (ht_ne : t ≠ 0)
    (hP_ne : (taylorShift Number.aperyPconifold
      Number.aperyConifoldZ1Poly).eval t ≠ 0) :
    HasDerivWithinAt (fun u =>
        2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
        + u * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u)
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
        (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t))
      (Set.Iic t) t :=
  (yApery_y2_linear_ODE c₀ M₀ B hB_nn hM0_small hM0_large hM0_thresh hB
    s hs_pos hs_lt t ht_mem ht_ne hP_ne).hasDerivWithinAt

/-- Frobenius candidate also has the `(Ici t)` within-form. -/
theorem yApery_y2_linear_ODE_within_Ici
    (c₀ : ℝ) (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m, M₀ ≤ m →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly
              Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j' ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j')
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_pos : 0 < s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (t : ℝ) (ht_mem : t ∈ Metric.ball (0 : ℝ) s) (ht_ne : t ≠ 0)
    (hP_ne : (taylorShift Number.aperyPconifold
      Number.aperyConifoldZ1Poly).eval t ≠ 0) :
    HasDerivWithinAt (fun u =>
        2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u
        + u * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ u)
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
        (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t
          + t * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ t))
      (Set.Ici t) t :=
  (yApery_y2_linear_ODE c₀ M₀ B hB_nn hM0_small hM0_large hM0_thresh hB
    s hs_pos hs_lt t ht_mem ht_ne hP_ne).hasDerivWithinAt

/-!
## Continuity of the ODE quotient on the boundary corridor

The function `φ(t) := Q_sh(t) / P_sh(t)` (the slope of the linear ODE
`ż = φ · z`) is continuous on the boundary corridor `[z₁−1, −ε]` since
both polynomials are continuous and `P_sh` is non-vanishing throughout
(by `aperyPconifold_taylorShift_ne_zero_on_boundary_corridor`).

Continuity gives interval-integrability — the prerequisite for the
explicit exponential formula `z(t) = z(b) · exp(∫_b^t φ dτ)`, which
constructively realises the existence side of the boundary-uniqueness
chain.
-/

/-- The slope `φ = Q_sh / P_sh` is continuous on the boundary corridor
`[z₁−1, −ε]`. -/
lemma aperyConifoldSlope_continuousOn_boundary_corridor
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 - Number.aperyConifoldZ1Poly) :
    ContinuousOn (fun t =>
      (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t)
      (Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)) := by
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (taylorShift Number.aperyQconifold
      Number.aperyConifoldZ1Poly).continuous.continuousOn
  · exact (taylorShift Number.aperyPconifold
      Number.aperyConifoldZ1Poly).continuous.continuousOn
  · intro t ht
    exact aperyPconifold_taylorShift_ne_zero_on_boundary_corridor
      ε hε_pos hε_le ht

/-- The slope `φ = Q_sh / P_sh` is interval-integrable on the boundary
corridor `[z₁−1, −ε]`. Continuous on a compact closed interval ⇒
integrable; restated in `IntervalIntegrable` form. -/
lemma aperyConifoldSlope_intervalIntegrable_boundary_corridor
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 - Number.aperyConifoldZ1Poly) :
    IntervalIntegrable (fun t =>
      (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t)
      MeasureTheory.volume (Number.aperyConifoldZ1Poly - 1) (-ε) := by
  have hcont := aperyConifoldSlope_continuousOn_boundary_corridor ε hε_pos hε_le
  have hab : Number.aperyConifoldZ1Poly - 1 ≤ -ε := by linarith
  exact (hcont.intervalIntegrable_of_Icc hab)

/-!
## Explicit exponential extension on the boundary corridor

For a first-order linear ODE `ż = φ(t) · z` with `φ` continuous on a
closed interval, the solution is given by the explicit exponential
formula. On the boundary corridor `[z₁−1, −ε]` we get a constructive
existence witness: `Y(t) := init_v · exp(∫_{−ε}^t φ(τ) dτ)`. This
function is continuous on the corridor, equals `init_v` at the right
endpoint `−ε`, and satisfies the linear ODE.

Combined with `aperyConifold_solution_unique_left_of_zero`, this
closes both sides (existence + uniqueness) of the boundary-value
problem on the corridor.
-/

/-- **Explicit exponential extension** of a prescribed value `init_v` at
the right endpoint `−ε` of the boundary corridor. -/
noncomputable def aperyConifoldExpExtension
    (ε : ℝ) (init_v : ℝ) : ℝ → ℝ :=
  fun t => init_v * Real.exp (∫ τ in (-ε)..t,
    (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval τ /
    (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval τ)

/-- The exponential extension agrees with `init_v` at the right endpoint. -/
@[simp] lemma aperyConifoldExpExtension_at_right (ε init_v : ℝ) :
    aperyConifoldExpExtension ε init_v (-ε) = init_v := by
  unfold aperyConifoldExpExtension
  simp

/-- The corridor extension is ℝ-linear in the right-endpoint datum
`init_v` at every point `t`. Direct from the explicit closed form
`init_v · exp(∫_{−ε}^t φ)`. -/
lemma aperyConifoldExpExtension_smul_init_v
    (ε c init_v t : ℝ) :
    aperyConifoldExpExtension ε (c * init_v) t =
      c * aperyConifoldExpExtension ε init_v t := by
  unfold aperyConifoldExpExtension
  ring

/-- The corridor extension distributes over a sum of right-endpoint data
at every point `t`. Direct from the explicit closed form. -/
lemma aperyConifoldExpExtension_add_init_v
    (ε init_v₁ init_v₂ t : ℝ) :
    aperyConifoldExpExtension ε (init_v₁ + init_v₂) t =
      aperyConifoldExpExtension ε init_v₁ t +
      aperyConifoldExpExtension ε init_v₂ t := by
  unfold aperyConifoldExpExtension
  ring

@[simp] lemma aperyConifoldExpExtension_zero_init_v (ε t : ℝ) :
    aperyConifoldExpExtension ε 0 t = 0 := by
  unfold aperyConifoldExpExtension
  ring

/-- Pointwise continuity of the slope `φ = Q_sh / P_sh` at any `t` in the
open arc `(−24√2, 0)`. -/
lemma aperyConifoldSlope_continuousAt
    {t : ℝ} (h_left : -(24 * Real.sqrt 2) < t) (h_right : t < 0) :
    ContinuousAt (fun τ =>
      (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval τ /
      (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval τ) t := by
  have hP : (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t ≠ 0 :=
    aperyPconifold_taylorShift_ne_zero_left h_left h_right
  exact ((taylorShift Number.aperyQconifold
      Number.aperyConifoldZ1Poly).continuous.continuousAt).div
    ((taylorShift Number.aperyPconifold
      Number.aperyConifoldZ1Poly).continuous.continuousAt) hP

/-- Continuity of the exponential extension on the closed Apéry boundary
corridor `[z₁−1, −ε]`. The integral `∫_{−ε}^t φ` is continuous in `t`
because `φ` is continuous on the corridor; composing with `Real.exp`
and multiplying by the constant `init_v` preserves continuity. -/
lemma aperyConifoldExpExtension_continuousOn
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 - Number.aperyConifoldZ1Poly)
    (init_v : ℝ) :
    ContinuousOn (aperyConifoldExpExtension ε init_v)
      (Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)) := by
  unfold aperyConifoldExpExtension
  set φ : ℝ → ℝ := fun τ =>
    (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval τ /
    (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval τ
  have hab : Number.aperyConifoldZ1Poly - 1 ≤ -ε := by linarith
  have h_int_corr : IntervalIntegrable φ MeasureTheory.volume
      (Number.aperyConifoldZ1Poly - 1) (-ε) :=
    aperyConifoldSlope_intervalIntegrable_boundary_corridor ε hε_pos hε_le
  -- −ε ∈ [[z₁−1, −ε]] ⇒ primitive `t ↦ ∫_{−ε}^t φ` is continuous on the uIcc.
  have h_neg_mem : (-ε : ℝ) ∈ Set.uIcc (Number.aperyConifoldZ1Poly - 1) (-ε) :=
    Set.right_mem_uIcc
  have h_integral_cont' : ContinuousOn
      (fun t => ∫ τ in (-ε)..t, φ τ)
      (Set.uIcc (Number.aperyConifoldZ1Poly - 1) (-ε)) :=
    intervalIntegral.continuousOn_primitive_interval' h_int_corr h_neg_mem
  have h_uIcc : Set.uIcc (Number.aperyConifoldZ1Poly - 1) (-ε) =
      Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε) := Set.uIcc_of_le hab
  rw [h_uIcc] at h_integral_cont'
  have h_exp_cont : ContinuousOn
      (fun t => Real.exp (∫ τ in (-ε)..t, φ τ))
      (Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)) :=
    Real.continuous_exp.comp_continuousOn h_integral_cont'
  exact continuousOn_const.mul h_exp_cont

/-- Differentiability of the exponential extension at any interior point
of the boundary corridor: at `t ∈ Ioc (z₁−1) (−ε)` it satisfies the
linear ODE `ż = φ(t) · z`. (Even at the right endpoint `−ε` the
derivative exists in the full real-line sense, since `φ` is continuous
in a full neighbourhood of every corridor point — the corridor lies
strictly inside the open arc `(−24√2, 0)`.) -/
lemma aperyConifoldExpExtension_hasDerivAt
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 - Number.aperyConifoldZ1Poly)
    (init_v : ℝ)
    {t : ℝ} (ht : t ∈ Set.Ioc (Number.aperyConifoldZ1Poly - 1) (-ε)) :
    HasDerivAt (aperyConifoldExpExtension ε init_v)
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
       aperyConifoldExpExtension ε init_v t) t := by
  set φ : ℝ → ℝ := fun τ =>
    (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval τ /
    (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval τ
  obtain ⟨ht_left, ht_right⟩ := ht
  -- t lies strictly inside (−24√2, 0).
  have h24 : (1 : ℝ) < 24 * Real.sqrt 2 := one_lt_twentyfour_sqrt_two
  have hz1_pos : 0 < Number.aperyConifoldZ1Poly := aperyConifoldZ1Poly_pos
  have h_arc_left : -(24 * Real.sqrt 2) < t := by linarith
  have h_arc_right : t < 0 := by linarith
  -- φ continuous at t.
  have h_φ_at : ContinuousAt φ t :=
    aperyConifoldSlope_continuousAt h_arc_left h_arc_right
  -- Interval integrability of φ on −ε..t (contained in the corridor).
  have h_int_φ : IntervalIntegrable φ MeasureTheory.volume (-ε) t := by
    have h_corr := aperyConifoldSlope_intervalIntegrable_boundary_corridor
      ε hε_pos hε_le
    apply h_corr.mono_set
    have h_corr_le : Number.aperyConifoldZ1Poly - 1 ≤ -ε := by linarith
    have h_t_le_negε : t ≤ -ε := ht_right
    rw [Set.uIcc_of_le h_corr_le, Set.uIcc_comm, Set.uIcc_of_le h_t_le_negε]
    exact Set.Icc_subset_Icc (le_of_lt ht_left) le_rfl
  -- StronglyMeasurableAtFilter φ (𝓝 t) via continuity on the open arc.
  have h_arc_open : IsOpen (Set.Ioo (-(24 * Real.sqrt 2)) (0 : ℝ)) := isOpen_Ioo
  have h_t_in_arc : t ∈ Set.Ioo (-(24 * Real.sqrt 2)) (0 : ℝ) :=
    ⟨h_arc_left, h_arc_right⟩
  have h_φ_contOn_arc : ContinuousOn φ (Set.Ioo (-(24 * Real.sqrt 2)) (0 : ℝ)) := by
    intro τ hτ
    exact (aperyConifoldSlope_continuousAt hτ.1 hτ.2).continuousWithinAt
  have h_meas : StronglyMeasurableAtFilter φ (nhds t) MeasureTheory.volume :=
    ContinuousOn.stronglyMeasurableAtFilter h_arc_open h_φ_contOn_arc t h_t_in_arc
  have h_FTC : HasDerivAt (fun u => ∫ τ in (-ε)..u, φ τ) (φ t) t :=
    intervalIntegral.integral_hasDerivAt_right h_int_φ h_meas h_φ_at
  -- Chain rule with exp.
  have h_exp : HasDerivAt (fun u => Real.exp (∫ τ in (-ε)..u, φ τ))
      (Real.exp (∫ τ in (-ε)..t, φ τ) * φ t) t :=
    h_FTC.exp
  -- Multiply by constant init_v.
  have h_mul := h_exp.const_mul init_v
  -- Massage RHS to match the goal.
  have h_eq : init_v * (Real.exp (∫ τ in (-ε)..t, φ τ) * φ t) =
      φ t * aperyConifoldExpExtension ε init_v t := by
    unfold aperyConifoldExpExtension; ring
  rw [h_eq] at h_mul
  exact h_mul

/-- Iic-form of the derivative: same as `aperyConifoldExpExtension_hasDerivAt`
but stated as `HasDerivWithinAt … (Iic t) t`, ready for plugging into
`aperyConifold_solution_unique_left_of_zero`. -/
lemma aperyConifoldExpExtension_hasDerivWithinAt_Iic
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 - Number.aperyConifoldZ1Poly)
    (init_v : ℝ)
    {t : ℝ} (ht : t ∈ Set.Ioc (Number.aperyConifoldZ1Poly - 1) (-ε)) :
    HasDerivWithinAt (aperyConifoldExpExtension ε init_v)
      ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
       (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
       aperyConifoldExpExtension ε init_v t)
      (Set.Iic t) t :=
  (aperyConifoldExpExtension_hasDerivAt ε hε_pos hε_le init_v ht).hasDerivWithinAt

/-- **Existence side of the boundary value, packaged.** For every
right-endpoint initial value `init_v ∈ ℝ`, the explicit exponential
extension `aperyConifoldExpExtension ε init_v` is a continuous solution
of the conifold ODE on the boundary corridor `[z₁−1, −ε]` with that
right-endpoint value. -/
theorem aperyConifoldExpExtension_is_corridor_solution
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 - Number.aperyConifoldZ1Poly)
    (init_v : ℝ) :
    ContinuousOn (aperyConifoldExpExtension ε init_v)
      (Set.Icc (Number.aperyConifoldZ1Poly - 1) (-ε)) ∧
    (∀ t ∈ Set.Ioc (Number.aperyConifoldZ1Poly - 1) (-ε),
      HasDerivWithinAt (aperyConifoldExpExtension ε init_v)
        ((taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval t /
         (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval t *
         aperyConifoldExpExtension ε init_v t)
        (Set.Iic t) t) ∧
    aperyConifoldExpExtension ε init_v (-ε) = init_v :=
  ⟨aperyConifoldExpExtension_continuousOn ε hε_pos hε_le init_v,
   fun _ ht => aperyConifoldExpExtension_hasDerivWithinAt_Iic
     ε hε_pos hε_le init_v ht,
   aperyConifoldExpExtension_at_right ε init_v⟩

/-!
## Closed-form boundary connection coefficient

The value of the corridor solution at the Apéry physical boundary
`t = z₁ − 1` is, by the explicit exponential formula, the right-endpoint
initial datum `init_v` multiplied by a single ε-dependent real number:

  `Y(z₁ − 1) = init_v · exp(∫_{−ε}^{z₁−1} φ(τ) dτ)`.

We package this scalar as `aperyConifoldBoundaryConnection ε`. It is the
*connection coefficient* between the corridor right endpoint and the
Apéry physical boundary, as a function of ε. -/

/-- **Connection coefficient (corridor right endpoint → Apéry boundary).**
The closed-form scalar transporting a corridor right-endpoint datum to
the Apéry physical boundary `z = 1`. -/
noncomputable def aperyConifoldBoundaryConnection (ε : ℝ) : ℝ :=
  Real.exp (∫ τ in (-ε)..(Number.aperyConifoldZ1Poly - 1),
    (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly).eval τ /
    (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly).eval τ)

/-- The connection coefficient is strictly positive (an `exp` value). -/
lemma aperyConifoldBoundaryConnection_pos (ε : ℝ) :
    0 < aperyConifoldBoundaryConnection ε := by
  unfold aperyConifoldBoundaryConnection
  exact Real.exp_pos _

/-- **Closed-form boundary value.** The exponential extension at the
Apéry physical boundary `t = z₁ − 1` is the right-endpoint datum
multiplied by the connection coefficient. -/
@[simp] lemma aperyConifoldExpExtension_at_apery_boundary
    (ε init_v : ℝ) :
    aperyConifoldExpExtension ε init_v (Number.aperyConifoldZ1Poly - 1) =
      init_v * aperyConifoldBoundaryConnection ε := rfl

/-- **Closed-form boundary functional.** The map sending a corridor
right-endpoint datum `init_v` to the Apéry boundary value of the unique
corridor solution is the ℝ-linear functional `init_v ↦ init_v · K(ε)`
where `K(ε) = aperyConifoldBoundaryConnection ε`. The map is therefore
multiplicative-linear, and in particular vanishes iff `init_v = 0`
(since `K(ε) > 0`).

This is the structural fact underlying the connection-coefficient
extraction: the Apéry boundary value depends *linearly* on the corridor
right-endpoint datum, with a single explicit transport factor. -/
theorem aperyConifold_boundary_value_linear_in_endpoint
    (ε α β init_v₁ init_v₂ : ℝ) :
    aperyConifoldExpExtension ε (α * init_v₁ + β * init_v₂)
        (Number.aperyConifoldZ1Poly - 1) =
      α * aperyConifoldExpExtension ε init_v₁
            (Number.aperyConifoldZ1Poly - 1) +
      β * aperyConifoldExpExtension ε init_v₂
            (Number.aperyConifoldZ1Poly - 1) := by
  simp [aperyConifoldExpExtension_at_apery_boundary]
  ring

/-- **Apéry boundary value is ℝ-linear in the seed `c₀`.** Composition of
`yApery_y2_smul_c₀` (the corridor right-endpoint datum
`y₂(c₀, −ε) := 2·V'(c₀,−ε) − ε·V''(c₀,−ε)` is ℝ-linear in `c₀`) with
the closed-form transport factor `K(ε)`. This is the connection-
coefficient identity for one Frobenius branch: the boundary value at
`z = 1` (i.e. `t = z₁ − 1`) of the corridor extension of the Frobenius
solution `yApery c₀` equals `c₀ · y₂(1, −ε) · K(ε)`. -/
theorem aperyConifold_boundary_value_smul_c₀
    (ε c c₀ : ℝ) :
    aperyConifoldExpExtension ε
        (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 (c * c₀) (-ε)
          + (-ε) * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 (c * c₀) (-ε))
        (Number.aperyConifoldZ1Poly - 1) =
      c * aperyConifoldExpExtension ε
        (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ (-ε)
          + (-ε) * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ (-ε))
        (Number.aperyConifoldZ1Poly - 1) := by
  rw [yApery_y2_smul_c₀ c c₀ (-ε)]
  simp [aperyConifoldExpExtension_at_apery_boundary]
  ring

/-! ## Packaged ρ=1 boundary functional

For convenience downstream, we package the full chain
"seed `c₀` → `y₂` corridor right-endpoint datum at `t=−ε` → boundary
value at `t=z₁−1`" into a single named functional. -/

/-- **Apéry boundary functional (ρ=1 branch).** Composition of the
right-endpoint corridor datum `y₂(c₀, −ε) = 2·V'(c₀,−ε) − ε·V''(c₀,−ε)`
with the closed-form transport factor `K(ε)`. Closed form
`y₂(c₀, −ε) · K(ε)`. -/
noncomputable def aperyApéryBoundaryFunctional (ε c₀ : ℝ) : ℝ :=
  aperyConifoldExpExtension ε
    (2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ (-ε)
      + (-ε) * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₀ (-ε))
    (Number.aperyConifoldZ1Poly - 1)

/-- The packaged boundary functional is ℝ-linear in the seed `c₀`. Direct
restatement of `aperyConifold_boundary_value_smul_c₀` with the new name. -/
lemma aperyApéryBoundaryFunctional_smul_c₀
    (ε c c₀ : ℝ) :
    aperyApéryBoundaryFunctional ε (c * c₀) =
      c * aperyApéryBoundaryFunctional ε c₀ := by
  unfold aperyApéryBoundaryFunctional
  exact aperyConifold_boundary_value_smul_c₀ ε c c₀

/-- The packaged boundary functional vanishes for the zero seed. -/
@[simp] lemma aperyApéryBoundaryFunctional_zero (ε : ℝ) :
    aperyApéryBoundaryFunctional ε 0 = 0 := by
  have h := aperyApéryBoundaryFunctional_smul_c₀ ε 0 0
  rw [zero_mul, zero_mul] at h
  exact h

/-! ## Branch amplitude — explicit factorisation

For the connection-coefficient extraction we need to factor the boundary
functional as `c₀ · A(ε) · K(ε)` where `A(ε)` is a *branch amplitude*
depending only on `ε` (and the chosen indicial root), independent of the
seed `c₀`. This makes the seed-dependence completely explicit.

The branch amplitude for the `ρ = 1` Apéry conifold branch is the value
of the y₂ functional at the corridor right endpoint `t = −ε`, evaluated
at the unit seed `c₀ = 1`. -/

/-- **Branch amplitude (ρ=1).** The y₂ value at the corridor right
endpoint `t = −ε` evaluated at seed `c₀ = 1`. By scalar linearity of the
y₂ functional in the seed, every other seed reduces to `c₀ · A_one(ε)`. -/
noncomputable def aperyBranchAmplitude_one (ε : ℝ) : ℝ :=
  2 * frobeniusValueDeriv (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε)
    + (-ε) * frobeniusValueDeriv2 (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε)

/-- **Closed-form factorisation.** The packaged boundary functional
factors as `c₀ · A_one(ε) · K(ε)`, exhibiting the seed dependence as a
single scalar multiplication. -/
theorem aperyApéryBoundaryFunctional_factor (ε c₀ : ℝ) :
    aperyApéryBoundaryFunctional ε c₀ =
      c₀ * aperyBranchAmplitude_one ε *
        aperyConifoldBoundaryConnection ε := by
  unfold aperyApéryBoundaryFunctional aperyBranchAmplitude_one
  have hc : c₀ = c₀ * 1 := (mul_one c₀).symm
  conv_lhs => rw [hc]
  rw [yApery_y2_smul_c₀ c₀ 1 (-ε)]
  simp [aperyConifoldExpExtension_at_apery_boundary]

/-- **Branch amplitude at ε = 0.** Limit value of the ρ=1 amplitude as the
corridor right endpoint approaches the conifold. Reduces to a single
Frobenius coefficient: `A_one(0) = 2 · c₁` where `c₁ := frobeniusCoeff (...) 1`
is the index-1 Frobenius coefficient at unit seed. The `(-ε)·V''(...)`
term vanishes at `ε = 0`. -/
@[simp] lemma aperyBranchAmplitude_one_at_zero :
    aperyBranchAmplitude_one 0 =
      2 * frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 1 := by
  unfold aperyBranchAmplitude_one
  rw [show ((-0 : ℝ)) = 0 from neg_zero]
  rw [frobeniusValueDeriv_zero, frobeniusValueDeriv2_zero]
  ring

/-- **Vanishing characterisation.** The packaged ρ=1 boundary functional
vanishes iff either the seed `c₀` or the branch amplitude `A_one(ε)` is
zero. Direct from the closed-form factorisation `c₀ · A · K` together
with `K(ε) > 0`. -/
theorem aperyApéryBoundaryFunctional_eq_zero_iff (ε c₀ : ℝ) :
    aperyApéryBoundaryFunctional ε c₀ = 0 ↔
      c₀ = 0 ∨ aperyBranchAmplitude_one ε = 0 := by
  rw [aperyApéryBoundaryFunctional_factor]
  have hK := aperyConifoldBoundaryConnection_pos ε
  have hK_ne : aperyConifoldBoundaryConnection ε ≠ 0 := ne_of_gt hK
  rw [mul_eq_zero, mul_eq_zero]
  refine ⟨?_, ?_⟩
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hK_ne
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)

/-- **Sign characterisation.** The boundary functional's sign matches the
sign of the seed-amplitude product `c₀ · A_one(ε)`, since `K(ε) > 0`. -/
lemma aperyApéryBoundaryFunctional_pos_iff (ε c₀ : ℝ) :
    0 < aperyApéryBoundaryFunctional ε c₀ ↔
      0 < c₀ * aperyBranchAmplitude_one ε := by
  rw [aperyApéryBoundaryFunctional_factor]
  exact mul_pos_iff_of_pos_right (aperyConifoldBoundaryConnection_pos ε)

/-- **Boundary functional at `ε = 0`.** Combining
`aperyApéryBoundaryFunctional_factor` with
`aperyBranchAmplitude_one_at_zero` gives the explicit form
`func(0, c₀) = c₀ · (2 · c₁_unit) · K(0)`,
where `c₁_unit := frobeniusCoeff (...) 1 1 1` is the index-1 Frobenius
coefficient at unit seed. This is the limiting value of the ρ=1
boundary chain as the corridor shrinks to the conifold. -/
@[simp] lemma aperyApéryBoundaryFunctional_at_zero (c₀ : ℝ) :
    aperyApéryBoundaryFunctional 0 c₀ =
      c₀ *
        (2 * frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 1) *
        aperyConifoldBoundaryConnection 0 := by
  rw [aperyApéryBoundaryFunctional_factor, aperyBranchAmplitude_one_at_zero]

/-- **Index-1 Frobenius coefficient at unit seed (ρ=1 branch).**
Named alias for the apery conifold's first nontrivial Frobenius
coefficient at indicial root `1`, with seed normalised to `1`.
This is the structural building block that the corridor amplitude
limits to: `A_one(0) = 2 · aperyFrobeniusOneCoeff_unit`. -/
noncomputable def aperyFrobeniusOneCoeff_unit : ℝ :=
  frobeniusCoeff (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 1

/-- The amplitude at `ε = 0` in terms of the named alias. -/
lemma aperyBranchAmplitude_one_at_zero' :
    aperyBranchAmplitude_one 0 = 2 * aperyFrobeniusOneCoeff_unit := by
  rw [aperyBranchAmplitude_one_at_zero]
  rfl

/-- The boundary functional at `ε = 0` in terms of the named alias. -/
lemma aperyApéryBoundaryFunctional_at_zero' (c₀ : ℝ) :
    aperyApéryBoundaryFunctional 0 c₀ =
      c₀ * (2 * aperyFrobeniusOneCoeff_unit) *
        aperyConifoldBoundaryConnection 0 := by
  rw [aperyApéryBoundaryFunctional_at_zero]
  rfl

/-- **ρ=0 branch amplitude at corridor right endpoint.** Since the
ρ=0 Frobenius branch is `V₀(c₀, t)` with no leading factor, the
"amplitude" reduces to a direct evaluation: `V₀(1, −ε)`. The value of
the unit-seed regular Frobenius series at `t = −ε`. -/
noncomputable def aperyBranchAmplitude_zero (ε : ℝ) : ℝ :=
  frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 1 (-ε)

/-- **Seed factorisation of the ρ=0 branch at corridor right endpoint.**
For any seed `c₀`, `yAperyZero c₀ (−ε) = c₀ · aperyBranchAmplitude_zero ε`.
Direct from `frobeniusValue_smul_c₀` with the simple-zero hypothesis at
the conifold. -/
lemma yAperyZero_at_neg_eps (ε c₀ : ℝ) :
    yAperyZero c₀ (-ε) = c₀ * aperyBranchAmplitude_zero ε := by
  unfold yAperyZero aperyBranchAmplitude_zero
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  have h := frobeniusValue_smul_c₀ (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 0 c₀ 1 hpk (-ε)
  rw [mul_one] at h
  exact h

/-- **ρ=0 amplitude at `ε = 0`.** Reduces to the seed value `1`.
At the conifold itself `V₀(1, 0) = 1` by `frobeniusValue_zero`. -/
@[simp] lemma aperyBranchAmplitude_zero_at_zero :
    aperyBranchAmplitude_zero 0 = 1 := by
  unfold aperyBranchAmplitude_zero
  rw [neg_zero, frobeniusValue_zero]

/-- **Continuity of the ρ=0 branch amplitude on a Frobenius disk.** Wraps
`frobeniusValue_continuousOn_general` (which admits `Q(z₁) ≠ 0` via the
threshold condition) and composes with the sign flip `ε ↦ −ε`. -/
lemma aperyBranchAmplitude_zero_continuousOn_general
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(0 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(0 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    ContinuousOn aperyBranchAmplitude_zero (Set.Icc (-s) s) := by
  unfold aperyBranchAmplitude_zero
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(0 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(0 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hthresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hs_lt' : s * (1 + 2 * (((2 + 2 : ℕ) : ℝ)) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    rw [hps3]
    have : ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [this]
    have h2 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h2]
    exact hs_lt
  have hcont :
      ContinuousOn (fun t => frobeniusValue
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 0 1 t) (Set.Icc (-s) s) :=
    frobeniusValue_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 0 1 M₀ hpk hslope
      hM0_small' hM0_large' hthresh' B hB_nn hB s hs_nn hs_lt'
  have hneg : ContinuousOn (fun ε : ℝ => -ε) (Set.Icc (-s) s) :=
    continuous_neg.continuousOn
  have hmaps : Set.MapsTo (fun ε : ℝ => -ε) (Set.Icc (-s) s) (Set.Icc (-s) s) := by
    intro ε hε
    rw [Set.mem_Icc] at hε ⊢
    constructor
    · linarith
    · linarith
  exact hcont.comp hneg hmaps

/-- **ρ=0 branch amplitude — shift decomposition.** Wraps
`frobeniusValue_eq_c0_add_t_mul_tail_general` for the apery instance:
under the disk hypothesis `|ε|·K < 1`, the regular branch amplitude
splits as `1 + (−ε) · tail(ε)`, where `tail(ε)` is the formal series
`Σ aₘ₊₁ · (−ε)ᵐ`. Quantitative basis for any `|aperyBranchAmplitude_zero ε − 1|`
bound, since `|tail(ε)|` is itself bounded by the geometric envelope. -/
lemma aperyBranchAmplitude_zero_eq_one_add_eps_tail
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(0 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(0 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    aperyBranchAmplitude_zero ε =
      1 + (-ε) * ∑' m, frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 0 1 (m + 1) * (-ε) ^ m := by
  unfold aperyBranchAmplitude_zero
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(0 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(0 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hthresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hε' : |(-ε)| * (1 + 2 * (((2 + 2 : ℕ) : ℝ)) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    rw [hps3, abs_neg]
    have h4 : ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [h4]
    have h2 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h2]
    exact hε
  exact frobeniusValue_eq_c0_add_t_mul_tail_general
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
    Number.aperyConifoldZ1Poly 0 1 M₀ hpk hslope
    hM0_small' hM0_large' hthresh' B hB_nn hB (-ε) hε'

/-- **ρ=0 deviation form.** Algebraic restatement of
`aperyBranchAmplitude_zero_eq_one_add_eps_tail`:
`aperyBranchAmplitude_zero ε − 1 = (−ε) · tail(ε)`.
The "deviation from 1" is exactly `−ε` times the tail series. -/
lemma aperyBranchAmplitude_zero_sub_one_eq
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(0 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(0 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    aperyBranchAmplitude_zero ε - 1 =
      (-ε) * ∑' m, frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 0 1 (m + 1) * (-ε) ^ m := by
  have h := aperyBranchAmplitude_zero_eq_one_add_eps_tail
    M₀ B hB_nn hM0_small hM0_large hM0_thresh hB ε hε
  linarith

/-- **ρ=0 deviation magnitude.** From the deviation form, the absolute
value of `aperyBranchAmplitude_zero ε − 1` equals `|ε|` times the
tail magnitude. Bounds on the tail propagate directly to bounds on
the core deviation. -/
lemma aperyBranchAmplitude_zero_abs_sub_one_eq
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(0 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(0 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    |aperyBranchAmplitude_zero ε - 1| =
      |ε| * |∑' m, frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 0 1 (m + 1) * (-ε) ^ m| := by
  rw [aperyBranchAmplitude_zero_sub_one_eq M₀ B hB_nn hM0_small hM0_large
    hM0_thresh hB ε hε, abs_mul, abs_neg]

/-- **ρ=0 deviation upper bound.** Combining
`aperyBranchAmplitude_zero_abs_sub_one_eq` with the tail tsum sup-norm
bound `frobeniusCoeff_tail_tsum_abs_le_general` controls the deviation
of the ρ=0 amplitude from `1`:
`|A_0(ε) − 1| ≤ |ε| · ∑ |fc(m+1)| · |ε|^m`.
This is the analytic input that drives quantitative non-vanishing of
`aperyBranchAmplitude_zero` near the corridor right endpoint. -/
lemma aperyBranchAmplitude_zero_abs_sub_one_le
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(0 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(0 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    |aperyBranchAmplitude_zero ε - 1| ≤
      |ε| * ∑' m, |frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 0 1 (m + 1)| * |ε| ^ m := by
  rw [aperyBranchAmplitude_zero_abs_sub_one_eq M₀ B hB_nn hM0_small hM0_large
    hM0_thresh hB ε hε]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg ε)
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(0 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(0 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hthresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hε' : |(-ε)| * (1 + 2 * (((2 + 2 : ℕ) : ℝ)) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    rw [hps3, abs_neg]
    have h4 : ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [h4]
    have h2 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h2]
    exact hε
  have h := frobeniusCoeff_tail_tsum_abs_le_general
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
    Number.aperyConifoldZ1Poly 0 1 M₀ hpk hslope hM0_small' hM0_large' hthresh'
    B hB_nn hB (-ε) hε'
  rw [abs_neg] at h
  exact h

/-- **ρ=0 core positivity from a deviation bound.** If the explicit
tail tsum at scale `|ε|` times `|ε|` falls below `1`, then the ρ=0
amplitude is strictly positive — in particular non-vanishing. This is
the analytic-to-algebraic bridge: bounds on the Frobenius coefficient
tail propagate to actual non-vanishing of the branch amplitude. -/
lemma aperyBranchAmplitude_zero_pos_of_dev_bound
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(0 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(0 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(0 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (hdev : |ε| * ∑' m, |frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 0 1 (m + 1)| * |ε| ^ m < 1) :
    0 < aperyBranchAmplitude_zero ε := by
  have hbound := aperyBranchAmplitude_zero_abs_sub_one_le M₀ B hB_nn hM0_small
    hM0_large hM0_thresh hB ε hε
  have h_lt : |aperyBranchAmplitude_zero ε - 1| < 1 := hbound.trans_lt hdev
  have habs := abs_lt.mp h_lt
  linarith [habs.1]

/-- **ρ=1/2 branch amplitude at corridor right endpoint.** The
ρ=1/2 Frobenius branch carries a leading `√(-t)` factor, so at
`t = −ε` (with `ε ≥ 0`) the amplitude reads
`√ε · V_{1/2}(1, −ε)`. -/
noncomputable def aperyBranchAmplitude_half (ε : ℝ) : ℝ :=
  Real.sqrt ε * frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε)

/-- **Seed factorisation of the ρ=1/2 branch at corridor right endpoint.**
`yAperyHalf c_half (−ε) = c_half · aperyBranchAmplitude_half ε`.
The `√ε` agrees with `√(−(−ε))` regardless of the sign of `ε`. -/
lemma yAperyHalf_at_neg_eps (ε c_half : ℝ) :
    yAperyHalf c_half (-ε) = c_half * aperyBranchAmplitude_half ε := by
  unfold yAperyHalf aperyBranchAmplitude_half
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  have h := frobeniusValue_smul_c₀ (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) c_half 1 hpk (-ε)
  rw [mul_one] at h
  rw [h, show (-(-ε)) = ε from by ring]
  ring

/-- **ρ=1/2 amplitude at `ε = 0`.** Vanishes because of the `√ε` factor
multiplying a finite quantity. -/
@[simp] lemma aperyBranchAmplitude_half_at_zero :
    aperyBranchAmplitude_half 0 = 0 := by
  unfold aperyBranchAmplitude_half
  rw [Real.sqrt_zero, zero_mul]

/-- **ρ=1 branch value at corridor right endpoint** (NOT the y₂
amplitude — that is `aperyBranchAmplitude_one`). Carries the explicit
`(−ε)` prefactor: `yApery c₁ (−ε) = c₁ · (−ε) · V₁(1, −ε)`. -/
noncomputable def aperyBranchValue_one (ε : ℝ) : ℝ :=
  (-ε) * frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε)

/-- **Seed factorisation of the ρ=1 branch value at corridor right
endpoint.** -/
lemma yApery_at_neg_eps (ε c₁ : ℝ) :
    yApery c₁ (-ε) = c₁ * aperyBranchValue_one ε := by
  unfold yApery aperyBranchValue_one
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := Number.aperyPconifold_eval_z1
  have h := frobeniusValue_smul_c₀ (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 c₁ 1 hpk (-ε)
  rw [mul_one] at h
  rw [h]
  ring

/-- **ρ=1 branch value at `ε = 0`.** Vanishes via the `(−ε)` factor. -/
@[simp] lemma aperyBranchValue_one_at_zero :
    aperyBranchValue_one 0 = 0 := by
  unfold aperyBranchValue_one
  rw [neg_zero, zero_mul]

/-- **Inner ρ=1/2 Frobenius series (no `√ε` prefactor).** The bare
`V_{1/2}(1, −ε)` series sum, used to expose the leading-order
`A_½(ε) = √ε · (1 + O(ε))` structure for non-vanishing arguments. -/
noncomputable def aperyBranchHalfCore (ε : ℝ) : ℝ :=
  frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε)

/-- **Half-core at the conifold itself equals `1`.** Direct from
`frobeniusValue_zero`: the m=0 series term is the seed `c₀ = 1`. -/
@[simp] lemma aperyBranchHalfCore_at_zero :
    aperyBranchHalfCore 0 = 1 := by
  unfold aperyBranchHalfCore
  rw [neg_zero, frobeniusValue_zero]

/-- **Continuity of the inner ρ=1/2 Frobenius series on a Frobenius disk.**
Same skeleton as `aperyBranchAmplitude_zero_continuousOn_general`, with
`ρ = 1/2`. The bare core has no `√ε` factor, so continuity follows
directly from `frobeniusValue_continuousOn_general` composed with `ε ↦ −ε`. -/
lemma aperyBranchHalfCore_continuousOn_general
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    ContinuousOn aperyBranchHalfCore (Set.Icc (-s) s) := by
  unfold aperyBranchHalfCore
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hthresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hs_lt' : s * (1 + 2 * (((2 + 2 : ℕ) : ℝ)) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    rw [hps3]
    have : ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [this]
    have h2 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h2]
    exact hs_lt
  have hcont :
      ContinuousOn (fun t => frobeniusValue
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly (1 / 2) 1 t) (Set.Icc (-s) s) :=
    frobeniusValue_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly (1 / 2) 1 M₀ hpk hslope
      hM0_small' hM0_large' hthresh' B hB_nn hB s hs_nn hs_lt'
  have hneg : ContinuousOn (fun ε : ℝ => -ε) (Set.Icc (-s) s) :=
    continuous_neg.continuousOn
  have hmaps : Set.MapsTo (fun ε : ℝ => -ε) (Set.Icc (-s) s) (Set.Icc (-s) s) := by
    intro ε hε
    rw [Set.mem_Icc] at hε ⊢
    constructor
    · linarith
    · linarith
  exact hcont.comp hneg hmaps

/-- **Factored form of the ρ=1/2 amplitude.** `A_½(ε) = √ε · core`. By
definition. -/
lemma aperyBranchAmplitude_half_factored (ε : ℝ) :
    aperyBranchAmplitude_half ε = Real.sqrt ε * aperyBranchHalfCore ε := rfl

/-- **Continuity of the ρ=1/2 branch amplitude on a Frobenius disk.**
Lifts `aperyBranchHalfCore_continuousOn_general` by multiplying with the
continuous `√ε` factor (`Real.continuous_sqrt`). -/
lemma aperyBranchAmplitude_half_continuousOn_general
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    ContinuousOn aperyBranchAmplitude_half (Set.Icc (-s) s) := by
  have hcore : ContinuousOn aperyBranchHalfCore (Set.Icc (-s) s) :=
    aperyBranchHalfCore_continuousOn_general M₀ B hB_nn
      hM0_small hM0_large hM0_thresh hB s hs_nn hs_lt
  have hsqrt : ContinuousOn (fun ε : ℝ => Real.sqrt ε) (Set.Icc (-s) s) :=
    Real.continuous_sqrt.continuousOn
  have hprod :
      ContinuousOn (fun ε : ℝ => Real.sqrt ε * aperyBranchHalfCore ε)
        (Set.Icc (-s) s) := hsqrt.mul hcore
  exact hprod.congr (fun ε _ => (aperyBranchAmplitude_half_factored ε).symm)

/-- **Half-core — shift decomposition.** Mirror of
`aperyBranchAmplitude_zero_eq_one_add_eps_tail` with `ρ = 1/2`. Under
the disk hypothesis, `aperyBranchHalfCore ε = 1 + (−ε)·tail_{1/2}(ε)`. -/
lemma aperyBranchHalfCore_eq_one_add_eps_tail
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    aperyBranchHalfCore ε =
      1 + (-ε) * ∑' m, frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly (1 / 2) 1 (m + 1) * (-ε) ^ m := by
  unfold aperyBranchHalfCore
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hthresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hε' : |(-ε)| * (1 + 2 * (((2 + 2 : ℕ) : ℝ)) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    rw [hps3, abs_neg]
    have h4 : ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [h4]
    have h2 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h2]
    exact hε
  exact frobeniusValue_eq_c0_add_t_mul_tail_general
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
    Number.aperyConifoldZ1Poly (1 / 2) 1 M₀ hpk hslope
    hM0_small' hM0_large' hthresh' B hB_nn hB (-ε) hε'

/-- **Half-core deviation form.** Algebraic restatement of
`aperyBranchHalfCore_eq_one_add_eps_tail`. -/
lemma aperyBranchHalfCore_sub_one_eq
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    aperyBranchHalfCore ε - 1 =
      (-ε) * ∑' m, frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly (1 / 2) 1 (m + 1) * (-ε) ^ m := by
  have h := aperyBranchHalfCore_eq_one_add_eps_tail
    M₀ B hB_nn hM0_small hM0_large hM0_thresh hB ε hε
  linarith

/-- **Half-core deviation magnitude.** -/
lemma aperyBranchHalfCore_abs_sub_one_eq
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    |aperyBranchHalfCore ε - 1| =
      |ε| * |∑' m, frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly (1 / 2) 1 (m + 1) * (-ε) ^ m| := by
  rw [aperyBranchHalfCore_sub_one_eq M₀ B hB_nn hM0_small hM0_large
    hM0_thresh hB ε hε, abs_mul, abs_neg]

/-- **Half-core deviation upper bound.** -/
lemma aperyBranchHalfCore_abs_sub_one_le
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    |aperyBranchHalfCore ε - 1| ≤
      |ε| * ∑' m, |frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly (1 / 2) 1 (m + 1)| * |ε| ^ m := by
  rw [aperyBranchHalfCore_abs_sub_one_eq M₀ B hB_nn hM0_small hM0_large
    hM0_thresh hB ε hε]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg ε)
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hthresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hε' : |(-ε)| * (1 + 2 * (((2 + 2 : ℕ) : ℝ)) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    rw [hps3, abs_neg]
    have h4 : ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [h4]
    have h2 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h2]
    exact hε
  have h := frobeniusCoeff_tail_tsum_abs_le_general
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
    Number.aperyConifoldZ1Poly (1 / 2) 1 M₀ hpk hslope hM0_small' hM0_large' hthresh'
    B hB_nn hB (-ε) hε'
  rw [abs_neg] at h
  exact h

/-- **Half-core positivity from a deviation bound.** -/
lemma aperyBranchHalfCore_pos_of_dev_bound
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (hdev : |ε| * ∑' m, |frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly (1 / 2) 1 (m + 1)| * |ε| ^ m < 1) :
    0 < aperyBranchHalfCore ε := by
  have hbound := aperyBranchHalfCore_abs_sub_one_le M₀ B hB_nn hM0_small
    hM0_large hM0_thresh hB ε hε
  have h_lt : |aperyBranchHalfCore ε - 1| < 1 := hbound.trans_lt hdev
  have habs := abs_lt.mp h_lt
  linarith [habs.1]

/-- **Inner ρ=1 Frobenius series (no `(−ε)` prefactor).** The bare
`V_1(1, −ε)` series sum, used to expose the leading-order
`V_1(ε) = (−ε) · (1 + O(ε))` structure for non-vanishing arguments. -/
noncomputable def aperyBranchOneCore (ε : ℝ) : ℝ :=
  frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε)

/-- **One-core at the conifold itself equals `1`.** Direct from
`frobeniusValue_zero`. -/
@[simp] lemma aperyBranchOneCore_at_zero :
    aperyBranchOneCore 0 = 1 := by
  unfold aperyBranchOneCore
  rw [neg_zero, frobeniusValue_zero]

/-- **One-core — shift decomposition.** Mirror of
`aperyBranchAmplitude_zero_eq_one_add_eps_tail` with `ρ = 1`. Under
the disk hypothesis, `aperyBranchOneCore ε = 1 + (−ε)·tail_1(ε)`. -/
lemma aperyBranchOneCore_eq_one_add_eps_tail
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    aperyBranchOneCore ε =
      1 + (-ε) * ∑' m, frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 1 (m + 1) * (-ε) ^ m := by
  unfold aperyBranchOneCore
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hthresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hε' : |(-ε)| * (1 + 2 * (((2 + 2 : ℕ) : ℝ)) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    rw [hps3, abs_neg]
    have h4 : ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [h4]
    have h2 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h2]
    exact hε
  exact frobeniusValue_eq_c0_add_t_mul_tail_general
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
    Number.aperyConifoldZ1Poly 1 1 M₀ hpk hslope
    hM0_small' hM0_large' hthresh' B hB_nn hB (-ε) hε'

/-- **One-core deviation form.** Algebraic restatement of
`aperyBranchOneCore_eq_one_add_eps_tail`. -/
lemma aperyBranchOneCore_sub_one_eq
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    aperyBranchOneCore ε - 1 =
      (-ε) * ∑' m, frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 1 (m + 1) * (-ε) ^ m := by
  have h := aperyBranchOneCore_eq_one_add_eps_tail
    M₀ B hB_nn hM0_small hM0_large hM0_thresh hB ε hε
  linarith

/-- **One-core deviation magnitude.** -/
lemma aperyBranchOneCore_abs_sub_one_eq
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    |aperyBranchOneCore ε - 1| =
      |ε| * |∑' m, frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 1 (m + 1) * (-ε) ^ m| := by
  rw [aperyBranchOneCore_sub_one_eq M₀ B hB_nn hM0_small hM0_large
    hM0_thresh hB ε hε, abs_mul, abs_neg]

/-- **One-core deviation upper bound.** -/
lemma aperyBranchOneCore_abs_sub_one_le
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    |aperyBranchOneCore ε - 1| ≤
      |ε| * ∑' m, |frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 1 (m + 1)| * |ε| ^ m := by
  rw [aperyBranchOneCore_abs_sub_one_eq M₀ B hB_nn hM0_small hM0_large
    hM0_thresh hB ε hε]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg ε)
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hthresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hε' : |(-ε)| * (1 + 2 * (((2 + 2 : ℕ) : ℝ)) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    rw [hps3, abs_neg]
    have h4 : ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [h4]
    have h2 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h2]
    exact hε
  have h := frobeniusCoeff_tail_tsum_abs_le_general
    (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
    Number.aperyConifoldZ1Poly 1 1 M₀ hpk hslope hM0_small' hM0_large' hthresh'
    B hB_nn hB (-ε) hε'
  rw [abs_neg] at h
  exact h

/-- **One-core positivity from a deviation bound.** -/
lemma aperyBranchOneCore_pos_of_dev_bound
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (ε : ℝ)
    (hε : |ε| * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1)
    (hdev : |ε| * ∑' m, |frobeniusCoeff
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 1 (m + 1)| * |ε| ^ m < 1) :
    0 < aperyBranchOneCore ε := by
  have hbound := aperyBranchOneCore_abs_sub_one_le M₀ B hB_nn hM0_small
    hM0_large hM0_thresh hB ε hε
  have h_lt : |aperyBranchOneCore ε - 1| < 1 := hbound.trans_lt hdev
  have habs := abs_lt.mp h_lt
  linarith [habs.1]

/-- **Continuity of the inner ρ=1 Frobenius series on a Frobenius disk.**
Same skeleton as the ρ=0 and ρ=1/2 versions, with `ρ = 1`. The bare core
has no `(−ε)` factor, so continuity follows directly from
`frobeniusValue_continuousOn_general` composed with `ε ↦ −ε`. -/
lemma aperyBranchOneCore_continuousOn_general
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    ContinuousOn aperyBranchOneCore (Set.Icc (-s) s) := by
  unfold aperyBranchOneCore
  have hps2 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2 =
      Number.aperyQconifold := rfl
  have hps3 : (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 3 =
      Number.aperyPconifold := rfl
  have hpk : ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1)).eval
      Number.aperyConifoldZ1Poly = 0 := by rw [hps3]; exact Number.aperyPconifold_eval_z1
  have hslope : (Polynomial.derivative
      ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly ≠ 0 := by
    rw [hps3]; exact Number.aperyPconifold_deriv_eval_z1_ne_zero
  have hM0_small' : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + ((2 : ℕ) : ℝ)) < ((m + 1 : ℕ) : ℝ) := by
    intro m hm
    have := hM0_small m hm
    push_cast at this ⊢
    linarith
  have hM0_large' : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * ((2 : ℕ) : ℝ) ≤ (m : ℝ) := by
    intro m hm
    have := hM0_large m hm
    push_cast at this ⊢
    linarith
  have hthresh' : ∀ m', M₀ ≤ m' →
      2 * |((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2).eval
            Number.aperyConifoldZ1Poly| ≤
        |(Polynomial.derivative
            ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
          Number.aperyConifoldZ1Poly| *
          (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - ((2 : ℕ) : ℝ)) := by
    intro m' hm'
    rw [hps2, hps3]
    have := hM0_thresh m' hm'
    push_cast at this ⊢
    linarith
  have hs_lt' : s * (1 + 2 * (((2 + 2 : ℕ) : ℝ)) * B * ((2 : ℝ) ^ (2 + 1)) /
      |(Polynomial.derivative
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) (2 + 1))).eval
        Number.aperyConifoldZ1Poly|) < 1 := by
    rw [hps3]
    have : ((2 + 2 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
    rw [this]
    have h2 : ((2 : ℝ) ^ (2 + 1)) = (2 : ℝ) ^ 3 := by norm_num
    rw [h2]
    exact hs_lt
  have hcont :
      ContinuousOn (fun t => frobeniusValue
        (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
        Number.aperyConifoldZ1Poly 1 1 t) (Set.Icc (-s) s) :=
    frobeniusValue_continuousOn_general
      (aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) 2
      Number.aperyConifoldZ1Poly 1 1 M₀ hpk hslope
      hM0_small' hM0_large' hthresh' B hB_nn hB s hs_nn hs_lt'
  have hneg : ContinuousOn (fun ε : ℝ => -ε) (Set.Icc (-s) s) :=
    continuous_neg.continuousOn
  have hmaps : Set.MapsTo (fun ε : ℝ => -ε) (Set.Icc (-s) s) (Set.Icc (-s) s) := by
    intro ε hε
    rw [Set.mem_Icc] at hε ⊢
    constructor
    · linarith
    · linarith
  exact hcont.comp hneg hmaps

/-- **Factored form of the ρ=1 branch value.** `V_1(ε) = (−ε) · core`.
By definition. -/
lemma aperyBranchValue_one_factored (ε : ℝ) :
    aperyBranchValue_one ε = (-ε) * aperyBranchOneCore ε := rfl

/-- **Continuity of the ρ=1 branch value on a Frobenius disk.** Lifts
`aperyBranchOneCore_continuousOn_general` by multiplying with the
continuous `(−ε)` factor. -/
lemma aperyBranchValue_one_continuousOn_general
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    ContinuousOn aperyBranchValue_one (Set.Icc (-s) s) := by
  have hcore : ContinuousOn aperyBranchOneCore (Set.Icc (-s) s) :=
    aperyBranchOneCore_continuousOn_general M₀ B hB_nn
      hM0_small hM0_large hM0_thresh hB s hs_nn hs_lt
  have hneg : ContinuousOn (fun ε : ℝ => -ε) (Set.Icc (-s) s) :=
    continuous_neg.continuousOn
  have hprod :
      ContinuousOn (fun ε : ℝ => (-ε) * aperyBranchOneCore ε)
        (Set.Icc (-s) s) := hneg.mul hcore
  exact hprod.congr (fun ε _ => (aperyBranchValue_one_factored ε).symm)

/-- **Three-branch combined corridor right-endpoint value.** For
`t = −ε`, the superposition reads
`triple(c₀, c_half, c₁; −ε) = c₀ · A_0(ε) + c_half · A_½(ε) + c₁ · V_1(ε)`,
each branch contributing its own seed-factored amplitude/value. -/
lemma aperyBranchTriple_at_neg_eps (ε c₀ c_half c₁ : ℝ) :
    aperyBranchTriple c₀ c_half c₁ (-ε) =
      c₀ * aperyBranchAmplitude_zero ε +
      c_half * aperyBranchAmplitude_half ε +
      c₁ * aperyBranchValue_one ε := by
  unfold aperyBranchTriple
  rw [yAperyZero_at_neg_eps, yAperyHalf_at_neg_eps, yApery_at_neg_eps]

/-- **Sanity check at ε = 0.** Specialising the combined factorisation
at `ε = 0` recovers `aperyBranchTriple_at_zero` (= `c₀`) via the
named-amplitude evaluations
`A_0(0) = 1`, `A_½(0) = 0`, `V_1(0) = 0`. -/
lemma aperyBranchTriple_at_neg_eps_zero (c₀ c_half c₁ : ℝ) :
    aperyBranchTriple c₀ c_half c₁ (-0) = c₀ := by
  rw [aperyBranchTriple_at_neg_eps,
      aperyBranchAmplitude_zero_at_zero,
      aperyBranchAmplitude_half_at_zero,
      aperyBranchValue_one_at_zero]
  ring

/-- **Linearity of the right-endpoint functional in the seed triple
(uniform smul).** Direct corollary of `aperyBranchTriple_smul` plus
the new seed factorisation. -/
lemma aperyBranchTriple_at_neg_eps_smul (ε c c₀ c_half c₁ : ℝ) :
    aperyBranchTriple (c * c₀) (c * c_half) (c * c₁) (-ε) =
      c * aperyBranchTriple c₀ c_half c₁ (-ε) :=
  aperyBranchTriple_smul c c₀ c_half c₁ (-ε)

/-- **Linearity of the right-endpoint functional in the seed triple
(componentwise add).** Direct from `aperyBranchTriple_add`. -/
lemma aperyBranchTriple_at_neg_eps_add
    (ε c₀₁ c_half₁ c₁₁ c₀₂ c_half₂ c₁₂ : ℝ) :
    aperyBranchTriple c₀₁ c_half₁ c₁₁ (-ε) +
        aperyBranchTriple c₀₂ c_half₂ c₁₂ (-ε) =
      (yAperyZero c₀₁ (-ε) + yAperyZero c₀₂ (-ε)) +
      (yAperyHalf c_half₁ (-ε) + yAperyHalf c_half₂ (-ε)) +
      (yApery c₁₁ (-ε) + yApery c₁₂ (-ε)) :=
  aperyBranchTriple_add c₀₁ c_half₁ c₁₁ c₀₂ c_half₂ c₁₂ (-ε)

/-! ## Connection-coefficient interface

Structural Prop wrapping the assertion *"the triple `(a₀, a_½, a₁)` is the
connection coefficient triple for `f` on the set `I` near the conifold"*.
The actual numerical values of the triple are transcendental
(involving `π²`, ζ-values) and live outside Mathlib; this interface
lets downstream consumers state and reason about the connection
coefficients without yet pinning them down.
-/

/-- **Connection-coefficient predicate.** A triple `(a₀, a_half, a₁)`
represents the connection coefficients of a function `f : ℝ → ℝ` on a
set `I` of `t`-values (with `t = z − z₁`) iff for every `t ∈ I`,
`f(z₁ + t) = aperyBranchTriple a₀ a_half a₁ t`.

This is the abstract carrier; specific instantiations (e.g., for the
ζ(3) sum-of-cubes generating function) require analytic continuation
machinery and transcendental coefficient values, both deferred. -/
def IsAperyConnectionCoeffsOn
    (a₀ a_half a₁ : ℝ) (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) =
    aperyBranchTriple a₀ a_half a₁ t

/-- **Linearity of the connection-coefficient predicate (smul).** If
`(a₀, a_half, a₁)` represents `f` on `I`, then for any `c : ℝ`,
`(c·a₀, c·a_half, c·a₁)` represents `c·f` on `I`. -/
lemma IsAperyConnectionCoeffsOn.smul
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ} (c : ℝ)
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) :
    IsAperyConnectionCoeffsOn (c * a₀) (c * a_half) (c * a₁)
      (fun z => c * f z) I := by
  intro t ht
  simp only
  rw [h t ht, aperyBranchTriple_smul]

/-- **Linearity of the connection-coefficient predicate (add).** The
predicate is additive in `(triple, f)`: triples for `f` and `g` on the
same domain combine to a triple for `f + g`. -/
lemma IsAperyConnectionCoeffsOn.add
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hg : IsAperyConnectionCoeffsOn b₀ b_half b₁ g I) :
    IsAperyConnectionCoeffsOn (a₀ + b₀) (a_half + b_half) (a₁ + b₁)
      (fun z => f z + g z) I := by
  intro t ht
  simp only
  rw [hf t ht, hg t ht, ← aperyBranchTriple_add_seeds]

/-- **Seed-subtractivity of the branch triple.** Direct corollary of
seed-additivity composed with seed-scaling by `−1`. -/
lemma aperyBranchTriple_sub_seeds
    (a₀ a_h a₁ b₀ b_h b₁ t : ℝ) :
    aperyBranchTriple (a₀ - b₀) (a_h - b_h) (a₁ - b₁) t =
      aperyBranchTriple a₀ a_h a₁ t - aperyBranchTriple b₀ b_h b₁ t := by
  have hadd := aperyBranchTriple_add_seeds a₀ a_h a₁ (-b₀) (-b_h) (-b₁) t
  have hneg : aperyBranchTriple (-b₀) (-b_h) (-b₁) t =
      -aperyBranchTriple b₀ b_h b₁ t := by
    have h := aperyBranchTriple_smul (-1) b₀ b_h b₁ t
    have e1 : (-1 : ℝ) * b₀ = -b₀ := by ring
    have e2 : (-1 : ℝ) * b_h = -b_h := by ring
    have e3 : (-1 : ℝ) * b₁ = -b₁ := by ring
    rw [e1, e2, e3] at h
    linarith [h]
  have e1 : a₀ + -b₀ = a₀ - b₀ := by ring
  have e2 : a_h + -b_h = a_h - b_h := by ring
  have e3 : a₁ + -b₁ = a₁ - b₁ := by ring
  rw [e1, e2, e3, hneg] at hadd
  linarith [hadd]

/-- **Linearity (sub).** Direct from `add` (or seed-subtractivity). -/
lemma IsAperyConnectionCoeffsOn.sub
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hg : IsAperyConnectionCoeffsOn b₀ b_half b₁ g I) :
    IsAperyConnectionCoeffsOn (a₀ - b₀) (a_half - b_half) (a₁ - b₁)
      (fun z => f z - g z) I := by
  intro t ht
  simp only
  rw [hf t ht, hg t ht, aperyBranchTriple_sub_seeds]

/-- **Domain union.** A triple representing `f` on both `I` and `J`
represents it on `I ∪ J`. Useful when corridor and right-of-conifold
patches are proved separately. -/
lemma IsAperyConnectionCoeffsOn.union
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I J : Set ℝ}
    (hI : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hJ : IsAperyConnectionCoeffsOn a₀ a_half a₁ f J) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁ f (I ∪ J) := by
  intro t ht
  rcases ht with ht | ht
  · exact hI t ht
  · exact hJ t ht

/-- **Domain intersection.** Restriction to either factor. -/
lemma IsAperyConnectionCoeffsOn.inter_left
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I J : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁ f (I ∩ J) :=
  fun t ht => h t ht.1

lemma IsAperyConnectionCoeffsOn.inter_right
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I J : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f J) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁ f (I ∩ J) :=
  fun t ht => h t ht.2

/-- **Empty domain.** Vacuously, any triple represents any function on
the empty set. -/
@[simp] lemma IsAperyConnectionCoeffsOn.empty
    (a₀ a_half a₁ : ℝ) (f : ℝ → ℝ) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁ f ∅ :=
  fun _ ht => (ht).elim

/-- **Singleton domain at zero.** Reduces to a single equation
`f(z₁) = a₀`; the singular pair is unconstrained. -/
lemma IsAperyConnectionCoeffsOn.singleton_zero_iff
    (a₀ a_half a₁ : ℝ) (f : ℝ → ℝ) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁ f {0} ↔
      f Number.aperyConifoldZ1Poly = a₀ := by
  constructor
  · intro h
    have := h 0 rfl
    rw [add_zero, aperyBranchTriple_at_zero] at this
    exact this
  · intro h t ht
    rcases ht with rfl
    rw [add_zero, aperyBranchTriple_at_zero, h]

/-- **Common-triple agreement.** If the same triple `(a₀, a_half, a₁)`
represents both `f` and `g` on `I`, they agree on `z₁ + I`. Both
predicates pin down the shifted function to the canonical
`aperyBranchTriple`, so `f = g` there. -/
lemma IsAperyConnectionCoeffsOn.f_eq_g_of_common_triple
    {a₀ a_half a₁ : ℝ} {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hg : IsAperyConnectionCoeffsOn a₀ a_half a₁ g I) :
    ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) =
              g (Number.aperyConifoldZ1Poly + t) := by
  intro t ht
  rw [hf t ht, hg t ht]

/-- **Function congruence.** If `f` and `g` agree on `z₁ + I`, the
predicate transfers from `f` to `g`. -/
lemma IsAperyConnectionCoeffsOn.congr
    {a₀ a_half a₁ : ℝ} {f g : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hfg : ∀ t ∈ I,
      f (Number.aperyConifoldZ1Poly + t) = g (Number.aperyConifoldZ1Poly + t)) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁ g I := by
  intro t ht
  rw [← hfg t ht, h t ht]

/-- **Iff characterisation via shifted equality.** The predicate is
exactly pointwise agreement of the shifted function with the canonical
branch triple. Combines `shifted_eq` and `of_shifted_eqOn`. -/
lemma IsAperyConnectionCoeffsOn.iff_shifted_eqOn
    (a₀ a_half a₁ : ℝ) (f : ℝ → ℝ) (I : Set ℝ) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁ f I ↔
      Set.EqOn (fun t => f (Number.aperyConifoldZ1Poly + t))
        (fun t => aperyBranchTriple a₀ a_half a₁ t) I :=
  Iff.rfl

/-- **Negation atom.** Sign-flip the triple together with the function. -/
lemma IsAperyConnectionCoeffsOn.neg
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) :
    IsAperyConnectionCoeffsOn (-a₀) (-a_half) (-a₁) (fun z => -(f z)) I := by
  have := h.smul (-1)
  simp only [neg_one_mul] at this
  exact this

/-- **Zero-triple iff zero-shift.** `(0,0,0)` represents `f` iff `f`
vanishes on `z₁ + I`. -/
lemma IsAperyConnectionCoeffsOn.zero_iff
    (f : ℝ → ℝ) (I : Set ℝ) :
    IsAperyConnectionCoeffsOn 0 0 0 f I ↔
      ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) = 0 := by
  constructor
  · intro h t ht
    have := h t ht
    rwa [aperyBranchTriple_zero] at this
  · intro h t ht
    rw [aperyBranchTriple_zero, h t ht]

/-- **Connection-coefficient extraction at the conifold (regular
component).** If `(a₀, a_half, a₁)` represents `f` on a set `I`
containing `0`, then `a₀ = f(z₁)`. Direct from `aperyBranchTriple_at_zero`. -/
lemma IsAperyConnectionCoeffsOn.regular_seed
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I) :
    f Number.aperyConifoldZ1Poly = a₀ := by
  have := h 0 h0
  rw [add_zero] at this
  rw [this, aperyBranchTriple_at_zero]

/-- **Right-endpoint value via connection coefficients.** If
`(a₀, a_half, a₁)` represents `f` on a set `I` containing `−ε`, then
`f(z₁ − ε) = a₀ · A_0(ε) + a_half · A_½(ε) + a₁ · V_1(ε)`. -/
lemma IsAperyConnectionCoeffsOn.right_endpoint
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε : ℝ} (hε : (-ε) ∈ I) :
    f (Number.aperyConifoldZ1Poly + (-ε)) =
      a₀ * aperyBranchAmplitude_zero ε +
      a_half * aperyBranchAmplitude_half ε +
      a₁ * aperyBranchValue_one ε := by
  rw [h (-ε) hε, aperyBranchTriple_at_neg_eps]

/-- **Restriction to a smaller domain.** If `(a₀, a_half, a₁)`
represents `f` on `I` and `J ⊆ I`, then it represents `f` on `J`. -/
lemma IsAperyConnectionCoeffsOn.mono
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I J : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (hJI : J ⊆ I) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁ f J :=
  fun t ht => h t (hJI ht)

/-- **Pure regular branch.** If `f(z) = a₀ · V₀(1, z − z₁)` on `I`, then
`(a₀, 0, 0)` represents `f` on `I`. -/
lemma IsAperyConnectionCoeffsOn.of_pure_regular
    (a₀ : ℝ) (f : ℝ → ℝ) (I : Set ℝ)
    (h : ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) = yAperyZero a₀ t) :
    IsAperyConnectionCoeffsOn a₀ 0 0 f I := by
  intro t ht
  rw [h t ht, aperyBranchTriple_only_zero_branch]

/-- **Pure ρ=1 branch.** If `f(z) = a₁ · t · V_1(1, z − z₁)` on `I`,
then `(0, 0, a₁)` represents `f` on `I`. -/
lemma IsAperyConnectionCoeffsOn.of_pure_one
    (a₁ : ℝ) (f : ℝ → ℝ) (I : Set ℝ)
    (h : ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) = yApery a₁ t) :
    IsAperyConnectionCoeffsOn 0 0 a₁ f I := by
  intro t ht
  rw [h t ht, aperyBranchTriple_only_one_branch]

/-- **Pure ρ=1/2 branch.** If `f(z) = a_half · √(−t) · V_{1/2}(1, z − z₁)`
on `I`, then `(0, a_half, 0)` represents `f` on `I`. -/
lemma IsAperyConnectionCoeffsOn.of_pure_half
    (a_half : ℝ) (f : ℝ → ℝ) (I : Set ℝ)
    (h : ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) = yAperyHalf a_half t) :
    IsAperyConnectionCoeffsOn 0 a_half 0 f I := by
  intro t ht
  rw [h t ht, aperyBranchTriple_only_half_branch]

/-- **Three-pure-branch composition.** Given separate pure-branch
witnesses (one per indicial root), the pointwise sum represents the
combined triple. Constructive companion to `add` — corresponds to
the canonical decomposition `f = f_0 + f_½ + f_1`. -/
lemma IsAperyConnectionCoeffsOn.of_three_pure
    (a₀ a_half a₁ : ℝ) (Y₀ Y_half Y_one : ℝ → ℝ) (I : Set ℝ)
    (hY₀ : ∀ t ∈ I,
      Y₀ (Number.aperyConifoldZ1Poly + t) = yAperyZero a₀ t)
    (hY_half : ∀ t ∈ I,
      Y_half (Number.aperyConifoldZ1Poly + t) = yAperyHalf a_half t)
    (hY_one : ∀ t ∈ I,
      Y_one (Number.aperyConifoldZ1Poly + t) = yApery a₁ t) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁
      (fun z => Y₀ z + Y_half z + Y_one z) I := by
  intro t ht
  simp only
  rw [hY₀ t ht, hY_half t ht, hY_one t ht]
  rfl

/-- **Zero triple represents the zero function.** Trivial constructor:
the all-zero triple `(0, 0, 0)` represents the constant-zero function
on any set. -/
lemma IsAperyConnectionCoeffsOn.zero (I : Set ℝ) :
    IsAperyConnectionCoeffsOn 0 0 0 (fun _ => (0 : ℝ)) I := by
  intro t _
  rw [aperyBranchTriple_zero]

/-- **Two triples agreeing on a set with `0 ∈ I` must share `a₀`.**
Necessary condition for connection-coefficient uniqueness: any two
representations of the same function pin down the regular-branch seed
to `f(z₁)`. The other components require additional witness data
(separated points, continuity, etc.). -/
lemma IsAperyConnectionCoeffsOn.regular_unique
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hb : IsAperyConnectionCoeffsOn b₀ b_half b₁ f I)
    (h0 : (0 : ℝ) ∈ I) :
    a₀ = b₀ := by
  have ha0 := ha.regular_seed h0
  have hb0 := hb.regular_seed h0
  linarith

/-- **Shifted form of the predicate.** Defining
`f_sh(t) := f(z₁ + t)`, the predicate reads
`f_sh = aperyBranchTriple a₀ a_half a₁` pointwise on `I`. -/
lemma IsAperyConnectionCoeffsOn.shifted_eq
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) :
    Set.EqOn (fun t => f (Number.aperyConifoldZ1Poly + t))
      (fun t => aperyBranchTriple a₀ a_half a₁ t) I := h

/-- **EqOn-form constructor.** A function whose shift agrees with the
branch triple on `I` satisfies the connection predicate. -/
lemma IsAperyConnectionCoeffsOn.of_shifted_eqOn
    (a₀ a_half a₁ : ℝ) (f : ℝ → ℝ) (I : Set ℝ)
    (h : Set.EqOn (fun t => f (Number.aperyConifoldZ1Poly + t))
      (fun t => aperyBranchTriple a₀ a_half a₁ t) I) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁ f I := h

/-- **Singular-pair difference at the right endpoint.** If two triples
represent the same `f` on `I`, and `0 ∈ I` (so `a₀ = b₀`), then for any
`−ε ∈ I` the singular pair satisfies the algebraic constraint
`(a_half − b_half) · A_½(ε) + (a₁ − b₁) · V_1(ε) = 0`.
This is the algebraic atom for ρ=1/2, ρ=1 uniqueness once two distinct
witnesses (different ε) are exhibited. -/
lemma IsAperyConnectionCoeffsOn.singular_difference
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hb : IsAperyConnectionCoeffsOn b₀ b_half b₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε : ℝ} (hε : (-ε) ∈ I) :
    (a_half - b_half) * aperyBranchAmplitude_half ε +
      (a₁ - b₁) * aperyBranchValue_one ε = 0 := by
  have ha₀ := ha.regular_unique hb h0
  have ha_eps := ha.right_endpoint hε
  have hb_eps := hb.right_endpoint hε
  have heq : a₀ * aperyBranchAmplitude_zero ε +
        a_half * aperyBranchAmplitude_half ε +
        a₁ * aperyBranchValue_one ε =
      b₀ * aperyBranchAmplitude_zero ε +
        b_half * aperyBranchAmplitude_half ε +
        b₁ * aperyBranchValue_one ε := by
    rw [← ha_eps, ← hb_eps]
  rw [ha₀] at heq
  linarith

/-- **Singular-pair determinant unfolding.** Explicit factorisation of
the 2×2 determinant in terms of the underlying Frobenius series at unit
seed:
`Δ(ε₁,ε₂) = √ε₁·√ε₂ · (√ε₁ · V_{1/2}(1,−ε₂) · V_1(1,−ε₁) −
                       √ε₂ · V_{1/2}(1,−ε₁) · V_1(1,−ε₂))`.
The `√ε₁·√ε₂` prefactor is positive for `ε₁, ε₂ > 0`; the bracket is
the analytic content (leading order `√ε₁ − √ε₂`). -/
lemma aperyBranchSingularDet_factor {ε₁ ε₂ : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) :
    aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ =
      Real.sqrt ε₁ * Real.sqrt ε₂ *
        (Real.sqrt ε₁ *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          Real.sqrt ε₂ *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂)) := by
  unfold aperyBranchAmplitude_half aperyBranchValue_one
  have h₁ : Real.sqrt ε₁ ^ 2 = ε₁ := Real.sq_sqrt hε₁
  have h₂ : Real.sqrt ε₂ ^ 2 = ε₂ := Real.sq_sqrt hε₂
  linear_combination
    (- Real.sqrt ε₂ *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁)) * h₁ +
    (Real.sqrt ε₁ *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂)) * h₂

/-- **Δ is antisymmetric in its arguments.** Pure ring identity. -/
lemma aperyBranchSingularDet_antisymm (ε₁ ε₂ : ℝ) :
    aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ =
      -(aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ -
          aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂) := by
  ring

/-- **Δ vanishes on the diagonal.** When the two corridor witnesses
coincide `ε₁ = ε₂`, the determinant is structurally zero — the two
witnesses give the same equation, no new information. -/
@[simp] lemma aperyBranchSingularDet_at_diag (ε : ℝ) :
    aperyBranchAmplitude_half ε * aperyBranchValue_one ε -
        aperyBranchAmplitude_half ε * aperyBranchValue_one ε = 0 := by
  ring

/-- **Distinct ε's are necessary for nondegeneracy.** Contrapositive of
the diagonal vanishing — if `Δ(ε₁, ε₂) ≠ 0` then `ε₁ ≠ ε₂`. -/
lemma aperyBranchSingularDet_ne_zero_imp_ne
    {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ε₁ ≠ ε₂ := by
  intro heq
  apply hdet
  rw [heq]
  ring

/-- **Δ vanishes at the conifold endpoint.** If either `ε = 0` then
`A_½(0) = 0` (square-root prefactor) so the determinant collapses to
`-A_½(ε') · V_1(0)` times something that still factors through `√0`.
Concretely both diagonal copies of `√ε` go to zero. -/
@[simp] lemma aperyBranchSingularDet_at_zero_left (ε : ℝ) :
    aperyBranchAmplitude_half 0 * aperyBranchValue_one ε -
        aperyBranchAmplitude_half ε * aperyBranchValue_one 0 = 0 := by
  simp [aperyBranchAmplitude_half_at_zero, aperyBranchValue_one,
    show ((-0 : ℝ)) = 0 from by ring, zero_mul, mul_zero]

@[simp] lemma aperyBranchSingularDet_at_zero_right (ε : ℝ) :
    aperyBranchAmplitude_half ε * aperyBranchValue_one 0 -
        aperyBranchAmplitude_half 0 * aperyBranchValue_one ε = 0 := by
  simp [aperyBranchAmplitude_half_at_zero, aperyBranchValue_one,
    show ((-0 : ℝ)) = 0 from by ring, zero_mul, mul_zero]

/-- **Δ nonvanishing reduces to bracket nonvanishing.** For `ε₁, ε₂ > 0`,
`Δ ≠ 0` iff the bracket
`√ε₁ · V_{1/2}(1,−ε₂) · V_1(1,−ε₁) − √ε₂ · V_{1/2}(1,−ε₁) · V_1(1,−ε₂) ≠ 0`.
This isolates the analytic content (Frobenius series asymptotics)
from the universal positive prefactor `√ε₁ · √ε₂`. -/
lemma aperyBranchSingularDet_ne_zero_iff
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0 ↔
      Real.sqrt ε₁ *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          Real.sqrt ε₂ *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) ≠ 0 := by
  rw [aperyBranchSingularDet_factor hε₁.le hε₂.le]
  have hs₁ : Real.sqrt ε₁ ≠ 0 := Real.sqrt_ne_zero'.mpr hε₁
  have hs₂ : Real.sqrt ε₂ ≠ 0 := Real.sqrt_ne_zero'.mpr hε₂
  constructor
  · intro h hb
    apply h
    rw [hb, mul_zero]
  · intro hb h
    apply hb
    have hpre : Real.sqrt ε₁ * Real.sqrt ε₂ ≠ 0 := mul_ne_zero hs₁ hs₂
    exact (mul_eq_zero.mp h).resolve_left hpre

/-- **Three-branch uniqueness via two witnesses.** If two triples
represent the same `f` on `I` containing `0` and two distinct points
`−ε₁, −ε₂`, and the 2×2 determinant of the singular-pair amplitudes
`Δ := A_½(ε₁) · V_1(ε₂) − A_½(ε₂) · V_1(ε₁)` is nonzero, then both
triples coincide. -/
lemma IsAperyConnectionCoeffsOn.unique_of_two_witnesses
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hb : IsAperyConnectionCoeffsOn b₀ b_half b₁ f I)
    (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₀ = b₀ ∧ a_half = b_half ∧ a₁ = b₁ := by
  refine ⟨ha.regular_unique hb h0, ?_, ?_⟩
  all_goals {
    have h1 := ha.singular_difference hb h0 hε₁
    have h2 := ha.singular_difference hb h0 hε₂
    set A1 := aperyBranchAmplitude_half ε₁
    set A2 := aperyBranchAmplitude_half ε₂
    set V1 := aperyBranchValue_one ε₁
    set V2 := aperyBranchValue_one ε₂
    set Δ := A1 * V2 - A2 * V1 with hΔdef
    set dh := a_half - b_half with hdh
    set d1 := a₁ - b₁ with hd1
    have h1' : dh * A1 + d1 * V1 = 0 := h1
    have h2' : dh * A2 + d1 * V2 = 0 := h2
    have hkey_dh : dh * Δ = 0 := by linear_combination V2 * h1' - V1 * h2'
    have hkey_d1 : d1 * Δ = 0 := by linear_combination A1 * h2' - A2 * h1'
    have hΔ_ne : Δ ≠ 0 := hdet
    first
    | (have : dh = 0 := by
        rcases mul_eq_zero.mp hkey_dh with h | h
        · exact h
        · exact absurd h hΔ_ne
       linarith)
    | (have : d1 = 0 := by
        rcases mul_eq_zero.mp hkey_d1 with h | h
        · exact h
        · exact absurd h hΔ_ne
       linarith)
  }

/-- **Cramer formula for `a_half`.** Under the connection-coefficient
predicate with two ε witnesses and nondegenerate determinant, the
ρ=1/2 seed is recovered as a ratio of the corridor-residue determinant
to `Δ`. Concretely, with
`R(ε) := f(z₁ − ε) − a₀ · A_0(ε)`,
`a_half · Δ = R(ε₁) · V_1(ε₂) − R(ε₂) · V_1(ε₁)`. -/
lemma IsAperyConnectionCoeffsOn.a_half_cramer
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I) :
    a_half *
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) =
      (f (Number.aperyConifoldZ1Poly + (-ε₁)) -
          a₀ * aperyBranchAmplitude_zero ε₁) * aperyBranchValue_one ε₂ -
      (f (Number.aperyConifoldZ1Poly + (-ε₂)) -
          a₀ * aperyBranchAmplitude_zero ε₂) * aperyBranchValue_one ε₁ := by
  have h₁ := h.right_endpoint hε₁
  have h₂ := h.right_endpoint hε₂
  linear_combination
    aperyBranchValue_one ε₁ * h₂ - aperyBranchValue_one ε₂ * h₁

/-- **Cramer formula for `a₁`.** Companion to `a_half_cramer`:
`a₁ · Δ = R(ε₂) · A_½(ε₁) − R(ε₁) · A_½(ε₂)`. -/
lemma IsAperyConnectionCoeffsOn.a_one_cramer
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I) :
    a₁ *
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) =
      (f (Number.aperyConifoldZ1Poly + (-ε₂)) -
          a₀ * aperyBranchAmplitude_zero ε₂) * aperyBranchAmplitude_half ε₁ -
      (f (Number.aperyConifoldZ1Poly + (-ε₁)) -
          a₀ * aperyBranchAmplitude_zero ε₁) * aperyBranchAmplitude_half ε₂ := by
  have h₁ := h.right_endpoint hε₁
  have h₂ := h.right_endpoint hε₂
  linear_combination
    aperyBranchAmplitude_half ε₂ * h₁ - aperyBranchAmplitude_half ε₁ * h₂

/-- **Canonical representative.** Every triple `(a₀, a_half, a₁)`
admits a function realising it on any set: namely the branch-triple
itself, viewed as a function of `z` via the shift `t = z − z₁`.
This is a "free" constructor — no analytic hypotheses on `f`. -/
lemma IsAperyConnectionCoeffsOn.canonical
    (a₀ a_half a₁ : ℝ) (I : Set ℝ) :
    IsAperyConnectionCoeffsOn a₀ a_half a₁
      (fun z => aperyBranchTriple a₀ a_half a₁ (z - Number.aperyConifoldZ1Poly)) I := by
  intro t _
  simp [show (Number.aperyConifoldZ1Poly + t - Number.aperyConifoldZ1Poly) = t from by ring]

/-- **Existence of a representative for any triple.** -/
lemma IsAperyConnectionCoeffsOn.exists_of_triple
    (a₀ a_half a₁ : ℝ) (I : Set ℝ) :
    ∃ f : ℝ → ℝ, IsAperyConnectionCoeffsOn a₀ a_half a₁ f I :=
  ⟨_, IsAperyConnectionCoeffsOn.canonical a₀ a_half a₁ I⟩

/-- **Closed form for `a_half`** (division version of `a_half_cramer`).
When the determinant is nonzero, `a_half` is exactly the residue ratio. -/
lemma IsAperyConnectionCoeffsOn.a_half_eq_div
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a_half =
      ((f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            a₀ * aperyBranchAmplitude_zero ε₁) * aperyBranchValue_one ε₂ -
        (f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            a₀ * aperyBranchAmplitude_zero ε₂) * aperyBranchValue_one ε₁) /
      (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  have hc := h.a_half_cramer hε₁ hε₂
  rw [eq_div_iff hdet, hc]

/-- **Closed form for `a₁`** (division version of `a_one_cramer`). -/
lemma IsAperyConnectionCoeffsOn.a_one_eq_div
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₁ =
      ((f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            a₀ * aperyBranchAmplitude_zero ε₂) * aperyBranchAmplitude_half ε₁ -
        (f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            a₀ * aperyBranchAmplitude_zero ε₁) * aperyBranchAmplitude_half ε₂) /
      (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  have hc := h.a_one_cramer hε₁ hε₂
  rw [eq_div_iff hdet, hc]

/-- **a_half from f only.** Closed form not depending on `a₀`: replace
`a₀ = f(z₁)` using `regular_seed`. The right-hand side is a pure
functional of `f`. -/
lemma IsAperyConnectionCoeffsOn.a_half_from_f
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a_half =
      ((f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₁) *
              aperyBranchValue_one ε₂ -
        (f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₂) *
              aperyBranchValue_one ε₁) /
      (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  have ha₀ := h.regular_seed h0
  have he := h.a_half_eq_div hε₁ hε₂ hdet
  rw [he, ha₀]

/-- **a₁ from f only.** Companion to `a_half_from_f`. -/
lemma IsAperyConnectionCoeffsOn.a_one_from_f
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₁ =
      ((f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₂) *
              aperyBranchAmplitude_half ε₁ -
        (f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₁) *
              aperyBranchAmplitude_half ε₂) /
      (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  have ha₀ := h.regular_seed h0
  have he := h.a_one_eq_div hε₁ hε₂ hdet
  rw [he, ha₀]

/-- **Uniqueness from positive witnesses + bracket nonvanishing.**
A repackaging of `unique_of_two_witnesses` that exposes the bracket
structurally — drops the abstract `hdet` and accepts the cleaner
"√ε₁ · V_½(−ε₂) · V_1(−ε₁) ≠ √ε₂ · V_½(−ε₁) · V_1(−ε₂)" form. -/
lemma IsAperyConnectionCoeffsOn.unique_of_positive_witnesses
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hb : IsAperyConnectionCoeffsOn b₀ b_half b₁ f I)
    (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁_pos : 0 < ε₁) (hε₂_pos : 0 < ε₂)
    (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hbracket :
      Real.sqrt ε₁ *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          Real.sqrt ε₂ *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) ≠ 0) :
    a₀ = b₀ ∧ a_half = b_half ∧ a₁ = b₁ :=
  ha.unique_of_two_witnesses hb h0 hε₁ hε₂
    ((aperyBranchSingularDet_ne_zero_iff hε₁_pos hε₂_pos).mpr hbracket)

/-- **Abstract bracket-nonvanishing skeleton.** If two scalars
`(s₁, s₂)` are nonnegative and distinct, and the perturbations
`(δ₁, δ₂)` are dominated by the principal product `|V₀·(s₁−s₂)|`,
then `s₁·(V₀+δ₁) − s₂·(V₀+δ₂) ≠ 0`. Pure real algebra. -/
lemma bracket_ne_zero_skeleton
    {s₁ s₂ V₀ δ₁ δ₂ : ℝ}
    (h_s₁ : 0 ≤ s₁) (h_s₂ : 0 ≤ s₂)
    (h_dom : s₁ * |δ₁| + s₂ * |δ₂| < |V₀ * (s₁ - s₂)|) :
    s₁ * (V₀ + δ₁) - s₂ * (V₀ + δ₂) ≠ 0 := by
  intro heq
  -- From `heq`, derive `V₀·(s₁−s₂) = s₂·δ₂ − s₁·δ₁`.
  have h_eq : V₀ * (s₁ - s₂) = s₂ * δ₂ - s₁ * δ₁ := by linarith
  have h_abs : |V₀ * (s₁ - s₂)| ≤ s₁ * |δ₁| + s₂ * |δ₂| := by
    rw [h_eq]
    calc |s₂ * δ₂ - s₁ * δ₁|
        ≤ |s₂ * δ₂| + |s₁ * δ₁| := by
          have := abs_sub (s₂ * δ₂) (s₁ * δ₁); linarith
      _ = s₂ * |δ₂| + s₁ * |δ₁| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h_s₂, abs_of_nonneg h_s₁]
      _ = s₁ * |δ₁| + s₂ * |δ₂| := by ring
  linarith

/-- **Leading-order bracket decomposition.** Pure algebraic identity:
the corridor bracket splits as
`V₀·U₀·(√ε₁ − √ε₂) + √ε₁ · δ₁ - √ε₂ · δ₂`
where `δᵢ` are perturbations of the products from their `V₀·U₀` value
at the conifold. When `δᵢ` are small (Frobenius continuity), the
principal term dominates and bracket ≠ 0 for `ε₁ ≠ ε₂` distinct positive. -/
lemma aperyBranchSingularBracket_decomp
    (ε₁ ε₂ V_half_0 V_one_0 : ℝ) :
    Real.sqrt ε₁ *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
      Real.sqrt ε₂ *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) =
    V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂) +
    Real.sqrt ε₁ * (
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁)
        - V_half_0 * V_one_0) -
    Real.sqrt ε₂ * (
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂)
        - V_half_0 * V_one_0) := by
  ring

/-- **Apery bracket nonvanishing under perturbation control.**
Concrete instantiation of `bracket_ne_zero_skeleton` to the Apéry
conifold Frobenius products. If the off-diagonal Frobenius products
`V_{1/2}(-εᵢ) · V_1(-εⱼ)` are close enough to the conifold value
`V_half_0 · V_one_0`, the bracket is nonzero. The closeness
hypothesis encodes Frobenius continuity at `t = 0` — the part that
needs Mathlib's analytic-continuation machinery to discharge in full
generality. -/
lemma aperyBranchSingularBracket_ne_zero_of_perturbation
    {ε₁ ε₂ V_half_0 V_one_0 : ℝ}
    (h_dom :
      Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0| +
      Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0|
        < |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) :
    Real.sqrt ε₁ *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
      Real.sqrt ε₂ *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) ≠ 0 := by
  have hsk := bracket_ne_zero_skeleton (V₀ := V_half_0 * V_one_0)
    (s₁ := Real.sqrt ε₁) (s₂ := Real.sqrt ε₂)
    (δ₁ := frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1/2) 1 (-ε₂) *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
        V_half_0 * V_one_0)
    (δ₂ := frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1/2) 1 (-ε₁) *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
        V_half_0 * V_one_0)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) h_dom
  intro hzero
  apply hsk
  linarith [hzero]

/-- **Δ nonvanishing from perturbation control.** Closes the ring
between `aperyBranchSingularBracket_ne_zero_of_perturbation`
(bracket ≠ 0) and `aperyBranchSingularDet_ne_zero_iff` (Δ ≠ 0 ↔
bracket ≠ 0 for ε > 0): under the perturbation domination
hypothesis, the 2×2 determinant `Δ` is nonzero directly. -/
lemma aperyBranchSingularDet_ne_zero_of_perturbation
    {ε₁ ε₂ V_half_0 V_one_0 : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (h_dom :
      Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0| +
      Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0|
        < |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) :
    aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0 :=
  (aperyBranchSingularDet_ne_zero_iff hε₁ hε₂).mpr
    (aperyBranchSingularBracket_ne_zero_of_perturbation h_dom)

/-- **Uniform-bound sufficient condition for `h_dom`.** Replaces the
mixed weighted absolute-value sum by a single uniform off-diagonal
perturbation bound `M`. If both off-diagonal Frobenius products
satisfy `|V_½(-εᵢ)·V_1(-εⱼ) - V_half_0·V_one_0| ≤ M` and the
quantitative comparison `(√ε₁ + √ε₂) · M < |V_half_0·V_one_0| ·
|√ε₁ - √ε₂|` holds, then the perturbation domination hypothesis
of `aperyBranchSingularBracket_ne_zero_of_perturbation` is satisfied.

This is the structural separation: `M` is the analytic content
(supplied by Frobenius series uniform continuity at `t = 0`), the
quantitative comparison is a real-arithmetic check parameterised by
`ε`. -/
lemma aperyBranchSingular_h_dom_of_uniform_bound
    {ε₁ ε₂ V_half_0 V_one_0 M : ℝ}
    (hM₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
            V_half_0 * V_one_0| ≤ M)
    (hM₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
            V_half_0 * V_one_0| ≤ M)
    (hcmp : (Real.sqrt ε₁ + Real.sqrt ε₂) * M <
              |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) :
    Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0| +
      Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0|
        < |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)| := by
  have hs₁ : 0 ≤ Real.sqrt ε₁ := Real.sqrt_nonneg _
  have hs₂ : 0 ≤ Real.sqrt ε₂ := Real.sqrt_nonneg _
  have h₁ : Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0| ≤ Real.sqrt ε₁ * M :=
    mul_le_mul_of_nonneg_left hM₁ hs₁
  have h₂ : Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0| ≤ Real.sqrt ε₂ * M :=
    mul_le_mul_of_nonneg_left hM₂ hs₂
  have hsum : Real.sqrt ε₁ * M + Real.sqrt ε₂ * M =
      (Real.sqrt ε₁ + Real.sqrt ε₂) * M := by ring
  linarith

/-- **Product-difference triangle bound.** Standard estimate
`|ab - cd| ≤ |a|·|b-d| + |d|·|a-c|`. Used to decompose the
off-diagonal Frobenius product perturbation into individual
Lipschitz-style bounds on `V_½` and `V_1`. -/
lemma abs_mul_sub_mul_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a| * |b - d| + |d| * |a - c| := by
  have h : a * b - c * d = a * (b - d) + d * (a - c) := by ring
  rw [h]
  calc |a * (b - d) + d * (a - c)|
      ≤ |a * (b - d)| + |d * (a - c)| := abs_add_le _ _
    _ = |a| * |b - d| + |d| * |a - c| := by rw [abs_mul, abs_mul]

/-- **Lipschitz-style sufficient bound for the off-diagonal
perturbation `M`.** Given uniform bounds
- `|V_½(-εᵢ)| ≤ B_half` (boundedness of V_½ near `t = 0`)
- `|V_½(-εᵢ) - V_half_0| ≤ μ` (Lipschitz/continuity of V_½ at `t = 0`)
- `|V_1(-εⱼ) - V_one_0| ≤ ν` (Lipschitz/continuity of V_1 at `t = 0`)

then both off-diagonal Frobenius products satisfy
`|V_½(-εᵢ)·V_1(-εⱼ) - V_half_0·V_one_0| ≤ B_half·ν + |V_one_0|·μ`.

This factors the gap-A obligation into the canonical Frobenius
analytic data (uniform bound + modulus of continuity at the
indicial point) — exactly what Mathlib's analytic-continuation
machinery delivers once instantiated. -/
lemma aperyBranchSingular_offdiag_bound
    {ε₁ ε₂ V_half_0 V_one_0 B_half μ ν : ℝ}
    (h_bound₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| ≤ B_half)
    (h_bound₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| ≤ B_half)
    (h_lip_half₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) -
                  V_half_0| ≤ μ)
    (h_lip_half₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) -
                  V_half_0| ≤ μ)
    (h_lip_one₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
                  V_one_0| ≤ ν)
    (h_lip_one₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
                  V_one_0| ≤ ν) :
    |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
      V_half_0 * V_one_0| ≤ B_half * ν + |V_one_0| * μ ∧
    |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
      V_half_0 * V_one_0| ≤ B_half * ν + |V_one_0| * μ := by
  refine ⟨?_, ?_⟩
  · calc |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0|
        ≤ |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| *
          |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
            V_one_0| +
          |V_one_0| *
          |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) -
            V_half_0| := abs_mul_sub_mul_le _ _ _ _
      _ ≤ B_half * ν + |V_one_0| * μ := by
          have h_left : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| *
              |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
                V_one_0| ≤ B_half * ν :=
            mul_le_mul h_bound₁ h_lip_one₁ (abs_nonneg _)
              (le_trans (abs_nonneg _) h_bound₁)
          have h_right : |V_one_0| *
              |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) -
                V_half_0| ≤ |V_one_0| * μ :=
            mul_le_mul_of_nonneg_left h_lip_half₁ (abs_nonneg _)
          linarith
  · calc |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0|
        ≤ |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| *
          |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
            V_one_0| +
          |V_one_0| *
          |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) -
            V_half_0| := abs_mul_sub_mul_le _ _ _ _
      _ ≤ B_half * ν + |V_one_0| * μ := by
          have h_left : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| *
              |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
                V_one_0| ≤ B_half * ν :=
            mul_le_mul h_bound₂ h_lip_one₂ (abs_nonneg _)
              (le_trans (abs_nonneg _) h_bound₂)
          have h_right : |V_one_0| *
              |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) -
                V_half_0| ≤ |V_one_0| * μ :=
            mul_le_mul_of_nonneg_left h_lip_half₂ (abs_nonneg _)
          linarith

/-- **√ε strict monotonicity at distinct positive arguments.**
Used as the leading-order discriminant: `√ε₁ ≠ √ε₂` for `0 < ε₁ ≠ ε₂`. -/
lemma sqrt_ne_of_pos_ne {ε₁ ε₂ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (hne : ε₁ ≠ ε₂) :
    Real.sqrt ε₁ ≠ Real.sqrt ε₂ := by
  intro heq
  apply hne
  have h₁' : Real.sqrt ε₁ ^ 2 = ε₁ := Real.sq_sqrt h₁.le
  have h₂' : Real.sqrt ε₂ ^ 2 = ε₂ := Real.sq_sqrt h₂.le
  rw [← h₁', ← h₂', heq]

/-- **Triple-equality form of uniqueness.** Same content as
`unique_of_two_witnesses` but returns the triple equality
`(a₀, a_half, a₁) = (b₀, b_half, b₁)` instead of the conjunction. -/
lemma IsAperyConnectionCoeffsOn.triple_eq_of_two_witnesses
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hb : IsAperyConnectionCoeffsOn b₀ b_half b₁ f I)
    (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    (a₀, a_half, a₁) = (b₀, b_half, b₁) := by
  obtain ⟨h0', hh, h1⟩ := ha.unique_of_two_witnesses hb h0 hε₁ hε₂ hdet
  simp [h0', hh, h1]

/-- **At-most-one triple represents `f`.** The connection-coefficient
predicate has at most one realising triple under bracket
nondegeneracy — packaged as `Subsingleton`-style. -/
lemma IsAperyConnectionCoeffsOn.unique_triple
    {f : ℝ → ℝ} {I : Set ℝ}
    (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ∀ a b : ℝ × ℝ × ℝ,
      IsAperyConnectionCoeffsOn a.1 a.2.1 a.2.2 f I →
      IsAperyConnectionCoeffsOn b.1 b.2.1 b.2.2 f I →
      a = b := by
  intro a b ha hb
  exact ha.triple_eq_of_two_witnesses hb h0 hε₁ hε₂ hdet

/-- **Uniqueness from perturbation control.** End-to-end corollary:
under positive corridor witnesses `−ε₁, −ε₂ ∈ I` (with `ε₁, ε₂ > 0`)
and the perturbation domination hypothesis encoding Frobenius
continuity at `t = 0`, the connection-coefficient triple of `f` on
`I` is unique. This wires the algebraic skeleton
(`aperyBranchSingularBracket_ne_zero_of_perturbation` →
`aperyBranchSingularDet_ne_zero_of_perturbation`) into the predicate
uniqueness theorem (`unique_of_two_witnesses`). -/
lemma IsAperyConnectionCoeffsOn.unique_of_perturbation
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hb : IsAperyConnectionCoeffsOn b₀ b_half b₁ f I)
    (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ V_half_0 V_one_0 : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hε₁I : (-ε₁) ∈ I) (hε₂I : (-ε₂) ∈ I)
    (h_dom :
      Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0| +
      Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0|
        < |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) :
    a₀ = b₀ ∧ a_half = b_half ∧ a₁ = b₁ :=
  ha.unique_of_two_witnesses hb h0 hε₁I hε₂I
    (aperyBranchSingularDet_ne_zero_of_perturbation hε₁ hε₂ h_dom)

/-- **End-to-end uniqueness from Frobenius Lipschitz data.** Single
user-facing API combining the full chain
  uniform bound + V_½ continuity + V_1 continuity + ε comparison
    → triple uniqueness.

Inputs (the canonical Frobenius analytic data at the indicial point):
- `B_half`: uniform bound on `V_½(1, −ε)` for ε ∈ {ε₁, ε₂}
- `μ`: continuity modulus of `V_½` at `t = 0` (over ε ∈ {ε₁, ε₂})
- `ν`: continuity modulus of `V_1` at `t = 0` (over ε ∈ {ε₁, ε₂})
- `hcmp`: quantitative ε comparison ensuring the perturbation is
  smaller than the leading-order `√ε`-discriminant

When this theorem is used in production, `B_half, μ, ν` are supplied
by Mathlib's analytic-continuation machinery on the apery conifold
Frobenius series, and `hcmp` is checked numerically. -/
lemma IsAperyConnectionCoeffsOn.unique_of_lipschitz
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hb : IsAperyConnectionCoeffsOn b₀ b_half b₁ f I)
    (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ V_half_0 V_one_0 B_half μ ν : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hε₁I : (-ε₁) ∈ I) (hε₂I : (-ε₂) ∈ I)
    (h_bound₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| ≤ B_half)
    (h_bound₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| ≤ B_half)
    (h_lip_half₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) -
                  V_half_0| ≤ μ)
    (h_lip_half₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) -
                  V_half_0| ≤ μ)
    (h_lip_one₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
                  V_one_0| ≤ ν)
    (h_lip_one₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
                  V_one_0| ≤ ν)
    (hcmp : (Real.sqrt ε₁ + Real.sqrt ε₂) * (B_half * ν + |V_one_0| * μ) <
              |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) :
    a₀ = b₀ ∧ a_half = b_half ∧ a₁ = b₁ := by
  obtain ⟨hM₁, hM₂⟩ := aperyBranchSingular_offdiag_bound
    h_bound₁ h_bound₂ h_lip_half₁ h_lip_half₂ h_lip_one₁ h_lip_one₂
  exact ha.unique_of_perturbation hb h0 hε₁ hε₂ hε₁I hε₂I
    (aperyBranchSingular_h_dom_of_uniform_bound hM₁ hM₂ hcmp)

/-- **Three-point interpolation by a connection-coefficient triple.**
Given any function `f`, when the singular-pair determinant `Δ` is
nonzero, there exists a triple `(a₀, a_half, a₁)` such that the
canonical realiser matches `f` at the three points
`{z₁, z₁ − ε₁, z₁ − ε₂}`. The triple is uniquely determined by
Cramer's rule applied to the 2×2 singular system after fixing
`a₀ := f(z₁)`.

This is the existence companion to
`IsAperyConnectionCoeffsOn.unique_of_two_witnesses`: together they
witness that 3-point pointwise data (regular endpoint plus two
singular witnesses) characterises the connection-coefficient triple
modulo bracket nondegeneracy. -/
lemma aperyTriple_interpolates_three_points
    (f : ℝ → ℝ) {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ∃ a₀ a_half a₁ : ℝ,
      aperyBranchTriple a₀ a_half a₁ 0 = f Number.aperyConifoldZ1Poly ∧
      aperyBranchTriple a₀ a_half a₁ (-ε₁) =
        f (Number.aperyConifoldZ1Poly + (-ε₁)) ∧
      aperyBranchTriple a₀ a_half a₁ (-ε₂) =
        f (Number.aperyConifoldZ1Poly + (-ε₂)) := by
  set a₀ := f Number.aperyConifoldZ1Poly with ha₀_def
  set v₁ := f (Number.aperyConifoldZ1Poly + (-ε₁)) -
              a₀ * aperyBranchAmplitude_zero ε₁ with hv₁_def
  set v₂ := f (Number.aperyConifoldZ1Poly + (-ε₂)) -
              a₀ * aperyBranchAmplitude_zero ε₂ with hv₂_def
  set Δ := aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ with hΔ_def
  refine ⟨a₀,
    (v₁ * aperyBranchValue_one ε₂ - v₂ * aperyBranchValue_one ε₁) / Δ,
    (v₂ * aperyBranchAmplitude_half ε₁ - v₁ * aperyBranchAmplitude_half ε₂) / Δ,
    ?_, ?_, ?_⟩
  · simp [aperyBranchTriple_at_zero]
  · rw [aperyBranchTriple_at_neg_eps]
    field_simp
    have hgoal :
        a₀ * aperyBranchAmplitude_zero ε₁ * Δ +
          ((v₁ * aperyBranchValue_one ε₂ - v₂ * aperyBranchValue_one ε₁) *
              aperyBranchAmplitude_half ε₁ +
            (v₂ * aperyBranchAmplitude_half ε₁ -
              v₁ * aperyBranchAmplitude_half ε₂) *
              aperyBranchValue_one ε₁) =
        (a₀ * aperyBranchAmplitude_zero ε₁ + v₁) * Δ := by
      simp only [hΔ_def]; ring
    linarith [hgoal,
      show f (Number.aperyConifoldZ1Poly + (-ε₁)) =
        a₀ * aperyBranchAmplitude_zero ε₁ + v₁ from by
          simp [hv₁_def]]
  · rw [aperyBranchTriple_at_neg_eps]
    field_simp
    have hgoal :
        a₀ * aperyBranchAmplitude_zero ε₂ * Δ +
          ((v₁ * aperyBranchValue_one ε₂ - v₂ * aperyBranchValue_one ε₁) *
              aperyBranchAmplitude_half ε₂ +
            (v₂ * aperyBranchAmplitude_half ε₁ -
              v₁ * aperyBranchAmplitude_half ε₂) *
              aperyBranchValue_one ε₂) =
        (a₀ * aperyBranchAmplitude_zero ε₂ + v₂) * Δ := by
      simp only [hΔ_def]; ring
    linarith [hgoal,
      show f (Number.aperyConifoldZ1Poly + (-ε₂)) =
        a₀ * aperyBranchAmplitude_zero ε₂ + v₂ from by
          simp [hv₂_def]]

/-- **Predicate-level witness from 3-point interpolation.** Given any
function `f` and bracket nondegeneracy `Δ ≠ 0`, there exists a triple
`(a₀, a_half, a₁)` such that `IsAperyConnectionCoeffsOn a₀ a_half a₁
f {0, -ε₁, -ε₂}`. The triple is the Cramer extraction. Together with
`unique_of_two_witnesses` this gives "exists-and-unique" on the
3-point set: the singular witnesses plus the regular endpoint
characterise the triple via real-algebraic data alone (no analytic
continuation needed). -/
lemma IsAperyConnectionCoeffsOn.exists_on_three_points
    (f : ℝ → ℝ) {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ∃ a₀ a_half a₁ : ℝ,
      IsAperyConnectionCoeffsOn a₀ a_half a₁ f
        ({0, -ε₁, -ε₂} : Set ℝ) := by
  obtain ⟨a₀, a_half, a₁, hz, hε1, hε2⟩ :=
    aperyTriple_interpolates_three_points f hdet
  refine ⟨a₀, a_half, a₁, ?_⟩
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · rw [add_zero]; exact hz.symm
  · exact hε1.symm
  · exact hε2.symm

/-- **`ExistsUnique`-style packaging on the 3-point set.** Combines
`exists_on_three_points` with `triple_eq_of_two_witnesses` into a
single `∃!` statement. The Cramer-extracted triple is the unique
realiser of the connection-coefficient predicate on
`{0, −ε₁, −ε₂}` whenever `Δ ≠ 0`. -/
lemma IsAperyConnectionCoeffsOn.existsUnique_on_three_points
    (f : ℝ → ℝ) {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ∃! abc : ℝ × ℝ × ℝ,
      IsAperyConnectionCoeffsOn abc.1 abc.2.1 abc.2.2 f
        ({0, -ε₁, -ε₂} : Set ℝ) := by
  obtain ⟨a₀, a_half, a₁, ha⟩ := exists_on_three_points f hdet
  refine ⟨(a₀, a_half, a₁), ha, ?_⟩
  rintro ⟨b₀, b_half, b₁⟩ hb
  have h0 : (0 : ℝ) ∈ ({0, -ε₁, -ε₂} : Set ℝ) := by simp
  have hε1 : (-ε₁) ∈ ({0, -ε₁, -ε₂} : Set ℝ) := by simp
  have hε2 : (-ε₂) ∈ ({0, -ε₁, -ε₂} : Set ℝ) := by simp
  exact hb.triple_eq_of_two_witnesses ha h0 hε1 hε2 hdet

/-- **Three-branch ℝ-linear independence** under bracket
nondegeneracy. If the connection-coefficient triple `(c₀, c_half, c₁)`
realises the zero function on a set containing the regular endpoint
and two singular witnesses with `Δ ≠ 0`, then all three coefficients
are zero. This is the linear-independence statement of
`{Y_0, Y_{1/2}, Y_1}` in the function space, gated by Δ. -/
lemma IsAperyConnectionCoeffsOn.linear_indep_of_two_witnesses
    {c₀ c_half c₁ : ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn c₀ c_half c₁ (fun _ => (0 : ℝ)) I)
    (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    c₀ = 0 ∧ c_half = 0 ∧ c₁ = 0 := by
  have hzero : IsAperyConnectionCoeffsOn 0 0 0 (fun _ => (0 : ℝ)) I := by
    intro t _; exact (aperyBranchTriple_zero t).symm
  exact h.unique_of_two_witnesses hzero h0 hε₁ hε₂ hdet

/-- **Regular amplitude positivity from continuity at conifold.** At
the conifold `aperyBranchAmplitude_zero 0 = 1`. Given a continuity
modulus `μ_zero` such that `|V₀(1,−ε) − 1| ≤ μ_zero` and `μ_zero < 1`,
the regular amplitude is strictly positive. -/
lemma aperyBranchAmplitude_zero_pos_of_close
    {ε μ_zero : ℝ}
    (h_lip : |aperyBranchAmplitude_zero ε - 1| ≤ μ_zero)
    (h_small : μ_zero < 1) :
    0 < aperyBranchAmplitude_zero ε := by
  have h_abs := abs_sub_lt_iff.mp (lt_of_le_of_lt h_lip h_small)
  linarith [h_abs.1, h_abs.2]

/-- **Regular branch vanishing characterisation.** When the regular
amplitude is positive (holds near the conifold), the regular branch
evaluation `yAperyZero c₀ (-ε)` vanishes iff the seed `c₀` does. -/
lemma yAperyZero_eq_zero_iff_of_amp_pos {ε c₀ : ℝ}
    (h_amp : 0 < aperyBranchAmplitude_zero ε) :
    yAperyZero c₀ (-ε) = 0 ↔ c₀ = 0 := by
  rw [yAperyZero_at_neg_eps]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_right h_amp.ne',
    fun hc => by rw [hc, zero_mul]⟩

/-- **Half-branch vanishing characterisation.** For `ε > 0` (so
`√ε > 0`) and a nonvanishing `V_½(1, −ε)`, the ρ=1/2 branch
evaluation `yAperyHalf c_half (−ε)` vanishes iff the seed `c_half`
does. -/
lemma yAperyHalf_eq_zero_iff_of_pos
    {ε c_half : ℝ} (hε : 0 < ε)
    (hV : frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε) ≠ 0) :
    yAperyHalf c_half (-ε) = 0 ↔ c_half = 0 := by
  rw [yAperyHalf_at_neg_eps]
  unfold aperyBranchAmplitude_half
  have hs : Real.sqrt ε ≠ 0 := Real.sqrt_ne_zero'.mpr hε
  refine ⟨fun h => ?_, fun hc => by rw [hc, zero_mul]⟩
  rcases mul_eq_zero.mp h with hc | hsv
  · exact hc
  · exact absurd ((mul_eq_zero.mp hsv).resolve_left hs) hV

/-- **One-branch vanishing characterisation.** For `ε > 0` and
nonvanishing `V_1(1, −ε)`, the ρ=1 branch evaluation
`yApery c₁ (−ε)` vanishes iff the seed `c₁` does. -/
lemma yApery_eq_zero_iff_of_pos
    {ε c₁ : ℝ} (hε : 0 < ε)
    (hV : frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε) ≠ 0) :
    yApery c₁ (-ε) = 0 ↔ c₁ = 0 := by
  rw [yApery_at_neg_eps]
  unfold aperyBranchValue_one
  have hne : (-ε) ≠ 0 := by intro h; linarith [neg_eq_zero.mp h]
  refine ⟨fun h => ?_, fun hc => by rw [hc, zero_mul]⟩
  rcases mul_eq_zero.mp h with hc | hev
  · exact hc
  · exact absurd ((mul_eq_zero.mp hev).resolve_left hne) hV

/-- **V_½ positivity from continuity at conifold.** Unit-seed
Frobenius value at `t = 0` equals `1` (`frobeniusValue_zero`), so
any continuity bound `|V_½(1, −ε) − 1| ≤ μ < 1` keeps the value
strictly positive. Discharges the nonvanishing hypothesis of
`yAperyHalf_eq_zero_iff_of_pos`. -/
lemma frobeniusValue_half_pos_of_close
    {ε μ : ℝ}
    (h_lip : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε) - 1| ≤ μ)
    (h_small : μ < 1) :
    0 < frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε) := by
  have h_abs := abs_sub_lt_iff.mp (lt_of_le_of_lt h_lip h_small)
  linarith [h_abs.1, h_abs.2]

/-- **V_1 positivity from continuity at conifold.** Same shape as
`frobeniusValue_half_pos_of_close`. Discharges the nonvanishing
hypothesis of `yApery_eq_zero_iff_of_pos`. -/
lemma frobeniusValue_one_pos_of_close
    {ε μ : ℝ}
    (h_lip : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε) - 1| ≤ μ)
    (h_small : μ < 1) :
    0 < frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε) := by
  have h_abs := abs_sub_lt_iff.mp (lt_of_le_of_lt h_lip h_small)
  linarith [h_abs.1, h_abs.2]

/-- **Near-conifold positivity bundle.** Single packaging of the
three positivity-from-continuity atoms: under continuity moduli
`μ_zero, μ_half, μ_one < 1` for the three unit-seed Frobenius
values at `−ε`, all three are strictly positive. Useful as a single
hypothesis when discharging nonvanishing assumptions across branches. -/
lemma aperyBranches_pos_at_neg_eps
    {ε μ_zero μ_half μ_one : ℝ}
    (h_zero : |aperyBranchAmplitude_zero ε - 1| ≤ μ_zero)
    (h_half : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε) - 1| ≤ μ_half)
    (h_one : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε) - 1| ≤ μ_one)
    (hμ_zero : μ_zero < 1) (hμ_half : μ_half < 1) (hμ_one : μ_one < 1) :
    0 < aperyBranchAmplitude_zero ε ∧
    0 < frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε) ∧
    0 < frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε) :=
  ⟨aperyBranchAmplitude_zero_pos_of_close h_zero hμ_zero,
   frobeniusValue_half_pos_of_close h_half hμ_half,
   frobeniusValue_one_pos_of_close h_one hμ_one⟩

/-- **Quantitative lower bound on |Δ| from perturbation control.**
The 2×2 determinant satisfies
`|Δ| ≥ √ε₁·√ε₂ · (|V_half_0·V_one_0·(√ε₁ − √ε₂)| − (√ε₁·δ₁ + √ε₂·δ₂))`
where `δ₁, δ₂` bound the off-diagonal Frobenius-product perturbations.
When the bracket bound `(√ε₁·δ₁ + √ε₂·δ₂)` is strictly less than the
principal `|V_half_0·V_one_0·(√ε₁−√ε₂)|`, this gives a strictly
positive lower bound on `|Δ|`. Useful for stability/asymptotic
analysis where mere `Δ ≠ 0` is not enough. -/
lemma aperyBranchSingularDet_abs_lower_bound
    {ε₁ ε₂ V_half_0 V_one_0 : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) :
    Real.sqrt ε₁ * Real.sqrt ε₂ *
      (|V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)| -
        (Real.sqrt ε₁ *
          |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
            V_half_0 * V_one_0| +
          Real.sqrt ε₂ *
          |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
            V_half_0 * V_one_0|)) ≤
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  set V₀p := V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂) with hV₀p
  set δ₁ := frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
      Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
    frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
      Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
    V_half_0 * V_one_0 with hδ₁
  set δ₂ := frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
      Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
    frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
      Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
    V_half_0 * V_one_0 with hδ₂
  set bracket := Real.sqrt ε₁ *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
    Real.sqrt ε₂ *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) with hbracket
  have h_factor : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
      aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ =
      Real.sqrt ε₁ * Real.sqrt ε₂ * bracket :=
    aperyBranchSingularDet_factor hε₁ hε₂
  have h_sqrt_nn : 0 ≤ Real.sqrt ε₁ * Real.sqrt ε₂ :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_abs_eq : |Real.sqrt ε₁ * Real.sqrt ε₂ * bracket| =
      Real.sqrt ε₁ * Real.sqrt ε₂ * |bracket| := by
    rw [abs_mul, abs_of_nonneg h_sqrt_nn]
  rw [h_factor, h_abs_eq]
  apply mul_le_mul_of_nonneg_left _ h_sqrt_nn
  have h_decomp : bracket = V₀p + (Real.sqrt ε₁ * δ₁ - Real.sqrt ε₂ * δ₂) := by
    simp only [hbracket, hV₀p, hδ₁, hδ₂]; ring
  have h_perturb_le : |Real.sqrt ε₁ * δ₁ - Real.sqrt ε₂ * δ₂| ≤
      Real.sqrt ε₁ * |δ₁| + Real.sqrt ε₂ * |δ₂| := by
    calc |Real.sqrt ε₁ * δ₁ - Real.sqrt ε₂ * δ₂|
        ≤ |Real.sqrt ε₁ * δ₁| + |Real.sqrt ε₂ * δ₂| := abs_sub _ _
      _ = Real.sqrt ε₁ * |δ₁| + Real.sqrt ε₂ * |δ₂| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
            abs_of_nonneg (Real.sqrt_nonneg _)]
  have h_rev_tri : |V₀p| - |Real.sqrt ε₁ * δ₁ - Real.sqrt ε₂ * δ₂| ≤ |bracket| := by
    rw [h_decomp]
    have h := abs_sub_abs_le_abs_sub V₀p (-(Real.sqrt ε₁ * δ₁ - Real.sqrt ε₂ * δ₂))
    have h_eq : V₀p - -(Real.sqrt ε₁ * δ₁ - Real.sqrt ε₂ * δ₂) =
        V₀p + (Real.sqrt ε₁ * δ₁ - Real.sqrt ε₂ * δ₂) := by ring
    rw [h_eq, abs_neg] at h
    linarith
  have h_V₀p_abs : |V₀p| = |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)| := by
    simp only [hV₀p]
  rw [h_V₀p_abs] at h_rev_tri
  linarith

/-- **Strict |Δ| > 0 from a perturbation-domination hypothesis.**
If both `ε_i > 0` and the perturbation bound
`√ε₁·|δ₁| + √ε₂·|δ₂|` is strictly less than the principal
`|V_half_0·V_one_0·(√ε₁−√ε₂)|`, then the 2×2 determinant has strictly
positive absolute value. Useful when stability/asymptotic analysis
requires a quantitative non-degeneracy beyond `Δ ≠ 0`. -/
lemma aperyBranchSingularDet_abs_pos_of_perturbation_lt
    {ε₁ ε₂ V_half_0 V_one_0 : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (h_dom :
      Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0| +
      Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0| <
      |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) :
    0 < |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  have h_lb := aperyBranchSingularDet_abs_lower_bound
    (V_half_0 := V_half_0) (V_one_0 := V_one_0) hε₁.le hε₂.le
  have h_sqrt_pos : 0 < Real.sqrt ε₁ * Real.sqrt ε₂ :=
    mul_pos (Real.sqrt_pos.mpr hε₁) (Real.sqrt_pos.mpr hε₂)
  have h_inner_pos :
      0 < |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)| -
        (Real.sqrt ε₁ *
          |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
            V_half_0 * V_one_0| +
          Real.sqrt ε₂ *
          |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
            frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
              Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
            V_half_0 * V_one_0|) := by linarith
  have h_prod_pos := mul_pos h_sqrt_pos h_inner_pos
  linarith

/-- **Lipschitz form of strict |Δ| > 0.**
Given uniform-bound + continuity moduli `(B_half, μ, ν)` for `V_½, V_1`
near the conifold, plus `ε_i > 0` and the size comparison
`(√ε₁ + √ε₂)·(B_half·ν + |V_one_0|·μ) < |V_half_0·V_one_0·(√ε₁−√ε₂)|`,
the singular-pair determinant has strictly positive absolute value.
End-to-end wrapper parallel to `unique_of_lipschitz`, but supplying
quantitative non-degeneracy. -/
lemma aperyBranchSingularDet_abs_pos_of_lipschitz
    {ε₁ ε₂ V_half_0 V_one_0 B_half μ ν : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (h_bound₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| ≤ B_half)
    (h_bound₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| ≤ B_half)
    (h_lip_half₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) -
                  V_half_0| ≤ μ)
    (h_lip_half₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) -
                  V_half_0| ≤ μ)
    (h_lip_one₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
                  V_one_0| ≤ ν)
    (h_lip_one₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                    Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
                  V_one_0| ≤ ν)
    (h_cmp : (Real.sqrt ε₁ + Real.sqrt ε₂) * (B_half * ν + |V_one_0| * μ) <
      |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) :
    0 < |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  obtain ⟨hM₁, hM₂⟩ := aperyBranchSingular_offdiag_bound
    h_bound₁ h_bound₂ h_lip_half₁ h_lip_half₂ h_lip_one₁ h_lip_one₂
  set M := B_half * ν + |V_one_0| * μ with hM
  have h_M_nn : 0 ≤ M := by
    have h_bound_nn : 0 ≤ B_half := le_trans (abs_nonneg _) h_bound₁
    have h_one_nn : 0 ≤ |V_one_0| := abs_nonneg _
    have h_ν_nn : 0 ≤ ν := le_trans (abs_nonneg _) h_lip_one₁
    have h_μ_nn : 0 ≤ μ := le_trans (abs_nonneg _) h_lip_half₁
    have := mul_nonneg h_bound_nn h_ν_nn
    have := mul_nonneg h_one_nn h_μ_nn
    simp only [hM]; linarith
  have h_perturb_le :
      Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0| +
      Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0| ≤
      (Real.sqrt ε₁ + Real.sqrt ε₂) * M := by
    have h₁ : Real.sqrt ε₁ * _ ≤ Real.sqrt ε₁ * M :=
      mul_le_mul_of_nonneg_left hM₁ (Real.sqrt_nonneg _)
    have h₂ : Real.sqrt ε₂ * _ ≤ Real.sqrt ε₂ * M :=
      mul_le_mul_of_nonneg_left hM₂ (Real.sqrt_nonneg _)
    have h_ring : Real.sqrt ε₁ * M + Real.sqrt ε₂ * M =
        (Real.sqrt ε₁ + Real.sqrt ε₂) * M := by ring
    linarith
  exact aperyBranchSingularDet_abs_pos_of_perturbation_lt
    (V_half_0 := V_half_0) (V_one_0 := V_one_0) hε₁ hε₂
    (by linarith)

/-- **Strict positivity of the principal term `|V_h₀·V_1₀·(√ε₁−√ε₂)|`.**
The "ideal" leading-order piece of the bracket is strictly positive
exactly when both reference values are nonzero and the two ε-points
are distinct (with `ε_i ≥ 0`). Used to discharge the size-comparison
hypothesis in `*_pos_of_lipschitz` for any concrete distinct-ε regime. -/
lemma aperyBranchSingularDet_principal_abs_pos
    {ε₁ ε₂ V_half_0 V_one_0 : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (h_ne : ε₁ ≠ ε₂)
    (h_half : V_half_0 ≠ 0) (h_one : V_one_0 ≠ 0) :
    0 < |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)| := by
  rw [abs_pos]
  have h_sqrt_ne : Real.sqrt ε₁ ≠ Real.sqrt ε₂ := by
    intro heq
    apply h_ne
    have h₁ : Real.sqrt ε₁ ^ 2 = ε₁ := Real.sq_sqrt hε₁
    have h₂ : Real.sqrt ε₂ ^ 2 = ε₂ := Real.sq_sqrt hε₂
    have h_sq : Real.sqrt ε₁ ^ 2 = Real.sqrt ε₂ ^ 2 := by rw [heq]
    linarith
  have h_diff_ne : Real.sqrt ε₁ - Real.sqrt ε₂ ≠ 0 := sub_ne_zero.mpr h_sqrt_ne
  exact mul_ne_zero (mul_ne_zero h_half h_one) h_diff_ne

/-- **|Δ| factored as `√ε₁·√ε₂·|bracket|`.**
Direct absolute-value form of the factor lemma. Pairs with the
abs lower bound for two-sided control on `|Δ|`. -/
lemma aperyBranchSingularDet_abs_eq_sqrt_prod_mul_bracket
    {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) :
    |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
      aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| =
    Real.sqrt ε₁ * Real.sqrt ε₂ *
      |Real.sqrt ε₁ *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
        Real.sqrt ε₂ *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂)| := by
  rw [aperyBranchSingularDet_factor hε₁ hε₂, abs_mul,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

/-- **Triangle-inequality upper bound on the bracket.**
The 2×2 bracket `√ε₁·V_½(−ε₂)·V_1(−ε₁) − √ε₂·V_½(−ε₁)·V_1(−ε₂)` is
bounded in absolute value by `(√ε₁ + √ε₂)·B_half·B_one` whenever
`B_half, B_one` are uniform sup bounds on the two Frobenius series
near the conifold. Pairs with the lower bound for stability estimates. -/
lemma aperyBranchSingularBracket_abs_le_uniform
    {ε₁ ε₂ B_half B_one : ℝ}
    (h_half₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| ≤ B_half)
    (h_half₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| ≤ B_half)
    (h_one₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁)| ≤ B_one)
    (h_one₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂)| ≤ B_one) :
    |Real.sqrt ε₁ *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
      Real.sqrt ε₂ *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
        frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
          Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂)| ≤
      (Real.sqrt ε₁ + Real.sqrt ε₂) * (B_half * B_one) := by
  set A := Real.sqrt ε₁ *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) with hA
  set B := Real.sqrt ε₂ *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
      frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
        Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) with hB
  have h_B_half_nn : 0 ≤ B_half := le_trans (abs_nonneg _) h_half₁
  have h_B_one_nn : 0 ≤ B_one := le_trans (abs_nonneg _) h_one₁
  have h_A_le : |A| ≤ Real.sqrt ε₁ * (B_half * B_one) := by
    have : |A| = Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁)| := by
      simp only [hA, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [this]
    have h₁ : Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| ≤
        Real.sqrt ε₁ * B_half :=
      mul_le_mul_of_nonneg_left h_half₁ (Real.sqrt_nonneg _)
    have h₂ : Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁)| ≤
        Real.sqrt ε₁ * B_half * B_one :=
      mul_le_mul h₁ h_one₁ (abs_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) h_B_half_nn)
    linarith [h₂, mul_assoc (Real.sqrt ε₁) B_half B_one]
  have h_B_le : |B| ≤ Real.sqrt ε₂ * (B_half * B_one) := by
    have : |B| = Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂)| := by
      simp only [hB, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [this]
    have h₁ : Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| ≤
        Real.sqrt ε₂ * B_half :=
      mul_le_mul_of_nonneg_left h_half₂ (Real.sqrt_nonneg _)
    have h₂ : Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂)| ≤
        Real.sqrt ε₂ * B_half * B_one :=
      mul_le_mul h₁ h_one₂ (abs_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) h_B_half_nn)
    linarith [h₂, mul_assoc (Real.sqrt ε₂) B_half B_one]
  calc |A - B| ≤ |A| + |B| := abs_sub _ _
    _ ≤ Real.sqrt ε₁ * (B_half * B_one) + Real.sqrt ε₂ * (B_half * B_one) := by linarith
    _ = (Real.sqrt ε₁ + Real.sqrt ε₂) * (B_half * B_one) := by ring

/-- **|Δ| upper bound from uniform sup bounds.**
Combining the factor `|Δ| = √ε₁·√ε₂·|bracket|` with the bracket
triangle-inequality bound yields
`|Δ| ≤ √ε₁·√ε₂·(√ε₁+√ε₂)·B_half·B_one`. -/
lemma aperyBranchSingularDet_abs_le_uniform
    {ε₁ ε₂ B_half B_one : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (h_half₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂)| ≤ B_half)
    (h_half₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁)| ≤ B_half)
    (h_one₁ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁)| ≤ B_one)
    (h_one₂ : |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂)| ≤ B_one) :
    |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
      aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| ≤
      Real.sqrt ε₁ * Real.sqrt ε₂ *
        ((Real.sqrt ε₁ + Real.sqrt ε₂) * (B_half * B_one)) := by
  rw [aperyBranchSingularDet_abs_eq_sqrt_prod_mul_bracket hε₁ hε₂]
  exact mul_le_mul_of_nonneg_left
    (aperyBranchSingularBracket_abs_le_uniform h_half₁ h_half₂ h_one₁ h_one₂)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- **Quantitative `|Δ| ≥ c·√ε₁·√ε₂·|principal|` from a fractional
domination hypothesis.** If the perturbation bound is at most `(1−c)`
times the principal `|V_half_0·V_one_0·(√ε₁−√ε₂)|` for `c ∈ [0,1]`,
then `|Δ|` admits the strict lower bound `c·√ε₁·√ε₂·|principal|`.
Useful as a robust quantitative non-degeneracy that scales with `c`. -/
lemma aperyBranchSingularDet_abs_lower_bound_fraction
    {ε₁ ε₂ V_half_0 V_one_0 c : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (h_dom :
      Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0| +
      Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0| ≤
      (1 - c) * |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) :
    c * (Real.sqrt ε₁ * Real.sqrt ε₂ *
        |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) ≤
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  have h_lb := aperyBranchSingularDet_abs_lower_bound
    (V_half_0 := V_half_0) (V_one_0 := V_one_0) hε₁ hε₂
  have h_principal_nn : 0 ≤ |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)| :=
    abs_nonneg _
  have h_sqrt_nn : 0 ≤ Real.sqrt ε₁ * Real.sqrt ε₂ :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_inner :
      c * |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)| ≤
        |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)| -
          (Real.sqrt ε₁ *
            |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
              frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
              V_half_0 * V_one_0| +
            Real.sqrt ε₂ *
            |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
              frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
              V_half_0 * V_one_0|) := by linarith
  calc c * (Real.sqrt ε₁ * Real.sqrt ε₂ *
              |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|)
      = Real.sqrt ε₁ * Real.sqrt ε₂ *
          (c * |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) := by ring
    _ ≤ Real.sqrt ε₁ * Real.sqrt ε₂ *
          (|V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)| -
            (Real.sqrt ε₁ *
              |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
                frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
                V_half_0 * V_one_0| +
              Real.sqrt ε₂ *
              |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
                frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
                  Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
                V_half_0 * V_one_0|)) :=
      mul_le_mul_of_nonneg_left h_inner h_sqrt_nn
    _ ≤ _ := h_lb

/-- **Half-margin |Δ| lower bound.** Special case `c = 1/2` of the
fractional bound: if the perturbation is at most half the principal,
then `|Δ| ≥ (1/2)·√ε₁·√ε₂·|principal|`. Standard "halve the principal"
stability margin. -/
lemma aperyBranchSingularDet_abs_lower_bound_half
    {ε₁ ε₂ V_half_0 V_one_0 : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (h_dom :
      Real.sqrt ε₁ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₂) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₁) -
          V_half_0 * V_one_0| +
      Real.sqrt ε₂ *
        |frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly (1 / 2) 1 (-ε₁) *
          frobeniusValue (aperyPsSeq 0 0 Number.aperyQconifold
            Number.aperyPconifold) 2 Number.aperyConifoldZ1Poly 1 1 (-ε₂) -
          V_half_0 * V_one_0| ≤
      (1 / 2) * |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) :
    (1 / 2) * (Real.sqrt ε₁ * Real.sqrt ε₂ *
        |V_half_0 * V_one_0 * (Real.sqrt ε₁ - Real.sqrt ε₂)|) ≤
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  have h := aperyBranchSingularDet_abs_lower_bound_fraction
    (V_half_0 := V_half_0) (V_one_0 := V_one_0) (c := 1 / 2) hε₁ hε₂
  apply h
  have h_eq : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  rw [h_eq]
  exact h_dom

/-- **Triple of f-evaluations from a connection-coefficient witness.**
Given `IsAperyConnectionCoeffsOn a₀ a_half a₁ f I` with
`{0, −ε₁, −ε₂} ⊆ I`, packages the three resulting `f`-equations at
`z₁, z₁ − ε₁, z₁ − ε₂` into a single tuple — convenient when invoking
the Cramer / uniqueness machinery. -/
lemma IsAperyConnectionCoeffsOn.eval_three_points
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (h0 : (0 : ℝ) ∈ I) (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I) :
    f Number.aperyConifoldZ1Poly = a₀ ∧
    f (Number.aperyConifoldZ1Poly + (-ε₁)) =
        aperyBranchTriple a₀ a_half a₁ (-ε₁) ∧
    f (Number.aperyConifoldZ1Poly + (-ε₂)) =
        aperyBranchTriple a₀ a_half a₁ (-ε₂) := by
  refine ⟨?_, h _ hε₁, h _ hε₂⟩
  have h0' := h _ h0
  rw [add_zero] at h0'
  rw [h0', aperyBranchTriple_at_zero]

/-- **Three f-evaluations in amplitude form.** Like `eval_three_points`
but unfolds the right-hand sides via `aperyBranchTriple_at_neg_eps`,
exposing `(a₀, a_half, a₁)` linearly against `(V₀_amp, A_h, V_1)` —
this is exactly the system whose Cramer solution is `a_half_eq_div`/
`a_one_eq_div`. -/
lemma IsAperyConnectionCoeffsOn.eval_three_points_amp
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (h0 : (0 : ℝ) ∈ I) (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I) :
    f Number.aperyConifoldZ1Poly = a₀ ∧
    f (Number.aperyConifoldZ1Poly + (-ε₁)) =
        a₀ * aperyBranchAmplitude_zero ε₁ +
        a_half * aperyBranchAmplitude_half ε₁ +
        a₁ * aperyBranchValue_one ε₁ ∧
    f (Number.aperyConifoldZ1Poly + (-ε₂)) =
        a₀ * aperyBranchAmplitude_zero ε₂ +
        a_half * aperyBranchAmplitude_half ε₂ +
        a₁ * aperyBranchValue_one ε₂ := by
  obtain ⟨h₀, h₁, h₂⟩ := h.eval_three_points h0 hε₁ hε₂
  refine ⟨h₀, ?_, ?_⟩
  · rw [h₁, aperyBranchTriple_at_neg_eps]
  · rw [h₂, aperyBranchTriple_at_neg_eps]

/-- **All three connection coefficients are determined by `f` alone.**
Given a witness with `{0, −ε₁, −ε₂} ⊆ I` and Δ ≠ 0, the entire triple
`(a₀, a_half, a₁)` is computed from `f` evaluated only at those three
points — no auxiliary data. Bundles `regular_seed`, `a_half_from_f`,
`a_one_from_f`. -/
lemma IsAperyConnectionCoeffsOn.triple_from_f
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₀ = f Number.aperyConifoldZ1Poly ∧
    a_half =
      ((f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₁) *
              aperyBranchValue_one ε₂ -
        (f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₂) *
              aperyBranchValue_one ε₁) /
      (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) ∧
    a₁ =
      ((f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₂) *
              aperyBranchAmplitude_half ε₁ -
        (f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₁) *
              aperyBranchAmplitude_half ε₂) /
      (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) :=
  ⟨(h.regular_seed h0).symm,
   h.a_half_from_f h0 hε₁ hε₂ hdet,
   h.a_one_from_f h0 hε₁ hε₂ hdet⟩

/-- **Triple agreement from three-point f-agreement.** If `f` and `g`
agree at `{z₁, z₁ − ε₁, z₁ − ε₂}` and both are connection-coefficient
witnesses on a common index set (with `Δ ≠ 0`), then their connection
coefficient triples coincide. Direct corollary of `triple_from_f`. -/
lemma IsAperyConnectionCoeffsOn.triple_eq_of_three_point_agreement
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hg : IsAperyConnectionCoeffsOn b₀ b_half b₁ g I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0)
    (h_pt0 : f Number.aperyConifoldZ1Poly = g Number.aperyConifoldZ1Poly)
    (h_pt1 : f (Number.aperyConifoldZ1Poly + (-ε₁)) =
             g (Number.aperyConifoldZ1Poly + (-ε₁)))
    (h_pt2 : f (Number.aperyConifoldZ1Poly + (-ε₂)) =
             g (Number.aperyConifoldZ1Poly + (-ε₂))) :
    a₀ = b₀ ∧ a_half = b_half ∧ a₁ = b₁ := by
  obtain ⟨ha₀, ha_half, ha₁⟩ := hf.triple_from_f h0 hε₁ hε₂ hdet
  obtain ⟨hb₀, hb_half, hb₁⟩ := hg.triple_from_f h0 hε₁ hε₂ hdet
  refine ⟨?_, ?_, ?_⟩
  · rw [ha₀, hb₀, h_pt0]
  · rw [ha_half, hb_half, h_pt0, h_pt1, h_pt2]
  · rw [ha₁, hb₁, h_pt0, h_pt1, h_pt2]

/-- **Three-point vanishing forces zero triple.** If `f` is a connection-
coefficient witness (Δ ≠ 0) and vanishes at `{z₁, z₁ − ε₁, z₁ − ε₂}`,
then the triple is identically zero. Specialisation of `triple_from_f`. -/
lemma IsAperyConnectionCoeffsOn.triple_zero_of_three_point_vanish
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0)
    (h_pt0 : f Number.aperyConifoldZ1Poly = 0)
    (h_pt1 : f (Number.aperyConifoldZ1Poly + (-ε₁)) = 0)
    (h_pt2 : f (Number.aperyConifoldZ1Poly + (-ε₂)) = 0) :
    a₀ = 0 ∧ a_half = 0 ∧ a₁ = 0 := by
  obtain ⟨ha₀, ha_half, ha₁⟩ := h.triple_from_f h0 hε₁ hε₂ hdet
  refine ⟨?_, ?_, ?_⟩
  · rw [ha₀, h_pt0]
  · rw [ha_half, h_pt0, h_pt1, h_pt2]; ring
  · rw [ha₁, h_pt0, h_pt1, h_pt2]; ring

/-- **Iff form: zero triple ↔ three-point vanishing.** Under a witness
hypothesis with Δ ≠ 0 and `{0, −ε₁, −ε₂} ⊆ I`, the triple is zero
exactly when `f` vanishes at the three test points. The reverse
direction is the predicate identity at zero triple (`yAperyZero/Half/One`
all vanish for zero seeds at non-zero arguments — and `aperyBranchTriple
0 0 0 t = 0` is `aperyBranchTriple_zero`). -/
lemma IsAperyConnectionCoeffsOn.triple_zero_iff_three_point_vanish
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    (a₀ = 0 ∧ a_half = 0 ∧ a₁ = 0) ↔
    (f Number.aperyConifoldZ1Poly = 0 ∧
     f (Number.aperyConifoldZ1Poly + (-ε₁)) = 0 ∧
     f (Number.aperyConifoldZ1Poly + (-ε₂)) = 0) := by
  refine ⟨fun ⟨h₀, h_h, h₁⟩ => ?_, fun ⟨h_pt0, h_pt1, h_pt2⟩ =>
    h.triple_zero_of_three_point_vanish h0 hε₁ hε₂ hdet h_pt0 h_pt1 h_pt2⟩
  subst h₀; subst h_h; subst h₁
  obtain ⟨h₀_eq, h₁_eq, h₂_eq⟩ := h.eval_three_points h0 hε₁ hε₂
  refine ⟨h₀_eq, ?_, ?_⟩
  · rw [h₁_eq, aperyBranchTriple_zero]
  · rw [h₂_eq, aperyBranchTriple_zero]

/-- **`|a_half|` as |numerator| / |Δ|.** Direct `abs_div` form of the
closed-form `a_half_eq_div`, ready for stability estimates that bound
`|a_half|` via a numerator bound divided by a `|Δ|` lower bound. -/
lemma IsAperyConnectionCoeffsOn.a_half_abs_eq_div
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    |a_half| =
      |((f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            a₀ * aperyBranchAmplitude_zero ε₁) * aperyBranchValue_one ε₂ -
        (f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            a₀ * aperyBranchAmplitude_zero ε₂) * aperyBranchValue_one ε₁)| /
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  rw [h.a_half_eq_div hε₁ hε₂ hdet, abs_div]

/-- **`|a₁|` as |numerator| / |Δ|.** Companion to `a_half_abs_eq_div`. -/
lemma IsAperyConnectionCoeffsOn.a_one_abs_eq_div
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    |a₁| =
      |((f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            a₀ * aperyBranchAmplitude_zero ε₂) * aperyBranchAmplitude_half ε₁ -
        (f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            a₀ * aperyBranchAmplitude_zero ε₁) * aperyBranchAmplitude_half ε₂)| /
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  rw [h.a_one_eq_div hε₁ hε₂ hdet, abs_div]

/-- **Triangle bound `|a·b - c·d| ≤ |a|·|b| + |c|·|d|`.**
Pure ℝ-algebra workhorse for stability estimates on the
connection-coefficient numerators. -/
lemma abs_mul_sub_mul_triangle (a b c d : ℝ) :
    |a * b - c * d| ≤ |a| * |b| + |c| * |d| := by
  calc |a * b - c * d| ≤ |a * b| + |c * d| := abs_sub _ _
    _ = |a| * |b| + |c| * |d| := by rw [abs_mul, abs_mul]

/-- **Triangle bound on `a_half` numerator.** Direct application of
`abs_mul_sub_mul_triangle` to the explicit numerator of
`a_half_abs_eq_div`. Pure ℝ — no predicate hypothesis. -/
lemma aperyConnection_a_half_numerator_abs_le (f : ℝ → ℝ) (a₀ ε₁ ε₂ : ℝ) :
    |((f (Number.aperyConifoldZ1Poly + (-ε₁)) -
          a₀ * aperyBranchAmplitude_zero ε₁) * aperyBranchValue_one ε₂ -
      (f (Number.aperyConifoldZ1Poly + (-ε₂)) -
          a₀ * aperyBranchAmplitude_zero ε₂) * aperyBranchValue_one ε₁)| ≤
      |f (Number.aperyConifoldZ1Poly + (-ε₁)) -
          a₀ * aperyBranchAmplitude_zero ε₁| * |aperyBranchValue_one ε₂| +
      |f (Number.aperyConifoldZ1Poly + (-ε₂)) -
          a₀ * aperyBranchAmplitude_zero ε₂| * |aperyBranchValue_one ε₁| :=
  abs_mul_sub_mul_triangle _ _ _ _

/-- **Triangle bound on `a₁` numerator.** Companion to the `a_half`
version. -/
lemma aperyConnection_a_one_numerator_abs_le (f : ℝ → ℝ) (a₀ ε₁ ε₂ : ℝ) :
    |((f (Number.aperyConifoldZ1Poly + (-ε₂)) -
          a₀ * aperyBranchAmplitude_zero ε₂) * aperyBranchAmplitude_half ε₁ -
      (f (Number.aperyConifoldZ1Poly + (-ε₁)) -
          a₀ * aperyBranchAmplitude_zero ε₁) * aperyBranchAmplitude_half ε₂)| ≤
      |f (Number.aperyConifoldZ1Poly + (-ε₂)) -
          a₀ * aperyBranchAmplitude_zero ε₂| * |aperyBranchAmplitude_half ε₁| +
      |f (Number.aperyConifoldZ1Poly + (-ε₁)) -
          a₀ * aperyBranchAmplitude_zero ε₁| * |aperyBranchAmplitude_half ε₂| :=
  abs_mul_sub_mul_triangle _ _ _ _

/-- **End-to-end `|a_half|` stability bound.** Combines `a_half_abs_eq_div`
with the numerator triangle bound to give `|a_half| ≤ (numerator-side
sum) / |Δ|`. Plug in any `|Δ|` lower bound to convert into a fully
quantitative bound on `|a_half|`. -/
lemma IsAperyConnectionCoeffsOn.a_half_abs_le_div
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    |a_half| ≤
      (|f (Number.aperyConifoldZ1Poly + (-ε₁)) -
          a₀ * aperyBranchAmplitude_zero ε₁| * |aperyBranchValue_one ε₂| +
        |f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            a₀ * aperyBranchAmplitude_zero ε₂| * |aperyBranchValue_one ε₁|) /
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  rw [h.a_half_abs_eq_div hε₁ hε₂ hdet]
  apply div_le_div_of_nonneg_right (aperyConnection_a_half_numerator_abs_le _ _ _ _)
    (abs_nonneg _)

/-- **End-to-end `|a₁|` stability bound.** Companion to
`a_half_abs_le_div`. -/
lemma IsAperyConnectionCoeffsOn.a_one_abs_le_div
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    |a₁| ≤
      (|f (Number.aperyConifoldZ1Poly + (-ε₂)) -
          a₀ * aperyBranchAmplitude_zero ε₂| * |aperyBranchAmplitude_half ε₁| +
        |f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            a₀ * aperyBranchAmplitude_zero ε₁| * |aperyBranchAmplitude_half ε₂|) /
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  rw [h.a_one_abs_eq_div hε₁ hε₂ hdet]
  apply div_le_div_of_nonneg_right (aperyConnection_a_one_numerator_abs_le _ _ _ _)
    (abs_nonneg _)

/-- **`|a_half|` stability bound (f-only form).** Like `a_half_abs_le_div`
but uses `f(z₁)` in place of `a₀` via `regular_seed`, giving a bound
that depends only on `f`-values. -/
lemma IsAperyConnectionCoeffsOn.a_half_abs_le_div_from_f
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    |a_half| ≤
      (|f (Number.aperyConifoldZ1Poly + (-ε₁)) -
          f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₁| *
            |aperyBranchValue_one ε₂| +
        |f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₂| *
            |aperyBranchValue_one ε₁|) /
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  have h_le := h.a_half_abs_le_div hε₁ hε₂ hdet
  rw [← h.regular_seed h0] at h_le
  exact h_le

/-- **`|a₁|` stability bound (f-only form).** Companion to
`a_half_abs_le_div_from_f`. -/
lemma IsAperyConnectionCoeffsOn.a_one_abs_le_div_from_f
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    |a₁| ≤
      (|f (Number.aperyConifoldZ1Poly + (-ε₂)) -
          f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₂| *
            |aperyBranchAmplitude_half ε₁| +
        |f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₁| *
            |aperyBranchAmplitude_half ε₂|) /
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  have h_le := h.a_one_abs_le_div hε₁ hε₂ hdet
  rw [← h.regular_seed h0] at h_le
  exact h_le

/-- **`|a₀|` evaluated via `f`.** Direct corollary of `regular_seed`:
the magnitude of the regular connection coefficient equals `|f(z₁)|`. -/
lemma IsAperyConnectionCoeffsOn.a_zero_abs_eq_from_f
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I) :
    |a₀| = |f Number.aperyConifoldZ1Poly| := by
  rw [← h.regular_seed h0]

/-- **Connection residual at `−ε`.** The discrepancy between `f(z₁ − ε)`
and the regular component `f(z₁) · A_0(ε)`. Captures the `a_half · A_½(ε)
+ a₁ · V_1(ε)` part of the right-endpoint expansion. -/
noncomputable def aperyConnectionResidual (f : ℝ → ℝ) (ε : ℝ) : ℝ :=
  f (Number.aperyConifoldZ1Poly + (-ε)) -
    f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε

/-- **Residual vanishes at `ε = 0`.** Since `A_0(0) = 1`, the residual
collapses to zero — the regular branch absorbs `f(z₁)` exactly. -/
@[simp] lemma aperyConnectionResidual_zero (f : ℝ → ℝ) :
    aperyConnectionResidual f 0 = 0 := by
  unfold aperyConnectionResidual
  simp [aperyBranchAmplitude_zero_at_zero]

/-- **Residual is additive in `f`.** -/
lemma aperyConnectionResidual_add (f g : ℝ → ℝ) (ε : ℝ) :
    aperyConnectionResidual (fun x => f x + g x) ε =
      aperyConnectionResidual f ε + aperyConnectionResidual g ε := by
  unfold aperyConnectionResidual; ring

/-- **Residual is homogeneous in `f`.** -/
lemma aperyConnectionResidual_smul (c : ℝ) (f : ℝ → ℝ) (ε : ℝ) :
    aperyConnectionResidual (fun x => c * f x) ε =
      c * aperyConnectionResidual f ε := by
  unfold aperyConnectionResidual; ring

/-- **Residual is subtractive in `f`.** -/
lemma aperyConnectionResidual_sub (f g : ℝ → ℝ) (ε : ℝ) :
    aperyConnectionResidual (fun x => f x - g x) ε =
      aperyConnectionResidual f ε - aperyConnectionResidual g ε := by
  unfold aperyConnectionResidual; ring

/-- **Residual of the negation.** -/
lemma aperyConnectionResidual_neg (f : ℝ → ℝ) (ε : ℝ) :
    aperyConnectionResidual (fun x => -(f x)) ε =
      -(aperyConnectionResidual f ε) := by
  unfold aperyConnectionResidual; ring

/-- **Residual of the zero function.** -/
@[simp] lemma aperyConnectionResidual_zero_fn (ε : ℝ) :
    aperyConnectionResidual (fun _ => (0 : ℝ)) ε = 0 := by
  unfold aperyConnectionResidual; ring

/-- **Residual vanishes iff value matches regular branch.** Direct
restatement of the definition: `residual f ε = 0` is exactly the equation
`f(z₁ − ε) = f(z₁) · A_0(ε)`. -/
lemma aperyConnectionResidual_eq_zero_iff (f : ℝ → ℝ) (ε : ℝ) :
    aperyConnectionResidual f ε = 0 ↔
      f (Number.aperyConifoldZ1Poly + (-ε)) =
        f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε := by
  unfold aperyConnectionResidual
  exact sub_eq_zero

/-- **Residual is zero on the regular branch.** When `f x = c · A_0(z₁ - x)`
… actually the cleaner statement: residual of a constant function is the
constant itself times `(1 − A_0(ε))`. -/
lemma aperyConnectionResidual_const (c : ℝ) (ε : ℝ) :
    aperyConnectionResidual (fun _ => c) ε =
      c * (1 - aperyBranchAmplitude_zero ε) := by
  unfold aperyConnectionResidual; ring

/-- **Residual decomposition (continuity form).** Splits the residual into
the local discrepancy `f(z₁ − ε) − f(z₁)` and the regular-branch
deviation `f(z₁) · (1 − A_0(ε))`. Useful for showing residual → 0 as
`ε → 0` from continuity of `f` and `A_0(0) = 1`. -/
lemma aperyConnectionResidual_decomp (f : ℝ → ℝ) (ε : ℝ) :
    aperyConnectionResidual f ε =
      (f (Number.aperyConifoldZ1Poly + (-ε)) - f Number.aperyConifoldZ1Poly) +
      f Number.aperyConifoldZ1Poly * (1 - aperyBranchAmplitude_zero ε) := by
  unfold aperyConnectionResidual; ring

/-- **Residual triangle bound (raw form).** Bounds `|residual|` by the
sum of the two endpoint magnitudes — the simplest crude bound, useful
when no continuity information is available. -/
lemma aperyConnectionResidual_abs_le_raw (f : ℝ → ℝ) (ε : ℝ) :
    |aperyConnectionResidual f ε| ≤
      |f (Number.aperyConifoldZ1Poly + (-ε))| +
      |f Number.aperyConifoldZ1Poly| * |aperyBranchAmplitude_zero ε| := by
  unfold aperyConnectionResidual
  calc |f (Number.aperyConifoldZ1Poly + (-ε)) -
          f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε|
      ≤ |f (Number.aperyConifoldZ1Poly + (-ε))| +
        |f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε| := abs_sub _ _
    _ = |f (Number.aperyConifoldZ1Poly + (-ε))| +
        |f Number.aperyConifoldZ1Poly| * |aperyBranchAmplitude_zero ε| := by rw [abs_mul]

/-- **Residual triangle bound (continuity form).** -/
lemma aperyConnectionResidual_abs_le_decomp (f : ℝ → ℝ) (ε : ℝ) :
    |aperyConnectionResidual f ε| ≤
      |f (Number.aperyConifoldZ1Poly + (-ε)) - f Number.aperyConifoldZ1Poly| +
      |f Number.aperyConifoldZ1Poly| * |1 - aperyBranchAmplitude_zero ε| := by
  rw [aperyConnectionResidual_decomp]
  calc |(f (Number.aperyConifoldZ1Poly + (-ε)) - f Number.aperyConifoldZ1Poly) +
          f Number.aperyConifoldZ1Poly * (1 - aperyBranchAmplitude_zero ε)|
      ≤ |f (Number.aperyConifoldZ1Poly + (-ε)) - f Number.aperyConifoldZ1Poly| +
        |f Number.aperyConifoldZ1Poly * (1 - aperyBranchAmplitude_zero ε)| :=
        abs_add_le _ _
    _ = |f (Number.aperyConifoldZ1Poly + (-ε)) - f Number.aperyConifoldZ1Poly| +
        |f Number.aperyConifoldZ1Poly| * |1 - aperyBranchAmplitude_zero ε| := by
        rw [abs_mul]

/-- **Residual identity.** When `(a₀, a_half, a₁)` represents `f` on a set
containing `0` and `−ε`, the connection residual at `−ε` equals
`a_half · A_½(ε) + a₁ · V_1(ε)`. Direct from `right_endpoint` and
`regular_seed`. -/
lemma IsAperyConnectionCoeffsOn.aperyConnectionResidual_eq
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε : ℝ} (hε : (-ε) ∈ I) :
    aperyConnectionResidual f ε =
      a_half * aperyBranchAmplitude_half ε + a₁ * aperyBranchValue_one ε := by
  unfold aperyConnectionResidual
  rw [h.right_endpoint hε, h.regular_seed h0]
  ring

/-- **Triangle bound on `|residual|`.** When `(a₀, a_half, a₁)` represents
`f` on a set containing `0` and `−ε`, the residual is controlled by the
singular coefficients: `|residual(ε)| ≤ |a_half|·|A_½(ε)| + |a₁|·|V_1(ε)|`. -/
lemma IsAperyConnectionCoeffsOn.aperyConnectionResidual_abs_le
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε : ℝ} (hε : (-ε) ∈ I) :
    |aperyConnectionResidual f ε| ≤
      |a_half| * |aperyBranchAmplitude_half ε| +
      |a₁| * |aperyBranchValue_one ε| := by
  rw [h.aperyConnectionResidual_eq h0 hε]
  calc |a_half * aperyBranchAmplitude_half ε + a₁ * aperyBranchValue_one ε|
      ≤ |a_half * aperyBranchAmplitude_half ε| + |a₁ * aperyBranchValue_one ε| :=
        abs_add_le _ _
    _ = |a_half| * |aperyBranchAmplitude_half ε| +
        |a₁| * |aperyBranchValue_one ε| := by rw [abs_mul, abs_mul]

/-- **The 2×2 singular-pair determinant is anti-symmetric under
`ε`-swap.** -/
lemma aperyBranchSingularDet_swap (ε₁ ε₂ : ℝ) :
    aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ -
        aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ =
      -(aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  ring

/-- **`|Δ|` is symmetric under `ε`-swap.** -/
lemma aperyBranchSingularDet_abs_swap (ε₁ ε₂ : ℝ) :
    |aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ -
        aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂| =
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  rw [aperyBranchSingularDet_swap]
  exact abs_neg _

/-- **Δ vanishes on the diagonal.** When `ε₁ = ε₂`, the two columns of the
2×2 singular system are identical, so the determinant is zero. -/
@[simp] lemma aperyBranchSingularDet_diag (ε : ℝ) :
    aperyBranchAmplitude_half ε * aperyBranchValue_one ε -
        aperyBranchAmplitude_half ε * aperyBranchValue_one ε = 0 := by
  ring

/-- **Closed form for `a_half` (residual form).** Cramer's rule
expressed via the connection residuals. -/
lemma IsAperyConnectionCoeffsOn.a_half_eq_div_residual
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a_half =
      (aperyConnectionResidual f ε₁ * aperyBranchValue_one ε₂ -
        aperyConnectionResidual f ε₂ * aperyBranchValue_one ε₁) /
      (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  simpa [aperyConnectionResidual] using h.a_half_from_f h0 hε₁ hε₂ hdet

/-- **Closed form for `a₁` (residual form).** -/
lemma IsAperyConnectionCoeffsOn.a_one_eq_div_residual
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₁ =
      (aperyConnectionResidual f ε₂ * aperyBranchAmplitude_half ε₁ -
        aperyConnectionResidual f ε₁ * aperyBranchAmplitude_half ε₂) /
      (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  simpa [aperyConnectionResidual] using h.a_one_from_f h0 hε₁ hε₂ hdet

/-- **`|a_half|` stability bound packaged via residuals.** Rephrases
`a_half_abs_le_div_from_f` using `aperyConnectionResidual`. -/
lemma IsAperyConnectionCoeffsOn.a_half_abs_le_div_residual
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    |a_half| ≤
      (|aperyConnectionResidual f ε₁| * |aperyBranchValue_one ε₂| +
        |aperyConnectionResidual f ε₂| * |aperyBranchValue_one ε₁|) /
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  simpa [aperyConnectionResidual] using h.a_half_abs_le_div_from_f h0 hε₁ hε₂ hdet

/-- **`|a₁|` stability bound packaged via residuals.** Companion to
`a_half_abs_le_div_residual`. -/
lemma IsAperyConnectionCoeffsOn.a_one_abs_le_div_residual
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (h0 : (0 : ℝ) ∈ I)
    {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    |a₁| ≤
      (|aperyConnectionResidual f ε₂| * |aperyBranchAmplitude_half ε₁| +
        |aperyConnectionResidual f ε₁| * |aperyBranchAmplitude_half ε₂|) /
      |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  simpa [aperyConnectionResidual] using h.a_one_abs_le_div_from_f h0 hε₁ hε₂ hdet

/-- **Apéry connection-coefficient representability.** A function `f` is
representable on `I` if some triple `(a₀, a_half, a₁)` satisfies
`IsAperyConnectionCoeffsOn`. -/
def HasAperyConnectionCoeffsOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ a₀ a_half a₁ : ℝ, IsAperyConnectionCoeffsOn a₀ a_half a₁ f I

/-- **Witness extraction.** -/
lemma IsAperyConnectionCoeffsOn.hasAperyConnectionCoeffsOn
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (h : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) :
    HasAperyConnectionCoeffsOn f I :=
  ⟨a₀, a_half, a₁, h⟩

/-- **Representability is monotone in the domain.** Reuses
`IsAperyConnectionCoeffsOn.mono` (already in scope). -/
lemma HasAperyConnectionCoeffsOn.mono
    {f : ℝ → ℝ} {I J : Set ℝ}
    (h : HasAperyConnectionCoeffsOn f I) (hJ : J ⊆ I) :
    HasAperyConnectionCoeffsOn f J := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  exact ⟨a₀, a_half, a₁, h.mono hJ⟩

/-- **Closure under scalar multiplication.** -/
lemma HasAperyConnectionCoeffsOn.smul (c : ℝ) {f : ℝ → ℝ} {I : Set ℝ}
    (h : HasAperyConnectionCoeffsOn f I) :
    HasAperyConnectionCoeffsOn (fun z => c * f z) I := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  exact ⟨c * a₀, c * a_half, c * a₁, h.smul c⟩

/-- **Closure under addition.** Combine two representations on the same
domain into one for the pointwise sum. -/
lemma HasAperyConnectionCoeffsOn.add {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : HasAperyConnectionCoeffsOn f I)
    (hg : HasAperyConnectionCoeffsOn g I) :
    HasAperyConnectionCoeffsOn (fun z => f z + g z) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  obtain ⟨b₀, b_half, b₁, hg⟩ := hg
  exact ⟨a₀ + b₀, a_half + b_half, a₁ + b₁, hf.add hg⟩

/-- **Closure under negation.** -/
lemma HasAperyConnectionCoeffsOn.neg {f : ℝ → ℝ} {I : Set ℝ}
    (hf : HasAperyConnectionCoeffsOn f I) :
    HasAperyConnectionCoeffsOn (fun z => -(f z)) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  exact ⟨-a₀, -a_half, -a₁, hf.neg⟩

/-- **Closure under subtraction.** -/
lemma HasAperyConnectionCoeffsOn.sub {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : HasAperyConnectionCoeffsOn f I)
    (hg : HasAperyConnectionCoeffsOn g I) :
    HasAperyConnectionCoeffsOn (fun z => f z - g z) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  obtain ⟨b₀, b_half, b₁, hg⟩ := hg
  exact ⟨a₀ - b₀, a_half - b_half, a₁ - b₁, hf.sub hg⟩

/-- **Zero function is representable.** Trivial witness `(0, 0, 0)`. -/
lemma HasAperyConnectionCoeffsOn.zero (I : Set ℝ) :
    HasAperyConnectionCoeffsOn (fun _ => (0 : ℝ)) I :=
  ⟨0, 0, 0, IsAperyConnectionCoeffsOn.zero I⟩

/-- **Singleton-`{0}` representability.** Every function `f` is representable
on the trivial domain `{0}`: take `a₀ := f(z₁)`, with `a_half = a₁ = 0`.
The shift constraint at `t = 0` collapses to `f(z₁) = a₀`, which holds by
choice. -/
lemma HasAperyConnectionCoeffsOn.singleton_zero (f : ℝ → ℝ) :
    HasAperyConnectionCoeffsOn f {0} :=
  ⟨f Number.aperyConifoldZ1Poly, 0, 0,
    (IsAperyConnectionCoeffsOn.singleton_zero_iff
      (f Number.aperyConifoldZ1Poly) 0 0 f).2 rfl⟩

/-- **Empty-domain representability.** With no constraints, the witness
`(0, 0, 0)` works vacuously. -/
lemma HasAperyConnectionCoeffsOn.empty (f : ℝ → ℝ) :
    HasAperyConnectionCoeffsOn f (∅ : Set ℝ) :=
  ⟨0, 0, 0, fun _ ht => by exact absurd ht (Set.notMem_empty _)⟩

/-- **Three-point representability.** Every function `f` is representable
on the canonical three-point test set `{0, −ε₁, −ε₂}` whenever Δ ≠ 0.
Direct lift of `IsAperyConnectionCoeffsOn.exists_on_three_points`. -/
lemma HasAperyConnectionCoeffsOn.three_points (f : ℝ → ℝ) {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    HasAperyConnectionCoeffsOn f ({0, -ε₁, -ε₂} : Set ℝ) := by
  obtain ⟨a₀, a_half, a₁, h⟩ :=
    IsAperyConnectionCoeffsOn.exists_on_three_points f hdet
  exact ⟨a₀, a_half, a₁, h⟩

/-- **Three-point representability (explicit triple).** Strengthens
`three_points` by exposing the unique triple `(a₀, a_half, a₁)` from the
Cramer formulas, with `a₀ = f(z₁)`. Under Δ ≠ 0, the witness is unique. -/
lemma HasAperyConnectionCoeffsOn.three_points_witness (f : ℝ → ℝ) {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ∃ a₀ a_half a₁ : ℝ,
      IsAperyConnectionCoeffsOn a₀ a_half a₁ f ({0, -ε₁, -ε₂} : Set ℝ) ∧
      a₀ = f Number.aperyConifoldZ1Poly := by
  obtain ⟨a₀, a_half, a₁, h⟩ :=
    IsAperyConnectionCoeffsOn.exists_on_three_points f hdet
  have h0 : (0 : ℝ) ∈ ({0, -ε₁, -ε₂} : Set ℝ) := by simp
  exact ⟨a₀, a_half, a₁, h, (h.regular_seed h0).symm⟩

/-- **Closure under domain union.** -/
lemma HasAperyConnectionCoeffsOn.union_of_witness
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I J : Set ℝ}
    (hI : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hJ : IsAperyConnectionCoeffsOn a₀ a_half a₁ f J) :
    HasAperyConnectionCoeffsOn f (I ∪ J) :=
  ⟨a₀, a_half, a₁, hI.union hJ⟩

/-- **Regular seed witness extraction.** If `f` is representable on `I`
containing `0`, then there exists a regular-branch coefficient witness
equal to `f(z₁)`. (The witness is just `a₀` from any representation.) -/
lemma HasAperyConnectionCoeffsOn.exists_regular_witness
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) :
    ∃ a₀ a_half a₁ : ℝ,
      IsAperyConnectionCoeffsOn a₀ a_half a₁ f I ∧
      a₀ = f Number.aperyConifoldZ1Poly := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  exact ⟨a₀, a_half, a₁, h, (h.regular_seed h0).symm⟩

/-- **Residual lies in the singular span.** If `f` is representable on `I`
containing `0` and `−ε`, then `residual(ε)` equals `a_half · A_½(ε) +
a₁ · V_1(ε)` for some pair `(a_half, a₁)`. -/
lemma HasAperyConnectionCoeffsOn.exists_singular_pair
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε : ℝ} (hε : (-ε) ∈ I) :
    ∃ a_half a₁ : ℝ,
      aperyConnectionResidual f ε =
        a_half * aperyBranchAmplitude_half ε +
        a₁ * aperyBranchValue_one ε := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  exact ⟨a_half, a₁, h.aperyConnectionResidual_eq h0 hε⟩

/-- **Three-point vanishing forces zero on all of `z₁ + I`.** At the
representability level, if `f` is `Has`-representable on `I`, vanishes
at `{z₁, z₁ − ε₁, z₁ − ε₂}` (with Δ ≠ 0), then `f` vanishes on
`z₁ + t` for every `t ∈ I`. -/
lemma HasAperyConnectionCoeffsOn.eq_zero_of_three_point_vanish
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0)
    (h_pt0 : f Number.aperyConifoldZ1Poly = 0)
    (h_pt1 : f (Number.aperyConifoldZ1Poly + (-ε₁)) = 0)
    (h_pt2 : f (Number.aperyConifoldZ1Poly + (-ε₂)) = 0) :
    ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) = 0 := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  obtain ⟨ha₀, ha_half, ha₁⟩ :=
    h.triple_zero_of_three_point_vanish h0 hε₁ hε₂ hdet h_pt0 h_pt1 h_pt2
  intro t ht
  have := h t ht
  rw [ha₀, ha_half, ha₁, aperyBranchTriple_zero] at this
  exact this

/-- **Three-point agreement forces global agreement on `z₁ + I`.** If
`f` and `g` are both representable on `I` and agree at the three test
points `{z₁, z₁ − ε₁, z₁ − ε₂}` (Δ ≠ 0), then `f` and `g` agree on
`z₁ + t` for every `t ∈ I`. Direct via `f - g` reduction to
`eq_zero_of_three_point_vanish`. -/
lemma HasAperyConnectionCoeffsOn.eq_of_three_point_agreement
    {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : HasAperyConnectionCoeffsOn f I)
    (hg : HasAperyConnectionCoeffsOn g I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0)
    (h_pt0 : f Number.aperyConifoldZ1Poly = g Number.aperyConifoldZ1Poly)
    (h_pt1 : f (Number.aperyConifoldZ1Poly + (-ε₁)) =
             g (Number.aperyConifoldZ1Poly + (-ε₁)))
    (h_pt2 : f (Number.aperyConifoldZ1Poly + (-ε₂)) =
             g (Number.aperyConifoldZ1Poly + (-ε₂))) :
    ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) =
              g (Number.aperyConifoldZ1Poly + t) := by
  have hdiff : HasAperyConnectionCoeffsOn (fun z => f z - g z) I := hf.sub hg
  have hzero : ∀ t ∈ I, (fun z => f z - g z) (Number.aperyConifoldZ1Poly + t) = 0 :=
    hdiff.eq_zero_of_three_point_vanish h0 hε₁ hε₂ hdet
      (by simp [h_pt0]) (by simp [h_pt1]) (by simp [h_pt2])
  intro t ht
  have := hzero t ht
  linarith

/-- **Right-endpoint expansion (representability form).** If `f` is
representable on `I` containing `0` and `−ε`, then there is a
singular-branch pair `(a_half, a₁)` such that `f(z₁ − ε)` decomposes as
`f(z₁) · A_0(ε) + a_half · A_½(ε) + a₁ · V_1(ε)`. -/
lemma HasAperyConnectionCoeffsOn.right_endpoint
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε : ℝ} (hε : (-ε) ∈ I) :
    ∃ a_half a₁ : ℝ,
      f (Number.aperyConifoldZ1Poly + (-ε)) =
        f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε +
        a_half * aperyBranchAmplitude_half ε +
        a₁ * aperyBranchValue_one ε := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  refine ⟨a_half, a₁, ?_⟩
  rw [h.right_endpoint hε, h.regular_seed h0]

/-- **`|a_half|` stability bound at the Has-level.** Existence of a
singular witness `a_half` (extracted from any representation) bounded by
the f-only stability expression. -/
lemma HasAperyConnectionCoeffsOn.exists_a_half_abs_le_div_from_f
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ∃ a_half : ℝ,
      |a_half| ≤
        (|f (Number.aperyConifoldZ1Poly + (-ε₁)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₁| *
              |aperyBranchValue_one ε₂| +
          |f (Number.aperyConifoldZ1Poly + (-ε₂)) -
              f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₂| *
              |aperyBranchValue_one ε₁|) /
        |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  exact ⟨a_half, h.a_half_abs_le_div_from_f h0 hε₁ hε₂ hdet⟩

/-- **`|a₁|` stability bound at the Has-level.** Companion to
`exists_a_half_abs_le_div_from_f`. -/
lemma HasAperyConnectionCoeffsOn.exists_a_one_abs_le_div_from_f
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ∃ a₁ : ℝ,
      |a₁| ≤
        (|f (Number.aperyConifoldZ1Poly + (-ε₂)) -
            f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₂| *
              |aperyBranchAmplitude_half ε₁| +
          |f (Number.aperyConifoldZ1Poly + (-ε₁)) -
              f Number.aperyConifoldZ1Poly * aperyBranchAmplitude_zero ε₁| *
              |aperyBranchAmplitude_half ε₂|) /
        |aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁| := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  exact ⟨a₁, h.a_one_abs_le_div_from_f h0 hε₁ hε₂ hdet⟩

/-- **Pure ρ=0 branch lift.** If `f(z₁ + t) = yAperyZero a₀ t` on `I`, then
`f` is representable. Has-level lift of `IsAperyConnectionCoeffsOn.of_pure_regular`. -/
lemma HasAperyConnectionCoeffsOn.of_pure_regular
    (a₀ : ℝ) (f : ℝ → ℝ) (I : Set ℝ)
    (h : ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) = yAperyZero a₀ t) :
    HasAperyConnectionCoeffsOn f I :=
  ⟨a₀, 0, 0, IsAperyConnectionCoeffsOn.of_pure_regular a₀ f I h⟩

/-- **Pure ρ=1/2 branch lift.** Has-level companion to
`IsAperyConnectionCoeffsOn.of_pure_half`. -/
lemma HasAperyConnectionCoeffsOn.of_pure_half
    (a_half : ℝ) (f : ℝ → ℝ) (I : Set ℝ)
    (h : ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) = yAperyHalf a_half t) :
    HasAperyConnectionCoeffsOn f I :=
  ⟨0, a_half, 0, IsAperyConnectionCoeffsOn.of_pure_half a_half f I h⟩

/-- **Pure ρ=1 branch lift.** Has-level companion to
`IsAperyConnectionCoeffsOn.of_pure_one`. -/
lemma HasAperyConnectionCoeffsOn.of_pure_one
    (a₁ : ℝ) (f : ℝ → ℝ) (I : Set ℝ)
    (h : ∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) = yApery a₁ t) :
    HasAperyConnectionCoeffsOn f I :=
  ⟨0, 0, a₁, IsAperyConnectionCoeffsOn.of_pure_one a₁ f I h⟩

/-- **Regular-seed pinning at Has-level.** Every realising triple
`(a₀, a_half, a₁)` of a function `f` on `I ∋ 0` satisfies `a₀ = f(z₁)`. -/
lemma HasAperyConnectionCoeffsOn.forall_regular_seed_eq
    {f : ℝ → ℝ} {I : Set ℝ} (h0 : (0 : ℝ) ∈ I) :
    ∀ a₀ a_half a₁ : ℝ,
      IsAperyConnectionCoeffsOn a₀ a_half a₁ f I →
      a₀ = f Number.aperyConifoldZ1Poly :=
  fun _ _ _ ha => (ha.regular_seed h0).symm

/-- **Smul-left invariance under nonzero scalar.** Has-level representability
of `c · f` on `I` is equivalent to that of `f`, when `c ≠ 0`. Forward: smul.
Backward: smul by `1/c`. -/
lemma HasAperyConnectionCoeffsOn.smul_iff
    {c : ℝ} (hc : c ≠ 0) {f : ℝ → ℝ} {I : Set ℝ} :
    HasAperyConnectionCoeffsOn (fun z => c * f z) I ↔
      HasAperyConnectionCoeffsOn f I := by
  refine ⟨fun h => ?_, fun h => h.smul c⟩
  have hinv : (1 / c) * c = 1 := by field_simp
  obtain ⟨a₀, a_half, a₁, h⟩ := h.smul (1 / c)
  refine ⟨a₀, a_half, a₁, h.congr (fun t _ => ?_)⟩
  change 1 / c * (c * f (Number.aperyConifoldZ1Poly + t)) =
        f (Number.aperyConifoldZ1Poly + t)
  rw [← mul_assoc, hinv, one_mul]

/-- **Has-level uniqueness of the witness triple under bracket nondegeneracy.**
If `f` is representable on `I` containing `0` and two singular witnesses
`−ε₁, −ε₂` with `Δ ≠ 0`, then the realising triple is unique
(packaged as `ExistsUnique`). -/
lemma HasAperyConnectionCoeffsOn.existsUnique_witness
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ∃! abc : ℝ × ℝ × ℝ,
      IsAperyConnectionCoeffsOn abc.1 abc.2.1 abc.2.2 f I := by
  obtain ⟨a₀, a_half, a₁, ha⟩ := h
  refine ⟨(a₀, a_half, a₁), ha, ?_⟩
  rintro ⟨b₀, b_half, b₁⟩ hb
  exact hb.triple_eq_of_two_witnesses ha h0 hε₁ hε₂ hdet

/-- **Has-level Iff via shifted equality.** Has-level form of
`iff_shifted_eqOn`: representability is exactly the existence of a triple
`(a₀, a_half, a₁)` such that the shifted function equals `aperyBranchTriple`
pointwise on `I`. -/
lemma HasAperyConnectionCoeffsOn.iff_exists_eqOn
    (f : ℝ → ℝ) (I : Set ℝ) :
    HasAperyConnectionCoeffsOn f I ↔
      ∃ a₀ a_half a₁ : ℝ,
        Set.EqOn (fun t => f (Number.aperyConifoldZ1Poly + t))
          (fun t => aperyBranchTriple a₀ a_half a₁ t) I :=
  Iff.rfl

/-- **Congruence atom.** Has-level companion to
`IsAperyConnectionCoeffsOn.congr`: representability transports along
shifted-pointwise equality. -/
lemma HasAperyConnectionCoeffsOn.congr
    {f g : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (hfg : ∀ t ∈ I,
      f (Number.aperyConifoldZ1Poly + t) = g (Number.aperyConifoldZ1Poly + t)) :
    HasAperyConnectionCoeffsOn g I := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  exact ⟨a₀, a_half, a₁, h.congr hfg⟩

/-- **Inter-left.** Has-level companion to `IsAperyConnectionCoeffsOn.inter_left`. -/
lemma HasAperyConnectionCoeffsOn.inter_left
    {f : ℝ → ℝ} {I J : Set ℝ} (h : HasAperyConnectionCoeffsOn f I) :
    HasAperyConnectionCoeffsOn f (I ∩ J) := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  exact ⟨a₀, a_half, a₁, h.inter_left⟩

/-- **Inter-right.** Has-level companion to `IsAperyConnectionCoeffsOn.inter_right`. -/
lemma HasAperyConnectionCoeffsOn.inter_right
    {f : ℝ → ℝ} {I J : Set ℝ} (h : HasAperyConnectionCoeffsOn f J) :
    HasAperyConnectionCoeffsOn f (I ∩ J) := by
  obtain ⟨a₀, a_half, a₁, h⟩ := h
  exact ⟨a₀, a_half, a₁, h.inter_right⟩

/-- **Iff form of three-point vanishing.** A representable function vanishes
on every `z₁ + I` iff it vanishes at the three test points `0, −ε₁, −ε₂`
under bracket nondegeneracy. -/
lemma HasAperyConnectionCoeffsOn.eq_zero_iff_three_point_vanish
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    (∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) = 0) ↔
      f Number.aperyConifoldZ1Poly = 0 ∧
      f (Number.aperyConifoldZ1Poly + (-ε₁)) = 0 ∧
      f (Number.aperyConifoldZ1Poly + (-ε₂)) = 0 := by
  refine ⟨fun hall => ?_, fun ⟨h_pt0, h_pt1, h_pt2⟩ => ?_⟩
  · refine ⟨?_, hall (-ε₁) hε₁, hall (-ε₂) hε₂⟩
    have := hall 0 h0; simpa using this
  · exact h.eq_zero_of_three_point_vanish h0 hε₁ hε₂ hdet h_pt0 h_pt1 h_pt2

/-- **Iff form of three-point agreement.** Two representable functions agree
on every `z₁ + I` iff they agree at the three test points `0, −ε₁, −ε₂`
under bracket nondegeneracy. The forward direction is by specialisation of
the global agreement; the backward direction is `eq_of_three_point_agreement`. -/
lemma HasAperyConnectionCoeffsOn.eq_iff_three_point_agreement
    {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : HasAperyConnectionCoeffsOn f I)
    (hg : HasAperyConnectionCoeffsOn g I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    (∀ t ∈ I, f (Number.aperyConifoldZ1Poly + t) =
              g (Number.aperyConifoldZ1Poly + t)) ↔
      f Number.aperyConifoldZ1Poly = g Number.aperyConifoldZ1Poly ∧
      f (Number.aperyConifoldZ1Poly + (-ε₁)) =
        g (Number.aperyConifoldZ1Poly + (-ε₁)) ∧
      f (Number.aperyConifoldZ1Poly + (-ε₂)) =
        g (Number.aperyConifoldZ1Poly + (-ε₂)) := by
  refine ⟨fun hall => ?_, fun ⟨h_pt0, h_pt1, h_pt2⟩ => ?_⟩
  · refine ⟨?_, hall (-ε₁) hε₁, hall (-ε₂) hε₂⟩
    have := hall 0 h0; simpa using this
  · exact hf.eq_of_three_point_agreement hg h0 hε₁ hε₂ hdet h_pt0 h_pt1 h_pt2

/-- **Three-pure-branch composition lift.** Has-level companion to
`IsAperyConnectionCoeffsOn.of_three_pure`: pointwise sum of three
pure-branch witnesses is representable. -/
lemma HasAperyConnectionCoeffsOn.of_three_pure
    (a₀ a_half a₁ : ℝ) (Y₀ Y_half Y_one : ℝ → ℝ) (I : Set ℝ)
    (hY₀ : ∀ t ∈ I, Y₀ (Number.aperyConifoldZ1Poly + t) = yAperyZero a₀ t)
    (hY_half : ∀ t ∈ I,
      Y_half (Number.aperyConifoldZ1Poly + t) = yAperyHalf a_half t)
    (hY_one : ∀ t ∈ I,
      Y_one (Number.aperyConifoldZ1Poly + t) = yApery a₁ t) :
    HasAperyConnectionCoeffsOn (fun z => Y₀ z + Y_half z + Y_one z) I :=
  ⟨a₀, a_half, a₁,
    IsAperyConnectionCoeffsOn.of_three_pure a₀ a_half a₁ Y₀ Y_half Y_one I
      hY₀ hY_half hY_one⟩

/-- **Residual of pure regular branch is zero.** When `f x := yAperyZero a₀ (x − z₁)`
(the regular Frobenius branch shifted to act on the original variable), the
connection residual at any `ε` vanishes identically: `f(z₁ − ε) = a₀ · A_0(ε)`
exactly absorbs the regular-branch contribution. -/
lemma aperyConnectionResidual_pure_regular_shift (a₀ ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => yAperyZero a₀ (x - Number.aperyConifoldZ1Poly)) ε = 0 := by
  unfold aperyConnectionResidual
  simp only []
  have h_zero : yAperyZero a₀ ((Number.aperyConifoldZ1Poly : ℝ) -
      Number.aperyConifoldZ1Poly) = a₀ := by
    rw [sub_self]; exact yAperyZero_at_zero a₀
  have heq : (Number.aperyConifoldZ1Poly + (-ε)) -
      Number.aperyConifoldZ1Poly = -ε := by ring
  have h_neg_eps : yAperyZero a₀ ((Number.aperyConifoldZ1Poly + (-ε)) -
      Number.aperyConifoldZ1Poly) = a₀ * aperyBranchAmplitude_zero ε := by
    rw [heq]; exact yAperyZero_at_neg_eps ε a₀
  rw [h_zero, h_neg_eps]; ring

/-- **Residual of pure half branch.** When `f x := yAperyHalf a_half (x − z₁)`,
the residual extracts exactly `a_half · A_½(ε)` — the regular branch sees
nothing (since `yAperyHalf · 0 = 0`), and the corridor-right-endpoint
factorisation gives the singular-half amplitude. -/
lemma aperyConnectionResidual_pure_half_shift (a_half ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => yAperyHalf a_half (x - Number.aperyConifoldZ1Poly)) ε =
      a_half * aperyBranchAmplitude_half ε := by
  unfold aperyConnectionResidual
  simp only []
  have h_zero : yAperyHalf a_half ((Number.aperyConifoldZ1Poly : ℝ) -
      Number.aperyConifoldZ1Poly) = 0 := by
    rw [sub_self]; exact yAperyHalf_at_zero a_half
  have heq : (Number.aperyConifoldZ1Poly + (-ε)) -
      Number.aperyConifoldZ1Poly = -ε := by ring
  have h_neg_eps : yAperyHalf a_half ((Number.aperyConifoldZ1Poly + (-ε)) -
      Number.aperyConifoldZ1Poly) = a_half * aperyBranchAmplitude_half ε := by
    rw [heq]; exact yAperyHalf_at_neg_eps ε a_half
  rw [h_zero, h_neg_eps]; ring

/-- **Residual of pure one branch.** When `f x := yApery a₁ (x − z₁)`,
the residual extracts exactly `a₁ · V_1(ε)` — same logic as the half
branch. -/
lemma aperyConnectionResidual_pure_one_shift (a₁ ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => yApery a₁ (x - Number.aperyConifoldZ1Poly)) ε =
      a₁ * aperyBranchValue_one ε := by
  unfold aperyConnectionResidual
  simp only []
  have h_zero : yApery a₁ ((Number.aperyConifoldZ1Poly : ℝ) -
      Number.aperyConifoldZ1Poly) = 0 := by
    rw [sub_self]; exact yApery_at_zero a₁
  have heq : (Number.aperyConifoldZ1Poly + (-ε)) -
      Number.aperyConifoldZ1Poly = -ε := by ring
  have h_neg_eps : yApery a₁ ((Number.aperyConifoldZ1Poly + (-ε)) -
      Number.aperyConifoldZ1Poly) = a₁ * aperyBranchValue_one ε := by
    rw [heq]; exact yApery_at_neg_eps ε a₁
  rw [h_zero, h_neg_eps]; ring

/-- **Residual of the full Frobenius triple.** When `f x := aperyBranchTriple
a₀ a_half a₁ (x − z₁)` (the three-branch superposition shifted to the
original variable), the residual equals exactly the singular pair
`a_half · A_½(ε) + a₁ · V_1(ε)`. Direct corollary of the three
pure-branch residual atoms via additivity of the residual functional. -/
lemma aperyConnectionResidual_pure_triple_shift (a₀ a_half a₁ ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => aperyBranchTriple a₀ a_half a₁ (x - Number.aperyConifoldZ1Poly)) ε =
      a_half * aperyBranchAmplitude_half ε + a₁ * aperyBranchValue_one ε := by
  have hsplit : (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
      (x - Number.aperyConifoldZ1Poly)) =
      (fun x : ℝ => yAperyZero a₀ (x - Number.aperyConifoldZ1Poly) +
        yAperyHalf a_half (x - Number.aperyConifoldZ1Poly) +
        yApery a₁ (x - Number.aperyConifoldZ1Poly)) := by
    funext x; unfold aperyBranchTriple; rfl
  rw [hsplit]
  have hadd1 := aperyConnectionResidual_add
    (fun x => yAperyZero a₀ (x - Number.aperyConifoldZ1Poly) +
      yAperyHalf a_half (x - Number.aperyConifoldZ1Poly))
    (fun x => yApery a₁ (x - Number.aperyConifoldZ1Poly)) ε
  have hadd2 := aperyConnectionResidual_add
    (fun x => yAperyZero a₀ (x - Number.aperyConifoldZ1Poly))
    (fun x => yAperyHalf a_half (x - Number.aperyConifoldZ1Poly)) ε
  rw [hadd1, hadd2]
  rw [aperyConnectionResidual_pure_regular_shift,
      aperyConnectionResidual_pure_half_shift,
      aperyConnectionResidual_pure_one_shift]
  ring

/-- **Residual sup-bound.** If `f(z₁ − ε)` and `f(z₁)` are both bounded
in absolute value by `M`, then `|residual f ε| ≤ M · (1 + |A_0(ε)|)`.
A useful sup-norm-style envelope. -/
lemma aperyConnectionResidual_abs_le_sup
    {f : ℝ → ℝ} {ε M : ℝ}
    (h_left : |f (Number.aperyConifoldZ1Poly + (-ε))| ≤ M)
    (h_right : |f Number.aperyConifoldZ1Poly| ≤ M) :
    |aperyConnectionResidual f ε| ≤ M * (1 + |aperyBranchAmplitude_zero ε|) := by
  have h_main := aperyConnectionResidual_abs_le_raw f ε
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) h_right
  have hA_nn : 0 ≤ |aperyBranchAmplitude_zero ε| := abs_nonneg _
  have h_term2 :
      |f Number.aperyConifoldZ1Poly| * |aperyBranchAmplitude_zero ε| ≤
        M * |aperyBranchAmplitude_zero ε| :=
    mul_le_mul_of_nonneg_right h_right hA_nn
  have hsum : |f (Number.aperyConifoldZ1Poly + (-ε))| +
        |f Number.aperyConifoldZ1Poly| * |aperyBranchAmplitude_zero ε| ≤
      M + M * |aperyBranchAmplitude_zero ε| := by linarith [h_left, h_term2]
  have h_target : M + M * |aperyBranchAmplitude_zero ε| =
      M * (1 + |aperyBranchAmplitude_zero ε|) := by ring
  linarith [h_main, hsum, h_target.symm.le]

/-- **Residual as deviation from regular-branch shadow.** The residual
equals the difference between the actual value `f(z₁ − ε)` and the
ρ=0 branch evaluated with seed `f(z₁)` at the same corridor point:
`residual f ε = f(z₁ − ε) − yAperyZero(f(z₁), −ε)`. This recasts the
residual as "how much `f` deviates from the unique regular Frobenius
branch with the matching `t = 0` value". -/
lemma aperyConnectionResidual_eq_sub_yAperyZero (f : ℝ → ℝ) (ε : ℝ) :
    aperyConnectionResidual f ε =
      f (Number.aperyConifoldZ1Poly + (-ε)) -
      yAperyZero (f Number.aperyConifoldZ1Poly) (-ε) := by
  unfold aperyConnectionResidual
  rw [yAperyZero_at_neg_eps]

/-- **Singular-pair vanishing from two residual zeros.** Pure ℝ algebra:
if a candidate `(a_h, a₁)` produces vanishing residual at two distinct
ε values (`a_h·A_½(εᵢ) + a₁·V_1(εᵢ) = 0`, `i = 1, 2`) and the 2×2
determinant `Δ(ε₁, ε₂) ≠ 0`, then `a_h = a₁ = 0`. The Cramer cousin of
`unique_of_two_witnesses` at the residual level. -/
lemma aperyConnection_singular_pair_zero_of_residual_zero
    {a_half a₁ ε₁ ε₂ : ℝ}
    (h1 : a_half * aperyBranchAmplitude_half ε₁ + a₁ * aperyBranchValue_one ε₁ = 0)
    (h2 : a_half * aperyBranchAmplitude_half ε₂ + a₁ * aperyBranchValue_one ε₂ = 0)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a_half = 0 ∧ a₁ = 0 := by
  set Δ := aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ with hΔ
  have ha_h : a_half * Δ = 0 := by
    have h1' := h1
    have h2' := h2
    have hcalc : a_half * Δ =
        (a_half * aperyBranchAmplitude_half ε₁ + a₁ * aperyBranchValue_one ε₁) *
          aperyBranchValue_one ε₂ -
        (a_half * aperyBranchAmplitude_half ε₂ + a₁ * aperyBranchValue_one ε₂) *
          aperyBranchValue_one ε₁ := by simp [hΔ]; ring
    rw [hcalc, h1', h2']; ring
  have ha₁ : a₁ * Δ = 0 := by
    have hcalc : a₁ * Δ =
        -(a_half * aperyBranchAmplitude_half ε₁ + a₁ * aperyBranchValue_one ε₁) *
          aperyBranchAmplitude_half ε₂ +
        (a_half * aperyBranchAmplitude_half ε₂ + a₁ * aperyBranchValue_one ε₂) *
          aperyBranchAmplitude_half ε₁ := by simp [hΔ]; ring
    rw [hcalc, h1, h2]; ring
  refine ⟨?_, ?_⟩
  · rcases mul_eq_zero.mp ha_h with h | h
    · exact h
    · exact absurd h hdet
  · rcases mul_eq_zero.mp ha₁ with h | h
    · exact h
    · exact absurd h hdet

/-- **Cramer extraction for the singular pair from arbitrary residual data.**
Pure ℝ algebra: given the linear system
`a_h·A_½(εᵢ) + a₁·V_1(εᵢ) = rᵢ` (`i = 1, 2`) and `Δ(ε₁, ε₂) ≠ 0`, the
seeds are uniquely determined by Cramer's rule:
`a_h = (r₁·V_1(ε₂) − r₂·V_1(ε₁)) / Δ` and
`a₁ = (−r₁·A_½(ε₂) + r₂·A_½(ε₁)) / Δ`. -/
lemma aperyConnection_singular_pair_solve
    {a_half a₁ ε₁ ε₂ r₁ r₂ : ℝ}
    (h1 : a_half * aperyBranchAmplitude_half ε₁ + a₁ * aperyBranchValue_one ε₁ = r₁)
    (h2 : a_half * aperyBranchAmplitude_half ε₂ + a₁ * aperyBranchValue_one ε₂ = r₂)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a_half = (r₁ * aperyBranchValue_one ε₂ - r₂ * aperyBranchValue_one ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) ∧
      a₁ = (-(r₁ * aperyBranchAmplitude_half ε₂) +
            r₂ * aperyBranchAmplitude_half ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  set Δ := aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ with hΔ
  have ha_h_mul : a_half * Δ =
      r₁ * aperyBranchValue_one ε₂ - r₂ * aperyBranchValue_one ε₁ := by
    have hcalc : a_half * Δ =
        (a_half * aperyBranchAmplitude_half ε₁ + a₁ * aperyBranchValue_one ε₁) *
          aperyBranchValue_one ε₂ -
        (a_half * aperyBranchAmplitude_half ε₂ + a₁ * aperyBranchValue_one ε₂) *
          aperyBranchValue_one ε₁ := by simp [hΔ]; ring
    rw [hcalc, h1, h2]
  have ha₁_mul : a₁ * Δ =
      -(r₁ * aperyBranchAmplitude_half ε₂) + r₂ * aperyBranchAmplitude_half ε₁ := by
    have hcalc : a₁ * Δ =
        -(a_half * aperyBranchAmplitude_half ε₁ + a₁ * aperyBranchValue_one ε₁) *
          aperyBranchAmplitude_half ε₂ +
        (a_half * aperyBranchAmplitude_half ε₂ + a₁ * aperyBranchValue_one ε₂) *
          aperyBranchAmplitude_half ε₁ := by simp [hΔ]; ring
    rw [hcalc, h1, h2]; ring
  refine ⟨?_, ?_⟩
  · rw [eq_div_iff hdet]; exact ha_h_mul
  · rw [eq_div_iff hdet]; exact ha₁_mul

/-- **Triple recovery from residual data.** For `f x := aperyBranchTriple
a₀ a_half a₁ (x − z₁)` and any two ε values with `Δ(ε₁, ε₂) ≠ 0`, the
seeds are recovered by:
- `a₀ = f(z₁)` (regular seed = value at conifold).
- `a_half = (residual(ε₁)·V_1(ε₂) − residual(ε₂)·V_1(ε₁)) / Δ`.
- `a₁ = (−residual(ε₁)·A_½(ε₂) + residual(ε₂)·A_½(ε₁)) / Δ`.
Combines `pure_triple_shift` (residual = a_h·A_½ + a₁·V_1) with
`singular_pair_solve` (Cramer's rule). -/
lemma aperyConnection_triple_recover (a₀ a_half a₁ ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₀ = (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
            (x - Number.aperyConifoldZ1Poly)) Number.aperyConifoldZ1Poly ∧
    a_half =
      ((aperyConnectionResidual
          (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
            (x - Number.aperyConifoldZ1Poly)) ε₁) * aperyBranchValue_one ε₂ -
       (aperyConnectionResidual
          (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
            (x - Number.aperyConifoldZ1Poly)) ε₂) * aperyBranchValue_one ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) ∧
    a₁ =
      (-((aperyConnectionResidual
          (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
            (x - Number.aperyConifoldZ1Poly)) ε₁) * aperyBranchAmplitude_half ε₂) +
       (aperyConnectionResidual
          (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
            (x - Number.aperyConifoldZ1Poly)) ε₂) * aperyBranchAmplitude_half ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  have h_a₀ : a₀ = (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
            (x - Number.aperyConifoldZ1Poly)) Number.aperyConifoldZ1Poly := by
    change a₀ = aperyBranchTriple a₀ a_half a₁ (Number.aperyConifoldZ1Poly -
            Number.aperyConifoldZ1Poly)
    rw [sub_self]; rw [aperyBranchTriple_at_zero]
  have hres1 := (aperyConnectionResidual_pure_triple_shift a₀ a_half a₁ ε₁).symm
  have hres2 := (aperyConnectionResidual_pure_triple_shift a₀ a_half a₁ ε₂).symm
  have h_solve := aperyConnection_singular_pair_solve hres1 hres2 hdet
  exact ⟨h_a₀, h_solve.1, h_solve.2⟩

/-- **Residual is invariant under adding a regular branch.** Adding
`yAperyZero c (x − z₁)` to `f` does not change the residual, since the
regular branch contributes zero residual. Direct from
`aperyConnectionResidual_add` and `_pure_regular_shift`. -/
lemma aperyConnectionResidual_add_yAperyZero_shift
    (f : ℝ → ℝ) (c ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => f x + yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε =
      aperyConnectionResidual f ε := by
  rw [aperyConnectionResidual_add f
        (fun x : ℝ => yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε,
      aperyConnectionResidual_pure_regular_shift]
  ring

/-- **Residual is invariant under subtracting a regular branch.** -/
lemma aperyConnectionResidual_sub_yAperyZero_shift
    (f : ℝ → ℝ) (c ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => f x - yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε =
      aperyConnectionResidual f ε := by
  rw [aperyConnectionResidual_sub f
        (fun x : ℝ => yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε,
      aperyConnectionResidual_pure_regular_shift]
  ring

/-- **Residual transforms additively under singular ρ=1/2 branch
addition.** Adding `yAperyHalf b (x − z₁)` to `f` shifts the residual
by exactly `b · A_½(ε)`. -/
lemma aperyConnectionResidual_add_yAperyHalf_shift
    (f : ℝ → ℝ) (b ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => f x + yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε =
      aperyConnectionResidual f ε + b * aperyBranchAmplitude_half ε := by
  rw [aperyConnectionResidual_add f
        (fun x : ℝ => yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε,
      aperyConnectionResidual_pure_half_shift]

/-- **Residual transforms additively under singular ρ=1 branch
addition.** Adding `yApery c (x − z₁)` to `f` shifts the residual by
exactly `c · V_1(ε)`. -/
lemma aperyConnectionResidual_add_yApery_shift
    (f : ℝ → ℝ) (c ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => f x + yApery c (x - Number.aperyConifoldZ1Poly)) ε =
      aperyConnectionResidual f ε + c * aperyBranchValue_one ε := by
  rw [aperyConnectionResidual_add f
        (fun x : ℝ => yApery c (x - Number.aperyConifoldZ1Poly)) ε,
      aperyConnectionResidual_pure_one_shift]

/-- **Residual transforms under singular ρ=1/2 branch subtraction.**
Subtracting `yAperyHalf b (x − z₁)` from `f` shifts the residual by
exactly `−b · A_½(ε)`. -/
lemma aperyConnectionResidual_sub_yAperyHalf_shift
    (f : ℝ → ℝ) (b ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => f x - yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε =
      aperyConnectionResidual f ε - b * aperyBranchAmplitude_half ε := by
  rw [aperyConnectionResidual_sub f
        (fun x : ℝ => yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε,
      aperyConnectionResidual_pure_half_shift]

/-- **Residual transforms under singular ρ=1 branch subtraction.**
Subtracting `yApery c (x − z₁)` from `f` shifts the residual by
exactly `−c · V_1(ε)`. -/
lemma aperyConnectionResidual_sub_yApery_shift
    (f : ℝ → ℝ) (c ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => f x - yApery c (x - Number.aperyConifoldZ1Poly)) ε =
      aperyConnectionResidual f ε - c * aperyBranchValue_one ε := by
  rw [aperyConnectionResidual_sub f
        (fun x : ℝ => yApery c (x - Number.aperyConifoldZ1Poly)) ε,
      aperyConnectionResidual_pure_one_shift]

/-- **Predicate shift under regular-branch addition.** Adding
`yAperyZero c (x − z₁)` to `f` lifts the connection-coefficient
predicate, shifting only the regular seed `a₀ ↦ a₀ + c`. -/
lemma IsAperyConnectionCoeffsOn.add_yAperyZero_shift
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (c : ℝ) :
    IsAperyConnectionCoeffsOn (a₀ + c) a_half a₁
      (fun x : ℝ => f x + yAperyZero c (x - Number.aperyConifoldZ1Poly)) I := by
  have hpure : IsAperyConnectionCoeffsOn c 0 0
      (fun x : ℝ => yAperyZero c (x - Number.aperyConifoldZ1Poly)) I := by
    refine IsAperyConnectionCoeffsOn.of_pure_regular c _ I ?_
    intro t _
    simp [add_sub_cancel_left]
  have hsum := hf.add hpure
  simpa [add_zero] using hsum

/-- **Predicate shift under ρ=1/2 branch addition.** Adding
`yAperyHalf b (x − z₁)` to `f` shifts only the half-branch seed
`a_half ↦ a_half + b`. -/
lemma IsAperyConnectionCoeffsOn.add_yAperyHalf_shift
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (b : ℝ) :
    IsAperyConnectionCoeffsOn a₀ (a_half + b) a₁
      (fun x : ℝ => f x + yAperyHalf b (x - Number.aperyConifoldZ1Poly)) I := by
  have hpure : IsAperyConnectionCoeffsOn 0 b 0
      (fun x : ℝ => yAperyHalf b (x - Number.aperyConifoldZ1Poly)) I := by
    refine IsAperyConnectionCoeffsOn.of_pure_half b _ I ?_
    intro t _
    simp [add_sub_cancel_left]
  have hsum := hf.add hpure
  simpa [add_zero] using hsum

/-- **Predicate shift under ρ=1 branch addition.** Adding
`yApery c (x − z₁)` to `f` shifts only the one-branch seed
`a₁ ↦ a₁ + c`. -/
lemma IsAperyConnectionCoeffsOn.add_yApery_shift
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (c : ℝ) :
    IsAperyConnectionCoeffsOn a₀ a_half (a₁ + c)
      (fun x : ℝ => f x + yApery c (x - Number.aperyConifoldZ1Poly)) I := by
  have hpure : IsAperyConnectionCoeffsOn 0 0 c
      (fun x : ℝ => yApery c (x - Number.aperyConifoldZ1Poly)) I := by
    refine IsAperyConnectionCoeffsOn.of_pure_one c _ I ?_
    intro t _
    simp [add_sub_cancel_left]
  have hsum := hf.add hpure
  simpa [add_zero] using hsum

/-- **Predicate shift under regular-branch subtraction.** -/
lemma IsAperyConnectionCoeffsOn.sub_yAperyZero_shift
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (c : ℝ) :
    IsAperyConnectionCoeffsOn (a₀ - c) a_half a₁
      (fun x : ℝ => f x - yAperyZero c (x - Number.aperyConifoldZ1Poly)) I := by
  have hpure : IsAperyConnectionCoeffsOn c 0 0
      (fun x : ℝ => yAperyZero c (x - Number.aperyConifoldZ1Poly)) I := by
    refine IsAperyConnectionCoeffsOn.of_pure_regular c _ I ?_
    intro t _
    simp [add_sub_cancel_left]
  have hdiff := hf.sub hpure
  simpa [sub_zero] using hdiff

/-- **Predicate shift under ρ=1/2 branch subtraction.** -/
lemma IsAperyConnectionCoeffsOn.sub_yAperyHalf_shift
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (b : ℝ) :
    IsAperyConnectionCoeffsOn a₀ (a_half - b) a₁
      (fun x : ℝ => f x - yAperyHalf b (x - Number.aperyConifoldZ1Poly)) I := by
  have hpure : IsAperyConnectionCoeffsOn 0 b 0
      (fun x : ℝ => yAperyHalf b (x - Number.aperyConifoldZ1Poly)) I := by
    refine IsAperyConnectionCoeffsOn.of_pure_half b _ I ?_
    intro t _
    simp [add_sub_cancel_left]
  have hdiff := hf.sub hpure
  simpa [sub_zero] using hdiff

/-- **Predicate shift under ρ=1 branch subtraction.** -/
lemma IsAperyConnectionCoeffsOn.sub_yApery_shift
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I) (c : ℝ) :
    IsAperyConnectionCoeffsOn a₀ a_half (a₁ - c)
      (fun x : ℝ => f x - yApery c (x - Number.aperyConifoldZ1Poly)) I := by
  have hpure : IsAperyConnectionCoeffsOn 0 0 c
      (fun x : ℝ => yApery c (x - Number.aperyConifoldZ1Poly)) I := by
    refine IsAperyConnectionCoeffsOn.of_pure_one c _ I ?_
    intro t _
    simp [add_sub_cancel_left]
  have hdiff := hf.sub hpure
  simpa [sub_zero] using hdiff

/-- **Has-level closure under regular-branch addition.** -/
lemma HasAperyConnectionCoeffsOn.add_yAperyZero_shift
    {f : ℝ → ℝ} {I : Set ℝ} (hf : HasAperyConnectionCoeffsOn f I) (c : ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => f x + yAperyZero c (x - Number.aperyConifoldZ1Poly)) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  exact ⟨a₀ + c, a_half, a₁, hf.add_yAperyZero_shift c⟩

/-- **Has-level closure under ρ=1/2 branch addition.** -/
lemma HasAperyConnectionCoeffsOn.add_yAperyHalf_shift
    {f : ℝ → ℝ} {I : Set ℝ} (hf : HasAperyConnectionCoeffsOn f I) (b : ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => f x + yAperyHalf b (x - Number.aperyConifoldZ1Poly)) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  exact ⟨a₀, a_half + b, a₁, hf.add_yAperyHalf_shift b⟩

/-- **Has-level closure under ρ=1 branch addition.** -/
lemma HasAperyConnectionCoeffsOn.add_yApery_shift
    {f : ℝ → ℝ} {I : Set ℝ} (hf : HasAperyConnectionCoeffsOn f I) (c : ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => f x + yApery c (x - Number.aperyConifoldZ1Poly)) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  exact ⟨a₀, a_half, a₁ + c, hf.add_yApery_shift c⟩

/-- **Has-level closure under regular-branch subtraction.** -/
lemma HasAperyConnectionCoeffsOn.sub_yAperyZero_shift
    {f : ℝ → ℝ} {I : Set ℝ} (hf : HasAperyConnectionCoeffsOn f I) (c : ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => f x - yAperyZero c (x - Number.aperyConifoldZ1Poly)) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  exact ⟨a₀ - c, a_half, a₁, hf.sub_yAperyZero_shift c⟩

/-- **Has-level closure under ρ=1/2 branch subtraction.** -/
lemma HasAperyConnectionCoeffsOn.sub_yAperyHalf_shift
    {f : ℝ → ℝ} {I : Set ℝ} (hf : HasAperyConnectionCoeffsOn f I) (b : ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => f x - yAperyHalf b (x - Number.aperyConifoldZ1Poly)) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  exact ⟨a₀, a_half - b, a₁, hf.sub_yAperyHalf_shift b⟩

/-- **Has-level closure under ρ=1 branch subtraction.** -/
lemma HasAperyConnectionCoeffsOn.sub_yApery_shift
    {f : ℝ → ℝ} {I : Set ℝ} (hf : HasAperyConnectionCoeffsOn f I) (c : ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => f x - yApery c (x - Number.aperyConifoldZ1Poly)) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  exact ⟨a₀, a_half, a₁ - c, hf.sub_yApery_shift c⟩

/-- **Pure-triple shift constructor.** The literal shifted Frobenius
triple `fun x ↦ aperyBranchTriple b₀ b_h b₁ (x − z₁)` carries the
triple `(b₀, b_h, b₁)` on every set. Pointwise unfold via
`add_sub_cancel_left`. -/
lemma IsAperyConnectionCoeffsOn.of_pure_triple_shift
    (b₀ b_half b₁ : ℝ) (I : Set ℝ) :
    IsAperyConnectionCoeffsOn b₀ b_half b₁
      (fun x : ℝ => aperyBranchTriple b₀ b_half b₁
        (x - Number.aperyConifoldZ1Poly)) I := by
  intro t _
  simp [add_sub_cancel_left]

/-- **Predicate shift under full triple addition.** Cumulative version
of the three single-branch atoms: adding the literal shifted triple
shifts the seed coordinatewise. -/
lemma IsAperyConnectionCoeffsOn.add_aperyBranchTriple_shift
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (b₀ b_half b₁ : ℝ) :
    IsAperyConnectionCoeffsOn (a₀ + b₀) (a_half + b_half) (a₁ + b₁)
      (fun x : ℝ => f x + aperyBranchTriple b₀ b_half b₁
        (x - Number.aperyConifoldZ1Poly)) I :=
  hf.add (IsAperyConnectionCoeffsOn.of_pure_triple_shift b₀ b_half b₁ I)

/-- **Predicate shift under full triple subtraction.** -/
lemma IsAperyConnectionCoeffsOn.sub_aperyBranchTriple_shift
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (hf : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (b₀ b_half b₁ : ℝ) :
    IsAperyConnectionCoeffsOn (a₀ - b₀) (a_half - b_half) (a₁ - b₁)
      (fun x : ℝ => f x - aperyBranchTriple b₀ b_half b₁
        (x - Number.aperyConifoldZ1Poly)) I :=
  hf.sub (IsAperyConnectionCoeffsOn.of_pure_triple_shift b₀ b_half b₁ I)

/-- **Has-level closure under full triple addition.** -/
lemma HasAperyConnectionCoeffsOn.add_aperyBranchTriple_shift
    {f : ℝ → ℝ} {I : Set ℝ} (hf : HasAperyConnectionCoeffsOn f I)
    (b₀ b_half b₁ : ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => f x + aperyBranchTriple b₀ b_half b₁
        (x - Number.aperyConifoldZ1Poly)) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  exact ⟨a₀ + b₀, a_half + b_half, a₁ + b₁,
    hf.add_aperyBranchTriple_shift b₀ b_half b₁⟩

/-- **Has-level closure under full triple subtraction.** -/
lemma HasAperyConnectionCoeffsOn.sub_aperyBranchTriple_shift
    {f : ℝ → ℝ} {I : Set ℝ} (hf : HasAperyConnectionCoeffsOn f I)
    (b₀ b_half b₁ : ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => f x - aperyBranchTriple b₀ b_half b₁
        (x - Number.aperyConifoldZ1Poly)) I := by
  obtain ⟨a₀, a_half, a₁, hf⟩ := hf
  exact ⟨a₀ - b₀, a_half - b_half, a₁ - b₁,
    hf.sub_aperyBranchTriple_shift b₀ b_half b₁⟩

/-- **Existence: shifted regular Frobenius branch is representable.**
The literal `fun x ↦ yAperyZero c (x − z₁)` carries the triple
`(c, 0, 0)` on every set. -/
lemma HasAperyConnectionCoeffsOn.yAperyZero_shift (c : ℝ) (I : Set ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => yAperyZero c (x - Number.aperyConifoldZ1Poly)) I := by
  refine ⟨c, 0, 0, ?_⟩
  refine IsAperyConnectionCoeffsOn.of_pure_regular c _ I ?_
  intro t _
  simp [add_sub_cancel_left]

/-- **Existence: shifted ρ=1/2 singular Frobenius branch is
representable.** Carries `(0, b, 0)`. -/
lemma HasAperyConnectionCoeffsOn.yAperyHalf_shift (b : ℝ) (I : Set ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => yAperyHalf b (x - Number.aperyConifoldZ1Poly)) I := by
  refine ⟨0, b, 0, ?_⟩
  refine IsAperyConnectionCoeffsOn.of_pure_half b _ I ?_
  intro t _
  simp [add_sub_cancel_left]

/-- **Existence: shifted ρ=1 singular Frobenius branch is
representable.** Carries `(0, 0, c)`. -/
lemma HasAperyConnectionCoeffsOn.yApery_shift (c : ℝ) (I : Set ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => yApery c (x - Number.aperyConifoldZ1Poly)) I := by
  refine ⟨0, 0, c, ?_⟩
  refine IsAperyConnectionCoeffsOn.of_pure_one c _ I ?_
  intro t _
  simp [add_sub_cancel_left]

/-- **Existence: shifted full triple is representable.** Cumulative
form — the literal `fun x ↦ aperyBranchTriple b₀ b_h b₁ (x − z₁)`
carries `(b₀, b_h, b₁)` on every set. -/
lemma HasAperyConnectionCoeffsOn.aperyBranchTriple_shift
    (b₀ b_half b₁ : ℝ) (I : Set ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ => aperyBranchTriple b₀ b_half b₁
        (x - Number.aperyConifoldZ1Poly)) I :=
  ⟨b₀, b_half, b₁,
    IsAperyConnectionCoeffsOn.of_pure_triple_shift b₀ b_half b₁ I⟩

/-- **Residual of a scaled shifted triple.** Direct composition of
`aperyConnectionResidual_smul` with `aperyConnectionResidual_pure_triple_shift`.
For the literal `c · aperyBranchTriple a₀ a_h a₁ (x − z₁)`, the residual
is `c · (a_h · A_½(ε) + a₁ · V_1(ε))`. -/
lemma aperyConnectionResidual_smul_pure_triple_shift
    (c a₀ a_half a₁ ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => c * aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)) ε =
      c * (a_half * aperyBranchAmplitude_half ε +
        a₁ * aperyBranchValue_one ε) := by
  rw [aperyConnectionResidual_smul c
        (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)) ε,
      aperyConnectionResidual_pure_triple_shift]

/-- **Residual of the negated shifted triple.** -/
lemma aperyConnectionResidual_neg_pure_triple_shift
    (a₀ a_half a₁ ε : ℝ) :
    aperyConnectionResidual
        (fun x : ℝ => -(aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly))) ε =
      -(a_half * aperyBranchAmplitude_half ε +
        a₁ * aperyBranchValue_one ε) := by
  rw [aperyConnectionResidual_neg
        (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)) ε,
      aperyConnectionResidual_pure_triple_shift]

/-- **Definitional decomposition of the branch triple.** Direct unfold:
`aperyBranchTriple a₀ a_h a₁ t = yAperyZero a₀ t + yAperyHalf a_h t + yApery a₁ t`.
Useful as a rewrite when working with the literal three-summand form. -/
lemma aperyBranchTriple_decomp (a₀ a_half a₁ t : ℝ) :
    aperyBranchTriple a₀ a_half a₁ t =
      yAperyZero a₀ t + yAperyHalf a_half t + yApery a₁ t := rfl

/-- **Pointwise equality of the shifted triple with the literal
three-summand form.** Direct corollary of `aperyBranchTriple_decomp`
applied at `t = x - z₁`. -/
lemma aperyBranchTriple_shift_eq_sum
    (a₀ a_half a₁ x : ℝ) :
    aperyBranchTriple a₀ a_half a₁ (x - Number.aperyConifoldZ1Poly) =
      yAperyZero a₀ (x - Number.aperyConifoldZ1Poly) +
      yAperyHalf a_half (x - Number.aperyConifoldZ1Poly) +
      yApery a₁ (x - Number.aperyConifoldZ1Poly) := rfl

/-- **Existence: the explicit three-summand shifted Frobenius
combination is representable.** Has-level lift of
`HasAperyConnectionCoeffsOn.aperyBranchTriple_shift` via the
definitional decomposition; useful when downstream code prefers the
explicit summand form. -/
lemma HasAperyConnectionCoeffsOn.three_branch_shift_sum
    (a₀ a_half a₁ : ℝ) (I : Set ℝ) :
    HasAperyConnectionCoeffsOn
      (fun x : ℝ =>
        yAperyZero a₀ (x - Number.aperyConifoldZ1Poly) +
        yAperyHalf a_half (x - Number.aperyConifoldZ1Poly) +
        yApery a₁ (x - Number.aperyConifoldZ1Poly)) I :=
  HasAperyConnectionCoeffsOn.aperyBranchTriple_shift a₀ a_half a₁ I

/-- **Algebraic seed-injectivity at three witness points.** Pure
real-algebra atom: if two seed triples agree on `aperyBranchTriple` at
`t ∈ {0, −ε₁, −ε₂}` and the singular bracket determinant is nonzero,
the seed triples coincide. Direct combination of
`IsAperyConnectionCoeffsOn.of_pure_triple_shift` (left realiser),
construction of the right realiser via the three pointwise equalities,
and `triple_eq_of_two_witnesses`. -/
lemma aperyBranchTriple_seeds_eq_of_three_witnesses
    (a₀ a_half a₁ b₀ b_half b₁ : ℝ)
    {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0)
    (h_zero : aperyBranchTriple a₀ a_half a₁ 0 =
              aperyBranchTriple b₀ b_half b₁ 0)
    (h_e1 : aperyBranchTriple a₀ a_half a₁ (-ε₁) =
            aperyBranchTriple b₀ b_half b₁ (-ε₁))
    (h_e2 : aperyBranchTriple a₀ a_half a₁ (-ε₂) =
            aperyBranchTriple b₀ b_half b₁ (-ε₂)) :
    (a₀, a_half, a₁) = (b₀, b_half, b₁) := by
  let I : Set ℝ := ({(0 : ℝ), -ε₁, -ε₂} : Set ℝ)
  let f : ℝ → ℝ := fun x =>
    aperyBranchTriple a₀ a_half a₁ (x - Number.aperyConifoldZ1Poly)
  have ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I :=
    IsAperyConnectionCoeffsOn.of_pure_triple_shift a₀ a_half a₁ I
  have hb : IsAperyConnectionCoeffsOn b₀ b_half b₁ f I := by
    intro t ht
    have hf : f (Number.aperyConifoldZ1Poly + t) =
        aperyBranchTriple a₀ a_half a₁ t := by
      simp only [f]
      rw [add_sub_cancel_left]
    rcases ht with rfl | rfl | rfl
    · rw [hf]; exact h_zero
    · rw [hf]; exact h_e1
    · rw [hf]; exact h_e2
  have h0_in : (0 : ℝ) ∈ I := by simp [I]
  have hε₁_in : (-ε₁) ∈ I := by simp [I]
  have hε₂_in : (-ε₂) ∈ I := by simp [I]
  exact ha.triple_eq_of_two_witnesses hb h0_in hε₁_in hε₂_in hdet

/-- **Algebraic seed-vanishing at three witness points.** Specialisation
of `aperyBranchTriple_seeds_eq_of_three_witnesses` to `(b₀, b_h, b₁) = 0`:
if `aperyBranchTriple a₀ a_h a₁` vanishes at `t ∈ {0, −ε₁, −ε₂}` and the
singular bracket is non-degenerate, all three seeds are zero. -/
lemma aperyBranchTriple_seeds_zero_of_three_point_vanish
    (a₀ a_half a₁ : ℝ)
    {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0)
    (h_zero : aperyBranchTriple a₀ a_half a₁ 0 = 0)
    (h_e1 : aperyBranchTriple a₀ a_half a₁ (-ε₁) = 0)
    (h_e2 : aperyBranchTriple a₀ a_half a₁ (-ε₂) = 0) :
    a₀ = 0 ∧ a_half = 0 ∧ a₁ = 0 := by
  have heq : (a₀, a_half, a₁) = ((0 : ℝ), (0 : ℝ), (0 : ℝ)) := by
    refine aperyBranchTriple_seeds_eq_of_three_witnesses
      a₀ a_half a₁ 0 0 0 hdet ?_ ?_ ?_
    · rw [aperyBranchTriple_zero]; exact h_zero
    · rw [aperyBranchTriple_zero]; exact h_e1
    · rw [aperyBranchTriple_zero]; exact h_e2
  simp only [Prod.mk.injEq] at heq
  exact ⟨heq.1, heq.2.1, heq.2.2⟩

/-- **Iff version of the three-point seed-vanishing test.** Captures
the equivalence in both directions: if the singular bracket is
non-degenerate, vanishing at three witness points is equivalent to all
three seeds being zero. -/
lemma aperyBranchTriple_seeds_zero_iff_three_point_vanish
    (a₀ a_half a₁ : ℝ)
    {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    (aperyBranchTriple a₀ a_half a₁ 0 = 0 ∧
       aperyBranchTriple a₀ a_half a₁ (-ε₁) = 0 ∧
       aperyBranchTriple a₀ a_half a₁ (-ε₂) = 0) ↔
      (a₀ = 0 ∧ a_half = 0 ∧ a₁ = 0) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact aperyBranchTriple_seeds_zero_of_three_point_vanish
      a₀ a_half a₁ hdet h0 h1 h2
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> exact aperyBranchTriple_zero _

/-- **Iff version of three-point seed agreement.** Under non-degenerate
singular bracket, agreement of two `aperyBranchTriple` evaluations at
the three witness points is equivalent to seed-triple equality. -/
lemma aperyBranchTriple_seeds_eq_iff_three_point_agreement
    (a₀ a_half a₁ b₀ b_half b₁ : ℝ)
    {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    (aperyBranchTriple a₀ a_half a₁ 0 =
        aperyBranchTriple b₀ b_half b₁ 0 ∧
     aperyBranchTriple a₀ a_half a₁ (-ε₁) =
        aperyBranchTriple b₀ b_half b₁ (-ε₁) ∧
     aperyBranchTriple a₀ a_half a₁ (-ε₂) =
        aperyBranchTriple b₀ b_half b₁ (-ε₂)) ↔
      (a₀, a_half, a₁) = (b₀, b_half, b₁) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact aperyBranchTriple_seeds_eq_of_three_witnesses
      a₀ a_half a₁ b₀ b_half b₁ hdet h0 h1 h2
  · rintro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩

/-- **Pointwise function-level equivalence.** Under non-degenerate
singular bracket, two `aperyBranchTriple` functions are pointwise equal
iff their seed triples coincide. The forward direction uses three
witness points; the reverse is `rfl` (definitional from seed equality). -/
lemma aperyBranchTriple_funeq_iff_seeds_eq
    (a₀ a_half a₁ b₀ b_half b₁ : ℝ)
    {ε₁ ε₂ : ℝ}
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    (∀ t : ℝ,
        aperyBranchTriple a₀ a_half a₁ t = aperyBranchTriple b₀ b_half b₁ t)
      ↔ (a₀, a_half, a₁) = (b₀, b_half, b₁) := by
  constructor
  · intro h
    exact aperyBranchTriple_seeds_eq_of_three_witnesses
      a₀ a_half a₁ b₀ b_half b₁ hdet (h 0) (h (-ε₁)) (h (-ε₂))
  · rintro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro _; rfl

/-- **Finset additivity over seed triples.** For a finite family of
seed triples indexed by a `Finset`, the branch evaluation of the summed
seeds equals the summed evaluations. Direct induction on the finset
using `aperyBranchTriple_add_seeds`. -/
lemma aperyBranchTriple_finset_sum {α : Type*}
    (s : Finset α) (c₀ c_half c₁ : α → ℝ) (t : ℝ) :
    aperyBranchTriple (∑ i ∈ s, c₀ i) (∑ i ∈ s, c_half i)
        (∑ i ∈ s, c₁ i) t =
      ∑ i ∈ s, aperyBranchTriple (c₀ i) (c_half i) (c₁ i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact aperyBranchTriple_zero t
  | @insert a s' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
          Finset.sum_insert ha, aperyBranchTriple_add_seeds, ih]

/-- **Predicate closure under Finset summation.** If a finite family of
functions `f i` each carries a connection-coefficient triple
`(a₀ i, a_h i, a₁ i)` on a common domain `I`, then the pointwise sum
function carries the seed sum. Direct Finset induction on `.add` plus
zero base case. -/
lemma IsAperyConnectionCoeffsOn.finset_sum {α : Type*}
    {f : α → ℝ → ℝ} {a₀ a_half a₁ : α → ℝ} {I : Set ℝ}
    (s : Finset α)
    (h : ∀ i ∈ s, IsAperyConnectionCoeffsOn (a₀ i) (a_half i) (a₁ i) (f i) I) :
    IsAperyConnectionCoeffsOn
      (∑ i ∈ s, a₀ i) (∑ i ∈ s, a_half i) (∑ i ∈ s, a₁ i)
      (fun z => ∑ i ∈ s, f i z) I := by
  intro t ht
  rw [aperyBranchTriple_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact h i hi t ht

/-- **Has-level closure under Finset summation.** Existential
counterpart: a finite sum of representable functions is representable. -/
lemma HasAperyConnectionCoeffsOn.finset_sum {α : Type*}
    {f : α → ℝ → ℝ} {I : Set ℝ}
    (s : Finset α)
    (h : ∀ i ∈ s, HasAperyConnectionCoeffsOn (f i) I) :
    HasAperyConnectionCoeffsOn (fun z => ∑ i ∈ s, f i z) I := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact HasAperyConnectionCoeffsOn.zero I
  | @insert a s' ha ih =>
      have hf : HasAperyConnectionCoeffsOn (f a) I :=
        h a (Finset.mem_insert.mpr (Or.inl rfl))
      have hrest : ∀ i ∈ s', HasAperyConnectionCoeffsOn (f i) I :=
        fun i hi => h i (Finset.mem_insert.mpr (Or.inr hi))
      have ih' := ih hrest
      have hsum : (fun z => ∑ i ∈ insert a s', f i z) =
          (fun z => f a z + ∑ i ∈ s', f i z) := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hsum]
      exact hf.add ih'

/-- **Residual additivity over a Finset of summands.** The connection
residual is linear, so a Finset-sum of functions has its residual equal
to the Finset-sum of individual residuals. Direct induction using
`aperyConnectionResidual_add`. -/
lemma aperyConnectionResidual_finset_sum {α : Type*}
    (s : Finset α) (f : α → ℝ → ℝ) (ε : ℝ) :
    aperyConnectionResidual (fun z => ∑ i ∈ s, f i z) ε =
      ∑ i ∈ s, aperyConnectionResidual (f i) ε := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact aperyConnectionResidual_zero_fn ε
  | @insert a s' ha ih =>
      have hsum : (fun z => ∑ i ∈ insert a s', f i z) =
          (fun z => f a z + ∑ i ∈ s', f i z) := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hsum, aperyConnectionResidual_add, ih, Finset.sum_insert ha]

/-- **Pointwise residual congruence.** The residual of `f` at `ε` depends
only on `f` evaluated at the two points `z₁` and `z₁ − ε`. -/
lemma aperyConnectionResidual_congr_pt {f g : ℝ → ℝ} {ε : ℝ}
    (h0 : f Number.aperyConifoldZ1Poly = g Number.aperyConifoldZ1Poly)
    (h1 : f (Number.aperyConifoldZ1Poly + (-ε)) =
          g (Number.aperyConifoldZ1Poly + (-ε))) :
    aperyConnectionResidual f ε = aperyConnectionResidual g ε := by
  unfold aperyConnectionResidual
  rw [h0, h1]

/-- **Cramer recovery from `IsAperyConnectionCoeffsOn` data.** If
`(a₀, a_half, a₁)` represents `f` on `I`, and `0, −ε₁, −ε₂ ∈ I` with
non-degenerate Δ, then the seeds are recovered explicitly from `f`'s
values at `z₁` and from the residual at `ε₁, ε₂`:
- `a₀ = f(z₁)`,
- `a_half = (residual(ε₁)·V_1(ε₂) − residual(ε₂)·V_1(ε₁)) / Δ`,
- `a₁ = (−residual(ε₁)·A_½(ε₂) + residual(ε₂)·A_½(ε₁)) / Δ`.
This generalizes `aperyConnection_triple_recover` from the canonical
shifted-triple function to arbitrary `f` representable on `I`. -/
lemma IsAperyConnectionCoeffsOn.cramer_recover
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₀ = f Number.aperyConifoldZ1Poly ∧
    a_half =
      (aperyConnectionResidual f ε₁ * aperyBranchValue_one ε₂ -
        aperyConnectionResidual f ε₂ * aperyBranchValue_one ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) ∧
    a₁ =
      (-(aperyConnectionResidual f ε₁ * aperyBranchAmplitude_half ε₂) +
        aperyConnectionResidual f ε₂ * aperyBranchAmplitude_half ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) := by
  have hf0 : f Number.aperyConifoldZ1Poly = a₀ := by
    have hp := ha 0 h0
    rw [add_zero, aperyBranchTriple_at_zero] at hp
    exact hp
  have h_a₀ : a₀ = f Number.aperyConifoldZ1Poly := hf0.symm
  have hres_eq : ∀ ε, (-ε) ∈ I →
      aperyConnectionResidual f ε =
        a_half * aperyBranchAmplitude_half ε +
          a₁ * aperyBranchValue_one ε := by
    intro ε hε
    have h_pure := aperyConnectionResidual_pure_triple_shift a₀ a_half a₁ ε
    have h_congr : aperyConnectionResidual f ε =
        aperyConnectionResidual
          (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
            (x - Number.aperyConifoldZ1Poly)) ε := by
      apply aperyConnectionResidual_congr_pt
      · rw [hf0]
        show a₀ = aperyBranchTriple a₀ a_half a₁
          (Number.aperyConifoldZ1Poly - Number.aperyConifoldZ1Poly)
        rw [sub_self, aperyBranchTriple_at_zero]
      · rw [ha (-ε) hε]
        show aperyBranchTriple a₀ a_half a₁ (-ε) =
          aperyBranchTriple a₀ a_half a₁
            (Number.aperyConifoldZ1Poly + (-ε) - Number.aperyConifoldZ1Poly)
        congr 1; ring
    rw [h_congr, h_pure]
  have h1 := (hres_eq ε₁ hε₁).symm
  have h2 := (hres_eq ε₂ hε₂).symm
  have h_solve := aperyConnection_singular_pair_solve h1 h2 hdet
  exact ⟨h_a₀, h_solve.1, h_solve.2⟩

/-- **Has-level Cramer recovery.** Given representability of `f` on `I`,
the explicit Cramer formulas in terms of `f`'s value at `z₁` and the
residuals at `ε₁, ε₂` form a valid witness — promoting the abstract
`HasAperyConnectionCoeffsOn` to a concrete `IsAperyConnectionCoeffsOn`
with the unique seeds laid bare. Combines `existsUnique_witness` (any
witness is unique) with `IsAperyConnectionCoeffsOn.cramer_recover`. -/
lemma HasAperyConnectionCoeffsOn.cramer_recover
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    IsAperyConnectionCoeffsOn
      (f Number.aperyConifoldZ1Poly)
      ((aperyConnectionResidual f ε₁ * aperyBranchValue_one ε₂ -
         aperyConnectionResidual f ε₂ * aperyBranchValue_one ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁))
      ((-(aperyConnectionResidual f ε₁ * aperyBranchAmplitude_half ε₂) +
         aperyConnectionResidual f ε₂ * aperyBranchAmplitude_half ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁))
      f I := by
  obtain ⟨a₀, a_half, a₁, ha⟩ := h
  obtain ⟨h_a₀, h_a_h, h_a₁⟩ := ha.cramer_recover h0 hε₁ hε₂ hdet
  rw [← h_a₀, ← h_a_h, ← h_a₁]
  exact ha

/-- **`a_half` projection from Cramer recovery.** Pure projection of the
second component, factored out so downstream callers can request only the
half-branch coefficient. -/
lemma IsAperyConnectionCoeffsOn.a_half_residual_form
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a_half =
      (aperyConnectionResidual f ε₁ * aperyBranchValue_one ε₂ -
        aperyConnectionResidual f ε₂ * aperyBranchValue_one ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) :=
  (ha.cramer_recover h0 hε₁ hε₂ hdet).2.1

/-- **`a₁` projection from Cramer recovery.** Companion projection for
the regular-irregular blend's third coefficient. -/
lemma IsAperyConnectionCoeffsOn.a_one_residual_form
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₁ =
      (-(aperyConnectionResidual f ε₁ * aperyBranchAmplitude_half ε₂) +
        aperyConnectionResidual f ε₂ * aperyBranchAmplitude_half ε₁) /
        (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁) :=
  (ha.cramer_recover h0 hε₁ hε₂ hdet).2.2

/-- **Extracted regular seed.** The first connection coefficient is just
the value of `f` at the conifold point. No probe data needed. -/
noncomputable def aperyExtractRegular (f : ℝ → ℝ) : ℝ :=
  f Number.aperyConifoldZ1Poly

/-- **Extracted half-branch seed.** Cramer's rule for the second
component, parameterised by two probe offsets `ε₁, ε₂`. Well-defined as
a real number whenever the determinant is nonzero, but stated as a pure
expression so the result type is `ℝ` (not `Option ℝ`). -/
noncomputable def aperyExtractHalf (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) : ℝ :=
  (aperyConnectionResidual f ε₁ * aperyBranchValue_one ε₂ -
    aperyConnectionResidual f ε₂ * aperyBranchValue_one ε₁) /
    (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
      aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁)

/-- **Extracted one-branch seed.** Cramer's rule for the third
component, parameterised by two probe offsets `ε₁, ε₂`. -/
noncomputable def aperyExtractOne (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) : ℝ :=
  (-(aperyConnectionResidual f ε₁ * aperyBranchAmplitude_half ε₂) +
    aperyConnectionResidual f ε₂ * aperyBranchAmplitude_half ε₁) /
    (aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
      aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁)

/-- **Has-level extract = witness.** Under representability and a
non-degenerate Δ, the named extraction functions form a valid witness.
This is the definitional repackaging of `cramer_recover` into the
`aperyExtract{Regular,Half,One}` interface, giving downstream code
stable named projections. -/
lemma HasAperyConnectionCoeffsOn.is_extract
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    IsAperyConnectionCoeffsOn (aperyExtractRegular f)
      (aperyExtractHalf f ε₁ ε₂) (aperyExtractOne f ε₁ ε₂) f I := by
  unfold aperyExtractRegular aperyExtractHalf aperyExtractOne
  exact h.cramer_recover h0 hε₁ hε₂ hdet

/-- **Witness equals extract under Has.** Any concrete witness's
coordinates equal the named extraction values. Lifts the universal Cramer
formula to the named interface. -/
lemma IsAperyConnectionCoeffsOn.eq_extract
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₀ = aperyExtractRegular f ∧
    a_half = aperyExtractHalf f ε₁ ε₂ ∧
    a₁ = aperyExtractOne f ε₁ ε₂ := by
  unfold aperyExtractRegular aperyExtractHalf aperyExtractOne
  exact ha.cramer_recover h0 hε₁ hε₂ hdet

/-- **Extract regular: zero on zero.** -/
@[simp] lemma aperyExtractRegular_zero :
    aperyExtractRegular (fun _ : ℝ => (0 : ℝ)) = 0 := rfl

/-- **Extract regular: additivity.** -/
lemma aperyExtractRegular_add (f g : ℝ → ℝ) :
    aperyExtractRegular (fun x => f x + g x) =
      aperyExtractRegular f + aperyExtractRegular g := rfl

/-- **Extract regular: scalar multiplication.** -/
lemma aperyExtractRegular_smul (c : ℝ) (f : ℝ → ℝ) :
    aperyExtractRegular (fun x => c * f x) = c * aperyExtractRegular f := rfl

/-- **Extract regular: negation.** -/
lemma aperyExtractRegular_neg (f : ℝ → ℝ) :
    aperyExtractRegular (fun x => -(f x)) = -(aperyExtractRegular f) := rfl

/-- **Extract regular: subtraction.** -/
lemma aperyExtractRegular_sub (f g : ℝ → ℝ) :
    aperyExtractRegular (fun x => f x - g x) =
      aperyExtractRegular f - aperyExtractRegular g := rfl

/-- **Extract half: zero on zero.** -/
@[simp] lemma aperyExtractHalf_zero (ε₁ ε₂ : ℝ) :
    aperyExtractHalf (fun _ : ℝ => (0 : ℝ)) ε₁ ε₂ = 0 := by
  unfold aperyExtractHalf
  rw [aperyConnectionResidual_zero_fn, aperyConnectionResidual_zero_fn]
  ring

/-- **Extract half: additivity.** Linearity in `f` of the numerator
combined with division by a fixed denominator. -/
lemma aperyExtractHalf_add (f g : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractHalf (fun x => f x + g x) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ + aperyExtractHalf g ε₁ ε₂ := by
  unfold aperyExtractHalf
  rw [aperyConnectionResidual_add, aperyConnectionResidual_add]
  ring

/-- **Extract half: scalar multiplication.** -/
lemma aperyExtractHalf_smul (c : ℝ) (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractHalf (fun x => c * f x) ε₁ ε₂ =
      c * aperyExtractHalf f ε₁ ε₂ := by
  unfold aperyExtractHalf
  rw [aperyConnectionResidual_smul, aperyConnectionResidual_smul]
  ring

/-- **Extract half: negation.** -/
lemma aperyExtractHalf_neg (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractHalf (fun x => -(f x)) ε₁ ε₂ =
      -(aperyExtractHalf f ε₁ ε₂) := by
  unfold aperyExtractHalf
  rw [aperyConnectionResidual_neg, aperyConnectionResidual_neg]
  ring

/-- **Extract half: subtraction.** -/
lemma aperyExtractHalf_sub (f g : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractHalf (fun x => f x - g x) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ - aperyExtractHalf g ε₁ ε₂ := by
  unfold aperyExtractHalf
  rw [aperyConnectionResidual_sub, aperyConnectionResidual_sub]
  ring

/-- **Extract one: zero on zero.** -/
@[simp] lemma aperyExtractOne_zero (ε₁ ε₂ : ℝ) :
    aperyExtractOne (fun _ : ℝ => (0 : ℝ)) ε₁ ε₂ = 0 := by
  unfold aperyExtractOne
  rw [aperyConnectionResidual_zero_fn, aperyConnectionResidual_zero_fn]
  ring

/-- **Extract one: additivity.** -/
lemma aperyExtractOne_add (f g : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractOne (fun x => f x + g x) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ + aperyExtractOne g ε₁ ε₂ := by
  unfold aperyExtractOne
  rw [aperyConnectionResidual_add, aperyConnectionResidual_add]
  ring

/-- **Extract one: scalar multiplication.** -/
lemma aperyExtractOne_smul (c : ℝ) (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractOne (fun x => c * f x) ε₁ ε₂ =
      c * aperyExtractOne f ε₁ ε₂ := by
  unfold aperyExtractOne
  rw [aperyConnectionResidual_smul, aperyConnectionResidual_smul]
  ring

/-- **Extract one: negation.** -/
lemma aperyExtractOne_neg (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractOne (fun x => -(f x)) ε₁ ε₂ =
      -(aperyExtractOne f ε₁ ε₂) := by
  unfold aperyExtractOne
  rw [aperyConnectionResidual_neg, aperyConnectionResidual_neg]
  ring

/-- **Extract one: subtraction.** -/
lemma aperyExtractOne_sub (f g : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractOne (fun x => f x - g x) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ - aperyExtractOne g ε₁ ε₂ := by
  unfold aperyExtractOne
  rw [aperyConnectionResidual_sub, aperyConnectionResidual_sub]
  ring

/-! ### Extract values on pure shifted branches

The following nine atoms compute `aperyExtract{Regular,Half,One}` on the
three pure shifted branches. Diagonal entries (regular→regular,
half→half, one→one) recover the seed; off-diagonal entries vanish.
The diagonal Half→Half and One→One cases require the non-degenerate
Cramer determinant; all other cases are unconditional. -/

@[simp] lemma aperyExtractRegular_pure_regular_shift (c : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => yAperyZero c (x - Number.aperyConifoldZ1Poly)) = c := by
  change yAperyZero c (Number.aperyConifoldZ1Poly - Number.aperyConifoldZ1Poly) = c
  rw [sub_self, yAperyZero_at_zero]

@[simp] lemma aperyExtractRegular_pure_half_shift (b : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => yAperyHalf b (x - Number.aperyConifoldZ1Poly)) = 0 := by
  change yAperyHalf b (Number.aperyConifoldZ1Poly - Number.aperyConifoldZ1Poly) = 0
  rw [sub_self, yAperyHalf_at_zero]

@[simp] lemma aperyExtractRegular_pure_one_shift (a : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => yApery a (x - Number.aperyConifoldZ1Poly)) = 0 := by
  change yApery a (Number.aperyConifoldZ1Poly - Number.aperyConifoldZ1Poly) = 0
  rw [sub_self, yApery_at_zero]

@[simp] lemma aperyExtractHalf_pure_regular_shift (c ε₁ ε₂ : ℝ) :
    aperyExtractHalf
        (fun x : ℝ => yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ = 0 := by
  unfold aperyExtractHalf
  rw [aperyConnectionResidual_pure_regular_shift,
      aperyConnectionResidual_pure_regular_shift]
  ring

lemma aperyExtractHalf_pure_half_shift (b ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractHalf
        (fun x : ℝ => yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ = b := by
  unfold aperyExtractHalf
  rw [aperyConnectionResidual_pure_half_shift,
      aperyConnectionResidual_pure_half_shift]
  rw [div_eq_iff hdet]
  ring

@[simp] lemma aperyExtractHalf_pure_one_shift (a ε₁ ε₂ : ℝ) :
    aperyExtractHalf
        (fun x : ℝ => yApery a (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ = 0 := by
  unfold aperyExtractHalf
  rw [aperyConnectionResidual_pure_one_shift,
      aperyConnectionResidual_pure_one_shift]
  rw [show a * aperyBranchValue_one ε₁ * aperyBranchValue_one ε₂ -
          a * aperyBranchValue_one ε₂ * aperyBranchValue_one ε₁ = 0 from by ring]
  exact zero_div _

@[simp] lemma aperyExtractOne_pure_regular_shift (c ε₁ ε₂ : ℝ) :
    aperyExtractOne
        (fun x : ℝ => yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ = 0 := by
  unfold aperyExtractOne
  rw [aperyConnectionResidual_pure_regular_shift,
      aperyConnectionResidual_pure_regular_shift]
  ring

@[simp] lemma aperyExtractOne_pure_half_shift (b ε₁ ε₂ : ℝ) :
    aperyExtractOne
        (fun x : ℝ => yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ = 0 := by
  unfold aperyExtractOne
  rw [aperyConnectionResidual_pure_half_shift,
      aperyConnectionResidual_pure_half_shift]
  rw [show -(b * aperyBranchAmplitude_half ε₁ * aperyBranchAmplitude_half ε₂) +
          b * aperyBranchAmplitude_half ε₂ * aperyBranchAmplitude_half ε₁ = 0 from by ring]
  exact zero_div _

lemma aperyExtractOne_pure_one_shift (a ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractOne
        (fun x : ℝ => yApery a (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ = a := by
  unfold aperyExtractOne
  rw [aperyConnectionResidual_pure_one_shift,
      aperyConnectionResidual_pure_one_shift]
  rw [div_eq_iff hdet]
  ring

/-! ### Extract on the full `aperyBranchTriple` shifted form

These three atoms compose the linearity of `aperyExtract*` with the
diagonal/off-diagonal pure-branch values to recover all three seeds
from the canonical shifted-triple function. They are the workhorse
identities for downstream Cramer arguments: any function that *is* the
canonical shifted triple has its seeds visible by direct extraction. -/

@[simp] lemma aperyExtractRegular_pure_triple_shift (a₀ a_half a₁ : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)) = a₀ := by
  change aperyBranchTriple a₀ a_half a₁
      (Number.aperyConifoldZ1Poly - Number.aperyConifoldZ1Poly) = a₀
  rw [sub_self, aperyBranchTriple_at_zero]

lemma aperyExtractHalf_pure_triple_shift (a₀ a_half a₁ ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractHalf
        (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ = a_half := by
  have hcan := IsAperyConnectionCoeffsOn.canonical a₀ a_half a₁ (Set.univ : Set ℝ)
  exact ((hcan.eq_extract (Set.mem_univ _) (Set.mem_univ _)
    (Set.mem_univ _) hdet).2.1).symm

lemma aperyExtractOne_pure_triple_shift (a₀ a_half a₁ ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractOne
        (fun x : ℝ => aperyBranchTriple a₀ a_half a₁
          (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ = a₁ := by
  have hcan := IsAperyConnectionCoeffsOn.canonical a₀ a_half a₁ (Set.univ : Set ℝ)
  exact ((hcan.eq_extract (Set.mem_univ _) (Set.mem_univ _)
    (Set.mem_univ _) hdet).2.2).symm

/-! ### Extract under additive pure-branch shifts

These nine atoms describe how `aperyExtract{Regular,Half,One}`
transforms when `f` is shifted by a pure shifted branch
(`yAperyZero c (·−z₁)`, `yAperyHalf b (·−z₁)`, `yApery a (·−z₁)`).
Adding a regular branch is unconditional; adding a half- or one-branch
that affects its own extract requires the Cramer determinant. -/

@[simp] lemma aperyExtractRegular_add_yAperyZero_shift (f : ℝ → ℝ) (c : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => f x + yAperyZero c (x - Number.aperyConifoldZ1Poly)) =
      aperyExtractRegular f + c := by
  rw [aperyExtractRegular_add, aperyExtractRegular_pure_regular_shift]

@[simp] lemma aperyExtractHalf_add_yAperyZero_shift
    (f : ℝ → ℝ) (c ε₁ ε₂ : ℝ) :
    aperyExtractHalf
        (fun x : ℝ => f x + yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ := by
  rw [aperyExtractHalf_add, aperyExtractHalf_pure_regular_shift, add_zero]

@[simp] lemma aperyExtractOne_add_yAperyZero_shift
    (f : ℝ → ℝ) (c ε₁ ε₂ : ℝ) :
    aperyExtractOne
        (fun x : ℝ => f x + yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ := by
  rw [aperyExtractOne_add, aperyExtractOne_pure_regular_shift, add_zero]

@[simp] lemma aperyExtractRegular_add_yAperyHalf_shift (f : ℝ → ℝ) (b : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => f x + yAperyHalf b (x - Number.aperyConifoldZ1Poly)) =
      aperyExtractRegular f := by
  rw [aperyExtractRegular_add, aperyExtractRegular_pure_half_shift, add_zero]

lemma aperyExtractHalf_add_yAperyHalf_shift
    (f : ℝ → ℝ) (b ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractHalf
        (fun x : ℝ => f x + yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ + b := by
  rw [aperyExtractHalf_add, aperyExtractHalf_pure_half_shift _ _ _ hdet]

@[simp] lemma aperyExtractOne_add_yAperyHalf_shift
    (f : ℝ → ℝ) (b ε₁ ε₂ : ℝ) :
    aperyExtractOne
        (fun x : ℝ => f x + yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ := by
  rw [aperyExtractOne_add, aperyExtractOne_pure_half_shift, add_zero]

@[simp] lemma aperyExtractRegular_add_yApery_shift (f : ℝ → ℝ) (a : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => f x + yApery a (x - Number.aperyConifoldZ1Poly)) =
      aperyExtractRegular f := by
  rw [aperyExtractRegular_add, aperyExtractRegular_pure_one_shift, add_zero]

@[simp] lemma aperyExtractHalf_add_yApery_shift
    (f : ℝ → ℝ) (a ε₁ ε₂ : ℝ) :
    aperyExtractHalf
        (fun x : ℝ => f x + yApery a (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ := by
  rw [aperyExtractHalf_add, aperyExtractHalf_pure_one_shift, add_zero]

lemma aperyExtractOne_add_yApery_shift
    (f : ℝ → ℝ) (a ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractOne
        (fun x : ℝ => f x + yApery a (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ + a := by
  rw [aperyExtractOne_add, aperyExtractOne_pure_one_shift _ _ _ hdet]

/-! ### Extract under subtractive pure-branch shifts

Subtractive companion to the additive shift hexad — same nine entries
but with the seed appearing with a minus sign on the diagonal. -/

@[simp] lemma aperyExtractRegular_sub_yAperyZero_shift (f : ℝ → ℝ) (c : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => f x - yAperyZero c (x - Number.aperyConifoldZ1Poly)) =
      aperyExtractRegular f - c := by
  rw [aperyExtractRegular_sub, aperyExtractRegular_pure_regular_shift]

@[simp] lemma aperyExtractHalf_sub_yAperyZero_shift
    (f : ℝ → ℝ) (c ε₁ ε₂ : ℝ) :
    aperyExtractHalf
        (fun x : ℝ => f x - yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ := by
  rw [aperyExtractHalf_sub, aperyExtractHalf_pure_regular_shift, sub_zero]

@[simp] lemma aperyExtractOne_sub_yAperyZero_shift
    (f : ℝ → ℝ) (c ε₁ ε₂ : ℝ) :
    aperyExtractOne
        (fun x : ℝ => f x - yAperyZero c (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ := by
  rw [aperyExtractOne_sub, aperyExtractOne_pure_regular_shift, sub_zero]

@[simp] lemma aperyExtractRegular_sub_yAperyHalf_shift (f : ℝ → ℝ) (b : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => f x - yAperyHalf b (x - Number.aperyConifoldZ1Poly)) =
      aperyExtractRegular f := by
  rw [aperyExtractRegular_sub, aperyExtractRegular_pure_half_shift, sub_zero]

lemma aperyExtractHalf_sub_yAperyHalf_shift
    (f : ℝ → ℝ) (b ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractHalf
        (fun x : ℝ => f x - yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ - b := by
  rw [aperyExtractHalf_sub, aperyExtractHalf_pure_half_shift _ _ _ hdet]

@[simp] lemma aperyExtractOne_sub_yAperyHalf_shift
    (f : ℝ → ℝ) (b ε₁ ε₂ : ℝ) :
    aperyExtractOne
        (fun x : ℝ => f x - yAperyHalf b (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ := by
  rw [aperyExtractOne_sub, aperyExtractOne_pure_half_shift, sub_zero]

@[simp] lemma aperyExtractRegular_sub_yApery_shift (f : ℝ → ℝ) (a : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => f x - yApery a (x - Number.aperyConifoldZ1Poly)) =
      aperyExtractRegular f := by
  rw [aperyExtractRegular_sub, aperyExtractRegular_pure_one_shift, sub_zero]

@[simp] lemma aperyExtractHalf_sub_yApery_shift
    (f : ℝ → ℝ) (a ε₁ ε₂ : ℝ) :
    aperyExtractHalf
        (fun x : ℝ => f x - yApery a (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ := by
  rw [aperyExtractHalf_sub, aperyExtractHalf_pure_one_shift, sub_zero]

lemma aperyExtractOne_sub_yApery_shift
    (f : ℝ → ℝ) (a ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractOne
        (fun x : ℝ => f x - yApery a (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ - a := by
  rw [aperyExtractOne_sub, aperyExtractOne_pure_one_shift _ _ _ hdet]

/-! ### Extract under additive / subtractive full-triple shifts

The full `aperyBranchTriple b₀ b_half b₁` shifted form is the canonical
"all three pure branches" generator. Extract is linear, so each
component shifts independently by the corresponding seed. Six atoms
total: three for addition (`+ aperyBranchTriple b₀ b_half b₁ (·−z₁)`)
and three for subtraction. -/

@[simp] lemma aperyExtractRegular_add_aperyBranchTriple_shift
    (f : ℝ → ℝ) (b₀ b_half b₁ : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => f x + aperyBranchTriple b₀ b_half b₁
          (x - Number.aperyConifoldZ1Poly)) =
      aperyExtractRegular f + b₀ := by
  rw [aperyExtractRegular_add, aperyExtractRegular_pure_triple_shift]

lemma aperyExtractHalf_add_aperyBranchTriple_shift
    (f : ℝ → ℝ) (b₀ b_half b₁ ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractHalf
        (fun x : ℝ => f x + aperyBranchTriple b₀ b_half b₁
          (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ + b_half := by
  rw [aperyExtractHalf_add,
      aperyExtractHalf_pure_triple_shift _ _ _ _ _ hdet]

lemma aperyExtractOne_add_aperyBranchTriple_shift
    (f : ℝ → ℝ) (b₀ b_half b₁ ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractOne
        (fun x : ℝ => f x + aperyBranchTriple b₀ b_half b₁
          (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ + b₁ := by
  rw [aperyExtractOne_add,
      aperyExtractOne_pure_triple_shift _ _ _ _ _ hdet]

@[simp] lemma aperyExtractRegular_sub_aperyBranchTriple_shift
    (f : ℝ → ℝ) (b₀ b_half b₁ : ℝ) :
    aperyExtractRegular
        (fun x : ℝ => f x - aperyBranchTriple b₀ b_half b₁
          (x - Number.aperyConifoldZ1Poly)) =
      aperyExtractRegular f - b₀ := by
  rw [aperyExtractRegular_sub, aperyExtractRegular_pure_triple_shift]

lemma aperyExtractHalf_sub_aperyBranchTriple_shift
    (f : ℝ → ℝ) (b₀ b_half b₁ ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractHalf
        (fun x : ℝ => f x - aperyBranchTriple b₀ b_half b₁
          (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractHalf f ε₁ ε₂ - b_half := by
  rw [aperyExtractHalf_sub,
      aperyExtractHalf_pure_triple_shift _ _ _ _ _ hdet]

lemma aperyExtractOne_sub_aperyBranchTriple_shift
    (f : ℝ → ℝ) (b₀ b_half b₁ ε₁ ε₂ : ℝ)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    aperyExtractOne
        (fun x : ℝ => f x - aperyBranchTriple b₀ b_half b₁
          (x - Number.aperyConifoldZ1Poly)) ε₁ ε₂ =
      aperyExtractOne f ε₁ ε₂ - b₁ := by
  rw [aperyExtractOne_sub,
      aperyExtractOne_pure_triple_shift _ _ _ _ _ hdet]

/-! ### Extract over Finset summations

Each named extraction distributes over a `Finset`-sum of summands.
This generalises `aperyExtract*_add` (binary case) to arbitrary
finite linear combinations indexed by any type. -/

lemma aperyExtractRegular_finset_sum {α : Type*}
    (s : Finset α) (f : α → ℝ → ℝ) :
    aperyExtractRegular (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, aperyExtractRegular (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact aperyExtractRegular_zero
  | @insert a s' ha ih =>
      have hsum : (fun z => ∑ i ∈ insert a s', f i z) =
          (fun z => f a z + ∑ i ∈ s', f i z) := by
        funext z; rw [Finset.sum_insert ha]
      rw [hsum, aperyExtractRegular_add, ih, Finset.sum_insert ha]

lemma aperyExtractHalf_finset_sum {α : Type*}
    (s : Finset α) (f : α → ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractHalf (fun z => ∑ i ∈ s, f i z) ε₁ ε₂ =
      ∑ i ∈ s, aperyExtractHalf (f i) ε₁ ε₂ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact aperyExtractHalf_zero ε₁ ε₂
  | @insert a s' ha ih =>
      have hsum : (fun z => ∑ i ∈ insert a s', f i z) =
          (fun z => f a z + ∑ i ∈ s', f i z) := by
        funext z; rw [Finset.sum_insert ha]
      rw [hsum, aperyExtractHalf_add, ih, Finset.sum_insert ha]

lemma aperyExtractOne_finset_sum {α : Type*}
    (s : Finset α) (f : α → ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractOne (fun z => ∑ i ∈ s, f i z) ε₁ ε₂ =
      ∑ i ∈ s, aperyExtractOne (f i) ε₁ ε₂ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact aperyExtractOne_zero ε₁ ε₂
  | @insert a s' ha ih =>
      have hsum : (fun z => ∑ i ∈ insert a s', f i z) =
          (fun z => f a z + ∑ i ∈ s', f i z) := by
        funext z; rw [Finset.sum_insert ha]
      rw [hsum, aperyExtractOne_add, ih, Finset.sum_insert ha]

/-- **Regular extract congruence.** `aperyExtractRegular f` depends only on
the value `f z₁`. -/
lemma aperyExtractRegular_congr {f g : ℝ → ℝ}
    (h0 : f Number.aperyConifoldZ1Poly = g Number.aperyConifoldZ1Poly) :
    aperyExtractRegular f = aperyExtractRegular g := by
  unfold aperyExtractRegular; exact h0

/-- **Half extract congruence.** `aperyExtractHalf f ε₁ ε₂` depends only on
the values `f z₁`, `f (z₁ − ε₁)`, `f (z₁ − ε₂)`. -/
lemma aperyExtractHalf_congr {f g : ℝ → ℝ} {ε₁ ε₂ : ℝ}
    (h0 : f Number.aperyConifoldZ1Poly = g Number.aperyConifoldZ1Poly)
    (h1 : f (Number.aperyConifoldZ1Poly + (-ε₁)) =
          g (Number.aperyConifoldZ1Poly + (-ε₁)))
    (h2 : f (Number.aperyConifoldZ1Poly + (-ε₂)) =
          g (Number.aperyConifoldZ1Poly + (-ε₂))) :
    aperyExtractHalf f ε₁ ε₂ = aperyExtractHalf g ε₁ ε₂ := by
  unfold aperyExtractHalf
  rw [aperyConnectionResidual_congr_pt h0 h1,
      aperyConnectionResidual_congr_pt h0 h2]

/-- **One extract congruence.** `aperyExtractOne f ε₁ ε₂` depends only on
the values `f z₁`, `f (z₁ − ε₁)`, `f (z₁ − ε₂)`. -/
lemma aperyExtractOne_congr {f g : ℝ → ℝ} {ε₁ ε₂ : ℝ}
    (h0 : f Number.aperyConifoldZ1Poly = g Number.aperyConifoldZ1Poly)
    (h1 : f (Number.aperyConifoldZ1Poly + (-ε₁)) =
          g (Number.aperyConifoldZ1Poly + (-ε₁)))
    (h2 : f (Number.aperyConifoldZ1Poly + (-ε₂)) =
          g (Number.aperyConifoldZ1Poly + (-ε₂))) :
    aperyExtractOne f ε₁ ε₂ = aperyExtractOne g ε₁ ε₂ := by
  unfold aperyExtractOne
  rw [aperyConnectionResidual_congr_pt h0 h1,
      aperyConnectionResidual_congr_pt h0 h2]

/-- **Regular extract `EqOn` congruence.** If `f` and `g` agree on a set
`S ⊆ ℝ` containing `z₁`, then `aperyExtractRegular f = aperyExtractRegular g`. -/
lemma aperyExtractRegular_congr_eqOn {f g : ℝ → ℝ} {S : Set ℝ}
    (hfg : Set.EqOn f g S) (hz1 : Number.aperyConifoldZ1Poly ∈ S) :
    aperyExtractRegular f = aperyExtractRegular g :=
  aperyExtractRegular_congr (hfg hz1)

/-- **Half extract `EqOn` congruence.** If `f` and `g` agree on a set
`S ⊆ ℝ` containing `{z₁, z₁ − ε₁, z₁ − ε₂}`, then the half extracts agree. -/
lemma aperyExtractHalf_congr_eqOn {f g : ℝ → ℝ} {ε₁ ε₂ : ℝ} {S : Set ℝ}
    (hfg : Set.EqOn f g S) (hz1 : Number.aperyConifoldZ1Poly ∈ S)
    (h1 : Number.aperyConifoldZ1Poly + (-ε₁) ∈ S)
    (h2 : Number.aperyConifoldZ1Poly + (-ε₂) ∈ S) :
    aperyExtractHalf f ε₁ ε₂ = aperyExtractHalf g ε₁ ε₂ :=
  aperyExtractHalf_congr (hfg hz1) (hfg h1) (hfg h2)

/-- **One extract `EqOn` congruence.** If `f` and `g` agree on a set
`S ⊆ ℝ` containing `{z₁, z₁ − ε₁, z₁ − ε₂}`, then the one extracts agree. -/
lemma aperyExtractOne_congr_eqOn {f g : ℝ → ℝ} {ε₁ ε₂ : ℝ} {S : Set ℝ}
    (hfg : Set.EqOn f g S) (hz1 : Number.aperyConifoldZ1Poly ∈ S)
    (h1 : Number.aperyConifoldZ1Poly + (-ε₁) ∈ S)
    (h2 : Number.aperyConifoldZ1Poly + (-ε₂) ∈ S) :
    aperyExtractOne f ε₁ ε₂ = aperyExtractOne g ε₁ ε₂ :=
  aperyExtractOne_congr (hfg hz1) (hfg h1) (hfg h2)

/-- **Single-component projection: `a₀ = ExtractRegular`.** Split form of
`eq_extract` for the regular component. -/
lemma IsAperyConnectionCoeffsOn.regular_eq_extract
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₀ = aperyExtractRegular f :=
  (ha.eq_extract h0 hε₁ hε₂ hdet).1

/-- **Single-component projection: `a_half = ExtractHalf`.** Split form of
`eq_extract` for the half-branch component. -/
lemma IsAperyConnectionCoeffsOn.half_eq_extract
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a_half = aperyExtractHalf f ε₁ ε₂ :=
  (ha.eq_extract h0 hε₁ hε₂ hdet).2.1

/-- **Single-component projection: `a₁ = ExtractOne`.** Split form of
`eq_extract` for the one-branch component. -/
lemma IsAperyConnectionCoeffsOn.one_eq_extract
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₁ = aperyExtractOne f ε₁ ε₂ :=
  (ha.eq_extract h0 hε₁ hε₂ hdet).2.2

/-- **Has-level uniqueness via extract.** Under representability and
non-degenerate Δ, any two witness triples coincide — both equal the
extract triple. -/
lemma HasAperyConnectionCoeffsOn.witness_eq_via_extract
    {a₀ a_half a₁ b₀ b_half b₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (hb : IsAperyConnectionCoeffsOn b₀ b_half b₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    a₀ = b₀ ∧ a_half = b_half ∧ a₁ = b₁ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ha.regular_eq_extract h0 hε₁ hε₂ hdet,
        hb.regular_eq_extract h0 hε₁ hε₂ hdet]
  · rw [ha.half_eq_extract h0 hε₁ hε₂ hdet,
        hb.half_eq_extract h0 hε₁ hε₂ hdet]
  · rw [ha.one_eq_extract h0 hε₁ hε₂ hdet,
        hb.one_eq_extract h0 hε₁ hε₂ hdet]

/-- **Has-level extract triple is the unique witness.** Under
representability and a non-degenerate Δ, the extract triple is the
unique connection-coefficient triple. -/
lemma HasAperyConnectionCoeffsOn.existsUnique_extract
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    ∃! abc : ℝ × ℝ × ℝ,
      IsAperyConnectionCoeffsOn abc.1 abc.2.1 abc.2.2 f I ∧
      abc.1 = aperyExtractRegular f ∧
      abc.2.1 = aperyExtractHalf f ε₁ ε₂ ∧
      abc.2.2 = aperyExtractOne f ε₁ ε₂ := by
  refine ⟨(aperyExtractRegular f, aperyExtractHalf f ε₁ ε₂,
           aperyExtractOne f ε₁ ε₂),
          ⟨h.is_extract h0 hε₁ hε₂ hdet, rfl, rfl, rfl⟩, ?_⟩
  rintro ⟨b₀, b_half, b₁⟩ ⟨_, hb0, hbh, hb1⟩
  simp only [Prod.mk.injEq]
  exact ⟨hb0, hbh, hb1⟩

/-- **Cramer determinant.** Δ(ε₁,ε₂) = A_½(ε₁)·V_1(ε₂) − A_½(ε₂)·V_1(ε₁).
The named denominator that appears in `aperyExtract{Half,One}` and in all
hypotheses requiring non-degenerate two-probe singular geometry. -/
noncomputable def aperyConnectionDet (ε₁ ε₂ : ℝ) : ℝ :=
  aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
    aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁

/-- **Det antisymmetry.** Swapping the two probes negates Δ. -/
lemma aperyConnectionDet_swap (ε₁ ε₂ : ℝ) :
    aperyConnectionDet ε₂ ε₁ = -(aperyConnectionDet ε₁ ε₂) := by
  unfold aperyConnectionDet; ring

/-- **Det diagonal vanishes.** Δ(ε,ε) = 0. -/
@[simp] lemma aperyConnectionDet_self (ε : ℝ) :
    aperyConnectionDet ε ε = 0 := by
  unfold aperyConnectionDet; ring

/-- **Det unfold.** Expands `aperyConnectionDet` into its A_½ · V_1 form. -/
lemma aperyConnectionDet_def (ε₁ ε₂ : ℝ) :
    aperyConnectionDet ε₁ ε₂ =
      aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ := rfl

/-- **Det factored form (positive probes).** Pulls the `√ε₁·√ε₂`
prefactor out of the 2×2 connection determinant. With `0 ≤ ε₁` and
`0 ≤ ε₂`, the identity
`Δ = √ε₁·√ε₂ · (√ε₁·H_₂·O_₁ − √ε₂·H_₁·O_₂)` exposes the leading-order
structure: at small ε the bracket tends to `√ε₁·1·1 − √ε₂·1·1 =
√ε₁ − √ε₂`, so Δ ≠ 0 ⟺ √ε₁ ≠ √ε₂ at small ε (Vandermonde-like). -/
lemma aperyConnectionDet_factored {ε₁ ε₂ : ℝ}
    (h₁ : 0 ≤ ε₁) (h₂ : 0 ≤ ε₂) :
    aperyConnectionDet ε₁ ε₂ =
      Real.sqrt ε₁ * Real.sqrt ε₂ *
        (Real.sqrt ε₁ * aperyBranchHalfCore ε₂ * aperyBranchOneCore ε₁ -
          Real.sqrt ε₂ * aperyBranchHalfCore ε₁ * aperyBranchOneCore ε₂) := by
  have hk1 : Real.sqrt ε₁ * Real.sqrt ε₁ = ε₁ := Real.mul_self_sqrt h₁
  have hk2 : Real.sqrt ε₂ * Real.sqrt ε₂ = ε₂ := Real.mul_self_sqrt h₂
  unfold aperyConnectionDet
  rw [aperyBranchAmplitude_half_factored ε₁,
      aperyBranchAmplitude_half_factored ε₂,
      aperyBranchValue_one_factored ε₁,
      aperyBranchValue_one_factored ε₂]
  linear_combination
    Real.sqrt ε₁ * aperyBranchHalfCore ε₁ * aperyBranchOneCore ε₂ * hk2
      - Real.sqrt ε₂ * aperyBranchHalfCore ε₂ * aperyBranchOneCore ε₁ * hk1

/-- **Joint continuity of the 2×2 connection determinant.** Given the
hypothesis bundle for both ρ=1/2 and ρ=1 (sharing M₀, B, threshold,
disk), the function `(ε₁, ε₂) ↦ Δ(ε₁, ε₂)` is continuous on
`Icc(-s, s) × Icc(-s, s)`. This is the building block for path-arguments
that propagate non-vanishing of Δ from a known reference point. -/
lemma aperyConnectionDet_continuousOn_general
    (M₀ : ℕ) (B : ℝ) (hB_nn : 0 ≤ B)
    (hM0_small_half : ∀ m, M₀ ≤ m →
        (|(1 / 2 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large_half : ∀ m, M₀ ≤ m →
        3 * |(1 / 2 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh_half : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 / 2 : ℝ)| - (2 : ℝ)))
    (hM0_small_one : ∀ m, M₀ ≤ m → (|(1 : ℝ)| + (2 : ℝ)) < ((m + 1 : ℕ) : ℝ))
    (hM0_large_one : ∀ m, M₀ ≤ m → 3 * |(1 : ℝ)| + 3 * (2 : ℝ) ≤ (m : ℝ))
    (hM0_thresh_one : ∀ m', M₀ ≤ m' →
        2 * |Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold| ≤
          |Polynomial.eval Number.aperyConifoldZ1Poly
              (Polynomial.derivative Number.aperyPconifold)| *
            (((m' + 1 : ℕ) : ℝ) - |(1 : ℝ)| - (2 : ℝ)))
    (hB : ∀ j ∈ Finset.range 4, ∀ ℓ : ℕ,
        |Polynomial.coeff (taylorShift
          ((aperyPsSeq 0 0 Number.aperyQconifold Number.aperyPconifold) j)
          Number.aperyConifoldZ1Poly) ℓ| ≤ B)
    (s : ℝ) (hs_nn : 0 ≤ s)
    (hs_lt : s * (1 + 2 * (4 : ℝ) * B * ((2 : ℝ) ^ 3) /
      |Polynomial.eval Number.aperyConifoldZ1Poly
        (Polynomial.derivative Number.aperyPconifold)|) < 1) :
    ContinuousOn (fun p : ℝ × ℝ => aperyConnectionDet p.1 p.2)
      ((Set.Icc (-s) s) ×ˢ (Set.Icc (-s) s)) := by
  have hAhalf : ContinuousOn aperyBranchAmplitude_half (Set.Icc (-s) s) :=
    aperyBranchAmplitude_half_continuousOn_general M₀ B hB_nn
      hM0_small_half hM0_large_half hM0_thresh_half hB s hs_nn hs_lt
  have hVone : ContinuousOn aperyBranchValue_one (Set.Icc (-s) s) :=
    aperyBranchValue_one_continuousOn_general M₀ B hB_nn
      hM0_small_one hM0_large_one hM0_thresh_one hB s hs_nn hs_lt
  have hfst : ContinuousOn (fun p : ℝ × ℝ => p.1)
      ((Set.Icc (-s) s) ×ˢ (Set.Icc (-s) s)) :=
    continuous_fst.continuousOn
  have hsnd : ContinuousOn (fun p : ℝ × ℝ => p.2)
      ((Set.Icc (-s) s) ×ˢ (Set.Icc (-s) s)) :=
    continuous_snd.continuousOn
  have hmaps_fst : Set.MapsTo (fun p : ℝ × ℝ => p.1)
      ((Set.Icc (-s) s) ×ˢ (Set.Icc (-s) s)) (Set.Icc (-s) s) := fun _ hp => hp.1
  have hmaps_snd : Set.MapsTo (fun p : ℝ × ℝ => p.2)
      ((Set.Icc (-s) s) ×ˢ (Set.Icc (-s) s)) (Set.Icc (-s) s) := fun _ hp => hp.2
  have hA1 : ContinuousOn (fun p : ℝ × ℝ => aperyBranchAmplitude_half p.1)
      ((Set.Icc (-s) s) ×ˢ (Set.Icc (-s) s)) := hAhalf.comp hfst hmaps_fst
  have hA2 : ContinuousOn (fun p : ℝ × ℝ => aperyBranchAmplitude_half p.2)
      ((Set.Icc (-s) s) ×ˢ (Set.Icc (-s) s)) := hAhalf.comp hsnd hmaps_snd
  have hV1 : ContinuousOn (fun p : ℝ × ℝ => aperyBranchValue_one p.1)
      ((Set.Icc (-s) s) ×ˢ (Set.Icc (-s) s)) := hVone.comp hfst hmaps_fst
  have hV2 : ContinuousOn (fun p : ℝ × ℝ => aperyBranchValue_one p.2)
      ((Set.Icc (-s) s) ×ˢ (Set.Icc (-s) s)) := hVone.comp hsnd hmaps_snd
  exact (hA1.mul hV2).sub (hA2.mul hV1)

/-- **Det non-vanishing reduces to bracket non-vanishing (positive
probes).** With `0 < ε₁`, `0 < ε₂`, the `√ε₁·√ε₂` prefactor in
`aperyConnectionDet_factored` is nonzero, so `Δ ≠ 0` iff the
Vandermonde-like bracket is nonzero. This is the operational form
used to discharge `Δ ≠ 0` hypotheses in the canonical extraction
pipeline. -/
lemma aperyConnectionDet_ne_zero_iff_bracket {ε₁ ε₂ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    aperyConnectionDet ε₁ ε₂ ≠ 0 ↔
      Real.sqrt ε₁ * aperyBranchHalfCore ε₂ * aperyBranchOneCore ε₁ -
        Real.sqrt ε₂ * aperyBranchHalfCore ε₁ * aperyBranchOneCore ε₂ ≠ 0 := by
  rw [aperyConnectionDet_factored h₁.le h₂.le]
  have hs1 : Real.sqrt ε₁ ≠ 0 := (Real.sqrt_pos.mpr h₁).ne'
  have hs2 : Real.sqrt ε₂ ≠ 0 := (Real.sqrt_pos.mpr h₂).ne'
  constructor
  · intro h hbr
    apply h
    rw [hbr, mul_zero]
  · intro hbr
    exact mul_ne_zero (mul_ne_zero hs1 hs2) hbr

/-- **`aperyConnectionDet` at unit cores reduces to `√ε₁·√ε₂·(√ε₁−√ε₂)`.**
Polynomial identity at the leading-order ideal limit: when both
`HalfCore` and `OneCore` are `1` at both probes, the 2×2 connection
det collapses to the trivial Vandermonde-like form. -/
lemma aperyConnectionDet_unit_cores_eq {ε₁ ε₂ : ℝ}
    (h₁ : 0 ≤ ε₁) (h₂ : 0 ≤ ε₂)
    (hH1 : aperyBranchHalfCore ε₁ = 1)
    (hH2 : aperyBranchHalfCore ε₂ = 1)
    (hO1 : aperyBranchOneCore ε₁ = 1)
    (hO2 : aperyBranchOneCore ε₂ = 1) :
    aperyConnectionDet ε₁ ε₂ =
      Real.sqrt ε₁ * Real.sqrt ε₂ * (Real.sqrt ε₁ - Real.sqrt ε₂) := by
  rw [aperyConnectionDet_factored h₁ h₂, hH1, hH2, hO1, hO2]
  ring

/-- **`aperyConnectionDet` non-vanishing in the unit-core ideal limit.**
For positive distinct probes with all cores equal to `1`,
`aperyConnectionDet ≠ 0`. The 2-probe sibling of
`apery3Det_unit_cores_ne_zero`. -/
lemma aperyConnectionDet_unit_cores_ne_zero {ε₁ ε₂ : ℝ}
    (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h12 : ε₁ ≠ ε₂)
    (hH1 : aperyBranchHalfCore ε₁ = 1)
    (hH2 : aperyBranchHalfCore ε₂ = 1)
    (hO1 : aperyBranchOneCore ε₁ = 1)
    (hO2 : aperyBranchOneCore ε₂ = 1) :
    aperyConnectionDet ε₁ ε₂ ≠ 0 := by
  rw [aperyConnectionDet_unit_cores_eq h₁.le h₂.le hH1 hH2 hO1 hO2]
  have hs1 : Real.sqrt ε₁ ≠ 0 := (Real.sqrt_pos.mpr h₁).ne'
  have hs2 : Real.sqrt ε₂ ≠ 0 := (Real.sqrt_pos.mpr h₂).ne'
  refine mul_ne_zero (mul_ne_zero hs1 hs2) ?_
  intro h
  have hs : Real.sqrt ε₁ = Real.sqrt ε₂ := sub_eq_zero.mp h
  exact h12 ((Real.sqrt_inj h₁.le h₂.le).mp hs)

/-- **Det non-vanishing iff expanded form non-vanishing.** Bridge between
the named `hdet : aperyConnectionDet ε₁ ε₂ ≠ 0` and the expanded
hypothesis used throughout the existing Has-level interface. -/
lemma aperyConnectionDet_ne_zero_iff {ε₁ ε₂ : ℝ} :
    aperyConnectionDet ε₁ ε₂ ≠ 0 ↔
      aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
        aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0 := Iff.rfl

/-- **Half extract via named Det.** Rewrites the denominator to
`aperyConnectionDet` for downstream use. -/
lemma aperyExtractHalf_eq_div_det (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractHalf f ε₁ ε₂ =
      (aperyConnectionResidual f ε₁ * aperyBranchValue_one ε₂ -
        aperyConnectionResidual f ε₂ * aperyBranchValue_one ε₁) /
        aperyConnectionDet ε₁ ε₂ := rfl

/-- **One extract via named Det.** Rewrites the denominator to
`aperyConnectionDet` for downstream use. -/
lemma aperyExtractOne_eq_div_det (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractOne f ε₁ ε₂ =
      (-(aperyConnectionResidual f ε₁ * aperyBranchAmplitude_half ε₂) +
        aperyConnectionResidual f ε₂ * aperyBranchAmplitude_half ε₁) /
        aperyConnectionDet ε₁ ε₂ := rfl

/-- **Half extract antisymmetry under probe swap.** -/
lemma aperyExtractHalf_swap (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractHalf f ε₂ ε₁ = aperyExtractHalf f ε₁ ε₂ := by
  unfold aperyExtractHalf
  rw [show
    (aperyConnectionResidual f ε₂ * aperyBranchValue_one ε₁ -
        aperyConnectionResidual f ε₁ * aperyBranchValue_one ε₂) =
      -((aperyConnectionResidual f ε₁ * aperyBranchValue_one ε₂ -
          aperyConnectionResidual f ε₂ * aperyBranchValue_one ε₁)) from by ring]
  rw [show
    (aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ -
        aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂) =
      -((aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁)) from by ring]
  rw [neg_div_neg_eq]

/-- **One extract antisymmetry under probe swap.** -/
lemma aperyExtractOne_swap (f : ℝ → ℝ) (ε₁ ε₂ : ℝ) :
    aperyExtractOne f ε₂ ε₁ = aperyExtractOne f ε₁ ε₂ := by
  unfold aperyExtractOne
  rw [show
    (-(aperyConnectionResidual f ε₂ * aperyBranchAmplitude_half ε₁) +
        aperyConnectionResidual f ε₁ * aperyBranchAmplitude_half ε₂) =
      -((-(aperyConnectionResidual f ε₁ * aperyBranchAmplitude_half ε₂) +
          aperyConnectionResidual f ε₂ * aperyBranchAmplitude_half ε₁))
      from by ring]
  rw [show
    (aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ -
        aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂) =
      -((aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
          aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁)) from by ring]
  rw [neg_div_neg_eq]

/-- **Has-level shifted equality via extract.** Under representability and
non-degenerate Δ, the shifted function equals the branch triple built from
the named extract values, pointwise on `I`. The extract triple is the
"intrinsic" reconstruction of `f` on the corridor right-endpoint. -/
lemma HasAperyConnectionCoeffsOn.shifted_eq_extract
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyBranchAmplitude_half ε₁ * aperyBranchValue_one ε₂ -
            aperyBranchAmplitude_half ε₂ * aperyBranchValue_one ε₁ ≠ 0) :
    Set.EqOn (fun t => f (Number.aperyConifoldZ1Poly + t))
      (fun t => aperyBranchTriple (aperyExtractRegular f)
        (aperyExtractHalf f ε₁ ε₂) (aperyExtractOne f ε₁ ε₂) t) I :=
  (h.is_extract h0 hε₁ hε₂ hdet).shifted_eq

/-- **Det vanishes when first probe is zero.** Δ(0, ε) = 0. Together with
the swap antisymmetry, captures the singular geometry where `ε = 0` is a
degenerate probe direction. -/
@[simp] lemma aperyConnectionDet_zero_left (ε : ℝ) :
    aperyConnectionDet 0 ε = 0 := by
  unfold aperyConnectionDet
  rw [aperyBranchAmplitude_half_at_zero, aperyBranchValue_one_at_zero]
  ring

/-- **Det vanishes when second probe is zero.** Δ(ε, 0) = 0. -/
@[simp] lemma aperyConnectionDet_zero_right (ε : ℝ) :
    aperyConnectionDet ε 0 = 0 := by
  unfold aperyConnectionDet
  rw [aperyBranchAmplitude_half_at_zero, aperyBranchValue_one_at_zero]
  ring

/-- **Det non-vanishing forces both probes nonzero.** If `Δ(ε₁, ε₂) ≠ 0`,
then `ε₁ ≠ 0` and `ε₂ ≠ 0` (and `ε₁ ≠ ε₂`). -/
lemma aperyConnectionDet_ne_zero_probes_nonzero {ε₁ ε₂ : ℝ}
    (hdet : aperyConnectionDet ε₁ ε₂ ≠ 0) :
    ε₁ ≠ 0 ∧ ε₂ ≠ 0 ∧ ε₁ ≠ ε₂ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; subst h; simp at hdet
  · intro h; subst h; simp at hdet
  · intro h; subst h; simp at hdet

/-- **Has-level `is_extract` with named Det.** Wrapper of `is_extract`
accepting `hdet : aperyConnectionDet ε₁ ε₂ ≠ 0`. -/
lemma HasAperyConnectionCoeffsOn.is_extract_det
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyConnectionDet ε₁ ε₂ ≠ 0) :
    IsAperyConnectionCoeffsOn (aperyExtractRegular f)
      (aperyExtractHalf f ε₁ ε₂) (aperyExtractOne f ε₁ ε₂) f I :=
  h.is_extract h0 hε₁ hε₂ hdet

/-- **Witness equals extract with named Det.** -/
lemma IsAperyConnectionCoeffsOn.eq_extract_det
    {a₀ a_half a₁ : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : IsAperyConnectionCoeffsOn a₀ a_half a₁ f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyConnectionDet ε₁ ε₂ ≠ 0) :
    a₀ = aperyExtractRegular f ∧
    a_half = aperyExtractHalf f ε₁ ε₂ ∧
    a₁ = aperyExtractOne f ε₁ ε₂ :=
  ha.eq_extract h0 hε₁ hε₂ hdet

/-- **Has-level shifted reconstruction with named Det.** -/
lemma HasAperyConnectionCoeffsOn.shifted_eq_extract_det
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ : ℝ} (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hdet : aperyConnectionDet ε₁ ε₂ ≠ 0) :
    Set.EqOn (fun t => f (Number.aperyConifoldZ1Poly + t))
      (fun t => aperyBranchTriple (aperyExtractRegular f)
        (aperyExtractHalf f ε₁ ε₂) (aperyExtractOne f ε₁ ε₂) t) I :=
  h.shifted_eq_extract h0 hε₁ hε₂ hdet

/-- **Half extract probe-pair invariance.** Under representability and two
non-degenerate probe pairs `(ε₁, ε₂)` and `(ε₁', ε₂')` (both with all
witness points in `I`), the half extract values agree. Both equal the
same a_half coefficient of the canonical witness. -/
lemma HasAperyConnectionCoeffsOn.extractHalf_probe_invariant
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ ε₁' ε₂' : ℝ}
    (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hε₁' : (-ε₁') ∈ I) (hε₂' : (-ε₂') ∈ I)
    (hdet : aperyConnectionDet ε₁ ε₂ ≠ 0)
    (hdet' : aperyConnectionDet ε₁' ε₂' ≠ 0) :
    aperyExtractHalf f ε₁ ε₂ = aperyExtractHalf f ε₁' ε₂' := by
  obtain ⟨a₀, a_half, a₁, ha⟩ := h
  rw [← ha.half_eq_extract h0 hε₁ hε₂ hdet,
      ← ha.half_eq_extract h0 hε₁' hε₂' hdet']

/-- **One extract probe-pair invariance.** Symmetric statement for the
ρ=1 component. -/
lemma HasAperyConnectionCoeffsOn.extractOne_probe_invariant
    {f : ℝ → ℝ} {I : Set ℝ} (h : HasAperyConnectionCoeffsOn f I)
    (h0 : (0 : ℝ) ∈ I) {ε₁ ε₂ ε₁' ε₂' : ℝ}
    (hε₁ : (-ε₁) ∈ I) (hε₂ : (-ε₂) ∈ I)
    (hε₁' : (-ε₁') ∈ I) (hε₂' : (-ε₂') ∈ I)
    (hdet : aperyConnectionDet ε₁ ε₂ ≠ 0)
    (hdet' : aperyConnectionDet ε₁' ε₂' ≠ 0) :
    aperyExtractOne f ε₁ ε₂ = aperyExtractOne f ε₁' ε₂' := by
  obtain ⟨a₀, a_half, a₁, ha⟩ := h
  rw [← ha.one_eq_extract h0 hε₁ hε₂ hdet,
      ← ha.one_eq_extract h0 hε₁' hε₂' hdet']

/-! ## taylorShift coefficient closed forms for `aperyQconifold`

These pass the Frobenius substitution (`taylorShift Q z₁`) coefficients
through their derivative-evaluation identities. Combined with the
generic `taylorShift_coeff_{zero,one,two,three}` lemmas in
`Substitution.lean` and the closed-form `aperyQconifold_*_eval_z1_abs`
identities in `AperyConifoldIndicial.lean`, they give explicit values
for `|coeff (taylorShift aperyQconifold z₁) ℓ|` at `ℓ = 0, 1, 2`. -/

/-- The constant Taylor coefficient of `aperyQconifold` shifted to the
conifold equals `q(z₁)`. -/
lemma aperyQconifold_taylorShift_coeff_zero :
    Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) 0
      = Polynomial.eval Number.aperyConifoldZ1Poly Number.aperyQconifold :=
  taylorShift_coeff_zero Number.aperyQconifold Number.aperyConifoldZ1Poly

/-- `|coeff (taylorShift Q z₁) 0| = 20772·√2 − 29376`. -/
lemma aperyQconifold_taylorShift_coeff_zero_abs :
    |Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) 0|
      = 20772 * Real.sqrt 2 - 29376 := by
  rw [aperyQconifold_taylorShift_coeff_zero,
      Number.aperyQconifold_eval_z1_abs]

/-- The first-order Taylor coefficient of `aperyQconifold` shifted to
the conifold equals `-q'(z₁)`. The sign comes from the Jacobian
`dz/dt = -1`. -/
lemma aperyQconifold_taylorShift_coeff_one :
    Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) 1
      = - Polynomial.eval Number.aperyConifoldZ1Poly
          (Polynomial.derivative Number.aperyQconifold) :=
  taylorShift_coeff_one Number.aperyQconifold Number.aperyConifoldZ1Poly

/-- `|coeff (taylorShift Q z₁) 1| = 3672·√2 − 5187`. -/
lemma aperyQconifold_taylorShift_coeff_one_abs :
    |Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) 1|
      = 3672 * Real.sqrt 2 - 5187 := by
  rw [aperyQconifold_taylorShift_coeff_one, abs_neg,
      Number.aperyQconifold_deriv_eval_z1_abs]

/-- The second-order Taylor coefficient of `aperyQconifold` shifted to
the conifold equals `q''(z₁) / 2`. The factor `(-1)^2 = 1` from the
Jacobian cancels out. -/
lemma aperyQconifold_taylorShift_coeff_two :
    Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) 2
      = Polynomial.eval Number.aperyConifoldZ1Poly
          (Polynomial.derivative (Polynomial.derivative Number.aperyQconifold))
        / 2 :=
  taylorShift_coeff_two Number.aperyQconifold Number.aperyConifoldZ1Poly

/-- `|coeff (taylorShift Q z₁) 2| = 216·√2 − 153`. -/
lemma aperyQconifold_taylorShift_coeff_two_abs :
    |Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) 2|
      = 216 * Real.sqrt 2 - 153 := by
  rw [aperyQconifold_taylorShift_coeff_two, abs_div,
      Number.aperyQconifold_deriv2_eval_z1_abs,
      show |(2 : ℝ)| = 2 from abs_of_pos (by norm_num)]
  ring

/-- The third-order Taylor coefficient of `aperyQconifold` shifted to
the conifold equals `-q'''(z₁) / 6 = -6`. -/
lemma aperyQconifold_taylorShift_coeff_three :
    Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) 3
      = -6 := by
  rw [taylorShift_coeff_three, Number.aperyQconifold_deriv3_eval_z1]
  norm_num

/-- `|coeff (taylorShift Q z₁) 3| = 6`. -/
lemma aperyQconifold_taylorShift_coeff_three_abs :
    |Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) 3|
      = 6 := by
  rw [aperyQconifold_taylorShift_coeff_three]
  norm_num

/-- The natural degree of `aperyQconifold` is at most `3`. -/
lemma aperyQconifold_natDegree_le : Number.aperyQconifold.natDegree ≤ 3 := by
  unfold Number.aperyQconifold
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ?_ ?_
  · refine (Polynomial.natDegree_add_le _ _).trans ?_
    refine max_le ?_ ?_
    · exact (Polynomial.natDegree_monomial_le _).trans (by norm_num)
    · exact (Polynomial.natDegree_monomial_le _).trans (by norm_num)
  · exact Polynomial.natDegree_monomial_le _

/-- For `ℓ ≥ 4`, the `ℓ`-th Taylor coefficient of `aperyQconifold`
shifted to the conifold vanishes. (Q has degree at most `3`.) -/
lemma aperyQconifold_taylorShift_coeff_eq_zero_of_four_le
    {ℓ : ℕ} (hℓ : 4 ≤ ℓ) :
    Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) ℓ = 0 :=
  taylorShift_coeff_eq_zero_of_natDegree_lt
    Number.aperyQconifold Number.aperyConifoldZ1Poly ℓ
    (lt_of_le_of_lt aperyQconifold_natDegree_le (by omega))

/-- The natural degree of `aperyPconifold` is at most `4`. -/
lemma aperyPconifold_natDegree_le : Number.aperyPconifold.natDegree ≤ 4 := by
  unfold Number.aperyPconifold
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ?_ ?_
  · refine (Polynomial.natDegree_add_le _ _).trans ?_
    refine max_le ?_ ?_
    · exact (Polynomial.natDegree_monomial_le _).trans (by norm_num)
    · exact (Polynomial.natDegree_monomial_le _).trans (by norm_num)
  · exact Polynomial.natDegree_monomial_le _

/-- The constant Taylor coefficient of `aperyPconifold` shifted to the
conifold equals `p(z₁) = 0`. (`z₁` is a root of `p`.) -/
lemma aperyPconifold_taylorShift_coeff_zero :
    Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 0 = 0 := by
  rw [taylorShift_coeff_zero, Number.aperyPconifold_eval_z1]

/-- `|coeff (taylorShift P z₁) 0| = 0`. -/
lemma aperyPconifold_taylorShift_coeff_zero_abs :
    |Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 0| = 0 := by
  rw [aperyPconifold_taylorShift_coeff_zero, abs_zero]

/-- The first-order Taylor coefficient of `aperyPconifold` shifted to
the conifold equals `-p'(z₁)`. -/
lemma aperyPconifold_taylorShift_coeff_one :
    Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 1
      = - Polynomial.eval Number.aperyConifoldZ1Poly
          (Polynomial.derivative Number.aperyPconifold) :=
  taylorShift_coeff_one Number.aperyPconifold Number.aperyConifoldZ1Poly

/-- `|coeff (taylorShift P z₁) 1| = 13848·√2 − 19584`. This is the
key denominator in the ratio-test bound for the Frobenius series. -/
lemma aperyPconifold_taylorShift_coeff_one_abs :
    |Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 1|
      = 13848 * Real.sqrt 2 - 19584 := by
  rw [aperyPconifold_taylorShift_coeff_one, abs_neg,
      Number.aperyPconifold_deriv_eval_z1_abs]

/-- The second-order Taylor coefficient of `aperyPconifold` shifted to
the conifold equals `p''(z₁) / 2`. -/
lemma aperyPconifold_taylorShift_coeff_two :
    Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 2
      = Polynomial.eval Number.aperyConifoldZ1Poly
          (Polynomial.derivative (Polynomial.derivative Number.aperyPconifold))
        / 2 :=
  taylorShift_coeff_two Number.aperyPconifold Number.aperyConifoldZ1Poly

/-- `|coeff (taylorShift P z₁) 2| = 1224·√2 − 1729`. -/
lemma aperyPconifold_taylorShift_coeff_two_abs :
    |Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 2|
      = 1224 * Real.sqrt 2 - 1729 := by
  rw [aperyPconifold_taylorShift_coeff_two, abs_div,
      Number.aperyPconifold_deriv2_eval_z1_abs,
      show |(2 : ℝ)| = 2 from abs_of_pos (by norm_num)]
  ring

/-- The third-order Taylor coefficient of `aperyPconifold` shifted to
the conifold equals `-p'''(z₁) / 6`. -/
lemma aperyPconifold_taylorShift_coeff_three :
    Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 3
      = - Polynomial.eval Number.aperyConifoldZ1Poly
          (Polynomial.derivative (Polynomial.derivative
              (Polynomial.derivative Number.aperyPconifold))) / 6 :=
  taylorShift_coeff_three Number.aperyPconifold Number.aperyConifoldZ1Poly

/-- `|coeff (taylorShift P z₁) 3| = 48·√2 − 34`. -/
lemma aperyPconifold_taylorShift_coeff_three_abs :
    |Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 3|
      = 48 * Real.sqrt 2 - 34 := by
  rw [aperyPconifold_taylorShift_coeff_three, abs_div, abs_neg,
      Number.aperyPconifold_deriv3_eval_z1_abs,
      show |(6 : ℝ)| = 6 from abs_of_pos (by norm_num)]
  ring

/-- The fourth-order Taylor coefficient of `aperyPconifold` shifted to
the conifold equals `p''''(z₁) / 24 = 1`. -/
lemma aperyPconifold_taylorShift_coeff_four :
    Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 4
      = 1 := by
  rw [taylorShift_coeff_four, Number.aperyPconifold_deriv4_eval_z1]
  norm_num

/-- `|coeff (taylorShift P z₁) 4| = 1`. -/
lemma aperyPconifold_taylorShift_coeff_four_abs :
    |Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) 4| = 1 := by
  rw [aperyPconifold_taylorShift_coeff_four]
  norm_num

/-- For `ℓ ≥ 5`, the `ℓ`-th Taylor coefficient of `aperyPconifold`
shifted to the conifold vanishes. (P has degree at most `4`.) -/
lemma aperyPconifold_taylorShift_coeff_eq_zero_of_five_le
    {ℓ : ℕ} (hℓ : 5 ≤ ℓ) :
    Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) ℓ = 0 :=
  taylorShift_coeff_eq_zero_of_natDegree_lt
    Number.aperyPconifold Number.aperyConifoldZ1Poly ℓ
    (lt_of_le_of_lt aperyPconifold_natDegree_le (by omega))

/-- Uniform bound: for every `ℓ`, the `ℓ`-th Taylor coefficient of
`aperyQconifold` shifted to the conifold satisfies `|·| ≤ 153`. The
maximum `≈ 152.5` is attained at `ℓ = 2`. -/
lemma aperyQconifold_taylorShift_coeff_abs_le (ℓ : ℕ) :
    |Polynomial.coeff
        (taylorShift Number.aperyQconifold Number.aperyConifoldZ1Poly) ℓ|
      ≤ 153 := by
  by_cases hℓ : 4 ≤ ℓ
  · rw [aperyQconifold_taylorShift_coeff_eq_zero_of_four_le hℓ, abs_zero]
    norm_num
  push_neg at hℓ
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsqrt_pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  interval_cases ℓ
  · rw [aperyQconifold_taylorShift_coeff_zero_abs]
    linarith [sq_nonneg (20772 * Real.sqrt 2 - 29529), hsq, hsqrt_pos]
  · rw [aperyQconifold_taylorShift_coeff_one_abs]
    linarith [sq_nonneg (3672 * Real.sqrt 2 - 5340), hsq, hsqrt_pos]
  · rw [aperyQconifold_taylorShift_coeff_two_abs]
    linarith [sq_nonneg (216 * Real.sqrt 2 - 306), hsq, hsqrt_pos]
  · rw [aperyQconifold_taylorShift_coeff_three_abs]
    norm_num

/-- Uniform bound: for every `ℓ`, the `ℓ`-th Taylor coefficient of
`aperyPconifold` shifted to the conifold satisfies `|·| ≤ 153`. The
maximum `≈ 33.9` is attained at `ℓ = 3`. The bound `153` is chosen to
match the Q-side bound for downstream convenience. -/
lemma aperyPconifold_taylorShift_coeff_abs_le (ℓ : ℕ) :
    |Polynomial.coeff
        (taylorShift Number.aperyPconifold Number.aperyConifoldZ1Poly) ℓ|
      ≤ 153 := by
  by_cases hℓ : 5 ≤ ℓ
  · rw [aperyPconifold_taylorShift_coeff_eq_zero_of_five_le hℓ, abs_zero]
    norm_num
  push_neg at hℓ
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsqrt_pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  interval_cases ℓ
  · rw [aperyPconifold_taylorShift_coeff_zero_abs]
    norm_num
  · rw [aperyPconifold_taylorShift_coeff_one_abs]
    linarith [sq_nonneg (13848 * Real.sqrt 2 - 19737), hsq, hsqrt_pos]
  · rw [aperyPconifold_taylorShift_coeff_two_abs]
    linarith [sq_nonneg (1224 * Real.sqrt 2 - 1882), hsq, hsqrt_pos]
  · rw [aperyPconifold_taylorShift_coeff_three_abs]
    linarith [sq_nonneg (48 * Real.sqrt 2 - 187), hsq, hsqrt_pos]
  · rw [aperyPconifold_taylorShift_coeff_four_abs]
    norm_num

/-- **Per-coefficient weighted-sum bound for Q.**
`Σ_{ℓ=0}^3 |Q_ℓ|·2^ℓ ≤ 672`. The closed-form sum is `28980·√2 - 40314 ≈ 670`,
verified by `(40986 − 28980·√2)·(40986 + 28980·√2) = 171396 > 0`.

This is the natural sharpening of the uniform `B = 153` estimate: the
uniform bound replaces this Σ with `4·B·8 = 4896`, a factor `~7` looser.
A future refactor of `abs_frobeniusCoeff_succ_gronwall_uniform` to use
this weighted form will tighten the convergence threshold proportionally. -/
lemma aperyQconifold_taylorShift_weighted_sum_le :
    ∑ ℓ ∈ Finset.range 4,
        |Polynomial.coeff (taylorShift Number.aperyQconifold
          Number.aperyConifoldZ1Poly) ℓ| * (2 : ℝ) ^ ℓ ≤ 672 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             pow_zero, pow_one, mul_one,
             aperyQconifold_taylorShift_coeff_zero_abs,
             aperyQconifold_taylorShift_coeff_one_abs,
             aperyQconifold_taylorShift_coeff_two_abs,
             aperyQconifold_taylorShift_coeff_three_abs]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_factor :
      (40986 - 28980 * Real.sqrt 2) * (40986 + 28980 * Real.sqrt 2) = 171396 := by
    have hexpand : (40986 - 28980 * Real.sqrt 2) * (40986 + 28980 * Real.sqrt 2) =
        (40986 : ℝ)^2 - (28980 * Real.sqrt 2)^2 := by ring
    rw [hexpand, mul_pow, hsq]
    norm_num
  have h_sum_pos : 0 < 40986 + 28980 * Real.sqrt 2 := by positivity
  have h_diff_pos : 0 < 40986 - 28980 * Real.sqrt 2 := by
    nlinarith [h_factor, h_sum_pos]
  linarith [h_diff_pos]

/-- **Per-coefficient weighted-sum bound for P.**
`Σ_{ℓ=0}^4 |P_ℓ|·2^ℓ ≤ 300`. Closed-form sum is `32976·√2 - 46340 ≈ 299`,
verified by `(46640 − 32976·√2)·(46640 + 32976·√2) = 456448 > 0`. The
uniform `B = 153` estimate gives `5·153·16 = 12240` for the same sum,
a factor `~41` looser. Companion to `aperyQconifold_taylorShift_weighted_sum_le`. -/
lemma aperyPconifold_taylorShift_weighted_sum_le :
    ∑ ℓ ∈ Finset.range 5,
        |Polynomial.coeff (taylorShift Number.aperyPconifold
          Number.aperyConifoldZ1Poly) ℓ| * (2 : ℝ) ^ ℓ ≤ 300 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             pow_zero, pow_one, mul_one,
             aperyPconifold_taylorShift_coeff_zero_abs,
             aperyPconifold_taylorShift_coeff_one_abs,
             aperyPconifold_taylorShift_coeff_two_abs,
             aperyPconifold_taylorShift_coeff_three_abs,
             aperyPconifold_taylorShift_coeff_four_abs]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_factor :
      (46640 - 32976 * Real.sqrt 2) * (46640 + 32976 * Real.sqrt 2) = 456448 := by
    have hexpand : (46640 - 32976 * Real.sqrt 2) * (46640 + 32976 * Real.sqrt 2) =
        (46640 : ℝ)^2 - (32976 * Real.sqrt 2)^2 := by ring
    rw [hexpand, mul_pow, hsq]
    norm_num
  have h_sum_pos : 0 < 46640 + 32976 * Real.sqrt 2 := by positivity
  have h_diff_pos : 0 < 46640 - 32976 * Real.sqrt 2 := by
    nlinarith [h_factor, h_sum_pos]
  linarith [h_diff_pos]

/-- **Q weighted-sum extended to `Finset.range 5`.** Trivially extends
`aperyQconifold_taylorShift_weighted_sum_le` by adding the `ℓ = 4` term
which is `0` (since `Q` has degree `3`). Bridge for unifying Q and P
under a common range. -/
lemma aperyQconifold_taylorShift_weighted_sum_5_le :
    ∑ ℓ ∈ Finset.range 5,
        |Polynomial.coeff (taylorShift Number.aperyQconifold
          Number.aperyConifoldZ1Poly) ℓ| * (2 : ℝ) ^ ℓ ≤ 672 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, Finset.sum_range_succ]
  rw [aperyQconifold_taylorShift_coeff_eq_zero_of_four_le (le_refl 4),
      abs_zero, zero_mul, add_zero]
  exact aperyQconifold_taylorShift_weighted_sum_le

end Number.Frobenius
end Ripple
