import Ripple.Number.Hypergeometric.Clausen
import Ripple.Number.Modular.CMEvaluation163
import Ripple.Number.Modular.CMEvaluationTargets
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Period bridge for Gaussian hypergeometric functions

This file records the analytic interfaces needed to turn the remaining
Ramanujan and Chudnovsky `clausenGaussSq` CM evaluations into period and
Wronskian statements.

The statements are intentionally factored and named.  No axiom is introduced:
the remaining classical analytic theorems below stay as explicit proof
placeholders until the elliptic-period and Schwarz-map infrastructure is
formalized.
-/

noncomputable section

namespace Ripple
namespace Number
namespace Hypergeometric

open Complex Filter Bornology
open scoped Interval Topology

/-- The local branch domain for the Frobenius logarithm `log (i z)` inside the
unit disk. -/
private def gauss2F1FrobeniusBranchDomain : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ Complex.I * z ∈ Complex.slitPlane ∧ ‖z‖ < 1}

/-- Project-local abbreviation for Mathlib's ordinary Gaussian hypergeometric
function, specialized to complex parameters and argument. -/
noncomputable def gauss2F1 (a b c : ℂ) : ℂ → ℂ :=
  ordinaryHypergeometric a b c

/-- The digamma factor in the analytic Frobenius correction coefficients for
the logarithmic second solution of the degenerate `c = 1` equation. -/
noncomputable def gauss2F1SecondSolutionDigammaFactor (a b : ℂ) (n : ℕ) : ℂ :=
  Complex.digamma (a + n) - Complex.digamma a +
    (Complex.digamma (b + n) - Complex.digamma b) -
    2 * (Complex.digamma ((n : ℂ) + 1) - Complex.digamma 1)

/-- Coefficients of the analytic Frobenius correction in the logarithmic
second solution of the degenerate `c = 1` Gaussian hypergeometric equation. -/
noncomputable def gauss2F1SecondSolutionCoeff (a b : ℂ) (n : ℕ) : ℂ :=
  gauss2F1Coeff a b 1 n * gauss2F1SecondSolutionDigammaFactor a b n

/-- Normalization constant for the Frobenius logarithmic branch used in the
period Wronskian bridge. -/
noncomputable def gauss2F1SecondSolutionNorm (a b : ℂ) : ℂ :=
  Complex.Gamma a * Complex.Gamma b / (2 * (Real.pi : ℂ) * Complex.I)

/-- The logarithmic part alone, using the branch `log (i z)`.  Its cut is the
positive imaginary axis, so both positive and negative real CM arguments lie
on the same differentiability branch. -/
noncomputable def gauss2F1LogSecondPart (a b : ℂ) : ℂ → ℂ :=
  fun z => Complex.log (Complex.I * z) * gauss2F1 a b 1 z

/-- Analytic Frobenius correction term in the `c = 1` second local solution.
The summation starts at exponent `1`, as in the classical formula. -/
noncomputable def gauss2F1FrobeniusCorrection (a b : ℂ) : ℂ → ℂ :=
  fun z => ∑' n : ℕ, gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ (n + 1)

/-- Frobenius second local solution for the degenerate `c = 1`
hypergeometric equation:
`log (i z) * ₂F₁(a,b;1;z)` plus the analytic correction series. -/
noncomputable def gauss2F1SecondSolution (a b : ℂ) : ℂ → ℂ :=
  fun z => gauss2F1SecondSolutionNorm a b *
    (gauss2F1LogSecondPart a b z + gauss2F1FrobeniusCorrection a b z)

/-- Euler form of the second-order Gaussian hypergeometric differential
operator for `₂F₁(a,b;1;z)`. -/
noncomputable def gauss2F1Operator (a b : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * deriv (deriv f) z + (1 - (a + b + 1) * z) * deriv f z - a * b * f z

private lemma gauss2F1Operator_const_mul (a b c z : ℂ) (f : ℂ → ℂ) :
    gauss2F1Operator a b (fun w => c * f w) z =
      c * gauss2F1Operator a b f z := by
  unfold gauss2F1Operator
  simp [deriv_const_mul_field]
  ring

private lemma gauss2F1Operator_add
    (a b z : ℂ) (f g : ℂ → ℂ)
    (h₁ : deriv (fun w => f w + g w) z = deriv f z + deriv g z)
    (h₂ : deriv (deriv (fun w => f w + g w)) z =
      deriv (deriv f) z + deriv (deriv g) z) :
    gauss2F1Operator a b (fun w => f w + g w) z =
      gauss2F1Operator a b f z + gauss2F1Operator a b g z := by
  unfold gauss2F1Operator
  rw [h₂, h₁]
  ring

/-- The Legendre complete elliptic integral of the first kind,
with the principal complex power branch:

`K(k) = ∫₀^{π/2} (1 - k² sin² θ)^(-1/2) dθ`.
-/
noncomputable def ellipticK (k : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2,
    (1 - k ^ 2 * ((Real.sin θ : ℂ) ^ 2)) ^ (-(1 / 2 : ℂ))

@[simp] theorem ellipticK_zero :
    ellipticK 0 = ((Real.pi / 2 : ℝ) : ℂ) := by
  unfold ellipticK
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, sub_zero, Complex.one_cpow,
    intervalIntegral.integral_const]
  change ((Real.pi / 2 : ℝ) : ℂ) * 1 = ((Real.pi / 2 : ℝ) : ℂ)
  simp

@[simp] theorem gauss2F1_half_half_one_zero :
    gauss2F1 (1 / 2) (1 / 2) 1 0 = 1 := by
  simp [gauss2F1]

theorem gauss2F1_one_eq_tsum (a b z : ℂ) :
    gauss2F1 a b 1 z = ∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n := by
  rw [gauss2F1, ordinaryHypergeometric_eq_tsum]
  apply tsum_congr
  intro n
  rw [gauss2F1Coeff, ordinaryHypergeometricCoefficient]
  simp

theorem gauss2F1_half_half_one_eq_tsum (z : ℂ) :
    gauss2F1 (1 / 2) (1 / 2) 1 z =
      ∑' n : ℕ,
        ((ascPochhammer ℂ n).eval (1 / 2 : ℂ) *
            (ascPochhammer ℂ n).eval (1 / 2 : ℂ) /
          (Nat.factorial n : ℂ) ^ 2) * z ^ n := by
  rw [gauss2F1_one_eq_tsum]
  apply tsum_congr
  intro n
  rw [gauss2F1Coeff_one_eq]

theorem complex_gamma_half_sq :
    Complex.Gamma (1 / 2 : ℂ) ^ 2 = (Real.pi : ℂ) := by
  have hGamma : Complex.Gamma (1 / 2 : ℂ) = (Real.Gamma (1 / 2 : ℝ) : ℂ) := by
    have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [← hcast]
    exact Complex.Gamma_ofReal (1 / 2 : ℝ)
  calc
    Complex.Gamma (1 / 2 : ℂ) ^ 2 = ((Real.Gamma (1 / 2 : ℝ) : ℂ)) ^ 2 := by
      rw [hGamma]
    _ = (Real.Gamma (1 / 2 : ℝ) ^ 2 : ℂ) := by norm_num
    _ = (Real.pi : ℂ) := by
      rw [Real.Gamma_one_half_eq]
      rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_nonneg]

theorem betaIntegral_half_half_eq_pi :
    Complex.betaIntegral (1 / 2 : ℂ) (1 / 2 : ℂ) = (Real.pi : ℂ) := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div]
  · rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num]
    rw [Complex.Gamma_one]
    rw [← pow_two]
    simpa [one_div] using complex_gamma_half_sq
  · norm_num [Complex.ext_iff]
  · norm_num [Complex.ext_iff]

private lemma gamma_nat_add_half_eq_ascPochhammer (n : ℕ) :
    Complex.Gamma ((n : ℂ) + 1 / 2) =
      (ascPochhammer ℂ n).eval (1 / 2 : ℂ) * Complex.Gamma (1 / 2 : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [show ((n : ℂ) + 1) + 1 / 2 = ((n : ℂ) + 1 / 2) + 1 by ring]
      rw [Complex.Gamma_add_one]
      rw [ih]
      rw [ascPochhammer_succ_eval]
      ring
      intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      have hn : 0 ≤ (n : ℝ) := by positivity
      linarith

private lemma beta_half_coeff_eq_hypergeom_coeff (n : ℕ) :
    Ring.choose ((1 / 2 : ℂ) + n - 1) n *
        (Complex.betaIntegral ((n : ℂ) + 1 / 2) (1 / 2) / (Real.pi : ℂ)) =
      ((ascPochhammer ℂ n).eval (1 / 2 : ℂ) *
            (ascPochhammer ℂ n).eval (1 / 2 : ℂ) /
          (Nat.factorial n : ℂ) ^ 2) := by
  have hchoose : Ring.choose ((1 / 2 : ℂ) + n - 1) n =
      (ascPochhammer ℂ n).eval (1 / 2 : ℂ) / (Nat.factorial n : ℂ) := by
    have hmul := Ring.factorial_nsmul_multichoose_eq_ascPochhammer
      (R := ℂ) (1 / 2 : ℂ) n
    rw [Ring.multichoose_eq] at hmul
    replace hmul : (Nat.factorial n : ℂ) *
        Ring.choose ((1 / 2 : ℂ) + n - 1) n =
        (ascPochhammer ℂ n).eval (1 / 2 : ℂ) := by
      simpa [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] using hmul
    have hfac : (Nat.factorial n : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    rw [eq_div_iff hfac]
    rw [mul_comm]
    exact hmul
  have hbeta : Complex.betaIntegral ((n : ℂ) + 1 / 2) (1 / 2) / (Real.pi : ℂ) =
      (ascPochhammer ℂ n).eval (1 / 2 : ℂ) / (Nat.factorial n : ℂ) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div]
    rw [gamma_nat_add_half_eq_ascPochhammer]
    rw [show (n : ℂ) + 1 / 2 + 1 / 2 = (n : ℂ) + 1 by ring]
    rw [Complex.Gamma_nat_eq_factorial]
    have hhalf_sq : Complex.Gamma (1 / 2 : ℂ) * Complex.Gamma (1 / 2 : ℂ) =
        (Real.pi : ℂ) := by
      rw [← pow_two]
      exact complex_gamma_half_sq
    rw [← hhalf_sq]
    have hfac : (Nat.factorial n : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hgamma : Complex.Gamma (1 / 2 : ℂ) ≠ 0 := by
      rw [Complex.Gamma_one_half_eq]
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
    field_simp [hfac, hgamma]
    ring_nf
    · norm_num [Complex.ext_iff]
      positivity
    · norm_num [Complex.ext_iff]
  rw [hchoose, hbeta]
  ring_nf

private lemma eulerHalfKernel_seriesTerm_integral (z : ℂ) (n : ℕ) :
    (∫ t : ℝ in 0..1,
        (t : ℂ) ^ (-(1 / 2 : ℂ)) *
          (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) *
            (Ring.choose ((1 / 2 : ℂ) + n - 1) n * (z * (t : ℂ)) ^ n)) =
      Ring.choose ((1 / 2 : ℂ) + n - 1) n * z ^ n *
        Complex.betaIntegral ((n : ℂ) + 1 / 2) (1 / 2) := by
  rw [Complex.betaIntegral]
  calc
    (∫ t : ℝ in 0..1,
        (t : ℂ) ^ (-(1 / 2 : ℂ)) *
          (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) *
            (Ring.choose ((1 / 2 : ℂ) + n - 1) n * (z * (t : ℂ)) ^ n)) =
        ∫ t : ℝ in 0..1,
          (Ring.choose ((1 / 2 : ℂ) + n - 1) n * z ^ n) *
            ((t : ℂ) ^ ((n : ℂ) + 1 / 2 - 1) *
              (1 - (t : ℂ)) ^ ((1 / 2 : ℂ) - 1)) := by
      apply intervalIntegral.integral_congr_ae_restrict
      apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
      filter_upwards [Filter.self_mem_codiscreteWithin (Ι (0 : ℝ) 1)] with t ht
      have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have htpos : 0 < t := htIoc.1
      have htC_ne : (t : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt htpos
      rw [mul_pow]
      have ht_pow : (t : ℂ) ^ (-(1 / 2 : ℂ)) * (t : ℂ) ^ n =
          (t : ℂ) ^ ((n : ℂ) + 1 / 2 - 1) := by
        rw [← Complex.cpow_natCast (t : ℂ) n]
        rw [← Complex.cpow_add _ _ htC_ne]
        congr 1
        ring
      rw [show -(1 / 2 : ℂ) = (1 / 2 : ℂ) - 1 by ring]
      rw [← ht_pow]
      ring_nf
    _ = Ring.choose ((1 / 2 : ℂ) + n - 1) n * z ^ n *
          (∫ x : ℝ in 0..1,
            (x : ℂ) ^ ((n : ℂ) + 1 / 2 - 1) *
              (1 - (x : ℂ)) ^ ((1 / 2 : ℂ) - 1)) := by
      exact intervalIntegral.integral_const_mul
        (Ring.choose ((1 / 2 : ℂ) + n - 1) n * z ^ n)
        (fun x : ℝ =>
          (x : ℂ) ^ ((n : ℂ) + 1 / 2 - 1) *
            (1 - (x : ℂ)) ^ ((1 / 2 : ℂ) - 1))

theorem period_hypergeom_half_zero :
    gauss2F1 (1 / 2) (1 / 2) 1 ((0 : ℂ) ^ 2) =
      (2 / (Real.pi : ℂ)) * ellipticK 0 := by
  simp [gauss2F1]

/-- Legendre-family period normalized as
`ω₁(λ) = π * ₂F₁(1/2,1/2;1;λ)`. -/
noncomputable def legendrePeriod (lambda : ℂ) : ℂ :=
  (Real.pi : ℂ) * gauss2F1 (1 / 2) (1 / 2) 1 lambda

/-- Direct Wronskian computation for the logarithmic part alone,
`gauss2F1LogSecondPart a b z = log (i z) * gauss2F1 a b 1 z`.

This documents the computation from the earlier placeholder and is not the
classical Picard-Fuchs Wronskian for the genuine Frobenius second solution. -/
theorem hypergeom_logSecondSolution_wronskian
    (a b z : ℂ) (hz : Complex.I * z ∈ Complex.slitPlane)
    (hf : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z) :
    gauss2F1 a b 1 z * deriv (gauss2F1LogSecondPart a b) z -
      deriv (gauss2F1 a b 1) z * gauss2F1LogSecondPart a b z =
        gauss2F1 a b 1 z ^ 2 / z := by
  have hlog : HasDerivAt (fun w : ℂ => Complex.log (Complex.I * w)) z⁻¹ z := by
    have h := (Complex.hasDerivAt_log hz).comp z ((hasDerivAt_id z).const_mul Complex.I)
    convert h using 1
    field_simp [Complex.slitPlane_ne_zero hz]
  have hprod : HasDerivAt (gauss2F1LogSecondPart a b)
      (z⁻¹ * gauss2F1 a b 1 z +
        Complex.log (Complex.I * z) * deriv (gauss2F1 a b 1) z) z := by
    exact hlog.mul hf
  rw [hprod.deriv]
  simp [gauss2F1LogSecondPart]
  ring_nf

/-! ### Frobenius second-solution analytic gaps -/

/-- Analytic transport of the proved formal `₂F₁(a,b;1;z)` power-series
ODE to the differential-operator statement on the interior of the convergence
disk.  Proved via term-by-term differentiation + coefficient recurrence. -/

private lemma gauss2F1Series_radius_ge_one (a b : ℂ) :
    ((1 : NNReal) : ENNReal) ≤ (ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).radius := by
  by_cases ha : ∃ k : ℕ, (k : ℂ) = -a
  · rcases ha with ⟨k, hk⟩
    have hrewrite : a = -(k : ℂ) := by
      have hneg := congrArg Neg.neg hk
      simpa using hneg.symm
    rw [hrewrite, ordinaryHypergeometric_radius_top_of_neg_nat₁]
    simp
  · by_cases hb : ∃ k : ℕ, (k : ℂ) = -b
    · rcases hb with ⟨k, hk⟩
      have hrewrite : b = -(k : ℂ) := by
        have hneg := congrArg Neg.neg hk
        simpa using hneg.symm
      rw [hrewrite, ordinaryHypergeometric_radius_top_of_neg_nat₂]
      simp
    · have habc : ∀ kn : ℕ, (kn : ℂ) ≠ -a ∧ (kn : ℂ) ≠ -b ∧ (kn : ℂ) ≠ -(1 : ℂ) := by
        intro kn
        constructor
        · exact fun h => ha ⟨kn, h⟩
        constructor
        · exact fun h => hb ⟨kn, h⟩
        · intro h
          have hr := congrArg Complex.re h
          norm_num at hr
          have hkn : (0 : ℝ) ≤ kn := by exact_mod_cast Nat.zero_le kn
          linarith
      rw [ordinaryHypergeometricSeries_radius_eq_one ℂ a b (1 : ℂ) habc]
      simp

private lemma gauss2F1Series_radius_pos (a b : ℂ) :
    0 < (ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).radius := by
  exact zero_lt_one.trans_le (gauss2F1Series_radius_ge_one a b)

private lemma gamma_ne_zero_no_neg_nat {a : ℂ} (hGa : Complex.Gamma a ≠ 0) :
    ∀ m : ℕ, a ≠ -m := by
  intro m hm
  exact hGa ((Complex.Gamma_eq_zero_iff a).mpr ⟨m, hm⟩)

private lemma nat_add_one_ne_neg_nat (n : ℕ) :
    ∀ m : ℕ, ((n : ℂ) + 1) ≠ -m := by
  intro m hm
  have h := congrArg Complex.re hm
  norm_num at h
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hmnonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  linarith

private lemma nat_succ_cast_ne_zero (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  linarith

private lemma gamma_ne_zero_add_nat_ne_zero (a : ℂ) (n : ℕ)
    (hGa : Complex.Gamma a ≠ 0) : a + n ≠ 0 := by
  intro h
  have ha := gamma_ne_zero_no_neg_nat hGa n
  apply ha
  linear_combination h

private lemma inv_nat_add_tendsto_zero (a : ℂ) :
    Filter.Tendsto (fun n : ℕ => (a + n)⁻¹) atTop (𝓝 0) := by
  have hnat : Filter.Tendsto (fun n : ℕ => (n : ℂ)) atTop (cobounded ℂ) :=
    tendsto_natCast_atTop_cobounded
  have hadd : Filter.Tendsto (fun z : ℂ => a + z) (cobounded ℂ) (cobounded ℂ) :=
    tendsto_const_add_cobounded a
  exact Filter.tendsto_inv₀_cobounded.comp (hadd.comp hnat)

private lemma exists_pos_norm_inv_nat_add_le (a : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖(a + n)⁻¹‖ ≤ C := by
  have hbdd : Bornology.IsBounded (Set.range fun n : ℕ => (a + n)⁻¹) :=
    Metric.isBounded_range_of_tendsto _ (inv_nat_add_tendsto_zero a)
  rcases hbdd.exists_pos_norm_le with ⟨C, hCpos, hC⟩
  exact ⟨C, hCpos, fun n => hC _ ⟨n, rfl⟩⟩

private lemma gauss2F1SecondSolutionDigammaFactor_zero (a b : ℂ) :
    gauss2F1SecondSolutionDigammaFactor a b 0 = 0 := by
  simp [gauss2F1SecondSolutionDigammaFactor]

private lemma gauss2F1SecondSolutionCoeff_digamma_step
    (a b : ℂ) (n : ℕ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    gauss2F1SecondSolutionDigammaFactor a b (n + 1) -
      gauss2F1SecondSolutionDigammaFactor a b n =
      (a + n)⁻¹ + (b + n)⁻¹ - 2 * ((n : ℂ) + 1)⁻¹ := by
  have ha := gamma_ne_zero_no_neg_nat hGa
  have hb := gamma_ne_zero_no_neg_nat hGb
  have hda := Complex.digamma_apply_add_one (a + n) ?_
  · have hdb := Complex.digamma_apply_add_one (b + n) ?_
    · have hdn := Complex.digamma_apply_add_one ((n : ℂ) + 1)
        (nat_add_one_ne_neg_nat n)
      unfold gauss2F1SecondSolutionDigammaFactor
      rw [show a + (n + 1 : ℕ) = a + n + 1 by norm_num; ring]
      rw [show b + (n + 1 : ℕ) = b + n + 1 by norm_num; ring]
      rw [show (((n + 1 : ℕ) : ℂ) + 1) = ((n : ℂ) + 1) + 1 by norm_num]
      rw [hda, hdb, hdn]
      ring
    · intro m hm
      have hbzero : b = -(n + m : ℕ) := by
        have h : b = -((n : ℂ) + m) := by linear_combination hm
        simpa [Nat.cast_add] using h
      exact hb (n + m) hbzero
  · intro m hm
    have hazero : a = -(n + m : ℕ) := by
      have h : a = -((n : ℂ) + m) := by linear_combination hm
      simpa [Nat.cast_add] using h
    exact ha (n + m) hazero

private lemma gauss2F1SecondSolutionDigammaFactor_norm_le_linear
    (a b : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖gauss2F1SecondSolutionDigammaFactor a b n‖ ≤ C * ((n : ℝ) + 1) := by
  rcases exists_pos_norm_inv_nat_add_le a with ⟨Ca, hCa_pos, hCa⟩
  rcases exists_pos_norm_inv_nat_add_le b with ⟨Cb, hCb_pos, hCb⟩
  rcases exists_pos_norm_inv_nat_add_le (1 : ℂ) with ⟨C1, hC1_pos, hC1⟩
  let C : ℝ := Ca + Cb + 2 * C1
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro n
  induction n with
  | zero =>
      simp [gauss2F1SecondSolutionDigammaFactor_zero, hC_pos.le]
  | succ n ih =>
      let inc : ℂ := (a + n)⁻¹ + (b + n)⁻¹ - 2 * ((n : ℂ) + 1)⁻¹
      have hstep := gauss2F1SecondSolutionCoeff_digamma_step a b n hGa hGb
      have hq :
          gauss2F1SecondSolutionDigammaFactor a b (n + 1) =
            gauss2F1SecondSolutionDigammaFactor a b n + inc := by
        dsimp [inc]
        linear_combination hstep
      have hone : ‖(((n : ℂ) + 1)⁻¹)‖ ≤ C1 := by
        have h := hC1 n
        simpa [add_comm] using h
      have htwo : ‖(2 : ℂ) * (((n : ℂ) + 1)⁻¹)‖ ≤ 2 * C1 := by
        rw [norm_mul]
        have hnorm_two : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [hnorm_two]
        linarith [hone]
      have hinc : ‖inc‖ ≤ C := by
        calc
          ‖inc‖ ≤ ‖(a + n)⁻¹ + (b + n)⁻¹‖ +
              ‖(2 : ℂ) * (((n : ℂ) + 1)⁻¹)‖ := by
                dsimp [inc]
                exact norm_sub_le _ _
          _ ≤ (‖(a + n)⁻¹‖ + ‖(b + n)⁻¹‖) +
              ‖(2 : ℂ) * (((n : ℂ) + 1)⁻¹)‖ := by
                linarith [norm_add_le (a + n)⁻¹ (b + n)⁻¹]
          _ ≤ C := by
                dsimp [C]
                linarith [hCa n, hCb n, htwo]
      calc
        ‖gauss2F1SecondSolutionDigammaFactor a b (n + 1)‖
            = ‖gauss2F1SecondSolutionDigammaFactor a b n + inc‖ := by rw [hq]
        _ ≤ ‖gauss2F1SecondSolutionDigammaFactor a b n‖ + ‖inc‖ := norm_add_le _ _
        _ ≤ C * ((n : ℝ) + 1) + C := by linarith
        _ = C * (((n + 1 : ℕ) : ℝ) + 1) := by
              norm_num
              ring

private lemma gauss2F1SecondSolutionCoeff_recurrence_alg
    (A B u C Cs : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hu : u ≠ 0)
    (hrec : u ^ 2 * Cs = A * B * C) :
    A * B * C * (A⁻¹ + B⁻¹ - 2 * u⁻¹) =
      (A + B) * C - 2 * u * Cs := by
  calc
    A * B * C * (A⁻¹ + B⁻¹ - 2 * u⁻¹)
        = B * C + A * C - 2 * (A * B * C) * u⁻¹ := by
          field_simp [hA, hB]
    _ = B * C + A * C - 2 * (u ^ 2 * Cs) * u⁻¹ := by rw [hrec]
    _ = (A + B) * C - 2 * u * Cs := by
          field_simp [hu]
          ring

private lemma gauss2F1SecondSolutionCoeff_recurrence
    (a b : ℂ) (n : ℕ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    ((n + 1 : ℕ) : ℂ) ^ 2 * gauss2F1SecondSolutionCoeff a b (n + 1) -
      (a + n) * (b + n) * gauss2F1SecondSolutionCoeff a b n =
      (((2 : ℂ) * n + a + b) * gauss2F1Coeff a b 1 n -
        2 * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1)) := by
  let A : ℂ := a + n
  let B : ℂ := b + n
  let u : ℂ := (n : ℂ) + 1
  let C : ℂ := gauss2F1Coeff a b 1 n
  let Cs : ℂ := gauss2F1Coeff a b 1 (n + 1)
  let q : ℂ := gauss2F1SecondSolutionDigammaFactor a b n
  let qs : ℂ := gauss2F1SecondSolutionDigammaFactor a b (n + 1)
  have hrec : u ^ 2 * Cs = A * B * C := by
    dsimp [A, B, C, Cs, u]
    simpa using gauss2F1Coeff_succ_one a b n
  have hq : qs - q = A⁻¹ + B⁻¹ - 2 * u⁻¹ := by
    dsimp [A, B, u, q, qs]
    simpa using gauss2F1SecondSolutionCoeff_digamma_step a b n hGa hGb
  have hA : A ≠ 0 := by simpa [A] using gamma_ne_zero_add_nat_ne_zero a n hGa
  have hB : B ≠ 0 := by simpa [B] using gamma_ne_zero_add_nat_ne_zero b n hGb
  have hu : u ≠ 0 := by simpa [u] using nat_succ_cast_ne_zero n
  have hfirst :
      u ^ 2 * (Cs * qs) - A * B * (C * q) = A * B * C * (qs - q) := by
    calc
      u ^ 2 * (Cs * qs) - A * B * (C * q)
          = (u ^ 2 * Cs) * qs - A * B * C * q := by ring
      _ = (A * B * C) * qs - A * B * C * q := by rw [hrec]
      _ = A * B * C * (qs - q) := by ring
  have hsecond : A * B * C * (qs - q) = (A + B) * C - 2 * u * Cs := by
    rw [hq]
    exact gauss2F1SecondSolutionCoeff_recurrence_alg A B u C Cs hA hB hu hrec
  simp [gauss2F1SecondSolutionCoeff]
  change u ^ 2 * (Cs * qs) - A * B * (C * q) =
    ((2 : ℂ) * n + a + b) * C - 2 * u * Cs
  rw [hfirst, hsecond]
  congr 1
  dsimp [A, B]
  ring

/-- Formal power series for the analytic Frobenius correction term. -/
noncomputable def gauss2F1FrobeniusCorrectionPS (a b : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (gauss2F1SecondSolutionCoeff a b)

/-- Formal multilinear series for the analytic Frobenius correction term. -/
noncomputable def gauss2F1FrobeniusCorrectionFMLS (a b : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (gauss2F1SecondSolutionCoeff a b)

@[simp] private lemma coeff_gauss2F1FrobeniusCorrectionPS (a b : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (gauss2F1FrobeniusCorrectionPS a b) =
      gauss2F1SecondSolutionCoeff a b n := by
  simp [gauss2F1FrobeniusCorrectionPS]

private lemma gauss2F1FrobeniusCorrectionPS_inhom_ode
    (a b : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    psTheta (psTheta (gauss2F1FrobeniusCorrectionPS a b)) =
      PowerSeries.X *
          ((psTheta (psTheta (gauss2F1FrobeniusCorrectionPS a b)) +
              PowerSeries.C (a + b) * psTheta (gauss2F1FrobeniusCorrectionPS a b)) +
            PowerSeries.C (a * b) * gauss2F1FrobeniusCorrectionPS a b) +
        PowerSeries.C (a + b) * PowerSeries.X * gauss2F1SeriesPS a b -
        PowerSeries.C 2 *
          (psTheta (gauss2F1SeriesPS a b) -
            PowerSeries.X * psTheta (gauss2F1SeriesPS a b)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [psTheta]
  | succ n =>
      simp only [map_add, map_sub, coeff_psTheta, coeff_gauss2F1FrobeniusCorrectionPS,
        coeff_gauss2F1SeriesPS, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      rw [show (PowerSeries.C a + PowerSeries.C b : PowerSeries ℂ) =
        PowerSeries.C (a + b) by simp]
      rw [PowerSeries.coeff_C_mul]
      rw [coeff_psTheta]
      rw [show PowerSeries.C (a + b) * PowerSeries.X * gauss2F1SeriesPS a b =
        PowerSeries.C (a + b) * (PowerSeries.X * gauss2F1SeriesPS a b) by ring]
      rw [PowerSeries.coeff_C_mul]
      rw [PowerSeries.coeff_succ_X_mul]
      rw [coeff_gauss2F1FrobeniusCorrectionPS, coeff_gauss2F1SeriesPS]
      have hrec := gauss2F1SecondSolutionCoeff_recurrence a b n hGa hGb
      calc
        ((n + 1 : ℕ) : ℂ) *
            (((n + 1 : ℕ) : ℂ) * gauss2F1SecondSolutionCoeff a b (n + 1))
            = (a + n) * (b + n) * gauss2F1SecondSolutionCoeff a b n +
                ((2 : ℂ) * n + a + b) * gauss2F1Coeff a b 1 n -
                2 * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) := by
              linear_combination hrec
        _ = (n : ℂ) * ((n : ℂ) * gauss2F1SecondSolutionCoeff a b n) +
              (a + b) * ((n : ℂ) * gauss2F1SecondSolutionCoeff a b n) +
              a * b * gauss2F1SecondSolutionCoeff a b n +
              (a + b) * gauss2F1Coeff a b 1 n -
              2 * (((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) -
                (n : ℂ) * gauss2F1Coeff a b 1 n) := by
            ring

private lemma gauss2F1_derivSeries_term (a b z : ℂ) (n : ℕ) :
    (((ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).derivSeries n) (fun _ => z)) 1 =
      ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  change z ^ n * ((((ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).derivSeries).coeff n) 1) =
    ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  simp only [nsmul_eq_mul]
  rw [(by
    simp [gauss2F1Coeff, ordinaryHypergeometricSeries] :
      (ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).coeff (n + 1) =
        gauss2F1Coeff a b 1 (n + 1))]
  ring_nf

private lemma gauss2F1_abs_series_summable_of_norm_lt_one
    (a b z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖gauss2F1Coeff a b 1 n * z ^ n‖ := by
  let p := ordinaryHypergeometricSeries ℂ a b (1 : ℂ)
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1Series_radius_ge_one a b)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_ball : z ∈ Metric.eball (0 : ℂ) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem
  have hs := p.summable_norm_apply hmem_ball
  convert hs using 1
  ext n
  rw [ordinaryHypergeometricSeries_apply_eq]
  simp [gauss2F1Coeff, ordinaryHypergeometricCoefficient]

private lemma gauss2F1_abs_theta1_summable_of_norm_lt_one
    (a b z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖(n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n‖ := by
  let p := ordinaryHypergeometricSeries ℂ a b (1 : ℂ)
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1Series_radius_ge_one a b)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_deriv_ball : z ∈ Metric.eball (0 : ℂ) p.derivSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem.trans_le p.radius_le_radius_derivSeries
  have hs_deriv : Summable fun n : ℕ =>
      ‖((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n‖ := by
    have hs := p.derivSeries.summable_norm_apply hmem_deriv_ball
    have hs_apply : Summable fun n : ℕ => ‖((p.derivSeries n (fun _ => z)) 1 : ℂ)‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hs
      intro n
      simpa using (p.derivSeries n (fun _ => z)).le_opNorm (1 : ℂ)
    convert hs_apply using 1
    ext n
    simpa [p] using congrArg norm (gauss2F1_derivSeries_term a b z n).symm
  let f : ℕ → ℝ := fun n => ‖(n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n‖
  have htail : Summable fun n : ℕ => f (n + 1) := by
    convert hs_deriv.mul_left ‖z‖ using 1
    ext n
    change ‖(((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ (n + 1))‖ =
      ‖z‖ * ‖((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n‖
    rw [pow_succ]
    have hmul :
        ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * (z ^ n * z) =
          (((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n) * z := by
      ring
    rw [hmul, norm_mul, mul_comm]
  exact (summable_nat_add_iff 1).mp htail

private lemma gauss2F1SecondSolutionCoeff_abs_series_summable_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖gauss2F1SecondSolutionCoeff a b n * z ^ n‖ := by
  rcases gauss2F1SecondSolutionDigammaFactor_norm_le_linear a b hGa hGb with
    ⟨C, hCpos, hC⟩
  have hs0 := gauss2F1_abs_series_summable_of_norm_lt_one a b z hz
  have hs1 := gauss2F1_abs_theta1_summable_of_norm_lt_one a b z hz
  have hsg : Summable fun n : ℕ =>
      C * (‖(n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n‖ +
        ‖gauss2F1Coeff a b 1 n * z ^ n‖) :=
    (hs1.add hs0).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hsg
  intro n
  let q := gauss2F1SecondSolutionDigammaFactor a b n
  let base := gauss2F1Coeff a b 1 n * z ^ n
  have hbase_nonneg : 0 ≤ ‖base‖ := norm_nonneg _
  have hq_bound : ‖q‖ ≤ C * ((n : ℝ) + 1) := by
    simpa [q] using hC n
  have htheta :
      ‖(n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n‖ = (n : ℝ) * ‖base‖ := by
    have hmul :
        (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n =
          (n : ℂ) * (gauss2F1Coeff a b 1 n * z ^ n) := by
      ring
    rw [hmul, norm_mul, Complex.norm_natCast]
  calc
    ‖gauss2F1SecondSolutionCoeff a b n * z ^ n‖
        = ‖base * q‖ := by
            simp [gauss2F1SecondSolutionCoeff, q, base]
            ring
    _ = ‖base‖ * ‖q‖ := by rw [norm_mul]
    _ ≤ ‖base‖ * (C * ((n : ℝ) + 1)) := by
          gcongr
    _ = C * ((n : ℝ) * ‖base‖ + ‖base‖) := by ring
    _ = C * (‖(n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n‖ + ‖base‖) := by
          rw [htheta]
    _ = C * (‖(n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n‖ +
          ‖gauss2F1Coeff a b 1 n * z ^ n‖) := by
          rfl

private lemma gauss2F1FrobeniusCorrectionFMLS_radius_ge_one
    (a b : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    (1 : ENNReal) ≤ (gauss2F1FrobeniusCorrectionFMLS a b).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  let z : ℂ := (r : ℝ)
  have hz : ‖z‖ < 1 := by
    rw [show ‖z‖ = (r : ℝ) by
      dsimp [z]
      exact Complex.norm_of_nonneg r.coe_nonneg]
    have hr' : (r : ENNReal) < ((1 : NNReal) : ENNReal) := by simpa using hr
    exact ENNReal.coe_lt_coe.mp hr'
  have hs :=
    gauss2F1SecondSolutionCoeff_abs_series_summable_of_norm_lt_one a b z hGa hGb hz
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  convert hs using 1
  ext n
  rw [gauss2F1FrobeniusCorrectionFMLS, FormalMultilinearSeries.ofScalars_norm]
  have hzpow : ‖z ^ n‖ = (r : ℝ) ^ n := by
    rw [norm_pow]
    dsimp [z]
    rw [Complex.norm_of_nonneg r.coe_nonneg]
  rw [norm_mul, hzpow]

private lemma gauss2F1SecondSolutionCoeff_series_summable_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => gauss2F1SecondSolutionCoeff a b n * z ^ n :=
  (gauss2F1SecondSolutionCoeff_abs_series_summable_of_norm_lt_one
    a b z hGa hGb hz).of_norm

private lemma gauss2F1FrobeniusCorrection_eq_fmls_sum_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    gauss2F1FrobeniusCorrection a b z =
      (gauss2F1FrobeniusCorrectionFMLS a b).sum z := by
  let d : ℕ → ℂ := gauss2F1SecondSolutionCoeff a b
  have hs : Summable fun n : ℕ => d n * z ^ n := by
    simpa [d] using gauss2F1SecondSolutionCoeff_series_summable_of_norm_lt_one
      a b z hGa hGb hz
  have hsum : (gauss2F1FrobeniusCorrectionFMLS a b).sum z =
      ∑' n : ℕ, d n * z ^ n := by
    dsimp [gauss2F1FrobeniusCorrectionFMLS, d]
    change FormalMultilinearSeries.ofScalarsSum (E := ℂ)
      (gauss2F1SecondSolutionCoeff a b) z =
        ∑' n : ℕ, gauss2F1SecondSolutionCoeff a b n * z ^ n
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    apply tsum_congr
    intro n
    simp [d, smul_eq_mul]
  rw [hsum]
  unfold gauss2F1FrobeniusCorrection
  rw [hs.tsum_eq_zero_add]
  have h0 : d 0 * z ^ 0 = 0 := by
    simp [d, gauss2F1SecondSolutionCoeff, gauss2F1SecondSolutionDigammaFactor_zero]
  rw [h0, zero_add]

private lemma gauss2F1FrobeniusCorrection_eventually_eq_fmls_sum
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    gauss2F1FrobeniusCorrection a b =ᶠ[𝓝 z]
      (gauss2F1FrobeniusCorrectionFMLS a b).sum := by
  have hopen : IsOpen {w : ℂ | ‖w‖ < 1} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact gauss2F1FrobeniusCorrection_eq_fmls_sum_of_norm_lt_one a b w hGa hGb hw

private lemma gauss2F1FrobeniusCorrection_derivSeries_term
    (a b z : ℂ) (n : ℕ) :
    (((gauss2F1FrobeniusCorrectionFMLS a b).derivSeries n) (fun _ => z)) 1 =
      ((n + 1 : ℕ) : ℂ) * gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  change z ^ n * ((((gauss2F1FrobeniusCorrectionFMLS a b).derivSeries).coeff n) 1) =
    ((n + 1 : ℕ) : ℂ) * gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  simp only [nsmul_eq_mul]
  rw [(by
    simp [gauss2F1FrobeniusCorrectionFMLS, FormalMultilinearSeries.coeff_ofScalars] :
      (gauss2F1FrobeniusCorrectionFMLS a b).coeff (n + 1) =
        gauss2F1SecondSolutionCoeff a b (n + 1))]
  ring_nf

private lemma gauss2F1FrobeniusCorrection_hasDerivAt_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    HasDerivAt (gauss2F1FrobeniusCorrection a b)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
        gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n) z := by
  let p := gauss2F1FrobeniusCorrectionFMLS a b
  have hrpos : 0 < p.radius := by
    exact zero_lt_one.trans_le (gauss2F1FrobeniusCorrectionFMLS_radius_ge_one a b hGa hGb)
  have hps : HasFPowerSeriesOnBall p.sum p 0 p.radius := p.hasFPowerSeriesOnBall hrpos
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1FrobeniusCorrectionFMLS_radius_ge_one a b hGa hGb)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_ball : z ∈ Metric.eball (0 : ℂ) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem
  have hmem_deriv_ball : z ∈ Metric.eball (0 : ℂ) p.derivSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem.trans_le p.radius_le_radius_derivSeries
  have hfd_series : fderiv ℂ p.sum z = p.derivSeries.sum z := by
    simpa [zero_add] using hps.fderiv.sum (y := z) hmem_ball
  have hfd := hps.hasFDerivAt (x := 0) (y := z) hmem
  have hcurry_eq : ((continuousMultilinearCurryFin1 ℂ ℂ ℂ) (p.changeOrigin z 1)) 1 =
      ((p.derivSeries.sum z : ℂ →L[ℂ] ℂ) 1) := by
    have hfd_eq := hfd.fderiv
    rw [zero_add] at hfd_eq
    rw [← hfd_eq, hfd_series]
  have hderiv_sum : HasDerivAt p.sum (((p.derivSeries.sum z) : ℂ →L[ℂ] ℂ) 1) z := by
    simpa [zero_add, hcurry_eq] using hfd.hasDerivAt
  have happly : (((p.derivSeries.sum z) : ℂ →L[ℂ] ℂ) 1) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
        gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n := by
    unfold FormalMultilinearSeries.sum
    rw [show ((∑' n : ℕ, p.derivSeries n fun _ => z) : ℂ →L[ℂ] ℂ) 1 =
        (∑' n : ℕ, ((p.derivSeries n (fun _ => z)) 1 : ℂ)) by
      exact ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ) :
        (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ).map_tsum
          (p.derivSeries.summable hmem_deriv_ball))]
    apply tsum_congr
    intro n
    simpa [p] using gauss2F1FrobeniusCorrection_derivSeries_term a b z n
  rw [← happly]
  exact hderiv_sum.congr_of_eventuallyEq
    (gauss2F1FrobeniusCorrection_eventually_eq_fmls_sum a b z hGa hGb hz)

private lemma gauss2F1FrobeniusCorrection_deriv_eventually_eq_fderiv_sum
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    (fun w : ℂ => deriv (gauss2F1FrobeniusCorrection a b) w) =ᶠ[𝓝 z]
      fun w : ℂ =>
        ((fderiv ℂ (gauss2F1FrobeniusCorrectionFMLS a b).sum w : ℂ →L[ℂ] ℂ) 1) := by
  let p := gauss2F1FrobeniusCorrectionFMLS a b
  have hrpos : 0 < p.radius := by
    exact zero_lt_one.trans_le (gauss2F1FrobeniusCorrectionFMLS_radius_ge_one a b hGa hGb)
  have hps : HasFPowerSeriesOnBall p.sum p 0 p.radius := p.hasFPowerSeriesOnBall hrpos
  have hopen : IsOpen {w : ℂ | ‖w‖ < 1} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  have hmem : ((‖w‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1FrobeniusCorrectionFMLS_radius_ge_one a b hGa hGb)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hw : ‖w‖₊ < (1 : NNReal))
  have hderiv_sum : HasDerivAt p.sum (deriv p.sum w) w := by
    simpa [zero_add] using
      (hps.hasFDerivAt (x := 0) (y := w) hmem).differentiableAt.hasDerivAt
  have hderiv_corr : HasDerivAt (gauss2F1FrobeniusCorrection a b) (deriv p.sum w) w :=
    hderiv_sum.congr_of_eventuallyEq
      (gauss2F1FrobeniusCorrection_eventually_eq_fmls_sum a b w hGa hGb hw)
  rw [hderiv_corr.deriv]
  rfl

private lemma gauss2F1FrobeniusCorrection_hasSecondDerivAt_series_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    HasDerivAt (deriv (gauss2F1FrobeniusCorrection a b))
      (((((gauss2F1FrobeniusCorrectionFMLS a b).derivSeries.derivSeries.sum z) :
        ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) 1) 1) z := by
  let p := gauss2F1FrobeniusCorrectionFMLS a b
  have hrpos : 0 < p.radius := by
    exact zero_lt_one.trans_le (gauss2F1FrobeniusCorrectionFMLS_radius_ge_one a b hGa hGb)
  have hps : HasFPowerSeriesOnBall p.sum p 0 p.radius := p.hasFPowerSeriesOnBall hrpos
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1FrobeniusCorrectionFMLS_radius_ge_one a b hGa hGb)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hfdps : HasFPowerSeriesOnBall (fderiv ℂ p.sum) p.derivSeries 0 p.radius := hps.fderiv
  have hfd2ps := hfdps.fderiv
  have hmem_ball : z ∈ Metric.eball (0 : ℂ) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem
  have hfd2sum : fderiv ℂ (fderiv ℂ p.sum) z = p.derivSeries.derivSeries.sum z := by
    simpa [zero_add] using hfd2ps.sum (y := z) hmem_ball
  have hdiff_fd : DifferentiableAt ℂ (fderiv ℂ p.sum) z := by
    simpa [zero_add] using (hfdps.hasFDerivAt (x := 0) (y := z) hmem).differentiableAt
  have hbase : HasDerivAt
      (fun y : ℂ => ((fderiv ℂ p.sum y : ℂ →L[ℂ] ℂ) 1))
      ((((fderiv ℂ (fderiv ℂ p.sum) z : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) 1) 1)) z := by
    simpa using hdiff_fd.hasDerivAt.clm_apply (hasDerivAt_const (x := z) (c := (1 : ℂ)))
  convert hbase.congr_of_eventuallyEq
    (gauss2F1FrobeniusCorrection_deriv_eventually_eq_fderiv_sum a b z hGa hGb hz) using 1
  rw [hfd2sum]

private lemma gauss2F1FrobeniusCorrection_secondDerivSeries_term
    (a b z : ℂ) (n : ℕ) :
    (((((gauss2F1FrobeniusCorrectionFMLS a b).derivSeries.derivSeries n)
        (fun _ => z)) 1) 1) =
      ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n := by
  let p := gauss2F1FrobeniusCorrectionFMLS a b
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  change ((z ^ n • (((p.derivSeries.derivSeries).coeff n))) 1) 1 =
    ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
      gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  rw [ContinuousLinearMap.smul_apply]
  rw [(by
    rw [FormalMultilinearSeries.derivSeries_coeff_one]
    simp only [nsmul_eq_mul] :
      p.derivSeries.coeff (n + 1) 1 = ((n + 2 : ℕ) : ℂ) * p.coeff (n + 2))]
  rw [(by
    simp [gauss2F1FrobeniusCorrectionFMLS, FormalMultilinearSeries.coeff_ofScalars] :
      (gauss2F1FrobeniusCorrectionFMLS a b).coeff (n + 2) =
        gauss2F1SecondSolutionCoeff a b (n + 2))]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring_nf

private lemma gauss2F1FrobeniusCorrection_hasSecondDerivAt_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    HasDerivAt (deriv (gauss2F1FrobeniusCorrection a b))
      (∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n) z := by
  let p := gauss2F1FrobeniusCorrectionFMLS a b
  have hbase :=
    gauss2F1FrobeniusCorrection_hasSecondDerivAt_series_of_norm_lt_one a b z hGa hGb hz
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1FrobeniusCorrectionFMLS_radius_ge_one a b hGa hGb)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_second_ball : z ∈ Metric.eball (0 : ℂ) p.derivSeries.derivSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem.trans_le ((p.radius_le_radius_derivSeries).trans
      p.derivSeries.radius_le_radius_derivSeries)
  have happly : (((p.derivSeries.derivSeries.sum z : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) 1) 1) =
      ∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n := by
    unfold FormalMultilinearSeries.sum
    rw [show (((∑' n : ℕ, p.derivSeries.derivSeries n fun _ => z) :
          ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) 1) 1 =
        (∑' n : ℕ, ((((p.derivSeries.derivSeries n (fun _ => z)) 1) 1 : ℂ))) by
      let L₁ : (ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) →L[ℂ] (ℂ →L[ℂ] ℂ) :=
        ContinuousLinearMap.apply ℂ (ℂ →L[ℂ] ℂ) (1 : ℂ)
      let L₂ : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
        ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
      change (L₂ (L₁ (∑' n : ℕ, p.derivSeries.derivSeries n fun _ => z))) =
        ∑' n : ℕ, L₂ (L₁ (p.derivSeries.derivSeries n fun _ => z))
      rw [L₁.map_tsum (p.derivSeries.derivSeries.summable hmem_second_ball)]
      exact L₂.map_tsum ((p.derivSeries.derivSeries.summable hmem_second_ball).map
        L₁ L₁.continuous)]
    apply tsum_congr
    intro n
    simpa [p] using gauss2F1FrobeniusCorrection_secondDerivSeries_term a b z n
  rw [← happly]
  simpa [p] using hbase

private lemma gauss2F1_hasDerivAt_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    HasDerivAt (gauss2F1 a b 1)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n) z := by
  let p := ordinaryHypergeometricSeries ℂ a b (1 : ℂ)
  have hps : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (gauss2F1Series_radius_pos a b)
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1Series_radius_ge_one a b)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_ball : z ∈ Metric.eball (0 : ℂ) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem
  have hmem_deriv_ball : z ∈ Metric.eball (0 : ℂ) p.derivSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem.trans_le p.radius_le_radius_derivSeries
  have hfd_series : fderiv ℂ p.sum z = p.derivSeries.sum z := by
    simpa [zero_add] using hps.fderiv.sum (y := z) hmem_ball
  have hfd := hps.hasFDerivAt (x := 0) (y := z) hmem
  have hcurry_eq : ((continuousMultilinearCurryFin1 ℂ ℂ ℂ) (p.changeOrigin z 1)) 1 =
      ((p.derivSeries.sum z : ℂ →L[ℂ] ℂ) 1) := by
    have hfd_eq := hfd.fderiv
    rw [zero_add] at hfd_eq
    rw [← hfd_eq, hfd_series]
  have hderiv : HasDerivAt p.sum (((p.derivSeries.sum z) : ℂ →L[ℂ] ℂ) 1) z := by
    simpa [zero_add, hcurry_eq] using hfd.hasDerivAt
  have happly : (((p.derivSeries.sum z) : ℂ →L[ℂ] ℂ) 1) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n := by
    unfold FormalMultilinearSeries.sum
    rw [show ((∑' n : ℕ, p.derivSeries n fun _ => z) : ℂ →L[ℂ] ℂ) 1 =
        (∑' n : ℕ, ((p.derivSeries n (fun _ => z)) 1 : ℂ)) by
      exact ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ) :
        (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ).map_tsum
          (p.derivSeries.summable hmem_deriv_ball))]
    apply tsum_congr
    intro n
    simpa [p] using gauss2F1_derivSeries_term a b z n
  rw [← happly]
  simpa [gauss2F1, p, ordinaryHypergeometric] using hderiv

private lemma gauss2F1_hasSecondDerivAt_series_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    HasDerivAt (deriv (gauss2F1 a b 1))
      (((((ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).derivSeries.derivSeries.sum z) :
        ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) 1) 1) z := by
  let p := ordinaryHypergeometricSeries ℂ a b (1 : ℂ)
  have hps : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (gauss2F1Series_radius_pos a b)
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1Series_radius_ge_one a b)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hfdps : HasFPowerSeriesOnBall (fderiv ℂ p.sum) p.derivSeries 0 p.radius := hps.fderiv
  have hfd2ps := hfdps.fderiv
  have hmem_ball : z ∈ Metric.eball (0 : ℂ) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem
  have hfd2sum : fderiv ℂ (fderiv ℂ p.sum) z = p.derivSeries.derivSeries.sum z := by
    simpa [zero_add] using hfd2ps.sum (y := z) hmem_ball
  have hdiff_fd : DifferentiableAt ℂ (fderiv ℂ p.sum) z := by
    simpa [zero_add] using (hfdps.hasFDerivAt (x := 0) (y := z) hmem).differentiableAt
  have hderiv_eq : deriv (gauss2F1 a b 1) =
      fun y => ((fderiv ℂ p.sum y : ℂ →L[ℂ] ℂ) 1) := by
    funext y
    rfl
  rw [hderiv_eq]
  have happly : HasDerivAt (fun y => ((fderiv ℂ p.sum y : ℂ →L[ℂ] ℂ) 1))
      ((((fderiv ℂ (fderiv ℂ p.sum) z : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) 1) 1)) z := by
    simpa using hdiff_fd.hasDerivAt.clm_apply (hasDerivAt_const (x := z) (c := (1 : ℂ)))
  convert happly using 1
  rw [hfd2sum]

private lemma gauss2F1_secondDerivSeries_term (a b z : ℂ) (n : ℕ) :
    (((((ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).derivSeries.derivSeries n)
        (fun _ => z)) 1) 1) =
      ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 2) *
        z ^ n := by
  let p := ordinaryHypergeometricSeries ℂ a b (1 : ℂ)
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  change ((z ^ n • (((p.derivSeries.derivSeries).coeff n))) 1) 1 =
    ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 2) * z ^ n
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  rw [ContinuousLinearMap.smul_apply]
  rw [(by
    rw [FormalMultilinearSeries.derivSeries_coeff_one]
    simp only [nsmul_eq_mul] :
      p.derivSeries.coeff (n + 1) 1 = ((n + 2 : ℕ) : ℂ) * p.coeff (n + 2))]
  rw [(by
    simp [gauss2F1Coeff, ordinaryHypergeometricSeries] :
      (ordinaryHypergeometricSeries ℂ a b (1 : ℂ)).coeff (n + 2) =
        gauss2F1Coeff a b 1 (n + 2))]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring_nf

private lemma gauss2F1_hasSecondDerivAt_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    HasDerivAt (deriv (gauss2F1 a b 1))
      (∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1Coeff a b 1 (n + 2) * z ^ n) z := by
  let p := ordinaryHypergeometricSeries ℂ a b (1 : ℂ)
  have hbase := gauss2F1_hasSecondDerivAt_series_of_norm_lt_one a b z hz
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1Series_radius_ge_one a b)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_second_ball : z ∈ Metric.eball (0 : ℂ) p.derivSeries.derivSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem.trans_le ((p.radius_le_radius_derivSeries).trans
      p.derivSeries.radius_le_radius_derivSeries)
  have happly : (((p.derivSeries.derivSeries.sum z : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) 1) 1) =
      ∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1Coeff a b 1 (n + 2) * z ^ n := by
    unfold FormalMultilinearSeries.sum
    rw [show (((∑' n : ℕ, p.derivSeries.derivSeries n fun _ => z) :
          ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) 1) 1 =
        (∑' n : ℕ, ((((p.derivSeries.derivSeries n (fun _ => z)) 1) 1 : ℂ))) by
      let L₁ : (ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) →L[ℂ] (ℂ →L[ℂ] ℂ) :=
        ContinuousLinearMap.apply ℂ (ℂ →L[ℂ] ℂ) (1 : ℂ)
      let L₂ : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
        ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
      change (L₂ (L₁ (∑' n : ℕ, p.derivSeries.derivSeries n fun _ => z))) =
        ∑' n : ℕ, L₂ (L₁ (p.derivSeries.derivSeries n fun _ => z))
      rw [L₁.map_tsum (p.derivSeries.derivSeries.summable hmem_second_ball)]
      exact L₂.map_tsum ((p.derivSeries.derivSeries.summable hmem_second_ball).map
        L₁ L₁.continuous)]
    apply tsum_congr
    intro n
    simpa [p] using gauss2F1_secondDerivSeries_term a b z n
  rw [← happly]
  simpa [p] using hbase

private lemma gauss2F1_derivSeries_summable_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n := by
  let p := ordinaryHypergeometricSeries ℂ a b (1 : ℂ)
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1Series_radius_ge_one a b)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_deriv_ball : z ∈ Metric.eball (0 : ℂ) p.derivSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem.trans_le p.radius_le_radius_derivSeries
  have hsclm := p.derivSeries.summable hmem_deriv_ball
  have hsapp : Summable fun n : ℕ => ((p.derivSeries n (fun _ => z)) 1 : ℂ) :=
    hsclm.map (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) (ContinuousLinearMap.continuous _)
  convert hsapp using 1
  ext n
  simpa [p] using (gauss2F1_derivSeries_term a b z n).symm

private lemma gauss2F1_theta_eval_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) =
      z * ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n := by
  let f : ℕ → ℂ := fun n => (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n
  let g : ℕ → ℂ := fun n => ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n
  have hg : Summable g := gauss2F1_derivSeries_summable_of_norm_lt_one a b z hz
  have htail : Summable fun n : ℕ => f (n + 1) := by
    convert hg.mul_left z using 1
    ext n
    simp [f, g, pow_succ]
    ring
  have hf : Summable f := (summable_nat_add_iff 1).mp htail
  change (∑' n : ℕ, f n) = z * ∑' n : ℕ, g n
  nth_rw 1 [hf.tsum_eq_zero_add]
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0, zero_add]
  calc
    (∑' n : ℕ, f (n + 1)) = ∑' n : ℕ, z * g n := by
      apply tsum_congr
      intro n
      simp [f, g, pow_succ]
      ring
    _ = z * ∑' n : ℕ, g n := hg.tsum_mul_left z

private lemma gauss2F1_secondDerivSeries_summable_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
      gauss2F1Coeff a b 1 (n + 2) * z ^ n := by
  let p := ordinaryHypergeometricSeries ℂ a b (1 : ℂ)
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1Series_radius_ge_one a b)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_second_ball : z ∈ Metric.eball (0 : ℂ) p.derivSeries.derivSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem.trans_le ((p.radius_le_radius_derivSeries).trans
      p.derivSeries.radius_le_radius_derivSeries)
  have hsclm := p.derivSeries.derivSeries.summable hmem_second_ball
  let L₁ : (ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) →L[ℂ] (ℂ →L[ℂ] ℂ) :=
    ContinuousLinearMap.apply ℂ (ℂ →L[ℂ] ℂ) (1 : ℂ)
  let L₂ : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
  have hsapp : Summable fun n : ℕ => L₂ (L₁ (p.derivSeries.derivSeries n (fun _ => z))) := by
    exact (hsclm.map L₁ L₁.continuous).map L₂ L₂.continuous
  convert hsapp using 1
  ext n
  simpa [p, L₁, L₂] using (gauss2F1_secondDerivSeries_term a b z n).symm

private lemma gauss2F1_theta_falling_eval_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (n : ℂ) * ((n : ℂ) - 1) * gauss2F1Coeff a b 1 n * z ^ n) =
      z ^ 2 * ∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1Coeff a b 1 (n + 2) * z ^ n := by
  let f : ℕ → ℂ := fun n => (n : ℂ) * ((n : ℂ) - 1) * gauss2F1Coeff a b 1 n * z ^ n
  let g : ℕ → ℂ := fun n => ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
    gauss2F1Coeff a b 1 (n + 2) * z ^ n
  have hg : Summable g := gauss2F1_secondDerivSeries_summable_of_norm_lt_one a b z hz
  have htail2 : Summable fun n : ℕ => f (n + 2) := by
    convert hg.mul_left (z ^ 2) using 1
    ext n
    simp [f, g, pow_add]
    ring
  have htail1 : Summable fun n : ℕ => f (n + 1) := (summable_nat_add_iff 1).mp htail2
  have hf : Summable f := (summable_nat_add_iff 1).mp htail1
  change (∑' n : ℕ, f n) = z ^ 2 * ∑' n : ℕ, g n
  rw [hf.tsum_eq_zero_add]
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0, zero_add]
  rw [htail1.tsum_eq_zero_add]
  have hf1 : f (0 + 1) = 0 := by norm_num [f]
  rw [hf1, zero_add]
  calc
    (∑' b : ℕ, f (b + 1 + 1)) = ∑' n : ℕ, z ^ 2 * g n := by
      apply tsum_congr
      intro n
      simp [f, g, pow_add]
      ring
    _ = z ^ 2 * ∑' n : ℕ, g n := hg.tsum_mul_left (z ^ 2)

private lemma gauss2F1_theta2_eval_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (n : ℂ) * (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) =
      z * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n) +
      z ^ 2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1Coeff a b 1 (n + 2) * z ^ n) := by
  let theta1 : ℕ → ℂ := fun n => (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n
  let fall : ℕ → ℂ := fun n => (n : ℂ) * ((n : ℂ) - 1) * gauss2F1Coeff a b 1 n * z ^ n
  have htheta1 : Summable theta1 := by
    have h := gauss2F1_derivSeries_summable_of_norm_lt_one a b z hz
    have htail : Summable fun n : ℕ => theta1 (n + 1) := by
      convert h.mul_left z using 1
      ext n
      simp [theta1, pow_succ]
      ring
    exact (summable_nat_add_iff 1).mp htail
  have hfall : Summable fall := by
    have hg := gauss2F1_secondDerivSeries_summable_of_norm_lt_one a b z hz
    have htail2 : Summable fun n : ℕ => fall (n + 2) := by
      convert hg.mul_left (z ^ 2) using 1
      ext n
      simp [fall, pow_add]
      ring
    have htail1 : Summable fun n : ℕ => fall (n + 1) := (summable_nat_add_iff 1).mp htail2
    exact (summable_nat_add_iff 1).mp htail1
  have hsum : (∑' n : ℕ, (theta1 n + fall n)) = (∑' n : ℕ, theta1 n) + (∑' n : ℕ, fall n) :=
    htheta1.tsum_add hfall
  calc
    (∑' n : ℕ, (n : ℂ) * (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n)
        = (∑' n : ℕ, (theta1 n + fall n)) := by
          apply tsum_congr
          intro n
          simp [theta1, fall]
          ring
    _ = (∑' n : ℕ, theta1 n) + (∑' n : ℕ, fall n) := hsum
    _ = z * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n) +
      z ^ 2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1Coeff a b 1 (n + 2) * z ^ n) := by
          rw [gauss2F1_theta_eval_of_norm_lt_one a b z hz,
            gauss2F1_theta_falling_eval_of_norm_lt_one a b z hz]

private lemma gauss2F1_series_summable_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => gauss2F1Coeff a b 1 n * z ^ n := by
  let p := ordinaryHypergeometricSeries ℂ a b (1 : ℂ)
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1Series_radius_ge_one a b)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_ball : z ∈ Metric.eball (0 : ℂ) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem
  have hs := p.summable hmem_ball
  convert hs using 1
  ext n
  rw [ordinaryHypergeometricSeries_apply_eq]
  simp [gauss2F1Coeff, ordinaryHypergeometricCoefficient]

private lemma gauss2F1_theta1_summable_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n := by
  let theta1 : ℕ → ℂ := fun n => (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n
  have h := gauss2F1_derivSeries_summable_of_norm_lt_one a b z hz
  have htail : Summable fun n : ℕ => theta1 (n + 1) := by
    convert h.mul_left z using 1
    ext n
    simp [theta1, pow_succ]
    ring
  exact (summable_nat_add_iff 1).mp htail

private lemma gauss2F1_theta_falling_summable_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (n : ℂ) * ((n : ℂ) - 1) * gauss2F1Coeff a b 1 n * z ^ n := by
  let fall : ℕ → ℂ := fun n => (n : ℂ) * ((n : ℂ) - 1) * gauss2F1Coeff a b 1 n * z ^ n
  have hg := gauss2F1_secondDerivSeries_summable_of_norm_lt_one a b z hz
  have htail2 : Summable fun n : ℕ => fall (n + 2) := by
    convert hg.mul_left (z ^ 2) using 1
    ext n
    simp [fall, pow_add]
    ring
  have htail1 : Summable fun n : ℕ => fall (n + 1) := (summable_nat_add_iff 1).mp htail2
  exact (summable_nat_add_iff 1).mp htail1

private lemma gauss2F1_theta2_summable_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (n : ℂ) * (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n := by
  let theta1 : ℕ → ℂ := fun n => (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n
  let fall : ℕ → ℂ := fun n => (n : ℂ) * ((n : ℂ) - 1) * gauss2F1Coeff a b 1 n * z ^ n
  have htheta1 : Summable theta1 := gauss2F1_theta1_summable_of_norm_lt_one a b z hz
  have hfall : Summable fall := gauss2F1_theta_falling_summable_of_norm_lt_one a b z hz
  have hsum : Summable fun n : ℕ => theta1 n + fall n := htheta1.add hfall
  convert hsum using 1
  ext n
  simp [theta1, fall]
  ring_nf

private lemma gauss2F1_theta_recurrence_of_norm_lt_one (a b z : ℂ) (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (n : ℂ) * (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) =
      z * ((∑' n : ℕ, (n : ℂ) * (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) +
        (a + b) * (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) +
        a * b * (∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n)) := by
  let f : ℕ → ℂ := fun n => (n : ℂ) * (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n
  let h : ℕ → ℂ := fun n => (((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
    gauss2F1Coeff a b 1 n * z ^ n)
  have hs0 : Summable fun n : ℕ => gauss2F1Coeff a b 1 n * z ^ n :=
    gauss2F1_series_summable_of_norm_lt_one a b z hz
  have hs1 : Summable fun n : ℕ => (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n :=
    gauss2F1_theta1_summable_of_norm_lt_one a b z hz
  have hs2 : Summable f := gauss2F1_theta2_summable_of_norm_lt_one a b z hz
  have hh : Summable h := by
    have h2 : Summable fun n : ℕ => (n : ℂ) * (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n := hs2
    have h1 : Summable fun n : ℕ => (a + b) * ((n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) := hs1.mul_left (a + b)
    have h0 : Summable fun n : ℕ => a * b * (gauss2F1Coeff a b 1 n * z ^ n) := hs0.mul_left (a * b)
    convert (h2.add h1).add h0 using 1
    ext n
    simp [h]
    ring
  have htail : Summable fun n : ℕ => f (n + 1) := by
    convert hh.mul_left z using 1
    ext n
    have hrec := gauss2F1Coeff_succ_one a b n
    have hrec' : ((n : ℂ) + 1) * ((n : ℂ) + 1) *
        gauss2F1Coeff a b 1 (n + 1) =
        (((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
          gauss2F1Coeff a b 1 n) := by
      calc
        ((n : ℂ) + 1) * ((n : ℂ) + 1) * gauss2F1Coeff a b 1 (n + 1)
            = ((n : ℂ) + 1) ^ 2 * gauss2F1Coeff a b 1 (n + 1) := by ring
        _ = (a + n) * (b + n) * gauss2F1Coeff a b 1 n := hrec
        _ = (((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
          gauss2F1Coeff a b 1 n) := by ring
    simp [f, h, pow_succ]
    rw [hrec']
    ring
  have hf : Summable f := (summable_nat_add_iff 1).mp htail
  change (∑' n : ℕ, f n) = z * ((∑' n : ℕ, f n) +
    (a + b) * (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) +
    a * b * (∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n))
  have hf0 : f 0 = 0 := by simp [f]
  calc
    (∑' n : ℕ, f n) = f 0 + ∑' n : ℕ, f (n + 1) := hf.tsum_eq_zero_add
    _ = ∑' n : ℕ, f (n + 1) := by rw [hf0, zero_add]
    _ = ∑' n : ℕ, z * h n := by
      apply tsum_congr
      intro n
      have hrec := gauss2F1Coeff_succ_one a b n
      have hrec' : ((n : ℂ) + 1) * ((n : ℂ) + 1) *
          gauss2F1Coeff a b 1 (n + 1) =
          (((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
            gauss2F1Coeff a b 1 n) := by
        calc
          ((n : ℂ) + 1) * ((n : ℂ) + 1) * gauss2F1Coeff a b 1 (n + 1)
              = ((n : ℂ) + 1) ^ 2 * gauss2F1Coeff a b 1 (n + 1) := by ring
          _ = (a + n) * (b + n) * gauss2F1Coeff a b 1 n := hrec
          _ = (((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
            gauss2F1Coeff a b 1 n) := by ring
      simp [f, h, pow_succ]
      rw [hrec']
      ring
    _ = z * ∑' n : ℕ, h n := hh.tsum_mul_left z
    _ = z * ((∑' n : ℕ, f n) +
      (a + b) * (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) +
      a * b * (∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n)) := by
        congr 1
        calc
          (∑' n : ℕ, h n) = (∑' n : ℕ, (f n +
              (a + b) * ((n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) +
              a * b * (gauss2F1Coeff a b 1 n * z ^ n))) := by
                apply tsum_congr
                intro n
                simp [f, h]
                ring
          _ = (∑' n : ℕ, f n) +
              (∑' n : ℕ, (a + b) * ((n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n)) +
              (∑' n : ℕ, a * b * (gauss2F1Coeff a b 1 n * z ^ n)) := by
                rw [(hs2.add (hs1.mul_left (a + b))).tsum_add (hs0.mul_left (a * b))]
                rw [hs2.tsum_add (hs1.mul_left (a + b))]
          _ = (∑' n : ℕ, f n) +
              (a + b) * (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) +
              a * b * (∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n) := by
                rw [(hs1.tsum_mul_left (a + b)), (hs0.tsum_mul_left (a * b))]

theorem gauss2F1_operator_eq_zero_of_norm_lt_one
    (a b z : ℂ) (hz : ‖z‖ < 1) :
    gauss2F1Operator a b (gauss2F1 a b 1) z = 0 := by
  let S0 : ℂ := ∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n
  let D1 : ℂ := ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n
  let D2 : ℂ := ∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
    gauss2F1Coeff a b 1 (n + 2) * z ^ n
  let T1 : ℂ := ∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n
  let T2 : ℂ := ∑' n : ℕ, (n : ℂ) * (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n
  have hS0 : gauss2F1 a b 1 z = S0 := by
    simpa [S0] using gauss2F1_one_eq_tsum a b z
  have hD1 : deriv (gauss2F1 a b 1) z = D1 := by
    simpa [D1] using (gauss2F1_hasDerivAt_of_norm_lt_one a b z hz).deriv
  have hD2 : deriv (deriv (gauss2F1 a b 1)) z = D2 := by
    simpa [D2] using (gauss2F1_hasSecondDerivAt_of_norm_lt_one a b z hz).deriv
  have hT1 : T1 = z * D1 := by
    simpa [T1, D1] using gauss2F1_theta_eval_of_norm_lt_one a b z hz
  have hT2 : T2 = z * D1 + z ^ 2 * D2 := by
    simpa [T2, D1, D2] using gauss2F1_theta2_eval_of_norm_lt_one a b z hz
  have hrec : T2 = z * (T2 + (a + b) * T1 + a * b * S0) := by
    simpa [T2, T1, S0] using gauss2F1_theta_recurrence_of_norm_lt_one a b z hz
  unfold gauss2F1Operator
  rw [hD2, hD1, hS0]
  by_cases hz0 : z = 0
  · subst z
    have hS0zero : S0 = 1 := by
      unfold S0
      rw [tsum_eq_single 0]
      · simp [gauss2F1Coeff, ordinaryHypergeometricCoefficient]
      · intro n hn
        cases n with
        | zero => exact False.elim (hn rfl)
        | succ n => simp
    have hD1zero : D1 = a * b := by
      unfold D1
      rw [tsum_eq_single 0]
      · norm_num [gauss2F1Coeff, ordinaryHypergeometricCoefficient]
      · intro n hn
        cases n with
        | zero => exact False.elim (hn rfl)
        | succ n => simp
    rw [hS0zero, hD1zero]
    ring
  · have hzT : z * (z * (1 - z) * D2 + (1 - (a + b + 1) * z) * D1 - a * b * S0) = 0 := by
      rw [hT1, hT2] at hrec
      calc
        z * (z * (1 - z) * D2 + (1 - (a + b + 1) * z) * D1 - a * b * S0)
            = (z * D1 + z ^ 2 * D2) - z * (z * D1 + z ^ 2 * D2 + (a + b) * (z * D1) + a * b * S0) := by ring
        _ = 0 := by
            nth_rw 1 [hrec]
            ring
    have hzT' : z * (z * (1 - z) * D2 + (1 - (a + b + 1) * z) * D1 - a * b * S0) = z * 0 := by simpa using hzT
    exact mul_left_cancel₀ hz0 hzT'

private lemma gauss2F1FrobeniusCorrection_derivSeries_summable_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) *
      gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n := by
  let p := gauss2F1FrobeniusCorrectionFMLS a b
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1FrobeniusCorrectionFMLS_radius_ge_one a b hGa hGb)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_deriv_ball : z ∈ Metric.eball (0 : ℂ) p.derivSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem.trans_le p.radius_le_radius_derivSeries
  have hsclm := p.derivSeries.summable hmem_deriv_ball
  have hsapp : Summable fun n : ℕ => ((p.derivSeries n (fun _ => z)) 1 : ℂ) :=
    hsclm.map (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) (ContinuousLinearMap.continuous _)
  convert hsapp using 1
  ext n
  simpa [p] using (gauss2F1FrobeniusCorrection_derivSeries_term a b z n).symm

private lemma gauss2F1FrobeniusCorrection_theta_eval_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (n : ℂ) * gauss2F1SecondSolutionCoeff a b n * z ^ n) =
      z * ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
        gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n := by
  let f : ℕ → ℂ := fun n => (n : ℂ) * gauss2F1SecondSolutionCoeff a b n * z ^ n
  let g : ℕ → ℂ := fun n => ((n + 1 : ℕ) : ℂ) *
    gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n
  have hg : Summable g :=
    gauss2F1FrobeniusCorrection_derivSeries_summable_of_norm_lt_one a b z hGa hGb hz
  have htail : Summable fun n : ℕ => f (n + 1) := by
    convert hg.mul_left z using 1
    ext n
    simp [f, g, pow_succ]
    ring
  have hf : Summable f := (summable_nat_add_iff 1).mp htail
  change (∑' n : ℕ, f n) = z * ∑' n : ℕ, g n
  nth_rw 1 [hf.tsum_eq_zero_add]
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0, zero_add]
  calc
    (∑' n : ℕ, f (n + 1)) = ∑' n : ℕ, z * g n := by
      apply tsum_congr
      intro n
      simp [f, g, pow_succ]
      ring
    _ = z * ∑' n : ℕ, g n := hg.tsum_mul_left z

private lemma gauss2F1FrobeniusCorrection_secondDerivSeries_summable_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
      gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n := by
  let p := gauss2F1FrobeniusCorrectionFMLS a b
  have hmem : ((‖z‖₊ : ENNReal) < p.radius) := by
    apply lt_of_lt_of_le _ (gauss2F1FrobeniusCorrectionFMLS_radius_ge_one a b hGa hGb)
    exact ENNReal.coe_lt_coe.mpr (by simpa using hz : ‖z‖₊ < (1 : NNReal))
  have hmem_second_ball : z ∈ Metric.eball (0 : ℂ) p.derivSeries.derivSeries.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    exact hmem.trans_le ((p.radius_le_radius_derivSeries).trans
      p.derivSeries.radius_le_radius_derivSeries)
  have hsclm := p.derivSeries.derivSeries.summable hmem_second_ball
  let L₁ : (ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) →L[ℂ] (ℂ →L[ℂ] ℂ) :=
    ContinuousLinearMap.apply ℂ (ℂ →L[ℂ] ℂ) (1 : ℂ)
  let L₂ : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
  have hsapp : Summable fun n : ℕ => L₂ (L₁ (p.derivSeries.derivSeries n (fun _ => z))) := by
    exact (hsclm.map L₁ L₁.continuous).map L₂ L₂.continuous
  convert hsapp using 1
  ext n
  simpa [p, L₁, L₂] using
    (gauss2F1FrobeniusCorrection_secondDerivSeries_term a b z n).symm

private lemma gauss2F1FrobeniusCorrection_theta_falling_eval_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (n : ℂ) * ((n : ℂ) - 1) *
        gauss2F1SecondSolutionCoeff a b n * z ^ n) =
      z ^ 2 * ∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n := by
  let f : ℕ → ℂ := fun n => (n : ℂ) * ((n : ℂ) - 1) *
    gauss2F1SecondSolutionCoeff a b n * z ^ n
  let g : ℕ → ℂ := fun n => ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
    gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n
  have hg : Summable g :=
    gauss2F1FrobeniusCorrection_secondDerivSeries_summable_of_norm_lt_one
      a b z hGa hGb hz
  have htail2 : Summable fun n : ℕ => f (n + 2) := by
    convert hg.mul_left (z ^ 2) using 1
    ext n
    simp [f, g, pow_add]
    ring
  have htail1 : Summable fun n : ℕ => f (n + 1) := (summable_nat_add_iff 1).mp htail2
  have hf : Summable f := (summable_nat_add_iff 1).mp htail1
  change (∑' n : ℕ, f n) = z ^ 2 * ∑' n : ℕ, g n
  rw [hf.tsum_eq_zero_add]
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0, zero_add]
  rw [htail1.tsum_eq_zero_add]
  have hf1 : f (0 + 1) = 0 := by norm_num [f]
  rw [hf1, zero_add]
  calc
    (∑' b : ℕ, f (b + 1 + 1)) = ∑' n : ℕ, z ^ 2 * g n := by
      apply tsum_congr
      intro n
      simp [f, g, pow_add]
      ring
    _ = z ^ 2 * ∑' n : ℕ, g n := hg.tsum_mul_left (z ^ 2)

private lemma gauss2F1FrobeniusCorrection_theta2_eval_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (n : ℂ) * (n : ℂ) *
        gauss2F1SecondSolutionCoeff a b n * z ^ n) =
      z * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
        gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n) +
      z ^ 2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
        gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n) := by
  let theta1 : ℕ → ℂ :=
    fun n => (n : ℂ) * gauss2F1SecondSolutionCoeff a b n * z ^ n
  let fall : ℕ → ℂ :=
    fun n => (n : ℂ) * ((n : ℂ) - 1) *
      gauss2F1SecondSolutionCoeff a b n * z ^ n
  have htheta1 : Summable theta1 := by
    have h := gauss2F1FrobeniusCorrection_derivSeries_summable_of_norm_lt_one
      a b z hGa hGb hz
    have htail : Summable fun n : ℕ => theta1 (n + 1) := by
      convert h.mul_left z using 1
      ext n
      simp [theta1, pow_succ]
      ring
    exact (summable_nat_add_iff 1).mp htail
  have hfall : Summable fall := by
    have hg := gauss2F1FrobeniusCorrection_secondDerivSeries_summable_of_norm_lt_one
      a b z hGa hGb hz
    have htail2 : Summable fun n : ℕ => fall (n + 2) := by
      convert hg.mul_left (z ^ 2) using 1
      ext n
      simp [fall, pow_add]
      ring
    have htail1 : Summable fun n : ℕ => fall (n + 1) := (summable_nat_add_iff 1).mp htail2
    exact (summable_nat_add_iff 1).mp htail1
  have hsum : (∑' n : ℕ, (theta1 n + fall n)) =
      (∑' n : ℕ, theta1 n) + (∑' n : ℕ, fall n) :=
    htheta1.tsum_add hfall
  calc
    (∑' n : ℕ, (n : ℂ) * (n : ℂ) *
        gauss2F1SecondSolutionCoeff a b n * z ^ n)
        = (∑' n : ℕ, (theta1 n + fall n)) := by
          apply tsum_congr
          intro n
          simp [theta1, fall]
          ring
    _ = (∑' n : ℕ, theta1 n) + (∑' n : ℕ, fall n) := hsum
    _ = z * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
          gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n) +
        z ^ 2 * (∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
          gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n) := by
          rw [gauss2F1FrobeniusCorrection_theta_eval_of_norm_lt_one a b z hGa hGb hz,
            gauss2F1FrobeniusCorrection_theta_falling_eval_of_norm_lt_one
              a b z hGa hGb hz]

private lemma gauss2F1FrobeniusCorrection_theta1_summable_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (n : ℂ) *
      gauss2F1SecondSolutionCoeff a b n * z ^ n := by
  let theta1 : ℕ → ℂ :=
    fun n => (n : ℂ) * gauss2F1SecondSolutionCoeff a b n * z ^ n
  have h := gauss2F1FrobeniusCorrection_derivSeries_summable_of_norm_lt_one
    a b z hGa hGb hz
  have htail : Summable fun n : ℕ => theta1 (n + 1) := by
    convert h.mul_left z using 1
    ext n
    simp [theta1, pow_succ]
    ring
  exact (summable_nat_add_iff 1).mp htail

private lemma gauss2F1FrobeniusCorrection_theta_falling_summable_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (n : ℂ) * ((n : ℂ) - 1) *
      gauss2F1SecondSolutionCoeff a b n * z ^ n := by
  let fall : ℕ → ℂ := fun n => (n : ℂ) * ((n : ℂ) - 1) *
    gauss2F1SecondSolutionCoeff a b n * z ^ n
  have hg := gauss2F1FrobeniusCorrection_secondDerivSeries_summable_of_norm_lt_one
    a b z hGa hGb hz
  have htail2 : Summable fun n : ℕ => fall (n + 2) := by
    convert hg.mul_left (z ^ 2) using 1
    ext n
    simp [fall, pow_add]
    ring
  have htail1 : Summable fun n : ℕ => fall (n + 1) := (summable_nat_add_iff 1).mp htail2
  exact (summable_nat_add_iff 1).mp htail1

private lemma gauss2F1FrobeniusCorrection_theta2_summable_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (n : ℂ) * (n : ℂ) *
      gauss2F1SecondSolutionCoeff a b n * z ^ n := by
  let theta1 : ℕ → ℂ :=
    fun n => (n : ℂ) * gauss2F1SecondSolutionCoeff a b n * z ^ n
  let fall : ℕ → ℂ := fun n => (n : ℂ) * ((n : ℂ) - 1) *
    gauss2F1SecondSolutionCoeff a b n * z ^ n
  have htheta1 : Summable theta1 :=
    gauss2F1FrobeniusCorrection_theta1_summable_of_norm_lt_one a b z hGa hGb hz
  have hfall : Summable fall :=
    gauss2F1FrobeniusCorrection_theta_falling_summable_of_norm_lt_one a b z hGa hGb hz
  have hsum : Summable fun n : ℕ => theta1 n + fall n := htheta1.add hfall
  convert hsum using 1
  ext n
  simp [theta1, fall]
  ring_nf

private lemma gauss2F1FrobeniusCorrection_theta_recurrence_of_norm_lt_one
    (a b z : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (n : ℂ) * (n : ℂ) *
        gauss2F1SecondSolutionCoeff a b n * z ^ n) =
      z * ((∑' n : ℕ, (n : ℂ) * (n : ℂ) *
          gauss2F1SecondSolutionCoeff a b n * z ^ n) +
        (a + b) * (∑' n : ℕ, (n : ℂ) *
          gauss2F1SecondSolutionCoeff a b n * z ^ n) +
        a * b * (∑' n : ℕ, gauss2F1SecondSolutionCoeff a b n * z ^ n)) +
      (a + b) * z * (∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n) -
      2 * ((∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) -
        z * (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n)) := by
  let f : ℕ → ℂ := fun n => (n : ℂ) * (n : ℂ) *
    gauss2F1SecondSolutionCoeff a b n * z ^ n
  let q : ℕ → ℂ := fun n =>
    ((((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
        gauss2F1SecondSolutionCoeff a b n +
      (((2 : ℂ) * n + a + b) * gauss2F1Coeff a b 1 n -
        2 * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1))) * z ^ n)
  have hsd0 : Summable fun n : ℕ => gauss2F1SecondSolutionCoeff a b n * z ^ n :=
    gauss2F1SecondSolutionCoeff_series_summable_of_norm_lt_one a b z hGa hGb hz
  have hsd1 : Summable fun n : ℕ => (n : ℂ) *
      gauss2F1SecondSolutionCoeff a b n * z ^ n :=
    gauss2F1FrobeniusCorrection_theta1_summable_of_norm_lt_one a b z hGa hGb hz
  have hsd2 : Summable f :=
    gauss2F1FrobeniusCorrection_theta2_summable_of_norm_lt_one a b z hGa hGb hz
  have hsc0 : Summable fun n : ℕ => gauss2F1Coeff a b 1 n * z ^ n :=
    gauss2F1_series_summable_of_norm_lt_one a b z hz
  have hsc1 : Summable fun n : ℕ => (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n :=
    gauss2F1_theta1_summable_of_norm_lt_one a b z hz
  have hscD : Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) *
      gauss2F1Coeff a b 1 (n + 1) * z ^ n :=
    gauss2F1_derivSeries_summable_of_norm_lt_one a b z hz
  have hq : Summable q := by
    have hd2 : Summable fun n : ℕ => (n : ℂ) * (n : ℂ) *
        gauss2F1SecondSolutionCoeff a b n * z ^ n := hsd2
    have hd1 : Summable fun n : ℕ => (a + b) *
        ((n : ℂ) * gauss2F1SecondSolutionCoeff a b n * z ^ n) := hsd1.mul_left (a + b)
    have hd0 : Summable fun n : ℕ => a * b *
        (gauss2F1SecondSolutionCoeff a b n * z ^ n) := hsd0.mul_left (a * b)
    have hc1 : Summable fun n : ℕ => (2 : ℂ) *
        ((n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) := hsc1.mul_left 2
    have hc0 : Summable fun n : ℕ => (a + b) *
        (gauss2F1Coeff a b 1 n * z ^ n) := hsc0.mul_left (a + b)
    have hcD : Summable fun n : ℕ => (-2 : ℂ) *
        (((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1) * z ^ n) :=
      hscD.mul_left (-2)
    convert ((((hd2.add hd1).add hd0).add hc1).add hc0).add hcD using 1
    ext n
    simp [q]
    ring
  have htail : Summable fun n : ℕ => f (n + 1) := by
    convert hq.mul_left z using 1
    ext n
    have hrec := gauss2F1SecondSolutionCoeff_recurrence a b n hGa hGb
    have hcoeff :
        ((n : ℂ) + 1) * ((n : ℂ) + 1) *
            gauss2F1SecondSolutionCoeff a b (n + 1) =
          (((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
            gauss2F1SecondSolutionCoeff a b n +
            (((2 : ℂ) * n + a + b) * gauss2F1Coeff a b 1 n -
              2 * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1))) := by
      calc
        ((n : ℂ) + 1) * ((n : ℂ) + 1) *
            gauss2F1SecondSolutionCoeff a b (n + 1)
            = ((n + 1 : ℕ) : ℂ) ^ 2 *
                gauss2F1SecondSolutionCoeff a b (n + 1) := by
              have hcast : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by norm_num
              rw [hcast, pow_two]
        _ = (a + n) * (b + n) * gauss2F1SecondSolutionCoeff a b n +
          (((2 : ℂ) * n + a + b) * gauss2F1Coeff a b 1 n -
            2 * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1)) := by
            linear_combination hrec
        _ = (((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
          gauss2F1SecondSolutionCoeff a b n +
          (((2 : ℂ) * n + a + b) * gauss2F1Coeff a b 1 n -
            2 * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1))) := by
            ring
    have hcoeff' := hcoeff
    simp [Nat.add_comm] at hcoeff'
    simp [f, q, pow_succ, Nat.add_comm]
    rw [hcoeff']
    ring_nf
  have hf : Summable f := (summable_nat_add_iff 1).mp htail
  change (∑' n : ℕ, f n) =
    z * ((∑' n : ℕ, f n) +
      (a + b) * (∑' n : ℕ, (n : ℂ) *
        gauss2F1SecondSolutionCoeff a b n * z ^ n) +
      a * b * (∑' n : ℕ, gauss2F1SecondSolutionCoeff a b n * z ^ n)) +
    (a + b) * z * (∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n) -
    2 * ((∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) -
      z * (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n))
  have hf0 : f 0 = 0 := by simp [f]
  calc
    (∑' n : ℕ, f n) = f 0 + ∑' n : ℕ, f (n + 1) := hf.tsum_eq_zero_add
    _ = ∑' n : ℕ, f (n + 1) := by rw [hf0, zero_add]
    _ = ∑' n : ℕ, z * q n := by
      apply tsum_congr
      intro n
      have hrec := gauss2F1SecondSolutionCoeff_recurrence a b n hGa hGb
      have hcoeff :
          ((n : ℂ) + 1) * ((n : ℂ) + 1) *
              gauss2F1SecondSolutionCoeff a b (n + 1) =
            (((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
              gauss2F1SecondSolutionCoeff a b n +
              (((2 : ℂ) * n + a + b) * gauss2F1Coeff a b 1 n -
                2 * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1))) := by
        calc
          ((n : ℂ) + 1) * ((n : ℂ) + 1) *
              gauss2F1SecondSolutionCoeff a b (n + 1)
              = ((n + 1 : ℕ) : ℂ) ^ 2 *
                  gauss2F1SecondSolutionCoeff a b (n + 1) := by
                have hcast : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by norm_num
                rw [hcast, pow_two]
          _ = (a + n) * (b + n) * gauss2F1SecondSolutionCoeff a b n +
            (((2 : ℂ) * n + a + b) * gauss2F1Coeff a b 1 n -
              2 * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1)) := by
              linear_combination hrec
          _ = (((n : ℂ) * (n : ℂ) + (a + b) * (n : ℂ) + a * b) *
            gauss2F1SecondSolutionCoeff a b n +
            (((2 : ℂ) * n + a + b) * gauss2F1Coeff a b 1 n -
              2 * ((n + 1 : ℕ) : ℂ) * gauss2F1Coeff a b 1 (n + 1))) := by
              ring
      have hcoeff' := hcoeff
      simp [Nat.add_comm] at hcoeff'
      simp [f, q, pow_succ, Nat.add_comm]
      rw [hcoeff']
      ring_nf
    _ = z * ∑' n : ℕ, q n := hq.tsum_mul_left z
    _ = z * ((∑' n : ℕ, f n) +
        (a + b) * (∑' n : ℕ, (n : ℂ) *
          gauss2F1SecondSolutionCoeff a b n * z ^ n) +
        a * b * (∑' n : ℕ, gauss2F1SecondSolutionCoeff a b n * z ^ n)) +
      (a + b) * z * (∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n) -
      2 * ((∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) -
        z * (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n)) := by
        have hqsum :
            (∑' n : ℕ, q n) =
              (∑' n : ℕ, f n) +
              (a + b) * (∑' n : ℕ, (n : ℂ) *
                gauss2F1SecondSolutionCoeff a b n * z ^ n) +
              a * b * (∑' n : ℕ, gauss2F1SecondSolutionCoeff a b n * z ^ n) +
              2 * (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) +
              (a + b) * (∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n) -
              2 * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
                gauss2F1Coeff a b 1 (n + 1) * z ^ n) := by
          calc
            (∑' n : ℕ, q n) =
                ∑' n : ℕ,
                  (f n +
                    (a + b) * ((n : ℂ) *
                      gauss2F1SecondSolutionCoeff a b n * z ^ n) +
                    a * b * (gauss2F1SecondSolutionCoeff a b n * z ^ n) +
                    2 * ((n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) +
                    (a + b) * (gauss2F1Coeff a b 1 n * z ^ n) +
                    (-2 : ℂ) * (((n + 1 : ℕ) : ℂ) *
                      gauss2F1Coeff a b 1 (n + 1) * z ^ n)) := by
                  apply tsum_congr
                  intro n
                  simp [f, q]
                  ring
            _ = (∑' n : ℕ, f n) +
                (∑' n : ℕ, (a + b) * ((n : ℂ) *
                  gauss2F1SecondSolutionCoeff a b n * z ^ n)) +
                (∑' n : ℕ, a * b *
                  (gauss2F1SecondSolutionCoeff a b n * z ^ n)) +
                (∑' n : ℕ, 2 * ((n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n)) +
                (∑' n : ℕ, (a + b) * (gauss2F1Coeff a b 1 n * z ^ n)) +
                (∑' n : ℕ, (-2) * (((n + 1 : ℕ) : ℂ) *
                  gauss2F1Coeff a b 1 (n + 1) * z ^ n)) := by
                  rw [(((((hsd2.add (hsd1.mul_left (a + b))).add
                    (hsd0.mul_left (a * b))).add (hsc1.mul_left 2)).add
                    (hsc0.mul_left (a + b))).tsum_add (hscD.mul_left (-2)))]
                  rw [((((hsd2.add (hsd1.mul_left (a + b))).add
                    (hsd0.mul_left (a * b))).add (hsc1.mul_left 2)).tsum_add
                    (hsc0.mul_left (a + b)))]
                  rw [(((hsd2.add (hsd1.mul_left (a + b))).add
                    (hsd0.mul_left (a * b))).tsum_add (hsc1.mul_left 2))]
                  rw [((hsd2.add (hsd1.mul_left (a + b))).tsum_add
                    (hsd0.mul_left (a * b)))]
                  rw [hsd2.tsum_add (hsd1.mul_left (a + b))]
            _ = (∑' n : ℕ, f n) +
                (a + b) * (∑' n : ℕ, (n : ℂ) *
                  gauss2F1SecondSolutionCoeff a b n * z ^ n) +
                a * b * (∑' n : ℕ, gauss2F1SecondSolutionCoeff a b n * z ^ n) +
                2 * (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) +
                (a + b) * (∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n) -
                2 * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
                  gauss2F1Coeff a b 1 (n + 1) * z ^ n) := by
                  rw [(hsd1.tsum_mul_left (a + b)), (hsd0.tsum_mul_left (a * b)),
                    (hsc1.tsum_mul_left 2), (hsc0.tsum_mul_left (a + b)),
                    (hscD.tsum_mul_left (-2))]
                  ring
        rw [hqsum]
        have hthetaF := gauss2F1_theta_eval_of_norm_lt_one a b z hz
        ring_nf at hthetaF ⊢
        rw [← hthetaF]
        have hthetaComm :
            (∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n) =
              (∑' n : ℕ, z ^ n * (n : ℂ) * gauss2F1Coeff a b 1 n) := by
          apply tsum_congr
          intro n
          ring
        rw [hthetaComm]
        ring_nf

private lemma gauss2F1FrobeniusCorrection_operator_eq_source
    (a b z : ℂ) (hz0 : z ≠ 0)
    (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (hz : ‖z‖ < 1) :
    gauss2F1Operator a b (gauss2F1FrobeniusCorrection a b) z =
      (a + b) * gauss2F1 a b 1 z -
        2 * (1 - z) * deriv (gauss2F1 a b 1) z := by
  let S0G : ℂ := ∑' n : ℕ, gauss2F1SecondSolutionCoeff a b n * z ^ n
  let D1G : ℂ := ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) *
    gauss2F1SecondSolutionCoeff a b (n + 1) * z ^ n
  let D2G : ℂ := ∑' n : ℕ, ((n + 2 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) *
    gauss2F1SecondSolutionCoeff a b (n + 2) * z ^ n
  let T1G : ℂ := ∑' n : ℕ, (n : ℂ) *
    gauss2F1SecondSolutionCoeff a b n * z ^ n
  let T2G : ℂ := ∑' n : ℕ, (n : ℂ) * (n : ℂ) *
    gauss2F1SecondSolutionCoeff a b n * z ^ n
  let S0F : ℂ := ∑' n : ℕ, gauss2F1Coeff a b 1 n * z ^ n
  let T1F : ℂ := ∑' n : ℕ, (n : ℂ) * gauss2F1Coeff a b 1 n * z ^ n
  have hS0G : gauss2F1FrobeniusCorrection a b z = S0G := by
    let d : ℕ → ℂ := gauss2F1SecondSolutionCoeff a b
    have hs : Summable fun n : ℕ => d n * z ^ n := by
      simpa [d] using gauss2F1SecondSolutionCoeff_series_summable_of_norm_lt_one
        a b z hGa hGb hz
    unfold gauss2F1FrobeniusCorrection
    change (∑' n : ℕ, d (n + 1) * z ^ (n + 1)) = (∑' n : ℕ, d n * z ^ n)
    rw [hs.tsum_eq_zero_add]
    have h0 : d 0 * z ^ 0 = 0 := by
      simp [d, gauss2F1SecondSolutionCoeff, gauss2F1SecondSolutionDigammaFactor_zero]
    rw [h0, zero_add]
  have hD1G : deriv (gauss2F1FrobeniusCorrection a b) z = D1G := by
    simpa [D1G] using
      (gauss2F1FrobeniusCorrection_hasDerivAt_of_norm_lt_one a b z hGa hGb hz).deriv
  have hD2G : deriv (deriv (gauss2F1FrobeniusCorrection a b)) z = D2G := by
    simpa [D2G] using
      (gauss2F1FrobeniusCorrection_hasSecondDerivAt_of_norm_lt_one
        a b z hGa hGb hz).deriv
  have hT1G : T1G = z * D1G := by
    simpa [T1G, D1G] using
      gauss2F1FrobeniusCorrection_theta_eval_of_norm_lt_one a b z hGa hGb hz
  have hT2G : T2G = z * D1G + z ^ 2 * D2G := by
    simpa [T2G, D1G, D2G] using
      gauss2F1FrobeniusCorrection_theta2_eval_of_norm_lt_one a b z hGa hGb hz
  have hS0F : gauss2F1 a b 1 z = S0F := by
    simpa [S0F] using gauss2F1_one_eq_tsum a b z
  have hT1F : T1F = z * deriv (gauss2F1 a b 1) z := by
    have hD1F := (gauss2F1_hasDerivAt_of_norm_lt_one a b z hz).deriv
    have htheta := gauss2F1_theta_eval_of_norm_lt_one a b z hz
    rw [hD1F] 
    simpa [T1F] using htheta
  have hrec : T2G =
      z * (T2G + (a + b) * T1G + a * b * S0G) +
      (a + b) * z * S0F - 2 * (T1F - z * T1F) := by
    simpa [T2G, T1G, S0G, S0F, T1F] using
      gauss2F1FrobeniusCorrection_theta_recurrence_of_norm_lt_one a b z hGa hGb hz
  unfold gauss2F1Operator
  rw [hD2G, hD1G, hS0G, hS0F]
  have hmul : z *
      (z * (1 - z) * D2G + (1 - (a + b + 1) * z) * D1G - a * b * S0G) =
        z * ((a + b) * S0F - 2 * (1 - z) * deriv (gauss2F1 a b 1) z) := by
    rw [hT1G, hT2G, hT1F] at hrec
    calc
      z * (z * (1 - z) * D2G + (1 - (a + b + 1) * z) * D1G - a * b * S0G)
          = (z * D1G + z ^ 2 * D2G) -
              z * (z * D1G + z ^ 2 * D2G + (a + b) * (z * D1G) + a * b * S0G) := by
            ring
      _ = (a + b) * z * S0F - 2 * (z * deriv (gauss2F1 a b 1) z -
              z * (z * deriv (gauss2F1 a b 1) z)) := by
            linear_combination hrec
      _ = z * ((a + b) * S0F - 2 * (1 - z) * deriv (gauss2F1 a b 1) z) := by
            ring
  exact mul_left_cancel₀ hz0 hmul

private lemma log_I_hasDerivAt (z : ℂ) (hz : Complex.I * z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => Complex.log (Complex.I * w)) z⁻¹ z := by
  have h := (Complex.hasDerivAt_log hz).comp z ((hasDerivAt_id z).const_mul Complex.I)
  convert h using 1
  field_simp [Complex.slitPlane_ne_zero hz]

private lemma log_I_deriv_eventually_eq_inv
    (z : ℂ) (hz : Complex.I * z ∈ Complex.slitPlane) :
    (fun w : ℂ => deriv (fun u : ℂ => Complex.log (Complex.I * u)) w) =ᶠ[𝓝 z]
      fun w : ℂ => w⁻¹ := by
  have hopen : IsOpen ((fun w : ℂ => Complex.I * w) ⁻¹' Complex.slitPlane) :=
    Complex.isOpen_slitPlane.preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact (log_I_hasDerivAt w hw).deriv

private lemma log_I_hasSecondDerivAt
    (z : ℂ) (hz : z ≠ 0) (hbranch : Complex.I * z ∈ Complex.slitPlane) :
    HasDerivAt (deriv (fun w : ℂ => Complex.log (Complex.I * w))) (-(z ^ 2)⁻¹) z := by
  exact (hasDerivAt_inv hz).congr_of_eventuallyEq
    (log_I_deriv_eventually_eq_inv z hbranch)

private lemma gauss2F1_eventually_hasDerivAt_of_norm_lt_one
    (a b z : ℂ) (hz : ‖z‖ < 1) :
    ∀ᶠ w in 𝓝 z,
      HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) w) w := by
  have hopen : IsOpen {w : ℂ | ‖w‖ < 1} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact (gauss2F1_hasDerivAt_of_norm_lt_one a b w hw).differentiableAt.hasDerivAt

private lemma gauss2F1_eventually_hasSecondDerivAt_of_norm_lt_one
    (a b z : ℂ) (hz : ‖z‖ < 1) :
    ∀ᶠ w in 𝓝 z,
      HasDerivAt (deriv (gauss2F1 a b 1)) (deriv (deriv (gauss2F1 a b 1)) w) w := by
  have hopen : IsOpen {w : ℂ | ‖w‖ < 1} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact (gauss2F1_hasSecondDerivAt_of_norm_lt_one a b w hw).differentiableAt.hasDerivAt

private lemma gauss2F1LogSecondPart_hasDerivAt
    (a b z : ℂ) (hbranch : Complex.I * z ∈ Complex.slitPlane)
    (hy : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z) :
    HasDerivAt (gauss2F1LogSecondPart a b)
      (z⁻¹ * gauss2F1 a b 1 z +
        Complex.log (Complex.I * z) * deriv (gauss2F1 a b 1) z) z := by
  exact (log_I_hasDerivAt z hbranch).mul hy

private lemma gauss2F1LogSecondPart_deriv_eventually_eq
    (a b z : ℂ) (hbranch : Complex.I * z ∈ Complex.slitPlane) (hd : ‖z‖ < 1) :
    (fun w : ℂ => deriv (gauss2F1LogSecondPart a b) w) =ᶠ[𝓝 z]
      fun w : ℂ =>
        w⁻¹ * gauss2F1 a b 1 w +
          Complex.log (Complex.I * w) * deriv (gauss2F1 a b 1) w := by
  have hopen : IsOpen ((fun w : ℂ => Complex.I * w) ⁻¹' Complex.slitPlane) :=
    Complex.isOpen_slitPlane.preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds hbranch,
    gauss2F1_eventually_hasDerivAt_of_norm_lt_one a b z hd] with w hw hyw
  exact (gauss2F1LogSecondPart_hasDerivAt a b w hw hyw).deriv

private lemma gauss2F1LogSecondPart_hasSecondDerivAt
    (a b z : ℂ) (hz : z ≠ 0) (hbranch : Complex.I * z ∈ Complex.slitPlane)
    (hd : ‖z‖ < 1)
    (hy : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z)
    (hy₂ : HasDerivAt (deriv (gauss2F1 a b 1))
      (deriv (deriv (gauss2F1 a b 1)) z) z) :
    HasDerivAt (deriv (gauss2F1LogSecondPart a b))
      (-(z ^ 2)⁻¹ * gauss2F1 a b 1 z +
        z⁻¹ * deriv (gauss2F1 a b 1) z +
        (z⁻¹ * deriv (gauss2F1 a b 1) z +
          Complex.log (Complex.I * z) * deriv (deriv (gauss2F1 a b 1)) z)) z := by
  have h₁ : HasDerivAt
      (fun w : ℂ => w⁻¹ * gauss2F1 a b 1 w)
      (-(z ^ 2)⁻¹ * gauss2F1 a b 1 z +
        z⁻¹ * deriv (gauss2F1 a b 1) z) z := by
    exact (hasDerivAt_inv hz).mul hy
  have h₂ : HasDerivAt
      (fun w : ℂ => Complex.log (Complex.I * w) * deriv (gauss2F1 a b 1) w)
      (z⁻¹ * deriv (gauss2F1 a b 1) z +
        Complex.log (Complex.I * z) * deriv (deriv (gauss2F1 a b 1)) z) z := by
    exact (log_I_hasDerivAt z hbranch).mul hy₂
  exact (h₁.add h₂).congr_of_eventuallyEq
    (gauss2F1LogSecondPart_deriv_eventually_eq a b z hbranch hd)

private lemma gauss2F1LogSecondPart_operator_algebra
    (a b z L Y Y' Y'' : ℂ) (hz : z ≠ 0)
    (hy : z * (1 - z) * Y'' + (1 - (a + b + 1) * z) * Y' - a * b * Y = 0) :
    z * (1 - z) * (-((z ^ 2)⁻¹ * Y) + z⁻¹ * Y' + (z⁻¹ * Y' + L * Y'')) +
        (1 - (a + b + 1) * z) * (z⁻¹ * Y + L * Y') - a * b * (L * Y) =
      2 * (1 - z) * Y' - (a + b) * Y := by
  have hmain :
      z * (1 - z) * (-((z ^ 2)⁻¹ * Y) + z⁻¹ * Y' + (z⁻¹ * Y' + L * Y'')) +
          (1 - (a + b + 1) * z) * (z⁻¹ * Y + L * Y') - a * b * (L * Y) =
        L * (z * (1 - z) * Y'' + (1 - (a + b + 1) * z) * Y' - a * b * Y) +
          (2 * (1 - z) * Y' - (a + b) * Y) := by
    field_simp [hz]
    ring
  rw [hmain, hy]
  ring

private lemma gauss2F1LogSecondPart_operator_eq_source
    (a b z : ℂ) (hz : z ≠ 0) (hbranch : Complex.I * z ∈ Complex.slitPlane)
    (hd : ‖z‖ < 1)
    (hy : gauss2F1Operator a b (gauss2F1 a b 1) z = 0) :
    gauss2F1Operator a b (gauss2F1LogSecondPart a b) z =
      2 * (1 - z) * deriv (gauss2F1 a b 1) z - (a + b) * gauss2F1 a b 1 z := by
  have hy₁ : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z :=
    (gauss2F1_hasDerivAt_of_norm_lt_one a b z hd).differentiableAt.hasDerivAt
  have hy₂ : HasDerivAt (deriv (gauss2F1 a b 1))
      (deriv (deriv (gauss2F1 a b 1)) z) z :=
    (gauss2F1_hasSecondDerivAt_of_norm_lt_one a b z hd).differentiableAt.hasDerivAt
  have hlog₁ := gauss2F1LogSecondPart_hasDerivAt a b z hbranch hy₁
  have hlog₂ := gauss2F1LogSecondPart_hasSecondDerivAt a b z hz hbranch hd hy₁ hy₂
  unfold gauss2F1Operator
  rw [hlog₁.deriv, hlog₂.deriv]
  unfold gauss2F1Operator at hy
  simp [gauss2F1LogSecondPart]
  exact gauss2F1LogSecondPart_operator_algebra a b z (Complex.log (Complex.I * z))
    (gauss2F1 a b 1 z) (deriv (gauss2F1 a b 1) z)
    (deriv (deriv (gauss2F1 a b 1)) z) hz hy

private lemma gauss2F1SecondSolution_inner_operator_eq_zero_of_correction_source
    (a b z : ℂ) (hz : z ≠ 0) (hbranch : Complex.I * z ∈ Complex.slitPlane)
    (hd : ‖z‖ < 1)
    (h₁ : deriv (fun w =>
        gauss2F1LogSecondPart a b w + gauss2F1FrobeniusCorrection a b w) z =
      deriv (gauss2F1LogSecondPart a b) z + deriv (gauss2F1FrobeniusCorrection a b) z)
    (h₂ : deriv (deriv (fun w =>
        gauss2F1LogSecondPart a b w + gauss2F1FrobeniusCorrection a b w)) z =
      deriv (deriv (gauss2F1LogSecondPart a b)) z +
        deriv (deriv (gauss2F1FrobeniusCorrection a b)) z)
    (hcorr : gauss2F1Operator a b (gauss2F1FrobeniusCorrection a b) z =
      (a + b) * gauss2F1 a b 1 z -
        2 * (1 - z) * deriv (gauss2F1 a b 1) z) :
    gauss2F1Operator a b
      (fun w => gauss2F1LogSecondPart a b w + gauss2F1FrobeniusCorrection a b w) z = 0 := by
  rw [gauss2F1Operator_add a b z
    (gauss2F1LogSecondPart a b) (gauss2F1FrobeniusCorrection a b) h₁ h₂]
  rw [gauss2F1LogSecondPart_operator_eq_source a b z hz hbranch hd
    (gauss2F1_operator_eq_zero_of_norm_lt_one a b z hd), hcorr]
  ring

private lemma gauss2F1SecondSolution_operator_eq_zero_of_inner
    (a b z : ℂ)
    (hinner : gauss2F1Operator a b
      (fun w => gauss2F1LogSecondPart a b w + gauss2F1FrobeniusCorrection a b w) z = 0) :
    gauss2F1Operator a b (gauss2F1SecondSolution a b) z = 0 := by
  unfold gauss2F1SecondSolution
  rw [gauss2F1Operator_const_mul]
  simp [hinner]

/-- The corrected Frobenius second solution satisfies the Gaussian
hypergeometric equation away from the singular points. -/
theorem gauss2F1SecondSolution_operator_eq_zero
    (a b z : ℂ) (hz : z ≠ 0) (_hz1 : z ≠ 1)
    (hbranch : Complex.I * z ∈ Complex.slitPlane) (hd : ‖z‖ < 1)
    (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    gauss2F1Operator a b (gauss2F1SecondSolution a b) z = 0 := by
  have hy₁ : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z :=
    (gauss2F1_hasDerivAt_of_norm_lt_one a b z hd).differentiableAt.hasDerivAt
  have hy₂ : HasDerivAt (deriv (gauss2F1 a b 1))
      (deriv (deriv (gauss2F1 a b 1)) z) z :=
    (gauss2F1_hasSecondDerivAt_of_norm_lt_one a b z hd).differentiableAt.hasDerivAt
  have hlog₁ : HasDerivAt (gauss2F1LogSecondPart a b)
      (deriv (gauss2F1LogSecondPart a b) z) z :=
    (gauss2F1LogSecondPart_hasDerivAt a b z hbranch hy₁).differentiableAt.hasDerivAt
  have hcorr₁ : HasDerivAt (gauss2F1FrobeniusCorrection a b)
      (deriv (gauss2F1FrobeniusCorrection a b) z) z :=
    (gauss2F1FrobeniusCorrection_hasDerivAt_of_norm_lt_one
      a b z hGa hGb hd).differentiableAt.hasDerivAt
  have h₁ : deriv (fun w =>
        gauss2F1LogSecondPart a b w + gauss2F1FrobeniusCorrection a b w) z =
      deriv (gauss2F1LogSecondPart a b) z +
        deriv (gauss2F1FrobeniusCorrection a b) z :=
    (hlog₁.add hcorr₁).deriv
  have hlog₂_raw := gauss2F1LogSecondPart_hasSecondDerivAt a b z hz hbranch hd hy₁ hy₂
  have hlog₂ : HasDerivAt (deriv (gauss2F1LogSecondPart a b))
      (deriv (deriv (gauss2F1LogSecondPart a b)) z) z :=
    hlog₂_raw.differentiableAt.hasDerivAt
  have hcorr₂ : HasDerivAt (deriv (gauss2F1FrobeniusCorrection a b))
      (deriv (deriv (gauss2F1FrobeniusCorrection a b)) z) z :=
    (gauss2F1FrobeniusCorrection_hasSecondDerivAt_of_norm_lt_one
      a b z hGa hGb hd).differentiableAt.hasDerivAt
  have hderiv_add_eventually :
      (fun w : ℂ => deriv (fun u =>
        gauss2F1LogSecondPart a b u + gauss2F1FrobeniusCorrection a b u) w) =ᶠ[𝓝 z]
        fun w : ℂ =>
          deriv (gauss2F1LogSecondPart a b) w +
            deriv (gauss2F1FrobeniusCorrection a b) w := by
    have hopen_branch : IsOpen ((fun w : ℂ => Complex.I * w) ⁻¹' Complex.slitPlane) :=
      Complex.isOpen_slitPlane.preimage (continuous_const.mul continuous_id)
    have hopen_disk : IsOpen {w : ℂ | ‖w‖ < 1} :=
      isOpen_lt continuous_norm continuous_const
    filter_upwards [hopen_branch.mem_nhds hbranch, hopen_disk.mem_nhds hd] with w hwbranch hwd
    have hyw : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) w) w :=
      (gauss2F1_hasDerivAt_of_norm_lt_one a b w hwd).differentiableAt.hasDerivAt
    have hlogw : HasDerivAt (gauss2F1LogSecondPart a b)
        (deriv (gauss2F1LogSecondPart a b) w) w :=
      (gauss2F1LogSecondPart_hasDerivAt a b w hwbranch hyw).differentiableAt.hasDerivAt
    have hcorrw : HasDerivAt (gauss2F1FrobeniusCorrection a b)
        (deriv (gauss2F1FrobeniusCorrection a b) w) w :=
      (gauss2F1FrobeniusCorrection_hasDerivAt_of_norm_lt_one
        a b w hGa hGb hwd).differentiableAt.hasDerivAt
    exact (hlogw.add hcorrw).deriv
  have h₂ : deriv (deriv (fun w =>
        gauss2F1LogSecondPart a b w + gauss2F1FrobeniusCorrection a b w)) z =
      deriv (deriv (gauss2F1LogSecondPart a b)) z +
        deriv (deriv (gauss2F1FrobeniusCorrection a b)) z :=
    ((hlog₂.add hcorr₂).congr_of_eventuallyEq hderiv_add_eventually).deriv
  have hcorr_source := gauss2F1FrobeniusCorrection_operator_eq_source a b z hz hGa hGb hd
  exact gauss2F1SecondSolution_operator_eq_zero_of_inner a b z
    (gauss2F1SecondSolution_inner_operator_eq_zero_of_correction_source
      a b z hz hbranch hd h₁ h₂ hcorr_source)

/-- The principal `₂F₁(a,b;1;z)` branch satisfies the Gaussian hypergeometric
ODE inside the convergence disk.  On the unit circle the Mathlib `tsum`
may converge while `deriv` defaults to 0, making the operator nonzero;
the correct global statement needs analytic continuation. -/
theorem gauss2F1_operator_eq_zero
    (a b z : ℂ) (_hz : z ≠ 0) (_hz1 : z ≠ 1) (hd : ‖z‖ < 1) :
    gauss2F1Operator a b (gauss2F1 a b 1) z = 0 :=
  gauss2F1_operator_eq_zero_of_norm_lt_one a b z hd

private lemma gauss2F1SecondSolution_hasDerivAt
    (a b z : ℂ) (hbranch : Complex.I * z ∈ Complex.slitPlane) (hd : ‖z‖ < 1)
    (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    HasDerivAt (gauss2F1SecondSolution a b)
      (deriv (gauss2F1SecondSolution a b) z) z := by
  have hy₁ : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z :=
    (gauss2F1_hasDerivAt_of_norm_lt_one a b z hd).differentiableAt.hasDerivAt
  have hlog : HasDerivAt (gauss2F1LogSecondPart a b)
      (deriv (gauss2F1LogSecondPart a b) z) z :=
    (gauss2F1LogSecondPart_hasDerivAt a b z hbranch hy₁).differentiableAt.hasDerivAt
  have hcorr : HasDerivAt (gauss2F1FrobeniusCorrection a b)
      (deriv (gauss2F1FrobeniusCorrection a b) z) z :=
    (gauss2F1FrobeniusCorrection_hasDerivAt_of_norm_lt_one
      a b z hGa hGb hd).differentiableAt.hasDerivAt
  have hinner : HasDerivAt
      (fun w => gauss2F1LogSecondPart a b w + gauss2F1FrobeniusCorrection a b w)
      (deriv (gauss2F1LogSecondPart a b) z +
        deriv (gauss2F1FrobeniusCorrection a b) z) z :=
    hlog.add hcorr
  unfold gauss2F1SecondSolution
  exact (hinner.const_mul (gauss2F1SecondSolutionNorm a b)).differentiableAt.hasDerivAt

private lemma gauss2F1SecondSolution_hasSecondDerivAt
    (a b z : ℂ) (hz : z ≠ 0) (hbranch : Complex.I * z ∈ Complex.slitPlane)
    (hd : ‖z‖ < 1)
    (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    HasDerivAt (deriv (gauss2F1SecondSolution a b))
      (deriv (deriv (gauss2F1SecondSolution a b)) z) z := by
  let inner : ℂ → ℂ := fun w =>
    gauss2F1LogSecondPart a b w + gauss2F1FrobeniusCorrection a b w
  have hy₁ : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z :=
    (gauss2F1_hasDerivAt_of_norm_lt_one a b z hd).differentiableAt.hasDerivAt
  have hy₂ : HasDerivAt (deriv (gauss2F1 a b 1))
      (deriv (deriv (gauss2F1 a b 1)) z) z :=
    (gauss2F1_hasSecondDerivAt_of_norm_lt_one a b z hd).differentiableAt.hasDerivAt
  have hlog₂_raw := gauss2F1LogSecondPart_hasSecondDerivAt a b z hz hbranch hd hy₁ hy₂
  have hlog₂ : HasDerivAt (deriv (gauss2F1LogSecondPart a b))
      (deriv (deriv (gauss2F1LogSecondPart a b)) z) z :=
    hlog₂_raw.differentiableAt.hasDerivAt
  have hcorr₂ : HasDerivAt (deriv (gauss2F1FrobeniusCorrection a b))
      (deriv (deriv (gauss2F1FrobeniusCorrection a b)) z) z :=
    (gauss2F1FrobeniusCorrection_hasSecondDerivAt_of_norm_lt_one
      a b z hGa hGb hd).differentiableAt.hasDerivAt
  have hderiv_add_eventually :
      (fun w : ℂ => deriv inner w) =ᶠ[𝓝 z]
        fun w : ℂ =>
          deriv (gauss2F1LogSecondPart a b) w +
            deriv (gauss2F1FrobeniusCorrection a b) w := by
    have hopen_branch : IsOpen ((fun w : ℂ => Complex.I * w) ⁻¹' Complex.slitPlane) :=
      Complex.isOpen_slitPlane.preimage (continuous_const.mul continuous_id)
    have hopen_disk : IsOpen {w : ℂ | ‖w‖ < 1} :=
      isOpen_lt continuous_norm continuous_const
    filter_upwards [hopen_branch.mem_nhds hbranch, hopen_disk.mem_nhds hd] with w hwbranch hwd
    have hyw : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) w) w :=
      (gauss2F1_hasDerivAt_of_norm_lt_one a b w hwd).differentiableAt.hasDerivAt
    have hlogw : HasDerivAt (gauss2F1LogSecondPart a b)
        (deriv (gauss2F1LogSecondPart a b) w) w :=
      (gauss2F1LogSecondPart_hasDerivAt a b w hwbranch hyw).differentiableAt.hasDerivAt
    have hcorrw : HasDerivAt (gauss2F1FrobeniusCorrection a b)
        (deriv (gauss2F1FrobeniusCorrection a b) w) w :=
      (gauss2F1FrobeniusCorrection_hasDerivAt_of_norm_lt_one
        a b w hGa hGb hwd).differentiableAt.hasDerivAt
    exact (hlogw.add hcorrw).deriv
  have hinner₂ : HasDerivAt (deriv inner) (deriv (deriv inner) z) z :=
    ((hlog₂.add hcorr₂).congr_of_eventuallyEq hderiv_add_eventually).differentiableAt.hasDerivAt
  have hscaled₂ : HasDerivAt (fun w => gauss2F1SecondSolutionNorm a b * deriv inner w)
      (gauss2F1SecondSolutionNorm a b * deriv (deriv inner) z) z :=
    hinner₂.const_mul (gauss2F1SecondSolutionNorm a b)
  have hderiv_y_eventually :
      (fun w : ℂ => deriv (gauss2F1SecondSolution a b) w) =ᶠ[𝓝 z]
        fun w : ℂ => gauss2F1SecondSolutionNorm a b * deriv inner w := by
    have hopen_branch : IsOpen ((fun w : ℂ => Complex.I * w) ⁻¹' Complex.slitPlane) :=
      Complex.isOpen_slitPlane.preimage (continuous_const.mul continuous_id)
    have hopen_disk : IsOpen {w : ℂ | ‖w‖ < 1} :=
      isOpen_lt continuous_norm continuous_const
    filter_upwards [hopen_branch.mem_nhds hbranch, hopen_disk.mem_nhds hd] with w hwbranch hwd
    have hyw : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) w) w :=
      (gauss2F1_hasDerivAt_of_norm_lt_one a b w hwd).differentiableAt.hasDerivAt
    have hlogw : HasDerivAt (gauss2F1LogSecondPart a b)
        (deriv (gauss2F1LogSecondPart a b) w) w :=
      (gauss2F1LogSecondPart_hasDerivAt a b w hwbranch hyw).differentiableAt.hasDerivAt
    have hcorrw : HasDerivAt (gauss2F1FrobeniusCorrection a b)
        (deriv (gauss2F1FrobeniusCorrection a b) w) w :=
      (gauss2F1FrobeniusCorrection_hasDerivAt_of_norm_lt_one
        a b w hGa hGb hwd).differentiableAt.hasDerivAt
    have hinnerw : HasDerivAt inner
        (deriv (gauss2F1LogSecondPart a b) w +
          deriv (gauss2F1FrobeniusCorrection a b) w) w :=
      hlogw.add hcorrw
    have hy2w : HasDerivAt (gauss2F1SecondSolution a b)
        (gauss2F1SecondSolutionNorm a b * deriv inner w) w := by
      unfold gauss2F1SecondSolution
      exact (hinnerw.differentiableAt.hasDerivAt.const_mul
        (gauss2F1SecondSolutionNorm a b))
    exact hy2w.deriv
  exact (hscaled₂.congr_of_eventuallyEq hderiv_y_eventually).differentiableAt.hasDerivAt

private lemma gauss2F1_wronskian_deriv_identity
    (a b z : ℂ) (f g : ℂ → ℂ)
    (hf₁ : HasDerivAt f (deriv f z) z)
    (hf₂ : HasDerivAt (deriv f) (deriv (deriv f) z) z)
    (hg₁ : HasDerivAt g (deriv g z) z)
    (hg₂ : HasDerivAt (deriv g) (deriv (deriv g) z) z)
    (hfode : gauss2F1Operator a b f z = 0)
    (hgode : gauss2F1Operator a b g z = 0) :
    z * (1 - z) *
        deriv (fun w => f w * deriv g w - deriv f w * g w) z =
      ((a + b + 1) * z - 1) * (f z * deriv g z - deriv f z * g z) := by
  have hleft : HasDerivAt (fun w => f w * deriv g w)
      (deriv f z * deriv g z + f z * deriv (deriv g) z) z :=
    hf₁.mul hg₂
  have hright : HasDerivAt (fun w => deriv f w * g w)
      (deriv (deriv f) z * g z + deriv f z * deriv g z) z :=
    hf₂.mul hg₁
  have hWderiv : HasDerivAt (fun w => f w * deriv g w - deriv f w * g w)
      ((deriv f z * deriv g z + f z * deriv (deriv g) z) -
        (deriv (deriv f) z * g z + deriv f z * deriv g z)) z :=
    hleft.sub hright
  rw [hWderiv.deriv]
  unfold gauss2F1Operator at hfode hgode
  have hlin :
      z * (1 - z) *
          ((deriv f z * deriv g z + f z * deriv (deriv g) z) -
            (deriv (deriv f) z * g z + deriv f z * deriv g z)) +
        (1 - (a + b + 1) * z) * (f z * deriv g z - deriv f z * g z) = 0 := by
    linear_combination f z * hgode - g z * hfode
  linear_combination hlin

private lemma one_sub_mem_slitPlane_of_norm_lt_one (z : ℂ) (hz : ‖z‖ < 1) :
    1 - z ∈ Complex.slitPlane := by
  simpa [sub_eq_add_neg] using
    Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hz)

private lemma gauss2F1FrobeniusBranchCenter_mem :
    (-Complex.I / 2 : ℂ) ∈ gauss2F1FrobeniusBranchDomain := by
  norm_num [gauss2F1FrobeniusBranchDomain, Complex.mem_slitPlane_iff,
    Complex.normSq, Complex.normSq_apply]

private lemma gauss2F1FrobeniusBranchDomain_isOpen :
    IsOpen gauss2F1FrobeniusBranchDomain := by
  dsimp [gauss2F1FrobeniusBranchDomain]
  exact (isOpen_ne (x := (0 : ℂ))).inter
    ((Complex.isOpen_slitPlane.preimage (continuous_const.mul continuous_id)).inter
      (isOpen_lt continuous_norm continuous_const))

private lemma gauss2F1FrobeniusBranchDomain_starConvex :
    StarConvex ℝ (-Complex.I / 2 : ℂ) gauss2F1FrobeniusBranchDomain := by
  intro z hz α β hα hβ hsum
  dsimp [gauss2F1FrobeniusBranchDomain] at hz ⊢
  let c : ℂ := -Complex.I / 2
  have hc_norm : ‖c‖ < 1 := by
    norm_num [c, Complex.normSq, Complex.normSq_apply]
  have hbranch : Complex.I * (α • c + β • z) ∈ Complex.slitPlane := by
    by_cases hβ0 : β = 0
    · have hα1 : α = 1 := by linarith
      subst β
      subst α
      norm_num [c, Complex.mem_slitPlane_iff]
    · have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      rw [Complex.mem_slitPlane_iff] at hz ⊢
      rcases hz.2.1 with hz_im | hz_re
      · left
        simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          Complex.add_im, Complex.smul_im, c] at hz_im ⊢
        norm_num at hz_im ⊢
        nlinarith
      · right
        simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
          Complex.add_re, Complex.smul_re, c] at hz_re ⊢
        norm_num at hz_re ⊢
        exact ⟨hβ0, hz_re⟩
  have hnorm : ‖α • c + β • z‖ < 1 := by
    have hnorm_le : ‖α • c + β • z‖ ≤ α * ‖c‖ + β * ‖z‖ := by
      calc
        ‖α • c + β • z‖ ≤ ‖α • c‖ + ‖β • z‖ := norm_add_le _ _
        _ ≤ α * ‖c‖ + β * ‖z‖ := by
          have hαle : ‖α • c‖ ≤ α * ‖c‖ := by
            simpa [Real.norm_of_nonneg hα] using (norm_smul_le α c)
          have hβle : ‖β • z‖ ≤ β * ‖z‖ := by
            simpa [Real.norm_of_nonneg hβ] using (norm_smul_le β z)
          linarith
    have hz_norm : ‖z‖ < 1 := hz.2.2
    have hc_gap : 0 < 1 - ‖c‖ := by linarith
    have hz_gap : 0 < 1 - ‖z‖ := by linarith
    have hgap : 0 < α * (1 - ‖c‖) + β * (1 - ‖z‖) := by
      by_cases hα0 : α = 0
      · have hβ1 : β = 1 := by linarith
        nlinarith
      · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        have hnonneg : 0 ≤ β * (1 - ‖z‖) := mul_nonneg hβ hz_gap.le
        linarith [mul_pos hαpos hc_gap]
    have hweighted : α * ‖c‖ + β * ‖z‖ < 1 := by
      linarith
    exact lt_of_le_of_lt hnorm_le hweighted
  refine ⟨?_, hbranch, hnorm⟩
  intro hw0
  exact Complex.slitPlane_ne_zero hbranch (by simpa [hw0])

private lemma gauss2F1FrobeniusBranchDomain_isPreconnected :
    IsPreconnected gauss2F1FrobeniusBranchDomain :=
  (gauss2F1FrobeniusBranchDomain_starConvex.isPathConnected
    gauss2F1FrobeniusBranchCenter_mem).isConnected.isPreconnected

private lemma gauss2F1_wronskian_hasDerivAt
    (z : ℂ) (f g : ℂ → ℂ)
    (hf₁ : HasDerivAt f (deriv f z) z)
    (hf₂ : HasDerivAt (deriv f) (deriv (deriv f) z) z)
    (hg₁ : HasDerivAt g (deriv g z) z)
    (hg₂ : HasDerivAt (deriv g) (deriv (deriv g) z) z) :
    HasDerivAt (fun w => f w * deriv g w - deriv f w * g w)
      ((deriv f z * deriv g z + f z * deriv (deriv g) z) -
        (deriv (deriv f) z * g z + deriv f z * deriv g z)) z := by
  exact (hf₁.mul hg₂).sub (hf₂.mul hg₁)

private lemma gauss2F1_scaled_wronskian_hasDerivAt_zero
    (a b z : ℂ) (f g : ℂ → ℂ) (hz : z ≠ 0) (hz1 : z ≠ 1)
    (hslit : 1 - z ∈ Complex.slitPlane)
    (hf₁ : HasDerivAt f (deriv f z) z)
    (hf₂ : HasDerivAt (deriv f) (deriv (deriv f) z) z)
    (hg₁ : HasDerivAt g (deriv g z) z)
    (hg₂ : HasDerivAt (deriv g) (deriv (deriv g) z) z)
    (hfode : gauss2F1Operator a b f z = 0)
    (hgode : gauss2F1Operator a b g z = 0) :
    HasDerivAt
      (fun w => w * (1 - w) ^ (a + b) *
        (f w * deriv g w - deriv f w * g w)) 0 z := by
  let W : ℂ → ℂ := fun w => f w * deriv g w - deriv f w * g w
  let W' : ℂ :=
    (deriv f z * deriv g z + f z * deriv (deriv g) z) -
      (deriv (deriv f) z * g z + deriv f z * deriv g z)
  have hW : HasDerivAt W W' z := by
    simpa [W, W'] using gauss2F1_wronskian_hasDerivAt z f g hf₁ hf₂ hg₁ hg₂
  have hWderiv : deriv W z = W' := hW.deriv
  have hAbel :
      z * (1 - z) * W' =
        ((a + b + 1) * z - 1) * W z := by
    rw [← hWderiv]
    simpa [W] using
      gauss2F1_wronskian_deriv_identity a b z f g hf₁ hf₂ hg₁ hg₂ hfode hgode
  have hbase : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_const (x := z) (c := (1 : ℂ))).sub (hasDerivAt_id z)
  have hpow : HasDerivAt (fun w : ℂ => (1 - w) ^ (a + b))
      (-(a + b) * (1 - z) ^ (a + b - 1)) z := by
    convert hbase.cpow_const (c := a + b) hslit using 1
    ring
  have hscale : HasDerivAt (fun w : ℂ => w * (1 - w) ^ (a + b))
      ((1 - z) ^ (a + b) - z * (a + b) * (1 - z) ^ (a + b - 1)) z := by
    convert (hasDerivAt_id z).mul hpow using 1
    simp only [id_eq]
    ring
  have hprod := hscale.mul hW
  have hone_ne : (1 - z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hpow_step :
      (1 - z) ^ (a + b) = (1 - z) ^ (a + b - 1) * (1 - z) := by
    calc
      (1 - z) ^ (a + b) = (1 - z) ^ ((a + b - 1) + 1) := by
        congr 1
        ring
      _ = (1 - z) ^ (a + b - 1) * (1 - z) := by
        rw [Complex.cpow_add _ _ hone_ne, Complex.cpow_one]
  have hzero :
      ((1 - z) ^ (a + b) - z * (a + b) * (1 - z) ^ (a + b - 1)) * W z +
          z * (1 - z) ^ (a + b) * W' = 0 := by
    rw [hpow_step]
    calc
      ((1 - z) ^ (a + b - 1) * (1 - z) -
            z * (a + b) * (1 - z) ^ (a + b - 1)) * W z +
          z * ((1 - z) ^ (a + b - 1) * (1 - z)) * W' =
          (1 - z) ^ (a + b - 1) *
            (((1 - z) - z * (a + b)) * W z + z * (1 - z) * W') := by
            ring
      _ = (1 - z) ^ (a + b - 1) *
            (((1 - z) - z * (a + b)) * W z +
              ((a + b + 1) * z - 1) * W z) := by
            rw [hAbel]
      _ = 0 := by
            ring
  simpa [W, hzero] using hprod

private lemma gauss2F1SecondSolution_wronskian_decompose
    (a b z : ℂ) (hz : z ≠ 0)
    (hbranch : Complex.I * z ∈ Complex.slitPlane) (hd : ‖z‖ < 1)
    (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
        deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z =
      gauss2F1SecondSolutionNorm a b *
        (gauss2F1 a b 1 z ^ 2 / z +
          gauss2F1 a b 1 z * deriv (gauss2F1FrobeniusCorrection a b) z -
          deriv (gauss2F1 a b 1) z * gauss2F1FrobeniusCorrection a b z) := by
  have hy₁ : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z :=
    (gauss2F1_hasDerivAt_of_norm_lt_one a b z hd).differentiableAt.hasDerivAt
  have hlog : HasDerivAt (gauss2F1LogSecondPart a b)
      (z⁻¹ * gauss2F1 a b 1 z +
        Complex.log (Complex.I * z) * deriv (gauss2F1 a b 1) z) z :=
    gauss2F1LogSecondPart_hasDerivAt a b z hbranch hy₁
  have hcorr : HasDerivAt (gauss2F1FrobeniusCorrection a b)
      (deriv (gauss2F1FrobeniusCorrection a b) z) z :=
    (gauss2F1FrobeniusCorrection_hasDerivAt_of_norm_lt_one
      a b z hGa hGb hd).differentiableAt.hasDerivAt
  have hinner : HasDerivAt
      (fun w => gauss2F1LogSecondPart a b w + gauss2F1FrobeniusCorrection a b w)
      (z⁻¹ * gauss2F1 a b 1 z +
        Complex.log (Complex.I * z) * deriv (gauss2F1 a b 1) z +
        deriv (gauss2F1FrobeniusCorrection a b) z) z :=
    hlog.add hcorr
  have hsecond : HasDerivAt (gauss2F1SecondSolution a b)
      (gauss2F1SecondSolutionNorm a b *
        (z⁻¹ * gauss2F1 a b 1 z +
          Complex.log (Complex.I * z) * deriv (gauss2F1 a b 1) z +
          deriv (gauss2F1FrobeniusCorrection a b) z)) z := by
    unfold gauss2F1SecondSolution
    exact hinner.const_mul (gauss2F1SecondSolutionNorm a b)
  rw [hsecond.deriv]
  unfold gauss2F1SecondSolution gauss2F1LogSecondPart
  field_simp [hz]
  ring

private lemma gauss2F1_zero (a b : ℂ) :
    gauss2F1 a b 1 0 = 1 := by
  rw [gauss2F1_one_eq_tsum]
  rw [tsum_eq_single 0]
  · simp [gauss2F1Coeff, ordinaryHypergeometricCoefficient]
  · intro n hn
    cases n with
    | zero => exact False.elim (hn rfl)
    | succ n => simp

private lemma gauss2F1FrobeniusCorrection_zero (a b : ℂ) :
    gauss2F1FrobeniusCorrection a b 0 = 0 := by
  unfold gauss2F1FrobeniusCorrection
  simp

private lemma gauss2F1_continuousAt_zero (a b : ℂ) :
    ContinuousAt (gauss2F1 a b 1) 0 :=
  (gauss2F1_hasDerivAt_of_norm_lt_one a b 0 (by norm_num)).continuousAt

private lemma gauss2F1_deriv_continuousAt_zero (a b : ℂ) :
    ContinuousAt (fun z => deriv (gauss2F1 a b 1) z) 0 :=
  (gauss2F1_hasSecondDerivAt_of_norm_lt_one a b 0 (by norm_num)).continuousAt

private lemma gauss2F1FrobeniusCorrection_continuousAt_zero
    (a b : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    ContinuousAt (gauss2F1FrobeniusCorrection a b) 0 :=
  (gauss2F1FrobeniusCorrection_hasDerivAt_of_norm_lt_one
    a b 0 hGa hGb (by norm_num)).continuousAt

private lemma gauss2F1FrobeniusCorrection_deriv_continuousAt_zero
    (a b : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    ContinuousAt (fun z => deriv (gauss2F1FrobeniusCorrection a b) z) 0 :=
  (gauss2F1FrobeniusCorrection_hasSecondDerivAt_of_norm_lt_one
    a b 0 hGa hGb (by norm_num)).continuousAt

private lemma gauss2F1_frobenius_regularized_inner_tendsto_one
    (a b : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    Tendsto (fun z : ℂ =>
      gauss2F1 a b 1 z ^ 2 +
        z * (gauss2F1 a b 1 z * deriv (gauss2F1FrobeniusCorrection a b) z -
          deriv (gauss2F1 a b 1) z * gauss2F1FrobeniusCorrection a b z))
      (𝓝 0) (𝓝 1) := by
  have hy : Tendsto (gauss2F1 a b 1) (𝓝 0) (𝓝 1) := by
    simpa [gauss2F1_zero] using (gauss2F1_continuousAt_zero a b).tendsto
  have hy' : Tendsto (fun z => deriv (gauss2F1 a b 1) z) (𝓝 0)
      (𝓝 (deriv (gauss2F1 a b 1) 0)) :=
    (gauss2F1_deriv_continuousAt_zero a b).tendsto
  have hG : Tendsto (gauss2F1FrobeniusCorrection a b) (𝓝 0) (𝓝 0) := by
    simpa [gauss2F1FrobeniusCorrection_zero] using
      (gauss2F1FrobeniusCorrection_continuousAt_zero a b hGa hGb).tendsto
  have hG' : Tendsto (fun z => deriv (gauss2F1FrobeniusCorrection a b) z) (𝓝 0)
      (𝓝 (deriv (gauss2F1FrobeniusCorrection a b) 0)) :=
    (gauss2F1FrobeniusCorrection_deriv_continuousAt_zero a b hGa hGb).tendsto
  have hbracket : Tendsto (fun z : ℂ =>
      gauss2F1 a b 1 z * deriv (gauss2F1FrobeniusCorrection a b) z -
        deriv (gauss2F1 a b 1) z * gauss2F1FrobeniusCorrection a b z)
      (𝓝 0) (𝓝 (1 * deriv (gauss2F1FrobeniusCorrection a b) 0 -
        deriv (gauss2F1 a b 1) 0 * 0)) := by
    exact (hy.mul hG').sub (hy'.mul hG)
  have hz : Tendsto (fun z : ℂ => z) (𝓝 0) (𝓝 0) := tendsto_id
  have hmain := (hy.mul hy).add (hz.mul hbracket)
  simpa [pow_two] using hmain

private lemma gauss2F1_frobenius_punctured_inner_tendsto_one
    (a b : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    Tendsto (fun z : ℂ =>
      z * (gauss2F1 a b 1 z ^ 2 / z +
        gauss2F1 a b 1 z * deriv (gauss2F1FrobeniusCorrection a b) z -
          deriv (gauss2F1 a b 1) z * gauss2F1FrobeniusCorrection a b z))
      (𝓝[≠] 0) (𝓝 1) := by
  have hmain :=
    (gauss2F1_frobenius_regularized_inner_tendsto_one a b hGa hGb).mono_left
      (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  field_simp [hz0]
  ring

private lemma gauss2F1SecondSolution_regularized_wronskian_tendsto_norm
    (a b : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    Tendsto (fun z : ℂ =>
      z * (gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
        deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z))
      (𝓝[{z : ℂ | z ≠ 0 ∧ Complex.I * z ∈ Complex.slitPlane ∧ ‖z‖ < 1}] 0)
      (𝓝 (gauss2F1SecondSolutionNorm a b)) := by
  let D : Set ℂ := {z : ℂ | z ≠ 0 ∧ Complex.I * z ∈ Complex.slitPlane ∧ ‖z‖ < 1}
  let inner : ℂ → ℂ := fun z =>
    gauss2F1 a b 1 z ^ 2 / z +
      gauss2F1 a b 1 z * deriv (gauss2F1FrobeniusCorrection a b) z -
        deriv (gauss2F1 a b 1) z * gauss2F1FrobeniusCorrection a b z
  have hinner : Tendsto (fun z : ℂ => z * inner z) (𝓝[D] 0) (𝓝 1) := by
    have hpunct := gauss2F1_frobenius_punctured_inner_tendsto_one a b hGa hGb
    exact hpunct.mono_left (nhdsWithin_mono 0 (by
      intro z hz
      exact hz.1))
  have hnorm : Tendsto (fun z : ℂ => gauss2F1SecondSolutionNorm a b * (z * inner z))
      (𝓝[D] 0) (𝓝 (gauss2F1SecondSolutionNorm a b)) := by
    simpa using hinner.const_mul (gauss2F1SecondSolutionNorm a b)
  refine hnorm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hzD
  have hdecomp := gauss2F1SecondSolution_wronskian_decompose
    a b z hzD.1 hzD.2.1 hzD.2.2 hGa hGb
  dsimp [inner]
  rw [hdecomp]
  ring

private lemma zero_mem_closure_gauss2F1FrobeniusBranchDomain :
    (0 : ℂ) ∈ closure gauss2F1FrobeniusBranchDomain := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := by
    have hδle : δ ≤ ε / 2 := min_le_left _ _
    linarith
  have hδ1 : δ < 1 := by
    have hδle : δ ≤ 1 / 2 := min_le_right _ _
    linarith
  have hnorm : ‖(-(δ : ℂ))‖ = δ := by
    rw [norm_neg]
    apply (sq_eq_sq₀ (norm_nonneg _) hδpos.le).mp
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  refine ⟨-(δ : ℂ), ?_, ?_⟩
  · dsimp [gauss2F1FrobeniusBranchDomain]
    refine ⟨?_, ?_, ?_⟩
    · exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hδpos.ne')
    · rw [Complex.mem_slitPlane_iff]
      right
      simp [hδpos.ne']
    · simpa [hnorm] using hδ1
  · have habsδ : |δ| = δ := abs_of_nonneg hδpos.le
    simpa [dist_eq_norm, hnorm, habsδ] using hδε

private lemma gauss2F1SecondSolution_scaled_wronskian_tendsto_norm
    (a b : ℂ) (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    Tendsto (fun z : ℂ =>
      z * (1 - z) ^ (a + b) *
        (gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
          deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z))
      (𝓝[gauss2F1FrobeniusBranchDomain] 0)
      (𝓝 (gauss2F1SecondSolutionNorm a b)) := by
  let W : ℂ → ℂ := fun z =>
    gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
      deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z
  have hreg : Tendsto (fun z : ℂ => z * W z)
      (𝓝[gauss2F1FrobeniusBranchDomain] 0)
      (𝓝 (gauss2F1SecondSolutionNorm a b)) := by
    simpa [W, gauss2F1FrobeniusBranchDomain] using
      gauss2F1SecondSolution_regularized_wronskian_tendsto_norm a b hGa hGb
  have hpow_at : ContinuousAt (fun z : ℂ => (1 - z) ^ (a + b)) 0 := by
    have hbase : ContinuousAt (fun z : ℂ => 1 - z) 0 :=
      continuousAt_const.sub continuousAt_id
    have hexp : ContinuousAt (fun _ : ℂ => a + b) 0 := continuousAt_const
    exact hbase.cpow hexp (by simp)
  have hpow : Tendsto (fun z : ℂ => (1 - z) ^ (a + b))
      (𝓝[gauss2F1FrobeniusBranchDomain] 0) (𝓝 1) := by
    simpa using hpow_at.tendsto.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun z : ℂ => (z * W z) * (1 - z) ^ (a + b))
      (𝓝[gauss2F1FrobeniusBranchDomain] 0)
      (𝓝 (gauss2F1SecondSolutionNorm a b)) := by
    simpa using hreg.mul hpow
  refine hprod.congr' ?_
  filter_upwards with z
  dsimp [W]
  ring

private lemma gauss2F1SecondSolution_scaled_wronskian_eq_norm
    (a b z : ℂ) (hzD : z ∈ gauss2F1FrobeniusBranchDomain)
    (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    z * (1 - z) ^ (a + b) *
        (gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
          deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z) =
      gauss2F1SecondSolutionNorm a b := by
  let F : ℂ → ℂ := fun w =>
    w * (1 - w) ^ (a + b) *
      (gauss2F1 a b 1 w * deriv (gauss2F1SecondSolution a b) w -
        deriv (gauss2F1 a b 1) w * gauss2F1SecondSolution a b w)
  let c : ℂ := -Complex.I / 2
  have hcD : c ∈ gauss2F1FrobeniusBranchDomain := by
    simpa [c] using gauss2F1FrobeniusBranchCenter_mem
  have hFderiv : ∀ w ∈ gauss2F1FrobeniusBranchDomain, HasDerivAt F 0 w := by
    intro w hw
    have hw0 : w ≠ 0 := hw.1
    have hwbranch : Complex.I * w ∈ Complex.slitPlane := hw.2.1
    have hwd : ‖w‖ < 1 := hw.2.2
    have hw1 : w ≠ 1 := by
      intro h
      have : ‖w‖ = 1 := by simp [h]
      linarith
    have hslit : 1 - w ∈ Complex.slitPlane :=
      one_sub_mem_slitPlane_of_norm_lt_one w hwd
    have hy₁ : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) w) w :=
      (gauss2F1_hasDerivAt_of_norm_lt_one a b w hwd).differentiableAt.hasDerivAt
    have hy₂ : HasDerivAt (deriv (gauss2F1 a b 1))
        (deriv (deriv (gauss2F1 a b 1)) w) w :=
      (gauss2F1_hasSecondDerivAt_of_norm_lt_one a b w hwd).differentiableAt.hasDerivAt
    have hy2₁ : HasDerivAt (gauss2F1SecondSolution a b)
        (deriv (gauss2F1SecondSolution a b) w) w :=
      gauss2F1SecondSolution_hasDerivAt a b w hwbranch hwd hGa hGb
    have hy2₂ : HasDerivAt (deriv (gauss2F1SecondSolution a b))
        (deriv (deriv (gauss2F1SecondSolution a b)) w) w :=
      gauss2F1SecondSolution_hasSecondDerivAt a b w hw0 hwbranch hwd hGa hGb
    have hyode : gauss2F1Operator a b (gauss2F1 a b 1) w = 0 :=
      gauss2F1_operator_eq_zero_of_norm_lt_one a b w hwd
    have hy2ode : gauss2F1Operator a b (gauss2F1SecondSolution a b) w = 0 :=
      gauss2F1SecondSolution_operator_eq_zero a b w hw0 hw1 hwbranch hwd hGa hGb
    simpa [F] using
      gauss2F1_scaled_wronskian_hasDerivAt_zero a b w
        (gauss2F1 a b 1) (gauss2F1SecondSolution a b) hw0 hw1 hslit
        hy₁ hy₂ hy2₁ hy2₂ hyode hy2ode
  have hdiff : DifferentiableOn ℂ F gauss2F1FrobeniusBranchDomain := by
    intro w hw
    exact (hFderiv w hw).differentiableAt.differentiableWithinAt
  have hderiv_zero : gauss2F1FrobeniusBranchDomain.EqOn (deriv F) 0 := by
    intro w hw
    exact (hFderiv w hw).deriv
  have hconst_zc : F z = F c :=
    gauss2F1FrobeniusBranchDomain_isOpen.is_const_of_deriv_eq_zero
      gauss2F1FrobeniusBranchDomain_isPreconnected hdiff hderiv_zero hzD hcD
  have hconst_on : gauss2F1FrobeniusBranchDomain.EqOn F (fun _ : ℂ => F c) := by
    intro w hw
    exact gauss2F1FrobeniusBranchDomain_isOpen.is_const_of_deriv_eq_zero
      gauss2F1FrobeniusBranchDomain_isPreconnected hdiff hderiv_zero hw hcD
  have hlimF : Tendsto F (𝓝[gauss2F1FrobeniusBranchDomain] 0)
      (𝓝 (gauss2F1SecondSolutionNorm a b)) := by
    simpa [F] using
      gauss2F1SecondSolution_scaled_wronskian_tendsto_norm a b hGa hGb
  haveI : NeBot (𝓝[gauss2F1FrobeniusBranchDomain] (0 : ℂ)) :=
    mem_closure_iff_nhdsWithin_neBot.mp zero_mem_closure_gauss2F1FrobeniusBranchDomain
  have hlimFc : Tendsto F (𝓝[gauss2F1FrobeniusBranchDomain] 0) (𝓝 (F c)) := by
    exact tendsto_const_nhds.congr' hconst_on.eventuallyEq_nhdsWithin.symm
  have hc_eq : F c = gauss2F1SecondSolutionNorm a b :=
    tendsto_nhds_unique hlimFc hlimF
  calc
    z * (1 - z) ^ (a + b) *
        (gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
          deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z) = F z := by
          rfl
    _ = F c := hconst_zc
    _ = gauss2F1SecondSolutionNorm a b := hc_eq

/- Abel/Wronskian evaluation for the true Frobenius pair, including the
normalizing constant determined by the local Frobenius expansion at zero. -/
/-- Abel/Wronskian for the Frobenius pair.  The `Gamma a ≠ 0` hypotheses
exclude non-positive-integer parameters where `Complex.Gamma` returns 0 by
convention but the actual Wronskian is nonzero (e.g. a=b=0 gives W=1/z).

The Abel factor is `(1 - z) ^ (a + b)`.  A denominator `z * (1 - z)` would be
false for general parameters: the Frobenius expansion gives constant term
`a + b` after the leading `1/z`, while `1 / (z * (1 - z))` has constant term
`1` (for example `a = b = 1/4`).

The branch and disk hypotheses are the local Frobenius domain where the
present `tsum` and `log (i z)` infrastructure proves differentiability. -/
theorem hypergeom_frobenius_wronskian_from_abel
    (a b z : ℂ) (hz : z ≠ 0) (hz1 : z ≠ 1)
    (hbranch : Complex.I * z ∈ Complex.slitPlane) (hd : ‖z‖ < 1)
    (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0)
    (_hy₁ : gauss2F1Operator a b (gauss2F1 a b 1) z = 0)
    (_hy₂ : gauss2F1Operator a b (gauss2F1SecondSolution a b) z = 0) :
    gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
      deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z =
        Complex.Gamma a * Complex.Gamma b /
          (2 * (Real.pi : ℂ) * Complex.I * z * (1 - z) ^ (a + b)) := by
  let W : ℂ :=
    gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
      deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z
  let P : ℂ := (1 - z) ^ (a + b)
  have hzD : z ∈ gauss2F1FrobeniusBranchDomain := ⟨hz, hbranch, hd⟩
  have hscaled :
      z * P * W = Complex.Gamma a * Complex.Gamma b /
        (2 * (Real.pi : ℂ) * Complex.I) := by
    simpa [W, P, gauss2F1SecondSolutionNorm] using
      gauss2F1SecondSolution_scaled_wronskian_eq_norm a b z hzD hGa hGb
  have hone : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hP : P ≠ 0 := by
    dsimp [P]
    change (1 - z) ^ (a + b) ≠ 0
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl hone
  have hden : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    norm_num [Complex.ext_iff, Real.pi_ne_zero]
  calc
    gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
        deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z = W := by
          rfl
    _ = (z * P * W) / (z * P) := by
          field_simp [hz, hP]
    _ = (Complex.Gamma a * Complex.Gamma b /
          (2 * (Real.pi : ℂ) * Complex.I)) / (z * P) := by
          rw [hscaled]
    _ = Complex.Gamma a * Complex.Gamma b /
          (2 * (Real.pi : ℂ) * Complex.I * z * (1 - z) ^ (a + b)) := by
          dsimp [P]
          field_simp [hden, hz, hP]

/-- Wronskian of the normalized `₂F₁(a,b;1;z)` branch and its second
solution.  This is the Picard-Fuchs/Legendre-relation bridge that exposes the
`1 / π` factor. -/
theorem hypergeom_wronskian (a b : ℂ) (z : ℂ) (hz : z ≠ 0) (hz1 : z ≠ 1)
    (hbranch : Complex.I * z ∈ Complex.slitPlane) (hd : ‖z‖ < 1)
    (hGa : Complex.Gamma a ≠ 0) (hGb : Complex.Gamma b ≠ 0) :
    gauss2F1 a b 1 z * deriv (gauss2F1SecondSolution a b) z -
      deriv (gauss2F1 a b 1) z * gauss2F1SecondSolution a b z =
        Complex.Gamma a * Complex.Gamma b /
          (2 * (Real.pi : ℂ) * Complex.I * z * (1 - z) ^ (a + b)) := by
  exact hypergeom_frobenius_wronskian_from_abel a b z hz hz1 hbranch hd hGa hGb
    (gauss2F1_operator_eq_zero_of_norm_lt_one a b z hd)
    (gauss2F1SecondSolution_operator_eq_zero a b z hz hz1 hbranch hd hGa hGb)

/-- Real-parameter wrapper for the Wronskian theorem. -/
theorem hypergeom_wronskian_real (a b : ℝ) (z : ℂ) (hz : z ≠ 0) (hz1 : z ≠ 1)
    (hbranch : Complex.I * z ∈ Complex.slitPlane) (hd : ‖z‖ < 1)
    (hGa : Complex.Gamma (a : ℂ) ≠ 0)
    (hGb : Complex.Gamma (b : ℂ) ≠ 0) :
    gauss2F1 (a : ℂ) (b : ℂ) 1 z *
        deriv (gauss2F1SecondSolution (a : ℂ) (b : ℂ)) z -
      deriv (gauss2F1 (a : ℂ) (b : ℂ) 1) z *
        gauss2F1SecondSolution (a : ℂ) (b : ℂ) z =
        (Real.Gamma a : ℂ) * (Real.Gamma b : ℂ) /
          (2 * (Real.pi : ℂ) * Complex.I * z * (1 - z) ^ ((a : ℂ) + (b : ℂ))) := by
  simpa [Complex.Gamma_ofReal] using
    hypergeom_wronskian (a : ℂ) (b : ℂ) z hz hz1 hbranch hd hGa hGb

/-- Euler integral kernel for `₂F₁(1/2,1/2;1;z)`. -/
noncomputable def eulerHalfKernel (z : ℂ) (t : ℝ) : ℂ :=
    (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) *
        (1 - z * (t : ℂ)) ^ (-(1 / 2 : ℂ))

private lemma eulerHalfKernel_series_hasSum {z : ℂ} (hz : ‖z‖ < 1) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ =>
        (t : ℂ) ^ (-(1 / 2 : ℂ)) *
          (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) *
            (Ring.choose ((1 / 2 : ℂ) + n - 1) n * (z * (t : ℂ)) ^ n))
      (eulerHalfKernel z t) := by
  have hnormt : ‖(t : ℂ)‖ ≤ 1 := by
    have hnormt_eq : ‖(t : ℂ)‖ = t := by
      apply (sq_eq_sq₀ (norm_nonneg _) ht.1.le).mp
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    rw [hnormt_eq]
    exact ht.2.le
  have hzt_norm : ‖z * (t : ℂ)‖ < 1 :=
    (norm_mul_le z (t : ℂ)).trans_lt
      (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hz hnormt)
  have hy : z * (t : ℂ) ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right]
    exact ENNReal.coe_lt_coe.mpr
      (by simpa using hzt_norm : ‖z * (t : ℂ)‖₊ < (1 : NNReal))
  have hbin := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
    (1 / 2 : ℂ)).hasSum hy
  simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff, eulerHalfKernel,
    mul_assoc, mul_left_comm, mul_comm, Complex.cpow_neg] using
      hbin.mul_left ((t : ℂ) ^ (-(1 / 2 : ℂ)) *
        (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)))

/-- Euler integral for `₂F₁(1/2,1/2;1;z)`. -/
noncomputable def eulerHalfIntegral (z : ℂ) : ℂ :=
  ∫ t : ℝ in 0..1, eulerHalfKernel z t

private lemma binomial_half_summable_norm_of_lt {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun n : ℕ => ‖Ring.choose ((1 / 2 : ℂ) + n - 1) n‖ * r ^ n := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    .ofScalars ℂ fun n : ℕ => Ring.choose ((1 / 2 : ℂ) + n - 1) n
  let rnn : NNReal := ⟨r, hr0⟩
  have hp : HasFPowerSeriesOnBall (fun x : ℂ => 1 / (1 - x) ^ (1 / 2 : ℂ)) p 0 1 := by
    exact Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℂ)
  have hnn : rnn < (1 : NNReal) := by
    dsimp [rnn]
    exact_mod_cast hr
  have hlt : ENNReal.ofNNReal rnn < p.radius := by
    exact (ENNReal.coe_lt_coe.mpr hnn).trans_le hp.r_le
  have hs := p.summable_norm_mul_pow (r := rnn) hlt
  simpa [p, rnn, FormalMultilinearSeries.ofScalars_norm] using hs

private lemma eulerHalfKernel_base_norm_intervalIntegrable :
    IntervalIntegrable (fun t : ℝ => ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ))‖) MeasureTheory.volume 0 1 := by
  have hbase : IntervalIntegrable (fun t : ℝ =>
      (t : ℂ) ^ ((1 / 2 : ℂ) - 1) *
      (1 - (t : ℂ)) ^ ((1 / 2 : ℂ) - 1)) MeasureTheory.volume 0 1 := by
    exact Complex.betaIntegral_convergent (by norm_num [Complex.ext_iff])
      (by norm_num [Complex.ext_iff])
  convert hbase.norm using 1
  ext t
  congr 2 <;> ring

private lemma eulerHalfKernel_series_bound (z : ℂ) (n : ℕ) :
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ι (0 : ℝ) 1 →
      ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) *
          (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) *
            (Ring.choose ((1 / 2 : ℂ) + n - 1) n * (z * (t : ℂ)) ^ n)‖ ≤
        ‖Ring.choose ((1 / 2 : ℂ) + n - 1) n‖ * ‖z‖ ^ n *
          ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) *
            (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ))‖ := by
  refine MeasureTheory.ae_of_all _ ?_
  intro t ht
  have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc ht
  have hnormt : ‖(t : ℂ)‖ ≤ 1 := by
    have ht01 : 0 ≤ t ∧ t ≤ 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht'
    have hnormt_eq : ‖(t : ℂ)‖ = |t| := by simp
    rw [hnormt_eq, abs_of_nonneg ht01.1]
    exact ht01.2
  calc
    ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) *
          (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) *
            (Ring.choose ((1 / 2 : ℂ) + n - 1) n * (z * (t : ℂ)) ^ n)‖
        = ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) *
            (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ))‖ *
          (‖Ring.choose ((1 / 2 : ℂ) + n - 1) n‖ * ‖z * (t : ℂ)‖ ^ n) := by
          rw [norm_mul,
            norm_mul (Ring.choose ((1 / 2 : ℂ) + n - 1) n) ((z * (t : ℂ)) ^ n),
            norm_pow]
    _ ≤ ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) *
            (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ))‖ *
          (‖Ring.choose ((1 / 2 : ℂ) + n - 1) n‖ * ‖z‖ ^ n) := by
          gcongr
          exact (norm_mul_le z (t : ℂ)).trans
            (mul_le_of_le_one_right (norm_nonneg z) hnormt)
    _ = ‖Ring.choose ((1 / 2 : ℂ) + n - 1) n‖ * ‖z‖ ^ n *
          ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) *
            (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ))‖ := by ring

private lemma eulerHalfKernel_bound_integrable (z : ℂ) (hz : ‖z‖ < 1) :
    IntervalIntegrable (fun t : ℝ => ∑' n : ℕ,
        ‖Ring.choose ((1 / 2 : ℂ) + n - 1) n‖ * ‖z‖ ^ n *
          ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) *
            (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ))‖) MeasureTheory.volume 0 1 := by
  have hs : Summable fun n : ℕ =>
      ‖Ring.choose ((1 / 2 : ℂ) + n - 1) n‖ * ‖z‖ ^ n :=
    binomial_half_summable_norm_of_lt (norm_nonneg z) hz
  convert eulerHalfKernel_base_norm_intervalIntegrable.const_mul
    (∑' n : ℕ, ‖Ring.choose ((1 / 2 : ℂ) + n - 1) n‖ * ‖z‖ ^ n) using 1
  ext t
  rw [hs.tsum_mul_right]

private lemma eulerHalfIntegral_series_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ∫ t : ℝ in 0..1,
        (t : ℂ) ^ (-(1 / 2 : ℂ)) *
          (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) *
            (Ring.choose ((1 / 2 : ℂ) + n - 1) n * (z * (t : ℂ)) ^ n))
      (eulerHalfIntegral z) := by
  unfold eulerHalfIntegral
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
    (fun n t => ‖Ring.choose ((1 / 2 : ℂ) + n - 1) n‖ * ‖z‖ ^ n *
      ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) *
        (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ))‖) ?_ ?_ ?_ ?_ ?_
  · intro n
    fun_prop
  · exact eulerHalfKernel_series_bound z
  · refine MeasureTheory.ae_of_all _ ?_
    intro t ht
    exact (binomial_half_summable_norm_of_lt (norm_nonneg z) hz).mul_right
      ‖(t : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ))‖
  · exact eulerHalfKernel_bound_integrable z hz
  · refine MeasureTheory.ae_of_all _ ?_
    intro t ht
    have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    by_cases ht1 : t = 1
    · subst t
      simp [eulerHalfKernel]
    · exact eulerHalfKernel_series_hasSum hz ⟨htIoc.1, lt_of_le_of_ne htIoc.2 ht1⟩

theorem eulerHalfIntegral_zero :
    eulerHalfIntegral 0 = (Real.pi : ℂ) := by
  rw [← betaIntegral_half_half_eq_pi]
  unfold eulerHalfIntegral eulerHalfKernel Complex.betaIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  norm_num [Complex.one_cpow]

theorem eulerHalfIntegral_zero_eq_two_ellipticK_zero :
    eulerHalfIntegral ((0 : ℂ) ^ 2) = 2 * ellipticK 0 := by
  simp [eulerHalfIntegral_zero]
  ring_nf

/-- Euler's integral representation for the normalized branch
`₂F₁(1/2,1/2;1;z)`.  This is the analytic theorem missing from Mathlib's
current `ordinaryHypergeometric` API. -/
theorem gauss2F1_half_half_one_eq_eulerHalfIntegral (z : ℂ) (hz : ‖z‖ < 1) :
    gauss2F1 (1 / 2) (1 / 2) 1 z =
      (1 / (Real.pi : ℂ)) * eulerHalfIntegral z := by
  rw [gauss2F1_half_half_one_eq_tsum]
  have hseries : HasSum (fun n : ℕ =>
      Ring.choose ((1 / 2 : ℂ) + n - 1) n * z ^ n *
        Complex.betaIntegral ((n : ℂ) + 1 / 2) (1 / 2))
      (eulerHalfIntegral z) := by
    convert eulerHalfIntegral_series_hasSum z hz using 1
    ext n
    exact (eulerHalfKernel_seriesTerm_integral z n).symm
  have hscaled := hseries.mul_left (1 / (Real.pi : ℂ))
  have htarget : HasSum (fun n : ℕ =>
      ((ascPochhammer ℂ n).eval (1 / 2 : ℂ) *
            (ascPochhammer ℂ n).eval (1 / 2 : ℂ) /
          (Nat.factorial n : ℂ) ^ 2) * z ^ n)
      ((1 / (Real.pi : ℂ)) * eulerHalfIntegral z) := by
    convert hscaled using 1
    ext n
    rw [← beta_half_coeff_eq_hypergeom_coeff n]
    ring
  exact htarget.tsum_eq

/-- The substitution `t = sin² θ` in the Euler integral, with the principal
complex power branch. -/
theorem eulerHalfIntegral_k_sq_eq_pullback (k : ℂ) :
    eulerHalfIntegral (k ^ 2) =
      ∫ θ : ℝ in 0..Real.pi / 2,
        (2 * Real.sin θ * Real.cos θ : ℝ) •
          eulerHalfKernel (k ^ 2) (Real.sin θ ^ 2) := by
  unfold eulerHalfIntegral
  symm
  have hsubst := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
      (f := fun θ : ℝ => Real.sin θ ^ 2)
      (f' := fun θ : ℝ => 2 * Real.sin θ * Real.cos θ)
      (g := eulerHalfKernel (k ^ 2))
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (hf := (Real.continuous_sin.pow 2).continuousOn)
      (hff' := by
        intro θ hθ
        have hs : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
        convert hs.pow 2 using 1
        ring)
      (hf' := by
        intro θ hθ
        have hpi2nonneg : 0 ≤ Real.pi / 2 := by positivity
        rw [min_eq_left hpi2nonneg, max_eq_right hpi2nonneg] at hθ
        have hsin : 0 ≤ Real.sin θ := by
          apply Real.sin_nonneg_of_mem_Icc
          constructor <;> linarith [hθ.1, hθ.2]
        have hcos : 0 ≤ Real.cos θ := by
          apply Real.cos_nonneg_of_mem_Icc
          constructor <;> linarith [hθ.1, hθ.2]
        positivity)
  simpa only [Function.comp_apply, Real.sin_zero, Real.sin_pi_div_two,
    zero_pow, one_pow, pow_two, zero_mul, one_mul] using hsubst

private lemma cpow_neg_half_sq_mul_self_of_pos {x : ℝ} (hx : 0 < x) :
    ((x ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * (x : ℂ) = 1 := by
  have hexp : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by
    norm_num
  rw [hexp]
  rw [← Complex.ofReal_cpow (sq_nonneg x) (-(1 / 2 : ℝ))]
  rw [← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [Real.rpow_def_of_pos (sq_pos_of_pos hx)]
  rw [Real.log_pow x 2]
  have hmul : ((2 : ℕ) : ℝ) * Real.log x * (-(1 / 2 : ℝ)) = -Real.log x := by
    ring
  rw [hmul]
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp [ne_of_gt hx]

private lemma cpow_neg_half_sq_of_pos {x : ℝ} (hx : 0 < x) :
    ((x ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = (x : ℂ)⁻¹ := by
  have h := cpow_neg_half_sq_mul_self_of_pos hx
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hx)] at h ⊢
  exact h

private lemma eulerHalfKernel_pullback_pointwise (k : ℂ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (2 * Real.sin θ * Real.cos θ : ℝ) •
          eulerHalfKernel (k ^ 2) (Real.sin θ ^ 2) =
      2 * (1 - k ^ 2 * ((Real.sin θ : ℂ) ^ 2)) ^ (-(1 / 2 : ℂ)) := by
  have hspos : 0 < Real.sin θ := by
    apply Real.sin_pos_of_mem_Ioo
    constructor
    · exact hθ.1
    · linarith [hθ.2, Real.pi_pos]
  have hcpos : 0 < Real.cos θ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hs' := cpow_neg_half_sq_of_pos hspos
  have hc' := cpow_neg_half_sq_of_pos hcpos
  unfold eulerHalfKernel
  rw [show (1 - ((Real.sin θ ^ 2 : ℝ) : ℂ)) = ((Real.cos θ ^ 2 : ℝ) : ℂ) by
    rw [Complex.ofReal_pow]
    norm_cast
    rw [← Real.sin_sq_add_cos_sq θ]
    ring_nf]
  rw [show (((Real.sin θ ^ 2 : ℝ) : ℂ)) = (Real.sin θ : ℂ) ^ 2 by
    norm_num]
  rw [show ((Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) =
      ((Real.sin θ ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) by
    norm_num]
  rw [hs', hc']
  change ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) *
      ((Real.sin θ : ℂ)⁻¹ * (Real.cos θ : ℂ)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) =
    2 * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))
  rw [show ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) =
      (Real.sin θ : ℂ) * (Real.cos θ : ℂ) * 2 by
    norm_num
    ring_nf]
  rw [show (Real.sin θ : ℂ) * (Real.cos θ : ℂ) * 2 *
      ((Real.sin θ : ℂ)⁻¹ * (Real.cos θ : ℂ)⁻¹ *
        (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) =
    ((Real.sin θ : ℂ) * (Real.sin θ : ℂ)⁻¹) *
      ((Real.cos θ : ℂ) * (Real.cos θ : ℂ)⁻¹) *
      (2 * (1 - k ^ 2 * (Real.sin θ : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))) by
    ring_nf]
  rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hspos)),
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hcpos))]
  ring_nf

/-- The algebraic simplification after the substitution `t = sin² θ`.
This contains the endpoint-null and principal-branch bookkeeping:
`(sin² θ)^(-1/2) (cos² θ)^(-1/2) · 2 sin θ cos θ = 2`
for the interval integral. -/
theorem eulerHalfIntegral_pullback_simplifies_to_ellipticK (k : ℂ) :
    (∫ θ : ℝ in 0..Real.pi / 2,
        (2 * Real.sin θ * Real.cos θ : ℝ) •
          eulerHalfKernel (k ^ 2) (Real.sin θ ^ 2)) =
      2 * ellipticK k := by
  unfold ellipticK
  rw [show 2 * (∫ θ : ℝ in 0..Real.pi / 2,
        (1 - k ^ 2 * ((Real.sin θ : ℂ) ^ 2)) ^ (-(1 / 2 : ℂ))) =
      ∫ θ : ℝ in 0..Real.pi / 2,
        2 * (1 - k ^ 2 * ((Real.sin θ : ℂ) ^ 2)) ^ (-(1 / 2 : ℂ)) by
    exact (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := Real.pi / 2) (r := (2 : ℂ))
      (f := fun θ : ℝ =>
        (1 - k ^ 2 * ((Real.sin θ : ℂ) ^ 2)) ^ (-(1 / 2 : ℂ)))).symm]
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  have hcosCodiscrete : Real.cos ⁻¹' ({0}ᶜ : Set ℝ) ∈ Filter.codiscrete ℝ := by
    apply Real.analyticOnNhd_cos.preimage_zero_mem_codiscrete (x := 0)
    simp
  filter_upwards
      [Filter.self_mem_codiscreteWithin (Ι (0 : ℝ) (Real.pi / 2)),
        Filter.codiscreteWithin.mono
          (by tauto : Ι (0 : ℝ) (Real.pi / 2) ⊆ Set.univ) hcosCodiscrete]
    with θ hθ hcos
  have hθIoc : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
    simpa [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
  have hθlt : θ < Real.pi / 2 := by
    by_contra hnot
    have hge : Real.pi / 2 ≤ θ := le_of_not_gt hnot
    have heq : θ = Real.pi / 2 := le_antisymm hθIoc.2 hge
    have hzero : Real.cos θ = 0 := by
      rw [heq, Real.cos_pi_div_two]
    exact hcos hzero
  exact eulerHalfKernel_pullback_pointwise k ⟨hθIoc.1, hθlt⟩

theorem eulerHalfIntegral_k_sq_eq_two_ellipticK (k : ℂ) :
    eulerHalfIntegral (k ^ 2) = 2 * ellipticK k := by
  rw [eulerHalfIntegral_k_sq_eq_pullback]
  exact eulerHalfIntegral_pullback_simplifies_to_ellipticK k

/-- Jacobi's period-hypergeometric identity:
`₂F₁(1/2,1/2;1;k²) = (2/π) K(k)`. -/
theorem period_hypergeom_half (k : ℂ) (hk : ‖k ^ 2‖ < 1) :
    gauss2F1 (1 / 2) (1 / 2) 1 (k ^ 2) =
      (2 / (Real.pi : ℂ)) * ellipticK k := by
  rw [gauss2F1_half_half_one_eq_eulerHalfIntegral (k ^ 2) hk]
  rw [eulerHalfIntegral_k_sq_eq_two_ellipticK]
  ring_nf

/-- The same identity in period normalization:
`ω₁(k²) = 2 K(k)`. -/
theorem legendrePeriod_eq_two_ellipticK (k : ℂ) (hk : ‖k ^ 2‖ < 1) :
    legendrePeriod (k ^ 2) = 2 * ellipticK k := by
  unfold legendrePeriod
  rw [period_hypergeom_half k hk]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]

theorem legendrePeriod_zero_eq_two_ellipticK_zero :
    legendrePeriod ((0 : ℂ) ^ 2) = 2 * ellipticK 0 := by
  unfold legendrePeriod
  simp [gauss2F1]
  ring_nf

/-- The Legendre lambda value of the discriminant `-163` CM elliptic curve,
using the theta-constant construction already present in the modular layer. -/
noncomputable def cm163LegendreLambda : ℂ :=
  Modular.thetaLambda (Modular.heegnerTau163 : ℂ)

/-- A named placeholder for the Legendre lambda value of the discriminant
`-58` CM point used in Ramanujan's 1914 identity.  The target branch is the
small lambda value already recorded in the modular endpoint file. -/
noncomputable def cm58LegendreLambda : ℂ :=
  Modular.ramanujanLambda58Target

/-- Algebraic conversion from the Legendre lambda `j`-map to the Chudnovsky
hypergeometric argument.  This is the variable identity needed by the true
Schwarz pullback; the missing analytic part is the hypergeometric
transformation/prefactor, not this rational simplification. -/
theorem kleinJFromLambda_argument_eq (lam J : ℂ)
    (hJ : Modular.kleinJFromLambda lam = J)
    (hden : 1 - lam + lam ^ 2 ≠ 0) :
    (1728 : ℂ) / J =
      (27 / 4) * (lam ^ 2 * (1 - lam) ^ 2) / (1 - lam + lam ^ 2) ^ 3 := by
  rw [← hJ]
  unfold Modular.kleinJFromLambda
  field_simp [hden]
  ring

/-- If the Legendre `j`-value is nonzero, then the numerator
`1 - λ + λ²` in the classical `j(λ)` expression is nonzero. -/
theorem kleinJFromLambda_num_ne_zero_of_eq_ne_zero (lam J : ℂ)
    (hJ : Modular.kleinJFromLambda lam = J) (hJ0 : J ≠ 0) :
    1 - lam + lam ^ 2 ≠ 0 := by
  intro hnum
  apply hJ0
  rw [← hJ]
  unfold Modular.kleinJFromLambda
  rw [hnum]
  simp

/-- Nonzero-target version of `kleinJFromLambda_argument_eq`. -/
theorem kleinJFromLambda_argument_eq_of_ne_zero (lam J : ℂ)
    (hJ : Modular.kleinJFromLambda lam = J) (hJ0 : J ≠ 0) :
    (1728 : ℂ) / J =
      (27 / 4) * (lam ^ 2 * (1 - lam) ^ 2) / (1 - lam + lam ^ 2) ^ 3 :=
  kleinJFromLambda_argument_eq lam J hJ
    (kleinJFromLambda_num_ne_zero_of_eq_ne_zero lam J hJ hJ0)

/-- Specialization of the `j`-argument conversion to the degree-58 lambda
target.  The Ramanujan pullback uses the much simpler `λ^2`; this lemma
records that the level-one `j` argument is a different rational expression,
so the two Schwarz routes should not be conflated. -/
theorem ramanujanJ58_argument_from_lambda :
    (1728 : ℂ) / Modular.ramanujanJ58Target =
      (27 / 4) * (cm58LegendreLambda ^ 2 * (1 - cm58LegendreLambda) ^ 2) /
        (1 - cm58LegendreLambda + cm58LegendreLambda ^ 2) ^ 3 := by
  unfold cm58LegendreLambda Modular.ramanujanJ58Target
  exact kleinJFromLambda_argument_eq Modular.ramanujanLambda58Target
    (Modular.kleinJFromLambda Modular.ramanujanLambda58Target) rfl (by
      unfold Modular.ramanujanLambda58Target
      norm_num)

/-- Chudnovsky variable conversion once the modular layer supplies
`j(λ(τ₁₆₃)) = heegnerJ163Target`.  This is the algebraic half of the
level-one Schwarz bridge. -/
theorem chudnovsky_argument_from_lambda_of_kleinJ
    (hJ : Modular.kleinJFromLambda cm163LegendreLambda = Modular.heegnerJ163Target) :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      (27 / 4) * (cm163LegendreLambda ^ 2 * (1 - cm163LegendreLambda) ^ 2) /
        (1 - cm163LegendreLambda + cm163LegendreLambda ^ 2) ^ 3 :=
  kleinJFromLambda_argument_eq_of_ne_zero cm163LegendreLambda
    Modular.heegnerJ163Target hJ (by
      unfold Modular.heegnerJ163Target
      norm_num)

/-- Sanity check for the Ramanujan bridge: the same-argument, no-prefactor
`(1/8,3/8) -> (1/2,1/2)` shape is not an identity of Frobenius germs.
The true Schwarz bridge must expose its algebraic pullback/prefactor data. -/
private lemma ramanujan_same_argument_pullback_formal_coeff_mismatch :
    gauss2F1SeriesPS (1 / 8) (3 / 8) ≠
      gauss2F1SeriesPS (1 / 2) (1 / 2) := by
  intro h
  have h1 := congrArg (fun p : PowerSeries ℂ => PowerSeries.coeff (R := ℂ) 1 p) h
  simp [gauss2F1SeriesPS, gauss2F1Coeff, ordinaryHypergeometricCoefficient] at h1
  norm_num at h1

/-- The algebraic argument identity in Ramanujan's quadratic pullback at the
CM-58 point.  The previous same-argument, no-prefactor hypergeometric equality
was the wrong Schwarz shape: `1 / 99⁴` is the square of the selected Legendre
lambda branch, while the analytic transformation still has to expose its
prefactor data separately. -/
theorem ramanujan_quadratic_period_pullback :
    cm58LegendreLambda ^ 2 = 1 / (99 : ℂ) ^ 4 := by
  unfold cm58LegendreLambda
  exact Modular.ramanujanLambda58Target_sq

theorem ramanujanCM58Argument_eq_cm58LegendreLambda_sq :
    (1 / (99 : ℂ) ^ 4) = cm58LegendreLambda ^ 2 :=
  ramanujan_quadratic_period_pullback.symm

theorem period_hypergeom_half_ramanujan_cm58_pullback :
    gauss2F1 (1 / 2) (1 / 2) 1 (1 / (99 : ℂ)^4) =
      (2 / (Real.pi : ℂ)) * ellipticK cm58LegendreLambda := by
  rw [ramanujanCM58Argument_eq_cm58LegendreLambda_sq]
  exact period_hypergeom_half cm58LegendreLambda (by
    rw [ramanujan_quadratic_period_pullback]
    norm_num [Complex.normSq, Complex.normSq_apply])

theorem legendrePeriod_ramanujan_cm58_pullback :
    legendrePeriod (1 / (99 : ℂ)^4) =
      2 * ellipticK cm58LegendreLambda := by
  rw [ramanujanCM58Argument_eq_cm58LegendreLambda_sq]
  exact legendrePeriod_eq_two_ellipticK cm58LegendreLambda (by
    rw [ramanujan_quadratic_period_pullback]
    norm_num [Complex.normSq, Complex.normSq_apply])

/-- Chudnovsky's algebraic Schwarz argument conversion, with the modular
level-41 endpoint used to supply `j(λ(τ₁₆₃)) = heegnerJ163Target`. -/
theorem chudnovsky_schwarz_period_pullback_of_level41
    (hlevel41 :
      Modular.evalPhi41DiagIsolatedC
          (Modular.kleinJ Modular.heegnerTau163_div41) = 0) :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      (27 / 4) * (cm163LegendreLambda ^ 2 * (1 - cm163LegendreLambda) ^ 2) /
        (1 - cm163LegendreLambda + cm163LegendreLambda ^ 2) ^ 3 := by
  exact chudnovsky_argument_from_lambda_of_kleinJ (by
    unfold cm163LegendreLambda
    exact Modular.kleinJFromLambda_thetaLambda_heegnerTau163_eq_target_of_phi41_diag_div41 hlevel41)

theorem chudnovsky_schwarz_period_pullback_cm163 :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      (27 / 4) * (cm163LegendreLambda ^ 2 * (1 - cm163LegendreLambda) ^ 2) /
        (1 - cm163LegendreLambda + cm163LegendreLambda ^ 2) ^ 3 := by
  exact chudnovsky_schwarz_period_pullback_of_level41 Modular.level41_input_cm163

/-- Chudnovsky's Schwarz argument conversion from the finite level-41
q-expansion certificate.  This is the downstream endpoint of the Euler
product and Sturm-bound infrastructure. -/
theorem chudnovsky_schwarz_period_pullback_of_sturm_certificate
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientCertificate)
    (hvalue :
      Modular.phi41Level41ClearedQExpansion = 0 →
        Modular.evalSparseBivarClearedC Modular.phi41SparseTerms 42 42
          (Modular.E4 Modular.heegnerTau163 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163)
          (Modular.E4 Modular.heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163_div41) = 0) :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      (27 / 4) * (cm163LegendreLambda ^ 2 * (1 - cm163LegendreLambda) ^ 2) /
        (1 - cm163LegendreLambda + cm163LegendreLambda ^ 2) ^ 3 := by
  exact chudnovsky_schwarz_period_pullback_of_level41
    (Modular.level41_input_of_phi41Level41ClearedQExpansion_sturm_certificate
      hsturm hcert hvalue)

theorem chudnovsky_schwarz_period_pullback_of_sturm_range_certificate
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientRangeCertificate)
    (hvalue :
      Modular.phi41Level41ClearedQExpansion = 0 →
        Modular.evalSparseBivarClearedC Modular.phi41SparseTerms 42 42
          (Modular.E4 Modular.heegnerTau163 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163)
          (Modular.E4 Modular.heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163_div41) = 0) :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      (27 / 4) * (cm163LegendreLambda ^ 2 * (1 - cm163LegendreLambda) ^ 2) /
        (1 - cm163LegendreLambda + cm163LegendreLambda ^ 2) ^ 3 := by
  exact chudnovsky_schwarz_period_pullback_of_sturm_certificate hsturm
    (Modular.phi41Level41SturmCoefficientCertificate_of_range hcert) hvalue

theorem chudnovsky_schwarz_period_pullback_of_sturm_eval
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n Modular.phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (Modular.heegnerTau163_div41 : ℂ) ^ n)
        (Modular.evalSparseBivarClearedC Modular.phi41SparseTerms 42 42
          (Modular.E4 Modular.heegnerTau163 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163)
          (Modular.E4 Modular.heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163_div41))) :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      (27 / 4) * (cm163LegendreLambda ^ 2 * (1 - cm163LegendreLambda) ^ 2) /
        (1 - cm163LegendreLambda + cm163LegendreLambda ^ 2) ^ 3 := by
  exact chudnovsky_schwarz_period_pullback_of_level41
    (Modular.level41_input_of_phi41Level41ClearedQExpansion_sturm_eval
      hsturm hcert hseries)

theorem chudnovsky_schwarz_period_pullback_of_sturm_range_eval
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientRangeCertificate)
    (hseries :
      HasSum (fun n : ℕ =>
        PowerSeries.coeff (R := ℂ) n Modular.phi41Level41ClearedQExpansion *
          Function.Periodic.qParam 1 (Modular.heegnerTau163_div41 : ℂ) ^ n)
        (Modular.evalSparseBivarClearedC Modular.phi41SparseTerms 42 42
          (Modular.E4 Modular.heegnerTau163 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163)
          (Modular.E4 Modular.heegnerTau163_div41 ^ 3)
          (ModularForm.discriminant Modular.heegnerTau163_div41))) :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      (27 / 4) * (cm163LegendreLambda ^ 2 * (1 - cm163LegendreLambda) ^ 2) /
        (1 - cm163LegendreLambda + cm163LegendreLambda ^ 2) ^ 3 := by
  exact chudnovsky_schwarz_period_pullback_of_sturm_eval hsturm
    (Modular.phi41Level41SturmCoefficientCertificate_of_range hcert) hseries

theorem chudnovsky_schwarz_period_pullback_of_sturm_sparse_term_eval
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientCertificate)
    (hterms : Modular.phi41Level41SparseTermEvaluationCertificate) :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      (27 / 4) * (cm163LegendreLambda ^ 2 * (1 - cm163LegendreLambda) ^ 2) /
        (1 - cm163LegendreLambda + cm163LegendreLambda ^ 2) ^ 3 := by
  exact chudnovsky_schwarz_period_pullback_of_level41
    (Modular.level41_input_of_phi41Level41ClearedQExpansion_sturm_sparse_term_eval
      hsturm hcert hterms)

theorem chudnovsky_schwarz_period_pullback_of_sturm_range_sparse_term_eval
    (hsturm : Modular.phi41Level41SturmPrinciple)
    (hcert : Modular.phi41Level41SturmCoefficientRangeCertificate)
    (hterms : Modular.phi41Level41SparseTermEvaluationCertificate) :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      (27 / 4) * (cm163LegendreLambda ^ 2 * (1 - cm163LegendreLambda) ^ 2) /
        (1 - cm163LegendreLambda + cm163LegendreLambda ^ 2) ^ 3 := by
  exact chudnovsky_schwarz_period_pullback_of_sturm_sparse_term_eval hsturm
    (Modular.phi41Level41SturmCoefficientCertificate_of_range hcert) hterms

private lemma gamma_pos_real_ne_zero {x : ℝ} (hx : 0 < x) :
    Complex.Gamma (x : ℂ) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have h := congrArg Complex.re hm
  simp at h
  have hmnonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  linarith

private lemma gamma_one_third_ne_zero :
    Complex.Gamma (1 / 3 : ℂ) ≠ 0 := by
  simpa using gamma_pos_real_ne_zero (x := (1 / 3 : ℝ)) (by norm_num)

private lemma gamma_one_fourth_ne_zero :
    Complex.Gamma (1 / 4 : ℂ) ≠ 0 := by
  simpa using gamma_pos_real_ne_zero (x := (1 / 4 : ℝ)) (by norm_num)

private lemma gamma_one_eighth_ne_zero :
    Complex.Gamma (1 / 8 : ℂ) ≠ 0 := by
  simpa using gamma_pos_real_ne_zero (x := (1 / 8 : ℝ)) (by norm_num)

private lemma gamma_three_eighths_ne_zero :
    Complex.Gamma (3 / 8 : ℂ) ≠ 0 := by
  simpa using gamma_pos_real_ne_zero (x := (3 / 8 : ℝ)) (by norm_num)

private lemma gamma_one_twelfth_ne_zero :
    Complex.Gamma (1 / 12 : ℂ) ≠ 0 := by
  simpa using gamma_pos_real_ne_zero (x := (1 / 12 : ℝ)) (by norm_num)

private lemma gamma_five_twelfths_ne_zero :
    Complex.Gamma (5 / 12 : ℂ) ≠ 0 := by
  simpa using gamma_pos_real_ne_zero (x := (5 / 12 : ℝ)) (by norm_num)

/-- Chowla-Selberg input at discriminant `-163`: the corresponding elliptic
period is an algebraic multiple of a Gamma value.  This is stated in the form
needed by the Chudnovsky CM evaluation. -/
theorem chowla_selberg_cm163_period
    (hA : IsAlgebraic ℚ
      (legendrePeriod cm163LegendreLambda * (2 * (Real.pi : ℂ)) /
        Complex.Gamma (1 / 3 : ℂ) ^ 3)) :
    ∃ A : ℂ, IsAlgebraic ℚ A ∧
      legendrePeriod cm163LegendreLambda =
        A * Complex.Gamma (1 / 3 : ℂ) ^ 3 / (2 * (Real.pi : ℂ)) := by
  refine ⟨legendrePeriod cm163LegendreLambda * (2 * (Real.pi : ℂ)) /
      Complex.Gamma (1 / 3 : ℂ) ^ 3, hA, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hgamma3 : Complex.Gamma (1 / 3 : ℂ) ^ 3 ≠ 0 :=
    pow_ne_zero 3 gamma_one_third_ne_zero
  field_simp [hpi, hgamma3, gamma_one_third_ne_zero]
  rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ gamma_one_third_ne_zero, mul_one]

/-! ## CM period inputs and derivative extraction -/

/-- Chowla-Selberg input at discriminant `-58`, in the same normalized form
as the existing `-163` period statement. -/
theorem chowla_selberg_cm58_period
    (hA : IsAlgebraic ℚ
      (legendrePeriod cm58LegendreLambda * (2 * (Real.pi : ℂ)) /
        (Complex.Gamma (1 / 4 : ℂ) * Complex.Gamma (1 / 8 : ℂ)))) :
    ∃ A : ℂ, IsAlgebraic ℚ A ∧
      legendrePeriod cm58LegendreLambda =
        A * Complex.Gamma (1 / 4 : ℂ) * Complex.Gamma (1 / 8 : ℂ) /
          (2 * (Real.pi : ℂ)) := by
  refine ⟨legendrePeriod cm58LegendreLambda * (2 * (Real.pi : ℂ)) /
      (Complex.Gamma (1 / 4 : ℂ) * Complex.Gamma (1 / 8 : ℂ)), hA, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hgamma :
      Complex.Gamma (1 / 4 : ℂ) * Complex.Gamma (1 / 8 : ℂ) ≠ 0 :=
    mul_ne_zero gamma_one_fourth_ne_zero gamma_one_eighth_ne_zero
  field_simp [hpi, hgamma, gamma_one_fourth_ne_zero, gamma_one_eighth_ne_zero]
  rw [div_eq_mul_inv]
  rw [show legendrePeriod cm58LegendreLambda *
        Complex.Gamma (1 / 4 : ℂ) * Complex.Gamma (1 / 8 : ℂ) =
        legendrePeriod cm58LegendreLambda *
          (Complex.Gamma (1 / 4 : ℂ) * Complex.Gamma (1 / 8 : ℂ)) by
      ring]
  rw [mul_assoc, mul_inv_cancel₀ hgamma, mul_one]

/-! ### Clausen square chain rule -/

/-- Chain rule for the Clausen square at parameters satisfying
`a + b + 1/2 = 1`.  This is the purely formal derivative step used by the
Ramanujan and Chudnovsky extraction layers. -/
theorem deriv_clausenGaussSq_eq_two_mul_gauss2F1
    (a b z : ℂ) (hab : a + b + 1 / 2 = 1)
    (hf : HasDerivAt (gauss2F1 a b 1) (deriv (gauss2F1 a b 1) z) z) :
    deriv (clausenGaussSq a b) z =
      2 * gauss2F1 a b 1 z * deriv (gauss2F1 a b 1) z := by
  have hsq : HasDerivAt (fun w => gauss2F1 a b 1 w ^ 2)
      (2 * gauss2F1 a b 1 z * deriv (gauss2F1 a b 1) z) z := by
    simpa [pow_one, mul_assoc] using hf.pow 2
  have hfun : clausenGaussSq a b = fun w => gauss2F1 a b 1 w ^ 2 := by
    funext w
    unfold clausenGaussSq clausenGauss gauss2F1
    rw [hab]
  rw [hfun]
  exact hsq.deriv

theorem deriv_clausenGaussSq_ramanujan_cm58 :
    deriv (clausenGaussSq (1 / 8) (3 / 8)) (1 / (99 : ℂ)^4) =
      2 * gauss2F1 (1 / 8) (3 / 8) 1 (1 / (99 : ℂ)^4) *
        deriv (gauss2F1 (1 / 8) (3 / 8) 1) (1 / (99 : ℂ)^4) := by
  have hf : HasDerivAt (gauss2F1 (1 / 8) (3 / 8) 1)
      (deriv (gauss2F1 (1 / 8) (3 / 8) 1) (1 / (99 : ℂ)^4))
      (1 / (99 : ℂ)^4) := by
    have hd :=
      clausenGauss_ramanujan_differentiableAt_of_norm_lt_one (1 / (99 : ℂ)^4)
        (by norm_num [Complex.normSq, Complex.normSq_apply])
    unfold clausenGauss at hd
    rw [show (1 / 8 : ℂ) + 3 / 8 + 1 / 2 = 1 by norm_num] at hd
    simpa [gauss2F1] using hd.hasDerivAt
  exact deriv_clausenGaussSq_eq_two_mul_gauss2F1 (1 / 8) (3 / 8)
    (1 / (99 : ℂ)^4) (by norm_num) hf

theorem deriv_clausenGaussSq_chudnovsky_cm163 :
    deriv (clausenGaussSq (1 / 12) (5 / 12))
        ((1728 : ℂ) / Modular.heegnerJ163Target) =
      2 * gauss2F1 (1 / 12) (5 / 12) 1
          ((1728 : ℂ) / Modular.heegnerJ163Target) *
        deriv (gauss2F1 (1 / 12) (5 / 12) 1)
          ((1728 : ℂ) / Modular.heegnerJ163Target) := by
  have hf : HasDerivAt (gauss2F1 (1 / 12) (5 / 12) 1)
      (deriv (gauss2F1 (1 / 12) (5 / 12) 1)
        ((1728 : ℂ) / Modular.heegnerJ163Target))
      ((1728 : ℂ) / Modular.heegnerJ163Target) := by
    have hd :=
      clausenGauss_chudnovsky_differentiableAt_of_norm_lt_one
        ((1728 : ℂ) / Modular.heegnerJ163Target)
        (by norm_num [Modular.heegnerJ163Target, Complex.normSq, Complex.normSq_apply])
    unfold clausenGauss at hd
    rw [show (1 / 12 : ℂ) + 5 / 12 + 1 / 2 = 1 by norm_num] at hd
    simpa [gauss2F1] using hd.hasDerivAt
  exact deriv_clausenGaussSq_eq_two_mul_gauss2F1 (1 / 12) (5 / 12)
    ((1728 : ℂ) / Modular.heegnerJ163Target) (by norm_num) hf

/-! ### Post-chain-rule CM normalizations -/

/-- The exact Ramanujan CM58 linear combination after Clausen reduction. -/
noncomputable def ramanujanCM58DerivativeCombination : ℂ :=
  1103 * clausenGaussSq (1 / 8) (3 / 8) (1 / (99 : ℂ)^4) +
    26390 * (1 / (99 : ℂ)^4) *
      deriv (clausenGaussSq (1 / 8) (3 / 8)) (1 / (99 : ℂ)^4)

/-- The same Ramanujan CM58 combination after the formal Clausen-square
chain rule has been applied. -/
noncomputable def ramanujanCM58GaussDerivativeCombination : ℂ :=
  1103 * gauss2F1 (1 / 8) (3 / 8) 1 (1 / (99 : ℂ)^4) ^ 2 +
    26390 * (1 / (99 : ℂ)^4) *
      (2 * gauss2F1 (1 / 8) (3 / 8) 1 (1 / (99 : ℂ)^4) *
        deriv (gauss2F1 (1 / 8) (3 / 8) 1) (1 / (99 : ℂ)^4))

theorem ramanujanCM58Argument_ne_zero :
    (1 / (99 : ℂ)^4) ≠ 0 := by
  norm_num

theorem ramanujanCM58Argument_ne_one :
    (1 / (99 : ℂ)^4) ≠ 1 := by
  norm_num

theorem ramanujanCM58Argument_norm_lt_one :
    ‖(1 / (99 : ℂ)^4)‖ < 1 := by
  norm_num [Complex.normSq, Complex.normSq_apply]

theorem ramanujanCM58Argument_frobenius_branch :
    Complex.I * (1 / (99 : ℂ)^4) ∈ Complex.slitPlane := by
  norm_num [Complex.mem_slitPlane_iff]

theorem hypergeom_wronskian_ramanujan_cm58 :
    gauss2F1 (1 / 8) (3 / 8) 1 (1 / (99 : ℂ)^4) *
        deriv (gauss2F1SecondSolution (1 / 8) (3 / 8)) (1 / (99 : ℂ)^4) -
      deriv (gauss2F1 (1 / 8) (3 / 8) 1) (1 / (99 : ℂ)^4) *
        gauss2F1SecondSolution (1 / 8) (3 / 8) (1 / (99 : ℂ)^4) =
        Complex.Gamma (1 / 8) * Complex.Gamma (3 / 8) /
          (2 * (Real.pi : ℂ) * Complex.I * (1 / (99 : ℂ)^4) *
            (1 - (1 / (99 : ℂ)^4)) ^ ((1 / 8 : ℂ) + (3 / 8 : ℂ))) := by
  exact hypergeom_wronskian (1 / 8) (3 / 8) (1 / (99 : ℂ)^4)
    ramanujanCM58Argument_ne_zero
    ramanujanCM58Argument_ne_one
    ramanujanCM58Argument_frobenius_branch
    ramanujanCM58Argument_norm_lt_one
    gamma_one_eighth_ne_zero
    gamma_three_eighths_ne_zero

/-- The exact Chudnovsky CM163 linear combination after Clausen reduction. -/
noncomputable def chudnovskyCM163DerivativeCombination : ℂ :=
  13591409 *
      clausenGaussSq (1 / 12) (5 / 12) ((1728 : ℂ) / Modular.heegnerJ163Target) +
    545140134 * ((1728 : ℂ) / Modular.heegnerJ163Target) *
      deriv (clausenGaussSq (1 / 12) (5 / 12))
        ((1728 : ℂ) / Modular.heegnerJ163Target)

/-- The same Chudnovsky CM163 combination after the formal Clausen-square
chain rule has been applied. -/
noncomputable def chudnovskyCM163GaussDerivativeCombination : ℂ :=
  13591409 *
      gauss2F1 (1 / 12) (5 / 12) 1 ((1728 : ℂ) / Modular.heegnerJ163Target) ^ 2 +
    545140134 * ((1728 : ℂ) / Modular.heegnerJ163Target) *
      (2 * gauss2F1 (1 / 12) (5 / 12) 1
          ((1728 : ℂ) / Modular.heegnerJ163Target) *
        deriv (gauss2F1 (1 / 12) (5 / 12) 1)
          ((1728 : ℂ) / Modular.heegnerJ163Target))

/-- Chudnovsky's classical hypergeometric argument written directly from
`j(τ₁₆₃) = -640320³`. -/
noncomputable def chudnovskyCM163ClassicalArgument : ℂ :=
  -1728 / (640320 : ℂ)^3

theorem chudnovskyCM163Argument_eq_classical :
    (1728 : ℂ) / Modular.heegnerJ163Target =
      chudnovskyCM163ClassicalArgument := by
  unfold chudnovskyCM163ClassicalArgument
  exact Modular.chudnovsky_argument_from_j_target

theorem chudnovskyCM163Argument_ne_zero :
    ((1728 : ℂ) / Modular.heegnerJ163Target) ≠ 0 := by
  norm_num [Modular.heegnerJ163Target]

theorem chudnovskyCM163Argument_ne_one :
    ((1728 : ℂ) / Modular.heegnerJ163Target) ≠ 1 := by
  norm_num [Modular.heegnerJ163Target]

theorem chudnovskyCM163Argument_norm_lt_one :
    ‖((1728 : ℂ) / Modular.heegnerJ163Target)‖ < 1 := by
  norm_num [Modular.heegnerJ163Target, Complex.normSq, Complex.normSq_apply]

theorem chudnovskyCM163Argument_frobenius_branch :
    Complex.I * ((1728 : ℂ) / Modular.heegnerJ163Target) ∈ Complex.slitPlane := by
  norm_num [Modular.heegnerJ163Target, Complex.mem_slitPlane_iff]

theorem hypergeom_wronskian_chudnovsky_cm163 :
    gauss2F1 (1 / 12) (5 / 12) 1 ((1728 : ℂ) / Modular.heegnerJ163Target) *
        deriv (gauss2F1SecondSolution (1 / 12) (5 / 12))
          ((1728 : ℂ) / Modular.heegnerJ163Target) -
      deriv (gauss2F1 (1 / 12) (5 / 12) 1)
          ((1728 : ℂ) / Modular.heegnerJ163Target) *
        gauss2F1SecondSolution (1 / 12) (5 / 12)
          ((1728 : ℂ) / Modular.heegnerJ163Target) =
        Complex.Gamma (1 / 12) * Complex.Gamma (5 / 12) /
          (2 * (Real.pi : ℂ) * Complex.I *
            ((1728 : ℂ) / Modular.heegnerJ163Target) *
            (1 - ((1728 : ℂ) / Modular.heegnerJ163Target)) ^
              ((1 / 12 : ℂ) + (5 / 12 : ℂ))) := by
  exact hypergeom_wronskian (1 / 12) (5 / 12)
    ((1728 : ℂ) / Modular.heegnerJ163Target)
    chudnovskyCM163Argument_ne_zero
    chudnovskyCM163Argument_ne_one
    chudnovskyCM163Argument_frobenius_branch
    chudnovskyCM163Argument_norm_lt_one
    gamma_one_twelfth_ne_zero
    gamma_five_twelfths_ne_zero

/-- The Chudnovsky Gauss-derivative combination at the direct classical
argument `-1728 / 640320³`. -/
noncomputable def chudnovskyCM163GaussDerivativeCombinationClassical : ℂ :=
  13591409 *
      gauss2F1 (1 / 12) (5 / 12) 1 chudnovskyCM163ClassicalArgument ^ 2 +
    545140134 * chudnovskyCM163ClassicalArgument *
      (2 * gauss2F1 (1 / 12) (5 / 12) 1 chudnovskyCM163ClassicalArgument *
        deriv (gauss2F1 (1 / 12) (5 / 12) 1) chudnovskyCM163ClassicalArgument)

theorem ramanujanCM58DerivativeCombination_eq_gauss :
    ramanujanCM58DerivativeCombination =
      ramanujanCM58GaussDerivativeCombination := by
  unfold ramanujanCM58DerivativeCombination ramanujanCM58GaussDerivativeCombination
  rw [deriv_clausenGaussSq_ramanujan_cm58]
  congr 1
  unfold clausenGaussSq clausenGauss gauss2F1
  norm_num

theorem chudnovskyCM163DerivativeCombination_eq_gauss :
    chudnovskyCM163DerivativeCombination =
      chudnovskyCM163GaussDerivativeCombination := by
  unfold chudnovskyCM163DerivativeCombination chudnovskyCM163GaussDerivativeCombination
  rw [deriv_clausenGaussSq_chudnovsky_cm163]
  congr 1
  congr 1
  unfold clausenGaussSq clausenGauss gauss2F1
  norm_num

theorem chudnovskyCM163GaussDerivativeCombination_eq_classical :
    chudnovskyCM163GaussDerivativeCombination =
      chudnovskyCM163GaussDerivativeCombinationClassical := by
  unfold chudnovskyCM163GaussDerivativeCombination
    chudnovskyCM163GaussDerivativeCombinationClassical chudnovskyCM163ClassicalArgument
  rw [Modular.chudnovsky_argument_from_j_target]

theorem ramanujanCM58_after_chain_rule_target_iff :
    ramanujanCM58DerivativeCombination =
        ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) ↔
      ramanujanCM58GaussDerivativeCombination =
        ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) := by
  rw [ramanujanCM58DerivativeCombination_eq_gauss]

theorem chudnovskyCM163_after_chain_rule_target_iff :
    chudnovskyCM163DerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) ↔
      chudnovskyCM163GaussDerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) := by
  rw [chudnovskyCM163DerivativeCombination_eq_gauss]

theorem chudnovsky_prefactor_rpow_three_halves :
    Real.rpow (640320 : ℝ) (3 / 2 : ℝ) =
      (640320 : ℝ) * Real.sqrt (640320 : ℝ) := by
  change (640320 : ℝ) ^ (3 / 2 : ℝ) =
    (640320 : ℝ) * Real.sqrt (640320 : ℝ)
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 640320)]
  rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem chudnovsky_prefactor_complex_eq_sqrt_form :
    (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
        ((12 * Real.pi : ℝ) : ℂ) =
      ((53360 * Real.sqrt (640320 : ℝ) / Real.pi : ℝ) : ℂ) := by
  rw [chudnovsky_prefactor_rpow_three_halves]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, hpi]
  field_simp [hpi]
  ring

theorem chudnovskyCM163_after_chain_rule_classical_target_iff :
    chudnovskyCM163DerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) ↔
      chudnovskyCM163GaussDerivativeCombinationClassical =
        ((53360 * Real.sqrt (640320 : ℝ) / Real.pi : ℝ) : ℂ) := by
  rw [chudnovskyCM163DerivativeCombination_eq_gauss]
  rw [chudnovskyCM163GaussDerivativeCombination_eq_classical]
  rw [chudnovsky_prefactor_complex_eq_sqrt_form]

theorem ramanujan_cm58_periodDerivative_after_chain_rule :
    ramanujanCM58GaussDerivativeCombination =
        ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) →
    1103 * clausenGaussSq (1 / 8) (3 / 8) (1 / (99 : ℂ)^4) +
        26390 * (1 / (99 : ℂ)^4) *
          deriv (clausenGaussSq (1 / 8) (3 / 8)) (1 / (99 : ℂ)^4) =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) := by
  intro hnormalization
  exact ramanujanCM58_after_chain_rule_target_iff.mpr hnormalization

theorem chudnovsky_cm163_periodDerivative_after_chain_rule :
    chudnovskyCM163GaussDerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) →
    13591409 *
        clausenGaussSq (1 / 12) (5 / 12) ((1728 : ℂ) / Modular.heegnerJ163Target) +
      545140134 * ((1728 : ℂ) / Modular.heegnerJ163Target) *
        deriv (clausenGaussSq (1 / 12) (5 / 12))
          ((1728 : ℂ) / Modular.heegnerJ163Target) =
      (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
        ((12 * Real.pi : ℝ) : ℂ) := by
  intro hnormalization
  exact chudnovskyCM163_after_chain_rule_target_iff.mpr hnormalization

/-!
The next two lemmas are the intended extraction layer from the five analytic
bridges above to the exact coefficient-normalized derivative combinations
used by Ramanujan and Chudnovsky.  Their proofs should become pure
composition/chain-rule/algebra once the Schwarz pullback statements expose
the concrete pullback maps and prefactors.
-/

theorem ramanujan_cm58_periodDerivative_evaluation :
    ramanujanCM58GaussDerivativeCombination =
        ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) →
    1103 * clausenGaussSq (1 / 8) (3 / 8) (1 / (99 : ℂ)^4) +
        26390 * (1 / (99 : ℂ)^4) *
          deriv (clausenGaussSq (1 / 8) (3 / 8)) (1 / (99 : ℂ)^4) =
      ((9801 / (2 * Real.sqrt 2 * Real.pi) : ℝ) : ℂ) := by
  intro hnormalization
  have hpull := ramanujan_quadratic_period_pullback
  have hperiod := period_hypergeom_half cm58LegendreLambda (by
    rw [cm58LegendreLambda, Modular.ramanujanLambda58Target_sq]
    norm_num [Complex.normSq, Complex.normSq_apply])
  have hwr :
      gauss2F1 (1 / 8) (3 / 8) 1 (1 / (99 : ℂ)^4) *
          deriv (gauss2F1SecondSolution (1 / 8) (3 / 8)) (1 / (99 : ℂ)^4) -
        deriv (gauss2F1 (1 / 8) (3 / 8) 1) (1 / (99 : ℂ)^4) *
          gauss2F1SecondSolution (1 / 8) (3 / 8) (1 / (99 : ℂ)^4) =
          Complex.Gamma (1 / 8) * Complex.Gamma (3 / 8) /
            (2 * (Real.pi : ℂ) * Complex.I * (1 / (99 : ℂ)^4) *
              (1 - (1 / (99 : ℂ)^4)) ^ ((1 / 8 : ℂ) + (3 / 8 : ℂ))) := by
    exact hypergeom_wronskian_ramanujan_cm58
  have hcm := chowla_selberg_cm58_period
  have hclausen := deriv_clausenGaussSq_ramanujan_cm58
  exact ramanujan_cm58_periodDerivative_after_chain_rule hnormalization

theorem chudnovsky_cm163_periodDerivative_evaluation :
    chudnovskyCM163GaussDerivativeCombination =
        (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
          ((12 * Real.pi : ℝ) : ℂ) →
    13591409 *
        clausenGaussSq (1 / 12) (5 / 12) ((1728 : ℂ) / Modular.heegnerJ163Target) +
      545140134 * ((1728 : ℂ) / Modular.heegnerJ163Target) *
        deriv (clausenGaussSq (1 / 12) (5 / 12))
          ((1728 : ℂ) / Modular.heegnerJ163Target) =
      (Real.rpow (640320 : ℝ) (3 / 2 : ℝ) : ℂ) /
        ((12 * Real.pi : ℝ) : ℂ) := by
  intro hnormalization
  have hpull := chudnovsky_argument_from_lambda_of_kleinJ
  have hperiod := legendrePeriod_eq_two_ellipticK 0
      (by simp [norm_zero])
  have hwr :
      gauss2F1 (1 / 12) (5 / 12) 1 ((1728 : ℂ) / Modular.heegnerJ163Target) *
          deriv (gauss2F1SecondSolution (1 / 12) (5 / 12))
            ((1728 : ℂ) / Modular.heegnerJ163Target) -
        deriv (gauss2F1 (1 / 12) (5 / 12) 1)
            ((1728 : ℂ) / Modular.heegnerJ163Target) *
          gauss2F1SecondSolution (1 / 12) (5 / 12)
            ((1728 : ℂ) / Modular.heegnerJ163Target) =
          Complex.Gamma (1 / 12) * Complex.Gamma (5 / 12) /
            (2 * (Real.pi : ℂ) * Complex.I *
              ((1728 : ℂ) / Modular.heegnerJ163Target) *
              (1 - ((1728 : ℂ) / Modular.heegnerJ163Target)) ^
                ((1 / 12 : ℂ) + (5 / 12 : ℂ))) := by
    exact hypergeom_wronskian_chudnovsky_cm163
  have hcm := chowla_selberg_cm163_period
  have hclausen := deriv_clausenGaussSq_chudnovsky_cm163
  exact chudnovsky_cm163_periodDerivative_after_chain_rule hnormalization

end Hypergeometric
end Number
end Ripple
