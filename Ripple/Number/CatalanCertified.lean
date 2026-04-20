/-
  Ripple.Number.CatalanCertified — Catalan's constant G is LPP-computable

  Builds a `CertifiedBoundedTimeComputable` witness for Catalan's constant
  G = ∫₀^∞ s·exp(-s)/(1 + exp(-2s)) ds ≈ 0.9159
  and pairs it with a `PolyCRNDecomposition` to conclude
  `IsLPPComputable catalanConstant`.

  Derivation (Huang–Huls LPP paper Cor. 19, via the substitution W := 1 − V):
    X₀ = E,  E' = −E,          E(0) = 1       (E(t) = exp(−t))
    X₁ = R,  R' = E − R,       R(0) = 0       (R(t) = t·exp(−t))
    X₂ = W,  W' = 2·E²·W²,     W(0) = 1/2     (W(t) = 1/(1 + exp(−2t)))
    X₃ = G,  G' = R·W,         G(0) = 0

  The output G(t) = ∫₀ᵗ s·exp(−s)/(1 + exp(−2s)) ds converges to
  Catalan's constant exponentially fast: |G(t) − G| ≤ (t+1)·exp(−t).

  Production/degradation split:
    prod₀ := 0;                 degr₀ := C 1                     (E' = 0 − 1·E)
    prod₁ := X 0;               degr₁ := C 1                     (R' = X₀ − 1·R)
    prod₂ := C 2 · X 0^2 · X 2^2;  degr₂ := 0                   (W' = 2·X₀²·X₂² − 0·W)
    prod₃ := X 1 · X 2;         degr₃ := 0                       (G' = X₁·X₂ − 0·G)

  All monomial coefficients lie in {0, 1, 2} ⊂ ℚ≥0; initial concentrations
  lie in {0, 1/2, 1}.
-/

import Ripple.Core.BoundedTime
import Ripple.LPP.BoundedLPP
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Ripple.Number

open Ripple
open MvPolynomial
open Real
open MeasureTheory
open scoped Topology

/-! ## The Catalan integrand and its basic properties -/

/-- The integrand whose improper integral on `(0, ∞)` is Catalan's constant. -/
noncomputable def catalanIntegrand (s : ℝ) : ℝ :=
  s * exp (-s) / (1 + exp (-2 * s))

/-- Denominator is strictly positive. -/
private lemma one_add_exp_neg_two_pos (s : ℝ) : 0 < 1 + exp (-2 * s) := by
  have := exp_pos (-2 * s); linarith

/-- Denominator is ≥ 1. -/
private lemma one_add_exp_neg_two_ge_one (s : ℝ) : 1 ≤ 1 + exp (-2 * s) := by
  have := (exp_pos (-2 * s)).le; linarith

/-- The integrand is continuous on ℝ. -/
private lemma catalanIntegrand_continuous : Continuous catalanIntegrand := by
  unfold catalanIntegrand
  have h_num : Continuous (fun s : ℝ => s * exp (-s)) :=
    continuous_id.mul (Real.continuous_exp.comp continuous_neg)
  have h_den : Continuous (fun s : ℝ => 1 + exp (-2 * s)) :=
    continuous_const.add
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  exact h_num.div h_den (fun s => ne_of_gt (one_add_exp_neg_two_pos s))

/-- On `[0, ∞)`, the integrand is non-negative. -/
private lemma catalanIntegrand_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ catalanIntegrand s := by
  unfold catalanIntegrand
  exact div_nonneg (mul_nonneg hs (exp_pos _).le) (one_add_exp_neg_two_pos s).le

/-- On `[0, ∞)`, the integrand is bounded by `s · exp(-s)`. -/
private lemma catalanIntegrand_le {s : ℝ} (hs : 0 ≤ s) :
    catalanIntegrand s ≤ s * exp (-s) := by
  unfold catalanIntegrand
  have hpos : 0 < 1 + exp (-2 * s) := one_add_exp_neg_two_pos s
  have hge : 1 ≤ 1 + exp (-2 * s) := one_add_exp_neg_two_ge_one s
  rw [div_le_iff₀ hpos]
  have hnum_nn : 0 ≤ s * exp (-s) := mul_nonneg hs (exp_pos _).le
  calc s * exp (-s)
      = s * exp (-s) * 1 := by ring
    _ ≤ s * exp (-s) * (1 + exp (-2 * s)) :=
        mul_le_mul_of_nonneg_left hge hnum_nn

/-! ## Antiderivative of `s · exp(-s)` is `F(s) = -(s+1)·exp(-s)` -/

private lemma hasDerivAt_neg_sPlus1_exp_neg (s : ℝ) :
    HasDerivAt (fun u => -(u + 1) * exp (-u)) (s * exp (-s)) s := by
  have h_inner : HasDerivAt (fun u : ℝ => -(u + 1)) (-1) s := by
    have h1 : HasDerivAt (fun u : ℝ => u + 1) (1 : ℝ) s :=
      (hasDerivAt_id s).add_const 1
    have h2 := h1.neg
    convert h2 using 1
  have h_neg : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) s := by
    simpa [id] using (hasDerivAt_id s).neg
  have h_exp : HasDerivAt (fun u : ℝ => exp (-u)) (-exp (-s)) s := by
    convert h_neg.exp using 1; ring
  have := h_inner.mul h_exp
  convert this using 1
  ring

/-- `(s+1) · exp(-s) → 0` as `s → ∞`. -/
private lemma tendsto_sPlus1_exp_neg_atTop :
    Filter.Tendsto (fun s : ℝ => (s + 1) * exp (-s)) Filter.atTop (𝓝 0) := by
  have h1 : Filter.Tendsto (fun s : ℝ => s ^ 1 * exp (-s)) Filter.atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 : Filter.Tendsto (fun s : ℝ => exp (-s)) Filter.atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero
  have hsum : Filter.Tendsto (fun s : ℝ => s ^ 1 * exp (-s) + exp (-s))
      Filter.atTop (𝓝 (0 + 0)) := h1.add h2
  have hrw : (fun s : ℝ => (s + 1) * exp (-s)) =
      fun s : ℝ => s ^ 1 * exp (-s) + exp (-s) := by
    funext s; ring
  rw [hrw]; simpa using hsum

/-- `-(s+1) · exp(-s) → 0` as `s → ∞`. -/
private lemma tendsto_neg_sPlus1_exp_neg_atTop :
    Filter.Tendsto (fun s : ℝ => -(s + 1) * exp (-s)) Filter.atTop (𝓝 0) := by
  have h := tendsto_sPlus1_exp_neg_atTop.neg
  have hrw : (fun s : ℝ => -((s + 1) * exp (-s))) =
      fun s : ℝ => -(s + 1) * exp (-s) := by funext s; ring
  rw [hrw] at h; simpa using h

/-- Improper integral formula: `∫ s in Ioi a, s·exp(-s) = (a+1)·exp(-a)` for `a ≥ 0`.

Uses FTC on `(a, ∞)` with antiderivative `F(s) = -(s+1)·exp(-s)`, which
has `F'(s) = s·exp(-s) ≥ 0` on `(a, ∞)` (for `a ≥ 0`) and tends to `0` at infinity. -/
private lemma integral_Ioi_s_exp_neg {a : ℝ} (ha : 0 ≤ a) :
    ∫ s in Set.Ioi a, s * exp (-s) = (a + 1) * exp (-a) := by
  have hderiv : ∀ x ∈ Set.Ici a,
      HasDerivAt (fun u => -(u + 1) * exp (-u)) (x * exp (-x)) x :=
    fun x _ => hasDerivAt_neg_sPlus1_exp_neg x
  have hpos : ∀ x ∈ Set.Ioi a, 0 ≤ x * exp (-x) := fun x hx =>
    mul_nonneg (le_of_lt (lt_of_le_of_lt ha hx)) (exp_pos _).le
  have htend := tendsto_neg_sPlus1_exp_neg_atTop
  have hFTC := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend
  -- hFTC : ∫ x in Ioi a, x * exp (-x) = 0 - -(a + 1) * exp (-a)
  rw [hFTC]; ring

/-- `s · exp(-s)` is integrable on `Ioi a` for any `a ≥ 0`. -/
private lemma integrable_s_exp_neg_Ioi {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun s : ℝ => s * exp (-s)) (Set.Ioi a) := by
  have hderiv : ∀ x ∈ Set.Ici a,
      HasDerivAt (fun u => -(u + 1) * exp (-u)) (x * exp (-x)) x :=
    fun x _ => hasDerivAt_neg_sPlus1_exp_neg x
  have hpos : ∀ x ∈ Set.Ioi a, 0 ≤ x * exp (-x) := fun x hx =>
    mul_nonneg (le_of_lt (lt_of_le_of_lt ha hx)) (exp_pos _).le
  have htend := tendsto_neg_sPlus1_exp_neg_atTop
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend

/-- Integrand is integrable on `Ioi a` for `a ≥ 0`. -/
private lemma integrable_catalanIntegrand_Ioi' {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn catalanIntegrand (Set.Ioi a) := by
  have hcomp := integrable_s_exp_neg_Ioi ha
  have hcont : Continuous catalanIntegrand := catalanIntegrand_continuous
  refine Integrable.mono hcomp hcont.aestronglyMeasurable.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall (fun s hs => ?_)
  have hs_nn : 0 ≤ s := le_of_lt (lt_of_le_of_lt ha hs)
  rw [Real.norm_eq_abs, abs_of_nonneg (catalanIntegrand_nonneg hs_nn),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs_nn (exp_pos _).le)]
  exact catalanIntegrand_le hs_nn

/-! ## Catalan's constant as an improper integral -/

/-- Catalan's constant `G`, defined as the improper integral on `(0, ∞)`
of `s · exp(-s) / (1 + exp(-2s))`. -/
noncomputable def catalanConstant : ℝ :=
  ∫ s in Set.Ioi (0:ℝ), catalanIntegrand s

/-- Tail bound: for `t ≥ 0`, the tail integral from `t` to `∞` is bounded by
`(t+1) · exp(-t)`. -/
private lemma tail_le {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Set.Ioi t, catalanIntegrand s ≤ (t + 1) * exp (-t) := by
  have hint_cat : IntegrableOn catalanIntegrand (Set.Ioi t) :=
    integrable_catalanIntegrand_Ioi' ht
  have hint_exp : IntegrableOn (fun s : ℝ => s * exp (-s)) (Set.Ioi t) :=
    integrable_s_exp_neg_Ioi ht
  have hmono : ∫ s in Set.Ioi t, catalanIntegrand s ≤
      ∫ s in Set.Ioi t, s * exp (-s) := by
    refine setIntegral_mono_on hint_cat hint_exp measurableSet_Ioi ?_
    intro s hs
    have hs_nn : 0 ≤ s := le_of_lt (lt_of_le_of_lt ht hs)
    exact catalanIntegrand_le hs_nn
  rw [integral_Ioi_s_exp_neg ht] at hmono
  exact hmono

/-- The tail integral from `t` to `∞` is non-negative. -/
private lemma tail_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∫ s in Set.Ioi t, catalanIntegrand s := by
  refine setIntegral_nonneg measurableSet_Ioi ?_
  intro s hs
  exact catalanIntegrand_nonneg (le_of_lt (lt_of_le_of_lt ht hs))

/-- Additivity: `∫ in Ioi 0 = ∫ in Ioc 0 t + ∫ in Ioi t` for `t ≥ 0`. -/
private lemma integral_Ioi_split {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Set.Ioi (0:ℝ), catalanIntegrand s) =
    (∫ s in Set.Ioc (0:ℝ) t, catalanIntegrand s) +
    (∫ s in Set.Ioi t, catalanIntegrand s) := by
  have hunion : Set.Ioc (0:ℝ) t ∪ Set.Ioi t = Set.Ioi (0:ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi ht
  have hdisj : Disjoint (Set.Ioc (0:ℝ) t) (Set.Ioi t) := Set.Ioc_disjoint_Ioi_same
  have hint_Ioc : IntegrableOn catalanIntegrand (Set.Ioc (0:ℝ) t) := by
    refine (integrable_catalanIntegrand_Ioi' (le_refl 0)).mono_set ?_
    exact Set.Ioc_subset_Ioi_self
  have hint_Ioi : IntegrableOn catalanIntegrand (Set.Ioi t) :=
    integrable_catalanIntegrand_Ioi' ht
  rw [← hunion]
  rw [setIntegral_union hdisj measurableSet_Ioi hint_Ioc hint_Ioi]

/-! ## The closed-form solution `catalanSolution` -/

/-- Closed-form solution of the 4-variable PIVP:
   E(t) = exp(-t), R(t) = t·exp(-t), W(t) = 1/(1 + exp(-2t)),
   G(t) = ∫₀ᵗ s·exp(-s)/(1 + exp(-2s)) ds. -/
noncomputable def catalanSolution (t : ℝ) : Fin 4 → ℝ :=
  ![exp (-t), t * exp (-t), 1 / (1 + exp (-2 * t)),
    ∫ s in (0:ℝ)..t, catalanIntegrand s]

theorem catalan_sol_E (t : ℝ) : catalanSolution t 0 = exp (-t) := by
  simp [catalanSolution]

theorem catalan_sol_R (t : ℝ) : catalanSolution t 1 = t * exp (-t) := by
  simp [catalanSolution]

theorem catalan_sol_W (t : ℝ) : catalanSolution t 2 = 1 / (1 + exp (-2 * t)) := by
  simp [catalanSolution]

theorem catalan_sol_G (t : ℝ) :
    catalanSolution t 3 = ∫ s in (0:ℝ)..t, catalanIntegrand s := by
  simp [catalanSolution]

/-! ## The syntactic PolyPIVP for Catalan -/

/-- The syntactic `PolyPIVP 4`. -/
noncomputable def catalanPolyPIVP : PolyPIVP 4 where
  field := fun i =>
    match i with
    | 0 => - X 0
    | 1 => X 0 - X 1
    | 2 => C 2 * X 0 ^ 2 * X 2 ^ 2
    | 3 => X 1 * X 2
  init := fun i =>
    match i with
    | 0 => 1
    | 1 => 0
    | 2 => 1 / 2
    | 3 => 0
  output := 3

/-! ## Evaluate syntactic field on reals -/

/-- Direct evaluation of the syntactic field at a real state. -/
theorem catalanPolyPIVP_evalField_eq (x : Fin 4 → ℝ) (i : Fin 4) :
    catalanPolyPIVP.toPIVP.field x i =
      (match i with
        | (0 : Fin 4) => - x 0
        | (1 : Fin 4) => x 0 - x 1
        | (2 : Fin 4) => 2 * x 0 ^ 2 * x 2 ^ 2
        | (3 : Fin 4) => x 1 * x 2) := by
  show catalanPolyPIVP.evalField x i = _
  unfold PolyPIVP.evalField
  fin_cases i
  · show ((- X 0 : MvPolynomial (Fin 4) ℚ)).eval₂ (Rat.castHom ℝ) x = - x 0
    simp [MvPolynomial.eval₂_neg, MvPolynomial.eval₂_X]
  · show ((X 0 - X 1 : MvPolynomial (Fin 4) ℚ)).eval₂ (Rat.castHom ℝ) x = x 0 - x 1
    simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X]
  · show ((C 2 * X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 4) ℚ)).eval₂
          (Rat.castHom ℝ) x = 2 * x 0 ^ 2 * x 2 ^ 2
    simp [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_X]
  · show ((X 1 * X 2 : MvPolynomial (Fin 4) ℚ)).eval₂ (Rat.castHom ℝ) x = x 1 * x 2
    simp [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]

/-- Initial condition cast from ℚ to ℝ matches the closed-form at `t = 0`. -/
theorem catalanPolyPIVP_init_eq (i : Fin 4) :
    (catalanPolyPIVP.toPIVP.init i : ℝ) = catalanSolution 0 i := by
  show ((catalanPolyPIVP.init i : ℚ) : ℝ) = catalanSolution 0 i
  fin_cases i
  · simp [catalanPolyPIVP, catalanSolution]
  · simp [catalanPolyPIVP, catalanSolution]
  · show ((1/2 : ℚ) : ℝ) = 1 / (1 + Real.exp (-2 * 0))
    simp
    norm_num
  · show ((0 : ℚ) : ℝ) = ∫ s in (0:ℝ)..0, catalanIntegrand s
    simp

/-! ## Continuity of the closed-form solution -/

theorem catalanSolution_continuous : Continuous catalanSolution := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous fun t => catalanSolution t 0
    simp only [catalan_sol_E]
    exact Real.continuous_exp.comp continuous_neg
  · change Continuous fun t => catalanSolution t 1
    simp only [catalan_sol_R]
    exact continuous_id.mul (Real.continuous_exp.comp continuous_neg)
  · change Continuous fun t => catalanSolution t 2
    simp only [catalan_sol_W]
    have hden : Continuous (fun t : ℝ => 1 + exp (-2 * t)) :=
      continuous_const.add
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    exact continuous_const.div hden (fun t => ne_of_gt (one_add_exp_neg_two_pos t))
  · -- component 3: G(t) = ∫₀ᵗ f(s) ds, continuous as a function of t
    change Continuous fun t => catalanSolution t 3
    simp only [catalan_sol_G]
    have : Continuous fun t : ℝ => ∫ s in (0:ℝ)..t, catalanIntegrand s := by
      -- ∫ₐᵘ f for f continuous is continuous in u.
      exact intervalIntegral.continuous_primitive
        (fun a b => catalanIntegrand_continuous.intervalIntegrable a b) 0
    exact this

/-! ## Derivative of each component — the ODE is satisfied -/

/-- `catalanSolution` is a semantic solution of `catalanPolyPIVP.toPIVP`. -/
noncomputable def catalanPolySolution : PIVP.Solution catalanPolyPIVP.toPIVP where
  trajectory := catalanSolution
  init_cond := by
    funext i; exact (catalanPolyPIVP_init_eq i).symm
  is_solution := fun t _ => by
    -- Rewrite syntactic field to explicit form.
    have hfield : catalanPolyPIVP.toPIVP.field (catalanSolution t) =
        ![- exp (-t), exp (-t) - t * exp (-t),
          2 * exp (-t) ^ 2 * (1 / (1 + exp (-2 * t))) ^ 2,
          t * exp (-t) * (1 / (1 + exp (-2 * t)))] := by
      ext i
      rw [catalanPolyPIVP_evalField_eq]
      fin_cases i
      · show - catalanSolution t 0 = - exp (-t)
        rw [catalan_sol_E]
      · show catalanSolution t 0 - catalanSolution t 1 = exp (-t) - t * exp (-t)
        rw [catalan_sol_E, catalan_sol_R]
      · show 2 * catalanSolution t 0 ^ 2 * catalanSolution t 2 ^ 2 =
               2 * exp (-t) ^ 2 * (1 / (1 + exp (-2 * t))) ^ 2
        rw [catalan_sol_E, catalan_sol_W]
      · show catalanSolution t 1 * catalanSolution t 2 =
               t * exp (-t) * (1 / (1 + exp (-2 * t)))
        rw [catalan_sol_R, catalan_sol_W]
    rw [hfield, hasDerivAt_pi]
    have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
      simpa [id] using (hasDerivAt_id t).neg
    have h_exp_neg : HasDerivAt (fun s : ℝ => exp (-s)) (-exp (-t)) t := by
      convert h_neg.exp using 1; ring
    have h_neg_two : HasDerivAt (fun s : ℝ => -2 * s) (-2 : ℝ) t := by
      have := (hasDerivAt_id t).const_mul (-2 : ℝ)
      simpa using this
    have h_exp_neg_two : HasDerivAt (fun s : ℝ => exp (-2 * s))
        (-2 * exp (-2 * t)) t := by
      have := h_neg_two.exp
      convert this using 1; ring
    intro i; fin_cases i
    · -- d/dt exp(-t) = -exp(-t)
      change HasDerivAt (fun s => catalanSolution s 0) (- exp (-t)) t
      have : (fun s => catalanSolution s 0) = fun s => exp (-s) := by
        funext s; exact catalan_sol_E s
      rw [this]; exact h_exp_neg
    · -- d/dt (t * exp(-t)) = 1 * exp(-t) + t * (-exp(-t)) = exp(-t) - t*exp(-t)
      change HasDerivAt (fun s => catalanSolution s 1) (exp (-t) - t * exp (-t)) t
      have hsimp : (fun s => catalanSolution s 1) = fun s => s * exp (-s) := by
        funext s; exact catalan_sol_R s
      rw [hsimp]
      have := (hasDerivAt_id t).mul h_exp_neg
      convert this using 1; simp; ring
    · -- d/dt (1/(1 + exp(-2t))) = 2·exp(-2t) / (1+exp(-2t))²
      --                         = 2·exp(-t)² · (1/(1+exp(-2t)))²  (since exp(-t)² = exp(-2t))
      change HasDerivAt (fun s => catalanSolution s 2)
        (2 * exp (-t) ^ 2 * (1 / (1 + exp (-2 * t))) ^ 2) t
      have hsimp : (fun s => catalanSolution s 2) =
          fun s => 1 / (1 + exp (-2 * s)) := by
        funext s; exact catalan_sol_W s
      rw [hsimp]
      have h_den : HasDerivAt (fun s : ℝ => 1 + exp (-2 * s))
          (-2 * exp (-2 * t)) t := by
        have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ) + exp (-2 * s))
            (0 + (-2 * exp (-2 * t))) t :=
          (hasDerivAt_const t (1:ℝ)).add h_exp_neg_two
        convert h1 using 1; ring
      have hden_ne : (1 + exp (-2 * t)) ≠ 0 := ne_of_gt (one_add_exp_neg_two_pos t)
      have h_one := hasDerivAt_const t (1:ℝ)
      -- d/dt (1/u) = -(1 · u' - 0) / u² ... use .div:
      have h_div := h_one.div h_den hden_ne
      -- h_div : HasDerivAt (fun s => 1 / (1 + exp(-2s))) (D) t where
      --   D = (0 · (1 + exp(-2t)) - 1 · (-2·exp(-2t))) / (1+exp(-2t))²
      --     = 2·exp(-2t) / (1+exp(-2t))²
      convert h_div using 1
      have hsq : exp (-t) ^ 2 = exp (-2 * t) := by
        rw [sq, ← Real.exp_add]; ring_nf
      field_simp
      rw [hsq]; ring
    · -- d/dt ∫₀ᵗ f = f(t), where f(t) = t·exp(-t)/(1+exp(-2t)).
      change HasDerivAt (fun s => catalanSolution s 3)
        (t * exp (-t) * (1 / (1 + exp (-2 * t)))) t
      have hsimp : (fun s => catalanSolution s 3) =
          fun s => ∫ x in (0:ℝ)..s, catalanIntegrand x := by
        funext s; exact catalan_sol_G s
      rw [hsimp]
      have h_ftc : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, catalanIntegrand x)
          (catalanIntegrand t) t := by
        exact intervalIntegral.integral_hasDerivAt_right
          (catalanIntegrand_continuous.intervalIntegrable _ _)
          catalanIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
          catalanIntegrand_continuous.continuousAt
      convert h_ftc using 1
      unfold catalanIntegrand
      field_simp

/-! ## Boundedness -/

/-- On `[0, ∞)`: `E(t) ∈ [0, 1]`, `R(t) ∈ [0, 1/e] ⊂ [0, 1]`,
    `W(t) ∈ (0, 1]`, `G(t) ∈ [0, 1]`. So `‖catalanSolution t‖ ≤ 2`. -/
theorem catalan_bounded : catalanPolyPIVP.toPIVP.IsBounded catalanSolution := by
  refine ⟨2, by norm_num, ?_⟩
  intro t ht
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  intro i
  fin_cases i
  · -- E(t) = exp(-t) ∈ (0, 1]
    change ‖catalanSolution t 0‖ ≤ 2
    rw [catalan_sol_E]
    rw [norm_of_nonneg (exp_pos _).le]
    calc exp (-t)
        ≤ exp 0 := exp_le_exp.mpr (by linarith)
      _ = 1 := exp_zero
      _ ≤ 2 := by norm_num
  · -- R(t) = t·exp(-t) ∈ [0, 1]
    change ‖catalanSolution t 1‖ ≤ 2
    rw [catalan_sol_R]
    have hRnn : 0 ≤ t * exp (-t) := mul_nonneg ht (exp_pos _).le
    rw [norm_of_nonneg hRnn]
    have h_t_le_exp : t ≤ exp t := by
      have := Real.add_one_le_exp t
      linarith [this]
    calc t * exp (-t) ≤ exp t * exp (-t) :=
            mul_le_mul_of_nonneg_right h_t_le_exp (exp_pos _).le
      _ = exp (t + -t) := by rw [← Real.exp_add]
      _ = exp 0 := by ring_nf
      _ = 1 := exp_zero
      _ ≤ 2 := by norm_num
  · -- W(t) = 1/(1 + exp(-2t)) ∈ (0, 1]
    change ‖catalanSolution t 2‖ ≤ 2
    rw [catalan_sol_W]
    have hden_pos : 0 < 1 + exp (-2 * t) := one_add_exp_neg_two_pos t
    have hW_pos : 0 < 1 / (1 + exp (-2 * t)) := by positivity
    rw [norm_of_nonneg hW_pos.le]
    have hden_ge_1 : 1 ≤ 1 + exp (-2 * t) := one_add_exp_neg_two_ge_one t
    calc 1 / (1 + exp (-2 * t)) ≤ 1 / 1 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden_ge_1
      _ = 1 := by norm_num
      _ ≤ 2 := by norm_num
  · -- G(t) = ∫₀ᵗ f ∈ [0, ≤∫₀^∞f = Catalan ≤ 1]
    change ‖catalanSolution t 3‖ ≤ 2
    rw [catalan_sol_G]
    -- 0 ≤ G(t) ≤ ∫₀^∞ s·exp(-s) = 1, via comparison
    have hGint : IntervalIntegrable catalanIntegrand MeasureTheory.volume 0 t :=
      catalanIntegrand_continuous.intervalIntegrable _ _
    have hG_nn : 0 ≤ ∫ s in (0:ℝ)..t, catalanIntegrand s := by
      rw [intervalIntegral.integral_of_le ht]
      refine setIntegral_nonneg measurableSet_Ioc ?_
      intro s hs
      exact catalanIntegrand_nonneg (le_of_lt hs.1)
    have hG_le : ∫ s in (0:ℝ)..t, catalanIntegrand s ≤ 1 := by
      rw [intervalIntegral.integral_of_le ht]
      -- ∫ Ioc 0 t f ≤ ∫ Ioc 0 t (s·exp(-s)) ≤ ∫ Ioi 0 (s·exp(-s)) = (0+1)·exp(0) = 1.
      have hint_exp_Ioc : IntegrableOn (fun s : ℝ => s * exp (-s))
          (Set.Ioc (0:ℝ) t) := by
        refine (integrable_s_exp_neg_Ioi (le_refl 0)).mono_set ?_
        exact Set.Ioc_subset_Ioi_self
      have hint_cat_Ioc : IntegrableOn catalanIntegrand (Set.Ioc (0:ℝ) t) := by
        refine (integrable_catalanIntegrand_Ioi' (le_refl 0)).mono_set ?_
        exact Set.Ioc_subset_Ioi_self
      have hmono : ∫ s in Set.Ioc (0:ℝ) t, catalanIntegrand s ≤
          ∫ s in Set.Ioc (0:ℝ) t, s * exp (-s) := by
        refine setIntegral_mono_on hint_cat_Ioc hint_exp_Ioc measurableSet_Ioc ?_
        intro s hs
        exact catalanIntegrand_le (le_of_lt hs.1)
      -- Now bound ∫ Ioc 0 t (s·exp(-s)) ≤ ∫ Ioi 0 (s·exp(-s)) = 1
      have hexp_Ioi_nn : ∀ s, 0 ≤ (Set.Ioi (0:ℝ)).indicator (fun s => s * exp (-s)) s := by
        intro s
        by_cases hs : s ∈ Set.Ioi (0:ℝ)
        · rw [Set.indicator_of_mem hs]
          exact mul_nonneg (le_of_lt hs) (exp_pos _).le
        · simp [Set.indicator_of_notMem hs]
      -- Ioc 0 t ⊂ Ioi 0, so integral over Ioc ≤ integral over Ioi by non-negativity.
      have h_Ioc_le_Ioi : ∫ s in Set.Ioc (0:ℝ) t, s * exp (-s) ≤
          ∫ s in Set.Ioi (0:ℝ), s * exp (-s) := by
        have hint_Ioi : IntegrableOn (fun s : ℝ => s * exp (-s))
            (Set.Ioi (0:ℝ)) := integrable_s_exp_neg_Ioi (le_refl 0)
        refine setIntegral_mono_set hint_Ioi ?_ ?_
        · -- 0 ≤ f a.e. on Ioi 0
          refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
          exact Filter.Eventually.of_forall (fun s hs =>
            mul_nonneg (le_of_lt hs) (exp_pos _).le)
        · -- Ioc 0 t ⊂ᵐ Ioi 0
          exact Filter.Eventually.of_forall (fun s hs => hs.1)
      rw [integral_Ioi_s_exp_neg (le_refl 0)] at h_Ioc_le_Ioi
      have : (0 + 1) * exp (-(0:ℝ)) = 1 := by simp
      rw [this] at h_Ioc_le_Ioi
      linarith
    rw [norm_of_nonneg hG_nn]
    linarith

/-! ## Convergence: `|G(t) − catalanConstant| ≤ (t+1)·exp(-t)` -/

/-- For `t ≥ 0`: `G(t) = ∫ s in Ioc 0 t, f` equals the Ioc-integral of the
    Catalan integrand. -/
private lemma catalan_sol_G_eq_Ioc {t : ℝ} (ht : 0 ≤ t) :
    catalanSolution t 3 = ∫ s in Set.Ioc (0:ℝ) t, catalanIntegrand s := by
  rw [catalan_sol_G, intervalIntegral.integral_of_le ht]

/-- Main convergence bound. -/
theorem catalan_convergence (t : ℝ) (ht : 0 ≤ t) :
    |catalanSolution t 3 - catalanConstant| ≤ (t + 1) * exp (-t) := by
  rw [catalan_sol_G_eq_Ioc ht]
  unfold catalanConstant
  rw [integral_Ioi_split ht]
  -- Goal: |Ioc - (Ioc + Ioi)| = |-Ioi| = Ioi ≤ (t+1)·exp(-t)
  have h_tail_nn : 0 ≤ ∫ s in Set.Ioi t, catalanIntegrand s := tail_nonneg ht
  have h_tail_le : ∫ s in Set.Ioi t, catalanIntegrand s ≤ (t+1) * exp (-t) :=
    tail_le ht
  have : (∫ s in Set.Ioc (0:ℝ) t, catalanIntegrand s) -
           ((∫ s in Set.Ioc (0:ℝ) t, catalanIntegrand s) +
            ∫ s in Set.Ioi t, catalanIntegrand s) =
         - ∫ s in Set.Ioi t, catalanIntegrand s := by ring
  rw [this, abs_neg, abs_of_nonneg h_tail_nn]
  exact h_tail_le

/-! ## Tail → 0 implies `catalanConstant ∈ [0, 1]` -/

/-- Catalan's constant is non-negative (integral of non-negative function). -/
private lemma catalan_nonneg : 0 ≤ catalanConstant := by
  unfold catalanConstant
  refine setIntegral_nonneg measurableSet_Ioi ?_
  intro s hs
  exact catalanIntegrand_nonneg (le_of_lt hs)

/-- Catalan's constant is ≤ 1: bound by ∫₀^∞ s·exp(-s) = 1. -/
private lemma catalan_le_one : catalanConstant ≤ 1 := by
  unfold catalanConstant
  have hint_cat : IntegrableOn catalanIntegrand (Set.Ioi (0:ℝ)) :=
    integrable_catalanIntegrand_Ioi' (le_refl 0)
  have hint_exp : IntegrableOn (fun s : ℝ => s * exp (-s)) (Set.Ioi (0:ℝ)) :=
    integrable_s_exp_neg_Ioi (le_refl 0)
  have hmono : ∫ s in Set.Ioi (0:ℝ), catalanIntegrand s ≤
      ∫ s in Set.Ioi (0:ℝ), s * exp (-s) := by
    refine setIntegral_mono_on hint_cat hint_exp measurableSet_Ioi ?_
    intro s hs
    exact catalanIntegrand_le (le_of_lt hs)
  rw [integral_Ioi_s_exp_neg (le_refl 0)] at hmono
  simp at hmono
  exact hmono

/-! ## CertifiedBoundedTimeComputable witness -/

/-- For `t ≥ 2(r+1)`: `(t+1)·exp(-t) < exp(-r)`. -/
private lemma convergence_modulus_bound (r : ℕ) (t : ℝ)
    (ht : t ≥ 2 * ((r : ℝ) + 1) + 2) : (t + 1) * exp (-t) < exp (-(r : ℝ)) := by
  -- Strategy: (t+1) ≤ 2t (since t ≥ 1), so (t+1)·exp(-t) ≤ 2t·exp(-t).
  -- t·exp(-t) ≤ exp(-t/2) · (t·exp(-t/2))
  -- and t·exp(-t/2) → 0, but we need a concrete bound.
  -- Easier: use 1 + u ≤ exp(u) to get t + 1 ≤ exp(t/2) when t/2 ≥ ... hmm.
  -- Actually simplest: 1 + t ≤ exp(t/3) (eventually), giving
  -- (t+1)·exp(-t) ≤ exp(t/3 - t) = exp(-2t/3). For t ≥ (3/2)·r, exp(-2t/3) ≤ exp(-r).
  -- Let me use: for all x ≥ 0, 1 + x ≤ exp(x), so t + 1 ≤ exp(t).
  -- That gives (t+1)·exp(-t) ≤ 1. Not tight enough.
  -- Better: (1+t) · exp(-t) — at t = 0 gives 1, at t=∞ gives 0. Use t ≥ 2: t+1 ≤ 2t, and
  --   2t · exp(-t) ≤ 2t · exp(-t/2) · exp(-t/2).
  -- I need (t+1) · exp(-t) ≤ exp(-t/2) for t ≥ some threshold.
  -- Equivalent: (t+1) ≤ exp(t/2).
  -- exp(t/2) ≥ 1 + t/2 + (t/2)²/2 ≥ (t/2)²/2 = t²/8. For t ≥ 4: t²/8 ≥ 2t ≥ t+1.
  -- So for t ≥ 4: (t+1) ≤ t²/8 ≤ exp(t/2). Hence (t+1)·exp(-t) ≤ exp(-t/2).
  have hr_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have ht_ge_2 : t ≥ 2 := by linarith
  have ht_ge_4 : t ≥ 4 := by linarith
  have ht_pos : 0 < t := by linarith
  -- Step 1: (t + 1) ≤ exp (t / 2)
  -- Use: for x ≥ 0, 1 + x + x²/2 ≤ exp x (Mathlib: quadratic_le_exp_of_nonneg or similar).
  have h_quad_le : ∀ x : ℝ, 0 ≤ x → 1 + x + x^2 / 2 ≤ exp x := by
    intro x hx
    -- Use Real.add_one_le_exp twice? Or use `quadratic_le_exp`:
    have := Real.quadratic_le_exp_of_nonneg hx
    linarith
  have h_exp_half : exp (t / 2) ≥ 1 + t / 2 + (t/2)^2 / 2 :=
    h_quad_le (t/2) (by linarith)
  have h_tp1_le_quad : (t + 1) ≤ 1 + t / 2 + (t/2)^2 / 2 := by
    have : (t/2)^2 / 2 = t^2 / 8 := by ring
    rw [this]
    nlinarith [ht_ge_4, sq_nonneg (t - 4)]
  have h_tp1_le : (t + 1) ≤ exp (t / 2) := le_trans h_tp1_le_quad h_exp_half
  -- Step 2: (t+1) · exp(-t) ≤ exp(t/2) · exp(-t) = exp(-t/2).
  have hmul_le : (t + 1) * exp (-t) ≤ exp (t / 2) * exp (-t) :=
    mul_le_mul_of_nonneg_right h_tp1_le (exp_pos _).le
  have hexp_combine : exp (t / 2) * exp (-t) = exp (-(t/2)) := by
    rw [← Real.exp_add]; ring_nf
  -- Step 3: exp(-t/2) < exp(-r) requires t/2 > r, i.e. t > 2r.
  have h_t_half_gt_r : t / 2 > (r : ℝ) := by linarith
  have hexp_lt : exp (-(t/2)) < exp (-(r : ℝ)) := by
    apply exp_lt_exp.mpr
    linarith
  calc (t + 1) * exp (-t)
      ≤ exp (t / 2) * exp (-t) := hmul_le
    _ = exp (-(t/2)) := hexp_combine
    _ < exp (-(r : ℝ)) := hexp_lt

/-- `CertifiedBoundedTimeComputable` witness for Catalan's constant. -/
noncomputable def catalanCBTC : CertifiedBoundedTimeComputable 4 catalanConstant where
  pivp := catalanPolyPIVP
  sol := catalanPolySolution
  modulus := fun r => 2 * ((r : ℝ) + 1) + 2
  bounded := catalan_bounded
  trajectory_continuous := catalanSolution_continuous
  convergence := by
    intro r t htr
    have hr_nn : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r
    have ht_pos : 0 ≤ t := by
      have h1 : (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) + 2 := by linarith
      linarith
    show |catalanSolution t catalanPolyPIVP.output - catalanConstant| <
      Real.exp (-(r : ℝ))
    have hout : catalanPolyPIVP.output = (3 : Fin 4) := rfl
    rw [hout]
    calc |catalanSolution t 3 - catalanConstant|
        ≤ (t + 1) * exp (-t) := catalan_convergence t ht_pos
      _ < exp (-(r : ℝ)) := convergence_modulus_bound r t (le_of_lt htr)

/-! ## PolyCRNDecomposition witness -/

/-- Production polynomials: prod₀ = 0, prod₁ = X₀, prod₂ = 2·X₀²·X₂², prod₃ = X₁·X₂. -/
noncomputable def catalanProd : Fin 4 → MvPolynomial (Fin 4) ℚ
  | 0 => 0
  | 1 => X 0
  | 2 => C 2 * X 0 ^ 2 * X 2 ^ 2
  | 3 => X 1 * X 2

/-- Degradation polynomials: degr₀ = C 1, degr₁ = C 1, degr₂ = 0, degr₃ = 0. -/
noncomputable def catalanDegr : Fin 4 → MvPolynomial (Fin 4) ℚ
  | 0 => C 1
  | 1 => C 1
  | 2 => 0
  | 3 => 0

private lemma coeff_mul_nonneg {d : ℕ} (p q : MvPolynomial (Fin d) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) (hq : ∀ σ, 0 ≤ q.coeff σ) :
    ∀ σ, 0 ≤ (p * q).coeff σ := by
  classical
  intro σ
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_nonneg
  intro ⟨a, b⟩ _
  exact mul_nonneg (hp a) (hq b)

private lemma coeff_pow_nonneg {d : ℕ} (p : MvPolynomial (Fin d) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) (n : ℕ) :
    ∀ σ, 0 ≤ (p ^ n).coeff σ := by
  induction n with
  | zero => intro σ; simp [MvPolynomial.coeff_one]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    exact coeff_mul_nonneg _ _ ih hp

private lemma coeff_X_nonneg {d : ℕ} (i : Fin d) :
    ∀ σ, 0 ≤ ((X i : MvPolynomial (Fin d) ℚ)).coeff σ := by
  classical
  intro σ
  rw [MvPolynomial.coeff_X']
  split_ifs <;> norm_num

private lemma coeff_C_nonneg {d : ℕ} {c : ℚ} (hc : 0 ≤ c) :
    ∀ σ, 0 ≤ ((C c : MvPolynomial (Fin d) ℚ)).coeff σ := by
  intro σ
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hc
  · exact le_refl _

theorem catalanProd_nonneg (i : Fin 4) (σ : Fin 4 →₀ ℕ) :
    0 ≤ (catalanProd i).coeff σ := by
  fin_cases i
  · simp [catalanProd]
  · show 0 ≤ ((X 0 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_X_nonneg 0 σ
  · -- prod 2 = C 2 * X 0 ^ 2 * X 2 ^ 2
    show 0 ≤ ((C 2 * X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_mul_nonneg _ _
      (coeff_mul_nonneg _ _ (coeff_C_nonneg (by norm_num))
        (coeff_pow_nonneg _ (coeff_X_nonneg 0) 2))
      (coeff_pow_nonneg _ (coeff_X_nonneg 2) 2) σ
  · -- prod 3 = X 1 * X 2
    show 0 ≤ ((X 1 * X 2 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_mul_nonneg _ _ (coeff_X_nonneg 1) (coeff_X_nonneg 2) σ

theorem catalanDegr_nonneg (i : Fin 4) (σ : Fin 4 →₀ ℕ) :
    0 ≤ (catalanDegr i).coeff σ := by
  fin_cases i
  · show 0 ≤ ((C 1 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_C_nonneg (by norm_num) σ
  · show 0 ≤ ((C 1 : MvPolynomial (Fin 4) ℚ)).coeff σ
    exact coeff_C_nonneg (by norm_num) σ
  · simp [catalanDegr]
  · simp [catalanDegr]

theorem catalanPolyPIVP_init_nonneg (i : Fin 4) : 0 ≤ catalanPolyPIVP.init i := by
  fin_cases i
  · show (0 : ℚ) ≤ 1; norm_num
  · show (0 : ℚ) ≤ 0; norm_num
  · show (0 : ℚ) ≤ 1/2; norm_num
  · show (0 : ℚ) ≤ 0; norm_num

/-- Syntactic field decomposition: field_i = prod_i − degr_i · X_i. -/
theorem catalanPolyPIVP_field_eq (i : Fin 4) :
    catalanPolyPIVP.field i = catalanProd i - catalanDegr i * MvPolynomial.X i := by
  fin_cases i
  · -- field 0 = -X 0 = 0 - C 1 * X 0
    show (- X 0 : MvPolynomial (Fin 4) ℚ) = 0 - C 1 * X 0
    rw [MvPolynomial.C_1]; ring
  · -- field 1 = X 0 - X 1 = X 0 - C 1 * X 1
    show (X 0 - X 1 : MvPolynomial (Fin 4) ℚ) = X 0 - C 1 * X 1
    rw [MvPolynomial.C_1]; ring
  · -- field 2 = C 2 * X 0 ^ 2 * X 2 ^ 2 = (C 2 * X 0 ^ 2 * X 2 ^ 2) - 0 * X 2
    show (C 2 * X 0 ^ 2 * X 2 ^ 2 : MvPolynomial (Fin 4) ℚ) =
      C 2 * X 0 ^ 2 * X 2 ^ 2 - 0 * X 2
    ring
  · -- field 3 = X 1 * X 2 = X 1 * X 2 - 0 * X 3
    show (X 1 * X 2 : MvPolynomial (Fin 4) ℚ) = X 1 * X 2 - 0 * X 3
    ring

/-- `PolyCRNDecomposition` witness for `catalanPolyPIVP`. -/
noncomputable def catalanPCD : PolyCRNDecomposition 4 catalanPolyPIVP where
  prod := catalanProd
  degr := catalanDegr
  prod_nonneg := catalanProd_nonneg
  degr_nonneg := catalanDegr_nonneg
  init_nonneg := catalanPolyPIVP_init_nonneg
  field_eq := catalanPolyPIVP_field_eq

/-! ## Main theorem: Catalan's constant is LPP-computable -/

private theorem catalan_in_unit : 0 ≤ catalanConstant ∧ catalanConstant ≤ 1 :=
  ⟨catalan_nonneg, catalan_le_one⟩

/-- **Catalan's constant is LPP-computable** via the direct bounded-CRN-computable
route (no dual-rail). -/
theorem catalan_is_lpp_computable : ∃ _ : IsLPPComputable catalanConstant, True :=
  bounded_crn_is_lpp_computable_unconditional catalan_in_unit catalanCBTC catalanPCD

end Ripple.Number
