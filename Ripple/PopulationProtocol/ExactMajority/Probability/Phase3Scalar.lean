/-
Protocol-independent scalar estimates for the Phase-3 clock analysis.

Intended module:
  Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar

-/

import Ripple.Probability.DiscreteFreedman
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Stopping
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeScalar

section Filtered

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}

/-! ## Adapted Bernoulli moments and tails -/

/-- The first N indicators, indexed from zero. The indicator at t
is measurable at time t + 1; its conditional probability is controlled
at time t. -/
noncomputable def bernoulliCount (I : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range N, I t ω

theorem bernoulli_integrable
    {I : ℕ → Ω → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (t : ℕ) : Integrable (I t) μ := by
  refine Integrable.of_bound
    ((hI t).mono (ℱ.le (t + 1))).aestronglyMeasurable 1 ?_
  filter_upwards [hzeroOne t] with ω hω
  rcases hω with hω | hω <;> simp [hω]

theorem bernoulliCount_stronglyMeasurable
    {I : ℕ → Ω → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (N : ℕ) : StronglyMeasurable[ℱ N] (bernoulliCount I N) := by
  unfold bernoulliCount
  refine (Finset.range N).stronglyMeasurable_fun_sum ?_
  intro t ht
  exact (hI t).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.mp ht)))

theorem bernoulliCount_bounds
    {I : ℕ → Ω → ℝ}
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (N : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ bernoulliCount I N ω ∧
      bernoulliCount I N ω ≤ (N : ℝ) := by
  filter_upwards [ae_all_iff.2 hzeroOne] with ω hω
  constructor
  · exact Finset.sum_nonneg fun t _ => by
      rcases hω t with ht | ht <;> simp [ht]
  · calc
      bernoulliCount I N ω ≤ ∑ _t ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        rcases hω t with ht | ht <;> simp [ht]
      _ = (N : ℝ) := by simp

theorem bernoulli_exp_integrable
    {I : ℕ → Ω → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (θ : ℝ) (N : ℕ) :
    Integrable (fun ω => Real.exp (θ * bernoulliCount I N ω)) μ := by
  have hS : StronglyMeasurable (bernoulliCount I N) :=
    (bernoulliCount_stronglyMeasurable hI N).mono (ℱ.le N)
  have hsm : StronglyMeasurable
      (fun ω => Real.exp (θ * bernoulliCount I N ω)) := by
    fun_prop
  refine Integrable.of_bound hsm.aestronglyMeasurable
    (Real.exp (|θ| * (N : ℝ))) ?_
  filter_upwards [bernoulliCount_bounds hzeroOne N] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_le_exp]
  exact (mul_le_mul_of_nonneg_right (le_abs_self θ) hω.1).trans
    (mul_le_mul_of_nonneg_left hω.2 (abs_nonneg θ))

private theorem bernoulli_exp_identity
    {I : ℕ → Ω → ℝ}
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (θ : ℝ) (t : ℕ) :
    (fun ω => Real.exp (θ * I t ω)) =ᵐ[μ]
      fun ω => 1 + (Real.exp θ - 1) * I t ω := by
  filter_upwards [hzeroOne t] with ω hω
  rcases hω with hω | hω <;> simp [hω] <;> ring

private theorem bernoulli_condExp_exp
    {I : ℕ → Ω → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (θ : ℝ) (t : ℕ) :
    μ[fun ω => Real.exp (θ * I t ω) | ℱ t] =ᵐ[μ]
      fun ω => 1 + (Real.exp θ - 1) * μ[I t | ℱ t] ω := by
  have hadd := condExp_add
    (integrable_const (1 : ℝ))
    ((bernoulli_integrable hI hzeroOne t).const_mul (Real.exp θ - 1)) (ℱ t)
  have hmul :
      μ[fun ω => (Real.exp θ - 1) * I t ω | ℱ t] =ᵐ[μ]
        fun ω => (Real.exp θ - 1) * μ[I t | ℱ t] ω := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      condExp_smul (μ := μ) (Real.exp θ - 1) (I t) (ℱ t)
  have hlinear :
      μ[fun ω => 1 + (Real.exp θ - 1) * I t ω | ℱ t] =ᵐ[μ]
        fun ω => 1 + (Real.exp θ - 1) * μ[I t | ℱ t] ω := by
    filter_upwards [hadd, hmul] with ω haddω hmulω
    calc
      μ[fun ω => 1 + (Real.exp θ - 1) * I t ω | ℱ t] ω =
          μ[fun _ : Ω => (1 : ℝ) | ℱ t] ω +
            μ[fun ω => (Real.exp θ - 1) * I t ω | ℱ t] ω := haddω
      _ = 1 + (Real.exp θ - 1) * μ[I t | ℱ t] ω := by
        rw [condExp_const (ℱ.le t) (1 : ℝ), hmulω]
  exact (condExp_congr_ae (bernoulli_exp_identity hzeroOne θ t)).trans hlinear

/-- The common positive- and negative-parameter iteration. The coefficient
condition reverses the conditional-probability inequality automatically when
the exponential parameter is negative. -/
private theorem bernoulli_exp_moment_of_coefficient
    {I : ℕ → Ω → ℝ} {p : ℕ → ℝ} {θ : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcoef : ∀ t, ∀ᵐ ω ∂μ,
      (Real.exp θ - 1) * μ[I t | ℱ t] ω ≤ (Real.exp θ - 1) * p t)
    (N : ℕ) :
    (∫ ω, Real.exp (θ * bernoulliCount I N ω) ∂μ) ≤
      Real.exp ((Real.exp θ - 1) * ∑ t ∈ Finset.range N, p t) := by
  let Z : ℕ → Ω → ℝ :=
    fun n ω => Real.exp (θ * bernoulliCount I n ω)
  have hZint : ∀ n, Integrable (Z n) μ :=
    fun n => bernoulli_exp_integrable hI hzeroOne θ n
  have hZsm : ∀ n, StronglyMeasurable[ℱ n] (Z n) := by
    intro n
    have hS := bernoulliCount_stronglyMeasurable hI n
    dsimp [Z]
    fun_prop
  change (∫ ω, Z N ω ∂μ) ≤ _
  induction N with
  | zero => simp [Z, bernoulliCount]
  | succ N ih =>
      let G : Ω → ℝ := fun ω => Real.exp (θ * I N ω)
      have hGint : Integrable G μ := by
        have hp : Integrable
            (fun ω => 1 + (Real.exp θ - 1) * I N ω) μ :=
          (integrable_const (1 : ℝ)).add
            ((bernoulli_integrable hI hzeroOne N).const_mul (Real.exp θ - 1))
        exact hp.congr (bernoulli_exp_identity hzeroOne θ N).symm
      have hstep : Z (N + 1) = Z N * G := by
        funext ω
        simp only [Z, G, Pi.mul_apply, bernoulliCount,
          Finset.sum_range_succ, mul_add, Real.exp_add]
      have hstepae : Z (N + 1) =ᵐ[μ] Z N * G :=
        Filter.Eventually.of_forall (congrFun hstep)
      have hprodint : Integrable (Z N * G) μ :=
        (hZint (N + 1)).congr hstepae
      have hpull :
          μ[Z N * G | ℱ N] =ᵐ[μ] Z N * μ[G | ℱ N] :=
        condExp_mul_of_stronglyMeasurable_left (hZsm N) hprodint hGint
      have hce :
          μ[Z (N + 1) | ℱ N] =ᵐ[μ] Z N * μ[G | ℱ N] :=
        (condExp_congr_ae hstepae).trans hpull
      have hGbound :
          μ[G | ℱ N] ≤ᵐ[μ]
            fun _ => Real.exp ((Real.exp θ - 1) * p N) := by
        filter_upwards [bernoulli_condExp_exp hI hzeroOne θ N, hcoef N] with
          ω hid hcoefω
        change μ[fun ω => Real.exp (θ * I N ω) | ℱ N] ω ≤ _
        rw [hid]
        calc
          1 + (Real.exp θ - 1) * μ[I N | ℱ N] ω ≤
              1 + (Real.exp θ - 1) * p N := by linarith [hcoefω]
          _ ≤ Real.exp ((Real.exp θ - 1) * p N) := by
            simpa [add_comm] using
              Real.add_one_le_exp ((Real.exp θ - 1) * p N)
      have hbound :
          μ[Z (N + 1) | ℱ N] ≤ᵐ[μ]
            fun ω => Real.exp ((Real.exp θ - 1) * p N) * Z N ω := by
        filter_upwards [hce, hGbound] with ω hceω hGω
        change μ[Z (N + 1) | ℱ N] ω ≤ _
        rw [hceω]
        change Z N ω * μ[G | ℱ N] ω ≤ _
        calc
          Z N ω * μ[G | ℱ N] ω ≤
              Z N ω * Real.exp ((Real.exp θ - 1) * p N) :=
            mul_le_mul_of_nonneg_left hGω (Real.exp_nonneg _)
          _ = Real.exp ((Real.exp θ - 1) * p N) * Z N ω := mul_comm _ _
      calc
        (∫ ω, Z (N + 1) ω ∂μ) =
            ∫ ω, μ[Z (N + 1) | ℱ N] ω ∂μ :=
          (integral_condExp (ℱ.le N)).symm
        _ ≤ ∫ ω, Real.exp ((Real.exp θ - 1) * p N) * Z N ω ∂μ :=
          integral_mono_ae integrable_condExp
            ((hZint N).const_mul _) hbound
        _ = Real.exp ((Real.exp θ - 1) * p N) *
            ∫ ω, Z N ω ∂μ := by rw [integral_const_mul]
        _ ≤ Real.exp ((Real.exp θ - 1) * p N) *
            Real.exp ((Real.exp θ - 1) * ∑ t ∈ Finset.range N, p t) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp ((Real.exp θ - 1) * ∑ t ∈ Finset.range (N + 1), p t) := by
          rw [← Real.exp_add, Finset.sum_range_succ]
          congr 1
          ring

/-- Exponential moment bound. No independence assumption is used. -/
theorem adapted_bernoulli_exp_moment
    {I : ℕ → Ω → ℝ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, μ[I t | ℱ t] ≤ᵐ[μ] fun _ => p t)
    {θ : ℝ} (hθ : 0 ≤ θ) (N : ℕ) :
    (∫ ω, Real.exp (θ * bernoulliCount I N ω) ∂μ) ≤
      Real.exp ((Real.exp θ - 1) * ∑ t ∈ Finset.range N, p t) := by
  apply bernoulli_exp_moment_of_coefficient hI hzeroOne ?_ N
  intro t
  filter_upwards [hcond t] with ω hω
  exact mul_le_mul_of_nonneg_left hω
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hθ))

private theorem bernoulli_chernoff
    {I : ℕ → Ω → ℝ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, μ[I t | ℱ t] ≤ᵐ[μ] fun _ => p t)
    {θ r : ℝ} (hθ : 0 ≤ θ) (N : ℕ) :
    μ.real {ω | r ≤ bernoulliCount I N ω} ≤
      Real.exp ((Real.exp θ - 1) *
        (∑ t ∈ Finset.range N, p t) - θ * r) := by
  have hsub : {ω | r ≤ bernoulliCount I N ω} ⊆
      {ω | Real.exp (θ * r) ≤ Real.exp (θ * bernoulliCount I N ω)} := by
    intro ω hω
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ)
  have hprob := measureReal_mono (μ := μ) hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Real.exp_nonneg
      (θ * bernoulliCount I N ω)))
    (bernoulli_exp_integrable hI hzeroOne θ N) (Real.exp (θ * r))
  have hmul :
      Real.exp (θ * r) * μ.real {ω | r ≤ bernoulliCount I N ω} ≤
        Real.exp ((Real.exp θ - 1) * ∑ t ∈ Finset.range N, p t) :=
    (mul_le_mul_of_nonneg_left hprob (Real.exp_nonneg _)).trans
      (hmarkov.trans (adapted_bernoulli_exp_moment hI hzeroOne hcond hθ N))
  calc
    μ.real {ω | r ≤ bernoulliCount I N ω} ≤
        Real.exp ((Real.exp θ - 1) * ∑ t ∈ Finset.range N, p t) /
          Real.exp (θ * r) := by
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa [mul_comm] using hmul
    _ = _ := (Real.exp_sub _ _).symm

/-- Equation (16) in the positive-mean regime; the full endpoint-inclusive
version is proved below. The exponent is real exponentiation. -/
theorem adapted_bernoulli_upper_tail_of_pos
    {I : ℕ → Ω → ℝ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, μ[I t | ℱ t] ≤ᵐ[μ] fun _ => p t)
    (N : ℕ) {r : ℝ}
    (hmean : 0 < ∑ t ∈ Finset.range N, p t)
    (hr : (∑ t ∈ Finset.range N, p t) ≤ r) :
    μ.real {ω | r ≤ bernoulliCount I N ω} ≤
      (Real.exp 1 * (∑ t ∈ Finset.range N, p t) / r) ^ r := by
  let P : ℝ := ∑ t ∈ Finset.range N, p t
  have hP : 0 < P := hmean
  have hrpos : 0 < r := lt_of_lt_of_le hP hr
  let θ : ℝ := Real.log (r / P)
  have hratio : 1 ≤ r / P := (le_div_iff₀ hP).2 (by simpa using hr)
  have hθ : 0 ≤ θ := Real.log_nonneg hratio
  have hexp : Real.exp θ = r / P :=
    Real.exp_log (div_pos hrpos hP)
  have hcoef : (Real.exp θ - 1) * P = r - P := by
    rw [hexp]
    field_simp [hP.ne'] <;> ring
  have hbasepos : 0 < Real.exp 1 * P / r := by positivity
  have hbase : Real.exp 1 * P / r = Real.exp 1 / (r / P) := by
    field_simp [hP.ne', hrpos.ne'] <;> ring
  have hlogbase : Real.log (Real.exp 1 * P / r) = 1 - θ := by
    rw [hbase, Real.log_div (Real.exp_ne_zero 1)
      (div_ne_zero hrpos.ne' hP.ne'), Real.log_exp]
  have htail := bernoulli_chernoff hI hzeroOne hcond hθ N (r := r)
  change μ.real {ω | r ≤ bernoulliCount I N ω} ≤
    (Real.exp 1 * P / r) ^ r
  refine htail.trans ?_
  change Real.exp ((Real.exp θ - 1) * P - θ * r) ≤ _
  rw [Real.rpow_def_of_pos hbasepos, Real.exp_le_exp, hcoef, hlogbase]
  nlinarith [hP.le]

/-- Chernoff-type bound for adapted Bernoulli variables.
The independent binomial estimate is a special case. -/
theorem adapted_bernoulli_lower_tail
    {I : ℕ → Ω → ℝ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, (fun _ => p t) ≤ᵐ[μ] μ[I t | ℱ t])
    (N : ℕ) (k : ℝ) :
    μ.real {ω | bernoulliCount I N ω < k} ≤
      Real.exp (k * Real.log 2 - (∑ t ∈ Finset.range N, p t) / 2) := by
  let θ : ℝ := -Real.log 2
  have hθ : θ ≤ 0 := neg_nonpos.mpr (Real.log_nonneg (by norm_num))
  have hexp : Real.exp θ = (1 : ℝ) / 2 := by
    dsimp [θ]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hcoef : ∀ t, ∀ᵐ ω ∂μ,
      (Real.exp θ - 1) * μ[I t | ℱ t] ω ≤ (Real.exp θ - 1) * p t := by
    intro t
    filter_upwards [hcond t] with ω hω
    apply mul_le_mul_of_nonpos_left hω
    rw [hexp]
    norm_num
  have hmgf := bernoulli_exp_moment_of_coefficient hI hzeroOne hcoef N
  have hsub : {ω | bernoulliCount I N ω < k} ⊆
      {ω | Real.exp (θ * k) ≤ Real.exp (θ * bernoulliCount I N ω)} := by
    intro ω hω
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hω.le hθ)
  have hprob := measureReal_mono (μ := μ) hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Real.exp_nonneg
      (θ * bernoulliCount I N ω)))
    (bernoulli_exp_integrable hI hzeroOne θ N) (Real.exp (θ * k))
  have hmul :
      Real.exp (θ * k) * μ.real {ω | bernoulliCount I N ω < k} ≤
        Real.exp ((Real.exp θ - 1) * ∑ t ∈ Finset.range N, p t) :=
    (mul_le_mul_of_nonneg_left hprob (Real.exp_nonneg _)).trans
      (hmarkov.trans hmgf)
  calc
    μ.real {ω | bernoulliCount I N ω < k} ≤
        Real.exp ((Real.exp θ - 1) * ∑ t ∈ Finset.range N, p t) /
          Real.exp (θ * k) := by
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa [mul_comm] using hmul
    _ = Real.exp (k * Real.log 2 - (∑ t ∈ Finset.range N, p t) / 2) := by
      rw [← Real.exp_sub, hexp]
      congr 1
      dsimp [θ]
      ring

/-- The zero-mean endpoint. No sign assumption on the individual
deterministic bounds is required. -/
theorem adapted_bernoulli_upper_tail_zero_mean
    {I : ℕ → Ω → ℝ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, μ[I t | ℱ t] ≤ᵐ[μ] fun _ => p t)
    (N : ℕ) (hzero : ∑ t ∈ Finset.range N, p t = 0)
    (r : ℝ) (hr : 0 < r) :
    μ.real {ω | r ≤ bernoulliCount I N ω} = 0 := by
  have hint : Integrable (bernoulliCount I N) μ := by
    unfold bernoulliCount
    exact integrable_finsetSum _ fun t _ =>
      bernoulli_integrable hI hzeroOne t
  have hmean (t : ℕ) : (∫ ω, I t ω ∂μ) ≤ p t := by
    calc
      (∫ ω, I t ω ∂μ) =
          ∫ ω, (μ[I t | ℱ t]) ω ∂μ :=
        (integral_condExp (ℱ.le t)).symm
      _ ≤ ∫ _ : Ω, p t ∂μ :=
        integral_mono_ae integrable_condExp (integrable_const _) (hcond t)
      _ = p t := by simp
  have hsum :
      (∫ ω, bernoulliCount I N ω ∂μ) ≤ 0 := by
    calc
      (∫ ω, bernoulliCount I N ω ∂μ) =
          ∑ t ∈ Finset.range N, ∫ ω, I t ω ∂μ := by
        unfold bernoulliCount
        exact integral_finsetSum _ fun t _ =>
          bernoulli_integrable hI hzeroOne t
      _ ≤ ∑ t ∈ Finset.range N, p t :=
        Finset.sum_le_sum fun t _ => hmean t
      _ = 0 := hzero
  have hnonneg : 0 ≤ᵐ[μ] bernoulliCount I N := by
    filter_upwards [bernoulliCount_bounds hzeroOne N] with ω hω
    exact hω.1
  have hEzero : (∫ ω, bernoulliCount I N ω ∂μ) = 0 :=
    le_antisymm hsum (integral_nonneg_of_ae hnonneg)
  have haezero : bernoulliCount I N =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hEzero
  have hnot : ∀ᵐ ω ∂μ, ¬ r ≤ bernoulliCount I N ω := by
    filter_upwards [haezero] with ω hω
    change bernoulliCount I N ω = 0 at hω
    rw [hω]
    exact not_le.mpr hr
  have hnull : μ {ω | r ≤ bernoulliCount I N ω} = 0 := by
    simpa only [not_not] using (ae_iff.mp hnot)
  simp [Measure.real, hnull]

/-- Tail bound, including zero total mean and zero threshold.
For a positive threshold and zero mean the event has probability zero.
At zero threshold the conventional real-valued expression on the right
equals one. -/
theorem adapted_bernoulli_upper_tail
    {I : ℕ → Ω → ℝ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, μ[I t | ℱ t] ≤ᵐ[μ] fun _ => p t)
    (N : ℕ) {r : ℝ}
    (hmean : 0 ≤ ∑ t ∈ Finset.range N, p t)
    (hr : (∑ t ∈ Finset.range N, p t) ≤ r) :
    μ.real {ω | r ≤ bernoulliCount I N ω} ≤
      (Real.exp 1 * (∑ t ∈ Finset.range N, p t) / r) ^ r := by
  by_cases hpos : 0 < ∑ t ∈ Finset.range N, p t
  · exact adapted_bernoulli_upper_tail_of_pos hI hzeroOne hcond N hpos hr
  have hzero : ∑ t ∈ Finset.range N, p t = 0 :=
    le_antisymm (le_of_not_gt hpos) hmean
  by_cases hrpos : 0 < r
  · rw [adapted_bernoulli_upper_tail_zero_mean hI hzeroOne hcond N hzero r hrpos]
    exact Real.rpow_nonneg (by rw [hzero]; simp) _
  · have hrzero : r = 0 :=
      le_antisymm (le_of_not_gt hrpos) (hmean.trans hr)
    simpa [hrzero] using
      (show μ.real {ω | (0 : ℝ) ≤ bernoulliCount I N ω} ≤ 1 from
        measureReal_le_one)

/-- Equation (16) with any deterministic upper bound on the sum of the
stepwise bounds. -/
theorem adapted_bernoulli_upper_tail_of_total_bound
    {I : ℕ → Ω → ℝ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, μ[I t | ℱ t] ≤ᵐ[μ] fun _ => p t)
    (N : ℕ) {m r : ℝ}
    (hmean : 0 ≤ ∑ t ∈ Finset.range N, p t)
    (hm : (∑ t ∈ Finset.range N, p t) ≤ m) (hr : m ≤ r) :
    μ.real {ω | r ≤ bernoulliCount I N ω} ≤
      (Real.exp 1 * m / r) ^ r := by
  have hrnonneg : 0 ≤ r := hmean.trans (hm.trans hr)
  refine (adapted_bernoulli_upper_tail hI hzeroOne hcond N hmean
    (hm.trans hr)).trans ?_
  apply Real.rpow_le_rpow
  · exact div_nonneg (mul_nonneg (Real.exp_nonneg _) hmean) hrnonneg
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)) hrnonneg
  · exact hrnonneg

/-! ## Predictable stopping and filling after a target hit -/

/-- Keep the step indexed by t precisely when the target has not been
hit by time t. Thus the step which first hits the target is retained. -/
noncomputable def stoppedBernoulli
    (I : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) (t : ℕ) : Ω → ℝ :=
  {ω | (t : WithTop ℕ) < τ ω}.indicator (I t)

/-- Fill each success indicator by one after the target has been hit. -/
noncomputable def filledBernoulli
    (I : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) (t : ℕ) : Ω → ℝ :=
  stoppedBernoulli I τ t +
    ({ω | (t : WithTop ℕ) < τ ω}ᶜ).indicator (fun _ => 1)

private theorem stoppedBernoulli_adapted
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hτ : IsStoppingTime ℱ τ) :
    ∀ t, StronglyMeasurable[ℱ (t + 1)] (stoppedBernoulli I τ t) := by
  intro t
  exact (hI t).indicator
    ((ℱ.mono (Nat.le_succ t)) _ (hτ.measurableSet_gt t))

private theorem stoppedBernoulli_zero_one
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1) :
    ∀ t, ∀ᵐ ω ∂μ,
      stoppedBernoulli I τ t ω = 0 ∨ stoppedBernoulli I τ t ω = 1 := by
  intro t
  filter_upwards [hzeroOne t] with ω hω
  by_cases h : (t : WithTop ℕ) < τ ω
  · simpa [stoppedBernoulli, h] using hω
  · simp [stoppedBernoulli, h]

private theorem stoppedBernoulli_condExp_le
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hτ : IsStoppingTime ℱ τ) (hp : ∀ t, 0 ≤ p t)
    (hcond : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < τ ω →
      (μ[I t | ℱ t]) ω ≤ p t) :
    ∀ t, μ[stoppedBernoulli I τ t | ℱ t] ≤ᵐ[μ] fun _ => p t := by
  intro t
  have he :
      μ[stoppedBernoulli I τ t | ℱ t] =ᵐ[μ]
        {ω | (t : WithTop ℕ) < τ ω}.indicator (μ[I t | ℱ t]) :=
    condExp_indicator (bernoulli_integrable hI hzeroOne t)
      (hτ.measurableSet_gt t)
  filter_upwards [he, hcond t] with ω heω hcω
  rw [heω]
  by_cases h : (t : WithTop ℕ) < τ ω
  · simpa [h] using hcω h
  · simpa [h] using hp t

/-- Equation (14) for stopped indicators. The conditional bound is required
only before the stopping time; no conditioning on a future good event occurs. -/
theorem adapted_bernoulli_exp_moment_stopped
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hτ : IsStoppingTime ℱ τ) (hp : ∀ t, 0 ≤ p t)
    (hcond : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < τ ω →
      (μ[I t | ℱ t]) ω ≤ p t)
    {θ : ℝ} (hθ : 0 ≤ θ) (N : ℕ) :
    (∫ ω, Real.exp (θ * bernoulliCount (stoppedBernoulli I τ) N ω) ∂μ)
      ≤ Real.exp ((Real.exp θ - 1) * ∑ t ∈ Finset.range N, p t) := by
  exact adapted_bernoulli_exp_moment
    (stoppedBernoulli_adapted hI hτ)
    (stoppedBernoulli_zero_one hzeroOne)
    (stoppedBernoulli_condExp_le hI hzeroOne hτ hp hcond) hθ N

private theorem filledBernoulli_adapted
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hτ : IsStoppingTime ℱ τ) :
    ∀ t, StronglyMeasurable[ℱ (t + 1)] (filledBernoulli I τ t) := by
  intro t
  have hc : StronglyMeasurable[ℱ (t + 1)] (fun _ : Ω => (1 : ℝ)) :=
    stronglyMeasurable_const
  exact (stoppedBernoulli_adapted hI hτ t).add
    (hc.indicator
      ((ℱ.mono (Nat.le_succ t)) _ (hτ.measurableSet_gt t).compl))

private theorem filledBernoulli_zero_one
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1) :
    ∀ t, ∀ᵐ ω ∂μ,
      filledBernoulli I τ t ω = 0 ∨ filledBernoulli I τ t ω = 1 := by
  intro t
  filter_upwards [hzeroOne t] with ω hω
  by_cases h : (t : WithTop ℕ) < τ ω
  · simpa [filledBernoulli, stoppedBernoulli, h] using hω
  · simp [filledBernoulli, stoppedBernoulli, h]

private theorem filledBernoulli_condExp
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hτ : IsStoppingTime ℱ τ) (t : ℕ) :
    μ[filledBernoulli I τ t | ℱ t] =ᵐ[μ]
      fun ω => if (t : WithTop ℕ) < τ ω then (μ[I t | ℱ t]) ω else 1 := by
  classical
  let s : Set Ω := {ω | (t : WithTop ℕ) < τ ω}
  have hs : MeasurableSet[ℱ t] s := hτ.measurableSet_gt t
  have hi := bernoulli_integrable hI hzeroOne t
  have hleft : Integrable (s.indicator (I t)) μ :=
    hi.indicator ((ℱ.le t) _ hs)
  have hright : Integrable (sᶜ.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator ((ℱ.le t) _ hs.compl)
  change μ[s.indicator (I t) + sᶜ.indicator (fun _ => (1 : ℝ)) | ℱ t]
    =ᵐ[μ] _
  filter_upwards
    [condExp_add hleft hright (ℱ t), condExp_indicator hi hs,
      condExp_indicator (integrable_const (1 : ℝ)) hs.compl] with ω ha hl hr
  simp only [Pi.add_apply] at ha
  rw [ha, hl, hr, condExp_const (ℱ.le t) (1 : ℝ)]
  by_cases h : (t : WithTop ℕ) < τ ω <;> simp [s, h]

private theorem filledBernoulli_condExp_ge
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ} {p : ℕ → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hτ : IsStoppingTime ℱ τ) (hp : ∀ t, p t ≤ 1)
    (hcond : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < τ ω →
      p t ≤ (μ[I t | ℱ t]) ω) :
    ∀ t, (fun _ => p t) ≤ᵐ[μ] μ[filledBernoulli I τ t | ℱ t] := by
  intro t
  filter_upwards [filledBernoulli_condExp hI hzeroOne hτ t, hcond t] with ω he hc
  rw [he]
  by_cases h : (t : WithTop ℕ) < τ ω
  · simpa [h] using hc h
  · simpa [h] using hp t

/-- Before the target time the filled count is exactly the original count. -/
theorem filledBernoulli_count_eq_of_not_hit
    (I : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) (N : ℕ) (ω : Ω)
    (hN : (N : WithTop ℕ) < τ ω) :
    bernoulliCount (filledBernoulli I τ) N ω = bernoulliCount I N ω := by
  classical
  unfold bernoulliCount
  apply Finset.sum_congr rfl
  intro t ht
  have htN : (t : WithTop ℕ) ≤ (N : WithTop ℕ) := by
    exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp ht))
  have htτ : (t : WithTop ℕ) < τ ω := lt_of_le_of_lt htN hN
  simp [filledBernoulli, stoppedBernoulli, htτ]

/-- The adapted hitting-time form of (15). The caller supplies only the
deterministic implication that failing to hit entails fewer than k
successes. After hitting, indicators are filled by one inside this proof. -/
theorem adapted_success_hitting_tail
    {I : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ} {p : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hτ : IsStoppingTime ℱ τ) (hp : p ≤ 1)
    (hcond : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < τ ω →
      p ≤ (μ[I t | ℱ t]) ω)
    (N : ℕ) (k : ℝ)
    (hfail : ∀ ω, (N : WithTop ℕ) < τ ω → bernoulliCount I N ω < k) :
    μ.real {ω | (N : WithTop ℕ) < τ ω}
      ≤ Real.exp (k * Real.log 2 - (N : ℝ) * p / 2) := by
  have hsubset :
      {ω | (N : WithTop ℕ) < τ ω} ⊆
        {ω | bernoulliCount (filledBernoulli I τ) N ω < k} := by
    intro ω hω
    change bernoulliCount (filledBernoulli I τ) N ω < k
    rw [filledBernoulli_count_eq_of_not_hit I τ N ω hω]
    exact hfail ω hω
  have htail := adapted_bernoulli_lower_tail
    (filledBernoulli_adapted hI hτ)
    (filledBernoulli_zero_one hzeroOne)
    (filledBernoulli_condExp_ge hI hzeroOne hτ (fun _ => hp) hcond) N k
  exact (measureReal_mono hsubset).trans (by simpa using htail)

/-! ## Maximal supermartingale tail by Doob compensation -/

/-- The conditional variance of a variable bounded by b is at most b squared. -/
private theorem conditional_centered_square_le
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {D : Ω → ℝ} (hD : StronglyMeasurable[m0] D)
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂μ, |D ω| ≤ b) :
    μ[fun ω => (D ω - μ[D | m] ω) ^ 2 | m]
      ≤ᵐ[μ] fun _ => b ^ 2 := by
  have hLp : MemLp D 2 μ :=
    MemLp.of_bound hD.aestronglyMeasurable b
      (by simpa only [Real.norm_eq_abs] using hbound)
  have hsq : D ^ 2 ≤ᵐ[μ] fun _ => b ^ 2 := by
    filter_upwards [hbound] with ω hω
    change D ω ^ 2 ≤ b ^ 2
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hb] using hω)
  have hce :=
    condExp_mono (m := m) hLp.integrable_sq (integrable_const (b ^ 2)) hsq
  rw [condExp_const hm (b ^ 2)] at hce
  change ProbabilityTheory.condVar m D μ ≤ᵐ[μ] fun _ => b ^ 2
  exact (ProbabilityTheory.condVar_ae_le_condExp_sq hm hLp).trans hce

/-- Martingale tail bound. The martingale is the Doob martingale part,
translated to start at zero; its increment bound is 2*b, while its
conditional variance bound is b squared. -/
theorem supermartingale_max_tail_of_bounded_increments
    {Y : ℕ → Ω → ℝ} (hY : Supermartingale Y ℱ μ)
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, |Y (n + 1) ω - Y n ω| ≤ b)
    {u : ℝ} (hu : 0 < u) (N : ℕ) :
    Ripple.Probability.prob μ
      {ω | ∃ n, n ≤ N ∧ u ≤ Y n ω - Y 0 ω}
      ≤ Real.exp (-(u ^ 2) / (2 * ((N : ℝ) * b ^ 2 + 2 * b * u / 3))) := by
  let M : ℕ → Ω → ℝ :=
    fun n ω => martingalePart Y ℱ μ n ω - Y 0 ω
  let W : ℕ → Ω → ℝ := fun n _ => (n : ℝ) * b ^ 2
  have hM : Martingale M ℱ μ :=
    (martingale_martingalePart hY.stronglyAdapted hY.integrable).sub
      (martingale_const_fun ℱ μ (hY.stronglyMeasurable 0) (hY.integrable 0))
  have hMincr (n : ℕ) :
      (fun ω => M (n + 1) ω - M n ω) =
        fun ω => Y (n + 1) ω - Y n ω -
          μ[Y (n + 1) - Y n | ℱ n] ω := by
    funext ω
    dsimp only [M, martingalePart, Pi.sub_apply]
    rw [predictablePart_add_one]
    simp only [Pi.add_apply]
    ring
  have hMPbound :
      ∀ᵐ ω ∂μ, ∀ n,
        |martingalePart Y ℱ μ (n + 1) ω - martingalePart Y ℱ μ n ω|
          ≤ 2 * b := by
    simpa using
      (martingalePart_bdd_difference (R := (⟨b, hb⟩ : ℝ≥0)) ℱ
        (ae_all_iff.2 hbound))
  have hMbound (n : ℕ) :
      ∀ᵐ ω ∂μ, |M (n + 1) ω - M n ω| ≤ 2 * b := by
    filter_upwards [hMPbound] with ω hω
    calc
      |M (n + 1) ω - M n ω|
          = |martingalePart Y ℱ μ (n + 1) ω -
              martingalePart Y ℱ μ n ω| := by
                dsimp only [M]
                congr 1
                ring
      _ ≤ 2 * b := hω n
  have hvariance (n : ℕ) :
      μ[fun ω => (M (n + 1) ω - M n ω) ^ 2 | ℱ n]
        ≤ᵐ[μ] fun _ => b ^ 2 := by
    let D : Ω → ℝ := Y (n + 1) - Y n
    have hD : StronglyMeasurable D :=
      ((hY.stronglyMeasurable (n + 1)).mono (ℱ.le (n + 1))).sub
        ((hY.stronglyMeasurable n).mono (ℱ.le n))
    have heq :
        (fun ω => (M (n + 1) ω - M n ω) ^ 2) =
          fun ω => (D ω - μ[D | ℱ n] ω) ^ 2 := by
      funext ω
      rw [congr_fun (hMincr n) ω]
      rfl
    rw [heq]
    exact conditional_centered_square_le (ℱ.le n) hD hb (hbound n)
  have hyp : Ripple.Probability.DiscreteFreedmanHypothesis μ ℱ M W (2 * b) := by
    refine
      { martingale := hM
        init_zero := ?_
        increment_bound := hMbound
        c_nonneg := by positivity
        W_adapted := fun _ => stronglyMeasurable_const
        W_nonneg := ?_
        W_mono := ?_
        dW_predictable := fun n => by simp only [W]; exact stronglyMeasurable_const
        condvar_le_dW := ?_ }
    · exact ae_of_all μ fun ω => by simp [M]
    · intro n
      exact ae_of_all μ fun ω => by dsimp [W]; positivity
    · intro n
      exact ae_of_all μ fun ω => by
        dsimp [W]
        push_cast
        nlinarith [sq_nonneg b]
    · intro n
      have hW :
          (fun ω => W (n + 1) ω - W n ω) = fun _ => b ^ 2 := by
        funext ω
        dsimp [W]
        push_cast
        ring
      rw [hW]
      exact hvariance n
  have hdrift (n : ℕ) :
      μ[Y (n + 1) - Y n | ℱ n] ≤ᵐ[μ] (0 : Ω → ℝ) := by
    have hcur : μ[Y n | ℱ n] = Y n :=
      condExp_of_stronglyMeasurable (ℱ.le n)
        (hY.stronglyMeasurable n) (hY.integrable n)
    filter_upwards
      [condExp_sub (hY.integrable (n + 1)) (hY.integrable n) (ℱ n),
        hY.condExp_ae_le (Nat.le_succ n)] with ω hsub hnext
    have hsub' :
        μ[Y (n + 1) - Y n | ℱ n] ω =
          μ[Y (n + 1) | ℱ n] ω - Y n ω := by
      simpa only [Pi.sub_apply, hcur] using hsub
    change μ[Y (n + 1) - Y n | ℱ n] ω ≤ 0
    rw [hsub']
    linarith
  have hpred : ∀ᵐ ω ∂μ, ∀ n, predictablePart Y ℱ μ n ω ≤ 0 := by
    filter_upwards [ae_all_iff.2 hdrift] with ω hω n
    simp only [predictablePart, Finset.sum_apply]
    exact Finset.sum_nonpos fun i _ => hω i
  have hdom : ∀ᵐ ω ∂μ, ∀ n, Y n ω - Y 0 ω ≤ M n ω := by
    filter_upwards [hpred] with ω hω n
    dsimp only [M, martingalePart, Pi.sub_apply]
    linarith [hω n]
  have hsub :
      {ω | ∃ n, n ≤ N ∧ u ≤ Y n ω - Y 0 ω} ≤ᵐ[μ]
        {ω | (∃ n, n ≤ N ∧ u ≤ M n ω) ∧ W N ω ≤ (N : ℝ) * b ^ 2} := by
    filter_upwards [hdom] with ω hω hhit
    rcases hhit with ⟨n, hn, huY⟩
    exact ⟨⟨n, hn, huY.trans (hω n)⟩, le_rfl⟩
  have hprob :
      Ripple.Probability.prob μ {ω | ∃ n, n ≤ N ∧ u ≤ Y n ω - Y 0 ω}
        ≤ Ripple.Probability.prob μ
          {ω | (∃ n, n ≤ N ∧ u ≤ M n ω) ∧ W N ω ≤ (N : ℝ) * b ^ 2} := by
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  exact hprob.trans
    (Ripple.Probability.discrete_freedman hyp hu (by positivity) (N := N))

end Filtered

/-! ## Exact arithmetic for equations (37)--(42) -/

noncomputable def eightBlockQ (k : ℕ) : ℝ :=
  ((k : ℝ) + 2) ^ 2 / 400

/-- Equation (40), reindexed by k = 0,...,7. -/
noncomputable def eightBlockBase : ℝ :=
  (1 / 100 : ℝ) * (10 / 9 : ℝ) ^ 8 +
    (1 / 20 : ℝ) * ∑ k ∈ Finset.range 8,
      eightBlockQ (k + 1) * (10 / 9 : ℝ) ^ (8 - k)

/-- The entire envelope in equation (39), including the rounding terms. -/
noncomputable def eightBlockEnvelope : ℝ :=
  (10 / 9 : ℝ) ^ 8 * (10001 / 1000000 : ℝ) +
    (25001 / 500000 : ℝ) * ∑ k ∈ Finset.range 8,
      (eightBlockQ (k + 1) + (1 / 100000 : ℝ)) *
        (10 / 9 : ℝ) ^ (8 - k)

private theorem eight_block_reciprocal
    {C : ℝ} (hC : 1000000 ≤ C) :
    0 ≤ 1 / C ∧ 1 / C ≤ (1 / 1000000 : ℝ) := by
  have hpos : 0 < C := by linarith
  constructor
  · positivity
  · apply (div_le_div_iff₀ hpos (by norm_num)).2
    nlinarith

theorem eight_block_initial_square
    {C : ℝ} (hC : 1000000 ≤ C) :
    ((1 / 10 : ℝ) + 1 / C) ^ 2 ≤ (10001 / 1000000 : ℝ) := by
  obtain ⟨hi, hi'⟩ := eight_block_reciprocal hC
  calc
    ((1 / 10 : ℝ) + 1 / C) ^ 2
        ≤ ((1 / 10 : ℝ) + 1 / 1000000) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith [hi']) _
    _ ≤ (10001 / 1000000 : ℝ) := by norm_num

/-- The ceiling threshold version of the initial bound in (37). -/
theorem eight_block_initial_ceiling_square
    {C : ℝ} (hC : 1000000 ≤ C) :
    ((Nat.ceil (C / 10) : ℝ) / C) ^ 2 ≤ (10001 / 1000000 : ℝ) := by
  have hCpos : 0 < C := by linarith
  have hceil : (Nat.ceil (C / 10) : ℝ) ≤ C / 10 + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 ≤ C / 10)).le
  have hratio :
      (Nat.ceil (C / 10) : ℝ) / C ≤ (1 / 10 : ℝ) + 1 / C := by
    calc
      (Nat.ceil (C / 10) : ℝ) / C ≤ (C / 10 + 1) / C :=
        div_le_div_of_nonneg_right hceil hCpos.le
      _ = (1 / 10 : ℝ) + 1 / C := by
        field_simp [hCpos.ne'] <;> ring
  exact (pow_le_pow_left₀ (by positivity) hratio 2).trans
    (eight_block_initial_square hC)

theorem eight_block_rounding_correction
    {C : ℝ} (hC : 1000000 ≤ C) :
    9 / C + 81 / C ^ 2 < (1 / 100000 : ℝ) := by
  obtain ⟨hi, hi'⟩ := eight_block_reciprocal hC
  have hs : (1 / C) ^ 2 ≤ (1 / 1000000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hi hi' _
  have he : 81 / C ^ 2 = 81 * (1 / C) ^ 2 := by
    simp only [div_pow, one_pow]
    ring
  rw [he]
  have hn : 9 / C = 9 * (1 / C) := by ring
  rw [hn]
  nlinarith

/-- The deterministic finite-population and block-length facts in (37).
The last two conjuncts are the horizon comparisons used below (40). -/
theorem eight_block_calibration
    {C : ℝ} (hC : 1000000 ≤ C) :
    ((Nat.ceil (C / 20) : ℝ) / (C - 1) ≤ (25001 / 500000 : ℝ)) ∧
    (1 + 2 / (C - 1)) ^ Nat.ceil (C / 20) ≤ Real.exp (101 / 1000) ∧
    Real.exp (101 / 1000) < (10 / 9 : ℝ) ∧
    (10 / 9 : ℝ) ^ 8 < 3 ∧
    (2 / 5 : ℝ) * C ≤ 8 * (Nat.ceil (C / 20) : ℝ) ∧
    8 * (Nat.ceil (C / 20) : ℝ) ≤ C / 2 := by
  have hpos : 0 < C - 1 := by linarith
  have hceil :
      (Nat.ceil (C / 20) : ℝ) < C / 20 + 1 :=
    Nat.ceil_lt_add_one (by linarith : 0 ≤ C / 20)
  have hceil_lower : C / 20 ≤ (Nat.ceil (C / 20) : ℝ) :=
    Nat.le_ceil _
  have hdiv :
      (Nat.ceil (C / 20) : ℝ) / (C - 1) ≤
        (25001 / 500000 : ℝ) := by
    rw [div_le_iff₀ hpos]
    nlinarith
  have hbase :
      1 + 2 / (C - 1) ≤ Real.exp (2 / (C - 1)) := by
    linarith [Real.add_one_le_exp (2 / (C - 1))]
  have hpow :
      (1 + 2 / (C - 1)) ^ Nat.ceil (C / 20) ≤
        Real.exp ((Nat.ceil (C / 20) : ℝ) * (2 / (C - 1))) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hexponent :
      (Nat.ceil (C / 20) : ℝ) * (2 / (C - 1)) ≤
        (101 / 1000 : ℝ) := by
    calc
      (Nat.ceil (C / 20) : ℝ) * (2 / (C - 1)) =
          2 * ((Nat.ceil (C / 20) : ℝ) / (C - 1)) := by ring
      _ ≤ 2 * (25001 / 500000 : ℝ) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ ≤ (101 / 1000 : ℝ) := by norm_num
  have hexp : Real.exp (101 / 1000) < (10 / 9 : ℝ) := by
    have h := Real.exp_bound' (x := (101 / 1000 : ℝ))
      (by norm_num) (by norm_num) (n := 4) (by norm_num)
    refine lt_of_le_of_lt h ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact ⟨hdiv, hpow.trans (Real.exp_le_exp.mpr hexponent), hexp,
    by norm_num, by linarith, by linarith⟩

/-- Equation (38), with the block numbered k + 1. -/
theorem eight_block_square_envelope
    {C : ℝ} (hC : 1000000 ≤ C)
    (k : ℕ) (hk : k < 8) (x : ℝ) (hx : 0 ≤ x)
    (hupper : x ≤ ((k : ℝ) + 3) / 20 + 9 / C) :
    x ^ 2 ≤ eightBlockQ (k + 1) + (1 / 100000 : ℝ) := by
  have hCpos : 0 < C := by linarith
  have hkreal : (k : ℝ) ≤ 7 := by
    exact_mod_cast (show k ≤ 7 by omega)
  have hv : 0 ≤ 9 / C := by positivity
  have hcross :
      2 * (((k : ℝ) + 3) / 20) * (9 / C) ≤ 9 / C := by
    have hcoef : 2 * (((k : ℝ) + 3) / 20) ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_right hcoef hv
  have hsq : (9 / C) ^ 2 = 81 / C ^ 2 := by
    norm_num [div_pow]
  have hq : (((k : ℝ) + 3) / 20) ^ 2 = eightBlockQ (k + 1) := by
    simp only [eightBlockQ, Nat.cast_add, Nat.cast_one]
    ring
  have hcorr := eight_block_rounding_correction hC
  calc
    x ^ 2 ≤ (((k : ℝ) + 3) / 20 + 9 / C) ^ 2 :=
      pow_le_pow_left₀ hx hupper _
    _ ≤ (((k : ℝ) + 3) / 20) ^ 2 + (9 / C + 81 / C ^ 2) := by
      nlinarith
    _ ≤ (((k : ℝ) + 3) / 20) ^ 2 + (1 / 100000 : ℝ) := by
      linarith
    _ = eightBlockQ (k + 1) + (1 / 100000 : ℝ) := by rw [hq]

/-- Equations (39)--(40): exact base and full envelope, with exact margins. -/
theorem eight_block_envelope_exact :
    eightBlockBase = (310710671 / 3443737680 : ℝ) ∧
    eightBlockBase < (91 / 1000 : ℝ) ∧
    eightBlockEnvelope = (2157990844789531 / 23914845000000000 : ℝ) ∧
    (23 / 250 : ℝ) - eightBlockEnvelope =
      (42174895210469 / 23914845000000000 : ℝ) ∧
    eightBlockEnvelope < (23 / 250 : ℝ) := by
  norm_num [eightBlockBase, eightBlockEnvelope, eightBlockQ,
    Finset.sum_range_succ]

/-- Rational identities in the document's degree-six/Taylor-tail certificate. -/
theorem lemma67_taylor_data :
    (∑ j ∈ Finset.range 7, (9 / 10 : ℝ) ^ j / (j.factorial : ℝ)) =
        (196759709 / 80000000 : ℝ) ∧
    ((9 / 10 : ℝ) ^ 7 / (Nat.factorial 7 : ℝ)) / (1 - 9 / 80) =
        (531441 / 4970000000 : ℝ) ∧
    (196759709 / 80000000 : ℝ) + 531441 / 4970000000 =
        (97793826901 / 39760000000 : ℝ) ∧
    (123 / 50 : ℝ) - 97793826901 / 39760000000 =
        (15773099 / 39760000000 : ℝ) := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The exact rational upper certificate appearing in (42).
Mathlib's degree-eight Taylor bound is stronger than this certificate. -/
theorem exp_nine_tenths_le_certificate :
    Real.exp (9 / 10) ≤ (97793826901 / 39760000000 : ℝ) := by
  have h := Real.exp_bound' (x := (9 / 10 : ℝ))
    (by norm_num) (by norm_num) (n := 9) (by norm_num)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_nine_tenths_lt :
    Real.exp (9 / 10) < (123 / 50 : ℝ) :=
  lt_of_le_of_lt exp_nine_tenths_le_certificate (by norm_num)

private noncomputable def lemma67Primitive (s : ℝ) : ℝ :=
  -Real.exp (-2 * s) *
    ((s + 1 / 10) ^ 2 / 2 + (s + 1 / 10) / 2 + 1 / 4)

private theorem lemma67_primitive_deriv (s : ℝ) :
    HasDerivAt lemma67Primitive
      (((1 / 10 : ℝ) + s) ^ 2 * Real.exp (-2 * s)) s := by
  have hlin : HasDerivAt (fun y : ℝ => -2 * y) (-2) s := by
    simpa using (hasDerivAt_id s).const_mul (-2 : ℝ)
  have hshift : HasDerivAt (fun y : ℝ => y + 1 / 10) 1 s :=
    (hasDerivAt_id s).add_const _
  have hp : HasDerivAt
      (fun y : ℝ => (y + 1 / 10) ^ 2 / 2 + (y + 1 / 10) / 2 + 1 / 4)
      (s + 1 / 10 + 1 / 2) s := by
    convert (((hshift.pow 2).div_const 2).add (hshift.div_const 2)).add_const
      (1 / 4 : ℝ) using 1 <;> ring
  convert (hlin.exp.neg).mul hp using 1 <;>
    (try simp only [lemma67Primitive, Pi.neg_apply]) <;> ring

/-- Equation (41), as an actual interval-integral equality. -/
theorem lemma67_integral_exact :
    Real.exp (9 / 10) *
        ((1 / 100 : ℝ) +
          ∫ s in (0 : ℝ)..(9 / 20 : ℝ),
            ((1 / 10 : ℝ) + s) ^ 2 * Real.exp (-2 * s)) =
      (63 / 200 : ℝ) * Real.exp (9 / 10) - 541 / 800 := by
  have hint : IntervalIntegrable
      (fun s : ℝ => ((1 / 10 : ℝ) + s) ^ 2 * Real.exp (-2 * s))
      MeasureTheory.volume 0 (9 / 20) :=
    (by fun_prop : Continuous
      (fun s : ℝ => ((1 / 10 : ℝ) + s) ^ 2 * Real.exp (-2 * s))).intervalIntegrable _ _
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := lemma67Primitive)
    (f' := fun s : ℝ => ((1 / 10 : ℝ) + s) ^ 2 * Real.exp (-2 * s))
    (a := 0) (b := (9 / 20 : ℝ))
    (fun s _ => lemma67_primitive_deriv s) hint
  have hcancel :
      Real.exp (9 / 10 : ℝ) * Real.exp (-(9 / 10 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hcalc]
  norm_num only [lemma67Primitive, Real.exp_zero] at hcancel ⊢
  nlinarith

/-- The stronger strict bound stated in equation (42). -/
theorem lemma67_integral_lt_margin :
    Real.exp (9 / 10) *
        ((1 / 100 : ℝ) +
          ∫ s in (0 : ℝ)..(9 / 20 : ℝ),
            ((1 / 10 : ℝ) + s) ^ 2 * Real.exp (-2 * s)) <
      (1973 / 20000 : ℝ) := by
  rw [lemma67_integral_exact]
  nlinarith [exp_nine_tenths_lt]

theorem lemma67_integral_lt_tenth :
    Real.exp (9 / 10) *
        ((1 / 100 : ℝ) +
          ∫ s in (0 : ℝ)..(9 / 20 : ℝ),
            ((1 / 10 : ℝ) + s) ^ 2 * Real.exp (-2 * s)) < (1 / 10 : ℝ) :=
  lt_trans lemma67_integral_lt_margin (by norm_num)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeScalar
