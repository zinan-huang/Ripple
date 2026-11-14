/-
Scalar tails for nodes N07, N08 (scalar part), and N09.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.TimeTheorem
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Rev

open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.ScalarTails

open PhaseThreeScalar

open TimeTheorem (timePopulationThreshold logWindow time_population_bounds)

theorem time_population_scalar_bounds {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    0 < (n : ℝ) ∧ 100 ≤ Real.log (n : ℝ) := by
  have hbase : PhaseThreeModel.Numeric.populationThreshold ≤ n :=
    (time_population_bounds hn).1
  have hdensity : (6 / 25 : ℝ) * n ≤ (n : ℝ) := by
    nlinarith only [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  obtain ⟨hnpos, hlog, _⟩ :=
    PhaseThreeModel.Numeric.logarithmic_inputs (C := n) hbase hdensity le_rfl
  exact ⟨hnpos, (by norm_num : (100 : ℝ) ≤ 536870912).trans hlog⟩

section Bernoulli

variable {Ω : Type*} {m : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m}

/-- Exact conditional probabilities permit either sign of the parameter. -/
theorem adapted_bernoulli_exp_moment_constant
    {I : ℕ → Ω → ℝ} {p : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hprob : ∀ t, μ[I t | ℱ t] =ᵐ[μ] (fun _ => p))
    (θ : ℝ) (N : ℕ) :
    (∫ ω, Real.exp (θ * bernoulliCount I N ω) ∂μ) ≤
      Real.exp ((Real.exp θ - 1) * (N : ℝ) * p) := by
  let Z : ℕ → Ω → ℝ :=
    fun k ω => Real.exp (θ * bernoulliCount I k ω)
  have hZint : ∀ k, Integrable (Z k) μ :=
    fun k => bernoulli_exp_integrable hI hzeroOne θ k
  have hZsm : ∀ k, StronglyMeasurable[ℱ k] (Z k) := by
    intro k
    have hS := bernoulliCount_stronglyMeasurable hI k
    dsimp [Z]
    fun_prop
  change (∫ ω, Z N ω ∂μ) ≤ _
  induction N with
  | zero => simp [Z, bernoulliCount]
  | succ N ih =>
      let G : Ω → ℝ := fun ω => Real.exp (θ * I N ω)
      have hid : G =ᵐ[μ]
          fun ω => 1 + (Real.exp θ - 1) * I N ω := by
        filter_upwards [hzeroOne N] with ω hω
        rcases hω with hω | hω <;> simp [G, hω] <;> ring
      have hGint : Integrable G μ :=
        ((integrable_const (1 : ℝ)).add
          ((bernoulli_integrable hI hzeroOne N).const_mul
            (Real.exp θ - 1))).congr hid.symm
      have hadd := condExp_add
        (integrable_const (1 : ℝ))
        ((bernoulli_integrable hI hzeroOne N).const_mul
          (Real.exp θ - 1)) (ℱ N)
      have hmul :
          μ[fun ω => (Real.exp θ - 1) * I N ω | ℱ N] =ᵐ[μ]
            fun ω => (Real.exp θ - 1) * μ[I N | ℱ N] ω := by
        simpa only [Pi.smul_apply, smul_eq_mul] using
          condExp_smul (μ := μ) (Real.exp θ - 1) (I N) (ℱ N)
      have hGce :
          μ[G | ℱ N] =ᵐ[μ]
            fun _ => 1 + (Real.exp θ - 1) * p := by
        filter_upwards [condExp_congr_ae hid, hadd, hmul, hprob N] with
          ω hcongω haddω hmulω hpω
        calc
          μ[G | ℱ N] ω =
              μ[fun ω => 1 + (Real.exp θ - 1) * I N ω | ℱ N] ω :=
            hcongω
          _ = μ[fun _ : Ω => (1 : ℝ) | ℱ N] ω +
              μ[fun ω => (Real.exp θ - 1) * I N ω | ℱ N] ω :=
            haddω
          _ = 1 + (Real.exp θ - 1) * p := by
            rw [condExp_const (ℱ.le N) (1 : ℝ), hmulω, hpω]
      have hstep : Z (N + 1) = Z N * G := by
        funext ω
        simp only [Z, G, Pi.mul_apply, bernoulliCount,
          Finset.sum_range_succ, mul_add, Real.exp_add]
      have hstepae : Z (N + 1) =ᵐ[μ] Z N * G :=
        Filter.Eventually.of_forall (congrFun hstep)
      have hpull :
          μ[Z N * G | ℱ N] =ᵐ[μ] Z N * μ[G | ℱ N] :=
        condExp_mul_of_stronglyMeasurable_left (hZsm N)
          ((hZint (N + 1)).congr hstepae) hGint
      have hce := (condExp_congr_ae hstepae).trans hpull
      have hbound :
          μ[Z (N + 1) | ℱ N] ≤ᵐ[μ]
            fun ω => Real.exp ((Real.exp θ - 1) * p) * Z N ω := by
        filter_upwards [hce, hGce] with ω hceω hGceω
        rw [hceω]
        change Z N ω * μ[G | ℱ N] ω ≤ _
        rw [hGceω]
        calc
          Z N ω * (1 + (Real.exp θ - 1) * p) ≤
              Z N ω * Real.exp ((Real.exp θ - 1) * p) :=
            mul_le_mul_of_nonneg_left
              (by simpa only [add_comm] using
                Real.add_one_le_exp ((Real.exp θ - 1) * p))
              (Real.exp_nonneg _)
          _ = _ := mul_comm _ _
      calc
        (∫ ω, Z (N + 1) ω ∂μ) =
            ∫ ω, μ[Z (N + 1) | ℱ N] ω ∂μ :=
          (integral_condExp (ℱ.le N)).symm
        _ ≤ ∫ ω, Real.exp ((Real.exp θ - 1) * p) * Z N ω ∂μ :=
          integral_mono_ae integrable_condExp
            ((hZint N).const_mul _) hbound
        _ = Real.exp ((Real.exp θ - 1) * p) *
            ∫ ω, Z N ω ∂μ := by rw [integral_const_mul]
        _ ≤ Real.exp ((Real.exp θ - 1) * p) *
            Real.exp ((Real.exp θ - 1) * (N : ℝ) * p) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp ((Real.exp θ - 1) * ((N + 1 : ℕ) : ℝ) * p) := by
          rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]
          congr 1
          ring

private theorem bernoulli_chernoff_event
    {I : ℕ → Ω → ℝ} {p θ r : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hprob : ∀ t, μ[I t | ℱ t] =ᵐ[μ] (fun _ => p))
    (N : ℕ) (A : Set Ω)
    (hA : A ⊆ {ω | θ * r ≤ θ * bernoulliCount I N ω}) :
    μ.real A ≤
      Real.exp ((Real.exp θ - 1) * (N : ℝ) * p - θ * r) := by
  have hsub : A ⊆
      {ω | Real.exp (θ * r) ≤ Real.exp (θ * bernoulliCount I N ω)} :=
    fun ω hω => Real.exp_le_exp.mpr (hA hω)
  have hmeasure := measureReal_mono (μ := μ) hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω =>
      Real.exp_nonneg (θ * bernoulliCount I N ω)))
    (bernoulli_exp_integrable hI hzeroOne θ N) (Real.exp (θ * r))
  have hmul :
      Real.exp (θ * r) * μ.real A ≤
        Real.exp ((Real.exp θ - 1) * (N : ℝ) * p) :=
    (mul_le_mul_of_nonneg_left hmeasure (Real.exp_nonneg _)).trans
      (hmarkov.trans
        (adapted_bernoulli_exp_moment_constant hI hzeroOne hprob θ N))
  calc
    μ.real A ≤
        Real.exp ((Real.exp θ - 1) * (N : ℝ) * p) /
          Real.exp (θ * r) := by
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa only [mul_comm] using hmul
    _ = _ := (Real.exp_sub _ _).symm

theorem bernoulli_chernoff_upper_scalar
    {I : ℕ → Ω → ℝ} {p θ r : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hprob : ∀ t, μ[I t | ℱ t] =ᵐ[μ] (fun _ => p))
    (hθ : 0 ≤ θ) (N : ℕ) :
    μ.real {ω | r ≤ bernoulliCount I N ω} ≤
      Real.exp ((Real.exp θ - 1) * (N : ℝ) * p - θ * r) :=
  bernoulli_chernoff_event hI hzeroOne hprob N _
    (fun _ hω => mul_le_mul_of_nonneg_left hω hθ)

theorem bernoulli_chernoff_lower_scalar
    {I : ℕ → Ω → ℝ} {p θ r : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hprob : ∀ t, μ[I t | ℱ t] =ᵐ[μ] (fun _ => p))
    (hθ : θ ≤ 0) (N : ℕ) :
    μ.real {ω | bernoulliCount I N ω ≤ r} ≤
      Real.exp ((Real.exp θ - 1) * (N : ℝ) * p - θ * r) :=
  bernoulli_chernoff_event hI hzeroOne hprob N _
    (fun _ hω => mul_le_mul_of_nonpos_left hω hθ)

end Bernoulli


/-! ## Adapted count death: N07 -/

section Death

variable {Ω : Type*} {m : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m}

/-- A real transform of a natural variable with a finite a.e. range is
integrable, regardless of its values outside that range. -/
private theorem death_nat_transform_integrable
    {X : Ω → ℕ} {M : ℕ}
    (hX : Measurable X)
    (hM : ∀ᵐ ω ∂μ, X ω ≤ M)
    (f : ℕ → ℝ) :
    Integrable (fun ω => f (X ω)) μ := by
  refine Integrable.of_bound
    (((measurable_of_countable f).comp hX).stronglyMeasurable.aestronglyMeasurable)
    (∑ j ∈ Finset.range (M + 1), ‖f j‖) ?_
  filter_upwards [hM] with ω hω
  exact Finset.single_le_sum
    (fun j _ => norm_nonneg (f j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hω))

private theorem death_pow_tangent
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    x ^ (k + 1) + ((k : ℝ) + 1) * x ^ k * (y - x) ≤
      y ^ (k + 1) := by
  induction k with
  | zero =>
      simp only [Nat.cast_zero, zero_add, pow_zero, pow_one, one_mul]
      linarith
  | succ k ih =>
      have hmul := mul_le_mul_of_nonneg_right ih hy
      have herr :
          0 ≤ ((k : ℝ) + 1) * x ^ k * (y - x) ^ 2 := by
        positivity
      simp only [Nat.cast_succ, pow_succ] at hmul ⊢
      nlinarith only [hmul, herr]

private theorem death_power_step
    {j k : ℕ} (hkj : k ≤ j) (b : ℝ) (hb : 0 ≤ b) :
    (1 + b) ^ k ≤
      (1 + b) ^ j -
        b * (1 + b) ^ (j - 1) *
          (if k < j then (1 : ℝ) else 0) := by
  cases j with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkj
      simp [hk]
  | succ j =>
      change (1 + b) ^ k ≤
        (1 + b) ^ (j + 1) -
          b * (1 + b) ^ j *
            (if k < j + 1 then (1 : ℝ) else 0)
      by_cases hlt : k < j + 1
      · have hk : k ≤ j := by omega
        calc
          (1 + b) ^ k ≤ (1 + b) ^ j :=
            pow_le_pow_right₀ (by linarith) hk
          _ = (1 + b) ^ (j + 1) -
                b * (1 + b) ^ j *
                  (if k < j + 1 then (1 : ℝ) else 0) := by
            rw [if_pos hlt, pow_succ]
            ring
      · have hk : k = j + 1 := by omega
        simp [hk]

private theorem death_power_drift
    (q b : ℝ) (hq : q ≤ 1) (hb : 0 ≤ b) (j : ℕ) :
    (1 + b) ^ j -
        b * (1 + b) ^ (j - 1) * (q * (j : ℝ)) ≤
      (1 + (1 - q) * b) ^ j := by
  cases j with
  | zero => simp
  | succ j =>
      have ht := death_pow_tangent
        (1 + b) (1 + (1 - q) * b)
        (by linarith)
        (by
          have : 0 ≤ (1 - q) * b :=
            mul_nonneg (sub_nonneg.mpr hq) hb
          linarith)
        j
      convert ht using 1 <;>
        simp only [Nat.succ_sub_one, Nat.cast_succ,
          Nat.succ_eq_add_one, pow_succ] <;>
        ring

/-- The one-step generating-function form of the falling-factorial
argument. Expanding (1 + b)^j gives its factorial generating function;
the proof keeps this polynomial intact. -/
private theorem death_pgf_step
    (J : ℕ → Ω → ℕ) (M : ℕ) (q : ℝ)
    (hq : q ≤ 1)
    (hJ : ∀ t, StronglyMeasurable[ℱ t] (J t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, J t ω ≤ M)
    (hmono : ∀ t, ∀ᵐ ω ∂μ, J (t + 1) ω ≤ J t ω)
    (hdeath : ∀ t,
      (fun ω => q * (J t ω : ℝ)) ≤ᵐ[μ]
        μ[fun ω =>
          if J (t + 1) ω < J t ω
          then (1 : ℝ) else 0 | ℱ t])
    (b : ℝ) (hb : 0 ≤ b) (t : ℕ) :
    (∫ ω, (1 + b) ^ J (t + 1) ω ∂μ) ≤
      ∫ ω, (1 + (1 - q) * b) ^ J t ω ∂μ := by
  let V : ℕ → Ω → ℝ :=
    fun s ω => (1 + b) ^ J s ω
  let D : Ω → ℝ :=
    fun ω => b * (1 + b) ^ (J t ω - 1)
  let B : Ω → ℝ :=
    fun ω => if J (t + 1) ω < J t ω then 1 else 0
  have hVsm (s : ℕ) : StronglyMeasurable[ℱ s] (V s) :=
    ((measurable_of_countable
      (fun j : ℕ => (1 + b) ^ j)).comp (hJ s).measurable).stronglyMeasurable
  have hVint (s : ℕ) : Integrable (V s) μ :=
    death_nat_transform_integrable
      ((hJ s).mono (ℱ.le s)).measurable
      (hbound s) (fun j => (1 + b) ^ j)
  have hDsm : StronglyMeasurable[ℱ t] D :=
    ((measurable_of_countable
      (fun j : ℕ => b * (1 + b) ^ (j - 1))).comp
        (hJ t).measurable).stronglyMeasurable
  have hDint : Integrable D μ :=
    death_nat_transform_integrable
      ((hJ t).mono (ℱ.le t)).measurable
      (hbound t) (fun j => b * (1 + b) ^ (j - 1))
  have hBsm : StronglyMeasurable[ℱ (t + 1)] B :=
    ((measurable_of_countable
      (fun p : ℕ × ℕ =>
        if p.1 < p.2 then (1 : ℝ) else 0)).comp
          ((hJ (t + 1)).measurable.prodMk
            ((hJ t).mono (ℱ.mono (Nat.le_succ t))).measurable)).stronglyMeasurable
  have hBnorm : ∀ ω, ‖B ω‖ ≤ 1 := by
    intro ω
    dsimp [B]
    split_ifs <;> norm_num
  have hBint : Integrable B μ :=
    Integrable.of_bound
      (hBsm.mono (ℱ.le (t + 1))).aestronglyMeasurable 1
      (Filter.Eventually.of_forall hBnorm)
  have hDBint : Integrable (D * B) μ :=
    hDint.mul_bdd
      (hBsm.mono (ℱ.le (t + 1))).aestronglyMeasurable
      (Filter.Eventually.of_forall hBnorm)
  have hpoint : V (t + 1) ≤ᵐ[μ] V t - D * B := by
    filter_upwards [hmono t] with ω hω
    exact death_power_step hω b hb
  have hCE :
      μ[V (t + 1) | ℱ t] ≤ᵐ[μ]
        μ[V t - D * B | ℱ t] :=
    condExp_mono (hVint (t + 1)) ((hVint t).sub hDBint) hpoint
  have hlinear :
      μ[V t - D * B | ℱ t] =ᵐ[μ]
        V t - D * μ[B | ℱ t] := by
    have hsubCE := condExp_sub (hVint t) hDBint (ℱ t)
    have hpull :=
      condExp_mul_of_stronglyMeasurable_left hDsm hDBint hBint
    have hfixed :=
      condExp_of_stronglyMeasurable (ℱ.le t) (hVsm t) (hVint t)
    filter_upwards [hsubCE, hpull] with ω hs hp
    simp only [Pi.sub_apply, Pi.mul_apply] at hs hp ⊢
    rw [hs, hfixed, hp]
  have hcond :
      μ[V (t + 1) | ℱ t] ≤ᵐ[μ]
        (fun ω => (1 + (1 - q) * b) ^ J t ω) := by
    filter_upwards [hCE, hlinear, hdeath t] with ω hc hl hd
    rw [hl] at hc
    have hDn : 0 ≤ D ω := by
      dsimp [D]
      positivity
    have hdrop :
        D ω * (q * (J t ω : ℝ)) ≤
          D ω * (μ[B | ℱ t]) ω :=
      mul_le_mul_of_nonneg_left hd hDn
    calc
      (μ[V (t + 1) | ℱ t]) ω ≤
          V t ω - D ω * (μ[B | ℱ t]) ω := hc
      _ ≤ V t ω - D ω * (q * (J t ω : ℝ)) :=
        sub_le_sub_left hdrop _
      _ ≤ (1 + (1 - q) * b) ^ J t ω :=
        death_power_drift q b hq hb (J t ω)
  have hWint :
      Integrable
        (fun ω => (1 + (1 - q) * b) ^ J t ω) μ :=
    death_nat_transform_integrable
      ((hJ t).mono (ℱ.le t)).measurable
      (hbound t) (fun j => (1 + (1 - q) * b) ^ j)
  calc
    (∫ ω, (1 + b) ^ J (t + 1) ω ∂μ) =
        ∫ ω, (μ[V (t + 1) | ℱ t]) ω ∂μ :=
      (integral_condExp (ℱ.le t)).symm
    _ ≤ ∫ ω, (1 + (1 - q) * b) ^ J t ω ∂μ :=
      integral_mono_ae integrable_condExp hWint hcond

private theorem death_pgf
    (J : ℕ → Ω → ℕ) (M : ℕ) (q : ℝ)
    (hq : q ≤ 1)
    (hJ : ∀ t, StronglyMeasurable[ℱ t] (J t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, J t ω ≤ M)
    (hmono : ∀ t, ∀ᵐ ω ∂μ, J (t + 1) ω ≤ J t ω)
    (hdeath : ∀ t,
      (fun ω => q * (J t ω : ℝ)) ≤ᵐ[μ]
        μ[fun ω =>
          if J (t + 1) ω < J t ω
          then (1 : ℝ) else 0 | ℱ t])
    (b : ℝ) (hb : 0 ≤ b) (T : ℕ) :
    (∫ ω, (1 + b) ^ J T ω ∂μ) ≤
      (1 + b * (1 - q) ^ T) ^ M := by
  induction T generalizing b with
  | zero =>
      simp only [pow_zero, mul_one]
      calc
        (∫ ω, (1 + b) ^ J 0 ω ∂μ) ≤
            ∫ _ : Ω, (1 + b) ^ M ∂μ := by
          refine integral_mono_ae
            (death_nat_transform_integrable
              ((hJ 0).mono (ℱ.le 0)).measurable
              (hbound 0) (fun j => (1 + b) ^ j))
            (integrable_const _) ?_
          filter_upwards [hbound 0] with ω hω
          exact pow_le_pow_right₀ (by linarith) hω
        _ = (1 + b) ^ M := by simp
  | succ T ih =>
      have hb' : 0 ≤ (1 - q) * b :=
        mul_nonneg (sub_nonneg.mpr hq) hb
      calc
        (∫ ω, (1 + b) ^ J (T + 1) ω ∂μ) ≤
            ∫ ω, (1 + (1 - q) * b) ^ J T ω ∂μ :=
          death_pgf_step J M q hq hJ hbound hmono hdeath b hb T
        _ ≤ (1 + ((1 - q) * b) * (1 - q) ^ T) ^ M :=
          ih ((1 - q) * b) hb'
        _ = (1 + b * (1 - q) ^ (T + 1)) ^ M := by
          congr 1
          rw [pow_succ]
          ring

/-- N07.
Multi-label deaths and kills to zero are allowed. -/
theorem adapted_death_exponential_tail
    (J : ℕ → Ω → ℕ) (M : ℕ) (q a : ℝ)
    (hq : 0 ≤ q) (hqM : q * M ≤ 1)
    (hJ : ∀ t, StronglyMeasurable[ℱ t] (J t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, J t ω ≤ M)
    (hmono : ∀ t, ∀ᵐ ω ∂μ, J (t + 1) ω ≤ J t ω)
    (hdeath : ∀ t,
      (fun ω => q * (J t ω : ℝ)) ≤ᵐ[μ]
        μ[fun ω =>
          if J (t + 1) ω < J t ω
          then (1 : ℝ) else 0 | ℱ t])
    (T : ℕ) :
    μ.real {ω | a * M ≤ (J T ω : ℝ)} ≤
      Real.exp ((7 * Real.exp (-q * T) - a * Real.log 8) * M) := by
  by_cases hMz : M = 0
  · subst M
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero]
    exact measureReal_le_one
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hMz)
  have hqone : q ≤ 1 := by
    calc
      q = q * 1 := by ring
      _ ≤ q * M := mul_le_mul_of_nonneg_left hMone hq
      _ ≤ 1 := hqM
  have hgeom :
      (1 - q) ^ T ≤ Real.exp (-q * (T : ℝ)) := by
    have hbase : 1 - q ≤ Real.exp (-q) := by
      linarith [Real.add_one_le_exp (-q)]
    calc
      (1 - q) ^ T ≤ (Real.exp (-q)) ^ T :=
        pow_le_pow_left₀ (sub_nonneg.mpr hqone) hbase T
      _ = Real.exp (-q * (T : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hpgf :
      (∫ ω, (8 : ℝ) ^ J T ω ∂μ) ≤
        (1 + 7 * (1 - q) ^ T) ^ M := by
    simpa only [show (1 : ℝ) + 7 = 8 by norm_num] using
      death_pgf J M q hqone hJ hbound hmono hdeath 7 (by norm_num) T
  have hbase :
      1 + 7 * (1 - q) ^ T ≤
        Real.exp (7 * Real.exp (-q * (T : ℝ))) := by
    have hexp := Real.add_one_le_exp
      (7 * Real.exp (-q * (T : ℝ)))
    linarith only [hgeom, hexp]
  have hmoment :
      (∫ ω, (8 : ℝ) ^ J T ω ∂μ) ≤
        Real.exp (7 * Real.exp (-q * (T : ℝ)) * M) := by
    calc
      (∫ ω, (8 : ℝ) ^ J T ω ∂μ) ≤
          (1 + 7 * (1 - q) ^ T) ^ M := hpgf
      _ ≤ (Real.exp (7 * Real.exp (-q * (T : ℝ)))) ^ M := by
        apply pow_le_pow_left₀ _ hbase M
        have : 0 ≤ (1 - q) ^ T :=
          pow_nonneg (sub_nonneg.mpr hqone) T
        positivity
      _ = Real.exp (7 * Real.exp (-q * (T : ℝ)) * M) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hexp_pow (j : ℕ) :
      Real.exp (Real.log 8 * (j : ℝ)) = (8 : ℝ) ^ j := by
    rw [mul_comm, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  have hsub :
      {ω | a * M ≤ (J T ω : ℝ)} ⊆
        {ω |
          Real.exp (Real.log 8 * (a * M)) ≤ (8 : ℝ) ^ J T ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [← hexp_pow (J T ω)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hω
        (Real.log_nonneg (by norm_num)))
  have hprob := measureReal_mono (μ := μ) hsub
  have hpowint : Integrable (fun ω => (8 : ℝ) ^ J T ω) μ :=
    death_nat_transform_integrable
      ((hJ T).mono (ℱ.le T)).measurable
      (hbound T) (fun j => (8 : ℝ) ^ j)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall
      (fun ω => pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) (J T ω)))
    hpowint (Real.exp (Real.log 8 * (a * M)))
  have hmul :
      Real.exp (Real.log 8 * (a * M)) *
          μ.real {ω | a * M ≤ (J T ω : ℝ)} ≤
        Real.exp (7 * Real.exp (-q * (T : ℝ)) * M) :=
    (mul_le_mul_of_nonneg_left hprob (Real.exp_nonneg _)).trans
      (hmarkov.trans hmoment)
  calc
    μ.real {ω | a * M ≤ (J T ω : ℝ)} ≤
        Real.exp (7 * Real.exp (-q * (T : ℝ)) * M) /
          Real.exp (Real.log 8 * (a * M)) := by
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa only [mul_comm] using hmul
    _ = Real.exp
        ((7 * Real.exp (-q * T) - a * Real.log 8) * M) := by
      rw [← Real.exp_sub]
      congr 1
      ring

end Death


/-! ## Timer participation bounds: N09 -/

private theorem timer_log_two_bounds :
    (69 / 100 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (347 / 500 : ℝ) := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 2
  have hhi := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hlo hhi
  constructor <;> linarith

private theorem timer_log_three_halves_bounds :
    0 ≤ Real.log (3 / 2 : ℝ) ∧
      Real.log (3 / 2 : ℝ) ≤ (41 / 100 : ℝ) := by
  have hhi := Real.log_div_le_sum_range_add
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hhi
  constructor
  · exact Real.log_nonneg (by norm_num)
  · linarith

private theorem timer_log_ratio :
    Real.log (3 / 2 : ℝ) ≤ (3 / 5 : ℝ) * Real.log 2 := by
  linarith [timer_log_two_bounds.1, timer_log_three_halves_bounds.2]

private theorem timer_exp_small :
    Real.exp (3 / 10 : ℝ) - 1 ≤ (7 / 20 : ℝ) := by
  have h := Real.exp_bound'
    (x := (3 / 10 : ℝ))
    (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private theorem timer_hour_one_le (n : ℕ) :
    (1 : ℝ) ≤ PhaseThreeModel.Numeric.clockHours n := by
  have hidx :
      (0 : ℝ) ≤ PhaseThreeModel.Numeric.hourIndex n :=
    Nat.cast_nonneg _
  simp only [PhaseThreeModel.Numeric.clockHours,
    Nat.cast_add, Nat.cast_one]
  linarith

private theorem timer_hour_log_bounds {n : ℕ}
    (hlog : 0 ≤ Real.log (n : ℝ)) :
    Real.log (n : ℝ) ≤
        ((PhaseThreeModel.Numeric.clockHours n : ℝ) - 1) *
          Real.log 2 ∧
      (PhaseThreeModel.Numeric.clockHours n : ℝ) * Real.log 2 ≤
        Real.log (n : ℝ) + 2 * Real.log 2 := by
  have hlp : 0 < Real.log 2 := by
    linarith [timer_log_two_bounds.1]
  have hlo :
      Real.log (n : ℝ) / Real.log 2 ≤
        (PhaseThreeModel.Numeric.hourIndex n : ℝ) := by
    rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
    exact Nat.le_ceil _
  have hhi :
      (PhaseThreeModel.Numeric.hourIndex n : ℝ) <
        Real.log (n : ℝ) / Real.log 2 + 1 := by
    rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
    exact Nat.ceil_lt_add_one (div_nonneg hlog hlp.le)
  constructor
  · have h := (div_le_iff₀ hlp).mp hlo
    simpa only [PhaseThreeModel.Numeric.clockHours,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h
  · have h :
        ((PhaseThreeModel.Numeric.hourIndex n : ℝ) - 1) *
            Real.log 2 < Real.log (n : ℝ) :=
      (lt_div_iff₀ hlp).mp (by linarith only [hhi])
    simp only [PhaseThreeModel.Numeric.clockHours,
      Nat.cast_add, Nat.cast_one]
    nlinarith only [h]

/-- Late timer, per-label scalar part.
The full counter requires one additional invocation because its zero test
precedes decrementing. -/
theorem late_timer_lower_scalar
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    {n : ℕ} (hn : timePopulationThreshold ≤ n)
    (I : ℕ → Ω → ℝ)
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hprob : ∀ t, μ[I t | ℱ t] =ᵐ[μ]
      (fun _ => 2 / (n : ℝ))) :
    μ.real {ω |
      ((50 * PhaseThreeModel.Numeric.clockHours n + 1 : ℕ) : ℝ) ≤
        PhaseThreeScalar.bernoulliCount I
          (Nat.ceil ((53 / 2 : ℝ) * n * Real.log (n : ℝ))) ω} ≤
      Real.rpow (n : ℝ) (-(153 / 50 : ℝ)) := by
  obtain ⟨hnpos, hnlog⟩ := time_population_scalar_bounds hn
  clear hn
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    linarith only [hnlog]
  have hnone : (1 : ℝ) ≤ n := by
    have h := Real.add_one_le_exp (Real.log (n : ℝ))
    rw [Real.exp_log hnpos] at h
    linarith only [h, hnlog]
  let N : ℕ := Nat.ceil ((53 / 2 : ℝ) * n * Real.log (n : ℝ))
  have hceil :
      (N : ℝ) ≤ (53 / 2 : ℝ) * n * Real.log (n : ℝ) + 1 := by
    dsimp [N]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hmean :
      (N : ℝ) * (2 / (n : ℝ)) ≤
        53 * Real.log (n : ℝ) + 2 := by
    calc
      (N : ℝ) * (2 / (n : ℝ)) =
          (2 * (N : ℝ)) / (n : ℝ) := by ring
      _ ≤ 53 * Real.log (n : ℝ) + 2 := by
        apply (div_le_iff₀ hnpos).2
        nlinarith only [hceil, hnone]
  have hcoefficient :
      (Real.exp (3 / 10 : ℝ) - 1) * (N : ℝ) *
          (2 / (n : ℝ)) ≤
        (7 / 20 : ℝ) * (53 * Real.log (n : ℝ) + 2) := by
    calc
      (Real.exp (3 / 10 : ℝ) - 1) * (N : ℝ) *
          (2 / (n : ℝ)) =
          (Real.exp (3 / 10 : ℝ) - 1) *
            ((N : ℝ) * (2 / (n : ℝ))) := by ring
      _ ≤ (7 / 20 : ℝ) * ((N : ℝ) * (2 / (n : ℝ))) :=
        mul_le_mul_of_nonneg_right timer_exp_small (by positivity)
      _ ≤ (7 / 20 : ℝ) * (53 * Real.log (n : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hmean (by norm_num)
  have hHone := timer_hour_one_le n
  have hHscaled :
      Real.log (n : ℝ) ≤
        (347 / 500 : ℝ) *
          ((PhaseThreeModel.Numeric.clockHours n : ℝ) - 1) := by
    calc
      Real.log (n : ℝ) ≤
          ((PhaseThreeModel.Numeric.clockHours n : ℝ) - 1) *
            Real.log 2 :=
        (timer_hour_log_bounds hlog).1
      _ ≤ ((PhaseThreeModel.Numeric.clockHours n : ℝ) - 1) *
          (347 / 500 : ℝ) :=
        mul_le_mul_of_nonneg_left timer_log_two_bounds.2
          (sub_nonneg.mpr hHone)
      _ = _ := by ring
  have htail := bernoulli_chernoff_upper_scalar
    (I := I) (p := 2 / (n : ℝ)) (θ := (3 / 10 : ℝ))
    (r := ((50 * PhaseThreeModel.Numeric.clockHours n + 1 : ℕ) : ℝ))
    hI hzeroOne hprob (by norm_num) N
  calc
    μ.real {ω |
        ((50 * PhaseThreeModel.Numeric.clockHours n + 1 : ℕ) : ℝ) ≤
          PhaseThreeScalar.bernoulliCount I N ω} ≤
        Real.exp
          ((Real.exp (3 / 10 : ℝ) - 1) * (N : ℝ) *
              (2 / (n : ℝ)) -
            (3 / 10 : ℝ) *
              ((50 * PhaseThreeModel.Numeric.clockHours n + 1 : ℕ) : ℝ)) :=
      htail
    _ ≤ Real.rpow (n : ℝ) (-(153 / 50 : ℝ)) := by
      change _ ≤ (n : ℝ) ^ (-(153 / 50 : ℝ))
      rw [Real.rpow_def_of_pos hnpos]
      apply Real.exp_le_exp.mpr
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      nlinarith only [hcoefficient, hHscaled, hHone]

/-- Late timer upper bound, scalar part.
The Chernoff parameter is negative log (3/2). -/
theorem late_timer_upper_scalar
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    {n : ℕ} (hn : timePopulationThreshold ≤ n)
    (I : ℕ → Ω → ℝ)
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hprob : ∀ t, μ[I t | ℱ t] =ᵐ[μ]
      (fun _ => 2 / (n : ℝ))) :
    μ.real {ω |
      PhaseThreeScalar.bernoulliCount I (logWindow n 54) ω ≤
        ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)} ≤
      1 / (n : ℝ) ^ 5 := by
  obtain ⟨hnpos, hnlog⟩ := time_population_scalar_bounds hn
  clear hn
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    linarith only [hnlog]
  have hceil :
      54 * (n : ℝ) * Real.log (n : ℝ) ≤
        (logWindow n 54 : ℝ) := by
    unfold logWindow
    exact Nat.le_ceil _
  have hmean :
      108 * Real.log (n : ℝ) ≤
        (logWindow n 54 : ℝ) * (2 / (n : ℝ)) := by
    calc
      108 * Real.log (n : ℝ) ≤
          (2 * (logWindow n 54 : ℝ)) / (n : ℝ) := by
        apply (le_div_iff₀ hnpos).2
        nlinarith only [hceil]
      _ = (logWindow n 54 : ℝ) * (2 / (n : ℝ)) := by ring
  have hscaled :
      (PhaseThreeModel.Numeric.clockHours n : ℝ) *
          Real.log (3 / 2 : ℝ) ≤
        (PhaseThreeModel.Numeric.clockHours n : ℝ) *
          ((3 / 5 : ℝ) * Real.log 2) :=
    mul_le_mul_of_nonneg_left timer_log_ratio (Nat.cast_nonneg _)
  have hhour := (timer_hour_log_bounds hlog).2
  have hclock :
      50 * (PhaseThreeModel.Numeric.clockHours n : ℝ) *
          Real.log (3 / 2 : ℝ) ≤
        30 * Real.log (n : ℝ) + 60 * Real.log 2 := by
    nlinarith only [hscaled, hhour]
  have htheta : -Real.log (3 / 2 : ℝ) ≤ 0 :=
    neg_nonpos.mpr timer_log_three_halves_bounds.1
  have hexp :
      Real.exp (-Real.log (3 / 2 : ℝ)) = (2 / 3 : ℝ) := by
    rw [Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  have htail := bernoulli_chernoff_lower_scalar
    (I := I) (p := 2 / (n : ℝ))
    (θ := -Real.log (3 / 2 : ℝ))
    (r := ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ))
    hI hzeroOne hprob htheta (logWindow n 54)
  calc
    μ.real {ω |
        PhaseThreeScalar.bernoulliCount I (logWindow n 54) ω ≤
          ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)} ≤
        Real.exp
          ((Real.exp (-Real.log (3 / 2 : ℝ)) - 1) *
              (logWindow n 54 : ℝ) * (2 / (n : ℝ)) -
            (-Real.log (3 / 2 : ℝ)) *
              ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)) :=
      htail
    _ ≤ Real.exp (-((5 : ℝ) * Real.log (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [hexp]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      nlinarith only [hmean, hclock, timer_log_two_bounds.2, hnlog]
    _ = 1 / (n : ℝ) ^ 5 := by
      have he :
          Real.exp ((5 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ 5 := by
        simpa only [Real.exp_log hnpos] using
          (Real.exp_nat_mul (Real.log (n : ℝ)) 5)
      rw [Real.exp_neg, he, one_div]


/-! ## Independent geometric epidemic phases: scalar N08 -/

/-- The geometric measure counts failures, so the actual waiting time is
k + 1. The bound uses exp (-lambda) >= 1 - lambda. -/
private theorem geometric_success_exp_moment
    (p : unitInterval) (hp : 0 < (p : ℝ))
    (θ : ℝ) (hθp : θ < (p : ℝ)) :
    Integrable
        (fun k : ℕ => Real.exp (θ * ((k : ℝ) + 1)))
        (ProbabilityTheory.geometricMeasure p) ∧
      (∫ k : ℕ, Real.exp (θ * ((k : ℝ) + 1))
        ∂ProbabilityTheory.geometricMeasure p) ≤
        (p : ℝ) / ((p : ℝ) - θ) := by
  have hpne : p ≠ 0 := by
    rintro rfl
    simp at hp
  let r : ℝ := (1 - (p : ℝ)) * Real.exp θ
  have hrnonneg : 0 ≤ r :=
    mul_nonneg (sub_nonneg.mpr p.property.2) (Real.exp_nonneg θ)
  have hrlt : r < 1 := by
    have hgap : 1 - (p : ℝ) < Real.exp (-θ) :=
      lt_of_lt_of_le (by linarith only [hθp]) (Real.one_sub_le_exp_neg θ)
    have hmul := mul_lt_mul_of_pos_right hgap (Real.exp_pos θ)
    simpa [r, Real.exp_neg] using hmul
  have hseries :
      HasSum (fun k : ℕ => r ^ k) (1 - r)⁻¹ :=
    hasSum_geometric_of_lt_one hrnonneg hrlt
  have hterm (k : ℕ) :
      (1 - (p : ℝ)) ^ k * (p : ℝ) *
          Real.exp (θ * ((k : ℝ) + 1)) =
        ((p : ℝ) * Real.exp θ) * r ^ k := by
    dsimp [r]
    rw [mul_add, mul_one, Real.exp_add]
    rw [show θ * (k : ℝ) = (k : ℝ) * θ by ring,
      Real.exp_nat_mul, mul_pow]
    ring
  have hint :
      Integrable
        (fun k : ℕ => Real.exp (θ * ((k : ℝ) + 1)))
        (ProbabilityTheory.geometricMeasure p) := by
    apply (ProbabilityTheory.integrable_geometricMeasure_iff hpne).2
    simpa only [Real.norm_eq_abs, Real.abs_exp, hterm] using
      hseries.summable.mul_left ((p : ℝ) * Real.exp θ)
  refine ⟨hint, ?_⟩
  have hmoment :
      (∫ k : ℕ, Real.exp (θ * ((k : ℝ) + 1))
        ∂ProbabilityTheory.geometricMeasure p) =
        ((p : ℝ) * Real.exp θ) * (1 - r)⁻¹ := by
    rw [ProbabilityTheory.integral_geometricMeasure hpne]
    simp_rw [smul_eq_mul, hterm]
    exact (hseries.mul_left ((p : ℝ) * Real.exp θ)).tsum_eq
  rw [hmoment, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (sub_pos.mpr hrlt) (sub_pos.mpr hθp)).2
  have hexp :
      (1 - θ) * Real.exp θ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right
      (Real.one_sub_le_exp_neg θ) (Real.exp_nonneg θ)
    simpa [Real.exp_neg] using h
  have hscaled := mul_le_mul_of_nonneg_left hexp hp.le
  dsimp [r]
  nlinarith only [hscaled]

private noncomputable def epidemicWallisFactor (k : ℕ) : ℝ :=
  (2 * ((k : ℝ) + 1)) / (2 * (k : ℝ) + 1)

/-- An elementary finite Wallis bound, including the empty product.
The induction's cleared-denominator inequality has slack exactly one. -/
private theorem epidemic_wallis_product_square (m : ℕ) :
    (∏ i : Fin m, epidemicWallisFactor i.val) ^ 2 ≤
      4 * (m : ℝ) + 1 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Fin.prod_univ_castSucc]
      change
        ((∏ i : Fin m, epidemicWallisFactor i.val) *
          epidemicWallisFactor m) ^ 2 ≤
          4 * ((m + 1 : ℕ) : ℝ) + 1
      rw [mul_pow]
      calc
        (∏ i : Fin m, epidemicWallisFactor i.val) ^ 2 *
            epidemicWallisFactor m ^ 2 ≤
            (4 * (m : ℝ) + 1) * epidemicWallisFactor m ^ 2 :=
          mul_le_mul_of_nonneg_right ih (sq_nonneg _)
        _ = ((4 * (m : ℝ) + 1) *
              (2 * ((m : ℝ) + 1)) ^ 2) /
              (2 * (m : ℝ) + 1) ^ 2 := by
          simp only [epidemicWallisFactor, div_pow]
          ring
        _ ≤ 4 * ((m + 1 : ℕ) : ℝ) + 1 := by
          apply (div_le_iff₀
            (sq_pos_of_pos (by positivity :
              0 < 2 * (m : ℝ) + 1))).2
          push_cast
          nlinarith

private theorem epidemic_phase_rate_bound
    {n : ℕ} (hn : 2 ≤ n)
    (i : Fin (n - 1)) (p : unitInterval)
    (hrate :
      (p : ℝ) =
        2 * ((i.val : ℝ) + 1) *
          ((n : ℝ) - ((i.val : ℝ) + 1)) /
          ((n : ℝ) * ((n : ℝ) - 1))) :
    0 < (p : ℝ) ∧
      1 / (n : ℝ) < (p : ℝ) ∧
      (p : ℝ) / ((p : ℝ) - 1 / (n : ℝ)) ≤
        epidemicWallisFactor i.val *
          epidemicWallisFactor i.rev.val := by
  let a : ℝ := (i.val : ℝ) + 1
  let b : ℝ := (i.rev.val : ℝ) + 1
  have ha : 1 ≤ a := by
    dsimp [a]
    exact le_add_of_nonneg_left (Nat.cast_nonneg i.val)
  have hb : 1 ≤ b := by
    dsimp [b]
    exact le_add_of_nonneg_left (Nat.cast_nonneg i.rev.val)
  have hindices : i.val + i.rev.val + 2 = n := by
    have hi := i.isLt
    simp only [Fin.val_rev]
    omega
  have hsum : a + b = (n : ℝ) := by
    have h :
        (i.val : ℝ) + (i.rev.val : ℝ) + 2 = (n : ℝ) := by
      exact_mod_cast hindices
    show (i.val : ℝ) + 1 + ((i.rev.val : ℝ) + 1) = (n : ℝ)
    linarith
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith only [hnreal]
  have hnsub : 0 < (n : ℝ) - 1 := by linarith only [hnreal]
  have habpos : 0 < a * b :=
    mul_pos (by linarith only [ha]) (by linarith only [hb])
  have hablower : (n : ℝ) - 1 ≤ a * b := by
    have h := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
    nlinarith only [h, hsum]
  have hpform :
      (p : ℝ) = 2 * a * b / ((n : ℝ) * ((n : ℝ) - 1)) := by
    calc
      (p : ℝ) =
          2 * ((i.val : ℝ) + 1) *
            ((n : ℝ) - ((i.val : ℝ) + 1)) /
            ((n : ℝ) * ((n : ℝ) - 1)) := hrate
      _ = 2 * a * b / ((n : ℝ) * ((n : ℝ) - 1)) := by
        change 2 * a * ((n : ℝ) - a) /
            ((n : ℝ) * ((n : ℝ) - 1)) = _
        rw [show (n : ℝ) - a = b by linarith only [hsum]]
  have hplower : 2 / (n : ℝ) ≤ (p : ℝ) := by
    rw [hpform]
    apply (div_le_div_iff₀ hnpos (mul_pos hnpos hnsub)).2
    have h := mul_le_mul_of_nonneg_left hablower hnpos.le
    nlinarith only [h]
  have hp : 0 < (p : ℝ) :=
    lt_of_lt_of_le (by positivity : 0 < 2 / (n : ℝ)) hplower
  have hθp : 1 / (n : ℝ) < (p : ℝ) :=
    lt_of_lt_of_le
      (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) hnpos) hplower
  refine ⟨hp, hθp, ?_⟩
  have hden : 0 < 2 * a * b - a - b + 1 := by
    nlinarith only [hablower, habpos, hsum]
  have hda : 0 < 2 * a - 1 := by linarith only [ha]
  have hdb : 0 < 2 * b - 1 := by linarith only [hb]
  have hratio :
      (p : ℝ) / ((p : ℝ) - 1 / (n : ℝ)) =
        2 * a * b / (2 * a * b - a - b + 1) := by
    apply (div_eq_div_iff (sub_pos.mpr hθp).ne' hden.ne').2
    simp only [hpform, ← hsum]
    field_simp [
      (show a + b ≠ 0 by linarith only [ha, hb]),
      (show a + b - 1 ≠ 0 by linarith only [ha, hb])]
    <;> ring
  have hwa :
      epidemicWallisFactor i.val = 2 * a / (2 * a - 1) := by
    dsimp [epidemicWallisFactor, a]
    congr 1 <;> ring
  have hwb :
      epidemicWallisFactor i.rev.val = 2 * b / (2 * b - 1) := by
    dsimp [epidemicWallisFactor, b]
    congr 1 <;> ring
  rw [hratio, hwa, hwb, div_mul_div_comm]
  apply (div_le_div_iff₀ hden (mul_pos hda hdb)).2
  nlinarith only [habpos.le]

private theorem independent_finite_product_integrable
    {Ω ι : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι]
    (X : ι → Ω → ℝ)
    (hX : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXi : ∀ i, Integrable (X i) μ) :
    Integrable (fun ω => ∏ i, X i ω) μ := by
  classical
  have hint (s : Finset ι) :
      Integrable (fun ω => ∏ i ∈ s, X i ω) μ := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using (integrable_const (1 : ℝ) : Integrable
          (fun _ : Ω => (1 : ℝ)) μ)
    | @insert i s his ih =>
        have hind :
            IndepFun (X i) (fun ω => ∏ j ∈ s, X j ω) μ := by
          simpa only [Finset.prod_fn] using
            (hX.indepFun_finsetProd_of_notMem hXm his).symm
        have hi := hind.integrable_mul (hXi i) ih
        simpa only [Finset.prod_insert his, Pi.mul_apply] using hi
  exact hint Finset.univ

/-- The scalar part of N08.
The independent comparison phases have the exact SI geometric laws.
Each G i counts failures, so the corresponding phase lasts G i + 1 steps.
Integrability is proved as part of the conclusion. -/
theorem epidemic_geometric_exp_moment
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (G : Fin (n - 1) → Ω → ℕ)
    (p : Fin (n - 1) → unitInterval)
    (hG : ∀ i, Measurable (G i))
    (hIndep : iIndepFun G μ)
    (hLaw : ∀ i, Measure.map (G i) μ =
      ProbabilityTheory.geometricMeasure (p i))
    (hRate : ∀ i,
      (p i : ℝ) =
        2 * ((i.val : ℝ) + 1) *
          ((n : ℝ) - ((i.val : ℝ) + 1)) /
          ((n : ℝ) * ((n : ℝ) - 1))) :
    Integrable
        (fun ω => Real.exp
          ((∑ i : Fin (n - 1), ((G i ω : ℝ) + 1)) / (n : ℝ))) μ ∧
      (∫ ω, Real.exp
        ((∑ i : Fin (n - 1), ((G i ω : ℝ) + 1)) / (n : ℝ)) ∂μ) ≤
        Real.exp 3 * (n : ℝ) := by
  classical
  let F : ℕ → ℝ := fun k =>
    Real.exp ((1 / (n : ℝ)) * ((k : ℝ) + 1))
  let X : Fin (n - 1) → Ω → ℝ := fun i ω => F (G i ω)
  have hFm : Measurable F := measurable_of_countable F
  have hXm : ∀ i, Measurable (X i) :=
    fun i => hFm.comp (hG i)
  have hXind : iIndepFun X μ :=
    hIndep.comp (fun _ => F) (fun _ => hFm)
  have hXi : ∀ i, Integrable (X i) μ := by
    intro i
    obtain ⟨hp, hθp, _⟩ :=
      epidemic_phase_rate_bound hn i (p i) (hRate i)
    have hgeom :=
      (geometric_success_exp_moment (p i) hp (1 / (n : ℝ)) hθp).1
    have hmap : Integrable F (Measure.map (G i) μ) := by
      rw [hLaw i]
      exact hgeom
    exact hmap.comp_aemeasurable (hG i).aemeasurable
  have hXbound (i : Fin (n - 1)) :
      (∫ ω, X i ω ∂μ) ≤
        epidemicWallisFactor i.val *
          epidemicWallisFactor i.rev.val := by
    obtain ⟨hp, hθp, hrat⟩ :=
      epidemic_phase_rate_bound hn i (p i) (hRate i)
    have hgeom :=
      (geometric_success_exp_moment (p i) hp (1 / (n : ℝ)) hθp).2
    have hmap :
        (∫ k, F k ∂Measure.map (G i) μ) =
          (∫ ω, X i ω ∂μ) :=
      integral_map (hG i).aemeasurable hFm.aestronglyMeasurable
    rw [hLaw i] at hmap
    rw [← hmap]
    exact hgeom.trans hrat
  have hexp :
      (fun ω => Real.exp
        ((∑ i : Fin (n - 1), ((G i ω : ℝ) + 1)) / (n : ℝ))) =
        (fun ω => ∏ i : Fin (n - 1), X i ω) := by
    funext ω
    calc
      Real.exp
          ((∑ i : Fin (n - 1), ((G i ω : ℝ) + 1)) / (n : ℝ)) =
          Real.exp
            (∑ i : Fin (n - 1),
              (1 / (n : ℝ)) * ((G i ω : ℝ) + 1)) := by
        congr 1
        rw [← Finset.mul_sum]
        ring
      _ = ∏ i : Fin (n - 1), X i ω := by
        rw [Real.exp_sum]
        try rfl
  have hreflect :
      (∏ i : Fin (n - 1), epidemicWallisFactor i.rev.val) =
        ∏ i : Fin (n - 1), epidemicWallisFactor i.val :=
    Fin.rev_bijective.prod_comp
      (fun i : Fin (n - 1) => epidemicWallisFactor i.val)
  constructor
  · rw [hexp]
    exact independent_finite_product_integrable X hXind hXm hXi
  · rw [hexp]
    calc
      (∫ ω, ∏ i : Fin (n - 1), X i ω ∂μ) =
          ∏ i : Fin (n - 1), ∫ ω, X i ω ∂μ :=
        hXind.integral_fun_prod_eq_prod_integral
          (fun i => (hXm i).aestronglyMeasurable)
      _ ≤ ∏ i : Fin (n - 1),
          (epidemicWallisFactor i.val *
            epidemicWallisFactor i.rev.val) := by
        apply Finset.prod_le_prod
        · intro i _
          apply integral_nonneg
          intro ω
          exact Real.exp_nonneg _
        · intro i _
          exact hXbound i
      _ = (∏ i : Fin (n - 1), epidemicWallisFactor i.val) ^ 2 := by
        rw [Finset.prod_mul_distrib, hreflect, pow_two]
      _ ≤ 4 * ((n - 1 : ℕ) : ℝ) + 1 :=
        epidemic_wallis_product_square (n - 1)
      _ ≤ 4 * (n : ℝ) := by
        have hcast :
            ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        rw [hcast]
        linarith
      _ ≤ Real.exp 3 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right
          (by linarith [Real.add_one_le_exp (3 : ℝ)])
          (Nat.cast_nonneg n)


end Ripple.PopulationProtocol.ExactMajority.ScalarTails
