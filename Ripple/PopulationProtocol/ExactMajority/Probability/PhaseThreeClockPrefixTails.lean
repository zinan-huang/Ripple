-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockPrefixTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar

/-!
# Bernoulli tails retaining a genuine prefix event

This is the prefix-weighted scalar interface needed by N12. The initial event
belongs to the time-zero sigma-algebra of the supplied filtration, which may
be a shifted pair-log filtration. Its probability remains as a factor in
every estimate. No conditioning on eventual clock success is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPrefixTails

open PhaseThreeScalar

variable {Ω : Type*} {m : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m}

/-- The original filtration, viewed from deterministic time s. -/
def shiftedFiltration (ℱ : Filtration ℕ m) (s : ℕ) : Filtration ℕ m where
  seq t := ℱ (s + t)
  mono' := by
    intro a b hab
    exact ℱ.mono (by omega)
  le' t := ℱ.le (s + t)

@[simp] theorem shiftedFiltration_apply (ℱ : Filtration ℕ m) (s t : ℕ) :
    shiftedFiltration ℱ s t = ℱ (s + t) := rfl

/-- The conditional MGF of an adapted zero-one variable is affine in its conditional mean. -/
theorem bernoulli_conditional_exp_identity
    {I : ℕ → Ω → ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (θ : ℝ) (t : ℕ) :
    μ[fun ω => Real.exp (θ * I t ω) | ℱ t] =ᵐ[μ]
      fun ω => 1 + (Real.exp θ - 1) * μ[I t | ℱ t] ω := by
  have hid :
      (fun ω => Real.exp (θ * I t ω)) =ᵐ[μ]
        fun ω => 1 + (Real.exp θ - 1) * I t ω := by
    filter_upwards [hzeroOne t] with ω hω
    rcases hω with hω | hω <;> simp [hω] <;> ring
  have hadd := condExp_add (integrable_const (1 : ℝ))
    ((bernoulli_integrable hI hzeroOne t).const_mul (Real.exp θ - 1)) (ℱ t)
  have hmul :
      μ[fun ω => (Real.exp θ - 1) * I t ω | ℱ t] =ᵐ[μ]
        fun ω => (Real.exp θ - 1) * μ[I t | ℱ t] ω := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      condExp_smul (μ := μ) (Real.exp θ - 1) (I t) (ℱ t)
  refine (condExp_congr_ae hid).trans ?_
  filter_upwards [hadd, hmul] with ω ha hm
  calc
    μ[fun ω => 1 + (Real.exp θ - 1) * I t ω | ℱ t] ω =
        μ[fun _ : Ω => (1 : ℝ) | ℱ t] ω +
          μ[fun ω => (Real.exp θ - 1) * I t ω | ℱ t] ω := ha
    _ = 1 + (Real.exp θ - 1) * μ[I t | ℱ t] ω := by
      rw [condExp_const (ℱ.le t) (1 : ℝ), hm]

/-- Exact conditional Bernoulli probability gives its exact conditional MGF. -/
theorem bernoulli_conditional_exp_eq
    {I : ℕ → Ω → ℝ} {p : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, μ[I t | ℱ t] =ᵐ[μ] fun _ => p)
    (θ : ℝ) (t : ℕ) :
    μ[fun ω => Real.exp (θ * I t ω) | ℱ t] =ᵐ[μ]
      fun _ => 1 + (Real.exp θ - 1) * p := by
  filter_upwards [bernoulli_conditional_exp_identity hI hzeroOne θ t, hcond t]
    with ω hid hp
  rw [hid, hp]

/-- The Bernoulli exponential bound with the probability of the prefix
event retained. The exponential parameter may have either sign. -/
theorem prefix_bernoulli_exp_moment_of_coefficient
    {I : ℕ → Ω → ℝ} {p θ : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcoef : ∀ t, ∀ᵐ ω ∂μ,
      (Real.exp θ - 1) * μ[I t | ℱ t] ω ≤ (Real.exp θ - 1) * p)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ) :
    (∫ ω, E.indicator (fun ω => Real.exp (θ * bernoulliCount I N ω)) ω ∂μ) ≤
      Real.exp ((Real.exp θ - 1) * p * (N : ℝ)) * μ.real E := by
  classical
  let Z : ℕ → Ω → ℝ :=
    fun k => E.indicator (fun ω => Real.exp (θ * bernoulliCount I k ω))
  have hEm : MeasurableSet E := (ℱ.le 0) _ hE
  have hZint (k : ℕ) : Integrable (Z k) μ :=
    (bernoulli_exp_integrable hI hzeroOne θ k).indicator hEm
  have hZsm (k : ℕ) : StronglyMeasurable[ℱ k] (Z k) := by
    have hS := bernoulliCount_stronglyMeasurable hI k
    have hexp : StronglyMeasurable[ℱ k]
        (fun ω => Real.exp (θ * bernoulliCount I k ω)) := by fun_prop
    exact hexp.indicator ((ℱ.mono (Nat.zero_le k)) _ hE)
  have hZpos (k : ℕ) (ω : Ω) : 0 ≤ Z k ω := by
    by_cases h : ω ∈ E <;> simp [Z, h, Real.exp_nonneg]
  change (∫ ω, Z N ω ∂μ) ≤ _
  induction N with
  | zero =>
      simpa [Z, bernoulliCount] using
        (integral_indicator_one (μ := μ) hEm).le
  | succ N ih =>
      let G : Ω → ℝ := fun ω => Real.exp (θ * I N ω)
      have hid : G =ᵐ[μ] fun ω => 1 + (Real.exp θ - 1) * I N ω := by
        filter_upwards [hzeroOne N] with ω hω
        rcases hω with hω | hω <;> simp [G, hω] <;> ring
      have hGint : Integrable G μ :=
        ((integrable_const (1 : ℝ)).add
          ((bernoulli_integrable hI hzeroOne N).const_mul
            (Real.exp θ - 1))).congr hid.symm
      have hstep : Z (N + 1) = Z N * G := by
        funext ω
        by_cases h : ω ∈ E <;>
          simp [Z, G, h, bernoulliCount, Finset.sum_range_succ,
            mul_add, Real.exp_add]
      have hstepae : Z (N + 1) =ᵐ[μ] Z N * G :=
        Filter.Eventually.of_forall (congrFun hstep)
      have hprodint : Integrable (Z N * G) μ :=
        (hZint (N + 1)).congr hstepae
      have hce :
          μ[Z (N + 1) | ℱ N] =ᵐ[μ] Z N * μ[G | ℱ N] :=
        (condExp_congr_ae hstepae).trans
          (condExp_mul_of_stronglyMeasurable_left (hZsm N) hprodint hGint)
      have hGbound :
          μ[G | ℱ N] ≤ᵐ[μ]
            fun _ => Real.exp ((Real.exp θ - 1) * p) := by
        filter_upwards [bernoulli_conditional_exp_identity hI hzeroOne θ N, hcoef N]
          with ω hid hcoefω
        change μ[fun ω => Real.exp (θ * I N ω) | ℱ N] ω ≤ _
        rw [hid]
        calc
          1 + (Real.exp θ - 1) * μ[I N | ℱ N] ω ≤
              1 + (Real.exp θ - 1) * p := by linarith
          _ ≤ Real.exp ((Real.exp θ - 1) * p) := by
            simpa [add_comm] using Real.add_one_le_exp ((Real.exp θ - 1) * p)
      have hbound :
          μ[Z (N + 1) | ℱ N] ≤ᵐ[μ]
            fun ω => Real.exp ((Real.exp θ - 1) * p) * Z N ω := by
        filter_upwards [hce, hGbound] with ω hceω hGω
        change μ[Z (N + 1) | ℱ N] ω ≤ _
        rw [hceω]
        change Z N ω * μ[G | ℱ N] ω ≤ _
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hGω (hZpos N ω)
      have harg :
          (Real.exp θ - 1) * p +
              (Real.exp θ - 1) * p * (N : ℝ) =
            (Real.exp θ - 1) * p * ((N + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      calc
        (∫ ω, Z (N + 1) ω ∂μ) =
            ∫ ω, μ[Z (N + 1) | ℱ N] ω ∂μ :=
          (integral_condExp (ℱ.le N)).symm
        _ ≤ ∫ ω, Real.exp ((Real.exp θ - 1) * p) * Z N ω ∂μ :=
          integral_mono_ae integrable_condExp ((hZint N).const_mul _) hbound
        _ = Real.exp ((Real.exp θ - 1) * p) * ∫ ω, Z N ω ∂μ :=
          integral_const_mul _ _
        _ ≤ Real.exp ((Real.exp θ - 1) * p) *
            (Real.exp ((Real.exp θ - 1) * p * (N : ℝ)) * μ.real E) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp ((Real.exp θ - 1) * p * ((N + 1 : ℕ) : ℝ)) *
            μ.real E := by
          rw [← mul_assoc, ← Real.exp_add, harg]

/-- The Bernoulli exponential bound with the probability of the prefix
event retained. The exponential parameter may have either sign. -/
theorem prefix_bernoulli_exp_moment
    {I : ℕ → Ω → ℝ} {p : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, μ[I t | ℱ t] =ᵐ[μ] fun _ => p)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (θ : ℝ) (N : ℕ) :
    (∫ ω, E.indicator (fun ω => Real.exp (θ * bernoulliCount I N ω)) ω ∂μ) ≤
      Real.exp ((Real.exp θ - 1) * p * (N : ℝ)) * μ.real E := by
  apply prefix_bernoulli_exp_moment_of_coefficient hI hzeroOne ?_ E hE N
  intro t
  filter_upwards [hcond t] with ω hω
  rw [hω]

/-- A two-sided exponential form: positive theta gives an upper tail and
negative theta gives a lower tail. -/
theorem prefix_bernoulli_exponential_tail_of_coefficient
    {I : ℕ → Ω → ℝ} {p θ : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcoef : ∀ t, ∀ᵐ ω ∂μ,
      (Real.exp θ - 1) * μ[I t | ℱ t] ω ≤ (Real.exp θ - 1) * p)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (r : ℝ) (N : ℕ) :
    μ.real (E ∩ {ω | θ * r ≤ θ * bernoulliCount I N ω}) ≤
      Real.exp ((Real.exp θ - 1) * p * (N : ℝ) - θ * r) * μ.real E := by
  classical
  let Z : Ω → ℝ :=
    E.indicator (fun ω => Real.exp (θ * bernoulliCount I N ω))
  have hEm : MeasurableSet E := (ℱ.le 0) _ hE
  have hZint : Integrable Z μ :=
    (bernoulli_exp_integrable hI hzeroOne θ N).indicator hEm
  have hZpos : ∀ ω, 0 ≤ Z ω := by
    intro ω
    by_cases h : ω ∈ E <;> simp [Z, h, Real.exp_nonneg]
  have hsub : E ∩ {ω | θ * r ≤ θ * bernoulliCount I N ω} ⊆
      {ω | Real.exp (θ * r) ≤ Z ω} := by
    rintro ω ⟨hω, hr⟩
    change Real.exp (θ * r) ≤ Z ω
    rw [show Z ω = Real.exp (θ * bernoulliCount I N ω) by simp [Z, hω]]
    exact Real.exp_le_exp.mpr hr
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ hZpos) hZint (Real.exp (θ * r))
  have hmul :
      Real.exp (θ * r) *
          μ.real (E ∩ {ω | θ * r ≤ θ * bernoulliCount I N ω}) ≤
        Real.exp ((Real.exp θ - 1) * p * (N : ℝ)) * μ.real E :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_nonneg _)).trans
      (hmarkov.trans (prefix_bernoulli_exp_moment_of_coefficient hI hzeroOne hcoef E hE N))
  calc
    μ.real (E ∩ {ω | θ * r ≤ θ * bernoulliCount I N ω}) ≤
        (Real.exp ((Real.exp θ - 1) * p * (N : ℝ)) * μ.real E) /
          Real.exp (θ * r) := by
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa only [mul_comm] using hmul
    _ = Real.exp ((Real.exp θ - 1) * p * (N : ℝ) - θ * r) * μ.real E := by
      rw [Real.exp_sub]
      ring
/-- A two-sided exponential form: positive theta gives an upper tail and
negative theta gives a lower tail. -/
theorem prefix_bernoulli_exponential_tail
    {I : ℕ → Ω → ℝ} {p : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, μ[I t | ℱ t] =ᵐ[μ] fun _ => p)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (θ r : ℝ) (N : ℕ) :
    μ.real (E ∩ {ω | θ * r ≤ θ * bernoulliCount I N ω}) ≤
      Real.exp ((Real.exp θ - 1) * p * (N : ℝ) - θ * r) * μ.real E := by
  apply prefix_bernoulli_exponential_tail_of_coefficient hI hzeroOne ?_ E hE r N
  intro t
  filter_upwards [hcond t] with ω hω
  rw [hω]


/-- A lower conditional-probability floor gives a lower tail with the
original probability of the prefix event retained. -/
theorem prefix_adapted_bernoulli_lower_tail
    {I : ℕ → Ω → ℝ} {p : ℝ}
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hcond : ∀ t, (fun _ => p) ≤ᵐ[μ] μ[I t | ℱ t])
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ) (k : ℝ) :
    μ.real (E ∩ {ω | bernoulliCount I N ω < k}) ≤
      Real.exp (k * Real.log 2 - p * (N : ℝ) / 2) * μ.real E := by
  let θ : ℝ := -Real.log 2
  have hθ : θ ≤ 0 := neg_nonpos.mpr (Real.log_nonneg (by norm_num))
  have hexp : Real.exp θ = (1 : ℝ) / 2 := by
    dsimp [θ]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hcoef : ∀ t, ∀ᵐ ω ∂μ,
      (Real.exp θ - 1) * μ[I t | ℱ t] ω ≤ (Real.exp θ - 1) * p := by
    intro t
    filter_upwards [hcond t] with ω hω
    apply mul_le_mul_of_nonpos_left hω
    rw [hexp]
    norm_num
  have hsub : E ∩ {ω | bernoulliCount I N ω < k} ⊆
      E ∩ {ω | θ * k ≤ θ * bernoulliCount I N ω} := by
    rintro ω ⟨hEω, hcount⟩
    exact ⟨hEω, mul_le_mul_of_nonpos_left hcount.le hθ⟩
  have htail := prefix_bernoulli_exponential_tail_of_coefficient
    hI hzeroOne hcoef E hE k N
  have harg :
      (Real.exp θ - 1) * p * (N : ℝ) - θ * k =
        k * Real.log 2 - p * (N : ℝ) / 2 := by
    rw [hexp]
    dsimp [θ]
    ring
  exact (measureReal_mono hsub).trans (by simpa only [harg] using htail)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPrefixTails

end
