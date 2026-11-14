-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingScalar.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingScalar

theorem bernoulli_hoeffding (p s : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    Real.exp (-s * p) * (1 + (Real.exp s - 1) * p) ≤
      Real.exp (s ^ 2 / 8) := by
  let p' : ℝ≥0 := Real.toNNReal p
  have hp' : p' ≤ 1 := by
    show Real.toNNReal p ≤ 1
    rw [← Real.toNNReal_one]
    exact Real.toNNReal_le_toNNReal hpone
  let X : Bool → ℝ := fun b => cond b 1 0
  have hmean : (∫ b, X b ∂(PMF.bernoulli p' hp').toMeasure) = p := by
    simpa [X, p', Real.coe_toNNReal p hp] using PMF.bernoulli_expectation hp'
  have hmeas : AEMeasurable X (PMF.bernoulli p' hp').toMeasure :=
    Measurable.of_discrete.aemeasurable
  have hbounded : ∀ᵐ b ∂(PMF.bernoulli p' hp').toMeasure,
      X b ∈ Set.Icc (0 : ℝ) 1 := by
    exact Filter.Eventually.of_forall (fun b => by cases b <;> simp [X])
  have hsg := hasSubgaussianMGF_of_mem_Icc hmeas hbounded
  have h := hsg.mgf_le s
  have heval :
      mgf (fun b => X b - ∫ c, X c ∂(PMF.bernoulli p' hp').toMeasure)
        (PMF.bernoulli p' hp').toMeasure s =
      Real.exp (-s * p) * (1 + (Real.exp s - 1) * p) := by
    rw [hmean]
    simp only [mgf, PMF.integral_eq_sum]
    simp [X, p', Real.coe_toNNReal p hp, NNReal.coe_sub hp', show s * (1 - p) = -s * p + s by ring,
      Real.exp_add] <;> ring
  rw [heval] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  norm_num <;> ring

noncomputable def factor (θ a q A B : ℝ) : ℝ :=
  Real.exp (θ * a * (B - q * A) - θ ^ 2 * A / 8)

noncomputable def base (θ a q : ℝ) : ℝ :=
  Real.exp (-θ * a * q - θ ^ 2 / 8)

theorem factor_linear (θ a q A B : ℝ)
    (hA : A = 0 ∨ A = 1) (hB : B = 0 ∨ B = 1) (hBA : B ≤ A) :
    factor θ a q A B =
      1 + (base θ a q - 1) * A +
        (base θ a q * (Real.exp (θ * a) - 1)) * B := by
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · simp [factor]
  · norm_num at hBA
  · simp [factor, base] <;> congr 1 <;> ring
  · have he : θ * a * (1 - q) - θ ^ 2 / 8 =
        (-θ * a * q - θ ^ 2 / 8) + θ * a := by ring
    simp only [factor, base, mul_one]
    rw [he, Real.exp_add]
    ring

theorem base_bounds {θ a q : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hq : 0 ≤ q) :
    0 ≤ base θ a q ∧ base θ a q ≤ 1 := by
  refine ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr ?_⟩
  have hprod : 0 ≤ θ * a * q := mul_nonneg (mul_nonneg hθ ha) hq
  have hsq := sq_nonneg θ
  nlinarith

theorem factor_bounds {θ a q A B : ℝ}
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (haone : a ≤ 1) (hq : 0 ≤ q)
    (hA : A = 0 ∨ A = 1) (hB : B = 0 ∨ B = 1) (hBA : B ≤ A) :
    0 ≤ factor θ a q A B ∧ factor θ a q A B ≤ Real.exp θ := by
  refine ⟨Real.exp_nonneg _, Real.exp_le_exp.mpr ?_⟩
  have hqA : 0 ≤ q * A := mul_nonneg hq (by rcases hA with rfl | rfl <;> norm_num)
  have hBupper : B ≤ 1 := by rcases hB with rfl | rfl <;> norm_num
  have hApos : 0 ≤ A := by rcases hA with rfl | rfl <;> norm_num
  have hab : a * (B - q * A) ≤ 1 := by
    calc
      a * (B - q * A) ≤ a * 1 := mul_le_mul_of_nonneg_left (by linarith) ha
      _ ≤ 1 := by simpa using haone
  have hcharge : 0 ≤ θ ^ 2 * A / 8 :=
    div_nonneg (mul_nonneg (sq_nonneg θ) hApos) (by norm_num)
  have hmain := mul_le_mul_of_nonneg_left hab hθ
  change θ * a * (B - q * A) - θ ^ 2 * A / 8 ≤ θ
  nlinarith

theorem linear_factor_le_one {θ a q x z : ℝ}
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (haone : a ≤ 1) (hq : 0 ≤ q)
    (hx : 0 ≤ x) (hzx : z ≤ x) (hzq : z ≤ q * x) :
    1 + (base θ a q - 1) * x +
        (base θ a q * (Real.exp (θ * a) - 1)) * z ≤ 1 := by
  have hr : 0 ≤ base θ a q := (base_bounds hθ ha hq).1
  have hs : 0 ≤ θ * a := mul_nonneg hθ ha
  have he : 0 ≤ Real.exp (θ * a) - 1 := by
    have h := Real.one_le_exp_iff.mpr hs
    linarith
  have hc : 0 ≤ base θ a q * (Real.exp (θ * a) - 1) := mul_nonneg hr he
  by_cases hqone : q ≤ 1
  · have hh := bernoulli_hoeffding q (θ * a) hq hqone
    have hasq : a ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr haone)]
    have hsq : (θ * a) ^ 2 ≤ θ ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr hasq)]
    have hcharged :
        base θ a q * (1 + (Real.exp (θ * a) - 1) * q) ≤ 1 := by
      calc
        base θ a q * (1 + (Real.exp (θ * a) - 1) * q) =
            Real.exp (-θ ^ 2 / 8) *
              (Real.exp (-(θ * a) * q) * (1 + (Real.exp (θ * a) - 1) * q)) := by
          rw [base, show -θ * a * q - θ ^ 2 / 8 =
            -θ ^ 2 / 8 + (-(θ * a) * q) by ring, Real.exp_add]
          ring
        _ ≤ Real.exp (-θ ^ 2 / 8) * Real.exp ((θ * a) ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
        _ = Real.exp (-θ ^ 2 / 8 + (θ * a) ^ 2 / 8) := (Real.exp_add _ _).symm
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hz := mul_le_mul_of_nonneg_left hzq hc
    have hh' := mul_le_mul_of_nonneg_right hcharged hx
    nlinarith
  · have hqge : 1 ≤ q := le_of_lt (lt_of_not_ge hqone)
    have hcharged : base θ a q * Real.exp (θ * a) ≤ 1 := by
      rw [base, ← Real.exp_add]
      apply Real.exp_le_one_iff.mpr
      have hprod : 0 ≤ θ * a * (q - 1) := mul_nonneg hs (sub_nonneg.mpr hqge)
      nlinarith [sq_nonneg θ]
    have hz := mul_le_mul_of_nonneg_left hzx hc
    have hh' := mul_le_mul_of_nonneg_right hcharged hx
    nlinarith

section Filtered

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}

structure Trials (A B a q : ℕ → Ω → ℝ) : Prop where
  event_measurable : ∀ t, StronglyMeasurable[ℱ (t + 1)] (A t)
  bad_measurable : ∀ t, StronglyMeasurable[ℱ (t + 1)] (B t)
  coefficient_measurable : ∀ t, StronglyMeasurable[ℱ t] (a t)
  ratio_measurable : ∀ t, StronglyMeasurable[ℱ t] (q t)
  event_binary : ∀ t, ∀ᵐ ω ∂μ, A t ω = 0 ∨ A t ω = 1
  bad_binary : ∀ t, ∀ᵐ ω ∂μ, B t ω = 0 ∨ B t ω = 1
  bad_subset : ∀ t, B t ≤ᵐ[μ] A t
  coefficient_bounds : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ a t ω ∧ a t ω ≤ 1
  ratio_nonneg : ∀ t, 0 ≤ᵐ[μ] q t
  hazard : ∀ t, μ[B t | ℱ t] ≤ᵐ[μ] fun ω => q t ω * μ[A t | ℱ t] ω

variable {A B a q : ℕ → Ω → ℝ}

theorem Trials.event_integrable (h : Trials (μ := μ) (ℱ := ℱ) A B a q) (t : ℕ) :
    Integrable (A t) μ :=
  PhaseThreeScalar.bernoulli_integrable h.event_measurable h.event_binary t

theorem Trials.bad_integrable (h : Trials (μ := μ) (ℱ := ℱ) A B a q) (t : ℕ) :
    Integrable (B t) μ :=
  PhaseThreeScalar.bernoulli_integrable h.bad_measurable h.bad_binary t

noncomputable def eventCount (A : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range N, A t ω

noncomputable def score (A B a q : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range N, a t ω * (B t ω - q t ω * A t ω)

noncomputable def capital (A B a q : ℕ → Ω → ℝ) (θ : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  Real.exp (θ * score A B a q N ω - θ ^ 2 * eventCount A N ω / 8)

theorem Trials.score_measurable (h : Trials (μ := μ) (ℱ := ℱ) A B a q) (N : ℕ) :
    StronglyMeasurable[ℱ N] (score A B a q N) := by
  unfold score
  refine (Finset.range N).stronglyMeasurable_fun_sum ?_
  intro t ht
  have htN : t + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp ht)
  have htN' : t ≤ N := le_trans (Nat.le_succ t) htN
  exact ((h.coefficient_measurable t).mono (ℱ.mono htN')).mul
    (((h.bad_measurable t).mono (ℱ.mono htN)).sub
      (((h.ratio_measurable t).mono (ℱ.mono htN')).mul
        ((h.event_measurable t).mono (ℱ.mono htN))))

theorem Trials.capital_measurable (h : Trials (μ := μ) (ℱ := ℱ) A B a q)
    (θ : ℝ) (N : ℕ) :
    StronglyMeasurable[ℱ N] (capital A B a q θ N) := by
  have hs := h.score_measurable N
  have hc : StronglyMeasurable[ℱ N] (eventCount A N) :=
    PhaseThreeScalar.bernoulliCount_stronglyMeasurable h.event_measurable N
  unfold capital
  fun_prop

theorem Trials.score_upper (h : Trials (μ := μ) (ℱ := ℱ) A B a q) (N : ℕ) :
    ∀ᵐ ω ∂μ, score A B a q N ω ≤ (N : ℝ) := by
  have hall : ∀ᵐ ω ∂μ, ∀ t,
      a t ω * (B t ω - q t ω * A t ω) ≤ 1 := by
    refine ae_all_iff.mpr fun t => ?_
    filter_upwards [h.event_binary t, h.bad_binary t, h.coefficient_bounds t,
      h.ratio_nonneg t] with ω hA hB ha hq
    have hAz : 0 ≤ A t ω := by rcases hA with hA | hA <;> simp [hA]
    have hBo : B t ω ≤ 1 := by rcases hB with hB | hB <;> simp [hB]
    have hqA := mul_nonneg hq hAz
    calc
      a t ω * (B t ω - q t ω * A t ω) ≤ a t ω * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) ha.1
      _ ≤ 1 := by simpa using ha.2
  filter_upwards [hall] with ω hω
  calc
    score A B a q N ω ≤ ∑ _t ∈ Finset.range N, (1 : ℝ) :=
      Finset.sum_le_sum (fun t _ => hω t)
    _ = N := by simp

theorem Trials.capital_integrable (h : Trials (μ := μ) (ℱ := ℱ) A B a q)
    {θ : ℝ} (hθ : 0 ≤ θ) (N : ℕ) :
    Integrable (capital A B a q θ N) μ := by
  refine Integrable.of_bound
    ((h.capital_measurable θ N).mono (ℱ.le N)).aestronglyMeasurable
      (Real.exp (θ * N)) ?_
  filter_upwards [h.score_upper N,
    PhaseThreeScalar.bernoulliCount_bounds h.event_binary N] with ω hs hc
  change ‖Real.exp (θ * score A B a q N ω - θ ^ 2 * eventCount A N ω / 8)‖ ≤ Real.exp (θ * N)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  change θ * score A B a q N ω - θ ^ 2 * eventCount A N ω / 8 ≤ θ * N
  have hcount : 0 ≤ eventCount A N ω := hc.1
  have hcharge := div_nonneg (mul_nonneg (sq_nonneg θ) hcount) (by norm_num : (0:ℝ) ≤ 8)
  have hmain := mul_le_mul_of_nonneg_left hs hθ
  linarith

theorem Trials.factor_integrable (h : Trials (μ := μ) (ℱ := ℱ) A B a q)
    {θ : ℝ} (hθ : 0 ≤ θ) (t : ℕ) :
    Integrable (fun ω => factor θ (a t ω) (q t ω) (A t ω) (B t ω)) μ := by
  have ha := (h.coefficient_measurable t).mono (ℱ.le t)
  have hq := (h.ratio_measurable t).mono (ℱ.le t)
  have hA := (h.event_measurable t).mono (ℱ.le (t+1))
  have hB := (h.bad_measurable t).mono (ℱ.le (t+1))
  have hm : StronglyMeasurable
      (fun ω => factor θ (a t ω) (q t ω) (A t ω) (B t ω)) := by
    unfold factor
    fun_prop
  refine Integrable.of_bound hm.aestronglyMeasurable (Real.exp θ) ?_
  filter_upwards [h.event_binary t, h.bad_binary t, h.bad_subset t,
    h.coefficient_bounds t, h.ratio_nonneg t] with ω hA hB hBA ha hq
  have hb := factor_bounds hθ ha.1 ha.2 hq hA hB hBA
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

theorem Trials.factor_condExp_le (h : Trials (μ := μ) (ℱ := ℱ) A B a q)
    {θ : ℝ} (hθ : 0 ≤ θ) (t : ℕ) :
    μ[fun ω => factor θ (a t ω) (q t ω) (A t ω) (B t ω) | ℱ t] ≤ᵐ[μ]
      fun _ => (1 : ℝ) := by
  let U : Ω → ℝ := fun ω => base θ (a t ω) (q t ω) - 1
  let W : Ω → ℝ := fun ω =>
    base θ (a t ω) (q t ω) * (Real.exp (θ * a t ω) - 1)
  have hUsm : StronglyMeasurable[ℱ t] U := by
    have ha := h.coefficient_measurable t
    have hq := h.ratio_measurable t
    dsimp [U, base]
    fun_prop
  have hWsm : StronglyMeasurable[ℱ t] W := by
    have ha := h.coefficient_measurable t
    have hq := h.ratio_measurable t
    dsimp [W, base]
    fun_prop
  have hUAint : Integrable (U * A t) μ := by
    have hm := ((hUsm.mono (ℱ.le t)).mul
      ((h.event_measurable t).mono (ℱ.le (t+1)))).aestronglyMeasurable (μ := μ)
    refine Integrable.of_bound hm 1 ?_
    filter_upwards [h.event_binary t, h.coefficient_bounds t,
      h.ratio_nonneg t] with ω hA ha hq
    have hr := base_bounds hθ ha.1 hq
    have hu : |U ω| ≤ 1 := by dsimp [U]; exact abs_le.mpr ⟨by linarith, by linarith⟩
    rcases hA with hA | hA
    · simp [Pi.mul_apply, hA]
    · simpa [Pi.mul_apply, hA, Real.norm_eq_abs] using hu
  have hWBint : Integrable (W * B t) μ := by
    have hm := ((hWsm.mono (ℱ.le t)).mul
      ((h.bad_measurable t).mono (ℱ.le (t+1)))).aestronglyMeasurable (μ := μ)
    refine Integrable.of_bound hm (Real.exp θ) ?_
    filter_upwards [h.bad_binary t, h.coefficient_bounds t,
      h.ratio_nonneg t] with ω hB ha hq
    have hr := base_bounds hθ ha.1 hq
    have hes : 1 ≤ Real.exp (θ * a t ω) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hθ ha.1)
    have het : Real.exp (θ * a t ω) ≤ Real.exp θ :=
      Real.exp_le_exp.mpr (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha.2 hθ)
    have hwzero : 0 ≤ W ω := mul_nonneg hr.1 (sub_nonneg.mpr hes)
    have hwbound : W ω ≤ Real.exp θ := by
      dsimp [W]
      nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hes)]
    rcases hB with hB | hB
    · simp [Pi.mul_apply, hB, Real.exp_nonneg]
    · simpa [Pi.mul_apply, hB, Real.norm_eq_abs, abs_of_nonneg hwzero] using hwbound
  have hlinear : (fun ω => factor θ (a t ω) (q t ω) (A t ω) (B t ω)) =ᵐ[μ]
      fun ω => 1 + U ω * A t ω + W ω * B t ω := by
    filter_upwards [h.event_binary t, h.bad_binary t, h.bad_subset t] with ω hA hB hBA
    exact factor_linear θ _ _ _ _ hA hB hBA
  have hleft := condExp_add (integrable_const (1 : ℝ)) hUAint (ℱ t)
  have hsum := condExp_add ((integrable_const (1 : ℝ)).add hUAint) hWBint (ℱ t)
  have hpullA := condExp_mul_of_stronglyMeasurable_left hUsm hUAint
    (h.event_integrable t)
  have hpullB := condExp_mul_of_stronglyMeasurable_left hWsm hWBint
    (h.bad_integrable t)
  have hApos : 0 ≤ᵐ[μ] A t := by
    filter_upwards [h.event_binary t] with ω hA
    rcases hA with hA | hA <;> simp [hA]
  have hCEpos := condExp_nonneg (m := ℱ t) hApos
  have hCEsub := condExp_mono (m := ℱ t) (h.bad_integrable t) (h.event_integrable t) (h.bad_subset t)
  filter_upwards [condExp_congr_ae hlinear, hleft, hsum, hpullA, hpullB,
    hCEpos, hCEsub, h.hazard t, h.coefficient_bounds t, h.ratio_nonneg t]
    with ω heq hl hs hpA hpB hx hzx hzq ha hq
  have hformula :
      μ[fun ω => factor θ (a t ω) (q t ω) (A t ω) (B t ω) | ℱ t] ω =
        1 + U ω * μ[A t | ℱ t] ω + W ω * μ[B t | ℱ t] ω := by
    rw [heq]
    change μ[(fun _ : Ω => (1 : ℝ)) + U * A t + W * B t | ℱ t] ω = _
    rw [hs, Pi.add_apply, hl, Pi.add_apply, condExp_const (ℱ.le t) (1 : ℝ), hpA, hpB] <;> rfl
  rw [hformula]
  exact linear_factor_le_one hθ ha.1 ha.2 hq hx hzx hzq

theorem capital_step (θ : ℝ) (N : ℕ) :
    capital A B a q θ (N+1) =
      capital A B a q θ N *
        (fun ω => factor θ (a N ω) (q N ω) (A N ω) (B N ω)) := by
  funext ω
  simp only [capital, score, eventCount, Finset.sum_range_succ, Pi.mul_apply, factor]
  rw [← Real.exp_add]
  congr 1
  ring

theorem Trials.capital_expectation_le (h : Trials (μ := μ) (ℱ := ℱ) A B a q)
    {θ : ℝ} (hθ : 0 ≤ θ) (N : ℕ) :
    (∫ ω, capital A B a q θ N ω ∂μ) ≤ 1 := by
  induction N with
  | zero => simp [capital, score, eventCount]
  | succ N ih =>
      let G : Ω → ℝ := fun ω => factor θ (a N ω) (q N ω) (A N ω) (B N ω)
      have hstep : capital A B a q θ (N+1) =ᵐ[μ] capital A B a q θ N * G :=
        Filter.Eventually.of_forall (congrFun (capital_step θ N))
      have hpull :
          μ[capital A B a q θ N * G | ℱ N] =ᵐ[μ]
            capital A B a q θ N * μ[G | ℱ N] :=
        condExp_mul_of_stronglyMeasurable_left (h.capital_measurable θ N)
          ((h.capital_integrable hθ (N+1)).congr hstep) (h.factor_integrable hθ N)
      have hce := (condExp_congr_ae hstep).trans hpull
      have hbound :
          μ[capital A B a q θ (N+1) | ℱ N] ≤ᵐ[μ] capital A B a q θ N := by
        filter_upwards [hce, h.factor_condExp_le hθ N] with ω hceω hg
        rw [hceω]
        change capital A B a q θ N ω * μ[G | ℱ N] ω ≤ _
        have hz : 0 ≤ capital A B a q θ N ω := Real.exp_nonneg _
        simpa using mul_le_mul_of_nonneg_left hg hz
      calc
        (∫ ω, capital A B a q θ (N+1) ω ∂μ) =
            ∫ ω, μ[capital A B a q θ (N+1) | ℱ N] ω ∂μ :=
          (integral_condExp (ℱ.le N)).symm
        _ ≤ ∫ ω, capital A B a q θ N ω ∂μ :=
          integral_mono_ae integrable_condExp (h.capital_integrable hθ N) hbound
        _ ≤ 1 := ih

theorem Trials.raw_tail (h : Trials (μ := μ) (ℱ := ℱ) A B a q)
    (γ k : ℝ) (hγ : 0 ≤ γ) (N : ℕ) :
    μ.real {ω | k ≤ eventCount A N ω ∧ γ * eventCount A N ω ≤ score A B a q N ω} ≤
      Real.exp (-2 * γ ^ 2 * k) := by
  let E : Set Ω := {ω | k ≤ eventCount A N ω ∧
    γ * eventCount A N ω ≤ score A B a q N ω}
  have hθ : 0 ≤ 4 * γ := mul_nonneg (by norm_num) hγ
  have hsub : E ⊆ {ω | Real.exp (2 * γ ^ 2 * k) ≤ capital A B a q (4*γ) N ω} := by
    intro ω hω
    apply Real.exp_le_exp.mpr
    change 2 * γ ^ 2 * k ≤
      4 * γ * score A B a q N ω - (4*γ)^2 * eventCount A N ω / 8
    have hmain := mul_le_mul_of_nonneg_left hω.2 hθ
    have hcount := mul_le_mul_of_nonneg_left hω.1 (by positivity : 0 ≤ 2*γ^2)
    nlinarith
  have hprob := measureReal_mono (μ := μ) hsub
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Real.exp_nonneg
      (4 * γ * score A B a q N ω - (4*γ)^2 * eventCount A N ω / 8)))
    (h.capital_integrable hθ N) (Real.exp (2*γ^2*k))
  have hmul : Real.exp (2*γ^2*k) * μ.real E ≤ 1 :=
    (mul_le_mul_of_nonneg_left hprob (Real.exp_nonneg _)).trans
      (hmarkov.trans (h.capital_expectation_le hθ N))
  change μ.real E ≤ _
  calc
    μ.real E ≤ 1 / Real.exp (2*γ^2*k) := by
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa [mul_comm] using hmul
    _ = Real.exp (-2*γ^2*k) := by rw [one_div, ← Real.exp_neg]; congr 1 <;> ring

end Filtered

noncomputable def forecast (M D k j b : ℝ) : ℝ :=
  b + (k-j) * (D-b) / (M-j)

theorem forecast_initial (M D k : ℝ) :
    forecast M D k 0 0 = D*k/M := by
  simp only [forecast, sub_zero, zero_add]
  ring

theorem forecast_terminal (M D k b : ℝ) :
    forecast M D k k b = b := by simp [forecast]

theorem forecast_increment (M D k j b x : ℝ)
    (hMj : M-j ≠ 0) (hMnext : M-j-1 ≠ 0) :
    forecast M D k (j+1) (b+x) - forecast M D k j b =
      ((M-k)/(M-j-1)) * (x-(D-b)/(M-j)) := by
  unfold forecast
  have hMnext' : M-(j+1) ≠ 0 := by simpa [sub_add_eq_sub_sub] using hMnext
  field_simp [hMj, hMnext, hMnext'] <;> ring

theorem forecast_coefficient_bounds {M k j : ℕ}
    (hjk : j < k) (hkM : k < M) :
    0 ≤ ((M:ℝ)-k)/((M:ℝ)-j-1) ∧
      ((M:ℝ)-k)/((M:ℝ)-j-1) ≤ 1 := by
  have hden : 0 < (M:ℝ)-j-1 := by
    have hnat : j+1 < M := lt_of_le_of_lt (Nat.succ_le_iff.mpr hjk) hkM
    have hreal : (j:ℝ)+1 < M := by exact_mod_cast hnat
    linarith
  have hnum : 0 ≤ (M:ℝ)-k := sub_nonneg.mpr (by exact_mod_cast hkM.le)
  refine ⟨div_nonneg hnum hden.le, (div_le_one hden).2 ?_⟩
  have hjk' : (j:ℝ)+1 ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr hjk)
  linarith

theorem forecast_ratio_nonneg {M D j b : ℕ} (hjM : j < M) (hbD : b ≤ D) :
    0 ≤ ((D:ℝ)-b)/((M:ℝ)-j) := by
  apply div_nonneg
  · exact sub_nonneg.mpr (by exact_mod_cast hbD)
  · exact sub_nonneg.mpr (by exact_mod_cast hjM.le)

end Ripple.PopulationProtocol.ExactMajority.LateSamplingScalar
