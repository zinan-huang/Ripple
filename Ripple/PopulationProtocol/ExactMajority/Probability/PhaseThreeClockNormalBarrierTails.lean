-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockNormalBarrierTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalBarrierAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPrefixMaximal

/-!
# Stopped normal-front barrier from increment rates

The assumptions below are local process data: adapted front counts,
bounded normal-high count, their two increment laws and conditional rates,
and an observed first-stop time. The exponential drift is proved here.

The crossing endpoint is retained by the stopped process. A later guard
failure cannot erase an earlier crossing. PrefixMaximal then gives the
infinite-horizon P4 estimate without a time or excursion factor.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalBarrierTails

open PhaseThreeClockNormalBarrierAlgebra PhaseThreeClockPrefixMaximal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

open Classical in
def incrementIndicator (X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if X (t + 1) ω - X t ω = 1 then 1 else 0

theorem incrementIndicator_zero_one (X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    incrementIndicator X t ω = 0 ∨ incrementIndicator X t ω = 1 := by
  classical
  unfold incrementIndicator
  split_ifs <;> simp

theorem incrementIndicator_nonneg (X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ incrementIndicator X t ω := by
  rcases incrementIndicator_zero_one X t ω with h | h <;> simp [h]

theorem incrementIndicator_eq_increment (X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)
    (hx : X (t + 1) ω - X t ω = 0 ∨ X (t + 1) ω - X t ω = 1) :
    incrementIndicator X t ω = X (t + 1) ω - X t ω := by
  classical
  rcases hx with h | h <;> simp [incrementIndicator, h]

theorem incrementIndicator_stronglyMeasurable (X : ℕ → Ω → ℝ)
    (hX : StronglyAdapted ℱ X) (t : ℕ) :
    StronglyMeasurable[ℱ (t + 1)] (incrementIndicator X t) := by
  classical
  have hdiff : StronglyMeasurable[ℱ (t + 1)]
      (fun ω => X (t + 1) ω - X t ω) :=
    (hX (t + 1)).sub ((hX t).mono (ℱ.mono (Nat.le_succ t)))
  have hs : MeasurableSet[ℱ (t + 1)] {ω | X (t + 1) ω - X t ω = 1} :=
    measurableSet_eq_fun hdiff.measurable measurable_const
  exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable

theorem normal_raw_rate_bound (C D X Y pX pY : ℝ)
    (hC : 0 < C) (hD : 0 < D) (hX : 0 ≤ X)
    (hcap : X / C ≤ 101 / 1000)
    (hF : normalPotential C X Y ≤ 0)
    (hpX : 0 ≤ pX) (hpY : 0 ≤ pY)
    (hrX : 2 * X * (C - X) / D ≤ pX)
    (hrY : pY ≤ (X ^ 2 + 2 * C * Y) / D) :
    (Real.exp (1 / 10 : ℝ) - 1) * pY ≤
      (1 - Real.exp (-((9 / 100 : ℝ) * (2 * X + 1) / C))) * pX := by
  have hy : Y / C ≤ (9 / 10 : ℝ) * (X / C) ^ 2 := by
    have hY : Y ≤ (9 / 10 : ℝ) * X ^ 2 / C := by
      dsimp only [normalPotential] at hF
      linarith
    calc
      Y / C ≤ ((9 / 10 : ℝ) * X ^ 2 / C) / C :=
        div_le_div_of_nonneg_right hY hC.le
      _ = _ := by ring
  have hxnorm :
      2 * (X / C) * (1 - X / C) * (C ^ 2 / D) = 2 * X * (C - X) / D := by
    field_simp [ne_of_gt hC, ne_of_gt hD]
    <;> ring
  have hynorm :
      ((X / C) ^ 2 + 2 * (Y / C)) * (C ^ 2 / D) =
        (X ^ 2 + 2 * C * Y) / D := by
    field_simp [ne_of_gt hC, ne_of_gt hD]
    <;> ring
  have h := normal_barrier_rate_bound
    ((9 / 100 : ℝ) * (2 * X + 1) / C) (X / C) (Y / C) (C ^ 2 / D) pX pY
    (div_nonneg hX hC.le) hcap hy (by positivity) hpX hpY
    (normal_barrier_increment_coefficient C X hC)
    (by simpa only [hxnorm] using hrX) (by simpa only [hynorm] using hrY)
  linarith

/-- The early cutoff produces precisely the initial exponent used in P4. -/
theorem normal_initial_barrier (C X Y : ℝ) (hC : 0 < C)
    (hX : C ^ (51 / 100 : ℝ) ≤ X) (hY : Y ≤ 0) :
    normalPotential C X Y ≤ -(9 / 10 : ℝ) * C ^ (1 / 50 : ℝ) := by
  have hsq : (C ^ (51 / 100 : ℝ)) ^ 2 ≤ X ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hC.le _) hX 2
  have hpower : (C ^ (51 / 100 : ℝ)) ^ 2 / C = C ^ (1 / 50 : ℝ) := by
    calc
      (C ^ (51 / 100 : ℝ)) ^ 2 / C =
          (C ^ (51 / 100 : ℝ) * C ^ (51 / 100 : ℝ)) / C := by ring
      _ = C ^ ((51 / 100 : ℝ) + 51 / 100) / C := by rw [← Real.rpow_add hC]
      _ = C ^ ((1 / 50 : ℝ) + 1) / C := by norm_num
      _ = (C ^ (1 / 50 : ℝ) * C) / C := by
        rw [Real.rpow_add hC, Real.rpow_one]
      _ = _ := mul_div_cancel_right₀ _ (ne_of_gt hC)
  have hdiv := div_le_div_of_nonneg_right hsq hC.le
  rw [hpower] at hdiv
  unfold normalPotential
  have heq : (9 / 10 : ℝ) * X ^ 2 / C = (9 / 10 : ℝ) * (X ^ 2 / C) := by ring
  rw [heq]
  linarith

/-- Only elementary local conditions occur in this interface. In the
protocol application D is the ordered-pair denominator m(m-1). -/
structure NormalBarrierData (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (C D : ℝ) where
  positive_clock : 0 < C
  positive_denominator : 0 < D
  X : ℕ → Ω → ℝ
  Y : ℕ → Ω → ℝ
  stop : Ω → WithTop ℕ
  adapted_front : StronglyAdapted ℱ X
  adapted_normal : StronglyAdapted ℱ Y
  stopping : IsStoppingTime ℱ stop
  front_nonneg : ∀ t ω, 0 ≤ X t ω
  normal_upper : ∀ t ω, Y t ω ≤ C
  region : ∀ (t : ℕ) ω, (t : WithTop ℕ) < stop ω →
    X t ω / C ≤ 101 / 1000 ∧ normalPotential C (X t ω) (Y t ω) ≤ 0
  front_increment : ∀ (t : ℕ) ω, (t : WithTop ℕ) < stop ω →
    X (t + 1) ω - X t ω = 0 ∨ X (t + 1) ω - X t ω = 1
  normal_increment : ∀ (t : ℕ) ω, (t : WithTop ℕ) < stop ω →
    Y (t + 1) ω - Y t ω ≤ 0 ∨ Y (t + 1) ω - Y t ω = 1
  front_rate : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < stop ω →
    2 * X t ω * (C - X t ω) / D ≤ μ[incrementIndicator X t | ℱ t] ω
  normal_rate : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < stop ω →
    μ[incrementIndicator Y t | ℱ t] ω ≤ ((X t ω) ^ 2 + 2 * C * Y t ω) / D

def normalExp (C : ℝ) (X Y : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.exp (normalPotential C (X t ω) (Y t ω) / 10)

def stoppedNormalExp {C D : ℝ} (d : NormalBarrierData μ ℱ C D) : ℕ → Ω → ℝ :=
  stoppedProcess (normalExp C d.X d.Y) d.stop

theorem normalExp_stronglyAdapted {C D : ℝ} (d : NormalBarrierData μ ℱ C D) :
    StronglyAdapted ℱ (normalExp C d.X d.Y) := by
  intro t
  have hx := d.adapted_front t
  have hy := d.adapted_normal t
  unfold normalExp normalPotential
  fun_prop

theorem normalExp_bounds {C D : ℝ} (d : NormalBarrierData μ ℱ C D)
    (t : ℕ) (ω : Ω) :
    0 ≤ normalExp C d.X d.Y t ω ∧
      normalExp C d.X d.Y t ω ≤ Real.exp (C / 10) := by
  refine ⟨Real.exp_nonneg _, Real.exp_le_exp.mpr ?_⟩
  have hnonneg : 0 ≤ (9 / 10 : ℝ) * (d.X t ω) ^ 2 / C :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) d.positive_clock.le
  dsimp only [normalPotential]
  linarith [d.normal_upper t ω]

theorem stoppedNormalExp_stronglyAdapted {C D : ℝ}
    (d : NormalBarrierData μ ℱ C D) :
    StronglyAdapted ℱ (stoppedNormalExp d) :=
  (normalExp_stronglyAdapted d).stoppedProcess_of_discrete d.stopping

theorem stoppedNormalExp_bounds {C D : ℝ} (d : NormalBarrierData μ ℱ C D)
    (t : ℕ) (ω : Ω) :
    0 ≤ stoppedNormalExp d t ω ∧ stoppedNormalExp d t ω ≤ Real.exp (C / 10) :=
  normalExp_bounds d _ ω

private theorem bounded_integrable {f : Ω → ℝ} {B : ℝ}
    (hf : StronglyMeasurable f) (hb : ∀ ω, 0 ≤ f ω ∧ f ω ≤ B) :
    Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ (fun ω => ?_))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hb ω).1] using (hb ω).2

private theorem bounded_bernoulli_product {f I : Ω → ℝ} {B : ℝ}
    (hf : StronglyMeasurable f) (hI : StronglyMeasurable I)
    (hB : 0 ≤ B) (hb : ∀ ω, 0 ≤ f ω ∧ f ω ≤ B)
    (hbin : ∀ ω, I ω = 0 ∨ I ω = 1) :
    Integrable (fun ω => f ω * I ω) μ := by
  refine Integrable.of_bound (hf.mul hI).aestronglyMeasurable B
    (ae_of_all _ (fun ω => ?_))
  rcases hbin ω with hi | hi
  · simpa only [hi, mul_zero, norm_zero] using hB
  · simpa only [hi, mul_one, Real.norm_eq_abs, abs_of_nonneg (hb ω).1] using (hb ω).2

private theorem succ_le_of_lt_stop {t : ℕ} {τ : WithTop ℕ} (h : (t : WithTop ℕ) < τ) :
    ((t + 1 : ℕ) : WithTop ℕ) ≤ τ := by
  by_cases ht : τ = ⊤
  · simp only [ht, le_top]
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [← hk] at h ⊢
    have htk : t < k := WithTop.coe_lt_coe.mp h
    exact WithTop.coe_le_coe.mpr (by omega : t + 1 ≤ k)

private theorem conditional_affine_upper
    {U V P Q I J : Ω → ℝ} {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hU : StronglyMeasurable[m] U)
    (hP : StronglyMeasurable[m] P) (hQ : StronglyMeasurable[m] Q)
    (hUi : Integrable U μ) (hVi : Integrable V μ)
    (hIi : Integrable I μ) (hJi : Integrable J μ)
    (hPI : Integrable (fun ω => P ω * I ω) μ)
    (hQJ : Integrable (fun ω => Q ω * J ω) μ)
    (hstep : V ≤ᵐ[μ] fun ω => U ω + P ω * I ω - Q ω * J ω) :
    μ[V | m] ≤ᵐ[μ] fun ω =>
      U ω + P ω * μ[I | m] ω - Q ω * μ[J | m] ω := by
  have hcur : μ[U | m] = U := condExp_of_stronglyMeasurable hm hU hUi
  have hmono := condExp_mono (m := m) hVi ((hUi.add hPI).sub hQJ) hstep
  have hadd := condExp_add hUi hPI m
  have hsub := condExp_sub (hUi.add hPI) hQJ m
  have hpull := condExp_mul_of_stronglyMeasurable_left hP hPI hIi
  have hqpull := condExp_mul_of_stronglyMeasurable_left hQ hQJ hJi
  filter_upwards [hmono, hadd, hsub, hpull, hqpull] with ω hmω ha hs hp hq
  have ha' : μ[fun ω => U ω + P ω * I ω | m] ω =
      U ω + μ[fun ω => P ω * I ω | m] ω := by
    simpa only [Pi.add_apply, hcur] using ha
  have hs' : μ[fun ω => U ω + P ω * I ω - Q ω * J ω | m] ω =
      μ[fun ω => U ω + P ω * I ω | m] ω -
        μ[fun ω => Q ω * J ω | m] ω := by
    simpa only [Pi.sub_apply, Pi.add_apply] using hs
  have hp' : μ[fun ω => P ω * I ω | m] ω = P ω * μ[I | m] ω := by
    simpa only [Pi.mul_apply] using hp
  have hq' : μ[fun ω => Q ω * J ω | m] ω = Q ω * μ[J | m] ω := by
    simpa only [Pi.mul_apply] using hq
  change μ[V | m] ω ≤ U ω + P ω * μ[I | m] ω - Q ω * μ[J | m] ω
  have hm' : μ[V | m] ω ≤
      μ[fun ω => U ω + P ω * I ω - Q ω * J ω | m] ω := hmω
  rwa [hs', ha', hp', hq'] at hm'

def barrierDecay (C X : ℝ) : ℝ :=
  1 - Real.exp (-((9 / 100 : ℝ) * (2 * X + 1) / C))

theorem barrierDecay_bounds (C X : ℝ) (hC : 0 < C) (hX : 0 ≤ X) :
    0 ≤ barrierDecay C X ∧ barrierDecay C X ≤ 1 := by
  have ha : 0 ≤ (9 / 100 : ℝ) * (2 * X + 1) / C := by positivity
  have he : Real.exp (-((9 / 100 : ℝ) * (2 * X + 1) / C)) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr ha)
  unfold barrierDecay
  constructor
  · linarith
  · linarith [Real.exp_nonneg (-((9 / 100 : ℝ) * (2 * X + 1) / C))]

/-- The conditional exponential drift is derived, including the transition
that first crosses a barrier. The stopped process then stays frozen. -/
theorem stoppedNormalExp_conditional_step {C D : ℝ}
    (d : NormalBarrierData μ ℱ C D) (t : ℕ) :
    μ[stoppedNormalExp d (t + 1) | ℱ t] ≤ᵐ[μ] stoppedNormalExp d t := by
  classical
  let Z := stoppedNormalExp d
  let A : Set Ω := {ω | (t : WithTop ℕ) < d.stop ω}
  let b : ℝ := Real.exp (1 / 10 : ℝ) - 1
  let B : ℝ := Real.exp (C / 10)
  let P : Ω → ℝ := A.indicator (fun ω => Z t ω * b)
  let Q : Ω → ℝ := A.indicator (fun ω => Z t ω * barrierDecay C (d.X t ω))
  have hA : MeasurableSet[ℱ t] A := d.stopping.measurableSet_gt t
  have hb : 0 ≤ b := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hB : 0 ≤ B := Real.exp_nonneg _
  have hZ := stoppedNormalExp_stronglyAdapted d
  have hZi (s : ℕ) : Integrable (Z s) μ :=
    bounded_integrable ((hZ s).mono (ℱ.le s)) (stoppedNormalExp_bounds d s)
  have hIX := incrementIndicator_stronglyMeasurable d.X d.adapted_front
  have hIY := incrementIndicator_stronglyMeasurable d.Y d.adapted_normal
  have hIXi : Integrable (incrementIndicator d.X t) μ :=
    PhaseThreeScalar.bernoulli_integrable hIX
      (fun s => ae_of_all _ (incrementIndicator_zero_one d.X s)) t
  have hIYi : Integrable (incrementIndicator d.Y t) μ :=
    PhaseThreeScalar.bernoulli_integrable hIY
      (fun s => ae_of_all _ (incrementIndicator_zero_one d.Y s)) t
  have hP : StronglyMeasurable[ℱ t] P :=
    ((hZ t).mul stronglyMeasurable_const).indicator hA
  have hdecay : StronglyMeasurable[ℱ t] (fun ω => barrierDecay C (d.X t ω)) := by
    have hx := d.adapted_front t
    unfold barrierDecay
    fun_prop
  have hQ : StronglyMeasurable[ℱ t] Q := ((hZ t).mul hdecay).indicator hA
  have hPb (ω : Ω) : 0 ≤ P ω ∧ P ω ≤ B * b := by
    by_cases ha : ω ∈ A
    · simp only [P, Set.indicator_of_mem ha]
      exact ⟨mul_nonneg (stoppedNormalExp_bounds d t ω).1 hb,
        mul_le_mul_of_nonneg_right (stoppedNormalExp_bounds d t ω).2 hb⟩
    · simp only [P, Set.indicator_of_notMem ha]
      exact ⟨le_rfl, mul_nonneg hB hb⟩
  have hQb (ω : Ω) : 0 ≤ Q ω ∧ Q ω ≤ B := by
    by_cases ha : ω ∈ A
    · simp only [Q, Set.indicator_of_mem ha]
      have hdb := barrierDecay_bounds C (d.X t ω) d.positive_clock (d.front_nonneg t ω)
      refine ⟨mul_nonneg (stoppedNormalExp_bounds d t ω).1 hdb.1, ?_⟩
      calc
        Z t ω * barrierDecay C (d.X t ω) ≤ Z t ω * 1 :=
          mul_le_mul_of_nonneg_left hdb.2 (stoppedNormalExp_bounds d t ω).1
        _ = Z t ω := mul_one _
        _ ≤ B := (stoppedNormalExp_bounds d t ω).2
    · simp only [Q, Set.indicator_of_notMem ha]
      exact ⟨le_rfl, hB⟩
  have hPI : Integrable (fun ω => P ω * incrementIndicator d.Y t ω) μ :=
    bounded_bernoulli_product (hP.mono (ℱ.le t))
      ((hIY t).mono (ℱ.le (t + 1))) (mul_nonneg hB hb) hPb
      (incrementIndicator_zero_one d.Y t)
  have hQJ : Integrable (fun ω => Q ω * incrementIndicator d.X t ω) μ :=
    bounded_bernoulli_product (hQ.mono (ℱ.le t))
      ((hIX t).mono (ℱ.le (t + 1))) hB hQb (incrementIndicator_zero_one d.X t)
  have hstep : Z (t + 1) ≤ᵐ[μ] fun ω =>
      Z t ω + P ω * incrementIndicator d.Y t ω - Q ω * incrementIndicator d.X t ω := by
    refine ae_of_all _ (fun ω => ?_)
    by_cases ha : ω ∈ A
    · have hτ : ((t + 1 : ℕ) : WithTop ℕ) ≤ d.stop ω := succ_le_of_lt_stop ha
      have hcur : Z t ω = normalExp C d.X d.Y t ω :=
        stoppedProcess_eq_of_le (le_of_lt ha)
      have hnext : Z (t + 1) ω = normalExp C d.X d.Y (t + 1) ω :=
        stoppedProcess_eq_of_le hτ
      let dx := d.X (t + 1) ω - d.X t ω
      let dy := d.Y (t + 1) ω - d.Y t ω
      have hx := d.front_increment t ω ha
      have hy := d.normal_increment t ω ha
      have hinc := normalPotential_exp_increment_bound C (d.X t ω) (d.Y t ω) dx dy
        d.positive_clock (d.front_nonneg t ω) hx hy
      have hdx : incrementIndicator d.X t ω = dx :=
        incrementIndicator_eq_increment d.X t ω hx
      simp only [P, Q, Set.indicator_of_mem ha, hcur, hnext]
      calc
        normalExp C d.X d.Y (t + 1) ω =
            normalExp C d.X d.Y t ω *
              Real.exp ((normalPotential C (d.X t ω + dx) (d.Y t ω + dy) -
                normalPotential C (d.X t ω) (d.Y t ω)) / 10) := by
          have hxnext : d.X t ω + dx = d.X (t + 1) ω := by dsimp only [dx]; ring
          have hynext : d.Y t ω + dy = d.Y (t + 1) ω := by dsimp only [dy]; ring
          unfold normalExp
          rw [hxnext, hynext, ← Real.exp_add]
          congr 1
          ring
        _ ≤ normalExp C d.X d.Y t ω *
            (1 + b * (if dy = 1 then 1 else 0) - barrierDecay C (d.X t ω) * dx) :=
          mul_le_mul_of_nonneg_left hinc (Real.exp_nonneg _)
        _ = _ := by
          rw [hdx]
          by_cases hdy : d.Y (t + 1) ω - d.Y t ω = 1 <;>
            simp only [incrementIndicator, dy, hdy, if_true, if_false] <;> ring
    · have hτ : d.stop ω ≤ (t : WithTop ℕ) := le_of_not_gt ha
      have hτnext : d.stop ω ≤ ((t + 1 : ℕ) : WithTop ℕ) :=
        hτ.trans (by exact_mod_cast Nat.le_succ t)
      have hsame : Z (t + 1) ω = Z t ω := by
        change stoppedProcess (normalExp C d.X d.Y) d.stop (t + 1) ω =
          stoppedProcess (normalExp C d.X d.Y) d.stop t ω
        rw [stoppedProcess_eq_of_ge (i := t + 1) hτnext, stoppedProcess_eq_of_ge (i := t) hτ]
      simp only [P, Q, Set.indicator_of_notMem ha, zero_mul, add_zero, sub_zero, hsame,
        le_refl]
  have hce := conditional_affine_upper (ℱ.le t) (hZ t) hP hQ
    (hZi t) (hZi (t + 1)) hIYi hIXi hPI hQJ hstep
  have hpx : 0 ≤ᵐ[μ] μ[incrementIndicator d.X t | ℱ t] :=
    condExp_nonneg (ae_of_all _ (incrementIndicator_nonneg d.X t))
  have hpy : 0 ≤ᵐ[μ] μ[incrementIndicator d.Y t | ℱ t] :=
    condExp_nonneg (ae_of_all _ (incrementIndicator_nonneg d.Y t))
  filter_upwards [hce, d.front_rate t, d.normal_rate t, hpx, hpy] with ω hceω hrx hry hpxω hpyω
  by_cases ha : ω ∈ A
  · have hrate := normal_raw_rate_bound C D (d.X t ω) (d.Y t ω)
      (μ[incrementIndicator d.X t | ℱ t] ω) (μ[incrementIndicator d.Y t | ℱ t] ω)
      d.positive_clock d.positive_denominator (d.front_nonneg t ω)
      (d.region t ω ha).1 (d.region t ω ha).2 hpxω hpyω (hrx ha) (hry ha)
    have hscaled := mul_le_mul_of_nonneg_left hrate (stoppedNormalExp_bounds d t ω).1
    have hce' : μ[Z (t + 1) | ℱ t] ω ≤
        Z t ω + (Z t ω * b) * μ[incrementIndicator d.Y t | ℱ t] ω -
          (Z t ω * barrierDecay C (d.X t ω)) * μ[incrementIndicator d.X t | ℱ t] ω := by
      simpa only [P, Q, Set.indicator_of_mem ha] using hceω
    change μ[Z (t + 1) | ℱ t] ω ≤ Z t ω
    dsimp only [b, barrierDecay] at hce' hscaled
    nlinarith only [hce', hscaled]
  · simpa only [P, Q, Set.indicator_of_notMem ha, zero_mul, add_zero, sub_zero] using hceω

theorem stoppedNormalExp_supermartingale {C D : ℝ}
    (d : NormalBarrierData μ ℱ C D) :
    Supermartingale (stoppedNormalExp d) ℱ μ :=
  supermartingale_nat (stoppedNormalExp_stronglyAdapted d)
    (fun t => bounded_integrable
      ((stoppedNormalExp_stronglyAdapted d t).mono (ℱ.le t))
      (stoppedNormalExp_bounds d t))
    (stoppedNormalExp_conditional_step d)

def normalBarrierCrossing {C D : ℝ} (d : NormalBarrierData μ ℱ C D) : Set Ω :=
  {ω | ∃ t : ℕ, (t : WithTop ℕ) ≤ d.stop ω ∧
    0 ≤ normalPotential C (d.X t ω) (d.Y t ω)}


theorem normalBarrierCrossing_measurable {C D : ℝ}
    (d : NormalBarrierData μ ℱ C D) :
    MeasurableSet (normalBarrierCrossing d) := by
  have heq : normalBarrierCrossing d =
      ⋃ t : ℕ, {ω | (t : WithTop ℕ) ≤ d.stop ω ∧
        0 ≤ normalPotential C (d.X t ω) (d.Y t ω)} := by
    ext ω
    simp only [normalBarrierCrossing, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  refine MeasurableSet.iUnion fun t => ?_
  have hF : StronglyMeasurable[ℱ t]
      (fun ω => normalPotential C (d.X t ω) (d.Y t ω)) := by
    have hx := d.adapted_front t
    have hy := d.adapted_normal t
    unfold normalPotential
    simpa only [div_eq_mul_inv] using
      hy.sub (((hx.pow 2).const_mul (9 / 10 : ℝ)).mul_const C⁻¹)
  exact (ℱ.le t) _ ((d.stopping.measurableSet_ge t).inter
    (measurableSet_le measurable_const hF.measurable))

def normalBarrierCrossingThrough {C D : ℝ}
    (d : NormalBarrierData μ ℱ C D) (N : ℕ) : Set Ω :=
  {ω | ∃ t ≤ N, (t : WithTop ℕ) ≤ d.stop ω ∧
    0 ≤ normalPotential C (d.X t ω) (d.Y t ω)}

theorem normalBarrierCrossingThrough_measurable {C D : ℝ}
    (d : NormalBarrierData μ ℱ C D) (N : ℕ) :
    MeasurableSet[ℱ N] (normalBarrierCrossingThrough d N) := by
  have heq : normalBarrierCrossingThrough d N =
      ⋃ t : ℕ, {ω | t ≤ N ∧ (t : WithTop ℕ) ≤ d.stop ω ∧
        0 ≤ normalPotential C (d.X t ω) (d.Y t ω)} := by
    ext ω
    simp only [normalBarrierCrossingThrough, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  refine MeasurableSet.iUnion fun t => ?_
  by_cases ht : t ≤ N
  · have hF : StronglyMeasurable[ℱ t]
        (fun ω => normalPotential C (d.X t ω) (d.Y t ω)) := by
      have hx := d.adapted_front t
      have hy := d.adapted_normal t
      unfold normalPotential
      simpa only [div_eq_mul_inv] using
      hy.sub (((hx.pow 2).const_mul (9 / 10 : ℝ)).mul_const C⁻¹)
    have hs : MeasurableSet[ℱ t] {ω | (t : WithTop ℕ) ≤ d.stop ω ∧
        0 ≤ normalPotential C (d.X t ω) (d.Y t ω)} :=
      (d.stopping.measurableSet_ge t).inter
        (measurableSet_le measurable_const hF.measurable)
    simpa only [ht, true_and] using (ℱ.mono ht) _ hs
  · simp only [ht, false_and, Set.setOf_false, MeasurableSet.empty]

/-- The crossing endpoint is included, even if it also reaches another
stopping barrier. Every later value of the auxiliary process is frozen. -/
theorem normal_barrier_prefix_tail {C D : ℝ}
    (d : NormalBarrierData μ ℱ C D)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (r : ℝ)
    (hinitial : ∀ ω ∈ E, normalPotential C (d.X 0 ω) (d.Y 0 ω) ≤ -r) :
    μ (E ∩ normalBarrierCrossing d) ≤ ENNReal.ofReal (Real.exp (-r / 10)) * μ E := by
  have hzero : ∀ ω ∈ E, stoppedNormalExp d 0 ω ≤ Real.exp (-r / 10) := by
    intro ω he
    have hcur : stoppedNormalExp d 0 ω = normalExp C d.X d.Y 0 ω :=
      stoppedProcess_eq_of_le (show (0 : WithTop ℕ) ≤ d.stop ω from zero_le)
    rw [hcur]
    exact Real.exp_le_exp.mpr (by linarith [hinitial ω he])
  apply (measure_mono ?_).trans
    (prefix_maximal (stoppedNormalExp_supermartingale d)
      (fun t ω => (stoppedNormalExp_bounds d t ω).1) E hE
      (Real.exp (-r / 10)) (Real.exp_nonneg _) hzero)
  rintro ω ⟨he, t, ht, hF⟩
  refine ⟨he, t, ?_⟩
  have hcur : stoppedNormalExp d t ω = normalExp C d.X d.Y t ω :=
    stoppedProcess_eq_of_le ht
  rw [hcur]
  apply Real.one_le_exp
  exact div_nonneg hF (by norm_num)

theorem normal_barrier_cutoff_prefix_tail {C D : ℝ}
    (d : NormalBarrierData μ ℱ C D)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (hfront : ∀ ω ∈ E, C ^ (51 / 100 : ℝ) ≤ d.X 0 ω)
    (hnormal : ∀ ω ∈ E, d.Y 0 ω ≤ 0) :
    μ (E ∩ normalBarrierCrossing d) ≤
      ENNReal.ofReal (Real.exp (-(9 / 100 : ℝ) * C ^ (1 / 50 : ℝ))) * μ E := by
  have h := normal_barrier_prefix_tail d E hE ((9 / 10 : ℝ) * C ^ (1 / 50 : ℝ))
    (fun ω he => by
      have h0 := normal_initial_barrier C (d.X 0 ω) (d.Y 0 ω) d.positive_clock
        (hfront ω he) (hnormal ω he)
      linarith)
  have heq : -((9 / 10 : ℝ) * C ^ (1 / 50 : ℝ)) / 10 =
      -(9 / 100 : ℝ) * C ^ (1 / 50 : ℝ) := by ring
  simpa only [heq] using h

theorem normal_barrier_calibrated_prefix_tail {C D : ℝ}
    (d : NormalBarrierData μ ℱ C D)
    (hlog : 4194304 ≤ Real.log C)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (hfront : ∀ ω ∈ E, C ^ (51 / 100 : ℝ) ≤ d.X 0 ω)
    (hnormal : ∀ ω ∈ E, d.Y 0 ω ≤ 0) :
    μ (E ∩ normalBarrierCrossing d) ≤ ENNReal.ofReal (C ^ (-100 : ℝ)) * μ E := by
  apply (normal_barrier_cutoff_prefix_tail d E hE hfront hnormal).trans
  have hC := d.positive_clock
  have hx0 : 0 ≤ Real.log C := by linarith
  obtain ⟨_, hsmall, _, _⟩ := PhaseThreeModel.Numeric.new_power_calibration hC hlog
  have hcal : Real.exp (-(9 / 100 : ℝ) * C ^ (1 / 50 : ℝ)) ≤ C ^ (-100 : ℝ) :=
    calc
      Real.exp (-(9 / 100 : ℝ) * C ^ (1 / 50 : ℝ)) ≤
          Real.exp (Real.log C * (-100)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := (Real.rpow_def_of_pos hC _).symm
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal hcal) _

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockNormalBarrierTails

end
