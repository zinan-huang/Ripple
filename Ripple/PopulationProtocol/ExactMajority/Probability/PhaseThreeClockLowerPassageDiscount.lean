-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockLowerPassageDiscount.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockLowerPassageAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalBarrierTails

/-!
The P7 discounted process is indexed by the number of actual Clock
contacts while retaining the raw filtration.  Compensation by that
contact count gives an infinite-raw-horizon maximal bound.  This file
proves the scalar exponential construction; LowerPassageProcess supplies
every local datum from the actual protocol law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageDiscount

open PhaseThreeScalar PhaseThreeClockPrefixMaximal
  PhaseThreeClockOpportunityProcess PhaseThreeClockNormalBarrierTails
  PhaseThreeClockLowerPassageAlgebra

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}

structure LowerPassageData (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (C : ℕ) where
  large : 1000000 ≤ C
  Y : ℕ → Ω → ℝ
  N : ℕ → Ω → ℕ
  J : ℕ → Ω → ℝ
  stop : Ω → WithTop ℕ
  adapted_front : StronglyAdapted ℱ Y
  adapted_count : ∀ t, Measurable[ℱ t] (N t)
  adapted_tick : ∀ t, StronglyMeasurable[ℱ (t + 1)] (J t)
  stopping : IsStoppingTime ℱ stop
  front_nonneg : ∀ t ω, 0 ≤ Y t ω
  front_upper : ∀ t ω, Y t ω ≤ (C : ℝ)
  front_increment : ∀ t ω, Y (t + 1) ω - Y t ω = 0 ∨ Y (t + 1) ω - Y t ω = 1
  tick_zero_one : ∀ t ω, J t ω = 0 ∨ J t ω = 1
  increment_le_tick : ∀ t ω, incrementIndicator Y t ω ≤ J t ω
  count_zero : ∀ ω, N 0 ω = 0
  count_step : ∀ t ω, (N (t + 1) ω : ℝ) = (N t ω : ℝ) + J t ω
  region : ∀ (t : ℕ) ω, (t : WithTop ℕ) < stop ω → N t ω < lowerHorizon C
  rate : ∀ t : ℕ, ∀ᵐ ω ∂μ, (t : WithTop ℕ) < stop ω →
    (μ[incrementIndicator Y t | ℱ t]) ω ≤
      (μ[J t | ℱ t]) ω * lowerRate C (N t ω) (Y t ω)

def lowerExp {C : ℕ} (d : LowerPassageData μ ℱ C) (t : ℕ) (ω : Ω) : ℝ :=
  Real.exp (lowerExponent C (d.N t ω) (d.Y t ω))

def stoppedLowerExp {C : ℕ} (d : LowerPassageData μ ℱ C) : ℕ → Ω → ℝ :=
  stoppedProcess (lowerExp d) d.stop

theorem lowerExp_adapted {C : ℕ} (d : LowerPassageData μ ℱ C) :
    StronglyAdapted ℱ (lowerExp d) := by
  intro t
  have hY := d.adapted_front t
  have hD : StronglyMeasurable[ℱ t] (fun ω => lowerDiscount C (d.N t ω)) :=
    ((measurable_of_countable (lowerDiscount C)).comp (d.adapted_count t)).stronglyMeasurable
  have hU : StronglyMeasurable[ℱ t] (fun ω => lowerEnvelope C (d.N t ω)) :=
    ((measurable_of_countable (lowerEnvelope C)).comp (d.adapted_count t)).stronglyMeasurable
  have hN : StronglyMeasurable[ℱ t] (fun ω => (d.N t ω : ℝ)) :=
    ((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp
      (d.adapted_count t)).stronglyMeasurable
  unfold lowerExp lowerExponent
  exact Real.continuous_exp.comp_stronglyMeasurable
    (((hD.const_mul (1 / 1000 : ℝ)).mul (hY.sub hU)).sub (hN.const_mul (3 / 1000000 : ℝ)))

theorem lowerExp_bounds {C : ℕ} (d : LowerPassageData μ ℱ C) (t : ℕ) (ω : Ω) :
    0 ≤ lowerExp d t ω ∧ lowerExp d t ω ≤ Real.exp ((C : ℝ) / 1000) :=
  ⟨Real.exp_nonneg _, Real.exp_le_exp.mpr
    (lowerExponent_upper C (d.N t ω) d.large _ (d.front_upper t ω))⟩

theorem stoppedLowerExp_adapted {C : ℕ} (d : LowerPassageData μ ℱ C) :
    StronglyAdapted ℱ (stoppedLowerExp d) :=
  (lowerExp_adapted d).stoppedProcess_of_discrete d.stopping

theorem stoppedLowerExp_bounds {C : ℕ} (d : LowerPassageData μ ℱ C) (t : ℕ) (ω : Ω) :
    0 ≤ stoppedLowerExp d t ω ∧
      stoppedLowerExp d t ω ≤ Real.exp ((C : ℝ) / 1000) :=
  lowerExp_bounds d _ ω

theorem lower_stop_succ {t : ℕ} {τ : WithTop ℕ} (h : (t : WithTop ℕ) < τ) :
    ((t + 1 : ℕ) : WithTop ℕ) ≤ τ := by
  by_cases ht : τ = ⊤
  · simp only [ht, le_top]
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [← hk] at h ⊢
    have htk : t < k := WithTop.coe_lt_coe.mp h
    exact WithTop.coe_le_coe.mpr (by omega : t + 1 ≤ k)

/-- The exponential drift is derived from the local front/count laws. -/
theorem stoppedLowerExp_supermartingale {C : ℕ} (d : LowerPassageData μ ℱ C) :
    Supermartingale (stoppedLowerExp d) ℱ μ := by
  classical
  let Z := stoppedLowerExp d
  let P := incrementIndicator d.Y
  let b : ℕ → Ω → ℝ := fun t =>
    {ω | (t : WithTop ℕ) < d.stop ω}.indicator
      (fun ω => Real.exp ((1 / 1000 : ℝ) * lowerDiscount C (d.N t ω + 1)) - 1)
  let D : ℕ → Ω → ℝ := fun t =>
    {ω | (t : WithTop ℕ) < d.stop ω}.indicator
      (fun ω => (1 / 1000 : ℝ) * lowerDiscount C (d.N t ω + 1) *
        lowerRate C (d.N t ω) (d.Y t ω) + 3 / 1000000)
  have hdisc (t : ℕ) : StronglyMeasurable[ℱ t]
      (fun ω => lowerDiscount C (d.N t ω + 1)) :=
    ((measurable_of_countable (fun j : ℕ => lowerDiscount C (j + 1))).comp
      (d.adapted_count t)).stronglyMeasurable
  have hsource (t : ℕ) : StronglyMeasurable[ℱ t]
      (fun ω => lowerSource C (d.N t ω)) :=
    ((measurable_of_countable (lowerSource C)).comp
      (d.adapted_count t)).stronglyMeasurable
  have hb (t : ℕ) : StronglyMeasurable[ℱ t] (b t) := by
    have hf := hdisc t
    apply StronglyMeasurable.indicator ?_ (d.stopping.measurableSet_gt t)
    exact (Real.continuous_exp.comp_stronglyMeasurable (hf.const_mul (1 / 1000 : ℝ))).sub
      stronglyMeasurable_const
  have hD (t : ℕ) : StronglyMeasurable[ℱ t] (D t) := by
    have hf := hdisc t
    have hs := hsource t
    have hy := d.adapted_front t
    apply StronglyMeasurable.indicator ?_ (d.stopping.measurableSet_gt t)
    unfold lowerRate
    simpa only [div_eq_mul_inv] using
      ((hf.const_mul (1 / 1000 : ℝ)).mul
        (((hy.const_mul (2 : ℝ)).mul_const (((C : ℝ) - 1)⁻¹)).add hs)).add
        stronglyMeasurable_const
  have hbraw (j : ℕ) :
      0 ≤ Real.exp ((1 / 1000 : ℝ) * lowerDiscount C (j + 1)) - 1 ∧
        Real.exp ((1 / 1000 : ℝ) * lowerDiscount C (j + 1)) - 1 ≤ 1 := by
    have hd := lowerDiscount_bounds C (j + 1) d.large
    have hz : (1 / 1000 : ℝ) * lowerDiscount C (j + 1) ≤ 1 / 1000 := by linarith
    have he := exp_small_increment ((1 / 1000 : ℝ) * lowerDiscount C (j + 1))
      (mul_nonneg (by norm_num) hd.1.le) (by linarith)
    have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num) hd.1.le) hz 2
    exact ⟨he.1, by nlinarith only [he.2, hz, hs]⟩
  have hbb (t : ℕ) (ω : Ω) : 0 ≤ b t ω ∧ b t ω ≤ 1 := by
    by_cases ht : (t : WithTop ℕ) < d.stop ω
    · simpa only [b, Set.indicator_of_mem (show ω ∈ {ω | (t : WithTop ℕ) < d.stop ω} from ht)] using hbraw (d.N t ω)
    · simp only [b, Set.indicator_of_notMem (show ω ∉ {ω | (t : WithTop ℕ) < d.stop ω} from ht)]
      norm_num
  have hDn (t : ℕ) (ω : Ω) : 0 ≤ D t ω := by
    by_cases ht : (t : WithTop ℕ) < d.stop ω
    · have hk := lowerRate_bounds C (d.N t ω) d.large (d.region t ω ht).le
        (d.Y t ω) (d.front_nonneg t ω) (d.front_upper t ω)
      have hd := lowerDiscount_bounds C (d.N t ω + 1) d.large
      simp only [D, Set.indicator_of_mem (show ω ∈ {ω | (t : WithTop ℕ) < d.stop ω} from ht)]
      exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd.1.le) hk.1) (by norm_num)
    · simp only [D, Set.indicator_of_notMem (show ω ∉ {ω | (t : WithTop ℕ) < d.stop ω} from ht), le_refl]
  have hP (t : ℕ) : StronglyMeasurable[ℱ (t + 1)] (P t) :=
    incrementIndicator_stronglyMeasurable d.Y d.adapted_front t
  have hstep : ∀ t, Z (t + 1) ≤ᵐ[μ] fun ω =>
      Z t ω * (Real.exp (-D t ω * d.J t ω) * (1 + b t ω * P t ω)) := by
    intro t
    refine ae_of_all _ (fun ω => ?_)
    by_cases ht : (t : WithTop ℕ) < d.stop ω
    · have hcur : Z t ω = lowerExp d t ω := stoppedProcess_eq_of_le ht.le
      have hnext : Z (t + 1) ω = lowerExp d (t + 1) ω :=
        stoppedProcess_eq_of_le (lower_stop_succ ht)
      have hp := incrementIndicator_eq_increment d.Y t ω (d.front_increment t ω)
      have hY : d.Y (t + 1) ω = d.Y t ω + P t ω := by
        change incrementIndicator d.Y t ω = _ at hp
        dsimp only [P]
        linarith only [hp]
      have hJ := d.count_step t ω
      rcases d.tick_zero_one t ω with hzero | hone
      · have hpzero : P t ω = 0 := by
          have hle := d.increment_le_tick t ω
          have hnonneg := incrementIndicator_nonneg d.Y t ω
          dsimp only [P]
          rw [hzero] at hle
          linarith
        have hN : d.N (t + 1) ω = d.N t ω := by
          rw [hzero, add_zero] at hJ
          exact_mod_cast hJ
        simp only [hcur, hnext, lowerExp, hN, hY, hpzero, add_zero,
          hzero, mul_zero, neg_mul, Real.exp_zero, mul_one, le_refl]
      · have hN : d.N (t + 1) ω = d.N t ω + 1 := by
          rw [hone] at hJ
          exact_mod_cast hJ
        have he := lowerExponent_tick C (d.N t ω) d.large (d.region t ω ht)
          (d.Y t ω) (P t ω)
        show Z (t + 1) ω ≤ Z t ω * (Real.exp (-D t ω * d.J t ω) * (1 + b t ω * P t ω))
        rw [hcur, hnext]
        unfold lowerExp
        rw [hN, hY]
        apply (Real.exp_le_exp.mpr he).trans_eq
        rw [exp_bernoulli_factor _ _ _ _ (incrementIndicator_zero_one d.Y t ω)]
        simp only [b, D, Set.indicator_of_mem (show ω ∈ {ω | (t : WithTop ℕ) < d.stop ω} from ht), hone, mul_one]
        rfl
    · have hτ : d.stop ω ≤ (t : WithTop ℕ) := le_of_not_gt ht
      have hτnext : d.stop ω ≤ ((t + 1 : ℕ) : WithTop ℕ) :=
        hτ.trans (by exact_mod_cast Nat.le_succ t)
      have hsame : Z (t + 1) ω = Z t ω := by
        change stoppedProcess (lowerExp d) d.stop (t + 1) ω =
          stoppedProcess (lowerExp d) d.stop t ω
        rw [stoppedProcess_eq_of_ge (i := t + 1) hτnext, stoppedProcess_eq_of_ge (i := t) hτ]
      simp only [b, D, Set.indicator_of_notMem (show ω ∉ {ω | (t : WithTop ℕ) < d.stop ω} from ht), hsame, neg_zero,
        zero_mul, Real.exp_zero, add_zero, one_mul, mul_one, le_refl]
  have hrate : ∀ t, ∀ᵐ ω ∂μ,
      b t ω * (μ[P t | ℱ t]) ω ≤ (μ[d.J t | ℱ t]) ω * D t ω := by
    intro t
    have hp : 0 ≤ᵐ[μ] μ[P t | ℱ t] :=
      condExp_nonneg (ae_of_all _ (incrementIndicator_nonneg d.Y t))
    have hq : 0 ≤ᵐ[μ] μ[d.J t | ℱ t] := condExp_nonneg (ae_of_all _ (fun ω => by
      rcases d.tick_zero_one t ω with h | h <;> simp only [h] <;> norm_num))
    filter_upwards [d.rate t, hp, hq] with ω hr hpω hqω
    by_cases ht : (t : WithTop ℕ) < d.stop ω
    · simp only [b, D, Set.indicator_of_mem (show ω ∈ {ω | (t : WithTop ℕ) < d.stop ω} from ht)]
      exact lower_exponential_rate C (d.N t ω) d.large (d.region t ω ht).le
        (d.Y t ω) _ _ (d.front_nonneg t ω) (d.front_upper t ω) hpω hqω (hr ht)
    · simp only [b, D, Set.indicator_of_notMem (show ω ∉ {ω | (t : WithTop ℕ) < d.stop ω} from ht), zero_mul, mul_zero, le_refl]
  exact opportunity_supermartingale Z b D P d.J
    (fun _ => Real.exp ((C : ℝ) / 1000)) (fun _ => 1)
    (stoppedLowerExp_adapted d) hb hD (stoppedLowerExp_bounds d) hbb hDn
    hP d.adapted_tick (incrementIndicator_zero_one d.Y) d.tick_zero_one
    d.increment_le_tick hstep hrate

def lowerCrossing {C : ℕ} (d : LowerPassageData μ ℱ C) : Set Ω :=
  {ω | ∃ t : ℕ, (t : WithTop ℕ) ≤ d.stop ω ∧
    d.N t ω ≤ lowerHorizon C ∧ (StageEventSpec.bulkThreshold C : ℝ) ≤ d.Y t ω}

/-- Original-law P7 crossing estimate, including the crossing endpoint. -/
theorem lower_crossing_prefix_tail {C : ℕ} (d : LowerPassageData μ ℱ C)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (hinitial : ∀ ω ∈ E,
      d.Y 0 ω ≤ (StageEventSpec.bulkThreshold C : ℝ) ^ 2 / (C : ℝ)) :
    μ (E ∩ lowerCrossing d) ≤
      ENNReal.ofReal (Real.exp (-(C : ℝ) / 1000000)) * μ E := by
  have hzero : ∀ ω ∈ E, stoppedLowerExp d 0 ω ≤ 1 := by
    intro ω he
    have hc : stoppedLowerExp d 0 ω = lowerExp d 0 ω :=
      stoppedProcess_eq_of_le (show (0 : WithTop ℕ) ≤ d.stop ω from zero_le)
    rw [hc]
    unfold lowerExp
    rw [d.count_zero]
    apply Real.exp_le_one_iff.mpr
    have hg := lower_initial_gap C d.large (d.Y 0 ω) (hinitial ω he)
    have hd := lowerDiscount_bounds C 0 d.large
    dsimp only [lowerExponent]
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hd.1.le) (by linarith)
  have ht := prefix_crossing_tail (stoppedLowerExp_supermartingale d)
    (fun t ω => (stoppedLowerExp_bounds d t ω).1) E hE
    1 (Real.exp (-(C : ℝ) / 1000000)) (by norm_num) (Real.exp_nonneg _) hzero
    (lowerCrossing d) (by
      rintro ω ⟨t, ht, hN, hY⟩
      refine ⟨t, ?_⟩
      have he : stoppedLowerExp d t ω = lowerExp d t ω :=
        stoppedProcess_eq_of_le ht
      rw [he, lowerExp, ← Real.exp_add]
      apply Real.one_le_exp
      have hhit := lowerExponent_at_hit C (d.N t ω) d.large hN (d.Y t ω) hY
      linarith)
  simpa only [mul_one] using ht

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockLowerPassageDiscount

end
