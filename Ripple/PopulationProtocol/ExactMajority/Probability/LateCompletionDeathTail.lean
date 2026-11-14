-- Ripple/PopulationProtocol/ExactMajority/Probability/LateCompletionDeathTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingStoppedDebtLaw

/-!
# First-moment extinction for an adapted count-death process

`ScalarTails.adapted_death_exponential_tail` controls a positive fraction of
an initial population.  Phase-5 sampling needs extinction of the last item.
This file proves the corresponding first-moment estimate from the same
conditional death hypothesis, then applies it to the existing killed debt
process and its original-law stopping-time splice.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.LateCompletionDeathTail

open TimeTheorem PairLog PhaseOneDrain
open AveragingRecordedExpectation AveragingRecordedSplice
open AveragingStoppedDebt

variable {Ω : Type*} {m : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m}

private theorem natCast_integrable_of_bound
    (J : ℕ → Ω → ℕ) (M t : ℕ)
    (hJ : ∀ u, StronglyMeasurable[ℱ u] (J u))
    (hbound : ∀ u, ∀ᵐ ω ∂μ, J u ω ≤ M) :
    Integrable (fun ω => (J t ω : ℝ)) μ := by
  have hm : Measurable (J t) :=
    ((hJ t).mono (ℱ.le t)).measurable
  refine (integrable_const (M : ℝ)).mono'
    ((measurable_from_nat (f := ((↑) : ℕ → ℝ))).comp hm).aestronglyMeasurable ?_
  filter_upwards [hbound t] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hω

/-- One-step first-moment contraction.  Multi-item deaths are allowed; the
only required event is a strict decrease of the natural-valued process. -/
theorem adapted_death_mean_step
    (J : ℕ → Ω → ℕ) (M : ℕ) (q : ℝ)
    (hJ : ∀ u, StronglyMeasurable[ℱ u] (J u))
    (hbound : ∀ u, ∀ᵐ ω ∂μ, J u ω ≤ M)
    (hmono : ∀ u, ∀ᵐ ω ∂μ, J (u + 1) ω ≤ J u ω)
    (hdeath : ∀ u,
      (fun ω => q * (J u ω : ℝ)) ≤ᵐ[μ]
        μ[fun ω => if J (u + 1) ω < J u ω then (1 : ℝ) else 0 | ℱ u])
    (t : ℕ) :
    (∫ ω, (J (t + 1) ω : ℝ) ∂μ) ≤
      (1 - q) * ∫ ω, (J t ω : ℝ) ∂μ := by
  let X : ℕ → Ω → ℝ := fun u ω => (J u ω : ℝ)
  let D : Ω → ℝ :=
    fun ω => if J (t + 1) ω < J t ω then 1 else 0
  have hXsm (u : ℕ) : StronglyMeasurable[ℱ u] (X u) :=
    ((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp
      (hJ u).measurable).stronglyMeasurable
  have hXint (u : ℕ) : Integrable (X u) μ :=
    natCast_integrable_of_bound J M u hJ hbound
  have hDsm : StronglyMeasurable[ℱ (t + 1)] D :=
    ((measurable_of_countable
      (fun p : ℕ × ℕ => if p.1 < p.2 then (1 : ℝ) else 0)).comp
        ((hJ (t + 1)).measurable.prodMk
          ((hJ t).mono (ℱ.mono (Nat.le_succ t))).measurable)).stronglyMeasurable
  have hDint : Integrable D μ := by
    refine (integrable_const (1 : ℝ)).mono'
      (hDsm.mono (ℱ.le (t + 1))).aestronglyMeasurable ?_
    exact ae_of_all μ fun ω => by
      dsimp [D]
      split_ifs <;> norm_num
  have hpoint : X (t + 1) ≤ᵐ[μ] X t - D := by
    filter_upwards [hmono t] with ω hω
    by_cases hd : J (t + 1) ω < J t ω
    · simp only [Pi.sub_apply, X, D, if_pos hd]
      have hn : J (t + 1) ω + 1 ≤ J t ω := by omega
      have hn' : (J (t + 1) ω : ℝ) + 1 ≤ (J t ω : ℝ) := by
        exact_mod_cast hn
      linarith
    · simp only [Pi.sub_apply, X, D, if_neg hd, sub_zero]
      exact_mod_cast hω
  have hce :
      μ[X (t + 1) | ℱ t] ≤ᵐ[μ]
        μ[X t - D | ℱ t] :=
    condExp_mono (hXint (t + 1)) ((hXint t).sub hDint) hpoint
  have hlinear :
      μ[X t - D | ℱ t] =ᵐ[μ]
        X t - μ[D | ℱ t] := by
    have hsub := condExp_sub (hXint t) hDint (ℱ t)
    have hfixed :=
      condExp_of_stronglyMeasurable (ℱ.le t) (hXsm t) (hXint t)
    filter_upwards [hsub] with ω hsubω
    simp only [Pi.sub_apply] at hsubω ⊢
    rw [hsubω, hfixed]
  have hdeath' :
      (fun ω => q * X t ω) ≤ᵐ[μ] μ[D | ℱ t] := by
    simpa only [X, D] using hdeath t
  have hcontract :
      μ[X (t + 1) | ℱ t] ≤ᵐ[μ]
        fun ω => (1 - q) * X t ω := by
    filter_upwards [hce, hlinear, hdeath'] with ω hceω hlinearω hdeathω
    rw [hlinearω] at hceω
    calc
      μ[X (t + 1) | ℱ t] ω ≤
          X t ω - μ[D | ℱ t] ω := hceω
      _ ≤ X t ω - q * X t ω := sub_le_sub_left hdeathω _
      _ = (1 - q) * X t ω := by ring
  calc
    (∫ ω, X (t + 1) ω ∂μ) =
        ∫ ω, μ[X (t + 1) | ℱ t] ω ∂μ :=
      (integral_condExp (ℱ.le t)).symm
    _ ≤ ∫ ω, (1 - q) * X t ω ∂μ :=
      integral_mono_ae integrable_condExp
        ((hXint t).const_mul (1 - q)) hcontract
    _ = (1 - q) * ∫ ω, X t ω ∂μ := by
      rw [integral_const_mul]

/-- Iterated first-moment contraction. -/
theorem adapted_death_mean
    (J : ℕ → Ω → ℕ) (M : ℕ) (q : ℝ)
    (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hJ : ∀ u, StronglyMeasurable[ℱ u] (J u))
    (hbound : ∀ u, ∀ᵐ ω ∂μ, J u ω ≤ M)
    (hmono : ∀ u, ∀ᵐ ω ∂μ, J (u + 1) ω ≤ J u ω)
    (hdeath : ∀ u,
      (fun ω => q * (J u ω : ℝ)) ≤ᵐ[μ]
        μ[fun ω => if J (u + 1) ω < J u ω then (1 : ℝ) else 0 | ℱ u])
    (T : ℕ) :
    (∫ ω, (J T ω : ℝ) ∂μ) ≤ (M : ℝ) * (1 - q) ^ T := by
  induction T with
  | zero =>
      have hleft := natCast_integrable_of_bound J M 0 hJ hbound
      calc
        (∫ ω, (J 0 ω : ℝ) ∂μ) ≤ ∫ _ : Ω, (M : ℝ) ∂μ := by
          refine integral_mono_ae hleft (integrable_const _) ?_
          filter_upwards [hbound 0] with ω hω
          exact_mod_cast hω
        _ = (M : ℝ) * (1 - q) ^ 0 := by simp
  | succ T ih =>
      calc
        (∫ ω, (J (T + 1) ω : ℝ) ∂μ) ≤
            (1 - q) * ∫ ω, (J T ω : ℝ) ∂μ :=
          adapted_death_mean_step J M q hJ hbound hmono hdeath T
        _ ≤ (1 - q) * ((M : ℝ) * (1 - q) ^ T) :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hqone)
        _ = (M : ℝ) * (1 - q) ^ (T + 1) := by
          rw [pow_succ]
          ring

/-- Extinction form of N07.  This is the interface needed for the last
unsampled Reserve: `Pr(J_T > 0) ≤ M exp(-qT)`. -/
theorem adapted_death_extinction_tail
    (J : ℕ → Ω → ℕ) (M : ℕ) (q : ℝ)
    (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hJ : ∀ u, StronglyMeasurable[ℱ u] (J u))
    (hbound : ∀ u, ∀ᵐ ω ∂μ, J u ω ≤ M)
    (hmono : ∀ u, ∀ᵐ ω ∂μ, J (u + 1) ω ≤ J u ω)
    (hdeath : ∀ u,
      (fun ω => q * (J u ω : ℝ)) ≤ᵐ[μ]
        μ[fun ω => if J (u + 1) ω < J u ω then (1 : ℝ) else 0 | ℱ u])
    (T : ℕ) :
    μ.real {ω | 1 ≤ J T ω} ≤
      (M : ℝ) * Real.exp (-q * T) := by
  have hmean := adapted_death_mean J M q hq hqone
    hJ hbound hmono hdeath T
  have hInt := natCast_integrable_of_bound J M T hJ hbound
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => Nat.cast_nonneg (J T ω)) hInt (1 : ℝ)
  have hprob :
      μ.real {ω | 1 ≤ J T ω} ≤
        ∫ ω, (J T ω : ℝ) ∂μ := by
    have hevent :
        {ω | (1 : ℝ) ≤ (J T ω : ℝ)} = {ω | 1 ≤ J T ω} := by
      ext ω
      exact_mod_cast Iff.rfl
    simpa only [one_mul, hevent] using hmarkov
  have hgeom : (1 - q) ^ T ≤ Real.exp (-q * T) := by
    have hbase : 1 - q ≤ Real.exp (-q) := by
      linarith [Real.add_one_le_exp (-q)]
    calc
      (1 - q) ^ T ≤ (Real.exp (-q)) ^ T :=
        pow_le_pow_left₀ (sub_nonneg.mpr hqone) hbase T
      _ = Real.exp (-q * T) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    μ.real {ω | 1 ≤ J T ω} ≤
        ∫ ω, (J T ω : ℝ) ∂μ := hprob
    _ ≤ (M : ℝ) * (1 - q) ^ T := hmean
    _ ≤ (M : ℝ) * Real.exp (-q * T) :=
      mul_le_mul_of_nonneg_left hgeom (Nat.cast_nonneg M)

variable {L K : ℕ}

/-- Joint killed-prefix failure event.  A gate failure is not counted as a
completion failure; it kills the process, so no future event is conditioned on. -/
def extinctionFailure (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M T : ℕ) : Set (TimeTheorem.Ω L K) :=
  {ω | DebtLive init s F A W M T ω ∧
    1 ≤ Nat.ceil (F (trace init ω (s + T)) - A)}

theorem measurableSet_extinctionFailure (init : Cfg L K) (s : ℕ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M T : ℕ) :
    MeasurableSet (extinctionFailure init s F A W M T) := by
  have hlarge : MeasurableSet[pairLogFiltration L K (s + T)]
      {ω | 1 ≤ Nat.ceil (F (trace init ω (s + T)) - A)} :=
    (Set.to_countable
      {c : Cfg L K | 1 ≤ Nat.ceil (F c - A)}).measurableSet.preimage
        (measurable_trace_at init (s + T))
  exact (pairLogFiltration L K).le (s + T) _
    ((measurableSet_debtLive init s F A W M T).inter hlarge)

open Classical in
/-- Local extinction tail for the existing killed debt process. -/
theorem stoppedDebt_extinction_tail
    (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M : ℕ) (q : ℝ) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      q * (Nat.ceil (F c - A) : ℝ) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) :
    (recordedFuture init s p).real
      (extinctionFailure init s F A W M T) ≤
        (M : ℝ) * Real.exp (-q * T) := by
  have htail := adapted_death_extinction_tail
    (μ := recordedFuture init s p) (ℱ := shiftedPairLog L K s)
    (stoppedDebt init s F A W M) M q hq hqone
    (stoppedDebt_stronglyMeasurable init s F A W M)
    (fun t => ae_of_all _ fun ω => stoppedDebt_le init s F A W M hmono t ω)
    (fun t => ae_of_all _ fun ω => stoppedDebt_mono init s F A W M hmono t ω)
    (stoppedDebt_conditional_death init s p F A W M q hservice) T
  refine (measureReal_mono ?_).trans htail
  rintro ω ⟨hlive, hpositive⟩
  show 1 ≤ stoppedDebt init s F A W M T ω
  unfold stoppedDebt
  rw [if_pos hlive]
  exact hpositive

open Classical in
/-- ENNReal form under one recorded continuation. -/
theorem recorded_extinction_tail
    (init : Cfg L K) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L K)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M : ℕ) (q : ℝ) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      q * (Nat.ceil (F c - A) : ℝ) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) :
    recordedFuture init s p (extinctionFailure init s F A W M T) ≤
      ENNReal.ofReal ((M : ℝ) * Real.exp (-q * T)) := by
  have hreal := stoppedDebt_extinction_tail init s p F A W M q
    hq hqone hmono hservice T
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] using hcast

open Classical in
/-- Original-law splice over a genuine pair-log stopping time. -/
theorem extinction_tail_at_pastTime
    (init : Cfg L K) (τ : TimeTheorem.Ω L K → WithTop ℕ) (hτ : PairLogPastTime τ)
    (F : Cfg L K → ℚ) (A : ℚ) (W : Cfg L K → Prop)
    (M : ℕ) (q : ℝ) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hmono : ∀ c, W c → ∀ d, W (applyDraw c d) →
      F (applyDraw c d) ≤ F c)
    (hservice : ∀ c, W c →
      q * (Nat.ceil (F c - A) : ℝ) ≤
        ∫ d, (if ¬ W (applyDraw c d) ∨ F (applyDraw c d) + 1 ≤ F c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure)
    (T : ℕ) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ extinctionFailure init s F A W M T} ≤
      ENNReal.ofReal ((M : ℝ) * Real.exp (-q * T)) :=
  law_at_past_time_bound init τ hτ
    (fun s => extinctionFailure init s F A W M T)
    (fun s => measurableSet_extinctionFailure init s F A W M T) _
    (fun s p => recorded_extinction_tail init s p F A W M q
      hq hqone hmono hservice T)

end Ripple.PopulationProtocol.ExactMajority.LateCompletionDeathTail

end
