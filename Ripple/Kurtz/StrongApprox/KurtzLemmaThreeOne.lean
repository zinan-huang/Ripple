-- Ripple/Kurtz/StrongApprox/KurtzLemmaThreeOne.lean
import Ripple.Kurtz.StrongApprox.AllTimeKMTPoissonLaw

/-!
# Kurtz 1978, Lemma 3.1, on the all-time space

T. G. Kurtz, "Strong approximation theorems for density dependent Markov
chains", Stochastic Process. Appl. 6 (1978), Lemma 3.1 (p. 230): *Let `B(t)` be
Brownian motion with `E B(t) = Var B(t) = t`.  Then a Poisson process `Y(t)`
can be constructed on the same sample space as `B(t)` so that
`sup_{t ≥ 0} |Y(t) - B(t)| / (log t ∨ 2) = K < ∞` a.s. and `E exp {λ K} < ∞`
for some `λ > 0`.*

Here the probability space is `allTimeKMTMeasure`, `B(t) = t + W(t)` with
`W = allTimeKMTBrownian` a standard Brownian motion on every dyadic horizon,
continuous for every sample, and `Y = allTimeKMTPoisson` a unit-rate Poisson
process (monotone, right continuous, unit jumps a.s., independent Poisson
increments over every finite grid).

Differences from the statement in the paper:

* The pair is constructed jointly on one space, in the form that Kurtz's
  Theorem 3.3 consumes ("Assume that `Y_l` and `B_l` satisfy the conclusion of
  Lemma 3.1").
* The Brownian clause is proved in the form `DyadicBrownianOn` on every
  horizon `2^N` together with continuity of every path; the finite-dimensional
  law at arbitrary real times follows from these two facts and is not
  restated.
* The variable `K` is dominated by the stronger variable
  `allTimeKMTXi = sup |Y - t - W| / log (max 2 t)`: since
  `log t ∨ 2 ≥ log (max 2 t)`, Kurtz's `K ≤ Ξ`, so the tail and the
  exponential moment of `Ξ` bound those of `K`.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.KurtzLemmaThreeOne

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology
open AllTimeKMT ContinuousFiniteHorizonKMT AllTimeKMTLaws AllTimeKMTBrownianLaw
open AllTimeKMTPoissonLaw AllTimeKurtzMoment

/-! ## The variable of Kurtz's Lemma 3.1 -/

/-- Kurtz's drifted Brownian motion `B(t) = t + W(t)`. -/
def allTimeKMTDriftedBrownian (t : ℝ) (ω : AllTimeKMTSpace) : ℝ :=
  t + allTimeKMTBrownian t ω

/-- Normalized error at time `t`, with the denominator `log t ∨ 2`. -/
def kurtzRatio (t : ℝ) (ω : AllTimeKMTSpace) : ℝ :=
  |(allTimeKMTPoisson t ω : ℝ) - allTimeKMTDriftedBrownian t ω| /
    max (Real.log t) 2

/-- `K = sup_{t ≥ 0} |Y(t) - B(t)| / (log t ∨ 2)`. -/
def kurtzLemmaThreeOneK (ω : AllTimeKMTSpace) : ℝ≥0∞ :=
  ⨆ t : {t : ℝ // 0 ≤ t}, ENNReal.ofReal (kurtzRatio t.1 ω)

theorem log_max_two_le_kurtz_denominator (t : ℝ) :
    Real.log (max 2 t) ≤ max (Real.log t) 2 := by
  rcases le_total t 2 with h | h
  · rw [max_eq_left h]
    have := Real.log_two_lt_d9
    exact le_trans (by linarith) (le_max_right _ _)
  · rw [max_eq_right h]
    exact le_max_left _ _

theorem kurtzLemmaThreeOneK_le_Xi (ω : AllTimeKMTSpace) :
    kurtzLemmaThreeOneK ω ≤ allTimeKMTXi ω := by
  rw [allTimeKMTXi_eq_real_sup]
  unfold kurtzLemmaThreeOneK allTimeKMTXiReal
  refine iSup_mono fun t => ENNReal.ofReal_le_ofReal ?_
  unfold kurtzRatio allTimeKMTRatio allTimeKMTDriftedBrownian
  have hpos : 0 < Real.log (max 2 t.1) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hnum : (allTimeKMTPoisson t.1 ω : ℝ) - (t.1 + allTimeKMTBrownian t.1 ω) =
      (allTimeKMTPoisson t.1 ω : ℝ) - t.1 - allTimeKMTBrownian t.1 ω := by ring
  rw [hnum]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hpos
    (log_max_two_le_kurtz_denominator t.1)

/-! ## Measurability -/

theorem iSup_real_eq_iSup_rat (f : ℝ → ℝ)
    (hrc : ∀ t, 0 ≤ t → ContinuousWithinAt f (Ici t) t) :
    (⨆ t : {t : ℝ // 0 ≤ t}, ENNReal.ofReal (f t.1)) =
      ⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (f (q.1 : ℝ)) := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    by_contra hlt
    have hlt' : (⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (f (q.1 : ℝ))) <
        ENNReal.ofReal (f t.1) := lt_of_not_ge hlt
    have hne : (⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (f (q.1 : ℝ))) ≠ ⊤ :=
      ne_top_of_lt hlt'
    have hm : (⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (f (q.1 : ℝ))).toReal <
        f t.1 := (ENNReal.lt_ofReal_iff_toReal_lt hne).mp hlt'
    have hrat : ∀ q : ℚ, 0 ≤ q → f (q : ℝ) ≤
        (⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (f (q.1 : ℝ))).toReal := by
      intro q hq
      have h1 : ENNReal.ofReal (f (q : ℝ)) ≤
          ⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (f (q.1 : ℝ)) :=
        le_iSup (fun r : {r : ℚ // 0 ≤ r} => ENNReal.ofReal (f (r.1 : ℝ)))
          ⟨q, hq⟩
      exact (ENNReal.ofReal_le_iff_le_toReal hne).mp h1
    have hcont := hrc t.1 t.2
    have hev : ∀ᶠ s in nhdsWithin t.1 (Ici t.1),
        (⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (f (q.1 : ℝ))).toReal < f s :=
      hcont.eventually (lt_mem_nhds hm)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t.1 < t.1 + ε by linarith)
    have hq0 : 0 ≤ q := by
      have : (0 : ℝ) ≤ q := le_trans t.2 hq1.le
      exact_mod_cast this
    have hdist : dist (q : ℝ) t.1 < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hgt := hball hdist (mem_Ici.mpr hq1.le)
    exact absurd (hrat q hq0) (not_le.mpr hgt)
  · refine iSup_le fun q => ?_
    exact le_iSup (fun t : {t : ℝ // 0 ≤ t} => ENNReal.ofReal (f t.1))
      ⟨(q.1 : ℝ), by exact_mod_cast q.2⟩

theorem max_log_two_eq_log_max {t : ℝ} (ht : 0 ≤ t) :
    max (Real.log t) 2 = Real.log (max t (Real.exp 2)) := by
  rcases le_total t (Real.exp 2) with h | h
  · rw [max_eq_right h, Real.log_exp]
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [← h0]; simp
    · have : Real.log t ≤ 2 := by
        calc Real.log t ≤ Real.log (Real.exp 2) :=
              Real.log_le_log h0 h
          _ = 2 := Real.log_exp 2
      exact max_eq_right this
  · rw [max_eq_left h]
    have : 2 ≤ Real.log t := by
      calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 2) h
    exact max_eq_left this

theorem kurtzRatio_rightContinuous (ω : AllTimeKMTSpace) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousWithinAt (fun s => kurtzRatio s ω) (Ici t) t := by
  have hnum : ContinuousWithinAt (fun s : ℝ =>
      |(allTimeKMTPoisson s ω : ℝ) - allTimeKMTDriftedBrownian s ω|)
      (Ici t) t := by
    have h := continuous_abs.continuousAt.comp_continuousWithinAt
      (allTimeKMTError_rightContinuous ω ht)
    refine h.congr (fun s _ => ?_) ?_
    · simp only [Function.comp, allTimeKMTDriftedBrownian]
      congr 1
      ring
    · simp only [Function.comp, allTimeKMTDriftedBrownian]
      congr 1
      ring
  have hD : Continuous (fun s : ℝ => Real.log (max s (Real.exp 2))) :=
    Continuous.log (continuous_id.max continuous_const)
      (fun s => (lt_of_lt_of_le (Real.exp_pos 2) (le_max_right _ _)).ne')
  have hDpos : 0 < Real.log (max t (Real.exp 2)) :=
    Real.log_pos (lt_of_lt_of_le (by
      have := Real.add_one_le_exp (2 : ℝ); linarith) (le_max_right _ _))
  have hq := hnum.div hD.continuousWithinAt hDpos.ne'
  refine hq.congr (fun s hs => ?_) ?_
  · unfold kurtzRatio
    rw [max_log_two_eq_log_max (le_trans ht (mem_Ici.mp hs))]
    rfl
  · unfold kurtzRatio
    rw [max_log_two_eq_log_max ht]
    rfl

theorem kurtzLemmaThreeOneK_eq_rat (ω : AllTimeKMTSpace) :
    kurtzLemmaThreeOneK ω =
      ⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (kurtzRatio (q.1 : ℝ) ω) :=
  iSup_real_eq_iSup_rat (fun s => kurtzRatio s ω)
    (fun t ht => kurtzRatio_rightContinuous ω ht)

theorem measurable_kurtzRatio (t : ℝ) : Measurable (kurtzRatio t) := by
  unfold kurtzRatio allTimeKMTDriftedBrownian
  have h1 : Measurable fun ω : AllTimeKMTSpace =>
      (allTimeKMTPoisson t ω : ℝ) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
      (measurable_allTimeKMTPoisson t)
  exact (((h1.sub (measurable_const.add
    (measurable_allTimeKMTBrownian t))).abs)).div_const _

theorem measurable_kurtzLemmaThreeOneK : Measurable kurtzLemmaThreeOneK := by
  have : kurtzLemmaThreeOneK = fun ω =>
      ⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (kurtzRatio (q.1 : ℝ) ω) := by
    funext ω
    exact kurtzLemmaThreeOneK_eq_rat ω
  rw [this]
  exact Measurable.iSup fun _ => (measurable_kurtzRatio _).ennreal_ofReal

/-! ## Finiteness and exponential moment -/

theorem kurtzLemmaThreeOneK_ae_ne_top :
    ∀ᵐ ω ∂allTimeKMTMeasure, kurtzLemmaThreeOneK ω ≠ ⊤ := by
  filter_upwards [allTimeKMTXi_ae_ne_top] with ω hω
  exact ne_top_of_le_ne_top hω (kurtzLemmaThreeOneK_le_Xi ω)

theorem integrable_exp_kurtzLemmaThreeOneK {θ : ℝ} (hθ0 : 0 < θ)
    (hθγ : θ < allTimeKurtzGamma) :
    Integrable (fun ω => Real.exp (θ * (kurtzLemmaThreeOneK ω).toReal))
      allTimeKMTMeasure := by
  refine (integral_exp_allTimeKMTXi_le hθ0 hθγ).1.mono' ?_ ?_
  · exact (Real.measurable_exp.comp (measurable_const.mul
      measurable_kurtzLemmaThreeOneK.ennreal_toReal)).aestronglyMeasurable
  · filter_upwards [allTimeKMTXi_ae_ne_top] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hθ0.le
    exact ENNReal.toReal_mono hω (kurtzLemmaThreeOneK_le_Xi ω)

/-! ## The lemma -/

/-- **Kurtz 1978, Lemma 3.1**, on the all-time space `allTimeKMTMeasure`. -/
theorem kurtz_lemma_three_one :
    -- `W` is Brownian on every dyadic horizon, continuous for every sample
    (∀ N : ℕ, DyadicBrownianOn allTimeKMTMeasure
      (fun t ω => allTimeKMTBrownian t ω) ((2 : ℝ) ^ N)) ∧
    (∀ ω, Continuous (fun t => allTimeKMTBrownian t ω)) ∧
    -- `Y` is a unit-rate Poisson process
    (∀ ω s t, s ≤ t → allTimeKMTPoisson s ω ≤ allTimeKMTPoisson t ω) ∧
    (∀ ω t, ContinuousWithinAt (fun s => (allTimeKMTPoisson s ω : ℝ)) (Ici t) t) ∧
    (∀ᵐ ω ∂allTimeKMTMeasure, ∀ t : ℝ, 0 ≤ t →
      allTimeKMTPoisson t ω =
          allTimeKMTPoissonLeft t ω + allTimeKMTPoissonMultiplicity t ω ∧
        allTimeKMTPoissonMultiplicity t ω ≤ 1 ∧
        (0 < allTimeKMTPoisson t ω - allTimeKMTPoissonLeft t ω →
          allTimeKMTPoisson t ω - allTimeKMTPoissonLeft t ω = 1)) ∧
    (∀ {r : ℕ} (grid : Fin (r + 1) → ℝ), grid 0 = 0 → StrictMono grid →
      allTimeKMTMeasure.map (allTimeKMTPoissonIncrementVector grid) =
          DyadicConditionalPoissonPath.poissonIncrementProduct grid ∧
        iIndepFun (fun i ω => allTimeKMTPoissonIncrementVector grid ω i)
          allTimeKMTMeasure) ∧
    -- `K < ∞` a.s. with an exponential moment
    (∀ᵐ ω ∂allTimeKMTMeasure, kurtzLemmaThreeOneK ω ≠ ⊤) ∧
    (0 < allTimeKurtzGamma / 2 ∧
      Integrable (fun ω => Real.exp
        (allTimeKurtzGamma / 2 * (kurtzLemmaThreeOneK ω).toReal))
        allTimeKMTMeasure) := by
  have hg := allTimeKurtzGamma_pos
  refine ⟨allTimeKMTBrownian_dyadicBrownianOn, allTimeKMTBrownian_continuous,
    fun ω s t hst => allTimeKMTPoisson_mono ω hst,
    allTimeKMTPoisson_rightContinuous, allTimeKMTPoisson_unitJumps_ae,
    fun grid hz hs => ⟨allTimeKMTPoisson_incrementVector_law grid hz hs,
      allTimeKMTPoisson_increment_iIndep grid hz hs⟩,
    kurtzLemmaThreeOneK_ae_ne_top, by positivity,
    integrable_exp_kurtzLemmaThreeOneK (by positivity) (by linarith)⟩

end Ripple.Kurtz.StrongApprox.KurtzLemmaThreeOne

end
