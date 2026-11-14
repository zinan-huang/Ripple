-- Ripple/Kurtz/StrongApprox/DyadicEntropyCommonLevel.lean
import Ripple.Kurtz.StrongApprox.BrownianEntropyMomentVariable
import Ripple.Kurtz.StrongApprox.AllTimeKurtzMoment

/-!
# One entropy level for all channels and dyadic horizons

Brownian modulus input of Kurtz 1978, Lemma 3.2 (p. 231) and Theorem 3.3(a)
(p. 232): the random variable `M_l` of the paper (the Brownian modulus of the
driver `W_l` over the clock horizon) is replaced by the entropy level of
`BrownianEntropyMomentVariable`, shifted by the horizon price so that one
variable serves all horizons.

Subtracting `(j + 1) log 2` from the entropy level at horizon `2 ^ j`
makes the horizon union bound summable. The resulting extended random variable
has exponential tail with prefactor equal to the number of channels. Its real
projection has an exponential moment, and on one full-measure event it controls
the entropy modulus on every dyadic horizon simultaneously.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- The logarithmic price paid for including the `j`th dyadic horizon. -/
def dyadicEntropyPenalty (j : ℕ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) * Real.log 2

theorem dyadicEntropyPenalty_nonneg (j : ℕ) :
    0 ≤ dyadicEntropyPenalty j := by
  unfold dyadicEntropyPenalty
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))

/-- A common extended level; the finite channel set may be empty. -/
def dyadicEntropyCommonLevel (W : ι → ℝ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ l : ι, ⨆ j : ℕ,
    ENNReal.ofReal ((brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω).toReal -
      dyadicEntropyPenalty j)

/-- The totalized real projection, assigned zero when the extended level is infinite. -/
def dyadicEntropyCommonReal (W : ι → ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  (dyadicEntropyCommonLevel W ω).toReal

theorem measurable_dyadicEntropyCommonLevel
    {W : ι → ℝ → Ω → ℝ} (hW : ∀ l t, Measurable (W l t)) :
    Measurable (dyadicEntropyCommonLevel W) := by
  classical
  exact Measurable.iSup fun l => Measurable.iSup fun j =>
    (((measurable_brownianEntropyLevel (hW l) ((2 : ℝ) ^ j)).ennreal_toReal).sub
      measurable_const).ennreal_ofReal

theorem measurable_dyadicEntropyCommonReal
    {W : ι → ℝ → Ω → ℝ} (hW : ∀ l t, Measurable (W l t)) :
    Measurable (dyadicEntropyCommonReal W) :=
  (measurable_dyadicEntropyCommonLevel hW).ennreal_toReal

theorem dyadicEntropyCommonReal_nonneg (W : ι → ℝ → Ω → ℝ) (ω : Ω) :
    0 ≤ dyadicEntropyCommonReal W ω := ENNReal.toReal_nonneg

private theorem dyadicEntropy_geometric_sum :
    ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) = 1 := by
  have h : ∀ j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) =
      (1 / 2 : ℝ≥0∞) ^ (j + 1) := by
    intro j
    rw [ENNReal.ofReal_pow (by norm_num)]
    congr 1
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  simp_rw [h]
  simp only [pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_div,
    ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- The sharp union-bound prefactor is the number of channels; no independence is used. -/
theorem law_dyadicEntropyCommonLevel_gt
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → ℝ → Ω → ℝ}
    (hW : ∀ l j, DyadicBrownianOn P (W l) ((2 : ℝ) ^ (j : ℕ)))
    {x : ℝ} (hx : 0 ≤ x) :
    P {ω | ENNReal.ofReal x < dyadicEntropyCommonLevel W ω} ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Real.exp (-x)) := by
  classical
  let E : ι → ℕ → Set Ω := fun l j =>
    {ω | ENNReal.ofReal x < ENNReal.ofReal
      ((brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω).toReal -
        dyadicEntropyPenalty j)}
  have hsub : {ω | ENNReal.ofReal x < dyadicEntropyCommonLevel W ω} ⊆
      ⋃ l : ι, ⋃ j : ℕ, E l j := by
    intro ω hω
    change ENNReal.ofReal x < ⨆ l : ι, ⨆ j : ℕ,
      ENNReal.ofReal ((brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω).toReal -
        dyadicEntropyPenalty j) at hω
    rw [lt_iSup_iff] at hω
    obtain ⟨l, hl⟩ := hω
    rw [lt_iSup_iff] at hl
    obtain ⟨j, hj⟩ := hl
    exact mem_iUnion.mpr ⟨l, mem_iUnion.mpr ⟨j, hj⟩⟩
  have hterm : ∀ l j, P (E l j) ≤ ENNReal.ofReal (Real.exp (-x)) *
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) := by
    intro l j
    have hp := dyadicEntropyPenalty_nonneg j
    have hsubset : E l j ⊆ {ω | ENNReal.ofReal (x + dyadicEntropyPenalty j) <
        brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω} := by
      intro ω hω
      have hr : x < (brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω).toReal -
          dyadicEntropyPenalty j :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx).mp hω
      have hne : brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω ≠ ⊤ := by
        intro htop
        rw [htop] at hr
        simp only [ENNReal.toReal_top, zero_sub] at hr
        linarith
      calc
        ENNReal.ofReal (x + dyadicEntropyPenalty j) < ENNReal.ofReal
            (brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (add_nonneg hx hp)).mpr (by linarith)
        _ = brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω :=
          ENNReal.ofReal_toReal hne
    have he : Real.exp (-(x + dyadicEntropyPenalty j)) =
        Real.exp (-x) * (1 / 2 : ℝ) ^ (j + 1) := by
      rw [neg_add, Real.exp_add]
      congr 1
      exact AllTimeKurtzMoment.exp_neg_nat_mul_log_two (j + 1)
    calc
      P (E l j) ≤ P {ω | ENNReal.ofReal (x + dyadicEntropyPenalty j) <
          brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω} := measure_mono hsubset
      _ ≤ ENNReal.ofReal (Real.exp (-(x + dyadicEntropyPenalty j))) :=
        law_brownianEntropyLevel_gt (pow_pos (by norm_num) j)
          (add_nonneg hx hp) (hW l j)
      _ = _ := by rw [he, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  calc
    P {ω | ENNReal.ofReal x < dyadicEntropyCommonLevel W ω} ≤
        P (⋃ l : ι, ⋃ j : ℕ, E l j) := measure_mono hsub
    _ ≤ ∑' l : ι, P (⋃ j : ℕ, E l j) := measure_iUnion_le _
    _ ≤ ∑' l : ι, ∑' j : ℕ, ENNReal.ofReal (Real.exp (-x)) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 1)) := by
      apply ENNReal.tsum_le_tsum
      intro l
      exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (hterm l))
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * Real.exp (-x)) := by
      simp only [ENNReal.tsum_mul_left, dyadicEntropy_geometric_sum, mul_one,
        tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp

/-- A measurable common level is almost surely finite. -/
theorem dyadicEntropyCommonLevel_ae_ne_top
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → ℝ → Ω → ℝ}
    (hW : ∀ l j, DyadicBrownianOn P (W l) ((2 : ℝ) ^ (j : ℕ))) :
    ∀ᵐ ω ∂P, dyadicEntropyCommonLevel W ω ≠ ⊤ := by
  have hle : ∀ n : ℕ, P {ω | dyadicEntropyCommonLevel W ω = ⊤} ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * Real.exp (-(n : ℝ))) := by
    intro n
    refine (measure_mono ?_).trans
      (law_dyadicEntropyCommonLevel_gt hW (Nat.cast_nonneg n))
    intro ω hω
    change ENNReal.ofReal (n : ℝ) < dyadicEntropyCommonLevel W ω
    rw [hω]
    exact ENNReal.ofReal_lt_top
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
      ((Fintype.card ι : ℝ) * Real.exp (-(n : ℝ)))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa using ENNReal.tendsto_ofReal (h.const_mul (Fintype.card ι : ℝ))
  have hzero : P {ω | dyadicEntropyCommonLevel W ω = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto' hlim hle) bot_le
  rw [ae_iff]
  simpa using hzero

/-- Exponential moment of the common real level for every parameter in `(0,1)`. -/
theorem lintegral_exp_dyadicEntropyCommonReal_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → ℝ → Ω → ℝ}
    (hW : ∀ l j, DyadicBrownianOn P (W l) ((2 : ℝ) ^ (j : ℕ)))
    {θ : ℝ} (hθ : 0 < θ) (hθone : θ < 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * dyadicEntropyCommonReal W ω)) ∂P ≤
      ENNReal.ofReal (1 + (Fintype.card ι : ℝ) * θ / (1 - θ)) := by
  refine AllTimeKurtzMoment.lintegral_exp_le_of_tail
    (measurable_dyadicEntropyCommonReal fun l => (hW l 0).eval_measurable)
    (dyadicEntropyCommonReal_nonneg W) (Nat.cast_nonneg _) hθ hθone ?_
  intro t ht
  have hsub : {ω | t < dyadicEntropyCommonReal W ω} ⊆
      {ω | ENNReal.ofReal t < dyadicEntropyCommonLevel W ω} := by
    intro ω hω
    have hne : dyadicEntropyCommonLevel W ω ≠ ⊤ := by
      intro htop
      change t < (dyadicEntropyCommonLevel W ω).toReal at hω
      rw [htop] at hω
      simp only [ENNReal.toReal_top] at hω
      exact (not_lt_of_ge ht.le) hω
    calc
      ENNReal.ofReal t < ENNReal.ofReal (dyadicEntropyCommonLevel W ω).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hω
      _ = dyadicEntropyCommonLevel W ω := ENNReal.ofReal_toReal hne
  simpa only [one_mul] using
    (measure_mono hsub).trans (law_dyadicEntropyCommonLevel_gt hW ht.le)

/-- Real integral and integrability, rather than merely a bound on a totalized integral. -/
theorem integral_exp_dyadicEntropyCommonReal_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → ℝ → Ω → ℝ}
    (hW : ∀ l j, DyadicBrownianOn P (W l) ((2 : ℝ) ^ (j : ℕ)))
    {θ : ℝ} (hθ : 0 < θ) (hθone : θ < 1) :
    Integrable (fun ω => Real.exp (θ * dyadicEntropyCommonReal W ω)) P ∧
      ∫ ω, Real.exp (θ * dyadicEntropyCommonReal W ω) ∂P ≤
        1 + (Fintype.card ι : ℝ) * θ / (1 - θ) := by
  have hm : Measurable (fun ω => Real.exp (θ * dyadicEntropyCommonReal W ω)) :=
    Real.measurable_exp.comp (measurable_const.mul
      (measurable_dyadicEntropyCommonReal fun l => (hW l 0).eval_measurable))
  have hn : 0 ≤ᵐ[P] (fun ω => Real.exp (θ * dyadicEntropyCommonReal W ω)) :=
    Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hb := lintegral_exp_dyadicEntropyCommonReal_le hW hθ hθone
  have hi : Integrable (fun ω => Real.exp (θ * dyadicEntropyCommonReal W ω)) P :=
    ⟨hm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal _ hb
  have hc : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hd : 0 < 1 - θ := by linarith
  positivity

/-- Every dyadic level is bounded by the common real level plus its horizon penalty. -/
theorem brownianEntropyLevel_toReal_le_common
    (W : ι → ℝ → Ω → ℝ) {ω : Ω}
    (hfinite : dyadicEntropyCommonLevel W ω ≠ ⊤) (l : ι) (j : ℕ) :
    (brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω).toReal ≤
      dyadicEntropyCommonReal W ω + dyadicEntropyPenalty j := by
  have hle : ENNReal.ofReal
      ((brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω).toReal -
        dyadicEntropyPenalty j) ≤ dyadicEntropyCommonLevel W ω :=
    le_iSup_of_le l (le_iSup_of_le j le_rfl)
  have hr := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hle
  change (brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω).toReal -
    dyadicEntropyPenalty j ≤ dyadicEntropyCommonReal W ω at hr
  linarith

/-- Pointwise consequence on the common event of finite levels and continuous paths. -/
theorem brownianEntropyBound_of_commonLevel
    {W : ι → ℝ → Ω → ℝ} {ω : Ω}
    (hfinite : dyadicEntropyCommonLevel W ω ≠ ⊤)
    (hlevels : ∀ l j, brownianEntropyLevel (W l) ((2 : ℝ) ^ (j : ℕ)) ω ≠ ⊤)
    (hcont : ∀ l, Continuous (fun t => W l t ω)) :
    ∀ l j, ∀ u ∈ Icc (0 : ℝ) ((2 : ℝ) ^ (j : ℕ)),
      ∀ v ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j),
      |W l u ω - W l v ω| ≤ brownianEntropyBound ((2 : ℝ) ^ j)
        (2 + dyadicEntropyCommonReal W ω + dyadicEntropyPenalty j) |u - v| := by
  intro l j
  have ha : 2 ≤ 2 + dyadicEntropyCommonReal W ω + dyadicEntropyPenalty j := by
    linarith [dyadicEntropyCommonReal_nonneg W ω, dyadicEntropyPenalty_nonneg j]
  have hlt : brownianEntropyLevel (W l) ((2 : ℝ) ^ j) ω < ENNReal.ofReal
      (2 + dyadicEntropyCommonReal W ω + dyadicEntropyPenalty j) := by
    rw [← ENNReal.ofReal_toReal (hlevels l j)]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr
    linarith [brownianEntropyLevel_toReal_le_common W hfinite l j]
  simpa only [max_eq_left ha] using
    brownianEntropyLevel_pathwise (pow_pos (by norm_num) j) (hcont l) hlt

/-- One full-measure event supports every channel, horizon and pair of real times. -/
theorem brownianEntropyBound_of_commonLevel_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → ℝ → Ω → ℝ}
    (hW : ∀ l j, DyadicBrownianOn P (W l) ((2 : ℝ) ^ (j : ℕ))) :
    ∀ᵐ ω ∂P, dyadicEntropyCommonLevel W ω ≠ ⊤ ∧
      (∀ l j, brownianEntropyLevel (W l) ((2 : ℝ) ^ (j : ℕ)) ω ≠ ⊤) ∧
      (∀ l, Continuous (fun t => W l t ω)) ∧
      ∀ l j, ∀ u ∈ Icc (0 : ℝ) ((2 : ℝ) ^ (j : ℕ)),
        ∀ v ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j),
        |W l u ω - W l v ω| ≤ brownianEntropyBound ((2 : ℝ) ^ j)
          (2 + dyadicEntropyCommonReal W ω + dyadicEntropyPenalty j) |u - v| := by
  have hl : ∀ᵐ ω ∂P, ∀ l j,
      brownianEntropyLevel (W l) ((2 : ℝ) ^ (j : ℕ)) ω ≠ ⊤ := by
    apply ae_all_iff.mpr
    intro l
    apply ae_all_iff.mpr
    intro j
    exact brownianEntropyLevel_ae_ne_top (pow_pos (by norm_num) j) (hW l j)
  have hc : ∀ᵐ ω ∂P, ∀ l, Continuous (fun t => W l t ω) :=
    ae_all_iff.mpr fun l => (hW l 0).continuous_ae
  filter_upwards [dyadicEntropyCommonLevel_ae_ne_top hW, hl, hc] with ω hω hlω hcω
  exact ⟨hω, hlω, hcω, brownianEntropyBound_of_commonLevel hω hlω hcω⟩


end Ripple.Kurtz.StrongApprox

end
