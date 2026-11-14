-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseNineContinuationBits.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseNineBitProtocol
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseNineBitAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.WindowConcentration

/-!
A quantitative upper passage estimate for all three opinion bits.
The reciprocal deficit contracts by 1-1/n even from a single carrier.
Backup entry is a completed state of each stopped epidemic.  All
probability estimates below use the original law or its genuine kernel.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseNineContinuationBits

open TimeTheorem PairLog AdvanceEpidemics UniformRecovery
  PhaseNineBitProtocol PhaseNineBitAlgebra

variable {L K : ℕ}

open Classical in
private theorem two_level_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (f : X → ℝ≥0∞)
    (a z p : ℝ) (ha : 0 ≤ a) (haz : a ≤ z)
    (hprob : ENNReal.ofReal p ≤ μ E)
    (hpoint : ∀ᵐ x ∂μ, f x ≤ if x ∈ E then ENNReal.ofReal a else ENNReal.ofReal z) :
    ∫⁻ x, f x ∂μ ≤ ENNReal.ofReal (z - p * (z - a)) := by
  have hz : 0 ≤ z := ha.trans haz
  have hqle : μ E ≤ 1 := by
    calc
      μ E ≤ μ Set.univ := measure_mono (Set.subset_univ E)
      _ = 1 := measure_univ
  have hqtop : μ E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hqle
  let q := (μ E).toReal
  have hqnonneg : 0 ≤ q := ENNReal.toReal_nonneg
  have hqone : q ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hqle
    simpa only [ENNReal.toReal_one] using h
  have hq : μ E = ENNReal.ofReal q := (ENNReal.ofReal_toReal hqtop).symm
  have hpq : p ≤ q := by
    apply (ENNReal.ofReal_le_ofReal_iff hqnonneg).mp
    simpa only [← hq] using hprob
  have hqc : μ Eᶜ = ENNReal.ofReal (1 - q) := by
    rw [measure_compl hE hqtop, measure_univ, hq,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub 1 hqnonneg]
  calc
    _ ≤ ∫⁻ x, (if x ∈ E then ENNReal.ofReal a else ENNReal.ofReal z) ∂μ :=
      lintegral_mono_ae hpoint
    _ = (∫⁻ x in E, ENNReal.ofReal a ∂μ) +
        (∫⁻ x in Eᶜ, ENNReal.ofReal z ∂μ) := by
      rw [← lintegral_add_compl _ hE]
      congr 1
      · apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hE] with x hx
        simp only [if_pos hx]
      · apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hE.compl] with x hx
        simp only [Set.mem_compl_iff] at hx
        simp only [if_neg hx]
    _ = ENNReal.ofReal a * μ E + ENNReal.ofReal z * μ Eᶜ := by
      rw [lintegral_const, Measure.restrict_apply_univ,
        lintegral_const, Measure.restrict_apply_univ]
    _ = ENNReal.ofReal (a * q + z * (1 - q)) := by
      rw [hq, hqc, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hz,
        ← ENNReal.ofReal_add (mul_nonneg ha hqnonneg)
          (mul_nonneg hz (by linarith))]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h := mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr haz)
      nlinarith only [h]

private theorem support_ae (c : Cfg L K) (P : Cfg L K → Prop)
    (h : ∀ d ∈ ((NonuniformMajority L K).stepDistOrSelf c).support, P d) :
    ∀ᵐ d ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, P d := by
  rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
  intro d hd hnot
  exact hnot (h d hd)

def bitPotential (b : Fin 3) (n : ℕ) (c : Cfg L K) : ℝ≥0∞ :=
  ENNReal.ofReal (reciprocalDeficit n (infectionCount b n c))

open Classical in
def windowPotential (b : Fin 3) (n : ℕ) (c : Cfg L K) : ℝ≥0∞ :=
  if allPhaseGe 9 n c then bitPotential b n c else ⊤

theorem bitPotential_drift (b : Fin 3) (n : ℕ) (hn : 2 ≤ n)
    (c : Cfg L K) (hc : allPhaseGe 9 n c) :
    ∫⁻ d, bitPotential b n d ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - 1 / (n : ℝ)) * bitPotential b n c := by
  classical
  letI : IsProbabilityMeasure ((NonuniformMajority L K).stepDistOrSelf c).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  change ∫⁻ d, bitPotential b n d
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  have himax := infectionCount_le b n c hc.1
  by_cases hzero : infectionCount b n c = 0
  · have hnext : ∀ᵐ d ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        bitPotential b n d = 0 := by
      apply support_ae
      intro d hd
      rcases step_support_zero b n c d hc hzero hd with hz | hf
      · simp only [bitPotential, hz, reciprocalDeficit_zero, ENNReal.ofReal_zero]
      · simp only [bitPotential, hf, reciprocalDeficit_full, ENNReal.ofReal_zero]
    rw [show (∫⁻ d, bitPotential b n d
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) = 0 from
      (lintegral_eq_zero_iff (Measurable.of_discrete)).2 hnext]
    exact zero_le
  by_cases hfull : infectionCount b n c = n
  · have hnext : ∀ᵐ d ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        bitPotential b n d = 0 := by
      apply support_ae
      intro d hd
      have hlo := step_support_mono b n c d hc hd
      have hhi := infectionCount_le b n d (allPhaseGe_absorbing 9 n c d hc hd).1
      have heq : infectionCount b n d = n := by omega
      simp only [bitPotential, heq, reciprocalDeficit_full, ENNReal.ofReal_zero]
    rw [show (∫⁻ d, bitPotential b n d
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) = 0 from
      (lintegral_eq_zero_iff (Measurable.of_discrete)).2 hnext]
    exact zero_le
  have hi : 1 ≤ infectionCount b n c := by omega
  have hilt : infectionCount b n c < n := by omega
  let i := infectionCount b n c
  have hile : i + 1 ≤ n := by dsimp [i]; omega
  let E : Set (Cfg L K) := {d | i + 1 ≤ infectionCount b n d}
  have hprob : ENNReal.ofReal (bitRiseRate n i) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure E := by
    have h := bit_advance_probability b n hn c hc hilt
    simpa only [bitRiseRate, i, E, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub hilt.le] using h
  have hpoint : ∀ᵐ d ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
      bitPotential b n d ≤
        if d ∈ E then ENNReal.ofReal (reciprocalDeficit n (i + 1))
        else ENNReal.ofReal (reciprocalDeficit n i) := by
    apply support_ae
    intro d hd
    have hmax := infectionCount_le b n d (allPhaseGe_absorbing 9 n c d hc hd).1
    have hmono := step_support_mono b n c d hc hd
    by_cases hE : d ∈ E
    · rw [if_pos hE]
      exact ENNReal.ofReal_le_ofReal
        (reciprocalDeficit_antitone n (i + 1) (infectionCount b n d)
          hn (by omega) hE hmax)
    · rw [if_neg hE]
      exact ENNReal.ofReal_le_ofReal
        (reciprocalDeficit_antitone n i (infectionCount b n d) hn hi hmono hmax)
  have hz := reciprocalDeficit_nonneg n (i + 1) hn hile
  have haz := reciprocalDeficit_antitone n i (i + 1) hn hi
    (Nat.le_succ i) hile
  have hmain := two_level_integral
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure E
    (DiscreteMeasurableSpace.forall_measurableSet _)
    (bitPotential b n)
    (reciprocalDeficit n (i + 1)) (reciprocalDeficit n i) (bitRiseRate n i)
    hz haz hprob (by
      filter_upwards [hpoint] with d hd
      by_cases hE : d ∈ E
      · simpa only [if_pos hE] using hd
      · simpa only [if_neg hE] using hd)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) := by
    have hdiv : 1 / (n : ℝ) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    linarith
  calc
    _ ≤ ENNReal.ofReal (reciprocalDeficit n i -
        bitRiseRate n i * (reciprocalDeficit n i - reciprocalDeficit n (i + 1))) :=
      hmain
    _ ≤ ENNReal.ofReal ((1 - 1 / (n : ℝ)) * reciprocalDeficit n i) :=
      ENNReal.ofReal_le_ofReal (reciprocalDeficit_step n i hn hi hilt)
    _ = _ := by rw [ENNReal.ofReal_mul hbase]; rfl

theorem windowPotential_drift (b : Fin 3) (n : ℕ) (hn : 2 ≤ n)
    (c : Cfg L K) (hc : allPhaseGe 9 n c) :
    ∫⁻ d, windowPotential b n d ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - 1 / (n : ℝ)) * windowPotential b n c := by
  classical
  have heq : (∫⁻ d, windowPotential b n d
      ∂((NonuniformMajority L K).transitionKernel c)) =
      ∫⁻ d, bitPotential b n d ∂((NonuniformMajority L K).transitionKernel c) := by
    apply lintegral_congr_ae
    apply support_ae
    intro d hd
    simp only [windowPotential, if_pos (allPhaseGe_absorbing 9 n c d hc hd)]
  rw [heq, windowPotential, if_pos hc]
  exact bitPotential_drift b n hn c hc

theorem bit_kernel_tail (b : Fin 3) (n : ℕ) (hn : 2 ≤ n)
    (c : Cfg L K) (hc : allPhaseGe 9 n c) :
    ((NonuniformMajority L K).transitionKernel ^ logWindow n 12) c
      {d | 1 ≤ windowPotential b n d} ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 10) := by
  have ht := WindowConcentration.measure_ge_thresh_on_absorbing
    (NonuniformMajority L K) (windowPotential b n) (Measurable.of_discrete)
    (allPhaseGe 9 n) (allPhaseGe_absorbing 9 n)
    (ENNReal.ofReal (1 - 1 / (n : ℝ)))
    (windowPotential_drift b n hn)
    (logWindow n 12) c hc 1 one_ne_zero ENNReal.one_ne_top
  rw [div_one] at ht
  have hinit : windowPotential b n c ≤ ENNReal.ofReal ((n : ℝ) ^ 2) := by
    classical
    rw [windowPotential, if_pos hc]
    exact ENNReal.ofReal_le_ofReal
      (reciprocalDeficit_le_square n (infectionCount b n c) hn
        (infectionCount_le b n c hc.1))
  exact ht.trans ((mul_le_mul_left' hinit _).trans (reciprocal_tail_calibration n hn))

private theorem three_bit_budget (n : ℕ) (hn : 2 ≤ n) :
    (∑' _ : Fin 3, ENNReal.ofReal (1 / (n : ℝ) ^ 10)) ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) := by
  have hnonneg : 0 ≤ 1 / (n : ℝ) ^ 10 := by positivity
  rw [tsum_fintype]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rw [← ENNReal.ofReal_add hnonneg hnonneg,
    ← ENNReal.ofReal_add hnonneg (add_nonneg hnonneg hnonneg)]
  apply ENNReal.ofReal_le_ofReal
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hpow : 1 ≤ (n : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  have hten : (n : ℝ) ^ 10 = ((n : ℝ) ^ 5) ^ 2 := by ring
  calc
    1 / (n : ℝ) ^ 10 + (1 / (n : ℝ) ^ 10 + 1 / (n : ℝ) ^ 10) =
        3 / (n : ℝ) ^ 10 := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (pow_pos hp _) (pow_pos hp _)).2
      rw [hten]
      nlinarith only [hpow, sq_nonneg ((n : ℝ) ^ 5 - 1)]

theorem phase_nine_uniform_kernel_tail (n : ℕ) (hn : 2 ≤ n)
    (c : Cfg L K) (hc : allPhaseGe 9 n c) :
    ((NonuniformMajority L K).transitionKernel ^ logWindow n 12) c
      {d | ¬ Backup d ∧ ¬ UniformOpinions d} ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) := by
  classical
  have hsub : {d : Cfg L K | ¬ Backup d ∧ ¬ UniformOpinions d} ⊆
      ⋃ b : Fin 3, {d | 1 ≤ windowPotential b n d} := by
    intro d hd
    by_cases hQ : allPhaseGe 9 n d
    · obtain ⟨b, hbpos, hblt⟩ :=
        nonuniform_has_partial_bit n (by omega) d hQ.1 hd.1 hd.2
      apply Set.mem_iUnion.mpr
      refine ⟨b, ?_⟩
      change 1 ≤ windowPotential b n d
      rw [windowPotential, if_pos hQ]
      change 1 ≤ ENNReal.ofReal (reciprocalDeficit n (infectionCount b n d))
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (reciprocalDeficit_one_le n _ hn hbpos hblt)
    · apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      change 1 ≤ windowPotential 0 n d
      simp only [windowPotential, if_neg hQ, le_top]
  calc
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ logWindow n 12) c
        (⋃ b : Fin 3, {d | 1 ≤ windowPotential b n d}) := measure_mono hsub
    _ ≤ ∑' b : Fin 3, ((NonuniformMajority L K).transitionKernel ^ logWindow n 12) c
        {d | 1 ≤ windowPotential b n d} := measure_iUnion_le _
    _ ≤ ∑' _ : Fin 3, ENNReal.ofReal (1 / (n : ℝ) ^ 10) :=
      ENNReal.tsum_le_tsum (fun b => bit_kernel_tail b n hn c hc)
    _ ≤ _ := three_bit_budget n hn

/-- The observed prefix is the only restriction on the scheduler law. -/
theorem phase_nine_uniform_prefix_tail (init : Cfg L K) {n : ℕ}
    (hn : 2 ≤ n) (s : ℕ)
    (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ a ∈ A, (prefixCfg init s a).card = n ∧
      UniformRecovery.PurePhase 9 (prefixCfg init s a)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
      (¬ (∃ a ∈ trace init ω (s + logWindow n 12), 10 ≤ a.phase.val) ∧
        ¬ UniformRecovery.UniformOpinions (trace init ω (s + logWindow n 12)))} ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  apply PhaseTwoThresholds.recorded_prefix_endpoint_bound
    init s (logWindow n 12) A {d | ¬ Backup d ∧ ¬ UniformOpinions d}
    (ENNReal.ofReal (6 / (n : ℝ) ^ 5))
  intro a ha
  exact phase_nine_uniform_kernel_tail n hn _ ⟨(hA a ha).1,
    fun d hd => le_of_eq ((hA a ha).2 d hd).symm⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseNineContinuationBits

end
