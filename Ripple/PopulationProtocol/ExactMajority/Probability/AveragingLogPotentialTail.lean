-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingLogPotentialTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCompensatedLog
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingPotentialDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingNumerics
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedSplice

/-!
# The compensated logarithmic tail for the actual augmented potential

The gate below consists of current configuration facts. Its drift is proved
from the implemented transition and the two-orientation ready-zero rectangle.
There is no conditional-drift or supermartingale assumption in the tail theorem.
The underlying measure is the ordinary continuation of a recorded pair-log prefix.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingLogPotentialTail

open TimeTheorem PairLog PhaseOneDrain
open AveragingIntegerPotential AveragingPotentialService AveragingPotentialDrift
open AveragingRecordedExpectation AveragingCompensatedLog AveragingNumerics

variable {L : ℕ}

theorem augmentedPhiNat_draw_integral_drift (h : ℕ) (hh : 1 ≤ h)
    (c : Cfg L 256) (hn : 2 ≤ c.card) (hc : PotentialDomain c) :
    (∫ d, (augmentedPhiNat h (applyDraw c d) : ℝ) ∂(drawLaw c).toMeasure) ≤
      (1 - (readyRate h c).toReal) * (augmentedPhiNat h c : ℝ) := by
  have hmap :
      (∫⁻ d, (augmentedPhiNat h (applyDraw c d) : ℝ≥0∞)
        ∂(drawLaw c).toMeasure) =
      ∫⁻ c', (augmentedPhiNat h c' : ℝ≥0∞)
        ∂(NonuniformMajority L 256).transitionKernel c := by
    rw [← drawLaw_map_toMeasure c,
      lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  have hfinite :
      (1 - readyRate h c) * (augmentedPhiNat h c : ℝ≥0∞) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    · exact ENNReal.natCast_ne_top _
  have hreal := ENNReal.toReal_mono hfinite
    (augmentedPhiNat_kernel_drift h hh c hn hc)
  have hcast :
      (∫ d, (augmentedPhiNat h (applyDraw c d) : ℝ) ∂(drawLaw c).toMeasure) =
      (∫⁻ d, (augmentedPhiNat h (applyDraw c d) : ℝ≥0∞)
        ∂(drawLaw c).toMeasure).toReal := by
    simpa only [ENNReal.toReal_natCast] using
      (integral_toReal
        (measurable_of_countable
          (fun d : Draw L 256 =>
            (augmentedPhiNat h (applyDraw c d) : ℝ≥0∞))).aemeasurable
        (ae_of_all (drawLaw c).toMeasure
          (fun d => ENNReal.natCast_lt_top (augmentedPhiNat h (applyDraw c d)))))
  rw [hcast, hmap]
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le (readyRate_le_one h c hn) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_natCast] using hreal

structure LogGate (n M h : ℕ) (c : Cfg L 256) : Prop where
  domain : PotentialDomain c
  population : c.card = n
  ready_floor : (17 / 100 : ℝ) * (M : ℝ) ≤ (readyZeroCount h c : ℝ)
  atom_pair : ∀ s ∈ c, ∀ t ∈ c,
    (augmentedAgentPhiNat h s : ℝ) + (augmentedAgentPhiNat h t : ℝ) ≤ atomBound n

theorem readyRate_lower {n M h : ℕ} (hn : 2 ≤ n)
    (c : Cfg L 256) (hc : LogGate n M h c) :
    potentialDrift n M ≤ (readyRate h c).toReal := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : (c.totalPairs : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    simp only [Config.totalPairs, hc.population, Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdenpos : (0 : ℝ) < c.totalPairs := by
    rw [hden]
    exact mul_pos hnpos (by linarith only [hnreal])
  have hdensmall : (c.totalPairs : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [hden]
    nlinarith only [hnpos]
  calc
    potentialDrift n M = ((17 / 100 : ℝ) * M) / (n : ℝ) ^ 2 := rfl
    _ ≤ (readyZeroCount h c : ℝ) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hc.ready_floor (sq_nonneg _)
    _ ≤ (readyZeroCount h c : ℝ) / (c.totalPairs : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdenpos hdensmall
    _ = (readyRate h c).toReal := by
      simp only [readyRate, ENNReal.toReal_div, ENNReal.toReal_natCast]

theorem actual_potential_draw_drop {n M h : ℕ} (hh : 1 ≤ h)
    (c : Cfg L 256) (hc : LogGate n M h c)
    (hn : 0 < (n : ℝ)) (d : Draw L 256) :
    (augmentedPhiNat h c : ℝ) -
      (augmentedPhiNat h (applyDraw c d) : ℝ) ≤ atomBound n := by
  classical
  cases d with
  | none => simpa only [applyDraw, sub_self] using atomBound_nonneg hn
  | some p =>
      let s := p.1.1
      let t := p.2.1
      change (augmentedPhiNat h c : ℝ) -
        (augmentedPhiNat h
          (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) : ℝ) ≤ _
      by_cases happ : Protocol.Applicable c s t
      · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
        have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
        have hmono := phiNat_step_le h hh c hc.domain s t
        have hdrop := phiNat_step_drop_le_pair h c s t happ
        have hcast :
            (augmentedPhiNat h c : ℝ) -
                (augmentedPhiNat h
                  (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) : ℝ) ≤
              (augmentedAgentPhiNat h s : ℝ) + (augmentedAgentPhiNat h t : ℝ) := by
          have hncast :
              ((augmentedPhiNat h c -
                augmentedPhiNat h
                  (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) : ℕ) : ℝ) ≤
                ((augmentedAgentPhiNat h s + augmentedAgentPhiNat h t : ℕ) : ℝ) := by
            exact_mod_cast hdrop
          simpa only [Nat.cast_sub hmono, Nat.cast_add] using hncast
        exact hcast.trans (hc.atom_pair s hs t ht)
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ, sub_self]
        exact atomBound_nonneg hn

/-- The full next-step drift is derived before any exit increment is replaced. -/
theorem actual_logControl {n M h : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) (hMn : M ≤ n)
    (hh : 1 ≤ h) (G : ℕ → Cfg L 256 → Prop)
    (hgate : ∀ t c, G t c → LogGate n M h c) :
    LogControl (augmentedPhiNat h) G (potentialTarget M)
      (potentialDrift n M) (logJumpBound n) (atomBound n) := by
  have hnpos := (population_log_lower hn).1
  have hnNat : 0 < n := by exact_mod_cast hnpos
  have hnlarge : 40 ≤ n := (time_population_bounds hn).2
  have hM : 0 < M := by omega
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  refine
    { threshold_pos := by unfold potentialTarget; positivity
      rate_nonneg := by unfold potentialDrift; positivity
      radius_nonneg := (logJumpBound_pos hnNat).le
      drop_nonneg := atomBound_nonneg hnpos
      drop_small := atomBound_le_half_target hn hmain
      radius_bound := compensated_jump_bound hn hmain hMn
      potential_mono := ?_
      drop_bound := ?_
      full_drift := ?_ }
  · intro t c hg d
    exact phiNat_draw_le h hh c (hgate t c hg).domain d
  · intro t c hg d
    exact actual_potential_draw_drop hh c (hgate t c hg) hnpos d
  · intro t c hg
    have hc := hgate t c hg
    have hcard : 2 ≤ c.card := by rw [hc.population]; omega
    exact (augmentedPhiNat_draw_integral_drift h hh c hcard hc.domain).trans
      (mul_le_mul_of_nonneg_right
        (sub_le_sub_left (readyRate_lower (by omega) c hc) 1)
        (Nat.cast_nonneg _))

theorem actual_logarithmic_survival_tail {n M h : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) (hMn : M ≤ n)
    (hh : 1 ≤ h) (init : Cfg L 256) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L 256)
    (G : ℕ → Cfg L 256 → Prop) (hgate : ∀ t c, G t c → LogGate n M h c) :
    Ripple.Probability.prob (recordedFuture init s p)
      {ω | Alive init s (augmentedPhiNat h) G (potentialTarget M)
          (potentialTrials n M) ω ∧
        (augmentedPhiNat h (trace init ω s) : ℝ) ≤ (103 / 250 : ℝ) * M} ≤
      1 / (n : ℝ) ^ 20 := by
  have hnpos := (population_log_lower hn).1
  have hnNat : 0 < n := by exact_mod_cast hnpos
  have hM : 0 < M := by omega
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hratio : ((103 / 250 : ℝ) * M) / potentialTarget M = 412 := by
    unfold potentialTarget
    field_simp [ne_of_gt hMreal]
    <;> ring
  have hnum : (3 : ℝ) ≤
      potentialDrift n M * potentialTrials n M -
        Real.log (((103 / 250 : ℝ) * M) / potentialTarget M) := by
    rw [hratio]
    exact (compensated_work_exceeds_three hnNat hM).le
  have htail := logarithmic_survival_tail init s p (augmentedPhiNat h) G
    (potentialTarget M) (potentialDrift n M) (logJumpBound n) (atomBound n)
    (actual_logControl hn hmain hMn hh G hgate)
    ((103 / 250 : ℝ) * M) (by positivity) 3 (by norm_num)
    (potentialTrials n M) hnum
  have hscalar := freedman_tail_le_inverse_power
    (N := potentialTrials n M) hn (potentialTrials_le (by omega) hmain)
  have hden :
      Real.exp (-((3 : ℝ) ^ 2) /
        (2 * ((potentialTrials n M : ℝ) * logJumpBound n ^ 2 +
          2 * logJumpBound n * 3 / 3))) =
      Real.exp (-9 /
        (2 * ((potentialTrials n M : ℝ) * logJumpBound n ^ 2 +
          2 * logJumpBound n))) := by congr 1 <;> ring
  rw [hden] at htail
  exact htail.trans hscalar


def LogSurvival (init : Cfg L 256) (s n M h : ℕ)
    (G : ℕ → Cfg L 256 → Prop) : Set (Ω L 256) :=
  {ω | Alive init s (augmentedPhiNat h) G (potentialTarget M)
      (potentialTrials n M) ω ∧
    (augmentedPhiNat h (trace init ω s) : ℝ) ≤ (103 / 250 : ℝ) * M}

theorem logSurvival_measurable (init : Cfg L 256) (s n M h : ℕ)
    (G : ℕ → Cfg L 256 → Prop) :
    MeasurableSet (LogSurvival init s n M h G) := by
  have halive : MeasurableSet
      {ω | Alive init s (augmentedPhiNat h) G (potentialTarget M)
        (potentialTrials n M) ω} := by
    have heq :
        {ω | Alive init s (augmentedPhiNat h) G (potentialTarget M)
          (potentialTrials n M) ω} =
        (frestrictLe (π := fun _ : ℕ => Draw L 256) (s + potentialTrials n M)) ⁻¹'
          {p | prefixAlive init s (augmentedPhiNat h) G (potentialTarget M)
            (potentialTrials n M) p} := by
      ext ω
      exact (prefixAlive_frestrict_iff init s (augmentedPhiNat h) G
        (potentialTarget M) (potentialTrials n M) ω).symm
    rw [heq]
    exact (Set.to_countable _).measurableSet.preimage
      (measurable_frestrictLe (X := fun _ : ℕ => Draw L 256) _)
  have hstart : MeasurableSet
      {ω | (augmentedPhiNat h (trace init ω s) : ℝ) ≤ (103 / 250 : ℝ) * M} :=
    (Set.to_countable {c : Cfg L 256 |
      (augmentedPhiNat h c : ℝ) ≤ (103 / 250 : ℝ) * M}).measurableSet.preimage
        ((measurable_pi_apply s).comp (measurable_trace init))
  exact halive.inter hstart

theorem actual_logarithmic_survival_ennreal {n M h : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) (hMn : M ≤ n)
    (hh : 1 ≤ h) (init : Cfg L 256) (s : ℕ)
    (p : (i : Finset.Iic s) → Draw L 256)
    (G : ℕ → Cfg L 256 → Prop) (hgate : ∀ t c, G t c → LogGate n M h c) :
    recordedFuture init s p (LogSurvival init s n M h G) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) := by
  have htail := actual_logarithmic_survival_tail hn hmain hMn hh init s p G hgate
  change (recordedFuture init s p (LogSurvival init s n M h G)).toReal ≤ _ at htail
  rw [← ENNReal.ofReal_toReal
    (measure_ne_top (recordedFuture init s p) (LogSurvival init s n M h G))]
  exact ENNReal.ofReal_le_ofReal htail

/-- A joint event under the original law, with an arbitrary event in the
recorded past. The local failure cost is multiplied by its prefix mass. -/
theorem actual_logarithmic_survival_from_prefix {n M h : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) (hMn : M ≤ n)
    (hh : 1 ≤ h) (init : Cfg L 256) (s : ℕ)
    (A : Set ((i : Finset.Iic s) → Draw L 256))
    (G : ℕ → Cfg L 256 → Prop) (hgate : ∀ t c, G t c → LogGate n M h c) :
    law init {ω |
      frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A ∧
        ω ∈ LogSurvival init s n M h G} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} :=
  AveragingRecordedSplice.law_prefix_joint_bound init s A
    (LogSurvival init s n M h G) (logSurvival_measurable init s n M h G) _
    (fun p _ => actual_logarithmic_survival_ennreal hn hmain hMn hh init s p G hgate)

/-- The same local logarithmic estimate at an arbitrary pair-log stopping
time. The gates and the target are tested on the actual stopped trace. -/
theorem actual_logarithmic_survival_at_past_time {n M h : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) (hMn : M ≤ n)
    (hh : 1 ≤ h) (init : Cfg L 256)
    (σ : Ω L 256 → WithTop ℕ) (hσ : PairLogPastTime σ)
    (G : ℕ → Cfg L 256 → Prop) (hgate : ∀ t c, G t c → LogGate n M h c) :
    law init {ω | ∃ s : ℕ, σ ω = (s : WithTop ℕ) ∧
      ω ∈ LogSurvival init s n M h G} ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 20) :=
  AveragingRecordedSplice.law_at_past_time_bound init σ hσ
    (fun s => LogSurvival init s n M h G)
    (fun s => logSurvival_measurable init s n M h G) _
    (fun s p => actual_logarithmic_survival_ennreal hn hmain hMn hh init s p G hgate)

end Ripple.PopulationProtocol.ExactMajority.AveragingLogPotentialTail

end
