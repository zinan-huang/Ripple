import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoHeightDomain
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoHeightMoments

/-!
# Concrete one-step activation-height growth

The selected Clock-class sum is evaluated under the actual ordered occurrence
scheduler. Both orientations and the C-1 exclusion are retained. The resulting
rate is at most 14/(25n), using the SeedProfile Clock density.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

open TimeTheorem PhaseTwoActivation PhaseTwoActivationLocal

variable {L : ℕ}

def clockPairBonus (s t : AgentState L 256) : ℝ≥0∞ :=
  if s.role = .clock ∧ t.role = .clock then
    (clockWeight s : ℝ≥0∞) + (clockWeight t : ℝ≥0∞) else 0

theorem killedPotential_step_le (n : ℕ) (c : Cfg L 256)
    (hc : HeightDomain n c) (hwindow : ¬ HeightBeforeBackup c)
    (s t : AgentState L 256) :
    killedPotential (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      killedPotential c + clockPairBonus s t := by
  classical
  have hadd : ∀ (r : Cfg L 256) (x y : AgentState L 256),
      clockPotential (r + {x, y}) =
        clockPotential r + ((clockWeight x : ℝ≥0∞) + (clockWeight y : ℝ≥0∞)) := by
    intro r x y
    simp only [clockPotential, Config.sumOf, Multiset.insert_eq_cons, Multiset.map_add,
      Multiset.sum_add, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton]
  by_cases hback : Backup c
  · have hnext := backup_step c s t hback
    simp only [killedPotential, if_pos hback, if_pos hnext, zero_add, zero_le]
  · by_cases hnext : Backup (Protocol.stepOrSelf (NonuniformMajority L 256) c s t)
    · simp only [killedPotential, if_pos hnext, if_neg hback, zero_le]
    · obtain ⟨hrange, _⟩ := hc.active.resolve_left hback
      have hheight : ¬ Height c := fun h => hwindow ⟨h, hback⟩
      have hlow := no_height_active_clock_below c hheight
      by_cases happ : Protocol.Applicable c s t
      · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
        have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
        have hstep : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
            c - {s, t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
          unfold Protocol.stepOrSelf
          rw [if_pos happ] <;> rfl
        have hlmem : (Transition L 256 s t).1 ∈
            Protocol.stepOrSelf (NonuniformMajority L 256) c s t := by
          rw [hstep]
          simp
        have hrmem : (Transition L 256 s t).2 ∈
            Protocol.stepOrSelf (NonuniformMajority L 256) c s t := by
          rw [hstep]
          simp
        have hno := (no_backup_iff _).mp hnext
        have hpairNat := transition_weight_pair_le s t (hrange s hs) (hrange t ht)
          (hlow s hs) (hlow t ht) (hno _ hlmem) (hno _ hrmem)
        have hpair :
            (clockWeight (Transition L 256 s t).1 : ℝ≥0∞) +
              (clockWeight (Transition L 256 s t).2 : ℝ≥0∞) ≤
            (clockWeight s : ℝ≥0∞) + (clockWeight t : ℝ≥0∞) +
              clockPairBonus s t := by
          by_cases hcc : s.role = .clock ∧ t.role = .clock
          · simp only [if_pos hcc] at hpairNat
            simp only [clockPairBonus, if_pos hcc]
            exact_mod_cast hpairNat
          · simp only [if_neg hcc, add_zero] at hpairNat
            simp only [clockPairBonus, if_neg hcc, add_zero]
            exact_mod_cast hpairNat
        have hbefore :
            clockPotential c = clockPotential (c - {s, t}) +
              ((clockWeight s : ℝ≥0∞) + (clockWeight t : ℝ≥0∞)) := by
          have h := hadd (c - {s, t}) s t
          rwa [Multiset.sub_add_cancel happ] at h
        have hafter :
            clockPotential (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) =
              clockPotential (c - {s, t}) +
                ((clockWeight (Transition L 256 s t).1 : ℝ≥0∞) +
                  (clockWeight (Transition L 256 s t).2 : ℝ≥0∞)) := by
          rw [hstep]
          exact hadd _ _ _
        simp only [killedPotential, if_neg hback, if_neg hnext]
        rw [hbefore, hafter]
        calc clockPotential (c - {s, t}) +
            ((clockWeight (Transition L 256 s t).1 : ℝ≥0∞) +
              (clockWeight (Transition L 256 s t).2 : ℝ≥0∞)) ≤
            clockPotential (c - {s, t}) +
              ((clockWeight s : ℝ≥0∞) + (clockWeight t : ℝ≥0∞) +
                clockPairBonus s t) := add_le_add le_rfl hpair
          _ = clockPotential (c - {s, t}) +
              ((clockWeight s : ℝ≥0∞) + (clockWeight t : ℝ≥0∞)) +
                clockPairBonus s t := (add_assoc _ _ _).symm
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
        exact le_add_of_nonneg_right zero_le

theorem clock_class_rate_le {n C : ℕ} (hn : 2 ≤ n) (hdensity : 25 * C ≤ 7 * n) :
    (2 * ((C - 1 : ℕ) : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (14 / (25 * (n : ℝ))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpred : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hden : (0 : ℝ) < (n : ℝ) * ((n - 1 : ℕ) : ℝ) := mul_pos hnpos hpred
  have hlinearNat : 25 * (C - 1) ≤ 7 * (n - 1) := by omega
  have hlinear : (25 : ℝ) * ((C - 1 : ℕ) : ℝ) ≤
      7 * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hlinearNat
  have hprod := mul_le_mul_of_nonneg_right hlinear hnpos.le
  have hreal :
      (2 * ((C - 1 : ℕ) : ℝ)) / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) ≤
        14 / (25 * (n : ℝ)) := by
    apply (div_le_div_iff₀ hden (by positivity)).2
    nlinarith only [hprod]
  have hnum :
      ENNReal.ofReal (2 * ((C - 1 : ℕ) : ℝ)) =
        2 * ((C - 1 : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hdenCast :
      ENNReal.ofReal ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) =
        (n : ℝ≥0∞) * ((n - 1 : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    simp
  calc (2 * ((C - 1 : ℕ) : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)) =
      ENNReal.ofReal
        ((2 * ((C - 1 : ℕ) : ℝ)) / ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) := by
        rw [ENNReal.ofReal_div_of_pos hden, hnum, hdenCast, Nat.cast_mul]
    _ ≤ ENNReal.ofReal (14 / (25 * (n : ℝ))) := ENNReal.ofReal_le_ofReal hreal

/-- Actual transition-kernel growth; no probabilistic hypothesis remains. -/
theorem killedPotential_drift {n : ℕ} (hn : 2 ≤ n) (c : Cfg L 256)
    (hc : HeightDomain n c) (hwindow : ¬ HeightBeforeBackup c) :
    ∫⁻ c', killedPotential c' ∂(NonuniformMajority L 256).transitionKernel c ≤
      heightRate n * killedPotential c := by
  classical
  have hcard : 2 ≤ c.card := by rw [hc.card_eq]; exact hn
  rw [Phase0Window.lintegral_transitionKernel_eq_sum
    (NonuniformMajority L 256) c hcard]
  by_cases hback : Backup c
  · have hzero (p : AgentState L 256 × AgentState L 256) :
        killedPotential (Protocol.stepOrSelf (NonuniformMajority L 256) c p.1 p.2) = 0 := by
      simp only [killedPotential, if_pos (backup_step c p.1 p.2 hback)]
    rw [Finset.sum_eq_zero (fun p _ => by rw [hzero p, zero_mul])]
    exact zero_le
  · have hdensity := (hc.active.resolve_left hback).2
    have hrate :
        2 * ((clockPopulation c - 1 : ℕ) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞) ≤
          ENNReal.ofReal (14 / (25 * (n : ℝ))) := by
      simpa only [Config.totalPairs, hc.card_eq] using clock_class_rate_le hn hdensity
    have hsumprob : (∑ p : AgentState L 256 × AgentState L 256,
        c.interactionProb p.1 p.2) = 1 := by
      have h := (c.interactionPMF hcard).tsum_coe
      rw [tsum_eq_sum (s := Finset.univ)
        (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at h
      convert h using 1
    have hbonus :
        (∑ p : AgentState L 256 × AgentState L 256,
          clockPairBonus p.1 p.2 * c.interactionProb p.1 p.2) =
        (2 * ((clockPopulation c - 1 : ℕ) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)) *
          clockPotential c := by
      exact selected_class_weight_sum c (fun a => a.role = .clock)
        (fun a => (clockWeight a : ℝ≥0∞)) (fun a ha => by
          simp only [clockWeight, if_neg ha, Nat.cast_zero])
    calc (∑ p : AgentState L 256 × AgentState L 256,
        killedPotential (Protocol.stepOrSelf (NonuniformMajority L 256) c p.1 p.2) *
          c.interactionProb p.1 p.2) ≤
        ∑ p : AgentState L 256 × AgentState L 256,
          (killedPotential c + clockPairBonus p.1 p.2) *
            c.interactionProb p.1 p.2 := by
          apply Finset.sum_le_sum
          intro p _
          exact mul_le_mul_right' (killedPotential_step_le n c hc hwindow p.1 p.2) _
      _ = killedPotential c +
          ∑ p : AgentState L 256 × AgentState L 256,
            clockPairBonus p.1 p.2 * c.interactionProb p.1 p.2 := by
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumprob, mul_one]
      _ = killedPotential c +
          (2 * ((clockPopulation c - 1 : ℕ) : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞)) *
            clockPotential c := by rw [hbonus]
      _ ≤ killedPotential c +
          ENNReal.ofReal (14 / (25 * (n : ℝ))) * clockPotential c :=
        add_le_add le_rfl (mul_le_mul_right' hrate _)
      _ = heightRate n * killedPotential c := by
        simp only [killedPotential, if_neg hback, heightRate, add_mul, one_mul]

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoHeight

end
