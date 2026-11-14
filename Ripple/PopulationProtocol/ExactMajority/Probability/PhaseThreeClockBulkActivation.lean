-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockBulkActivation.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSharpActivation
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinningCalibrated

/-!
Actual macroscopic activation from a first bulk front, in 20*m raw
interactions.  A smaller exponential tilt than the paper uses is enough
at the compiled population threshold and reuses the proved waiting-product
process without introducing an independent geometric sequence.

The tail below is on the original pair-log law at an observed prefix.
It does not assume any future lower-passage, no-backup or hour event.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBulkActivation

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockActivationLaw PhaseThreeClockActivationCalibration
  PhaseThreeClockSharpActivation PhaseThreeModel.Numeric

variable {L K m : ℕ}

noncomputable def bulkActivationLaunch (m : ℕ) : ℕ :=
  Nat.ceil ((3 : ℝ) * (m : ℝ) / 125)

theorem bulkActivationLaunch_pos (m : ℕ) (hm : 200 ≤ m) :
    1 ≤ bulkActivationLaunch m := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hceil : (3 : ℝ) * (m : ℝ) / 125 ≤ (bulkActivationLaunch m : ℝ) :=
    Nat.le_ceil _
  have h : (1 : ℝ) ≤ (bulkActivationLaunch m : ℝ) := by linarith
  exact_mod_cast h

theorem bulkActivationLaunch_le_macro (m : ℕ) :
    bulkActivationLaunch m ≤ macroThreshold m := by
  apply Nat.ceil_mono
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem bulkActivationLaunch_mean (m : ℕ) (hm : 200 ≤ m) :
    (∑ j ∈ Finset.Ico (bulkActivationLaunch m) (macroThreshold m),
      1 / activationProbability m j) ≤ 6 * (m : ℝ) := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hr := bulkActivationLaunch_pos m hm
  have hrp : (0 : ℝ) < (bulkActivationLaunch m : ℝ) := by
    exact_mod_cast (show 0 < bulkActivationLaunch m by omega)
  have hceil : (3 : ℝ) * (m : ℝ) / 125 ≤ (bulkActivationLaunch m : ℝ) :=
    Nat.le_ceil _
  have hratio : (m : ℝ) / (bulkActivationLaunch m : ℝ) ≤ 125 / 3 := by
    apply (div_le_iff₀ hrp).2
    linarith
  have hlog := Real.log_le_log (div_pos hmp hrp) hratio
  rw [Real.log_div (ne_of_gt hmp) (ne_of_gt hrp)] at hlog
  have hmean := activation_mean_log_bound m (bulkActivationLaunch m)
    (macroThreshold m) hr (bulkActivationLaunch_le_macro m)
    (macroThreshold_le_population m) (macroThreshold_gap m)
  have hbar :
      Real.log (m : ℝ) - Real.log (bulkActivationLaunch m : ℝ) +
        Real.log (100 : ℝ) + 2 ≤ 12 := by
    have hs := log_small_bounds
    linarith only [hlog, hs.2.1, hs.2.2]
  have hmul := mul_le_mul_of_nonneg_left hbar
    (show (0 : ℝ) ≤ (m : ℝ) / 2 by positivity)
  linarith only [hmean, hmul]

theorem bulkActivationLaunch_probability_floor (m j : ℕ)
    (hm : 200 ≤ m) (hj : j ∈ Finset.Ico (bulkActivationLaunch m) (macroThreshold m)) :
    (1 / 200 : ℝ) ≤ activationProbability m j := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  let r := Nat.floor ((m : ℝ) / 100)
  have hrhi : (r : ℝ) ≤ (m : ℝ) / 100 := Nat.floor_le (by positivity)
  have hrlo : (m : ℝ) / 100 - 1 < (r : ℝ) := Nat.sub_one_lt_floor _
  have hlaunch : (3 : ℝ) * (m : ℝ) / 125 ≤ (bulkActivationLaunch m : ℝ) :=
    Nat.le_ceil _
  obtain ⟨hrj, hjb⟩ := Finset.mem_Ico.mp hj
  have hrjR : (bulkActivationLaunch m : ℝ) ≤ j := by exact_mod_cast hrj
  have hrj' : r ≤ j := by
    have h : (r : ℝ) ≤ j := by linarith
    exact_mod_cast h
  have hp := activation_probability_floor_aux m r j (by omega) hrhi hrj' hjb
  have hf : (1 / 200 : ℝ) ≤ (r : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmp).2
    linarith
  exact hf.trans hp

/-- The 20*m activation endpoint estimate, with its actual transition
law discharged by the existing waiting-product martingale. -/
theorem bulk_activation_prefix_tail (init : Cfg L K) (hm : 200 ≤ init.card)
    (u : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K u] E)
    (hstart : ∀ ω ∈ E, bulkActivationLaunch init.card ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)) :
    law init (E ∩ {ω |
      PhaseThreeClockActivationLaw.activeCount
        (virtualLabels init ω (u + 20 * init.card)) < macroThreshold init.card}) ≤
      ENNReal.ofReal (Real.exp (-(init.card : ℝ) / 20000)) * law init E := by
  have hp (j : ℕ) (hj : j ∈ Finset.Ico (bulkActivationLaunch init.card)
      (macroThreshold init.card)) :
      0 < activationProbability init.card j ∧
        (1 / 200000 : ℝ) / activationProbability init.card j ≤ 1 / 1000 := by
    have hf := bulkActivationLaunch_probability_floor init.card j hm hj
    have hpos : 0 < activationProbability init.card j :=
      lt_of_lt_of_le (by norm_num) hf
    refine ⟨hpos, (div_le_iff₀ hpos).2 ?_⟩
    linarith
  have ht := activation_prefix_exponential_tail init (by omega) u
    (bulkActivationLaunch init.card) (macroThreshold init.card) (20 * init.card)
    (1 / 200000 : ℝ) (bulkActivationLaunch_le_macro init.card) (by norm_num)
    (fun j hj => (hp j hj).1) (fun j hj => (hp j hj).2) E hE hstart
  apply ht.trans
  apply mul_le_mul_right'
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hmean := bulkActivationLaunch_mean init.card hm
  have hnonneg : (0 : ℝ) ≤ init.card := Nat.cast_nonneg _
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hmean, hnonneg]

theorem positive_front_le_activeCount (f : Fin m → AgentState L K)
    (ell : ℕ) (hell : 1 ≤ ell) :
    frontCount f ell ≤ PhaseThreeClockActivationLaw.activeCount f := by
  classical
  unfold frontCount PhaseThreeClockActivationLaw.activeCount
  apply Finset.card_le_card
  intro i hi
  simp only [aboveSet, activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  by_contra h
  have hz : effMinute (f i) = 0 := by simp only [effMinute, if_neg h]
  rw [hz] at hi
  omega

theorem bulkActivationLaunch_le_bulk (m C : ℕ)
    (hdensity : (6 / 25 : ℝ) * (m : ℝ) ≤ (C : ℝ)) :
    bulkActivationLaunch m ≤ StageEventSpec.bulkThreshold C := by
  apply Nat.ceil_mono
  linarith

theorem active_launch_of_bulk (f : Fin m → AgentState L K) (C ell : ℕ)
    (hell : 1 ≤ ell) (hdensity : (6 / 25 : ℝ) * (m : ℝ) ≤ (C : ℝ))
    (hbulk : StageEventSpec.bulkThreshold C ≤ frontCount f ell) :
    bulkActivationLaunch m ≤ PhaseThreeClockActivationLaw.activeCount f :=
  (bulkActivationLaunch_le_bulk m C hdensity).trans
    (hbulk.trans (positive_front_le_activeCount f ell hell))

/-- Both elementary errors used in P9a fit below C^(-101).
The spare power absorbs their sum. -/
theorem bulk_activation_error_calibration (m C : ℕ)
    (hm : populationThreshold ≤ m)
    (hdensity : (6 / 25 : ℝ) * (m : ℝ) ≤ (C : ℝ))
    (hCm : C ≤ m) :
    200 ≤ m ∧ 2 ≤ C ∧
      Real.exp (-(m : ℝ) / 20000) ≤ 1 / (C : ℝ) ^ 101 ∧
      Real.exp (-(19 / 90 : ℝ) * (C : ℝ)) ≤ 1 / (C : ℝ) ^ 101 := by
  obtain ⟨hCp, hx, -, -, -⟩ := logarithmic_inputs hm hdensity hCm
  have hlinear := (elementary_power_calibration hCp hx).2.2.2.2.1
  rw [Real.exp_log hCp] at hlinear
  have hCmR : (C : ℝ) ≤ m := by exact_mod_cast hCm
  have hCtwo : 2 ≤ C := by
    have h : (2 : ℝ) ≤ C := by linarith
    exact_mod_cast h
  have hmlarge : 200 ≤ m := by
    have h : (200 : ℝ) ≤ m := by linarith
    exact_mod_cast h
  have hexp :
      Real.exp (-(101 * Real.log (C : ℝ))) = 1 / (C : ℝ) ^ 101 := by
    rw [Real.exp_neg, show (101 : ℝ) * Real.log (C : ℝ) = ((101 : ℕ) : ℝ) * Real.log (C : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hCp, one_div]
  refine ⟨hmlarge, hCtwo, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(101 * Real.log (C : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := hexp
  · calc
      _ ≤ Real.exp (-(101 * Real.log (C : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := hexp

theorem two_spare_powers_le (C : ℕ) (hC : 2 ≤ C) :
    1 / (C : ℝ) ^ 101 + 1 / (C : ℝ) ^ 101 ≤ 1 / (C : ℝ) ^ 100 := by
  have hCR : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hCp : (0 : ℝ) < C := by linarith
  have hpow : 2 * (C : ℝ) ^ 100 ≤ (C : ℝ) ^ 101 := by
    rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left hCR
      (pow_nonneg hCp.le 100)]
  have hdiv : (2 : ℝ) / (C : ℝ) ^ 101 ≤ 1 / (C : ℝ) ^ 100 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    simpa only [one_mul] using hpow
  calc
    1 / (C : ℝ) ^ 101 + 1 / (C : ℝ) ^ 101 = 2 / (C : ℝ) ^ 101 := by ring
    _ ≤ _ := hdiv

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBulkActivation

end
