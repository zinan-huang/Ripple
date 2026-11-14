-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingProtectedCap.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingPotentialDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingNumerics
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeAveragingStops
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTieReadout

/-!
# Extinction during the protected cap interval

The gate tests only the current actual configuration. A cap checkpoint with
integer potential at most M/1000, followed by the persistent .77 M ready-zero
floor, has extinction failure at most n^-4 after logWindow n 16 interactions.

The final joint-event theorem intersects this bound with the complete clock
history and failure of the literal tie readout. It does not condition on clock
success, and it does not assert that the hour induction has produced the gate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingProtectedCap

open TimeTheorem StageEventSpec PairLog PhaseOneDrain PhaseThreeAveragingStops
open AveragingPotentialService AveragingPotentialDrift AveragingIntegerPotential
open AveragingNumerics AveragingTieReadout

variable {L n : ℕ}

def capRate (n M : ℕ) : ℝ :=
  (77 / 100 : ℝ) * (M : ℝ) / (n : ℝ) ^ 2

structure CapGate (n M h : ℕ) (c : Cfg L 256) : Prop where
  population : c.card = n
  domain : PotentialDomain c
  ready_floor : (77 / 100 : ℝ) * (M : ℝ) ≤ (readyZeroCount h c : ℝ)

theorem capRate_nonneg (n M : ℕ) : 0 ≤ capRate n M := by
  unfold capRate
  positivity

theorem capRate_le_readyRate {n M h : ℕ} (hn : 2 ≤ n)
    (c : Cfg L 256) (hc : CapGate n M h c) :
    ENNReal.ofReal (capRate n M) ≤ readyRate h c := by
  have hcard : 2 ≤ c.card := by rw [hc.population]; exact hn
  apply (ENNReal.ofReal_le_iff_le_toReal (readyRate_ne_top h c hcard)).2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (c.totalPairs : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    simp only [Config.totalPairs, hc.population, Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  have hdenpos : (0 : ℝ) < c.totalPairs := by
    rw [hden]
    exact mul_pos hnpos (by linarith only [hnr])
  have hdenle : (c.totalPairs : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [hden]
    nlinarith only [hnpos]
  calc
    capRate n M = ((77 / 100 : ℝ) * M) / (n : ℝ) ^ 2 := rfl
    _ ≤ (readyZeroCount h c : ℝ) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hc.ready_floor (sq_nonneg _)
    _ ≤ (readyZeroCount h c : ℝ) / (c.totalPairs : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdenpos hdenle
    _ = (readyRate h c).toReal := by
      simp only [readyRate, ENNReal.toReal_div, ENNReal.toReal_natCast]

theorem cap_kernel_drift {n M h : ℕ} (hn : 2 ≤ n) (hh : 1 ≤ h)
    (c : Cfg L 256) (hc : CapGate n M h c) :
    (∫⁻ c', (augmentedPhiNat h c' : ℝ≥0∞)
      ∂(NonuniformMajority L 256).transitionKernel c) ≤
        (1 - ENNReal.ofReal (capRate n M)) * augmentedPhiNat h c := by
  have hcard : 2 ≤ c.card := by rw [hc.population]; exact hn
  exact (augmentedPhiNat_kernel_drift h hh c hcard hc.domain).trans
    (mul_le_mul_right' (tsub_le_tsub_left (capRate_le_readyRate hn c hc) 1) _)

theorem capRate_le_one {n M : ℕ} (hn : 1 ≤ n) (hMn : M ≤ n) :
    capRate n M ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnunit : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (M : ℝ) ≤ n := by exact_mod_cast hMn
  unfold capRate
  apply (div_le_one (pow_pos hnpos 2)).2
  nlinarith only [hnunit, hmn, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]

theorem cap_work_exponent {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) :
    5 * Real.log (n : ℝ) ≤ capRate n M * (logWindow n 16 : ℝ) := by
  obtain ⟨hnpos, hlog⟩ := population_log_lower hn
  have hlogpos : 0 ≤ Real.log (n : ℝ) := by linarith only [hlog]
  have hceil : 16 * (n : ℝ) * Real.log (n : ℝ) ≤ (logWindow n 16 : ℝ) := by
    exact Nat.le_ceil _
  have hm : (12 : ℝ) * n ≤ 25 * (M : ℝ) := by exact_mod_cast hmain
  have hwork := mul_le_mul_of_nonneg_left hceil
    (show (0 : ℝ) ≤ (77 / 100 : ℝ) * M by positivity)
  have hdensity := mul_le_mul_of_nonneg_right hm
    (mul_nonneg hnpos.le hlogpos)
  have hnonneg := mul_nonneg (sq_nonneg (n : ℝ)) hlogpos
  have heq : capRate n M * (logWindow n 16 : ℝ) =
      ((77 / 100 : ℝ) * M * (logWindow n 16 : ℝ)) / (n : ℝ) ^ 2 := by
    unfold capRate
    ring
  rw [heq]
  apply (le_div_iff₀ (pow_pos hnpos 2)).2
  nlinarith only [hwork, hdensity, hnonneg]

theorem cap_contraction_scalar {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M)
    (hMn : M ≤ n) :
    (1 - ENNReal.ofReal (capRate n M)) ^ logWindow n 16 *
        ((M / 1000 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  have hnpos := (population_log_lower hn).1
  have hnforty := (time_population_bounds hn).2
  have hrzero := capRate_nonneg n M
  have hrone := capRate_le_one (by omega : 1 ≤ n) hMn
  have hsub : 0 ≤ 1 - capRate n M := sub_nonneg.mpr hrone
  have hbase : 1 - capRate n M ≤ Real.exp (-capRate n M) := by
    have h := Real.add_one_le_exp (-capRate n M)
    linarith only [h]
  have hp := pow_le_pow_left₀ hsub hbase (logWindow n 16)
  have hexp : (1 - capRate n M) ^ logWindow n 16 ≤
      Real.exp (-(capRate n M * (logWindow n 16 : ℝ))) := by
    rw [← Real.exp_nat_mul] at hp
    convert hp using 1 <;> congr 1 <;> ring
  have hsize : ((M / 1000 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.div_le_self M 1000).trans hMn
  have hreal :
      (1 - capRate n M) ^ logWindow n 16 * ((M / 1000 : ℕ) : ℝ) ≤
        1 / (n : ℝ) ^ 4 := by
    calc
      (1 - capRate n M) ^ logWindow n 16 * ((M / 1000 : ℕ) : ℝ) ≤
          Real.exp (-(capRate n M * (logWindow n 16 : ℝ))) *
            ((M / 1000 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _)
      _ ≤ Real.exp (-(5 * Real.log (n : ℝ))) * (n : ℝ) :=
        mul_le_mul
          (Real.exp_le_exp.mpr (neg_le_neg (cap_work_exponent hn hmain)))
          hsize (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = 1 / (n : ℝ) ^ 4 := by
        have h5 := exp_neg_log_nat hnpos 5
        push_cast at h5
        rw [h5]
        field_simp [ne_of_gt hnpos]
        <;> ring
  have heq :
      ENNReal.ofReal ((1 - capRate n M) ^ logWindow n 16 *
        ((M / 1000 : ℕ) : ℝ)) =
      (1 - ENNReal.ofReal (capRate n M)) ^ logWindow n 16 *
        ((M / 1000 : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (pow_nonneg hsub _), ENNReal.ofReal_pow hsub,
      ENNReal.ofReal_sub 1 hrzero]
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  rw [← heq]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Original-law extinction from an arbitrary observed cap checkpoint.
The gate is checked only before each sampled transition. -/
theorem protected_cap_extinction_tail {n M h : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M)
    (hMn : M ≤ n) (hh : 1 ≤ h)
    (init : Cfg L 256) (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) :
    law init
      (driftFailureAt init τ (augmentedPhiNat h) (CapGate n M h)
        (logWindow n 16) (M / 1000)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  have hnlarge := (time_population_bounds hn).2
  exact (potential_drift_tail_at_pastTime init τ hτ
    (augmentedPhiNat h) (CapGate n M h) (ENNReal.ofReal (capRate n M))
    (fun c hc => cap_kernel_drift (by omega) hh c hc)
    (logWindow n 16) (M / 1000)).trans
      (cap_contraction_scalar hn hmain hMn)

theorem cap_index_pos {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    1 ≤ PhaseThreeModel.Numeric.hourIndex n := by
  obtain ⟨-, -, hlog, hH, -, -⟩ := time_hour_calibration hn
  have hreal : (6 : ℝ) ≤ (PhaseThreeModel.Numeric.clockHours n : ℝ) :=
    hlog.trans hH
  have hnat : 6 ≤ PhaseThreeModel.Numeric.clockHours n := by exact_mod_cast hreal
  unfold PhaseThreeModel.Numeric.clockHours at hnat
  omega

/-- Failure at the genuine first Phase-4 seed, intersected with the complete
clock history and the produced cap gates. The probability measure is unchanged. -/
theorem tie_readout_failure_on_protected_cap {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M)
    (hMn : M ≤ n) (init : InputCfg n)
    (τ : InputLog n → WithTop ℕ) (hτ : PairLogPastTime τ) :
    law init {ω | ∃ S T ρ, ∃ w : ClockTimes init,
      ClockHistory init ω S T ρ w ∧
      τ ω = (w.cap : WithTop ℕ) ∧ initialGap init = 0 ∧
      1000 * augmentedPhiNat (PhaseThreeModel.Numeric.hourIndex n)
        (trace init ω w.cap) ≤ M ∧
      (∀ v, w.cap ≤ v → v < w.cap + logWindow n 16 →
        CapGate n M (PhaseThreeModel.Numeric.hourIndex n) (trace init ω v)) ∧
      ¬ tieReadout init (trace init ω ρ)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  refine (measure_mono ?_).trans
    (protected_cap_extinction_tail hn hmain hMn (cap_index_pos hn) init τ hτ)
  rintro ω ⟨S, T, ρ, w, hclock, htime, hgap, hstart, hgate, hbad⟩
  refine ⟨w.cap, htime, ?_, hgate, ?_⟩
  · omega
  · by_contra hnot
    have hzero : augmentedPhiNat (PhaseThreeModel.Numeric.hourIndex n)
        (trace init ω (w.cap + logWindow n 16)) = 0 := by omega
    have hTend : T ≤ w.cap + logWindow n 16 :=
      hclock.all_before_cap.trans (Nat.le_add_right _ _)
    have hend : w.cap + logWindow n 16 ≤ ρ :=
      hclock.protected_settling.le
    have hphase : ∀ a ∈ trace init ω (w.cap + logWindow n 16),
        3 ≤ a.phase.val := by
      intro a ha
      exact (hclock.all_three _ hTend hclock.protected_settling a ha).ge
    have hcarrier := nonmainZero_of_clockHistory hclock hTend hend
    have hshallow : shallowPotential (PhaseThreeModel.Numeric.hourIndex n)
        (trace init ω (w.cap + logWindow n 16)) = 0 := by
      rw [← augmentedPhiNat_eq_shallowPotential _ _ hphase hcarrier]
      exact hzero
    exact hbad (tieReadout_at_first_exit_of_zero_potential hclock hgap hTend hend hshallow)

end Ripple.PopulationProtocol.ExactMajority.AveragingProtectedCap

end
