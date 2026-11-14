-- Ripple/PopulationProtocol/ExactMajority/Probability/LatePhaseSixDrainPaperNumerics.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSharpPotentialNumerics
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTimerPrefixScalar
import Ripple.PopulationProtocol.ExactMajority.Probability.ScalarTails

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainPaperNumerics

open TimeTheorem LateTimerPrefixScalar

/-- Paper Lemma 10 work interval: `ceil(23.4 n log n)`. -/
def phaseSixDrainHorizon (n : ℕ) : ℕ :=
  Nat.ceil ((117 / 5 : ℝ) * (n : ℝ) * Real.log (n : ℝ))

/-- The drain row's standalone failure budget. -/
noncomputable def phaseSixDrainBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.rpow (n : ℝ) (-(202 / 100 : ℝ)))

/-- The exact one-step contraction supplied by N17. -/
def phaseSixDrainRateReal (n : ℕ) : ℝ :=
  1 - (43281 : ℝ) / (320000 * ((n : ℝ) - 1))

noncomputable def phaseSixDrainRate (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (phaseSixDrainRateReal n)

theorem phaseSixDrainRateReal_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ phaseSixDrainRateReal n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 320000 * ((n : ℝ) - 1) := by nlinarith
  unfold phaseSixDrainRateReal
  rw [sub_nonneg, div_le_one hden]
  nlinarith

theorem phaseSixDrainRateReal_le_one {n : ℕ} (hn : 2 ≤ n) :
    phaseSixDrainRateReal n ≤ 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 ≤ (320000 : ℝ) * ((n : ℝ) - 1) := mul_nonneg (by norm_num) (by linarith)
  unfold phaseSixDrainRateReal
  have hq : 0 ≤ (43281 : ℝ) / (320000 * ((n : ℝ) - 1)) :=
    div_nonneg (by norm_num) hden
  linarith

/-- The two ceilings really fit under the timer ceiling.  The two possible
rounding units are paid by the paper's `0.1 n log n` slack; at the repository's
population threshold `n log n ≥ 100`, so the slack is at least ten. -/
theorem spread_add_drain_horizon_le_protection
    {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    logWindow n 3 + phaseSixDrainHorizon n ≤ protectionHorizon n := by
  obtain ⟨hnpos, hnlog⟩ := ScalarTails.time_population_scalar_bounds hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hnOne : (1 : ℝ) ≤ n := by
    have h := Real.add_one_le_exp (Real.log (n : ℝ))
    rw [Real.exp_log hnpos] at h
    linarith
  clear hn
  let x : ℝ := (n : ℝ) * Real.log (n : ℝ)
  have hx : (20 : ℝ) ≤ x := by
    have hmul : (1 : ℝ) * 100 ≤ (n : ℝ) * Real.log (n : ℝ) :=
      mul_le_mul hnOne hnlog (by norm_num) (by positivity)
    dsimp [x]
    nlinarith
  have hspread : (logWindow n 3 : ℝ) < 3 * x + 1 := by
    change
      (Nat.ceil ((3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) : ℝ) <
        3 * x + 1
    convert Nat.ceil_lt_add_one
      (show 0 ≤ (3 : ℝ) * (n : ℝ) * Real.log (n : ℝ) by positivity)
      using 1 <;> dsimp [x] <;> ring
  have hdrain : (phaseSixDrainHorizon n : ℝ) < (117 / 5 : ℝ) * x + 1 := by
    unfold phaseSixDrainHorizon
    convert Nat.ceil_lt_add_one
      (show 0 ≤ (117 / 5 : ℝ) * (n : ℝ) * Real.log (n : ℝ) by positivity)
      using 1 <;> dsimp [x] <;> ring
  have hprotect : (53 / 2 : ℝ) * x ≤ (protectionHorizon n : ℝ) := by
    unfold protectionHorizon
    convert Nat.le_ceil
      ((53 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ))
      using 1 <;> dsimp [x] <;> ring
  have hcoefficient :=
    LateSharpPotentialNumerics.drain_horizon_fits_protection
  have hreal :
      ((logWindow n 3 + phaseSixDrainHorizon n : ℕ) : ℝ) ≤
        (protectionHorizon n : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast hreal

/-- The rounded 23.4-unit interval supplies the full paper exponent. -/
private theorem drainRate_pow_le_rpow
    {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    phaseSixDrainRateReal n ^ phaseSixDrainHorizon n ≤
      Real.rpow (n : ℝ)
        (-((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) := by
  obtain ⟨hnpos, hnlog⟩ := ScalarTails.time_population_scalar_bounds hn
  have hnlarge : 2 ≤ n := by
    have := (time_population_bounds hn).2
    omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hnlarge
  clear hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hnsub : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  let x : ℝ := (43281 : ℝ) / (320000 * ((n : ℝ) - 1))
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one (by positivity : (0 : ℝ) < 320000 * ((n : ℝ) - 1))]
    nlinarith
  have hrate : phaseSixDrainRateReal n = 1 - x := by
    dsimp [x, phaseSixDrainRateReal]
  have hceil :
      (117 / 5 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
        (phaseSixDrainHorizon n : ℝ) := by
    unfold phaseSixDrainHorizon
    exact Nat.le_ceil _
  have hratio :
      (1 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) :=
    (le_div_iff₀ hnsub).2 (by linarith)
  have heq :
      x * ((117 / 5 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) =
        ((43281 / 320000 : ℝ) * (117 / 5 : ℝ) *
          Real.log (n : ℝ)) * ((n : ℝ) / ((n : ℝ) - 1)) := by
    dsimp [x]
    field_simp [ne_of_gt hnsub]
  have hbefore :
      (43281 / 320000 : ℝ) * (117 / 5 : ℝ) * Real.log (n : ℝ) ≤
        x * ((117 / 5 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) := by
    rw [heq]
    exact le_mul_of_one_le_right (by positivity) hratio
  have hscaled := mul_le_mul_of_nonneg_left hceil hx0
  have hdecay :
      (43281 / 320000 : ℝ) * (117 / 5 : ℝ) * Real.log (n : ℝ) ≤
        x * (phaseSixDrainHorizon n : ℝ) :=
    hbefore.trans hscaled
  calc
    phaseSixDrainRateReal n ^ phaseSixDrainHorizon n =
        (1 - x) ^ phaseSixDrainHorizon n := by rw [hrate]
    _ ≤ (Real.exp (-x)) ^ phaseSixDrainHorizon n :=
      pow_le_pow_left₀ (sub_nonneg.mpr hx1)
        (by nlinarith [Real.add_one_le_exp (-x)]) _
    _ = Real.exp (-x * (phaseSixDrainHorizon n : ℝ)) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    _ ≤ Real.exp
        (-((43281 / 320000 : ℝ) * (117 / 5 : ℝ) *
          Real.log (n : ℝ))) :=
      Real.exp_le_exp.mpr (by rw [neg_mul]; exact neg_le_neg hdecay)
    _ = Real.rpow (n : ℝ)
        (-((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) := by
      rw [show Real.rpow (n : ℝ) (-((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) =
          Real.exp (Real.log (n : ℝ) *
            (-((43281 / 320000 : ℝ) * (117 / 5 : ℝ)))) from
        Real.rpow_def_of_pos hnpos _]
      congr 1
      ring

/-- Scalar Lemma 10 calculation.  This is proved here, not carried as a
premise of the first-barrier theorem. -/
theorem phaseSixDrain_decay_calibration
    {n : ℕ} (hn : timePopulationThreshold ≤ n) :
    phaseSixDrainRateReal n ^ phaseSixDrainHorizon n *
        ((1 / 1000 : ℝ) * Real.rpow (n : ℝ) (114 / 100 : ℝ)) ≤
      Real.rpow (n : ℝ) (-(202 / 100 : ℝ)) := by
  obtain ⟨hnpos, hnlog⟩ := ScalarTails.time_population_scalar_bounds hn
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hrate := drainRate_pow_le_rpow hn
  clear hn
  have hmargin :
      (114 / 100 : ℝ) -
          ((43281 / 320000 : ℝ) * (117 / 5 : ℝ)) <
        -(202 / 100 : ℝ) := by
    nlinarith [LateSharpPotentialNumerics.drain_exponent_margin]
  have hpow :
      Real.rpow (n : ℝ)
          ((114 / 100 : ℝ) -
            ((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) <
        Real.rpow (n : ℝ) (-(202 / 100 : ℝ)) := by
    rw [show Real.rpow (n : ℝ)
          ((114 / 100 : ℝ) - ((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) =
        Real.exp (Real.log (n : ℝ) *
          ((114 / 100 : ℝ) - ((43281 / 320000 : ℝ) * (117 / 5 : ℝ)))) from
        Real.rpow_def_of_pos hnpos _,
      show Real.rpow (n : ℝ) (-(202 / 100 : ℝ)) =
        Real.exp (Real.log (n : ℝ) * (-(202 / 100 : ℝ))) from
        Real.rpow_def_of_pos hnpos _]
    exact Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left hmargin hlogpos)
  calc
    phaseSixDrainRateReal n ^ phaseSixDrainHorizon n *
        ((1 / 1000 : ℝ) * Real.rpow (n : ℝ) (114 / 100 : ℝ)) ≤
      Real.rpow (n : ℝ)
          (-((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) *
        ((1 / 1000 : ℝ) * Real.rpow (n : ℝ) (114 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_right hrate
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hnpos.le _))
    _ = (1 / 1000 : ℝ) *
        Real.rpow (n : ℝ)
          ((114 / 100 : ℝ) -
            ((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) := by
      calc
        _ = (1 / 1000 : ℝ) *
            (Real.rpow (n : ℝ)
                (-((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) *
              Real.rpow (n : ℝ) (114 / 100 : ℝ)) := by ring
        _ = _ := by
          have hsum : (-((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) + (114 / 100 : ℝ) =
              (114 / 100 : ℝ) - ((43281 / 320000 : ℝ) * (117 / 5 : ℝ)) := by ring
          have hmul : Real.rpow (n : ℝ) (-((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) *
              Real.rpow (n : ℝ) (114 / 100 : ℝ) =
              Real.rpow (n : ℝ) ((114 / 100 : ℝ) -
                ((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) := by
            rw [← hsum]
            exact (Real.rpow_add hnpos _ _).symm
          rw [hmul]
    _ ≤ Real.rpow (n : ℝ)
          ((114 / 100 : ℝ) -
            ((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) := by
      have hp : 0 < Real.rpow (n : ℝ) ((114 / 100 : ℝ) -
          ((43281 / 320000 : ℝ) * (117 / 5 : ℝ))) :=
        Real.rpow_pos_of_pos hnpos _
      nlinarith
    _ ≤ Real.rpow (n : ℝ) (-(202 / 100 : ℝ)) := hpow.le

/-- The calibrated bound with the actual sharp initial potential. -/
theorem phaseSixDrain_scalar_real
    {n potential : ℕ} (hn : timePopulationThreshold ≤ n)
    (hpotential :
      (potential : ℝ) <
        (1 / 1000 : ℝ) * Real.rpow (n : ℝ) (114 / 100 : ℝ)) :
    phaseSixDrainRateReal n ^ phaseSixDrainHorizon n * (potential : ℝ) ≤
      Real.rpow (n : ℝ) (-(202 / 100 : ℝ)) := by
  have hnlarge : 2 ≤ n := by
    have := (time_population_bounds hn).2
    omega
  calc
    phaseSixDrainRateReal n ^ phaseSixDrainHorizon n * (potential : ℝ) ≤
        phaseSixDrainRateReal n ^ phaseSixDrainHorizon n *
          ((1 / 1000 : ℝ) * Real.rpow (n : ℝ) (114 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpotential.le
        (pow_nonneg (phaseSixDrainRateReal_nonneg hnlarge) _)
    _ ≤ Real.rpow (n : ℝ) (-(202 / 100 : ℝ)) :=
      phaseSixDrain_decay_calibration hn

/-- ENNReal form consumed by the killed first-barrier theorem. -/
theorem phaseSixDrain_scalar_ennreal
    {n potential : ℕ} (hn : timePopulationThreshold ≤ n)
    (hpotential :
      (potential : ℝ) <
        (1 / 1000 : ℝ) * Real.rpow (n : ℝ) (114 / 100 : ℝ)) :
    phaseSixDrainRate n ^ phaseSixDrainHorizon n * (potential : ℝ≥0∞) ≤
      phaseSixDrainBudget n := by
  have hnlarge : 2 ≤ n := by
    have := (time_population_bounds hn).2
    omega
  have hreal := phaseSixDrain_scalar_real hn hpotential
  unfold phaseSixDrainRate phaseSixDrainBudget
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_pow (phaseSixDrainRateReal_nonneg hnlarge)]
  rw [← ENNReal.ofReal_mul
    (pow_nonneg (phaseSixDrainRateReal_nonneg hnlarge)
      (phaseSixDrainHorizon n))]
  exact ENNReal.ofReal_le_ofReal hreal

/-!
THEOREM LIST
* `phaseSixDrainHorizon`, `phaseSixDrainBudget`
* `spread_add_drain_horizon_le_protection`
* `phaseSixDrain_decay_calibration`
* `phaseSixDrain_scalar_real`, `phaseSixDrain_scalar_ennreal`

CLOSES
* The literal `23.4` work horizon.
* The ceiling-level `ceil(3 n log n) + ceil(23.4 n log n) ≤
  ceil(26.5 n log n)` inequality.
* The standalone `n^(-2.02)` scalar conversion from the sharp initial
  exponent of `LateSharpInitialPotential`; no scalar estimate is carried by later structures.

UNFINISHED
* Nothing mathematical in this file.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LatePhaseSixDrainPaperNumerics

end
