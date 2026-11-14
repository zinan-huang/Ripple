-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSharpPotentialNumerics.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSharpPotentialTransport

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority
namespace LateSharpPotentialNumerics

open TimeTheorem
open LateStrengthening LateF6OriginalLaw LateMixedFuel
open LateSamplingStrongSeedReceipt
open LateSharpPotentialTransport

/-- `q = floor(log n / 25)` has the required real upper bound. -/
theorem terminalCutoff_cast_le
    (n : ℕ) (hn : 1 ≤ n) :
    (terminalCutoff n : ℝ) ≤ Real.log (n : ℝ) / 25 := by
  unfold terminalCutoff
  apply Nat.floor_le
  exact div_nonneg
    (Real.log_nonneg (by exact_mod_cast hn)) (by norm_num)

/-- `32^q ≤ n^(log 32 / 25)`. -/
theorem cutoff_power_cast_le
    (n : ℕ) (hn : 1 ≤ n) :
    (((32 ^ terminalCutoff n : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (Real.log 32 / 25) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hfloor := terminalCutoff_cast_le n hn
  calc
    (((32 ^ terminalCutoff n : ℕ) : ℝ)) =
        (32 : ℝ) ^ terminalCutoff n := by norm_num
    _ = (32 : ℝ) ^ (terminalCutoff n : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (32 : ℝ) ^ (Real.log (n : ℝ) / 25) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
    _ = (n : ℝ) ^ (Real.log 32 / 25) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 32),
        Real.rpow_def_of_pos hnpos]
      congr 1
      ring

/-- Certified exponent comparison: `log 32 / 25 < .14`. -/
theorem log_thirtyTwo_div_twentyFive_lt_fourteen_hundredths :
    Real.log 32 / 25 < (14 / 100 : ℝ) := by
  have hlog : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  rw [hlog]
  nlinarith [Real.log_two_lt_d9]

/-- For `n ≥ 2`, the paper's strict `1.14` envelope. -/
theorem paper_power_comparison
    (n : ℕ) (hn : 2 ≤ n) :
    (1 / 1000 : ℝ) * n * (n : ℝ) ^ (Real.log 32 / 25) <
      (1 / 1000 : ℝ) * (n : ℝ) ^ (114 / 100 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnone : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hnone
  have hpow :
      (n : ℝ) ^ (Real.log 32 / 25) <
        (n : ℝ) ^ (14 / 100 : ℝ) := by
    rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos]
    exact Real.exp_lt_exp.mpr
      (mul_lt_mul_of_pos_left
        log_thirtyTwo_div_twentyFive_lt_fourteen_hundredths hlogpos)
  have hfactor : 0 < (1 / 1000 : ℝ) * n := by positivity
  calc
    (1 / 1000 : ℝ) * n * (n : ℝ) ^ (Real.log 32 / 25)
        < (1 / 1000 : ℝ) * n * (n : ℝ) ^ (14 / 100 : ℝ) :=
      mul_lt_mul_of_pos_left hpow hfactor
    _ = (1 / 1000 : ℝ) * (n : ℝ) ^ (114 / 100 : ℝ) := by
      calc
        (1 / 1000 : ℝ) * n * (n : ℝ) ^ (14 / 100 : ℝ)
            = (1 / 1000 : ℝ) *
              ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (14 / 100 : ℝ)) := by
                rw [Real.rpow_one]
                ring
        _ = (1 / 1000 : ℝ) *
              (n : ℝ) ^ ((1 : ℝ) + 14 / 100) := by
                rw [← Real.rpow_add hnpos]
        _ = (1 / 1000 : ℝ) * (n : ℝ) ^ (114 / 100 : ℝ) := by
                norm_num

/-- Abstract cast of equation (46) to the strict paper envelope. -/
theorem scaled_largePotential_lt_paper_power
    {n potential : ℕ} (hn : 2 ≤ n)
    (hbound : 1000 * potential ≤ 32 ^ terminalCutoff n * n) :
    (potential : ℝ) <
      (1 / 1000 : ℝ) * (n : ℝ) ^ (114 / 100 : ℝ) := by
  have hcast :
      (1000 : ℝ) * (potential : ℝ) ≤
        (((32 ^ terminalCutoff n : ℕ) : ℝ)) * (n : ℝ) := by
    exact_mod_cast hbound
  calc
    (potential : ℝ) =
        (1 / 1000 : ℝ) * ((1000 : ℝ) * potential) := by ring
    _ ≤ (1 / 1000 : ℝ) *
        ((((32 ^ terminalCutoff n : ℕ) : ℝ)) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcast (by norm_num)
    _ = (1 / 1000 : ℝ) * (n : ℝ) *
        (((32 ^ terminalCutoff n : ℕ) : ℝ)) := by ring
    _ ≤ (1 / 1000 : ℝ) * (n : ℝ) *
        (n : ℝ) ^ (Real.log 32 / 25) :=
      mul_le_mul_of_nonneg_left
        (cutoff_power_cast_le n (by omega))
        (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
    _ < (1 / 1000 : ℝ) * (n : ℝ) ^ (114 / 100 : ℝ) :=
      paper_power_comparison n hn

/-- Equation (46), now attached to the actual homogeneous work snapshot. -/
theorem homogeneous_largePotential_lt_paper_power
    {n : ℕ} {init : InputCfg n} {omega : InputLog n}
    {allStart seed completed homogeneous M C R ell : ℕ} {sigma : Sign}
    (hn : 2 ≤ n)
    (hpath : Prefix init omega allStart seed completed)
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous)
    (hread : LateSeedReadout init M ell sigma (trace init omega seed))
    (hdensity : StrongSeedDensity n M C R) :
    (LatePotential.shallowLargePotential ell
        (trace init omega homogeneous) : ℝ) <
      (1 / 1000 : ℝ) * (n : ℝ) ^ (114 / 100 : ℝ) := by
  exact scaled_largePotential_lt_paper_power hn
    (homogeneous_largePotential_scaled_le_population
      hpath hmixed hread hdensity)

/-- Equation (48): the exponent margin really exceeds `2.02`. -/
theorem drain_exponent_margin :
    (63 / 32 : ℝ) * (687 / 10000) * (234 / 10) - 114 / 100 >
      (202 / 100 : ℝ) := by
  norm_num

/-- The repaired `23.4` drain still fits below the protection horizon. -/
theorem drain_horizon_fits_protection :
    (3 : ℝ) + 234 / 10 < 265 / 10 := by
  norm_num

end LateSharpPotentialNumerics
end Ripple.PopulationProtocol.ExactMajority

end
