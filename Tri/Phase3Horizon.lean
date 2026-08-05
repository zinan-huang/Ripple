/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase3Reconciled
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The gamma-scaled phase-3 horizon

The buffered phase-3 entry permits an initial minority of order
`gamma * log_2 n`.  Consequently its corrected geometric potential can be as
large as `n ^ (gamma / 2)`.  A horizon independent of `gamma` cannot suppress
that initial value uniformly.

This module scales the phase-3 horizon by `gamma`, repeats the stopped-chain
and Feller decomposition at that horizon, and proves that the corrected-
potential contribution is at most `n ^ (-gamma)` when the horizon constant is
`16`.
-/

namespace Tri

open scoped ENNReal

/-- The phase-3 horizon with the necessary linear dependence on `gamma`. -/
def phase3HorizonScaled (C₃ n γ : ℕ) : ℕ :=
  C₃ * γ * n * Nat.log 2 n

/-- The corrected-potential contribution at the gamma-scaled horizon. -/
noncomputable def phase3ScaledPotentialError (C₃ n γ : ℕ) : ℝ≥0∞ :=
  phase3Factor n ^ phase3HorizonScaled C₃ n γ *
    ENNReal.ofReal ((2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1)

/-- The gamma-scaled phase-3 error is the corrected-potential term plus the
unchanged reconciled Feller escape term. -/
noncomputable def phase3ScaledError
    (C₃ n γ aLo bHi : ℕ) : ℝ≥0∞ :=
  phase3ScaledPotentialError C₃ n γ +
    phase3ReconciledFellerError n γ aLo bHi

/-- The uniform entry power is bounded by `n ^ (gamma / 2)`, with a real
exponent. -/
theorem phase3_initial_power_le_rpow (n γ : ℕ) (h3 : 3 ≤ n) :
    (2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1 ≤
      (n : ℝ) ^ ((γ : ℝ) / 2) := by
  have hfloorNat :
      2 * ((γ * Nat.log 2 n) / 2) ≤ γ * Nat.log 2 n := by
    omega
  have hfloorCast :
      (((γ * Nat.log 2 n) / 2 : ℕ) : ℝ) ≤
        (γ : ℝ) * (Nat.log 2 n : ℝ) / 2 := by
    have hcast :
        (2 : ℝ) * (((γ * Nat.log 2 n) / 2 : ℕ) : ℝ) ≤
          (γ : ℝ) * (Nat.log 2 n : ℝ) := by
      exact_mod_cast hfloorNat
    nlinarith
  have hpowNat : 2 ^ Nat.log 2 n ≤ n :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowCast : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  calc
    (2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1 ≤
        (2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) :=
      sub_le_self _ zero_le_one
    _ = (2 : ℝ) ^ ((((γ * Nat.log 2 n) / 2 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^
        ((γ : ℝ) * (Nat.log 2 n : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloorCast
    _ = ((2 : ℝ) ^ (Nat.log 2 n : ℝ)) ^ ((γ : ℝ) / 2) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ = ((2 : ℝ) ^ Nat.log 2 n) ^ ((γ : ℝ) / 2) := by
      rw [Real.rpow_natCast]
    _ ≤ (n : ℝ) ^ ((γ : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hpowCast (by positivity)

/-- The scaled potential error is bounded by the real envelope consisting of
the initial `n ^ (gamma / 2)` factor and the scaled geometric decay. -/
theorem phase3ScaledPotentialError_le_real
    (C₃ n γ : ℕ) (h3 : 3 ≤ n) :
    phase3ScaledPotentialError C₃ n γ ≤
      ENNReal.ofReal
        ((n : ℝ) ^ ((γ : ℝ) / 2) *
          (1 - ((105 : ℝ) / 128) / (n : ℝ)) ^
            phase3HorizonScaled C₃ n γ) := by
  let q : ℝ := 1 - ((105 : ℝ) / 128) / (n : ℝ)
  have hq : 0 ≤ q := by
    simpa [q] using phase3_factor_nonneg n h3
  change
    ENNReal.ofReal q ^ phase3HorizonScaled C₃ n γ *
        ENNReal.ofReal ((2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1) ≤
      ENNReal.ofReal
        ((n : ℝ) ^ ((γ : ℝ) / 2) *
          q ^ phase3HorizonScaled C₃ n γ)
  calc
    ENNReal.ofReal q ^ phase3HorizonScaled C₃ n γ *
          ENNReal.ofReal ((2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1) =
        ENNReal.ofReal
          (q ^ phase3HorizonScaled C₃ n γ *
            ((2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1)) := by
      rw [ENNReal.ofReal_mul (pow_nonneg hq _), ENNReal.ofReal_pow hq]
    _ ≤ ENNReal.ofReal
        ((n : ℝ) ^ ((γ : ℝ) / 2) *
          q ^ phase3HorizonScaled C₃ n γ) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        q ^ phase3HorizonScaled C₃ n γ *
              ((2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1) ≤
            q ^ phase3HorizonScaled C₃ n γ *
              (n : ℝ) ^ ((γ : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left
            (phase3_initial_power_le_rpow n γ h3) (pow_nonneg hq _)
        _ = (n : ℝ) ^ ((γ : ℝ) / 2) *
            q ^ phase3HorizonScaled C₃ n γ := by ring

/-- With horizon constant `16`, the real potential envelope is at most
`n ^ (-gamma)`.  The proof uses `log n ≤ 2 * floor(log_2 n)` for `n ≥ 3`;
the exponent margin is
`16 * (105 / 128) - 3 * log 2 > 0`. -/
theorem phase3_scaled_real_error_bound (n γ : ℕ) (h3 : 3 ≤ n) :
    (n : ℝ) ^ ((γ : ℝ) / 2) *
        (1 - ((105 : ℝ) / 128) / (n : ℝ)) ^
          phase3HorizonScaled 16 n γ ≤
      ((n : ℝ)⁻¹) ^ (γ : ℝ) := by
  let q : ℝ := 1 - ((105 : ℝ) / 128) / (n : ℝ)
  let B : ℕ := 16 * γ * Nat.log 2 n
  have hnpos : (0 : ℝ) < n := by positivity
  have hq : 0 ≤ q := by
    simpa [q] using phase3_factor_nonneg n h3
  have haLe : (105 / 128 : ℝ) ≤ (n : ℝ) := by
    calc
      (105 / 128 : ℝ) ≤ 3 := by norm_num
      _ ≤ (n : ℝ) := by exact_mod_cast h3
  have hblock : q ^ n ≤ Real.exp (-(105 / 128 : ℝ)) := by
    simpa [q] using Real.one_sub_div_pow_le_exp_neg haLe
  have htime : phase3HorizonScaled 16 n γ = n * B := by
    simp only [phase3HorizonScaled, B]
    ring
  have hdecay :
      q ^ phase3HorizonScaled 16 n γ ≤
        Real.exp (-(105 / 128 : ℝ) * (B : ℝ)) := by
    calc
      q ^ phase3HorizonScaled 16 n γ = (q ^ n) ^ B := by
        rw [htime, pow_mul]
      _ ≤ (Real.exp (-(105 / 128 : ℝ))) ^ B :=
        pow_le_pow_left₀ (pow_nonneg hq n) hblock B
      _ = Real.exp (-(105 / 128 : ℝ) * (B : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hlogPos : 0 < Nat.log 2 n :=
    Nat.log_pos (by norm_num) (by omega)
  have hpowUpper :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  have hpowUpperCast :
      (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast hpowUpper
  have hlogUpper :
      Real.log (n : ℝ) <
        ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 := by
    have h := Real.log_lt_log hnpos hpowUpperCast
    simpa only [Real.log_pow] using h
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogBound :
      Real.log (n : ℝ) ≤ 2 * (Nat.log 2 n : ℝ) := by
    calc
      Real.log (n : ℝ) ≤
          ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 :=
        hlogUpper.le
      _ ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlogTwo (by positivity)
      _ ≤ 2 * (Nat.log 2 n : ℝ) := by
        norm_num only [Nat.cast_add, Nat.cast_one, mul_one]
        have hlogCast : (1 : ℝ) ≤ Nat.log 2 n := by
          exact_mod_cast hlogPos
        linarith
  have hscaledLog :
      Real.log (n : ℝ) * (γ : ℝ) ≤
        (2 * (Nat.log 2 n : ℝ)) * (γ : ℝ) :=
    mul_le_mul_of_nonneg_right hlogBound (by positivity)
  have hBCast :
      (B : ℝ) = 16 * (γ : ℝ) * (Nat.log 2 n : ℝ) := by
    simp only [B, Nat.cast_mul, Nat.cast_ofNat]
  have hexponent :
      Real.log (n : ℝ) * ((γ : ℝ) / 2) +
          (-(105 / 128 : ℝ) * (B : ℝ)) ≤
        -Real.log (n : ℝ) * (γ : ℝ) := by
    rw [hBCast]
    nlinarith
  change
    (n : ℝ) ^ ((γ : ℝ) / 2) *
        q ^ phase3HorizonScaled 16 n γ ≤
      ((n : ℝ)⁻¹) ^ (γ : ℝ)
  calc
    (n : ℝ) ^ ((γ : ℝ) / 2) *
          q ^ phase3HorizonScaled 16 n γ ≤
        (n : ℝ) ^ ((γ : ℝ) / 2) *
          Real.exp (-(105 / 128 : ℝ) * (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = Real.exp
        (Real.log (n : ℝ) * ((γ : ℝ) / 2) +
          (-(105 / 128 : ℝ) * (B : ℝ))) := by
      rw [Real.rpow_def_of_pos hnpos, Real.exp_add]
    _ ≤ Real.exp (-Real.log (n : ℝ) * (γ : ℝ)) :=
      (Real.exp_le_exp).2 hexponent
    _ = ((n : ℝ)⁻¹) ^ (γ : ℝ) := by
      rw [Real.rpow_def_of_pos (inv_pos.mpr hnpos), Real.log_inv]

/-- For the explicit rational exponent `c = 1` and horizon constant `C₃ = 16`,
the corrected-potential error is at most `n⁻¹ ^ (c * gamma)`. -/
theorem phase3ScaledPotentialError_le_inverse (n γ : ℕ) (h3 : 3 ≤ n) :
    phase3ScaledPotentialError 16 n γ ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) := by
  simp only [one_mul]
  calc
    phase3ScaledPotentialError 16 n γ ≤
        ENNReal.ofReal
          ((n : ℝ) ^ ((γ : ℝ) / 2) *
            (1 - ((105 : ℝ) / 128) / (n : ℝ)) ^
              phase3HorizonScaled 16 n γ) :=
      phase3ScaledPotentialError_le_real 16 n γ h3
    _ ≤ ENNReal.ofReal (((n : ℝ)⁻¹) ^ (γ : ℝ)) :=
      ENNReal.ofReal_le_ofReal (phase3_scaled_real_error_bound n γ h3)
    _ = (n : ℝ≥0∞)⁻¹ ^ (γ : ℝ) := by
      have hnpos : (0 : ℝ) < n := by positivity
      rw [← ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hnpos),
        ENNReal.ofReal_inv_of_pos hnpos, ENNReal.ofReal_natCast]

/-- The reconciled phase-3 argument reaches all-`X` consensus at the
gamma-scaled horizon, with the scaled potential error and the unchanged
Feller escape error. -/
theorem phase3_reaches_scaled
    (C₃ n γ aLo bHi : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (haLo : aLo + γ * Nat.log 2 n + 1 = n)
    (hbHi : bHi + 1 = γ * Nat.log 2 n) :
    Reaches (triChain n) (phase3HorizonScaled C₃ n γ) (Phase3Entry n γ)
      (IsXMajority n) (phase3ScaledError C₃ n γ aLo bHi) := by
  intro x hentry
  obtain ⟨y, k, hpop, hk, hdynamic⟩ :=
    Phase3Reconciled.phase3_escape_le_feller
      n γ (phase3HorizonScaled C₃ n γ) x aLo bHi
        h3 hγ hsize hentry haLo hbHi
  have hbuffer := phase3Entry_buffered hpop hentry hsize
  have hy : y ≤ (γ * Nat.log 2 n) / 2 := by omega
  have hkmin : (γ * Nat.log 2 n) / 2 + 1 ≤ k := by omega
  have hsize' : 6 * (γ * Nat.log 2 n) ≤ n := by
    simpa only [Nat.mul_assoc] using hsize
  have hthreshold := phase3_reconciled_threshold_two n γ h3 hγ hsize
  have haLoPos : 0 < aLo := by omega
  have hbHiPos : 0 < bHi := by omega
  have hmajority : bHi ≤ aLo := by omega
  have haLoCast : (aLo : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have haLoTop : (aLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top aLo
  have hbase : (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤ 1 := by
    calc
      (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) ≤
          (aLo : ℝ≥0∞) / (aLo : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hmajority) _
      _ = 1 := ENNReal.div_self haLoCast haLoTop
  have hpotential :
      expect (iter (phase3Stop n) (phase3HorizonScaled C₃ n γ) x)
          (phase3StoppedPotential n) ≤
        phase3ScaledPotentialError C₃ n γ := by
    calc
      expect (iter (phase3Stop n) (phase3HorizonScaled C₃ n γ) x)
          (phase3StoppedPotential n) ≤
          phase3Factor n ^ phase3HorizonScaled C₃ n γ *
            phase3StoppedPotential n x :=
        phase3Stop_expect_iter_le n (phase3HorizonScaled C₃ n γ) x h3
      _ ≤ phase3Factor n ^ phase3HorizonScaled C₃ n γ *
          ENNReal.ofReal ((2 : ℝ) ^ ((γ * Nat.log 2 n) / 2) - 1) :=
        mul_le_mul_right (phase3StoppedPotential_entry_le hpop hentry) _
      _ = phase3ScaledPotentialError C₃ n γ := rfl
  have hescapeExact :
      phase3EscapeMass n (phase3HorizonScaled C₃ n γ) x ≤
        ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k :=
    (phase3EscapeMass_le_reconciled_hitProb h3 hentry.1 hsize haLo).trans
      hdynamic
  have hescape :
      phase3EscapeMass n (phase3HorizonScaled C₃ n γ) x ≤
        phase3ReconciledFellerError n γ aLo bHi := by
    exact hescapeExact.trans (by
      unfold phase3ReconciledFellerError
      exact pow_le_pow_right_of_le_one' hbase hkmin)
  calc
    (∑' z, if IsXMajority n z then 0 else
        iter (triChain n) (phase3HorizonScaled C₃ n γ) x z) ≤
        expect (iter (phase3Stop n) (phase3HorizonScaled C₃ n γ) x)
            (phase3StoppedPotential n) +
          phase3EscapeMass n (phase3HorizonScaled C₃ n γ) x :=
      phase3_failure_le_expect_add_escape n
        (phase3HorizonScaled C₃ n γ) x h3
    _ ≤ phase3ScaledPotentialError C₃ n γ +
        phase3ReconciledFellerError n γ aLo bHi :=
      add_le_add hpotential hescape
    _ = phase3ScaledError C₃ n γ aLo bHi := rfl

#print axioms phase3_initial_power_le_rpow
#print axioms phase3ScaledPotentialError_le_real
#print axioms phase3_scaled_real_error_bound
#print axioms phase3ScaledPotentialError_le_inverse
#print axioms phase3_reaches_scaled

end Tri
