/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Explicit Phase-6 multiplicative-drift horizon

This file converts the analytic horizon used by the Phase-6 drift engine into
the displayed `O(n (L+1))` interaction bound.  The only quantitative input on
the sampled reserve pool is `n ≤ 25 K₀`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.DriftHorizon
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiBound
import Ripple.PopulationProtocol.ExactMajority.Probability.PaperRegime

namespace Ripple.PopulationProtocol.ExactMajority

/-- The Phase-6 drift horizon fits in `87 n (L+1)` interactions when the
reserve pool has the paper-scale linear floor `n ≤ 25 K₀`. -/
theorem phase6_driftHorizon_le_87
    {n L l K₀ : ℕ}
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L) (hlL : l ≤ L)
    (hK₀linear : n ≤ 25 * K₀) :
    DriftSurvival.driftHorizon (K₀ : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) 2
      ≤ 87 * n * (L + 1) := by
  rw [DriftSurvival.driftHorizon, Nat.ceil_le]
  have hK₀0 : 0 < K₀ := by omega
  have hK₀R0 : (0 : ℝ) < K₀ := by exact_mod_cast hK₀0
  have hpow4 : 4 ^ (l - 1) ≤ 4 ^ L :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPhiNat :
      Phase6PhiPotential.phase6PhiMax n l ≤ 2 ^ (3 * L) := by
    rw [Phase6PhiPotential.phase6PhiMax]
    calc
      n * 4 ^ (l - 1) ≤ 2 ^ L * 4 ^ L := Nat.mul_le_mul hnL hpow4
      _ = 2 ^ (3 * L) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
        congr 1
        omega
  have hSecondNat : 2 * n ^ 2 ≤ 2 ^ (2 * L + 1) := by
    calc
      2 * n ^ 2 ≤ 2 * (2 ^ L) ^ 2 :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hnL 2)
      _ = 2 ^ (2 * L + 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega
  have hPhiPos : 0 < Phase6PhiPotential.phase6PhiMax n l := by
    rw [Phase6PhiPotential.phase6PhiMax]
    positivity
  have hlogPhi :
      Real.log (Phase6PhiPotential.phase6PhiMax n l : ℝ)
        ≤ (3 * L : ℕ) * Real.log 2 := by
    calc
      Real.log (Phase6PhiPotential.phase6PhiMax n l : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (3 * L)) := by
            apply Real.log_le_log
            · exact_mod_cast hPhiPos
            · exact_mod_cast hPhiNat
      _ = (3 * L : ℕ) * Real.log 2 := Real.log_pow 2 (3 * L)
  have hlogSecond :
      Real.log ((2 : ℝ) * n ^ 2)
        ≤ (2 * L + 1 : ℕ) * Real.log 2 := by
    calc
      Real.log ((2 : ℝ) * n ^ 2)
          ≤ Real.log ((2 : ℝ) ^ (2 * L + 1)) := by
            apply Real.log_le_log
            · positivity
            · exact_mod_cast hSecondNat
      _ = (2 * L + 1 : ℕ) * Real.log 2 := Real.log_pow 2 (2 * L + 1)
  have hlogSum :
      Real.log (Phase6PhiPotential.phase6PhiMax n l : ℝ) +
          Real.log ((2 : ℝ) * n ^ 2)
        ≤ (5 * (L : ℝ) + 1) * Real.log 2 := by
    calc
      Real.log (Phase6PhiPotential.phase6PhiMax n l : ℝ) +
            Real.log ((2 : ℝ) * n ^ 2)
          ≤ ((3 * L : ℕ) : ℝ) * Real.log 2 +
              ((2 * L + 1 : ℕ) : ℝ) * Real.log 2 := add_le_add hlogPhi hlogSecond
      _ = (5 * (L : ℝ) + 1) * Real.log 2 := by push_cast; ring
  have hlogSum0 :
      0 ≤ Real.log (Phase6PhiPotential.phase6PhiMax n l : ℝ) +
          Real.log ((2 : ℝ) * n ^ 2) := by
    apply add_nonneg
    · exact Real.log_nonneg (by exact_mod_cast Phase6PhiPotential.one_le_phase6PhiMax n l (by omega))
    · apply Real.log_nonneg
      have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hrate :
      (n : ℝ) * ((n : ℝ) - 1) / K₀ ≤ 25 * n := by
    rw [div_le_iff₀ hK₀R0]
    have hK₀linearR : (n : ℝ) ≤ 25 * K₀ := by exact_mod_cast hK₀linear
    nlinarith
  have hlogConstant :
      25 * ((5 * (L : ℝ) + 1) * Real.log 2)
        ≤ 87 * ((L : ℝ) + 1) := by
    have hfactor : 0 ≤ 25 * (5 * (L : ℝ) + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hfactor
    norm_num at hmul ⊢
    nlinarith
  calc
    (n : ℝ) * ((n : ℝ) - 1) / K₀ *
          (Real.log (Phase6PhiPotential.phase6PhiMax n l : ℝ) +
            Real.log ((2 : ℝ) * n ^ 2))
        ≤ (25 * n) *
          (Real.log (Phase6PhiPotential.phase6PhiMax n l : ℝ) +
            Real.log ((2 : ℝ) * n ^ 2)) :=
      mul_le_mul_of_nonneg_right hrate hlogSum0
    _ ≤ (25 * n) * ((5 * (L : ℝ) + 1) * Real.log 2) := by
      exact mul_le_mul_of_nonneg_left hlogSum (by positivity)
    _ ≤ (n : ℝ) * (87 * ((L : ℝ) + 1)) := by
      nlinarith [hlogConstant]
    _ = (87 * n * (L + 1) : ℕ) := by push_cast; ring

/-- A round-number wrapper for displays that reserve constant `90` for
Phase 6. -/
theorem phase6_driftHorizon_le_90
    {n L l K₀ : ℕ}
    (hn : 2 ≤ n) (hnL : n ≤ 2 ^ L) (hlL : l ≤ L)
    (hK₀linear : n ≤ 25 * K₀) :
    DriftSurvival.driftHorizon (K₀ : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) 2
      ≤ 90 * n * (L + 1) := by
  refine (phase6_driftHorizon_le_87 hn hnL hlL hK₀linear).trans ?_
  gcongr
  norm_num

/-- Paper-regime specialization.  The regime equation
`L = Nat.clog 2 n` supplies the power-of-two population ceiling. -/
theorem phase6_driftHorizon_le_87_of_regime
    {n L K l K₀ : ℕ}
    (hReg : PaperRegime.Regime n L K) (hlL : l ≤ L)
    (hK₀linear : n ≤ 25 * K₀) :
    DriftSurvival.driftHorizon (K₀ : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) 2
      ≤ 87 * n * (L + 1) := by
  apply phase6_driftHorizon_le_87 hReg.two_le_n _ hlL hK₀linear
  rw [hReg.hLlog]
  exact Nat.le_pow_clog (by norm_num) n

#print axioms phase6_driftHorizon_le_87
#print axioms phase6_driftHorizon_le_90
#print axioms phase6_driftHorizon_le_87_of_regime

end Ripple.PopulationProtocol.ExactMajority
