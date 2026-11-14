-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedTwoLevelArithmetic.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalDebtDeadlines

/-!
# Rounding and the physical window for the two-level service

Natural subtraction implements the positive part in the stopped barrier.
The .002 and .009 ceilings cost two units in the majority alternative;
the .018 and .009 ceilings together with the floor cost three in the debt
alternative. The clock calculation retains the role ratio C/M <= 7/12
and pays both raw-time ceilings.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem StageEventSpec
open AveragingNumerics AveragingTerminalDebtDeadlines

/-- Integer form of max(0, min(X - ceil(.002 M), floor(Y) - ceil(.018 M))). -/
def twoLevelBarrier (M X : ℕ) (Y : ℚ) : ℕ :=
  min (X - Nat.ceil ((1 / 500 : ℚ) * M))
    (Nat.floor Y - Nat.ceil ((9 / 500 : ℚ) * M))

def twoLevelTarget (M : ℕ) : ℕ :=
  Nat.ceil ((9 / 1000 : ℚ) * M)

def twoLevelTrials (n M : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ) * ((n : ℝ) - 1) / (twoLevelTarget M : ℝ))

theorem twoLevelTarget_ge (M : ℕ) :
    (9 / 1000 : ℚ) * M ≤ (twoLevelTarget M : ℚ) :=
  Nat.le_ceil _

theorem twoLevelTarget_ge_real (M : ℕ) :
    (9 / 1000 : ℝ) * M ≤ (twoLevelTarget M : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).2 (twoLevelTarget_ge M)
  push_cast at h
  exact h

theorem twoLevelTarget_pos {M : ℕ} (hM : 0 < M) :
    0 < twoLevelTarget M := by
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hpos : (0 : ℚ) < (twoLevelTarget M : ℚ) :=
    lt_of_lt_of_le (by positivity) (twoLevelTarget_ge M)
  exact_mod_cast hpos

theorem twoLevelTarget_pos_real {M : ℕ} (hM : 0 < M) :
    (0 : ℝ) < (twoLevelTarget M : ℝ) := by
  exact_mod_cast twoLevelTarget_pos hM

theorem twoLevelTarget_le (M : ℕ) :
    twoLevelTarget M ≤ M := by
  apply Nat.ceil_le.mpr
  have hM : (0 : ℚ) ≤ M := Nat.cast_nonneg M
  linarith

/-- Keep the rounding losses explicit before using the population threshold. -/
theorem two_level_alternative_with_rounding (M X : ℕ) (Y : ℚ)
    (hJ : twoLevelBarrier M X Y ≤ twoLevelTarget M) :
    (X : ℚ) < (11 / 1000 : ℚ) * M + 2 ∨
      Y < (27 / 1000 : ℚ) * M + 3 := by
  have ha : (Nat.ceil ((1 / 500 : ℚ) * M) : ℚ) <
      (1 / 500 : ℚ) * M + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hb : (Nat.ceil ((9 / 500 : ℚ) * M) : ℚ) <
      (9 / 500 : ℚ) * M + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have ht : (twoLevelTarget M : ℚ) <
      (9 / 1000 : ℚ) * M + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hcases :
      X ≤ Nat.ceil ((1 / 500 : ℚ) * M) + twoLevelTarget M ∨
        Nat.floor Y ≤ Nat.ceil ((9 / 500 : ℚ) * M) + twoLevelTarget M := by
    unfold twoLevelBarrier at hJ
    rcases le_total
      (X - Nat.ceil ((1 / 500 : ℚ) * M))
      (Nat.floor Y - Nat.ceil ((9 / 500 : ℚ) * M)) with h | h
    · rw [min_eq_left h] at hJ
      exact Or.inl (by omega)
    · rw [min_eq_right h] at hJ
      exact Or.inr (by omega)
  rcases hcases with hx | hy
  · left
    have hxq : (X : ℚ) ≤ (Nat.ceil ((1 / 500 : ℚ) * M) : ℚ) +
        (twoLevelTarget M : ℚ) := by exact_mod_cast hx
    linarith only [hxq, ha, ht]
  · right
    have hyq : (Nat.floor Y : ℚ) ≤
        (Nat.ceil ((9 / 500 : ℚ) * M) : ℚ) +
          (twoLevelTarget M : ℚ) := by exact_mod_cast hy
    have hfloor := Nat.lt_floor_add_one Y
    linarith only [hyq, hb, ht, hfloor]

theorem two_level_alternative (M X : ℕ) (Y : ℚ)
    (hM : 30000 ≤ M)
    (hJ : twoLevelBarrier M X Y ≤ twoLevelTarget M) :
    (X : ℚ) ≤ (111 / 10000 : ℚ) * M ∨
      Y ≤ (271 / 10000 : ℚ) * M := by
  have hMr : (30000 : ℚ) ≤ M := by exact_mod_cast hM
  rcases two_level_alternative_with_rounding M X Y hJ with hx | hy
  · exact Or.inl (by linarith only [hx, hMr])
  · exact Or.inr (by linarith only [hy, hMr])

/-- Public logarithmic bounds suffice; no enormous natural power is evaluated. -/
theorem main_count_large_for_two_level_rounding {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) :
    30000 ≤ M := by
  have hm := mass_log_comparison hn hmain
  have hl := Calibration.population_log_lower hn
  have hMr : (30000 : ℝ) ≤ M := by linarith only [hm, hl]
  exact_mod_cast hMr

theorem twoLevelTrials_deadline (n M : ℕ) :
    (n : ℝ) * ((n : ℝ) - 1) / (twoLevelTarget M : ℝ) ≤
      (twoLevelTrials n M : ℝ) :=
  Nat.le_ceil _

theorem two_level_work_below_hour (n C M : ℕ)
    (hn : 12 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hCcard : C ≤ n) (hratio : 12 * C ≤ 7 * M) :
    ((clockWarmup n C + twoLevelTrials n M : ℕ) : ℝ) <
      (70 : ℝ) * (n : ℝ) ^ 2 / C := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hbp := twoLevelTarget_pos_real hM
  have hnreal : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hCr : (C : ℝ) ≤ n := by exact_mod_cast hCcard
  have hratioR : (12 : ℝ) * C ≤ 7 * M := by exact_mod_cast hratio
  have hNnonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    exact mul_nonneg hnnonneg (by linarith only [hnreal])
  have hw : (clockWarmup n C : ℝ) <
      (5 : ℝ) * (n : ℝ) ^ 2 / C + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have ht : (twoLevelTrials n M : ℝ) <
      (n : ℝ) * ((n : ℝ) - 1) / (twoLevelTarget M : ℝ) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hNnonneg hbp.le)
  have hservice :
      (n : ℝ) * ((n : ℝ) - 1) / (twoLevelTarget M : ℝ) ≤
        (1000 / 9 : ℝ) * (n : ℝ) ^ 2 / M := by
    apply (div_le_iff₀ hbp).2
    have hmul := mul_le_mul_of_nonneg_left (twoLevelTarget_ge_real M)
      (show 0 ≤ (1000 / 9 : ℝ) * (n : ℝ) ^ 2 / M by positivity)
    have heq : ((1000 / 9 : ℝ) * (n : ℝ) ^ 2 / M) *
        ((9 / 1000 : ℝ) * M) = (n : ℝ) ^ 2 := by
      field_simp [ne_of_gt hMp]
      <;> ring
    rw [heq] at hmul
    nlinarith only [hmul, hnnonneg]
  have hquot : (1000 / 9 : ℝ) / M ≤ (1750 / 27 : ℝ) / C := by
    apply (div_le_div_iff₀ hMp hCp).2
    nlinarith only [hratioR]
  have hwork : (1000 / 9 : ℝ) * (n : ℝ) ^ 2 / M ≤
      (1750 / 27 : ℝ) * (n : ℝ) ^ 2 / C := by
    have hs := mul_le_mul_of_nonneg_left hquot (sq_nonneg (n : ℝ))
    convert hs using 1 <;> ring
  have hunit : (12 : ℝ) ≤ (n : ℝ) ^ 2 / C := by
    apply (le_div_iff₀ hCp).2
    have hnprod := mul_nonneg hnnonneg
      (show (0 : ℝ) ≤ (n : ℝ) - 12 by linarith only [hnreal])
    nlinarith only [hnprod, hCr]
  push_cast
  have ew : (5 : ℝ) * (n : ℝ) ^ 2 / C =
      5 * ((n : ℝ) ^ 2 / C) := mul_div_assoc _ _ _
  have et : (70 : ℝ) * (n : ℝ) ^ 2 / C =
      70 * ((n : ℝ) ^ 2 / C) := mul_div_assoc _ _ _
  have es : (1750 / 27 : ℝ) * (n : ℝ) ^ 2 / C =
      1750 / 27 * ((n : ℝ) ^ 2 / C) := mul_div_assoc _ _ _
  linarith only [hw, ht, hservice, hwork, hunit, ew, et, es]

theorem two_level_work_fits_window (n C M width : ℕ)
    (hn : 12 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hCcard : C ≤ n) (hratio : 12 * C ≤ 7 * M)
    (hwidth : 70 * n ^ 2 < C * width) :
    clockWarmup n C + twoLevelTrials n M < width := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  have hw : (70 : ℝ) * (n : ℝ) ^ 2 < (C : ℝ) * width := by
    exact_mod_cast hwidth
  have hdiv : (70 : ℝ) * (n : ℝ) ^ 2 / C < width :=
    (div_lt_iff₀ hCp).2 (by simpa only [mul_comm] using hw)
  have h := (two_level_work_below_hour n C M hn hC hM hCcard hratio).trans hdiv
  exact_mod_cast h

theorem two_level_work_fits_clock_history {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    {w : ClockTimes init} (H : ClockHistory init ω S T ρ w)
    (hn : timePopulationThreshold ≤ n) (h : ℕ)
    (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
    w.start h + clockWarmup n (clockCount (trace init ω S)) +
        twoLevelTrials n (timeMainCount (trace init ω S)) < w.finish h := by
  have hST := AveragingEventInterface.clockHistory_seed_lt_exit H
  have hSρ : S < ρ := lt_of_le_of_lt hST.1 hST.2
  have hd := H.density S le_rfl hSρ
  have hnforty : 40 ≤ n := (time_population_bounds hn).2
  have hC : 0 < clockCount (trace init ω S) := by omega
  have hM : 0 < timeMainCount (trace init ω S) := by omega
  have hCcard : clockCount (trace init ω S) ≤ n := by omega
  have hratio : 12 * clockCount (trace init ω S) ≤
      7 * timeMainCount (trace init ω S) := by omega
  have hfit := two_level_work_fits_window n
    (clockCount (trace init ω S)) (timeMainCount (trace init ω S))
    (w.finish h - w.start h) (by omega) hC hM hCcard hratio (H.raw_width h hh)
  omega

theorem two_level_service_tail_le_inverse_power {n M : ℕ}
    (hn : timePopulationThreshold ≤ n) (hmain : 12 * n ≤ 25 * M) :
    Real.exp (-(twoLevelTarget M : ℝ) / 6) ≤ 1 / (n : ℝ) ^ 20 := by
  have hb := twoLevelTarget_ge_real M
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  calc
    Real.exp (-(twoLevelTarget M : ℝ) / 6) ≤ Real.exp (-(M : ℝ) / 1000) :=
      Real.exp_le_exp.mpr (by linarith only [hb, hM])
    _ ≤ 1 / (n : ℝ) ^ 20 := mass_tail_le_inverse_power hn hmain

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
