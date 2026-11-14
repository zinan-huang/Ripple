-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHourWork.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCore

/-!
# Rounded Main work allowances inside the raw hour window

The strict raw-width bound 70*n^2 < C*D implies both work allowances
used by ClockCore. Every ceiling is retained. The proof only needs
1 <= C <= M, C <= n, and 1 <= n; the seed density interval supplies C <= M.

This is the deterministic numerical implication after a raw-width event
has been established. Embedded Clock time alone is not used as raw time.
-/

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourWork

open TimeTheorem PairLog PhaseThreeClockCore

theorem rounded_work_of_ratios (x y : ℝ) (D : ℕ)
    (hx : 1 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) (hD : 70 * x < (D : ℝ)) :
    Nat.ceil (2 * x) + Nat.ceil (47 * y) + 1 ≤ D ∧
      Nat.ceil (51 * y) ≤ D := by
  have hfirst := Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * x)
  have hsecond := Nat.ceil_lt_add_one (by positivity : 0 ≤ 47 * y)
  have hthird := Nat.ceil_lt_add_one (by positivity : 0 ≤ 51 * y)
  constructor
  · have hreal :
        ((Nat.ceil (2 * x) + Nat.ceil (47 * y) + 1 : ℕ) : ℝ) ≤ D := by
      push_cast
      linarith
    exact_mod_cast hreal
  · have hreal : (Nat.ceil (51 * y) : ℝ) ≤ D := by linarith
    exact_mod_cast hreal

theorem work_allowances_of_raw_width (n C M D : ℕ)
    (hn : 1 ≤ n) (hC : 1 ≤ C) (hCM : C ≤ M) (hCn : C ≤ n)
    (hwidth : 70 * n ^ 2 < C * D) :
    Nat.ceil ((2 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ)) +
        Nat.ceil ((47 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ)) + 1 ≤ D ∧
      Nat.ceil ((51 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ)) ≤ D := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hCMR : (C : ℝ) ≤ M := by exact_mod_cast hCM
  have hCnR : (C : ℝ) ≤ n := by exact_mod_cast hCn
  have hCp : (0 : ℝ) < C := by linarith
  have hMp : (0 : ℝ) < M := by linarith
  let x : ℝ := (n : ℝ) ^ 2 / (C : ℝ)
  let y : ℝ := (n : ℝ) ^ 2 / (M : ℝ)
  have hx : 1 ≤ x := by
    apply (le_div_iff₀ hCp).2
    have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ n)
      (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1)
    nlinarith
  have hy : 0 ≤ y := div_nonneg (sq_nonneg _) hMp.le
  have hyx : y ≤ x := by
    apply (div_le_div_iff₀ hMp hCp).2
    exact mul_le_mul_of_nonneg_left hCMR (sq_nonneg _)
  have hwidthR : 70 * (n : ℝ) ^ 2 < (C : ℝ) * (D : ℝ) := by
    exact_mod_cast hwidth
  have hdiv : 70 * (n : ℝ) ^ 2 / (C : ℝ) < (D : ℝ) :=
    (div_lt_iff₀ hCp).2 (by nlinarith only [hwidthR])
  have hD : 70 * x < (D : ℝ) := by
    simpa only [x, mul_div_assoc] using hdiv
  have h := rounded_work_of_ratios x y D hx hy hyx hD
  have hxreal : 2 * x = (2 : ℝ) * (n : ℝ) ^ 2 / (C : ℝ) := by
    dsimp only [x]
    ring
  have hyfirst : 47 * y = (47 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ) := by
    dsimp only [y]
    ring
  have hysecond : 51 * y = (51 : ℝ) * (n : ℝ) ^ 2 / (M : ℝ) := by
    dsimp only [y]
    ring
  rw [hxreal, hyfirst, hysecond] at h
  exact h

theorem clock_le_main_of_density (n C M : ℕ)
    (hmain : 12 * n ≤ 25 * M) (hclock : 25 * C ≤ 7 * n) :
    C ≤ M := by omega

/-- Both work fields of ClockCore follow from its raw-width field and
seed density bounds. There is no separate probabilistic work event. -/
theorem core_work_allowances_of_raw_width {n : ℕ} (init : InputCfg n)
    (cfg : ℕ → InputCfg n)
    (S : ℕ) (w : StageEventSpec.ClockTimes init)
    (hn : 1 ≤ n)
    (hC : 1 ≤ StageEventSpec.clockCount (cfg S))
    (hCn : StageEventSpec.clockCount (cfg S) ≤ n)
    (hdensity : 12 * n ≤ 25 * timeMainCount (cfg S) ∧
      25 * StageEventSpec.clockCount (cfg S) ≤ 7 * n)
    (hwidth : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
      70 * n ^ 2 <
        StageEventSpec.clockCount (cfg S) * (w.finish h - w.start h)) :
    (∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
      Nat.ceil ((2 : ℝ) * (n : ℝ) ^ 2 / (StageEventSpec.clockCount (cfg S) : ℝ)) +
        Nat.ceil ((47 : ℝ) * (n : ℝ) ^ 2 / (timeMainCount (cfg S) : ℝ)) + 1 ≤
          w.finish h - w.start h) ∧
    (∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
      Nat.ceil ((51 : ℝ) * (n : ℝ) ^ 2 / (timeMainCount (cfg S) : ℝ)) ≤
        w.finish h - w.start h) := by
  have hCM := clock_le_main_of_density n (StageEventSpec.clockCount (cfg S))
    (timeMainCount (cfg S)) hdensity.1 hdensity.2
  constructor
  · intro h hh
    exact (work_allowances_of_raw_width n _ _ _ hn hC hCM hCn (hwidth h hh)).1
  · intro h hh
    exact (work_allowances_of_raw_width n _ _ _ hn hC hCM hCn (hwidth h hh)).2

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourWork

end
