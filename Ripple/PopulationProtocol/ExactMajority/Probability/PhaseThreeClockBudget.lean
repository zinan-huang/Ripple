import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockExit

/-!
# The §11 budget with the spread window `u = 7` (N12)

With the N08 spread window `logWindow n 7` the spread error is `e^3 n^{-6} ≤ n^{-5}`
for `n ≥ 21`, and the P15 exit-deadline row is `n^{-12} ≤ n^{-5}`. The headline then
needs only the virtual-core tail with budget `6 / n^5` and the exit-deadline tail with
budget `1 / n^12`. Small `n` is excluded by `GoodInput` (`n ≥ 40`), as in N11.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBudget

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer PhaseThreeClockAssembly
  PhaseThreeClockExit

theorem exp_three_le : Real.exp 3 ≤ 21 := by
  have h := Real.exp_one_lt_d9
  have h' : Real.exp 1 ≤ 2.72 := by linarith
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h3]
  calc Real.exp 1 ^ 3 ≤ (2.72 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h' 3
    _ ≤ 21 := by norm_num

theorem spread_term_le {n : ℕ} (hn : 21 ≤ n) :
    Real.exp 3 * Real.rpow (n : ℝ) (1 - ((7 : ℕ) : ℝ)) ≤ 1 / (n : ℝ) ^ 5 := by
  have hnR : (21 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hr : Real.rpow (n : ℝ) (1 - ((7 : ℕ) : ℝ)) = 1 / (n : ℝ) ^ 6 := by
    have : (1 - ((7 : ℕ) : ℝ)) = -((6 : ℕ) : ℝ) := by norm_num
    rw [this, show Real.rpow (n : ℝ) (-((6 : ℕ) : ℝ)) = (n : ℝ) ^ (-((6 : ℕ) : ℝ)) from rfl,
      Real.rpow_neg hpos.le, Real.rpow_natCast, one_div]
  rw [hr]
  have h21 := exp_three_le
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h6 : (n : ℝ) ^ 6 = (n : ℝ) ^ 5 * n := by ring
  rw [h6]
  have hp5 : (0 : ℝ) < (n : ℝ) ^ 5 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hnR hp5.le]

theorem exit_term_le {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) / (n : ℝ) ^ 12 ≤ 1 / (n : ℝ) ^ 5 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ hnR (by norm_num)

/-- The §11 budget: `6 / n^5` for the virtual core, `1 / n^12` for the exit deadline and
the N08 spread error at `u = 7` sum to at most `8 / n^5` for `n ≥ 21`. -/
theorem budget_u7 {n : ℕ} (hn : 21 ≤ n) :
    ENNReal.ofReal (6 / (n : ℝ) ^ 5) +
      (ENNReal.ofReal (1 / (n : ℝ) ^ 12) +
        ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (1 - ((7 : ℕ) : ℝ)))) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) := by
  have hnR : (21 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have h1 : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 12 := by positivity
  have h2 : (0 : ℝ) ≤ Real.exp 3 * Real.rpow (n : ℝ) (1 - ((7 : ℕ) : ℝ)) := by
    have := Real.rpow_nonneg hpos.le (1 - ((7 : ℕ) : ℝ))
    positivity
  rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by positivity) (add_nonneg h1 h2)]
  apply ENNReal.ofReal_le_ofReal
  have hs := spread_term_le hn
  have he := exit_term_le (n := n) (by omega)
  have : (8 : ℝ) / (n : ℝ) ^ 5 = 6 / (n : ℝ) ^ 5 + (1 / (n : ℝ) ^ 5 + 1 / (n : ℝ) ^ 5) := by ring
  rw [this]
  linarith

/-- The N12 headline from the two remaining tails with explicit budgets. -/
theorem asynchronous_clock_estimate_of_tails {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (hcore : law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5))
    (hexit : law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      VirtualGoodAt init s ω ∧ ¬ ExitDeadlineAt init s ω} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 12)) :
    law init (phaseClockFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) := by
  have h40 : 40 ≤ n := (time_population_bounds hinput.1).2
  exact asynchronous_clock_estimate_of_global_inputs init hinput ⟨hcore, hexit⟩ 7
    (by norm_num) (by norm_num) (budget_u7 (by omega))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBudget

end
