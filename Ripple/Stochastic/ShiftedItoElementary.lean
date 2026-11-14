import Ripple.Stochastic.StrongSDEShortWindows
import Ripple.Stochastic.BoundedStochasticExponential

/-!
# Deterministic translation of elementary Itô integrals

The identity is exact for the finite increment sums, on
every sample and at every time. Extension of this identity to the completed
predictable domain is a separate obligation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Ripple.Stochastic.StrongSDEShortWindows
open BoundedStochasticExponential

variable {Ω : Type*}

/-- Translation commutes with stopping at a deterministic elapsed time. -/
theorem translated_min (a u t : ℝ≥0) : min (a + u) (a + t) = a + min u t := by
  rcases le_total u t with h | h
  · rw [min_eq_left h, min_eq_left (add_le_add le_rfl h)]
  · rw [min_eq_right h, min_eq_right (add_le_add le_rfl h)]

/-- The basepoint subtraction cancels in every elementary increment. -/
theorem shifted_simpleSum (B : ℝ≥0 → Ω → ℝ) (a : ℝ≥0)
    (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    simpleSum (shiftedDriver B a) s c n t ω =
      simpleSum B (fun k => a + s k) c n (a + t) ω := by
  unfold simpleSum
  apply Finset.sum_congr rfl
  intro k _
  simp only [shiftedDriver, translated_min]
  ring

/-- Translating a time window preserves every compensator increment. -/
theorem shifted_simpleBracket (a : ℝ≥0) (s : ℕ → ℝ≥0)
    (c : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    simpleBracket s c n t ω =
      simpleBracket (fun k => a + s k) c n (a + t) ω := by
  unfold simpleBracket
  apply Finset.sum_congr rfl
  intro k _
  simp only [translated_min, NNReal.coe_add, NNReal.coe_min, min_add_add_left]
  ring

/-- The translated sum starts at zero at the physical beginning of its window. -/
theorem translated_simpleSum_initial (B : ℝ≥0 → Ω → ℝ) (a : ℝ≥0)
    (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    simpleSum B (fun k => a + s k) c n a ω = 0 := by
  have h := shifted_simpleSum B a s c n 0 ω
  simpa only [simpleSum, min_zero, shiftedDriver, add_zero, sub_self, mul_zero,
    Finset.sum_const_zero] using h.symm

end Ripple.Stochastic.StrongSDEShortWindows
