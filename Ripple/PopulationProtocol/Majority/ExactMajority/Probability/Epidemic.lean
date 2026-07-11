/-
Epidemic convergence (Lemma 4.5 of Doty et al.).

Lemma 4.5: An epidemic that starts with `a·n` infected agents reaches `b·n`
infected agents in expected parallel time
  `E[t] = (1/2) · ln(b·(1−a) / (a·(1−b)))`
and concentrates:
  `P[|t − E[t]| > ε·E[t]] ≤ exp(−Θ(ε² · E[t] · n · c))`
where `c := min(a, 1−b)`.

This file proves the expected-time positivity fact and the final
union-bound/complement step of the concentration estimate from supplied
one-sided tails.  The remaining epidemic coupling is the derivation of those
one-sided tails from reciprocal-capture waiting times and Janson's geometric
bound.

Reference: Doty et al., Lemma 4.5.
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory
open scoped Real ENNReal
open Set

namespace ExactMajority

/-- Expected parallel time of an epidemic from infected fraction `a` to
fraction `b`. Doty et al. give
`E[t] = (1/2) · ln(b·(1−a) / (a·(1−b)))`. -/
noncomputable def epidemicExpectedTime (a b : ℝ) : ℝ :=
  (Real.log (b * (1 - a) / (a * (1 - b)))) / 2

/-- The expected time is positive whenever `0 < a < b < 1`. -/
theorem epidemicExpectedTime_pos
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    0 < epidemicExpectedTime a b := by
  unfold epidemicExpectedTime
  have h_log_pos : 0 < Real.log (b * (1 - a) / (a * (1 - b))) := by
    apply Real.log_pos
    have h1a : 0 < 1 - a := by linarith
    have h1b : 0 < 1 - b := by linarith
    have hpos : 0 < a * (1 - b) := mul_pos ha h1b
    rw [lt_div_iff₀ hpos, one_mul]
    nlinarith
  positivity

/-- Conditional form of the **epidemic concentration bound** (Doty et al.
Lemma 4.5).

Let `(Ω, μ)` be a probability space, `T : Ω → ℝ` an a.e.-measurable hitting
time random variable for an epidemic from infected fraction `a` to fraction
`b` over `n` agents. Let `E := epidemicExpectedTime a b` and
`c := min a (1 − b)`.

Then for any tolerance `ε > 0`:
  `μ {ω | |T(ω) − E| > ε · E} ≤ exp(−ε² · E · n · c)`.

This theorem performs the deterministic final step once the two one-sided
tail estimates have been supplied with the constant loss already absorbed. -/
theorem epidemic_concentration_of_tail_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → ℝ) (_hT : AEMeasurable T μ)
    (a b ε : ℝ)
    (_ha : 0 < a) (_hab : a < b) (_hb : b < 1) (_hε : 0 < ε)
    (n : ℕ) (_hn : 0 < n)
    (h_upper : μ.real {ω | (1 + ε) * epidemicExpectedTime a b ≤ T ω} ≤
      (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 *
        epidemicExpectedTime a b * (n : ℝ) * min a (1 - b))))
    (h_lower : μ.real {ω | T ω ≤ (1 - ε) * epidemicExpectedTime a b} ≤
      (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 *
        epidemicExpectedTime a b * (n : ℝ) * min a (1 - b)))) :
    ∃ C : ℝ, 0 < C ∧
      μ.real {ω | |T ω - epidemicExpectedTime a b| >
                  ε * epidemicExpectedTime a b} ≤
        Real.exp (- C * ε ^ 2 * epidemicExpectedTime a b * (n : ℝ) *
                  min a (1 - b)) := by
  let E : ℝ := epidemicExpectedTime a b
  let r : ℝ :=
    Real.exp (-((1 / 8 : ℝ) * ε ^ 2 * E * (n : ℝ) * min a (1 - b)))
  set A := {ω | (1 + ε) * E < T ω}
  set B := {ω | T ω < (1 - ε) * E}
  have hA : μ.real A ≤ (1 / 2 : ℝ) * r := by
    exact (measureReal_mono (μ := μ) (s₁ := A)
      (s₂ := {ω | (1 + ε) * epidemicExpectedTime a b ≤ T ω})
      (by
        intro ω hω
        change (1 + ε) * E < T ω at hω
        exact le_of_lt (by simpa [E] using hω))).trans (by simpa [r, E] using h_upper)
  have hB : μ.real B ≤ (1 / 2 : ℝ) * r := by
    exact (measureReal_mono (μ := μ) (s₁ := B)
      (s₂ := {ω | T ω ≤ (1 - ε) * epidemicExpectedTime a b})
      (by
        intro ω hω
        change T ω < (1 - ε) * E at hω
        exact le_of_lt (by simpa [E] using hω))).trans (by simpa [r, E] using h_lower)
  have h_union : μ.real (A ∪ B) ≤ r := by
    calc
      μ.real (A ∪ B) ≤ μ.real A + μ.real B := measureReal_union_le A B
      _ ≤ (1 / 2 : ℝ) * r + (1 / 2 : ℝ) * r := add_le_add hA hB
      _ = r := by ring
  have h_event_subset :
      {ω | |T ω - epidemicExpectedTime a b| > ε * epidemicExpectedTime a b} ⊆ A ∪ B := by
    intro ω hω
    have h_abs : ε * E < |T ω - E| := by
      simpa [E] using hω
    rcases (lt_abs.mp h_abs) with h_hi | h_lo
    · left
      change (1 + ε) * E < T ω
      nlinarith
    · right
      change T ω < (1 - ε) * E
      nlinarith
  refine ⟨1 / 8, by norm_num, ?_⟩
  exact (measureReal_mono (μ := μ) h_event_subset).trans (by simpa [r, E] using h_union)

end ExactMajority
