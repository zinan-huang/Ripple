/-
Epidemic time (Doty et al. Lemma 4.5).

Reference: Doty et al. Lemma 4.5; relies on Theorem 4.3 (Janson) +
Corollary 4.4.

Setting: starting with `a · n` infected agents in a population of `n`,
the epidemic process `i, s → i, i` (one infected agent infects one
susceptible) reaches `b · n` infected at expected parallel time

  E[t] = (ln(b) - ln(1−b) - ln(a) + ln(1−a)) / 2
       = (1/2) · ln(b·(1−a) / (a·(1−b))).

By Corollary 4.4, with very high probability
  (1 − ε) E[t] < t < (1 + ε) E[t]
fails with probability bounded by `exp(-Θ(ε² · E[t] · n · c))` where
`c = min(a, 1−b)`.

This file proves the epidemic-time formula facts available in the current
development and records the final concentration combination as a conditional
theorem from already-proved one-sided tail bounds.  The geometric waiting-time
coupling and Janson estimates still need to be connected separately.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Epidemic
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.JansonGeometric

open MeasureTheory ProbabilityTheory
open scoped Real BigOperators ENNReal

namespace ExactMajority

/-- Alias for the canonical expected epidemic time from `Epidemic.lean`.

This keeps the older `epidemicTime` API used by the Janson-facing file while
avoiding a second copy of the formula. -/
noncomputable abbrev epidemicTime (a b : ℝ) : ℝ :=
  epidemicExpectedTime a b

/-- The two epidemic-time names are definitionally the same. -/
theorem epidemicTime_eq_epidemicExpectedTime (a b : ℝ) :
    epidemicTime a b = epidemicExpectedTime a b := rfl

/-- The expected epidemic time is positive when `0 < a < b < 1`. -/
theorem epidemicTime_pos (a b : ℝ) (_ha : 0 < a) (_hab : a < b) (_hb : b < 1) :
    0 < epidemicTime a b := by
  exact epidemicExpectedTime_pos a b _ha _hab _hb

/-- Conditional form of **Doty Lemma 4.5 concentration**.

For an epidemic process on `n` agents going from infected fraction `a` to
fraction `b`, with hitting time `T : Ω → ℝ` on probability space
`(Ω, P)`, the parallel time `t = T / n` satisfies
  `P[|t − E[t]| > ε · E[t]] ≤ exp(-Θ(ε² · E[t] · n · min(a, 1−b)))`.

The full lemma is derived from Janson's geometric concentration applied to the
sum of the per-step geometric waiting times.

This only applies the union-bound/complement step after the two one-sided tail
estimates have been supplied, with the analytic constant loss already absorbed. -/
theorem epidemicTime_concentration_of_tail_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ) (_hT : AEMeasurable T P)
    (a b ε : ℝ)
    (_ha : 0 < a) (_hab : a < b) (_hb : b < 1) (_hε : 0 < ε)
    (n : ℕ) (_hn : 0 < n)
    (h_upper : P.real {ω | (1 + ε) * epidemicTime a b ≤ T ω} ≤
      (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 *
        epidemicTime a b * (n : ℝ) * min a (1 - b))))
    (h_lower : P.real {ω | T ω ≤ (1 - ε) * epidemicTime a b} ≤
      (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 *
        epidemicTime a b * (n : ℝ) * min a (1 - b)))) :
    ∃ C : ℝ, 0 < C ∧
      P.real {ω | |T ω - epidemicTime a b| >
                  ε * epidemicTime a b} ≤
        Real.exp (- C * ε ^ 2 * (epidemicTime a b) * (n : ℝ) *
                  min a (1 - b)) := by
  let E : ℝ := epidemicTime a b
  let r : ℝ :=
    Real.exp (-((1 / 8 : ℝ) * ε ^ 2 * E * (n : ℝ) * min a (1 - b)))
  set A := {ω | (1 + ε) * E < T ω}
  set B := {ω | T ω < (1 - ε) * E}
  have hA : P.real A ≤ (1 / 2 : ℝ) * r := by
    exact (measureReal_mono (μ := P) (s₁ := A)
      (s₂ := {ω | (1 + ε) * epidemicTime a b ≤ T ω})
      (by
        intro ω hω
        change (1 + ε) * E < T ω at hω
        exact le_of_lt (by simpa [E] using hω))).trans (by simpa [r, E] using h_upper)
  have hB : P.real B ≤ (1 / 2 : ℝ) * r := by
    exact (measureReal_mono (μ := P) (s₁ := B)
      (s₂ := {ω | T ω ≤ (1 - ε) * epidemicTime a b})
      (by
        intro ω hω
        change T ω < (1 - ε) * E at hω
        exact le_of_lt (by simpa [E] using hω))).trans (by simpa [r, E] using h_lower)
  have h_union : P.real (A ∪ B) ≤ r := by
    calc
      P.real (A ∪ B) ≤ P.real A + P.real B := measureReal_union_le A B
      _ ≤ (1 / 2 : ℝ) * r + (1 / 2 : ℝ) * r := add_le_add hA hB
      _ = r := by ring
  have h_event_subset :
      {ω | |T ω - epidemicTime a b| > ε * epidemicTime a b} ⊆ A ∪ B := by
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
  exact (measureReal_mono (μ := P) h_event_subset).trans (by simpa [r, E] using h_union)

end ExactMajority
