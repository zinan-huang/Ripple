import Ripple.Probability.CountingBridge.Hitting

/-! # Survival probabilities and null non-hitting paths

The finite-word survival events decrease to the event of never hitting the target.
Continuity from above converts the rational survival criterion to a null-set statement.
-/

open MeasureTheory
open scoped ENNReal

namespace Ripple.CountingBridge

open Words FirstHit

variable {S α : Type*} [Fintype α] (next : S → α → S) (P : S → Prop) (x : S)

private theorem ofReal_ratio [Nonempty α] (a T : ℕ) :
    ENNReal.ofReal (((a : ℚ) / (Fintype.card α : ℚ) ^ T : ℚ) : ℝ) =
      (a : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ T := by
  have hn : 0 < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
    ENNReal.ofReal_div_of_pos (pow_pos hn T), ENNReal.ofReal_pow hn.le, ENNReal.ofReal_natCast]

variable [Nonempty α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

private theorem measure_of_word_indicator (T : ℕ) (f : Word α → ℕ)
    (s : Set (ℕ → α)) (hs : MeasurableSet s)
    (hf : ∀ ω, (f («prefix» T ω) : ℝ≥0∞) = s.indicator 1 ω) :
    μ α s = (wordSum α T f : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ T := by
  rw [← lintegral_indicator_one hs]
  exact (lintegral_congr fun ω => (hf ω).symm).trans (lintegral_word_function T f)

/-- The probability of surviving strictly past time `T` is the number of surviving words
of length `T` divided by `card α ^ T`. -/
theorem survival_measure_count (T : ℕ) :
    μ α {ω | (T : ℕ∞) < τ next P x ω} =
      (survivalNumerator next P x T : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ T := by
  classical
  apply measure_of_word_indicator T (survivalWord next P x) _
    ((measurable_τ next P x) (MeasurableSet.of_discrete (s := Set.Ioi (T : ℕ∞))))
  intro ω
  by_cases h : (T : ℕ∞) < τ next P x ω <;> simp [survivalWord_prefix, Set.indicator, h]

/-- Survival probability as a rational, cast explicitly through the real numbers. -/
theorem survival_measure (T : ℕ) :
    μ α {ω | (T : ℕ∞) < τ next P x ω} =
      ENNReal.ofReal (survivalProb next P x T : ℝ) := by
  rw [survivalProb, ofReal_ratio]
  exact survival_measure_count next P x T

/-- The rational truncated expectation is the integral of the truncated hitting time. -/
theorem truncatedExpectation_eq_lintegral (T : ℕ) :
    ENNReal.ofReal (truncatedExpectation next P x T : ℝ) =
      ∫⁻ ω, min (τ next P x ω : ℝ≥0∞) T ∂μ α := by
  rw [truncatedExpectation, ofReal_ratio]
  exact (lintegral_min_hit_eq next P x T).symm

/-- The point mass at a finite time is the rational first-hit probability. -/
theorem firstHit_measure (T : ℕ) :
    μ α {ω | τ next P x ω = (T : ℕ∞)} =
      ENNReal.ofReal (firstHitProb next P x T : ℝ) := by
  classical
  rw [firstHitProb, ofReal_ratio]
  apply measure_of_word_indicator T (firstHitWord next P x) _
    ((measurable_τ next P x) (measurableSet_singleton _))
  intro ω
  by_cases h : τ next P x ω = (T : ℕ∞) <;> simp [firstHitWord_prefix, Set.indicator, h]

/-- Vanishing survival probabilities are equivalent to almost-sure hitting. -/
theorem ae_hits_iff :
    AlmostSurelyHits next P x ↔ μ α {ω | τ next P x ω = ⊤} = 0 := by
  let A (t : ℕ) := {ω | (t : ℕ∞) < τ next P x ω}
  have hm (t : ℕ) : MeasurableSet (A t) :=
    (measurable_τ next P x) (MeasurableSet.of_discrete (s := Set.Ioi (t : ℕ∞)))
  have hanti : Antitone A := by
    intro i j hij ω hj
    exact lt_of_le_of_lt (show (i : ℕ∞) ≤ j from Nat.cast_le.mpr hij)
      (show (j : ℕ∞) < τ next P x ω from hj)
  have hset : {ω | τ next P x ω = ⊤} = ⋂ t, A t := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, A]
    cases h : τ next P x ω using ENat.recTopCoe with
    | top => simp
    | coe k =>
      refine iff_of_false (by simp) (fun hall => ?_)
      exact (lt_irrefl _) (hall k)
  rw [hset, hanti.measure_iInter (fun i => (hm i).nullMeasurableSet)
    ⟨0, measure_ne_top (μ α) _⟩]
  have hrat (m t : ℕ) : (m : ℚ) * survivalProb next P x t ≤ 1 ↔
      (m : ℝ≥0∞) * μ α (A t) ≤ 1 := by
    have hmass : μ α (A t) = ENNReal.ofReal (survivalProb next P x t : ℝ) :=
      (survival_measure_count next P x t).trans (ofReal_ratio _ _).symm
    rw [hmass, ← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (Nat.cast_nonneg m),
      ENNReal.ofReal_le_one]
    exact_mod_cast Iff.rfl
  constructor
  · intro h
    by_contra hpos
    obtain ⟨m, hlarge⟩ := ENNReal.exists_nat_mul_gt hpos ENNReal.one_ne_top
    obtain ⟨t, ht⟩ := h m
    exact (not_lt_of_ge ((mul_le_mul_right (iInf_le (fun j => μ α (A j)) t) _).trans
      ((hrat m t).mp ht))) hlarge
  · intro h m
    by_cases hz : m = 0
    · exact ⟨0, by simp [hz]⟩
    have hmz : (m : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hz
    have hlt : (⨅ i, μ α (A i)) < (m : ℝ≥0∞)⁻¹ := by simp [h]
    obtain ⟨t, ht⟩ := iInf_lt_iff.mp hlt
    refine ⟨t, (hrat m t).mpr ?_⟩
    rw [ENNReal.mul_le_iff_le_inv hmz (ENNReal.natCast_ne_top m), mul_one]
    exact ht.le

end Ripple.CountingBridge
