import Ripple.Probability.CountingBridge.Events

/-! # Rational first-hit moments and the expectation of the hitting time

For an almost surely finite hitting time, its expectation is the supremum of the partial
first moments `∑_{t ≤ K} t * P(τ = t)`. Hence the rational predicate
`ExpectedHittingTimeAtMost` is equivalent to almost-sure hitting together with the bound
on the integral of `τ`.
-/

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Ripple.CountingBridge

open FirstHit

variable {S α : Type*} [Fintype α] (next : S → α → S) (P : S → Prop) (x : S)

private theorem firstHitProb_nonneg (t : ℕ) : 0 ≤ firstHitProb next P x t := by
  unfold firstHitProb
  positivity

private theorem partialExpectation_nonneg (K : ℕ) : 0 ≤ partialExpectation next P x K := by
  induction K with
  | zero => exact le_rfl
  | succ K ih => exact add_nonneg ih (mul_nonneg (Nat.cast_nonneg _) (firstHitProb_nonneg ..))

/-- The rational moment through time `K` is the finite sum of the weighted first-hit masses. -/
private theorem partialExpectation_eq_sum (K : ℕ) :
    ENNReal.ofReal (partialExpectation next P x K : ℝ) =
      ∑ t ∈ Finset.range (K + 1),
        (t : ℝ≥0∞) * ENNReal.ofReal (firstHitProb next P x t : ℝ) := by
  induction K with
  | zero => simp [partialExpectation]
  | succ K ih =>
    have hle : 0 ≤ (partialExpectation next P x K : ℝ) :=
      Rat.cast_nonneg.mpr (partialExpectation_nonneg ..)
    have hp : 0 ≤ (firstHitProb next P x (K + 1) : ℝ) :=
      Rat.cast_nonneg.mpr (firstHitProb_nonneg ..)
    rw [partialExpectation, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
      ENNReal.ofReal_add hle (mul_nonneg (Nat.cast_nonneg _) hp),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ih,
      Finset.sum_range_succ _ (K + 1)]

/-- For an almost surely finite hitting time, every contribution to its integral comes from
one of its finite fibers. -/
theorem lintegral_hit_eq_iSup_partial
    [Nonempty α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (hnull : μ α {ω | τ next P x ω = ⊤} = 0) :
    (∫⁻ ω, (τ next P x ω : ℝ≥0∞) ∂μ α) =
      ⨆ K : ℕ, ENNReal.ofReal (partialExpectation next P x K : ℝ) := by
  let N (ω : ℕ → α) := (τ next P x ω).toNat
  have hm : Measurable N := (measurable_of_countable ENat.toNat).comp (measurable_τ next P x)
  have hfin : ∀ᵐ ω ∂μ α, τ next P x ω ≠ ⊤ := ae_iff.mpr (by simpa using hnull)
  have hmass (k : ℕ) : (k : ℝ≥0∞) * (μ α).map N {k} =
      k * ENNReal.ofReal (firstHitProb next P x k : ℝ) := by
    cases k with
    | zero => simp
    | succ t =>
      rw [Measure.map_apply hm (measurableSet_singleton _)]
      have hset : N ⁻¹' {t + 1} = {ω | τ next P x ω = ((t + 1 : ℕ) : ℕ∞)} := by
        ext ω
        exact ENat.toNat_eq_iff (Nat.succ_ne_zero t)
      rw [hset, firstHit_measure]
  calc
    _ = ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ α := by
      apply lintegral_congr_ae
      filter_upwards [hfin] with ω hω
      simpa only [N, ENat.toENNReal_coe] using congrArg ENat.toENNReal (ENat.natCast_toNat hω).symm
    _ = ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂(μ α).map N :=
      (lintegral_map (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))) hm).symm
    _ = ∑' k : ℕ, (k : ℝ≥0∞) * (μ α).map N {k} := lintegral_countable' _
    _ = ∑' k : ℕ, (k : ℝ≥0∞) * ENNReal.ofReal (firstHitProb next P x k : ℝ) :=
      tsum_congr hmass
    _ = _ := by
      rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)]
      exact iSup_congr fun K => (partialExpectation_eq_sum next P x K).symm

/-- The rational expected-time bound is equivalent to almost-sure hitting and the same
bound on the integral. The nonnegative rational bound is embedded through `ℝ`. -/
theorem expected_iff [Nonempty α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (B : ℚ≥0) :
    ExpectedHittingTimeAtMost next P x (B : ℚ) ↔
      μ α {ω | τ next P x ω = ⊤} = 0 ∧
        (∫⁻ ω, (τ next P x ω : ℝ≥0∞) ∂μ α) ≤
          ENNReal.ofReal ((B : ℚ) : ℝ) := by
  rw [ExpectedHittingTimeAtMost, ae_hits_iff]
  apply and_congr_right
  intro hnull
  rw [lintegral_hit_eq_iSup_partial next P x hnull, iSup_le_iff]
  exact forall_congr' fun K =>
    (Rat.cast_le (K := ℝ)).symm.trans
      (ENNReal.ofReal_le_ofReal_iff (Rat.cast_nonneg.mpr B.property)).symm

/-- For a nonnegative rational bound, the rational expected-time predicate is equivalent
to null non-hitting mass and the integral bound, with both rational casts explicit. -/
theorem expectedHittingTimeAtMost_iff [Nonempty α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (B : ℚ) (hB : 0 ≤ B) :
    ExpectedHittingTimeAtMost next P x B ↔
      μ α {ω | τ next P x ω = ⊤} = 0 ∧
        (∫⁻ ω, (τ next P x ω : ℝ≥0∞) ∂μ α) ≤ ENNReal.ofReal (B : ℝ) := by
  exact expected_iff next P x (⟨B, hB⟩ : ℚ≥0)

end Ripple.CountingBridge
