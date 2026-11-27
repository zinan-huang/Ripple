import Ripple.Probability.CountingBridge.Events
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Waiting for a letter from a fixed set

The Boolean state records whether a letter from a nonempty set `G` of good letters has
appeared. The number of words of length `T` without a good letter is
`(card α - card G) ^ T`, and summing the corresponding survival probabilities gives the
expected first hitting time `card α / card G`. For `α = Fin n` and `G` the letters below
`k`, this is the mean `n / k` of a geometric waiting time.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Ripple.CountingBridge

open Words FirstHit

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The state becomes true at the first letter in `G` and stays true. -/
def geometricStep (G : Finset α) (x : Bool) (e : α) : Bool :=
  x || decide (e ∈ G)

/-- Under the uniform letter law a fresh letter lies in `G` with probability
`card G / card α`. -/
theorem geometric_success_measure [Nonempty α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (G : Finset α) :
    μ α {ω | geometricStep G false (ω 0) = true} = (G.card : ℝ≥0∞) / Fintype.card α := by
  have hset : {ω : ℕ → α | geometricStep G false (ω 0) = true} =
      (fun ω => ω 0) ⁻¹' (G : Set α) := by
    ext ω
    simp [geometricStep]
  rw [hset, ← Measure.map_apply (measurable_pi_apply 0) G.measurableSet, μ,
    Measure.infinitePi_map_eval]
  change (PMF.uniformOfFintype α).toMeasure (G : Set α) = _
  rw [PMF.toMeasure_uniformOfFintype_apply _ G.measurableSet]
  simp

private theorem geometric_survivors (G : Finset α) (T : ℕ) :
    survivalNumerator (geometricStep G) (· = true) false T =
      (Fintype.card α - G.card) ^ T := by
  let S := survivalWord (geometricStep G) (· = true)
  have hterminal (w : Word α) : S true w = 0 := by
    cases w <;> simp [S, survivalWord]
  have hcard : ((Finset.univ : Finset α).filter (fun e => ¬ e ∈ G)).card =
      Fintype.card α - G.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset α)) (fun e => e ∈ G)
    rw [Finset.filter_univ_mem, Finset.card_univ] at h
    omega
  change wordSum α T (S false) = _
  induction T with
  | zero => simp [wordSum, allWords, S, survivalWord]
  | succ T ih =>
    rw [wordSum_succ]
    calc
      _ = ∑ e : α, if e ∈ G then 0 else (Fintype.card α - G.card) ^ T := by
        refine Finset.sum_congr rfl fun e _ => ?_
        have hstep (w : Word α) : S false (e :: w) =
            if e ∈ G then 0 else S false w := by
          by_cases he : e ∈ G
          · simpa [S, survivalWord, geometricStep, he] using hterminal w
          · simp [S, survivalWord, geometricStep, he]
        by_cases he : e ∈ G
        · simp only [hstep, if_pos he, wordSum_eq_sum_tuples, Finset.sum_const_zero]
        · simpa only [hstep, if_neg he] using ih
      _ = _ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, hcard,
          smul_eq_mul, pow_succ, Nat.mul_comm]

private theorem enat_eq_tsum_tails (a : ℕ∞) :
    (a : ℝ≥0∞) = ∑' t : ℕ, if (t : ℕ∞) < a then (1 : ℝ≥0∞) else 0 := by
  cases a using ENat.recTopCoe with
  | top => simp
  | coe m =>
    simp only [ENat.toENNReal_coe, ENat.natCast_lt_natCast]
    rw [tsum_eq_sum (s := Finset.range m) (fun i hi => if_neg (by simpa using hi))]
    rw [Finset.sum_ite_of_true (fun i hi => Finset.mem_range.mp hi)]
    simp

omit [DecidableEq α] in
/-- The expectation of an extended natural hitting time is the sum of its strict tails. -/
theorem lintegral_hit_eq_tsum_survival {S : Type*} [Nonempty α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (next : S → α → S) (P : S → Prop) (x : S) :
    (∫⁻ ω, (τ next P x ω : ℝ≥0∞) ∂μ α) =
      ∑' t : ℕ, μ α {ω | (t : ℕ∞) < τ next P x ω} := by
  classical
  let A (t : ℕ) := {ω | (t : ℕ∞) < τ next P x ω}
  have hm (t : ℕ) : MeasurableSet (A t) :=
    (measurable_τ next P x) (MeasurableSet.of_discrete (s := Set.Ioi (t : ℕ∞)))
  calc
    _ = ∫⁻ ω, ∑' t, (A t).indicator (1 : (ℕ → α) → ℝ≥0∞) ω ∂μ α := by
      apply lintegral_congr
      intro ω
      simpa only [Set.indicator, A, Set.mem_ofPred_eq, Pi.one_apply] using
        enat_eq_tsum_tails (τ next P x ω)
    _ = _ := by
      rw [lintegral_tsum
        (f := fun t => (A t).indicator (1 : (ℕ → α) → ℝ≥0∞))
        (fun t => (measurable_const.indicator (hm t)).aemeasurable)]
      exact tsum_congr fun t => lintegral_indicator_one (hm t)

/-- Starting before the first good letter, the mean waiting time is `card α / card G`. -/
theorem geometric_hitting_mean [Nonempty α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (G : Finset α) (hG : G.Nonempty) :
    (∫⁻ ω, (τ (geometricStep G) (· = true) false ω : ℝ≥0∞) ∂μ α) =
      (Fintype.card α : ℝ≥0∞) / G.card := by
  have hn : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsub :
      (Fintype.card α : ℝ≥0∞) - (↑(Fintype.card α - G.card) : ℝ≥0∞) = G.card := by
    rw [← ENNReal.natCast_sub, Nat.sub_sub_self (Finset.card_le_univ G)]
  have hp : 1 - (↑(Fintype.card α - G.card) : ℝ≥0∞) / Fintype.card α =
      (G.card : ℝ≥0∞) / Fintype.card α := by
    calc
      _ = (Fintype.card α : ℝ≥0∞) / Fintype.card α -
          (↑(Fintype.card α - G.card) : ℝ≥0∞) / Fintype.card α := by
        rw [ENNReal.div_self hn (by simp)]
      _ = _ := by rw [← ENNReal.sub_div (fun _ _ => hn), hsub]
  rw [lintegral_hit_eq_tsum_survival]
  calc
    _ = ∑' t : ℕ, ((↑(Fintype.card α - G.card) : ℝ≥0∞) / Fintype.card α) ^ t := by
      refine tsum_congr fun t => ?_
      rw [survival_measure_count, geometric_survivors G t, Nat.cast_pow]
      simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
    _ = _ := by
      rw [ENNReal.tsum_geometric, hp, ENNReal.inv_div (Or.inl (by simp))
        (Or.inr (Nat.cast_ne_zero.mpr hG.card_pos.ne'))]

/-- Waiting for a letter below `k` among `n` uniform letters takes `n / k` steps
on average. -/
theorem geometric_hitting_mean_fin (n : ℕ) [NeZero n] (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (∫⁻ ω, (τ (geometricStep ((Finset.univ : Finset (Fin n)).filter fun e => e.val < k))
        (· = true) false ω : ℝ≥0∞) ∂μ (Fin n)) = (n : ℝ≥0∞) / k := by
  have hcard : ((Finset.univ : Finset (Fin n)).filter fun e => e.val < k).card = k := by
    simp [Fin.card_filter_val_lt, Nat.min_eq_right hkn]
  rw [geometric_hitting_mean _ (Finset.card_pos.mp (by rw [hcard]; exact hk)), hcard,
    Fintype.card_fin]

end Ripple.CountingBridge
