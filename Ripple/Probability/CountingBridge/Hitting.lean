import Ripple.Probability.CountingBridge.WordLaw
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.ENatENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# First hitting times along an infinite letter sequence

The run from `x` reads the letters of `ω` in order. Its hitting time `τ` is the first
time at which the state satisfies `P`; time zero tests the initial state, and a path that
avoids `P` forever has hitting time `⊤`. The word indicators and costs of `Counts`
evaluated on the first `T` letters are the corresponding events and truncations of `τ`.
-/

open MeasureTheory
open scoped ENNReal

namespace Ripple.CountingBridge

open Words FirstHit

variable {S α : Type*}
variable (next : S → α → S) (P : S → Prop)

/-- The state after the first `t` letters, starting at `x`. -/
noncomputable def run (x : S) (ω : ℕ → α) (t : ℕ) : S :=
  («prefix» t ω).foldl next x

private theorem prefix_tail (ω : ℕ → α) (t : ℕ) :
    «prefix» (t + 1) ω = ω 0 :: «prefix» t (fun j => ω (j + 1)) := by
  unfold «prefix»
  rw [List.ofFn_succ]
  rfl

@[simp] theorem run_zero (x : S) (ω : ℕ → α) : run next x ω 0 = x := by
  simp [run, «prefix»]

theorem run_succ_tail (x : S) (ω : ℕ → α) (t : ℕ) :
    run next x ω (t + 1) = run next (next x (ω 0)) (fun j => ω (j + 1)) t := by
  simp [run, prefix_tail]

/-- Every function of the first `T` letters is measurable, for any measurable codomain. -/
private theorem measurable_prefix_function [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [Countable α] {β : Type*} [MeasurableSpace β] (T : ℕ) (f : Word α → β) :
    Measurable fun ω => f («prefix» T ω) :=
  (measurable_of_countable f).comp (measurable_prefix T)

/-- At each fixed time the state is measurable for any measurable space on the states. -/
theorem measurable_run [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    [MeasurableSpace S] (x : S) (T : ℕ) :
    Measurable fun ω => run next x ω T :=
  measurable_prefix_function T (fun w => w.foldl next x)

open Classical in
/-- First time at which the run satisfies `P`, with value `⊤` if no such time exists. -/
noncomputable def τ (x : S) (ω : ℕ → α) : ℕ∞ :=
  if h : ∃ t, P (run next x ω t) then (Nat.find h : ℕ∞) else ⊤

theorem τ_eq_top_iff (x : S) (ω : ℕ → α) :
    τ next P x ω = ⊤ ↔ ∀ t, ¬ P (run next x ω t) := by
  classical
  by_cases h : ∃ t, P (run next x ω t) <;> simp [τ, h, ← not_exists]

theorem τ_eq_zero_iff (x : S) (ω : ℕ → α) : τ next P x ω = 0 ↔ P x := by
  classical
  by_cases h : ∃ t, P (run next x ω t)
  · simp [τ, h, Nat.find_eq_zero]
  · have hx : ¬ P x := fun hp => h ⟨0, by simpa using hp⟩
    simp [τ, h, hx]

/-- After a missed initial test, the first letter advances the clock by one. -/
theorem τ_of_not_target (x : S) (ω : ℕ → α) (hx : ¬ P x) :
    τ next P x ω = τ next P (next x (ω 0)) (fun j => ω (j + 1)) + 1 := by
  classical
  let q := fun t => P (run next x ω t)
  let r := fun t => P (run next (next x (ω 0)) (fun j => ω (j + 1)) t)
  have hshift (i : ℕ) : q (i + 1) ↔ r i := by simp [q, r, run_succ_tail]
  have hz : ¬ q 0 := by simpa [q] using hx
  have hex : (∃ t, q t) ↔ ∃ t, r t := by
    constructor
    · rintro ⟨_ | t, ht⟩
      · exact (hz ht).elim
      · exact ⟨t, (hshift t).mp ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨t + 1, (hshift t).mpr ht⟩
  change (if h : ∃ t, q t then (Nat.find h : ℕ∞) else ⊤) =
    (if h : ∃ t, r t then (Nat.find h : ℕ∞) else ⊤) + 1
  by_cases hq : ∃ t, q t
  · have hr := hex.mp hq
    have hs : ∃ t, q (t + 1) := ⟨Nat.find hr, (hshift _).mpr (Nat.find_spec hr)⟩
    have hf : Nat.find hq = Nat.find hr + 1 :=
      (Nat.find_comp_succ hq hs hz).trans
        (congrArg (· + 1) (Nat.find_congr' (fun {i} => hshift i)))
    simpa only [dif_pos hq, dif_pos hr, Nat.cast_add, Nat.cast_one] using
      congrArg (fun t : ℕ => (t : ℕ∞)) hf
  · have hr := mt hex.mpr hq
    simp only [dif_neg hq, dif_neg hr, top_add]

open Classical in
/-- The survival indicator on a word records strict survival through its endpoint. -/
theorem survivalWord_prefix (x : S) (ω : ℕ → α) (T : ℕ) :
    survivalWord next P x («prefix» T ω) = if (T : ℕ∞) < τ next P x ω then 1 else 0 := by
  classical
  induction T generalizing x ω with
  | zero =>
    by_cases hx : P x <;> simp [«prefix», survivalWord, pos_iff_ne_zero, τ_eq_zero_iff, hx]
  | succ T ih =>
    by_cases hx : P x
    · simp [prefix_tail, survivalWord, hx, (τ_eq_zero_iff next P x ω).mpr hx]
    · simp only [prefix_tail, survivalWord, if_neg hx, τ_of_not_target next P x ω hx,
        Nat.cast_succ, ENat.add_lt_add_iff_right ENat.one_ne_top]
      exact ih _ _

open Classical in
/-- The first-hit indicator selects precisely the paths with a first visit at the endpoint. -/
theorem firstHitWord_prefix (x : S) (ω : ℕ → α) (T : ℕ) :
    firstHitWord next P x («prefix» T ω) = if τ next P x ω = (T : ℕ∞) then 1 else 0 := by
  classical
  induction T generalizing x ω with
  | zero => simp [«prefix», firstHitWord, τ_eq_zero_iff]
  | succ T ih =>
    by_cases hx : P x
    · have hne : (0 : ℕ∞) ≠ ((T + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast (Nat.succ_ne_zero T).symm
      simp only [prefix_tail, firstHitWord, if_pos hx,
        (τ_eq_zero_iff next P x ω).mpr hx, if_neg hne]
    · simp only [prefix_tail, firstHitWord, if_neg hx, τ_of_not_target next P x ω hx,
        Nat.cast_succ, (ENat.add_left_injective_of_ne_top ENat.one_ne_top).eq_iff]
      exact ih _ _

/-- The finite hitting-time fibers are cylinders. They determine measurability into `ℕ∞`. -/
theorem measurable_τ [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    (x : S) : Measurable (τ next P x) := by
  classical
  apply ENat.measurable_iff.mpr
  intro T
  have heq : τ next P x ⁻¹' {(T : ℕ∞)} =
      (fun ω => firstHitWord next P x («prefix» T ω)) ⁻¹' {1} := by
    ext ω
    simp [firstHitWord_prefix, Set.mem_singleton_iff]
  rw [heq]
  exact measurable_prefix_function T (firstHitWord next P x) (measurableSet_singleton 1)

/-- The finite-word cost is the first hitting time truncated at the word length. -/
theorem costWord_prefix (x : S) (ω : ℕ → α) (T : ℕ) :
    (costWord next P x («prefix» T ω) : ℕ∞) = min (τ next P x ω) (T : ℕ∞) := by
  classical
  induction T generalizing x ω with
  | zero => simp [«prefix», costWord]
  | succ T ih =>
    rw [prefix_tail]
    by_cases hx : P x
    · simp [costWord, hx, (τ_eq_zero_iff next P x ω).mpr hx]
    · rw [τ_of_not_target next P x ω hx, Nat.cast_succ, min_add_add_right]
      have hcost (e : α) (w : Word α) :
          costWord next P x (e :: w) = costWord next P (next x e) w + 1 := by
        simp [costWord, hx, Nat.add_comm]
      rw [hcost, Nat.cast_add, Nat.cast_one, ih]

section Uniform

variable [Fintype α] [Nonempty α] [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- The expectation of the hitting time truncated at `T` is the total truncated cost over
words of length `T`, divided by `card α ^ T`. -/
theorem lintegral_min_hit_eq (x : S) (T : ℕ) :
    ∫⁻ ω, min (τ next P x ω : ℝ≥0∞) T ∂μ α =
      (costNumerator next P x T : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ T := by
  calc
    _ = ∫⁻ ω, (costWord next P x («prefix» T ω) : ℝ≥0∞) ∂μ α := by
      apply lintegral_congr
      intro ω
      simpa only [ENat.toENNReal_coe, ENat.toENNReal_min] using
        congrArg ENat.toENNReal (costWord_prefix next P x ω T).symm
    _ = _ := lintegral_word_function T (costWord next P x)

/-- Monotone convergence identifies the expected hitting time, including infinite values. -/
theorem lintegral_hit_eq_iSup (x : S) :
    ∫⁻ ω, (τ next P x ω : ℝ≥0∞) ∂μ α =
      ⨆ T : ℕ, (costNumerator next P x T : ℝ≥0∞) /
        (Fintype.card α : ℝ≥0∞) ^ T := by
  let f (T : ℕ) (ω : ℕ → α) := min (τ next P x ω : ℝ≥0∞) T
  have hsup (ω : ℕ → α) : (τ next P x ω : ℝ≥0∞) = ⨆ T, f T ω := by
    change _ = ⨆ T : ℕ, (τ next P x ω : ℝ≥0∞) ⊓ (T : ℝ≥0∞)
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hm : Measurable (fun ω => (τ next P x ω : ℝ≥0∞)) :=
    (measurable_of_countable ENat.toENNReal).comp (measurable_τ next P x)
  calc
    _ = ∫⁻ ω, ⨆ T, f T ω ∂μ α := lintegral_congr hsup
    _ = ⨆ T, ∫⁻ ω, f T ω ∂μ α := lintegral_iSup (fun _ => hm.min measurable_const)
      (fun _ _ hab ω => min_le_min_left _ (Nat.cast_le.mpr hab))
    _ = _ := iSup_congr fun T => lintegral_min_hit_eq next P x T

end Uniform

end Ripple.CountingBridge
