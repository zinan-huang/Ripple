import Ripple.Probability.CountingBridge.WordLaw

/-! # First-prefix stopping and uniform continuations

A stopping rule reads the history in chronological order, including the empty
history. At the first accepted history, its continuation event reads the unused
suffix. Uniform bounds for all terminal histories transfer to the initial
history, even when the stopping depth depends on the observed letters.
-/

namespace Ripple.CountingBridge

open MeasureTheory Words
open scoped ENNReal BigOperators

noncomputable section

variable {α : Type*}

/-- The information supplied by the first `T` letters. -/
@[implicit_reducible]
def prefixSigma (T : ℕ) : MeasurableSpace (ℕ → α) :=
  MeasurableSpace.comap («prefix» (α := α) T) ⊤

/-- Taking an initial part of a sampled prefix gives the shorter sampled prefix. -/
theorem prefix_take {S T : ℕ} (h : S ≤ T) (ω : ℕ → α) :
    («prefix» T ω).take S = «prefix» S ω := by
  apply List.ext_getElem
  · simp [«prefix», Nat.min_eq_left h]
  · intro i hi hj
    simp [«prefix»]

/-- Prefix information increases with the observation horizon. -/
theorem prefixSigma_mono {S T : ℕ} (h : S ≤ T) :
    prefixSigma (α := α) S ≤ prefixSigma T := by
  intro A hA
  obtain ⟨B, _, hB⟩ := hA
  refine ⟨(fun w : Word α => w.take S) ⁻¹' B, trivial, ?_⟩
  rw [← hB]
  ext ω
  simp only [Set.mem_preimage, prefix_take h]

/-- Every event determined by a finite prefix is measurable in the product space. -/
theorem prefixSigma_le [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    (T : ℕ) : prefixSigma (α := α) T ≤ (inferInstance : MeasurableSpace (ℕ → α)) := by
  intro s hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact (measurable_prefix T) hA

/-- The cylinder of any predicate on words belongs to the prefix sigma algebra. -/
theorem measurableSet_prefixSigma (T : ℕ) (E : Word α → Prop) :
    MeasurableSet[prefixSigma T] {ω | E («prefix» T ω)} :=
  ⟨{w | E w}, trivial, rfl⟩

/-- A stopping word is accepted by the rule, and none of its proper prefixes is. -/
def IsStoppingPrefix (stop : Word α → Bool) (w : Word α) : Prop :=
  stop w = true ∧ ∀ k < w.length, stop (w.take k) = false

/-- Having the first stop exactly at time `T` is determined by the first `T` letters. -/
theorem measurableSet_stoppingPrefix (stop : Word α → Bool) (T : ℕ) :
    MeasurableSet[prefixSigma T] {ω | IsStoppingPrefix stop («prefix» T ω)} :=
  measurableSet_prefixSigma T (IsStoppingPrefix stop)

/-- Inspect prefixes until the first stop, then apply `F` to the complete history
and unused suffix. A word without a stop does not satisfy the event. -/
def firstPrefixEvent (stop : Word α → Bool) (F : Word α → Word α → Prop)
    (history : Word α) : Word α → Prop
  | [] => if stop history then F history [] else False
  | e :: es => if stop history then F history (e :: es)
      else firstPrefixEvent stop F (history ++ [e]) es

private theorem firstPrefixEvent_at_stop (stop : Word α → Bool)
    (F : Word α → Word α → Prop)
    (history : Word α) (hs : stop history = true) (u : Word α) :
    firstPrefixEvent stop F history u = F history u := by
  cases u <;> simp [firstPrefixEvent, hs]

open Classical in
/-- Summing a stopping tree preserves a uniform fraction bound on every terminal
continuation. This is the finite-word first-prefix strong Markov estimate. -/
theorem first_prefix_count_transfer [Fintype α] (stop : Word α → Bool)
    (F : Word α → Word α → Prop) (p q : ℕ)
    (hbound : ∀ h, stop h = true → ∀ t,
      p * wordSum α t (fun u => if F h u then 1 else 0) ≤ q * Fintype.card α ^ t)
    (history : Word α) (t : ℕ) :
    p * wordSum α t (fun u => if firstPrefixEvent stop F history u then 1 else 0) ≤
      q * Fintype.card α ^ t := by
  classical
  induction t generalizing history with
  | zero =>
      by_cases hs : stop history = true
      · simpa only [firstPrefixEvent_at_stop stop F history hs] using hbound history hs 0
      · simp [wordSum_eq_sum_tuples, firstPrefixEvent, hs]
  | succ t ih =>
      by_cases hs : stop history = true
      · simpa only [firstPrefixEvent_at_stop stop F history hs] using
          hbound history hs (t + 1)
      · simp only [wordSum_succ, firstPrefixEvent, hs, Finset.mul_sum]
        calc
          (∑ e : α, p * wordSum α t
              (fun u => if firstPrefixEvent stop F (history ++ [e]) u then 1 else 0)) ≤
              ∑ _e : α, q * Fintype.card α ^ t :=
            Finset.sum_le_sum fun e _ => ih (history ++ [e])
          _ = q * Fintype.card α ^ (t + 1) := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, pow_succ]
            ring

open Classical in
/-- The probability of an arbitrary word predicate is its normalized indicator sum. -/
theorem measure_prefix_event [Fintype α] [Nonempty α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (T : ℕ) (E : Word α → Prop) :
    μ α {ω | E («prefix» T ω)} =
      (wordSum α T (fun w => if E w then 1 else 0) : ℝ≥0∞) /
        (Fintype.card α : ℝ≥0∞) ^ T := by
  classical
  have hmeas : MeasurableSet {ω | E («prefix» T ω)} :=
    prefixSigma_le T _ (measurableSet_prefixSigma T E)
  calc
    _ = ∫⁻ ω, (if E («prefix» T ω) then 1 else 0 : ℝ≥0∞) ∂μ α := by
      simpa [Set.indicator_apply] using (lintegral_indicator_one hmeas).symm
    _ = _ := by
      simpa using lintegral_word_function T (fun w => if E w then 1 else 0)

open Classical in
/-- The measure form of the counting first-prefix transfer. No positivity of `p`
or `q` is needed; the alphabet is nonempty. -/
theorem first_prefix_fraction_transfer [Fintype α] [Nonempty α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (stop : Word α → Bool) (F : Word α → Word α → Prop)
    (p q : ℕ)
    (hbound : ∀ h, stop h = true → ∀ t,
      p * wordSum α t (fun u => if F h u then 1 else 0) ≤ q * Fintype.card α ^ t)
    (history : Word α) (T : ℕ) :
    (p : ℝ≥0∞) * μ α {ω | firstPrefixEvent stop F history («prefix» T ω)} ≤ q := by
  classical
  rw [measure_prefix_event, ← mul_div_assoc,
    ENNReal.div_le_iff (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (by simp)]
  exact_mod_cast first_prefix_count_transfer stop F p q hbound history T

/-- A uniform continuation probability bound at every stopping history transfers
to the first-prefix event at every finite horizon. -/
theorem first_prefix_measure_transfer [Fintype α] [Nonempty α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (stop : Word α → Bool) (F : Word α → Word α → Prop)
    (p q : ℕ)
    (hbound : ∀ h, stop h = true → ∀ t,
      (p : ℝ≥0∞) * μ α {ω | F h («prefix» t ω)} ≤ q)
    (history : Word α) (T : ℕ) :
    (p : ℝ≥0∞) * μ α {ω | firstPrefixEvent stop F history («prefix» T ω)} ≤ q := by
  classical
  apply first_prefix_fraction_transfer stop F p q ?_ history T
  intro h hs t
  have hprob := hbound h hs t
  rw [measure_prefix_event, ← mul_div_assoc,
    ENNReal.div_le_iff (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (by simp)] at hprob
  exact_mod_cast hprob

end

end Ripple.CountingBridge
