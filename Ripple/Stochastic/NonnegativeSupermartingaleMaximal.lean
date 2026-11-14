import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Tactic

/-!
# A sharp finite-horizon maximal bound for nonnegative supermartingales

The first crossing is capped at the terminal index. Optional stopping is applied
 to the negative process. Nonnegativity permits discarding the complement of the
crossing event. The bound uses the initial expectation and has constant one.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Ripple.Stochastic.SupermartingaleMaximal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P] {F : Filtration ℕ mΩ} {Z : ℕ → Ω → ℝ}

/-- Bounded optional sampling in the direction needed for a supermartingale. -/
theorem integral_stoppedValue_le_initial (hZ : Supermartingale Z F P)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime F τ) {n : ℕ}
    (hbound : ∀ ω, τ ω ≤ n) :
    (∫ ω, stoppedValue Z τ ω ∂P) ≤ ∫ ω, Z 0 ω ∂P := by
  have h := hZ.neg.expected_stoppedValue_mono
    (isStoppingTime_const F 0) hτ (fun _ => bot_le) hbound
  simpa only [stoppedValue_const, stoppedValue, Pi.neg_apply,
    integral_neg, neg_le_neg_iff] using h

/-- The sharp finite-grid Ville bound, in real-valued measure form. -/
theorem finite_maximal_le (hZ : Supermartingale Z F P)
    (hnonneg : ∀ n ω, 0 ≤ Z n ω) (a : ℝ) (n : ℕ) :
    a * P.real {ω | ∃ k ≤ n, a ≤ Z k ω} ≤ ∫ ω, Z 0 ω ∂P := by
  classical
  let E : Set Ω := {ω | ∃ k ≤ n, a ≤ Z k ω}
  let τ : Ω → ℕ∞ := fun ω => (hittingBtwn Z (Ici a) 0 n ω : ℕ)
  have hτ : IsStoppingTime F τ :=
    hZ.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hb : ∀ ω, τ ω ≤ n := fun ω => by
    dsimp [τ]
    exact_mod_cast (hittingBtwn_le (u := Z) (s := Ici a) (n := 0) (m := n) ω)
  have hI : Integrable (stoppedValue Z τ) P :=
    integrable_stoppedValue ℕ hτ hZ.integrable hb
  have hE : MeasurableSet E := by
    change MeasurableSet {ω | ∃ k, k ≤ n ∧ a ≤ Z k ω}
    simp only [setOf_exists]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k ≤ n
    · simpa only [hk, true_and] using
        (measurableSet_le measurable_const ((hZ.stronglyMeasurable k).measurable.mono
          (F.le k) le_rfl))
    · simp only [hk, false_and, setOf_false, MeasurableSet.empty]
  have hhit : ∀ ω ∈ E, a ≤ stoppedValue Z τ ω := by
    rintro ω ⟨k, hk, ha⟩
    exact stoppedValue_hittingBtwn_mem ⟨k, ⟨Nat.zero_le k, hk⟩, ha⟩
  have hpoint : ∀ ω, E.indicator (fun _ => a) ω ≤ stoppedValue Z τ ω := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa only [indicator_of_mem hω] using hhit ω hω
    · simpa only [indicator_of_notMem hω] using hnonneg (τ ω).untopA ω
  have hle := integral_mono ((integrable_const a).indicator hE) hI hpoint
  have hleft : (∫ ω, E.indicator (fun _ => a) ω ∂P) = a * P.real E := by
    rw [integral_indicator hE, integral_const]
    simp [Measure.real_def, smul_eq_mul, mul_comm]
  rw [hleft] at hle
  exact hle.trans (integral_stoppedValue_le_initial hZ hτ hb)

/-- Extended-valued measure form, retaining the sharp constant. -/
theorem finite_maximal_measure_le (hZ : Supermartingale Z F P)
    (hnonneg : ∀ n ω, 0 ≤ Z n ω) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    P {ω | ∃ k ≤ n, a ≤ Z k ω} ≤
      ENNReal.ofReal ((∫ ω, Z 0 ω ∂P) / a) := by
  have h := finite_maximal_le hZ hnonneg a n
  have hdiv : P.real {ω | ∃ k ≤ n, a ≤ Z k ω} ≤
      (∫ ω, Z 0 ω ∂P) / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using h
  calc
    P {ω | ∃ k ≤ n, a ≤ Z k ω} =
        ENNReal.ofReal (P.real {ω | ∃ k ≤ n, a ≤ Z k ω}) := by
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hdiv

/-- Exhaustion of finite horizons gives the sharp discrete-time Ville inequality. -/
theorem countable_maximal_measure_le (hZ : Supermartingale Z F P)
    (hnonneg : ∀ n ω, 0 ≤ Z n ω) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ k, a ≤ Z k ω} ≤
      ENNReal.ofReal ((∫ ω, Z 0 ω ∂P) / a) := by
  let E : ℕ → Set Ω := fun n => {ω | ∃ k ≤ n, a ≤ Z k ω}
  have hm : Monotone E := by
    rintro n m hnm ω ⟨k, hk, haω⟩
    exact ⟨k, hk.trans hnm, haω⟩
  have hset : {ω | ∃ k, a ≤ Z k ω} = ⋃ n, E n := by
    ext ω
    constructor
    · rintro ⟨k, hk⟩
      exact mem_iUnion.mpr ⟨k, k, le_rfl, hk⟩
    · intro hω
      obtain ⟨n, k, _, hk⟩ := mem_iUnion.mp hω
      exact ⟨k, hk⟩
  rw [hset, hm.measure_iUnion]
  exact iSup_le fun n => finite_maximal_measure_le hZ hnonneg ha n

end Ripple.Stochastic.SupermartingaleMaximal
