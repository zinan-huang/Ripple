-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockPotentialTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPrefixTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinning

/-!
# Prefix-weighted contraction and the P3a numerical horizon

A bounded adapted nonnegative process with one-step multiplicative drift
has the same drift after intersection with any event observed at its start.
The tail theorem allows an arbitrary failure event dominated by the current
potential; it does not assume that failure is measurable at the start.

The final elementary calibration is exactly the 30 m log m / m^9 one.
Application to the virtual front supplies the concrete process, drift,
and failure domination separately.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPotentialTail

open PhaseThreeClockThinning

section Filtered

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

/-- A process bounded between zero and one is integrable at every time. -/
theorem bounded_potential_integrable
    {Z : ℕ → Ω → ℝ}
    (hZ : ∀ t, StronglyMeasurable[ℱ t] (Z t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω ∧ Z t ω ≤ 1)
    (t : ℕ) : Integrable (Z t) μ := by
  refine Integrable.of_bound ((hZ t).mono (ℱ.le t)).aestronglyMeasurable 1 ?_
  filter_upwards [hbound t] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2


/-- A concrete affine decrease against a selected Bernoulli event produces
the conditional multiplicative drift. The decrement D is observed at the
current time, and all products are integrable by the stated bounds. -/
theorem affine_conditional_drift
    {Z D I : ℕ → Ω → ℝ} {a : ℝ}
    (hZ : ∀ t, StronglyMeasurable[ℱ t] (Z t))
    (hZbound : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω ∧ Z t ω ≤ 1)
    (hD : ∀ t, StronglyMeasurable[ℱ t] (D t))
    (hDbound : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ D t ω ∧ D t ω ≤ 1)
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hstep : ∀ t, Z (t + 1) ≤ᵐ[μ]
      fun ω => Z t ω - D t ω * I t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂μ,
      a * Z t ω ≤ D t ω * (μ[I t | ℱ t]) ω) :
    ∀ t, μ[Z (t + 1) | ℱ t] ≤ᵐ[μ]
      fun ω => (1 - a) * Z t ω := by
  intro t
  have hZi := bounded_potential_integrable hZ hZbound t
  have hZn := bounded_potential_integrable hZ hZbound (t + 1)
  have hIi := PhaseThreeScalar.bernoulli_integrable hI hzeroOne t
  have hprod : Integrable (fun ω => D t ω * I t ω) μ := by
    refine Integrable.of_bound
      (((hD t).mono (ℱ.le t)).mul
        ((hI t).mono (ℱ.le (t + 1)))).aestronglyMeasurable 1 ?_
    filter_upwards [hDbound t, hzeroOne t] with ω hd hi
    rcases hi with hi | hi
    · simp [hi]
    · simpa only [hi, mul_one, Real.norm_eq_abs, abs_of_nonneg hd.1] using hd.2
  have hcur : μ[Z t | ℱ t] = Z t :=
    condExp_of_stronglyMeasurable (ℱ.le t) (hZ t) hZi
  have hmono := condExp_mono (m := ℱ t) hZn (hZi.sub hprod) (hstep t)
  have hsub := condExp_sub hZi hprod (ℱ t)
  have hpull := condExp_mul_of_stronglyMeasurable_left (hD t) hprod hIi
  filter_upwards [hmono, hsub, hpull, hrate t] with ω hm hs hp hr
  have hprodce :
      μ[fun ω => D t ω * I t ω | ℱ t] ω =
        D t ω * (μ[I t | ℱ t]) ω := by
    simpa only [Pi.mul_apply] using hp
  have hsubce :
      μ[fun ω => Z t ω - D t ω * I t ω | ℱ t] ω =
        Z t ω - μ[fun ω => D t ω * I t ω | ℱ t] ω := by
    simpa only [Pi.sub_apply, hcur] using hs
  rw [hprodce] at hsubce
  have hm' :
      μ[Z (t + 1) | ℱ t] ω ≤
        μ[fun ω => Z t ω - D t ω * I t ω | ℱ t] ω := hm
  rw [hsubce] at hm'
  change μ[Z (t + 1) | ℱ t] ω ≤ (1 - a) * Z t ω
  nlinarith

/-- Multiplicative contraction with the original prefix mass retained. -/
theorem prefix_potential_moment
    {Z : ℕ → Ω → ℝ} {q : ℝ}
    (hZ : ∀ t, StronglyMeasurable[ℱ t] (Z t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω ∧ Z t ω ≤ 1)
    (hq : 0 ≤ q)
    (hdrift : ∀ t, μ[Z (t + 1) | ℱ t] ≤ᵐ[μ] fun ω => q * Z t ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ) :
    (∫ ω, E.indicator (Z N) ω ∂μ) ≤ q ^ N * μ.real E := by
  classical
  have hEm : MeasurableSet E := (ℱ.le 0) _ hE
  have hint (t : ℕ) : Integrable (E.indicator (Z t)) μ :=
    (bounded_potential_integrable hZ hbound t).indicator hEm
  induction N with
  | zero =>
      have hupper : E.indicator (Z 0) ≤ᵐ[μ]
          E.indicator (fun _ : Ω => (1 : ℝ)) := by
        filter_upwards [hbound 0] with ω hω
        by_cases he : ω ∈ E
        · simpa only [Set.indicator_of_mem he] using hω.2
        · simp [he]
      have hle := integral_mono_ae (hint 0)
        ((integrable_const (1 : ℝ)).indicator hEm) hupper
      have h1 : ∫ ω, E.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ = μ.real E := by
        rw [integral_indicator_const _ hEm]
        simp
      rw [pow_zero, one_mul]
      exact hle.trans h1.le
  | succ N ih =>
      have hEN : MeasurableSet[ℱ N] E :=
        (ℱ.mono (Nat.zero_le N)) _ hE
      have hce :
          μ[E.indicator (Z (N + 1)) | ℱ N] =ᵐ[μ]
            E.indicator (μ[Z (N + 1) | ℱ N]) :=
        condExp_indicator (bounded_potential_integrable hZ hbound (N + 1)) hEN
      have hdom :
          μ[E.indicator (Z (N + 1)) | ℱ N] ≤ᵐ[μ]
            fun ω => q * E.indicator (Z N) ω := by
        filter_upwards [hce, hdrift N] with ω he hd
        change μ[E.indicator (Z (N + 1)) | ℱ N] ω ≤ q * E.indicator (Z N) ω
        rw [he]
        by_cases hω : ω ∈ E
        · simpa only [Set.indicator_of_mem hω] using hd
        · simp [hω]
      calc
        (∫ ω, E.indicator (Z (N + 1)) ω ∂μ) =
            ∫ ω, μ[E.indicator (Z (N + 1)) | ℱ N] ω ∂μ :=
          (integral_condExp (ℱ.le N)).symm
        _ ≤ ∫ ω, q * E.indicator (Z N) ω ∂μ :=
          integral_mono_ae integrable_condExp ((hint N).const_mul q) hdom
        _ = q * ∫ ω, E.indicator (Z N) ω ∂μ :=
          integral_const_mul _ _
        _ ≤ q * (q ^ N * μ.real E) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (N + 1) * μ.real E := by
          rw [pow_succ]
          ring

/-- A current-potential domination turns contraction into a prefix-weighted
tail. The event B need not be measurable for this finite-measure statement. -/
theorem prefix_potential_tail
    {Z : ℕ → Ω → ℝ} {q : ℝ}
    (hZ : ∀ t, StronglyMeasurable[ℱ t] (Z t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω ∧ Z t ω ≤ 1)
    (hq : 0 ≤ q)
    (hdrift : ∀ t, μ[Z (t + 1) | ℱ t] ≤ᵐ[μ] fun ω => q * Z t ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ)
    (B : Set Ω) (R : ℝ) (hR : 0 ≤ R)
    (hB : ∀ ω ∈ B, 1 ≤ R * Z N ω) :
    μ.real (E ∩ B) ≤ R * q ^ N * μ.real E := by
  classical
  let Y : Ω → ℝ := fun ω => R * E.indicator (Z N) ω
  have hEm : MeasurableSet E := (ℱ.le 0) _ hE
  have hYint : Integrable Y μ :=
    ((bounded_potential_integrable hZ hbound N).indicator hEm).const_mul R
  have hYnonneg : ∀ᵐ ω ∂μ, 0 ≤ Y ω := by
    filter_upwards [hbound N] with ω hω
    by_cases he : ω ∈ E
    · simpa only [Y, Set.indicator_of_mem he] using mul_nonneg hR hω.1
    · simp [Y, he]
  have hsub : E ∩ B ⊆ {ω | (1 : ℝ) ≤ Y ω} := by
    rintro ω ⟨he, hb⟩
    show (1 : ℝ) ≤ R * E.indicator (Z N) ω
    rw [Set.indicator_of_mem he]
    exact hB ω hb
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hYnonneg hYint (1 : ℝ)
  calc
    μ.real (E ∩ B) ≤ μ.real {ω | (1 : ℝ) ≤ Y ω} :=
      measureReal_mono hsub
    _ ≤ ∫ ω, Y ω ∂μ := by simpa only [one_mul] using hmarkov
    _ = R * ∫ ω, E.indicator (Z N) ω ∂μ := integral_const_mul _ _
    _ ≤ R * (q ^ N * μ.real E) :=
      mul_le_mul_of_nonneg_left
        (prefix_potential_moment hZ hbound hq hdrift E hE N) hR
    _ = R * q ^ N * μ.real E := by ring

theorem prefix_potential_tail_ennreal
    {Z : ℕ → Ω → ℝ} {q : ℝ}
    (hZ : ∀ t, StronglyMeasurable[ℱ t] (Z t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω ∧ Z t ω ≤ 1)
    (hq : 0 ≤ q)
    (hdrift : ∀ t, μ[Z (t + 1) | ℱ t] ≤ᵐ[μ] fun ω => q * Z t ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ)
    (B : Set Ω) (R : ℝ) (hR : 0 ≤ R)
    (hB : ∀ ω ∈ B, 1 ≤ R * Z N ω) :
    μ (E ∩ B) ≤ ENNReal.ofReal (R * q ^ N) * μ E :=
  measure_le_of_real_weighted_bound μ (E ∩ B) E (R * q ^ N)
    (mul_nonneg hR (pow_nonneg hq N))
    (prefix_potential_tail hZ hbound hq hdrift E hE N B R hR hB)

end Filtered

/-! ## Exact elementary P3a calibration -/

theorem clock_contraction_nonneg (m : ℕ) (hm : 1 ≤ m) :
    (0 : ℝ) ≤ 1 - 1 / (3 * (m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < 3 * (m : ℝ) := by positivity
  have hfrac : (1 : ℝ) / (3 * (m : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hden).2
    linarith
  linarith

theorem clock_contraction_pow_le_exp (m N : ℕ) (hm : 1 ≤ m) :
    (1 - 1 / (3 * (m : ℝ))) ^ N ≤
      Real.exp (-(N : ℝ) / (3 * (m : ℝ))) := by
  have hbase : 1 - 1 / (3 * (m : ℝ)) ≤
      Real.exp (-(1 / (3 * (m : ℝ)))) := by
    simpa only [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-(1 / (3 * (m : ℝ))))
  calc
    (1 - 1 / (3 * (m : ℝ))) ^ N ≤
        (Real.exp (-(1 / (3 * (m : ℝ))))) ^ N :=
      pow_le_pow_left₀ (clock_contraction_nonneg m hm) hbase N
    _ = Real.exp (-(N : ℝ) / (3 * (m : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The coefficient may be any nonnegative R at most m. -/
theorem potential_tail_calibration (m N : ℕ) (hm : 1 ≤ m)
    (R : ℝ) (hR : 0 ≤ R) (hRm : R ≤ (m : ℝ))
    (hN : 30 * (m : ℝ) * Real.log (m : ℝ) ≤ (N : ℝ)) :
    R * (1 - 1 / (3 * (m : ℝ))) ^ N ≤ 1 / (m : ℝ) ^ 9 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hden : (0 : ℝ) < 3 * (m : ℝ) := by positivity
  have hratio : 10 * Real.log (m : ℝ) ≤ (N : ℝ) / (3 * (m : ℝ)) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hexp : Real.exp (10 * Real.log (m : ℝ)) = (m : ℝ) ^ 10 := by
    change Real.exp ((10 : ℕ) * Real.log (m : ℝ)) = _
    rw [Real.exp_nat_mul, Real.exp_log hmpos]
  have hlast :
      (m : ℝ) * Real.exp (-(10 * Real.log (m : ℝ))) = 1 / (m : ℝ) ^ 9 := by
    rw [Real.exp_neg, hexp]
    field_simp [ne_of_gt hmpos] <;> ring
  calc
    R * (1 - 1 / (3 * (m : ℝ))) ^ N ≤
        R * Real.exp (-(N : ℝ) / (3 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (clock_contraction_pow_le_exp m N hm) hR
    _ ≤ (m : ℝ) * Real.exp (-(N : ℝ) / (3 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_right hRm (Real.exp_nonneg _)
    _ ≤ (m : ℝ) * Real.exp (-(10 * Real.log (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [neg_div]; linarith)) hmpos.le
    _ = 1 / (m : ℝ) ^ 9 := hlast

theorem potential_tail_calibration_ceiling (m : ℕ) (hm : 1 ≤ m)
    (R : ℝ) (hR : 0 ≤ R) (hRm : R ≤ (m : ℝ)) :
    R * (1 - 1 / (3 * (m : ℝ))) ^
        Nat.ceil (30 * (m : ℝ) * Real.log (m : ℝ)) ≤ 1 / (m : ℝ) ^ 9 :=
  potential_tail_calibration m _ hm R hR hRm (Nat.le_ceil _)

/-- The target ceil(C/10) supplies a coefficient no greater than m. -/
theorem five_ceiling_tenth_le_population (m C : ℕ) (hm : 10 ≤ m) (hC : C ≤ m) :
    5 * Nat.ceil ((C : ℝ) / 10) ≤ m := by
  have hmR : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCR : (C : ℝ) ≤ (m : ℝ) := by exact_mod_cast hC
  have hc := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (C : ℝ) / 10)
  have hreal : (5 : ℝ) * (Nat.ceil ((C : ℝ) / 10) : ℝ) ≤ (m : ℝ) := by
    linarith
  exact_mod_cast hreal

section Calibrated

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

/-- Direct prefix-weighted P3a-sized tail from the concrete contraction premises. -/
theorem prefix_potential_calibrated_tail
    {Z : ℕ → Ω → ℝ} (m N : ℕ) (hm : 1 ≤ m)
    (hZ : ∀ t, StronglyMeasurable[ℱ t] (Z t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ Z t ω ∧ Z t ω ≤ 1)
    (hdrift : ∀ t, μ[Z (t + 1) | ℱ t] ≤ᵐ[μ]
      fun ω => (1 - 1 / (3 * (m : ℝ))) * Z t ω)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (B : Set Ω) (R : ℝ) (hR : 0 ≤ R) (hRm : R ≤ (m : ℝ))
    (hB : ∀ ω ∈ B, 1 ≤ R * Z N ω)
    (hN : 30 * (m : ℝ) * Real.log (m : ℝ) ≤ (N : ℝ)) :
    μ (E ∩ B) ≤ ENNReal.ofReal (1 / (m : ℝ) ^ 9) * μ E := by
  apply (prefix_potential_tail_ennreal hZ hbound (clock_contraction_nonneg m hm)
    hdrift E hE N B R hR hB).trans
  exact mul_le_mul_right'
    (ENNReal.ofReal_le_ofReal (potential_tail_calibration m N hm R hR hRm hN)) _

end Calibrated

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPotentialTail

end
