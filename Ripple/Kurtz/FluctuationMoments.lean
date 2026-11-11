import Ripple.Kurtz.FluctuationCompensator
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Jump-count moments and integrability of the fluctuation functionals

This file supplies the moment, tail, and integrability clauses of
docs/audit/FIX-KURTZ2-FINAL.md, Section 4.2, Lemma L6, using the indicator
tilt from Section 2, Lemma 2.4.

The canonical record space and measure, and the total jump and compensated
functionals, are the existing definitions. In the basic count theorems,
Λ is a bound on the total exit rate (the document's Λ_n).
The final uniform corollary displays the density-dependent N * Λ bound.
-/

namespace Ripple.Kurtz

open MeasureTheory Filter Topology Set Finset
open Ripple.CTMC
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The number of genuine jumps among the first r records by time T. -/
def fluctuationJumpCountPartial (M : DensityDepCTMC d) (T : ℝ) (r : ℕ)
    (ω : M.canonicalRecordΩ) : ℕ :=
  ∑ k ∈ Finset.range r,
    if QMatrix.recTime ω (k + 1) ≤ T ∧ (ω (k + 1)).2 ≠ (ω k).2 then 1 else 0

private theorem fm_recTime_measurable (M : DensityDepCTMC d) (k : ℕ) :
    Measurable (fun ω : M.canonicalRecordΩ => QMatrix.recTime ω k) := by
  unfold QMatrix.recTime
  exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply (j + 1)).fst

theorem measurable_fluctuationJumpCountPartial (M : DensityDepCTMC d)
    (T : ℝ) (r : ℕ) :
    Measurable (fluctuationJumpCountPartial M T r) := by
  classical
  unfold fluctuationJumpCountPartial
  refine Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.ite
    ((measurableSet_le (fm_recTime_measurable M (k + 1)) measurable_const).inter
      (measurableSet_eq_fun (measurable_pi_apply (k + 1)).snd
        (measurable_pi_apply k).snd).compl)
    measurable_const measurable_const

theorem fluctuationJumpCountPartial_le (M : DensityDepCTMC d)
    (T : ℝ) (r : ℕ) (ω : M.canonicalRecordΩ) :
    fluctuationJumpCountPartial M T r ω ≤ r := by
  calc
    _ ≤ ∑ _k ∈ Finset.range r, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs <;> omega
    _ = r := by simp

private theorem fm_countReal_measurable (M : DensityDepCTMC d) (T : ℝ) (r : ℕ) :
    Measurable (fun ω => (fluctuationJumpCountPartial M T r ω : ℝ)) :=
  (Measurable.of_discrete : Measurable (fun k : ℕ => (k : ℝ))).comp
    (measurable_fluctuationJumpCountPartial M T r)

/-- Finite record counts have an integrable exponential, without a rate hypothesis. -/
theorem integrable_fluctuationExpJumpCountPartial (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) (T : ℝ) (r : ℕ) :
    Integrable (fun ω => Real.exp (fluctuationJumpCountPartial M T r ω : ℝ))
      (M.canonicalRecordMeasure z) := by
  refine (integrable_const (Real.exp (r : ℝ))).mono'
    (Real.measurable_exp.comp (fm_countReal_measurable M T r)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact_mod_cast fluctuationJumpCountPartial_le M T r ω

private def fm_countTilt {S : Type*} [DecidableEq S] : ℝ → S → S → ℂ :=
  fun _ x y => if y ≠ x then 1 else 0

private theorem fm_countTilt_isExpTilt {S : Type*} [Fintype S] [DecidableEq S] :
    IsExpTilt (fm_countTilt (S := S)) ∅ where
  diag := fun _ _ => by simp [fm_countTilt]
  meas := fun _ _ => measurable_const
  bdd := ⟨1, fun _ x y => by
    by_cases h : y ≠ x <;> simp [fm_countTilt, h]⟩
  countable := Set.countable_empty
  cont := fun _ _ _ _ => continuousAt_const

private theorem fm_countTilt_compensator {S : Type*} [Fintype S] [DecidableEq S]
    (Q : QMatrix S) (s : ℝ) (x : S) :
    Q.expCompRate fm_countTilt s x = (((Real.exp 1 - 1) * Q.exitRate x : ℝ) : ℂ) := by
  classical
  calc
    _ = ∑ y ∈ Finset.univ.filter (· ≠ x),
        (Q.rate x y : ℂ) * (Complex.exp 1 - 1) := by
      unfold QMatrix.expCompRate
      refine Finset.sum_congr rfl fun y hy => ?_
      simp only [fm_countTilt, if_pos (Finset.mem_filter.mp hy).2]
    _ = _ := by
      simp only [QMatrix.exitRate, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_sum, Complex.ofReal_one, Complex.ofReal_exp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      ring

private def fm_countCompensator (M : DensityDepCTMC d) (T : ℝ) (r : ℕ)
    (ω : M.canonicalRecordΩ) : ℝ :=
  ∑ k ∈ Finset.range r,
    (min (QMatrix.recTime ω (k + 1)) T - min (QMatrix.recTime ω k) T) *
      ((Real.exp 1 - 1) * M.exitRateAt (ω k).2)

private theorem fm_countCompensator_measurable (M : DensityDepCTMC d) (T : ℝ) (r : ℕ) :
    Measurable (fm_countCompensator M T r) := by
  unfold fm_countCompensator
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (((fm_recTime_measurable M (k + 1)).min measurable_const).sub
      ((fm_recTime_measurable M k).min measurable_const)).mul
    (measurable_const.mul
      ((Measurable.of_discrete : Measurable M.exitRateAt).comp
        (measurable_pi_apply k).snd))

private theorem fm_count_expSum_eq (M : DensityDepCTMC d) (T : ℝ) (r : ℕ)
    (ω : M.canonicalRecordΩ) (hnn : ∀ k, 0 ≤ (ω (k + 1)).1) :
    M.toQMatrix.expSum fm_countTilt T r ω =
      ((((fluctuationJumpCountPartial M T r ω : ℝ) -
        fm_countCompensator M T r ω) : ℝ) : ℂ) := by
  classical
  have ht (k : ℕ) : 0 ≤ QMatrix.recTime ω k := by
    exact Finset.sum_nonneg fun j _ => hnn j
  have hs (k : ℕ) :
      QMatrix.recTime ω (k + 1) = QMatrix.recTime ω k + (ω (k + 1)).1 := by
    simp only [QMatrix.recTime, Finset.sum_range_succ]
  have hc :
      (fluctuationJumpCountPartial M T r ω : ℝ) =
        ∑ k ∈ Finset.range r,
          if QMatrix.recTime ω (k + 1) ≤ T ∧ (ω (k + 1)).2 ≠ (ω k).2
          then (1 : ℝ) else 0 := by
    unfold fluctuationJumpCountPartial
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero]
  rw [hc, fm_countCompensator, ← Finset.sum_sub_distrib, Complex.ofReal_sum]
  unfold QMatrix.expSum
  refine Finset.sum_congr rfl fun k hk => ?_
  unfold QMatrix.expStepExponent
  simp only [fm_countTilt_compensator, intervalIntegral.integral_const,
    Complex.real_smul, max_eq_left (ht k), max_eq_left (hnn k), ← hs k]
  by_cases htime : QMatrix.recTime ω (k + 1) ≤ T
  · by_cases hstate : (ω (k + 1)).2 ≠ (ω k).2
    · simp [fm_countTilt, htime, hstate, DensityDepCTMC.exitRateAt]
    · simp [fm_countTilt, htime, hstate, DensityDepCTMC.exitRateAt]
  · simp [fm_countTilt, htime, DensityDepCTMC.exitRateAt]

private theorem fm_countCompensator_bounds (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) (r : ℕ) (ω : M.canonicalRecordΩ)
    (hnn : ∀ k, 0 ≤ (ω (k + 1)).1) :
    0 ≤ fm_countCompensator M T r ω ∧
      fm_countCompensator M T r ω ≤ (Real.exp 1 - 1) * Λ * T := by
  have he : 0 ≤ Real.exp 1 - 1 := by
    have h := Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    simpa only [Real.exp_zero] using sub_nonneg.mpr h
  have hΛ0 : 0 ≤ Λ := (M.exitRateAt_nonneg z).trans (hΛ z)
  have hs (k : ℕ) :
      QMatrix.recTime ω (k + 1) = QMatrix.recTime ω k + (ω (k + 1)).1 := by
    simp only [QMatrix.recTime, Finset.sum_range_succ]
  have hd (k : ℕ) :
      0 ≤ min (QMatrix.recTime ω (k + 1)) T - min (QMatrix.recTime ω k) T := by
    apply sub_nonneg.mpr
    exact min_le_min (by rw [hs k]; linarith [hnn k]) le_rfl
  constructor
  · exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hd k) (mul_nonneg he (M.exitRateAt_nonneg _))
  · have hsum : fm_countCompensator M T r ω ≤
        ((Real.exp 1 - 1) * Λ) * min (QMatrix.recTime ω r) T := by
      induction r with
      | zero => simp [fm_countCompensator, QMatrix.recTime, min_eq_left hT]
      | succ r ih =>
          have hterm := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hΛ (ω r).2) he) (hd r)
          calc
            fm_countCompensator M T (r + 1) ω =
                fm_countCompensator M T r ω +
                  (min (QMatrix.recTime ω (r + 1)) T - min (QMatrix.recTime ω r) T) *
                    ((Real.exp 1 - 1) * M.exitRateAt (ω r).2) := by
              simp only [fm_countCompensator, Finset.sum_range_succ]
            _ ≤ ((Real.exp 1 - 1) * Λ) * min (QMatrix.recTime ω r) T +
                  (min (QMatrix.recTime ω (r + 1)) T - min (QMatrix.recTime ω r) T) *
                    ((Real.exp 1 - 1) * Λ) := add_le_add ih hterm
            _ = ((Real.exp 1 - 1) * Λ) * min (QMatrix.recTime ω (r + 1)) T := by ring
    exact hsum.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg he hΛ0))

/-- L6 and Lemma 2.4: the finite-count exponential moment under the canonical record law. -/
theorem fluctuation_integral_exp_jumpCountPartial (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) (r : ℕ) :
    ∫ ω, Real.exp (fluctuationJumpCountPartial M T r ω : ℝ)
      ∂M.canonicalRecordMeasure z ≤ Real.exp ((Real.exp 1 - 1) * Λ * T) := by
  let Z : M.canonicalRecordΩ → ℝ := fun ω =>
    Real.exp ((fluctuationJumpCountPartial M T r ω : ℝ) - fm_countCompensator M T r ω)
  have hnn : ∀ᵐ ω ∂M.canonicalRecordMeasure z, ∀ k, 0 ≤ (ω (k + 1)).1 :=
    M.toQMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae z
  have hZm : Measurable Z :=
    Real.measurable_exp.comp ((fm_countReal_measurable M T r).sub
      (fm_countCompensator_measurable M T r))
  have hZi : Integrable Z (M.canonicalRecordMeasure z) := by
    refine (integrable_const (Real.exp (r : ℝ))).mono' hZm.aestronglyMeasurable ?_
    filter_upwards [hnn] with ω hω
    change ‖Real.exp ((fluctuationJumpCountPartial M T r ω : ℝ) -
      fm_countCompensator M T r ω)‖ ≤ Real.exp (r : ℝ)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hc : (fluctuationJumpCountPartial M T r ω : ℝ) ≤ r := by
      exact_mod_cast fluctuationJumpCountPartial_le M T r ω
    have hcomp := (fm_countCompensator_bounds M z hT hΛ r ω hω).1
    linarith
  have hZ : ∫ ω, Z ω ∂M.canonicalRecordMeasure z = 1 := by
    have h := M.toQMatrix.integral_cexp_expSum fm_countTilt_isExpTilt T z r
    change (∫ ω, Complex.exp (M.toQMatrix.expSum fm_countTilt T r ω)
      ∂M.canonicalRecordMeasure z) = 1 at h
    have heq :
        (fun ω => Complex.exp (M.toQMatrix.expSum fm_countTilt T r ω)) =ᵐ[
          M.canonicalRecordMeasure z] (fun ω => (Z ω : ℂ)) := by
      filter_upwards [hnn] with ω hω
      rw [fm_count_expSum_eq M T r ω hω, ← Complex.ofReal_exp]
    rw [integral_congr_ae heq, integral_complex_ofReal] at h
    exact_mod_cast h
  calc
    _ ≤ ∫ ω, Real.exp ((Real.exp 1 - 1) * Λ * T) * Z ω
        ∂M.canonicalRecordMeasure z := by
      apply integral_mono_ae (integrable_fluctuationExpJumpCountPartial M z T r)
        (hZi.const_mul _)
      filter_upwards [hnn] with ω hω
      dsimp [Z]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcomp := (fm_countCompensator_bounds M z hT hΛ r ω hω).2
      linarith
    _ = _ := by rw [integral_const_mul, hZ, mul_one]

/-- The nonnegative-integral form of the finite-count exponential-moment bound. -/
theorem fluctuation_lintegral_exp_jumpCountPartial (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) (r : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (fluctuationJumpCountPartial M T r ω : ℝ))
      ∂M.canonicalRecordMeasure z ≤ ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * Λ * T)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_fluctuationExpJumpCountPartial M z T r)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (fluctuation_integral_exp_jumpCountPartial M z hT hΛ r)

/-! ## L6: the extended count, its exponential moment, and its tail -/

/-- The genuine jump count, retaining the value infinity on explosive records. -/
def fluctuationJumpCount (M : DensityDepCTMC d) (T : ℝ)
    (ω : M.canonicalRecordΩ) : ℝ≥0∞ :=
  ⨆ r, (fluctuationJumpCountPartial M T r ω : ℝ≥0∞)

/-- The extended exponential of the genuine jump count. The supremum of
finite-count exponentials is infinite on explosion and agrees with the
usual exponential whenever the count is finite, as proved below. -/
def fluctuationExpJumpCount (M : DensityDepCTMC d) (T : ℝ)
    (ω : M.canonicalRecordΩ) : ℝ≥0∞ :=
  ⨆ r, ENNReal.ofReal
    (Real.exp (fluctuationJumpCountPartial M T r ω : ℝ))

theorem fluctuationJumpCountPartial_mono (M : DensityDepCTMC d) (T : ℝ)
    (ω : M.canonicalRecordΩ) :
    Monotone (fun r => fluctuationJumpCountPartial M T r ω) := by
  classical
  apply monotone_nat_of_le_succ
  intro r
  simp only [fluctuationJumpCountPartial, Finset.sum_range_succ]
  omega

theorem measurable_fluctuationJumpCount (M : DensityDepCTMC d) (T : ℝ) :
    Measurable (fluctuationJumpCount M T) :=
  Measurable.iSup fun r =>
    (Measurable.of_discrete :
      Measurable (fun k : ℕ => (k : ℝ≥0∞))).comp
        (measurable_fluctuationJumpCountPartial M T r)

theorem measurable_fluctuationExpJumpCount (M : DensityDepCTMC d) (T : ℝ) :
    Measurable (fluctuationExpJumpCount M T) :=
  Measurable.iSup fun r =>
    (Measurable.of_discrete :
      Measurable (fun k : ℕ => ENNReal.ofReal (Real.exp (k : ℝ)))).comp
        (measurable_fluctuationJumpCountPartial M T r)

/-- L6: monotone convergence gives the exponential moment of the full
extended count, with the same constant as for every finite record count. -/
theorem fluctuation_lintegral_exp_jumpCount (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) :
    (∫⁻ ω, fluctuationExpJumpCount M T ω
      ∂M.canonicalRecordMeasure z) ≤
        ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * Λ * T)) := by
  let f : ℕ → M.canonicalRecordΩ → ℝ≥0∞ := fun r ω =>
    ENNReal.ofReal (Real.exp (fluctuationJumpCountPartial M T r ω : ℝ))
  have hf : ∀ r, Measurable (f r) := fun r =>
    (Measurable.of_discrete :
      Measurable (fun k : ℕ => ENNReal.ofReal (Real.exp (k : ℝ)))).comp
        (measurable_fluctuationJumpCountPartial M T r)
  have hmono : Monotone f := by
    intro r s hrs ω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact_mod_cast fluctuationJumpCountPartial_mono M T ω hrs
  calc
    (∫⁻ ω, fluctuationExpJumpCount M T ω ∂M.canonicalRecordMeasure z) =
        ⨆ r, ∫⁻ ω, f r ω ∂M.canonicalRecordMeasure z :=
      lintegral_iSup hf hmono
    _ ≤ ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * Λ * T)) :=
      iSup_le fun r =>
        fluctuation_lintegral_exp_jumpCountPartial M z hT hΛ r

private theorem fm_exp_one_sub_one_pos : 0 < Real.exp 1 - 1 := by
  have h : Real.exp 0 < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  simpa only [Real.exp_zero, sub_pos] using h

/-- The discrete estimate giving L6's exact denominator e - 1. -/
private theorem fm_nat_le_exp_div (k : ℕ) :
    (k : ℝ) ≤ Real.exp (k : ℝ) / (Real.exp 1 - 1) := by
  have he : 0 < Real.exp 1 - 1 := fm_exp_one_sub_one_pos
  have hber : ∀ j : ℕ, 1 + (j : ℝ) * (Real.exp 1 - 1) ≤ Real.exp (j : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hx : 1 ≤ Real.exp (j : ℝ) := by
        simpa only [Real.exp_zero] using
          (Real.exp_le_exp.mpr (Nat.cast_nonneg j))
      have hmul := mul_nonneg (sub_nonneg.mpr hx) he.le
      rw [Nat.cast_succ, Real.exp_add]
      nlinarith
  apply (le_div_iff₀ he).mpr
  linarith [hber k]

/-- L6's explicit expectation estimate, in extended-integral form. -/
theorem fluctuation_lintegral_jumpCount (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) :
    (∫⁻ ω, fluctuationJumpCount M T ω ∂M.canonicalRecordMeasure z) ≤
      ENNReal.ofReal
        (Real.exp ((Real.exp 1 - 1) * Λ * T) / (Real.exp 1 - 1)) := by
  have he : 0 < Real.exp 1 - 1 := fm_exp_one_sub_one_pos
  have hm : ∀ r, Measurable
      (fun ω => (fluctuationJumpCountPartial M T r ω : ℝ≥0∞)) := fun r =>
    (Measurable.of_discrete :
      Measurable (fun k : ℕ => (k : ℝ≥0∞))).comp
        (measurable_fluctuationJumpCountPartial M T r)
  have hmono : Monotone
      (fun r ω => (fluctuationJumpCountPartial M T r ω : ℝ≥0∞)) := by
    intro r s hrs ω
    change (fluctuationJumpCountPartial M T r ω : ℝ≥0∞) ≤
      (fluctuationJumpCountPartial M T s ω : ℝ≥0∞)
    exact_mod_cast fluctuationJumpCountPartial_mono M T ω hrs
  change (∫⁻ ω, ⨆ r, (fluctuationJumpCountPartial M T r ω : ℝ≥0∞)
    ∂M.canonicalRecordMeasure z) ≤ _
  rw [lintegral_iSup hm hmono]
  apply iSup_le
  intro r
  have hexp : Measurable (fun ω : M.canonicalRecordΩ =>
      ENNReal.ofReal (Real.exp (fluctuationJumpCountPartial M T r ω : ℝ))) :=
    (Measurable.of_discrete :
      Measurable (fun k : ℕ => ENNReal.ofReal (Real.exp (k : ℝ)))).comp
        (measurable_fluctuationJumpCountPartial M T r)
  calc
    (∫⁻ ω, (fluctuationJumpCountPartial M T r ω : ℝ≥0∞)
        ∂M.canonicalRecordMeasure z) ≤
      ∫⁻ ω, ENNReal.ofReal
        (Real.exp (fluctuationJumpCountPartial M T r ω : ℝ)) /
          ENNReal.ofReal (Real.exp 1 - 1) ∂M.canonicalRecordMeasure z := by
      apply lintegral_mono
      intro ω
      change (fluctuationJumpCountPartial M T r ω : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp (fluctuationJumpCountPartial M T r ω : ℝ)) /
          ENNReal.ofReal (Real.exp 1 - 1)
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos he]
      exact ENNReal.ofReal_le_ofReal (fm_nat_le_exp_div _)
    _ = (∫⁻ ω, ENNReal.ofReal
          (Real.exp (fluctuationJumpCountPartial M T r ω : ℝ))
          ∂M.canonicalRecordMeasure z) / ENNReal.ofReal (Real.exp 1 - 1) := by
      simp only [div_eq_mul_inv]
      exact lintegral_mul_const _ hexp
    _ ≤ ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * Λ * T)) /
          ENNReal.ofReal (Real.exp 1 - 1) := by
      exact mul_le_mul_right'
        (fluctuation_lintegral_exp_jumpCountPartial M z hT hΛ r) _
    _ = ENNReal.ofReal
          (Real.exp ((Real.exp 1 - 1) * Λ * T) / (Real.exp 1 - 1)) :=
      (ENNReal.ofReal_div_of_pos he).symm

theorem fluctuationJumpCount_ne_top_ae (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) :
    ∀ᵐ ω ∂M.canonicalRecordMeasure z, fluctuationJumpCount M T ω ≠ ∞ := by
  have hi : (∫⁻ ω, fluctuationJumpCount M T ω
      ∂M.canonicalRecordMeasure z) ≠ ∞ :=
    ne_of_lt ((fluctuation_lintegral_jumpCount M z hT hΛ).trans_lt (by simp))
  exact (ae_lt_top (measurable_fluctuationJumpCount M T) hi).mono
    fun _ h => h.ne

theorem integrable_fluctuationJumpCount_toReal (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) :
    Integrable (fun ω => (fluctuationJumpCount M T ω).toReal)
      (M.canonicalRecordMeasure z) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_fluctuationJumpCount M T).aemeasurable
  exact ne_of_lt
    ((fluctuation_lintegral_jumpCount M z hT hΛ).trans_lt (by simp))

/-- L6's expectation estimate as an ordinary real expectation. -/
theorem fluctuation_integral_jumpCount (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) :
    (∫ ω, (fluctuationJumpCount M T ω).toReal
      ∂M.canonicalRecordMeasure z) ≤
        Real.exp ((Real.exp 1 - 1) * Λ * T) / (Real.exp 1 - 1) := by
  have ha : ∀ᵐ ω ∂M.canonicalRecordMeasure z,
      fluctuationJumpCount M T ω < ∞ :=
    (fluctuationJumpCount_ne_top_ae M z hT hΛ).mono
      fun _ h => lt_top_iff_ne_top.mpr h
  rw [integral_toReal (measurable_fluctuationJumpCount M T).aemeasurable ha]
  have hb := ENNReal.toReal_mono (by simp)
    (fluctuation_lintegral_jumpCount M z hT hΛ)
  simpa only [ENNReal.toReal_ofReal
    (div_nonneg (Real.exp_pos _).le fm_exp_one_sub_one_pos.le)] using hb

private theorem fm_nat_threshold {p : ℕ → ℕ} {q : ℕ} (hq : 1 ≤ q)
    (h : (q : ℝ≥0∞) ≤ ⨆ r, (p r : ℝ≥0∞)) :
    ∃ r, q ≤ p r := by
  by_contra! hn
  have hu : (⨆ r, (p r : ℝ≥0∞)) ≤ ((q - 1 : ℕ) : ℝ≥0∞) := by
    apply iSup_le
    intro r
    have hr : p r ≤ q - 1 := by have := hn r; omega
    exact_mod_cast hr
  have hlt : ((q - 1 : ℕ) : ℝ≥0∞) < (q : ℝ≥0∞) := by
    exact_mod_cast (show q - 1 < q by omega)
  exact (lt_irrefl (q : ℝ≥0∞)) ((h.trans hu).trans_lt hlt)

/-- L6's count tail for every positive integer threshold.
The event uses the extended count, including explosive records. -/
theorem fluctuation_jumpCount_tail (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) (q : ℕ) (hq : 1 ≤ q) :
    M.canonicalRecordMeasure z {ω | (q : ℝ≥0∞) ≤ fluctuationJumpCount M T ω} ≤
      ENNReal.ofReal (Real.exp (-(q : ℝ) + (Real.exp 1 - 1) * Λ * T)) := by
  have hsubset :
      {ω : M.canonicalRecordΩ | (q : ℝ≥0∞) ≤ fluctuationJumpCount M T ω} ⊆
      {ω | ENNReal.ofReal (Real.exp (q : ℝ)) ≤ fluctuationExpJumpCount M T ω} := by
    intro ω hω
    change (q : ℝ≥0∞) ≤
      ⨆ j, (fluctuationJumpCountPartial M T j ω : ℝ≥0∞) at hω
    change ENNReal.ofReal (Real.exp (q : ℝ)) ≤
      ⨆ j, ENNReal.ofReal (Real.exp (fluctuationJumpCountPartial M T j ω : ℝ))
    obtain ⟨r, hr⟩ := fm_nat_threshold hq hω
    refine le_trans ?_
      (le_iSup (f := fun j : ℕ =>
        ENNReal.ofReal (Real.exp (fluctuationJumpCountPartial M T j ω : ℝ))) r)
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact_mod_cast hr
  calc
    M.canonicalRecordMeasure z {ω | (q : ℝ≥0∞) ≤ fluctuationJumpCount M T ω} ≤
        M.canonicalRecordMeasure z
          {ω | ENNReal.ofReal (Real.exp (q : ℝ)) ≤ fluctuationExpJumpCount M T ω} :=
      measure_mono hsubset
    _ ≤ (∫⁻ ω, fluctuationExpJumpCount M T ω ∂M.canonicalRecordMeasure z) /
          ENNReal.ofReal (Real.exp (q : ℝ)) :=
      meas_ge_le_lintegral_div
        (measurable_fluctuationExpJumpCount M T).aemeasurable
        (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) (by simp)
    _ ≤ ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * Λ * T)) /
          ENNReal.ofReal (Real.exp (q : ℝ)) :=
      mul_le_mul_right' (fluctuation_lintegral_exp_jumpCount M z hT hΛ) _
    _ = ENNReal.ofReal
          (Real.exp (-(q : ℝ) + (Real.exp 1 - 1) * Λ * T)) := by
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
      congr 2
      ring

/-- The extended exponential dominates the count on every record. -/
theorem fluctuationJumpCount_le_expJumpCount (M : DensityDepCTMC d)
    (T : ℝ) (ω : M.canonicalRecordΩ) :
    fluctuationJumpCount M T ω ≤ fluctuationExpJumpCount M T ω := by
  apply iSup_le
  intro r
  apply le_trans _ (le_iSup _ r)
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  linarith [Real.add_one_le_exp (fluctuationJumpCountPartial M T r ω : ℝ)]

theorem fluctuationExpJumpCount_eq_top (M : DensityDepCTMC d)
    (T : ℝ) (ω : M.canonicalRecordΩ)
    (hω : fluctuationJumpCount M T ω = ∞) :
    fluctuationExpJumpCount M T ω = ∞ := by
  apply eq_top_iff.mpr
  calc
    ∞ = fluctuationJumpCount M T ω := hω.symm
    _ ≤ fluctuationExpJumpCount M T ω :=
      fluctuationJumpCount_le_expJumpCount M T ω

private theorem fm_sup_nat_exp_eq (p : ℕ → ℕ)
    (hp : (⨆ r, (p r : ℝ≥0∞)) ≠ ∞) :
    (⨆ r, ENNReal.ofReal (Real.exp (p r : ℝ))) =
      ENNReal.ofReal (Real.exp ((⨆ r, (p r : ℝ≥0∞)).toReal)) := by
  classical
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt hp
  have hpK : ∀ r, p r < K := by
    intro r
    have h := (le_iSup (fun j => (p j : ℝ≥0∞)) r).trans_lt hK
    exact_mod_cast h
  let s : Finset ℕ := (Finset.range K).filter (fun k => ∃ r, p r = k)
  have hmem : ∀ r, p r ∈ s := fun r =>
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hpK r), ⟨r, rfl⟩⟩
  have hs : s.Nonempty := ⟨p 0, hmem 0⟩
  obtain ⟨r, hr⟩ := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hmax : ∀ j, p j ≤ p r := by
    intro j
    rw [hr]
    exact Finset.le_max' s (p j) (hmem j)
  have hc : (⨆ j, (p j : ℝ≥0∞)) = (p r : ℝ≥0∞) := by
    apply le_antisymm
    · exact iSup_le fun j => by exact_mod_cast hmax j
    · exact le_iSup (f := fun j : ℕ => (p j : ℝ≥0∞)) r
  have he : (⨆ j, ENNReal.ofReal (Real.exp (p j : ℝ))) =
      ENNReal.ofReal (Real.exp (p r : ℝ)) := by
    apply le_antisymm
    · apply iSup_le
      intro j
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact_mod_cast hmax j
    · exact le_iSup
        (f := fun j : ℕ => ENNReal.ofReal (Real.exp (p j : ℝ))) r
  rw [hc, he, ENNReal.toReal_natCast]

/-- On every finite-count record, the extended exponential is the usual
exponential of the count. -/
theorem fluctuationExpJumpCount_eq_of_ne_top (M : DensityDepCTMC d)
    (T : ℝ) (ω : M.canonicalRecordΩ)
    (hω : fluctuationJumpCount M T ω ≠ ∞) :
    fluctuationExpJumpCount M T ω =
      ENNReal.ofReal (Real.exp ((fluctuationJumpCount M T ω).toReal)) :=
  fm_sup_nat_exp_eq (fun r => fluctuationJumpCountPartial M T r ω) hω

/-- The ordinary exponential of the a.s.-finite count is integrable. -/
theorem integrable_exp_fluctuationJumpCount_toReal (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) :
    Integrable (fun ω => Real.exp ((fluctuationJumpCount M T ω).toReal))
      (M.canonicalRecordMeasure z) := by
  have hi : (∫⁻ ω, fluctuationExpJumpCount M T ω
      ∂M.canonicalRecordMeasure z) ≠ ∞ :=
    ne_of_lt ((fluctuation_lintegral_exp_jumpCount M z hT hΛ).trans_lt (by simp))
  have hreal := integrable_toReal_of_lintegral_ne_top
    (measurable_fluctuationExpJumpCount M T).aemeasurable hi
  apply hreal.congr
  filter_upwards [fluctuationJumpCount_ne_top_ae M z hT hΛ] with ω hω
  rw [fluctuationExpJumpCount_eq_of_ne_top M T ω hω,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- L6's infinite-count exponential moment as an ordinary real expectation.
The extended version above also controls the explosion event. -/
theorem fluctuation_integral_exp_jumpCount (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) :
    (∫ ω, Real.exp ((fluctuationJumpCount M T ω).toReal)
      ∂M.canonicalRecordMeasure z) ≤
        Real.exp ((Real.exp 1 - 1) * Λ * T) := by
  have hi : (∫⁻ ω, fluctuationExpJumpCount M T ω
      ∂M.canonicalRecordMeasure z) ≠ ∞ :=
    ne_of_lt ((fluctuation_lintegral_exp_jumpCount M z hT hΛ).trans_lt (by simp))
  have ha := ae_lt_top (measurable_fluctuationExpJumpCount M T) hi
  have heq : (fun ω => Real.exp ((fluctuationJumpCount M T ω).toReal)) =ᵐ[
      M.canonicalRecordMeasure z]
      (fun ω => (fluctuationExpJumpCount M T ω).toReal) := by
    filter_upwards [fluctuationJumpCount_ne_top_ae M z hT hΛ] with ω hω
    rw [fluctuationExpJumpCount_eq_of_ne_top M T ω hω,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [integral_congr_ae heq,
    integral_toReal (measurable_fluctuationExpJumpCount M T).aemeasurable ha]
  have hb := ENNReal.toReal_mono (by simp)
    (fluctuation_lintegral_exp_jumpCount M z hT hΛ)
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using hb

/-! ## Explicit document corollaries -/

/-- Lemma 2.4's finite-count tail. Setting q = r gives its displayed
record-count estimate; L6 uses the full-count version above. -/
theorem fluctuation_jumpCountPartial_tail (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ Λ) (r q : ℕ) (hq : 1 ≤ q) :
    M.canonicalRecordMeasure z {ω | q ≤ fluctuationJumpCountPartial M T r ω} ≤
      ENNReal.ofReal (Real.exp (-(q : ℝ) + (Real.exp 1 - 1) * Λ * T)) := by
  refine (measure_mono ?_).trans (fluctuation_jumpCount_tail M z hT hΛ q hq)
  intro ω hω
  change q ≤ fluctuationJumpCountPartial M T r ω at hω
  have hc : (q : ℝ≥0∞) ≤ (fluctuationJumpCountPartial M T r ω : ℝ≥0∞) := by
    exact_mod_cast hω
  exact hc.trans
    (le_iSup (fun j => (fluctuationJumpCountPartial M T j ω : ℝ≥0∞)) r)

/-- L6's density-dependent expectation bound with N and the uniform
per-population rate constant explicit in the type. -/
theorem fluctuation_integral_jumpCount_uniform (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {T Λ : ℝ} (hT : 0 ≤ T)
    (hΛ : ∀ x, M.exitRateAt x ≤ (M.N : ℝ) * Λ) :
    (∫ ω, (fluctuationJumpCount M T ω).toReal
      ∂M.canonicalRecordMeasure z) ≤
        Real.exp ((Real.exp 1 - 1) * (M.N : ℝ) * Λ * T) /
          (Real.exp 1 - 1) := by
  simpa only [mul_assoc] using
    (fluctuation_integral_jumpCount M z (Λ := (M.N : ℝ) * Λ) hT hΛ)

/-! ## Integrability of the already-defined total functionals -/

private theorem fm_scaled_coord (M : DensityDepCTMC d)
    (x : Fin d → Fin (M.N + 1)) (i : Fin d) :
    0 ≤ M.scaledState x i ∧ M.scaledState x i ≤ 1 := by
  have hN : (0 : ℝ) < M.N := by exact_mod_cast M.hN
  change 0 ≤ (x i : ℝ) / M.N ∧ (x i : ℝ) / M.N ≤ 1
  refine ⟨div_nonneg (Nat.cast_nonneg _) hN.le, ?_⟩
  apply (div_le_one hN).2
  exact_mod_cast (Nat.le_of_lt_succ (x i).isLt)

private theorem fm_scaled_sub_norm_le_one (M : DensityDepCTMC d)
    (x y : Fin d → Fin (M.N + 1)) :
    ‖M.scaledState y - M.scaledState x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  change ‖M.scaledState y i - M.scaledState x i‖ ≤ 1
  rw [Real.norm_eq_abs]
  have hx := fm_scaled_coord M x i
  have hy := fm_scaled_coord M y i
  apply abs_le.mpr
  constructor <;> linarith

/-- L6's sharp coordinate-sum bound on each finite jump functional.
The test is the bounded Borel extension used in the total definition. -/
theorem fluctuation_abs_jumpPartial_le (M : DensityDepCTMC d)
    {ψ : ℝ → Fin d → ℝ} {τ T C : ℝ}
    (hτ : τ ≤ T) (hC : 0 ≤ C) (hψC : ∀ s, ‖ψ s‖ ≤ C)
    (r : ℕ) (ω : M.canonicalRecordΩ) :
    |fluctuationJumpPartialSum M ψ τ r ω| ≤
      (d : ℝ) * C * (fluctuationJumpCountPartial M T r ω : ℝ) := by
  classical
  have hterm (k : ℕ) :
      |fluctuationJumpSummand M ψ τ k ω| ≤ (d : ℝ) * C *
        ((if QMatrix.recTime ω (k + 1) ≤ T ∧
          (ω (k + 1)).2 ≠ (ω k).2 then 1 else 0 : ℕ) : ℝ) := by
    by_cases hk : QMatrix.recTime ω (k + 1) ≤ τ ∧
        (ω (k + 1)).2 ≠ (ω k).2
    · have hkT : QMatrix.recTime ω (k + 1) ≤ T ∧
          (ω (k + 1)).2 ≠ (ω k).2 := ⟨hk.1.trans hτ, hk.2⟩
      simp only [fluctuationJumpSummand, if_pos hk, if_pos hkT,
        Nat.cast_one, mul_one]
      calc
        |ψ (QMatrix.recTime ω (k + 1)) ⬝ᵥ
            (M.scaledState (ω (k + 1)).2 - M.scaledState (ω k).2)|
            ≤ (d : ℝ) * ‖ψ (QMatrix.recTime ω (k + 1))‖ *
              ‖M.scaledState (ω (k + 1)).2 - M.scaledState (ω k).2‖ :=
          fluctuation_abs_dot_le _ _
        _ ≤ (d : ℝ) * C * 1 :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (hψC _) (Nat.cast_nonneg _))
            (fm_scaled_sub_norm_le_one M _ _) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hC)
        _ = (d : ℝ) * C := mul_one _
    · simp only [fluctuationJumpSummand, if_neg hk, abs_zero]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (Nat.cast_nonneg _)
  calc
    |fluctuationJumpPartialSum M ψ τ r ω|
        ≤ ∑ k ∈ Finset.range r, |fluctuationJumpSummand M ψ τ k ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range r, (d : ℝ) * C *
        ((if QMatrix.recTime ω (k + 1) ≤ T ∧
          (ω (k + 1)).2 ≠ (ω k).2 then 1 else 0 : ℕ) : ℝ) :=
      Finset.sum_le_sum fun k _ => hterm k
    _ = (d : ℝ) * C * (fluctuationJumpCountPartial M T r ω : ℝ) := by
      simp only [fluctuationJumpCountPartial, Nat.cast_sum, Finset.mul_sum]

/-- The total zero-off-Cauchy functional is dominated by the total genuine
jump count whenever that count is finite. This also covers ambient records
outside the common good-record event. -/
theorem fluctuation_abs_jumpFunctional_le (M : DensityDepCTMC d)
    {ψ : ℝ → Fin d → ℝ} {τ T C : ℝ} {ω : M.canonicalRecordΩ}
    (hτ : τ ≤ T) (hC : 0 ≤ C) (hψC : ∀ s, ‖ψ s‖ ≤ C)
    (hfinite : fluctuationJumpCount M T ω ≠ ∞) :
    |fluctuationJumpFunctional M ψ τ ω| ≤
      (d : ℝ) * C * (fluctuationJumpCount M T ω).toReal := by
  classical
  have hcount (r : ℕ) :
      (fluctuationJumpCountPartial M T r ω : ℝ) ≤
        (fluctuationJumpCount M T ω).toReal := by
    have hle : (fluctuationJumpCountPartial M T r ω : ℝ≥0∞) ≤
        fluctuationJumpCount M T ω :=
      le_iSup (fun j => (fluctuationJumpCountPartial M T j ω : ℝ≥0∞)) r
    simpa using ENNReal.toReal_mono hfinite hle
  have hb (r : ℕ) :
      |fluctuationJumpPartialSum M ψ τ r ω| ≤
        (d : ℝ) * C * (fluctuationJumpCount M T ω).toReal :=
    (fluctuation_abs_jumpPartial_le M hτ hC hψC r ω).trans
      (mul_le_mul_of_nonneg_left (hcount r)
        (mul_nonneg (Nat.cast_nonneg _) hC))
  by_cases hu : CauchySeq (fun r => fluctuationJumpPartialSum M ψ τ r ω)
  · have ht : Tendsto (fun r => fluctuationJumpPartialSum M ψ τ r ω)
        atTop (𝓝 (fluctuationJumpFunctional M ψ τ ω)) := by
      simpa only [fluctuationJumpFunctional, fluctuationLimitZero, dif_pos hu]
        using (cauchySeq_tendsto_of_complete hu).choose_spec
    exact le_of_tendsto ht.abs (Eventually.of_forall hb)
  · simpa only [fluctuationJumpFunctional, fluctuationLimitZero, dif_neg hu,
      abs_zero] using
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hC)
        (ENNReal.toReal_nonneg (a := fluctuationJumpCount M T ω)))

/-- L6: the already-defined total jump functional is integrable for every
bounded Borel test, hence for the document's bounded extension of a C1 test.
The finite lattice supplies the exit-rate bound; no extra rate hypothesis
is imposed here. -/
theorem integrable_fluctuationJumpFunctional (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {ψ : ℝ → Fin d → ℝ}
    (hψ : Measurable ψ) (hψb : ∃ C : ℝ, ∀ s, ‖ψ s‖ ≤ C)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fluctuationJumpFunctional M ψ τ) (M.canonicalRecordMeasure z) := by
  obtain ⟨C, hψC⟩ := hψb
  have hC : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hψC 0)
  obtain ⟨Λ, _hΛpos, hΛ⟩ := M.exists_exitRateAt_bound
  have hcount := integrable_fluctuationJumpCount_toReal M z hτ hΛ
  have hfinite := fluctuationJumpCount_ne_top_ae M z hτ hΛ
  refine (hcount.const_mul ((d : ℝ) * C)).mono'
    (measurable_fluctuationJumpFunctional M hψ τ).aestronglyMeasurable ?_
  filter_upwards [hfinite] with ω hω
  simpa only [Real.norm_eq_abs] using
    fluctuation_abs_jumpFunctional_le M (le_refl τ) hC hψC hω

private theorem fm_abs_integral_le {τ C : ℝ} (hτ : 0 ≤ τ)
    (f : ℝ → ℝ) (hb : ∀ s ∈ Icc 0 τ, |f s| ≤ C) :
    |∫ s in Icc 0 τ, f s| ≤ τ * C := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) τ)) :=
    ⟨by simpa using (measure_Icc_lt_top : volume (Icc (0 : ℝ) τ) < ⊤)⟩
  have hbound : (fun s => |f s|) ≤ᵐ[volume.restrict (Icc 0 τ)]
      (fun _ => C) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    exact hb s hs
  calc
    |∫ s in Icc 0 τ, f s| ≤ ∫ s in Icc 0 τ, |f s| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (f := f) (μ := volume.restrict (Icc 0 τ)))
    _ ≤ ∫ _s in Icc (0 : ℝ) τ, C :=
      integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg (f s))
        (integrable_const C) hbound
    _ = τ * C := by
      simp [Real.volume_Icc, hτ, smul_eq_mul]

/-- The drift part of L6 is integrable. A finite-state bound is sufficient,
since every total frozen readout is a scaled lattice state, even on bad
ambient records. -/
theorem integrable_fluctuationDriftIntegral (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {ψ : ℝ → Fin d → ℝ}
    (hψ : Measurable ψ) (hψb : ∃ C : ℝ, ∀ s, ‖ψ s‖ ≤ C)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fluctuationDriftIntegral M ψ τ) (M.canonicalRecordMeasure z) := by
  classical
  obtain ⟨C, hψC⟩ := hψb
  have hC : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hψC 0)
  let B : ℝ :=
    ∑ x : Fin d → Fin (M.N + 1), ‖M.rateSpec.drift (M.scaledState x)‖
  have hF (x : Fin d → Fin (M.N + 1)) :
      ‖M.rateSpec.drift (M.scaledState x)‖ ≤ B := by
    exact Finset.single_le_sum
      (f := fun y : Fin d → Fin (M.N + 1) =>
        ‖M.rateSpec.drift (M.scaledState y)‖)
      (fun y _ => norm_nonneg _) (Finset.mem_univ x)
  have hbound (ω : M.canonicalRecordΩ) :
      |fluctuationDriftIntegral M ψ τ ω| ≤ τ * ((d : ℝ) * C * B) := by
    change |∫ s in Icc 0 τ, ψ s ⬝ᵥ
      M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω)| ≤
        τ * ((d : ℝ) * C * B)
    apply fm_abs_integral_le hτ
    intro s _
    have hFs :
        ‖M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s ω)‖ ≤ B := by
      change ‖M.rateSpec.drift
        (M.scaledState ((M.canonicalPathMap ω).frozenStateAt s))‖ ≤ B
      exact hF _
    exact (fluctuation_abs_dot_le _ _).trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_left (hψC s) (Nat.cast_nonneg _))
        hFs (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC))
  refine (integrable_const (τ * ((d : ℝ) * C * B))).mono'
    (measurable_fluctuationDriftIntegral M hψ τ).aestronglyMeasurable ?_
  exact Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using hbound ω

/-- L6: the total compensated jump functional I_n = J_n - drift integral
is integrable under the canonical record law. -/
theorem integrable_fluctuationCompensatedJump (M : DensityDepCTMC d)
    (z : Fin d → Fin (M.N + 1)) {ψ : ℝ → Fin d → ℝ}
    (hψ : Measurable ψ) (hψb : ∃ C : ℝ, ∀ s, ‖ψ s‖ ≤ C)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fluctuationCompensatedJump M ψ τ)
      (M.canonicalRecordMeasure z) := by
  simpa only [fluctuationCompensatedJump] using
    (integrable_fluctuationJumpFunctional M z hψ hψb hτ).sub
      (integrable_fluctuationDriftIntegral M z hψ hψb hτ)

end

end Ripple.Kurtz
