/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kernel-native cancellation clock concentration

This file is protocol-free probability infrastructure.  The state space is an
abstract discrete measurable space, `K` is an arbitrary Markov kernel, and `C`
is a natural-valued progress/cancellation counter.  The reusable clock is

  `H k = sum_{i < k} 1 / q_i`.

The concentration engine is built on the repository's kernel-native
Azuma-Hoeffding lemma `ExactMajority.azuma_tail`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AzumaKernel
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Data.Finset.Fold

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ExactMajority
namespace CancelClockConcentration

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Integrated inverse-rate clock `H(k) = sum_{i=0}^{k-1} 1/q_i`.

For `k > D`, terms beyond `D` contribute `0`; all applications below use
`k ≤ D` or the capped version `integratedInvRateClockCap`. -/
noncomputable def integratedInvRateClock (D : ℕ) (q : Fin D → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, if hi : i < D then (q ⟨i, hi⟩)⁻¹ else 0

/-- The clock stopped at the target level `D`. -/
noncomputable def integratedInvRateClockCap (D : ℕ) (q : Fin D → ℝ) (k : ℕ) : ℝ :=
  integratedInvRateClock D q (min k D)

/-- Canonical increment scale
`max(1, max_i (1/q_i - 1))`, implemented as a fold so the empty target
case has value `1`. -/
noncomputable def invRateSlack (D : ℕ) (q : Fin D → ℝ) : ℝ :=
  (Finset.range D).fold max 1
    (fun i => if hi : i < D then (q ⟨i, hi⟩)⁻¹ - 1 else 0)

/-- Active states are those below the target counter value. -/
def activeSet (C : Ω → ℕ) (D : ℕ) : Set Ω := {x | C x < D}

/-- The target-stopped kernel on the original state space. -/
noncomputable def stoppedKernel [DiscreteMeasurableSpace Ω]
    (K : Kernel Ω Ω) (C : Ω → ℕ) (D : ℕ) : Kernel Ω Ω :=
  by
    classical
    exact Kernel.piecewise
      (DiscreteMeasurableSpace.forall_measurableSet (activeSet C D)) K Kernel.id

instance stoppedKernel_isMarkov [DiscreteMeasurableSpace Ω]
    (K : Kernel Ω Ω) [IsMarkovKernel K] (C : Ω → ℕ) (D : ℕ) :
    IsMarkovKernel (stoppedKernel K C D) := by
  classical
  unfold stoppedKernel
  infer_instance

/-- The stopped, clock-augmented kernel.

From `(t, x)`, if `C x < D` it runs one `K` step and increments the clock to
`t+1`; once `C x ≥ D`, it freezes both coordinates. -/
noncomputable def clockKernel [DiscreteMeasurableSpace Ω] [DiscreteMeasurableSpace (ℕ × Ω)]
    (K : Kernel Ω Ω) (C : Ω → ℕ) (D : ℕ) :
    Kernel (ℕ × Ω) (ℕ × Ω) where
  toFun z :=
    if C z.2 < D then
      (K z.2).map (fun y => (z.1 + 1, y))
    else
      Measure.dirac z
  measurable' := Measurable.of_discrete

set_option linter.flexible false in
instance clockKernel_isMarkov [DiscreteMeasurableSpace Ω] [DiscreteMeasurableSpace (ℕ × Ω)]
    (K : Kernel Ω Ω) [IsMarkovKernel K] (C : Ω → ℕ) (D : ℕ) :
    IsMarkovKernel (clockKernel K C D) := by
  constructor
  intro z
  unfold clockKernel
  by_cases hz : C z.2 < D
  · simp [hz]
    haveI : IsProbabilityMeasure (K z.2) := IsMarkovKernel.isProbabilityMeasure z.2
    exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable)
  · simp [hz]
    infer_instance

/-- The stopped Azuma potential on the clock-augmented state. -/
noncomputable def stoppedClockPotential
    (D : ℕ) (q : Fin D → ℝ) (C : Ω → ℕ) (z : ℕ × Ω) : ℝ :=
  (z.1 : ℝ) - integratedInvRateClockCap D q (C z.2)

theorem integratedInvRateClock_zero (D : ℕ) (q : Fin D → ℝ) :
    integratedInvRateClock D q 0 = 0 := by
  simp [integratedInvRateClock]

theorem integratedInvRateClock_succ_of_lt
    (D : ℕ) (q : Fin D → ℝ) {i : ℕ} (hi : i < D) :
    integratedInvRateClock D q (i + 1)
      = integratedInvRateClock D q i + (q ⟨i, hi⟩)⁻¹ := by
  simp [integratedInvRateClock, Finset.sum_range_succ, hi]

theorem integratedInvRateClockCap_of_lt
    (D : ℕ) (q : Fin D → ℝ) {i : ℕ} (hi : i < D) :
    integratedInvRateClockCap D q i = integratedInvRateClock D q i := by
  simp [integratedInvRateClockCap, Nat.min_eq_left hi.le]

theorem integratedInvRateClockCap_succ_of_lt
    (D : ℕ) (q : Fin D → ℝ) {i : ℕ} (hi : i < D) :
    integratedInvRateClockCap D q (i + 1) =
      integratedInvRateClock D q i + (q ⟨i, hi⟩)⁻¹ := by
  rw [integratedInvRateClockCap, Nat.min_eq_left (Nat.succ_le_iff.mpr hi),
    integratedInvRateClock_succ_of_lt D q hi]

theorem invRateSlack_ge_one (D : ℕ) (q : Fin D → ℝ) :
    1 ≤ invRateSlack D q := by
  rw [invRateSlack]
  exact (Finset.le_fold_max (s := Finset.range D)
    (b := (1 : ℝ))
    (f := fun i => if hi : i < D then (q ⟨i, hi⟩)⁻¹ - 1 else 0) 1).2 (Or.inl le_rfl)

theorem invRateSlack_rate_le (D : ℕ) (q : Fin D → ℝ) (i : Fin D) :
    (q i)⁻¹ - 1 ≤ invRateSlack D q := by
  rw [invRateSlack]
  refine (Finset.le_fold_max (s := Finset.range D)
    (b := (1 : ℝ))
    (f := fun j => if hj : j < D then (q ⟨j, hj⟩)⁻¹ - 1 else 0)
    ((q i)⁻¹ - 1)).2 ?_
  refine Or.inr ⟨i.1, Finset.mem_range.mpr i.2, ?_⟩
  simp [i.2]

theorem integratedInvRateClock_nonneg
    (D : ℕ) (q : Fin D → ℝ) (hqpos : ∀ i, 0 < q i) (k : ℕ) :
    0 ≤ integratedInvRateClock D q k := by
  unfold integratedInvRateClock
  exact Finset.sum_nonneg (fun i hi => by
    by_cases hiD : i < D
    · simp [hiD, (hqpos ⟨i, hiD⟩).le]
    · simp [hiD])

theorem integratedInvRateClock_mono_to_target
    (D : ℕ) (q : Fin D → ℝ) (hqpos : ∀ i, 0 < q i)
    {k : ℕ} (hk : k ≤ D) :
    integratedInvRateClock D q k ≤ integratedInvRateClock D q D := by
  unfold integratedInvRateClock
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
  · intro i hi
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hk)
  · intro i hiD hik
    by_cases hlt : i < D
    · simp [hlt, (hqpos ⟨i, hlt⟩).le]
    · simp [hlt]

theorem integratedInvRateClockCap_le_target
    (D : ℕ) (q : Fin D → ℝ) (hqpos : ∀ i, 0 < q i) (k : ℕ) :
    integratedInvRateClockCap D q k ≤ integratedInvRateClock D q D := by
  exact integratedInvRateClock_mono_to_target D q hqpos (Nat.min_le_right _ _)

theorem integratedInvRateClockCap_nonneg
    (D : ℕ) (q : Fin D → ℝ) (hqpos : ∀ i, 0 < q i) (k : ℕ) :
    0 ≤ integratedInvRateClockCap D q k := by
  exact integratedInvRateClock_nonneg D q hqpos _

theorem integrable_fixedTime_potential [DiscreteMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : ℕ) (q : Fin D → ℝ) (C : Ω → ℕ) (hqpos : ∀ i, 0 < q i) (n : ℕ) :
    Integrable (fun y => (n : ℝ) - integratedInvRateClockCap D q (C y)) μ := by
  let B : ℝ := (n : ℝ) + integratedInvRateClock D q D
  have hBint : Integrable (fun _ : Ω => B) μ := integrable_const B
  refine Integrable.mono' hBint Measurable.of_discrete.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  have hcap0 : 0 ≤ integratedInvRateClockCap D q (C y) :=
    integratedInvRateClockCap_nonneg D q hqpos (C y)
  have hcapD : integratedInvRateClockCap D q (C y) ≤ integratedInvRateClock D q D :=
    integratedInvRateClockCap_le_target D q hqpos (C y)
  have hD0 : 0 ≤ integratedInvRateClock D q D :=
    integratedInvRateClock_nonneg D q hqpos D
  calc
    ‖(n : ℝ) - integratedInvRateClockCap D q (C y)‖
        = |(n : ℝ) - integratedInvRateClockCap D q (C y)| := rfl
    _ ≤ |(n : ℝ)| + |integratedInvRateClockCap D q (C y)| := by
      simpa using abs_sub_le (n : ℝ) 0 (integratedInvRateClockCap D q (C y))
    _ = (n : ℝ) + integratedInvRateClockCap D q (C y) := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ n), abs_of_nonneg hcap0]
    _ ≤ B := by
      unfold B
      linarith

section AugmentedKernel

variable [DiscreteMeasurableSpace Ω] [DiscreteMeasurableSpace (ℕ × Ω)]

private theorem isMarkovKernel_pow {α : Type*} [MeasurableSpace α]
    (κ : Kernel α α) [IsMarkovKernel κ] (m : ℕ) :
    IsMarkovKernel (κ ^ m) := by
  induction m with
  | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMarkovKernel (Kernel.id : Kernel α α))
  | succ m ih =>
      haveI := ih
      rw [pow_succ]
      exact inferInstanceAs (IsMarkovKernel ((κ ^ m) ∘ₖ κ))

set_option linter.flexible false in
theorem integral_clockKernel_active
    (K : Kernel Ω Ω) (C : Ω → ℕ) (D : ℕ)
    (z : ℕ × Ω) (hz : C z.2 < D) (f : ℕ × Ω → ℝ) :
    ∫ z', f z' ∂(clockKernel K C D z)
      = ∫ y, f (z.1 + 1, y) ∂(K z.2) := by
  unfold clockKernel
  simp [hz]
  rw [MeasureTheory.integral_map (Measurable.of_discrete.aemeasurable)
    (Measurable.of_discrete.aestronglyMeasurable)]

theorem integral_clockKernel_inactive
    (K : Kernel Ω Ω) (C : Ω → ℕ) (D : ℕ)
    (z : ℕ × Ω) (hz : ¬ C z.2 < D) (f : ℕ × Ω → ℝ) :
    ∫ z', f z' ∂(clockKernel K C D z) = f z := by
  unfold clockKernel
  simp [hz]

/-- Projection of the augmented stopped kernel to the original state space. -/
theorem clockKernel_project_snd
    (K : Kernel Ω Ω) [IsMarkovKernel K] (C : Ω → ℕ) (D : ℕ)
    (S : Set Ω) (hS : MeasurableSet S) (n : ℕ) (x : Ω) (t : ℕ) :
    (clockKernel K C D ^ t) (n, x) {z | z.2 ∈ S}
      = (stoppedKernel K C D ^ t) x S := by
  classical
  induction t generalizing n x with
  | zero =>
      rw [show (clockKernel K C D ^ 0) = Kernel.id from pow_zero _,
        show (stoppedKernel K C D ^ 0) = Kernel.id from pow_zero _,
        Kernel.id_apply, Kernel.id_apply,
        Measure.dirac_apply' (n, x) MeasurableSet.of_discrete,
        Measure.dirac_apply' x hS]
      rfl
  | succ t ih =>
      have hE : MeasurableSet ({z : ℕ × Ω | z.2 ∈ S}) := MeasurableSet.of_discrete
      rw [show t + 1 = 1 + t from by ring,
        Kernel.pow_add_apply_eq_lintegral (clockKernel K C D) 1 t (n, x) hE,
        Kernel.pow_add_apply_eq_lintegral (stoppedKernel K C D) 1 t x hS,
        pow_one, pow_one]
      by_cases hx : C x < D
      · have hclock_apply :
            clockKernel K C D (n, x) = (K x).map (fun y => (n + 1, y)) := by
          simp [clockKernel, hx]
        have hstop_apply :
            stoppedKernel K C D x = K x := by
          unfold stoppedKernel
          rw [Kernel.piecewise_apply]
          simp [activeSet, hx]
        rw [hclock_apply, hstop_apply]
        rw [MeasureTheory.lintegral_map (Kernel.measurable_coe _ hE) Measurable.of_discrete]
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall (fun y => by simp [ih (n + 1) y])
      · have hclock_apply :
            clockKernel K C D (n, x) = Measure.dirac (n, x) := by
          simp [clockKernel, hx]
        have hstop_apply :
            stoppedKernel K C D x = Kernel.id x := by
          unfold stoppedKernel
          rw [Kernel.piecewise_apply]
          simp [activeSet, hx]
        rw [hclock_apply, hstop_apply]
        rw [lintegral_dirac' (n, x) (Kernel.measurable_coe _ hE)]
        rw [Kernel.id_apply, lintegral_dirac' x (Kernel.measurable_coe _ hS)]
        exact ih n x

set_option linter.flexible false in
/-- One-step bounded difference for the stopped clock potential. -/
theorem stoppedClockPotential_bdd
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (C : Ω → ℕ) (D : ℕ) (q : Fin D → ℝ) (L : ℝ)
    (hqpos : ∀ i, 0 < q i) (hqle : ∀ i, q i ≤ 1)
    (hL1 : 1 ≤ L) (hLrate : ∀ i : Fin D, (q i)⁻¹ - 1 ≤ L)
    (hstep : ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1) :
    ∀ z, ∀ᵐ z' ∂(clockKernel K C D z),
      |stoppedClockPotential D q C z' - stoppedClockPotential D q C z| ≤ L := by
  intro z
  by_cases hz : C z.2 < D
  · unfold clockKernel
    simp [hz]
    rw [MeasureTheory.ae_map_iff (Measurable.of_discrete.aemeasurable)
      (by exact MeasurableSet.of_discrete)]
    filter_upwards [hstep z.2 hz] with y hy
    let i : Fin D := ⟨C z.2, hz⟩
    have hcur :
        integratedInvRateClockCap D q (C z.2) = integratedInvRateClock D q (C z.2) :=
      integratedInvRateClockCap_of_lt D q hz
    rcases hy with hstay | hinc
    · have hycap :
          integratedInvRateClockCap D q (C y) = integratedInvRateClock D q (C z.2) := by
        rw [hstay, integratedInvRateClockCap_of_lt D q hz]
      have hdiff :
          stoppedClockPotential D q C (z.1 + 1, y) - stoppedClockPotential D q C z = 1 := by
        simp [stoppedClockPotential, hcur, hycap]
      rw [hdiff, abs_one]
      exact hL1
    · have hycap :
          integratedInvRateClockCap D q (C y)
            = integratedInvRateClock D q (C z.2) + (q i)⁻¹ := by
        rw [hinc]
        exact integratedInvRateClockCap_succ_of_lt D q hz
      have hdiff :
          stoppedClockPotential D q C (z.1 + 1, y) - stoppedClockPotential D q C z
            = 1 - (q i)⁻¹ := by
        simp [stoppedClockPotential, hcur, hycap, i]
        ring
      have hinv_ge : 1 ≤ (q i)⁻¹ := (one_le_inv₀ (hqpos i)).2 (hqle i)
      have habs : |1 - (q i)⁻¹| = (q i)⁻¹ - 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr hinv_ge)]
        ring
      rw [hdiff, habs]
      exact hLrate i
  · unfold clockKernel
    simp [hz]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hL1

omit [DiscreteMeasurableSpace (ℕ × Ω)] in
/-- Expected clock increase is at least one before the target. -/
theorem expected_clock_increase_ge_one
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (C : Ω → ℕ) (D : ℕ) (q : Fin D → ℝ)
    (hqpos : ∀ i, 0 < q i)
    (hstep : ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hsucc : ∀ x (hx : C x < D),
      q ⟨C x, hx⟩ ≤ (K x).real {y | C y = C x + 1})
    (x : Ω) (hx : C x < D) :
    integratedInvRateClock D q (C x) + 1
      ≤ ∫ y, integratedInvRateClockCap D q (C y) ∂(K x) := by
  let i : Fin D := ⟨C x, hx⟩
  let S : Set Ω := {y | C y = C x + 1}
  have hS : MeasurableSet S := MeasurableSet.of_discrete
  have hH_int : Integrable (fun y => integratedInvRateClockCap D q (C y)) (K x) := by
    have hneg := integrable_fixedTime_potential (K x) D q C hqpos 0
    simpa using hneg.neg
  have hInd_int : Integrable (fun y => S.indicator (fun _ : Ω => (1 : ℝ)) y) (K x) :=
    (integrable_const (1 : ℝ)).indicator hS
  have hR_int :
      Integrable
        (fun y => integratedInvRateClock D q (C x)
          + (q i)⁻¹ * S.indicator (fun _ : Ω => (1 : ℝ)) y) (K x) :=
    (integrable_const (integratedInvRateClock D q (C x))).add (hInd_int.const_mul (q i)⁻¹)
  have hpoint :
      (fun y => integratedInvRateClock D q (C x)
          + (q i)⁻¹ * S.indicator (fun _ : Ω => (1 : ℝ)) y)
        ≤ᵐ[K x] (fun y => integratedInvRateClockCap D q (C y)) := by
    filter_upwards [hstep x hx] with y hy
    rcases hy with hstay | hinc
    · have hnot : y ∉ S := by
        intro hyS
        simp only [S, Set.mem_setOf_eq] at hyS
        omega
      simp [S, hnot, hstay, integratedInvRateClockCap_of_lt D q hx]
    · have hyS : y ∈ S := by
        simp [S, hinc]
      have hcap :
          integratedInvRateClockCap D q (C y)
            = integratedInvRateClock D q (C x) + (q i)⁻¹ := by
        rw [hinc]
        exact integratedInvRateClockCap_succ_of_lt D q hx
      simp [S, hyS, hcap]
  have hle_int :
      ∫ y, integratedInvRateClock D q (C x)
          + (q i)⁻¹ * S.indicator (fun _ : Ω => (1 : ℝ)) y ∂(K x)
        ≤ ∫ y, integratedInvRateClockCap D q (C y) ∂(K x) :=
    integral_mono_ae hR_int hH_int hpoint
  have hcalc :
      ∫ y, integratedInvRateClock D q (C x)
          + (q i)⁻¹ * S.indicator (fun _ : Ω => (1 : ℝ)) y ∂(K x)
        = integratedInvRateClock D q (C x) + (q i)⁻¹ * (K x).real S := by
    have hind :
        ∫ a, S.indicator (fun _ : Ω => (1 : ℝ)) a ∂(K x) = (K x).real S := by
      simpa using integral_indicator_one (μ := K x) hS
    rw [integral_add (integrable_const _) (hInd_int.const_mul (q i)⁻¹)]
    rw [integral_const, probReal_univ, one_smul]
    rw [integral_const_mul, hind]
  have hprob : q i ≤ (K x).real S := by
    simpa [i, S] using hsucc x hx
  have hgain : 1 ≤ (q i)⁻¹ * (K x).real S := by
    have hnonneg : 0 ≤ (q i)⁻¹ := inv_nonneg.mpr (hqpos i).le
    calc
      1 = (q i)⁻¹ * q i := by
        rw [inv_mul_cancel₀ (ne_of_gt (hqpos i))]
      _ ≤ (q i)⁻¹ * (K x).real S := by
        exact mul_le_mul_of_nonneg_left hprob hnonneg
  calc
    integratedInvRateClock D q (C x) + 1
        ≤ integratedInvRateClock D q (C x) + (q i)⁻¹ * (K x).real S := by
          linarith
    _ = ∫ y, integratedInvRateClock D q (C x)
          + (q i)⁻¹ * S.indicator (fun _ : Ω => (1 : ℝ)) y ∂(K x) := hcalc.symm
    _ ≤ ∫ y, integratedInvRateClockCap D q (C y) ∂(K x) := hle_int

set_option linter.flexible false in
/-- Supermartingale drift for `t - H(C_t)` on the stopped clock kernel. -/
theorem stoppedClockPotential_drift
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (C : Ω → ℕ) (D : ℕ) (q : Fin D → ℝ)
    (hqpos : ∀ i, 0 < q i)
    (hstep : ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hsucc : ∀ x (hx : C x < D),
      q ⟨C x, hx⟩ ≤ (K x).real {y | C y = C x + 1}) :
    ∀ z, ∫ z', stoppedClockPotential D q C z' ∂(clockKernel K C D z)
      ≤ stoppedClockPotential D q C z := by
  intro z
  by_cases hz : C z.2 < D
  · rw [integral_clockKernel_active K C D z hz]
    have hH_int : Integrable (fun y => integratedInvRateClockCap D q (C y)) (K z.2) := by
      have hneg := integrable_fixedTime_potential (K z.2) D q C hqpos 0
      simpa using hneg.neg
    have hpot_int :
        Integrable (fun y => stoppedClockPotential D q C (z.1 + 1, y)) (K z.2) := by
      simpa [stoppedClockPotential] using
        integrable_fixedTime_potential (K z.2) D q C hqpos (z.1 + 1)
    have hcur :
        integratedInvRateClockCap D q (C z.2) = integratedInvRateClock D q (C z.2) :=
      integratedInvRateClockCap_of_lt D q hz
    have hinc :=
      expected_clock_increase_ge_one K C D q hqpos hstep hsucc z.2 hz
    calc
      ∫ y, stoppedClockPotential D q C (z.1 + 1, y) ∂(K z.2)
          = (z.1 + 1 : ℝ) - ∫ y, integratedInvRateClockCap D q (C y) ∂(K z.2) := by
            simp [stoppedClockPotential]
            rw [integral_sub (integrable_const _) hH_int]
            rw [integral_const, probReal_univ, one_smul]
      _ ≤ (z.1 + 1 : ℝ) - (integratedInvRateClock D q (C z.2) + 1) := by
            linarith
      _ = stoppedClockPotential D q C z := by
            simp [stoppedClockPotential, hcur]
  · rw [integral_clockKernel_inactive K C D z hz]

set_option linter.flexible false in
/-- Under the augmented kernel, any still-active state after `t` steps has
clock coordinate exactly `t`. -/
theorem clockKernel_active_time_support
    (K : Kernel Ω Ω) [IsMarkovKernel K] (C : Ω → ℕ) (D : ℕ)
    (x₀ : Ω) (t : ℕ) :
    (clockKernel K C D ^ t) (0, x₀) {z | C z.2 < D ∧ z.1 ≠ t} = 0 := by
  induction t with
  | zero =>
      rw [show (clockKernel K C D ^ 0) = Kernel.id from pow_zero _,
        Kernel.id_apply,
        Measure.dirac_apply' (0, x₀) MeasurableSet.of_discrete]
      simp
  | succ t ih =>
      let Bad : Set (ℕ × Ω) := {z | C z.2 < D ∧ z.1 ≠ t + 1}
      have hBad : MeasurableSet Bad := MeasurableSet.of_discrete
      rw [Kernel.pow_succ_apply_eq_lintegral (clockKernel K C D) t (0, x₀) hBad]
      rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hBad)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{z | ¬ (C z.2 < D ∧ z.1 ≠ t)}, ?_, ?_⟩
      · rw [mem_ae_iff]
        have hcompl :
            ({z : ℕ × Ω | ¬ (C z.2 < D ∧ z.1 ≠ t)}ᶜ : Set (ℕ × Ω))
              = {z | C z.2 < D ∧ z.1 ≠ t} := by
          ext z
          simp
        rw [hcompl]
        exact ih
      · intro z hzgood
        simp only [Set.mem_setOf_eq, not_and, not_not] at hzgood
        by_cases hz : C z.2 < D
        · have hzt : z.1 = t := hzgood hz
          unfold clockKernel
          simp [hz, Bad]
          rw [Measure.map_apply Measurable.of_discrete hBad]
          have hpre :
              (fun y : Ω => (z.1 + 1, y)) ⁻¹' Bad = ∅ := by
            ext y
            simp [Bad, hzt]
          rw [hpre, measure_empty]
        · unfold clockKernel
          simp [hz, Bad]

omit [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [DiscreteMeasurableSpace (ℕ × Ω)] in
theorem stoppedClockPotential_start
    (D : ℕ) (q : Fin D → ℝ) (C : Ω → ℕ) (x₀ : Ω) (hC0 : C x₀ = 0) :
    stoppedClockPotential D q C (0, x₀) = 0 := by
  simp [stoppedClockPotential, integratedInvRateClockCap, hC0, integratedInvRateClock_zero]

/-- Core stopped-clock concentration, strict-time form.

This is the direct Azuma consequence for the stopped, clock-augmented kernel.
It assumes only the monotone unit-step support and the per-level success
probability floor. -/
theorem cancelClock_concentration_augmented_strict
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (C : Ω → ℕ) (D : ℕ) (q : Fin D → ℝ) (L : ℝ) (x₀ : Ω)
    (hC0 : C x₀ = 0)
    (hqpos : ∀ i, 0 < q i) (hqle : ∀ i, q i ≤ 1)
    (hL1 : 1 ≤ L) (hLrate : ∀ i : Fin D, (q i)⁻¹ - 1 ≤ L)
    (hstep : ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hsucc : ∀ x (hx : C x < D),
      q ⟨C x, hx⟩ ≤ (K x).real {y | C y = C x + 1})
    (T : ℕ) (hT : integratedInvRateClock D q D < (T : ℝ)) :
    (clockKernel K C D ^ T) (0, x₀) {z | C z.2 < D}
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) - integratedInvRateClock D q D) ^ 2)
            / (2 * (T : ℝ) * L ^ 2))) := by
  let Φ : ℕ × Ω → ℝ := stoppedClockPotential D q C
  let lam : ℝ := (T : ℝ) - integratedInvRateClock D q D
  have hΦ0 : Φ (0, x₀) = 0 := stoppedClockPotential_start D q C x₀ hC0
  have hlam : 0 < lam := by
    unfold lam
    linarith
  have hHD0 : 0 ≤ integratedInvRateClock D q D :=
    integratedInvRateClock_nonneg D q hqpos D
  have hTposR : (0 : ℝ) < T := by
    linarith
  have ht : 1 ≤ T := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.cast_pos.mp hTposR))
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hazuma :
      (clockKernel K C D ^ T) (0, x₀) {z | Φ (0, x₀) + lam ≤ Φ z}
        ≤ ENNReal.ofReal (Real.exp (-(lam ^ 2) / (2 * T * L ^ 2))) :=
    azuma_tail (clockKernel K C D) Φ Measurable.of_discrete L hLpos
      (stoppedClockPotential_bdd K C D q L hqpos hqle hL1 hLrate hstep)
      (stoppedClockPotential_drift K C D q hqpos hstep hsucc)
      T ht (0, x₀) hlam
  have hsupport :
      (clockKernel K C D ^ T) (0, x₀) {z | C z.2 < D ∧ z.1 ≠ T} = 0 :=
    clockKernel_active_time_support K C D x₀ T
  have hactive_subset :
      {z : ℕ × Ω | C z.2 < D} ⊆
        {z | Φ (0, x₀) + lam ≤ Φ z} ∪ {z | C z.2 < D ∧ z.1 ≠ T} := by
    intro z hz
    by_cases htime : z.1 = T
    · left
      have hcap_le :
          integratedInvRateClockCap D q (C z.2) ≤ integratedInvRateClock D q D :=
        integratedInvRateClockCap_le_target D q hqpos (C z.2)
      simp only [Set.mem_setOf_eq, hΦ0, zero_add, Φ, lam, stoppedClockPotential]
      rw [htime]
      linarith
    · right
      exact ⟨hz, htime⟩
  calc
    (clockKernel K C D ^ T) (0, x₀) {z | C z.2 < D}
        ≤ (clockKernel K C D ^ T) (0, x₀)
            ({z | Φ (0, x₀) + lam ≤ Φ z} ∪ {z | C z.2 < D ∧ z.1 ≠ T}) :=
          measure_mono hactive_subset
    _ ≤ (clockKernel K C D ^ T) (0, x₀) {z | Φ (0, x₀) + lam ≤ Φ z}
          + (clockKernel K C D ^ T) (0, x₀) {z | C z.2 < D ∧ z.1 ≠ T} :=
          measure_union_le _ _
    _ = (clockKernel K C D ^ T) (0, x₀) {z | Φ (0, x₀) + lam ≤ Φ z} := by
          rw [hsupport, add_zero]
    _ ≤ ENNReal.ofReal (Real.exp (-(lam ^ 2) / (2 * T * L ^ 2))) := hazuma
    _ = ENNReal.ofReal (Real.exp
          (-(((T : ℝ) - integratedInvRateClock D q D) ^ 2)
            / (2 * (T : ℝ) * L ^ 2))) := by
          unfold lam
          norm_num

/-- Core stopped-clock concentration for all `T ≥ H(D)`. -/
theorem cancelClock_concentration_augmented
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (C : Ω → ℕ) (D : ℕ) (q : Fin D → ℝ) (L : ℝ) (x₀ : Ω)
    (hC0 : C x₀ = 0)
    (hqpos : ∀ i, 0 < q i) (hqle : ∀ i, q i ≤ 1)
    (hL1 : 1 ≤ L) (hLrate : ∀ i : Fin D, (q i)⁻¹ - 1 ≤ L)
    (hstep : ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hsucc : ∀ x (hx : C x < D),
      q ⟨C x, hx⟩ ≤ (K x).real {y | C y = C x + 1})
    (T : ℕ) (hT : integratedInvRateClock D q D ≤ (T : ℝ)) :
    (clockKernel K C D ^ T) (0, x₀) {z | C z.2 < D}
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) - integratedInvRateClock D q D) ^ 2)
            / (2 * (T : ℝ) * L ^ 2))) := by
  by_cases hstrict : integratedInvRateClock D q D < (T : ℝ)
  · exact cancelClock_concentration_augmented_strict
      K C D q L x₀ hC0 hqpos hqle hL1 hLrate hstep hsucc T hstrict
  · have hle : (T : ℝ) ≤ integratedInvRateClock D q D := le_of_not_gt hstrict
    have hEq : (T : ℝ) - integratedInvRateClock D q D = 0 := by linarith
    haveI : IsMarkovKernel (clockKernel K C D ^ T) :=
      isMarkovKernel_pow (clockKernel K C D) T
    calc
      (clockKernel K C D ^ T) (0, x₀) {z | C z.2 < D}
          ≤ (clockKernel K C D ^ T) (0, x₀) Set.univ :=
            measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal (Real.exp
          (-(((T : ℝ) - integratedInvRateClock D q D) ^ 2)
            / (2 * (T : ℝ) * L ^ 2))) := by
            rw [hEq]
            simp

/-- Core stopped-kernel concentration on the original state space. -/
theorem cancelClock_concentration_stoppedKernel
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (C : Ω → ℕ) (D : ℕ) (q : Fin D → ℝ) (L : ℝ) (x₀ : Ω)
    (hC0 : C x₀ = 0)
    (hqpos : ∀ i, 0 < q i) (hqle : ∀ i, q i ≤ 1)
    (hL1 : 1 ≤ L) (hLrate : ∀ i : Fin D, (q i)⁻¹ - 1 ≤ L)
    (hstep : ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hsucc : ∀ x (hx : C x < D),
      q ⟨C x, hx⟩ ≤ (K x).real {y | C y = C x + 1})
    (T : ℕ) (hT : integratedInvRateClock D q D ≤ (T : ℝ)) :
    (stoppedKernel K C D ^ T) x₀ {x | C x < D}
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) - integratedInvRateClock D q D) ^ 2)
            / (2 * (T : ℝ) * L ^ 2))) := by
  have hproj :=
    clockKernel_project_snd K C D (activeSet C D)
      (DiscreteMeasurableSpace.forall_measurableSet _) 0 x₀ T
  have haug :=
    cancelClock_concentration_augmented K C D q L x₀ hC0 hqpos hqle
      hL1 hLrate hstep hsucc T hT
  change (stoppedKernel K C D ^ T) x₀ (activeSet C D)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) - integratedInvRateClock D q D) ^ 2)
            / (2 * (T : ℝ) * L ^ 2)))
  rw [← hproj]
  simpa [activeSet] using haug

/-- Canonical-`L` stopped-kernel concentration. -/
theorem cancelClock_concentration_stoppedKernel_canonicalL
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (C : Ω → ℕ) (D : ℕ) (q : Fin D → ℝ) (x₀ : Ω)
    (hC0 : C x₀ = 0)
    (hqpos : ∀ i, 0 < q i) (hqle : ∀ i, q i ≤ 1)
    (hstep : ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hsucc : ∀ x (hx : C x < D),
      q ⟨C x, hx⟩ ≤ (K x).real {y | C y = C x + 1})
    (T : ℕ) (hT : integratedInvRateClock D q D ≤ (T : ℝ)) :
    (stoppedKernel K C D ^ T) x₀ {x | C x < D}
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) - integratedInvRateClock D q D) ^ 2)
            / (2 * (T : ℝ) * (invRateSlack D q) ^ 2))) := by
  exact cancelClock_concentration_stoppedKernel K C D q (invRateSlack D q) x₀
    hC0 hqpos hqle (invRateSlack_ge_one D q) (invRateSlack_rate_le D q)
    hstep hsucc T hT

/-- Original-kernel concentration when the supplied kernel is already the
target-stopped kernel.  Without such a no-return/stopping condition, the
corresponding statement for arbitrary `K` is false: the chain may hit `D` and
then later return to `{C < D}`. -/
theorem cancelClock_concentration_kernel_of_stopped
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (C : Ω → ℕ) (D : ℕ) (q : Fin D → ℝ) (x₀ : Ω)
    (hstopped : stoppedKernel K C D = K)
    (hC0 : C x₀ = 0)
    (hqpos : ∀ i, 0 < q i) (hqle : ∀ i, q i ≤ 1)
    (hstep : ∀ x, C x < D → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hsucc : ∀ x (hx : C x < D),
      q ⟨C x, hx⟩ ≤ (K x).real {y | C y = C x + 1})
    (T : ℕ) (hT : integratedInvRateClock D q D ≤ (T : ℝ)) :
    (K ^ T) x₀ {x | C x < D}
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) - integratedInvRateClock D q D) ^ 2)
            / (2 * (T : ℝ) * (invRateSlack D q) ^ 2))) := by
  rw [← hstopped]
  exact cancelClock_concentration_stoppedKernel_canonicalL K C D q x₀
    hC0 hqpos hqle hstep hsucc T hT

end AugmentedKernel

/-! ## Two-sided count-floor instantiation -/

section TwoSided

/-- Two-sided ordered-pair cancellation probability floor. -/
noncomputable def twoSidedQ (A₀ B₀ n D : ℕ) : Fin D → ℝ :=
  fun i => (2 : ℝ) * ((A₀ - i.1 : ℕ) : ℝ) * ((B₀ - i.1 : ℕ) : ℝ)
    / ((n : ℝ) * (n - 1 : ℕ))

theorem twoSidedQ_pos {A₀ B₀ n D : ℕ}
    (hD : D < B₀) (hBA : B₀ ≤ A₀) (hn : 2 ≤ n) :
    ∀ i : Fin D, 0 < twoSidedQ A₀ B₀ n D i := by
  intro i
  have hiB : i.1 < B₀ := lt_trans i.2 hD
  have hiA : i.1 < A₀ := lt_of_lt_of_le hiB hBA
  have hAi : 0 < A₀ - i.1 := Nat.sub_pos_of_lt hiA
  have hBi : 0 < B₀ - i.1 := Nat.sub_pos_of_lt hiB
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hn1 : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hn)
  have hAiR : (0 : ℝ) < (A₀ - i.1 : ℕ) := by exact_mod_cast hAi
  have hBiR : (0 : ℝ) < (B₀ - i.1 : ℕ) := by exact_mod_cast hBi
  unfold twoSidedQ
  exact div_pos (mul_pos (mul_pos (by norm_num) hAiR) hBiR) (mul_pos hn0 hn1)

/-- Count floors plus an ordered-pair scheduling lower bound imply H3 for
`twoSidedQ`.  The hypotheses are deliberately protocol-free: `A` and `B` are
arbitrary state observables. -/
theorem twoSided_success_lower_bound
    (K : Kernel Ω Ω) (C A B : Ω → ℕ) (A₀ B₀ n D : ℕ)
    (hn : 2 ≤ n)
    (hAfloor : ∀ x (_ : C x < D), ((A₀ - C x : ℕ) : ℝ) ≤ A x)
    (hBfloor : ∀ x (_ : C x < D), ((B₀ - C x : ℕ) : ℝ) ≤ B x)
    (hpair : ∀ x (_ : C x < D),
      (2 * (A x : ℝ) * (B x : ℝ)) / ((n : ℝ) * (n - 1 : ℕ))
        ≤ (K x).real {y | C y = C x + 1}) :
    ∀ x (hx : C x < D),
      twoSidedQ A₀ B₀ n D ⟨C x, hx⟩
        ≤ (K x).real {y | C y = C x + 1} := by
  intro x hx
  have hden_pos : (0 : ℝ) < (n : ℝ) * (n - 1 : ℕ) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
    have hn1 : (0 : ℝ) < (n - 1 : ℕ) := by
      exact_mod_cast (Nat.sub_pos_of_lt hn)
    positivity
  have hA0 : 0 ≤ ((A₀ - C x : ℕ) : ℝ) := by positivity
  have hB0 : 0 ≤ ((B₀ - C x : ℕ) : ℝ) := by positivity
  have hA : 0 ≤ (A x : ℝ) := by positivity
  have hB : 0 ≤ (B x : ℝ) := by positivity
  have hnum :
      2 * ((A₀ - C x : ℕ) : ℝ) * ((B₀ - C x : ℕ) : ℝ)
        ≤ 2 * (A x : ℝ) * (B x : ℝ) := by
    nlinarith [hAfloor x hx, hBfloor x hx, hA0, hB0, hA, hB]
  simpa [twoSidedQ] using
    (div_le_div_of_nonneg_right hnum hden_pos.le).trans (hpair x hx)

set_option linter.flexible false in
/-- If all per-level success probabilities are bounded below by `ρ`, then the
integrated inverse-rate clock is at most `D/ρ`.  This is the formal constant-
fraction clock estimate used when `ρ = Θ(1)`. -/
theorem integratedInvRateClock_le_div_of_uniform_lower
    (D : ℕ) (q : Fin D → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hq : ∀ i : Fin D, ρ ≤ q i) :
    integratedInvRateClock D q D ≤ (D : ℝ) / ρ := by
  unfold integratedInvRateClock
  calc
    ∑ i ∈ Finset.range D, (if hi : i < D then (q ⟨i, hi⟩)⁻¹ else 0)
        ≤ ∑ _i ∈ Finset.range D, ρ⁻¹ := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have hiD : i < D := Finset.mem_range.mp hi
          simp [hiD]
          exact inv_anti₀ hρ (hq ⟨i, hiD⟩)
    _ = (D : ℝ) / ρ := by
          rw [Finset.sum_const, Finset.card_range]
          ring

/-- Uniform lower bound on `q` gives a uniform upper bound on the canonical
increment scale `L`. -/
theorem invRateSlack_le_of_uniform_lower
    (D : ℕ) (q : Fin D → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hq : ∀ i : Fin D, ρ ≤ q i) :
    invRateSlack D q ≤ max 1 (ρ⁻¹ - 1) := by
  rw [invRateSlack]
  refine (Finset.fold_max_le (s := Finset.range D)
    (b := (1 : ℝ))
    (f := fun i => if hi : i < D then (q ⟨i, hi⟩)⁻¹ - 1 else 0)
    (max 1 (ρ⁻¹ - 1))).2 ?_
  constructor
  · exact le_max_left _ _
  · intro i hi
    have hiD : i < D := Finset.mem_range.mp hi
    rw [dif_pos hiD]
    exact (sub_le_sub_right (inv_anti₀ hρ (hq ⟨i, hiD⟩)) (1 : ℝ)).trans
      (le_max_right _ _)

end TwoSided

end CancelClockConcentration
end ExactMajority
