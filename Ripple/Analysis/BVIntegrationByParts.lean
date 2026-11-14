import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
The deterministic integration-by-parts functional for a Lipschitz coefficient.
The construction uses the Lebesgue integral of the ordinary derivative. Its
integrability follows from measurability and the interior Lipschitz bound;
endpoint values of the derivative do not affect the integral.
-/

open Set MeasureTheory Filter
open scoped Interval NNReal

namespace Ripple.Analysis.BVIntegrationByParts

/-- The pathwise integral, with the initial boundary term omitted. For paths
starting at zero this is the usual integration-by-parts expression. -/
noncomputable def J (a w : ℝ → ℝ) (t : ℝ) : ℝ :=
  a t * w t - ∫ s in 0..t, w s * deriv a s

/-- A Lipschitz coefficient has an integrable ordinary derivative, including
when its values outside the closed interval are arbitrary. -/
theorem intervalIntegrable_deriv {a : ℝ → ℝ} {T : ℝ} {K : ℝ≥0}
    (hT : 0 ≤ T) (ha : LipschitzOnWith K a (Icc 0 T)) :
    IntervalIntegrable (deriv a) volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).2
  refine (integrable_const (μ := volume.restrict (Ioo 0 T)) (K : ℝ)).mono'
    (aestronglyMeasurable_deriv a _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hs.1 hs.2) ha

/-- Continuous paths can multiply the derivative inside the interval integral. -/
theorem intervalIntegrable_integrand {a w : ℝ → ℝ} {T : ℝ} {K : ℝ≥0}
    (hT : 0 ≤ T) (ha : LipschitzOnWith K a (Icc 0 T))
    (hw : ContinuousOn w (Icc 0 T)) :
    IntervalIntegrable (fun s => w s * deriv a s) volume 0 T := by
  apply (intervalIntegrable_deriv hT ha).continuousOn_mul
  simpa only [uIcc_of_le hT] using hw

/-- The functional has continuous paths on the same closed interval. -/
theorem continuousOn_J {a w : ℝ → ℝ} {T : ℝ} {K : ℝ≥0}
    (hT : 0 ≤ T) (ha : LipschitzOnWith K a (Icc 0 T))
    (hw : ContinuousOn w (Icc 0 T)) :
    ContinuousOn (J a w) (Icc 0 T) := by
  have hi := intervalIntegrable_integrand hT ha hw
  have hc : ContinuousOn (fun t => ∫ s in 0..t, w s * deriv a s) (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using
      (intervalIntegral.continuousOn_primitive_interval' hi
        (left_mem_uIcc : (0 : ℝ) ∈ [[0, T]]))
  exact (ha.continuousOn.mul hw).sub hc

@[simp] theorem J_zero_path (a : ℝ → ℝ) (t : ℝ) : J a (fun _ => 0) t = 0 := by
  simp [J]

@[simp] theorem J_zero_time (a w : ℝ → ℝ) : J a w 0 = a 0 * w 0 := by
  simp [J]

theorem J_zero_time_of_initial {a w : ℝ → ℝ} (hw : w 0 = 0) : J a w 0 = 0 := by
  simp [hw]

/-- Additivity in the continuous driving path. -/
theorem J_add {a w v : ℝ → ℝ} {t : ℝ} {K : ℝ≥0}
    (ht : 0 ≤ t) (ha : LipschitzOnWith K a (Icc 0 t))
    (hw : ContinuousOn w (Icc 0 t)) (hv : ContinuousOn v (Icc 0 t)) :
    J a (fun s => w s + v s) t = J a w t + J a v t := by
  simp only [J, add_mul, intervalIntegral.integral_add
    (intervalIntegrable_integrand ht ha hw) (intervalIntegrable_integrand ht ha hv)]
  ring

/-- Scalar linearity requires no additional regularity of the path. -/
theorem J_const_mul (a w : ℝ → ℝ) (c t : ℝ) :
    J a (fun s => c * w s) t = c * J a w t := by
  simp only [J, mul_assoc, intervalIntegral.integral_const_mul]
  ring

/-- Subtraction in the continuous driving path. -/
theorem J_sub {a w v : ℝ → ℝ} {t : ℝ} {K : ℝ≥0}
    (ht : 0 ≤ t) (ha : LipschitzOnWith K a (Icc 0 t))
    (hw : ContinuousOn w (Icc 0 t)) (hv : ContinuousOn v (Icc 0 t)) :
    J a (fun s => w s - v s) t = J a w t - J a v t := by
  simp only [J, sub_mul, intervalIntegral.integral_sub
    (intervalIntegrable_integrand ht ha hw) (intervalIntegrable_integrand ht ha hv)]
  ring

/-- A uniform bound on the integrand yields an explicit integral bound.
Only the endpoint at `t` needs to be removed from the half-open integral domain. -/
theorem abs_integral_mul_deriv_le {a w : ℝ → ℝ} {t M : ℝ} {K : ℝ≥0}
    (ht : 0 ≤ t) (ha : LipschitzOnWith K a (Icc 0 t))
    (hM : 0 ≤ M) (hw : ∀ s ∈ Icc 0 t, |w s| ≤ M) :
    |∫ s in 0..t, w s * deriv a s| ≤ M * (K : ℝ) * t := by
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := ae_iff.mpr (by simp)
  have hb : ∀ᵐ s : ℝ ∂volume, s ∈ Ι (0 : ℝ) t →
      ‖w s * deriv a s‖ ≤ M * (K : ℝ) := by
    filter_upwards [hne] with s hst hs
    have hs' : s ∈ Ioc 0 t := by simpa only [uIoc_of_le ht] using hs
    have hd : ‖deriv a s‖ ≤ (K : ℝ) :=
      norm_deriv_le_of_lipschitzOn
        (Icc_mem_nhds hs'.1 (lt_of_le_of_ne hs'.2 hst)) ha
    rw [norm_mul, Real.norm_eq_abs (w s)]
    exact mul_le_mul (hw s ⟨hs'.1.le, hs'.2⟩) hd (norm_nonneg _) hM
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hb

/-- Operator bound with an arbitrary bound for the uniform distance of paths. -/
theorem abs_J_sub_le {a w v : ℝ → ℝ} {t M : ℝ} {K : ℝ≥0}
    (ht : 0 ≤ t) (ha : LipschitzOnWith K a (Icc 0 t))
    (hw : ContinuousOn w (Icc 0 t)) (hv : ContinuousOn v (Icc 0 t))
    (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc 0 t, |w s - v s| ≤ M) :
    |J a w t - J a v t| ≤ (|a t| + (K : ℝ) * t) * M := by
  have hi := abs_integral_mul_deriv_le ht ha hM hbound
  calc
    |J a w t - J a v t| =
        |a t * (w t - v t) - ∫ s in 0..t, (w s - v s) * deriv a s| := by
      rw [← J_sub ht ha hw hv]
      rfl
    _ ≤ |a t| * |w t - v t| + |∫ s in 0..t, (w s - v s) * deriv a s| := by
      simpa only [Real.norm_eq_abs, abs_mul] using
        norm_sub_le (a t * (w t - v t)) (∫ s in 0..t, (w s - v s) * deriv a s)
    _ ≤ |a t| * M + M * (K : ℝ) * t :=
      add_le_add (mul_le_mul_of_nonneg_left (hbound t ⟨ht, le_rfl⟩) (abs_nonneg _)) hi
    _ = (|a t| + (K : ℝ) * t) * M := by ring

/-- The supremum version of the pathwise Lipschitz estimate. -/
theorem abs_J_sub_le_sup {a w v : ℝ → ℝ} {t : ℝ} {K : ℝ≥0}
    (ht : 0 ≤ t) (ha : LipschitzOnWith K a (Icc 0 t))
    (hw : ContinuousOn w (Icc 0 t)) (hv : ContinuousOn v (Icc 0 t)) :
    |J a w t - J a v t| ≤ (|a t| + (K : ℝ) * t) *
      sSup ((fun s => |w s - v s|) '' Icc 0 t) := by
  have hb : BddAbove ((fun s => |w s - v s|) '' Icc 0 t) :=
    (isCompact_Icc.image_of_continuousOn (hw.sub hv).abs).bddAbove
  have hbound : ∀ s ∈ Icc 0 t,
      |w s - v s| ≤ sSup ((fun r => |w r - v r|) '' Icc 0 t) := by
    intro s hs
    exact le_csSup hb (mem_image_of_mem _ hs)
  have hM : 0 ≤ sSup ((fun r => |w r - v r|) '' Icc 0 t) :=
    (abs_nonneg (w 0 - v 0)).trans (hbound 0 ⟨le_rfl, ht⟩)
  exact abs_J_sub_le ht ha hw hv hM hbound

/-- The supremum estimate at every time in a prescribed coefficient interval. -/
theorem abs_J_sub_le_sup_of_mem {a w v : ℝ → ℝ} {T t : ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 T))
    (hw : ContinuousOn w (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (ht : t ∈ Icc 0 T) :
    |J a w t - J a v t| ≤ (|a t| + (K : ℝ) * t) *
      sSup ((fun s => |w s - v s|) '' Icc 0 t) := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T :=
    fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  exact abs_J_sub_le_sup ht.1 (ha.mono hsub) (hw.mono hsub) (hv.mono hsub)

end Ripple.Analysis.BVIntegrationByParts
