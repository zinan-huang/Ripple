import Ripple.Analysis.BochnerSquareIntegrable
import Ripple.Kurtz.StrongApprox.WienerIntegralPathBridge

/-!
# Moving time cutoffs in one deterministic L² space

The coefficient is continuous and uniformly bounded; the moving cutoff is
discontinuous only on a null time slice. Dominated convergence therefore
gives continuity in L², and hence Bochner integrability on compact intervals.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace Ripple.Analysis.MovingTriangleKernel

variable {T : ℝ≥0} {q : ℝ → ℝ → ℝ} {C : ℝ}

/-- The common-horizon kernel, with zero padding past the observation time. -/
def slice (q : ℝ → ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  (Ioc (0 : ℝ) t).indicator (q t)

theorem measurable_slice (hq : Continuous (Function.uncurry q)) (t : ℝ) :
    Measurable (slice q t) :=
  (hq.comp (continuous_const.prodMk continuous_id)).measurable.indicator measurableSet_Ioc

theorem measurable_uncurry_slice (hq : Continuous (Function.uncurry q)) :
    Measurable (Function.uncurry (slice q)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  convert hq.measurable.indicator hs using 1

theorem abs_slice_le (hC : 0 ≤ C) (hb : ∀ t s, |q t s| ≤ C) (t s : ℝ) :
    |slice q t s| ≤ C := by
  by_cases hs : s ∈ Ioc (0 : ℝ) t
  · simpa only [slice, indicator_of_mem hs] using hb t s
  · simp only [slice, indicator_of_notMem hs, abs_zero]
    exact hC

theorem memLp_slice (hq : Continuous (Function.uncurry q))
    (hC : 0 ≤ C) (hb : ∀ t s, |q t s| ≤ C) (t : ℝ) :
    MemLp (slice q t) 2 (volume.restrict (Ioc (0 : ℝ) T)) := by
  apply MemLp.of_bound (measurable_slice hq t).aestronglyMeasurable C
  exact ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using abs_slice_le hC hb t s

/-- All observation times use the same Hilbert space. -/
def sliceLp (T : ℝ≥0) (hq : Continuous (Function.uncurry q))
    (hC : 0 ≤ C) (hb : ∀ t s, |q t s| ≤ C) (t : ℝ) :
    Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) T)) :=
  (memLp_slice hq hC hb t).toLp (slice q t)

theorem sliceLp_ae (hq : Continuous (Function.uncurry q))
    (hC : 0 ≤ C) (hb : ∀ t s, |q t s| ≤ C) (t : ℝ) :
    (sliceLp T hq hC hb t : ℝ → ℝ) =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] slice q t :=
  (memLp_slice hq hC hb t).coeFn_toLp

/-- For a fixed integration time, only the diagonal can obstruct continuity
in the observation time. This diagonal has zero Lebesgue measure. -/
theorem continuousAt_slice_of_ne (hq : Continuous (Function.uncurry q))
    {t s : ℝ} (hne : s ≠ t) : ContinuousAt (fun r => slice q r s) t := by
  by_cases hs : 0 < s
  · rcases lt_or_gt_of_ne hne with hst | hts
    · have heq : (fun r => slice q r s) =ᶠ[𝓝 t] fun r => q r s := by
        filter_upwards [isOpen_Ioi.mem_nhds hst] with r hr
        exact indicator_of_mem (show s ∈ Ioc (0 : ℝ) r from ⟨hs, hr.le⟩) _
      exact ((hq.comp (continuous_id.prodMk continuous_const)).continuousAt).congr heq.symm
    · have heq : (fun r => slice q r s) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hts] with r hr
        exact indicator_of_notMem (by exact fun h => (not_le_of_gt hr) h.2) _
      exact continuousAt_const.congr heq.symm
  · have hz : (fun r => slice q r s) = fun _ => (0 : ℝ) := by
      funext r
      exact indicator_of_notMem (fun h => hs h.1) _
    rw [hz]
    exact continuousAt_const

/-- The moving-cutoff path is continuous as a path of L² equivalence classes. -/
theorem continuous_sliceLp (hq : Continuous (Function.uncurry q))
    (hC : 0 ≤ C) (hb : ∀ t s, |q t s| ≤ C) :
    Continuous (sliceLp T hq hC hb) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact BochnerSquareIntegrable.tendsto_toLp_of_dominated
    (fun r => memLp_slice hq hC hb r) (memLp_slice hq hC hb t)
    (memLp_const C)
    (Eventually.of_forall fun r => ae_of_all _ (abs_slice_le hC hb r))
    (ae_of_all _ (abs_slice_le hC hb t))
    ((ae_restrict_of_ae (by rw [ae_iff]; simp) :
        ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) T)), s ≠ t).mono
      fun s hst => (continuousAt_slice_of_ne hq hst).tendsto)

/-- This is the L²-valued integrability needed by Wiener/Bochner commutation. -/
theorem intervalIntegrable_sliceLp (hq : Continuous (Function.uncurry q))
    (hC : 0 ≤ C) (hb : ∀ t s, |q t s| ≤ C) (a b : ℝ) :
    IntervalIntegrable (sliceLp T hq hC hb) volume a b :=
  (continuous_sliceLp hq hC hb).intervalIntegrable a b

/-- Integrating a moving cutoff gives the integral over the forward triangle.
The distinction between the closed and half-open lower endpoint is null. -/
theorem integral_slice (hq : Continuous (Function.uncurry q))
    {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, slice q r s) =
      if s ≤ t then ∫ r in s..t, q r s else 0 := by
  rw [intervalIntegral.integral_of_le ht]
  by_cases hst : s ≤ t
  · rw [if_pos hst]
    have heq : (fun r => slice q r s) = (Ici s).indicator (fun r => q r s) := by
      funext r
      simp only [slice, indicator, mem_Ioc, mem_Ici, hs, true_and]
    rw [heq, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici s ∩ Ioc 0 t = Icc s t := by
      ext r
      constructor
      · intro h
        exact ⟨h.1, h.2.2⟩
      · intro h
        exact ⟨h.1, hs.trans_le h.1, h.2⟩
    rw [hset, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hst]
  · rw [if_neg hst]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact indicator_of_notMem (fun h => hst (h.2.trans hr.2)) _

/-- The deterministic Volterra identity in the common L² space. Joint scalar
integrability and Bochner integrability are consequences of the stated bounds;
they are not additional hypotheses on the moving triangle. -/
theorem sliceLp_integral_eq
    {p : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {Cp Cg : ℝ}
    (hq : Continuous (Function.uncurry q))
    (hC : 0 ≤ C) (hb : ∀ t s, |q t s| ≤ C)
    (hp : Continuous (Function.uncurry p))
    (hCp : 0 ≤ Cp) (hpb : ∀ t s, |p t s| ≤ Cp)
    (hg : Continuous g) (hCg : 0 ≤ Cg) (hgb : ∀ s, |g s| ≤ Cg)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (heq : ∀ s ∈ Icc 0 t, q t s = g s + ∫ r in s..t, p r s) :
    sliceLp T hq hC hb t =
      sliceLp T (q := fun _ s => g s) (hg.comp continuous_snd) hCg (fun _ => hgb) t +
        ∫ r in (0 : ℝ)..t, sliceLp T hp hCp hpb r := by
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  let μ := volume.restrict (Ioc (0 : ℝ) (T : ℝ))
  letI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    dsimp only [ν]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  let y : Lp ℝ 2 μ := sliceLp T hq hC hb t -
    sliceLp T (q := fun _ s => g s) (hg.comp continuous_snd) hCg (fun _ => hgb) t
  have hi : (∫ r, sliceLp T hp hCp hpb r ∂ν) = y := by
    apply BochnerSquareIntegrable.integral_eq_of_representative
      ((intervalIntegrable_sliceLp hp hCp hpb 0 t).1)
      (ae_of_all _ fun r => sliceLp_ae hp hCp hpb r)
    · filter_upwards [Lp.coeFn_sub (sliceLp T hq hC hb t)
          (sliceLp T (q := fun _ s => g s) (hg.comp continuous_snd) hCg (fun _ => hgb) t),
        sliceLp_ae hq hC hb t,
        sliceLp_ae (q := fun _ s => g s) (hg.comp continuous_snd) hCg (fun _ => hgb) t,
        ae_restrict_mem measurableSet_Ioc] with s hsub hq' hg' hs
      change y s = _
      change 0 < s ∧ s ≤ (T : ℝ) at hs
      change (_ - _ : Lp ℝ 2 μ) s = _ at hsub
      rw [hsub, Pi.sub_apply, hq', hg']
      change slice q t s - (Ioc (0 : ℝ) t).indicator g s =
        ∫ r in Ioc (0 : ℝ) t, slice p r s
      rw [← intervalIntegral.integral_of_le ht.1, integral_slice hp hs.1 ht.1]
      by_cases hst : s ≤ t
      · rw [if_pos hst, slice, indicator_of_mem (show s ∈ Ioc (0 : ℝ) t from ⟨hs.1, hst⟩),
          indicator_of_mem (show s ∈ Ioc (0 : ℝ) t from ⟨hs.1, hst⟩), heq s ⟨hs.1.le, hst⟩]
        ring
      · rw [if_neg hst, slice,
          indicator_of_notMem (fun h => hst h.2),
          indicator_of_notMem (fun h => hst h.2), sub_self]
    · intro z
      apply BochnerSquareIntegrable.integrable_test_product
        (measurable_uncurry_slice hp).aestronglyMeasurable
        (memLp_const Cp)
      exact ae_of_all _ fun z =>
        (abs_slice_le hCp hpb z.1 z.2).trans (le_abs_self Cp)
  rw [intervalIntegral.integral_of_le ht.1]
  change _ = _ + ∫ r, sliceLp T hp hCp hpb r ∂ν
  rw [hi]
  dsimp only [y]
  abel

end Ripple.Analysis.MovingTriangleKernel
