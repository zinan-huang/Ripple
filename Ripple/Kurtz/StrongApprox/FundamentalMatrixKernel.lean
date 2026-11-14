import Ripple.Kurtz.StrongApprox.FundamentalMatrixRegularity
import Ripple.Analysis.MovingTriangleKernel

/-!
# Bounded scalar kernels from the actual fundamental evolution

The common-horizon kernel is extended continuously to all real time pairs by
clamping both times and moving the end time above the initial time. A second
extension holds the observation time fixed and clamps the initial time below
it. Both extensions agree with the actual kernel on its integration triangle.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology NNReal

namespace Ripple.Kurtz.StrongApprox.VolterraGaussian.FundamentalKernel

variable {d : ℕ}

/-- Projection to the common compact time horizon. -/
def clamp (T : ℝ≥0) (s : ℝ) : ℝ := max 0 (min (T : ℝ) s)

theorem clamp_mem (T : ℝ≥0) (s : ℝ) : clamp T s ∈ Icc (0 : ℝ) (T : ℝ) :=
  ⟨le_max_left _ _, max_le T.coe_nonneg (min_le_left _ _)⟩

@[simp] theorem clamp_of_mem {T : ℝ≥0} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (T : ℝ)) :
    clamp T s = s := by
  simp only [clamp, min_eq_right hs.2, max_eq_right hs.1]

theorem lipschitzWith_clamp (T : ℝ≥0) : LipschitzWith 1 (clamp T) := by
  exact (LipschitzWith.id.const_min (T : ℝ)).const_max 0

@[fun_prop] theorem continuous_clamp (T : ℝ≥0) : Continuous (clamp T) :=
  (lipschitzWith_clamp T).continuous

/-- The amplitude bound supplied by its time-Lipschitz constant. -/
def amplitudeBound (T : ℝ≥0) (a : ℝ → ℝ) (Ka : ℝ≥0) : ℝ :=
  |a 0| + (Ka : ℝ) * (T : ℝ)

theorem amplitudeBound_nonneg (T : ℝ≥0) (a : ℝ → ℝ) (Ka : ℝ≥0) :
    0 ≤ amplitudeBound T a Ka := by
  unfold amplitudeBound
  positivity

theorem abs_amplitude_le {T : ℝ≥0} {a : ℝ → ℝ} {Ka : ℝ≥0}
    (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (T : ℝ)) :
    |a s| ≤ amplitudeBound T a Ka := by
  have hdiff := ha.dist_le_mul s hs 0 ⟨le_rfl, T.coe_nonneg⟩
  rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hs.1] at hdiff
  have hmul := mul_le_mul_of_nonneg_left hs.2 Ka.coe_nonneg
  have habs : |a s| ≤ |a s - a 0| + |a 0| := by
    simpa only [sub_add_cancel] using abs_add_le (a s - a 0) (a 0)
  dsimp [amplitudeBound]
  linarith

/-- The globally bounded common-horizon kernel before inserting its cutoff. -/
def q (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (T : ℝ≥0) (a : ℝ → ℝ) (v : Fin d → ℝ) (i : Fin d) (t s : ℝ) : ℝ :=
  a (clamp T s) *
    (fundamentalCLM A T (max (clamp T t) (clamp T s)) (clamp T s) v) i

/-- A uniform bound valid at every extended time pair. -/
def bound (T : ℝ≥0) (a : ℝ → ℝ) (Ka K : ℝ≥0) (v : Fin d → ℝ) : ℝ :=
  amplitudeBound T a Ka * Real.exp ((K : ℝ) * (T : ℝ)) * ‖v‖

theorem bound_nonneg (T : ℝ≥0) (a : ℝ → ℝ) (Ka K : ℝ≥0) (v : Fin d → ℝ) :
    0 ≤ bound T a Ka K v := by
  unfold bound
  exact mul_nonneg (mul_nonneg (amplitudeBound_nonneg T a Ka) (Real.exp_nonneg _))
    (norm_nonneg _)

/-- Clamping puts every time pair inside the true evolution triangle. -/
theorem continuous_q
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ}
    (hA : Continuous A) (hc : Continuous a) (v : Fin d → ℝ) (i : Fin d) :
    Continuous (Function.uncurry (q A T a v i)) := by
  have ht : Continuous (fun p : ℝ × ℝ => clamp T p.1) :=
    (continuous_clamp T).comp continuous_fst
  have hs : Continuous (fun p : ℝ × ℝ => clamp T p.2) :=
    (continuous_clamp T).comp continuous_snd
  have hPhi : Continuous (fun p : ℝ × ℝ =>
      fundamentalCLM A T (max (clamp T p.1) (clamp T p.2)) (clamp T p.2)) := by
    apply (continuousOn_fundamentalCLM_triangle_of_continuous hA).comp_continuous
      ((ht.max hs).prodMk hs)
    intro p
    exact ⟨(clamp_mem T p.2).1, le_max_right _ _,
      max_le (clamp_mem T p.1).2 (clamp_mem T p.2).2⟩
  exact (hc.comp hs).mul ((continuous_apply i).comp (hPhi.clm_apply continuous_const))

/-- Coordinate evaluation does not enlarge the sup norm of a vector. -/
theorem abs_evolution_apply_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    {s t : ℝ} (hs : 0 ≤ s) (ht : t ∈ Icc s (T : ℝ))
    (v : Fin d → ℝ) (i : Fin d) :
    |(fundamentalCLM A T t s v) i| ≤ Real.exp ((K : ℝ) * (T : ℝ)) * ‖v‖ := by
  calc
    |(fundamentalCLM A T t s v) i| ≤ ‖fundamentalCLM A T t s v‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fundamentalCLM A T t s v) i
    _ ≤ ‖fundamentalCLM A T t s‖ * ‖v‖ := (fundamentalCLM A T t s).le_opNorm v
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (norm_fundamentalCLM_le_uniform hA hAb hs ht) (norm_nonneg v)

theorem abs_q_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (v : Fin d → ℝ) (i : Fin d) (t s : ℝ) :
    |q A T a v i t s| ≤ bound T a Ka K v := by
  have hs := clamp_mem T s
  have ht := clamp_mem T t
  rw [q, abs_mul]
  calc
    _ ≤ amplitudeBound T a Ka * (Real.exp ((K : ℝ) * (T : ℝ)) * ‖v‖) :=
      mul_le_mul (abs_amplitude_le ha hs)
        (abs_evolution_apply_le hA hAb hs.1
          ⟨le_max_right _ _, max_le ht.2 hs.2⟩ v i)
        (abs_nonneg _) (amplitudeBound_nonneg T a Ka)
    _ = _ := by unfold bound; ring

/-- On the integration triangle the extension equals the actual kernel. -/
theorem q_of_mem
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0}
    {a : ℝ → ℝ} {v : Fin d → ℝ} {i : Fin d} {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (hs : s ∈ Icc (0 : ℝ) t) :
    q A T a v i t s = a s * (fundamentalCLM A T t s v) i := by
  simp only [q, clamp_of_mem ht, clamp_of_mem ⟨hs.1, hs.2.trans ht.2⟩,
    max_eq_left hs.2]

/-- A fixed-time extension, continuous even beyond the observation time. -/
def qFixed (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (T : ℝ≥0) (a : ℝ → ℝ) (v : Fin d → ℝ) (i : Fin d) (t s : ℝ) : ℝ :=
  a (clamp T s) * (fundamentalCLM A T t (min (clamp T s) t) v) i

theorem fixedStart_mem {T : ℝ≥0} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (s : ℝ) :
    min (clamp T s) t ∈ Icc (0 : ℝ) t :=
  ⟨le_min (clamp_mem T s).1 ht.1, min_le_right _ _⟩

theorem continuous_qFixed
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {t : ℝ}
    (hA : Continuous A) (hc : Continuous a) (ht : t ∈ Icc (0 : ℝ) (T : ℝ))
    (v : Fin d → ℝ) (i : Fin d) : Continuous (qFixed A T a v i t) := by
  have hPhi : Continuous (fun s => fundamentalCLM A T t (min (clamp T s) t)) :=
    (continuousOn_fundamentalCLM_start_of_continuous hA ht.2).comp_continuous
      ((continuous_clamp T).min continuous_const) (fixedStart_mem ht)
  exact (hc.comp (continuous_clamp T)).mul
    ((continuous_apply i).comp (hPhi.clm_apply continuous_const))

theorem qFixed_of_mem
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0}
    {a : ℝ → ℝ} {v : Fin d → ℝ} {i : Fin d} {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (hs : s ∈ Icc (0 : ℝ) t) :
    qFixed A T a v i t s = a s * (fundamentalCLM A T t s v) i := by
  simp only [qFixed, clamp_of_mem ⟨hs.1, hs.2.trans ht.2⟩, min_eq_left hs.2]

theorem q_eq_qFixed_of_mem
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0}
    {a : ℝ → ℝ} {v : Fin d → ℝ} {i : Fin d} {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (hs : s ∈ Icc (0 : ℝ) t) :
    q A T a v i t s = qFixed A T a v i t s := by
  rw [q_of_mem ht hs, qFixed_of_mem ht hs]

theorem abs_qFixed_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {t : ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (v : Fin d → ℝ) (i : Fin d) (s : ℝ) :
    |qFixed A T a v i t s| ≤ bound T a Ka K v := by
  have hs := fixedStart_mem ht s
  rw [qFixed, abs_mul]
  calc
    _ ≤ amplitudeBound T a Ka * (Real.exp ((K : ℝ) * (T : ℝ)) * ‖v‖) :=
      mul_le_mul (abs_amplitude_le ha (clamp_mem T s))
        (abs_evolution_apply_le hA hAb hs.1 ⟨hs.2, ht.2⟩ v i)
        (abs_nonneg _) (amplitudeBound_nonneg T a Ka)
    _ = _ := by unfold bound; ring

/-- Explicit global Lipschitz constant of the fixed-time scalar coefficient. -/
def fixedLipschitzConstant (T : ℝ≥0) (a : ℝ → ℝ) (Ka K : ℝ≥0) (v : Fin d → ℝ) : ℝ≥0 :=
  ⟨(Ka : ℝ) * Real.exp ((K : ℝ) * (T : ℝ)) * ‖v‖ +
      amplitudeBound T a Ka *
        (((K : ℝ) * Real.exp ((K : ℝ) * (T : ℝ))) * Real.exp ((K : ℝ) * (T : ℝ))) * ‖v‖,
    by
      have h := amplitudeBound_nonneg T a Ka
      positivity⟩

/-- The amplitude remains Lipschitz after clamping, even if the original
amplitude is only controlled on the compact time interval. -/
theorem lipschitzWith_amplitude_clamp {T : ℝ≥0} {a : ℝ → ℝ} {Ka : ℝ≥0}
    (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ))) :
    LipschitzWith Ka (fun s => a (clamp T s)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s r
  exact (ha.dist_le_mul _ (clamp_mem T s) _ (clamp_mem T r)).trans
    (mul_le_mul_of_nonneg_left (by simpa using (lipschitzWith_clamp T).dist_le_mul s r)
      Ka.coe_nonneg)

/-- A global Lipschitz extension of the fixed-observation coefficient. -/
theorem lipschitzWith_qFixed
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {t : ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (v : Fin d → ℝ) (i : Fin d) :
    LipschitzWith (fixedLipschitzConstant T a Ka K v) (qFixed A T a v i t) := by
  let E : ℝ := Real.exp ((K : ℝ) * (T : ℝ))
  let D : ℝ := ((K : ℝ) * E) * E
  let z : ℝ → ℝ := fun s => (fundamentalCLM A T t (min (clamp T s) t) v) i
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hzbound (s : ℝ) : |z s| ≤ E * ‖v‖ := by
    have hs := fixedStart_mem ht s
    exact abs_evolution_apply_le hA hAb hs.1 ⟨hs.2, ht.2⟩ v i
  have hzlip (s r : ℝ) : |z s - z r| ≤ (D * ‖v‖) * |s - r| := by
    have hstart := norm_fundamentalCLM_start_sub_le hA hAb ht.2
      (fixedStart_mem ht s) (fixedStart_mem ht r)
    have hmin : |min (clamp T s) t - min (clamp T r) t| ≤ |s - r| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        ((lipschitzWith_clamp T).min_const t).dist_le_mul s r
    calc
      |z s - z r| ≤ ‖(fundamentalCLM A T t (min (clamp T s) t) -
          fundamentalCLM A T t (min (clamp T r) t)) v‖ := by
        simpa only [z, ContinuousLinearMap.sub_apply, Pi.sub_apply, Real.norm_eq_abs] using
          norm_le_pi_norm ((fundamentalCLM A T t (min (clamp T s) t) -
            fundamentalCLM A T t (min (clamp T r) t)) v) i
      _ ≤ ‖fundamentalCLM A T t (min (clamp T s) t) -
          fundamentalCLM A T t (min (clamp T r) t)‖ * ‖v‖ :=
        (fundamentalCLM A T t (min (clamp T s) t) -
          fundamentalCLM A T t (min (clamp T r) t)).le_opNorm v
      _ ≤ (D * |min (clamp T s) t - min (clamp T r) t|) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hstart (norm_nonneg v)
      _ ≤ (D * |s - r|) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hD) (norm_nonneg v)
      _ = _ := by ring
  apply LipschitzWith.of_dist_le_mul
  intro s r
  have haDiff : |a (clamp T s) - a (clamp T r)| ≤ (Ka : ℝ) * |s - r| := by
    simpa only [Real.dist_eq] using (lipschitzWith_amplitude_clamp ha).dist_le_mul s r
  have hprod : qFixed A T a v i t s - qFixed A T a v i t r =
      (a (clamp T s) - a (clamp T r)) * z s + a (clamp T r) * (z s - z r) := by
    dsimp [qFixed, z]
    ring
  rw [Real.dist_eq, Real.dist_eq, hprod]
  calc
    _ ≤ |(a (clamp T s) - a (clamp T r)) * z s| +
        |a (clamp T r) * (z s - z r)| := abs_add_le _ _
    _ = |a (clamp T s) - a (clamp T r)| * |z s| +
        |a (clamp T r)| * |z s - z r| := by rw [abs_mul, abs_mul]
    _ ≤ ((Ka : ℝ) * |s - r|) * (E * ‖v‖) +
        amplitudeBound T a Ka * ((D * ‖v‖) * |s - r|) :=
      add_le_add
        (mul_le_mul haDiff (hzbound s) (abs_nonneg _) (mul_nonneg Ka.coe_nonneg (abs_nonneg _)))
        (mul_le_mul (abs_amplitude_le ha (clamp_mem T r)) (hzlip s r)
          (abs_nonneg _) (amplitudeBound_nonneg T a Ka))
    _ = _ := by
      rw [show ((fixedLipschitzConstant T a Ka K v : ℝ≥0) : ℝ) =
          (Ka : ℝ) * Real.exp ((K : ℝ) * (T : ℝ)) * ‖v‖ +
            amplitudeBound T a Ka *
              (((K : ℝ) * Real.exp ((K : ℝ) * (T : ℝ))) * Real.exp ((K : ℝ) * (T : ℝ))) * ‖v‖
          from rfl]
      dsimp only [D, E]
      ring

/-- The fixed-time coefficient meets the compact Lipschitz premise of `J`. -/
theorem lipschitzOnWith_qFixed
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {t : ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (v : Fin d → ℝ) (i : Fin d) :
    LipschitzOnWith (fixedLipschitzConstant T a Ka K v)
      (qFixed A T a v i t) (Icc (0 : ℝ) (T : ℝ)) :=
  (lipschitzWith_qFixed hA hAb ha ht v i).lipschitzOnWith

/-- The integrand in the forward kernel equation. Coefficients outside the
common horizon are evaluated at their clamped time. -/
def p (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (T : ℝ≥0) (a : ℝ → ℝ) (v : Fin d → ℝ) (i : Fin d) (t s : ℝ) : ℝ :=
  a (clamp T s) * (A (clamp T t)
    (fundamentalCLM A T (max (clamp T t) (clamp T s)) (clamp T s) v)) i

theorem continuous_p
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ}
    (hA : Continuous A) (hc : Continuous a) (v : Fin d → ℝ) (i : Fin d) :
    Continuous (Function.uncurry (p A T a v i)) := by
  have ht : Continuous (fun z : ℝ × ℝ => clamp T z.1) :=
    (continuous_clamp T).comp continuous_fst
  have hs : Continuous (fun z : ℝ × ℝ => clamp T z.2) :=
    (continuous_clamp T).comp continuous_snd
  have hPhi : Continuous (fun z : ℝ × ℝ =>
      fundamentalCLM A T (max (clamp T z.1) (clamp T z.2)) (clamp T z.2)) := by
    apply (continuousOn_fundamentalCLM_triangle_of_continuous hA).comp_continuous
      ((ht.max hs).prodMk hs)
    intro z
    exact ⟨(clamp_mem T z.2).1, le_max_right _ _,
      max_le (clamp_mem T z.1).2 (clamp_mem T z.2).2⟩
  exact (hc.comp hs).mul ((continuous_apply i).comp
    ((hA.comp ht).clm_apply (hPhi.clm_apply continuous_const)))

theorem abs_p_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (v : Fin d → ℝ) (i : Fin d) (t s : ℝ) :
    |p A T a v i t s| ≤ (K : ℝ) * bound T a Ka K v := by
  have hs := clamp_mem T s
  have ht := clamp_mem T t
  have hPhi : ‖fundamentalCLM A T (max (clamp T t) (clamp T s)) (clamp T s) v‖ ≤
      Real.exp ((K : ℝ) * (T : ℝ)) * ‖v‖ :=
    ((fundamentalCLM A T (max (clamp T t) (clamp T s)) (clamp T s)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right
        (norm_fundamentalCLM_le_uniform hA hAb hs.1
          ⟨le_max_right _ _, max_le ht.2 hs.2⟩) (norm_nonneg v))
  have haction : |(A (clamp T t)
      (fundamentalCLM A T (max (clamp T t) (clamp T s)) (clamp T s) v)) i| ≤
      (K : ℝ) * (Real.exp ((K : ℝ) * (T : ℝ)) * ‖v‖) := by
    calc
      _ ≤ ‖A (clamp T t)
          (fundamentalCLM A T (max (clamp T t) (clamp T s)) (clamp T s) v)‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm
          (A (clamp T t)
            (fundamentalCLM A T (max (clamp T t) (clamp T s)) (clamp T s) v)) i
      _ ≤ ‖A (clamp T t)‖ *
          ‖fundamentalCLM A T (max (clamp T t) (clamp T s)) (clamp T s) v‖ :=
        (A (clamp T t)).le_opNorm _
      _ ≤ _ := mul_le_mul (hAb _ ht) hPhi (norm_nonneg _) K.coe_nonneg
  rw [p, abs_mul]
  calc
    _ ≤ amplitudeBound T a Ka *
        ((K : ℝ) * (Real.exp ((K : ℝ) * (T : ℝ)) * ‖v‖)) :=
      mul_le_mul (abs_amplitude_le ha hs) haction (abs_nonneg _)
        (amplitudeBound_nonneg T a Ka)
    _ = _ := by unfold bound; ring

theorem p_of_mem
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0}
    {a : ℝ → ℝ} {v : Fin d → ℝ} {i : Fin d} {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (hs : s ∈ Icc (0 : ℝ) t) :
    p A T a v i t s = a s * (A t (fundamentalCLM A T t s v)) i := by
  simp only [p, clamp_of_mem ht, clamp_of_mem ⟨hs.1, hs.2.trans ht.2⟩,
    max_eq_left hs.2]

/-- The forcing coefficient before application of its time cutoff. -/
def g (T : ℝ≥0) (a : ℝ → ℝ) (v : Fin d → ℝ) (i : Fin d) (s : ℝ) : ℝ :=
  a (clamp T s) * v i

theorem continuous_g {T : ℝ≥0} {a : ℝ → ℝ}
    (hc : Continuous a) (v : Fin d → ℝ) (i : Fin d) : Continuous (g T a v i) :=
  (hc.comp (continuous_clamp T)).mul continuous_const

theorem abs_g_le {T : ℝ≥0} {a : ℝ → ℝ} {Ka : ℝ≥0}
    (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (v : Fin d → ℝ) (i : Fin d) (s : ℝ) :
    |g T a v i s| ≤ amplitudeBound T a Ka * ‖v‖ := by
  rw [g, abs_mul]
  exact mul_le_mul (abs_amplitude_le ha (clamp_mem T s))
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
    (abs_nonneg _) (amplitudeBound_nonneg T a Ka)

/-- The pointwise forward kernel equation on every genuine integration triangle. -/
theorem q_integral_eq
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0}
    {a : ℝ → ℝ} {v : Fin d → ℝ} {i : Fin d} {t s : ℝ}
    (hA : Continuous A) (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (hs : s ∈ Icc (0 : ℝ) t) :
    q A T a v i t s = g T a v i s + ∫ r in s..t, p A T a v i r s := by
  have hsT : s ≤ (T : ℝ) := hs.2.trans ht.2
  have hc := hA.clm_apply (continuous_fundamentalCLM_forward hA hsT v)
  have hcoord : (fundamentalCLM A T t s v) i =
      v i + ∫ r in s..t, (A r (fundamentalCLM A T r s v)) i := by
    have heq := congrArg (fun x : Fin d → ℝ => x i)
      (fundamentalCLM_integral_eq_apply hA hsT ⟨hs.2, ht.2⟩ v)
    have hcomm := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ
      ).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) s t)
    change (fundamentalCLM A T t s v) i =
      v i + (∫ r in s..t, A r (fundamentalCLM A T r s v)) i at heq
    exact heq.trans (congrArg (fun z : ℝ => v i + z) hcomm.symm)
  rw [q_of_mem ht hs, hcoord, mul_add]
  have hg : g T a v i s = a s * v i := by
    simp only [g, clamp_of_mem ⟨hs.1, hsT⟩]
  rw [hg, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hs.2] at hr
  exact (p_of_mem ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩ ⟨hs.1, hr.1⟩).symm

/-- The actual moving-cutoff kernels as elements of one common L² space. -/
def qLp
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (v : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) :=
  Analysis.MovingTriangleKernel.sliceLp T (continuous_q hA hc v i)
    (bound_nonneg T a Ka K v) (abs_q_le hA hAb ha v i) t

theorem continuous_qLp
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (v : Fin d → ℝ) (i : Fin d) : Continuous (qLp hA hAb hc ha v i) :=
  Analysis.MovingTriangleKernel.continuous_sliceLp (continuous_q hA hc v i)
    (bound_nonneg T a Ka K v) (abs_q_le hA hAb ha v i)

/-- The forward integrand in the same common L² space as `qLp`. -/
def pLp
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (v : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) :=
  Analysis.MovingTriangleKernel.sliceLp T (continuous_p hA hc v i)
    (mul_nonneg K.coe_nonneg (bound_nonneg T a Ka K v)) (abs_p_le hA hAb ha v i) t

/-- The cut-off forcing kernel; only the amplitude data enter its construction. -/
def gLp
    {T : ℝ≥0} {a : ℝ → ℝ} {Ka : ℝ≥0}
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (v : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) :=
  Analysis.MovingTriangleKernel.sliceLp T (q := fun _ s => g T a v i s)
    ((continuous_g hc v i).comp continuous_snd)
    (mul_nonneg (amplitudeBound_nonneg T a Ka) (norm_nonneg v))
    (fun _ => abs_g_le ha v i) t

theorem continuous_pLp
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (v : Fin d → ℝ) (i : Fin d) : Continuous (pLp hA hAb hc ha v i) :=
  Analysis.MovingTriangleKernel.continuous_sliceLp (continuous_p hA hc v i)
    (mul_nonneg K.coe_nonneg (bound_nonneg T a Ka K v)) (abs_p_le hA hAb ha v i)

theorem continuous_gLp
    {T : ℝ≥0} {a : ℝ → ℝ} {Ka : ℝ≥0}
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (v : Fin d → ℝ) (i : Fin d) : Continuous (gLp hc ha v i) :=
  Analysis.MovingTriangleKernel.continuous_sliceLp (q := fun _ s => g T a v i s)
    ((continuous_g hc v i).comp continuous_snd)
    (mul_nonneg (amplitudeBound_nonneg T a Ka) (norm_nonneg v))
    (fun _ => abs_g_le ha v i)

/-- The actual deterministic kernel satisfies its Volterra equation in L².
The required Bochner and joint scalar integrability follow from the producers
above and the generic moving-triangle theorem. -/
theorem qLp_integral_eq
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0} {a : ℝ → ℝ} {t : ℝ} {Ka K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) (T : ℝ), ‖A r‖ ≤ K)
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) (T : ℝ)))
    (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) (v : Fin d → ℝ) (i : Fin d) :
    qLp hA hAb hc ha v i t = gLp hc ha v i t +
      ∫ r in (0 : ℝ)..t, pLp hA hAb hc ha v i r := by
  exact Analysis.MovingTriangleKernel.sliceLp_integral_eq
    (continuous_q hA hc v i) (bound_nonneg T a Ka K v) (abs_q_le hA hAb ha v i)
    (continuous_p hA hc v i) (mul_nonneg K.coe_nonneg (bound_nonneg T a Ka K v))
    (abs_p_le hA hAb ha v i)
    (continuous_g hc v i) (mul_nonneg (amplitudeBound_nonneg T a Ka) (norm_nonneg v))
    (abs_g_le ha v i) ht (fun s hs => q_integral_eq hA ht hs)

end Ripple.Kurtz.StrongApprox.VolterraGaussian.FundamentalKernel
