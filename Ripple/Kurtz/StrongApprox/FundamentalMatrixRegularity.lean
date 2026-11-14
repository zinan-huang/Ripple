import Ripple.Kurtz.StrongApprox.FundamentalMatrixBounds
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Regularity of the constructed fundamental evolution

The integral equation and uniqueness give the cocycle law for the actual
columnwise Volterra construction. A short-interval estimate then gives
Lipschitz dependence on the initial time, without using an inverse evolution.
Both time arguments are jointly Lipschitz on the closed time triangle.
-/

noncomputable section
open Set MeasureTheory
open scoped NNReal Topology Interval

namespace Ripple.Kurtz.StrongApprox.VolterraGaussian

variable {d : ℕ}

/-- The operator-valued forward trajectory is continuous, including its chosen
extension outside the construction interval. This follows from its finite columns. -/
theorem continuous_fundamentalCLM_forward_operator
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s : ℝ}
    (hA : Continuous A) (hs : s ≤ T) :
    Continuous (fun t => fundamentalCLM A T t s) := by
  classical
  unfold fundamentalCLM
  refine continuous_finsetSum Finset.univ ?_
  intro j _
  have hc : Continuous (fun t => fun i => fundamentalMatrix A T t s i j) := by
    have h := (fundamentalMatrix_column_solution hA hs j).continuous.comp
      (continuous_id.sub (continuous_const : Continuous fun _ : ℝ => s))
    simpa only [Function.comp_def, id, add_sub_cancel] using h
  exact ((ContinuousLinearMap.smulRightL ℝ (Fin d → ℝ) (Fin d → ℝ)
    (ContinuousLinearMap.proj j)).continuous).comp hc

/-- The translated defining equation, expressed in the original time variable. -/
theorem fundamentalCLM_integral_eq_apply
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s t : ℝ}
    (hA : Continuous A) (hs : s ≤ T) (ht : t ∈ Icc s T) (x : Fin d → ℝ) :
    fundamentalCLM A T t s x =
      x + ∫ r in s..t, A r (fundamentalCLM A T r s x) := by
  have h := (fundamentalCLM_solution hA hs x).equation (t - s)
    ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 s⟩
  have hshift :
      (∫ r in (0 : ℝ)..(t - s), A (s + r) (fundamentalCLM A T (s + r) s x)) =
        ∫ r in s..t, A r (fundamentalCLM A T r s x) := by
    simpa only [add_zero, add_sub_cancel] using
      (intervalIntegral.integral_comp_add_left
        (fun r => A r (fundamentalCLM A T r s x)) s
        (a := (0 : ℝ)) (b := t - s))
  simpa only [add_sub_cancel, hshift] using h

/-- The forward Volterra equation in the Banach space of continuous linear maps. -/
theorem fundamentalCLM_integral_eq
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s t : ℝ}
    (hA : Continuous A) (hs : s ≤ T) (ht : t ∈ Icc s T) :
    fundamentalCLM A T t s =
      1 + ∫ r in s..t, (A r).comp (fundamentalCLM A T r s) := by
  have hi := hA.clm_comp (continuous_fundamentalCLM_forward_operator hA hs)
  apply ContinuousLinearMap.ext
  intro x
  have hcomm := (ContinuousLinearMap.apply ℝ (Fin d → ℝ) x).intervalIntegral_comp_comm
    (hi.intervalIntegrable (μ := volume) s t)
  change fundamentalCLM A T t s x = x +
    (∫ r in s..t, (A r).comp (fundamentalCLM A T r s)) x
  have hcomm' : (∫ r in s..t, (A r).comp (fundamentalCLM A T r s)) x =
      ∫ r in s..t, A r (fundamentalCLM A T r s x) := hcomm.symm
  rw [hcomm']
  exact fundamentalCLM_integral_eq_apply hA hs ht x

/-- Restarting an existing trajectory gives the same equation with its current
value as initial value. Its extension remains globally continuous. -/
theorem fundamentalCLM_restarted_solution
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s r : ℝ}
    (hA : Continuous A) (hsr : s ≤ r) (hrT : r ≤ T) (x : Fin d → ℝ) :
    Analysis.LinearVolterra.IsSolution (fun q => A (r + q))
      (fun _ => fundamentalCLM A T r s x)
      (fun q => fundamentalCLM A T (r + q) s x) (T - r) := by
  have hsT : s ≤ T := hsr.trans hrT
  have hc := continuous_fundamentalCLM_forward hA hsT x
  have hi := hA.clm_apply hc
  refine ⟨hc.comp (continuous_const.add continuous_id), ?_⟩
  intro q hq
  have ht : r + q ∈ Icc s T := by constructor <;> linarith [hq.1, hq.2]
  have heq := fundamentalCLM_integral_eq_apply hA hsT ht x
  have hbase := fundamentalCLM_integral_eq_apply hA hsT ⟨hsr, hrT⟩ x
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (μ := volume) s r) (hi.intervalIntegrable (μ := volume) r (r + q))
  have hshift :
      (∫ z in (0 : ℝ)..q, A (r + z) (fundamentalCLM A T (r + z) s x)) =
        ∫ z in r..(r + q), A z (fundamentalCLM A T z s x) := by
    simpa only [add_zero] using
      (intervalIntegral.integral_comp_add_left
        (fun z => A z (fundamentalCLM A T z s x)) r (a := (0 : ℝ)) (b := q))
  rw [hshift, heq, hbase, ← hsplit]
  abel

/-- The actual evolution satisfies the cocycle law by Volterra uniqueness. -/
theorem fundamentalCLM_cocycle
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s r t : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (htT : t ≤ T) :
    (fundamentalCLM A T t r).comp (fundamentalCLM A T r s) =
      fundamentalCLM A T t s := by
  have hrT := hrt.trans htT
  have hshift : Continuous (fun q => A (r + q)) :=
    hA.comp (continuous_const.add continuous_id)
  have hbound : ∀ q ∈ Icc 0 (T - r), ‖A (r + q)‖ ≤ K := by
    intro q hq
    apply hAb
    constructor <;> linarith [hq.1, hq.2]
  apply ContinuousLinearMap.ext
  intro x
  have heq := Analysis.LinearVolterra.eqOn_of_solution hshift
    (fundamentalCLM_restarted_solution hA hsr hrT x)
    (fundamentalCLM_solution hA hrT (fundamentalCLM A T r s x))
    (sub_nonneg.mpr hrT) K.coe_nonneg hbound
    ⟨sub_nonneg.mpr hrt, sub_le_sub_right htT r⟩
  simpa only [ContinuousLinearMap.comp_apply, add_sub_cancel] using heq.symm

/-- A uniform operator norm bound on the closed time triangle. -/
theorem norm_fundamentalCLM_le_uniform
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s t : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K)
    (hs : 0 ≤ s) (ht : t ∈ Icc s T) :
    ‖fundamentalCLM A T t s‖ ≤ Real.exp ((K : ℝ) * T) := by
  apply (norm_fundamentalCLM_le hA (ht.1.trans ht.2)
    (fun q hq => hAb q ⟨hs.trans hq.1, hq.2⟩) ht).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) K.coe_nonneg

/-- Differences of forward trajectories are integrals over the interval between
the two end times. Both end times lie after the same starting time. -/
theorem fundamentalCLM_forward_sub_apply
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s t u : ℝ}
    (hA : Continuous A) (ht : t ∈ Icc s T) (hu : u ∈ Icc s T) (x : Fin d → ℝ) :
    fundamentalCLM A T t s x - fundamentalCLM A T u s x =
      ∫ q in u..t, A q (fundamentalCLM A T q s x) := by
  have hsT := ht.1.trans ht.2
  have hi := hA.clm_apply (continuous_fundamentalCLM_forward hA hsT x)
  rw [fundamentalCLM_integral_eq_apply hA hsT ht,
    fundamentalCLM_integral_eq_apply hA hsT hu, add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (hi.intervalIntegrable (μ := volume) s t) (hi.intervalIntegrable s u)

/-- Uniform Lipschitz bound in the end time, in operator norm. -/
theorem norm_fundamentalCLM_forward_sub_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s t u : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K)
    (hs : 0 ≤ s) (ht : t ∈ Icc s T) (hu : u ∈ Icc s T) :
    ‖fundamentalCLM A T t s - fundamentalCLM A T u s‖ ≤
      ((K : ℝ) * Real.exp ((K : ℝ) * T)) * |t - u| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖fundamentalCLM A T t s x - fundamentalCLM A T u s x‖ ≤ _
  rw [fundamentalCLM_forward_sub_apply hA ht hu]
  have hb : ∀ q ∈ Ι u t,
      ‖A q (fundamentalCLM A T q s x)‖ ≤
        ((K : ℝ) * Real.exp ((K : ℝ) * T)) * ‖x‖ := by
    intro q hq
    change q ∈ Ioc (min u t) (max u t) at hq
    have hsq : s ≤ q := (le_min hu.1 ht.1).trans hq.1.le
    have hqT : q ≤ T := hq.2.trans (max_le hu.2 ht.2)
    calc
      ‖A q (fundamentalCLM A T q s x)‖ ≤
          ‖A q‖ * ‖fundamentalCLM A T q s x‖ := (A q).le_opNorm _
      _ ≤ (K : ℝ) * (Real.exp ((K : ℝ) * T) * ‖x‖) :=
        mul_le_mul (hAb q ⟨hs.trans hsq, hqT⟩)
          (((fundamentalCLM A T q s).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right
              (norm_fundamentalCLM_le_uniform hA hAb hs ⟨hsq, hqT⟩) (norm_nonneg x)))
          (norm_nonneg _) K.coe_nonneg
      _ = _ := by ring
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans_eq (by ring)

/-- The actual evolution tends linearly to the identity near the diagonal. -/
theorem norm_fundamentalCLM_sub_one_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s t : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K)
    (hs : 0 ≤ s) (ht : t ∈ Icc s T) :
    ‖fundamentalCLM A T t s - 1‖ ≤
      ((K : ℝ) * Real.exp ((K : ℝ) * T)) * (t - s) := by
  have hsT := ht.1.trans ht.2
  simpa only [fundamentalCLM_diagonal hA hsT,
    abs_of_nonneg (sub_nonneg.mpr ht.1)] using
    norm_fundamentalCLM_forward_sub_le hA hAb hs ht ⟨le_rfl, hsT⟩

/-- Initial-time differences factor without an inverse matrix. -/
theorem fundamentalCLM_start_sub_factor
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s r t : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (htT : t ≤ T) :
    fundamentalCLM A T t s - fundamentalCLM A T t r =
      (fundamentalCLM A T t r).comp (fundamentalCLM A T r s - 1) := by
  rw [← fundamentalCLM_cocycle hA hAb hs hsr hrt htT]
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- Ordered initial times have a uniform Lipschitz estimate. -/
theorem norm_fundamentalCLM_start_sub_le_of_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s r t : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (htT : t ≤ T) :
    ‖fundamentalCLM A T t s - fundamentalCLM A T t r‖ ≤
      (((K : ℝ) * Real.exp ((K : ℝ) * T)) * Real.exp ((K : ℝ) * T)) * (r - s) := by
  rw [fundamentalCLM_start_sub_factor hA hAb hs hsr hrt htT]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    ‖fundamentalCLM A T t r‖ * ‖fundamentalCLM A T r s - 1‖ ≤
        Real.exp ((K : ℝ) * T) *
          (((K : ℝ) * Real.exp ((K : ℝ) * T)) * (r - s)) :=
      mul_le_mul (norm_fundamentalCLM_le_uniform hA hAb (hs.trans hsr) ⟨hrt, htT⟩)
        (norm_fundamentalCLM_sub_one_le hA hAb hs ⟨hsr, hrt.trans htT⟩)
        (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by ring

/-- Uniform dependence on the initial time, for either ordering of the times. -/
theorem norm_fundamentalCLM_start_sub_le
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T t s r : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K)
    (htT : t ≤ T) (hs : s ∈ Icc 0 t) (hr : r ∈ Icc 0 t) :
    ‖fundamentalCLM A T t s - fundamentalCLM A T t r‖ ≤
      (((K : ℝ) * Real.exp ((K : ℝ) * T)) * Real.exp ((K : ℝ) * T)) * |s - r| := by
  rcases le_total s r with hsr | hrs
  · simpa only [abs_sub_comm s r, abs_of_nonneg (sub_nonneg.mpr hsr)] using
      norm_fundamentalCLM_start_sub_le_of_le hA hAb hs.1 hsr hr.2 htT
  · rw [norm_sub_rev]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hrs)] using
      norm_fundamentalCLM_start_sub_le_of_le hA hAb hr.1 hrs hs.2 htT

/-- The initial-time kernel is Lipschitz on its full closed integration interval. -/
theorem lipschitzOnWith_fundamentalCLM_start
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T t : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K) (htT : t ≤ T) :
    LipschitzOnWith
      ⟨((K : ℝ) * Real.exp ((K : ℝ) * T)) * Real.exp ((K : ℝ) * T), by positivity⟩
      (fun s => fundamentalCLM A T t s) (Icc 0 t) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs r hr
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    norm_fundamentalCLM_start_sub_le hA hAb htT hs hr

/-- Continuity in the initial time, as needed for deterministic kernel integrals. -/
theorem continuousOn_fundamentalCLM_start
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T t : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K) (htT : t ≤ T) :
    ContinuousOn (fun s => fundamentalCLM A T t s) (Icc 0 t) :=
  (lipschitzOnWith_fundamentalCLM_start hA hAb htT).continuousOn

/-- Joint regularity on the genuine time triangle. The larger end time provides
a common intermediate slice which is admissible for both initial times. -/
theorem lipschitzOnWith_fundamentalCLM_triangle
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K) :
    LipschitzOnWith
      ⟨(K : ℝ) * Real.exp ((K : ℝ) * T) +
          ((K : ℝ) * Real.exp ((K : ℝ) * T)) * Real.exp ((K : ℝ) * T), by positivity⟩
      (fun p : ℝ × ℝ => fundamentalCLM A T p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := by
  apply LipschitzOnWith.of_dist_le_mul
  rintro ⟨t, s⟩ ⟨hs, hst, htT⟩ ⟨u, r⟩ ⟨hr, hru, huT⟩
  let B : ℝ := (K : ℝ) * Real.exp ((K : ℝ) * T)
  let C : ℝ := B * Real.exp ((K : ℝ) * T)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmaxT : max t u ≤ T := max_le htT huT
  have hsm : s ≤ max t u := hst.trans (le_max_left _ _)
  have hrm : r ≤ max t u := hru.trans (le_max_right _ _)
  have hforwardLeft :
      dist (fundamentalCLM A T t s) (fundamentalCLM A T (max t u) s) ≤
        B * |t - max t u| := by
    simpa only [dist_eq_norm, B] using
      norm_fundamentalCLM_forward_sub_le hA hAb hs ⟨hst, htT⟩ ⟨hsm, hmaxT⟩
  have hstart :
      dist (fundamentalCLM A T (max t u) s) (fundamentalCLM A T (max t u) r) ≤
        C * |s - r| := by
    simpa only [dist_eq_norm, C, B] using
      norm_fundamentalCLM_start_sub_le hA hAb hmaxT ⟨hs, hsm⟩ ⟨hr, hrm⟩
  have hforwardRight :
      dist (fundamentalCLM A T (max t u) r) (fundamentalCLM A T u r) ≤
        B * |max t u - u| := by
    simpa only [dist_eq_norm, B] using
      norm_fundamentalCLM_forward_sub_le hA hAb hr ⟨hrm, hmaxT⟩ ⟨hru, huT⟩
  have hsum : |t - max t u| + |max t u - u| = |t - u| := by
    rcases le_total t u with htu | hut
    · simp [max_eq_right htu]
    · simp [max_eq_left hut]
  have htDist : |t - u| ≤ dist (t, s) (u, r) := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hsDist : |s - r| ≤ dist (t, s) (u, r) := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  calc
    dist (fundamentalCLM A T t s) (fundamentalCLM A T u r) ≤
        dist (fundamentalCLM A T t s) (fundamentalCLM A T (max t u) s) +
          dist (fundamentalCLM A T (max t u) s) (fundamentalCLM A T (max t u) r) +
          dist (fundamentalCLM A T (max t u) r) (fundamentalCLM A T u r) :=
      dist_triangle4 _ _ _ _
    _ ≤ B * |t - max t u| + C * |s - r| + B * |max t u - u| :=
      add_le_add (add_le_add hforwardLeft hstart) hforwardRight
    _ = B * |t - u| + C * |s - r| := by
      calc
        _ = B * (|t - max t u| + |max t u - u|) + C * |s - r| := by ring
        _ = _ := by rw [hsum]
    _ ≤ B * dist (t, s) (u, r) + C * dist (t, s) (u, r) :=
      add_le_add (mul_le_mul_of_nonneg_left htDist hB)
        (mul_le_mul_of_nonneg_left hsDist hC)
    _ = _ := by
      change _ = ((K : ℝ) * Real.exp (K * T) +
        (K : ℝ) * Real.exp (K * T) * Real.exp (K * T)) * dist (t, s) (u, r)
      dsimp only [B, C]
      ring

/-- The constructed fundamental evolution is jointly continuous on the entire
closed time triangle, including its diagonal and the zero horizon. -/
theorem continuousOn_fundamentalCLM_triangle
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hAb : ∀ q ∈ Icc 0 T, ‖A q‖ ≤ K) :
    ContinuousOn (fun p : ℝ × ℝ => fundamentalCLM A T p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} :=
  (lipschitzOnWith_fundamentalCLM_triangle hA hAb).continuousOn

/-- Compactness supplies the coefficient bound; no bound is an additional
premise for joint continuity of the constructed evolution. -/
theorem continuousOn_fundamentalCLM_triangle_of_continuous
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ}
    (hA : Continuous A) :
    ContinuousOn (fun p : ℝ × ℝ => fundamentalCLM A T p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)
    ).exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max 0 M, le_max_left _ _⟩
  exact continuousOn_fundamentalCLM_triangle (K := K) hA
    (fun q hq => (hM q hq).trans (le_max_right _ _))

/-- Initial-time continuity requires only continuity of the coefficient. -/
theorem continuousOn_fundamentalCLM_start_of_continuous
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T t : ℝ}
    (hA : Continuous A) (htT : t ≤ T) :
    ContinuousOn (fun s => fundamentalCLM A T t s) (Icc 0 t) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)
    ).exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max 0 M, le_max_left _ _⟩
  exact continuousOn_fundamentalCLM_start (K := K) hA
    (fun q hq => (hM q hq).trans (le_max_right _ _)) htT

end Ripple.Kurtz.StrongApprox.VolterraGaussian
