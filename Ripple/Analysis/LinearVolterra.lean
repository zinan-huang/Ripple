import Ripple.Analysis.StableGronwall
import Ripple.Kurtz.IntegralGronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Ripple.Analysis.PeanoBoundedExistence

/-!
# Linear Volterra equations on a compact time interval

The forcing term need only be continuous. The estimates and uniqueness below hold on every
finite nonnegative interval in a Banach space. Existence on arbitrary finite intervals is
constructed in a finite coordinate space using a bounded Peano equation and truncation.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology Interval NNReal

namespace Ripple.Analysis.LinearVolterra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The continuous-path formulation; values outside the specified interval are irrelevant to
its equation. Every continuous path on the closed interval has a continuous extension. -/
structure IsSolution (A : ℝ → E →L[ℝ] E) (G V : ℝ → E) (T : ℝ) : Prop where
  continuous : Continuous V
  equation : ∀ t ∈ Icc 0 T, V t = G t + ∫ s in (0 : ℝ)..t, A s (V s)

/-- The FTC hypotheses of the existing integral Gronwall theorem follow from continuity. -/
theorem integral_gronwall_continuous {u : ℝ → ℝ} {T M K : ℝ}
    (hu : Continuous u) (hT : 0 ≤ T) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hu_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ u t)
    (hineq : ∀ t ∈ Icc 0 T, u t ≤ M + ∫ s in (0 : ℝ)..t, K * u s) :
    ∀ t ∈ Icc 0 T, u t ≤ M * Real.exp (K * t) := by
  have hg : Continuous (fun s => K * u s) := continuous_const.mul hu
  have hp : Continuous (fun t => ∫ s in (0 : ℝ)..t, K * u s) := by
    exact intervalIntegral.continuous_primitive (fun x y => hg.intervalIntegrable x y) 0
  intro t ht
  exact Ripple.Kurtz.integral_gronwall hT hM hK hu_nonneg hineq
    (fun x _ => hg.intervalIntegrable 0 x)
    (fun _ _ => hg.continuousAt.continuousWithinAt)
    (fun x _ => hg.stronglyMeasurableAtFilter volume (nhdsWithin x (Ioi x)))
    (continuous_const.add hp).continuousOn t ht

/-- The operator norm bound transfers to the integral. -/
theorem norm_integral_apply_le
    {A : ℝ → E →L[ℝ] E} {V : ℝ → E} {T K t : ℝ}
    (hA : Continuous A) (hV : Continuous V)
    (hK : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K) (ht : t ∈ Icc 0 T) :
    ‖∫ s in (0 : ℝ)..t, A s (V s)‖ ≤ ∫ s in (0 : ℝ)..t, K * ‖V s‖ := by
  have hAV := hA.clm_apply hV
  apply (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
  apply intervalIntegral.integral_mono_on ht.1
    (hAV.norm.intervalIntegrable 0 t)
    ((continuous_const.mul hV.norm).intervalIntegrable 0 t)
  intro s hs
  exact ((A s).le_opNorm (V s)).trans
    (mul_le_mul_of_nonneg_right (hK s ⟨hs.1, hs.2.trans ht.2⟩) (norm_nonneg _))

/-- The forcing sup bound yields the usual exponential estimate on every finite interval. -/
theorem norm_le_exp
    {A : ℝ → E →L[ℝ] E} {G V : ℝ → E} {T M K : ℝ}
    (hA : Continuous A) (hV : IsSolution A G V T)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hAbound : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K)
    (hGbound : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ M) :
    ∀ t ∈ Icc 0 T, ‖V t‖ ≤ M * Real.exp (K * t) := by
  apply integral_gronwall_continuous hV.continuous.norm hT hM hK
    (fun _ _ => norm_nonneg _)
  intro t ht
  calc
    ‖V t‖ = ‖G t + ∫ s in (0 : ℝ)..t, A s (V s)‖ := congrArg norm (hV.equation t ht)
    _ ≤ ‖G t‖ + ‖∫ s in (0 : ℝ)..t, A s (V s)‖ := norm_add_le _ _
    _ ≤ M + ∫ s in (0 : ℝ)..t, K * ‖V s‖ :=
      add_le_add (hGbound t ht) (norm_integral_apply_le hA hV.continuous hAbound ht)

/-- Subtraction of two integral solutions preserves the coefficient and subtracts the forcing. -/
theorem IsSolution.sub
    {A : ℝ → E →L[ℝ] E} {G H V W : ℝ → E} {T : ℝ}
    (hA : Continuous A) (hV : IsSolution A G V T) (hW : IsSolution A H W T) :
    IsSolution A (fun t => G t - H t) (fun t => V t - W t) T := by
  refine ⟨hV.continuous.sub hW.continuous, ?_⟩
  intro t ht
  rw [hV.equation t ht, hW.equation t ht]
  have hint : (∫ s in (0 : ℝ)..t, A s (V s - W s)) =
      (∫ s in (0 : ℝ)..t, A s (V s)) - ∫ s in (0 : ℝ)..t, A s (W s) := by
    simp_rw [map_sub]
    exact intervalIntegral.integral_sub
      ((hA.clm_apply hV.continuous).intervalIntegrable 0 t)
      ((hA.clm_apply hW.continuous).intervalIntegrable 0 t)
  rw [hint]
  abel

/-- The solution depends continuously, with an explicit norm bound, on its forcing path. -/
theorem norm_sub_le_exp
    {A : ℝ → E →L[ℝ] E} {G H V W : ℝ → E} {T M K : ℝ}
    (hA : Continuous A) (hV : IsSolution A G V T) (hW : IsSolution A H W T)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hAbound : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K)
    (hforcing : ∀ t ∈ Icc 0 T, ‖G t - H t‖ ≤ M) :
    ∀ t ∈ Icc 0 T, ‖V t - W t‖ ≤ M * Real.exp (K * t) :=
  norm_le_exp hA (IsSolution.sub hA hV hW) hT hM hK hAbound hforcing

/-- Uniqueness concerns the specified interval, rather than arbitrary extensions outside it. -/
theorem eqOn_of_solution
    {A : ℝ → E →L[ℝ] E} {G V W : ℝ → E} {T K : ℝ}
    (hA : Continuous A) (hV : IsSolution A G V T) (hW : IsSolution A G W T)
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hAbound : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K) :
    EqOn V W (Icc 0 T) := by
  intro t ht
  have h := norm_sub_le_exp hA hV hW hT (le_refl (0 : ℝ)) hK hAbound
    (fun s _ => by simp) t ht
  have hz : ‖V t - W t‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Actual existence on a short interval, obtained by solving for the correction `V - G`.
No derivative of the continuous forcing is required. The numerical smallness condition is
used only for existence; the estimates and uniqueness above have no such restriction. -/
theorem exists_solution_of_mul_le
    {A : ℝ → E →L[ℝ] E} {G : ℝ → E} {T : ℝ} (K M : ℝ≥0)
    (hA : Continuous A) (hG : Continuous G) (hT : 0 ≤ T)
    (hAbound : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K)
    (hGbound : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ M)
    (hsmall : (K : ℝ) * T ≤ 1 / 2) :
    ∃ V : ℝ → E, IsSolution A G V T := by
  let a : ℝ≥0 := ⟨2 * (K : ℝ) * (M : ℝ) * T, by positivity⟩
  let L : ℝ≥0 := K * (a + M)
  let tzero : Icc (0 : ℝ) T := ⟨0, le_refl _, hT⟩
  let f : ℝ → E → E := fun t x => A t (x + G t)
  have hf : IsPicardLindelof f tzero (0 : E) a 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      rw [dist_eq_norm, dist_eq_norm]
      change ‖A t (x + G t) - A t (y + G t)‖ ≤ (K : ℝ) * ‖x - y‖
      rw [← map_sub, add_sub_add_right_eq_sub]
      exact ((A t).le_opNorm (x - y)).trans
        (mul_le_mul_of_nonneg_right (hAbound t ht) (norm_nonneg _))
    · intro x hx
      exact (hA.clm_apply (continuous_const.add hG)).continuousOn
    · intro t ht x hx
      have hxnorm : ‖x‖ ≤ (a : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      change ‖A t (x + G t)‖ ≤ (K : ℝ) * ((a : ℝ) + (M : ℝ))
      calc
        ‖A t (x + G t)‖ ≤ ‖A t‖ * ‖x + G t‖ := (A t).le_opNorm _
        _ ≤ (K : ℝ) * (‖x‖ + ‖G t‖) :=
          mul_le_mul (hAbound t ht) (norm_add_le _ _) (norm_nonneg _) K.coe_nonneg
        _ ≤ (K : ℝ) * ((a : ℝ) + (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add hxnorm (hGbound t ht)) K.coe_nonneg
    · change (K : ℝ) * ((a : ℝ) + (M : ℝ)) * max (T - 0) (0 - 0) ≤ (a : ℝ) - 0
      rw [sub_zero, sub_self, max_eq_left hT, sub_zero]
      have ha : (a : ℝ) = 2 * (K : ℝ) * (M : ℝ) * T := rfl
      have hprod := mul_le_mul_of_nonneg_right hsmall a.coe_nonneg
      nlinarith
  have hx : (0 : E) ∈ Metric.closedBall (0 : E) (0 : ℝ) := by simp
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  have heq := (ODE.FunSpace.isFixedPt_next_iff hf hx).mp hα
  refine ⟨fun t => G t + α.compProj t, ⟨hG.add α.continuous_compProj, ?_⟩⟩
  intro t ht
  have hc : α.compProj t = ∫ s in (0 : ℝ)..t, A s (α.compProj s + G s) := by
    rw [ODE.FunSpace.compProj_of_mem ht]
    simpa [ODE.picard, f, tzero] using heq ⟨t, ht⟩
  calc
    G t + α.compProj t = G t + ∫ s in (0 : ℝ)..t, A s (α.compProj s + G s) := by rw [hc]
    _ = G t + ∫ s in (0 : ℝ)..t, A s (G s + α.compProj s) := by simp_rw [add_comm]

section FiniteCoordinates

variable {ι : Type*} [Fintype ι]

/-- A bounded continuous, time-dependent finite-dimensional field has an integral solution.
The additional coordinate is a clock; its derivative is identically one. -/
theorem exists_bounded_timeDependent_solution
    (f : ℝ → (ι → ℝ) → (ι → ℝ))
    (hf : Continuous (Function.uncurry f)) {B T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x, ‖f t x‖ ≤ B) :
    ∃ y : ℝ → (ι → ℝ), Continuous y ∧
      ∀ t ∈ Icc 0 T, y t = ∫ s in (0 : ℝ)..t, f s (y s) := by
  classical
  let clock : (Option ι → ℝ) → ℝ := fun z => max 0 (min T (z none))
  let state : (Option ι → ℝ) → (ι → ℝ) := fun z i => z (some i)
  let F : (Option ι → ℝ) → (Option ι → ℝ) := fun z j =>
    match j with
    | none => 1
    | some i => f (clock z) (state z) i
  have hc : Continuous clock := by dsimp [clock]; fun_prop
  have hs : Continuous state := by dsimp [state]; fun_prop
  have hF : Continuous F := by
    apply continuous_pi
    intro j
    cases j with
    | none => exact continuous_const
    | some i => exact (continuous_apply i).comp (hf.comp (hc.prodMk hs))
  have hclockmem (z : Option ι → ℝ) : clock z ∈ Icc 0 T := by
    refine ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  have hFbound (z : Option ι → ℝ) : ‖F z‖ ≤ max 1 B := by
    rw [pi_norm_le_iff_of_nonneg (le_trans zero_le_one (le_max_left _ _))]
    intro j
    cases j with
    | none => simpa [F] using (le_max_left (1 : ℝ) B)
    | some i =>
      exact (norm_le_pi_norm (f (clock z) (state z)) i).trans
        ((hbound _ (hclockmem z) _).trans (le_max_right _ _))
  obtain ⟨z, hz, hzeq, _⟩ :=
    PeanoBoundedExistence.exists_peanoBounded_solution F hF (max 1 B) hFbound 0 hT
  have hcomp : Continuous (fun s => F (z s)) := hF.comp hz
  have hcoord (j : Option ι) (t : ℝ) (ht : t ∈ Icc 0 T) :
      z t j = ∫ s in (0 : ℝ)..t, F (z s) j := by
    have h := congrArg (fun q : Option ι → ℝ => q j) (hzeq t ht)
    simp only [Pi.add_apply, Pi.zero_apply, zero_add] at h
    exact h.trans ((ContinuousLinearMap.proj j : (Option ι → ℝ) →L[ℝ] ℝ
      ).intervalIntegral_comp_comm (hcomp.intervalIntegrable 0 t)).symm
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) : z t none = t := by
    simpa [F] using hcoord none t ht
  have hclock (t : ℝ) (ht : t ∈ Icc 0 T) : clock (z t) = t := by
    dsimp [clock]
    rw [htime t ht, min_eq_right ht.2, max_eq_right ht.1]
  let y : ℝ → (ι → ℝ) := fun t => state (z t)
  have hy : Continuous y := hs.comp hz
  refine ⟨y, hy, ?_⟩
  intro t ht
  ext i
  have heval : (∫ s in (0 : ℝ)..t, f s (y s)) i =
      ∫ s in (0 : ℝ)..t, f s (y s) i := by
    symm
    exact (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ
      ).intervalIntegral_comp_comm ((hf.comp (continuous_id.prodMk hy)).intervalIntegrable 0 t)
  rw [heval]
  change z t (some i) = _
  rw [hcoord (some i) t ht]
  apply intervalIntegral.integral_congr
  intro s hs'
  rw [uIcc_of_le ht.1] at hs'
  have hsT : s ∈ Icc 0 T := ⟨hs'.1, hs'.2.trans ht.2⟩
  change f (clock (z s)) (state (z s)) i = f s (y s) i
  rw [hclock s hsT]

/-- Coordinatewise clipping to a closed box. -/
def boxClamp (R : ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => max (-R) (min R (x i))

@[fun_prop]
theorem continuous_boxClamp (R : ℝ) : Continuous (boxClamp (ι := ι) R) := by
  unfold boxClamp
  fun_prop

/-- Clipping bounds the sup norm by the radius. -/
theorem norm_boxClamp_le_radius {R : ℝ} (hR : 0 ≤ R) (x : ι → ℝ) :
    ‖boxClamp R x‖ ≤ R := by
  rw [pi_norm_le_iff_of_nonneg hR]
  intro i
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clipping does not increase the sup norm. -/
theorem norm_boxClamp_le {R : ℝ} (hR : 0 ≤ R) (x : ι → ℝ) :
    ‖boxClamp R x‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  have hxi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hlow : -‖x‖ ≤ x i := (abs_le.mp hxi).1
  have hupp : x i ≤ ‖x‖ := (abs_le.mp hxi).2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact (le_min (by linarith [norm_nonneg x]) hlow).trans (le_max_right _ _)
  · exact max_le (by linarith [norm_nonneg x]) ((min_le_right _ _).trans hupp)

/-- Clipping fixes every point of the box. -/
theorem boxClamp_eq_self {R : ℝ} {x : ι → ℝ} (hx : ‖x‖ ≤ R) : boxClamp R x = x := by
  ext i
  have hxiNorm : |x i| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hxi : |x i| ≤ R := hxiNorm.trans hx
  simp only [boxClamp, min_eq_right (abs_le.mp hxi).2, max_eq_right (abs_le.mp hxi).1]

/-- Existence on every finite nonnegative interval for a continuous linear coefficient and
continuous forcing, in a finite coordinate space. The clipped correction satisfies an a priori
Gronwall bound, which proves that clipping was inactive throughout the desired interval. -/
theorem exists_solution
    {A : ℝ → (ι → ℝ) →L[ℝ] (ι → ℝ)} {G : ℝ → (ι → ℝ)} {T K M : ℝ}
    (hA : Continuous A) (hG : Continuous G) (hT : 0 ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hAbound : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K)
    (hGbound : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ M) :
    ∃ V : ℝ → (ι → ℝ), IsSolution A G V T := by
  let R : ℝ := M * Real.exp (K * T)
  have hR : 0 ≤ R := mul_nonneg hM (Real.exp_nonneg _)
  let f : ℝ → (ι → ℝ) → (ι → ℝ) := fun t y => A t (boxClamp R y + G t)
  have hf : Continuous (Function.uncurry f) := by
    exact (hA.comp continuous_fst).clm_apply
      (((continuous_boxClamp R).comp continuous_snd).add (hG.comp continuous_fst))
  have hbound : ∀ t ∈ Icc 0 T, ∀ y, ‖f t y‖ ≤ K * (R + M) := by
    intro t ht y
    exact ((A t).le_opNorm _).trans
      (mul_le_mul (hAbound t ht)
        ((norm_add_le _ _).trans (add_le_add (norm_boxClamp_le_radius hR y) (hGbound t ht)))
        (norm_nonneg _) hK)
  obtain ⟨y, hy, hyeq⟩ := exists_bounded_timeDependent_solution f hf hT hbound
  have hfy : Continuous (fun s => f s (y s)) := hf.comp (continuous_id.prodMk hy)
  have hineq : ∀ t ∈ Icc 0 T,
      ‖y t‖ + M ≤ M + ∫ s in (0 : ℝ)..t, K * (‖y s‖ + M) := by
    intro t ht
    have hi : ‖y t‖ ≤ ∫ s in (0 : ℝ)..t, K * (‖y s‖ + M) := by
      rw [hyeq t ht]
      apply (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
      apply intervalIntegral.integral_mono_on ht.1
        (hfy.norm.intervalIntegrable 0 t)
        ((continuous_const.mul (hy.norm.add continuous_const)).intervalIntegrable 0 t)
      intro s hs
      have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
      exact ((A s).le_opNorm _).trans
        (mul_le_mul (hAbound s hsT)
          ((norm_add_le _ _).trans (add_le_add (norm_boxClamp_le hR _) (hGbound s hsT)))
          (norm_nonneg _) hK)
    linarith
  have hgr := integral_gronwall_continuous (hy.norm.add continuous_const)
    hT hM hK (fun _ _ => add_nonneg (norm_nonneg _) hM) hineq
  have hybound : ∀ t ∈ Icc 0 T, ‖y t‖ ≤ R := by
    intro t ht
    have hg : ‖y t‖ + M ≤ M * Real.exp (K * t) := hgr t ht
    have he : M * Real.exp (K * t) ≤ R :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht.2 hK)) hM
    linarith
  refine ⟨fun t => G t + y t, ⟨hG.add hy, ?_⟩⟩
  intro t ht
  rw [hyeq t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
  dsimp [f]
  rw [boxClamp_eq_self (hybound s hsT), add_comm]

/-- Continuous coefficients and forcing alone suffice for existence and uniqueness on the
specified interval. Compactness supplies the finite norm bounds used by the construction. -/
theorem exists_solution_uniqueOn
    {A : ℝ → (ι → ℝ) →L[ℝ] (ι → ℝ)} {G : ℝ → (ι → ℝ)} {T : ℝ}
    (hA : Continuous A) (hG : Continuous G) (hT : 0 ≤ T) :
    ∃ V : ℝ → (ι → ℝ), IsSolution A G V T ∧
      ∀ W, IsSolution A G W T → EqOn V W (Icc 0 T) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  have hKnonneg : 0 ≤ K := (norm_nonneg (A 0)).trans (hK 0 ⟨le_rfl, hT⟩)
  have hMnonneg : 0 ≤ M := (norm_nonneg (G 0)).trans (hM 0 ⟨le_rfl, hT⟩)
  obtain ⟨V, hV⟩ := exists_solution hA hG hT hKnonneg hMnonneg hK hM
  exact ⟨V, hV, fun W hW => eqOn_of_solution hA hV hW hT hKnonneg hK⟩

end FiniteCoordinates

end Ripple.Analysis.LinearVolterra
