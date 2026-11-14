import Ripple.Kurtz.StrongApprox.FundamentalMatrixKernel
import Ripple.Kurtz.StrongApprox.WienerVolterraTransport

/-!
# The deterministic propagated kernel solves the lifted Volterra equation

The scalar triangle calculation is assembled into the finite coordinate
equation. Its forcing is the original unpropagated amplitude times the jump
vector, and its coefficient is the original matrix acting on L² coordinates.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators NNReal

namespace Ripple.Kurtz.StrongApprox.VolterraGaussian.FundamentalKernel

open Ripple.Analysis.MeanSquareVolterra
open Ripple.Analysis.MovingTriangleKernel
open Ripple.Analysis.BochnerSquareIntegrable

variable {d : ℕ}
  {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0}
  {a : ℝ → ℝ} {Ka K : ℝ≥0}

theorem qLp_ae
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) T, ‖A r‖ ≤ K)
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) T))
    (v : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    (qLp hA hAb hc ha v i t : ℝ → ℝ) =ᵐ[volume.restrict (Ioc (0 : ℝ) T)]
      slice (q A T a v i) t :=
  sliceLp_ae (continuous_q hA hc v i) (bound_nonneg T a Ka K v)
    (abs_q_le hA hAb ha v i) t

/-- The drifted scalar kernel is exactly the finite matrix action on the
propagated L² kernels, not a separately assumed coefficient process. -/
theorem pLp_eq_matrixLift
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) T, ‖A r‖ ≤ K)
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) T))
    (v : Fin d → ℝ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) (i : Fin d) :
    pLp hA hAb hc ha v i r =
      matrixLift (A r) (fun j => qLp hA hAb hc ha v j r) i := by
  classical
  apply Lp.ext
  have hsum := finite_sum_ae Finset.univ fun j : Fin d =>
    (A r (Pi.single j 1) i) • qLp hA hAb hc ha v j r
  have hterms : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) T), ∀ j : Fin d,
      ((A r (Pi.single j 1) i) • qLp hA hAb hc ha v j r) s =
        A r (Pi.single j 1) i * slice (q A T a v j) r s := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (A r (Pi.single j 1) i)
      (qLp hA hAb hc ha v j r), qLp_ae hA hAb hc ha v j r] with s hsm hj
    simp only [hsm, Pi.smul_apply, smul_eq_mul, hj]
  filter_upwards [sliceLp_ae (continuous_p hA hc v i)
      (mul_nonneg K.coe_nonneg (bound_nonneg T a Ka K v))
      (abs_p_le hA hAb ha v i) r,
    hsum, hterms, ae_restrict_mem measurableSet_Ioc] with s hp hs hj hsT
  change (pLp hA hAb hc ha v i r : ℝ → ℝ) s = _ at hp ⊢
  rw [hp, matrixLift_apply, hs]
  by_cases hsr : s ≤ r
  · have hs' : s ∈ Icc (0 : ℝ) r := ⟨hsT.1.le, hsr⟩
    rw [slice, indicator_of_mem (show s ∈ Ioc (0 : ℝ) r from ⟨hsT.1, hsr⟩), p_of_mem hr hs',
      matrix_apply (A r) (fundamentalCLM A T r s v) i]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hj j, slice, indicator_of_mem (show s ∈ Ioc (0 : ℝ) r from ⟨hsT.1, hsr⟩), q_of_mem hr hs']
    ring
  · rw [slice, indicator_of_notMem (fun h => hsr h.2)]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [hj j, slice, indicator_of_notMem (fun h => hsr h.2), mul_zero]

/-- The constructed deterministic kernel is a continuous L²-valued solution. -/
theorem qLp_isSolution
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) T, ‖A r‖ ≤ K)
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) T))
    (v : Fin d → ℝ) :
    Analysis.LinearVolterra.IsSolution (fun r => matrixLift (A r))
      (fun t i => gLp hc ha v i t)
      (fun t i => qLp hA hAb hc ha v i t) T := by
  refine ⟨continuous_pi fun i => continuous_qLp hA hAb hc ha v i, ?_⟩
  intro t ht
  funext i
  have hi := ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin d => Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) (T : ℝ)))) i).intervalIntegral_comp_comm
    (((continuous_matrixLift hA).clm_apply
      (continuous_pi fun j => continuous_qLp hA hAb hc ha v j)).intervalIntegrable (μ := volume) 0 t))
  simp only [ContinuousLinearMap.proj_apply] at hi
  rw [Pi.add_apply, ← hi, qLp_integral_eq hA hAb hc ha ht v i]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  exact pLp_eq_matrixLift hA hAb hc ha v ⟨hr.1, hr.2.trans ht.2⟩ i

/-- The deterministic forcing agrees with the original cutoff amplitude. -/
theorem gLp_eq_cutoffLp
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) T))
    (v : Fin d → ℝ) (i : Fin d) {t : ℝ≥0} (ht : t ≤ T) :
    gLp hc ha v i t = v i • WienerIntegralPathBridge.cutoffLp ht hc ha := by
  apply Lp.ext
  filter_upwards [sliceLp_ae (q := fun _ s => g T a v i s) ((continuous_g hc v i).comp continuous_snd)
      (mul_nonneg (amplitudeBound_nonneg T a Ka) (norm_nonneg v))
      (fun _ => abs_g_le ha v i) t,
    Lp.coeFn_smul (v i) (WienerIntegralPathBridge.cutoffLp ht hc ha),
    (WienerIntegralPathBridge.memLp_cutoff ht hc ha).coeFn_toLp]
      with s hg hsm ha'
  change (gLp hc ha v i t : ℝ → ℝ) s = _ at hg ⊢
  rw [hg, hsm, Pi.smul_apply, smul_eq_mul,
    show (WienerIntegralPathBridge.cutoffLp ht hc ha : ℝ → ℝ) s =
      WienerIntegralPathBridge.cutoff a t s from ha']
  by_cases hs : s ∈ Ioc (0 : ℝ) (t : ℝ)
  · simp only [slice, WienerIntegralPathBridge.cutoff, indicator_of_mem hs,
      g, clamp_of_mem ⟨hs.1.le, hs.2.trans (by exact_mod_cast ht)⟩]
    ring
  · simp only [slice, WienerIntegralPathBridge.cutoff, indicator_of_notMem hs, mul_zero]

/-- The propagated kernel can be tested using the same pathwise `J` bridge:
the fixed-time Lipschitz extension has exactly the same cutoff class. -/
theorem qLp_eq_cutoffLp
    (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) T, ‖A r‖ ≤ K)
    (hc : Continuous a) (ha : LipschitzOnWith Ka a (Icc (0 : ℝ) T))
    (v : Fin d → ℝ) (i : Fin d) {t : ℝ≥0} (ht : t ≤ T) :
    qLp hA hAb hc ha v i t =
      WienerIntegralPathBridge.cutoffLp ht
        (continuous_qFixed hA hc ⟨t.coe_nonneg, by exact_mod_cast ht⟩ v i)
        (lipschitzOnWith_qFixed hA hAb ha ⟨t.coe_nonneg, by exact_mod_cast ht⟩ v i) := by
  apply Lp.ext
  filter_upwards [qLp_ae hA hAb hc ha v i t,
    (WienerIntegralPathBridge.memLp_cutoff ht
      (continuous_qFixed hA hc ⟨t.coe_nonneg, by exact_mod_cast ht⟩ v i)
      (lipschitzOnWith_qFixed hA hAb ha ⟨t.coe_nonneg, by exact_mod_cast ht⟩ v i)).coeFn_toLp]
      with s hq hf
  rw [hq]
  refine Eq.trans ?_ hf.symm
  by_cases hs : s ∈ Ioc (0 : ℝ) (t : ℝ)
  · simp only [slice, WienerIntegralPathBridge.cutoff, indicator_of_mem hs]
    exact q_eq_qFixed_of_mem ⟨t.coe_nonneg, by exact_mod_cast ht⟩ ⟨hs.1.le, hs.2⟩
  · simp only [slice, WienerIntegralPathBridge.cutoff, indicator_of_notMem hs]

end Ripple.Kurtz.StrongApprox.VolterraGaussian.FundamentalKernel
