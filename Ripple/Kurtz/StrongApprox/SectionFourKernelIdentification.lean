import Ripple.Kurtz.StrongApprox.FundamentalKernelEquation
import Ripple.Kurtz.StrongApprox.SectionFourMeanSquareEquation
import Ripple.Kurtz.StrongApprox.ChannelWienerCovariance

/-!
# Identifying the actual limit with the propagated Wiener kernel

Both sides satisfy the same equation in a fixed random L² space. Uniqueness
therefore identifies each observation without requiring an uncountable
intersection of time-slice null events.
-/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox

open Ripple.Analysis.MeanSquareVolterra
open Ripple.Analysis.BochnerSquareIntegrable
open Ripple.Stochastic.MathFin.WienerIntegralL2
open VolterraGaussian.FundamentalKernel
open MeanSquarePath

variable {m d : ℕ}

/-- The original Wiener CLM for one physical product channel. -/
def channelWienerMap (T : ℝ≥0) (l : Fin m) :
    Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) T)) →L[ℝ]
      Lp ℝ 2 (channelKMTMeasure (Fin m)) := by
  letI := channelBrownian_isPreBrownian l
  exact wienerIntegralLp (μ := channelKMTMeasure (Fin m)) (channelBrownian l) T

section Generic

variable {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ≥0}
  {a : Fin m → ℝ → ℝ} {Ka : Fin m → ℝ≥0} {K : ℝ≥0}
  (hA : Continuous A) (hAb : ∀ r ∈ Icc (0 : ℝ) T, ‖A r‖ ≤ K)
  (hc : ∀ l, Continuous (a l))
  (ha : ∀ l, LipschitzOnWith (Ka l) (a l) (Icc (0 : ℝ) T))
  (v : Fin m → Fin d → ℝ)

/-- The stochastic image of the produced deterministic kernel. -/
def propagatedWiener (t : ℝ) : Fin d → Lp ℝ 2 (channelKMTMeasure (Fin m)) :=
  ∑ l, fun i => channelWienerMap T l (qLp hA hAb (hc l) (ha l) (v l) i t)

def unpropagatedWiener (t : ℝ) : Fin d → Lp ℝ 2 (channelKMTMeasure (Fin m)) :=
  ∑ l, fun i => channelWienerMap T l (gLp (hc l) (ha l) (v l) i t)

/-- The propagated process equation is derived by Bochner/CLM commutation
from the actual fundamental evolution's deterministic kernel equation. -/
theorem propagatedWiener_isSolution :
    Analysis.LinearVolterra.IsSolution (fun r => matrixLift (A r))
      (unpropagatedWiener hc ha v) (propagatedWiener hA hAb hc ha v) T := by
  apply isSolution_sum Finset.univ (continuous_matrixLift hA)
  intro l _
  exact isSolution_mapCoordinates (channelWienerMap T l) hA
    (qLp_isSolution hA hAb (hc l) (ha l) (v l))

/-- At a fixed time each propagated Wiener output is the actual pathwise
integration-by-parts value with the fixed-time Lipschitz coefficient. -/
theorem propagatedWiener_ae {t : ℝ≥0} (ht : t ≤ T) (i : Fin d) :
    (propagatedWiener hA hAb hc ha v t i : channelKMTSpace (Fin m) → ℝ)
      =ᵐ[channelKMTMeasure (Fin m)] fun ω =>
      ∑ l, ChannelWienerCovariance.channelJ (qFixed A T (a l) (v l) i t) l t ω := by
  have hsum := finite_sum_ae Finset.univ fun l : Fin m =>
    channelWienerMap T l (qLp hA hAb (hc l) (ha l) (v l) i t)
  have hterm : ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ l : Fin m,
      (channelWienerMap T l (qLp hA hAb (hc l) (ha l) (v l) i t) :
        channelKMTSpace (Fin m) → ℝ) ω =
      ChannelWienerCovariance.channelJ (qFixed A T (a l) (v l) i t) l t ω := by
    rw [ae_all_iff]
    intro l
    letI := channelBrownian_isPreBrownian l
    rw [qLp_eq_cutoffLp hA hAb (hc l) (ha l) (v l) i ht]
    exact WienerIntegralPathBridge.wienerIntegralLp_cutoff_ae_eq_J ht _ _
      (Eventually.of_forall (channelBrownian_continuous l))
  filter_upwards [hsum, hterm] with ω hs hl
  simpa only [propagatedWiener, Finset.sum_apply] using
    hs.trans (Finset.sum_congr rfl fun l _ => hl l)

end Generic

section Actual

variable {v : Fin m → Fin d → ℝ}
  {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ} {M : ℝ}
  {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L1 L2 : ℝ}
  (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
  (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
  (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
  (hL1 : ∀ x, ‖F' x‖ ≤ L1)
  (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
  (Lg : Fin m → ℝ≥0)
  (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)

include heps hM hf0 hfB h319 hL1 hL2n hL2 hLg in
/-- Actual V, not a newly chosen process, has the propagated-kernel formula
at each observation time. No representation is among the hypotheses. -/
theorem sectionFourV_ae_kernelJ (x0 : Fin d → ℝ) {T t : ℝ≥0} (ht : t ≤ T)
    (i : Fin d) :
    (fun ω => sectionFourV F' f v x0 T ω t i) =ᵐ[channelKMTMeasure (Fin m)]
      fun ω => ∑ l, ChannelWienerCovariance.channelJ
        (qFixed (sectionFourCoeff F' f v x0) T
          (fun s => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal))) (v l) i t) l t ω := by
  let A := sectionFourCoeff F' f v x0
  let amp : Fin m → ℝ → ℝ := fun l s => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal))
  have hA : Continuous A :=
    continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  let K : ℝ≥0 := ⟨L1, (norm_nonneg (F' 0)).trans (hL1 0)⟩
  have hAb : ∀ s ∈ Icc (0 : ℝ) T, ‖A s‖ ≤ K := fun s _ => hL1 _
  have hc : ∀ l, Continuous (amp l) := fun l =>
    Real.continuous_sqrt.comp ((continuous_rate_of_lip heps hM h319 l).comp
      ((continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0).comp continuous_real_toNNReal))
  have ha := fun l => lipschitzOn_sqrt_fluid (v := v) heps hM hf0 hfB h319 Lg hLg x0 T l
  let W := propagatedWiener hA hAb hc ha v
  let V := sectionFourL2Path (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T
  have hforce : EqOn (unpropagatedWiener hc ha v)
      (fluidForcingLp (v := v) heps hM hf0 hfB h319 Lg hLg x0 T) (Icc (0 : ℝ) T) := by
    intro r hr
    have hrn : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hr.2
    have hrcoe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ hr.1
    funext j
    simp only [unpropagatedWiener, Finset.sum_apply, fluidForcingLp,
      clampTime_of_mem T hr]
    apply Finset.sum_congr rfl
    intro l _
    have hg := gLp_eq_cutoffLp (hc l) (ha l) (v l) j hrn
    rw [hrcoe] at hg
    rw [hg, map_smul]
    rfl
  have hW := isSolution_congr_forcing
    (propagatedWiener_isSolution hA hAb hc ha v) hforce
  have heq : V t = W t :=
    eqOn_of_matrixLift_solutions hA T.coe_nonneg hAb
      (sectionFourL2Path_isSolution (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T)
      hW ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have hv := sectionFourL2Path_ae (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T
    ⟨t.coe_nonneg, by exact_mod_cast ht⟩ i
  have hw := propagatedWiener_ae hA hAb hc ha v ht i
  have heqi : V t i = W t i := congrFun heq i
  change (V t i : channelKMTSpace (Fin m) → ℝ) =ᵐ[_] _ at hv
  rw [heqi] at hv
  exact hv.symm.trans hw

end Actual
end Ripple.Kurtz.StrongApprox
