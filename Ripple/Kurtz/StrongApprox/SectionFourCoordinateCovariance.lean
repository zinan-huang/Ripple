import Ripple.Kurtz.StrongApprox.SectionFourKernelIdentification

/-!
# Coordinate covariance of the actual Section Four limit

The derived propagated-kernel representation and independence of the physical
Brownian channels give the covariance of any two coordinates at two times.
The coefficient in the resulting integral is the original rate, and the
evolution is the actual columnwise Volterra construction.
-/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox

open VolterraGaussian
open VolterraGaussian.FundamentalKernel

/-- Replacing either random variable on a null set preserves its covariance.
This is a statement about the defining integrals and needs no extra moments. -/
theorem covariance_congr_ae_pair
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y X' Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  unfold ProbabilityTheory.covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX, hY] with ω hx hy
  rw [hx, hy]

section Actual

variable {m d : ℕ} {v : Fin m → Fin d → ℝ}
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
/-- Each actual coordinate is square integrable at every observation in the
construction window, by its already constructed random L² representative. -/
theorem sectionFourV_coordinate_memLp (x0 : Fin d → ℝ) (T : ℝ≥0)
    {t : ℝ≥0} (ht : t ≤ T) (i : Fin d) :
    MemLp (fun ω => sectionFourV F' f v x0 T ω t i) 2
      (channelKMTMeasure (Fin m)) := by
  exact (Lp.memLp (MeanSquarePath.sectionFourL2Path (v := v)
    heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T t i)).ae_eq
      (MeanSquarePath.sectionFourL2Path_ae (v := v)
        heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T
          ⟨t.coe_nonneg, by exact_mod_cast ht⟩ i)

include heps hM hf0 hfB h319 hL1 hL2n hL2 hLg in
/-- Two-time, two-coordinate covariance of the actual Section Four process.
No kernel representation or covariance identity is assumed. -/
theorem sectionFourV_coordinate_covariance (x0 : Fin d → ℝ) (T : ℝ≥0)
    {t u : ℝ≥0} (ht : t ≤ T) (hu : u ≤ T) (i j : Fin d) :
    cov[fun ω => sectionFourV F' f v x0 T ω t i,
      fun ω => sectionFourV F' f v x0 T ω u j; channelKMTMeasure (Fin m)] =
      ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)),
        ∑ l : Fin m, f l (kurtzFluidLimit f v x0 s.toNNReal) *
          (fundamentalCLM (sectionFourCoeff F' f v x0) T t s (v l)) i *
          (fundamentalCLM (sectionFourCoeff F' f v x0) T u s (v l)) j := by
  classical
  let A := sectionFourCoeff F' f v x0
  let amp : Fin m → ℝ → ℝ :=
    fun l s => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal))
  let K : ℝ≥0 := ⟨L1, (norm_nonneg (F' 0)).trans (hL1 0)⟩
  let Ka : Fin m → ℝ≥0 := fun l => Lg l *
    ⟨kurtzDriftBound v eps, kurtzDriftBound_nonneg heps⟩
  have hA : Continuous A :=
    continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  have hAb : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), ‖A s‖ ≤ K := fun s _ => hL1 _
  have hc : ∀ l, Continuous (amp l) := fun l =>
    Real.continuous_sqrt.comp ((continuous_rate_of_lip heps hM h319 l).comp
      ((continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0).comp
        continuous_real_toNNReal))
  have ha : ∀ l, LipschitzOnWith (Ka l) (amp l) (Icc (0 : ℝ) (T : ℝ)) := fun l =>
    lipschitzOn_sqrt_fluid (v := v) heps hM hf0 hfB h319 Lg hLg x0 T l
  let qt : Fin m → ℝ → ℝ := fun l => qFixed A T (amp l) (v l) i t
  let qu : Fin m → ℝ → ℝ := fun l => qFixed A T (amp l) (v l) j u
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) :=
    ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have huI : (u : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) :=
    ⟨u.coe_nonneg, by exact_mod_cast hu⟩
  have hct : ∀ l, Continuous (qt l) := fun l =>
    continuous_qFixed hA (hc l) htI (v l) i
  have hcu : ∀ l, Continuous (qu l) := fun l =>
    continuous_qFixed hA (hc l) huI (v l) j
  have hlt : ∀ l, LipschitzOnWith (fixedLipschitzConstant T (amp l) (Ka l) K (v l))
      (qt l) (Icc (0 : ℝ) (T : ℝ)) := fun l =>
    lipschitzOnWith_qFixed hA hAb (ha l) htI (v l) i
  have hlu : ∀ l, LipschitzOnWith (fixedLipschitzConstant T (amp l) (Ka l) K (v l))
      (qu l) (Icc (0 : ℝ) (T : ℝ)) := fun l =>
    lipschitzOnWith_qFixed hA hAb (ha l) huI (v l) j
  have hrepT : (fun ω => sectionFourV F' f v x0 T ω t i) =ᵐ[channelKMTMeasure (Fin m)]
      fun ω => ∑ l, ChannelWienerCovariance.channelJ (qt l) l t ω :=
    sectionFourV_ae_kernelJ (v := v) heps hM hf0 hfB h319 hL1 hL2n hL2 Lg hLg x0 ht i
  have hrepU : (fun ω => sectionFourV F' f v x0 T ω u j) =ᵐ[channelKMTMeasure (Fin m)]
      fun ω => ∑ l, ChannelWienerCovariance.channelJ (qu l) l u ω :=
    sectionFourV_ae_kernelJ (v := v) heps hM hf0 hfB h319 hL1 hL2n hL2 Lg hLg x0 hu j
  calc
    _ = cov[fun ω => ∑ l, ChannelWienerCovariance.channelJ (qt l) l t ω,
        fun ω => ∑ l, ChannelWienerCovariance.channelJ (qu l) l u ω;
        channelKMTMeasure (Fin m)] := covariance_congr_ae_pair hrepT hrepU
    _ = ∑ l, ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)), qt l s * qu l s :=
      ChannelWienerCovariance.covariance_sum_channelJ ht hu hct hcu hlt hlu
    _ = ∫ s in Ioc (0 : ℝ) (min (t : ℝ) (u : ℝ)), ∑ l, qt l s * qu l s := by
      symm
      exact integral_finsetSum Finset.univ (fun l _ =>
        (((hct l).mul (hcu l)).intervalIntegrable 0 (min (t : ℝ) (u : ℝ))).1)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hst : s ≤ (t : ℝ) := hs.2.trans (min_le_left _ _)
      have hsu : s ≤ (u : ℝ) := hs.2.trans (min_le_right _ _)
      apply Finset.sum_congr rfl
      intro l _
      have hqt : qt l s = amp l s * (fundamentalCLM A T t s (v l)) i :=
        qFixed_of_mem htI ⟨hs.1.le, hst⟩
      have hqu : qu l s = amp l s * (fundamentalCLM A T u s (v l)) j :=
        qFixed_of_mem huI ⟨hs.1.le, hsu⟩
      rw [hqt, hqu]
      change (amp l s * (fundamentalCLM A T t s (v l)) i) *
          (amp l s * (fundamentalCLM A T u s (v l)) j) =
        f l (kurtzFluidLimit f v x0 s.toNNReal) *
          (fundamentalCLM A T t s (v l)) i * (fundamentalCLM A T u s (v l)) j
      calc
        _ = (amp l s) ^ 2 * (fundamentalCLM A T t s (v l)) i *
            (fundamentalCLM A T u s (v l)) j := by ring
        _ = _ := by dsimp only [amp]; rw [Real.sq_sqrt (hf0 l _)]

end Actual
end Ripple.Kurtz.StrongApprox
