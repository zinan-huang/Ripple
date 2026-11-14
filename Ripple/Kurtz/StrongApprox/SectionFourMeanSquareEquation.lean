import Ripple.Kurtz.StrongApprox.SectionFourPathMoments
import Ripple.Kurtz.StrongApprox.WienerIntegralPathBridge
import Ripple.Analysis.BochnerSquareIntegrable
import Ripple.Analysis.MeanSquareMatrixLift

/-!
# The actual Section Four equation in mean square

Compact random paths supply one square-integrable dominator for all time
coordinates. Time is clamped only to define a globally continuous L² path;
inside the construction horizon its representatives are the actual process.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox.MeanSquarePath

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {d : ℕ}

/-- Continuous clamping into the construction interval. -/
def clampTime (T : ℝ≥0) (s : ℝ) : Icc (0 : ℝ) (T : ℝ) :=
  ⟨max 0 (min T s), le_max_left _ _, max_le T.coe_nonneg (min_le_left _ _)⟩

@[fun_prop] theorem continuous_clampTime (T : ℝ≥0) : Continuous (clampTime T) := by
  exact (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

@[simp] theorem clampTime_of_mem (T : ℝ≥0) {s : ℝ} (hs : s ∈ Icc 0 (T : ℝ)) :
    (clampTime T s : ℝ) = s := by
  simp [clampTime, min_eq_right hs.2, max_eq_right hs.1]

/-- Evaluation of a square-integrable random compact path is square integrable. -/
theorem memLp_eval {T : ℝ≥0} {P : Ω → C(Icc (0 : ℝ) (T : ℝ), Fin d → ℝ)}
    (hP : MemLp P 2 μ) (s : ℝ) (i : Fin d) :
    MemLp (fun ω => P ω (clampTime T s) i) 2 μ := by
  have hm : AEStronglyMeasurable (fun ω => P ω (clampTime T s) i) μ :=
    ((ContinuousLinearMap.proj i).comp
      (ContinuousMap.evalCLM ℝ (clampTime T s))).continuous.comp_aestronglyMeasurable hP.1
  exact hP.norm.mono' hm (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact (norm_le_pi_norm (P ω (clampTime T s)) i).trans
      (ContinuousMap.norm_coe_le_norm (P ω) (clampTime T s)))

/-- The coordinate L² class of the clamped actual random path. -/
def coordinate {T : ℝ≥0} {P : Ω → C(Icc (0 : ℝ) (T : ℝ), Fin d → ℝ)}
    (hP : MemLp P 2 μ) (s : ℝ) (i : Fin d) : Lp ℝ 2 μ :=
  (memLp_eval hP s i).toLp (fun ω => P ω (clampTime T s) i)

 theorem coordinate_ae {T : ℝ≥0} {P : Ω → C(Icc (0 : ℝ) (T : ℝ), Fin d → ℝ)}
    (hP : MemLp P 2 μ) (s : ℝ) (i : Fin d) :
    (coordinate hP s i : Ω → ℝ) =ᵐ[μ] fun ω => P ω (clampTime T s) i :=
  (memLp_eval hP s i).coeFn_toLp

/-- Pointwise path continuity and the common uniform bound give norm continuity in L². -/
theorem continuous_coordinate {T : ℝ≥0}
    {P : Ω → C(Icc (0 : ℝ) (T : ℝ), Fin d → ℝ)} (hP : MemLp P 2 μ) :
    Continuous (coordinate hP) := by
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.2
  intro s
  apply Ripple.Analysis.BochnerSquareIntegrable.tendsto_toLp_of_dominated
    (fun r => memLp_eval hP r i) (memLp_eval hP s i) hP.norm
  · exact Eventually.of_forall fun r => ae_of_all _ fun ω =>
      (norm_le_pi_norm (P ω (clampTime T r)) i).trans
        (ContinuousMap.norm_coe_le_norm (P ω) (clampTime T r))
  · exact ae_of_all _ fun ω =>
      (norm_le_pi_norm (P ω (clampTime T s)) i).trans
        (ContinuousMap.norm_coe_le_norm (P ω) (clampTime T s))
  · exact ae_of_all _ fun ω =>
      (((continuous_apply i).comp (P ω).continuous).comp
        (continuous_clampTime T)).continuousAt.tendsto

open Ripple.Analysis.MeanSquareVolterra

private theorem sum_ae {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ 2 μ) :
    (fun ω => (∑ i ∈ s, f i) ω) =ᵐ[μ] fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero ℝ 2 μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with ω hadd hs
    simp only [hadd, hs, Pi.add_apply]

/-- The lifted matrix has the expected actual scalar representative. -/
theorem matrixLift_coordinate_ae {T : ℝ≥0}
    {P : Ω → C(Icc (0 : ℝ) (T : ℝ), Fin d → ℝ)} (hP : MemLp P 2 μ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (s : ℝ) (i : Fin d) :
    ((matrixLift A (coordinate hP s) i : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ]
      fun ω => A (P ω (clampTime T s)) i := by
  classical
  have hsum := sum_ae Finset.univ fun j =>
    (A (Pi.single j 1) i) • coordinate hP s j
  have hterm : ∀ᵐ ω ∂μ, ∀ j : Fin d,
      ((A (Pi.single j 1) i) • coordinate hP s j) ω =
        A (Pi.single j 1) i * P ω (clampTime T s) j := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (A (Pi.single j 1) i) (coordinate hP s j),
      coordinate_ae hP s j] with ω hsm hj
    simp only [hsm, Pi.smul_apply, smul_eq_mul, hj]
  filter_upwards [hsum, hterm] with ω hs ht
  rw [matrixLift_apply, hs, matrix_apply A (P ω (clampTime T s)) i]
  exact Finset.sum_congr rfl fun j _ => ht j

/-- A lifted deterministic matrix acts continuously on the mean-square path. -/
theorem continuous_matrix_coordinate {T : ℝ≥0}
    {P : Ω → C(Icc (0 : ℝ) (T : ℝ), Fin d → ℝ)} (hP : MemLp P 2 μ)
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} (hA : Continuous A) :
    Continuous (fun s => matrixLift (A s) (coordinate hP s)) := by
  apply continuous_pi
  intro i
  simp only [matrixLift_apply]
  apply continuous_finsetSum
  intro j _
  exact (((continuous_apply i).comp (hA.clm_apply continuous_const)).smul
    ((continuous_apply j).comp (continuous_coordinate hP)))

/-- Scalar Fubini identifies the lifted time integral with any supplied actual
pointwise-integral representative; the uniform random-path norm supplies its bound. -/
theorem integral_matrix_coordinate_eq [SFinite μ] {T t : ℝ≥0} (ht : t ≤ T)
    {P : Ω → C(Icc (0 : ℝ) (T : ℝ), Fin d → ℝ)} (hP : MemLp P 2 μ)
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} (hA : Continuous A)
    {C : ℝ} (hC : 0 ≤ C) (hAb : ∀ s, ‖A s‖ ≤ C)
    (i : Fin d) (y : Lp ℝ 2 μ)
    (hy : (y : Ω → ℝ) =ᵐ[μ] fun ω =>
      ∫ s in Ioc (0 : ℝ) (t : ℝ), A s (P ω (clampTime T s)) i) :
    (∫ s in Ioc (0 : ℝ) (t : ℝ), matrixLift (A s) (coordinate hP s) i) = y := by
  let ν := volume.restrict (Ioc (0 : ℝ) (t : ℝ))
  let g : ℝ → Ω → ℝ := fun s ω => A s (P ω (clampTime T s)) i
  have hg : AEStronglyMeasurable (Function.uncurry g) (ν.prod μ) := by
    have hc : Continuous (fun p : ℝ × C(Icc (0 : ℝ) (T : ℝ), Fin d → ℝ) =>
        A p.1 (p.2 (clampTime T p.1)) i) := by fun_prop
    exact hc.comp_aestronglyMeasurable
      (measurable_fst.aestronglyMeasurable.prodMk hP.1.comp_snd)
  have hbound : ∀ᵐ p ∂ν.prod μ, |g p.1 p.2| ≤ |C * ‖P p.2‖| := by
    apply ae_of_all
    intro p
    rw [abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
    exact (norm_le_pi_norm (A p.1 (P p.2 (clampTime T p.1))) i).trans
      (((A p.1).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (hAb p.1) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _) hC)))
  have hk : Integrable (fun s => matrixLift (A s) (coordinate hP s) i) ν := by
    exact (((continuous_apply i).comp (continuous_matrix_coordinate hP hA)).continuousOn.integrableOn_compact
      (K := Icc (0 : ℝ) (t : ℝ)) isCompact_Icc).mono_set
        (fun s hs => ⟨hs.1.le, hs.2⟩)
  refine Ripple.Analysis.BochnerSquareIntegrable.integral_eq_of_representative hk
    (ae_of_all _ fun s => matrixLift_coordinate_ae hP (A s) s i) hy ?_
  intro z
  exact Ripple.Analysis.BochnerSquareIntegrable.integrable_test_product hg
    (hP.norm.const_mul C) hbound z

end Ripple.Kurtz.StrongApprox.MeanSquarePath

namespace Ripple.Kurtz.StrongApprox.MeanSquarePath
open Ripple.Analysis.MeanSquareVolterra
open Ripple.Stochastic.MathFin.WienerIntegralL2

section Actual
variable {m d : ℕ} {v : Fin m → Fin d → ℝ}
    {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ} {M : ℝ}
    {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L1 L2 : ℝ}
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    (hL1 : ∀ x, ‖F' x‖ ≤ L1) (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)

/-- The globally continuous, clamped L² coordinates of the actual limit. -/
def sectionFourL2Path (x0 : Fin d → ℝ) (T : ℝ≥0) :
    ℝ → Fin d → Lp ℝ 2 (channelKMTMeasure (Fin m)) :=
  coordinate (sectionFourVPath_moments (v := v)
    heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T).2

 theorem continuous_sectionFourL2Path (x0 : Fin d → ℝ) (T : ℝ≥0) :
    Continuous (sectionFourL2Path (v := v)
      heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T) :=
  continuous_coordinate _

 theorem sectionFourL2Path_ae (x0 : Fin d → ℝ) (T : ℝ≥0)
    {s : ℝ} (hs : s ∈ Icc 0 (T : ℝ)) (i : Fin d) :
    (sectionFourL2Path (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T s i :
      channelKMTSpace (Fin m) → ℝ) =ᵐ[channelKMTMeasure (Fin m)]
      fun ω => sectionFourV F' f v x0 T ω s i := by
  filter_upwards [coordinate_ae
    (sectionFourVPath_moments (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T).2 s i]
    with ω hω
  simpa only [sectionFourL2Path, sectionFourVPath_apply, clampTime_of_mem T hs] using hω

/-- The actual fluid coefficient, as input to the fixed-horizon Wiener map. -/
def fluidWienerLp (x0 : Fin d → ℝ) (T t : ℝ≥0) (ht : t ≤ T) (l : Fin m) :
    Lp ℝ 2 (channelKMTMeasure (Fin m)) := by
  letI := channelBrownian_isPreBrownian l
  have hc : Continuous (fun s : ℝ => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal))) :=
    Real.continuous_sqrt.comp ((continuous_rate_of_lip heps hM h319 l).comp
      ((continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0).comp
        continuous_real_toNNReal))
  exact wienerIntegralLp (μ := channelKMTMeasure (Fin m)) (channelBrownian l) T
    (WienerIntegralPathBridge.cutoffLp ht hc
      (lipschitzOn_sqrt_fluid (v := v) heps hM hf0 hfB h319 Lg hLg x0 T l))

 theorem fluidWienerLp_ae (x0 : Fin d → ℝ) (T t : ℝ≥0) (ht : t ≤ T) (l : Fin m) :
    (fluidWienerLp (v := v) heps hM hf0 hfB h319 Lg hLg x0 T t ht l :
      channelKMTSpace (Fin m) → ℝ) =ᵐ[channelKMTMeasure (Fin m)]
      fun ω => Analysis.BVIntegrationByParts.J
        (fun s => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal)))
        (fun s => channelBrownian l s.toNNReal ω) t := by
  letI := channelBrownian_isPreBrownian l
  exact WienerIntegralPathBridge.wienerIntegralLp_cutoff_ae_eq_J ht _ _
    (Eventually.of_forall (channelBrownian_continuous l))

/-- The Wiener forcing extended to all real times by continuous time clamping. -/
def fluidForcingLp (x0 : Fin d → ℝ) (T : ℝ≥0) (s : ℝ) :
    Fin d → Lp ℝ 2 (channelKMTMeasure (Fin m)) :=
  fun i => ∑ l, (v l i) • fluidWienerLp (v := v) heps hM hf0 hfB h319 Lg hLg x0 T
    (clampTime T s).val.toNNReal
    (Real.toNNReal_le_iff_le_coe.2 (clampTime T s).property.2) l

/-- The original almost-sure Volterra equation lifted into fixed scalar L²
coordinates. Its forcing consists of the actual fixed-horizon Wiener maps. -/
theorem sectionFourL2Path_equation (x0 : Fin d → ℝ) (T t : ℝ≥0) (ht : t ≤ T)
    (i : Fin d) :
    sectionFourL2Path (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T t i =
      (∑ l, (v l i) • fluidWienerLp (v := v) heps hM hf0 hfB h319 Lg hLg x0 T t ht l) +
      ∫ s in Ioc (0 : ℝ) (t : ℝ),
        matrixLift (sectionFourCoeff F' f v x0 s)
          (sectionFourL2Path (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T s) i := by
  classical
  let P := sectionFourVPath (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T
  have hP : MemLp P 2 (channelKMTMeasure (Fin m)) :=
    (sectionFourVPath_moments (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T).2
  let k := sectionFourL2Path (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T
  let q : Lp ℝ 2 (channelKMTMeasure (Fin m)) :=
    ∑ l, (v l i) • fluidWienerLp (v := v) heps hM hf0 hfB h319 Lg hLg x0 T t ht l
  have hq : (q : channelKMTSpace (Fin m) → ℝ) =ᵐ[channelKMTMeasure (Fin m)]
      fun ω => ∑ l, (v l i) * Analysis.BVIntegrationByParts.J
        (fun s => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal)))
        (fun s => channelBrownian l s.toNNReal ω) t := by
    have hs := sum_ae Finset.univ fun l =>
      (v l i) • fluidWienerLp (v := v) heps hM hf0 hfB h319 Lg hLg x0 T t ht l
    have hterm : ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ l : Fin m,
        ((v l i) • fluidWienerLp (v := v) heps hM hf0 hfB h319 Lg hLg x0 T t ht l) ω =
          (v l i) * Analysis.BVIntegrationByParts.J
            (fun s => Real.sqrt (f l (kurtzFluidLimit f v x0 s.toNNReal)))
            (fun s => channelBrownian l s.toNNReal ω) t := by
      rw [ae_all_iff]
      intro l
      filter_upwards [Lp.coeFn_smul (v l i)
        (fluidWienerLp (v := v) heps hM hf0 hfB h319 Lg hLg x0 T t ht l),
        fluidWienerLp_ae (v := v) heps hM hf0 hfB h319 Lg hLg x0 T t ht l] with ω hsm hw
      simp only [hsm, Pi.smul_apply, smul_eq_mul, hw]
    filter_upwards [hs, hterm] with ω hs hw
    exact hs.trans (Finset.sum_congr rfl fun l _ => hw l)
  have htn : (t : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) :=
    ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have hy : ((k t i - q : Lp ℝ 2 (channelKMTMeasure (Fin m))) :
      channelKMTSpace (Fin m) → ℝ) =ᵐ[channelKMTMeasure (Fin m)]
      fun ω => ∫ s in Ioc (0 : ℝ) (t : ℝ),
        sectionFourCoeff F' f v x0 s (P ω (clampTime T s)) i := by
    filter_upwards [Lp.coeFn_sub (k t i) q,
      sectionFourL2Path_ae (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T htn i,
      hq, sectionFourV_ae_equation_J heps hM hf0 hfB h319 hL2n hL2 Lg hLg x0 T]
      with ω hsub hk hqω hω
    rw [hsub, Pi.sub_apply, hk, hqω]
    have he := congrFun (hω t htn) i
    have hi := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).intervalIntegral_comp_comm
      (((continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0).clm_apply
        (continuous_sectionFourV (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T ω)).intervalIntegrable
          (μ := volume) 0 t))
    simp only [ContinuousLinearMap.proj_apply, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm] at he hi
    rw [← hi] at he
    rw [he, add_sub_cancel_left]
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsT : s ∈ Icc (0 : ℝ) (T : ℝ) :=
      ⟨hs.1.le, hs.2.trans htn.2⟩
    simp only [P, sectionFourVPath_apply, clampTime_of_mem T hsT]
  have hA := continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  have hC : 0 ≤ L1 := (norm_nonneg (F' 0)).trans (hL1 0)
  have hInt := integral_matrix_coordinate_eq ht hP hA hC
    (fun s => hL1 _) i (k t i - q) hy
  change k t i = q + ∫ s in Ioc (0 : ℝ) (t : ℝ),
    matrixLift (sectionFourCoeff F' f v x0 s) (coordinate hP s) i
  rw [hInt]
  abel

/-- The actual process satisfies the vector L² Volterra equation, with no
mean-square equation included among the hypotheses. -/
theorem sectionFourL2Path_isSolution (x0 : Fin d → ℝ) (T : ℝ≥0) :
    Analysis.LinearVolterra.IsSolution
      (fun s => matrixLift (H := Lp ℝ 2 (channelKMTMeasure (Fin m)))
        (sectionFourCoeff F' f v x0 s))
      (fluidForcingLp (v := v) heps hM hf0 hfB h319 Lg hLg x0 T)
      (sectionFourL2Path (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T)
      T := by
  refine ⟨continuous_sectionFourL2Path (v := v)
    heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T, ?_⟩
  intro s hs
  let tn : ℝ≥0 := s.toNNReal
  have htn : tn ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
  have hcoe : (tn : ℝ) = s := Real.coe_toNNReal _ hs.1
  have hc : Continuous fun r => matrixLift (sectionFourCoeff F' f v x0 r)
      (sectionFourL2Path (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T r) :=
    continuous_matrix_coordinate
      (sectionFourVPath_moments (v := v) heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T).2
      (continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0)
  funext i
  have hi := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin d => Lp ℝ 2 (channelKMTMeasure (Fin m))) i).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) 0 s)
  simp only [ContinuousLinearMap.proj_apply] at hi
  rw [Pi.add_apply, ← hi, intervalIntegral.integral_of_le hs.1]
  have he := sectionFourL2Path_equation (v := v)
    heps hM hf0 hfB h319 hL2n hL2 hL1 Lg hLg x0 T tn htn i
  simpa only [hcoe, fluidForcingLp, clampTime_of_mem T hs, tn] using he

end Actual
end Ripple.Kurtz.StrongApprox.MeanSquarePath
