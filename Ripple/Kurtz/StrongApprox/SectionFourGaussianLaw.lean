import Ripple.Kurtz.StrongApprox.SectionFourRTailKurtz
import Ripple.Stochastic.BrownianMotion.Gaussian.BrownianMotion
import Ripple.Kurtz.StrongApprox.IndependentGaussianChannels
import Ripple.Kurtz.StrongApprox.ChannelBrownianFiltration
import Ripple.Kurtz.StrongApprox.DeterministicItoBridge
import Ripple.Kurtz.StrongApprox.CenteredGaussianLimit
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
The actual independent Brownian channels have centered Gaussian laws as random elements of
compact uniform path spaces. Bernstein approximation and a square-integrable Brownian maximum
produce this law from the existing finite-dimensional Gaussian process, including zero horizons.

The integration-by-parts functional and finite observations of the Volterra solution are
continuous linear path maps. The evolution matrix is defined from the same Volterra solver.
The actual Section Four process is identified with the composed path map in
`SectionFourGaussianIdentification`.

The stochastic kernel covariance identity is
not proved in this module.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

/-! Compact-path random variables use the Borel sigma algebra of uniform convergence, through
the `MeasurableSpace C(X, Y) := borel _` and `BorelSpace` instances of
`Ripple.Stochastic.BrownianMotion.Gaussian.BrownianMotion`. -/

namespace VolterraGaussian

variable {d : ℕ}

/-- Addition preserves the linear Volterra equation. -/
theorem isSolution_add
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ}
    {G H V W : ℝ → Fin d → ℝ}
    (hA : Continuous A) (hV : Analysis.LinearVolterra.IsSolution A G V T)
    (hW : Analysis.LinearVolterra.IsSolution A H W T) :
    Analysis.LinearVolterra.IsSolution A (fun t => G t + H t)
      (fun t => V t + W t) T := by
  refine ⟨hV.continuous.add hW.continuous, ?_⟩
  intro t ht
  rw [hV.equation t ht, hW.equation t ht]
  simp_rw [map_add]
  rw [intervalIntegral.integral_add
    ((hA.clm_apply hV.continuous).intervalIntegrable 0 t)
    ((hA.clm_apply hW.continuous).intervalIntegrable 0 t)]
  abel

/-- Scalar multiplication preserves the linear Volterra equation. -/
theorem isSolution_smul
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ}
    {G V : ℝ → Fin d → ℝ}
    (hV : Analysis.LinearVolterra.IsSolution A G V T) (c : ℝ) :
    Analysis.LinearVolterra.IsSolution A (fun t => c • G t) (fun t => c • V t) T := by
  refine ⟨continuous_const.smul hV.continuous, ?_⟩
  intro t ht
  rw [hV.equation t ht]
  simp only [map_smul, intervalIntegral.integral_smul, smul_add]

/-- The choice of a solution respects addition on the interval where uniqueness holds. -/
theorem volterraSol_add
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hT : 0 ≤ T)
    (hAb : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K)
    {G H : ℝ → Fin d → ℝ} (hG : Continuous G) (hH : Continuous H)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    volterraSol A T (fun s => G s + H s) t =
      volterraSol A T G t + volterraSol A T H t := by
  exact Analysis.LinearVolterra.eqOn_of_solution hA
    (volterraSol_spec hA (hG.add hH) hT)
    (isSolution_add hA (volterraSol_spec hA hG hT) (volterraSol_spec hA hH hT))
    hT K.coe_nonneg hAb ht

/-- The choice of a solution respects scalar multiplication on the specified interval. -/
theorem volterraSol_smul
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hT : 0 ≤ T)
    (hAb : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K)
    {G : ℝ → Fin d → ℝ} (hG : Continuous G) (c : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    volterraSol A T (fun s => c • G s) t = c • volterraSol A T G t := by
  exact Analysis.LinearVolterra.eqOn_of_solution hA
    (volterraSol_spec hA (continuous_const.smul hG) hT)
    (isSolution_smul (volterraSol_spec hA hG hT) c)
    hT K.coe_nonneg hAb ht

/-- Continuous extension of a compact path by its endpoint values. -/
def extendPath {T : ℝ} (hT : 0 ≤ T) (c : C(Icc (0 : ℝ) T, Fin d → ℝ))
    (s : ℝ) : Fin d → ℝ :=
  c ⟨max 0 (min T s), le_max_left _ _, max_le hT (min_le_left _ _)⟩

@[fun_prop] theorem continuous_extendPath {T : ℝ} (hT : 0 ≤ T)
    (c : C(Icc (0 : ℝ) T, Fin d → ℝ)) : Continuous (extendPath hT c) := by
  unfold extendPath
  exact c.continuous.comp
    ((continuous_const.max (continuous_const.min continuous_id)).subtype_mk _)

@[simp] theorem extendPath_of_mem {T s : ℝ} (hT : 0 ≤ T)
    (c : C(Icc (0 : ℝ) T, Fin d → ℝ)) (hs : s ∈ Icc 0 T) :
    extendPath hT c s = c ⟨s, hs⟩ := by
  simp [extendPath, min_eq_right hs.2, max_eq_right hs.1]

/-- Finite observations of the Volterra solution form a continuous linear map of the entire
continuous forcing path. This makes the use of Gaussian preservation under linear maps precise. -/
def observationCLM {k : ℕ}
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hT : 0 ≤ T)
    (hAb : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K)
    (t : Fin k → Icc (0 : ℝ) T) :
    C(Icc (0 : ℝ) T, Fin d → ℝ) →L[ℝ] (Fin k → Fin d → ℝ) where
  toFun c q := volterraSol A T (extendPath hT c) (t q)
  map_add' c c' := by
    have hsum : extendPath hT (c + c') = fun s => extendPath hT c s + extendPath hT c' s := rfl
    ext q r
    rw [hsum, volterraSol_add hA hT hAb
      (continuous_extendPath hT c) (continuous_extendPath hT c') (t q).property]
    rfl
  map_smul' a c := by
    have hsmul : extendPath hT (a • c) = fun s => a • extendPath hT c s := rfl
    ext q r
    rw [hsmul, volterraSol_smul hA hT hAb (continuous_extendPath hT c) a (t q).property]
    rfl
  cont := by
    have hLip : LipschitzWith (Real.exp ((K : ℝ) * T)).toNNReal
        (fun c : C(Icc (0 : ℝ) T, Fin d → ℝ) =>
          fun q => volterraSol A T (extendPath hT c) (t q)) := by
      refine LipschitzWith.of_dist_le_mul fun c c' => ?_
      rw [Real.coe_toNNReal _ (Real.exp_nonneg _), dist_eq_norm, dist_eq_norm]
      apply (pi_norm_le_iff_of_nonneg
        (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).2
      intro q
      have h := norm_volterraSol_sub_le hA hT K.coe_nonneg hAb
        (continuous_extendPath hT c) (continuous_extendPath hT c')
        (norm_nonneg (c - c')) (fun s _ => by
          exact ContinuousMap.norm_coe_le_norm (c - c')
            ⟨max 0 (min T s), le_max_left _ _, max_le hT (min_le_left _ _)⟩)
        (t q).property
      simpa only [Pi.sub_apply, mul_comm] using h
    exact hLip.continuous

/-- The finite-observation map evaluates the chosen solution of any continuous forcing.
Its arbitrary extension outside the horizon does not affect the observations. -/
theorem observationCLM_apply {k : ℕ}
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} {K : ℝ≥0}
    (hA : Continuous A) (hT : 0 ≤ T)
    (hAb : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K)
    (t : Fin k → Icc (0 : ℝ) T) {G : ℝ → Fin d → ℝ} (hG : Continuous G) :
    observationCLM hA hT hAb t ⟨fun s => G s, hG.comp continuous_subtype_val⟩ =
      fun q => volterraSol A T G (t q) := by
  ext q r
  have h := norm_volterraSol_sub_le hA hT K.coe_nonneg hAb
    (continuous_extendPath hT ⟨fun s => G s, hG.comp continuous_subtype_val⟩)
    hG (le_refl (0 : ℝ)) (fun s hs => by simp [extendPath_of_mem hT _ hs]) (t q).property
  have heq : volterraSol A T
      (extendPath hT ⟨fun s => G s, hG.comp continuous_subtype_val⟩) (t q) =
      volterraSol A T G (t q) := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using h) (norm_nonneg _)
  exact congrFun heq r

/-- The evolution matrix is defined from the actual Volterra solver, column by column.
`T` is an outer construction horizon, and `s` is the initial time. -/
def fundamentalMatrix
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T t s : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => volterraSol (fun r => A (s + r)) (T - s)
    (fun _ => Pi.single j 1) (t - s) i

/-- Every column satisfies the translated homogeneous evolution equation. -/
theorem fundamentalMatrix_column_solution
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s : ℝ}
    (hA : Continuous A) (hs : s ≤ T) (j : Fin d) :
    Analysis.LinearVolterra.IsSolution (fun r => A (s + r))
      (fun _ => Pi.single j 1)
      (fun r => fun i => fundamentalMatrix A T (s + r) s i j) (T - s) := by
  simpa only [fundamentalMatrix, add_sub_cancel_left] using
    (volterraSol_spec (hA.comp (continuous_const.add continuous_id))
      continuous_const (sub_nonneg.mpr hs) :
      Analysis.LinearVolterra.IsSolution (fun r => A (s + r))
        (fun _ => Pi.single j 1)
        (volterraSol (fun r => A (s + r)) (T - s) (fun _ => Pi.single j 1)) (T - s))

/-- The evolution matrix starts at the identity. -/
theorem fundamentalMatrix_diagonal
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T s : ℝ}
    (hA : Continuous A) (hs : s ≤ T) : fundamentalMatrix A T s s = 1 := by
  ext i j
  have h := (fundamentalMatrix_column_solution hA hs j).equation 0
    ⟨le_rfl, sub_nonneg.mpr hs⟩
  have hc := congrFun h i
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using hc

end VolterraGaussian


namespace GaussianContinuousPath

open Filter
open scoped unitInterval

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A finite list of observations of a Gaussian process, allowing repeated times. -/
theorem finiteList {S : Type*} {X : S → Ω → ℝ} (hX : IsGaussianProcess X P)
    {n : ℕ} (t : Fin n → S) : HasGaussianLaw (fun ω j => X (t j) ω) P := by
  let h := (hX.comp_right t).hasGaussianLaw (Finset.univ : Finset (Fin n))
  let L : ({j // j ∈ (Finset.univ : Finset (Fin n))} → ℝ) →L[ℝ] (Fin n → ℝ) :=
    { toFun x j := x ⟨j, Finset.mem_univ j⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      cont := by fun_prop }
  simpa only [L, Function.comp_apply, Finset.restrict_def] using h.map_fun L

/-- Reconstruction of a Bernstein polynomial from its finite list of samples. -/
def bernsteinAssembly (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] C(I, ℝ) :=
  ∑ k : Fin (n + 1),
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k).smulRight
      (bernstein n k)

theorem bernsteinAssembly_samples (n : ℕ) (f : C(I, ℝ)) :
    bernsteinAssembly n (fun k => f (bernstein.z k)) = bernsteinApproximation n f := by
  ext x
  rw [bernsteinApproximation.apply]
  simp [bernsteinAssembly, mul_comm]

/-- Bernstein approximation does not increase the path norm. -/
theorem norm_bernsteinApproximation_le (n : ℕ) (f : C(I, ℝ)) :
    ‖bernsteinApproximation n f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro x
  rw [bernsteinApproximation.apply]
  calc
    ‖∑ k : Fin (n + 1), bernstein n k x • f (bernstein.z k)‖ ≤
        ∑ k : Fin (n + 1), ‖bernstein n k x • f (bernstein.z k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin (n + 1), bernstein n k x * ‖f‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg bernstein_nonneg]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) bernstein_nonneg
    _ = ‖f‖ := by rw [← Finset.sum_mul, bernstein.probability, one_mul]

/-- A continuous path with centered jointly Gaussian finite-dimensional observations and
square-integrable uniform norm has a centered Gaussian law under every continuous linear form.
The centering and the variance are derived, rather than included among the premises. -/
theorem dual_law
    {Z : Ω → C(I, ℝ)} (hZ : Measurable Z) (hZtwo : MemLp Z 2 P)
    (hfinite : ∀ n, HasGaussianLaw
      (fun ω (j : Fin (n + 1)) => Z ω (bernstein.z j)) P)
    (hmean : ∀ t : I, ∫ ω, Z ω t ∂P = 0)
    (L : C(I, ℝ) →L[ℝ] ℝ) :
    HasLaw (fun ω => L (Z ω))
      (gaussianReal 0 (∫ ω, (L (Z ω)) ^ 2 ∂P).toNNReal) P := by
  let X : ℕ → Ω → ℝ := fun n ω => L (bernsteinApproximation n (Z ω))
  have hform (n : ℕ) : X n = fun ω =>
      ∑ k : Fin (n + 1), Z ω (bernstein.z k) * L (bernstein n k) := by
    funext ω
    have hb : bernsteinApproximation n (Z ω) =
        ∑ k : Fin (n + 1), Z ω (bernstein.z k) • bernstein n k := by
      ext x
      rw [bernsteinApproximation.apply]
      simp [mul_comm]
    simp only [X, hb, map_sum, map_smul, smul_eq_mul]
  have hgauss (n : ℕ) : HasGaussianLaw (X n) P := by
    simpa only [X, ContinuousLinearMap.coe_comp', Function.comp_apply,
      bernsteinAssembly_samples] using
      (hfinite n).map_fun (L.comp (bernsteinAssembly n))
  have hXm (n : ℕ) : Measurable (X n) := by
    rw [hform]
    exact Finset.measurable_sum _ fun k _ =>
      (((ContinuousMap.evalCLM ℝ (bernstein.z k)).continuous.measurable.comp hZ).mul_const _)
  have hXmzero (n : ℕ) : ∫ ω, X n ω ∂P = 0 := by
    rw [hform, integral_finsetSum Finset.univ (fun k _ =>
      ((hfinite n).eval k).integrable.mul_const (L (bernstein n k)))]
    simp_rw [integral_mul_const, hmean, zero_mul]
    simp
  have hlaw (n : ℕ) : HasLaw (X n)
      (gaussianReal 0 (Var[X n; P]).toNNReal) P := by
    refine ⟨(hgauss n).aemeasurable, ?_⟩
    simpa only [hXmzero] using (hgauss n).map_eq_gaussianReal
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (L (Z ω))) := by
    exact Filter.Eventually.of_forall fun ω =>
      L.continuous.continuousAt.tendsto.comp (bernsteinApproximation_uniform (Z ω))
  have hD : Integrable (fun ω => (‖L‖ * ‖Z ω‖) ^ 2) P :=
    (hZtwo.norm.const_mul ‖L‖).integrable_sq
  apply centeredGaussian_law_of_dominated_ae_tendsto hXm hlaw hlim hD
  intro n
  refine Filter.Eventually.of_forall fun ω => ?_
  have h1 : ‖X n ω‖ ≤ ‖L‖ * ‖Z ω‖ := (L.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_bernsteinApproximation_le n (Z ω)) (norm_nonneg L))
  rwa [Real.norm_eq_abs] at h1

/-- The resulting Banach-valued Gaussian law is stronger than separate Gaussian marginal laws. -/
theorem gaussian
    {Z : Ω → C(I, ℝ)} (hZ : Measurable Z) (hZtwo : MemLp Z 2 P)
    (hfinite : ∀ n, HasGaussianLaw
      (fun ω (j : Fin (n + 1)) => Z ω (bernstein.z j)) P)
    (hmean : ∀ t : I, ∫ ω, Z ω t ∂P = 0) : HasGaussianLaw Z P := by
  refine ⟨isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
  refine ⟨0, (∫ ω, (L (Z ω)) ^ 2 ∂P).toNNReal, ?_⟩
  rw [Measure.map_map L.continuous.measurable hZ]
  exact (dual_law hZ hZtwo hfinite hmean L).map_eq

end GaussianContinuousPath


open Ripple.Stochastic Ripple.Stochastic.AdaptedContinuousSpace
open Ripple.Stochastic.ContinuousItoConstruction Ripple.Stochastic.ContinuousItoElementary

/-- The actual channel Brownian motion as a random continuous path on a real interval. -/
def brownianPath {m : ℕ} (T : ℝ≥0) (l : Fin m)
    (ω : channelKMTSpace (Fin m)) : C(Icc (0 : ℝ) (T : ℝ), ℝ) :=
  ⟨fun t => channelKMTBrownian l t ω,
    (channelKMTBrownian_continuous l ω).comp continuous_subtype_val⟩

/-- Compact Brownian paths are measurable as path-valued random variables. -/
theorem measurable_brownianPath {m : ℕ} (T : ℝ≥0) (l : Fin m) :
    Measurable (brownianPath T l) := by
  letI : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, le_rfl, T.coe_nonneg⟩⟩
  exact (stronglyMeasurable_of_evaluations (brownianPath T l)
    (fun t => measurable_channelKMTBrownian l t)).measurable

/-- Doob's existing elementary integral bound supplies the uniform Brownian path L² norm. -/
theorem memLp_brownianPath {m : ℕ} (T : ℝ≥0) (l : Fin m) :
    MemLp (brownianPath T l) 2 (channelKMTMeasure (Fin m)) := by
  letI := channelBrownian_isFilteredPreBrownian l
  let hB := channelBrownian_continuous l
  let hBm := measurable_channelBrownian l
  let V := (FilteredItoIntegralCLM.iocSP_T
    (𝓖 := channelBrownianFiltration) hBm (zero_le : (0 : ℝ≥0) ≤ T) le_rfl
    (F := Set.univ) (@MeasurableSet.univ (channelKMTSpace (Fin m))
      (channelBrownianFiltration 0))).val
  have hmem := simpleIntegralPath_memLp (μ := channelKMTMeasure (Fin m)) T hB hBm V
  apply hmem.mono (measurable_brownianPath T l).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  let tn : Icc (0 : ℝ≥0) T :=
    ⟨t.val.toNNReal, zero_le, Real.toNNReal_le_iff_le_coe.2 t.property.2⟩
  have heq : simpleIntegralPath T hB V ω tn = brownianPath T l ω t := by
    rw [simpleIntegralPath_apply T hB hBm]
    dsimp only [V]
    rw [DeterministicItoBridge.itoSimpleProcess_iocSP]
    simp only [min_eq_right tn.property.2, min_eq_left (zero_le : (0 : ℝ≥0) ≤ (tn : ℝ≥0)),
      channelBrownian, NNReal.coe_zero, channelKMTBrownian_zero_start, sub_zero, brownianPath,
      ContinuousMap.coe_mk]
    congr 1
    exact Real.coe_toNNReal _ t.property.1
  rw [← heq]
  exact ContinuousMap.norm_coe_le_norm _ tn

/-- Rescale a compact Brownian path to the unit interval, for Bernstein approximation. -/
def unitBrownianPath {m : ℕ} (T : ℝ≥0) (l : Fin m)
    (ω : channelKMTSpace (Fin m)) : C(unitInterval, ℝ) :=
  ⟨fun t => channelBrownian l ⟨T * t, mul_nonneg T.coe_nonneg t.property.1⟩ ω,
    (channelBrownian_continuous l ω).comp
      ((continuous_const.mul continuous_subtype_val).subtype_mk _)⟩

theorem gaussian_unitBrownianPath {m : ℕ} (T : ℝ≥0) (l : Fin m) :
    HasGaussianLaw (unitBrownianPath T l) (channelKMTMeasure (Fin m)) := by
  have hmeas : Measurable (unitBrownianPath T l) :=
    (stronglyMeasurable_of_evaluations (unitBrownianPath T l)
      (fun t => measurable_channelBrownian l _)).measurable
  have htwo : MemLp (unitBrownianPath T l) 2 (channelKMTMeasure (Fin m)) := by
    apply (memLp_brownianPath T l).mono hmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro t
    let r : Icc (0 : ℝ) (T : ℝ) :=
      ⟨T * t, mul_nonneg T.coe_nonneg t.property.1,
        (mul_le_mul_of_nonneg_left t.property.2 T.coe_nonneg).trans_eq (mul_one _)⟩
    exact ContinuousMap.norm_coe_le_norm (brownianPath T l ω) r
  apply GaussianContinuousPath.gaussian hmeas htwo
  · intro n
    exact GaussianContinuousPath.finiteList
      (channelBrownian_isPreBrownian l).isGaussianProcess
      (fun j => ⟨T * (bernstein.z j : ℝ),
        mul_nonneg T.coe_nonneg (bernstein.z j).property.1⟩)
  · intro t
    exact (channelBrownian_isPreBrownian l).integral_eval _

/-- Brownian paths have Gaussian laws in the uniform Banach path space, including a zero horizon. -/
theorem brownianPath_gaussian {m : ℕ} (T : ℝ≥0) (l : Fin m) :
    HasGaussianLaw (brownianPath T l) (channelKMTMeasure (Fin m)) := by
  by_cases hT : T = 0
  · subst T
    have hz : brownianPath 0 l = fun _ => (0 : C(Icc (0 : ℝ) (0 : ℝ), ℝ)) := by
      funext ω
      ext t
      have ht : t.val = 0 := le_antisymm t.property.2 t.property.1
      show channelKMTBrownian l (t : ℝ) ω = 0
      rw [ht, channelKMTBrownian_zero_start]
    rw [hz]
    refine ⟨?_⟩
    rw [Measure.map_const, measure_univ, one_smul]
    infer_instance
  · have hTpos : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT)
    let scale : C(Icc (0 : ℝ) (T : ℝ), unitInterval) :=
      ⟨fun t => ⟨t.val / T, div_nonneg t.property.1 T.coe_nonneg,
          (div_le_one hTpos).2 t.property.2⟩,
        (continuous_subtype_val.div_const _).subtype_mk _⟩
    let L := ContinuousMap.compCLM ℝ ℝ scale
    have heq : (fun ω => L (unitBrownianPath T l ω)) = brownianPath T l := by
      funext ω
      ext t
      have hm : (T : ℝ) * (t.val / T) = t.val := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hTpos)]
      simp only [L, ContinuousMap.compCLM_apply, ContinuousMap.comp_apply,
        unitBrownianPath, ContinuousMap.coe_mk, scale, hm, channelBrownian, brownianPath]
      rfl
    rw [← heq]
    exact (gaussian_unitBrownianPath T l).map_fun L

/-- The original product construction makes the whole compact Brownian paths independent. -/
theorem brownianPath_independent {m : ℕ} (T : ℝ≥0) :
    iIndepFun (brownianPath (m := m) T) (channelKMTMeasure (Fin m)) := by
  letI : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, le_rfl, T.coe_nonneg⟩⟩
  let F : AllTimeKMT.AllTimeKMTSpace → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun ω =>
    ⟨fun t => AllTimeKMT.allTimeKMTBrownian t ω,
      (AllTimeKMTLaws.allTimeKMTBrownian_continuous ω).comp continuous_subtype_val⟩
  have hF : Measurable F := by
    exact (stronglyMeasurable_of_evaluations F
      (fun t => AllTimeKMT.measurable_allTimeKMTBrownian t)).measurable
  exact channelKMTEval_iIndep.comp (fun _ => F) (fun _ => hF)

/-- Joint Gaussian law of all actual compact Brownian paths. -/
theorem brownianPath_joint_gaussian {m : ℕ} (T : ℝ≥0) :
    HasGaussianLaw (fun ω (l : Fin m) => brownianPath T l ω)
      (channelKMTMeasure (Fin m)) :=
  (brownianPath_independent T).hasGaussianLaw (brownianPath_gaussian T)

/-- The actual path-vector Gaussian law is centered in the Banach space. -/
theorem brownianPath_joint_mean {m : ℕ} (T : ℝ≥0) :
    ∫ ω, (fun l : Fin m => brownianPath T l ω) ∂channelKMTMeasure (Fin m) = 0 := by
  ext l t
  let L : (Fin m → C(Icc (0 : ℝ) (T : ℝ), ℝ)) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ t).comp (ContinuousLinearMap.proj l)
  change L (∫ ω, (fun l : Fin m => brownianPath T l ω)
    ∂channelKMTMeasure (Fin m)) = 0
  rw [← L.integral_comp_comm (brownianPath_joint_gaussian T).integrable]
  have ht : ((t.val.toNNReal : ℝ≥0) : ℝ) = t.val := Real.coe_toNNReal _ t.property.1
  simpa only [L, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousMap.evalCLM_apply, ContinuousLinearMap.proj_apply, brownianPath,
    ContinuousMap.coe_mk, channelBrownian, ht] using
      (channelBrownian_isPreBrownian l).integral_eval t.val.toNNReal


/-- Extend a scalar compact path by clamping time to its interval. -/
def scalarExtend (T : ℝ≥0) (c : C(Icc (0 : ℝ) (T : ℝ), ℝ)) (s : ℝ) : ℝ :=
  c ⟨max 0 (min T s), le_max_left _ _, max_le T.coe_nonneg (min_le_left _ _)⟩

@[fun_prop] theorem continuous_scalarExtend (T : ℝ≥0)
    (c : C(Icc (0 : ℝ) (T : ℝ), ℝ)) : Continuous (scalarExtend T c) := by
  unfold scalarExtend
  exact c.continuous.comp
    ((continuous_const.max (continuous_const.min continuous_id)).subtype_mk _)

@[simp] theorem scalarExtend_of_mem (T : ℝ≥0)
    (c : C(Icc (0 : ℝ) (T : ℝ), ℝ)) {s : ℝ} (hs : s ∈ Icc 0 (T : ℝ)) :
    scalarExtend T c s = c ⟨s, hs⟩ := by
  simp [scalarExtend, min_eq_right hs.2, max_eq_right hs.1]

/-- The pathwise deterministic Wiener functional is a continuous linear map on compact paths. -/
def JPathCLM (T : ℝ≥0) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) :
    C(Icc (0 : ℝ) (T : ℝ), ℝ) →L[ℝ] C(Icc (0 : ℝ) (T : ℝ), ℝ) where
  toFun c :=
    ⟨fun t => Analysis.BVIntegrationByParts.J a (scalarExtend T c) t,
      (Analysis.BVIntegrationByParts.continuousOn_J T.coe_nonneg ha
        (continuous_scalarExtend T c).continuousOn).comp_continuous
          continuous_subtype_val (fun t => t.property)⟩
  map_add' c c' := by
    ext t
    exact Analysis.BVIntegrationByParts.J_add t.property.1
      (ha.mono (fun s hs => ⟨hs.1, hs.2.trans t.property.2⟩))
      (continuous_scalarExtend T c).continuousOn (continuous_scalarExtend T c').continuousOn
  map_smul' b c := by
    ext t
    exact Analysis.BVIntegrationByParts.J_const_mul a (scalarExtend T c) b t
  cont := by
    let B : ℝ := |a 0| + 2 * (K : ℝ) * T
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hab (t : Icc (0 : ℝ) (T : ℝ)) : |a t| + (K : ℝ) * t ≤ B := by
      have hd := ha.dist_le_mul (t : ℝ) t.property 0 ⟨le_rfl, T.coe_nonneg⟩
      rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg t.property.1] at hd
      have hmul := mul_le_mul_of_nonneg_left t.property.2 K.coe_nonneg
      have habs : |a t| ≤ |a t - a 0| + |a 0| := by
        simpa only [sub_add_cancel] using abs_add_le (a t - a 0) (a 0)
      dsimp [B]
      linarith
    have hLip : LipschitzWith B.toNNReal
        (fun c : C(Icc (0 : ℝ) (T : ℝ), ℝ) =>
          (⟨fun t => Analysis.BVIntegrationByParts.J a (scalarExtend T c) t,
            (Analysis.BVIntegrationByParts.continuousOn_J T.coe_nonneg ha
              (continuous_scalarExtend T c).continuousOn).comp_continuous
                continuous_subtype_val (fun t => t.property)⟩ :
              C(Icc (0 : ℝ) (T : ℝ), ℝ))) := by
      refine LipschitzWith.of_dist_le_mul fun c c' => ?_
      rw [Real.coe_toNNReal _ hB, dist_eq_norm, dist_eq_norm]
      apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg _))).2
      intro t
      have h := Analysis.BVIntegrationByParts.abs_J_sub_le t.property.1
        (ha.mono (fun s hs => ⟨hs.1, hs.2.trans t.property.2⟩))
        (continuous_scalarExtend T c).continuousOn (continuous_scalarExtend T c').continuousOn
        (norm_nonneg (c - c')) (fun s _ => by
          exact ContinuousMap.norm_coe_le_norm (c - c')
            ⟨max 0 (min T s), le_max_left _ _, max_le T.coe_nonneg (min_le_left _ _)⟩)
      exact h.trans (mul_le_mul_of_nonneg_right (hab t) (norm_nonneg _))
    exact hLip.continuous

@[simp] theorem JPathCLM_apply (T : ℝ≥0) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ)))
    (c : C(Icc (0 : ℝ) (T : ℝ), ℝ)) (t : Icc (0 : ℝ) (T : ℝ)) :
    JPathCLM T ha c t = Analysis.BVIntegrationByParts.J a (scalarExtend T c) t := rfl

/-- The clamped extension used by the path map agrees with the original Brownian path
on every integration interval involved in an observation before the horizon. -/
theorem JPathCLM_brownianPath {m : ℕ} (T : ℝ≥0) {a : ℝ → ℝ} {K : ℝ≥0}
    (ha : LipschitzOnWith K a (Icc 0 (T : ℝ))) (l : Fin m)
    (ω : channelKMTSpace (Fin m)) (t : Icc (0 : ℝ) (T : ℝ)) :
    JPathCLM T ha (brownianPath T l ω) t = Analysis.BVIntegrationByParts.J a
      (fun s => channelBrownian l s.toNNReal ω) t := by
  rw [JPathCLM_apply]
  have heq (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
      scalarExtend T (brownianPath T l ω) s = channelBrownian l s.toNNReal ω := by
    rw [scalarExtend_of_mem T _ hs]
    simp only [brownianPath, ContinuousMap.coe_mk, channelBrownian,
      Real.coe_toNNReal _ hs.1]
  unfold Analysis.BVIntegrationByParts.J
  rw [heq t t.property]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  dsimp only
  rw [heq s ⟨hs.1, hs.2.trans t.property.2⟩]

end Ripple.Kurtz.StrongApprox
