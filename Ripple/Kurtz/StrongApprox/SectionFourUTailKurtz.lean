import Ripple.Kurtz.StrongApprox.SectionFourRemainderBounds

/-!
# The `U_N` tail for the Kurtz diffusion on the channel space

The fluid limit `X` solves `X t = x₀ + ∫₀ᵗ F (X s) ds` with `F = tcDrift f v`, and the diffusion
`Z_N` solves the SDE `KurtzSDEPathsNN` with noise integrals
`M_l = ∫ sqrt (N f_l (Z_N)) dW_l` on the augmented channel filtration. Then

`sqrt N (Z_N - X) = Σ_l (∫ sqrt (f_l (Z_N)) dW_l) v_l + ∫₀ᵗ sqrt N (F (Z_N) - F (X))`,

since `M_l / N · sqrt N = ∫ sqrt (f_l (Z_N)) dW_l` by scalar linearity of the continuous Itô
integral. `F` is Lipschitz with constant `L = M Σ_l ‖v_l‖ ε_l` by (3.19), so Gronwall gives
`U_N ≤ e^{L T} max_i max (Sp i, Sm i)` (`sectionFour_U_bound_of_continuous`), where `Sp`, `Sm`
are the suprema of the two signed coordinate channel sums.

When `Z_N` has only almost surely continuous paths, the modification that vanishes on a null
set of the augmented filtration has the same noise integrals and the same `U_N` almost surely.

`sectionFour_U_tail_kurtz`: for every `N ≥ 2` and `r ≥ 0`,
`P (r < U_N) ≤ a_U exp (-b_U r²)` with `a_U = 2 max (1, d)` and `b_U = 1 / (2 e^{2 L T} Q)`
for any `Q ≥ T Σ_l ‖v_l‖² ε_l`, `Q > 0`; the constants do not depend on `N`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic Ripple.Stochastic.ContinuousItoLinear
open Ripple.Stochastic.ContinuousAdaptedIntegrand Ripple.Stochastic.FilteredItoIntegralCLM
open Ripple.Stochastic.FilteredItoIntegralL2
open SectionFourAssembly

/-! ## The drift -/

section Drift

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- The Lipschitz constant `M Σ_l ‖v_l‖ ε_l` of the drift `tcDrift f v`. -/
def kurtzDriftLip (v : ι → Fin d → ℝ) (eps : ι → ℝ) (M : ℝ) : ℝ :=
  M * ∑ l, ‖v l‖ * eps l

theorem kurtzDriftLip_nonneg {v : ι → Fin d → ℝ} {eps : ι → ℝ} {M : ℝ}
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M) : 0 ≤ kurtzDriftLip v eps M :=
  mul_nonneg hM (Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) (heps l))

theorem norm_tcDrift_sub_le {f : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ} {eps : ι → ℝ}
    {M : ℝ} (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (x y : Fin d → ℝ) :
    ‖tcDrift f v x - tcDrift f v y‖ ≤ kurtzDriftLip v eps M * ‖x - y‖ := by
  unfold tcDrift kurtzDriftLip
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  calc |f l x - f l y| * ‖v l‖ ≤ eps l * M * ‖x - y‖ * ‖v l‖ :=
        mul_le_mul_of_nonneg_right (h319 l x y) (norm_nonneg _)
    _ = M * (‖v l‖ * eps l) * ‖x - y‖ := by ring

omit [Fintype ι] in
theorem continuous_rate_of_lip {f : ι → (Fin d → ℝ) → ℝ} {eps : ι → ℝ} {M : ℝ}
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (l : ι) : Continuous (f l) := by
  have hK : 0 ≤ eps l * M := mul_nonneg (heps l) hM
  have hL : LipschitzWith (eps l * M).toNNReal (f l) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.coe_toNNReal _ hK, Real.dist_eq, dist_eq_norm]
    exact h319 l x y
  exact hL.continuous

theorem continuous_tcDrift {f : ι → (Fin d → ℝ) → ℝ} (hf : ∀ l, Continuous (f l))
    (v : ι → Fin d → ℝ) : Continuous (tcDrift f v) := by
  unfold tcDrift
  exact continuous_finsetSum _ fun l _ => (hf l).smul continuous_const

end Drift

/-! ## Null sets of the filtration are null for the predictable trim -/

section TrimNull

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem ae_trim_notMem {N0 : Set Ω} (hNF : ∀ t, MeasurableSet[F t] N0) (hN0 : μ N0 = 0)
    (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    ∀ᵐ z ∂trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas, z.2 ∉ N0 := by
  let G : ℝ≥0 → Ω → ℝ := fun _ => N0.indicator fun _ => (1 : ℝ)
  have hGa : ∀ t, Measurable[F t] (G t) := fun t => measurable_const.indicator (hNF t)
  have hGm : Measurable[F.predictable] (Function.uncurry G) :=
    (stronglyMeasurable_uncurry hGa (fun _ => continuous_const)).measurable
  have hset : (Set.univ : Set ℝ≥0) ×ˢ N0 = Function.uncurry G ⁻¹' {1} := by
    ext z
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage, Set.mem_singleton_iff,
      G, Function.uncurry]
    by_cases hz : z.2 ∈ N0
    · simp [hz]
    · simp [hz]
  have hpred : MeasurableSet[F.predictable] ((Set.univ : Set ℝ≥0) ×ˢ N0) := by
    rw [hset]
    exact hGm (measurableSet_singleton 1)
  have hzero : trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas ((Set.univ : Set ℝ≥0) ×ˢ N0) = 0 := by
    show ((timeMeasure_T T).prod μ).trim F.predictable_le_prod _ = 0
    rw [trim_measurableSet_eq _ hpred, Measure.prod_prod, hN0, mul_zero]
  refine ae_iff.2 (measure_mono_null ?_ hzero)
  intro z hz
  exact ⟨Set.mem_univ _, not_not.1 hz⟩

variable [IsFilteredPreBrownian B F μ]

/-- Integrands that agree off a null set of the filtration have the same continuous integral. -/
theorem continuousItoOfFun_congr_of_null {N0 : Set Ω} (hNF : ∀ t, MeasurableSet[F t] N0)
    (hN0 : μ N0 = 0) (T : ℝ≥0) (hB : ∀ ω, Continuous (fun t => B t ω))
    (hBmeas : ∀ t, Measurable (B t)) {H G : ℝ≥0 → Ω → ℝ}
    (hH : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hG : MemLp (Function.uncurry G) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hHG : ∀ s ω, ω ∉ N0 → H s ω = G s ω) :
    continuousItoOfFun μ F T hB hBmeas H = continuousItoOfFun μ F T hB hBmeas G := by
  rw [continuousItoOfFun_of_memLp T hB hBmeas hH, continuousItoOfFun_of_memLp T hB hBmeas hG,
    MemLp.toLp_congr hH hG ((ae_trim_notMem hNF hN0 T hBmeas).mono fun z hz => hHG z.1 z.2 hz)]

end TrimNull

/-! ## The channel space -/

section Channel

attribute [local instance] channelBrownian_isFilteredPreBrownian_augmented

variable {m d : ℕ}

/-- The noise integrals `∫ sqrt (N f_l (Z)) dW_l` of the SDE on the channel space. -/
def channelRateIntegral (T : ℝ≥0) (N : ℕ) (f : Fin m → (Fin d → ℝ) → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (l : Fin m) :
    ℝ≥0 → channelKMTSpace (Fin m) → ℝ :=
  continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
    (channelBrownian_continuous l) (measurable_channelBrownian l)
    (fun s ω => Real.sqrt ((N : ℝ) * f l (Z s ω)))

/-- The integrals `∫ sqrt (f_l (Z)) dW_l`. -/
def channelSqrtIntegral (T : ℝ≥0) (f : Fin m → (Fin d → ℝ) → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (l : Fin m) :
    ℝ≥0 → channelKMTSpace (Fin m) → ℝ :=
  continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
    (channelBrownian_continuous l) (measurable_channelBrownian l)
    (fun s ω => Real.sqrt (f l (Z s ω)))

variable {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ} {M : ℝ}

/-- (U1) for a diffusion with continuous paths: almost surely,
`U_N ≤ e^{L T} c` whenever all signed coordinate suprema are at most `c`. -/
theorem sectionFour_U_bound_of_continuous {N : ℕ} (hN : 0 < N)
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M) (hf : ∀ l, Continuous (f l))
    (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    {T : ℝ≥0} {x0 : Fin d → ℝ} {X : ℝ≥0 → Fin d → ℝ} (hX : Continuous X)
    (hXeq : ∀ t ≤ T, X t = x0 + ∫ s in (0 : ℝ)..(t : ℝ), tcDrift f v (X s.toNNReal))
    {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω)
    (hSDE : ∀ᵐ ω ∂channelKMTMeasure (Fin m), KMTTransfer.KurtzSDEPathsNN N f v T Z
      (channelRateIntegral T N f Z) (fun _ => x0) ω) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ c : ℝ, 0 ≤ c →
      (∀ i, sectionFourSup v f eps Z hf hfB hZa hZc T false i ω ≤ c ∧
        sectionFourSup v f eps Z hf hfB hZa hZc T true i ω ≤ c) →
      sectionFourRemainderU N X Z T ω ≤ Real.exp (kurtzDriftLip v eps M * T) * c := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hL := kurtzDriftLip_nonneg (v := v) heps hM
  have hmem : ∀ l, MemLp (Function.uncurry fun s ω => Real.sqrt (f l (Z s ω))) 2
      (trimMeasure_T (𝓖 := augmentedChannelBrownianFiltration)
        (μ := channelKMTMeasure (Fin m)) T (measurable_channelBrownian l)) := fun l =>
    memLp_sqrt_rate T (measurable_channelBrownian l) (hf l) (hfB l) hZa hZc
  have hJc : ∀ l ω, Continuous fun t => channelSqrtIntegral T f Z l t ω := by
    intro l ω
    unfold channelSqrtIntegral
    rw [continuousItoOfFun_of_memLp T _ _ (hmem l)]
    exact continuous_continuousItoNN T _ _ _ ω
  have hscale : ∀ l, ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t,
      channelRateIntegral T N f Z l t ω = Real.sqrt N * channelSqrtIntegral T f Z l t ω := by
    intro l
    have hfun : (fun s ω => Real.sqrt ((N : ℝ) * f l (Z s ω))) =
        fun s ω => Real.sqrt N * Real.sqrt (f l (Z s ω)) := by
      funext s ω
      exact Real.sqrt_mul (Nat.cast_nonneg N) _
    unfold channelRateIntegral channelSqrtIntegral
    rw [hfun]
    exact continuousItoOfFun_const_mul T _ _ (hmem l) _
  have hsign : ∀ p : Bool × Fin d × Fin m, ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t,
      continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous p.2.2) (measurable_channelBrownian p.2.2)
          (sectionFourSignedIntegrand v f Z p.1 p.2.1 p.2.2) t ω =
        ((if p.1 then -1 else 1) * v p.2.2 p.2.1) * channelSqrtIntegral T f Z p.2.2 t ω := by
    rintro ⟨neg, i, l⟩
    dsimp only
    have hfun : sectionFourSignedIntegrand v f Z neg i l =
        fun s ω => ((if neg then -1 else 1) * v l i) * Real.sqrt (f l (Z s ω)) := by
      funext s ω
      unfold sectionFourSignedIntegrand sectionFourIntegrand
      ring
    rw [hfun]
    exact continuousItoOfFun_const_mul T _ _ (hmem l) _
  filter_upwards [hSDE, ae_all_iff.2 hscale, ae_all_iff.2 hsign] with ω hsde hsc hsg c hc hSpm
  obtain ⟨-, hZeq⟩ := hsde
  have hFc := continuous_tcDrift hf v
  -- Gronwall for `D = sqrt N (Z - X)`
  have hgron := pathSupIcc_le_gronwall (T := (T : ℝ)) (L := kurtzDriftLip v eps M)
    T.coe_nonneg hL (ω := ω)
    (D := fun t ω => Real.sqrt N • (Z t.toNNReal ω - X t.toNNReal))
    (M := fun t ω => ∑ l, channelSqrtIntegral T f Z l t.toNNReal ω • v l)
    (Fd := fun t ω => Real.sqrt N •
      (tcDrift f v (Z t.toNNReal ω) - tcDrift f v (X t.toNNReal)))
    (continuous_const.smul (((hZc ω).comp continuous_real_toNNReal).sub
      (hX.comp continuous_real_toNNReal)))
    (continuous_finsetSum _ fun l _ =>
      ((hJc l ω).comp continuous_real_toNNReal).smul continuous_const).continuousOn
    (continuous_const.smul ((hFc.comp ((hZc ω).comp continuous_real_toNNReal)).sub
      (hFc.comp (hX.comp continuous_real_toNNReal)))).continuousOn
    (by
      intro t ht
      have ht' : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 ht.2
      have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.1
      have e1 := hZeq t.toNNReal ht'
      have e2 := hXeq t.toNNReal ht'
      rw [hcoe] at e1 e2
      dsimp only at e1 ⊢
      have hi1 : IntervalIntegrable (fun s => tcDrift f v (Z s.toNNReal ω)) volume 0 t :=
        (hFc.comp ((hZc ω).comp continuous_real_toNNReal)).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun s => tcDrift f v (X s.toNNReal)) volume 0 t :=
        (hFc.comp (hX.comp continuous_real_toNNReal)).intervalIntegrable _ _
      have hS : ∑ l, (channelRateIntegral T N f Z l t.toNNReal ω / (N : ℝ)) • v l =
          (Real.sqrt N)⁻¹ • ∑ l, channelSqrtIntegral T f Z l t.toNNReal ω • v l := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hsc l t.toNNReal, smul_smul]
        congr 1
        field_simp
        linear_combination channelSqrtIntegral T f Z l t.toNNReal ω * hsq
      have hinv : Real.sqrt (N : ℝ) • ((Real.sqrt N)⁻¹ •
          ∑ l, channelSqrtIntegral T f Z l t.toNNReal ω • v l) =
          ∑ l, channelSqrtIntegral T f Z l t.toNNReal ω • v l := by
        rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
      rw [e1, e2, intervalIntegral.integral_smul, intervalIntegral.integral_sub hi1 hi2, hS]
      simp only [smul_sub, smul_add, hinv]
      abel)
    (by
      intro u _
      dsimp only
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.le]
      calc Real.sqrt N * ‖tcDrift f v (Z u.toNNReal ω) - tcDrift f v (X u.toNNReal)‖
          ≤ Real.sqrt N * (kurtzDriftLip v eps M * ‖Z u.toNNReal ω - X u.toNNReal‖) :=
            mul_le_mul_of_nonneg_left (norm_tcDrift_sub_le h319 _ _) hs.le
        _ = kurtzDriftLip v eps M * (Real.sqrt N * ‖Z u.toNNReal ω - X u.toNNReal‖) := by
            ring)
  refine hgron.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  refine pathSupIcc_le_of_bound hc fun t ht => ?_
  have ht' : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 ht.2
  -- each signed channel sum at `t` is below its supremum
  have hle : ∀ (neg : Bool) (i : Fin d),
      (∑ l, continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourSignedIntegrand v f Z neg i l) t.toNNReal ω) ≤
        sectionFourSup v f eps Z hf hfB hZa hZc T neg i ω := by
    intro neg i
    have hbdd : BddAbove (range fun s : Icc (0 : ℝ≥0) T => ∑ l, channelContinuousIntegral T
        (sectionFourSignedIntegrand v f Z neg i)
        (sectionFourSignedIntegrand_adapted hf hZa neg i)
        (sectionFourSignedIntegrand_continuous hf hZc neg i)
        (sectionFourIntegrandBound v eps)
        (abs_sectionFourSignedIntegrand_le hfB neg i) l ω s) :=
      (isCompact_range (continuous_finsetSum _ fun l _ =>
        (channelContinuousIntegral T _ _ _ _ _ l ω).continuous)).bddAbove
    unfold sectionFourSup
    refine le_trans (le_of_eq ?_) (le_ciSup hbdd ⟨t.toNNReal, zero_le, ht'⟩)
    refine Finset.sum_congr rfl fun l _ => ?_
    exact (channelContinuousIntegral_eq_continuousItoOfFun T _ _ _ _ _ l ω
      ⟨t.toNNReal, zero_le, ht'⟩).symm
  refine (pi_norm_le_iff_of_nonneg hc).2 fun i => ?_
  have hp := hle false i
  have hm := hle true i
  have hvF : (∑ l, continuousItoOfFun (channelKMTMeasure (Fin m))
      augmentedChannelBrownianFiltration T (channelBrownian_continuous l)
      (measurable_channelBrownian l) (sectionFourSignedIntegrand v f Z false i l) t.toNNReal ω) =
      ∑ l, channelSqrtIntegral T f Z l t.toNNReal ω * v l i := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsg ⟨false, i, l⟩ t.toNNReal, if_neg Bool.false_ne_true]
    ring
  have hvT : (∑ l, continuousItoOfFun (channelKMTMeasure (Fin m))
      augmentedChannelBrownianFiltration T (channelBrownian_continuous l)
      (measurable_channelBrownian l) (sectionFourSignedIntegrand v f Z true i l) t.toNNReal ω) =
      -∑ l, channelSqrtIntegral T f Z l t.toNNReal ω * v l i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsg ⟨true, i, l⟩ t.toNNReal, if_pos rfl]
    ring
  rw [hvF] at hp
  rw [hvT] at hm
  have hcoord : (∑ l, channelSqrtIntegral T f Z l t.toNNReal ω • v l) i =
      ∑ l, channelSqrtIntegral T f Z l t.toNNReal ω * v l i := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcoord, Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith [(hSpm i).2], by linarith [(hSpm i).1]⟩

/-- A version continuous for every sample, equal to `Z` off a null set of the filtration. -/
theorem exists_null_continuity_set {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZc : ∀ᵐ ω ∂channelKMTMeasure (Fin m), Continuous fun t => Z t ω) :
    ∃ N0 : Set (channelKMTSpace (Fin m)), (∀ t, MeasurableSet[augmentedChannelBrownianFiltration t] N0) ∧
      channelKMTMeasure (Fin m) N0 = 0 ∧ ∀ ω, ω ∉ N0 → Continuous fun t => Z t ω := by
  obtain ⟨N0, hsub, hmeas, h0⟩ := exists_measurable_superset_of_null (ae_iff.1 hZc)
  refine ⟨N0, fun t => augmentedChannelBrownianFiltration_null t N0 hmeas h0, h0, ?_⟩
  intro ω hω
  by_contra hnc
  exact hω (hsub hnc)

/-- **The `U_N` tail.** For every `N ≥ 2` and `r ≥ 0`,
`P (r < U_N) ≤ a_U exp (-b_U r²)`, with `a_U = 2 max (1, d)` and
`b_U = 1 / (2 e^{2 L T} Q)`, `L = M Σ_l ‖v_l‖ ε_l`, for any `Q ≥ T Σ_l ‖v_l‖² ε_l` with
`Q > 0`. The premises are the model conditions on the rates, the fluid-limit equation for `X`,
adaptedness of `Z_N`, and the SDE of `Z_N` with its continuous noise integrals. -/
theorem sectionFour_U_tail_kurtz (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    {T : ℝ≥0} {Q : ℝ} (hQ : sectionFourQZero v eps T ≤ Q) (hQpos : 0 < Q)
    {x0 : Fin d → ℝ} {X : ℝ≥0 → Fin d → ℝ} (hX : Continuous X)
    (hXeq : ∀ t ≤ T, X t = x0 + ∫ s in (0 : ℝ)..(t : ℝ), tcDrift f v (X s.toNNReal))
    {Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t))
    (hSDE : ∀ N, 2 ≤ N → ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (channelRateIntegral T N f (Z N))
        (fun _ => x0) ω) :
    ∀ N, 2 ≤ N → ∀ r : ℝ, 0 ≤ r →
      channelKMTMeasure (Fin m) {ω | r < sectionFourRemainderU N X (Z N) T ω} ≤
        ENNReal.ofReal (sectionFourAU d *
          Real.exp (-sectionFourBU (Real.exp (kurtzDriftLip v eps M * T)) Q * r ^ 2)) := by
  intro N hN r hr
  have hf := continuous_rate_of_lip heps hM h319
  have hNpos : 0 < N := by omega
  obtain ⟨N0, hNF, hN0, hcont⟩ :=
    exists_null_continuity_set ((hSDE N hN).mono fun ω h => h.1)
  -- the modification, zero on `N0`
  let Z' : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ := fun t => N0ᶜ.indicator (Z N t)
  have hagree : ∀ ω, ω ∉ N0 → ∀ t, Z' t ω = Z N t ω := fun ω hω t =>
    Set.indicator_of_mem (Set.mem_compl hω) _
  have hZ'a : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z' t) := fun t =>
    (hZa N t).indicator (hNF t).compl
  have hZ'c : ∀ ω, Continuous fun t => Z' t ω := by
    intro ω
    by_cases hω : ω ∈ N0
    · have : (fun t => Z' t ω) = fun _ => 0 := by
        funext t
        exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω) _
      rw [this]
      exact continuous_const
    · have : (fun t => Z' t ω) = fun t => Z N t ω := funext (hagree ω hω)
      rw [this]
      exact hcont ω hω
  -- the noise integrals agree
  have hrate : channelRateIntegral T N f Z' = channelRateIntegral T N f (Z N) := by
    funext l
    have hge : ∀ x, (N : ℝ) * f l x ≤ (N : ℝ) * eps l := fun x =>
      mul_le_mul_of_nonneg_left (hfB l x) (Nat.cast_nonneg N)
    have hg : Continuous fun x => (N : ℝ) * f l x := continuous_const.mul (hf l)
    exact continuousItoOfFun_congr_of_null hNF hN0 T _ _
      (memLp_sqrt_rate (g := fun x => (N : ℝ) * f l x) T (measurable_channelBrownian l) hg hge
        hZ'a hZ'c)
      (memLp_sqrt_rate_of_ae (g := fun x => (N : ℝ) * f l x) T (measurable_channelBrownian l)
        (fun t A hA h0 => augmentedChannelBrownianFiltration_null t A hA h0) hg hge (hZa N)
        ((hSDE N hN).mono fun ω h => h.1))
      (fun s ω hω => by rw [hagree ω hω s])
  have hSDE' : ∀ᵐ ω ∂channelKMTMeasure (Fin m), KMTTransfer.KurtzSDEPathsNN N f v T Z'
      (channelRateIntegral T N f Z') (fun _ => x0) ω := by
    have hnot : ∀ᵐ ω ∂channelKMTMeasure (Fin m), ω ∉ N0 := measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hSDE N hN, hnot] with ω h hω
    rw [hrate]
    have hfun := hagree ω hω
    unfold KMTTransfer.KurtzSDEPathsNN at h ⊢
    simp only [hfun]
    exact h
  have hU := sectionFour_U_bound_of_continuous hNpos heps hM hf hfB h319 hX hXeq hZ'a hZ'c hSDE'
  obtain ⟨hbr, hmaxp, hmaxm⟩ := sectionFour_U_maximal_hypotheses hf hf0 hfB hZ'a hZ'c T
  have hUeq : ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      sectionFourRemainderU N X (Z N) T ω = sectionFourRemainderU N X Z' T ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    simp only [sectionFourRemainderU, pathSupIcc, hagree ω hω]
  have htail := sectionFour_U_tail (P := channelKMTMeasure (Fin m))
    (G := Real.exp (kurtzDriftLip v eps M * T)) (Q0 := Q) (Real.exp_pos _) hQpos hU
    (fun i => (hbr i).mono fun ω h => h.trans hQ) hmaxp hmaxm hr
  refine le_trans (measure_mono_ae ?_) htail
  filter_upwards [hUeq] with ω h hω
  show r < sectionFourRemainderU N X Z' T ω
  rw [← h]
  exact hω

end Channel

end Ripple.Kurtz.StrongApprox
