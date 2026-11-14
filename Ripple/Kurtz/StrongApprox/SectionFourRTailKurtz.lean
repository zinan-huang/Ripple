import Ripple.Kurtz.StrongApprox.FluidLimitODE

/-!
# The `R_N` tail for the Kurtz diffusion on the channel space

Let `X` be the fluid limit, `F = tcDrift f v` with derivative `F'`, `‖F'‖ ≤ L₁` and
`‖F' y - F' x‖ ≤ L₂ ‖y - x‖`, and `A s = F' (X s)`. The Gaussian limit `V` solves, path by path,
the linear Volterra equation

`V t = G t + ∫₀ᵗ A s (V s) ds`,  `G t = Σ_l (∫₀ᵗ sqrt (f_l (X s)) dW_l) v_l`

(`sectionFourV`, a sum over channels of chosen Volterra solutions). Each channel term at a fixed
time is a continuous function of the continuous representative of the channel integral, so `V t`
is measurable (`measurable_sectionFourV`).

For the diffusion `Z_N`, the remainder `E_N = sqrt N (sqrt N (Z_N - X) - V)` satisfies (R1)

`E_N = H_N + ∫ A E_N + Q_N`,

with `H_N = sqrt N Σ_l (∫ sqrt (f_l (Z_N)) dW_l - ∫ sqrt (f_l (X)) dW_l) v_l` and the Taylor forcing
`Q_N = ∫ N (F (Z_N) - F (X) - A (Z_N - X))`. The linear Volterra Gronwall bound and the Taylor
bound give `R_N ≤ e^{L₁ T} (sup ‖H_N‖ + (L₂ T / 2) U_N²)` (`sectionFour_R_bound_of_continuous`),
and the coordinate suprema of the remainder channel sums control `sup ‖H_N‖`
(`sectionFourHPath_sup_le`).

`sectionFour_R_tail_kurtz`: for every `N ≥ 2` and `r ≥ 0`,
`P (r < R_N) ≤ a_R exp (-c_R r)` with `a_R = 4 max (1, d)` and
`c_R = sectionFourCR G Q Q₁ (1 + L₂ T / 2)`, `G = e^{max (L, L₁) T}`, independent of `N`.
`sectionFour_R_expMoment_kurtz` is the uniform exponential moment of order `c_R / 2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic Ripple.Stochastic.ContinuousItoLinear
open Ripple.Stochastic.ContinuousAdaptedIntegrand Ripple.Stochastic.FilteredItoIntegralCLM
open Ripple.Stochastic.FilteredItoIntegralL2
open SectionFourAssembly

/-! ## Chosen solutions of linear Volterra equations -/

section Volterra

variable {d : ℕ}

/-- A chosen solution of `V t = G t + ∫₀ᵗ A s (V s) ds` on `[0, T]`. -/
def volterraSol (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T : ℝ) (G : ℝ → Fin d → ℝ) :
    ℝ → Fin d → ℝ :=
  Classical.epsilon fun V => Analysis.LinearVolterra.IsSolution A G V T

theorem volterraSol_spec {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ}
    {G : ℝ → Fin d → ℝ} (hA : Continuous A) (hG : Continuous G) (hT : 0 ≤ T) :
    Analysis.LinearVolterra.IsSolution A G (volterraSol A T G) T :=
  Classical.epsilon_spec
    ((Analysis.LinearVolterra.exists_solution_uniqueOn hA hG hT).imp fun _ h => h.1)

theorem isSolution_finsetSum {ι : Type*} (s : Finset ι)
    {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T : ℝ} (hA : Continuous A)
    {G V : ι → ℝ → Fin d → ℝ}
    (hV : ∀ l ∈ s, Analysis.LinearVolterra.IsSolution A (G l) (V l) T) :
    Analysis.LinearVolterra.IsSolution A (fun t => ∑ l ∈ s, G l t)
      (fun t => ∑ l ∈ s, V l t) T := by
  refine ⟨continuous_finsetSum _ fun l hl => (hV l hl).continuous, fun t ht => ?_⟩
  simp only [map_sum]
  rw [intervalIntegral.integral_finsetSum fun l hl =>
    (hA.clm_apply (hV l hl).continuous).intervalIntegrable 0 t, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l hl => (hV l hl).equation t ht

theorem norm_volterraSol_sub_le {A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {T K c : ℝ}
    (hA : Continuous A) (hT : 0 ≤ T) (hK : 0 ≤ K) (hAb : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ K)
    {G H : ℝ → Fin d → ℝ} (hG : Continuous G) (hH : Continuous H) (hc : 0 ≤ c)
    (hGH : ∀ t ∈ Icc 0 T, ‖G t - H t‖ ≤ c) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖volterraSol A T G t - volterraSol A T H t‖ ≤ c * Real.exp (K * T) :=
  (Analysis.LinearVolterra.norm_sub_le_exp hA (volterraSol_spec hA hG hT)
    (volterraSol_spec hA hH hT) hT hc hK hAb hGH t ht).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK)) hc)

theorem continuous_of_fderiv_lip {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L2 : ℝ}
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖) : Continuous F' := by
  have h : LipschitzWith L2.toNNReal F' := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.coe_toNNReal _ hL2n, dist_eq_norm, dist_eq_norm]
    exact hL2 y x
  exact h.continuous

end Volterra

/-! ## The channel space -/

section Channel

attribute [local instance] channelBrownian_isFilteredPreBrownian_augmented

variable {m d : ℕ} {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {M : ℝ} {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L1 L2 : ℝ}

theorem continuous_channelSqrtIntegral {T : ℝ≥0} (hf : ∀ l, Continuous (f l))
    (hfB : ∀ l x, f l x ≤ eps l) {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (l : Fin m) (ω : channelKMTSpace (Fin m)) :
    Continuous fun t => channelSqrtIntegral T f Z l t ω := by
  unfold channelSqrtIntegral
  rw [continuousItoOfFun_of_memLp T _ _
    (memLp_sqrt_rate T (measurable_channelBrownian l) (hf l) (hfB l) hZa hZc)]
  exact continuous_continuousItoNN T _ _ _ ω

/-- The coefficient `A s = F' (X s)` of the linearized equation. -/
def sectionFourCoeff (F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ) :
    ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  fun s => F' (kurtzFluidLimit f v x0 s.toNNReal)

theorem continuous_sectionFourCoeff (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖) (x0 : Fin d → ℝ) :
    Continuous (sectionFourCoeff F' f v x0) :=
  (continuous_of_fderiv_lip hL2n hL2).comp
    ((continuous_kurtzFluidLimit heps hM hf0 hfB h319 x0).comp continuous_real_toNNReal)

/-- The Gaussian limit: the sum over channels of the Volterra solutions with forcing
`(∫₀ᵗ sqrt (f_l (X s)) dW_l) v_l`. -/
def sectionFourV (F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ) (T : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) : ℝ → Fin d → ℝ :=
  fun t => ∑ l, volterraSol (sectionFourCoeff F' f v x0) T
    (fun s => channelSqrtIntegral T f (fun s _ => kurtzFluidLimit f v x0 s) l s.toNNReal ω •
      v l) t

theorem sectionFourV_isSolution (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖) (x0 : Fin d → ℝ) (T : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) :
    Analysis.LinearVolterra.IsSolution (sectionFourCoeff F' f v x0)
      (fun t => ∑ l,
        channelSqrtIntegral T f (fun s _ => kurtzFluidLimit f v x0 s) l t.toNNReal ω • v l)
      (sectionFourV F' f v x0 T ω) T := by
  have hf := continuous_rate_of_lip heps hM h319
  have hXc := continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0
  have hAc := continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  exact isSolution_finsetSum Finset.univ hAc fun l _ => volterraSol_spec hAc
    (((continuous_channelSqrtIntegral hf hfB (fun _ => measurable_const) (fun _ => hXc) l ω).comp
      continuous_real_toNNReal).smul continuous_const) T.coe_nonneg

/-- At each time of `[0, T]` the Gaussian limit is measurable. -/
theorem measurable_sectionFourV (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖) (x0 : Fin d → ℝ)
    {T : ℝ≥0} {t : ℝ} (ht : t ∈ Icc 0 (T : ℝ)) :
    Measurable fun ω => sectionFourV F' f v x0 T ω t := by
  have hf := continuous_rate_of_lip heps hM h319
  have hXc := continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0
  have hAc := continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  have hL1n : 0 ≤ L1 := (norm_nonneg _).trans (hL1 0)
  have hAb : ∀ s ∈ Icc (0 : ℝ) T, ‖sectionFourCoeff F' f v x0 s‖ ≤ L1 := fun s _ => hL1 _
  have hterm : ∀ l, Measurable fun ω => volterraSol (sectionFourCoeff F' f v x0) T
      (fun s => channelSqrtIntegral T f (fun s _ => kurtzFluidLimit f v x0 s) l s.toNNReal ω •
        v l) t := by
    intro l
    have hm := memLp_sqrt_rate (μ := channelKMTMeasure (Fin m))
      (F := augmentedChannelBrownianFiltration) (Z := fun s _ => kurtzFluidLimit f v x0 s) T
      (measurable_channelBrownian l) (hf l) (hfB l) (fun _ => measurable_const) (fun _ => hXc)
    have hJ : channelSqrtIntegral T f (fun s _ => kurtzFluidLimit f v x0 s) l =
        continuousItoNN T (channelBrownian_continuous l) (measurable_channelBrownian l)
          (hm.toLp _) := by
      unfold channelSqrtIntegral
      exact continuousItoOfFun_of_memLp T _ _ hm
    have hGc : ∀ c : C(Icc (0 : ℝ≥0) T, ℝ), Continuous fun s : ℝ =>
        c ⟨min s.toNNReal T, zero_le, min_le_right _ _⟩ • v l := fun c =>
      (c.continuous.comp ((continuous_real_toNNReal.min continuous_const).subtype_mk _)).smul
        continuous_const
    let Ψ : C(Icc (0 : ℝ≥0) T, ℝ) → Fin d → ℝ := fun c =>
      volterraSol (sectionFourCoeff F' f v x0) T
        (fun s => c ⟨min s.toNNReal T, zero_le, min_le_right _ _⟩ • v l) t
    have hΨ : Continuous Ψ := by
      have hK : 0 ≤ ‖v l‖ * Real.exp (L1 * T) := by positivity
      have hlip : LipschitzWith (‖v l‖ * Real.exp (L1 * T)).toNNReal Ψ := by
        refine LipschitzWith.of_dist_le_mul fun c c' => ?_
        rw [Real.coe_toNNReal _ hK, dist_eq_norm, dist_eq_norm]
        have h := norm_volterraSol_sub_le hAc T.coe_nonneg hL1n hAb (hGc c) (hGc c')
          (mul_nonneg (norm_nonneg (c - c')) (norm_nonneg (v l))) (fun s _ => by
            rw [← sub_smul, norm_smul]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            simpa using ContinuousMap.norm_coe_le_norm (c - c')
              ⟨min s.toNNReal T, zero_le, min_le_right _ _⟩) ht
        calc ‖Ψ c - Ψ c'‖ ≤ ‖c - c'‖ * ‖v l‖ * Real.exp (L1 * T) := h
          _ = ‖v l‖ * Real.exp (L1 * T) * ‖c - c'‖ := by ring
      exact hlip.continuous
    have hfun : (fun ω => volterraSol (sectionFourCoeff F' f v x0) T
        (fun s => channelSqrtIntegral T f (fun s _ => kurtzFluidLimit f v x0 s) l s.toNNReal ω •
          v l) t) = fun ω => Ψ (AdaptedContinuousSpace.representative
            (ContinuousItoElementary.continuousIto T (channelBrownian_continuous l)
              (measurable_channelBrownian l)
              (hm.toLp _)) ω) := by
      rw [hJ]
      rfl
    rw [hfun]
    exact (hΨ.comp_stronglyMeasurable
      (AdaptedContinuousSpace.representative_stronglyMeasurable _)).measurable
  unfold sectionFourV
  exact Finset.measurable_sum _ fun l _ => hterm l

/-! ## The remainder and its decomposition -/

/-- `E_N t = sqrt N (sqrt N (Z_N t - X t) - V t)`. -/
def sectionFourRemainderE (N : ℕ) (F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (T : ℝ≥0) :
    ℝ → channelKMTSpace (Fin m) → Fin d → ℝ :=
  fun t ω => Real.sqrt N • (Real.sqrt N • (Z t.toNNReal ω - kurtzFluidLimit f v x0 t.toNNReal) -
    sectionFourV F' f v x0 T ω t)

/-- `R_N = sup_{q ∈ ℚ ∩ [0,T]} ‖E_N q‖`. -/
def sectionFourRemainderR (N : ℕ) (F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (T : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) : ℝ :=
  pathSupIcc (T : ℝ) (sectionFourRemainderE N F' f v x0 Z T) ω

/-- `H_N t = sqrt N Σ_l (∫ sqrt (f_l (Z)) dW_l - ∫ sqrt (f_l (X)) dW_l) v_l`. -/
def sectionFourHPath (N : ℕ) (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ)
    (X : ℝ≥0 → Fin d → ℝ) (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (T : ℝ≥0) :
    ℝ → channelKMTSpace (Fin m) → Fin d → ℝ :=
  fun t ω => Real.sqrt N • ∑ l, (channelSqrtIntegral T f Z l t.toNNReal ω -
    channelSqrtIntegral T f (fun s _ => X s) l t.toNNReal ω) • v l

/-- The Taylor forcing `Q_N t = ∫₀ᵗ N (F (Z) - F (X) - A (Z - X))`. -/
def sectionFourTaylorQ (N : ℕ) (F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) :
    ℝ → channelKMTSpace (Fin m) → Fin d → ℝ :=
  fun t ω => ∫ u in (0 : ℝ)..t, (N : ℝ) • (tcDrift f v (Z u.toNNReal ω) -
    tcDrift f v (kurtzFluidLimit f v x0 u.toNNReal) -
    sectionFourCoeff F' f v x0 u (Z u.toNNReal ω - kurtzFluidLimit f v x0 u.toNNReal))

/-- The coordinate suprema of the remainder channel sums bound `sup ‖H_N‖`. -/
theorem sectionFourHPath_sup_le {N : ℕ} {X : ℝ≥0 → Fin d → ℝ}
    {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ} (hf : ∀ l, Continuous (f l))
    (hfB : ∀ l x, f l x ≤ eps l) (hX : Continuous X)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ c : ℝ, 0 ≤ c →
      (∀ i, sectionFourRemSup N v f eps X Z hf hfB hX hZa hZc T false i ω ≤ c ∧
        sectionFourRemSup N v f eps X Z hf hfB hX hZa hZc T true i ω ≤ c) →
      pathSupIcc (T : ℝ) (sectionFourHPath N f v X Z T) ω ≤ c := by
  have hXa : ∀ t, Measurable[augmentedChannelBrownianFiltration t]
      (fun _ : channelKMTSpace (Fin m) => X t) := fun _ => measurable_const
  have hcZ : ∀ (i : Fin d) (l : Fin m), ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t,
      continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourIntegrand v f Z i l) t ω =
        v l i * channelSqrtIntegral T f Z l t ω := fun i l =>
    continuousItoOfFun_const_mul T _ _
      (memLp_sqrt_rate T (measurable_channelBrownian l) (hf l) (hfB l) hZa hZc) _
  have hcX : ∀ (i : Fin d) (l : Fin m), ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t,
      continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourIntegrand v f (fun t _ => X t) i l) t ω =
        v l i * channelSqrtIntegral T f (fun s _ => X s) l t ω := fun i l =>
    continuousItoOfFun_const_mul T _ _
      (memLp_sqrt_rate (Z := fun s _ => X s) T (measurable_channelBrownian l) (hf l) (hfB l)
        hXa (fun _ => hX)) _
  have hpos : ∀ i l, sectionFourRemSigned N v f X Z false i l =
      sectionFourRemIntegrand N v f X Z i l := by
    intro i l
    funext s ω
    simp [sectionFourRemSigned]
  have hneg : ∀ (i : Fin d) (l : Fin m), ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t,
      continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourRemSigned N v f X Z true i l) t ω =
        -1 * continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourRemSigned N v f X Z false i l) t ω := by
    intro i l
    have hfun : sectionFourRemSigned N v f X Z true i l =
        fun s ω => -1 * sectionFourRemSigned N v f X Z false i l s ω := by
      funext s ω
      simp [sectionFourRemSigned]
    rw [hfun]
    exact continuousItoOfFun_const_mul T _ _
      (integrandMemLp T (measurable_channelBrownian l) _
        (sectionFourRemSigned_adapted hf hZa false i l)
        (sectionFourRemSigned_continuous hf hX hZc false i l) _
        (abs_sectionFourRemSigned_le hfB false i l)) _
  filter_upwards [ae_all_iff.2 fun i => sectionFourRemainder_channelSum_eq (N := N) (v := v)
      hf hfB hX hZa hZc T i, ae_all_iff.2 fun i => ae_all_iff.2 (hcZ i),
    ae_all_iff.2 fun i => ae_all_iff.2 (hcX i), ae_all_iff.2 fun i => ae_all_iff.2 (hneg i)]
    with ω hsum hz hx hn c hc hTpm
  refine pathSupIcc_le_of_bound hc fun t ht => ?_
  have ht' : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 ht.2
  have hle : ∀ (neg : Bool) (i : Fin d),
      (∑ l, continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourRemSigned N v f X Z neg i l) t.toNNReal ω) ≤
        sectionFourRemSup N v f eps X Z hf hfB hX hZa hZc T neg i ω := by
    intro neg i
    have hbdd : BddAbove (range fun s : Icc (0 : ℝ≥0) T => ∑ l, channelContinuousIntegral T
        (sectionFourRemSigned N v f X Z neg i)
        (sectionFourRemSigned_adapted hf hZa neg i)
        (sectionFourRemSigned_continuous hf hX hZc neg i)
        (sectionFourRemBound N v eps)
        (abs_sectionFourRemSigned_le hfB neg i) l ω s) :=
      (isCompact_range (continuous_finsetSum _ fun l _ =>
        (channelContinuousIntegral T _ _ _ _ _ l ω).continuous)).bddAbove
    unfold sectionFourRemSup
    refine le_trans (le_of_eq ?_) (le_ciSup hbdd ⟨t.toNNReal, zero_le, ht'⟩)
    refine Finset.sum_congr rfl fun l _ => ?_
    exact (channelContinuousIntegral_eq_continuousItoOfFun T _ _ _ _ _ l ω
      ⟨t.toNNReal, zero_le, ht'⟩).symm
  refine (pi_norm_le_iff_of_nonneg hc).2 fun i => ?_
  have hval : (∑ l, continuousItoOfFun (channelKMTMeasure (Fin m))
      augmentedChannelBrownianFiltration T (channelBrownian_continuous l)
      (measurable_channelBrownian l) (sectionFourRemSigned N v f X Z false i l) t.toNNReal ω) =
      sectionFourHPath N f v X Z T t ω i := by
    simp only [hpos]
    rw [hsum i t.toNNReal]
    simp only [sectionFourHPath, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hz, hx]
    rw [← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hT : (∑ l, continuousItoOfFun (channelKMTMeasure (Fin m))
      augmentedChannelBrownianFiltration T (channelBrownian_continuous l)
      (measurable_channelBrownian l) (sectionFourRemSigned N v f X Z true i l) t.toNNReal ω) =
      -∑ l, continuousItoOfFun (channelKMTMeasure (Fin m))
      augmentedChannelBrownianFiltration T (channelBrownian_continuous l)
      (measurable_channelBrownian l) (sectionFourRemSigned N v f X Z false i l) t.toNNReal ω := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hn i l t.toNNReal]; ring
  have hp := hle false i
  have hm := hle true i
  rw [hT] at hm
  rw [Real.norm_eq_abs, ← hval]
  exact abs_le.2 ⟨by linarith [(hTpm i).2], by linarith [(hTpm i).1]⟩

/-- (R1) and (R3) for a diffusion with continuous paths: almost surely
`R_N ≤ e^{L₁ T} (sup ‖H_N‖ + (L₂ T / 2) U_N²)`. -/
theorem sectionFour_R_bound_of_continuous {N : ℕ} (hN : 0 < N)
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M) (hf0 : ∀ l x, 0 ≤ f l x)
    (hfB : ∀ l x, f l x ≤ eps l) (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hFd : ∀ x, HasFDerivAt (tcDrift f v) (F' x) x) (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    {T : ℝ≥0} {x0 : Fin d → ℝ} {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω)
    (hSDE : ∀ᵐ ω ∂channelKMTMeasure (Fin m), KMTTransfer.KurtzSDEPathsNN N f v T Z
      (channelRateIntegral T N f Z) (fun _ => x0) ω) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), sectionFourRemainderR N F' f v x0 Z T ω ≤
      Real.exp (L1 * T) * (pathSupIcc (T : ℝ) (sectionFourHPath N f v
          (kurtzFluidLimit f v x0) Z T) ω +
        L2 * T / 2 * sectionFourRemainderU N (kurtzFluidLimit f v x0) Z T ω ^ 2) := by
  have hf := continuous_rate_of_lip heps hM h319
  have hFc := continuous_tcDrift hf v
  have hXc := continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0
  have hAc := continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  have hL1n : 0 ≤ L1 := (norm_nonneg _).trans (hL1 0)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hmem : ∀ l, MemLp (Function.uncurry fun s ω => Real.sqrt (f l (Z s ω))) 2
      (trimMeasure_T (𝓖 := augmentedChannelBrownianFiltration)
        (μ := channelKMTMeasure (Fin m)) T (measurable_channelBrownian l)) := fun l =>
    memLp_sqrt_rate T (measurable_channelBrownian l) (hf l) (hfB l) hZa hZc
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
  have hJz := continuous_channelSqrtIntegral (T := T) hf hfB hZa hZc
  have hJx := continuous_channelSqrtIntegral (T := T) hf hfB
    (Z := fun s _ => kurtzFluidLimit f v x0 s) (fun _ => measurable_const) (fun _ => hXc)
  have hVsol := sectionFourV_isSolution (F' := F') (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T
  filter_upwards [hSDE, ae_all_iff.2 hscale] with ω hsde hsc
  obtain ⟨-, hZeq⟩ := hsde
  have hZc' : Continuous fun u : ℝ => Z u.toNNReal ω := (hZc ω).comp continuous_real_toNNReal
  have hXc' : Continuous fun u : ℝ => kurtzFluidLimit f v x0 u.toNNReal :=
    hXc.comp continuous_real_toNNReal
  have hE : Continuous fun t => sectionFourRemainderE N F' f v x0 Z T t ω :=
    continuous_const.smul ((continuous_const.smul (hZc'.sub hXc')).sub (hVsol ω).continuous)
  have hcz : Continuous fun u : ℝ => sectionFourCoeff F' f v x0 u
      (Z u.toNNReal ω - kurtzFluidLimit f v x0 u.toNNReal) := hAc.clm_apply (hZc'.sub hXc')
  have hbv : Continuous fun u : ℝ => sectionFourCoeff F' f v x0 u
      (sectionFourV F' f v x0 T ω u) := hAc.clm_apply (hVsol ω).continuous
  have hF1 : Continuous fun u : ℝ => tcDrift f v (Z u.toNNReal ω) := hFc.comp hZc'
  have hF2 : Continuous fun u : ℝ => tcDrift f v (kurtzFluidLimit f v x0 u.toNNReal) :=
    hFc.comp hXc'
  have hq : Continuous fun u : ℝ => (N : ℝ) • (tcDrift f v (Z u.toNNReal ω) -
      tcDrift f v (kurtzFluidLimit f v x0 u.toNNReal) -
      sectionFourCoeff F' f v x0 u (Z u.toNNReal ω - kurtzFluidLimit f v x0 u.toNNReal)) :=
    continuous_const.smul ((hF1.sub hF2).sub hcz)
  have hEq : ∀ t ∈ Icc (0 : ℝ) T, sectionFourRemainderE N F' f v x0 Z T t ω =
      sectionFourHPath N f v (kurtzFluidLimit f v x0) Z T t ω +
        (∫ u in (0 : ℝ)..t, sectionFourCoeff F' f v x0 u
          (sectionFourRemainderE N F' f v x0 Z T u ω)) +
        sectionFourTaylorQ N F' f v x0 Z t ω := by
    intro t ht
    have ht' : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 ht.2
    have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.1
    have e1 := hZeq t.toNNReal ht'
    have e2 := kurtzFluidLimit_eq (v := v) heps hM hf0 hfB h319 x0 t.toNNReal
    rw [hcoe] at e1 e2
    dsimp only at e1
    have eV : sectionFourV F' f v x0 T ω t = (∑ l, channelSqrtIntegral T f
          (fun s _ => kurtzFluidLimit f v x0 s) l t.toNNReal ω • v l) +
        ∫ u in (0 : ℝ)..t, sectionFourCoeff F' f v x0 u (sectionFourV F' f v x0 T ω u) :=
      (hVsol ω).equation t ht
    have h1 : (∫ u in (0 : ℝ)..t, sectionFourCoeff F' f v x0 u
        (sectionFourRemainderE N F' f v x0 Z T u ω)) =
        (N : ℝ) • (∫ u in (0 : ℝ)..t, sectionFourCoeff F' f v x0 u
          (Z u.toNNReal ω - kurtzFluidLimit f v x0 u.toNNReal)) -
        Real.sqrt N • ∫ u in (0 : ℝ)..t, sectionFourCoeff F' f v x0 u
          (sectionFourV F' f v x0 T ω u) := by
      have hc1 : Continuous fun u : ℝ => (N : ℝ) • sectionFourCoeff F' f v x0 u
          (Z u.toNNReal ω - kurtzFluidLimit f v x0 u.toNNReal) := continuous_const.smul hcz
      have hc2 : Continuous fun u : ℝ => Real.sqrt (N : ℝ) • sectionFourCoeff F' f v x0 u
          (sectionFourV F' f v x0 T ω u) := continuous_const.smul hbv
      calc (∫ u in (0 : ℝ)..t, sectionFourCoeff F' f v x0 u
            (sectionFourRemainderE N F' f v x0 Z T u ω))
          = ∫ u in (0 : ℝ)..t, ((N : ℝ) • sectionFourCoeff F' f v x0 u
              (Z u.toNNReal ω - kurtzFluidLimit f v x0 u.toNNReal) -
            Real.sqrt (N : ℝ) • sectionFourCoeff F' f v x0 u
              (sectionFourV F' f v x0 T ω u)) := by
            refine intervalIntegral.integral_congr fun u _ => ?_
            simp only [sectionFourRemainderE, map_smul, map_sub, smul_sub, smul_smul, hsq]
        _ = _ := by
            rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
              (hc2.intervalIntegrable _ _), intervalIntegral.integral_smul,
              intervalIntegral.integral_smul]
    have h2 : sectionFourTaylorQ N F' f v x0 Z t ω =
        (N : ℝ) • ((∫ u in (0 : ℝ)..t, tcDrift f v (Z u.toNNReal ω)) -
          ∫ u in (0 : ℝ)..t, tcDrift f v (kurtzFluidLimit f v x0 u.toNNReal)) -
        (N : ℝ) • ∫ u in (0 : ℝ)..t, sectionFourCoeff F' f v x0 u
          (Z u.toNNReal ω - kurtzFluidLimit f v x0 u.toNNReal) := by
      have ia : IntervalIntegrable (fun u : ℝ => tcDrift f v (Z u.toNNReal ω) -
          tcDrift f v (kurtzFluidLimit f v x0 u.toNNReal)) volume 0 t :=
        (hF1.sub hF2).intervalIntegrable _ _
      unfold sectionFourTaylorQ
      rw [intervalIntegral.integral_smul, intervalIntegral.integral_sub ia
        (hcz.intervalIntegrable _ _), intervalIntegral.integral_sub
        (hF1.intervalIntegrable _ _) (hF2.intervalIntegrable _ _), smul_sub]
    have hS : Real.sqrt (N : ℝ) • ∑ l, (channelRateIntegral T N f Z l t.toNNReal ω / (N : ℝ)) •
        v l = ∑ l, channelSqrtIntegral T f Z l t.toNNReal ω • v l := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hsc l t.toNNReal, smul_smul]
      congr 1
      rw [← mul_div_assoc, ← mul_assoc, hsq, mul_div_cancel_left₀ _ hNr]
    have h3 : Real.sqrt (N : ℝ) • (Z t.toNNReal ω - kurtzFluidLimit f v x0 t.toNNReal) =
        (∑ l, channelSqrtIntegral T f Z l t.toNNReal ω • v l) +
        Real.sqrt (N : ℝ) • ((∫ u in (0 : ℝ)..t, tcDrift f v (Z u.toNNReal ω)) -
          ∫ u in (0 : ℝ)..t, tcDrift f v (kurtzFluidLimit f v x0 u.toNNReal)) := by
      rw [e1, e2, ← hS]
      simp only [smul_sub, smul_add]
      abel
    have hEt : sectionFourRemainderE N F' f v x0 Z T t ω = Real.sqrt (N : ℝ) •
        (Real.sqrt (N : ℝ) • (Z t.toNNReal ω - kurtzFluidLimit f v x0 t.toNNReal) -
          sectionFourV F' f v x0 T ω t) := rfl
    have hHt : sectionFourHPath N f v (kurtzFluidLimit f v x0) Z T t ω =
        Real.sqrt (N : ℝ) • ((∑ l, channelSqrtIntegral T f Z l t.toNNReal ω • v l) -
          ∑ l, channelSqrtIntegral T f (fun s _ => kurtzFluidLimit f v x0 s) l t.toNNReal ω •
            v l) := by
      simp only [sectionFourHPath, sub_smul, Finset.sum_sub_distrib]
    rw [h1, h2, hEt, hHt, eV, h3]
    simp only [smul_add, smul_sub, smul_smul, hsq]
    abel
  have hmain := pathSupIcc_le_linear_volterra (T := (T : ℝ)) (L1 := L1) T.coe_nonneg hL1n
    (A := sectionFourCoeff F' f v x0) (Ef := sectionFourRemainderE N F' f v x0 Z T)
    (H := sectionFourHPath N f v (kurtzFluidLimit f v x0) Z T)
    (Q := sectionFourTaylorQ N F' f v x0 Z) (ω := ω) hE (hAc.clm_apply hE).continuousOn
    (continuous_const.smul (continuous_finsetSum _ fun l _ =>
      (((hJz l ω).comp continuous_real_toNNReal).sub
        ((hJx l ω).comp continuous_real_toNNReal)).smul continuous_const)).continuousOn
    (intervalIntegral.continuous_primitive (fun a b => hq.intervalIntegrable a b) 0).continuousOn
    (fun u _ => hL1 _) hEq
  have hQb : pathSupIcc (T : ℝ) (sectionFourTaylorQ N F' f v x0 Z) ω ≤
      L2 * T / 2 * sectionFourRemainderU N (kurtzFluidLimit f v x0) Z T ω ^ 2 := by
    refine pathSupIcc_le_of_bound (mul_nonneg (div_nonneg (mul_nonneg hL2n T.coe_nonneg)
      zero_le_two) (sq_nonneg _)) fun t ht => ?_
    simp only [sectionFourTaylorQ]
    refine taylor_forcing_bound hL2n (fun u hu => ?_) t ht
    have hU := SectionFourAssembly.norm_le_pathSupIcc T.coe_nonneg
      (fun t ω => Real.sqrt N • (Z t.toNNReal ω - kurtzFluidLimit f v x0 t.toNNReal)) ω
      (continuous_const.smul (hZc'.sub hXc')).continuousOn hu
    refine (scaled_taylor_remainder_le hFd hL2 (Nat.cast_nonneg N)
      (kurtzFluidLimit f v x0 u.toNNReal) (Z u.toNNReal ω)).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hU 2)
      (div_nonneg hL2n zero_le_two)
  unfold sectionFourRemainderR
  exact hmain.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hQb) (Real.exp_pos _).le)

/-- The modification of a diffusion with almost surely continuous paths that vanishes on a
null set of the filtration: adapted, continuous for every sample, equal to `Z` almost surely,
and a solution of the same SDE. -/
theorem exists_kurtzSDE_modification (hf : ∀ l, Continuous (f l)) (hfB : ∀ l x, f l x ≤ eps l)
    {N : ℕ} {T : ℝ≥0} {x0 : Fin d → ℝ} {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hSDE : ∀ᵐ ω ∂channelKMTMeasure (Fin m), KMTTransfer.KurtzSDEPathsNN N f v T Z
      (channelRateIntegral T N f Z) (fun _ => x0) ω) :
    ∃ Z' : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ,
      (∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z' t)) ∧
      (∀ ω, Continuous fun t => Z' t ω) ∧
      (∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t, Z' t ω = Z t ω) ∧
      ∀ᵐ ω ∂channelKMTMeasure (Fin m), KMTTransfer.KurtzSDEPathsNN N f v T Z'
        (channelRateIntegral T N f Z') (fun _ => x0) ω := by
  obtain ⟨N0, hNF, hN0, hcont⟩ := exists_null_continuity_set (hSDE.mono fun ω h => h.1)
  let Z' : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ := fun t => N0ᶜ.indicator (Z t)
  have hagree : ∀ ω, ω ∉ N0 → ∀ t, Z' t ω = Z t ω := fun ω hω t =>
    Set.indicator_of_mem (Set.mem_compl hω) _
  have hZ'a : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z' t) := fun t =>
    (hZa t).indicator (hNF t).compl
  have hZ'c : ∀ ω, Continuous fun t => Z' t ω := by
    intro ω
    by_cases hω : ω ∈ N0
    · have : (fun t => Z' t ω) = fun _ => 0 := by
        funext t
        exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω) _
      rw [this]
      exact continuous_const
    · have : (fun t => Z' t ω) = fun t => Z t ω := funext (hagree ω hω)
      rw [this]
      exact hcont ω hω
  have hnot : ∀ᵐ ω ∂channelKMTMeasure (Fin m), ω ∉ N0 := measure_eq_zero_iff_ae_notMem.1 hN0
  have hrate : channelRateIntegral T N f Z' = channelRateIntegral T N f Z := by
    funext l
    have hge : ∀ x, (N : ℝ) * f l x ≤ (N : ℝ) * eps l := fun x =>
      mul_le_mul_of_nonneg_left (hfB l x) (Nat.cast_nonneg N)
    have hg : Continuous fun x => (N : ℝ) * f l x := continuous_const.mul (hf l)
    exact continuousItoOfFun_congr_of_null hNF hN0 T _ _
      (memLp_sqrt_rate (g := fun x => (N : ℝ) * f l x) T (measurable_channelBrownian l) hg hge
        hZ'a hZ'c)
      (memLp_sqrt_rate_of_ae (g := fun x => (N : ℝ) * f l x) T (measurable_channelBrownian l)
        (fun t A hA h0 => augmentedChannelBrownianFiltration_null t A hA h0) hg hge hZa
        (hSDE.mono fun ω h => h.1))
      (fun s ω hω => by rw [hagree ω hω s])
  refine ⟨Z', hZ'a, hZ'c, hnot.mono fun ω hω => hagree ω hω, ?_⟩
  filter_upwards [hSDE, hnot] with ω h hω
  rw [hrate]
  have hfun := hagree ω hω
  unfold KMTTransfer.KurtzSDEPathsNN at h ⊢
  simp only [hfun]
  exact h

/-! ## The tail and the exponential moment -/

/-- **The `R_N` tail.** For every `N ≥ 2` and `r ≥ 0`, `P (r < R_N) ≤ a_R exp (-c_R r)` with
`a_R = 4 max (1, d)` and `c_R = sectionFourCR G Q Q₁ (1 + L₂ T / 2)`,
`G = e^{max (L, L₁) T}`, `L = M Σ_l ‖v_l‖ ε_l`, for any `Q ≥ T Σ_l ‖v_l‖² ε_l` and
`Q₁ ≥ T Σ_l ‖v_l‖² Lg_l²`, both positive. The constants do not depend on `N`. -/
theorem sectionFour_R_tail_kurtz (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    {Lg : Fin m → ℝ} (hLg0 : ∀ l, 0 ≤ Lg l)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (hFd : ∀ x, HasFDerivAt (tcDrift f v) (F' x) x) (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    {T : ℝ≥0} {Q Q1 : ℝ} (hQ : sectionFourQZero v eps T ≤ Q) (hQpos : 0 < Q)
    (hQ1 : sectionFourCOne v Lg T ≤ Q1) (hQ1pos : 0 < Q1)
    {x0 : Fin d → ℝ} {Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t))
    (hSDE : ∀ N, 2 ≤ N → ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (channelRateIntegral T N f (Z N))
        (fun _ => x0) ω) :
    ∀ N, 2 ≤ N → ∀ r : ℝ, 0 ≤ r →
      channelKMTMeasure (Fin m) {ω | r < sectionFourRemainderR N F' f v x0 (Z N) T ω} ≤
        ENNReal.ofReal (sectionFourAR d * Real.exp (-sectionFourCR
          (Real.exp (max (kurtzDriftLip v eps M) L1 * T)) Q Q1 (1 + L2 * T / 2) * r)) := by
  intro N hN r hr
  have hf := continuous_rate_of_lip heps hM h319
  have hXc := continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0
  have hNpos : 0 < N := by omega
  obtain ⟨Z', hZ'a, hZ'c, hZZ, hSDE'⟩ := exists_kurtzSDE_modification hf hfB (hZa N) (hSDE N hN)
  have hUeq : ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      sectionFourRemainderU N (kurtzFluidLimit f v x0) (Z N) T ω =
        sectionFourRemainderU N (kurtzFluidLimit f v x0) Z' T ω := by
    filter_upwards [hZZ] with ω hω
    simp only [sectionFourRemainderU, pathSupIcc, hω]
  have hReq : ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      sectionFourRemainderR N F' f v x0 (Z N) T ω =
        sectionFourRemainderR N F' f v x0 Z' T ω := by
    filter_upwards [hZZ] with ω hω
    simp only [sectionFourRemainderR, sectionFourRemainderE, pathSupIcc, hω]
  have hGU : Real.exp (kurtzDriftLip v eps M * T) ≤
      Real.exp (max (kurtzDriftLip v eps M) L1 * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) T.coe_nonneg)
  have hGR : Real.exp (L1 * T) ≤ Real.exp (max (kurtzDriftLip v eps M) L1 * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) T.coe_nonneg)
  have hUtail : ∀ r : ℝ, 0 ≤ r → channelKMTMeasure (Fin m)
      {ω | r < sectionFourRemainderU N (kurtzFluidLimit f v x0) Z' T ω} ≤
      ENNReal.ofReal (sectionFourAU d * Real.exp (-sectionFourBU
        (Real.exp (max (kurtzDriftLip v eps M) L1 * T)) Q * r ^ 2)) := by
    intro r hr
    have h := sectionFour_U_tail_kurtz_fluid heps hM hf0 hfB h319 hQ hQpos hZa hSDE N hN r hr
    have hb : sectionFourBU (Real.exp (max (kurtzDriftLip v eps M) L1 * T)) Q ≤
        sectionFourBU (Real.exp (kurtzDriftLip v eps M * T)) Q := by
      unfold sectionFourBU
      refine one_div_le_one_div_of_le (mul_pos (mul_pos two_pos
        (pow_pos (Real.exp_pos _) 2)) hQpos) ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.exp_pos _).le hGU 2) zero_le_two) hQpos.le
    have hexp : -sectionFourBU (Real.exp (kurtzDriftLip v eps M * T)) Q * r ^ 2 ≤
        -sectionFourBU (Real.exp (max (kurtzDriftLip v eps M) L1 * T)) Q * r ^ 2 := by
      have := mul_le_mul_of_nonneg_right hb (sq_nonneg r)
      linarith
    have haU : 0 ≤ sectionFourAU d := by unfold sectionFourAU; positivity
    refine le_trans (measure_mono_ae ?_) (h.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) haU)))
    filter_upwards [hUeq] with ω h hω
    show r < sectionFourRemainderU N (kurtzFluidLimit f v x0) (Z N) T ω
    rw [h]
    exact hω
  have hB : 0 ≤ L2 * T / 2 := div_nonneg (mul_nonneg hL2n T.coe_nonneg) zero_le_two
  have hRU : ∀ᵐ ω ∂channelKMTMeasure (Fin m), sectionFourRemainderR N F' f v x0 Z' T ω ≤
      Real.exp (max (kurtzDriftLip v eps M) L1 * T) *
        (pathSupIcc (T : ℝ) (sectionFourHPath N f v (kurtzFluidLimit f v x0) Z' T) ω +
          L2 * T / 2 * sectionFourRemainderU N (kurtzFluidLimit f v x0) Z' T ω ^ 2) := by
    filter_upwards [sectionFour_R_bound_of_continuous hNpos heps hM hf0 hfB h319 hFd hL1 hL2n
      hL2 hZ'a hZ'c hSDE'] with ω h
    exact h.trans (mul_le_mul_of_nonneg_right hGR
      (add_nonneg (pathSupIcc_nonneg _ _ _) (mul_nonneg hB (sq_nonneg _))))
  have htail := sectionFour_R_tail_channel (N := N) (v := v) (eps := eps) hLg0 hLg hf hfB hXc
    hZ'a hZ'c T (Real.exp_pos _) hQpos hQ1pos hB hQ1 hUtail hRU
    (sectionFourHPath_sup_le hf hfB hXc hZ'a hZ'c T) hr
  refine le_trans (measure_mono_ae ?_) htail
  filter_upwards [hReq] with ω h hω
  show r < sectionFourRemainderR N F' f v x0 Z' T ω
  rw [← h]
  exact hω

/-- **Uniform exponential moment of `R_N`** of order `c_R / 2`, with constant `1 + a_R`. -/
theorem sectionFour_R_expMoment_kurtz (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    {Lg : Fin m → ℝ} (hLg0 : ∀ l, 0 ≤ Lg l)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (hFd : ∀ x, HasFDerivAt (tcDrift f v) (F' x) x) (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    {T : ℝ≥0} {Q Q1 : ℝ} (hQ : sectionFourQZero v eps T ≤ Q) (hQpos : 0 < Q)
    (hQ1 : sectionFourCOne v Lg T ≤ Q1) (hQ1pos : 0 < Q1)
    {x0 : Fin d → ℝ} {Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t))
    (hSDE : ∀ N, 2 ≤ N → ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (channelRateIntegral T N f (Z N))
        (fun _ => x0) ω) :
    UniformExpMoment (fun N => sectionFourRemainderR N F' f v x0 (Z N) T)
      (sectionFourCR (Real.exp (max (kurtzDriftLip v eps M) L1 * T)) Q Q1
        (1 + L2 * T / 2) / 2) (1 + sectionFourAR d) (channelKMTMeasure (Fin m)) := by
  have hA : 0 < 1 + L2 * T / 2 := by
    have := mul_nonneg hL2n T.coe_nonneg
    linarith
  have hc : 0 < sectionFourCR (Real.exp (max (kurtzDriftLip v eps M) L1 * T)) Q Q1
      (1 + L2 * T / 2) := by
    unfold sectionFourCR
    refine lt_min (div_pos one_pos (mul_pos (mul_pos (mul_pos (by norm_num)
      (pow_pos (Real.exp_pos _) 3)) hQpos) hA)) (div_pos hA (mul_pos (mul_pos (by norm_num)
      (Real.exp_pos _)) hQ1pos))
  have ha : 0 ≤ sectionFourAR d := by unfold sectionFourAR; positivity
  refine uniformExpMoment_of_exp_tail (fun N _ => ?_) (fun N _ ω => pathSupIcc_nonneg _ _ ω)
    hc ha (sectionFour_R_tail_kurtz heps hM hf0 hfB h319 hLg0 hLg hFd hL1 hL2n hL2 hQ hQpos
      hQ1 hQ1pos hZa hSDE)
  refine measurable_pathSupIcc _ _ fun q => ?_
  have hZm : Measurable (Z N (q : ℝ).toNNReal) :=
    (hZa N _).mono (augmentedChannelBrownianFiltration.le _) le_rfl
  exact (((hZm.sub measurable_const).const_smul (Real.sqrt (N : ℝ))).sub
    (measurable_sectionFourV heps hM hf0 hfB h319 hL1 hL2n hL2 x0 ⟨q.2.1, q.2.2⟩)).const_smul
      (Real.sqrt (N : ℝ))

end Channel

end Ripple.Kurtz.StrongApprox
