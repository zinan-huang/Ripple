import Ripple.Kurtz.StrongApprox.SectionFourRTailKurtz
import Ripple.Kurtz.StrongApprox.KurtzStrongSolution

/-!
# Kurtz, Theorem 4.4, from the Knight time change

On the channel space `channelKMTSpace (Fin m)` with the augmented channel filtration, let `Z_N`
(`N ≥ 2`) be adapted solutions of Kurtz's SDE with continuous paths, `M_{N,l}` their noise
integrals `channelRateIntegral`, `X` the fluid limit `kurtzFluidLimit` and `V` the Gaussian limit.
`V` is taken on all of `[0, ∞)` (`sectionFourVAll`): at time `t` it is `sectionFourV` on the
integer horizon `⌈t⌉`. On every horizon `T` it agrees almost surely with `sectionFourV` on `T`
(`sectionFourVAll_eq`), since the channel integrals on nested horizons agree
(`channelSqrtIntegral_horizon`) and the linear Volterra equation has unique solutions
(`sectionFourV_horizon`).

The only stochastic premise beyond the SDE is the Knight time change, allowing an extension
(`KnightTimeChangeData`): a probability space `(Ω', P')` with a measure-preserving map
`proj : Ω' → channelKMTSpace (Fin m)` and Brownian families `β N l`, independent over channels for
each `N ≥ 2`, with `M_{N,l} t = β_{N,l} (N ∫₀ᵗ f_l (Z_N))` along `proj` on every horizon.

`kurtz_theorem_four_four_of_knight`: on the transferred space
`kmtFamilyMeasure P' β` (a product extension of `(Ω', P')` carrying the chains `X_N` of the
time-change construction), for every horizon `T` there are measurable `γ_N ≥ 0`, `η > 0` and `C`
with `∫ exp (η γ_N) ≤ C` for all `N ≥ 2`, and almost surely, for all `N ≥ 2` and `t ∈ [0, T]`,

`‖sqrt N (X_N t - X t) - V t‖ ≤ γ_N log N / sqrt N`.

The chains, `Z_N ∘ proj`, and `V ∘ proj` do not depend on `T`. The proof applies
`transferred_finiteChannelKurtz_family_of_nnrealSDE` on `(Ω', P')` for the term `X_N - Z_N`,
pulls the `R_N` exponential moment `sectionFour_R_expMoment_kurtz` back along `proj ∘ fst`
(`uniformExpMoment_comp`), and combines both in `sectionFour_final_assembly`.
`kurtz_theorem_four_four_of_knight_strong` takes `Z_N` from
`exists_kurtz_strong_solution_family`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic Ripple.Stochastic.ContinuousItoLinear
open SectionFourAssembly

/-! ## Pulling a uniform exponential moment back along a map -/

section Pullback

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

theorem uniformExpMoment_comp {μ : Measure Ω₁} {P : Measure Ω₂} {g : Ω₁ → Ω₂}
    (hg : Measurable g) (hmap : μ.map g = P) {R : ℕ → Ω₂ → ℝ} {η C : ℝ}
    (h : UniformExpMoment R η C P) : UniformExpMoment (fun N z => R N (g z)) η C μ where
  eta_pos := h.eta_pos
  measurable N hN := (h.measurable N hN).comp hg
  nonneg N hN z := h.nonneg N hN (g z)
  integrable N hN := by
    have hm : AEStronglyMeasurable (fun y => Real.exp (η * R N y)) (μ.map g) :=
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable N hN))).aestronglyMeasurable
    have hi := h.integrable N hN
    rw [← hmap] at hi
    exact (integrable_map_measure hm hg.aemeasurable).1 hi
  integral_le N hN := by
    have hm : AEStronglyMeasurable (fun y => Real.exp (η * R N y)) (μ.map g) :=
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable N hN))).aestronglyMeasurable
    calc ∫ z, Real.exp (η * R N (g z)) ∂μ = ∫ y, Real.exp (η * R N y) ∂(μ.map g) :=
          (integral_map hg.aemeasurable hm).symm
      _ = ∫ y, Real.exp (η * R N y) ∂P := by rw [hmap]
      _ ≤ C := h.integral_le N hN

end Pullback

/-! ## The Gaussian limit on all times -/

section Channel

attribute [local instance] channelBrownian_isFilteredPreBrownian_augmented

variable {m d : ℕ} {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {M : ℝ} {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L1 L2 : ℝ}

/-- The channel integrals on nested horizons agree up to the smaller horizon. -/
theorem channelSqrtIntegral_horizon {T₁ T₂ : ℝ≥0} (h12 : T₁ ≤ T₂) (hf : ∀ l, Continuous (f l))
    (hfB : ∀ l x, f l x ≤ eps l) {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (l : Fin m) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ s ≤ T₁,
      channelSqrtIntegral T₂ f Z l s ω = channelSqrtIntegral T₁ f Z l s ω := by
  have hm := memLp_sqrt_rate (μ := channelKMTMeasure (Fin m))
    (F := augmentedChannelBrownianFiltration) T₂ (measurable_channelBrownian l) (hf l) (hfB l)
    hZa hZc
  have h := HorizonItoRestriction.windowIto_restrict h12 (channelBrownian_continuous l)
    (measurable_channelBrownian l) _ hm
  simp only [windowIto_eq_continuousItoOfFun] at h
  exact h

/-- The Gaussian limits on nested horizons agree up to the smaller horizon. -/
theorem sectionFourV_horizon (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖) (x0 : Fin d → ℝ)
    {T₁ T₂ : ℝ≥0} (h12 : T₁ ≤ T₂) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t ∈ Icc (0 : ℝ) T₁,
      sectionFourV F' f v x0 T₁ ω t = sectionFourV F' f v x0 T₂ ω t := by
  have hf := continuous_rate_of_lip heps hM h319
  have hXc := continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0
  have hAc := continuous_sectionFourCoeff (v := v) heps hM hf0 hfB h319 hL2n hL2 x0
  have hL1n : 0 ≤ L1 := (norm_nonneg _).trans (hL1 0)
  have hAb : ∀ s ∈ Icc (0 : ℝ) T₁, ‖sectionFourCoeff F' f v x0 s‖ ≤ L1 := fun s _ => hL1 _
  have hJc : ∀ (T : ℝ≥0) (l : Fin m) (ω : channelKMTSpace (Fin m)), Continuous fun s : ℝ =>
      channelSqrtIntegral T f (fun s _ => kurtzFluidLimit f v x0 s) l s.toNNReal ω • v l :=
    fun T l ω => ((continuous_channelSqrtIntegral hf hfB (fun _ => measurable_const)
      (fun _ => hXc) l ω).comp continuous_real_toNNReal).smul continuous_const
  have h12' : (T₁ : ℝ) ≤ T₂ := h12
  filter_upwards [ae_all_iff.2 fun l => channelSqrtIntegral_horizon h12 hf hfB
    (Z := fun s _ => kurtzFluidLimit f v x0 s) (fun _ => measurable_const) (fun _ => hXc) l]
    with ω hω t ht
  unfold sectionFourV
  refine Finset.sum_congr rfl fun l _ => ?_
  have hs1 := volterraSol_spec hAc (hJc T₁ l ω) T₁.coe_nonneg
  have hs2 := volterraSol_spec hAc (hJc T₂ l ω) T₂.coe_nonneg
  have hs2' : Analysis.LinearVolterra.IsSolution (sectionFourCoeff F' f v x0)
      (fun s => channelSqrtIntegral T₂ f (fun s _ => kurtzFluidLimit f v x0 s) l s.toNNReal ω •
        v l)
      (volterraSol (sectionFourCoeff F' f v x0) T₂ (fun s =>
        channelSqrtIntegral T₂ f (fun s _ => kurtzFluidLimit f v x0 s) l s.toNNReal ω • v l))
      T₁ := ⟨hs2.continuous, fun s hs => hs2.equation s ⟨hs.1, hs.2.trans h12'⟩⟩
  have h := Analysis.LinearVolterra.norm_sub_le_exp hAc hs1 hs2' T₁.coe_nonneg le_rfl hL1n hAb
    (fun s hs => by
      have hsT : s.toNNReal ≤ T₁ := Real.toNNReal_le_iff_le_coe.2 hs.2
      simp only [hω l s.toNNReal hsT, sub_self, norm_zero, le_refl]) t ht
  rw [zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- The Gaussian limit on all of `[0, ∞)`: at time `t`, the Gaussian limit on the integer
horizon `⌈t⌉`. -/
def sectionFourVAll (F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ) (x0 : Fin d → ℝ)
    (ω : channelKMTSpace (Fin m)) (t : ℝ) : Fin d → ℝ :=
  sectionFourV F' f v x0 (⌈t⌉₊ : ℝ≥0) ω t

/-- On every horizon `T`, the all-time Gaussian limit is the Gaussian limit on `T`, almost
surely, simultaneously for all `t ∈ [0, T]`. -/
theorem sectionFourVAll_eq (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖) (x0 : Fin d → ℝ)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t ∈ Icc (0 : ℝ) T,
      sectionFourVAll F' f v x0 ω t = sectionFourV F' f v x0 T ω t := by
  have hTK : T ≤ ((⌈(T : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
    exact Nat.le_ceil _
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂channelKMTMeasure (Fin m), n ≤ ⌈(T : ℝ)⌉₊ →
      ∀ t ∈ Icc (0 : ℝ) ((n : ℝ≥0) : ℝ), sectionFourV F' f v x0 (n : ℝ≥0) ω t =
        sectionFourV F' f v x0 ((⌈(T : ℝ)⌉₊ : ℕ) : ℝ≥0) ω t := by
    intro n
    by_cases hnK : n ≤ ⌈(T : ℝ)⌉₊
    · exact (sectionFourV_horizon heps hM hf0 hfB h319 hL1 hL2n hL2 x0
        (show (n : ℝ≥0) ≤ ((⌈(T : ℝ)⌉₊ : ℕ) : ℝ≥0) by exact_mod_cast hnK)).mono
          fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hnK
  filter_upwards [ae_all_iff.2 hn, sectionFourV_horizon heps hM hf0 hfB h319 hL1 hL2n hL2 x0
    hTK] with ω hω hT t ht
  have htn : ⌈t⌉₊ ≤ ⌈(T : ℝ)⌉₊ := Nat.ceil_mono ht.2
  have htc : t ∈ Icc (0 : ℝ) ((⌈t⌉₊ : ℝ≥0) : ℝ) := by
    refine ⟨ht.1, ?_⟩
    rw [NNReal.coe_natCast]
    exact Nat.le_ceil t
  unfold sectionFourVAll
  rw [hω ⌈t⌉₊ htn t htc]
  exact (hT t ht).symm

/-- Pathwise: `‖sqrt N (Z t - X t) - V t‖ ≤ R_N / sqrt N` on `[0, T]`. -/
theorem norm_sectionFour_diff_le (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖) (x0 : Fin d → ℝ)
    {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ} (hZc : ∀ ω, Continuous fun t => Z t ω)
    {N : ℕ} (hN : 0 < N) (T : ℝ≥0) (ω : channelKMTSpace (Fin m)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖Real.sqrt N • (Z t.toNNReal ω - kurtzFluidLimit f v x0 t.toNNReal) -
        sectionFourV F' f v x0 T ω t‖ ≤
      sectionFourRemainderR N F' f v x0 Z T ω / Real.sqrt N := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hXc := continuous_kurtzFluidLimit (v := v) heps hM hf0 hfB h319 x0
  have hE : Continuous fun t => sectionFourRemainderE N F' f v x0 Z T t ω :=
    continuous_const.smul ((continuous_const.smul (((hZc ω).comp continuous_real_toNNReal).sub
      (hXc.comp continuous_real_toNNReal))).sub
      (sectionFourV_isSolution (F' := F') (v := v) heps hM hf0 hfB h319 hL2n hL2 x0 T
        ω).continuous)
  have h := SectionFourAssembly.norm_le_pathSupIcc T.coe_nonneg
    (sectionFourRemainderE N F' f v x0 Z T) ω hE.continuousOn ht
  have hnorm : ‖sectionFourRemainderE N F' f v x0 Z T t ω‖ = Real.sqrt N *
      ‖Real.sqrt N • (Z t.toNNReal ω - kurtzFluidLimit f v x0 t.toNNReal) -
        sectionFourV F' f v x0 T ω t‖ := by
    rw [show sectionFourRemainderE N F' f v x0 Z T t ω = Real.sqrt (N : ℝ) •
      (Real.sqrt (N : ℝ) • (Z t.toNNReal ω - kurtzFluidLimit f v x0 t.toNNReal) -
        sectionFourV F' f v x0 T ω t) from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.le]
  rw [hnorm] at h
  rw [le_div_iff₀ hs, mul_comm]
  exact h

/-! ## The Knight time change and the theorem -/

/-- The Knight time change, allowing an extension: a probability space `(Ω', P')` with a
measure-preserving map to the channel space and Brownian families `β N l`, continuous and
independent over channels for each `N ≥ 2`, such that the noise integrals of `Z_N` are the
time-changed `β N l` along the map, on every horizon. These are the premises of
`transferred_finiteChannelKurtz_family_of_nnrealSDE` other than the SDE. -/
structure KnightTimeChangeData (Ω' : Type*) [MeasurableSpace Ω'] (P' : Measure Ω')
    (f : Fin m → (Fin d → ℝ) → ℝ) (Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) where
  /-- The map to the channel space. -/
  proj : Ω' → channelKMTSpace (Fin m)
  measurePreserving : MeasurePreserving proj P' (channelKMTMeasure (Fin m))
  /-- The internal Brownian families. -/
  β : ℕ → Fin m → ℝ≥0 → Ω' → ℝ
  measurable_β : ∀ N l t, Measurable (β N l t)
  isPreBrownian : ∀ N, 2 ≤ N → ∀ l, IsPreBrownian (β N l) P'
  continuous_β : ∀ N, 2 ≤ N → ∀ l, ∀ᵐ ω ∂P', Continuous fun t => β N l t ω
  iIndep : ∀ N, 2 ≤ N → iIndepFun (fun (l : Fin m) ω => fun t => β N l t ω) P'
  knight : ∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂P', KMTTransfer.KurtzKnightPathsNN N f T β
    (fun t ω => Z N t (proj ω)) (fun l t ω => channelRateIntegral T N f (Z N) l t (proj ω)) ω

/-- **Kurtz, Theorem 4.4, from the Knight time change.** For adapted solutions `Z_N` of Kurtz's
SDE with continuous paths and Knight time-change data `K`, on the transferred space
`kmtFamilyMeasure P' K.β` with the chains `X_N` of the time-change construction, the fluid limit
`X` and the all-time Gaussian limit `V ∘ proj`: for every horizon `T` there are measurable
`γ_N ≥ 0`, `η > 0` and `C` with `∫ exp (η γ_N) ≤ C` for all `N ≥ 2`, and almost surely, for all
`N ≥ 2` and `t ∈ [0, T]`, `‖sqrt N (X_N t - X t) - V t‖ ≤ γ_N log N / sqrt N`. -/
theorem kurtz_theorem_four_four_of_knight (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    {fN : ℕ → Fin m → (Fin d → ℝ) → ℝ} {Gamma : ℝ} (hGamma : 0 ≤ Gamma)
    (hfN0 : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hfNm : ∀ N, 2 ≤ N → ∀ l, Measurable (fN N l))
    (h32 : ∀ N, 2 ≤ N → ∀ l x, |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    {Lg : Fin m → ℝ} (hLg0 : ∀ l, 0 ≤ Lg l)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (hFd : ∀ x, HasFDerivAt (tcDrift f v) (F' x) x) (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖)
    {x0 : Fin d → ℝ} {Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}
    (hZa : ∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t))
    (hZc : ∀ N ω, Continuous fun t => Z N t ω)
    (hSDE : ∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (channelRateIntegral T N f (Z N))
        (fun _ => x0) ω)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (K : KnightTimeChangeData Ω' P' f Z) :
    ∀ T : ℝ≥0, ∃ (gamma : ℕ → Ω' × (ℕ × Fin m → KMTTransfer.KMTPoissonCode) → ℝ) (eta C : ℝ),
      0 < eta ∧ (∀ N, 2 ≤ N → Measurable (gamma N)) ∧
      (∀ N, 2 ≤ N → ∀ z, 0 ≤ gamma N z) ∧
      (∀ N, 2 ≤ N →
        Integrable (fun z => Real.exp (eta * gamma N z))
          (KMTTransfer.kmtFamilyMeasure P' K.β K.measurable_β) ∧
        ∫ z, Real.exp (eta * gamma N z) ∂KMTTransfer.kmtFamilyMeasure P' K.β K.measurable_β ≤
          C) ∧
      ∀ᵐ z ∂KMTTransfer.kmtFamilyMeasure P' K.β K.measurable_β, ∀ N : ℕ, 2 ≤ N →
        ∀ t ∈ Icc (0 : ℝ) T,
          ‖Real.sqrt N • (KMTTransfer.transferredChainFamily v fN eps hfN0 h31 hfNm
              (fun _ _ => x0) N z t - kurtzFluidLimit f v x0 t.toNNReal) -
            sectionFourVAll F' f v x0 (K.proj z.1) t‖ ≤
            gamma N z * Real.log (N : ℝ) / Real.sqrt N := by
  intro T
  have hπm : Measurable K.proj := K.measurePreserving.measurable
  have hgm : Measurable fun z : Ω' × (ℕ × Fin m → KMTTransfer.KMTPoissonCode) =>
      K.proj z.1 := hπm.comp measurable_fst
  have hmap : (KMTTransfer.kmtFamilyMeasure P' K.β K.measurable_β).map
      (fun z : Ω' × (ℕ × Fin m → KMTTransfer.KMTPoissonCode) => K.proj z.1) =
      channelKMTMeasure (Fin m) := by
    rw [show (fun z : Ω' × (ℕ × Fin m → KMTTransfer.KMTPoissonCode) => K.proj z.1) =
      K.proj ∘ Prod.fst from rfl, ← Measure.map_map hπm measurable_fst,
      KMTTransfer.kmtFamilyMeasure_map_fst, K.measurePreserving.map_eq]
  -- the term `X_N - Z_N`
  obtain ⟨lamB, CB, hlamB, -, hBm, hB0, -, hBint, hB7⟩ :=
    KMTTransfer.transferred_finiteChannelKurtz_family_of_nnrealSDE P' K.β K.measurable_β
      K.isPreBrownian K.continuous_β K.iIndep f fN v eps Gamma M T
      (fun N t ω => Z N t (K.proj ω))
      (fun N l t ω => channelRateIntegral T N f (Z N) l t (K.proj ω)) (fun _ _ => x0)
      heps hGamma hM hf0 hfB h319 hfN0 h31 hfNm h32
      (fun N hN => (ae_of_ae_map hπm.aemeasurable
        (by rw [K.measurePreserving.map_eq]; exact hSDE N hN T)).mono fun _ h => h)
      (fun N hN => K.knight N hN T)
  have hBeta : UniformExpMoment
      (fun N z => KMTTransfer.transferredKurtzBeta v eps Gamma M (T : ℝ) K.β N z) lamB CB
      (KMTTransfer.kmtFamilyMeasure P' K.β K.measurable_β) :=
    ⟨hlamB, hBm, hB0, fun N hN => (hBint N hN).1, fun N hN => (hBint N hN).2⟩
  -- the term `R_N`
  have hQ0 : 0 ≤ sectionFourQZero v eps T :=
    mul_nonneg T.coe_nonneg (Finset.sum_nonneg fun l _ => mul_nonneg (sq_nonneg _) (heps l))
  have hC1 : 0 ≤ sectionFourCOne v Lg T :=
    mul_nonneg T.coe_nonneg (Finset.sum_nonneg fun l _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hRP := sectionFour_R_expMoment_kurtz heps hM hf0 hfB h319 hLg0 hLg hFd hL1 hL2n hL2
    (le_add_of_nonneg_right zero_le_one) (by linarith) (le_add_of_nonneg_right zero_le_one)
    (by linarith) hZa (fun N hN => hSDE N hN T)
  have hR := uniformExpMoment_comp hgm hmap hRP
  have hA := sectionFour_final_assembly (P := KMTTransfer.kmtFamilyMeasure P' K.β K.measurable_β)
    (T := T) (X := fun t => kurtzFluidLimit f v x0 t.toNNReal)
    (V := fun t z => sectionFourV F' f v x0 T (K.proj z.1) t)
    (Z := fun N t z => Z N t.toNNReal (K.proj z.1))
    (Xchain := fun N t z => KMTTransfer.transferredChainFamily v fN eps hfN0 h31 hfNm
      (fun _ _ => x0) N z t) hBeta hR (hB7.mono fun _ h => h)
    (ae_of_all _ fun z N hN t ht => norm_sectionFour_diff_le heps hM hf0 hfB h319 hL2n hL2 x0
      (hZc N) (by omega) T (K.proj z.1) ht)
  dsimp only at hA
  obtain ⟨heta, hint, hbound⟩ := hA
  refine ⟨_, _, _, heta, fun N hN => ?_, fun N hN z => ?_, hint, ?_⟩
  · exact (hBeta.measurable N hN).add ((hR.measurable N hN).div_const _)
  · exact add_nonneg (hBeta.nonneg N hN z)
      (div_nonneg (hR.nonneg N hN z) (Real.log_nonneg one_le_two))
  · filter_upwards [hbound, ae_of_ae_map hgm.aemeasurable (by
      rw [hmap]
      exact sectionFourVAll_eq (F' := F') (v := v) heps hM hf0 hfB h319 hL1 hL2n hL2 x0 T)]
      with z hz hV N hN t ht
    rw [hV t ht]
    exact hz N hN t ht

/-- **Kurtz, Theorem 4.4, from the Knight time change, for the strong solutions.** There are
adapted solutions `Z_N` of Kurtz's SDE with continuous paths on the channel space such that for
any Knight time-change data for them the conclusion of `kurtz_theorem_four_four_of_knight`
holds. -/
theorem kurtz_theorem_four_four_of_knight_strong (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    {fN : ℕ → Fin m → (Fin d → ℝ) → ℝ} {Gamma : ℝ} (hGamma : 0 ≤ Gamma)
    (hfN0 : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hfNm : ∀ N, 2 ≤ N → ∀ l, Measurable (fN N l))
    (h32 : ∀ N, 2 ≤ N → ∀ l x, |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (hFd : ∀ x, HasFDerivAt (tcDrift f v) (F' x) x) (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖) (x0 : Fin d → ℝ) :
    ∃ Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ,
      (∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t)) ∧
      (∀ N ω, Continuous fun t => Z N t ω) ∧
      (∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
        KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (channelRateIntegral T N f (Z N))
          (fun _ => x0) ω) ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (K : KnightTimeChangeData Ω' P' f Z) (T : ℝ≥0),
        ∃ (gamma : ℕ → Ω' × (ℕ × Fin m → KMTTransfer.KMTPoissonCode) → ℝ) (eta C : ℝ),
          0 < eta ∧ (∀ N, 2 ≤ N → Measurable (gamma N)) ∧
          (∀ N, 2 ≤ N → ∀ z, 0 ≤ gamma N z) ∧
          (∀ N, 2 ≤ N →
            Integrable (fun z => Real.exp (eta * gamma N z))
              (KMTTransfer.kmtFamilyMeasure P' K.β K.measurable_β) ∧
            ∫ z, Real.exp (eta * gamma N z)
              ∂KMTTransfer.kmtFamilyMeasure P' K.β K.measurable_β ≤ C) ∧
          ∀ᵐ z ∂KMTTransfer.kmtFamilyMeasure P' K.β K.measurable_β, ∀ N : ℕ, 2 ≤ N →
            ∀ t ∈ Icc (0 : ℝ) T,
              ‖Real.sqrt N • (KMTTransfer.transferredChainFamily v fN eps hfN0 h31 hfNm
                  (fun _ _ => x0) N z t - kurtzFluidLimit f v x0 t.toNNReal) -
                sectionFourVAll F' f v x0 (K.proj z.1) t‖ ≤
                gamma N z * Real.log (N : ℝ) / Real.sqrt N := by
  obtain ⟨Z, hZa, hZc, -, hSDE⟩ :=
    exists_kurtz_strong_solution_family (v := v) heps hM hf0 hfB h319 Lg hLg x0
  refine ⟨Z, hZa, hZc, hSDE, fun Ω' _ P' _ K T => ?_⟩
  exact kurtz_theorem_four_four_of_knight heps hM hf0 hfB h319 hGamma hfN0 h31 hfNm h32
    (Lg := fun l => (Lg l : ℝ)) (fun l => (Lg l).coe_nonneg) hLg hFd hL1 hL2n hL2 hZa hZc hSDE
    K T

end Channel

end Ripple.Kurtz.StrongApprox
