import Ripple.Kurtz.StrongApprox.ChannelExponentialDriver
import Ripple.Kurtz.StrongApprox.SectionFourTails
import Ripple.Kurtz.StrongApprox.KurtzSDEContinuousIto
import Ripple.Stochastic.ContinuousAdaptedIntegrand

/-!
# Square-integrability of the rate integrands and the `U_N` maximal bounds

1. For a continuous rate `f` with `0 ≤ f ≤ ε` and an adapted state `Z`, the integrand
   `(s, ω) ↦ sqrt (f (Z s ω))` is in the predictable `L²` space of the Itô integral
   (`memLp_sqrt_rate`). Almost-sure path continuity suffices when the filtration contains the
   null sets (`memLp_sqrt_rate_of_ae`). This removes the premise `hmem` of
   `kurtzSDEPathsNN_of_continuousIto` (`kurtzSDEPathsNN_of_continuousIto_rates`).

2. On the channel space, the integrands `± v_l i sqrt (f_l (Z))` of coordinate `i` feed the
   multi-channel exponential maximal inequality `channel_bounded_continuous_exponential_maximal`.
   This gives the hypotheses `hmaxp`, `hmaxm` of `SectionFourAssembly.sectionFour_U_tail` for
   the suprema `sectionFourSup` of the two signed channel sums, with the bracket
   `sectionFourBracket`, and the bracket bound `hbr` with
   `Q₀ = T Σ_l ‖v_l‖² ε_l` (coordinatewise `T Σ_l v_{l,i}² ε_l`).
   The channel integrals are the continuous Itô integrals `continuousItoOfFun`
   (`channelContinuousIntegral_eq_continuousItoOfFun`), and the integral of the negative
   integrand is the negative of the integral, almost surely for all times.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic Ripple.Stochastic.ContinuousItoLinear
open Ripple.Stochastic.ContinuousAdaptedIntegrand Ripple.Stochastic.FilteredItoIntegralCLM
open Ripple.Stochastic.FilteredItoIntegralL2

/-! ## Square-integrability of the rate integrand -/

section RateIntegrand

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ} {d : ℕ}

/-- A bounded continuous rate of a continuous adapted state is a predictable `L²` integrand. -/
theorem memLp_sqrt_rate (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {e : ℝ}
    (hge : ∀ x, g x ≤ e)
    {Z : ℝ≥0 → Ω → Fin d → ℝ} (hZa : ∀ t, Measurable[F t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) :
    MemLp (Function.uncurry fun s ω => Real.sqrt (g (Z s ω))) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  have hsg : Continuous fun x => Real.sqrt (g x) := Real.continuous_sqrt.comp hg
  refine integrandMemLp T hBmeas _ (measurable_comp_sections hZa hsg)
    (continuous_comp_paths hZc hsg) (Real.sqrt e) fun t ω => ?_
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (hge _)

/-- The same with almost-sure path continuity, when every filtration level contains the
measurable null sets. -/
theorem memLp_sqrt_rate_of_ae (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {e : ℝ}
    (hge : ∀ x, g x ≤ e)
    {Z : ℝ≥0 → Ω → Fin d → ℝ} (hZa : ∀ t, Measurable[F t] (Z t))
    (hZc : ∀ᵐ ω ∂μ, Continuous fun t => Z t ω) :
    MemLp (Function.uncurry fun s ω => Real.sqrt (g (Z s ω))) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hZc)
  have hNF : ∀ t, MeasurableSet[F t] N := fun t => hnull t N hNmeas hN0
  have hsg : Continuous fun x => Real.sqrt (g x) := Real.continuous_sqrt.comp hg
  -- the modification, zero on `N`
  let H : ℝ≥0 → Ω → ℝ := fun s => Nᶜ.indicator fun ω => Real.sqrt (g (Z s ω))
  have hHa : ∀ t, Measurable[F t] (H t) := fun t =>
    (measurable_comp_sections hZa hsg t).indicator (hNF t).compl
  have hHc : ∀ ω, Continuous fun t => H t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · have : (fun t => H t ω) = fun _ => 0 := by
        funext t
        exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω) _
      rw [this]
      exact continuous_const
    · have : (fun t => H t ω) = fun t => Real.sqrt (g (Z t ω)) := by
        funext t
        exact Set.indicator_of_mem (Set.mem_compl hω) _
      rw [this]
      have hc : Continuous fun t => Z t ω := by
        by_contra hnc
        exact hω (hNsub hnc)
      exact hsg.comp hc
  have hHb : ∀ t ω, |H t ω| ≤ Real.sqrt e := by
    intro t ω
    by_cases hω : ω ∈ N
    · have h0 : H t ω = 0 := Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω) _
      rw [h0, abs_zero]
      exact Real.sqrt_nonneg _
    · have h1 : H t ω = Real.sqrt (g (Z t ω)) := Set.indicator_of_mem (Set.mem_compl hω) _
      rw [h1, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hge _)
  have hmem := integrandMemLp (μ := μ) T hBmeas H hHa hHc (Real.sqrt e) hHb
  -- the exceptional set `univ ×ˢ N` is predictable and null
  let G : ℝ≥0 → Ω → ℝ := fun _ => N.indicator fun _ => (1 : ℝ)
  have hGa : ∀ t, Measurable[F t] (G t) := fun t => measurable_const.indicator (hNF t)
  have hGc : ∀ ω, Continuous fun t => G t ω := fun ω => continuous_const
  have hGm : Measurable[F.predictable] (Function.uncurry G) :=
    (stronglyMeasurable_uncurry hGa hGc).measurable
  have hset : (Set.univ : Set ℝ≥0) ×ˢ N = Function.uncurry G ⁻¹' {1} := by
    ext z
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage, Set.mem_singleton_iff,
      G, Function.uncurry]
    by_cases hz : z.2 ∈ N
    · simp [hz]
    · simp [hz]
  have hpred : MeasurableSet[F.predictable] ((Set.univ : Set ℝ≥0) ×ˢ N) := by
    rw [hset]
    exact hGm (measurableSet_singleton 1)
  have hzero : trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas ((Set.univ : Set ℝ≥0) ×ˢ N) = 0 := by
    show ((timeMeasure_T T).prod μ).trim F.predictable_le_prod _ = 0
    rw [trim_measurableSet_eq _ hpred, Measure.prod_prod, hN0, mul_zero]
  refine hmem.ae_eq ?_
  refine ae_iff.2 (measure_mono_null ?_ hzero)
  intro z hz
  refine ⟨Set.mem_univ _, ?_⟩
  by_contra hzN
  apply hz
  show Nᶜ.indicator (fun ω => Real.sqrt (g (Z z.1 ω))) z.2 = Real.sqrt (g (Z z.1 z.2))
  exact Set.indicator_of_mem (Set.mem_compl hzN) _

end RateIntegrand

/-! ## The SDE without the square-integrability premise -/

/-- `kurtzSDEPathsNN_of_continuousIto` with the square-integrability premise discharged from
continuous rates `f_l ≤ ε_l` and an adapted state with almost surely continuous paths. -/
theorem kurtzSDEPathsNN_of_continuousIto_rates
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] {d : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    {B : ι → ℝ≥0 → Ω → ℝ} [∀ l, IsFilteredPreBrownian (B l) F P]
    (hB : ∀ l ω, Continuous (fun t => B l t ω)) (hBmeas : ∀ l t, Measurable (B l t))
    (hnull : ∀ t A, MeasurableSet A → P A = 0 → MeasurableSet[F t] A)
    {N : ℕ} (hN : 0 < N) {f : ι → (Fin d → ℝ) → ℝ} (hf : ∀ l, Continuous (f l))
    {eps : ι → ℝ} (hfB : ∀ l x, f l x ≤ eps l)
    {v : ι → Fin d → ℝ} {T : ℝ≥0}
    {Z : ℝ≥0 → Ω → Fin d → ℝ} (hZa : ∀ t, Measurable[F t] (Z t)) {x₀ : Fin d → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => Z t ω)
    (heq : ∀ᵐ ω ∂P, ∀ t ≤ T, Z t ω =
      Ripple.Stochastic.StrongSDE.sdeRhs (fun l => continuousItoOfFun P F T (hB l) (hBmeas l)) v
        (fun l x => Real.sqrt (f l x)) (tcDrift f v) x₀ N Z t ω) :
    ∀ᵐ ω ∂P, KMTTransfer.KurtzSDEPathsNN N f v T Z
      (fun l => continuousItoOfFun P F T (hB l) (hBmeas l)
        (fun s ω => Real.sqrt ((N : ℝ) * f l (Z s ω))))
      (fun _ => x₀) ω :=
  KMTTransfer.kurtzSDEPathsNN_of_continuousIto hB hBmeas hN
    (fun l => memLp_sqrt_rate_of_ae T (hBmeas l) hnull (hf l) (hfB l) hZa hcont)
    hcont heq

/-! ## The `U_N` maximal bounds on the channel space -/

section Channel

attribute [local instance] channelBrownian_isFilteredPreBrownian_augmented

variable {m d : ℕ}

/-- The channel integrand `v_{l,i} sqrt (f_l (Z))` of coordinate `i`. -/
def sectionFourIntegrand (v : Fin m → Fin d → ℝ) (f : Fin m → (Fin d → ℝ) → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (i : Fin d) (l : Fin m) (t : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) : ℝ :=
  v l i * Real.sqrt (f l (Z t ω))

/-- The common bound `Σ_l ‖v_l‖ sqrt ε_l` of all integrands. -/
def sectionFourIntegrandBound (v : Fin m → Fin d → ℝ) (eps : Fin m → ℝ) : ℝ :=
  ∑ l, ‖v l‖ * Real.sqrt (eps l)

theorem sectionFourIntegrandBound_nonneg (v : Fin m → Fin d → ℝ) (eps : Fin m → ℝ) :
    0 ≤ sectionFourIntegrandBound v eps :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

variable {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}

theorem abs_sectionFourIntegrand_le (hfB : ∀ l x, f l x ≤ eps l) (i : Fin d) (l : Fin m)
    (t : ℝ≥0) (ω : channelKMTSpace (Fin m)) :
    |sectionFourIntegrand v f Z i l t ω| ≤ sectionFourIntegrandBound v eps := by
  unfold sectionFourIntegrand sectionFourIntegrandBound
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hvi : |v l i| ≤ ‖v l‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (v l) i
  refine (mul_le_mul hvi (Real.sqrt_le_sqrt (hfB l _)) (Real.sqrt_nonneg _)
    (norm_nonneg _)).trans ?_
  exact Finset.single_le_sum
    (fun k (_ : k ∈ Finset.univ) => mul_nonneg (norm_nonneg (v k)) (Real.sqrt_nonneg (eps k)))
    (Finset.mem_univ l)

theorem sectionFourIntegrand_adapted (hf : ∀ l, Continuous (f l))
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t)) (i : Fin d)
    (l : Fin m) (t : ℝ≥0) :
    Measurable[augmentedChannelBrownianFiltration t] (sectionFourIntegrand v f Z i l t) :=
  ((Real.continuous_sqrt.comp (hf l)).measurable.comp (hZa t)).const_mul _

theorem sectionFourIntegrand_continuous (hf : ∀ l, Continuous (f l))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (i : Fin d) (l : Fin m)
    (ω : channelKMTSpace (Fin m)) :
    Continuous fun t => sectionFourIntegrand v f Z i l t ω :=
  continuous_const.mul (Real.continuous_sqrt.comp ((hf l).comp (hZc ω)))

/-- The bracket of coordinate `i`: `Σ_l ∫_0^T (v_{l,i} sqrt (f_l (Z s)))² ds`. -/
def sectionFourBracket (v : Fin m → Fin d → ℝ) (f : Fin m → (Fin d → ℝ) → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (T : ℝ≥0) (i : Fin d)
    (ω : channelKMTSpace (Fin m)) : ℝ :=
  ∑ l, ∫ s in Ioc (0 : ℝ≥0) T, (sectionFourIntegrand v f Z i l s ω) ^ 2 ∂timeMeasure

/-- (U2) coordinatewise: the bracket is at most `T Σ_l v_{l,i}² ε_l`, for every sample. -/
theorem sectionFourBracket_le_coord (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (T : ℝ≥0) (i : Fin d) (ω : channelKMTSpace (Fin m)) :
    sectionFourBracket v f Z T i ω ≤ (T : ℝ) * ∑ l, (v l i) ^ 2 * eps l := by
  have hT : timeMeasure.real (Ioc (0 : ℝ≥0) T) = (T : ℝ) := by
    rw [Measure.real_def, timeMeasure_Ioc]
    simp
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  have hb : ∀ s ∈ Ioc (0 : ℝ≥0) T,
      ‖(sectionFourIntegrand v f Z i l s ω) ^ 2‖ ≤ (v l i) ^ 2 * eps l := by
    intro s _
    unfold sectionFourIntegrand
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow,
      Real.sq_sqrt (hf0 l _)]
    exact mul_le_mul_of_nonneg_left (hfB l _) (sq_nonneg _)
  have h := norm_setIntegral_le_of_norm_le_const (by rw [timeMeasure_Ioc]; exact
    ENNReal.ofReal_lt_top) hb
  rw [hT] at h
  calc (∫ s in Ioc (0 : ℝ≥0) T, (sectionFourIntegrand v f Z i l s ω) ^ 2 ∂timeMeasure)
      ≤ ‖∫ s in Ioc (0 : ℝ≥0) T, (sectionFourIntegrand v f Z i l s ω) ^ 2 ∂timeMeasure‖ :=
        Real.le_norm_self _
    _ ≤ (v l i) ^ 2 * eps l * T := h
    _ = T * ((v l i) ^ 2 * eps l) := by ring

/-- `Q₀ = T Σ_l ‖v_l‖² ε_l`, a bound for every coordinate. -/
def sectionFourQZero (v : Fin m → Fin d → ℝ) (eps : Fin m → ℝ) (T : ℝ≥0) : ℝ :=
  (T : ℝ) * ∑ l, ‖v l‖ ^ 2 * eps l

/-- (U2): the bracket bound with one constant for all coordinates. -/
theorem sectionFourBracket_le (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (T : ℝ≥0) (i : Fin d) (ω : channelKMTSpace (Fin m)) :
    sectionFourBracket v f Z T i ω ≤ sectionFourQZero v eps T := by
  refine (sectionFourBracket_le_coord hf0 hfB T i ω).trans ?_
  unfold sectionFourQZero
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) T.coe_nonneg
  have he : 0 ≤ eps l := (hf0 l 0).trans (hfB l 0)
  refine mul_le_mul_of_nonneg_right ?_ he
  have hvi : |v l i| ≤ ‖v l‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (v l) i
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hvi 2

/-- A real supremum of a continuous function on `[0,T]` is attained. -/
theorem exists_le_of_le_iSup_Icc {T : ℝ≥0} {g : Icc (0 : ℝ≥0) T → ℝ} (hg : Continuous g)
    {s : ℝ} (hs : s ≤ ⨆ t, g t) : ∃ t, s ≤ g t := by
  haveI : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, zero_le⟩⟩
  obtain ⟨t0, -, ht0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hg.continuousOn
  exact ⟨t0, hs.trans (ciSup_le fun t => ht0 (Set.mem_univ t))⟩

/-- The signed integrand `σ v_{l,i} sqrt (f_l (Z))`, `σ = -1` when `neg`, else `σ = 1`. -/
def sectionFourSignedIntegrand (v : Fin m → Fin d → ℝ) (f : Fin m → (Fin d → ℝ) → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (neg : Bool) (i : Fin d) (l : Fin m)
    (t : ℝ≥0) (ω : channelKMTSpace (Fin m)) : ℝ :=
  (if neg then -1 else 1) * sectionFourIntegrand v f Z i l t ω

theorem sq_sectionFourSignedIntegrand (neg : Bool) (i : Fin d) (l : Fin m) (t : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) :
    (sectionFourSignedIntegrand v f Z neg i l t ω) ^ 2 =
      (sectionFourIntegrand v f Z i l t ω) ^ 2 := by
  unfold sectionFourSignedIntegrand
  cases neg <;> simp

theorem sectionFourSignedIntegrand_adapted (hf : ∀ l, Continuous (f l))
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t)) (neg : Bool)
    (i : Fin d) (l : Fin m) (t : ℝ≥0) :
    Measurable[augmentedChannelBrownianFiltration t]
      (sectionFourSignedIntegrand v f Z neg i l t) :=
  (sectionFourIntegrand_adapted hf hZa i l t).const_mul _

theorem sectionFourSignedIntegrand_continuous (hf : ∀ l, Continuous (f l))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (neg : Bool) (i : Fin d) (l : Fin m)
    (ω : channelKMTSpace (Fin m)) :
    Continuous fun t => sectionFourSignedIntegrand v f Z neg i l t ω :=
  continuous_const.mul (sectionFourIntegrand_continuous hf hZc i l ω)

theorem abs_sectionFourSignedIntegrand_le (hfB : ∀ l x, f l x ≤ eps l) (neg : Bool)
    (i : Fin d) (l : Fin m) (t : ℝ≥0) (ω : channelKMTSpace (Fin m)) :
    |sectionFourSignedIntegrand v f Z neg i l t ω| ≤ sectionFourIntegrandBound v eps := by
  unfold sectionFourSignedIntegrand
  rw [abs_mul]
  have h1 : |(if neg then -1 else 1 : ℝ)| = 1 := by cases neg <;> simp
  rw [h1, one_mul]
  exact abs_sectionFourIntegrand_le hfB i l t ω

variable (v f eps Z)

/-- The supremum over `[0,T]` of the signed channel sum
`Σ_l ∫_0^t σ v_{l,i} sqrt (f_l (Z)) dW_l`. -/
def sectionFourSup (hf : ∀ l, Continuous (f l)) (hfB : ∀ l x, f l x ≤ eps l)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) (neg : Bool) (i : Fin d)
    (ω : channelKMTSpace (Fin m)) : ℝ :=
  ⨆ t : Icc (0 : ℝ≥0) T, ∑ l, channelContinuousIntegral T
    (sectionFourSignedIntegrand v f Z neg i)
    (sectionFourSignedIntegrand_adapted hf hZa neg i)
    (sectionFourSignedIntegrand_continuous hf hZc neg i)
    (sectionFourIntegrandBound v eps)
    (abs_sectionFourSignedIntegrand_le hfB neg i) l ω t

variable {v f eps Z}

/-- The one-sided exponential maximal bound for either sign, with the bracket
`sectionFourBracket`. -/
theorem sectionFourSup_maximal (hf : ∀ l, Continuous (f l))
    (hfB : ∀ l x, f l x ≤ eps l)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) (neg : Bool) (i : Fin d)
    (s q : ℝ) (hs : 0 ≤ s) (hq : 0 < q) :
    channelKMTMeasure (Fin m)
        ({ω | s ≤ sectionFourSup v f eps Z hf hfB hZa hZc T neg i ω} ∩
          {ω | sectionFourBracket v f Z T i ω ≤ q}) ≤
      ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q))) := by
  have hmax := channel_bounded_continuous_exponential_maximal T
    (sectionFourSignedIntegrand v f Z neg i)
    (sectionFourSignedIntegrand_adapted hf hZa neg i)
    (sectionFourSignedIntegrand_continuous hf hZc neg i)
    (sectionFourIntegrandBound_nonneg v eps)
    (abs_sectionFourSignedIntegrand_le hfB neg i) hs hq
  refine le_trans (measure_mono ?_) hmax
  rintro ω ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · refine exists_le_of_le_iSup_Icc ?_ h1
    exact continuous_finset_sum _ fun l _ =>
      (channelContinuousIntegral T _ _ _ _ _ l ω).continuous
  · have h2' : sectionFourBracket v f Z T i ω ≤ q := h2
    unfold sectionFourBracket at h2'
    simpa only [sq_sectionFourSignedIntegrand] using h2'

/-- The hypotheses `hbr`, `hmaxp`, `hmaxm` of `SectionFourAssembly.sectionFour_U_tail`, with
`Sp i = sectionFourSup … false i`, `Sm i = sectionFourSup … true i`, `br i = sectionFourBracket`
and `Q₀ = sectionFourQZero v eps T`. -/
theorem sectionFour_U_maximal_hypotheses (hf : ∀ l, Continuous (f l))
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) :
    (∀ i, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      sectionFourBracket v f Z T i ω ≤ sectionFourQZero v eps T) ∧
    (∀ (i : Fin d) (s q : ℝ), 0 ≤ s → 0 < q →
      channelKMTMeasure (Fin m)
        ({ω | s ≤ sectionFourSup v f eps Z hf hfB hZa hZc T false i ω} ∩
          {ω | sectionFourBracket v f Z T i ω ≤ q}) ≤
        ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q)))) ∧
    (∀ (i : Fin d) (s q : ℝ), 0 ≤ s → 0 < q →
      channelKMTMeasure (Fin m)
        ({ω | s ≤ sectionFourSup v f eps Z hf hfB hZa hZc T true i ω} ∩
          {ω | sectionFourBracket v f Z T i ω ≤ q}) ≤
        ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q)))) :=
  ⟨fun i => ae_of_all _ fun ω => sectionFourBracket_le hf0 hfB T i ω,
    fun i s q hs hq => sectionFourSup_maximal hf hfB hZa hZc T false i s q hs hq,
    fun i s q hs hq => sectionFourSup_maximal hf hfB hZa hZc T true i s q hs hq⟩

/-- (U3) on the channel space: the tail of any `U` controlled by the two signed suprema. -/
theorem sectionFour_U_tail_channel (hf : ∀ l, Continuous (f l))
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0)
    {U : channelKMTSpace (Fin m) → ℝ} {G : ℝ} (hG : 0 < G)
    (hQ0 : 0 < sectionFourQZero v eps T)
    (hU : ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ c : ℝ, 0 ≤ c →
      (∀ i, sectionFourSup v f eps Z hf hfB hZa hZc T false i ω ≤ c ∧
        sectionFourSup v f eps Z hf hfB hZa hZc T true i ω ≤ c) → U ω ≤ G * c)
    {r : ℝ} (hr : 0 ≤ r) :
    channelKMTMeasure (Fin m) {ω | r < U ω} ≤
      ENNReal.ofReal (SectionFourAssembly.sectionFourAU d *
        Real.exp (-SectionFourAssembly.sectionFourBU G (sectionFourQZero v eps T) * r ^ 2)) := by
  obtain ⟨hbr, hmaxp, hmaxm⟩ := sectionFour_U_maximal_hypotheses hf hf0 hfB hZa hZc T
  exact SectionFourAssembly.sectionFour_U_tail hG hQ0 hU hbr hmaxp hmaxm hr

/-- The channel integral is the continuous Itô integral `continuousItoOfFun` at every time of
the window, for every sample. -/
theorem channelContinuousIntegral_eq_continuousItoOfFun (T : ℝ≥0)
    (H : Fin m → ℝ≥0 → channelKMTSpace (Fin m) → ℝ)
    (ha : ∀ j t, Measurable[augmentedChannelBrownianFiltration t] (H j t))
    (hc : ∀ j ω, Continuous (fun t => H j t ω)) (K : ℝ)
    (hb : ∀ j t ω, |H j t ω| ≤ K) (j : Fin m) (ω : channelKMTSpace (Fin m))
    (t : Icc (0 : ℝ≥0) T) :
    channelContinuousIntegral T H ha hc K hb j ω t =
      continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
        (channelBrownian_continuous j) (measurable_channelBrownian j) (H j) t.val ω := by
  rw [continuousItoOfFun_of_memLp T (channelBrownian_continuous j) (measurable_channelBrownian j)
    (integrandMemLp T (measurable_channelBrownian j) (H j) (ha j) (hc j) K (hb j))]
  have ht : (⟨min t.val T, zero_le, min_le_right _ _⟩ : Icc (0 : ℝ≥0) T) = t :=
    Subtype.ext (min_eq_left t.2.2)
  unfold continuousItoNN
  rw [ht]
  rfl

/-- The integral of the negative integrand is the negative of the integral, almost surely
for all times: the two signed channel sums are `±` one process. -/
theorem sectionFour_channelSum_neg (hf : ∀ l, Continuous (f l))
    (hfB : ∀ l x, f l x ≤ eps l)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) (i : Fin d) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t,
      ∑ l, continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (fun s ω => -1 * sectionFourIntegrand v f Z i l s ω) t ω =
        -∑ l, continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourIntegrand v f Z i l) t ω := by
  have h : ∀ l, ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t,
      continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (fun s ω => -1 * sectionFourIntegrand v f Z i l s ω) t ω =
        -1 * continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourIntegrand v f Z i l) t ω := fun l =>
    continuousItoOfFun_const_mul T (channelBrownian_continuous l) (measurable_channelBrownian l)
      (integrandMemLp T (measurable_channelBrownian l) _ (sectionFourIntegrand_adapted hf hZa i l)
        (sectionFourIntegrand_continuous hf hZc i l) _ (abs_sectionFourIntegrand_le hfB i l)) _
  filter_upwards [ae_all_iff.2 h] with ω hω t
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hω l t]
  ring

end Channel

end Ripple.Kurtz.StrongApprox
