import Ripple.Kurtz.StrongApprox.SectionFourChannelBounds

/-!
# The `R_N` maximal bounds on the channel space

For a continuous adapted state `Z` and a deterministic continuous path `X`, the integrands of
coordinate `i` are

`H_{l,i} = ± sqrt N · (v_{l,i} sqrt (f_l (Z t)) - v_{l,i} sqrt (f_l (X t)))`.

Under the square-root Lipschitz condition `|sqrt (f_l x) - sqrt (f_l y)| ≤ Lg_l ‖x - y‖` (a model
condition of Kurtz, Section 4), the bracket `Σ_l ∫_0^T H_{l,i}²` is at most `c₁ U²`, where
`U = pathSupIcc T (sqrt N (Z - X))` and `c₁ = T Σ_l ‖v_l‖² Lg_l²`
(coordinatewise `T Σ_l v_{l,i}² Lg_l²`). The multi-channel exponential maximal inequality gives
the one-sided bounds for both signs. `sectionFour_R_maximal_hypotheses` packages `hbrH`,
`hmaxHp`, `hmaxHm` as `SectionFourAssembly.sectionFour_R_tail` consumes them.

`sectionFourRemainder_channelSum_eq` identifies the summed integral with
`sqrt N` times the difference of the channel sums with `sqrt (f (Z))` and with `sqrt (f (X))`,
almost surely for all times.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic Ripple.Stochastic.ContinuousItoLinear
open Ripple.Stochastic.ContinuousAdaptedIntegrand Ripple.Stochastic.FilteredItoIntegralL2
open SectionFourAssembly

/-! ## Rational path suprema dominate continuous paths -/

/-- On `[0,T]` a path continuous there is dominated by its rational supremum. -/
theorem norm_le_pathSupIcc {Ω : Type*} {d : ℕ} {T : ℝ} {Y : ℝ → Ω → (Fin d → ℝ)} {ω : Ω}
    (hY : ContinuousOn (fun t => Y t ω) (Icc 0 T)) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ‖Y s ω‖ ≤ pathSupIcc T Y ω := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hY
  have hfin : (⨆ q : RatIcc T, ENNReal.ofReal ‖Y (q : ℝ) ω‖) ≠ ⊤ :=
    ((iSup_le fun q => ENNReal.ofReal_le_ofReal
      (by simpa only [norm_norm] using hC _ q.2)).trans_lt ENNReal.ofReal_lt_top).ne
  have hq : ∀ q : ℚ, (q : ℝ) ∈ Icc 0 T → ‖Y q ω‖ ≤ pathSupIcc T Y ω := by
    intro q hq
    unfold pathSupIcc
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
    exact le_iSup (fun q : RatIcc T => ENNReal.ofReal ‖Y (q : ℝ) ω‖) ⟨q, hq⟩
  set S := pathSupIcc T Y ω
  have hK : IsClosed (Icc 0 T ∩ (fun x => ‖Y x ω‖) ⁻¹' Iic S) :=
    hY.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  rcases eq_or_lt_of_le (hs.1.trans hs.2) with hT | hT
  · have hs0 : s = 0 := le_antisymm (hT ▸ hs.2) hs.1
    rw [hs0]
    have h0 : ((0 : ℚ) : ℝ) ∈ Icc (0 : ℝ) T := by
      rw [Rat.cast_zero]
      exact ⟨le_rfl, hT ▸ le_rfl⟩
    simpa using hq 0 h0
  · have hsub : Ioo 0 T ∩ range ((↑) : ℚ → ℝ) ⊆ Icc 0 T ∩ (fun x => ‖Y x ω‖) ⁻¹' Iic S := by
      rintro x ⟨hx, q, rfl⟩
      exact ⟨Ioo_subset_Icc_self hx, hq q (Ioo_subset_Icc_self hx)⟩
    have hIoo : Ioo 0 T ⊆ Icc 0 T ∩ (fun x => ‖Y x ω‖) ⁻¹' Iic S :=
      (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo).trans
        (closure_minimal hsub hK)
    have hIcc : Icc 0 T ⊆ Icc 0 T ∩ (fun x => ‖Y x ω‖) ⁻¹' Iic S := by
      intro x hx
      rw [← closure_Ioo hT.ne] at hx
      exact closure_minimal hIoo hK hx
    exact (hIcc hs).2

section Channel

attribute [local instance] channelBrownian_isFilteredPreBrownian_augmented

variable {m d : ℕ}

/-- `U = sup_{q ∈ ℚ ∩ [0,T]} ‖sqrt N (Z q - X q)‖`. -/
def sectionFourRemainderU (N : ℕ) (X : ℝ≥0 → Fin d → ℝ)
    (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (T : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) : ℝ :=
  pathSupIcc (T : ℝ) (fun t ω => Real.sqrt N • (Z t.toNNReal ω - X t.toNNReal)) ω

/-- The remainder integrand `sqrt N (v_{l,i} sqrt (f_l (Z t)) - v_{l,i} sqrt (f_l (X t)))`. -/
def sectionFourRemIntegrand (N : ℕ) (v : Fin m → Fin d → ℝ) (f : Fin m → (Fin d → ℝ) → ℝ)
    (X : ℝ≥0 → Fin d → ℝ) (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (i : Fin d)
    (l : Fin m) (t : ℝ≥0) (ω : channelKMTSpace (Fin m)) : ℝ :=
  Real.sqrt N * (sectionFourIntegrand v f Z i l t ω -
    sectionFourIntegrand v f (fun t _ => X t) i l t ω)

/-- The signed remainder integrand. -/
def sectionFourRemSigned (N : ℕ) (v : Fin m → Fin d → ℝ) (f : Fin m → (Fin d → ℝ) → ℝ)
    (X : ℝ≥0 → Fin d → ℝ) (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (neg : Bool)
    (i : Fin d) (l : Fin m) (t : ℝ≥0) (ω : channelKMTSpace (Fin m)) : ℝ :=
  (if neg then -1 else 1) * sectionFourRemIntegrand N v f X Z i l t ω

/-- The common bound `2 sqrt N Σ_l ‖v_l‖ sqrt ε_l`. -/
def sectionFourRemBound (N : ℕ) (v : Fin m → Fin d → ℝ) (eps : Fin m → ℝ) : ℝ :=
  Real.sqrt N * (2 * sectionFourIntegrandBound v eps)

theorem sectionFourRemBound_nonneg (N : ℕ) (v : Fin m → Fin d → ℝ) (eps : Fin m → ℝ) :
    0 ≤ sectionFourRemBound N v eps :=
  mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg zero_le_two (sectionFourIntegrandBound_nonneg v eps))

variable {N : ℕ} {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {X : ℝ≥0 → Fin d → ℝ} {Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ}

theorem sq_sectionFourRemSigned (neg : Bool) (i : Fin d) (l : Fin m) (t : ℝ≥0)
    (ω : channelKMTSpace (Fin m)) :
    (sectionFourRemSigned N v f X Z neg i l t ω) ^ 2 =
      (sectionFourRemIntegrand N v f X Z i l t ω) ^ 2 := by
  unfold sectionFourRemSigned
  cases neg <;> simp

theorem sectionFourRemSigned_adapted (hf : ∀ l, Continuous (f l))
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t)) (neg : Bool)
    (i : Fin d) (l : Fin m) (t : ℝ≥0) :
    Measurable[augmentedChannelBrownianFiltration t]
      (sectionFourRemSigned N v f X Z neg i l t) := by
  have hX : ∀ t, Measurable[augmentedChannelBrownianFiltration t]
      (fun _ : channelKMTSpace (Fin m) => X t) := fun _ => measurable_const
  exact (((sectionFourIntegrand_adapted hf hZa i l t).sub
    (sectionFourIntegrand_adapted (Z := fun t _ => X t) hf hX i l t)).const_mul _).const_mul _

theorem sectionFourRemSigned_continuous (hf : ∀ l, Continuous (f l))
    (hX : Continuous X) (hZc : ∀ ω, Continuous fun t => Z t ω) (neg : Bool) (i : Fin d)
    (l : Fin m) (ω : channelKMTSpace (Fin m)) :
    Continuous fun t => sectionFourRemSigned N v f X Z neg i l t ω :=
  continuous_const.mul (continuous_const.mul
    ((sectionFourIntegrand_continuous hf hZc i l ω).sub
      (sectionFourIntegrand_continuous (Z := fun t _ => X t) hf (fun _ => hX) i l ω)))

theorem abs_sectionFourRemSigned_le (hfB : ∀ l x, f l x ≤ eps l) (neg : Bool) (i : Fin d)
    (l : Fin m) (t : ℝ≥0) (ω : channelKMTSpace (Fin m)) :
    |sectionFourRemSigned N v f X Z neg i l t ω| ≤ sectionFourRemBound N v eps := by
  unfold sectionFourRemSigned sectionFourRemIntegrand sectionFourRemBound
  rw [abs_mul]
  have h1 : |(if neg then -1 else 1 : ℝ)| = 1 := by cases neg <;> simp
  rw [h1, one_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have ha := abs_le.1 (abs_sectionFourIntegrand_le (v := v) (Z := Z) hfB i l t ω)
  have hb := abs_le.1
    (abs_sectionFourIntegrand_le (v := v) (Z := fun t _ => X t) hfB i l t ω)
  exact abs_le.2 ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩

/-- The bracket of coordinate `i`: `Σ_l ∫_0^T H_{l,i}²`. -/
def sectionFourRemBracket (N : ℕ) (v : Fin m → Fin d → ℝ) (f : Fin m → (Fin d → ℝ) → ℝ)
    (X : ℝ≥0 → Fin d → ℝ) (Z : ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ) (T : ℝ≥0)
    (i : Fin d) (ω : channelKMTSpace (Fin m)) : ℝ :=
  ∑ l, ∫ s in Ioc (0 : ℝ≥0) T, (sectionFourRemIntegrand N v f X Z i l s ω) ^ 2 ∂timeMeasure

/-- `c₁ = T Σ_l ‖v_l‖² Lg_l²`, uniform in the coordinate. -/
def sectionFourCOne (v : Fin m → Fin d → ℝ) (Lg : Fin m → ℝ) (T : ℝ≥0) : ℝ :=
  (T : ℝ) * ∑ l, ‖v l‖ ^ 2 * Lg l ^ 2

/-- Pointwise: `|H_{l,i}(s)| ≤ ‖v_l‖ Lg_l U` on `[0,T]`. -/
theorem abs_sectionFourRemIntegrand_le {Lg : Fin m → ℝ} (hLg0 : ∀ l, 0 ≤ Lg l)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (hX : Continuous X) (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) (i : Fin d)
    (l : Fin m) {s : ℝ≥0} (hs : s ≤ T) (ω : channelKMTSpace (Fin m)) :
    |sectionFourRemIntegrand N v f X Z i l s ω| ≤
      ‖v l‖ * (Lg l * sectionFourRemainderU N X Z T ω) := by
  have hY : ContinuousOn (fun t : ℝ =>
      Real.sqrt N • (Z t.toNNReal ω - X t.toNNReal)) (Icc 0 (T : ℝ)) :=
    (continuous_const.smul (((hZc ω).comp continuous_real_toNNReal).sub
      (hX.comp continuous_real_toNNReal))).continuousOn
  have hU := norm_le_pathSupIcc (Y := fun t ω =>
      Real.sqrt N • (Z t.toNNReal ω - X t.toNNReal)) hY
    (show (s : ℝ) ∈ Icc 0 (T : ℝ) from ⟨s.coe_nonneg, by exact_mod_cast hs⟩)
  simp only [Real.toNNReal_coe] at hU
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hU
  unfold sectionFourRemIntegrand sectionFourIntegrand
  have hvi : |v l i| ≤ ‖v l‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (v l) i
  have hdiff := hLg l (Z s ω) (X s)
  rw [show Real.sqrt N * (v l i * Real.sqrt (f l (Z s ω)) - v l i * Real.sqrt (f l (X s))) =
      v l i * (Real.sqrt N * (Real.sqrt (f l (Z s ω)) - Real.sqrt (f l (X s)))) by ring,
    abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul hvi ?_ (by positivity) (norm_nonneg _)
  calc Real.sqrt N * |Real.sqrt (f l (Z s ω)) - Real.sqrt (f l (X s))|
      ≤ Real.sqrt N * (Lg l * ‖Z s ω - X s‖) :=
        mul_le_mul_of_nonneg_left hdiff (Real.sqrt_nonneg _)
    _ = Lg l * (Real.sqrt N * ‖Z s ω - X s‖) := by ring
    _ ≤ Lg l * sectionFourRemainderU N X Z T ω := mul_le_mul_of_nonneg_left hU (hLg0 l)

/-- (R4): the bracket is at most `c₁ U² = T Σ_l ‖v_l‖² Lg_l² · U²`, for every sample. -/
theorem sectionFourRemBracket_le {Lg : Fin m → ℝ} (hLg0 : ∀ l, 0 ≤ Lg l)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (hX : Continuous X) (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) (i : Fin d)
    (ω : channelKMTSpace (Fin m)) :
    sectionFourRemBracket N v f X Z T i ω ≤
      sectionFourCOne v Lg T * sectionFourRemainderU N X Z T ω ^ 2 := by
  have hT : timeMeasure.real (Ioc (0 : ℝ≥0) T) = (T : ℝ) := by
    rw [Measure.real_def, timeMeasure_Ioc]
    simp
  unfold sectionFourRemBracket sectionFourCOne
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  have hb : ∀ s ∈ Ioc (0 : ℝ≥0) T, ‖(sectionFourRemIntegrand N v f X Z i l s ω) ^ 2‖ ≤
      ‖v l‖ ^ 2 * Lg l ^ 2 * sectionFourRemainderU N X Z T ω ^ 2 := by
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have h := abs_sectionFourRemIntegrand_le (N := N) (v := v) hLg0 hLg hX hZc T i l hs.2 ω
    calc |sectionFourRemIntegrand N v f X Z i l s ω| ^ 2
        ≤ (‖v l‖ * (Lg l * sectionFourRemainderU N X Z T ω)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = ‖v l‖ ^ 2 * Lg l ^ 2 * sectionFourRemainderU N X Z T ω ^ 2 := by ring
  have h := norm_setIntegral_le_of_norm_le_const (by rw [timeMeasure_Ioc]; exact
    ENNReal.ofReal_lt_top) hb
  rw [hT] at h
  calc (∫ s in Ioc (0 : ℝ≥0) T, (sectionFourRemIntegrand N v f X Z i l s ω) ^ 2 ∂timeMeasure)
      ≤ ‖∫ s in Ioc (0 : ℝ≥0) T,
          (sectionFourRemIntegrand N v f X Z i l s ω) ^ 2 ∂timeMeasure‖ := Real.le_norm_self _
    _ ≤ ‖v l‖ ^ 2 * Lg l ^ 2 * sectionFourRemainderU N X Z T ω ^ 2 * T := h
    _ = T * (‖v l‖ ^ 2 * Lg l ^ 2 * sectionFourRemainderU N X Z T ω ^ 2) := by ring

variable (N v f eps X Z)

/-- The supremum over `[0,T]` of the signed remainder channel sum. -/
def sectionFourRemSup (hf : ∀ l, Continuous (f l)) (hfB : ∀ l x, f l x ≤ eps l)
    (hX : Continuous X)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) (neg : Bool) (i : Fin d)
    (ω : channelKMTSpace (Fin m)) : ℝ :=
  ⨆ t : Icc (0 : ℝ≥0) T, ∑ l, channelContinuousIntegral T
    (sectionFourRemSigned N v f X Z neg i)
    (sectionFourRemSigned_adapted hf hZa neg i)
    (sectionFourRemSigned_continuous hf hX hZc neg i)
    (sectionFourRemBound N v eps)
    (abs_sectionFourRemSigned_le hfB neg i) l ω t

variable {N v f eps X Z}

theorem sectionFourRemSup_maximal (hf : ∀ l, Continuous (f l)) (hfB : ∀ l x, f l x ≤ eps l)
    (hX : Continuous X)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) (neg : Bool) (i : Fin d)
    (s q : ℝ) (hs : 0 ≤ s) (hq : 0 < q) :
    channelKMTMeasure (Fin m)
        ({ω | s ≤ sectionFourRemSup N v f eps X Z hf hfB hX hZa hZc T neg i ω} ∩
          {ω | sectionFourRemBracket N v f X Z T i ω ≤ q}) ≤
      ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q))) := by
  have hmax := channel_bounded_continuous_exponential_maximal T
    (sectionFourRemSigned N v f X Z neg i)
    (sectionFourRemSigned_adapted hf hZa neg i)
    (sectionFourRemSigned_continuous hf hX hZc neg i)
    (sectionFourRemBound_nonneg N v eps)
    (abs_sectionFourRemSigned_le hfB neg i) hs hq
  refine le_trans (measure_mono ?_) hmax
  rintro ω ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · refine exists_le_of_le_iSup_Icc ?_ h1
    exact continuous_finsetSum _ fun l _ =>
      (channelContinuousIntegral T _ _ _ _ _ l ω).continuous
  · have h2' : sectionFourRemBracket N v f X Z T i ω ≤ q := h2
    unfold sectionFourRemBracket at h2'
    simpa only [sq_sectionFourRemSigned] using h2'

/-- The hypotheses `hbrH`, `hmaxHp`, `hmaxHm` of `SectionFourAssembly.sectionFour_R_tail`, with
`Tp i = sectionFourRemSup … false i`, `Tm i = sectionFourRemSup … true i`,
`brH i = sectionFourRemBracket`, `U = sectionFourRemainderU` and `c₁ = sectionFourCOne`. -/
theorem sectionFour_R_maximal_hypotheses {Lg : Fin m → ℝ} (hLg0 : ∀ l, 0 ≤ Lg l)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (hf : ∀ l, Continuous (f l)) (hfB : ∀ l x, f l x ≤ eps l) (hX : Continuous X)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) :
    (∀ i, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      sectionFourRemBracket N v f X Z T i ω ≤
        sectionFourCOne v Lg T * sectionFourRemainderU N X Z T ω ^ 2) ∧
    (∀ (i : Fin d) (s q : ℝ), 0 ≤ s → 0 < q →
      channelKMTMeasure (Fin m)
        ({ω | s ≤ sectionFourRemSup N v f eps X Z hf hfB hX hZa hZc T false i ω} ∩
          {ω | sectionFourRemBracket N v f X Z T i ω ≤ q}) ≤
        ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q)))) ∧
    (∀ (i : Fin d) (s q : ℝ), 0 ≤ s → 0 < q →
      channelKMTMeasure (Fin m)
        ({ω | s ≤ sectionFourRemSup N v f eps X Z hf hfB hX hZa hZc T true i ω} ∩
          {ω | sectionFourRemBracket N v f X Z T i ω ≤ q}) ≤
        ENNReal.ofReal (Real.exp (-(s ^ 2) / (2 * q)))) :=
  ⟨fun i => ae_of_all _ fun ω => sectionFourRemBracket_le hLg0 hLg hX hZc T i ω,
    fun i s q hs hq => sectionFourRemSup_maximal hf hfB hX hZa hZc T false i s q hs hq,
    fun i s q hs hq => sectionFourRemSup_maximal hf hfB hX hZa hZc T true i s q hs hq⟩

/-- (R5) on the channel space, with the remainder maximal hypotheses supplied. -/
theorem sectionFour_R_tail_channel {Lg : Fin m → ℝ} (hLg0 : ∀ l, 0 ≤ Lg l)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (hf : ∀ l, Continuous (f l)) (hfB : ∀ l x, f l x ≤ eps l) (hX : Continuous X)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0)
    {R Hsup : channelKMTSpace (Fin m) → ℝ} {G Q0 Q1 B : ℝ} (hG : 0 < G) (hQ0 : 0 < Q0)
    (hQ1 : 0 < Q1) (hB : 0 ≤ B) (hc1 : sectionFourCOne v Lg T ≤ Q1)
    (hUtail : ∀ r : ℝ, 0 ≤ r → channelKMTMeasure (Fin m)
        {ω | r < sectionFourRemainderU N X Z T ω} ≤
      ENNReal.ofReal (sectionFourAU d * Real.exp (-sectionFourBU G Q0 * r ^ 2)))
    (hRU : ∀ᵐ ω ∂channelKMTMeasure (Fin m),
      R ω ≤ G * (Hsup ω + B * sectionFourRemainderU N X Z T ω ^ 2))
    (hHsup : ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ c : ℝ, 0 ≤ c →
      (∀ i, sectionFourRemSup N v f eps X Z hf hfB hX hZa hZc T false i ω ≤ c ∧
        sectionFourRemSup N v f eps X Z hf hfB hX hZa hZc T true i ω ≤ c) → Hsup ω ≤ c)
    {r : ℝ} (hr : 0 ≤ r) :
    channelKMTMeasure (Fin m) {ω | r < R ω} ≤
      ENNReal.ofReal (sectionFourAR d * Real.exp (-sectionFourCR G Q0 Q1 (1 + B) * r)) := by
  obtain ⟨hbrH, hmaxHp, hmaxHm⟩ :=
    sectionFour_R_maximal_hypotheses (N := N) (v := v) (eps := eps) hLg0 hLg hf hfB hX hZa hZc T
  exact sectionFour_R_tail hG hQ0 hQ1 hB hc1
    (ae_of_all _ fun ω => pathSupIcc_nonneg _ _ ω) hUtail hRU hHsup hbrH hmaxHp hmaxHm hr

/-- The summed remainder integral is `sqrt N` times the difference of the channel sums with
`sqrt (f (Z))` and with `sqrt (f (X))`, almost surely for all times. -/
theorem sectionFourRemainder_channelSum_eq (hf : ∀ l, Continuous (f l))
    (hfB : ∀ l x, f l x ≤ eps l) (hX : Continuous X)
    (hZa : ∀ t, Measurable[augmentedChannelBrownianFiltration t] (Z t))
    (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ≥0) (i : Fin d) :
    ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t,
      ∑ l, continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourRemIntegrand N v f X Z i l) t ω =
        Real.sqrt N *
          (∑ l, continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration
              T (channelBrownian_continuous l) (measurable_channelBrownian l)
              (sectionFourIntegrand v f Z i l) t ω -
            ∑ l, continuousItoOfFun (channelKMTMeasure (Fin m))
              augmentedChannelBrownianFiltration T (channelBrownian_continuous l)
              (measurable_channelBrownian l)
              (sectionFourIntegrand v f (fun t _ => X t) i l) t ω) := by
  have hXa : ∀ t, Measurable[augmentedChannelBrownianFiltration t]
      (fun _ : channelKMTSpace (Fin m) => X t) := fun _ => measurable_const
  have hper : ∀ l, ∀ᵐ ω ∂channelKMTMeasure (Fin m), ∀ t,
      continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
          (channelBrownian_continuous l) (measurable_channelBrownian l)
          (sectionFourRemIntegrand N v f X Z i l) t ω =
        Real.sqrt N *
          (continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
              (channelBrownian_continuous l) (measurable_channelBrownian l)
              (sectionFourIntegrand v f Z i l) t ω -
            continuousItoOfFun (channelKMTMeasure (Fin m)) augmentedChannelBrownianFiltration T
              (channelBrownian_continuous l) (measurable_channelBrownian l)
              (sectionFourIntegrand v f (fun t _ => X t) i l) t ω) := by
    intro l
    have hA := integrandMemLp (μ := channelKMTMeasure (Fin m)) T (measurable_channelBrownian l)
      (sectionFourIntegrand v f Z i l) (sectionFourIntegrand_adapted hf hZa i l)
      (sectionFourIntegrand_continuous hf hZc i l) _ (abs_sectionFourIntegrand_le hfB i l)
    have hBm := integrandMemLp (μ := channelKMTMeasure (Fin m)) T (measurable_channelBrownian l)
      (sectionFourIntegrand v f (fun t _ => X t) i l)
      (sectionFourIntegrand_adapted (Z := fun t _ => X t) hf hXa i l)
      (sectionFourIntegrand_continuous (Z := fun t _ => X t) hf (fun _ => hX) i l) _
      (abs_sectionFourIntegrand_le (Z := fun t _ => X t) hfB i l)
    have hBneg : MemLp (Function.uncurry fun s ω =>
        -1 * sectionFourIntegrand v f (fun t _ => X t) i l s ω) 2
        (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := augmentedChannelBrownianFiltration)
          (μ := channelKMTMeasure (Fin m)) T (measurable_channelBrownian l)) :=
      hBm.const_mul (-1)
    have hG : MemLp (Function.uncurry fun s ω =>
        sectionFourIntegrand v f Z i l s ω +
          -1 * sectionFourIntegrand v f (fun t _ => X t) i l s ω) 2
        (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := augmentedChannelBrownianFiltration)
          (μ := channelKMTMeasure (Fin m)) T (measurable_channelBrownian l)) :=
      hA.add hBneg
    have h1 := continuousItoOfFun_const_mul T (channelBrownian_continuous l)
      (measurable_channelBrownian l) hG (Real.sqrt N)
    have h2 := continuousItoOfFun_add T (channelBrownian_continuous l)
      (measurable_channelBrownian l) hA hBneg
    have h3 := continuousItoOfFun_const_mul T (channelBrownian_continuous l)
      (measurable_channelBrownian l) hBm (-1)
    have hrem : sectionFourRemIntegrand N v f X Z i l = fun s ω => Real.sqrt N *
        (sectionFourIntegrand v f Z i l s ω +
          -1 * sectionFourIntegrand v f (fun t _ => X t) i l s ω) := by
      funext s ω
      unfold sectionFourRemIntegrand
      ring
    filter_upwards [h1, h2, h3] with ω e1 e2 e3 t
    rw [hrem, e1 t, e2 t, e3 t]
    ring
  filter_upwards [ae_all_iff.2 hper] with ω hω t
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => hω l t

end Channel

end Ripple.Kurtz.StrongApprox
