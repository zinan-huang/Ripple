import Ripple.Stochastic.KnightStepIntegral
import Ripple.Stochastic.FiniteChannelExponentialLimit

/-!
# Exponentials for bounded integrands with convergent strict-past samples

The producer used here is `FiniteChannelExponentialLimit`, through its
bounded elementary approximation theorem. Continuity of the input integrand
is replaced by convergence of its strict-past samples. The rectangular clock
masks satisfy this condition, as proved in `KnightStepIntegral`.

All approximation, uniform integrability, and mean-one premises are produced
inside this module.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.Knight
open AdaptedContinuousSpace ContinuousItoElementary ContinuousItoConstruction
open FilteredItoIntegralL2 FilteredItoIntegralCLM
open ContinuousAdaptedIntegrand FiniteChannelExponentialLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}

/-- Integrability of the two opposite normalized exponentials already gives
measurability of both the integral and its bracket. This lets consumers use
the normalized-exponential producer without separately proving measurability
of random inverse-time evaluations. -/
theorem aestronglyMeasurable_of_opposite_exponentials (Y Q : Ω → ℝ)
    (hp : Integrable (fun ω => Real.exp (Y ω - Q ω / 2)) P)
    (hm : Integrable (fun ω => Real.exp (-Y ω - Q ω / 2)) P) :
    AEStronglyMeasurable Y P ∧ AEStronglyMeasurable Q P := by
  have hlogp : AEStronglyMeasurable
      (fun ω => Real.log (Real.exp (Y ω - Q ω / 2))) P :=
    (Real.measurable_log.comp_aemeasurable hp.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hlogm : AEStronglyMeasurable
      (fun ω => Real.log (Real.exp (-Y ω - Q ω / 2))) P :=
    (Real.measurable_log.comp_aemeasurable hm.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  constructor
  · have h := AEStronglyMeasurable.mul_const (hlogp.sub hlogm) (1 / 2 : ℝ)
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, Real.log_exp]
    ring
  · have h := (hlogp.add hlogm).neg
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.neg_apply, Pi.add_apply, Real.log_exp]
    ring

section Scalar
variable {B : ℝ≥0 → Ω → ℝ} [IsFilteredPreBrownian B F P]

/-- A bounded adapted process whose strict-past samples converge is in the
actual predictable L² domain. This includes the discontinuous clock masks. -/
theorem sampledIntegrand_memLp (T : ℝ≥0) (hBm : ∀ t, Measurable (B t))
    (G : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (G t))
    (hsample : ∀ t ω, Tendsto
      (fun n : ℕ => G (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ω)
      atTop (nhds (G t ω))) (K : ℝ) (hb : ∀ t ω, |G t ω| ≤ K) :
    MemLp (Function.uncurry G) 2 (trimMeasure_T (𝓖 := F) (μ := P) T hBm) := by
  have hsm : StronglyMeasurable[F.predictable] (Function.uncurry G) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    apply stronglyMeasurable_of_tendsto atTop
      (fun n : ℕ => (measurable_sample ha
        (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity)).stronglyMeasurable)
    apply tendsto_pi_nhds.mpr
    intro z
    exact hsample z.1 z.2
  apply MemLp.of_bound hsm.aestronglyMeasurable K
  exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z.1 z.2

/-- The strict-past grid converges in predictable L², with no continuity
premise and no density hypothesis left to the caller. -/
theorem sampledAssembly_tendsto (T : ℝ≥0) (hBm : ∀ t, Measurable (B t))
    (G : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (G t))
    (hsample : ∀ t ω, Tendsto
      (fun n : ℕ => G (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ω)
      atTop (nhds (G t ω))) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t ω, |G t ω| ≤ K) :
    Tendsto (fun n : ℕ => simpleAssembly_T (𝓖 := F) (μ := P) T hBm
      (sampleSP T hBm G ha K hb (1 / ((n : ℝ≥0) + 1)))) atTop
      (nhds ((sampledIntegrand_memLp (P := P) T hBm G ha hsample K hb).toLp _)) := by
  apply boundedAssembly_tendsto T hBm
  · intro n
    exact ae_of_all _ fun z => sampleSP_bound T hBm G ha hK hb
      (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity) z.1 z.2
  · filter_upwards [(sampledIntegrand_memLp (P := P) T hBm G ha hsample K hb).coeFn_toLp] with z hz
    rw [hz]
    exact hb z.1 z.2
  · filter_upwards [BoundedPredictableApproximation.ae_window (μ := P) T hBm,
      (sampledIntegrand_memLp (P := P) T hBm G ha hsample K hb).coeFn_toLp] with z hz hφ
    rw [hφ]
    have heq : ∀ n : ℕ, ⇑(sampleSP T hBm G ha K hb
        (1 / ((n : ℝ≥0) + 1))).val z.1 z.2 =
        G (leftGrid (1 / ((n : ℝ≥0) + 1)) z.1) z.2 :=
      fun n => sampleSP_apply T hBm G ha K hb
        (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity) hz.1 hz.2 z.2
    simpa only [heq] using hsample z.1 z.2

/-- Bracket convergence uses the same elementary process as the stochastic
integral convergence. There is no independent bracket approximation. -/
theorem sampledBracket_tendsto (T : ℝ≥0) (hBm : ∀ t, Measurable (B t))
    (G : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (G t))
    (hsample : ∀ t ω, Tendsto
      (fun n : ℕ => G (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ω)
      atTop (nhds (G t ω))) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t ω, |G t ω| ≤ K)
    (t : Icc (0 : ℝ≥0) T) (ω : Ω) :
    Tendsto (fun n : ℕ => BoundedStochasticExponential.simpleBracket
      (samplePartition (1 / ((n : ℝ≥0) + 1)) T)
      (fun i ω => G (samplePartition (1 / ((n : ℝ≥0) + 1)) T i) ω)
      (sampleCells (1 / ((n : ℝ≥0) + 1)) T) t.val ω) atTop
      (nhds (∫ s in Ioc (0 : ℝ≥0) t.val, (G s ω) ^ 2 ∂timeMeasure)) := by
  let W := fun n : ℕ => sampleSP T hBm G ha K hb (1 / ((n : ℝ≥0) + 1))
  have hi : Tendsto (fun n => ∫ s, (⇑(W n).val s ω) ^ 2 ∂timeMeasure_T t.val)
      atTop (nhds (∫ s, (G s ω) ^ 2 ∂timeMeasure_T t.val)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => K ^ 2)
    · intro n
      exact ((BoundedPredictableApproximation.measurable_simple_time (W n).val ω).pow_const 2).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply ae_of_all
      intro s
      have hbnd := sampleSP_bound T hBm G ha hK hb
        (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity) s ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (abs_le.mp hbnd).1 (abs_le.mp hbnd).2
    · filter_upwards [ae_restrict_mem (μ := timeMeasure) measurableSet_Ioc] with s hs
      have heq : ∀ n : ℕ, ⇑(W n).val s ω =
          G (leftGrid (1 / ((n : ℝ≥0) + 1)) s) ω :=
        fun n => sampleSP_apply T hBm G ha K hb
          (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity)
          hs.1 (hs.2.trans t.property.2) ω
      simpa only [heq] using (hsample s ω).pow 2
  have heq : ∀ n : ℕ, BoundedStochasticExponential.simpleBracket
      (samplePartition (1 / ((n : ℝ≥0) + 1)) T)
      (fun i ω => G (samplePartition (1 / ((n : ℝ≥0) + 1)) T i) ω)
      (sampleCells (1 / ((n : ℝ≥0) + 1)) T) t.val ω =
      ∫ s, (⇑(W n).val s ω) ^ 2 ∂timeMeasure_T t.val :=
    fun n => sampleSP_bracket T hBm G ha K hb
      (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity) t.val t.property.2 ω
  simpa only [heq, timeMeasure_T] using hi

end Scalar

variable {d : ℕ} (B : Fin d → ℝ≥0 → Ω → ℝ)
  (hB : ∀ i, IsFilteredPreBrownian (B i) F P)

/-- The actual selected continuous integral of one sampled integrand. -/
def sampledChannelIntegral (T : ℝ≥0)
    (hBc : ∀ i ω, Continuous (fun t => B i t ω)) (hBm : ∀ i t, Measurable (B i t))
    (G : Fin d → ℝ≥0 → Ω → ℝ) (ha : ∀ i t, Measurable[F t] (G i t))
    (hsample : ∀ i t ω, Tendsto
      (fun n : ℕ => G i (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ω)
      atTop (nhds (G i t ω))) (K : ℝ) (hb : ∀ i t ω, |G i t ω| ≤ K)
    (i : Fin d) : Ω → C(Icc (0 : ℝ≥0) T, ℝ) := by
  letI := hB i
  exact representative (continuousIto T (hBc i) (hBm i)
    ((sampledIntegrand_memLp (P := P) T (hBm i) (G i) (ha i) (hsample i) K (hb i)).toLp _))

/-- One subsequence gives convergence of every actual continuous channel
integral path. Neither the masks nor the input paths need be continuous. -/
theorem exists_sampled_integral_subsequence (T : ℝ≥0)
    (hBc : ∀ i ω, Continuous (fun t => B i t ω)) (hBm : ∀ i t, Measurable (B i t))
    (G : Fin d → ℝ≥0 → Ω → ℝ) (ha : ∀ i t, Measurable[F t] (G i t))
    (hsample : ∀ i t ω, Tendsto
      (fun n : ℕ => G i (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ω)
      atTop (nhds (G i t ω))) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ i t ω, |G i t ω| ≤ K) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P, ∀ i,
      Tendsto (fun n => simpleIntegralPath T (hBc i)
        (sampleSP T (hBm i) (G i) (ha i) K (hb i)
          (1 / ((ns n : ℝ≥0) + 1))).val ω) atTop
        (nhds (sampledChannelIntegral B hB T hBc hBm G ha hsample K hb i ω)) := by
  let W := fun (i : Fin d) (n : ℕ) =>
    sampleSP T (hBm i) (G i) (ha i) K (hb i) (1 / ((n : ℝ≥0) + 1))
  have hpath : ∀ i, TendstoInMeasure P
      (fun n ω => simpleIntegralPath T (hBc i) (W i n).val ω) atTop
      (sampledChannelIntegral B hB T hBc hBm G ha hsample K hb i) := by
    intro i
    letI := hB i
    have hW := sampledAssembly_tendsto (P := P) T (hBm i) (G i) (ha i) (hsample i) hK (hb i)
    have hp : Tendsto (fun n => boundedSimplePathLp (μ := P) T (hBc i) (hBm i) (W i n))
        atTop (nhds (continuousIto T (hBc i) (hBm i)
          ((sampledIntegrand_memLp (P := P) T (hBm i) (G i) (ha i) (hsample i) K (hb i)).toLp _))) :=
      continuousIntegral_tendsto _ (simpleAssembly_T_denseRange T (hBm i)) _ _
        (boundedSimplePathLp_norm_le (μ := P) T (hBc i) (hBm i)) hW
    apply TendstoInMeasure.congr
      (fun n => (simpleIntegralPath_memLp (μ := P) T (hBc i) (hBm i) (W i n).val).coeFn_toLp)
      (representative_ae _) (tendstoInMeasure_of_tendsto_Lp hp)
  obtain ⟨ns, hns, hconv⟩ := exists_common_subsequence
    (fun i n ω => simpleIntegralPath T (hBc i) (W i n).val ω)
    (sampledChannelIntegral B hB T hBc hBm G ha hsample K hb) Finset.univ
    (fun i _ => hpath i)
  exact ⟨ns, hns, ae_all_iff.mpr fun i => hconv i (Finset.mem_univ i)⟩

variable
  (hcoord : ∀ r t : ℝ≥0, r ≤ t → iIndepFun (fun i ω => B i t ω - B i r ω) P)
  (hpast : ∀ r t : ℝ≥0, r ≤ t →
    Indep (MeasurableSpace.comap (fun ω i => B i t ω - B i r ω) inferInstance) (F r) P)

include hcoord hpast in
/-- The normalized exponential of the actual finite-channel integral is
integrable and has mean one. The discontinuous-input bridge, common grid,
uniform square bound, and Vitali passage are all discharged in the proof. -/
theorem sampled_vector_normalized_exponential (T : ℝ≥0)
    (hBc : ∀ i ω, Continuous (fun t => B i t ω)) (hBm : ∀ i t, Measurable (B i t))
    (hnull : ∀ t S, MeasurableSet S → P S = 0 → MeasurableSet[F t] S)
    (G : Fin d → ℝ≥0 → Ω → ℝ) (ha : ∀ i t, Measurable[F t] (G i t))
    (hsample : ∀ i t ω, Tendsto
      (fun n : ℕ => G i (leftGrid (1 / ((n : ℝ≥0) + 1)) t) ω)
      atTop (nhds (G i t ω))) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ i t ω, |G i t ω| ≤ K)
    (a : ℝ) (t : Icc (0 : ℝ≥0) T) :
    Integrable (fun ω => Real.exp
      (a * (∑ i, sampledChannelIntegral B hB T hBc hBm G ha hsample K hb i ω t) -
        a ^ 2 * (∑ i, ∫ r in Ioc (0 : ℝ≥0) t.val, (G i r ω) ^ 2 ∂timeMeasure) / 2)) P ∧
      (∫ ω, Real.exp
        (a * (∑ i, sampledChannelIntegral B hB T hBc hBm G ha hsample K hb i ω t) -
          a ^ 2 * (∑ i, ∫ r in Ioc (0 : ℝ≥0) t.val, (G i r ω) ^ 2 ∂timeMeasure) / 2) ∂P) = 1 := by
  let δ := fun n : ℕ => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)
  let s := fun n => samplePartition (δ n) T
  let c := fun n k ω i => G i (s n k) ω
  let N := fun n => sampleCells (δ n) T
  let M := fun (t : Icc (0 : ℝ≥0) T) ω =>
    ∑ i, sampledChannelIntegral B hB T hBc hBm G ha hsample K hb i ω t
  let Q := fun (t : Icc (0 : ℝ≥0) T) ω =>
    ∑ i, ∫ r in Ioc (0 : ℝ≥0) t.val, (G i r ω) ^ 2 ∂timeMeasure
  have hs : ∀ n, Monotone (s n) := fun n => samplePartition_mono (δ n) T
  have hz : ∀ n, s n 0 = 0 := fun n => samplePartition_zero (δ n) T
  have hca : ∀ n k, Measurable[F (s n k)] (c n k) := by
    intro n k
    letI : MeasurableSpace Ω := F (s n k)
    exact measurable_pi_lambda _ fun i => ha i (s n k)
  have hcb : ∀ n k ω i, |c n k ω i| ≤ K := fun n k ω i => hb i (s n k) ω
  have hconvQ : ∀ ω (t : Icc (0 : ℝ≥0) T), Tendsto
      (fun n => vectorBracket (s n) (c n) (N n) t.val ω) atTop (nhds (Q t ω)) := by
    intro ω t
    apply tendsto_finset_sum
    intro i _
    letI := hB i
    exact sampledBracket_tendsto T (hBm i) (G i) (ha i) (hsample i) hK (hb i) t ω
  obtain ⟨ns, hns, hpaths⟩ :=
    exists_sampled_integral_subsequence B hB T hBc hBm G ha hsample hK hb
  have hconvM : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ≥0) T, Tendsto
      (fun n => vectorSum B (s (ns n)) (c (ns n)) (N (ns n)) t.val ω)
      atTop (nhds (M t ω)) := by
    filter_upwards [hpaths] with ω hω t
    apply tendsto_finset_sum
    intro i _
    have hp := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto
      (sampledChannelIntegral B hB T hBc hBm G ha hsample K hb i ω)).comp (hω i)
    have heq : ∀ n, BoundedStochasticExponential.simpleSum (B i) (s (ns n))
        (fun k ω => c (ns n) k ω i) (N (ns n)) t.val ω =
        simpleIntegralPath T (hBc i)
          (sampleSP T (hBm i) (G i) (ha i) K (hb i) (δ (ns n))).val ω t := by
      intro n
      letI := hB i
      rw [simpleIntegralPath_apply T (hBc i) (hBm i)]
      exact sampleSP_simpleSum T (hBm i) (G i) (ha i) K (hb i) (δ (ns n)) t.val ω
    simpa only [heq] using hp
  have hMa : ∀ t : Icc (0 : ℝ≥0) T, StronglyMeasurable[F t.val] (M t) := by
    intro t
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    letI := hB i
    exact continuousIto_representative_adapted T (hBc i) (hBm i) hnull
      ((sampledIntegrand_memLp (P := P) T (hBm i) (G i) (ha i) (hsample i) K (hb i)).toLp _) t
  have hQa : ∀ t : Icc (0 : ℝ≥0) T, StronglyMeasurable[F t.val] (Q t) := by
    intro t
    have heq : Q t = fun ω => Filter.limsup
        (fun n => vectorBracket (s n) (c n) (N n) t.val ω) atTop :=
      funext fun ω => (hconvQ ω t).limsup_eq.symm
    rw [heq]
    exact (Measurable.limsup fun n =>
      (vectorBracket_stronglyAdapted (s n) (hs n) (c n) (hca n) (N n) t.val).measurable).stronglyMeasurable
  have hmart := vector_stochastic_exponential_compact_limit B hB hcoord hpast T
    (fun n => s (ns n)) (fun n => hs (ns n)) (fun n => hz (ns n))
    (fun n => c (ns n)) (fun n => hca (ns n)) (fun n => N (ns n))
    (fun n => hcb (ns n)) M Q hMa hQa hconvM
    (ae_of_all _ fun ω t => (hconvQ ω t).comp hns.tendsto_atTop) a
  have hmzero : ∀ᵐ ω ∂P, M ⟨0, zero_le, zero_le⟩ ω = 0 := by
    filter_upwards [hconvM] with ω hω
    have ht : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (nhds (M ⟨0, zero_le, zero_le⟩ ω)) := by
      simpa using hω ⟨0, zero_le, zero_le⟩
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨hmart.integrable t, ?_⟩
  calc
    _ = ∫ ω, P[fun ω => Real.exp (a * M t ω - a ^ 2 * Q t ω / 2) | F 0] ω ∂P :=
      (integral_condExp (F.le 0)).symm
    _ = ∫ ω, Real.exp (a * M ⟨0, zero_le, zero_le⟩ ω -
        a ^ 2 * Q ⟨0, zero_le, zero_le⟩ ω / 2) ∂P :=
      integral_congr_ae (hmart.condExp_ae_eq (show (⟨0, zero_le, zero_le⟩ : Icc (0 : ℝ≥0) T) ≤ t from t.property.1))
    _ = ∫ _ : Ω, (1 : ℝ) ∂P := by
      apply integral_congr_ae
      filter_upwards [hmzero] with ω hω
      simp [hω, Q]
    _ = 1 := by simp

/-- The original channel integral, written using the raw-function interface
required by the Kurtz clock adapter. -/
def channelItoOfFun (T : ℝ≥0)
    (hBc : ∀ i ω, Continuous (fun t => B i t ω)) (hBm : ∀ i t, Measurable (B i t))
    (H : Fin d → ℝ≥0 → Ω → ℝ) (i : Fin d) : ℝ≥0 → Ω → ℝ := by
  letI := hB i
  exact ContinuousItoLinear.continuousItoOfFun P F T (hBc i) (hBm i) (H i)

include hcoord hpast in
/-- The two normalized-exponential premises needed by the rectangular Knight
MGF theorem, now for the safe sum of actual stopped channel integrals.
Every input is a driver, integrand, or clock assumption; no exponential,
approximation, stopping-integral, or bracket-identification premise is carried.

The bound is for a fixed system and horizon; it need not be uniform in a
subsequent system-size parameter.
-/
theorem clock_step_normalized_exponential {κ : Type*} [Fintype κ]
    (g : IntervalGrid (Fin d) κ) (θ : κ → ℝ) (T : ℝ≥0)
    (hBc : ∀ i ω, Continuous (fun t => B i t ω)) (hBm : ∀ i t, Measurable (B i t))
    (hnull : ∀ t S, MeasurableSet S → P S = 0 → MeasurableSet[F t] S)
    [F.IsRightContinuous]
    (H : Fin d → ℝ≥0 → Ω → ℝ) (hHa : ∀ i t, Measurable[F t] (H i t))
    (hHc : ∀ i ω, Continuous (fun t => H i t ω))
    {K : ℝ} (hK : 0 ≤ K) (hHb : ∀ i t ω, |H i t ω| ≤ K)
    (A : Fin d → ℝ≥0 → Ω → ℝ≥0) (hAa : ∀ i, Adapted F (A i))
    (hAc : ∀ i ω, Continuous (fun t => A i t ω))
    (hAm : ∀ i ω, Monotone (fun t => A i t ω)) (hAz : ∀ i ω, A i 0 ω = 0)
    (hclock : ∀ i ω t,
      (∫ r in Ioc 0 t, (H i r ω) ^ 2 ∂timeMeasure) = (A i t ω : ℝ))
    (a : ℝ) (t : Icc (0 : ℝ≥0) T) :
    Integrable (fun ω => Real.exp
      (a * cappedStepSum g θ (channelItoOfFun B hB T hBc hBm H) A t.val ω -
        a ^ 2 * stepBracket g θ A t.val ω / 2)) P ∧
      (∫ ω, Real.exp
        (a * cappedStepSum g θ (channelItoOfFun B hB T hBc hBm H) A t.val ω -
          a ^ 2 * stepBracket g θ A t.val ω / 2) ∂P) = 1 := by
  classical
  let G := stepIntegrand g θ H A
  let C := (∑ j, |θ j|) * K
  have hC : 0 ≤ C := mul_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg (θ j)) hK
  have hGa : ∀ i r, Measurable[F r] (G i r) :=
    stepIntegrand_measurable g θ H A hHa hAa
  have hGs : ∀ i r ω, Tendsto
      (fun n : ℕ => G i (leftGrid (1 / ((n : ℝ≥0) + 1)) r) ω)
      atTop (nhds (G i r ω)) := stepIntegrand_sample_tendsto g θ H A hHc hAc hAm
  have hGb : ∀ i r ω, |G i r ω| ≤ C := stepIntegrand_bound g θ H A hK hHb
  have hstop : ∀ i u, IsStoppingTime F (clockInverseTime (A i) u) :=
    fun i u => clockInverseTime_isStoppingTime (hAa i) (hAc i) (hAm i) (hAz i) u
  have hHmem : ∀ i, MemLp (Function.uncurry (H i)) 2
      (trimMeasure_T (𝓖 := F) (μ := P) T (hBm i)) := by
    intro i
    letI := hB i
    exact integrandMemLp (μ := P) T (hBm i) (H i) (hHa i) (hHc i) K (hHb i)
  have hident : ∀ i, ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ≥0) T,
      sampledChannelIntegral B hB T hBc hBm G hGa hGs C hGb i ω t =
        ∑ j, if g.channel j = i then θ j *
          (channelItoOfFun B hB T hBc hBm H i
              (Ripple.ProbabilityTheory.clockStoppedTime (fun r => A i r ω) (g.upper j) t.val) ω -
            channelItoOfFun B hB T hBc hBm H i
              (Ripple.ProbabilityTheory.clockStoppedTime (fun r => A i r ω) (g.lower j) t.val) ω) else 0 := by
    intro i
    letI := hB i
    have hi := continuousItoOfFun_stepIntegrand g θ T (hBc i) (hBm i) H A i
      (hAc i) (hAm i) (hAz i) (hstop i) (hHmem i)
    have hraw := sampledIntegrand_memLp (P := P) T (hBm i) (G i) (hGa i) (hGs i) C (hGb i)
    filter_upwards [hi] with ω hω t
    have heval : sampledChannelIntegral B hB T hBc hBm G hGa hGs C hGb i ω t =
        ContinuousItoLinear.continuousItoOfFun P F T (hBc i) (hBm i) (G i) t.val ω := by
      rw [ContinuousItoLinear.continuousItoOfFun_of_memLp T (hBc i) (hBm i) hraw]
      simp only [sampledChannelIntegral, ContinuousItoLinear.continuousItoNN,
        min_eq_left t.property.2]
    rw [heval, hω t]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> rfl
  have hsum : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ≥0) T,
      (∑ i, sampledChannelIntegral B hB T hBc hBm G hGa hGs C hGb i ω t) =
        cappedStepSum g θ (channelItoOfFun B hB T hBc hBm H) A t.val ω := by
    filter_upwards [ae_all_iff.mpr hident] with ω hω t
    simp_rw [hω]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_eq_single (g.channel j)]
    · simp
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  have henergy : ∀ i ω r, IntegrableOn (fun s => (H i s ω) ^ 2) (Ioc 0 r) timeMeasure := by
    intro i ω r
    haveI : IsFiniteMeasure (timeMeasure.restrict (Ioc (0 : ℝ≥0) r)) := by
      change IsFiniteMeasure (timeMeasure_T r)
      infer_instance
    apply (integrable_const (K ^ 2)).mono'
      ((hHc i ω).measurable.pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.mp (hHb i s ω)).1 (abs_le.mp (hHb i s ω)).2
  have hbracket : ∀ ω,
      (∑ i, ∫ r in Ioc 0 t.val, (G i r ω) ^ 2 ∂timeMeasure) = stepBracket g θ A t.val ω :=
    stepIntegrand_energy g θ H A hAc hAm hAz hclock henergy t.val
  have hnormal := sampled_vector_normalized_exponential B hB hcoord hpast T
    hBc hBm hnull G hGa hGs hC hGb a t
  have heq : (fun ω => Real.exp
      (a * (∑ i, sampledChannelIntegral B hB T hBc hBm G hGa hGs C hGb i ω t) -
        a ^ 2 * (∑ i, ∫ r in Ioc 0 t.val, (G i r ω) ^ 2 ∂timeMeasure) / 2)) =ᵐ[P]
      (fun ω => Real.exp
        (a * cappedStepSum g θ (channelItoOfFun B hB T hBc hBm H) A t.val ω -
          a ^ 2 * stepBracket g θ A t.val ω / 2)) := by
    filter_upwards [hsum] with ω hω
    rw [hω t, hbracket ω]
  exact ⟨hnormal.1.congr heq, (integral_congr_ae heq).symm.trans hnormal.2⟩

end Ripple.Stochastic.Knight
