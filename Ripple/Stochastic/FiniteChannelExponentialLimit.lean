import Ripple.Stochastic.VectorStochasticExponential
import Ripple.Stochastic.BoundedStochasticExponential
import Ripple.Stochastic.BoundedPredictableApproximation
import Ripple.Stochastic.ContinuousAdaptedIntegrand

/-!
# Finite-channel stochastic exponential limits

The coordinates share a filtration and their fresh increment vector is
independent of that filtration. No independence of stochastic integrals is
required. The doubled-parameter exponential supplies the square bound used
in the uniform-integrability and Vitali passage.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.FiniteChannelExponentialLimit

open VectorStochasticExponential BoundedStochasticExponential
open ExponentialMartingaleLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {d : ℕ} {F : Filtration ℝ≥0 mΩ}

/-- The sum of elementary integrals, with one common partition. -/
def vectorSum (B : Fin d → ℝ≥0 → Ω → ℝ) (s : ℕ → ℝ≥0)
    (c : ℕ → Ω → Fin d → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j, simpleSum (B j) s (fun i ω => c i ω j) N t ω

/-- The compensator is the sum of channel energies, with no cross terms. -/
def vectorBracket (s : ℕ → ℝ≥0) (c : ℕ → Ω → Fin d → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j, simpleBracket s (fun i ω => c i ω j) N t ω

/-- The elementary vector exponential has exactly the summed integral and bracket. -/
theorem vector_exp_eq (B : Fin d → ℝ≥0 → Ω → ℝ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (c : ℕ → Ω → Fin d → ℝ)
    (lam : ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    vectorSimpleExponential B s (fun i ω j => lam * c i ω j) N t ω =
      Real.exp (lam * vectorSum B s c N t ω - lam ^ 2 * vectorBracket s c N t ω / 2) := by
  have hsum : vectorSum B s c N t ω =
      ∑ i ∈ Finset.range N, ∑ j, c i ω j *
        (B j (min (s (i + 1)) t) ω - B j (min (s i) t) ω) := by
    unfold vectorSum simpleSum
    rw [Finset.sum_comm]
  have hbracket : vectorBracket s c N t ω =
      ∑ i ∈ Finset.range N, ∑ j, (c i ω j) ^ 2 *
        (((min (s (i + 1)) t : ℝ≥0) : ℝ) - (min (s i) t : ℝ)) := by
    unfold vectorBracket simpleBracket
    rw [Finset.sum_comm]
  rw [vectorSimpleExponential_eq_exp_sum B s hs, hsum, hbracket]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum, mul_pow, mul_assoc]

@[simp] theorem vectorSum_zero (B : Fin d → ℝ≥0 → Ω → ℝ)
    (s : ℕ → ℝ≥0) (c : ℕ → Ω → Fin d → ℝ) (N : ℕ) (ω : Ω) :
    vectorSum B s c N 0 ω = 0 := by
  simp [vectorSum, simpleSum]

@[simp] theorem vectorBracket_zero (s : ℕ → ℝ≥0)
    (c : ℕ → Ω → Fin d → ℝ) (N : ℕ) (ω : Ω) :
    vectorBracket s c N 0 ω = 0 := by
  simp [vectorBracket, simpleBracket]

/-- A separate deterministic bound for each channel avoids an unnecessary
factor of the number of channels when the bounds differ. -/
theorem vectorBracket_le (s : ℕ → ℝ≥0) (hs : Monotone s) (hz : s 0 = 0)
    (c : ℕ → Ω → Fin d → ℝ) (K : Fin d → ℝ)
    (hK : ∀ i ω j, |c i ω j| ≤ K j) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    vectorBracket s c N t ω ≤ (∑ j, (K j) ^ 2) * (t : ℝ) := by
  unfold vectorBracket
  calc
    _ ≤ ∑ j, (K j) ^ 2 * (t : ℝ) := Finset.sum_le_sum fun j hj =>
      simpleBracket_le s hs hz (fun i ω => c i ω j) (fun i ω => hK i ω j) N t ω
    _ = _ := (Finset.sum_mul ..).symm

/-- Strong adaptation of the actual channel-energy sum. -/
theorem vectorBracket_stronglyAdapted (s : ℕ → ℝ≥0) (hs : Monotone s)
    (c : ℕ → Ω → Fin d → ℝ) (hc : ∀ i, Measurable[F (s i)] (c i)) (N : ℕ) :
    StronglyAdapted F (vectorBracket s c N) := by
  intro t
  apply Finset.stronglyMeasurable_fun_sum
  intro j hj
  exact simpleBracket_stronglyAdapted F s hs (fun i ω => c i ω j)
    (fun i => ((measurable_pi_apply j).comp (hc i)).stronglyMeasurable) N t

variable (B : Fin d → ℝ≥0 → Ω → ℝ)
  (hB : ∀ j, IsFilteredPreBrownian (B j) F P)
  (hcoord : ∀ r t : ℝ≥0, r ≤ t → iIndepFun (fun j ω => B j t ω - B j r ω) P)
  (hpast : ∀ r t : ℝ≥0, r ≤ t →
    Indep (MeasurableSpace.comap (fun ω j => B j t ω - B j r ω) inferInstance) (F r) P)

include hB hcoord hpast in
/-- The scaled vector exponential is produced by the conditional Gaussian identity. -/
theorem scaled_vector_martingale (s : ℕ → ℝ≥0) (hs : Monotone s)
    (c : ℕ → Ω → Fin d → ℝ) (hc : ∀ i, Measurable[F (s i)] (c i))
    {K : ℝ} (hK : ∀ i ω j, |c i ω j| ≤ K) (lam : ℝ) (N : ℕ) :
    Martingale (fun t ω => Real.exp (lam * vectorSum B s c N t ω -
      lam ^ 2 * vectorBracket s c N t ω / 2)) F P := by
  have hm := vectorSimpleExponential_isMartingale B hB hcoord hpast s hs
    (fun i ω j => lam * c i ω j)
    (fun i => by
      letI : MeasurableSpace Ω := F (s i)
      exact measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp (hc i)).const_mul lam)
    (fun i ω j => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hK i ω j) (abs_nonneg lam)) N
  have heq : vectorSimpleExponential B s (fun i ω j => lam * c i ω j) N = fun t ω =>
      Real.exp (lam * vectorSum B s c N t ω - lam ^ 2 * vectorBracket s c N t ω / 2) := by
    funext t ω
    exact vector_exp_eq B s hs c lam N t ω
  rw [heq] at hm
  exact hm

include hB hcoord hpast in
/-- Mean one follows from the genuine martingale and its initial value. -/
theorem scaled_vector_mean (s : ℕ → ℝ≥0) (hs : Monotone s)
    (c : ℕ → Ω → Fin d → ℝ) (hc : ∀ i, Measurable[F (s i)] (c i))
    {K : ℝ} (hK : ∀ i ω j, |c i ω j| ≤ K) (lam : ℝ) (N : ℕ) (t : ℝ≥0) :
    (∫ ω, Real.exp (lam * vectorSum B s c N t ω -
      lam ^ 2 * vectorBracket s c N t ω / 2) ∂P) = 1 := by
  have hm := scaled_vector_martingale B hB hcoord hpast s hs c hc hK lam N
  calc
    _ = ∫ ω, P[fun ω => Real.exp (lam * vectorSum B s c N t ω -
        lam ^ 2 * vectorBracket s c N t ω / 2) | F 0] ω ∂P :=
      (integral_condExp (F.le 0)).symm
    _ = ∫ ω, Real.exp (lam * vectorSum B s c N 0 ω -
        lam ^ 2 * vectorBracket s c N 0 ω / 2) ∂P :=
      integral_congr_ae (hm.condExp_ae_eq (zero_le : (0 : ℝ≥0) ≤ t))
    _ = 1 := by simp

include hB hcoord hpast in
/-- The square bound is uniform in the partition and its number of cells.
It uses the doubled vector exponential, so random predictable coefficients
are not assigned an unconditional Gaussian law. -/
theorem vector_exp_sq_bound (s : ℕ → ℝ≥0) (hs : Monotone s) (hz : s 0 = 0)
    (c : ℕ → Ω → Fin d → ℝ) (hc : ∀ i, Measurable[F (s i)] (c i))
    {K : ℝ} (hK : ∀ i ω j, |c i ω j| ≤ K) (lam : ℝ) (N : ℕ) (t : ℝ≥0) :
    Integrable (fun ω => (Real.exp (lam * vectorSum B s c N t ω -
      lam ^ 2 * vectorBracket s c N t ω / 2)) ^ 2) P ∧
    (∫ ω, (Real.exp (lam * vectorSum B s c N t ω -
      lam ^ 2 * vectorBracket s c N t ω / 2)) ^ 2 ∂P) ≤
      Real.exp (lam ^ 2 * ((d : ℝ) * K ^ 2 * (t : ℝ))) := by
  have hdouble := scaled_vector_martingale B hB hcoord hpast s hs c hc hK (2 * lam) N
  have hcambient : ∀ i j, Measurable (fun ω => c i ω j) :=
    fun i j => ((measurable_pi_apply j).comp (hc i)).mono (F.le _) le_rfl
  have hBambient : ∀ j u, Measurable (B j u) := fun j u =>
    (((hB j).stronglyAdapted u).mono (F.le u)).measurable
  apply exponential_sq_bound (vectorSum B s c N t) (vectorBracket s c N t) lam
    ((d : ℝ) * K ^ 2 * (t : ℝ))
  · unfold vectorSum simpleSum
    fun_prop
  · unfold vectorBracket simpleBracket
    fun_prop
  · apply ae_of_all
    intro ω
    simpa using vectorBracket_le s hs hz c (fun _ => K) hK N t ω
  · exact hdouble.integrable t
  · exact scaled_vector_mean B hB hcoord hpast s hs c hc hK (2 * lam) N t

include hB hcoord hpast in
/-- Uniform square bounds and Vitali construct the vector stochastic exponential
from bounded compatible elementary approximants. The only limit data are the
actual summed integral and summed bracket; UI is discharged in the proof. -/
theorem vector_stochastic_exponential_of_bounded_approximation
    (s : ℕ → ℕ → ℝ≥0) (hs : ∀ n, Monotone (s n)) (hz : ∀ n, s n 0 = 0)
    (c : ℕ → ℕ → Ω → Fin d → ℝ)
    (hc : ∀ n i, Measurable[F (s n i)] (c n i))
    (N : ℕ → ℕ) {K : ℝ} (hK : ∀ n i ω j, |c n i ω j| ≤ K)
    (M Q : ℝ≥0 → Ω → ℝ) (hM : StronglyAdapted F M) (hQ : StronglyAdapted F Q)
    (hlimM : ∀ t, ∀ᵐ ω ∂P, Tendsto
      (fun n => vectorSum B (s n) (c n) (N n) t ω) atTop (nhds (M t ω)))
    (hlimQ : ∀ t, ∀ᵐ ω ∂P, Tendsto
      (fun n => vectorBracket (s n) (c n) (N n) t ω) atTop (nhds (Q t ω))) (lam : ℝ) :
    Martingale (fun t ω => Real.exp (lam * M t ω - lam ^ 2 * Q t ω / 2)) F P := by
  apply martingale_of_ae_limit_of_sq_integral_le F
    (fun n t ω => Real.exp (lam * vectorSum B (s n) (c n) (N n) t ω -
      lam ^ 2 * vectorBracket (s n) (c n) (N n) t ω / 2))
  · exact fun n => scaled_vector_martingale B hB hcoord hpast
      (s n) (hs n) (c n) (hc n) (hK n) lam (N n)
  · intro t
    exact (Real.measurable_exp.comp (((hM t).measurable.const_mul lam).sub
      (((hQ t).measurable.const_mul (lam ^ 2)).div_const 2))).stronglyMeasurable
  · exact fun n t => (vector_exp_sq_bound B hB hcoord hpast
      (s n) (hs n) (hz n) (c n) (hc n) (hK n) lam (N n) t).1
  · exact fun t => ⟨Real.exp (lam ^ 2 * ((d : ℝ) * K ^ 2 * (t : ℝ))),
      fun n => (vector_exp_sq_bound B hB hcoord hpast
        (s n) (hs n) (hz n) (c n) (hc n) (hK n) lam (N n) t).2⟩
  · intro t
    filter_upwards [hlimM t, hlimQ t] with ω hm hq
    exact Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul hm).sub ((tendsto_const_nhds.mul hq).div_const 2))

include hB hcoord hpast in
/-- Sharp maximal inequality after the vector martingale limit has been produced. -/
theorem vector_bounded_approximation_exponential_maximal
    (s : ℕ → ℕ → ℝ≥0) (hs : ∀ n, Monotone (s n)) (hz : ∀ n, s n 0 = 0)
    (c : ℕ → ℕ → Ω → Fin d → ℝ)
    (hc : ∀ n i, Measurable[F (s n i)] (c n i))
    (N : ℕ → ℕ) {K : ℝ} (hK : ∀ n i ω j, |c n i ω j| ≤ K)
    (M Q : ℝ≥0 → Ω → ℝ) (hM : StronglyAdapted F M) (hQ : StronglyAdapted F Q)
    (hlimM : ∀ t, ∀ᵐ ω ∂P, Tendsto
      (fun n => vectorSum B (s n) (c n) (N n) t ω) atTop (nhds (M t ω)))
    (hlimQ : ∀ t, ∀ᵐ ω ∂P, Tendsto
      (fun n => vectorBracket (s n) (c n) (N n) t ω) atTop (nhds (Q t ω)))
    (hQmono : ∀ᵐ ω ∂P, Monotone (fun t => Q t ω))
    (hMcont : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hQcont : ∀ᵐ ω ∂P, Continuous (fun t => Q t ω))
    (T : ℝ≥0) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    P (ExponentialMaximal.crossingEvent M Q T r q) ≤
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  have hmzero : ∀ᵐ ω ∂P, M 0 ω = 0 := by
    filter_upwards [hlimM 0] with ω hω
    have ht : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (M 0 ω)) := by simpa using hω
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hqzero : ∀ᵐ ω ∂P, Q 0 ω = 0 := by
    filter_upwards [hlimQ 0] with ω hω
    have ht : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (Q 0 ω)) := by simpa using hω
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hZ := vector_stochastic_exponential_of_bounded_approximation B hB hcoord hpast
    s hs hz c hc N hK M Q hM hQ hlimM hlimQ (r / q)
  exact ContinuousExponentialMaximal.continuous_exponential_maximal_ae M Q
    hmzero hqzero hQmono hMcont hQcont T hr hq hZ.supermartingale

include hB hcoord hpast in
/-- The compact-window passage requires only convergence on the fixed window.
All elementary exponentials are stopped at the same deterministic horizon. -/
theorem vector_stochastic_exponential_compact_limit (T : ℝ≥0)
    (s : ℕ → ℕ → ℝ≥0) (hs : ∀ n, Monotone (s n)) (hz : ∀ n, s n 0 = 0)
    (c : ℕ → ℕ → Ω → Fin d → ℝ)
    (hc : ∀ n i, Measurable[F (s n i)] (c n i))
    (N : ℕ → ℕ) {K : ℝ} (hK : ∀ n i ω j, |c n i ω j| ≤ K)
    (M Q : Icc (0 : ℝ≥0) T → Ω → ℝ)
    (hM : ∀ t : Icc (0 : ℝ≥0) T, StronglyMeasurable[F t.val] (M t))
    (hQ : ∀ t : Icc (0 : ℝ≥0) T, StronglyMeasurable[F t.val] (Q t))
    (hlimM : ∀ᵐ ω ∂P, ∀ t, Tendsto
      (fun n => vectorSum B (s n) (c n) (N n) t.val ω) atTop (nhds (M t ω)))
    (hlimQ : ∀ᵐ ω ∂P, ∀ t, Tendsto
      (fun n => vectorBracket (s n) (c n) (N n) t.val ω) atTop (nhds (Q t ω))) (lam : ℝ) :
    Martingale (fun t ω => Real.exp (lam * M t ω - lam ^ 2 * Q t ω / 2))
      (Doob.Filtration.compMono mΩ F (fun t : Icc (0 : ℝ≥0) T => t.val)
        (fun _ _ h => h)) P := by
  apply martingale_of_ae_limit_of_sq_integral_le
    (Doob.Filtration.compMono mΩ F (fun t : Icc (0 : ℝ≥0) T => t.val)
      (fun _ _ h => h))
    (fun n t ω => Real.exp (lam * vectorSum B (s n) (c n) (N n) t.val ω -
      lam ^ 2 * vectorBracket (s n) (c n) (N n) t.val ω / 2))
  · intro n
    exact Doob.martingale_compMono
      (scaled_vector_martingale B hB hcoord hpast (s n) (hs n) (c n) (hc n) (hK n) lam (N n))
      (fun t : Icc (0 : ℝ≥0) T => t.val) (fun _ _ h => h)
  · intro t
    exact (Real.measurable_exp.comp (((hM t).measurable.const_mul lam).sub
      (((hQ t).measurable.const_mul (lam ^ 2)).div_const 2))).stronglyMeasurable
  · exact fun n t => (vector_exp_sq_bound B hB hcoord hpast
      (s n) (hs n) (hz n) (c n) (hc n) (hK n) lam (N n) t.val).1
  · exact fun t => ⟨Real.exp (lam ^ 2 * ((d : ℝ) * K ^ 2 * (t.val : ℝ))),
      fun n => (vector_exp_sq_bound B hB hcoord hpast
        (s n) (hs n) (hz n) (c n) (hc n) (hK n) lam (N n) t.val).2⟩
  · intro t
    filter_upwards [hlimM, hlimQ] with ω hm hq
    exact Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul (hm t)).sub ((tendsto_const_nhds.mul (hq t)).div_const 2))

/-- Bounded elementary integrands that converge almost everywhere converge
in the installed predictable L² domain. The proof uses the actual squared
error integral, so there is no density or norm-convergence premise. -/
theorem boundedAssembly_tendsto {Bscalar : ℝ≥0 → Ω → ℝ}
    [IsFilteredPreBrownian Bscalar F P] (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (Bscalar t))
    (W : ℕ → FilteredItoIntegralCLM.TBoundedSP (𝓖 := F) T hBmeas)
    (φ : Lp ℝ 2 (FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := P) T hBmeas))
    {K : ℝ} (hW : ∀ n, ∀ᵐ z ∂(FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := P) T hBmeas),
      |⇑(W n).val z.1 z.2| ≤ K)
    (hφ : ∀ᵐ z ∂(FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := P) T hBmeas), |φ z| ≤ K)
    (hlim : ∀ᵐ z ∂(FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := P) T hBmeas),
      Tendsto (fun n => ⇑(W n).val z.1 z.2) atTop (nhds (φ z))) :
    Tendsto (fun n => FilteredItoIntegralCLM.simpleAssembly_T (𝓖 := F) (μ := P) T hBmeas (W n))
      atTop (nhds φ) := by
  let ν := FilteredItoIntegralCLM.trimMeasure_T (𝓖 := F) (μ := P) T hBmeas
  let A := fun n => FilteredItoIntegralCLM.simpleAssembly_T (𝓖 := F) (μ := P) T hBmeas (W n)
  have hsq : Tendsto (fun n => ∫ z, (⇑(W n).val z.1 z.2 - φ z) ^ 2 ∂ν)
      atTop (nhds (0 : ℝ)) := by
    have hzero : (∫ z, (φ z - φ z) ^ 2 ∂ν) = (0 : ℝ) := by simp
    rw [← hzero]
    apply tendsto_integral_of_dominated_convergence (fun _ => (2 * K) ^ 2)
    · intro n
      exact (((FilteredItoIntegralCLM.memLp_uncurry_trim_T (𝓖 := F) (μ := P)
        T hBmeas (W n).val).aestronglyMeasurable).sub (Lp.memLp φ).aestronglyMeasurable).pow 2
    · exact integrable_const _
    · intro n
      filter_upwards [hW n, hφ] with z hw hp
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have he : |⇑(W n).val z.1 z.2 - φ z| ≤ 2 * K :=
        (abs_sub _ _).trans (by linarith)
      nlinarith [sq_abs (⇑(W n).val z.1 z.2 - φ z), abs_nonneg (⇑(W n).val z.1 z.2 - φ z)]
    · filter_upwards [hlim] with z hz
      exact (hz.sub tendsto_const_nhds).pow 2
  have heq : ∀ n, ‖A n - φ‖ ^ 2 = ∫ z, (⇑(W n).val z.1 z.2 - φ z) ^ 2 ∂ν := by
    intro n
    rw [FilteredItoIntegralL2.lp_two_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (A n) φ,
      (FilteredItoIntegralCLM.memLp_uncurry_trim_T (𝓖 := F) (μ := P)
        T hBmeas (W n).val).coeFn_toLp] with z hz ha
    change ((A n - φ) z) ^ 2 = _
    rw [hz]
    change (A n z - φ z) ^ 2 = _
    rw [show A n z = ⇑(W n).val z.1 z.2 from ha]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnormsq : Tendsto (fun n => ‖A n - φ‖ ^ 2) atTop (nhds (0 : ℝ)) := by
    simpa only [heq] using hsq
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hnormsq
  simp only [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr (fun n => ?_)
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (norm_nonneg _)

/-- The common deterministic grid converges in the actual predictable L²
norm for every bounded continuous adapted integrand. -/
theorem sampleAssembly_tendsto {Bscalar : ℝ≥0 → Ω → ℝ}
    [IsFilteredPreBrownian Bscalar F P] (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (Bscalar t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t ω, |H t ω| ≤ K) :
    Tendsto (fun n : ℕ => FilteredItoIntegralCLM.simpleAssembly_T (𝓖 := F) (μ := P) T hBmeas
      (ContinuousAdaptedIntegrand.sampleSP T hBmeas H ha K hb (1 / ((n : ℝ≥0) + 1))))
      atTop (nhds (ContinuousAdaptedIntegrand.integrandLp (μ := P) T hBmeas H ha hc K hb)) := by
  apply boundedAssembly_tendsto T hBmeas
  · intro n
    exact ae_of_all _ fun z => ContinuousAdaptedIntegrand.sampleSP_bound T hBmeas H ha hK hb
      (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity) z.1 z.2
  · exact ContinuousAdaptedIntegrand.integrandLp_bound (μ := P) T hBmeas H ha hc K hb
  · filter_upwards [BoundedPredictableApproximation.ae_window (μ := P) T hBmeas,
      ContinuousAdaptedIntegrand.integrandLp_coe (μ := P) T hBmeas H ha hc K hb] with z hz hφ
    rw [hφ]
    have heq : ∀ n : ℕ,
        ⇑(ContinuousAdaptedIntegrand.sampleSP T hBmeas H ha K hb
          (1 / ((n : ℝ≥0) + 1))).val z.1 z.2 =
        H (ContinuousAdaptedIntegrand.leftGrid (1 / ((n : ℝ≥0) + 1)) z.1) z.2 :=
      fun n => ContinuousAdaptedIntegrand.sampleSP_apply T hBmeas H ha K hb
        (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity) hz.1 hz.2 z.2
    simpa only [heq] using ContinuousAdaptedIntegrand.sample_tendsto hc z.1 z.2

/-- A finite family of convergences in measure admits one common a.e.
subsequence. The induction only refines subsequences already selected. -/
theorem exists_common_subsequence {ι E : Type*} [PseudoEMetricSpace E]
    (f : ι → ℕ → Ω → E) (g : ι → Ω → E) (S : Finset ι)
    (h : ∀ j ∈ S, TendstoInMeasure P (f j) atTop (g j)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ j ∈ S,
      ∀ᵐ ω ∂P, Tendsto (fun n => f j (ns n) ω) atTop (nhds (g j ω)) := by
  classical
  revert h
  induction S using Finset.cons_induction with
  | empty =>
    intro h
    exact ⟨id, strictMono_id, by simp⟩
  | cons j S hj ih =>
    intro h
    obtain ⟨ns, hns, hold⟩ := ih (fun k hk => h k (by simp only [Finset.mem_cons]; exact Or.inr hk))
    obtain ⟨u, hu, hnew⟩ := ((h j (by simp)).comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ns ∘ u, hns.comp hu, ?_⟩
    intro k hk
    rcases Finset.mem_cons.mp hk with rfl | hk
    · exact hnew
    · filter_upwards [hold k hk] with ω hω
      exact hω.comp hu.tendsto_atTop

/-- The chosen continuous version of each channel's actual integral. -/
def continuousChannelIntegral (T : ℝ≥0)
    (hBcont : ∀ j ω, Continuous (fun t => B j t ω))
    (hBmeas : ∀ j t, Measurable (B j t))
    (H : Fin d → ℝ≥0 → Ω → ℝ) (ha : ∀ j t, Measurable[F t] (H j t))
    (hc : ∀ j ω, Continuous (fun t => H j t ω)) (K : ℝ)
    (hb : ∀ j t ω, |H j t ω| ≤ K) (j : Fin d) : Ω → C(Icc (0 : ℝ≥0) T, ℝ) := by
  letI := hB j
  exact AdaptedContinuousSpace.representative
    (ContinuousItoElementary.continuousIto T (hBcont j) (hBmeas j)
      (ContinuousAdaptedIntegrand.integrandLp (μ := P) T (hBmeas j) (H j) (ha j) (hc j) K (hb j)))

/-- Compatible bounded approximants are produced by a deterministic grid shared
by all channels. One subsequence works for every continuous integral path. -/
theorem exists_sample_integral_subsequence (T : ℝ≥0)
    (hBcont : ∀ j ω, Continuous (fun t => B j t ω))
    (hBmeas : ∀ j t, Measurable (B j t))
    (H : Fin d → ℝ≥0 → Ω → ℝ) (ha : ∀ j t, Measurable[F t] (H j t))
    (hc : ∀ j ω, Continuous (fun t => H j t ω)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ j t ω, |H j t ω| ≤ K) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P, ∀ j,
      Tendsto (fun n => ContinuousItoConstruction.simpleIntegralPath T (hBcont j)
        (ContinuousAdaptedIntegrand.sampleSP T (hBmeas j) (H j) (ha j) K (hb j)
          (1 / ((ns n : ℝ≥0) + 1))).val ω)
        atTop (nhds (continuousChannelIntegral B hB T hBcont hBmeas H ha hc K hb j ω)) := by
  let W := fun (j : Fin d) (n : ℕ) =>
    ContinuousAdaptedIntegrand.sampleSP T (hBmeas j) (H j) (ha j) K (hb j)
      (1 / ((n : ℝ≥0) + 1))
  have hpath : ∀ j, TendstoInMeasure P
      (fun n ω => ContinuousItoConstruction.simpleIntegralPath T (hBcont j) (W j n).val ω) atTop
      (continuousChannelIntegral B hB T hBcont hBmeas H ha hc K hb j) := by
    intro j
    letI := hB j
    have hW := sampleAssembly_tendsto (P := P) T (hBmeas j) (H j) (ha j) (hc j) hK (hb j)
    have hp : Tendsto (fun n => ContinuousItoElementary.boundedSimplePathLp (μ := P) T
        (hBcont j) (hBmeas j) (W j n)) atTop
        (nhds (ContinuousItoElementary.continuousIto T (hBcont j) (hBmeas j)
          (ContinuousAdaptedIntegrand.integrandLp (μ := P) T (hBmeas j) (H j) (ha j) (hc j) K (hb j)))) :=
      ContinuousItoConstruction.continuousIntegral_tendsto _
        (FilteredItoIntegralCLM.simpleAssembly_T_denseRange T (hBmeas j)) _ _
        (ContinuousItoElementary.boundedSimplePathLp_norm_le (μ := P) T (hBcont j) (hBmeas j)) hW
    apply TendstoInMeasure.congr
      (fun n => (ContinuousItoElementary.simpleIntegralPath_memLp (μ := P) T (hBcont j)
        (hBmeas j) (W j n).val).coeFn_toLp)
      (AdaptedContinuousSpace.representative_ae _)
      (tendstoInMeasure_of_tendsto_Lp hp)
  obtain ⟨ns, hns, hconv⟩ := exists_common_subsequence
    (fun j n ω => ContinuousItoConstruction.simpleIntegralPath T (hBcont j) (W j n).val ω)
    (continuousChannelIntegral B hB T hBcont hBmeas H ha hc K hb) Finset.univ
    (fun j _ => hpath j)
  refine ⟨ns, hns, ae_all_iff.mpr (fun j => hconv j (Finset.mem_univ j))⟩

/-- The sum of the chosen continuous versions of the actual channel integrals. -/
def continuousVectorIntegral (T : ℝ≥0)
    (hBcont : ∀ j ω, Continuous (fun t => B j t ω))
    (hBmeas : ∀ j t, Measurable (B j t))
    (H : Fin d → ℝ≥0 → Ω → ℝ) (ha : ∀ j t, Measurable[F t] (H j t))
    (hc : ∀ j ω, Continuous (fun t => H j t ω)) (K : ℝ)
    (hb : ∀ j t ω, |H j t ω| ≤ K) (t : Icc (0 : ℝ≥0) T) (ω : Ω) : ℝ :=
  ∑ j, continuousChannelIntegral B hB T hBcont hBmeas H ha hc K hb j ω t

/-- The actual bracket of the finite-channel integral on a compact window. -/
def continuousVectorBracket (T : ℝ≥0) (H : Fin d → ℝ≥0 → Ω → ℝ)
    (t : Icc (0 : ℝ≥0) T) (ω : Ω) : ℝ :=
  ∑ j, ∫ s in Ioc (0 : ℝ≥0) t.val, (H j s ω) ^ 2 ∂FilteredItoIntegralL2.timeMeasure

/-- Bracket increments inherit the sum of the channel square bounds. -/
theorem vectorBracket_increment_bound (s : ℕ → ℝ≥0) (hs : Monotone s) (hz : s 0 = 0)
    (c : ℕ → Ω → Fin d → ℝ) {K : ℝ} (hK : ∀ i ω j, |c i ω j| ≤ K)
    (N : ℕ) {u t : ℝ≥0} (hut : u ≤ t) (ω : Ω) :
    0 ≤ vectorBracket s c N t ω - vectorBracket s c N u ω ∧
      vectorBracket s c N t ω - vectorBracket s c N u ω ≤
        (d : ℝ) * K ^ 2 * ((t : ℝ) - u) := by
  have hinc := fun j => BoundedPredictableApproximation.simpleBracket_increment_bound s hs hz
    (fun i ω => c i ω j) (fun i ω => hK i ω j) N hut ω
  unfold vectorBracket
  rw [← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_nonneg (fun j _ => (hinc j).1), ?_⟩
  calc
    _ ≤ ∑ j : Fin d, K ^ 2 * ((t : ℝ) - u) := Finset.sum_le_sum fun j _ => (hinc j).2
    _ = _ := by simp; ring

/-- The deterministic common-grid brackets converge pathwise to the original
input's time-square integral. No subsequence or quotient representative occurs. -/
theorem sampleBracket_tendsto {Bscalar : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (Bscalar t))
    (H : ℝ≥0 → Ω → ℝ) (ha : ∀ t, Measurable[F t] (H t))
    (hc : ∀ ω, Continuous (fun t => H t ω)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t ω, |H t ω| ≤ K) (t : Icc (0 : ℝ≥0) T) (ω : Ω) :
    Tendsto (fun n : ℕ => simpleBracket
      (ContinuousAdaptedIntegrand.samplePartition (1 / ((n : ℝ≥0) + 1)) T)
      (fun i ω => H (ContinuousAdaptedIntegrand.samplePartition (1 / ((n : ℝ≥0) + 1)) T i) ω)
      (ContinuousAdaptedIntegrand.sampleCells (1 / ((n : ℝ≥0) + 1)) T) t.val ω)
      atTop (nhds (∫ s in Ioc (0 : ℝ≥0) t.val, (H s ω) ^ 2 ∂FilteredItoIntegralL2.timeMeasure)) := by
  let W := fun n : ℕ => ContinuousAdaptedIntegrand.sampleSP T hBmeas H ha K hb
    (1 / ((n : ℝ≥0) + 1))
  have hi : Tendsto (fun n => ∫ s,
      (⇑(W n).val s ω) ^ 2 ∂FilteredItoIntegralCLM.timeMeasure_T t.val) atTop
      (nhds (∫ s, (H s ω) ^ 2 ∂FilteredItoIntegralCLM.timeMeasure_T t.val)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => K ^ 2)
    · intro n
      exact ((BoundedPredictableApproximation.measurable_simple_time (W n).val ω).pow_const 2).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply ae_of_all
      intro s
      have hbnd := ContinuousAdaptedIntegrand.sampleSP_bound T hBmeas H ha hK hb
        (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity) s ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (abs_le.mp hbnd).1 (abs_le.mp hbnd).2
    · filter_upwards [ae_restrict_mem (μ := FilteredItoIntegralL2.timeMeasure) measurableSet_Ioc] with s hs
      have heq : ∀ n : ℕ, ⇑(W n).val s ω =
          H (ContinuousAdaptedIntegrand.leftGrid (1 / ((n : ℝ≥0) + 1)) s) ω :=
        fun n => ContinuousAdaptedIntegrand.sampleSP_apply T hBmeas H ha K hb
          (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity) hs.1 (hs.2.trans t.property.2) ω
      simpa only [heq] using (ContinuousAdaptedIntegrand.sample_tendsto hc s ω).pow 2
  have heq : ∀ n : ℕ, simpleBracket
      (ContinuousAdaptedIntegrand.samplePartition (1 / ((n : ℝ≥0) + 1)) T)
      (fun i ω => H (ContinuousAdaptedIntegrand.samplePartition (1 / ((n : ℝ≥0) + 1)) T i) ω)
      (ContinuousAdaptedIntegrand.sampleCells (1 / ((n : ℝ≥0) + 1)) T) t.val ω =
      ∫ s, (⇑(W n).val s ω) ^ 2 ∂FilteredItoIntegralCLM.timeMeasure_T t.val := fun n =>
    ContinuousAdaptedIntegrand.sampleSP_bracket T hBmeas H ha K hb
      (show 0 < (1 : ℝ≥0) / ((n : ℝ≥0) + 1) from by positivity) t.val t.property.2 ω
  simpa only [heq, FilteredItoIntegralCLM.timeMeasure_T] using hi

include hB hcoord hpast in
/-- Construction of the actual finite-channel stochastic exponential for
bounded continuous adapted inputs, with regularity of its summed bracket. -/
theorem bounded_continuous_vector_exponential (T : ℝ≥0)
    (hBcont : ∀ j ω, Continuous (fun t => B j t ω))
    (hBmeas : ∀ j t, Measurable (B j t))
    (hnull : ∀ t A, MeasurableSet A → P A = 0 → MeasurableSet[F t] A)
    (H : Fin d → ℝ≥0 → Ω → ℝ) (ha : ∀ j t, Measurable[F t] (H j t))
    (hc : ∀ j ω, Continuous (fun t => H j t ω)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ j t ω, |H j t ω| ≤ K) :
    (∀ᵐ ω ∂P, continuousVectorIntegral B hB T hBcont hBmeas H ha hc K hb
      ⟨0, zero_le, zero_le⟩ ω = 0) ∧
    (∀ ω, Monotone (fun t => continuousVectorBracket T H t ω) ∧
      Continuous (fun t => continuousVectorBracket T H t ω)) ∧
    (∀ ω, Continuous (fun t => continuousVectorIntegral B hB T hBcont hBmeas H ha hc K hb t ω)) ∧
    ∀ lam : ℝ, Martingale
      (fun t ω => Real.exp (lam * continuousVectorIntegral B hB T hBcont hBmeas H ha hc K hb t ω -
        lam ^ 2 * continuousVectorBracket T H t ω / 2))
      (Doob.Filtration.compMono mΩ F (fun t : Icc (0 : ℝ≥0) T => t.val)
        (fun _ _ h => h)) P := by
  let δ := fun n : ℕ => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)
  let s := fun n => ContinuousAdaptedIntegrand.samplePartition (δ n) T
  let c := fun n i ω j => H j (s n i) ω
  let N := fun n => ContinuousAdaptedIntegrand.sampleCells (δ n) T
  let M := fun (t : Icc (0 : ℝ≥0) T) ω =>
    ∑ j, continuousChannelIntegral B hB T hBcont hBmeas H ha hc K hb j ω t
  let Q := continuousVectorBracket T H
  have hs : ∀ n, Monotone (s n) := fun n => ContinuousAdaptedIntegrand.samplePartition_mono (δ n) T
  have hz : ∀ n, s n 0 = 0 := fun n => ContinuousAdaptedIntegrand.samplePartition_zero (δ n) T
  have hca : ∀ n i, Measurable[F (s n i)] (c n i) :=
    fun n i => by
      letI : MeasurableSpace Ω := F (s n i)
      exact measurable_pi_lambda _ fun j => ha j (s n i)
  have hcb : ∀ n i ω j, |c n i ω j| ≤ K := fun n i ω j => hb j (s n i) ω
  have hconvQ : ∀ (ω : Ω) (t : Icc (0 : ℝ≥0) T), Tendsto (fun n => vectorBracket (s n) (c n) (N n) t.val ω)
      atTop (nhds (Q t ω)) := by
    intro ω t
    exact tendsto_finset_sum _ fun j _ => sampleBracket_tendsto T (hBmeas j)
      (H j) (ha j) (hc j) hK (hb j) t ω
  obtain ⟨ns, hns, hpaths⟩ := exists_sample_integral_subsequence B hB T hBcont hBmeas H ha hc hK hb
  have hconvM : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ≥0) T, Tendsto
      (fun n => vectorSum B (s (ns n)) (c (ns n)) (N (ns n)) t.val ω)
      atTop (nhds (M t ω)) := by
    filter_upwards [hpaths] with ω hω
    intro t
    apply tendsto_finset_sum
    intro j hj
    have hp := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto
      (continuousChannelIntegral B hB T hBcont hBmeas H ha hc K hb j ω)).comp (hω j)
    have heq : ∀ n, simpleSum (B j) (s (ns n)) (fun i ω => c (ns n) i ω j)
        (N (ns n)) t.val ω =
      ContinuousItoConstruction.simpleIntegralPath T (hBcont j)
        (ContinuousAdaptedIntegrand.sampleSP T (hBmeas j) (H j) (ha j) K (hb j) (δ (ns n))).val ω t := by
      intro n
      letI := hB j
      rw [ContinuousItoConstruction.simpleIntegralPath_apply T (hBcont j) (hBmeas j)]
      exact ContinuousAdaptedIntegrand.sampleSP_simpleSum T (hBmeas j) (H j) (ha j) K (hb j) (δ (ns n)) t.val ω
    simpa only [heq] using hp
  have hMa : ∀ t : Icc (0 : ℝ≥0) T, StronglyMeasurable[F t.val] (M t) := by
    intro t
    apply Finset.stronglyMeasurable_fun_sum
    intro j hj
    letI := hB j
    exact ContinuousItoElementary.continuousIto_representative_adapted T (hBcont j) (hBmeas j) hnull
      (ContinuousAdaptedIntegrand.integrandLp (μ := P) T (hBmeas j) (H j) (ha j) (hc j) K (hb j)) t
  have hQa : ∀ t : Icc (0 : ℝ≥0) T, StronglyMeasurable[F t.val] (Q t) := by
    intro t
    have heq : Q t = fun ω => Filter.limsup (fun n => vectorBracket (s n) (c n) (N n) t.val ω) atTop :=
      funext fun ω => (hconvQ ω t).limsup_eq.symm
    rw [heq]
    exact (Measurable.limsup fun n => (vectorBracket_stronglyAdapted (s n) (hs n)
      (c n) (hca n) (N n) t.val).measurable).stronglyMeasurable
  have hQreg : ∀ ω, Monotone (fun t => Q t ω) ∧ Continuous (fun t => Q t ω) := by
    intro ω
    have hinc : ∀ u t : Icc (0 : ℝ≥0) T, u ≤ t →
        0 ≤ Q t ω - Q u ω ∧ Q t ω - Q u ω ≤
          (d : ℝ) * K ^ 2 * ((t.val : ℝ) - u.val) := by
      intro u t hut
      have htend := (hconvQ ω t).sub (hconvQ ω u)
      have hbound := fun n => vectorBracket_increment_bound (s n) (hs n) (hz n)
        (c n) (hcb n) (N n) hut ω
      exact ⟨ge_of_tendsto htend (Eventually.of_forall fun n => (hbound n).1),
        le_of_tendsto htend (Eventually.of_forall fun n => (hbound n).2)⟩
    have hdist : ∀ u t : Icc (0 : ℝ≥0) T, u ≤ t →
        dist (Q t ω) (Q u ω) ≤ ((d : ℝ) * K ^ 2) * dist t u := by
      intro u t hut
      change dist (Q t ω) (Q u ω) ≤ ((d : ℝ) * K ^ 2) * dist (t.val : ℝ) (u.val : ℝ)
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (hinc u t hut).1,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hut))]
      exact (hinc u t hut).2
    have hlip : LipschitzWith ⟨(d : ℝ) * K ^ 2, mul_nonneg (Nat.cast_nonneg _) (sq_nonneg K)⟩
        (fun t => Q t ω) := by
      apply LipschitzWith.of_dist_le_mul
      intro t u
      rcases le_total u t with hut | htu
      · exact hdist u t hut
      · simpa only [dist_comm] using hdist t u htu
    exact ⟨fun u t hut => sub_nonneg.mp (hinc u t hut).1, hlip.continuous⟩
  have hmzero : ∀ᵐ ω ∂P, M ⟨0, zero_le, zero_le⟩ ω = 0 := by
    filter_upwards [hconvM] with ω hω
    have ht := hω ⟨0, zero_le, zero_le⟩
    have htzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (nhds (M ⟨0, zero_le, zero_le⟩ ω)) := by simpa using ht
    exact tendsto_nhds_unique htzero tendsto_const_nhds
  have hMcont : ∀ ω, Continuous (fun t => M t ω) := by
    intro ω
    exact continuous_finset_sum _ fun j _ =>
      (continuousChannelIntegral B hB T hBcont hBmeas H ha hc K hb j ω).continuous
  refine ⟨hmzero, hQreg, hMcont, fun lam => ?_⟩
  exact vector_stochastic_exponential_compact_limit B hB hcoord hpast T
    (fun n => s (ns n)) (fun n => hs (ns n)) (fun n => hz (ns n))
    (fun n => c (ns n)) (fun n => hca (ns n)) (fun n => N (ns n))
    (fun n => hcb (ns n)) M Q hMa hQa hconvM
    (ae_of_all _ fun ω t => (hconvQ ω t).comp hns.tendsto_atTop) lam

include hB hcoord hpast in
/-- Exact finite-channel maximal bound for actual bounded continuous adapted
inputs. Compatible approximants, their summed limits, the square bound, and
the exponential martingale are all constructed inside the proof. -/
theorem bounded_continuous_vector_exponential_maximal (T : ℝ≥0)
    (hBcont : ∀ j ω, Continuous (fun t => B j t ω))
    (hBmeas : ∀ j t, Measurable (B j t))
    (hnull : ∀ t A, MeasurableSet A → P A = 0 → MeasurableSet[F t] A)
    (H : Fin d → ℝ≥0 → Ω → ℝ) (ha : ∀ j t, Measurable[F t] (H j t))
    (hc : ∀ j ω, Continuous (fun t => H j t ω)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ j t ω, |H j t ω| ≤ K) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    P {ω | (∃ t : Icc (0 : ℝ≥0) T,
      r ≤ ∑ j, continuousChannelIntegral B hB T hBcont hBmeas H ha hc K hb j ω t) ∧
      (∑ j, ∫ s in Ioc (0 : ℝ≥0) T, (H j s ω) ^ 2 ∂FilteredItoIntegralL2.timeMeasure) ≤ q} ≤
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  obtain ⟨hmzero, hQreg, hMcont, hZ⟩ := bounded_continuous_vector_exponential
    B hB hcoord hpast T hBcont hBmeas hnull H ha hc hK hb
  have hqzero : ∀ᵐ ω ∂P, continuousVectorBracket T H ⟨0, zero_le, zero_le⟩ ω = 0 :=
    ae_of_all _ fun ω => by simp [continuousVectorBracket]
  exact ContinuousExponentialMaximal.compact_exponential_maximal_ae T
    (continuousVectorIntegral B hB T hBcont hBmeas H ha hc K hb) (continuousVectorBracket T H)
    hmzero hqzero (ae_of_all _ fun ω => (hQreg ω).1)
    (ae_of_all _ hMcont) (ae_of_all _ fun ω => (hQreg ω).2) hr hq (hZ (r / q)).supermartingale

/-- A common full-measure convergence event for all coordinates passes through
both finite sums. This is also valid for compact-window time indices. -/
theorem summed_channel_limits {ι : Type*}
    (U V : ℕ → Fin d → ι → Ω → ℝ) (M Q : Fin d → ι → Ω → ℝ)
    (hU : ∀ j, ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n => U n j t ω) atTop (nhds (M j t ω)))
    (hV : ∀ j, ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n => V n j t ω) atTop (nhds (Q j t ω))) :
    ∀ᵐ ω ∂P, ∀ t,
      Tendsto (fun n => ∑ j, U n j t ω) atTop (nhds (∑ j, M j t ω)) ∧
      Tendsto (fun n => ∑ j, V n j t ω) atTop (nhds (∑ j, Q j t ω)) := by
  filter_upwards [ae_all_iff.mpr hU, ae_all_iff.mpr hV] with ω hu hv
  intro t
  exact ⟨tendsto_finset_sum _ fun j hj => hu j t,
    tendsto_finset_sum _ fun j hj => hv j t⟩

end Ripple.Stochastic.FiniteChannelExponentialLimit
