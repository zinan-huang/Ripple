import Ripple.Stochastic.SimpleStochasticExponential
import Ripple.Stochastic.ExponentialMartingaleLimit
import Ripple.Stochastic.ContinuousExponentialMaximal

/-!
# Moment bounds and limits of bounded predictable stochastic exponentials

The elementary martingale is constructed from Gaussian increments in the imported
module. This file derives its uniform square moment and the martingale limit.
The last theorem exposes only bounded elementary approximation and convergence
of the integral and bracket; it does not assume an exponential martingale.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.BoundedStochasticExponential
open SimpleStochasticExponential ExponentialMartingaleLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The actual simple stochastic integral at a time, with stopped increments. -/
noncomputable def simpleSum (B : ℝ≥0 → Ω → ℝ) (s : ℕ → ℝ≥0)
    (c : ℕ → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, c i ω * (B (min (s (i + 1)) t) ω - B (min (s i) t) ω)

/-- The actual simple bracket, using the same partition and coefficients. -/
noncomputable def simpleBracket (s : ℕ → ℝ≥0)
    (c : ℕ → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, (c i ω) ^ 2 *
    (((min (s (i + 1)) t : ℝ≥0) : ℝ) - (min (s i) t : ℝ))

/-- Finite products of normalized cell factors have the asserted compensated exponent. -/
theorem simple_exp_eq (B : ℝ≥0 → Ω → ℝ) (s : ℕ → ℝ≥0)
    (c : ℕ → Ω → ℝ) (lam : ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    simpleDoleansExp (X := B) s (fun i ω => lam * c i ω) N t ω =
      Real.exp (lam * simpleSum B s c N t ω - lam ^ 2 * simpleBracket s c N t ω / 2) := by
  induction N with
  | zero => simp [simpleDoleansExp, simpleSum, simpleBracket]
  | succ N ih =>
    rw [simpleDoleansExp, ih, cellExp, ← Real.exp_add]
    congr 1
    simp only [simpleSum, simpleBracket, Finset.sum_range_succ, NNReal.coe_min]
    ring

/-- The deterministic quadratic-variation bound holds at every time, even
past the final partition point. -/
theorem simpleBracket_le (s : ℕ → ℝ≥0) (hs : Monotone s) (hszero : s 0 = 0)
    (c : ℕ → Ω → ℝ) {K : ℝ} (hc : ∀ i ω, |c i ω| ≤ K)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) : simpleBracket s c N t ω ≤ K ^ 2 * (t : ℝ) := by
  have htel : ∑ i ∈ Finset.range N,
      (((min (s (i + 1)) t : ℝ≥0) : ℝ) - (min (s i) t : ℝ)) =
      ((min (s N) t : ℝ≥0) : ℝ) - (min (s 0) t : ℝ) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [NNReal.coe_min]
      ring
  calc
    simpleBracket s c N t ω ≤ ∑ i ∈ Finset.range N,
        K ^ 2 * (((min (s (i + 1)) t : ℝ≥0) : ℝ) - (min (s i) t : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right
      · nlinarith [(abs_le.mp (hc i ω)).1, (abs_le.mp (hc i ω)).2]
      · exact sub_nonneg.mpr (by exact_mod_cast min_le_min_right t (hs (Nat.le_succ i)))
    _ = K ^ 2 * ((min (s N) t : ℝ≥0) : ℝ) := by
      rw [← Finset.mul_sum, htel, hszero]
      simp
    _ ≤ K ^ 2 * (t : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right (s N) t) (sq_nonneg K)

/-- The elementary bracket is adapted: a coefficient is used only after
its left endpoint, and the corresponding term vanishes before that time. -/
theorem simpleBracket_stronglyAdapted (F : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (c : ℕ → Ω → ℝ)
    (hc : ∀ i, StronglyMeasurable[F (s i)] (c i)) (N : ℕ) :
    StronglyAdapted F (simpleBracket s c N) := by
  intro t
  unfold simpleBracket
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  by_cases hit : s i ≤ t
  · exact ((((continuous_pow 2).comp_stronglyMeasurable ((hc i).mono (F.mono hit))).mul
      stronglyMeasurable_const))
  · have hti : t ≤ s i := le_of_lt (lt_of_not_ge hit)
    have htn : t ≤ s (i + 1) := hti.trans (hs (Nat.le_succ i))
    simpa only [NNReal.coe_min, min_eq_right (NNReal.coe_le_coe.mpr hti),
      min_eq_right (NNReal.coe_le_coe.mpr htn), sub_self, mul_zero] using
      (stronglyMeasurable_const : StronglyMeasurable[F t] (fun _ : Ω => (0 : ℝ)))

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
  [IsFilteredPreBrownian B F P]

/-- The initial value of every elementary exponential is one. -/
theorem simple_exp_zero (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    simpleDoleansExp (X := B) s c N 0 ω = 1 := by
  induction N with
  | zero => rfl
  | succ N ih => simp [simpleDoleansExp, cellExp, ih]

/-- Mean one is derived from the elementary continuous-time martingale. -/
theorem simple_exp_mean (s : ℕ → ℝ≥0) (hs : Monotone s)
    (c : ℕ → Ω → ℝ) (hc : ∀ i, StronglyMeasurable[F (s i)] (c i))
    {K : ℝ} (hK : ∀ i ω, |c i ω| ≤ K) (N : ℕ) (t : ℝ≥0) :
    (∫ ω, simpleDoleansExp (X := B) s c N t ω ∂P) = 1 := by
  have hZ := simpleDoleansExp_isMartingale (X := B) (P := P) s hs c hc hK N
  have hcond := hZ.condExp_ae_eq (show (0 : ℝ≥0) ≤ t from bot_le)
  calc
    (∫ ω, simpleDoleansExp (X := B) s c N t ω ∂P) =
        ∫ ω, P[fun ω => simpleDoleansExp (X := B) s c N t ω | F 0] ω ∂P :=
      (integral_condExp (F.le 0)).symm
    _ = ∫ ω, simpleDoleansExp (X := B) s c N 0 ω ∂P := integral_congr_ae hcond
    _ = 1 := by simp [simple_exp_zero]

/-- The rescaled elementary exponential is a continuous-time martingale. -/
theorem scaled_simple_martingale (s : ℕ → ℝ≥0) (hs : Monotone s)
    (c : ℕ → Ω → ℝ) (hc : ∀ i, StronglyMeasurable[F (s i)] (c i))
    {K : ℝ} (hK : ∀ i ω, |c i ω| ≤ K) (lam : ℝ) (N : ℕ) :
    Martingale (fun t ω => Real.exp (lam * simpleSum B s c N t ω -
      lam ^ 2 * simpleBracket s c N t ω / 2)) F P := by
  simpa only [simple_exp_eq] using
    (simpleDoleansExp_isMartingale (X := B) s hs (fun i ω => lam * c i ω)
      (fun i => (hc i).const_mul lam)
      (fun i ω => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK i ω) (abs_nonneg lam)) N)

/-- Uniform L² bound for elementary exponentials. It is independent of the
partition and its number of cells. -/
theorem simple_exp_sq_bound (s : ℕ → ℝ≥0) (hs : Monotone s) (hszero : s 0 = 0)
    (c : ℕ → Ω → ℝ) (hc : ∀ i, StronglyMeasurable[F (s i)] (c i))
    {K : ℝ} (hK : ∀ i ω, |c i ω| ≤ K) (lam : ℝ) (N : ℕ) (t : ℝ≥0) :
    Integrable (fun ω => (Real.exp (lam * simpleSum B s c N t ω -
      lam ^ 2 * simpleBracket s c N t ω / 2)) ^ 2) P ∧
    (∫ ω, (Real.exp (lam * simpleSum B s c N t ω -
      lam ^ 2 * simpleBracket s c N t ω / 2)) ^ 2 ∂P) ≤
      Real.exp (lam ^ 2 * (K ^ 2 * (t : ℝ))) := by
  have hdouble := scaled_simple_martingale (B := B) (P := P) s hs c hc hK (2 * lam) N
  have hmean : (∫ ω, Real.exp ((2 * lam) * simpleSum B s c N t ω -
      (2 * lam) ^ 2 * simpleBracket s c N t ω / 2) ∂P) = 1 := by
    simpa only [simple_exp_eq] using simple_exp_mean (B := B) s hs
      (fun i ω => (2 * lam) * c i ω) (fun i => (hc i).const_mul _)
      (fun i ω => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK i ω) (abs_nonneg _)) N t
  have hcmeas : ∀ i, Measurable (c i) := fun i => ((hc i).mono (F.le _)).measurable
  have hBmeas : ∀ u, Measurable (B u) := fun u =>
    ((IsFilteredPreBrownian.stronglyAdapted (X := B) (𝓕 := F) (P := P) u).mono (F.le u)).measurable
  apply exponential_sq_bound (simpleSum B s c N t) (simpleBracket s c N t) lam (K ^ 2 * (t : ℝ))
  · unfold simpleSum
    fun_prop
  · unfold simpleBracket
    fun_prop
  · exact ae_of_all _ (simpleBracket_le s hs hszero c hK N t)
  · exact hdouble.integrable t
  · exact hmean

/-- Bounded elementary approximations produce the stochastic exponential
martingale of their integral/bracket limit. All exponential martingale and
uniform-integrability premises are discharged internally. -/
theorem stochastic_exponential_of_bounded_approximation
    (s : ℕ → ℕ → ℝ≥0) (hs : ∀ n, Monotone (s n)) (hszero : ∀ n, s n 0 = 0)
    (c : ℕ → ℕ → Ω → ℝ) (hc : ∀ n i, StronglyMeasurable[F (s n i)] (c n i))
    (N : ℕ → ℕ) {K : ℝ} (hK : ∀ n i ω, |c n i ω| ≤ K)
    (M Q : ℝ≥0 → Ω → ℝ) (hM : StronglyAdapted F M) (hQ : StronglyAdapted F Q)
    (hlimM : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => simpleSum B (s n) (c n) (N n) t ω)
      atTop (nhds (M t ω)))
    (hlimQ : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => simpleBracket (s n) (c n) (N n) t ω)
      atTop (nhds (Q t ω))) (lam : ℝ) :
    Martingale (fun t ω => Real.exp (lam * M t ω - lam ^ 2 * Q t ω / 2)) F P := by
  apply martingale_of_ae_limit_of_sq_integral_le F
    (fun n t ω => Real.exp (lam * simpleSum B (s n) (c n) (N n) t ω -
      lam ^ 2 * simpleBracket (s n) (c n) (N n) t ω / 2))
  · exact fun n => scaled_simple_martingale (s n) (hs n) (c n) (hc n) (hK n) lam (N n)
  · intro t
    exact (Real.measurable_exp.comp (((hM t).measurable.const_mul lam).sub
      (((hQ t).measurable.const_mul (lam ^ 2)).div_const 2))).stronglyMeasurable
  · exact fun n t => (simple_exp_sq_bound (s n) (hs n) (hszero n) (c n) (hc n) (hK n) lam (N n) t).1
  · exact fun t => ⟨Real.exp (lam ^ 2 * (K ^ 2 * (t : ℝ))), fun n =>
      (simple_exp_sq_bound (s n) (hs n) (hszero n) (c n) (hc n) (hK n) lam (N n) t).2⟩
  · intro t
    filter_upwards [hlimM t, hlimQ t] with ω hMω hQω
    exact Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul hMω).sub ((tendsto_const_nhds.mul hQω).div_const 2))

/-- The continuous constrained maximal bound with its exponential martingale
produced by the bounded elementary approximation theorem. -/
theorem bounded_approximation_exponential_maximal
    (s : ℕ → ℕ → ℝ≥0) (hs : ∀ n, Monotone (s n)) (hszero : ∀ n, s n 0 = 0)
    (c : ℕ → ℕ → Ω → ℝ) (hc : ∀ n i, StronglyMeasurable[F (s n i)] (c n i))
    (N : ℕ → ℕ) {K : ℝ} (hK : ∀ n i ω, |c n i ω| ≤ K)
    (M Q : ℝ≥0 → Ω → ℝ) (hM : StronglyAdapted F M) (hQ : StronglyAdapted F Q)
    (hlimM : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => simpleSum B (s n) (c n) (N n) t ω)
      atTop (nhds (M t ω)))
    (hlimQ : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => simpleBracket (s n) (c n) (N n) t ω)
      atTop (nhds (Q t ω)))
    (hQmono : ∀ᵐ ω ∂P, Monotone (fun t => Q t ω))
    (hMcont : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hQcont : ∀ᵐ ω ∂P, Continuous (fun t => Q t ω))
    (T : ℝ≥0) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    P (ExponentialMaximal.crossingEvent M Q T r q) ≤
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  have hMzero : ∀ᵐ ω ∂P, M 0 ω = 0 := by
    filter_upwards [hlimM 0] with ω hω
    have h : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (M 0 ω)) := by
      simpa [simpleSum] using hω
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hQzero : ∀ᵐ ω ∂P, Q 0 ω = 0 := by
    filter_upwards [hlimQ 0] with ω hω
    have h : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (Q 0 ω)) := by
      simpa [simpleBracket] using hω
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hZ := stochastic_exponential_of_bounded_approximation s hs hszero c hc N hK
    M Q hM hQ hlimM hlimQ (r / q)
  exact ContinuousExponentialMaximal.continuous_exponential_maximal_ae
    M Q hMzero hQzero hQmono hMcont hQcont T hr hq hZ.supermartingale

end Ripple.Stochastic.BoundedStochasticExponential
