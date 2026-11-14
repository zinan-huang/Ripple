import Ripple.Stochastic.VectorContinuousRealization
import Ripple.Stochastic.ContinuousAdaptedIntegrand
import Ripple.Stochastic.ContinuousItoElementary
import Ripple.Stochastic.StrongSDEFixedPoint
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Concrete drift and coefficient maps on continuous adapted path space

The state space is the closed adapted subspace of the
Bochner space with the uniform path norm. The drift is the actual time
integral. Each diffusion term uses the installed scalar continuous Itô map
and is embedded along its given state-space direction.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace Ripple.Stochastic.StrongSDEConcreteMaps
open AdaptedContinuousSpace ContinuousItoElementary ContinuousAdaptedIntegrand
open FilteredItoIntegralCLM

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

abbrev Window (T : ℝ≥0) := Set.Icc (0 : ℝ≥0) T

instance windowNonempty (T : ℝ≥0) : Nonempty (Window T) :=
  ⟨⟨0, zero_le, zero_le⟩⟩

abbrev State (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :=
  vectorAdaptedSubmodule (E := E) (μ := μ) (fun t : Window T => F t.val)

theorem state_complete (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    CompleteSpace (State (E := E) (μ := μ) F T) :=
  vectorSpace_complete _ (fun t => F.le t.val)

/-- Endpoint freezing makes a compact-window state an all-time process. -/
def cappedTime (T t : ℝ≥0) : Window T :=
  ⟨min t T, zero_le, min_le_right _ _⟩

theorem cappedTime_continuous (T : ℝ≥0) : Continuous (cappedTime T) :=
  (continuous_id.min continuous_const).subtype_mk _

def realize (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X : State (E := E) (μ := μ) F T) (t : ℝ≥0) (ω : Ω) : E :=
  vectorRepresentative X.val ω (cappedTime T t)

theorem realize_continuous (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X : State (E := E) (μ := μ) F T) (ω : Ω) :
    Continuous (fun t => realize F T X t ω) :=
  (vectorRepresentative X.val ω).continuous.comp (cappedTime_continuous T)

theorem realize_adapted (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (X : State (E := E) (μ := μ) F T) : StronglyAdapted F (realize F T X) := by
  intro t
  have h : StronglyMeasurable[F (cappedTime T t).val]
      (fun ω => vectorRepresentative X.val ω (cappedTime T t)) :=
    vectorRepresentative_adapted (fun s : Window T => F s.val) (fun s => hnull s.val) X
      (cappedTime T t)
  exact StronglyMeasurable.mono h (F.mono (min_le_left t T))

theorem realize_supMoment (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X : State (E := E) (μ := μ) F T) :
    Integrable (fun ω => ⨆ t : Window T, ‖realize F T X t.val ω‖ ^ 2) μ := by
  have heq : ∀ t : Window T, cappedTime T t.val = t := by
    intro t
    exact Subtype.ext (min_eq_left t.property.2)
  simpa only [realize, heq] using vectorRepresentative_integrable_sup_sq X.val

/-- The original path is frozen before zero and after T only to define the
ordinary real-time drift integral. Its values on the window are unchanged. -/
def realTime (T : ℝ≥0) (s : ℝ) : Window T := cappedTime T s.toNNReal

theorem realTime_continuous (T : ℝ≥0) : Continuous (realTime T) :=
  (cappedTime_continuous T).comp continuous_real_toNNReal

def driftPath (T : ℝ≥0) (b : E → E) (hb : Continuous b) (x : C(Window T, E)) :
    C(Window T, E) :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t.val : ℝ), b (x (realTime T s)),
    (intervalIntegral.continuous_primitive
      (fun a c => (hb.comp (x.continuous.comp (realTime_continuous T))).intervalIntegrable a c)
      0).comp (NNReal.continuous_coe.comp continuous_subtype_val)⟩

theorem driftPath_norm_le (T : ℝ≥0) (b : E → E) (hb : Continuous b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C) (x : C(Window T, E)) :
    ‖driftPath T b hb x‖ ≤ (T : ℝ) * C := by
  apply (ContinuousMap.norm_le _ (mul_nonneg T.coe_nonneg hC)).mpr
  intro t
  exact (StrongSDE.norm_intervalIntegral_le _ t.val.coe_nonneg
    (fun _ _ => hbC _)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast t.property.2) hC)

theorem driftPath_difference (T : ℝ≥0) (b : E → E) {L : ℝ≥0}
    (hb : LipschitzWith L b) (x y : C(Window T, E)) :
    ‖driftPath T b hb.continuous x - driftPath T b hb.continuous y‖ ≤
      (T : ℝ) * L * ‖x - y‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have h := StrongSDE.drift_integral_difference_le b
    (fun s => x (realTime T s)) (fun s => y (realTime T s)) hb.continuous
    (x.continuous.comp (realTime_continuous T))
    (y.continuous.comp (realTime_continuous T)) t.val.coe_nonneg L.coe_nonneg
    (fun u v => by simpa only [dist_eq_norm] using hb.dist_le_mul u v)
    (fun s _ => (x - y).norm_coe_le_norm (realTime T s))
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast t.property.2) L.coe_nonneg)
    (norm_nonneg _))

theorem driftPath_lipschitz (T : ℝ≥0) (b : E → E) {L : ℝ≥0}
    (hb : LipschitzWith L b) : LipschitzWith (T * L) (driftPath T b hb.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_mul] using driftPath_difference T b hb x y

theorem driftPath_memLp (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (b : E → E) {L : ℝ≥0} (hb : LipschitzWith L b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (X : State (E := E) (μ := μ) F T) :
    MemLp (fun ω => driftPath T b hb.continuous (vectorRepresentative X.val ω)) 2 μ := by
  apply MemLp.of_bound
    ((driftPath_lipschitz T b hb).continuous.comp_stronglyMeasurable
      (vectorRepresentative_stronglyMeasurable X.val)).aestronglyMeasurable ((T : ℝ) * C)
  exact ae_of_all _ fun ω => driftPath_norm_le T b hb.continuous C hC hbC _

/-- Exact slice adaptation of the deterministic time integral. All real-time
arguments in the integral are first capped at the current time. -/
theorem driftPath_adapted (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (b : E → E) (hb : Continuous b) (X : State (E := E) (μ := μ) F T)
    (t : Window T) :
    StronglyMeasurable[F t.val]
      (fun ω => driftPath T b hb (vectorRepresentative X.val ω) t) := by
  let u : ℝ → Ω → E := fun s ω => b (realize F T X (min s.toNNReal t.val) ω)
  have hcont : ∀ ω, Continuous (fun s => u s ω) := fun ω =>
    hb.comp ((realize_continuous F T X ω).comp
      (continuous_real_toNNReal.min continuous_const))
  have hsm : ∀ s, StronglyMeasurable[F t.val] (u s) := fun s =>
    hb.comp_stronglyMeasurable
      ((realize_adapted F T hnull X (min s.toNNReal t.val)).mono
        (F.mono (min_le_right _ _)))
  have hint : StronglyMeasurable[F t.val]
      (fun ω => ∫ s in Ioc (0 : ℝ) (t.val : ℝ), u s ω) := by
    letI : MeasurableSpace Ω := F t.val
    exact (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont hsm).integral_prod_left
  have heq : (fun ω => driftPath T b hb (vectorRepresentative X.val ω) t) =
      fun ω => ∫ s in Ioc (0 : ℝ) (t.val : ℝ), u s ω := by
    funext ω
    change (∫ s in (0 : ℝ)..((t.val : ℝ≥0) : ℝ),
      b (vectorRepresentative X.val ω (realTime T s))) = _
    rw [intervalIntegral.integral_of_le t.val.coe_nonneg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hst : s.toNNReal ≤ t.val := by
      exact Real.toNNReal_le_iff_le_coe.mpr hs.2
    simp only [u, realize, realTime, min_eq_left hst]
  rw [heq]
  exact hint

/-- Drift as an actual element of the same closed adapted path space. -/
def drift (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (b : E → E) {L : ℝ≥0} (hb : LipschitzWith L b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (X : State (E := E) (μ := μ) F T) : State (E := E) (μ := μ) F T := by
  let hm := driftPath_memLp F T b hb C hC hbC X
  refine ⟨hm.toLp _, (mem_vectorAdaptedSubmodule _ _).mpr ?_⟩
  intro t
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  apply (driftPath_adapted F T hnull b hb.continuous X t).aestronglyMeasurable.congr
  filter_upwards [vectorEvalLp_ae t (hm.toLp _), hm.coeFn_toLp] with ω he hp
  rw [he, hp]

theorem drift_coe (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (b : E → E) {L : ℝ≥0} (hb : LipschitzWith L b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (X : State (E := E) (μ := μ) F T) :
    ((drift F T hnull b hb C hC hbC X).val : Ω → C(Window T, E)) =ᵐ[μ]
      fun ω => driftPath T b hb.continuous (vectorRepresentative X.val ω) :=
  (driftPath_memLp F T b hb C hC hbC X).coeFn_toLp

theorem drift_difference (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (b : E → E) {L : ℝ≥0} (hb : LipschitzWith L b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (X Y : State (E := E) (μ := μ) F T) :
    ‖drift F T hnull b hb C hC hbC X - drift F T hnull b hb C hC hbC Y‖ ≤
      (T : ℝ) * L * ‖X - Y‖ := by
  have key : ‖(drift F T hnull b hb C hC hbC X).val - (drift F T hnull b hb C hC hbC Y).val‖ ≤
      (T : ℝ) * L * ‖X.val - Y.val‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [drift_coe F T hnull b hb C hC hbC X,
      drift_coe F T hnull b hb C hC hbC Y,
      Lp.coeFn_sub (drift F T hnull b hb C hC hbC X).val
        (drift F T hnull b hb C hC hbC Y).val,
      Lp.coeFn_sub X.val Y.val, vectorRepresentative_ae X.val,
      vectorRepresentative_ae Y.val] with ω hx hy hd hxy hX hY
    rw [hd, hxy, Pi.sub_apply, Pi.sub_apply, hx, hy, hX, hY]
    simpa only [mul_assoc] using driftPath_difference T b hb
      (vectorRepresentative X.val ω) (vectorRepresentative Y.val ω)
  exact key

/-- The scalar L² norm of the pathwise difference norm equals the vector
path-space norm. This does not use an inner product on continuous paths. -/
theorem pathDifference_energy (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) :
    (∫ ω, ‖vectorRepresentative X.val ω - vectorRepresentative Y.val ω‖ ^ 2 ∂μ) =
      ‖X - Y‖ ^ 2 := by
  let R : Ω → ℝ := fun ω => ‖vectorRepresentative X.val ω - vectorRepresentative Y.val ω‖
  have hm : MemLp R 2 μ :=
    ((vectorRepresentative_memLp X.val).sub (vectorRepresentative_memLp Y.val)).norm
  let r : Lp ℝ 2 μ := hm.toLp R
  have hr : ‖r‖ = ‖X - Y‖ := by
    have hae : ∀ᵐ ω ∂μ, ‖r ω‖ = ‖(X.val - Y.val) ω‖ := by
      filter_upwards [hm.coeFn_toLp, Lp.coeFn_sub X.val Y.val,
        vectorRepresentative_ae X.val, vectorRepresentative_ae Y.val] with ω hr hs hx hy
      simp only [r, hr, hs, Pi.sub_apply, hx, hy, R, norm_norm]
    exact le_antisymm
      (Lp.norm_le_norm_of_ae_le (hae.mono fun _ h => h.le))
      (Lp.norm_le_norm_of_ae_le (hae.mono fun _ h => h.ge))
  rw [← hr, FilteredItoIntegralL2.lp_two_norm_sq]
  exact integral_congr_ae (hm.coeFn_toLp.symm.mono fun _ h => congrArg (fun x : ℝ => x ^ 2) h)

/-- Total notation for the actual integral on a compact window. Its value on
inputs outside the domain is immaterial; all SDE coefficients are proved to
lie in the domain before this definition is used. -/
def windowIto (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ℝ≥0 → Ω → ℝ) [IsFilteredPreBrownian B F μ]
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := by
  classical
  exact if h : MemLp (Function.uncurry H) 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) then
    representative (continuousIto T hB hBmeas (h.toLp (Function.uncurry H))) ω (cappedTime T t)
  else 0

private theorem lp_finset_sum_ae {ι V : Type*} [NormedAddCommGroup V]
    (s : Finset ι) (f : ι → Lp V 2 μ) :
    (fun ω => (∑ i ∈ s, f i) ω) =ᵐ[μ] fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero V 2 μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with ω ha hs
    simp only [ha, hs, Pi.add_apply]

section Noise
variable {ι : Type*} [Fintype ι]
  (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
  (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
  (hB : ∀ i ω, Continuous (fun t => B i t ω))
  (hBmeas : ∀ i t, Measurable (B i t))
  (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
  (ell : ι → E) (g : ι → E → ℝ) (hg : ∀ i, Continuous (g i))
  (K : ι → ℝ) (hK : ∀ i x, |g i x| ≤ K i)

def coefficient (X : State (E := E) (μ := μ) F T) (i : ι) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hBmeas i)) :=
  coefficientLp T (hBmeas i) (realize F T X)
    (fun t => (realize_adapted F T hnull X t).measurable)
    (realize_continuous F T X) (g i) (hg i) (K i) (hK i)

def channelIntegral (X : State (E := E) (μ := μ) F T) (i : ι) : PathLp (Window T) μ :=
  continuousIto T (hB i) (hBmeas i) (coefficient F T B hBmeas hnull g hg K hK X i)

theorem windowIto_coefficient (X : State (E := E) (μ := μ) F T)
    (i : ι) (t : ℝ≥0) (ω : Ω) :
    windowIto (μ := μ) F T (B i) (hB i) (hBmeas i) (fun s ω' => g i (realize F T X s ω')) t ω =
      representative (channelIntegral F T B hB hBmeas hnull g hg K hK X i) ω
        (cappedTime T t) := by
  have hm := integrandMemLp (μ := μ) T (hBmeas i) (fun s ω' => g i (realize F T X s ω'))
    (measurable_comp_sections (fun t => (realize_adapted F T hnull X t).measurable) (hg i))
    (continuous_comp_paths (realize_continuous F T X) (hg i))
    (K i) (fun _ _ => hK i _)
  simp only [windowIto, dif_pos hm]
  rfl

/-- The coefficient energy estimate is derived from its actual composition
with the continuous state, and its norm is the product-time L² norm. -/
theorem coefficient_difference (L : ι → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (g i))
    (X Y : State (E := E) (μ := μ) F T) (i : ι) :
    ‖coefficient F T B hBmeas hnull g hg K hK X i -
      coefficient F T B hBmeas hnull g hg K hK Y i‖ ^ 2 ≤
      (T : ℝ) * (L i : ℝ) ^ 2 * ‖X - Y‖ ^ 2 := by
  let R : Ω → ℝ := fun ω => ‖vectorRepresentative X.val ω - vectorRepresentative Y.val ω‖
  have hR : MemLp R 2 μ :=
    ((vectorRepresentative_memLp X.val).sub (vectorRepresentative_memLp Y.val)).norm
  have hd : ∀ t, t ≤ T → ∀ ω,
      |g i (realize F T X t ω) - g i (realize F T Y t ω)| ≤ (L i : ℝ) * R ω := by
    intro t _ ω
    have hi := (hLip i).dist_le_mul (realize F T X t ω) (realize F T Y t ω)
    rw [Real.dist_eq, dist_eq_norm] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left
      ((vectorRepresentative X.val ω - vectorRepresentative Y.val ω).norm_coe_le_norm
        (cappedTime T t)) (L i).coe_nonneg)
  have h := integrandLp_sub_norm_sq_le T (hBmeas i)
    (fun t ω => g i (realize F T X t ω)) (fun t ω => g i (realize F T Y t ω))
    (measurable_comp_sections (fun t => (realize_adapted F T hnull X t).measurable) (hg i))
    (measurable_comp_sections (fun t => (realize_adapted F T hnull Y t).measurable) (hg i))
    (continuous_comp_paths (realize_continuous F T X) (hg i))
    (continuous_comp_paths (realize_continuous F T Y) (hg i))
    (K i) (K i) (fun _ _ => hK i _) (fun _ _ => hK i _) R hR (L i) hd
  rw [pathDifference_energy F T X Y] at h
  exact h

theorem channelIntegral_difference (L : ι → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (g i))
    (X Y : State (E := E) (μ := μ) F T) (i : ι) :
    ‖channelIntegral F T B hB hBmeas hnull g hg K hK X i -
      channelIntegral F T B hB hBmeas hnull g hg K hK Y i‖ ≤
      2 * Real.sqrt (T : ℝ) * (L i : ℝ) * ‖X - Y‖ := by
  have he := coefficient_difference F T B hBmeas hnull g hg K hK L hLip X Y i
  have hc := continuousIto_norm_le T (hB i) (hBmeas i)
    (coefficient F T B hBmeas hnull g hg K hK X i -
      coefficient F T B hBmeas hnull g hg K hK Y i)
  have hs : ‖coefficient F T B hBmeas hnull g hg K hK X i -
      coefficient F T B hBmeas hnull g hg K hK Y i‖ ≤
      Real.sqrt (T : ℝ) * (L i : ℝ) * ‖X - Y‖ := by
    have hr := Real.sq_sqrt T.coe_nonneg
    have hn : 0 ≤ Real.sqrt (T : ℝ) * (L i : ℝ) * ‖X - Y‖ := by positivity
    have hp : (Real.sqrt (T : ℝ) * (L i : ℝ) * ‖X - Y‖) ^ 2 =
        (T : ℝ) * (L i : ℝ) ^ 2 * ‖X - Y‖ ^ 2 := by rw [mul_pow, mul_pow, hr]
    nlinarith [norm_nonneg (coefficient F T B hBmeas hnull g hg K hK X i -
      coefficient F T B hBmeas hnull g hg K hK Y i)]
  dsimp only [channelIntegral]
  rw [← map_sub]
  exact hc.trans (by nlinarith)

def noise (N : ℕ) (X : State (E := E) (μ := μ) F T) :
    State (E := E) (μ := μ) F T := by
  refine ⟨∑ i, (Real.sqrt (N : ℝ))⁻¹ •
    directionPathLp (ell i) (channelIntegral F T B hB hBmeas hnull g hg K hK X i), ?_⟩
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact directionPathLp_mem _ _ _ (continuousIto_mem_adapted T (hB i) (hBmeas i) _)

theorem noise_realization (N : ℕ) (X : State (E := E) (μ := μ) F T) :
    ∀ᵐ ω ∂μ, ∀ t,
      realize F T (noise F T B hB hBmeas hnull ell g hg K hK N X) t ω =
        ∑ i, ((Real.sqrt (N : ℝ))⁻¹ *
          windowIto (μ := μ) F T (B i) (hB i) (hBmeas i)
            (fun s ω' => g i (realize F T X s ω')) t ω) • ell i := by
  classical
  let J := channelIntegral F T B hB hBmeas hnull g hg K hK X
  let a := (Real.sqrt (N : ℝ))⁻¹
  have hterm : ∀ i, ∀ᵐ ω ∂μ,
      (a • directionPathLp (ell i) (J i)) ω =
        a • directionPathCLM (ell i) (representative (J i) ω) := by
    intro i
    filter_upwards [Lp.coeFn_smul a (directionPathLp (ell i) (J i)),
      directionPathLp_ae (ell i) (J i), representative_ae (J i)] with ω ha hd hr
    rw [ha, Pi.smul_apply, hd, hr]
  filter_upwards [vectorRepresentative_ae
    (noise F T B hB hBmeas hnull ell g hg K hK N X).val,
    lp_finset_sum_ae Finset.univ (fun i => a • directionPathLp (ell i) (J i)),
    ae_all_iff.mpr hterm] with ω hn hs hi
  intro t
  change vectorRepresentative _ ω (cappedTime T t) = _
  rw [← hn]
  change (∑ i, a • directionPathLp (ell i) (J i)) ω (cappedTime T t) = _
  rw [hs]
  simp only [ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i, windowIto_coefficient F T B hB hBmeas hnull g hg K hK X i t ω]
  change a • (representative (J i) ω (cappedTime T t) • ell i) = _
  rw [smul_smul]

/-- A finite-channel norm bound suffices for Picard contraction. It does not
assert independence of random integrals or use an unproduced vector isometry. -/
theorem noise_difference (L : ι → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (g i))
    (N : ℕ) (hN : 1 ≤ N) (X Y : State (E := E) (μ := μ) F T) :
    ‖noise F T B hB hBmeas hnull ell g hg K hK N X -
      noise F T B hB hBmeas hnull ell g hg K hK N Y‖ ≤
      2 * Real.sqrt (T : ℝ) * (∑ i, ‖ell i‖ * (L i : ℝ)) * ‖X - Y‖ := by
  classical
  have ha := StrongSDE.inverse_sqrt_nat_bounds hN
  change ‖(∑ i, (Real.sqrt (N : ℝ))⁻¹ • directionPathLp (ell i)
    (channelIntegral F T B hB hBmeas hnull g hg K hK X i)) -
    ∑ i, (Real.sqrt (N : ℝ))⁻¹ • directionPathLp (ell i)
    (channelIntegral F T B hB hBmeas hnull g hg K hK Y i)‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(Real.sqrt (N : ℝ))⁻¹ • directionPathLp (ell i)
          (channelIntegral F T B hB hBmeas hnull g hg K hK X i) -
        (Real.sqrt (N : ℝ))⁻¹ • directionPathLp (ell i)
          (channelIntegral F T B hB hBmeas hnull g hg K hK Y i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖ell i‖ * (2 * Real.sqrt (T : ℝ) * (L i : ℝ) * ‖X - Y‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
      calc
        _ ≤ ‖directionPathLp (ell i)
          (channelIntegral F T B hB hBmeas hnull g hg K hK X i -
           channelIntegral F T B hB hBmeas hnull g hg K hK Y i)‖ := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right ha.2 (norm_nonneg _)
        _ ≤ ‖ell i‖ * ‖channelIntegral F T B hB hBmeas hnull g hg K hK X i -
            channelIntegral F T B hB hBmeas hnull g hg K hK Y i‖ := directionPathLp_norm_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (channelIntegral_difference F T B hB hBmeas hnull g hg K hK L hLip X Y i)
          (norm_nonneg _)
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

theorem noise_difference_sq (L : ι → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (g i))
    (N : ℕ) (hN : 1 ≤ N) (X Y : State (E := E) (μ := μ) F T) :
    ‖noise F T B hB hBmeas hnull ell g hg K hK N X -
      noise F T B hB hBmeas hnull ell g hg K hK N Y‖ ^ 2 ≤
      4 * (T : ℝ) * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2 * ‖X - Y‖ ^ 2 := by
  have h := noise_difference F T B hB hBmeas hnull ell g hg K hK L hLip N hN X Y
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  have heq : (2 * Real.sqrt (T : ℝ) * (∑ i, ‖ell i‖ * (L i : ℝ)) * ‖X - Y‖) ^ 2 =
      4 * (T : ℝ) * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2 * ‖X - Y‖ ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt T.coe_nonneg]
    ring
  nlinarith

/-- The scalar terminal isometry used in every channel is the installed theorem. -/
theorem terminalIsometry (i : ι)
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hBmeas i))) :
    ‖itoIntegralCLM_T (𝓖 := F) (μ := μ) T (hBmeas i) U‖ = ‖U‖ :=
  itoIntegralCLM_T_norm T (hBmeas i) U

/-- Doob's bound is produced by the continuous integral construction and the
terminal isometry, rather than supplied by the SDE caller. -/
theorem doobMaximal (i : ι)
    (U : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T (hBmeas i))) :
    ‖continuousIto T (hB i) (hBmeas i) U‖ ^ 2 ≤
      4 * ‖itoIntegralCLM_T (𝓖 := F) (μ := μ) T (hBmeas i) U‖ ^ 2 := by
  rw [itoIntegralCLM_T_norm]
  have h := continuousIto_norm_le T (hB i) (hBmeas i) U
  nlinarith [norm_nonneg (continuousIto T (hB i) (hBmeas i) U), norm_nonneg U]

end Noise

/-- A deterministic initial state belongs to the actual adapted path carrier. -/
def initial (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (x : E) : State (E := E) (μ := μ) F T := by
  let hm : MemLp (fun _ : Ω => ContinuousMap.const (Window T) x) 2 μ := memLp_const _
  refine ⟨hm.toLp _, (mem_vectorAdaptedSubmodule _ _).mpr ?_⟩
  intro t
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  apply (stronglyMeasurable_const : StronglyMeasurable[F t.val] (fun _ : Ω => x)).aestronglyMeasurable.congr
  filter_upwards [vectorEvalLp_ae t (hm.toLp _), hm.coeFn_toLp] with ω he hp
  rw [he, hp]
  rfl

theorem initial_realization (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (x : E) :
    ∀ᵐ ω ∂μ, ∀ t, realize F T (initial (μ := μ) F T x) t ω = x := by
  filter_upwards [vectorRepresentative_ae (initial (μ := μ) F T x).val,
    (memLp_const (p := (2 : ℝ≥0∞)) (μ := μ) (ContinuousMap.const (Window T) x)).coeFn_toLp]
      with ω hr hc
  have hval : (initial (μ := μ) F T x).val =
      (memLp_const (p := (2 : ℝ≥0∞)) (μ := μ) (ContinuousMap.const (Window T) x)).toLp _ := rfl
  intro t
  change vectorRepresentative _ ω (cappedTime T t) = _
  rw [← hr, hval, hc]
  rfl

theorem realize_add (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (X Y : State (E := E) (μ := μ) F T) :
    ∀ᵐ ω ∂μ, ∀ t, realize F T (X + Y) t ω = realize F T X t ω + realize F T Y t ω := by
  filter_upwards [vectorRepresentative_ae (X + Y).val,
    vectorRepresentative_ae X.val, vectorRepresentative_ae Y.val,
    Lp.coeFn_add X.val Y.val] with ω hxy hx hy ha
  intro t
  change vectorRepresentative _ ω (cappedTime T t) = _
  rw [← hxy, Submodule.coe_add, ha, Pi.add_apply, hx, hy]
  rfl

/-- The one-step identity is proved for every input in the actual carrier. -/
theorem step_realization {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (hg : ∀ i, Continuous (g i))
    (K : ι → ℝ) (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) {L : ℝ≥0} (hb : LipschitzWith L b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C) (x₀ : E)
    (N : ℕ) (X : State (E := E) (μ := μ) F T) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T,
      realize F T (StrongSDE.picardStep (initial F T x₀)
        (drift F T hnull b hb C hC hbC)
        (noise F T B hB hBmeas hnull ell g hg K hK N) X) t ω =
      StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i))
        ell g b x₀ N (realize F T X) t ω := by
  let D := drift F T hnull b hb C hC hbC X
  let J := noise F T B hB hBmeas hnull ell g hg K hK N X
  filter_upwards [realize_add F T (initial F T x₀ + D) J,
    realize_add F T (initial F T x₀) D, initial_realization F T x₀,
    noise_realization F T B hB hBmeas hnull ell g hg K hK N X,
    vectorRepresentative_ae D.val, drift_coe F T hnull b hb C hC hbC X]
      with ω hsum hinit hi hn hD hd
  intro t ht
  have hdval : realize F T D t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), b (realize F T X s.toNNReal ω) := by
    change vectorRepresentative D.val ω (cappedTime T t) = _
    rw [← hD, hd]
    change (∫ s in (0 : ℝ)..((min t T : ℝ≥0) : ℝ),
      b (vectorRepresentative X.val ω (realTime T s))) = _
    rw [min_eq_left ht]
    rfl
  change realize F T ((initial F T x₀ + D) + J) t ω = _
  rw [hsum, hinit, hi, hn, hdval]
  dsimp [StrongSDE.sdeRhs]
  abel

/-- Local existence on the constructed carrier, with the drift and diffusion
maps fixed explicitly. The only small-window condition is displayed. -/
theorem exists_unique_concrete_picard {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C) (x₀ : E)
    (N : ℕ) (hN : 1 ≤ N)
    (hSmall : 2 * (T : ℝ) ^ 2 * (Lb : ℝ) ^ 2 +
      8 * (T : ℝ) * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2 < 1) :
    ∃! X : State (E := E) (μ := μ) F T,
      StrongSDE.picardStep (initial F T x₀) (drift F T hnull b hb C hC hbC)
        (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N) X = X := by
  letI := state_complete (E := E) (μ := μ) F T
  apply StrongSDE.exists_unique_picard _ _ _ T.coe_nonneg
    (sq_nonneg (∑ i, ‖ell i‖ * (L i : ℝ))) hSmall
  · intro X Y
    have h := drift_difference F T hnull b hb C hC hbC X Y
    have hs := mul_self_le_mul_self (norm_nonneg _) h
    nlinarith
  · exact noise_difference_sq F T B hB hBmeas hnull ell g
      (fun i => (hLip i).continuous) K hK L hLip N hN

/-- Every realization premise of the former abstract finite-horizon theorem
is supplied by the concrete maps. Smallness is still a local-window condition. -/
theorem exists_concrete_solution {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C) (x₀ : E)
    (N : ℕ) (hN : 1 ≤ N)
    (hSmall : 2 * (T : ℝ) ^ 2 * (Lb : ℝ) ^ 2 +
      8 * (T : ℝ) * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2 < 1) :
    ∃ X : State (E := E) (μ := μ) F T,
      StronglyAdapted F (realize F T X) ∧
      (∀ ω, Continuous (fun t => realize F T X t ω)) ∧
      Integrable (fun ω => ⨆ t : Window T, ‖realize F T X t.val ω‖ ^ 2) μ ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, realize F T X t ω =
        StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i))
          ell g b x₀ N (realize F T X) t ω) := by
  obtain ⟨X, hX, _⟩ := exists_unique_concrete_picard F T B hB hBmeas hnull
    ell g L hLip K hK b Lb hb C hC hbC x₀ N hN hSmall
  refine ⟨X, realize_adapted F T hnull X, realize_continuous F T X,
    realize_supMoment F T X, ?_⟩
  have hs := step_realization F T B hB hBmeas hnull ell g
    (fun i => (hLip i).continuous) K hK b hb C hC hbC x₀ N X
  simpa only [hX] using hs

/-- The continuous realization is faithful to the path-space quotient. -/
theorem eq_of_realize_eq (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    {X Y : State (E := E) (μ := μ) F T}
    (h : ∀ᵐ ω ∂μ, ∀ t ≤ T, realize F T X t ω = realize F T Y t ω) : X = Y := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [h, vectorRepresentative_ae X.val, vectorRepresentative_ae Y.val]
    with ω hω hx hy
  rw [hx, hy]
  apply ContinuousMap.ext
  intro t
  have hcap : cappedTime T t.val = t := Subtype.ext (min_eq_left t.property.2)
  simpa only [realize, hcap] using hω t.val t.property.2

/-- Uniqueness for solutions represented in the S² carrier follows from their
equations, not from a premise already asserting that they are fixed points. -/
theorem concrete_solution_unique {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C) (x₀ : E)
    (N : ℕ) (hN : 1 ≤ N)
    (hSmall : 2 * (T : ℝ) ^ 2 * (Lb : ℝ) ^ 2 +
      8 * (T : ℝ) * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2 < 1)
    (X Y : State (E := E) (μ := μ) F T)
    (hX : ∀ᵐ ω ∂μ, ∀ t ≤ T, realize F T X t ω =
      StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i))
        ell g b x₀ N (realize F T X) t ω)
    (hY : ∀ᵐ ω ∂μ, ∀ t ≤ T, realize F T Y t ω =
      StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i))
        ell g b x₀ N (realize F T Y) t ω) :
    X = Y ∧ ∀ᵐ ω ∂μ, ∀ t, realize F T X t ω = realize F T Y t ω := by
  let Φ := StrongSDE.picardStep (initial F T x₀) (drift F T hnull b hb C hC hbC)
    (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N)
  have hfixed : ∀ Z : State (E := E) (μ := μ) F T,
      (∀ᵐ ω ∂μ, ∀ t ≤ T, realize F T Z t ω =
        StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i))
          ell g b x₀ N (realize F T Z) t ω) → Φ Z = Z := by
    intro Z hZ
    apply eq_of_realize_eq F T
    filter_upwards [step_realization F T B hB hBmeas hnull ell g
      (fun i => (hLip i).continuous) K hK b hb C hC hbC x₀ N Z, hZ] with ω hs hz
    exact fun t ht => (hs t ht).trans (hz t ht).symm
  obtain ⟨Z, _, huniq⟩ := exists_unique_concrete_picard F T B hB hBmeas hnull
    ell g L hLip K hK b Lb hb C hC hbC x₀ N hN hSmall
  have hxy : X = Y := (huniq X (hfixed X hX)).trans (huniq Y (hfixed Y hY)).symm
  refine ⟨hxy, ?_⟩
  subst Y
  exact ae_of_all _ fun _ _ => rfl

/-- A square-integrable random initial condition, measurable at the start of
the window, embeds as a constant path. This is the carrier needed after a
deterministic time shift when continuing a solution. -/
def randomInitial (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (ξ : lpMeas E ℝ (F 0) 2 μ) : State (E := E) (μ := μ) F T := by
  let C : E →L[ℝ] C(Window T, E) := ContinuousLinearMap.const ℝ (Window T)
  refine ⟨C.compLpL 2 μ ξ.val, (mem_vectorAdaptedSubmodule _ _).mpr ?_⟩
  intro t
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have hξ := (mem_lpMeas_iff_aestronglyMeasurable.mp ξ.property).mono
    (F.mono (zero_le : (0 : ℝ≥0) ≤ t.val))
  apply hξ.congr
  filter_upwards [vectorEvalLp_ae t (C.compLpL 2 μ ξ.val),
    C.coeFn_compLpL ξ.val] with ω he hc
  rw [he, hc]
  rfl

theorem randomInitial_realization (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (ξ : lpMeas E ℝ (F 0) 2 μ) :
    ∀ᵐ ω ∂μ, ∀ t, realize F T (randomInitial F T ξ) t ω = ξ.val ω := by
  let C : E →L[ℝ] C(Window T, E) := ContinuousLinearMap.const ℝ (Window T)
  filter_upwards [vectorRepresentative_ae (randomInitial F T ξ).val,
    C.coeFn_compLpL ξ.val] with ω hr hc
  have hval : (randomInitial F T ξ).val = C.compLpL 2 μ ξ.val := rfl
  intro t
  change vectorRepresentative _ ω (cappedTime T t) = _
  rw [← hr, hval, hc]
  rfl

/-- The contraction does not depend on the initial condition. In particular
it applies to the random endpoint of a previous short window. -/
theorem exists_unique_picard_from_initial {ι : Type*} [Fintype ι]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C)
    (X₀ : State (E := E) (μ := μ) F T) (N : ℕ) (hN : 1 ≤ N)
    (hSmall : 2 * (T : ℝ) ^ 2 * (Lb : ℝ) ^ 2 +
      8 * (T : ℝ) * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2 < 1) :
    ∃! X : State (E := E) (μ := μ) F T,
      StrongSDE.picardStep X₀ (drift F T hnull b hb C hC hbC)
        (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N) X = X := by
  letI := state_complete (E := E) (μ := μ) F T
  apply StrongSDE.exists_unique_picard _ _ _ T.coe_nonneg
    (sq_nonneg (∑ i, ‖ell i‖ * (L i : ℝ))) hSmall
  · intro X Y
    have h := drift_difference F T hnull b hb C hC hbC X Y
    have hs := mul_self_le_mul_self (norm_nonneg _) h
    nlinarith
  · exact noise_difference_sq F T B hB hBmeas hnull ell g
      (fun i => (hLip i).continuous) K hK L hLip N hN

end Ripple.Stochastic.StrongSDEConcreteMaps
