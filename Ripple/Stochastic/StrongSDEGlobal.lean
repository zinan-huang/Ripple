import Ripple.Stochastic.HorizonItoRestriction
import Ripple.Stochastic.ConsistentHorizonProcess
import Ripple.Stochastic.StrongSDEGronwall
import Ripple.Stochastic.AllTimeIto

/-!
# Strong solutions on finite and infinite horizons

The finite-horizon existence theorem uses the concrete
factorial Picard construction. Uniqueness uses the actual continuous running
moment and integral Gronwall. Arbitrary adapted a.s. continuous solutions are
embedded after deriving their path moment from bounded coefficients.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Stochastic.StrongSDEGlobal
open AdaptedContinuousSpace StrongSDEConcreteMaps StrongSDESolutionSpace
open StrongSDETimeEstimate StrongSDERunningMoment ContinuousAdaptedIntegrand
open HorizonItoRestriction

variable {Ω E ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The original finite-channel equation with the installed window integrals. -/
def Equation (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (ell : ι → E) (g : ι → E → ℝ) (b : E → E) (x₀ : E) (N : ℕ)
    (Z : ℝ≥0 → Ω → E) : Prop :=
  ∀ᵐ ω ∂μ, ∀ t ≤ T, Z t ω =
    StrongSDE.sdeRhs (fun i => windowIto (μ := μ) F T (B i) (hB i) (hBmeas i)) ell g b x₀ N Z t ω

/-- The equation with the actual all-time locally square-integrable Itô integrals. -/
def GlobalEquation (F : Filtration ℝ≥0 mΩ)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (ell : ι → E) (g : ι → E → ℝ) (b : E → E) (x₀ : E) (N : ℕ)
    (Z : ℝ≥0 → Ω → E) : Prop :=
  ∀ᵐ ω ∂μ, ∀ t,
    Z t ω = StrongSDE.sdeRhs
      (fun i => AllTimeIto.globalIto (μ := μ) F (B i) (hB i) (hBmeas i)) ell g b x₀ N Z t ω

section Coefficients
variable (F : Filtration ℝ≥0 mΩ)
    (B : ι → ℝ≥0 → Ω → ℝ) [∀ i, IsFilteredPreBrownian (B i) F μ]
    (hB : ∀ i ω, Continuous (fun t => B i t ω))
    (hBmeas : ∀ i t, Measurable (B i t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (ell : ι → E) (g : ι → E → ℝ) (L : ι → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (g i)) (K : ι → ℝ)
    (hK : ∀ i x, |g i x| ≤ K i)
    (b : E → E) (Lb : ℝ≥0) (hb : LipschitzWith Lb b)
    (C : ℝ) (hC : 0 ≤ C) (hbC : ∀ x, ‖b x‖ ≤ C) (x₀ : E)

include hnull hLip hK hb hC hbC

/-- Existence on any finite horizon, with the original equation and moment.
No numerical smallness condition is present. Zero horizon is also allowed. -/
theorem exists_solution (T : ℝ≥0) (N : ℕ) (hN : 1 ≤ N) :
    ∃ X : State (E := E) (μ := μ) F T,
      StronglyAdapted F (realize F T X) ∧
      (∀ ω, Continuous (fun t => realize F T X t ω)) ∧
      Integrable (fun ω => ⨆ t : StrongSDEConcreteMaps.Window T,
        ‖realize F T X t.val ω‖ ^ 2) μ ∧
      Equation (μ := μ) F T B hB hBmeas ell g b x₀ N (realize F T X) := by
  obtain ⟨X, hx, _⟩ := exists_unique_concrete_picard_global F T B hB hBmeas hnull
    ell g L hLip K hK b Lb hb C hC hbC (initial F T x₀) N hN
  refine ⟨X, realize_adapted F T hnull X, realize_continuous F T X,
    realize_supMoment F T X, ?_⟩
  have h := step_realization F T B hB hBmeas hnull ell g
    (fun i => (hLip i).continuous) K hK b hb C hC hbC x₀ N X
  simpa only [hx] using h

/-- A carrier solution is fixed by the actual Picard map. -/
theorem fixed_of_equation (T : ℝ≥0) (N : ℕ)
    (X : State (E := E) (μ := μ) F T)
    (hx : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N (realize F T X)) :
    StrongSDE.picardStep (initial F T x₀) (drift F T hnull b hb C hC hbC)
      (noise F T B hB hBmeas hnull ell g (fun i => (hLip i).continuous) K hK N) X = X := by
  apply eq_of_realize_eq F T
  filter_upwards [step_realization F T B hB hBmeas hnull ell g
    (fun i => (hLip i).continuous) K hK b hb C hC hbC x₀ N X, hx] with ω hs he
  exact fun t ht => (hs t ht).trans (he t ht).symm

/-- Gronwall applied to the produced running moment proves carrier uniqueness
on the whole horizon; this argument does not use a short-time contraction. -/
theorem carrier_unique (T : ℝ≥0) (N : ℕ) (hN : 1 ≤ N)
    (X Y : State (E := E) (μ := μ) F T)
    (hx : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N (realize F T X))
    (hy : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N (realize F T Y)) : X = Y := by
  have hfx := fixed_of_equation F B hB hBmeas hnull ell g L hLip K hK
    b Lb hb C hC hbC x₀ T N X hx
  have hfy := fixed_of_equation F B hB hBmeas hnull ell g L hLip K hK
    b Lb hb C hC hbC x₀ T N Y hy
  let c := 2 * (T : ℝ) * (Lb : ℝ) ^ 2 + 8 * (∑ i, ‖ell i‖ * (L i : ℝ)) ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hvol : ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      runningProfile F T X Y t.toNNReal ≤
        ∫ s in (0 : ℝ)..t, c * runningProfile F T X Y s.toNNReal := by
    intro t ht
    have htt : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have h := picardStep_local_sq_le F T t.toNNReal htt B hB hBmeas hnull
      ell g L hLip K hK b Lb hb C hC hbC (initial F T x₀) N hN X Y
    rw [hfx, hfy, integral_timeMeasure_T_eq_intervalIntegral,
      Real.coe_toNNReal t ht.1] at h
    simpa only [intervalIntegral.integral_const_mul] using h
  have hz := StrongSDE.continuous_integral_gronwall_zero
    (runningProfile_real_continuous F T X Y) T.coe_nonneg hc
    (fun t _ => runningProfile_nonneg F T X Y t.toNNReal) hvol
    (T : ℝ) ⟨T.coe_nonneg, le_rfl⟩
  rw [Real.toNNReal_coe, runningProfile_terminal] at hz
  have hn : ‖X - Y‖ = 0 := by nlinarith [norm_nonneg (X - Y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Arbitrary adapted a.s. continuous solutions produce a genuine carrier
solution, with all window evaluations identified on one event. -/
theorem solution_in_carrier (T : ℝ≥0) (N : ℕ)
    (Z : ℝ≥0 → Ω → E) (ha : StronglyAdapted F Z)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => Z t ω))
    (hz : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N Z) :
    ∃ X : State (E := E) (μ := μ) F T,
      Equation (μ := μ) F T B hB hBmeas ell g b x₀ N (realize F T X) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, realize F T X t ω = Z t ω) := by
  obtain ⟨Y, hYa, hYc, hYZ⟩ := exists_continuous_adapted_modification F hnull Z ha hc
  have hyz : ∀ᵐ ω ∂μ, ∀ t ≤ T, Y t ω = Z t ω := hYZ.mono fun _ h t _ => h t
  have hR := sdeRhs_congr F T B hB hBmeas hnull ell g b x₀ N Y Z hyz
  have hYEq : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N Y := by
    filter_upwards [hyz, hz, hR] with ω hy hz hr
    exact fun t ht => (hy t ht).trans ((hz t ht).trans (hr t ht).symm)
  have hm := solution_memLp F T B hB hBmeas ell g (fun i => (hLip i).continuous)
    K hK b hb C hC hbC x₀ N Y hYa hYc hYEq
  let X := ofProcess F T Y hYa hYc hm
  have hXY := ofProcess_realize F T Y hYa hYc hm
  have hRXY := sdeRhs_congr F T B hB hBmeas hnull ell g b x₀ N (realize F T X) Y hXY
  refine ⟨X, ?_, ?_⟩
  · filter_upwards [hXY, hYEq, hRXY] with ω hxy hy hr
    exact fun t ht => (hxy t ht).trans ((hy t ht).trans (hr t ht).symm)
  · filter_upwards [hXY, hyz] with ω hxy hyz
    exact fun t ht => (hxy t ht).trans (hyz t ht)

/-- Pathwise uniqueness for all adapted a.s. continuous solutions, without
carrying a moment hypothesis. The moment and carrier embedding are produced. -/
theorem pathwise_unique (T : ℝ≥0) (N : ℕ) (hN : 1 ≤ N)
    (Z W : ℝ≥0 → Ω → E) (hZa : StronglyAdapted F Z) (hWa : StronglyAdapted F W)
    (hZc : ∀ᵐ ω ∂μ, Continuous (fun t => Z t ω))
    (hWc : ∀ᵐ ω ∂μ, Continuous (fun t => W t ω))
    (hZ : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N Z)
    (hW : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N W) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, Z t ω = W t ω := by
  obtain ⟨X, hx, hXZ⟩ := solution_in_carrier F B hB hBmeas hnull ell g L hLip K hK
    b Lb hb C hC hbC x₀ T N Z hZa hZc hZ
  obtain ⟨Y, hy, hYW⟩ := solution_in_carrier F B hB hBmeas hnull ell g L hLip K hK
    b Lb hb C hC hbC x₀ T N W hWa hWc hW
  have hxy := carrier_unique F B hB hBmeas hnull ell g L hLip K hK
    b Lb hb C hC hbC x₀ T N hN X Y hx hy
  subst Y
  filter_upwards [hXZ, hYW] with ω hz hw
  exact fun t ht => (hz t ht).symm.trans (hw t ht)

/-- The equation on a large horizon restricts to the SAME equation with the
smaller completed integral domain. The input integrability is constructed. -/
theorem equation_restrict {t T : ℝ≥0} (ht : t ≤ T) (N : ℕ)
    (Z : ℝ≥0 → Ω → E) (ha : StronglyAdapted F Z)
    (hc : ∀ ω, Continuous (fun s => Z s ω))
    (hz : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N Z) :
    Equation (μ := μ) F t B hB hBmeas ell g b x₀ N Z := by
  have hi : ∀ i, ∀ᵐ ω ∂μ, ∀ s ≤ t,
      windowIto (μ := μ) F T (B i) (hB i) (hBmeas i) (fun u ω => g i (Z u ω)) s ω =
        windowIto (μ := μ) F t (B i) (hB i) (hBmeas i) (fun u ω => g i (Z u ω)) s ω := by
    intro i
    apply windowIto_restrict ht (hB i) (hBmeas i)
    exact integrandMemLp (μ := μ) T (hBmeas i) _
      (measurable_comp_sections (fun s => (ha s).measurable) (hLip i).continuous)
      (continuous_comp_paths hc (hLip i).continuous) (K i) (fun _ _ => hK i _)
  filter_upwards [hz, ae_all_iff.mpr hi] with ω hz hi
  intro s hs
  rw [hz s (hs.trans ht)]
  unfold StrongSDE.sdeRhs
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [hi i s hs]

/-- Finite-window uniqueness needs continuity only on that window. Freezing
at T supplies the all-time functions used by the integral-domain API. -/
theorem pathwise_unique_on_window (T : ℝ≥0) (N : ℕ) (hN : 1 ≤ N)
    (Z W : ℝ≥0 → Ω → E) (hZa : StronglyAdapted F Z) (hWa : StronglyAdapted F W)
    (hZc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Z t ω) (Icc 0 T))
    (hWc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => W t ω) (Icc 0 T))
    (hZ : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N Z)
    (hW : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N W) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, Z t ω = W t ω := by
  let Z' : ℝ≥0 → Ω → E := fun t ω => Z (min t T) ω
  let W' : ℝ≥0 → Ω → E := fun t ω => W (min t T) ω
  have hZa' : StronglyAdapted F Z' := fun t =>
    (hZa (min t T)).mono (F.mono (min_le_left _ _))
  have hWa' : StronglyAdapted F W' := fun t =>
    (hWa (min t T)).mono (F.mono (min_le_left _ _))
  have hZc' : ∀ᵐ ω ∂μ, Continuous (fun t => Z' t ω) := by
    filter_upwards [hZc] with ω hω
    exact hω.restrict.comp (cappedTime_continuous T)
  have hWc' : ∀ᵐ ω ∂μ, Continuous (fun t => W' t ω) := by
    filter_upwards [hWc] with ω hω
    exact hω.restrict.comp (cappedTime_continuous T)
  have hz : ∀ᵐ ω ∂μ, ∀ t ≤ T, Z' t ω = Z t ω :=
    ae_of_all _ fun ω t ht => congrArg (fun s => Z s ω) (min_eq_left ht)
  have hw : ∀ᵐ ω ∂μ, ∀ t ≤ T, W' t ω = W t ω :=
    ae_of_all _ fun ω t ht => congrArg (fun s => W s ω) (min_eq_left ht)
  have heZ : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N Z' := by
    filter_upwards [hz, hZ, sdeRhs_congr F T B hB hBmeas hnull ell g b x₀ N Z' Z hz]
      with ω hh he hr
    exact fun t ht => (hh t ht).trans ((he t ht).trans (hr t ht).symm)
  have heW : Equation (μ := μ) F T B hB hBmeas ell g b x₀ N W' := by
    filter_upwards [hw, hW, sdeRhs_congr F T B hB hBmeas hnull ell g b x₀ N W' W hw]
      with ω hh he hr
    exact fun t ht => (hh t ht).trans ((he t ht).trans (hr t ht).symm)
  have heq := pathwise_unique F B hB hBmeas hnull ell g L hLip K hK
    b Lb hb C hC hbC x₀ T N hN Z' W' hZa' hWa' hZc' hWc' heZ heW
  filter_upwards [hz, hw, heq] with ω hz hw heq
  exact fun t ht => (hz t ht).symm.trans ((heq t ht).trans (hw t ht))


/-- A process satisfying the equation on every integer horizon can be chosen
on the original probability space, with one common window-identification event. -/
theorem exists_all_integer_solutions (N : ℕ) (hN : 1 ≤ N) :
    ∃ Z : ℝ≥0 → Ω → E, StronglyAdapted F Z ∧
      (∀ ω, Continuous (fun t => Z t ω)) ∧
      (∀ n : ℕ, Equation (μ := μ) F (n : ℝ≥0) B hB hBmeas ell g b x₀ N Z) := by
  classical
  have hex : ∀ n : ℕ, ∃ X : State (E := E) (μ := μ) F (n : ℝ≥0),
      StronglyAdapted F (realize F (n : ℝ≥0) X) ∧
      (∀ ω, Continuous (fun t => realize F (n : ℝ≥0) X t ω)) ∧
      Integrable (fun ω => ⨆ t : StrongSDEConcreteMaps.Window (n : ℝ≥0),
        ‖realize F (n : ℝ≥0) X t.val ω‖ ^ 2) μ ∧
      Equation (μ := μ) F (n : ℝ≥0) B hB hBmeas ell g b x₀ N (realize F (n : ℝ≥0) X) :=
    fun n => exists_solution F B hB hBmeas hnull ell g L hLip K hK
      b Lb hb C hC hbC x₀ n N hN
  choose X hXa hXc hXm hXe using hex
  let P : ℕ → ℝ≥0 → Ω → E := fun n => realize F (n : ℝ≥0) (X n)
  have hcons : ∀ m n : ℕ, m ≤ n → ∀ᵐ ω ∂μ, ∀ t ≤ (m : ℝ≥0), P m t ω = P n t ω := by
    intro m n hmn
    have hrestrict := equation_restrict F B hB hBmeas hnull ell g L hLip K hK
      b Lb hb C hC hbC x₀ (by exact_mod_cast hmn : (m : ℝ≥0) ≤ (n : ℝ≥0))
      N (P n) (hXa n) (hXc n) (hXe n)
    exact pathwise_unique F B hB hBmeas hnull ell g L hLip K hK
      b Lb hb C hC hbC x₀ m N hN (P m) (P n) (hXa m) (hXa n)
      (ae_of_all _ (hXc m)) (ae_of_all _ (hXc n)) (hXe m) hrestrict
  obtain ⟨Z, hZa, hZc, hmatch⟩ := ConsistentHorizonProcess.exists_global_process
    F hnull P hXa (fun n => ae_of_all _ (hXc n)) hcons
  refine ⟨Z, hZa, hZc, ?_⟩
  intro n
  have hzpn : ∀ᵐ ω ∂μ, ∀ t ≤ (n : ℝ≥0), Z t ω = P n t ω :=
    hmatch.mono fun _ h => h n
  have hr := sdeRhs_congr F n B hB hBmeas hnull ell g b x₀ N Z (P n) hzpn
  filter_upwards [hzpn, hXe n, hr] with ω hp he hr
  exact fun t ht => (hp t ht).trans ((he t ht).trans (hr t ht).symm)

/-- The all-time equation restricts to every integer horizon using the actual
integral coherence theorem, with input membership supplied from boundedness. -/
theorem globalEquation_on_integer (N : ℕ) (Z : ℝ≥0 → Ω → E)
    (ha : StronglyAdapted F Z) (hc : ∀ᵐ ω ∂μ, Continuous (fun t => Z t ω))
    (hz : GlobalEquation (μ := μ) F B hB hBmeas ell g b x₀ N Z) (n : ℕ) :
    Equation (μ := μ) F (n : ℝ≥0) B hB hBmeas ell g b x₀ N Z := by
  have hi : ∀ i, ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ t ≤ (k : ℝ≥0),
      AllTimeIto.globalIto (μ := μ) F (B i) (hB i) (hBmeas i) (fun s ω => g i (Z s ω)) t ω =
        windowIto (μ := μ) F k (B i) (hB i) (hBmeas i) (fun s ω => g i (Z s ω)) t ω := by
    intro i
    apply AllTimeIto.globalIto_integer_agreement (μ := μ) F (B i) (hB i) (hBmeas i)
    intro k
    exact coefficient_memLp_of_ae_continuous F k (B i) (hBmeas i) hnull Z ha hc
      (g i) (hLip i).continuous (K i) (hK i)
  filter_upwards [hz, ae_all_iff.mpr hi] with ω hz hi
  intro t ht
  rw [hz t]
  unfold StrongSDE.sdeRhs
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [hi i n t ht]

/-- All-time strong existence, with compact moments and a single event for
all nonnegative times. The initial state is deterministic, the scale is N⁻¹/²,
and all integrals are against the supplied original drivers. -/
theorem exists_all_time_solution (N : ℕ) (hN : 1 ≤ N) :
    ∃ Z : ℝ≥0 → Ω → E, StronglyAdapted F Z ∧
      (∀ ω, Continuous (fun t => Z t ω)) ∧
      (∀ T : ℝ≥0, Integrable (fun ω => ⨆ t : StrongSDEConcreteMaps.Window T,
        ‖Z t.val ω‖ ^ 2) μ) ∧
      GlobalEquation (μ := μ) F B hB hBmeas ell g b x₀ N Z := by
  obtain ⟨Z, hZa, hZc, hZE⟩ := exists_all_integer_solutions F B hB hBmeas hnull
    ell g L hLip K hK b Lb hb C hC hbC x₀ N hN
  refine ⟨Z, hZa, hZc, ?_, ?_⟩
  · intro T
    let n := ConsistentHorizonProcess.horizon T
    have ht : T ≤ (n : ℝ≥0) := ConsistentHorizonProcess.le_horizon T
    have heq := equation_restrict F B hB hBmeas hnull ell g L hLip K hK
      b Lb hb C hC hbC x₀ ht N Z hZa hZc (hZE n)
    exact arbitrary_solution_supMoment F T B hB hBmeas hnull ell g
      (fun i => (hLip i).continuous) K hK b hb C hC hbC x₀ N Z hZa
      (ae_of_all _ hZc) heq
  · filter_upwards [ae_all_iff.mpr hZE] with ω hω
    intro t
    rw [hω (ConsistentHorizonProcess.horizon t) t (ConsistentHorizonProcess.le_horizon t)]
    unfold StrongSDE.sdeRhs
    congr 2

/-- All-time pathwise uniqueness for adapted a.s. continuous solutions.
A compact moment assumption is unnecessary because coefficients are bounded. -/
theorem all_time_pathwise_unique (N : ℕ) (hN : 1 ≤ N)
    (Z W : ℝ≥0 → Ω → E) (hZa : StronglyAdapted F Z) (hWa : StronglyAdapted F W)
    (hZc : ∀ᵐ ω ∂μ, Continuous (fun t => Z t ω))
    (hWc : ∀ᵐ ω ∂μ, Continuous (fun t => W t ω))
    (hZ : GlobalEquation (μ := μ) F B hB hBmeas ell g b x₀ N Z)
    (hW : GlobalEquation (μ := μ) F B hB hBmeas ell g b x₀ N W) :
    ∀ᵐ ω ∂μ, ∀ t, Z t ω = W t ω := by
  apply ConsistentHorizonProcess.indistinguishable_of_integer_windows
  intro n
  apply pathwise_unique F B hB hBmeas hnull ell g L hLip K hK
    b Lb hb C hC hbC x₀ n N hN Z W hZa hWa hZc hWc
  · exact globalEquation_on_integer F B hB hBmeas hnull ell g L hLip K hK
      b Lb hb C hC hbC x₀ N Z hZa hZc hZ n
  · exact globalEquation_on_integer F B hB hBmeas hnull ell g L hLip K hK
      b Lb hb C hC hbC x₀ N W hWa hWc hW n

end Coefficients
end Ripple.Stochastic.StrongSDEGlobal
