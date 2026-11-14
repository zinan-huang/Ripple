import Ripple.Stochastic.ContinuousItoStopping

/-!
# Increment isometry for the installed continuous Itô integral

Constant stopping turns slice evaluation into terminal integration of a stopped
integrand. Subtraction, terminal isometry, and the explicit indicator identity
then give deterministic and randomly stopped increment second moments.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.ContinuousItoStoppedIsometry
open FilteredItoIntegralL2 FilteredItoIntegralCLM FilteredItoIntegralProcessGeneral
open ContinuousItoElementary ContinuousItoConsistency AdaptedContinuousSpace
open ContinuousItoStoppingGrid ContinuousItoStopping StoppedPredictableIntegrand

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- An installed predictable integrand stopped at a deterministic time. -/
def deterministicStoppedIntegrand (T s : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  stoppedIntegrand T hBmeas (isStoppingTime_const F s) φ

/-- Evaluation at a deterministic time is terminal integration of the
explicitly stopped predictable integrand. -/
theorem terminal_deterministic_stop (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {s : ℝ≥0} (hsT : s ≤ T)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    itoProcessCLM (𝓖 := F) (μ := μ) T T hBmeas
        (deterministicStoppedIntegrand T s hBmeas φ) =
      itoProcessCLM (𝓖 := F) (μ := μ) T s hBmeas φ := by
  apply Lp.ext
  have hstop := continuousIto_stopped_bounded T hB hBmeas
    (τ := fun _ : Ω => s) (isStoppingTime_const F s)
    (fun _ => hsT) φ
  have hleft := representative_eval_ae T hB hBmeas
    (deterministicStoppedIntegrand T s hBmeas φ) ⟨T, zero_le, le_rfl⟩
  have hright := representative_eval_ae T hB hBmeas φ ⟨s, zero_le, hsT⟩
  filter_upwards [hstop, hleft, hright] with ω hstopω hl hr
  have he : representative (continuousIto T hB hBmeas
      (deterministicStoppedIntegrand T s hBmeas φ)) ω ⟨T, zero_le, le_rfl⟩ =
      representative (continuousIto T hB hBmeas φ) ω ⟨s, zero_le, hsT⟩ := by
    simpa only [deterministicStoppedIntegrand, stoppedWindowTime, min_eq_right hsT]
      using hstopω ⟨T, zero_le, le_rfl⟩
  exact hl.symm.trans (he.trans hr)


/-- The predictable integrand corresponding to the increment from s to t. -/
def incrementIntegrand (T s t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
  deterministicStoppedIntegrand T t hBmeas φ -
    deterministicStoppedIntegrand T s hBmeas φ

/-- Subtraction of deterministic stopping indicators gives the interval (s,t]. -/
theorem stopping_indicator_sub {s t : ℝ≥0} (hst : s ≤ t)
    (f : ℝ≥0 × Ω → ℝ) (z : ℝ≥0 × Ω) :
    (stoppingRegion (fun _ : Ω => (t : WithTop ℝ≥0))).indicator f z -
        (stoppingRegion (fun _ : Ω => (s : WithTop ℝ≥0))).indicator f z =
      (Set.Ioc s t ×ˢ (Set.univ : Set Ω)).indicator f z := by
  by_cases hzs : z.1 ≤ s
  · have hzt : z.1 ≤ t := hzs.trans hst
    have hnot : z ∉ Set.Ioc s t ×ˢ (Set.univ : Set Ω) :=
      fun h => (not_lt_of_ge hzs) h.1.1
    simp only [Set.indicator_of_notMem hnot, stoppingRegion, Set.indicator_apply,
      Set.mem_setOf_eq, WithTop.coe_le_coe, hzs, hzt, and_true, sub_self]
  · have hsz : s < z.1 := lt_of_not_ge hzs
    have hzpos : 0 < z.1 := lt_of_le_of_lt zero_le hsz
    by_cases hzt : z.1 ≤ t
    · have h1 : z ∈ stoppingRegion (fun _ : Ω => (t : WithTop ℝ≥0)) :=
        ⟨hzpos, WithTop.coe_le_coe.2 hzt⟩
      have h2 : z ∉ stoppingRegion (fun _ : Ω => (s : WithTop ℝ≥0)) := fun h =>
        hzs (WithTop.coe_le_coe.1 h.2)
      have h3 : z ∈ Set.Ioc s t ×ˢ (Set.univ : Set Ω) := ⟨⟨hsz, hzt⟩, Set.mem_univ _⟩
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Set.indicator_of_mem h3, sub_zero]
    · have h1 : z ∉ stoppingRegion (fun _ : Ω => (t : WithTop ℝ≥0)) := fun h =>
        hzt (WithTop.coe_le_coe.1 h.2)
      have h2 : z ∉ stoppingRegion (fun _ : Ω => (s : WithTop ℝ≥0)) := fun h =>
        hzs (WithTop.coe_le_coe.1 h.2)
      have h3 : z ∉ Set.Ioc s t ×ˢ (Set.univ : Set Ω) := fun h => hzt h.1.2
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, Set.indicator_of_notMem h3,
        sub_self]

/-- The increment integrand represents exactly the raw interval restriction. -/
theorem incrementIntegrand_coeFn (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    {s t : ℝ≥0} (hst : s ≤ t)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    (incrementIntegrand T s t hBmeas φ : ℝ≥0 × Ω → ℝ) =ᵐ[
      trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas]
      (Set.Ioc s t ×ˢ (Set.univ : Set Ω)).indicator φ := by
  filter_upwards [Lp.coeFn_sub
    (deterministicStoppedIntegrand T t hBmeas φ)
    (deterministicStoppedIntegrand T s hBmeas φ),
    stoppedIntegrand_coeFn T hBmeas (isStoppingTime_const F t) φ,
    stoppedIntegrand_coeFn T hBmeas (isStoppingTime_const F s) φ]
      with z hd ht hs
  change ((deterministicStoppedIntegrand T t hBmeas φ -
    deterministicStoppedIntegrand T s hBmeas φ :
      Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z = _
  rw [hd, Pi.sub_apply]
  show (stoppedIntegrand (μ := μ) T hBmeas (isStoppingTime_const F t) φ : ℝ≥0 × Ω → ℝ) z -
    (stoppedIntegrand (μ := μ) T hBmeas (isStoppingTime_const F s) φ : ℝ≥0 × Ω → ℝ) z = _
  rw [ht, hs]
  exact stopping_indicator_sub hst _ z

/-- The time-slice increment is terminal integration of its produced integrand. -/
theorem itoProcessCLM_increment (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    {s t : ℝ≥0} (hsT : s ≤ T) (htT : t ≤ T)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    itoProcessCLM (𝓖 := F) (μ := μ) T t hBmeas φ -
        itoProcessCLM (𝓖 := F) (μ := μ) T s hBmeas φ =
      itoProcessCLM (𝓖 := F) (μ := μ) T T hBmeas
        (incrementIntegrand T s t hBmeas φ) := by
  rw [incrementIntegrand, map_sub, terminal_deterministic_stop T hB hBmeas htT,
    terminal_deterministic_stop T hB hBmeas hsT]

/-- Deterministic increment Itô isometry in the installed L² spaces. -/
theorem itoProcessCLM_increment_norm_sq (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    ‖itoProcessCLM (𝓖 := F) (μ := μ) T t hBmeas φ -
        itoProcessCLM (𝓖 := F) (μ := μ) T s hBmeas φ‖ ^ 2 =
      ∫ z in Set.Ioc s t ×ˢ (Set.univ : Set Ω), (φ z) ^ 2
        ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  rw [itoProcessCLM_increment T hB hBmeas (hst.trans htT) htT,
    itoProcessCLM_norm_terminal, lp_two_norm_sq,
    ← integral_indicator (measurableSet_predictable_Ioc_prod (𝓕 := F) s t MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards [incrementIntegrand_coeFn T hBmeas hst φ] with z hz
  rw [hz]
  by_cases hmem : z ∈ Set.Ioc s t ×ˢ (Set.univ : Set Ω)
  · simp only [Set.indicator_of_mem hmem]
  · simp only [Set.indicator_of_notMem hmem, zero_pow (by decide : 2 ≠ 0)]

/-- Deterministic increment second moments for the actual installed continuous
representative, rather than merely for its L² class. -/
theorem continuousIto_increment_moment (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (s t : Set.Icc (0 : ℝ≥0) T) (hst : s ≤ t) :
    (∫ ω, (representative (continuousIto T hB hBmeas φ) ω t -
        representative (continuousIto T hB hBmeas φ) ω s) ^ 2 ∂μ) =
      ∫ z in Set.Ioc s.val t.val ×ˢ (Set.univ : Set Ω), (φ z) ^ 2
        ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  rw [← itoProcessCLM_increment_norm_sq T hB hBmeas hst t.property.2 φ,
    lp_two_norm_sq]
  apply integral_congr_ae
  filter_upwards [representative_eval_ae T hB hBmeas φ s,
    representative_eval_ae T hB hBmeas φ t,
    Lp.coeFn_sub (itoProcessCLM (𝓖 := F) (μ := μ) T t.val hBmeas φ)
      (itoProcessCLM (𝓖 := F) (μ := μ) T s.val hBmeas φ)] with ω hs ht hd
  rw [hd, Pi.sub_apply, hs, ht]

/-- Randomly stopped increment second moments. The stopping identity is
instantiated with the actual stopped integrand, and its second moment is then
computed by deterministic increment isometry. -/
theorem continuousIto_stopped_increment_moment (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hbound : ∀ ω, τ ω ≤ T)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (s t : Set.Icc (0 : ℝ≥0) T) (hst : s ≤ t) :
    (∫ ω, (representative (continuousIto T hB hBmeas φ) ω (stoppedWindowTime T τ ω t) -
        representative (continuousIto T hB hBmeas φ) ω (stoppedWindowTime T τ ω s)) ^ 2 ∂μ) =
      ∫ z in Set.Ioc s.val t.val ×ˢ (Set.univ : Set Ω),
        ((stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0))).indicator φ z) ^ 2
          ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  calc
    _ = ∫ ω, (representative (continuousIto T hB hBmeas
          (stoppedIntegrand T hBmeas hτ φ)) ω t -
        representative (continuousIto T hB hBmeas
          (stoppedIntegrand T hBmeas hτ φ)) ω s) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [continuousIto_stopped_bounded T hB hBmeas hτ hbound φ] with ω hω
      rw [hω t, hω s]
    _ = ∫ z in Set.Ioc s.val t.val ×ˢ (Set.univ : Set Ω),
        (stoppedIntegrand T hBmeas hτ φ z) ^ 2
          ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
      continuousIto_increment_moment T hB hBmeas (stoppedIntegrand T hBmeas hτ φ) s t hst
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (stoppedIntegrand_coeFn T hBmeas hτ φ)] with z hz
      rw [hz]

/-- The intersection of a deterministic increment band and a stopping band
is the pathwise interval with both endpoints capped at the stopping time. -/
theorem stoppedBand_membership {s t a u : ℝ≥0} :
    (s < u ∧ u ≤ t ∧ 0 < u ∧ u ≤ a) ↔
      u ∈ Set.Ioc (min s a) (min t a) := by
  constructor
  · rintro ⟨hsu, hut, _, hua⟩
    exact ⟨lt_of_le_of_lt (min_le_left s a) hsu, le_min hut hua⟩
  · rintro ⟨hlo, hhi⟩
    have hua : u ≤ a := (le_min_iff.mp hhi).2
    have hsu : s < u := by
      rcases lt_or_ge s u with h | h
      · exact h
      · exact ((not_lt_of_ge (le_min h hua)) hlo).elim
    exact ⟨hsu, (le_min_iff.mp hhi).1,
      lt_of_le_of_lt zero_le hsu, hua⟩

/-- The squared stopped integrand on a deterministic band is precisely the
raw squared integrand on the corresponding randomly capped interval. -/
theorem stoppedBand_indicator (s t : ℝ≥0) (τ : Ω → ℝ≥0)
    (H : ℝ≥0 × Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    (Set.Ioc s t ×ˢ (Set.univ : Set Ω)).indicator
        (fun z => ((stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0))).indicator H z) ^ 2)
        (u, ω) =
      (Set.Ioc (min s (τ ω)) (min t (τ ω))).indicator
        (fun v => (H (v, ω)) ^ 2) u := by
  have hm : u ∈ Set.Ioc (min s (τ ω)) (min t (τ ω)) ↔
      (u, ω) ∈ Set.Ioc s t ×ˢ (Set.univ : Set Ω) ∧
      (u, ω) ∈ stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0)) := by
    simpa only [Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true,
      stoppingRegion, Set.mem_setOf_eq, WithTop.coe_le_coe, and_assoc]
      using (stoppedBand_membership (s := s) (t := t) (a := τ ω) (u := u)).symm
  by_cases hb : (u, ω) ∈ Set.Ioc s t ×ˢ (Set.univ : Set Ω)
  · by_cases hstop : (u, ω) ∈ stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0))
    · simp only [Set.indicator_of_mem hb, Set.indicator_of_mem hstop,
        Set.indicator_of_mem (hm.mpr ⟨hb, hstop⟩)]
    · have hout : u ∉ Set.Ioc (min s (τ ω)) (min t (τ ω)) :=
        fun h => hstop (hm.mp h).2
      simp only [Set.indicator_of_mem hb, Set.indicator_of_notMem hstop,
        Set.indicator_of_notMem hout, zero_pow (by decide : 2 ≠ 0)]
  · have hout : u ∉ Set.Ioc (min s (τ ω)) (min t (τ ω)) :=
      fun h => hb (hm.mp h).1
    simp only [Set.indicator_of_notMem hb, Set.indicator_of_notMem hout]

/-- Fubini turns the actual predictable product-space energy into the expected
pathwise time integral. Predictable measurability and L² membership are the only
analytic input about H; there is no energy identity hypothesis. -/
theorem stopped_energy_fubini (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0 × Ω → ℝ) (hHsm : StronglyMeasurable[F.predictable] H)
    (hH : MemLp H 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    {s t : ℝ≥0} (htT : t ≤ T) :
    (∫ z in Set.Ioc s t ×ˢ (Set.univ : Set Ω),
      ((stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0))).indicator H z) ^ 2
        ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) =
      ∫ ω, (∫ u in Set.Ioc (min s (τ ω)) (min t (τ ω)),
        (H (u, ω)) ^ 2 ∂timeMeasure) ∂μ := by
  let f : ℝ≥0 × Ω → ℝ := (Set.Ioc s t ×ˢ (Set.univ : Set Ω)).indicator
    (fun z => ((stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0))).indicator H z) ^ 2)
  have hband : MeasurableSet[F.predictable] (Set.Ioc s t ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod (𝓕 := F) s t MeasurableSet.univ
  have hstop := measurableSet_stoppingRegion hτ
  have hsm : StronglyMeasurable[F.predictable] f :=
    ((hHsm.indicator hstop).pow 2).indicator hband
  have hint : Integrable f (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) :=
    ((hH.indicator hstop).integrable_sq).indicator hband
  have hprod : Integrable f ((timeMeasure_T T).prod μ) :=
    integrable_of_integrable_trim F.predictable_le_prod hint
  rw [← integral_indicator hband]
  change (∫ z, f z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) = _
  rw [show trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas =
      ((timeMeasure_T T).prod μ).trim F.predictable_le_prod from rfl,
    ← integral_trim F.predictable_le_prod hsm,
    integral_prod_symm f hprod]
  apply integral_congr_ae
  filter_upwards with ω
  have hpoint : (fun u => f (u, ω)) =
      (Set.Ioc (min s (τ ω)) (min t (τ ω))).indicator
        (fun u => (H (u, ω)) ^ 2) := by
    funext u
    exact stoppedBand_indicator s t τ H u ω
  rw [hpoint, integral_indicator measurableSet_Ioc, timeMeasure_T,
    Measure.restrict_restrict_of_subset]
  exact fun u hu => ⟨lt_of_le_of_lt zero_le hu.1,
    hu.2.trans ((min_le_left _ _).trans htT)⟩

/-- The stopped increment law in the pathwise energy form needed for clock
bounds. The integral process is the installed continuous integral of hH.toLp H. -/
theorem continuousIto_stopped_increment_raw_moment (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ u, Measurable (B u))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hbound : ∀ ω, τ ω ≤ T)
    (H : ℝ≥0 × Ω → ℝ) (hHsm : StronglyMeasurable[F.predictable] H)
    (hH : MemLp H 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (s t : Set.Icc (0 : ℝ≥0) T) (hst : s ≤ t) :
    (∫ ω, (representative (continuousIto T hB hBmeas (hH.toLp H)) ω
        (stoppedWindowTime T τ ω t) -
      representative (continuousIto T hB hBmeas (hH.toLp H)) ω
        (stoppedWindowTime T τ ω s)) ^ 2 ∂μ) =
      ∫ ω, (∫ u in Set.Ioc (min s.val (τ ω)) (min t.val (τ ω)),
        (H (u, ω)) ^ 2 ∂timeMeasure) ∂μ := by
  rw [continuousIto_stopped_increment_moment T hB hBmeas hτ hbound
    (hH.toLp H) s t hst]
  calc
    _ = ∫ z in Set.Ioc s.val t.val ×ˢ (Set.univ : Set Ω),
        ((stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0))).indicator H z) ^ 2
          ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hH.coeFn_toLp] with z hz
      by_cases hmem : z ∈ stoppingRegion (fun ω => (τ ω : WithTop ℝ≥0))
      · simp only [Set.indicator_of_mem hmem, hz]
      · simp only [Set.indicator_of_notMem hmem]
    _ = _ := stopped_energy_fubini T hBmeas hτ H hHsm hH t.property.2

end Ripple.Stochastic.ContinuousItoStoppedIsometry
