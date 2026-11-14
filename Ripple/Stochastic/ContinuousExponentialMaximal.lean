import Ripple.Stochastic.DoobContinuous
import Ripple.Stochastic.ExponentialMaximal

/-!
# Continuous maximal bounds from the finite-grid Ville inequality

Dyadic finite grids first give a countable crossing bound. A continuous path
that reaches level a crosses every smaller positive level on a grid. Taking
those smaller levels up to a retains the non-strict crossing event, including
paths whose maximum is exactly a. The exponential constructor remains a
separate theorem; this module supplies the passage from that process to tails.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace Ripple.Stochastic.ContinuousExponentialMaximal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsFiniteMeasure P]

/-- Sampling preserves all three fields of a supermartingale. -/
theorem supermartingale_compMono {ι ι' : Type*} [Preorder ι] [Preorder ι']
    {F : Filtration ι' mΩ} {Z : ι' → Ω → ℝ}
    (hZ : Supermartingale Z F P) (τ : ι → ι') (hτ : Monotone τ) :
    Supermartingale (fun i => Z (τ i)) (Doob.Filtration.compMono mΩ F τ hτ) P :=
  ⟨fun i => hZ.stronglyAdapted (τ i),
    fun i j hij => hZ.2.1 (τ i) (τ j) (hτ hij), fun i => hZ.integrable (τ i)⟩

/-- The union of finite dyadic crossings satisfies Ville's sharp bound. -/
theorem dyadic_crossing_measure_le
    {F : Filtration ℝ mΩ} {Z : ℝ → Ω → ℝ}
    (hZ : Supermartingale Z F P) (hnonneg : ∀ t ω, 0 ≤ Z t ω)
    {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a) :
    P {ω | ∃ n : ℕ, ∃ k ≤ 2 ^ n, a ≤ Z (Doob.dyadicTime T n k) ω} ≤
      ENNReal.ofReal ((∫ ω, Z 0 ω ∂P) / a) := by
  let E : ℕ → Set Ω := fun n => {ω | ∃ k ≤ 2 ^ n, a ≤ Z (Doob.dyadicTime T n k) ω}
  have hmono : Monotone E := by
    apply monotone_nat_of_le_succ
    intro n ω hω
    obtain ⟨k, hk, hval⟩ := hω
    refine ⟨2 * k, ?_, ?_⟩
    · rw [pow_succ]
      omega
    · simpa only [Doob.dyadicTime_succ_two_mul] using hval
  have hset : {ω | ∃ n : ℕ, ∃ k ≤ 2 ^ n, a ≤ Z (Doob.dyadicTime T n k) ω} =
      ⋃ n, E n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
  rw [hset, hmono.measure_iUnion]
  apply iSup_le
  intro n
  have hsamp := supermartingale_compMono hZ (Doob.dyadicTime T n)
    (Doob.dyadicTime_monotone hT n)
  have h := SupermartingaleMaximal.finite_maximal_measure_le hsamp
    (fun k ω => hnonneg _ ω) ha (2 ^ n)
  simpa [E, Doob.dyadicTime, min_eq_left hT] using h

/-- A crossing at level a is controlled at every strictly smaller positive level. -/
theorem continuous_crossing_measure_le_of_lt
    {F : Filtration ℝ mΩ} {Z : ℝ → Ω → ℝ}
    (hZ : Supermartingale Z F P) (hnonneg : ∀ t ω, 0 ≤ Z t ω)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => Z t ω))
    {T a b : ℝ} (hT : 0 ≤ T) (hb : 0 < b) (hba : b < a) :
    P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, a ≤ Z t ω} ≤
      ENNReal.ofReal ((∫ ω, Z 0 ω ∂P) / b) := by
  apply le_trans ?_ (dyadic_crossing_measure_le hZ hnonneg hT hb)
  apply measure_mono_ae
  filter_upwards [hcont] with ω hω
  rintro ⟨t, ht, hval⟩
  rcases eq_or_lt_of_le hT with hzero | hpos
  · have htzero : t = 0 := le_antisymm (hzero ▸ ht.2) ht.1
    refine ⟨0, 0, by norm_num, ?_⟩
    simpa [Doob.dyadicTime, ← hzero, htzero] using hba.le.trans hval
  · have htend : Tendsto (fun n => Z (Doob.dyadicTime T n (Doob.dyadicIndex T t n)) ω)
        atTop (nhds (Z t ω)) :=
      hω.continuousAt.tendsto.comp
        ((Doob.tendsto_dyadicTime_dyadicIndex hpos ht.1 ht.2).mono_right nhdsWithin_le_nhds)
    obtain ⟨n, hn⟩ := (htend.eventually (Ioi_mem_nhds (hba.trans_le hval))).exists
    exact ⟨n, Doob.dyadicIndex T t n, Doob.dyadicIndex_le hpos ht.2 n, hn.le⟩

/-- Continuous nonnegative supermartingales satisfy the sharp non-strict crossing bound. -/
theorem continuous_maximal_measure_le
    {F : Filtration ℝ mΩ} {Z : ℝ → Ω → ℝ}
    (hZ : Supermartingale Z F P) (hnonneg : ∀ t ω, 0 ≤ Z t ω)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => Z t ω))
    {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a) :
    P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, a ≤ Z t ω} ≤
      ENNReal.ofReal ((∫ ω, Z 0 ω ∂P) / a) := by
  let b : ℕ → ℝ := fun n => a * (1 - ((1 : ℝ) / 2) ^ (n + 1))
  have hbpos (n : ℕ) : 0 < b n := by
    have hp : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hpnonneg : 0 ≤ ((1 : ℝ) / 2) ^ n := by positivity
    dsimp [b]
    rw [pow_succ]
    apply mul_pos ha
    linarith
  have hblt (n : ℕ) : b n < a := by
    have hp : 0 < ((1 : ℝ) / 2) ^ (n + 1) := by positivity
    dsimp [b]
    nlinarith
  have hpzero : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsucczero : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1)) atTop (nhds 0) := by
    simpa only [pow_succ, zero_mul] using hpzero.mul_const ((1 : ℝ) / 2)
  have hbtend : Tendsto b atTop (nhds a) := by
    simpa [b] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hsucczero) :
        Tendsto (fun n : ℕ => a * (1 - ((1 : ℝ) / 2) ^ (n + 1)))
          atTop (nhds (a * (1 - 0))))
  have hlim : Tendsto (fun n => ENNReal.ofReal ((∫ ω, Z 0 ω ∂P) / b n))
      atTop (nhds (ENNReal.ofReal ((∫ ω, Z 0 ω ∂P) / a))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.div hbtend ha.ne')
  exact ge_of_tendsto' hlim fun n =>
    continuous_crossing_measure_le_of_lt hZ hnonneg hcont hT (hbpos n) (hblt n)

/-- The time axis of the stochastic integral is nonnegative real. -/
theorem nnreal_continuous_maximal_measure_le
    {F : Filtration ℝ≥0 mΩ} {Z : ℝ≥0 → Ω → ℝ}
    (hZ : Supermartingale Z F P) (hnonneg : ∀ t ω, 0 ≤ Z t ω)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => Z t ω))
    (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ t ≤ T, a ≤ Z t ω} ≤ ENNReal.ofReal ((∫ ω, Z 0 ω ∂P) / a) := by
  have hmono : Monotone Real.toNNReal := fun _ _ hab => Real.toNNReal_le_toNNReal hab
  have hext := supermartingale_compMono hZ Real.toNNReal hmono
  have hextcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => Z t.toNNReal ω) := by
    filter_upwards [hcont] with ω hω
    exact hω.comp continuous_real_toNNReal
  have hbound := continuous_maximal_measure_le hext (fun t ω => hnonneg _ ω)
    hextcont T.coe_nonneg ha
  have hsub : {ω | ∃ t ≤ T, a ≤ Z t ω} ⊆
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) (T : ℝ), a ≤ Z t.toNNReal ω} := by
    rintro ω ⟨t, ht, hv⟩
    refine ⟨(t : ℝ), ⟨t.coe_nonneg, by exact_mod_cast ht⟩, ?_⟩
    simpa using hv
  exact (measure_mono hsub).trans (by simpa using hbound)

/-- The exact earlier crossing-event specification, once its exponential process is produced. -/
theorem continuous_exponential_maximal
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (M Q : ℝ≥0 → Ω → ℝ)
    (hMzero : ∀ ω, M 0 ω = 0) (hQzero : ∀ ω, Q 0 ω = 0)
    (hQmono : ∀ ω, Monotone (fun t => Q t ω))
    (hMcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => M t ω))
    (hQcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => Q t ω))
    (T : ℝ≥0) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q)
    (hZ : Supermartingale (ExponentialMaximal.stochasticExponential M Q (r / q)) F P) :
    P (ExponentialMaximal.crossingEvent M Q T r q) ≤
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  let lam : ℝ := r / q
  let a : ℝ := Real.exp (lam * r - lam ^ 2 * q / 2)
  have hlam : 0 ≤ lam := div_nonneg hr hq.le
  have ha : 0 < a := Real.exp_pos _
  have hZcont : ∀ᵐ ω ∂P, Continuous
      (fun t : ℝ≥0 => ExponentialMaximal.stochasticExponential M Q lam t ω) := by
    filter_upwards [hMcont, hQcont] with ω hm hq
    simp only [ExponentialMaximal.stochasticExponential]
    fun_prop
  have hmax := nnreal_continuous_maximal_measure_le hZ
    (fun t ω => (Real.exp_pos _).le) hZcont T ha
  have hinit : (∫ ω, ExponentialMaximal.stochasticExponential M Q lam 0 ω ∂P) = 1 := by
    simp [ExponentialMaximal.stochasticExponential, hMzero, hQzero]
  have hopt : 1 / a = Real.exp (-r ^ 2 / (2 * q)) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    exact ExponentialMaximal.optimized_exponent r hq
  rw [hinit, hopt] at hmax
  exact (measure_mono (ExponentialMaximal.crossingEvent_subset M Q hQmono T r q hlam)).trans hmax

/-- The same bound for representatives whose zero values and bracket
monotonicity hold outside one null event. This matches quotient-valued integrals. -/
theorem continuous_exponential_maximal_ae
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
    (M Q : ℝ≥0 → Ω → ℝ)
    (hMzero : ∀ᵐ ω ∂P, M 0 ω = 0) (hQzero : ∀ᵐ ω ∂P, Q 0 ω = 0)
    (hQmono : ∀ᵐ ω ∂P, Monotone (fun t => Q t ω))
    (hMcont : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hQcont : ∀ᵐ ω ∂P, Continuous (fun t => Q t ω))
    (T : ℝ≥0) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q)
    (hZ : Supermartingale (ExponentialMaximal.stochasticExponential M Q (r / q)) F P) :
    P (ExponentialMaximal.crossingEvent M Q T r q) ≤
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  let lam : ℝ := r / q
  let a : ℝ := Real.exp (lam * r - lam ^ 2 * q / 2)
  have hlam : 0 ≤ lam := div_nonneg hr hq.le
  have hZcont : ∀ᵐ ω ∂P, Continuous
      (fun t => ExponentialMaximal.stochasticExponential M Q lam t ω) := by
    filter_upwards [hMcont, hQcont] with ω hm hq
    simp only [ExponentialMaximal.stochasticExponential]
    fun_prop
  have hmax := nnreal_continuous_maximal_measure_le hZ
    (fun t ω => (Real.exp_pos _).le) hZcont T (Real.exp_pos (lam * r - lam ^ 2 * q / 2))
  have hinit : (∫ ω, ExponentialMaximal.stochasticExponential M Q lam 0 ω ∂P) = 1 := by
    calc
      (∫ ω, ExponentialMaximal.stochasticExponential M Q lam 0 ω ∂P) =
          ∫ _ : Ω, (1 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hMzero, hQzero] with ω hm hq
        simp [ExponentialMaximal.stochasticExponential, hm, hq]
      _ = 1 := by simp
  have hopt : 1 / a = Real.exp (-r ^ 2 / (2 * q)) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    exact ExponentialMaximal.optimized_exponent r hq
  change P {ω | ∃ t ≤ T, a ≤ ExponentialMaximal.stochasticExponential M Q lam t ω} ≤ _ at hmax
  rw [hinit, hopt] at hmax
  apply le_trans ?_ hmax
  apply measure_mono_ae
  filter_upwards [hQmono] with ω hmono
  rintro ⟨⟨t, ht, hMr⟩, hQt⟩
  exact ⟨t, ht, ExponentialMaximal.exp_threshold_le hlam hMr ((hmono ht).trans hQt)⟩

/-- A compact-window process needs no all-time extension hypothesis. Freezing
at the terminal time produces the extension used by the NNReal theorem. -/
theorem compact_continuous_maximal_measure_le
    (T : ℝ≥0) {F : Filtration (Set.Icc (0 : ℝ≥0) T) mΩ}
    {Z : Set.Icc (0 : ℝ≥0) T → Ω → ℝ}
    (hZ : Supermartingale Z F P) (hnonneg : ∀ t ω, 0 ≤ Z t ω)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω))
    {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ t, a ≤ Z t ω} ≤
      ENNReal.ofReal ((∫ ω, Z ⟨0, zero_le, zero_le⟩ ω ∂P) / a) := by
  let stop : ℝ≥0 → Set.Icc (0 : ℝ≥0) T :=
    fun t => ⟨min t T, zero_le, min_le_right _ _⟩
  have hmono : Monotone stop := fun _ _ h => min_le_min_right T h
  have hcstop : Continuous stop :=
    (continuous_id.min continuous_const).subtype_mk _
  have hm := supermartingale_compMono hZ stop hmono
  have hc : ∀ᵐ ω ∂P, Continuous (fun t => Z (stop t) ω) := by
    filter_upwards [hcont] with ω hω
    exact hω.comp hcstop
  have hbound := nnreal_continuous_maximal_measure_le hm
    (fun t ω => hnonneg _ ω) hc T ha
  have hsub : {ω | ∃ t, a ≤ Z t ω} ⊆
      {ω | ∃ t ≤ T, a ≤ Z (stop t) ω} := by
    rintro ω ⟨t, ht⟩
    refine ⟨t.val, t.property.2, ?_⟩
    have heq : stop t.val = t := Subtype.ext (min_eq_left t.property.2)
    simpa only [heq] using ht
  exact (measure_mono hsub).trans (by simpa [stop] using hbound)

/-- Exact exponential tail for a compact-window continuous integral and its
bracket. The measurable bracket may agree with the time integral only a.e. -/
theorem compact_exponential_maximal_ae
    [IsProbabilityMeasure P] (T : ℝ≥0)
    {F : Filtration (Set.Icc (0 : ℝ≥0) T) mΩ}
    (M Q : Set.Icc (0 : ℝ≥0) T → Ω → ℝ)
    (hMzero : ∀ᵐ ω ∂P, M ⟨0, zero_le, zero_le⟩ ω = 0)
    (hQzero : ∀ᵐ ω ∂P, Q ⟨0, zero_le, zero_le⟩ ω = 0)
    (hQmono : ∀ᵐ ω ∂P, Monotone (fun t => Q t ω))
    (hMcont : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hQcont : ∀ᵐ ω ∂P, Continuous (fun t => Q t ω))
    {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q)
    (hZ : Supermartingale
      (fun t ω => Real.exp ((r / q) * M t ω - (r / q) ^ 2 * Q t ω / 2)) F P) :
    P {ω | (∃ t, r ≤ M t ω) ∧ Q ⟨T, zero_le, le_rfl⟩ ω ≤ q} ≤
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  let lam : ℝ := r / q
  let a : ℝ := Real.exp (lam * r - lam ^ 2 * q / 2)
  have hlam : 0 ≤ lam := div_nonneg hr hq.le
  have hcont : ∀ᵐ ω ∂P, Continuous
      (fun t => Real.exp (lam * M t ω - lam ^ 2 * Q t ω / 2)) := by
    filter_upwards [hMcont, hQcont] with ω hm hq
    fun_prop
  have hmax := compact_continuous_maximal_measure_le T hZ
    (fun t ω => (Real.exp_pos _).le) hcont (Real.exp_pos (lam * r - lam ^ 2 * q / 2))
  have hinit : (∫ ω, Real.exp (lam * M ⟨0, zero_le, zero_le⟩ ω -
      lam ^ 2 * Q ⟨0, zero_le, zero_le⟩ ω / 2) ∂P) = 1 := by
    calc
      _ = ∫ _ : Ω, (1 : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hMzero, hQzero] with ω hm hq
        simp [hm, hq]
      _ = 1 := by simp
  have hopt : 1 / a = Real.exp (-r ^ 2 / (2 * q)) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    exact ExponentialMaximal.optimized_exponent r hq
  change P {ω | ∃ t, a ≤ Real.exp (lam * M t ω - lam ^ 2 * Q t ω / 2)} ≤
    ENNReal.ofReal ((∫ ω, Real.exp (lam * M ⟨0, zero_le, zero_le⟩ ω -
      lam ^ 2 * Q ⟨0, zero_le, zero_le⟩ ω / 2) ∂P) / a) at hmax
  rw [hinit, hopt] at hmax
  apply le_trans ?_ hmax
  apply measure_mono_ae
  filter_upwards [hQmono] with ω hmono
  rintro ⟨⟨t, ht⟩, hqω⟩
  exact ⟨t, ExponentialMaximal.exp_threshold_le hlam ht
    ((hmono t.property.2).trans hqω)⟩

end Ripple.Stochastic.ContinuousExponentialMaximal
