-- Ripple/Kurtz/StrongApprox/AllTimeKurtzMoment.lean
import Ripple.Kurtz.StrongApprox.AllTimeKMT

/-!
# The Kurtz 1978 Lemma 3.1 variable on the all-time space

`allTimeKMTXi ω = sup_{q ∈ ℚ≥0} |Y(q) - q - W(q)| / log (max 2 q)`, built from
the paths of `AllTimeKMT`.

* `allTimeKMTXi_tail`: `P(R₀ + x < Ξ) ≤ A e^(-γ x)` for `x ≥ 0`, with
  `R₀ = 2C + 1/b`, `γ = b log 2`, `A = (3/2) a`, where `C, a, b` are
  `allTimeKMTConstant`, `allTimeKMTPrefactor`, `allTimeKMTRate`;
* `allTimeKMTXi_ae_ne_top` and the exponential moment for `θ < γ`.

The events are existential over uncountable time sets; the bounds are on the
outer measure, as in `allTimeKMT_tail`.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.AllTimeKurtzMoment

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology
open AllTimeKMT ContinuousFiniteHorizonKMT

/-! ## The variable -/

/-- The normalized error at time `t`. -/
def allTimeKMTRatio (t : ℝ) (ω : AllTimeKMTSpace) : ℝ :=
  |(allTimeKMTPoisson t ω : ℝ) - t - allTimeKMTBrownian t ω| /
    Real.log (max 2 t)

theorem measurable_allTimeKMTRatio (t : ℝ) :
    Measurable (allTimeKMTRatio t) := by
  unfold allTimeKMTRatio
  have h1 : Measurable fun ω : AllTimeKMTSpace =>
      (allTimeKMTPoisson t ω : ℝ) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
      (measurable_allTimeKMTPoisson t)
  exact (((h1.sub measurable_const).sub
    (measurable_allTimeKMTBrownian t)).abs).div_const _

/-- The supremum over nonnegative rational times. -/
def allTimeKMTXi (ω : AllTimeKMTSpace) : ℝ≥0∞ :=
  ⨆ q : {q : ℚ // 0 ≤ q}, ENNReal.ofReal (allTimeKMTRatio (q.1 : ℝ) ω)

theorem measurable_allTimeKMTXi : Measurable allTimeKMTXi :=
  Measurable.iSup fun _ => (measurable_allTimeKMTRatio _).ennreal_ofReal

/-! ## Constants -/

/-- `R₀ = 2C + 1/b`. -/
def allTimeKurtzShift : ℝ := 2 * allTimeKMTConstant + 1 / allTimeKMTRate

/-- `γ = b log 2`. -/
def allTimeKurtzGamma : ℝ := allTimeKMTRate * Real.log 2

/-- `A = (3/2) a`. -/
def allTimeKurtzTailConstant : ℝ := (3 / 2) * allTimeKMTPrefactor

theorem allTimeKurtzShift_nonneg : 0 ≤ allTimeKurtzShift := by
  have h1 := allTimeKMTConstant_pos
  have h2 := allTimeKMTRate_pos
  unfold allTimeKurtzShift
  positivity

theorem allTimeKurtzGamma_pos : 0 < allTimeKurtzGamma := by
  have h2 := allTimeKMTRate_pos
  have h3 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold allTimeKurtzGamma
  positivity

theorem allTimeKMTPrefactor_ge_one : 1 ≤ allTimeKMTPrefactor := by
  have hden : 0 < 1 - allTimeKMTQ := sub_pos.mpr allTimeKMTQ_lt_one
  have hp : 0 < continuousKMTPrefactor := by
    unfold continuousKMTPrefactor
    positivity
  have hcore : 1 ≤ allTimeKMTCorePrefactor := by
    unfold allTimeKMTCorePrefactor
    have : 0 ≤ continuousKMTPrefactor / (1 - allTimeKMTQ) := by positivity
    linarith
  have hexp : 1 ≤ Real.exp (allTimeKMTRate * allTimeKMTBuffer) :=
    Real.one_le_exp (mul_nonneg allTimeKMTRate_pos.le
      allTimeKMTBuffer_pos.le)
  unfold allTimeKMTPrefactor
  nlinarith

theorem allTimeKurtzTailConstant_ge_one : 1 ≤ allTimeKurtzTailConstant := by
  have := allTimeKMTPrefactor_ge_one
  unfold allTimeKurtzTailConstant
  linarith

/-! ## The block events -/

/-- Block `n` is cut off at `T_n = 2^(n+1)`. -/
def kurtzBlockT (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 1)

/-- `L_n = max n 1 · log 2`. -/
def kurtzBlockL (n : ℕ) : ℝ := ((max n 1 : ℕ) : ℝ) * Real.log 2

/-- The shift making `C log T_n + shift = (R₀ + x) L_n`. -/
def kurtzBlockShift (x : ℝ) (n : ℕ) : ℝ :=
  (allTimeKurtzShift + x) * kurtzBlockL n -
    allTimeKMTConstant * Real.log (kurtzBlockT n)

def kurtzBlockEvent (x : ℝ) (n : ℕ) : Set AllTimeKMTSpace :=
  {ω | ∃ t : ℝ, t ∈ Icc (0 : ℝ) (kurtzBlockT n) ∧
    allTimeKMTConstant * Real.log (kurtzBlockT n) + kurtzBlockShift x n <
      |(allTimeKMTPoisson t ω : ℝ) - t - allTimeKMTBrownian t ω|}

theorem kurtzBlockT_ge_one (n : ℕ) : 1 ≤ kurtzBlockT n := by
  unfold kurtzBlockT
  exact one_le_pow₀ (by norm_num)

theorem kurtzBlockShift_bound {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (((max n 1 : ℕ) : ℝ) * Real.log 2 + allTimeKurtzGamma * x) ≤
      allTimeKMTRate * kurtzBlockShift x n := by
  have hb := allTimeKMTRate_pos
  have hC := allTimeKMTConstant_pos
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hm1 : (1 : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by
    exact_mod_cast le_max_right n 1
  have hmn : (n : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by
    exact_mod_cast le_max_left n 1
  have hlogT : Real.log (kurtzBlockT n) = ((n : ℝ) + 1) * Real.log 2 := by
    unfold kurtzBlockT
    rw [Real.log_pow]
    push_cast
    ring
  have key : allTimeKMTRate * kurtzBlockShift x n -
      (((max n 1 : ℕ) : ℝ) * Real.log 2 + allTimeKurtzGamma * x) =
      Real.log 2 * (allTimeKMTRate * allTimeKMTConstant *
          (2 * ((max n 1 : ℕ) : ℝ) - n - 1) +
        allTimeKMTRate * x * (((max n 1 : ℕ) : ℝ) - 1)) := by
    unfold kurtzBlockShift kurtzBlockL allTimeKurtzShift allTimeKurtzGamma
    rw [hlogT]
    field_simp
    ring
  have hnn : 0 ≤ Real.log 2 * (allTimeKMTRate * allTimeKMTConstant *
          (2 * ((max n 1 : ℕ) : ℝ) - n - 1) +
        allTimeKMTRate * x * (((max n 1 : ℕ) : ℝ) - 1)) := by
    apply mul_nonneg hl.le
    apply add_nonneg
    · apply mul_nonneg (mul_nonneg hb.le hC.le)
      linarith
    · apply mul_nonneg (mul_nonneg hb.le hx)
      linarith
  linarith

theorem kurtzBlockShift_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ kurtzBlockShift x n := by
  have hb := allTimeKMTRate_pos
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hm1 : (1 : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by
    exact_mod_cast le_max_right n 1
  have h := kurtzBlockShift_bound hx n
  have hg := allTimeKurtzGamma_pos
  have : 0 < allTimeKMTRate * kurtzBlockShift x n := by
    nlinarith [mul_nonneg hg.le hx, mul_pos hl (by linarith : (0 : ℝ) < ((max n 1 : ℕ) : ℝ))]
  exact (pos_iff_pos_of_mul_pos this).mp hb |>.le

theorem exp_neg_nat_mul_log_two (m : ℕ) :
    Real.exp (-((m : ℝ) * Real.log 2)) = (1 / 2 : ℝ) ^ m := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num),
    one_div, inv_pow]

theorem kurtzBlockEvent_measure_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    allTimeKMTMeasure (kurtzBlockEvent x n) ≤
      ENNReal.ofReal (allTimeKMTPrefactor * ((1 / 2 : ℝ) ^ (max n 1) *
        Real.exp (-(allTimeKurtzGamma * x)))) := by
  have hs := kurtzBlockShift_nonneg hx n
  have h := allTimeKMT_tail (T := kurtzBlockT n) (x := kurtzBlockShift x n)
    (kurtzBlockT_ge_one n) hs
  have hb := kurtzBlockShift_bound hx n
  calc
    allTimeKMTMeasure (kurtzBlockEvent x n) =
        ENNReal.ofReal (allTimeKMTMeasure.real (kurtzBlockEvent x n)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (allTimeKMTPrefactor *
        Real.exp (-(allTimeKMTRate * kurtzBlockShift x n))) :=
      ENNReal.ofReal_le_ofReal h
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ allTimeKMTPrefactor_pos.le
      calc
        Real.exp (-(allTimeKMTRate * kurtzBlockShift x n)) ≤
            Real.exp (-(((max n 1 : ℕ) : ℝ) * Real.log 2 +
              allTimeKurtzGamma * x)) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = (1 / 2 : ℝ) ^ (max n 1) *
            Real.exp (-(allTimeKurtzGamma * x)) := by
          rw [neg_add, Real.exp_add, exp_neg_nat_mul_log_two]

/-! ## Covering the level event -/

theorem allTimeKMTXi_gt_subset {x : ℝ} (hx : 0 ≤ x) :
    {ω | ENNReal.ofReal (allTimeKurtzShift + x) < allTimeKMTXi ω} ⊆
      ⋃ n : ℕ, kurtzBlockEvent x n := by
  intro ω hω
  have hω' : ENNReal.ofReal (allTimeKurtzShift + x) < allTimeKMTXi ω := hω
  unfold allTimeKMTXi at hω'
  rw [lt_iSup_iff] at hω'
  obtain ⟨⟨q, hq0⟩, hq⟩ := hω'
  rw [ENNReal.ofReal_lt_ofReal_iff'] at hq
  obtain ⟨hlt, _⟩ := hq
  have hq0r : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have hR0 := allTimeKurtzShift_nonneg
  have hmax2 : (2 : ℝ) ≤ max 2 (q : ℝ) := le_max_left _ _
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hell : 0 < Real.log (max 2 (q : ℝ)) :=
    lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) hmax2)
  have hZ : (allTimeKurtzShift + x) * Real.log (max 2 (q : ℝ)) <
      |(allTimeKMTPoisson (q : ℝ) ω : ℝ) - (q : ℝ) -
        allTimeKMTBrownian (q : ℝ) ω| := by
    have := (lt_div_iff₀ hell).mp hlt
    exact this
  -- a block index with L_n ≤ log (max 2 q) and q ≤ T_n
  have hex : ∃ n : ℕ, (q : ℝ) ≤ kurtzBlockT n ∧
      kurtzBlockL n ≤ Real.log (max 2 (q : ℝ)) := by
    by_cases hq2 : (q : ℝ) < 2
    · refine ⟨0, ?_, ?_⟩
      · unfold kurtzBlockT
        norm_num
        linarith
      · unfold kurtzBlockL
        simp only [zero_le, max_eq_right, Nat.cast_one, one_mul]
        exact Real.log_le_log (by norm_num) hmax2
    · have hq2' : (2 : ℝ) ≤ (q : ℝ) := le_of_not_gt hq2
      obtain ⟨k, hk1, hk2⟩ :=
        exists_nat_pow_near (x := (q : ℝ)) (y := (2 : ℝ))
          (by linarith) (by norm_num)
      have hk : 1 ≤ k := by
        by_contra hk0
        have : k = 0 := by omega
        subst this
        norm_num at hk2
        linarith
      refine ⟨k, hk2.le, ?_⟩
      unfold kurtzBlockL
      rw [max_eq_left hk, max_eq_right hq2']
      have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      calc (k : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k) := by
            rw [Real.log_pow]
        _ ≤ Real.log (q : ℝ) := Real.log_le_log hpos hk1
  obtain ⟨n, hqT, hL⟩ := hex
  refine Set.mem_iUnion.2 ⟨n, (q : ℝ), ⟨hq0r, hqT⟩, ?_⟩
  have h1 : (allTimeKurtzShift + x) * kurtzBlockL n ≤
      (allTimeKurtzShift + x) * Real.log (max 2 (q : ℝ)) :=
    mul_le_mul_of_nonneg_left hL (by linarith)
  unfold kurtzBlockShift
  linarith

/-! ## The tail of the variable -/

private theorem tsum_half_pow_succ :
    ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) = 1 := by
  have h : ∀ n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) =
      (1 / 2 : ℝ≥0∞) ^ (n + 1) := by
    intro n
    rw [ENNReal.ofReal_pow (by norm_num)]
    congr 1
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  simp only [h]
  simp only [pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_div,
    ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem allTimeKMTXi_tail {x : ℝ} (hx : 0 ≤ x) :
    allTimeKMTMeasure
        {ω | ENNReal.ofReal (allTimeKurtzShift + x) < allTimeKMTXi ω} ≤
      ENNReal.ofReal (allTimeKurtzTailConstant *
        Real.exp (-(allTimeKurtzGamma * x))) := by
  set E : ℝ := Real.exp (-(allTimeKurtzGamma * x)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have ha := allTimeKMTPrefactor_pos
  have hsub : {ω | ENNReal.ofReal (allTimeKurtzShift + x) < allTimeKMTXi ω} ⊆
      kurtzBlockEvent x 0 ∪ ⋃ n : ℕ, kurtzBlockEvent x (n + 1) := by
    intro ω hω
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (allTimeKMTXi_gt_subset hx hω)
    cases n with
    | zero => exact Or.inl hn
    | succ k => exact Or.inr (Set.mem_iUnion.2 ⟨k, hn⟩)
  have h0 : allTimeKMTMeasure (kurtzBlockEvent x 0) ≤
      ENNReal.ofReal (allTimeKMTPrefactor / 2 * E) := by
    refine (kurtzBlockEvent_measure_le hx 0).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    simp only [zero_le, max_eq_right, pow_one]
    ring
  have hterm : ∀ n : ℕ, allTimeKMTMeasure (kurtzBlockEvent x (n + 1)) ≤
      ENNReal.ofReal (allTimeKMTPrefactor * E) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
    intro n
    refine (kurtzBlockEvent_measure_le hx (n + 1)).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    have : max (n + 1) 1 = n + 1 := max_eq_left (by omega)
    rw [this]
    ring
  calc
    allTimeKMTMeasure
        {ω | ENNReal.ofReal (allTimeKurtzShift + x) < allTimeKMTXi ω} ≤
      allTimeKMTMeasure (kurtzBlockEvent x 0 ∪
        ⋃ n : ℕ, kurtzBlockEvent x (n + 1)) := measure_mono hsub
    _ ≤ allTimeKMTMeasure (kurtzBlockEvent x 0) +
        allTimeKMTMeasure (⋃ n : ℕ, kurtzBlockEvent x (n + 1)) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (allTimeKMTPrefactor / 2 * E) +
        ∑' n : ℕ, ENNReal.ofReal (allTimeKMTPrefactor * E) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
      gcongr
      exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal (allTimeKMTPrefactor / 2 * E) +
        ENNReal.ofReal (allTimeKMTPrefactor * E) := by
      rw [ENNReal.tsum_mul_left, tsum_half_pow_succ, mul_one]
    _ = ENNReal.ofReal (allTimeKurtzTailConstant * E) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold allTimeKurtzTailConstant
      ring


/-! ## Almost-sure finiteness and the exponential moment -/

/-- The tail at every positive level, with a single constant. -/
theorem allTimeKMTXi_tail_all {t : ℝ} (ht : 0 ≤ t) :
    allTimeKMTMeasure {ω | ENNReal.ofReal t < allTimeKMTXi ω} ≤
      ENNReal.ofReal (allTimeKurtzTailConstant *
        Real.exp (allTimeKurtzGamma * allTimeKurtzShift) *
        Real.exp (-(allTimeKurtzGamma * t))) := by
  have hA := allTimeKurtzTailConstant_ge_one
  have hg := allTimeKurtzGamma_pos
  by_cases hR : allTimeKurtzShift ≤ t
  · have hx : 0 ≤ t - allTimeKurtzShift := sub_nonneg.mpr hR
    have h := allTimeKMTXi_tail hx
    have hrw : allTimeKurtzShift + (t - allTimeKurtzShift) = t := by ring
    rw [hrw] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · have hlt : t < allTimeKurtzShift := lt_of_not_ge hR
    calc
      allTimeKMTMeasure {ω | ENNReal.ofReal t < allTimeKMTXi ω} ≤ 1 :=
        prob_le_one
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have h1 : (1 : ℝ) ≤ Real.exp (allTimeKurtzGamma *
            allTimeKurtzShift) * Real.exp (-(allTimeKurtzGamma * t)) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          nlinarith
        calc (1 : ℝ) ≤ allTimeKurtzTailConstant * 1 := by linarith
          _ ≤ allTimeKurtzTailConstant * (Real.exp (allTimeKurtzGamma *
              allTimeKurtzShift) * Real.exp (-(allTimeKurtzGamma * t))) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = _ := by ring

theorem allTimeKMTXi_ae_ne_top :
    ∀ᵐ ω ∂allTimeKMTMeasure, allTimeKMTXi ω ≠ ⊤ := by
  have hzero : allTimeKMTMeasure {ω | allTimeKMTXi ω = ⊤} = 0 := by
    have hle : ∀ n : ℕ, allTimeKMTMeasure {ω | allTimeKMTXi ω = ⊤} ≤
        ENNReal.ofReal (allTimeKurtzTailConstant *
          Real.exp (allTimeKurtzGamma * allTimeKurtzShift) *
          Real.exp (-(allTimeKurtzGamma * (n : ℝ)))) := by
      intro n
      refine le_trans (measure_mono ?_)
        (allTimeKMTXi_tail_all (Nat.cast_nonneg n))
      intro ω homega
      have h : allTimeKMTXi ω = ⊤ := homega
      show ENNReal.ofReal (n : ℝ) < allTimeKMTXi ω
      rw [h]
      exact ENNReal.ofReal_lt_top
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        (allTimeKurtzTailConstant *
          Real.exp (allTimeKurtzGamma * allTimeKurtzShift) *
          Real.exp (-(allTimeKurtzGamma * (n : ℝ))))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => Real.exp (-(allTimeKurtzGamma * (n : ℝ))))
          atTop (𝓝 0) := by
        have hg := allTimeKurtzGamma_pos
        have h1 : Tendsto (fun n : ℕ => allTimeKurtzGamma * (n : ℝ)) atTop
            atTop :=
          (tendsto_id.const_mul_atTop hg).comp tendsto_natCast_atTop_atTop
        exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      have h2 := h0.const_mul (allTimeKurtzTailConstant *
        Real.exp (allTimeKurtzGamma * allTimeKurtzShift))
      simpa using ENNReal.tendsto_ofReal h2
    exact le_antisymm (ge_of_tendsto' hlim hle) bot_le
  rw [ae_iff]
  simpa using hzero

/-- Layer-cake bound for an exponential moment from an exponential tail. -/
theorem lintegral_exp_le_of_tail
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hfm : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    {K γ θ : ℝ} (hK : 0 ≤ K) (hθ0 : 0 < θ) (hθγ : θ < γ)
    (htail : ∀ t : ℝ, 0 < t →
      P {ω | t < f ω} ≤ ENNReal.ofReal (K * Real.exp (-(γ * t)))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * f ω)) ∂P ≤
      ENNReal.ofReal (1 + K * θ / (γ - θ)) := by
  set g : ℝ → ℝ := fun t => θ * Real.exp (θ * t) with hg
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul P
    (Filter.Eventually.of_forall hf0) hfm.aemeasurable
    (fun t _ => hgc.intervalIntegrable 0 t)
    (Filter.Eventually.of_forall fun t => by simp only [hg]; positivity)
  have hprim : ∀ s : ℝ, ∫ t in (0 : ℝ)..s, g t = Real.exp (θ * s) - 1 := by
    intro s
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) s,
        HasDerivAt (fun x => Real.exp (θ * x)) (g x) x := by
      intro x _
      have h1 : HasDerivAt (fun x : ℝ => θ * x) θ x := by
        simpa using (hasDerivAt_id x).const_mul θ
      have h2 := (Real.hasDerivAt_exp (θ * x)).comp x h1
      simpa [hg, mul_comm] using h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hgc.intervalIntegrable 0 s)]
    simp
  have hdecay : 0 < γ - θ := by linarith
  have htail' : ∀ t ∈ Ioi (0 : ℝ),
      P {ω | t < f ω} * ENNReal.ofReal (g t) ≤
        ENNReal.ofReal (K * θ * Real.exp (-(γ - θ) * t)) := by
    intro t ht
    have ht0 : 0 < t := ht
    calc
      P {ω | t < f ω} * ENNReal.ofReal (g t) ≤
          ENNReal.ofReal (K * Real.exp (-(γ * t))) *
            ENNReal.ofReal (g t) :=
        mul_le_mul_right' (htail t ht0) _
      _ = ENNReal.ofReal (K * θ * Real.exp (-(γ - θ) * t)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [hg]
        have : K * Real.exp (-(γ * t)) * (θ * Real.exp (θ * t)) =
            K * θ * (Real.exp (-(γ * t)) * Real.exp (θ * t)) := by ring
        rw [this, ← Real.exp_add]
        congr 2
        ring
  have hint : ∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (K * θ * Real.exp (-(γ - θ) * t)) =
        ENNReal.ofReal (K * θ / (γ - θ)) := by
    have hI : IntegrableOn (fun t : ℝ => K * θ * Real.exp (-(γ - θ) * t))
        (Ioi (0 : ℝ)) volume :=
      (integrableOn_exp_mul_Ioi (a := -(γ - θ)) (by linarith)
        (0 : ℝ)).const_mul (K * θ)
    have hval : ∫ t in Ioi (0 : ℝ), K * θ * Real.exp (-(γ - θ) * t) =
        K * θ / (γ - θ) := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (a := -(γ - θ)) (by linarith) (0 : ℝ)]
      simp only [mul_zero, Real.exp_zero]
      field_simp
      try ring
    rw [← hval]
    symm
    exact ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun t => by positivity)
  have hmain :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * f ω) - 1) ∂P ≤
        ENNReal.ofReal (K * θ / (γ - θ)) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * f ω) - 1) ∂P =
          ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..f ω, g t) ∂P := by
        congr 1
        funext ω
        rw [hprim]
      _ = ∫⁻ t in Ioi (0 : ℝ), P {ω | t < f ω} *
          ENNReal.ofReal (g t) := hlayer
      _ ≤ ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (K * θ * Real.exp (-(γ - θ) * t)) :=
        setLIntegral_mono' measurableSet_Ioi htail'
      _ = ENNReal.ofReal (K * θ / (γ - θ)) := hint
  have hsplit : ∀ ω, ENNReal.ofReal (Real.exp (θ * f ω)) =
      1 + ENNReal.ofReal (Real.exp (θ * f ω) - 1) := by
    intro ω
    have h1 : (1 : ℝ) ≤ Real.exp (θ * f ω) :=
      Real.one_le_exp (mul_nonneg hθ0.le (hf0 ω))
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by linarith)]
    congr 1
    ring
  have hKθ : 0 ≤ K * θ / (γ - θ) := div_nonneg (mul_nonneg hK hθ0.le) hdecay.le
  calc
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * f ω)) ∂P =
        ∫⁻ ω, (1 + ENNReal.ofReal (Real.exp (θ * f ω) - 1)) ∂P := by
      congr 1
      funext ω
      exact hsplit ω
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * f ω) - 1) ∂P := by
      have h := lintegral_add_left (μ := P)
        (measurable_const (a := (1 : ℝ≥0∞)))
        (fun ω => ENNReal.ofReal (Real.exp (θ * f ω) - 1))
      simpa using h
    _ ≤ 1 + ENNReal.ofReal (K * θ / (γ - θ)) := by gcongr
    _ = ENNReal.ofReal (1 + K * θ / (γ - θ)) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hKθ]

/-- The exponential moment of the Kurtz variable, `0 < θ < γ`. -/
theorem lintegral_exp_allTimeKMTXi_le
    {θ : ℝ} (hθ0 : 0 < θ) (hθγ : θ < allTimeKurtzGamma) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (allTimeKMTXi ω).toReal))
        ∂allTimeKMTMeasure ≤
      ENNReal.ofReal (1 + (allTimeKurtzTailConstant *
        Real.exp (allTimeKurtzGamma * allTimeKurtzShift)) * θ /
          (allTimeKurtzGamma - θ)) := by
  refine lintegral_exp_le_of_tail
    (P := allTimeKMTMeasure) (f := fun ω => (allTimeKMTXi ω).toReal)
    measurable_allTimeKMTXi.ennreal_toReal (fun ω => ENNReal.toReal_nonneg)
    (by have := allTimeKurtzTailConstant_ge_one; positivity)
    hθ0 hθγ ?_
  intro t ht
  have hsub : {ω | t < (allTimeKMTXi ω).toReal} ⊆
      {ω | ENNReal.ofReal t < allTimeKMTXi ω} := by
    intro ω homega
    have h1 : t < (allTimeKMTXi ω).toReal := homega
    have hne : allTimeKMTXi ω ≠ ⊤ := by
      intro htop
      rw [htop] at h1
      simp at h1
      linarith
    show ENNReal.ofReal t < allTimeKMTXi ω
    calc ENNReal.ofReal t < ENNReal.ofReal (allTimeKMTXi ω).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr h1
      _ = allTimeKMTXi ω := ENNReal.ofReal_toReal hne
  exact (measure_mono hsub).trans (allTimeKMTXi_tail_all ht.le)

theorem integral_exp_allTimeKMTXi_le
    {θ : ℝ} (hθ0 : 0 < θ) (hθγ : θ < allTimeKurtzGamma) :
    Integrable (fun ω => Real.exp (θ * (allTimeKMTXi ω).toReal))
        allTimeKMTMeasure ∧
      ∫ ω, Real.exp (θ * (allTimeKMTXi ω).toReal) ∂allTimeKMTMeasure ≤
        1 + (allTimeKurtzTailConstant *
          Real.exp (allTimeKurtzGamma * allTimeKurtzShift)) * θ /
            (allTimeKurtzGamma - θ) := by
  have hmeas : Measurable (fun ω =>
      Real.exp (θ * (allTimeKMTXi ω).toReal)) :=
    Real.measurable_exp.comp
      (measurable_const.mul measurable_allTimeKMTXi.ennreal_toReal)
  have hnn : 0 ≤ᵐ[allTimeKMTMeasure] (fun ω =>
      Real.exp (θ * (allTimeKMTXi ω).toReal)) :=
    Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hbound := lintegral_exp_allTimeKMTXi_le hθ0 hθγ
  have hint : Integrable (fun ω =>
      Real.exp (θ * (allTimeKMTXi ω).toReal)) allTimeKMTMeasure :=
    ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).mpr
        (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  have hge : 0 ≤ 1 + (allTimeKurtzTailConstant *
      Real.exp (allTimeKurtzGamma * allTimeKurtzShift)) * θ /
        (allTimeKurtzGamma - θ) := by
    have h1 := allTimeKurtzTailConstant_ge_one
    have h2 : 0 < allTimeKurtzGamma - θ := by linarith
    positivity
  exact ENNReal.toReal_le_of_le_ofReal hge hbound


/-! ## The supremum over rational times is the supremum over real times -/

theorem allTimeBlockStart_mono : Monotone allTimeBlockStart := by
  intro a b hab
  unfold allTimeBlockStart allTimeBlockLength
  have : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
    pow_le_pow_right₀ (by norm_num) hab
  linarith

theorem allTimeBlock_eq_of_bounds {s : ℝ} {J : ℕ} (h0 : 0 ≤ s)
    (h1 : allTimeBlockStart J ≤ s) (h2 : s < allTimeBlockStart (J + 1)) :
    allTimeBlock s = J := by
  apply le_antisymm (allTimeBlock_le_of_lt_start h0 h2)
  by_contra hnot
  have hlt : allTimeBlock s + 1 ≤ J := by omega
  have hup := allTimeBlock_upper h0
  have hmono := allTimeBlockStart_mono hlt
  linarith

/-- The error `Y - t - W` is right-continuous at every `t ≥ 0`, for every
sample.  On the half-open block containing `t` it is a constant plus the
local block path, which is right-continuous (Poisson) and continuous
(Brownian). -/
theorem allTimeKMTError_rightContinuous (ω : AllTimeKMTSpace) {t : ℝ}
    (ht : 0 ≤ t) :
    ContinuousWithinAt
      (fun s => (allTimeKMTPoisson s ω : ℝ) - s - allTimeKMTBrownian s ω)
      (Ici t) t := by
  set J := allTimeBlock t with hJ
  have hb := allTimeBlock_bounds ht
  rw [← hJ] at hb
  set Sp : ℝ := ∑ j ∈ range J,
    (continuousKMTPoisson j (allTimeBlockLength j) (ω j) : ℝ) with hSp
  set Sw : ℝ := ∑ j ∈ range J,
    continuousKMTBrownian j (allTimeBlockLength j) (ω j) with hSw
  set F : ℝ → ℝ := fun s =>
    (Sp - Sw) + ((continuousKMTPoisson J (s - allTimeBlockStart J) (ω J) : ℝ) -
      continuousKMTBrownian J (s - allTimeBlockStart J) (ω J)) - s with hF
  have hPoisson : ContinuousWithinAt
      (fun s : ℝ => (continuousKMTPoisson J (s - allTimeBlockStart J) (ω J) : ℝ))
      (Ici t) t := by
    have hP := DyadicConditionalPoissonPath.committedContinuousPoisson_continuousWithinAt
      J (t - allTimeBlockStart J) (continuousKMTToContinuous J (ω J))
    have hsub : ContinuousWithinAt (fun s : ℝ => s - allTimeBlockStart J)
        (Ici t) t :=
      (continuous_id.sub continuous_const).continuousWithinAt
    refine ContinuousWithinAt.comp (g := fun u : ℝ =>
      (DyadicConditionalPoissonPath.committedContinuousPoisson J u
        (continuousKMTToContinuous J (ω J)) : ℝ)) hP hsub ?_
    intro s hs
    exact sub_le_sub_right (mem_Ici.mp hs) _
  have hBrown : ContinuousWithinAt
      (fun s : ℝ => continuousKMTBrownian J (s - allTimeBlockStart J) (ω J))
      (Ici t) t := by
    have hc : Continuous (fun s : ℝ =>
        continuousKMTBrownian J (s - allTimeBlockStart J) (ω J)) := by
      have := (BrownianFineDyadicCompletion.continuous_brownianPath J
        (continuousKMTToBrownian J (ω J))).comp
        (continuous_id.sub (continuous_const (y := allTimeBlockStart J)))
      exact this
    exact hc.continuousWithinAt
  have hFcont : ContinuousWithinAt F (Ici t) t := by
    simp only [hF]
    exact ((continuousWithinAt_const.add (hPoisson.sub hBrown)).sub
      continuousWithinAt_id)
  have hev : (fun s => (allTimeKMTPoisson s ω : ℝ) - s -
      allTimeKMTBrownian s ω) =ᶠ[nhdsWithin t (Ici t)] F := by
    have hlt : ∀ᶠ s in nhdsWithin t (Ici t), s < allTimeBlockStart (J + 1) :=
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hb.2)
    filter_upwards [hlt, self_mem_nhdsWithin] with s hs1 hs2
    have hs0 : 0 ≤ s := le_trans ht hs2
    have hlow : allTimeBlockStart J ≤ s := le_trans hb.1 hs2
    have hblk : allTimeBlock s = J := allTimeBlock_eq_of_bounds hs0 hlow hs1
    rw [allTimeKMTPoisson_of_nonneg s hs0, allTimeKMTBrownian_of_nonneg s hs0,
      hblk]
    simp only [hF, hSp, hSw, allTimeLocalTime, hblk]
    push_cast
    ring
  refine hFcont.congr_of_eventuallyEq hev ?_
  have hs1 : t < allTimeBlockStart (J + 1) := hb.2
  have hblk : allTimeBlock t = J := hJ.symm
  rw [allTimeKMTPoisson_of_nonneg t ht, allTimeKMTBrownian_of_nonneg t ht,
    hblk]
  simp only [hF, hSp, hSw, allTimeLocalTime, hblk]
  push_cast
  ring

theorem allTimeKMTRatio_rightContinuous (ω : AllTimeKMTSpace) {t : ℝ}
    (ht : 0 ≤ t) :
    ContinuousWithinAt (fun s => allTimeKMTRatio s ω) (Ici t) t := by
  unfold allTimeKMTRatio
  have hnum : ContinuousWithinAt (fun s : ℝ =>
      |(allTimeKMTPoisson s ω : ℝ) - s - allTimeKMTBrownian s ω|)
      (Ici t) t :=
    continuous_abs.continuousAt.comp_continuousWithinAt
      (allTimeKMTError_rightContinuous ω ht)
  have hlogc : Continuous (fun s : ℝ => Real.log (max 2 s)) :=
    Continuous.log (continuous_const.max continuous_id)
      (fun s => (lt_of_lt_of_le (by norm_num) (le_max_left 2 s)).ne')
  have hlogpos : 0 < Real.log (max 2 t) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_left 2 t))
  exact hnum.div hlogc.continuousWithinAt hlogpos.ne'

/-- The supremum over real times `t ≥ 0` (Kurtz's form of the variable). -/
def allTimeKMTXiReal (ω : AllTimeKMTSpace) : ℝ≥0∞ :=
  ⨆ t : {t : ℝ // 0 ≤ t}, ENNReal.ofReal (allTimeKMTRatio t.1 ω)

/-- For every sample, the rational supremum is the real supremum. -/
theorem allTimeKMTXi_eq_real_sup (ω : AllTimeKMTSpace) :
    allTimeKMTXi ω = allTimeKMTXiReal ω := by
  apply le_antisymm
  · unfold allTimeKMTXi allTimeKMTXiReal
    refine iSup_le fun q => ?_
    exact le_iSup (fun t : {t : ℝ // 0 ≤ t} =>
      ENNReal.ofReal (allTimeKMTRatio t.1 ω))
      ⟨(q.1 : ℝ), by exact_mod_cast q.2⟩
  · unfold allTimeKMTXiReal
    refine iSup_le fun t => ?_
    by_contra hlt
    have hlt' : allTimeKMTXi ω < ENNReal.ofReal (allTimeKMTRatio t.1 ω) :=
      lt_of_not_ge hlt
    have hne : allTimeKMTXi ω ≠ ⊤ := ne_top_of_lt hlt'
    have hm : (allTimeKMTXi ω).toReal < allTimeKMTRatio t.1 ω :=
      (ENNReal.lt_ofReal_iff_toReal_lt hne).mp hlt'
    have hrat : ∀ q : ℚ, 0 ≤ q →
        allTimeKMTRatio (q : ℝ) ω ≤ (allTimeKMTXi ω).toReal := by
      intro q hq
      have h1 : ENNReal.ofReal (allTimeKMTRatio (q : ℝ) ω) ≤
          allTimeKMTXi ω :=
        le_iSup (fun r : {r : ℚ // 0 ≤ r} =>
          ENNReal.ofReal (allTimeKMTRatio (r.1 : ℝ) ω)) ⟨q, hq⟩
      exact (ENNReal.ofReal_le_iff_le_toReal hne).mp h1
    have hcont := allTimeKMTRatio_rightContinuous ω t.2
    have hev : ∀ᶠ s in nhdsWithin t.1 (Ici t.1),
        (allTimeKMTXi ω).toReal < allTimeKMTRatio s ω :=
      hcont.eventually (lt_mem_nhds hm)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t.1 < t.1 + ε by linarith)
    have hq0 : 0 ≤ q := by
      have : (0 : ℝ) ≤ q := le_trans t.2 hq1.le
      exact_mod_cast this
    have hdist : dist (q : ℝ) t.1 < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hgt := hball hdist (mem_Ici.mpr hq1.le)
    exact absurd (hrat q hq0) (not_le.mpr hgt)

theorem allTimeKMTXi_eq_real_sup_ae :
    ∀ᵐ ω ∂allTimeKMTMeasure, allTimeKMTXi ω = allTimeKMTXiReal ω :=
  Filter.Eventually.of_forall allTimeKMTXi_eq_real_sup

/-- The real-time variable has the same tail. -/
theorem allTimeKMTXiReal_tail {x : ℝ} (hx : 0 ≤ x) :
    allTimeKMTMeasure
        {ω | ENNReal.ofReal (allTimeKurtzShift + x) < allTimeKMTXiReal ω} ≤
      ENNReal.ofReal (allTimeKurtzTailConstant *
        Real.exp (-(allTimeKurtzGamma * x))) := by
  have : {ω | ENNReal.ofReal (allTimeKurtzShift + x) < allTimeKMTXiReal ω} =
      {ω | ENNReal.ofReal (allTimeKurtzShift + x) < allTimeKMTXi ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, allTimeKMTXi_eq_real_sup]
  rw [this]
  exact allTimeKMTXi_tail hx

end Ripple.Kurtz.StrongApprox.AllTimeKurtzMoment

end
