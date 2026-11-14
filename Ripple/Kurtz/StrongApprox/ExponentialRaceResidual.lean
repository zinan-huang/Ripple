-- Ripple/Kurtz/StrongApprox/ExponentialRaceResidual.lean
import Mathlib

/-!
# Exact residual law for a finite exponential race

The fixed-winner factorization is adapted from the Apache-2.0 exponential
race proof in DLorell/stoch_to_det, as reorganized in
AlexisOlson/natural-latents.  It is reproduced here so the Kurtz construction
does not acquire an external dependency.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.ExponentialRace

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

/-- Independent unit exponential clocks. -/
noncomputable def clockLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => expMeasure 1

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (clockLaw ι) := by
  unfold clockLaw
  let : ∀ _ : ι, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  infer_instance

lemma expMeasure_one_Iic_zero : expMeasure 1 (Iic 0) = 0 := by
  let := isProbabilityMeasure_expMeasure (r := (1 : ℝ)) zero_lt_one
  have hreal : (expMeasure 1).real (Iic 0) = 0 := by
    rw [← cdf_eq_real]
    simpa using cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one 0
  exact (measureReal_eq_zero_iff).mp hreal

lemma expMeasure_one_Ioi (x : ℝ) (hx : 0 ≤ x) :
    expMeasure 1 (Ioi x) = ENNReal.ofReal (Real.exp (-x)) := by
  let := isProbabilityMeasure_expMeasure (r := (1 : ℝ)) zero_lt_one
  have hsub : 0 ≤ 1 - Real.exp (-x) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))
  have hreal : (expMeasure 1).real (Iic x) = 1 - Real.exp (-x) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one x,
      if_pos hx, one_mul]
  have hIic : expMeasure 1 (Iic x) =
      ENNReal.ofReal (1 - Real.exp (-x)) := by
    rw [← ofReal_measureReal, hreal]
  rw [show Ioi x = (Iic x)ᶜ by ext y; simp,
    measure_compl measurableSet_Iic (measure_ne_top (expMeasure 1) (Iic x)),
    measure_univ, hIic, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hsub]
  congr 1
  ring

private lemma expMeasure_one_tilt {t : ℝ} (ht : 0 < t) :
    (expMeasure 1).withDensity
        (fun y => ENNReal.ofReal
          (Real.exp (-((1 / t - 1) * y)))) =
      ENNReal.ofReal t • expMeasure (1 / t) := by
  have hpdf (r : ℝ) : Measurable (gammaPDF 1 r) := by
    unfold gammaPDF
    exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hweight : Measurable
      (fun y : ℝ => ENNReal.ofReal
        (Real.exp (-((1 / t - 1) * y)))) := by fun_prop
  unfold expMeasure gammaMeasure
  rw [← withDensity_mul volume (hpdf 1) hweight,
    ← withDensity_smul (μ := volume) (ENNReal.ofReal t) (hpdf (1 / t))]
  apply withDensity_congr_ae
  filter_upwards [] with y
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  simp only [gammaPDF_eq, Real.rpow_one, Real.Gamma_one, div_one,
    sub_self, Real.rpow_zero, mul_one, one_mul]
  by_cases hy : 0 ≤ y
  · simp only [if_pos hy]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul ht.le]
    congr 1
    rw [← Real.exp_add]
    field_simp [ht.ne']
    ring_nf
  · simp [if_neg hy]

private lemma map_div_expMeasure {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => x / t) (expMeasure (1 / t)) =
      expMeasure 1 := by
  let : IsProbabilityMeasure (expMeasure (1 / t)) :=
    isProbabilityMeasure_expMeasure (one_div_pos.mpr ht)
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure
      (Measure.map (fun x : ℝ => x / t) (expMeasure (1 / t))) :=
    Measure.isProbabilityMeasure_map (measurable_id.div_const t).aemeasurable
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply (f := fun y : ℝ => y / t)
      (measurable_id.div_const t) measurableSet_Iic]
  rw [show (fun y : ℝ => y / t) ⁻¹' Iic x = Iic (t * x) by
    ext y
    simp only [mem_preimage, mem_Iic]
    exact (div_le_iff₀ ht).trans (by ring_nf)]
  rw [← ofReal_cdf (expMeasure (1 / t)) (t * x),
    ← ofReal_cdf (expMeasure 1) x,
    ENNReal.toReal_ofReal (cdf_nonneg _ _),
    ENNReal.toReal_ofReal (cdf_nonneg _ _)]
  rw [cdf_expMeasure_eq (one_div_pos.mpr ht), cdf_expMeasure_eq zero_lt_one]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos (mul_nonneg ht.le hx)]
    congr 2
    field_simp [ht.ne']
  · have htx : ¬ 0 ≤ t * x := by nlinarith
    rw [if_neg hx, if_neg htx]

private lemma map_mul_expMeasure {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => t * x) (expMeasure t) = expMeasure 1 := by
  simpa [div_eq_mul_inv, ht.ne', mul_comm] using
    (map_div_expMeasure (t := 1 / t) (one_div_pos.mpr ht))

private lemma map_div_expMeasure_one {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => x / t) (expMeasure 1) = expMeasure t := by
  rw [← map_mul_expMeasure ht,
    Measure.map_map (g := fun x : ℝ => x / t) (f := fun x : ℝ => t * x)
      (by fun_prop) (by fun_prop)]
  simp [Function.comp_def, ht.ne']

private lemma map_sub_restrict_expMeasure_one {a : ℝ} (ha : 0 ≤ a) :
    Measure.map (fun x : ℝ => x - a)
        ((expMeasure 1).restrict (Ioi a)) =
      ENNReal.ofReal (Real.exp (-a)) • expMeasure 1 := by
  let ν : Measure ℝ := expMeasure 1
  let : IsProbabilityMeasure ν :=
    isProbabilityMeasure_expMeasure zero_lt_one
  apply Measure.ext_of_Iic
  intro x
  have hpre : (fun y : ℝ => y - a) ⁻¹' Iic x = Iic (x + a) := by
    ext y
    simp only [mem_preimage, mem_Iic, sub_le_iff_le_add]
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic, hpre,
    Measure.restrict_apply measurableSet_Iic,
    Measure.smul_apply, smul_eq_mul]
  by_cases hx : 0 ≤ x
  · have hxapos : 0 ≤ x + a := add_nonneg hx ha
    have hIoc : ν (Ioc a (x + a)) =
        ENNReal.ofReal (cdf ν (x + a) - cdf ν a) := by
      simpa only [measure_cdf] using (cdf ν).measure_Ioc a (x + a)
    rw [Set.inter_comm (Iic (x + a)), Ioi_inter_Iic,
      hIoc, ← ofReal_cdf ν x]
    dsimp [ν]
    rw [cdf_expMeasure_eq zero_lt_one,
      cdf_expMeasure_eq zero_lt_one,
      cdf_expMeasure_eq zero_lt_one]
    simp only [if_pos hxapos, if_pos ha, if_pos hx, one_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-a))]
    congr 1
    rw [show -(x + a) = -a + -x by ring, Real.exp_add]
    ring
  · have hnot : ¬a < x + a := by linarith
    rw [Set.inter_comm (Iic (x + a)), Ioi_inter_Iic,
      Ioc_eq_empty hnot, measure_empty, ← ofReal_cdf ν x]
    dsimp [ν]
    rw [cdf_expMeasure_eq zero_lt_one, if_neg hx]
    simp

private lemma map_scaled_excess_restrict_expMeasure_one
    {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    Measure.map (fun x : ℝ => x / t - u)
        ((expMeasure 1).restrict (Ioi (t * u))) =
      ENNReal.ofReal (Real.exp (-(t * u))) • expMeasure t := by
  have hcomp : (fun x : ℝ => x / t - u) =
      (fun y : ℝ => y / t) ∘ (fun x : ℝ => x - t * u) := by
    funext x
    dsimp only [Function.comp_apply]
    field_simp [ht.ne']
  rw [hcomp, ← Measure.map_map (g := fun y : ℝ => y / t)
      (f := fun x : ℝ => x - t * u) (measurable_id.div_const t)
      (measurable_id.sub_const (t * u)),
    map_sub_restrict_expMeasure_one (mul_nonneg ht.le hu),
    Measure.map_smul,
    map_div_expMeasure_one ht]

private noncomputable def weightedLosingExcessLaw
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (a : κ) : Measure ({i : κ // i ≠ a} → ℝ) :=
  Measure.pi fun i : {i : κ // i ≠ a} => expMeasure (t i.1)

private lemma map_losing_scaled_excess
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ)
    {u : ℝ} (hu : 0 ≤ u) :
    Measure.map
        (fun E : {i : κ // i ≠ a} → ℝ =>
          fun i => E i / t i.1 - u)
        ((Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).restrict
          (Set.pi Set.univ
            (fun i : {i : κ // i ≠ a} => Ioi (t i.1 * u)))) =
      (∏ i : {i : κ // i ≠ a},
          ENNReal.ofReal (Real.exp (-(t i.1 * u)))) •
        weightedLosingExcessLaw t a := by
  let d : {i : κ // i ≠ a} → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (Real.exp (-(t i.1 * u)))
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  let (i : {i : κ // i ≠ a}) : IsFiniteMeasure
      (d i • expMeasure (t i.1)) := ⟨by simp [d]⟩
  rw [Measure.restrict_pi_pi, Measure.pi_map_pi fun (i : {i : κ // i ≠ a}) =>
    (by fun_prop : AEMeasurable (fun x : ℝ => x / t i.1 - u)
      ((expMeasure 1).restrict (Ioi (t i.1 * u))))]
  simp_rw [map_scaled_excess_restrict_expMeasure_one (ht _) hu]
  change Measure.pi (fun i => d i • expMeasure (t i.1)) =
    (∏ i, d i) • weightedLosingExcessLaw t a
  unfold weightedLosingExcessLaw
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]

/-- Channel `a` is the strict winner of the weighted exponential race. -/
def strictClockWin {κ : Type*} (t : κ → ℝ) (a : κ)
    (E : κ → ℝ) : Prop :=
  ∀ b, b ≠ a → E a / t a < E b / t b

lemma strictClockWin_measurableSet
    {κ : Type*} [Fintype κ]
    (t : κ → ℝ) (a : κ) :
    MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
  unfold strictClockWin
  measurability

private noncomputable def winnerClockJoin
    {κ : Type*} [DecidableEq κ] (a : κ)
    (sr : ℝ × ({i : κ // i ≠ a} → ℝ)) : κ → ℝ :=
  fun i => if h : i = a then sr.1 else sr.2 ⟨i, h⟩

private lemma winnerClockJoin_measurable
    {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measurable (winnerClockJoin a) := by
  refine measurable_pi_iff.mpr ?_
  intro i
  by_cases hi : i = a <;>
    simp only [winnerClockJoin, hi, dite_true, dite_false] <;> fun_prop

private lemma clockReindex_law
    {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measure.map (winnerClockJoin a ∘ Prod.swap)
        ((Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1).prod
          (expMeasure 1)) = clockLaw κ := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  have hjoin : winnerClockJoin a ∘ Prod.swap = g ∘ f := by
    funext xy i
    have hf := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hfNone : f xy none = xy.2 := congrArg Prod.snd hf
    have hfSome (j : {i : κ // i ≠ a}) : f xy (some j) = xy.1 j :=
      congrFun (congrArg Prod.fst hf) j
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    by_cases hi : i = a
    · subst i
      simp [winnerClockJoin, e, hfNone]
    · simp [winnerClockJoin, hi, e,
        Equiv.optionSubtypeNe_symm_of_ne hi, hfSome]
  rw [hjoin, ← Measure.map_map g.measurable f.measurable]
  rw [show Measure.map f
      ((Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1).prod
        (expMeasure 1)) =
      Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) from
    Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)]
  exact Measure.pi_map_piCongrLeft e (fun _ : κ => expMeasure 1)

private lemma strictClockWin_join_section
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ) (y : ℝ) :
    (fun x : {i : κ // i ≠ a} → ℝ => winnerClockJoin a (y, x)) ⁻¹'
        {E | strictClockWin t a E} =
      Set.pi Set.univ (fun i : {i : κ // i ≠ a} => Ioi (t i.1 / t a * y)) := by
  ext x
  simp only [mem_preimage, mem_setOf_eq, strictClockWin,
    winnerClockJoin, dite_true, Set.mem_pi, mem_univ, true_implies, mem_Ioi]
  constructor
  · intro h i
    have hrel := h i.1 i.2
    simp only [i.2, dite_false] at hrel
    rw [div_mul_eq_mul_div, div_lt_iff₀ (ht a)]
    simpa only [mul_comm] using (div_lt_div_iff₀ (ht a) (ht i.1)).1 hrel
  · intro h b hba
    simp only [hba, dite_false]
    rw [div_lt_div_iff₀ (ht a) (ht b)]
    have hdiv := h ⟨b, hba⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (ht a)] at hdiv
    simpa only [mul_comm] using hdiv

private lemma map_eval_restrict_strictClockWin
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (fun E : κ → ℝ => E a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      ENNReal.ofReal (t a) • expMeasure (1 / t a) := by
  let : ∀ _ : κ, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let reindex := winnerClockJoin a ∘ Prod.swap
  have hreindex : Measurable reindex :=
    (winnerClockJoin_measurable a).comp measurable_swap
  let q := (Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).prod
    (expMeasure 1)
  have hmap : Measure.map reindex q = clockLaw κ := clockReindex_law a
  have hwin := strictClockWin_measurableSet t a
  have hcoord : (fun E : κ → ℝ => E a) ∘ reindex = Prod.snd := by
    funext xy
    simp [reindex, winnerClockJoin]
  have hsectionWin := strictClockWin_join_section t ht a
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne t a
  have hsubsum : (∑ i : {i : κ // i ≠ a}, t i.1) = 1 - t a := by
    linarith
  have hratio : (∑ i : {i : κ // i ≠ a}, t i.1 / t a) =
      1 / t a - 1 := by
    rw [← Finset.sum_div, hsubsum]
    field_simp [(ht a).ne']
  have hypos : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [mem_Iic, not_le] using hy
  have hprod : ∀ᵐ y : ℝ ∂(expMeasure 1),
      (∏ i : {i : κ // i ≠ a},
          expMeasure 1 (Ioi (t i.1 / t a * y))) =
        ENNReal.ofReal (Real.exp (-((1 / t a - 1) * y))) := by
    filter_upwards [hypos] with y hy
    simp_rw [expMeasure_one_Ioi _
      (mul_nonneg (div_nonneg (ht _).le (ht a).le) hy.le)]
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.exp_nonneg (-(t i.1 / t a * y))), ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hratio]
  have hclock :
      Measure.map (fun E : κ → ℝ => E a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        (expMeasure 1).withDensity
          (fun y => ENNReal.ofReal
            (Real.exp (-((1 / t a - 1) * y)))) := by
    rw [← hmap, Measure.restrict_map hreindex hwin,
      Measure.map_map (measurable_pi_apply a) hreindex, hcoord]
    ext s hs
    rw [Measure.map_apply measurable_snd hs,
      Measure.restrict_apply (measurable_snd hs)]
    have hset : MeasurableSet
        (Prod.snd ⁻¹' s ∩
          reindex ⁻¹' {E : κ → ℝ | strictClockWin t a E}) :=
      (measurable_snd hs).inter (hwin.preimage hreindex)
    rw [Measure.prod_apply_symm hset]
    have hsections : ∀ᵐ y : ℝ ∂(expMeasure 1),
        Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)
            ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
              (Prod.snd ⁻¹' s ∩
                reindex ⁻¹' {E : κ → ℝ | strictClockWin t a E})) =
          s.indicator (fun y => ENNReal.ofReal
            (Real.exp (-((1 / t a - 1) * y)))) y := by
      filter_upwards [hprod] with y hpy
      by_cases hys : y ∈ s
      · have hsec :
            (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
                (Prod.snd ⁻¹' s ∩
                  reindex ⁻¹' {E : κ → ℝ | strictClockWin t a E}) =
              Set.pi Set.univ
                (fun i : {i : κ // i ≠ a} => Ioi (t i.1 / t a * y)) := by
            ext x
            simp only [mem_preimage, mem_inter_iff]
            simpa only [reindex, Function.comp_apply, Prod.swap_prod_mk,
              mem_preimage, hys, true_and] using
              Set.ext_iff.mp (hsectionWin y) x
        rw [hsec, Measure.pi_pi, hpy, Set.indicator_of_mem hys]
      · have hsec :
            (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
                (Prod.snd ⁻¹' s ∩
                  reindex ⁻¹' {E : κ → ℝ | strictClockWin t a E}) = ∅ := by
            ext x
            simp [hys]
        rw [hsec, measure_empty, Set.indicator_of_notMem hys]
    rw [lintegral_congr_ae hsections, lintegral_indicator hs,
      ← withDensity_apply _ hs]
  rw [hclock, expMeasure_one_tilt (ht a)]

private theorem clock_min_excess_restrict_factorization
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map
        (fun E : κ → ℝ =>
          (E a / t a, fun i => E i / t i - E a / t a))
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      (ENNReal.ofReal (t a) • expMeasure 1).prod
        (Measure.map (fun r => winnerClockJoin a (0, r))
          (weightedLosingExcessLaw t a)) := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  let reindex := winnerClockJoin a ∘ Prod.swap
  have hreindex : Measurable reindex :=
    (winnerClockJoin_measurable a).comp measurable_swap
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  let q := loseμ.prod (expMeasure 1)
  let P := reindex ⁻¹' {E : κ → ℝ | strictClockWin t a E}
  let J : (({i : κ // i ≠ a} → ℝ) × ℝ) → ℝ × (κ → ℝ) :=
    fun xy =>
      (xy.2 / t a,
        winnerClockJoin a (0, fun i => xy.1 i / t i.1 - xy.2 / t a))
  have hmap : Measure.map reindex q = clockLaw κ := clockReindex_law a
  have hcoordA (xy : ({i : κ // i ≠ a} → ℝ) × ℝ) :
      reindex xy a = xy.2 := by simp [reindex, winnerClockJoin]
  have hcoordNe (xy : ({i : κ // i ≠ a} → ℝ) × ℝ)
      (i : {i : κ // i ≠ a}) : reindex xy i.1 = xy.1 i := by
    simp [reindex, winnerClockJoin, i.2]
  have hwin := strictClockWin_measurableSet t a
  have hP : MeasurableSet P := hwin.preimage hreindex
  have hsectionP := strictClockWin_join_section t ht a
  have hJ : Measurable J := by
    dsimp only [J]
    apply Measurable.prodMk
    · fun_prop
    · exact (winnerClockJoin_measurable a).comp (by fun_prop)
  have horig : Measurable (fun E : κ → ℝ =>
      (E a / t a, fun i => E i / t i - E a / t a)) := by fun_prop
  have hJcomp :
      (fun E : κ → ℝ =>
        (E a / t a, fun i => E i / t i - E a / t a)) ∘ reindex = J := by
    funext xy
    apply Prod.ext
    · simp only [Function.comp_apply, J]
      rw [hcoordA]
    · funext i
      by_cases hi : i = a
      · subst i
        simp [J, winnerClockJoin, hcoordA]
      · simp only [Function.comp_apply, J, winnerClockJoin, hi, dite_false]
        rw [hcoordNe xy ⟨i, hi⟩, hcoordA]
  have hsplit :
      Measure.map
          (fun E : κ → ℝ =>
            (E a / t a, fun i => E i / t i - E a / t a))
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        Measure.map J (q.restrict P) := by
    rw [← hmap, Measure.restrict_map hreindex hwin,
      Measure.map_map horig hreindex, hJcomp]
  have hminLaw :
      Measure.map (fun E : κ → ℝ => E a / t a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        ENNReal.ofReal (t a) • expMeasure 1 := by
    change Measure.map ((fun y : ℝ => y / t a) ∘
      (fun E : κ → ℝ => E a)) _ = _
    rw [← Measure.map_map (g := fun y : ℝ => y / t a)
        (measurable_id.div_const (t a)) (measurable_pi_apply a),
      map_eval_restrict_strictClockWin t ht htotal a,
      Measure.map_smul,
      map_div_expMeasure (ht a)]
  have hminSplit :
      Measure.map
          (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2 / t a)
          (q.restrict P) =
        ENNReal.ofReal (t a) • expMeasure 1 := by
    rw [← hminLaw, ← hmap, Measure.restrict_map hreindex hwin,
      Measure.map_map (g := fun E : κ → ℝ => E a / t a)
        (by fun_prop) hreindex]
    apply Measure.map_congr
    filter_upwards [] with xy
    dsimp only [Function.comp_apply]
    rw [hcoordA]
  rw [hsplit]
  let ρ : Measure ({i : κ // i ≠ a} → ℝ) :=
    weightedLosingExcessLaw t a
  let embed : ({i : κ // i ≠ a} → ℝ) → κ → ℝ :=
    fun r => winnerClockJoin a (0, r)
  let ρfull : Measure (κ → ℝ) := Measure.map embed ρ
  let : IsProbabilityMeasure ρ := by
    dsimp [ρ, weightedLosingExcessLaw]
    infer_instance
  have hembed : Measurable embed :=
    (winnerClockJoin_measurable a).comp
      (measurable_const.prodMk measurable_id)
  let : IsProbabilityMeasure ρfull :=
    Measure.isProbabilityMeasure_map hembed.aemeasurable
  change Measure.map J (q.restrict P) =
    (ENNReal.ofReal (t a) • expMeasure 1).prod ρfull
  apply Measure.ext_prod
  intro s r hs hr
  let first : (({i : κ // i ≠ a} → ℝ) × ℝ) → ℝ :=
    fun xy => xy.2 / t a
  let B : Set (({i : κ // i ≠ a} → ℝ) × ℝ) := first ⁻¹' s ∩ P
  let A : Set (({i : κ // i ≠ a} → ℝ) × ℝ) :=
    J ⁻¹' (s ×ˢ r) ∩ P
  have hfirstMeas : Measurable first := measurable_snd.div_const (t a)
  have hB : MeasurableSet B := (hs.preimage hfirstMeas).inter hP
  have hA : MeasurableSet A := ((hs.prod hr).preimage hJ).inter hP
  have hone : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [mem_Iic, not_le] using hy
  have hsections : ∀ᵐ y : ℝ ∂(expMeasure 1),
      loseμ ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A) =
        ρfull r *
          loseμ ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B) := by
    filter_upwards [hone] with y hy
    by_cases hys : y / t a ∈ s
    · let u : ℝ := y / t a
      let loseMap : ({i : κ // i ≠ a} → ℝ) →
          ({i : κ // i ≠ a} → ℝ) :=
        fun x i => x i / t i.1 - u
      let orth : Set ({i : κ // i ≠ a} → ℝ) :=
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} => Ioi (t i.1 * u))
      let rpre : Set ({i : κ // i ≠ a} → ℝ) := embed ⁻¹' r
      have hu : 0 ≤ u := div_nonneg hy.le (ht a).le
      have hloseMap : Measurable loseMap := by fun_prop
      have hrpre : MeasurableSet rpre := hr.preimage hembed
      have hPsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' P = orth := by
        change (fun x => winnerClockJoin a (y, x)) ⁻¹'
          {E | strictClockWin t a E} = orth
        rw [hsectionP]
        congr 1
        funext i
        congr 1
        dsimp only [u]
        field_simp [(ht a).ne']
      have hAsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A =
            loseMap ⁻¹' rpre ∩ orth := by
        ext x
        have hpiff : (x, y) ∈ P ↔ x ∈ orth :=
          Set.ext_iff.mp hPsec x
        simp only [A, mem_preimage, mem_inter_iff,
          Set.mem_prod, J, rpre, embed, loseMap]
        dsimp only [u]
        simp only [hys, true_and, hpiff]
      have hBsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B = orth := by
        ext x
        have hpiff : (x, y) ∈ P ↔ x ∈ orth :=
          Set.ext_iff.mp hPsec x
        simp only [B, mem_preimage, mem_inter_iff, first]
        simp only [hys, true_and, hpiff]
      have hlaw := map_losing_scaled_excess t ht a hu
      change Measure.map loseMap (loseμ.restrict orth) =
          (∏ i : {i : κ // i ≠ a},
            ENNReal.ofReal (Real.exp (-(t i.1 * u)))) • ρ at hlaw
      have hlawR := congrArg
        (fun μ : Measure ({i : κ // i ≠ a} → ℝ) => μ rpre) hlaw
      dsimp only at hlawR
      rw [Measure.map_apply hloseMap hrpre,
        Measure.restrict_apply (hrpre.preimage hloseMap),
        Measure.smul_apply, smul_eq_mul] at hlawR
      have horthMass : loseμ orth =
          ∏ i : {i : κ // i ≠ a},
            ENNReal.ofReal (Real.exp (-(t i.1 * u))) := by
        dsimp only [loseμ, orth]
        rw [Measure.pi_pi]
        simp_rw [expMeasure_one_Ioi _ (mul_nonneg (ht _).le hu)]
      have hρfull : ρfull r = ρ rpre := by
        dsimp only [ρfull]
        rw [Measure.map_apply hembed hr]
      rw [hAsec, hBsec, hlawR, horthMass, hρfull]
      ac_rfl
    · simp [A, B, J, first, Set.preimage, hys]
  rw [Measure.map_apply hJ (hs.prod hr),
    Measure.restrict_apply ((hs.prod hr).preimage hJ)]
  change q A = _
  rw [Measure.prod_apply_symm hA, lintegral_congr_ae hsections,
    lintegral_const_mul _ (measurable_measure_prodMk_right hB),
    ← Measure.prod_apply_symm hB]
  have hqB : q B = (ENNReal.ofReal (t a) • expMeasure 1) s := by
    rw [← hminSplit, Measure.map_apply hfirstMeas hs,
      Measure.restrict_apply (hs.preimage hfirstMeas)]
  rw [Measure.prod_prod, hqB]
  ac_rfl

private lemma map_weightedLosingExcess_scale
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ) :
    Measure.map
        (fun R : {i : κ // i ≠ a} → ℝ => fun i => t i.1 * R i)
        (weightedLosingExcessLaw t a) =
      Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1 := by
  let (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  rw [weightedLosingExcessLaw,
    Measure.pi_map_pi fun (i : {i : κ // i ≠ a}) =>
      (by fun_prop : AEMeasurable (fun x : ℝ => t i.1 * x) _)]
  simp_rw [map_mul_expMeasure (ht _)]

private lemma winnerClockJoin_law
    {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measure.map (winnerClockJoin a)
        ((expMeasure 1).prod
          (Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1)) =
      clockLaw κ := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  rw [← clockReindex_law a,
    ← Measure.map_map (winnerClockJoin_measurable a) measurable_swap,
    Measure.prod_swap]

/-- Remove the winning amount from all losing clocks and retain a fresh unit
exponential in the winning coordinate. -/
noncomputable def winnerResidualClock
    {κ : Type*} [DecidableEq κ] (t : κ → ℝ) (a : κ)
    (E : κ → ℝ) : κ → ℝ :=
  fun i => if _h : i = a then E a / t a
    else E i - t i * (E a / t a)

lemma winnerResidualClock_measurable
    {κ : Type*} [DecidableEq κ]
    (t : κ → ℝ) (a : κ) :
    Measurable (winnerResidualClock t a) := by
  refine measurable_pi_iff.mpr ?_
  intro i
  by_cases hi : i = a <;>
    simp only [winnerResidualClock, hi, dite_true, dite_false] <;> fun_prop

/-- On a fixed strict-winner cell, the transformed vector is fresh iid
`Exp(1)`, with total mass equal to the winner probability. -/
theorem winnerResidualClock_restrict_law
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (winnerResidualClock t a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      ENNReal.ofReal (t a) • clockLaw κ := by
  let ρ : Measure ({i : κ // i ≠ a} → ℝ) :=
    weightedLosingExcessLaw t a
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  let A : Measure ℝ := ENNReal.ofReal (t a) • expMeasure 1
  let embed : ({i : κ // i ≠ a} → ℝ) → κ → ℝ :=
    fun r => winnerClockJoin a (0, r)
  let norm : (κ → ℝ) → ℝ × (κ → ℝ) := fun E =>
    (E a / t a, fun i => E i / t i - E a / t a)
  let out : (ℝ × (κ → ℝ)) → κ → ℝ := fun sr i =>
    if i = a then sr.1 else t i * sr.2 i
  let loseScale : ({i : κ // i ≠ a} → ℝ) →
      ({i : κ // i ≠ a} → ℝ) := fun R i => t i.1 * R i
  let scale : (ℝ × ({i : κ // i ≠ a} → ℝ)) →
      ℝ × ({i : κ // i ≠ a} → ℝ) := Prod.map id loseScale
  have hnorm : Measurable norm := by fun_prop
  have hout : Measurable out := by
    refine measurable_pi_iff.mpr ?_
    intro i
    by_cases hi : i = a <;>
      simp only [out, hi, ite_true, ite_false] <;> fun_prop
  have hembed : Measurable embed :=
    (winnerClockJoin_measurable a).comp
      (measurable_const.prodMk measurable_id)
  have hloseScale : Measurable loseScale := by fun_prop
  have hscale : Measurable scale := measurable_id.prodMap hloseScale
  have hresidualNorm : winnerResidualClock t a = out ∘ norm := by
    funext E i
    by_cases hi : i = a <;>
      simp [winnerResidualClock, out, norm, hi, mul_sub,
        mul_div_cancel₀ _ (ht i).ne']
  have houtEmbed : out ∘ Prod.map id embed =
      winnerClockJoin a ∘ scale := by
    funext sr i
    by_cases hi : i = a <;>
      simp [out, scale, embed, loseScale, winnerClockJoin, hi]
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  let : IsProbabilityMeasure ρ := by
    dsimp [ρ, weightedLosingExcessLaw]
    infer_instance
  let : IsProbabilityMeasure loseμ := by
    dsimp [loseμ]
    infer_instance
  let : SFinite A := by
    dsimp [A]
    infer_instance
  have hscaleLaw : Measure.map scale (A.prod ρ) = A.prod loseμ := by
    rw [← Measure.map_prod_map A ρ measurable_id hloseScale, Measure.map_id]
    congr 1
    exact map_weightedLosingExcess_scale t ht a
  have hprod : A.prod (Measure.map embed ρ) =
      Measure.map (Prod.map id embed) (A.prod ρ) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map A ρ measurable_id hembed
  calc
    Measure.map (winnerResidualClock t a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        Measure.map out
          (Measure.map norm
            ((clockLaw κ).restrict {E | strictClockWin t a E})) := by
      rw [hresidualNorm]
      exact (Measure.map_map hout hnorm).symm
    _ = Measure.map out (A.prod (Measure.map embed ρ)) := by
      rw [clock_min_excess_restrict_factorization t ht htotal a]
    _ = Measure.map (winnerClockJoin a) (A.prod loseμ) := by
      rw [hprod, Measure.map_map hout (measurable_id.prodMap hembed),
        houtEmbed,
        ← Measure.map_map (winnerClockJoin_measurable a) hscale, hscaleLaw]
    _ = ENNReal.ofReal (t a) • clockLaw κ := by
      change Measure.map (winnerClockJoin a)
        ((ENNReal.ofReal (t a) • expMeasure 1).prod loseμ) = _
      rw [Measure.prod_smul_left,
        Measure.map_smul,
        winnerClockJoin_law a]

@[simp] lemma winnerResidualClock_apply_winner
    {κ : Type*} [DecidableEq κ] (t : κ → ℝ) (a : κ) (E : κ → ℝ) :
    winnerResidualClock t a E a = E a / t a := by
  simp [winnerResidualClock]

/-- The mass of the strict-winner cell. -/
theorem strictClockWin_measure
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    clockLaw κ {E | strictClockWin t a E} = ENNReal.ofReal (t a) := by
  have h := congrArg (fun ν : Measure (κ → ℝ) => ν Set.univ)
    (winnerResidualClock_restrict_law t ht htotal a)
  dsimp only at h
  rw [Measure.map_apply (winnerResidualClock_measurable t a)
      MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one] at h
  exact h

/-- On a fixed winner cell, the scaled minimum has winner mass times
`Exp(1)`. -/
theorem winnerWait_restrict_law
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (fun E : κ → ℝ => E a / t a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      ENNReal.ofReal (t a) • expMeasure 1 := by
  change Measure.map ((fun y : ℝ => y / t a) ∘
    (fun E : κ → ℝ => E a)) _ = _
  rw [← Measure.map_map (g := fun y : ℝ => y / t a)
      (measurable_id.div_const (t a)) (measurable_pi_apply a),
    map_eval_restrict_strictClockWin t ht htotal a,
    Measure.map_smul,
    map_div_expMeasure (ht a)]

/-- Sum of positive channel rates. -/
def rateTotal {κ : Type*} [Fintype κ] (r : κ → ℝ) : ℝ := ∑ i, r i

/-- Normalize a positive finite rate vector. -/
def normalizedRate {κ : Type*} [Fintype κ]
    (r : κ → ℝ) (i : κ) : ℝ := r i / rateTotal r

lemma rateTotal_pos {κ : Type*} [Fintype κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) : 0 < rateTotal r := by
  classical
  unfold rateTotal
  exact Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty

lemma normalizedRate_pos {κ : Type*} [Fintype κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (i : κ) :
    0 < normalizedRate r i :=
  div_pos (hr i) (rateTotal_pos r hr)

lemma sum_normalizedRate {κ : Type*} [Fintype κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) :
    ∑ i, normalizedRate r i = 1 := by
  rw [show (∑ i, normalizedRate r i) =
      rateTotal r / rateTotal r by
    simp only [normalizedRate, ← Finset.sum_div, rateTotal]]
  exact div_self (rateTotal_pos r hr).ne'

lemma strictClockWin_normalized_iff
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i)
    (E : κ → ℝ) (a : κ) :
    strictClockWin (normalizedRate r) a E ↔ strictClockWin r a E := by
  have hR := rateTotal_pos r hr
  have hscale (i : κ) :
      E i / normalizedRate r i = rateTotal r * (E i / r i) := by
    unfold normalizedRate
    field_simp [(hr i).ne', hR.ne']
  unfold strictClockWin
  constructor
  · intro h b hba
    have hb := h b hba
    rw [hscale a, hscale b] at hb
    exact lt_of_mul_lt_mul_left hb hR.le
  · intro h b hba
    rw [hscale a, hscale b]
    exact mul_lt_mul_of_pos_left (h b hba) hR

/-- Winner probability for unnormalized positive rates. -/
theorem strictClockWin_measure_of_rates
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (a : κ) :
    clockLaw κ {E | strictClockWin r a E} =
      ENNReal.ofReal (r a / rateTotal r) := by
  have hset : {E : κ → ℝ | strictClockWin r a E} =
      {E | strictClockWin (normalizedRate r) a E} := by
    ext E
    exact (strictClockWin_normalized_iff r hr E a).symm
  rw [hset]
  simpa [normalizedRate] using
    strictClockWin_measure (normalizedRate r)
      (normalizedRate_pos r hr) (sum_normalizedRate r hr) a

/-- Fresh residual-vector law for unnormalized positive rates. -/
theorem winnerResidualClock_restrict_law_of_rates
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (a : κ) :
    Measure.map (winnerResidualClock (normalizedRate r) a)
        ((clockLaw κ).restrict {E | strictClockWin r a E}) =
      ENNReal.ofReal (r a / rateTotal r) • clockLaw κ := by
  have hset : {E : κ → ℝ | strictClockWin r a E} =
      {E | strictClockWin (normalizedRate r) a E} := by
    ext E
    exact (strictClockWin_normalized_iff r hr E a).symm
  rw [hset]
  simpa [normalizedRate] using
    winnerResidualClock_restrict_law (normalizedRate r)
      (normalizedRate_pos r hr) (sum_normalizedRate r hr) a

/-- Joint winner/holding law: on winner `a`, physical waiting time has
`Exp(sum r)` law and the cell mass is `r a / sum r`. -/
theorem winnerWait_restrict_law_of_rates
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (a : κ) :
    Measure.map (fun E : κ → ℝ => E a / r a)
        ((clockLaw κ).restrict {E | strictClockWin r a E}) =
      ENNReal.ofReal (r a / rateTotal r) • expMeasure (rateTotal r) := by
  let R := rateTotal r
  let t := normalizedRate r
  have hR : 0 < R := rateTotal_pos r hr
  have ht : ∀ i, 0 < t i := normalizedRate_pos r hr
  have htotal : ∑ i, t i = 1 := sum_normalizedRate r hr
  have hset : {E : κ → ℝ | strictClockWin r a E} =
      {E | strictClockWin t a E} := by
    ext E
    exact (strictClockWin_normalized_iff r hr E a).symm
  have hfun : (fun E : κ → ℝ => E a / r a) =
      (fun y : ℝ => y / R) ∘ (fun E : κ → ℝ => E a / t a) := by
    funext E
    dsimp only [Function.comp_apply, R, t, normalizedRate]
    have hR' : rateTotal r ≠ 0 := hR.ne'
    field_simp [(hr a).ne', hR']
  rw [hset, hfun,
    ← Measure.map_map (g := fun y : ℝ => y / R) (measurable_id.div_const R)
      (by fun_prop : Measurable (fun E : κ → ℝ => E a / t a)),
    winnerWait_restrict_law t ht htotal a,
    Measure.map_smul,
    map_div_expMeasure_one hR]
  simp [R, t, normalizedRate]

/-- Survival function of the minimum of the weighted clocks. -/
theorem raceSurvival_measure
    {κ : Type*} [Fintype κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i)
    {u : ℝ} (hu : 0 ≤ u) :
    clockLaw κ {E | ∀ i, u < E i / r i} =
      ENNReal.ofReal (Real.exp (-(rateTotal r * u))) := by
  let : ∀ _ : κ, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  have hset : {E : κ → ℝ | ∀ i, u < E i / r i} =
      Set.pi Set.univ (fun i => Ioi (r i * u)) := by
    ext E
    simp only [mem_setOf_eq, Set.mem_pi, mem_univ, true_implies, mem_Ioi]
    exact forall_congr' fun i => (lt_div_iff₀ (hr i)).trans (by ring_nf)
  rw [clockLaw, hset, Measure.pi_pi]
  simp_rw [expMeasure_one_Ioi _ (mul_nonneg (hr _).le hu)]
  rw [← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.exp_nonneg (-(r i * u))),
    ← Real.exp_sum]
  congr 2
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
  rfl

end Ripple.Kurtz.StrongApprox.ExponentialRace

end
