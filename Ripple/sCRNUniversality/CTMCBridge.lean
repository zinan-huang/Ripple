import Ripple.CTMC.CTMC
import Ripple.sCRNUniversality.Stochastic.MassAction.Completion
import Ripple.sCRNUniversality.Stochastic.MassAction.RaceLaw
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.BorelCantelli
import Ripple.sCRNUniversality.RegisterMachine.Clocked.Theorem
import Ripple.sCRNUniversality.ClockedCTM.TMtoCTM

namespace Ripple.sCRNUniversality.CTMCBridge

open MeasureTheory ProbabilityTheory Preorder Classical
open Stochastic Stochastic.MassAction
open scoped ENNReal BigOperators

universe u v

/-- Independent unit-rate exponential clocks. -/
noncomputable def unitClockLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => expMeasure 1)

instance unitClockLaw_isProbabilityMeasure :
    IsProbabilityMeasure unitClockLaw := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  unfold unitClockLaw
  infer_instance

theorem unitClockLaw_map_eval (n : ℕ) :
    unitClockLaw.map (fun e : ℕ → ℝ => e n) = expMeasure 1 := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  exact Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) n

theorem unitClockLaw_eval (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    unitClockLaw {e | e n ∈ B} = expMeasure 1 B := by
  change unitClockLaw ((fun e : ℕ → ℝ => e n) ⁻¹' B) = _
  rw [← Measure.map_apply (measurable_pi_apply n) hB, unitClockLaw_map_eval]

theorem unitClockLaw_cylinder (F : Finset ℕ) (B : ℕ → Set ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i)) :
    unitClockLaw (Set.pi (F : Set ℕ) B) = ∏ i ∈ F, expMeasure 1 (B i) := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  exact Measure.infinitePi_pi (fun _ : ℕ => expMeasure 1) hB

/-- The exponential survival function, including the endpoint at zero. -/
theorem expMeasure_Ioi_of_nonneg {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    expMeasure r (Set.Ioi t) = ENNReal.ofReal (Real.exp (-(r * t))) := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hIic : (expMeasure r).real (Set.Iic t) = 1 - Real.exp (-(r * t)) := by
    rw [← cdf_eq_real (expMeasure r) t, cdf_expMeasure_eq hr t, if_pos ht]
  have hIoi : (expMeasure r).real (Set.Ioi t) = Real.exp (-(r * t)) := by
    rw [show Set.Ioi t = (Set.Iic t)ᶜ by ext x; simp]
    rw [measureReal_compl measurableSet_Iic, hIic]
    simp
  calc
    expMeasure r (Set.Ioi t) =
        ENNReal.ofReal ((expMeasure r).real (Set.Ioi t)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal (Real.exp (-(r * t))) := congrArg ENNReal.ofReal hIoi

/-- Dividing a unit exponential clock by a positive rate gives its exponential tail. -/
theorem unitClockLaw_div_tail (n : ℕ) (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
    unitClockLaw {e | t < e n / r} =
      ENNReal.ofReal (Real.exp (-(r * t))) := by
  have hset : {e : ℕ → ℝ | t < e n / r} =
      {e | e n ∈ Set.Ioi (t * r)} := by
    ext e
    exact lt_div_iff₀ hr
  rw [hset, unitClockLaw_eval n _ measurableSet_Ioi,
    expMeasure_Ioi_of_nonneg (by norm_num : (0 : ℝ) < 1)
      (mul_nonneg ht hr.le)]
  simp only [one_mul, mul_comm t r]

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

/-- A reaction-label trajectory and an independent sequence of unit clocks. -/
abbrev TimedΩ := ((n : ℕ) → Option N.I) × (ℕ → ℝ)

/-- Product extension for the marked jump-and-hold construction.
Physical holding times are scaled by the current propensity. -/
noncomputable def timedLaw (hPos : N.hasPositiveRates) (z0 : State S) :
    Measure (TimedΩ N) :=
  (rawLaw N hPos z0).prod unitClockLaw

instance timedLaw_isProbabilityMeasure (hPos : N.hasPositiveRates) (z0 : State S) :
    IsProbabilityMeasure (timedLaw N hPos z0) := by
  letI := rawLaw_isProbabilityMeasure N hPos z0
  unfold timedLaw
  infer_instance

variable (hPos : N.hasPositiveRates) (z0 : State S)

/-- The complete label path is independent of the complete sequence of unit clocks. -/
theorem timedLaw_labels_clocks (A : Set ((n : ℕ) → Option N.I))
    (D : Set (ℕ → ℝ)) :
    timedLaw N hPos z0 {η | η.1 ∈ A ∧ η.2 ∈ D} =
      rawLaw N hPos z0 A * unitClockLaw D := by
  change (rawLaw N hPos z0).prod unitClockLaw (A ×ˢ D) = _
  exact Measure.prod_prod A D

/-- All label events, including the headline events, retain their original probabilities. -/
theorem timedLaw_labels (A : Set ((n : ℕ) → Option N.I)) :
    timedLaw N hPos z0 {η | η.1 ∈ A} = rawLaw N hPos z0 A := by
  have h := timedLaw_labels_clocks N hPos z0 A Set.univ
  simpa only [Set.mem_univ, and_true, measure_univ, mul_one] using h

/-- Equality of the label-path marginal with the existing Ionescu--Tulcea law. -/
theorem timedLaw_map_labels :
    (timedLaw N hPos z0).map Prod.fst = rawLaw N hPos z0 := by
  simp only [timedLaw, Measure.map_fst_prod, measure_univ, one_smul]

/-- Joint probabilities with any finite family of exponential-clock observations. -/
theorem timedLaw_clock_cylinder (A : Set ((n : ℕ) → Option N.I))
    (F : Finset ℕ) (B : ℕ → Set ℝ) (hB : ∀ i ∈ F, MeasurableSet (B i)) :
    timedLaw N hPos z0 {η | η.1 ∈ A ∧ ∀ i ∈ F, η.2 i ∈ B i} =
      rawLaw N hPos z0 A * ∏ i ∈ F, expMeasure 1 (B i) := by
  change timedLaw N hPos z0 {η | η.1 ∈ A ∧ η.2 ∈ Set.pi (F : Set ℕ) B} = _
  rw [timedLaw_labels_clocks, unitClockLaw_cylinder F B hB]

theorem timedLaw_labels_divClock_tail
    (A : Set ((n : ℕ) → Option N.I)) (n : ℕ)
    (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
    timedLaw N hPos z0 {η | η.1 ∈ A ∧ t < η.2 n / r} =
      rawLaw N hPos z0 A * ENNReal.ofReal (Real.exp (-(r * t))) := by
  change timedLaw N hPos z0
      {η | η.1 ∈ A ∧ η.2 ∈ {e : ℕ → ℝ | t < e n / r}} = _
  rw [timedLaw_labels_clocks N hPos z0 A {e : ℕ → ℝ | t < e n / r},
    unitClockLaw_div_tail n r t hr ht]

/-- Total mass-action firing rate as a real number. -/
noncomputable def totalRate (z : State S) : ℝ :=
  (N.totalPropensity z : ℝ)

theorem totalRate_pos (hPos : N.hasPositiveRates) (z : State S) (hNT : ¬N.Terminal z) :
    0 < totalRate N z := by
  change (0 : ℝ) < (N.totalPropensity z : ℝ)
  exact_mod_cast totalPropensity_pos_of_nonTerminal N hPos hNT

/-- The next reaction mark and the scaled holding time have the mass-action
jump-and-hold law on every label-prefix event with a fixed current state. -/
theorem timedLaw_prefix_next_holding_tail
    (n : ℕ) (A : Set ((i : Finset.Iic n) → Option N.I)) (z : State S)
    (hA : ∀ p ∈ A, prefixToState N z0 n p = z)
    (hNT : ¬N.Terminal z) (o : Option N.I) (t : ℝ) (ht : 0 ≤ t) :
    timedLaw N hPos z0
      {η | frestrictLe n η.1 ∈ A ∧ η.1 (n + 1) = o ∧
        t < η.2 n / totalRate N (pathState N z0 η.1 n)} =
      rawLaw N hPos z0 {ω | frestrictLe n ω ∈ A} *
        massActionPMF N hPos z o *
        ENNReal.ofReal (Real.exp (-(totalRate N z * t))) := by
  let E : Set ((k : ℕ) → Option N.I) :=
    {ω | frestrictLe n ω ∈ A ∧ ω (n + 1) = o}
  have hstate (ω : (k : ℕ) → Option N.I) (hω : frestrictLe n ω ∈ A) :
      pathState N z0 ω n = z :=
    (prefixToState_eq_pathState N z0 ω n).symm.trans (hA _ hω)
  have hset :
      {η : TimedΩ N | frestrictLe n η.1 ∈ A ∧ η.1 (n + 1) = o ∧
        t < η.2 n / totalRate N (pathState N z0 η.1 n)} =
      {η | η.1 ∈ E ∧ t < η.2 n / totalRate N z} := by
    ext η
    constructor
    · rintro ⟨ha, ho, htail⟩
      refine ⟨⟨ha, ho⟩, ?_⟩
      simpa only [hstate η.1 ha] using htail
    · rintro ⟨⟨ha, ho⟩, htail⟩
      refine ⟨ha, ho, ?_⟩
      simpa only [hstate η.1 ha] using htail
  rw [hset, timedLaw_labels_divClock_tail N hPos z0 E n
    (totalRate N z) t (totalRate_pos N hPos z hNT) ht]
  change rawLaw N hPos z0 {ω | frestrictLe n ω ∈ A ∧ ω (n + 1) = o} *
    ENNReal.ofReal (Real.exp (-(totalRate N z * t))) = _
  rw [rawLaw_prefix_next N hPos z0 n A z hA o]

theorem massActionPMF_none_ne_zero_terminal (z : State S)
    (h : massActionPMF N hPos z none ≠ 0) : N.Terminal z := by
  classical
  by_contra hNT
  apply h
  change massActionWeight N hPos z none = 0
  simp only [massActionWeight, dif_neg hNT]

theorem massActionPMF_some_ne_zero_enabled (z : State S) (i : N.I)
    (h : massActionPMF N hPos z (some i) ≠ 0) : N.EnabledAt z i := by
  classical
  by_contra hNE
  apply h
  change massActionWeight N hPos z (some i) = 0
  by_cases hT : N.Terminal z
  · simp only [massActionWeight, dif_pos hT]
  · simp only [massActionWeight, dif_neg hT,
      jumpProbAt_eq_zero_of_not_enabled N hNE]
    rw [← ENNReal.coe_nnratCast, NNRat.cast_zero, ENNReal.coe_zero]

/-- Sanitization is inactive whenever the sampled reaction mark has nonzero probability. -/
theorem pathFired_eq_label_of_mass_ne_zero
    (ω : (k : ℕ) → Option N.I) (n : ℕ)
    (hmass : massActionPMF N hPos (pathState N z0 ω n) (ω (n + 1)) ≠ 0) :
    pathFired N z0 ω n = ω (n + 1) := by
  classical
  cases hω : ω (n + 1) with
  | none =>
      have hT : N.Terminal (pathState N z0 ω n) :=
        massActionPMF_none_ne_zero_terminal N hPos _
          (by simpa only [hω] using hmass)
      simp only [pathFired, dif_pos hT, hω]
  | some i =>
      have hE : N.EnabledAt (pathState N z0 ω n) i :=
        massActionPMF_some_ne_zero_enabled N hPos _ i
          (by simpa only [hω] using hmass)
      have hNT : ¬N.Terminal (pathState N z0 ω n) := fun hT => hT i hE
      simp only [pathFired, dif_neg hNT, hω,
        fireOptionSanitized_of_enabled N _ i hNT hE]

theorem timedLaw_null_label :
    timedLaw N hPos z0
      {η | ∃ n, massActionPMF N hPos (pathState N z0 η.1 n) (η.1 (n + 1)) = 0} = 0 := by
  change timedLaw N hPos z0
    {η | η.1 ∈ {ω | ∃ n,
      massActionPMF N hPos (pathState N z0 ω n) (ω (n + 1)) = 0}} = 0
  rw [timedLaw_labels]
  have hprefix (ω : (k : ℕ) → Option N.I) (n : ℕ) :
      prefixToState N z0 n (frestrictLe n ω) = pathState N z0 ω n := by
    exact prefixToState_eq_pathState N z0 ω n
  simpa only [hprefix] using rawLaw_null_label N hPos z0

/-- Almost surely, the raw labels are exactly the reaction labels of the valid CRN path. -/
theorem timedLaw_fired_eq_label_ae :
    ∀ᵐ η ∂timedLaw N hPos z0, ∀ n,
      pathFired N z0 η.1 n = η.1 (n + 1) := by
  have hnonnull : ∀ᵐ η ∂timedLaw N hPos z0, ¬ ∃ n,
      massActionPMF N hPos (pathState N z0 η.1 n) (η.1 (n + 1)) = 0 := by
    rw [ae_iff]
    simpa only [not_not] using timedLaw_null_label N hPos z0
  filter_upwards [hnonnull] with η hη n
  exact pathFired_eq_label_of_mass_ne_zero N hPos z0 η.1 n
    (fun h => hη ⟨n, h⟩)

end Ripple.sCRNUniversality.CTMCBridge

namespace Ripple.sCRNUniversality.CTMCBridge

open MeasureTheory ProbabilityTheory Preorder Classical
open Stochastic Stochastic.MassAction
open scoped ENNReal BigOperators

/-! ## Independent clocks and occupation-time expectations -/

/-- A unit exponential is strictly positive almost surely. -/
theorem expMeasure_one_pos_ae :
    ∀ᵐ x : ℝ ∂ProbabilityTheory.expMeasure 1, 0 < x := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hcdf := ProbabilityTheory.cdf_expMeasure_eq
    (by norm_num : (0 : ℝ) < 1) 0
  have hreal : (ProbabilityTheory.expMeasure 1).real (Set.Iic 0) = 0 := by
    rw [← ProbabilityTheory.cdf_eq_real (ProbabilityTheory.expMeasure 1) 0]
    simpa using hcdf
  have hzero : ProbabilityTheory.expMeasure 1 (Set.Iic 0) = 0 := by
    calc
      ProbabilityTheory.expMeasure 1 (Set.Iic 0) =
          ENNReal.ofReal ((ProbabilityTheory.expMeasure 1).real (Set.Iic 0)) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = 0 := by rw [hreal, ENNReal.ofReal_zero]
  have hnot : ∀ᵐ x : ℝ ∂ProbabilityTheory.expMeasure 1, x ∉ Set.Iic 0 :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hnot] with x hx
  exact lt_of_not_ge hx

/-- The nonnegative extended-real mean of a unit exponential is one. -/
theorem lintegral_expMeasure_one :
    ∫⁻ x : ℝ, ENNReal.ofReal x ∂ProbabilityTheory.expMeasure 1 = 1 := by
  have hnonneg :
      0 ≤ᵐ[ProbabilityTheory.expMeasure 1] (fun x : ℝ => x) :=
    expMeasure_one_pos_ae.mono fun _ hx => hx.le
  have hmean := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (ProbabilityTheory.integrable_id_expMeasure (by norm_num : (0 : ℝ) < 1))
    hnonneg
  rw [ProbabilityTheory.integral_expMeasure_id (by norm_num : (0 : ℝ) < 1),
    inv_one, ENNReal.ofReal_one] at hmean
  exact hmean.symm

/-- Every clock coordinate is strictly positive almost surely. -/
theorem unitClock_pos_ae (n : ℕ) :
    ∀ᵐ e ∂unitClockLaw, 0 < e n := by
  have hpos : ∀ᵐ x : ℝ ∂unitClockLaw.map (fun e => e n), 0 < x := by
    rw [unitClockLaw_map_eval]
    exact expMeasure_one_pos_ae
  exact MeasureTheory.ae_of_ae_map (measurable_pi_apply n).aemeasurable hpos

theorem unitClock_all_pos_ae :
    ∀ᵐ e ∂unitClockLaw, ∀ n : ℕ, 0 < e n :=
  ae_all_iff.2 unitClock_pos_ae

/-- Every clock coordinate has nonnegative mean one. -/
theorem lintegral_unitClock (n : ℕ) :
    ∫⁻ e, ENNReal.ofReal (e n) ∂unitClockLaw = 1 := by
  calc
    (∫⁻ e, ENNReal.ofReal (e n) ∂unitClockLaw) =
        ∫⁻ x : ℝ, ENNReal.ofReal x ∂unitClockLaw.map (fun e => e n) :=
      (MeasureTheory.lintegral_map measurable_id.ennreal_ofReal
        (measurable_pi_apply n)).symm
    _ = ∫⁻ x : ℝ, ENNReal.ofReal x ∂ProbabilityTheory.expMeasure 1 := by
      rw [unitClockLaw_map_eval]
    _ = 1 := lintegral_expMeasure_one

/-- A nonnegative path-dependent weight times each independent unit clock. -/
noncomputable def clockedSum {α : Type*}
    (w : ℕ → α → ℝ≥0∞) (u : α × (ℕ → ℝ)) : ℝ≥0∞ :=
  ∑' n, w n u.1 * ENNReal.ofReal (u.2 n)

theorem measurable_clockedSum {α : Type*} [MeasurableSpace α]
    (w : ℕ → α → ℝ≥0∞) (hw : ∀ n, Measurable (w n)) :
    Measurable (clockedSum w) := by
  have hc (n : ℕ) :
      Measurable (fun e : ℕ → ℝ => ENNReal.ofReal (e n)) :=
    (measurable_pi_apply n).ennreal_ofReal
  exact Measurable.tsum fun n =>
    ((hw n).comp measurable_fst).mul ((hc n).comp measurable_snd)

/-- Tonelli's bridge. No finiteness of the expectation is assumed. -/
theorem lintegral_clockedSum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : ℕ → α → ℝ≥0∞)
    (hw : ∀ n, Measurable (w n)) :
    (∫⁻ u, clockedSum w u ∂μ.prod unitClockLaw) =
      ∫⁻ ω, ∑' n, w n ω ∂μ := by
  have hc (n : ℕ) :
      Measurable (fun e : ℕ → ℝ => ENNReal.ofReal (e n)) :=
    (measurable_pi_apply n).ennreal_ofReal
  have hm (n : ℕ) :
      Measurable (fun u : α × (ℕ → ℝ) =>
        w n u.1 * ENNReal.ofReal (u.2 n)) :=
    ((hw n).comp measurable_fst).mul ((hc n).comp measurable_snd)
  calc
    (∫⁻ u, clockedSum w u ∂μ.prod unitClockLaw) =
        ∑' n, ∫⁻ u : α × (ℕ → ℝ),
          w n u.1 * ENNReal.ofReal (u.2 n) ∂μ.prod unitClockLaw :=
      MeasureTheory.lintegral_tsum fun n => (hm n).aemeasurable
    _ = ∑' n, ∫⁻ ω, w n ω ∂μ := by
      apply tsum_congr
      intro n
      rw [MeasureTheory.lintegral_prod_mul (hw n).aemeasurable (hc n).aemeasurable,
        lintegral_unitClock, mul_one]
    _ = ∫⁻ ω, ∑' n, w n ω ∂μ :=
      (MeasureTheory.lintegral_tsum fun n => (hw n).aemeasurable).symm

/-- Finite occupation expectation gives finite realized clocked occupation almost surely. -/
theorem clockedSum_lt_top_ae {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : ℕ → α → ℝ≥0∞)
    (hw : ∀ n, Measurable (w n))
    (hfin : (∫⁻ ω, ∑' n, w n ω ∂μ) ≠ ⊤) :
    ∀ᵐ u ∂μ.prod unitClockLaw, clockedSum w u < ⊤ := by
  apply MeasureTheory.ae_lt_top (measurable_clockedSum w hw)
  rw [lintegral_clockedSum μ w hw]
  exact hfin

section MassActionTime

universe uT vT
variable {S : Type uT} [Fintype S] [DecidableEq S]
variable (N : Network.{uT, vT} S) [DecidableEq N.I]

/-- The clock marginal remains the iid unit-exponential law. -/
theorem timedLaw_map_clocks (hPos : N.hasPositiveRates) (z0 : State S) :
    (timedLaw N hPos z0).map Prod.snd = unitClockLaw := by
  letI : IsProbabilityMeasure (rawLaw N hPos z0) :=
    rawLaw_isProbabilityMeasure N hPos z0
  exact (MeasureTheory.measurePreserving_snd
    (μ := rawLaw N hPos z0) (ν := unitClockLaw)).map_eq

theorem timedLaw_clocks_pos_ae (hPos : N.hasPositiveRates) (z0 : State S) :
    ∀ᵐ u ∂timedLaw N hPos z0, ∀ n : ℕ, 0 < u.2 n := by
  have hpos :
      ∀ᵐ e ∂(timedLaw N hPos z0).map Prod.snd, ∀ n : ℕ, 0 < e n := by
    rw [timedLaw_map_clocks N hPos z0]
    exact unitClock_all_pos_ae
  exact MeasureTheory.ae_of_ae_map measurable_snd.aemeasurable hpos

/-- The mean holding time uses the extended-real reciprocal, hence is infinite at rate zero. -/
noncomputable def meanHolding (z0 : State S) (n : ℕ)
    (ω : (k : ℕ) → Option N.I) : ℝ≥0∞ :=
  (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞)⁻¹

theorem measurable_meanHolding (z0 : State S) (n : ℕ) :
    Measurable (meanHolding N z0 n) := by
  refine measurable_of_frestrictLe N n _ ?_
  intro ω ω' h
  have hstate : pathState N z0 ω n = pathState N z0 ω' n := by
    rw [← prefixToState_eq_pathState N z0 ω n,
      ← prefixToState_eq_pathState N z0 ω' n]
    exact congrArg (prefixToState N z0 n) h
  simp only [meanHolding, hstate]

/-- An exponential holding time, as an extended nonnegative random variable. -/
noncomputable def holdingTime (z0 : State S) (n : ℕ) (u : TimedΩ N) : ℝ≥0∞ :=
  meanHolding N z0 n u.1 * ENNReal.ofReal (u.2 n)

/-- Rate zero means an infinite wait on the positive-clock event. -/
theorem holdingTime_eq_top_of_rate_eq_zero (z0 : State S) (n : ℕ) (u : TimedΩ N)
    (hRate : N.totalPropensity (pathState N z0 u.1 n) = 0)
    (hclock : 0 < u.2 n) :
    holdingTime N z0 n u = ⊤ := by
  have hc : ENNReal.ofReal (u.2 n) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hclock
  have hzero : ((0 : ℚ≥0) : ℝ≥0∞) = 0 := by
    rw [← ENNReal.coe_nnratCast, NNRat.cast_zero, ENNReal.coe_zero]
  simp only [holdingTime, meanHolding, hRate, hzero,
    ENNReal.inv_zero, ENNReal.top_mul hc]

theorem measurable_holdingTime (z0 : State S) (n : ℕ) :
    Measurable (holdingTime N z0 n) := by
  have hc :
      Measurable (fun e : ℕ → ℝ => ENNReal.ofReal (e n)) :=
    (measurable_pi_apply n).ennreal_ofReal
  exact ((measurable_meanHolding N z0 n).comp measurable_fst).mul
    (hc.comp measurable_snd)

theorem lintegral_holdingTime (hPos : N.hasPositiveRates)
    (z0 : State S) (n : ℕ) :
    (∫⁻ u, holdingTime N z0 n u ∂timedLaw N hPos z0) =
      ∫⁻ ω, meanHolding N z0 n ω ∂rawLaw N hPos z0 := by
  have hc :
      Measurable (fun e : ℕ → ℝ => ENNReal.ofReal (e n)) :=
    (measurable_pi_apply n).ennreal_ofReal
  change (∫⁻ u, meanHolding N z0 n u.1 * ENNReal.ofReal (u.2 n)
      ∂(rawLaw N hPos z0).prod unitClockLaw) = _
  rw [MeasureTheory.lintegral_prod_mul
    (measurable_meanHolding N z0 n).aemeasurable hc.aemeasurable,
    lintegral_unitClock, mul_one]

/-- Sum of the first k holding times. On positive-clock paths it is infinite if a requested firing lies after absorption. -/
noncomputable def jumpTime (z0 : State S) (k : ℕ) (u : TimedΩ N) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range k, holdingTime N z0 n u

theorem lintegral_jumpTime (hPos : N.hasPositiveRates)
    (z0 : State S) (k : ℕ) :
    (∫⁻ u, jumpTime N z0 k u ∂timedLaw N hPos z0) =
      ∫⁻ ω, ∑ n ∈ Finset.range k, meanHolding N z0 n ω ∂rawLaw N hPos z0 := by
  calc
    (∫⁻ u, jumpTime N z0 k u ∂timedLaw N hPos z0) =
        ∑ n ∈ Finset.range k,
          ∫⁻ u, holdingTime N z0 n u ∂timedLaw N hPos z0 :=
      MeasureTheory.lintegral_finsetSum (Finset.range k)
        (fun n _ => measurable_holdingTime N z0 n)
    _ = ∑ n ∈ Finset.range k,
        ∫⁻ ω, meanHolding N z0 n ω ∂rawLaw N hPos z0 := by
      apply Finset.sum_congr rfl
      intro n _
      exact lintegral_holdingTime N hPos z0 n
    _ = ∫⁻ ω, ∑ n ∈ Finset.range k, meanHolding N z0 n ω
        ∂rawLaw N hPos z0 :=
      (MeasureTheory.lintegral_finsetSum (Finset.range k)
        (fun n _ => measurable_meanHolding N z0 n)).symm

/-- Clocked occupation of a label-path mask. The headline masks are initial segments. -/
noncomputable def occupationTime (z0 : State S)
    (active : ℕ → ((k : ℕ) → Option N.I) → Prop) (u : TimedΩ N) : ℝ≥0∞ :=
  clockedSum
    (fun n => {ω | active n ω}.indicator (meanHolding N z0 n)) u

theorem occupationTime_eq_tsum (z0 : State S)
    (active : ℕ → ((k : ℕ) → Option N.I) → Prop) (u : TimedΩ N) :
    occupationTime N z0 active u =
      ∑' n, if active n u.1 then holdingTime N z0 n u else 0 := by
  classical
  unfold occupationTime clockedSum
  apply tsum_congr
  intro n
  by_cases hn : active n u.1
  · simp [Set.indicator_apply, hn, holdingTime]
  · simp [Set.indicator_apply, hn]

theorem measurable_occupationTime (z0 : State S)
    (active : ℕ → ((k : ℕ) → Option N.I) → Prop)
    (hactive : ∀ n, MeasurableSet {ω | active n ω}) :
    Measurable (occupationTime N z0 active) :=
  measurable_clockedSum _
    (fun n => (measurable_meanHolding N z0 n).indicator (hactive n))

/-- Exact occupation-time identity, with the same inverse-propensity integrand as expTime. -/
theorem lintegral_occupationTime (hPos : N.hasPositiveRates)
    (z0 : State S) (active : ℕ → ((k : ℕ) → Option N.I) → Prop)
    (hactive : ∀ n, MeasurableSet {ω | active n ω}) :
    (∫⁻ u, occupationTime N z0 active u ∂timedLaw N hPos z0) =
      ∫⁻ ω, ∑' n,
        (if active n ω then
          (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞)⁻¹
        else 0) ∂rawLaw N hPos z0 := by
  classical
  have h := lintegral_clockedSum (rawLaw N hPos z0)
    (fun n => {ω | active n ω}.indicator (meanHolding N z0 n))
    (fun n => (measurable_meanHolding N z0 n).indicator (hactive n))
  simpa only [occupationTime, timedLaw, meanHolding,
    Set.indicator_apply, Set.mem_setOf_eq] using h

theorem occupationTime_lt_top_ae (hPos : N.hasPositiveRates)
    (z0 : State S) (active : ℕ → ((k : ℕ) → Option N.I) → Prop)
    (hactive : ∀ n, MeasurableSet {ω | active n ω})
    (hfin :
      (∫⁻ ω, ∑' n, (if active n ω then
        (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞)⁻¹ else 0)
        ∂rawLaw N hPos z0) ≠ ⊤) :
    ∀ᵐ u ∂timedLaw N hPos z0, occupationTime N z0 active u < ⊤ := by
  apply MeasureTheory.ae_lt_top (measurable_occupationTime N z0 active hactive)
  rw [lintegral_occupationTime N hPos z0 active hactive]
  exact hfin

end MassActionTime

section HoldingTimeScaling

universe uH vH
variable {S : Type uH} [Fintype S] [DecidableEq S]
variable (N : Network.{uH, vH} S) [DecidableEq N.I]

/-- The real and extended-nonnegative casts of the total propensity agree. -/
theorem ofReal_totalRate (z : State S) :
    ENNReal.ofReal (totalRate N z) = (N.totalPropensity z : ℝ≥0∞) := by
  change ENNReal.ofReal (((N.totalPropensity z : NNReal) : ℝ)) =
    ((N.totalPropensity z : NNReal) : ℝ≥0∞)
  exact ENNReal.ofReal_coe_nnreal

/-- The extended holding time agrees with the real scaled clock whenever the rate is
positive. No sign hypothesis on the sampled clock is needed. -/
theorem holdingTime_eq_ofReal_div (z0 : State S) (n : ℕ) (u : TimedΩ N)
    (hRate : 0 < N.totalPropensity (pathState N z0 u.1 n)) :
    holdingTime N z0 n u =
      ENNReal.ofReal (u.2 n / totalRate N (pathState N z0 u.1 n)) := by
  have hr : 0 < totalRate N (pathState N z0 u.1 n) := by
    change (0 : ℝ) < (N.totalPropensity (pathState N z0 u.1 n) : ℝ)
    exact_mod_cast hRate
  rw [ENNReal.ofReal_div_of_pos hr, ofReal_totalRate N]
  simp only [holdingTime, meanHolding, div_eq_mul_inv, mul_comm]

end HoldingTimeScaling

/-! ## Bounded-rate nonexplosion -/

open Filter

/-- Infinitely many independent unit clocks exceed one, so their sum is infinite. -/
theorem unitClock_sum_eq_top_ae :
    ∀ᵐ e ∂unitClockLaw, (∑' n : ℕ, ENNReal.ofReal (e n)) = ⊤ := by
  let A : ℕ → Set (ℕ → ℝ) := fun n => {e | 1 < e n}
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurable_pi_apply n) measurableSet_Ioi
  have hInd : iIndepSet A unitClockLaw := by
    apply (iIndepSet_iff_meas_biInter hAm).2
    intro F
    have hset : (⋂ i ∈ F, A i) =
        Set.pi (F : Set ℕ) (fun _ => Set.Ioi (1 : ℝ)) := by
      ext e
      simp only [Set.mem_iInter, Set.mem_pi, Finset.mem_coe,
        A, Set.mem_setOf_eq, Set.mem_Ioi]
    rw [hset, unitClockLaw_cylinder F (fun _ => Set.Ioi (1 : ℝ))
      (fun _ _ => measurableSet_Ioi)]
    apply Finset.prod_congr rfl
    intro n _
    exact (unitClockLaw_eval n (Set.Ioi (1 : ℝ)) measurableSet_Ioi).symm
  have hprob (n : ℕ) :
      unitClockLaw (A n) = ENNReal.ofReal (Real.exp (-1)) := by
    rw [show A n = {e | e n ∈ Set.Ioi (1 : ℝ)} from rfl,
      unitClockLaw_eval n _ measurableSet_Ioi]
    simpa using expMeasure_Ioi_of_nonneg
      (r := 1) (t := 1) (by norm_num) (by norm_num)
  have hsum : (∑' n, unitClockLaw (A n)) = ⊤ := by
    simp_rw [hprob]
    exact ENNReal.tsum_const_eq_top_of_ne_zero
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
  have hBC : unitClockLaw (limsup A atTop) = 1 :=
    measure_limsup_eq_one hAm hInd hsum
  have hLm : MeasurableSet (limsup A atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat']
    exact MeasurableSet.iInter fun n =>
      MeasurableSet.iUnion fun i => hAm (i + n)
  have hL : ∀ᵐ e ∂unitClockLaw, e ∈ limsup A atTop := by
    rw [ae_iff]
    change unitClockLaw (limsup A atTop)ᶜ = 0
    rw [measure_compl hLm (measure_ne_top _ _), hBC, measure_univ, tsub_self]
  filter_upwards [hL] with e he
  by_contra hfinite
  have hzero := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hfinite
  have hsmall : ∀ᶠ n in atTop, ENNReal.ofReal (e n) < 1 :=
    (tendsto_order.1 hzero).2 1 (by simp)
  have hlarge : ∃ᶠ n in atTop, 1 < e n := by
    simpa only [A, Set.mem_setOf_eq] using mem_limsup_iff_frequently_mem.mp he
  rcases (hlarge.and_eventually hsmall).exists with ⟨n, hn, hsn⟩
  have hge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (e n) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hn.le
  exact (not_lt_of_ge hge) hsn

section BoundedRates

universe uB vB
variable {S : Type uB} [Fintype S] [DecidableEq S]
variable (N : Network.{uB, vB} S) [DecidableEq N.I]

theorem timedLaw_unitClock_sum_eq_top_ae
    (hPos : N.hasPositiveRates) (z0 : State S) :
    ∀ᵐ η ∂timedLaw N hPos z0,
      (∑' n : ℕ, ENNReal.ofReal (η.2 n)) = ⊤ := by
  have h : ∀ᵐ e ∂(timedLaw N hPos z0).map Prod.snd,
      (∑' n : ℕ, ENNReal.ofReal (e n)) = ⊤ := by
    rw [timedLaw_map_clocks N hPos z0]
    exact unitClock_sum_eq_top_ae
  exact ae_of_ae_map measurable_snd.aemeasurable h

/-- A finite upper bound on rates gives a positive lower multiple of each unit clock.
The bound may be zero: extended reciprocal arithmetic then gives infinite waiting. -/
theorem holdingTime_tsum_eq_top_of_bound (z0 : State S) (η : TimedΩ N)
    (R : ℝ≥0∞) (hR : R ≠ ⊤)
    (hbound : ∀ n,
      (N.totalPropensity (pathState N z0 η.1 n) : ℝ≥0∞) ≤ R)
    (hclock : (∑' n : ℕ, ENNReal.ofReal (η.2 n)) = ⊤) :
    (∑' n : ℕ, holdingTime N z0 n η) = ⊤ := by
  apply top_unique
  calc
    ⊤ = R⁻¹ * ∑' n : ℕ, ENNReal.ofReal (η.2 n) := by
      rw [hclock, ENNReal.mul_top (ENNReal.inv_ne_zero.mpr hR)]
    _ = ∑' n : ℕ, R⁻¹ * ENNReal.ofReal (η.2 n) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' n : ℕ, holdingTime N z0 n η := by
      apply ENNReal.tsum_le_tsum
      intro n
      change R⁻¹ * ENNReal.ofReal (η.2 n) ≤
        (N.totalPropensity (pathState N z0 η.1 n) : ℝ≥0∞)⁻¹ *
          ENNReal.ofReal (η.2 n)
      exact mul_le_mul_left (ENNReal.inv_le_inv.mpr (hbound n)) _

/-- Under an almost-sure uniform rate bound, infinitely many firings require infinite time. -/
theorem timedLaw_noExplosion_of_bound (hPos : N.hasPositiveRates)
    (z0 : State S) (R : ℝ≥0∞) (hR : R ≠ ⊤)
    (hbound : ∀ᵐ ω ∂rawLaw N hPos z0, ∀ n,
      (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞) ≤ R) :
    ∀ᵐ η ∂timedLaw N hPos z0,
      (∑' n : ℕ, holdingTime N z0 n η) = ⊤ := by
  have hlabels : ∀ᵐ ω ∂(timedLaw N hPos z0).map Prod.fst, ∀ n,
      (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞) ≤ R := by
    rw [timedLaw_map_labels N hPos z0]
    exact hbound
  have hb : ∀ᵐ η ∂timedLaw N hPos z0, ∀ n,
      (N.totalPropensity (pathState N z0 η.1 n) : ℝ≥0∞) ≤ R :=
    ae_of_ae_map measurable_fst.aemeasurable hlabels
  filter_upwards [hb, timedLaw_unitClock_sum_eq_top_ae N hPos z0] with η hη hc
  exact holdingTime_tsum_eq_top_of_bound N z0 η R hR hη hc

/-- For a pre-stopping mask, an infinite pre-stop run consumes infinite physical time.
The rate bound is required only while the mask is active. -/
theorem timedLaw_noExplosion_before_of_bound (hPos : N.hasPositiveRates)
    (z0 : State S) (active : ℕ → ((k : ℕ) → Option N.I) → Prop)
    (R : ℝ≥0∞) (hR : R ≠ ⊤)
    (hbound : ∀ᵐ ω ∂rawLaw N hPos z0, ∀ n, active n ω →
      (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞) ≤ R) :
    ∀ᵐ η ∂timedLaw N hPos z0, (∀ n, active n η.1) →
      occupationTime N z0 active η = ⊤ := by
  have hlabels : ∀ᵐ ω ∂(timedLaw N hPos z0).map Prod.fst,
      ∀ n, active n ω →
        (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞) ≤ R := by
    rw [timedLaw_map_labels N hPos z0]
    exact hbound
  have hb : ∀ᵐ η ∂timedLaw N hPos z0, ∀ n, active n η.1 →
      (N.totalPropensity (pathState N z0 η.1 n) : ℝ≥0∞) ≤ R :=
    ae_of_ae_map measurable_fst.aemeasurable hlabels
  filter_upwards [hb, timedLaw_unitClock_sum_eq_top_ae N hPos z0] with η hη hc
  intro hall
  have hsum := holdingTime_tsum_eq_top_of_bound N z0 η R hR
    (fun n => hη n (hall n)) hc
  rw [occupationTime_eq_tsum]
  simpa only [hall, if_true] using hsum


/-- A finite set containing every pre-stop state supplies the rate bound automatically. -/
theorem timedLaw_noExplosion_before_of_finite_states (hPos : N.hasPositiveRates)
    (z0 : State S) (active : ℕ → ((k : ℕ) → Option N.I) → Prop)
    (D : Finset (State S))
    (hreach : ∀ᵐ ω ∂rawLaw N hPos z0, ∀ n, active n ω →
      pathState N z0 ω n ∈ D) :
    ∀ᵐ η ∂timedLaw N hPos z0, (∀ n, active n η.1) →
      occupationTime N z0 active η = ⊤ := by
  classical
  let R : ℝ≥0∞ := ∑ z ∈ D, (N.totalPropensity z : ℝ≥0∞)
  have hR : R ≠ ⊤ := by
    change (∑ z ∈ D, (N.totalPropensity z : ℝ≥0∞)) ≠ ⊤
    apply ENNReal.sum_ne_top.mpr
    intro z _
    change ((N.totalPropensity z : NNReal) : ℝ≥0∞) ≠ ⊤
    exact ENNReal.coe_ne_top
  apply timedLaw_noExplosion_before_of_bound N hPos z0 active R hR
  filter_upwards [hreach] with ω hω n hn
  exact Finset.single_le_sum
    (f := fun z : State S => (N.totalPropensity z : ℝ≥0∞))
    (fun _ _ => zero_le') (hω n hn)

end BoundedRates

/-! ## First exits and the exact nonexplosion obligation -/

section MassActionFirstExit

open Classical

universe uE vE
variable {S : Type uE} [Fintype S] [DecidableEq S]
variable (N : Network.{uE, vE} S) [DecidableEq N.I]

/-- An initial-segment mask with endpoint k selects exactly the first k holding times. -/
theorem occupationTime_eq_jumpTime_of_mask (z0 : State S)
    (active : ℕ → ((j : ℕ) → Option N.I) → Prop)
    (u : TimedΩ N) (k : ℕ)
    (hactive : ∀ n, active n u.1 ↔ n < k) :
    occupationTime N z0 active u = jumpTime N z0 k u := by
  classical
  rw [occupationTime_eq_tsum]
  unfold jumpTime
  rw [tsum_eq_sum (s := Finset.range k)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos ((hactive n).2 (Finset.mem_range.mp hn))]
  · intro n hn
    apply if_neg
    intro h
    exact hn (Finset.mem_range.mpr ((hactive n).1 h))

/-- Time of the first inactive jump index, with infinity when no such index exists. -/
noncomputable def firstExitTime (z0 : State S)
    (active : ℕ → ((j : ℕ) → Option N.I) → Prop) (u : TimedΩ N) : ℝ≥0∞ :=
  if h : ∃ n, ¬ active n u.1 then jumpTime N z0 (Nat.find h) u else ⊤

/-- The only additional pointwise obligation is divergence on paths whose mask never closes.
For an initial-segment mask this is precisely nonexplosion before its stopping event. -/
theorem occupationTime_eq_firstExitTime (z0 : State S)
    (active : ℕ → ((j : ℕ) → Option N.I) → Prop) (u : TimedΩ N)
    (hsegment : ∀ {m n : ℕ}, m ≤ n → active n u.1 → active m u.1)
    (hdiv : (∀ n, active n u.1) → occupationTime N z0 active u = ⊤) :
    occupationTime N z0 active u = firstExitTime N z0 active u := by
  classical
  by_cases hexit : ∃ n, ¬ active n u.1
  · rw [firstExitTime, dif_pos hexit]
    apply occupationTime_eq_jumpTime_of_mask
    intro n
    constructor
    · intro hn
      by_contra hnot
      have hle : Nat.find hexit ≤ n := Nat.le_of_not_gt hnot
      exact (Nat.find_spec hexit) (hsegment hle hn)
    · intro hn
      exact not_not.mp (Nat.find_min hexit hn)
  · rw [firstExitTime, dif_neg hexit]
    apply hdiv
    intro n
    by_contra hn
    exact hexit ⟨n, hn⟩

/-- Almost-sure first-exit identification, with divergence exposed as a hypothesis. -/
theorem occupationTime_ae_eq_firstExitTime (hPos : N.hasPositiveRates)
    (z0 : State S) (active : ℕ → ((j : ℕ) → Option N.I) → Prop)
    (hsegment : ∀ (u : TimedΩ N) {m n : ℕ},
      m ≤ n → active n u.1 → active m u.1)
    (hdiv : ∀ᵐ u ∂timedLaw N hPos z0,
      (∀ n, active n u.1) → occupationTime N z0 active u = ⊤) :
    occupationTime N z0 active =ᵐ[timedLaw N hPos z0] firstExitTime N z0 active :=
  hdiv.mono fun u hu =>
    occupationTime_eq_firstExitTime N z0 active u (hsegment u) hu

/-- The first-exit expectation follows once the precise divergence obligation is proved. -/
theorem lintegral_firstExitTime (hPos : N.hasPositiveRates) (z0 : State S)
    (active : ℕ → ((j : ℕ) → Option N.I) → Prop)
    (hactive : ∀ n, MeasurableSet {ω | active n ω})
    (hsegment : ∀ (u : TimedΩ N) {m n : ℕ},
      m ≤ n → active n u.1 → active m u.1)
    (hdiv : ∀ᵐ u ∂timedLaw N hPos z0,
      (∀ n, active n u.1) → occupationTime N z0 active u = ⊤) :
    (∫⁻ u, firstExitTime N z0 active u ∂timedLaw N hPos z0) =
      ∫⁻ ω, ∑' n,
        (if active n ω then
          (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞)⁻¹
        else 0) ∂rawLaw N hPos z0 := by
  calc
    (∫⁻ u, firstExitTime N z0 active u ∂timedLaw N hPos z0) =
        ∫⁻ u, occupationTime N z0 active u ∂timedLaw N hPos z0 :=
      lintegral_congr_ae
        (occupationTime_ae_eq_firstExitTime N hPos z0 active hsegment hdiv).symm
    _ = ∫⁻ ω, ∑' n,
        (if active n ω then
          (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞)⁻¹
        else 0) ∂rawLaw N hPos z0 :=
      lintegral_occupationTime N hPos z0 active hactive

end MassActionFirstExit

/-! ## The complete expectation bridge under finite pre-stop reachability -/

section FiniteDomainExpectedTime

universe uF vF
variable {S : Type uF} [Fintype S] [DecidableEq S]
variable (N : Network.{uF, vF} S) [DecidableEq N.I]

/-- Finite pre-stop reachability discharges the nonexplosion hypothesis in the
first-exit expectation formula. No bound or finiteness of the expectation is assumed. -/
theorem lintegral_firstExitTime_of_finite_states
    (hPos : N.hasPositiveRates) (z0 : State S)
    (active : ℕ → ((j : ℕ) → Option N.I) → Prop)
    (hactive : ∀ n, MeasurableSet {ω | active n ω})
    (hsegment : ∀ (u : TimedΩ N) {m n : ℕ},
      m ≤ n → active n u.1 → active m u.1)
    (D : Finset (State S))
    (hreach : ∀ᵐ ω ∂rawLaw N hPos z0, ∀ n, active n ω →
      pathState N z0 ω n ∈ D) :
    (∫⁻ u, firstExitTime N z0 active u ∂timedLaw N hPos z0) =
      ∫⁻ ω, ∑' n,
        (if active n ω then
          (N.totalPropensity (pathState N z0 ω n) : ℝ≥0∞)⁻¹
        else 0) ∂rawLaw N hPos z0 :=
  lintegral_firstExitTime N hPos z0 active hactive hsegment
    (timedLaw_noExplosion_before_of_finite_states N hPos z0 active D hreach)

end FiniteDomainExpectedTime

/-! ## The existing headline masks and their exponential-clock lifts -/

section RegisterMachineHeadlines

open RegisterMachine RegisterMachine.Clocked

variable {Reg Label : Type} [Fintype Reg] [DecidableEq Reg]
  [Fintype Label] [DecidableEq Label] {M : RM Reg Label} {L a : ℕ}

/-- The exact live-before-target mask used by the register-machine expTime. -/
def registerActive (a : ℕ) (σ₀ : RState Reg Label L) (t n : ℕ) (ω : Ω M L) : Prop :=
  K n ω < t ∧ LiveState M (Z a σ₀ n ω)

private theorem register_live_of_tgt {i : Idx M L} {σ : RState Reg Label L}
    (hβ : beta M a i σ ≠ 0) (hlive : Live M (tgt M i σ).1) : Live M σ.1 := by
  rcases i with p | d | d | j | j
  · apply live_of_inc p σ.1
    by_contra h
    exact hβ (by simp [beta, h])
  · apply live_of_dec d σ.1
    by_contra h
    exact hβ (by simp [beta, h])
  · apply live_of_dec d σ.1
    by_contra h
    exact hβ (by simp [beta, h])
  · exact hlive
  · exact hlive

private theorem register_stateStep_enc (σ : RState Reg Label L)
    (o : Option (net M L).I) :
    ∃ τ, stateStep (net M L) (enc a σ) o = enc a τ := by
  classical
  by_cases hT : (net M L).Terminal (enc a σ)
  · exact ⟨σ, by simp only [stateStep, dif_pos hT]⟩
  · let i : Idx M L := fireOptionSanitized (net M L) (enc a σ) o hT
    have hi : beta M a i σ ≠ 0 := beta_ne_zero_of_enabled
      (fireOptionSanitized_enabled (net M L) (enc a σ) o hT)
    refine ⟨tgt M i σ, ?_⟩
    unfold stateStep
    rw [dif_neg hT]
    exact fire_enc M a i σ hi

private theorem register_Z_enc (a : ℕ) (σ₀ : RState Reg Label L) :
    ∀ n (ω : Ω M L), ∃ σ, Z a σ₀ n ω = enc a σ
  | 0, _ => ⟨σ₀, rfl⟩
  | n + 1, ω => by
    obtain ⟨σ, hσ⟩ := register_Z_enc a σ₀ n ω
    rw [Z_succ, hσ]
    exact register_stateStep_enc (a := a) σ (ω (n + 1))

private theorem register_liveState_of_stateStep
    (σ : RState Reg Label L) (o : Option (net M L).I)
    (hlive : LiveState M (stateStep (net M L) (enc a σ) o)) :
    LiveState M (enc a σ) := by
  classical
  by_cases hT : (net M L).Terminal (enc a σ)
  · simpa only [stateStep, dif_pos hT] using hlive
  · let i : Idx M L := fireOptionSanitized (net M L) (enc a σ) o hT
    have hi : beta M a i σ ≠ 0 := beta_ne_zero_of_enabled
      (fireOptionSanitized_enabled (net M L) (enc a σ) o hT)
    have hs : stateStep (net M L) (enc a σ) o = enc a (tgt M i σ) := by
      unfold stateStep
      rw [dif_neg hT]
      exact fire_enc M a i σ hi
    rw [hs] at hlive
    exact (liveState_enc (M := M) (a := a) σ.1 σ.2).2
      (register_live_of_tgt hi
        ((liveState_enc (M := M) (a := a) (tgt M i σ).1 (tgt M i σ).2).1 hlive))

/-- Halting is persistent, even for the total sanitized path construction. -/
theorem register_liveState_of_le (a : ℕ) (σ₀ : RState Reg Label L)
    (ω : Ω M L) {m n : ℕ} (hmn : m ≤ n) :
    LiveState M (Z a σ₀ n ω) → LiveState M (Z a σ₀ m ω) := by
  induction hmn with
  | refl => exact id
  | @step n hmn ih =>
    intro hlive
    apply ih
    obtain ⟨σ, hσ⟩ := register_Z_enc a σ₀ n ω
    rw [hσ]
    apply register_liveState_of_stateStep σ (ω (n + 1))
    simpa only [Z_succ, hσ] using hlive

/-- The register-machine occupation mask is an initial segment of jump indices. -/
theorem registerActive_initialSegment (a : ℕ) (σ₀ : RState Reg Label L)
    (t : ℕ) (ω : Ω M L) {m n : ℕ} (hmn : m ≤ n)
    (hn : registerActive a σ₀ t n ω) : registerActive a σ₀ t m ω :=
  ⟨lt_of_le_of_lt (K_mono ω hmn) hn.1,
    register_liveState_of_le a σ₀ ω hmn hn.2⟩

theorem measurableSet_registerActive (a : ℕ) (σ₀ : RState Reg Label L) (t n : ℕ) :
    MeasurableSet {ω : Ω M L | registerActive a σ₀ t n ω} := by
  let A : Set (Ω M L) := {ω | registerActive a σ₀ t n ω}
  have hA : A = frestrictLe n ⁻¹' (frestrictLe n '' A) := by
    ext ω
    constructor
    · intro h
      exact ⟨ω, h, rfl⟩
    · rintro ⟨ω', hω', h⟩
      change K n ω' < t ∧ LiveState M (Z a σ₀ n ω') at hω'
      change K n ω < t ∧ LiveState M (Z a σ₀ n ω)
      simpa only [K_det n h, Z_det a σ₀ n h] using hω'
  change MeasurableSet A
  rw [hA]
  exact measurable_frestrictLe n (measurableSet_prefixSet (net M L) n _)

private theorem register_pathState (a : ℕ) (σ₀ : RState Reg Label L)
    (n : ℕ) (ω : Ω M L) :
    pathState (net M L) (enc a σ₀) ω n = Z a σ₀ n ω :=
  (prefixToState_eq_pathState (net M L) (enc a σ₀) ω n).symm

/-- Realized exponential-clock time before the register-machine target or halting. -/
noncomputable def registerElapsed (M : RM Reg Label) (a : ℕ) (σ₀ : RState Reg Label L)
    (t : ℕ) (u : TimedΩ (net M L)) : ℝ≥0∞ :=
  occupationTime (net M L) (enc a σ₀) (registerActive a σ₀ t) u

/-- Exact identification of the original register-machine expTime functional. -/
theorem lintegral_registerElapsed (M : RM Reg Label) (a : ℕ)
    (σ₀ : RState Reg Label L) (t : ℕ) :
    (∫⁻ u, registerElapsed M a σ₀ t u
      ∂timedLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀)) =
        expTime (M := M) a σ₀ t := by
  classical
  have h := lintegral_occupationTime (net M L) (net_hasPositiveRates M L)
    (enc a σ₀) (registerActive a σ₀ t)
    (measurableSet_registerActive a σ₀ t)
  simpa only [registerElapsed, registerActive, expTime, law, register_pathState] using h

/-- SCWB Theorem 3.1 on the space carrying actual independent exponential clocks.
The unit-rate elapsed random variable is scaled by v/k, exactly as in the source theorem. -/
theorem scwb_theorem_3_1_timed (M : RM Reg Label) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ (y₀ : Reg → ℕ) (t : ℕ), 1 ≤ t → ∃ a : ℕ,
      timedLaw (net M 1) (net_hasPositiveRates M 1)
          (enc a ((M.start, y₀), Fin.last 1))
          {u | ¬ Simulates a ((M.start, y₀), Fin.last 1) (M.start, y₀) t u.1} ≤
        ENNReal.ofReal δ ∧
      ∀ v k : ℝ, 0 < v → 0 < k →
        ENNReal.ofReal (v / k) *
          (∫⁻ u, registerElapsed M a ((M.start, y₀), Fin.last 1) t u
            ∂timedLaw (net M 1) (net_hasPositiveRates M 1)
              (enc a ((M.start, y₀), Fin.last 1))) ≤
          ENNReal.ofReal (6 * v * t ^ 2 / (k * δ)) := by
  intro δ hδ hδ1 y₀ t ht
  obtain ⟨a, herr, htime⟩ := RegisterMachine.Clocked.scwb_theorem_3_1
    M δ hδ hδ1 y₀ t ht
  refine ⟨a, ?_, ?_⟩
  · simpa only [Set.mem_setOf_eq] using
      (timedLaw_labels (net M 1) (net_hasPositiveRates M 1)
        (enc a ((M.start, y₀), Fin.last 1))
        {ω | ¬ Simulates a ((M.start, y₀), Fin.last 1) (M.start, y₀) t ω}).trans_le herr
  · intro v k hv hk
    rw [lintegral_registerElapsed]
    exact htime v k hv hk

end RegisterMachineHeadlines

section ClockedCTMHeadlines

open ClockedCTM

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ}

/-- The exact before-tick mask used by the CTM expTime. -/
def ctmActive (N n : ℕ) (ω : ℕ → Option (Rx Q L)) : Prop := ticks n ω < N

/-- The CTM occupation mask is an initial segment of jump indices. -/
theorem ctmActive_initialSegment (N : ℕ) (ω : ℕ → Option (Rx Q L))
    {m n : ℕ} (hmn : m ≤ n) (hn : ctmActive N n ω) : ctmActive N m ω :=
  lt_of_le_of_lt (ticks_mono ω hmn) hn

theorem measurableSet_ctmActive (C : CTM Q) (N n : ℕ) :
    MeasurableSet {ω : ℕ → Option (net C L).I | ctmActive N n ω} := by
  let A : Set (ℕ → Option (net C L).I) := {ω | ctmActive N n ω}
  have hA : A = frestrictLe n ⁻¹' (frestrictLe n '' A) := by
    ext ω
    constructor
    · intro h
      exact ⟨ω, h, rfl⟩
    · rintro ⟨ω', hω', h⟩
      change ticks n ω' < N at hω'
      change ticks n ω < N
      simpa only [ticks_det n h] using hω'
  change MeasurableSet A
  rw [hA]
  exact measurable_frestrictLe n (measurableSet_prefixSet (net C L) n _)

private theorem ctm_pathState (C : CTM Q) (z0 : State (Sp Q L))
    (n : ℕ) (ω : ℕ → Option (Rx Q L)) :
    pathState (net C L) z0 ω n = traj C z0 n ω :=
  (prefixToState_eq_pathState (net C L) z0 ω n).symm

/-- Realized exponential-clock time before tick N. -/
noncomputable def ctmElapsed (C : CTM Q) (z0 : State (Sp Q L))
    (N : ℕ) (u : TimedΩ (net C L)) : ℝ≥0∞ :=
  occupationTime (net C L) z0 (ctmActive N) u

/-- Exact identification of the original CTM expTime functional. -/
theorem lintegral_ctmElapsed (C : CTM Q) (z0 : State (Sp Q L)) (N : ℕ) :
    (∫⁻ u, ctmElapsed C z0 N u
      ∂timedLaw (net C L) (net_hasPositiveRates C L) z0) =
        expTime C z0 N := by
  classical
  have h := lintegral_occupationTime (net C L) (net_hasPositiveRates C L)
    z0 (ctmActive N) (measurableSet_ctmActive C N)
  simpa only [ctmElapsed, ctmActive, expTime, ctm_pathState] using h

/-- SCWB Theorem 3.2 at the CTM level, lifted to independent exponential clocks. -/
theorem scwb_theorem_3_2_ctm_timed (C : CTM Q) (L : ℕ) (hL : 1 ≤ L) (n : ℕ) :
    ∃ f : ℕ, 1 ≤ f ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ (c0 : Q × List Bool) (hc0 : c0.2.length = n + 3) (t : ℕ), 1 ≤ t →
    ∃ a : ℕ, 2 ≤ a ∧
      timedLaw (net C L) (net_hasPositiveRates C L) (initState (L := L) n c0 a f)
          {u | ¬ Simulates (ctmSched C n c0 hc0) (4 * t)
            (initState (L := L) n c0 a f) u.1} ≤
        ENNReal.ofReal δ ∧
      ∀ v k : ℝ, 0 < v → 0 < k →
        ENNReal.ofReal (v / k) *
          (∫⁻ u, ctmElapsed C (initState (L := L) n c0 a f) (4 * t) u
            ∂timedLaw (net C L) (net_hasPositiveRates C L) (initState (L := L) n c0 a f)) ≤
          ENNReal.ofReal (8 * (3 / 2) ^ L * v * t ^ 2 * Θsum n / (k * δ)) := by
  obtain ⟨f, hf, hmain⟩ := ClockedCTM.scwb_theorem_3_2_ctm C L hL n
  refine ⟨f, hf, ?_⟩
  intro δ hδ hδ1 c0 hc0 t ht
  obtain ⟨a, ha, herr, htime⟩ := hmain δ hδ hδ1 c0 hc0 t ht
  refine ⟨a, ha, ?_, ?_⟩
  · simpa only [Set.mem_setOf_eq] using
      (timedLaw_labels (net C L) (net_hasPositiveRates C L)
        (initState (L := L) n c0 a f)
        {ω | ¬ Simulates (ctmSched C n c0 hc0) (4 * t)
          (initState (L := L) n c0 a f) ω}).trans_le herr
  · intro v k hv hk
    rw [lintegral_ctmElapsed]
    exact htime v k hv hk

end ClockedCTMHeadlines

section TuringMachineHeadline

open ClockedCTM

variable {QM : Type} [Fintype QM] [DecidableEq QM]

/-- The current Lean TM headline, with both of its exact constants, on timed paths. -/
theorem scwb_theorem_3_2_timed (M : TM.Machine QM Bool) (hb : M.blank = false)
    (L : ℕ) (hL : 1 ≤ L) (Lc : ℕ) (hLc : 2 ≤ Lc) :
    ∃ f : ℕ, 1 ≤ f ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ (c : TM.Cfg QM Bool) (t : ℕ), 1 ≤ t →
      (∀ t' ≤ t, tlen (tmRun M c t').tape ≤ Lc) →
    ∃ a : ℕ, 2 ≤ a ∧
      timedLaw (net (ctmOf M) L) (net_hasPositiveRates (ctmOf M) L)
          (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)
          {u | ¬ TmSimulates M Lc c t
            (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f) u.1} ≤
        ENNReal.ofReal δ ∧
      ∀ v k : ℝ, 0 < v → 0 < k →
        ENNReal.ofReal (v / k) *
          (∫⁻ u, ctmElapsed (ctmOf M)
              (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)
              (4 * ctmTime M Lc c t) u
            ∂timedLaw (net (ctmOf M) L) (net_hasPositiveRates (ctmOf M) L)
              (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)) ≤
          ENNReal.ofReal (2880 * (3 / 2) ^ L * v * ((2 * Lc : ℕ) : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            (1 + (((2 * Lc : ℕ) : ℝ) - 1) * Real.log 3) / (k * 3 ^ (2 * Lc) * δ)) ∧
        ENNReal.ofReal (v / k) *
          (∫⁻ u, ctmElapsed (ctmOf M)
              (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)
              (4 * ctmTime M Lc c t) u
            ∂timedLaw (net (ctmOf M) L) (net_hasPositiveRates (ctmOf M) L)
              (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)) ≤
          ENNReal.ofReal (3168 * (3 / 2) ^ L * v * ((2 * Lc : ℕ) : ℝ) ^ 3 * (t : ℝ) ^ 2 /
            (k * 3 ^ (2 * Lc) * δ)) := by
  obtain ⟨f, hf, hmain⟩ := ClockedCTM.scwb_theorem_3_2 M hb L hL Lc hLc
  refine ⟨f, hf, ?_⟩
  intro δ hδ hδ1 c t ht hsp
  obtain ⟨a, ha, herr, htime⟩ := hmain δ hδ hδ1 c t ht hsp
  refine ⟨a, ha, ?_, ?_⟩
  · simpa only [Set.mem_setOf_eq] using
      (timedLaw_labels (net (ctmOf M) L) (net_hasPositiveRates (ctmOf M) L)
        (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)
        {ω | ¬ TmSimulates M Lc c t
          (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f) ω}).trans_le herr
  · intro v k hv hk
    simpa only [lintegral_ctmElapsed] using htime v k hv hk

end TuringMachineHeadline

/-! ## Register-machine pretarget nonexplosion and the stopping-time headline -/

section RegisterMachineStopping

open RegisterMachine RegisterMachine.Clocked

variable {Reg Label : Type} [Fintype Reg] [DecidableEq Reg]
  [Fintype Label] [DecidableEq Label] {M : RM Reg Label} {L : ℕ}

private theorem register_step_count_le (a : ℕ) (σ : RState Reg Label L)
    (o : Option (net M L).I) (r : Reg)
    (hmass : massActionPMF (net M L) (net_hasPositiveRates M L) (enc a σ) o ≠ 0) :
    stateStep (net M L) (enc a σ) o (Sp.reg r) ≤ σ.1.2 r + rmOpt o := by
  classical
  cases o with
  | none =>
    have hT := massActionPMF_none_ne_zero_terminal
      (net M L) (net_hasPositiveRates M L) (enc a σ) hmass
    simpa only [stateStep, dif_pos hT, enc, rmOpt, Nat.add_zero]
      using (le_refl (σ.1.2 r))
  | some i =>
    have hi := massActionPMF_some_ne_zero_enabled
      (net M L) (net_hasPositiveRates M L) (enc a σ) i hmass
    have hNT : ¬ (net M L).Terminal (enc a σ) := fun hT => hT i hi
    have hs : stateStep (net M L) (enc a σ) (some i) = enc a (tgt M i σ) := by
      unfold stateStep
      rw [dif_neg hNT, fireOptionSanitized_of_enabled (net M L) (enc a σ) i hNT hi]
      exact fire_enc M a i σ (beta_ne_zero_of_enabled hi)
    rw [hs]
    rcases i with p | d | d | j | j
    · simp only [enc, tgt, rmOpt, isRM, if_true, Function.update_apply]
      split_ifs with hr
      · subst r
        omega
      · omega
    · simp only [enc, tgt, rmOpt, isRM, if_true, Function.update_apply]
      split_ifs with hr
      · subst r
        omega
      · omega
    · simp [enc, tgt, rmOpt, isRM]
    · simp [enc, tgt, rmOpt, isRM]
    · simp [enc, tgt, rmOpt, isRM]

/-- Along a valid label trajectory, each machine reaction increases any fixed register
by at most one and clock reactions do not increase it. -/
theorem register_count_le_of_valid (a : ℕ) (σ₀ : RState Reg Label L) (ω : Ω M L)
    (hvalid : ∀ n,
      massActionPMF (net M L) (net_hasPositiveRates M L) (Z a σ₀ n ω) (ω (n + 1)) ≠ 0) :
    ∀ n r, Z a σ₀ n ω (Sp.reg r) ≤ σ₀.1.2 r + K n ω := by
  intro n
  induction n with
  | zero =>
    intro r
    simp [Z_zero, enc, K]
  | succ n ih =>
    intro r
    obtain ⟨σ, hσ⟩ := register_Z_enc a σ₀ n ω
    have hmass : massActionPMF (net M L) (net_hasPositiveRates M L)
        (enc a σ) (ω (n + 1)) ≠ 0 := by
      simpa only [hσ] using hvalid n
    have hstep := register_step_count_le a σ (ω (n + 1)) r hmass
    have hprev := ih r
    rw [hσ] at hprev
    change σ.1.2 r ≤ σ₀.1.2 r + K n ω at hprev
    rw [Z_succ, hσ, K_succ]
    omega

/-- The register-count estimate is an almost-sure statement: raw labels of zero probability
are excluded, so sanitized fallback firings cannot invalidate the counter estimate. -/
theorem register_count_le_ae (M : RM Reg Label) (a : ℕ) (σ₀ : RState Reg Label L) :
    ∀ᵐ ω ∂rawLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀),
      ∀ n r, Z a σ₀ n ω (Sp.reg r) ≤ σ₀.1.2 r + K n ω := by
  have hvalid : ∀ᵐ ω ∂rawLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀),
      ∀ n, massActionPMF (net M L) (net_hasPositiveRates M L)
        (Z a σ₀ n ω) (ω (n + 1)) ≠ 0 := by
    have hnull := measure_eq_zero_iff_ae_notMem.mp
      (rawLaw_null_label (net M L) (net_hasPositiveRates M L) (enc a σ₀))
    filter_upwards [hnull] with ω hω n
    intro hzero
    exact hω ⟨n, hzero⟩
  filter_upwards [hvalid] with ω hω
  exact register_count_le_of_valid a σ₀ ω hω

/-- A finite propensity bound used only to prove nonexplosion; it does not change
any error or expected-time constant in the headline. -/
def registerRateBound (M : RM Reg Label) (a : ℕ) (σ₀ : RState Reg Label L) (t : ℕ) : ℕ :=
  Fintype.card (Idx M L) * (a + 1 + ∑ r : Reg, (σ₀.1.2 r + t))

private theorem register_beta_le (a : ℕ) (σ : RState Reg Label L) (B : ℕ)
    (hreg : ∀ r, σ.1.2 r ≤ B) (i : Idx M L) :
    beta M a i σ ≤ a + 1 + B := by
  classical
  rcases i with p | d | d | j | j
  · simp only [beta]
    split_ifs <;> omega
  · have hr := hreg d.1.2.1
    simp only [beta]
    split_ifs <;> omega
  · simp only [beta]
    split_ifs <;> omega
  · simp only [beta]
    split_ifs <;> omega
  · simp only [beta]
    split_ifs <;> omega

private theorem register_btot_le (a : ℕ) (σ₀ : RState Reg Label L) (t : ℕ)
    (σ : RState Reg Label L) (hreg : ∀ r, σ.1.2 r ≤ σ₀.1.2 r + t) :
    Btot M a σ ≤ registerRateBound M a σ₀ t := by
  classical
  have hsum : ∀ r, σ.1.2 r ≤ ∑ s : Reg, (σ₀.1.2 s + t) := by
    intro r
    exact (hreg r).trans
      (Finset.single_le_sum (f := fun s : Reg => σ₀.1.2 s + t)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ r))
  unfold Btot registerRateBound
  calc
    (∑ i : Idx M L, beta M a i σ) ≤
        ∑ _i : Idx M L, (a + 1 + ∑ r : Reg, (σ₀.1.2 r + t)) :=
      Finset.sum_le_sum fun i _ => register_beta_le a σ _ hsum i
    _ = Fintype.card (Idx M L) * (a + 1 + ∑ r : Reg, (σ₀.1.2 r + t)) := by
      simp

/-- The propensity bound holds on every pretarget state of almost every raw trajectory,
including trajectories that have already made an incorrect zero-test decision. -/
theorem register_rateBound_ae (M : RM Reg Label) (a : ℕ)
    (σ₀ : RState Reg Label L) (t : ℕ) :
    ∀ᵐ ω ∂rawLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀),
      ∀ n, registerActive a σ₀ t n ω →
        ((net M L).totalPropensity (pathState (net M L) (enc a σ₀) ω n) : ℝ≥0∞) ≤
          (registerRateBound M a σ₀ t : ℝ≥0∞) := by
  filter_upwards [register_count_le_ae M a σ₀] with ω hω n hn
  obtain ⟨σ, hσ⟩ := register_Z_enc a σ₀ n ω
  have hreg : ∀ r, σ.1.2 r ≤ σ₀.1.2 r + t := by
    intro r
    have hr := hω n r
    rw [hσ] at hr
    change σ.1.2 r ≤ σ₀.1.2 r + K n ω at hr
    have hk : K n ω < t := hn.1
    omega
  have hB := register_btot_le (M := M) a σ₀ t σ hreg
  have hcast (m : ℕ) : (((m : ℚ≥0)) : ℝ≥0∞) = (m : ℝ≥0∞) := by
    rw [← ENNReal.coe_nnratCast, NNRat.cast_natCast, ENNReal.coe_natCast]
  rw [register_pathState, hσ, totalPropensity_enc, hcast]
  exact_mod_cast hB

/-- No infinite register-machine pretarget execution can consume finite physical time. -/
theorem register_noExplosion_before (M : RM Reg Label) (a : ℕ)
    (σ₀ : RState Reg Label L) (t : ℕ) :
    ∀ᵐ u ∂timedLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀),
      (∀ n, registerActive a σ₀ t n u.1) → registerElapsed M a σ₀ t u = ⊤ := by
  exact timedLaw_noExplosion_before_of_bound (net M L) (net_hasPositiveRates M L)
    (enc a σ₀) (registerActive a σ₀ t) (registerRateBound M a σ₀ t : ℝ≥0∞)
    (ENNReal.natCast_ne_top _) (register_rateBound_ae M a σ₀ t)

/-- The random occupation sum is the actual first-exit clock time almost surely. -/
theorem registerElapsed_ae_eq_firstExitTime (M : RM Reg Label) (a : ℕ)
    (σ₀ : RState Reg Label L) (t : ℕ) :
    registerElapsed M a σ₀ t =ᵐ[
      timedLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀)]
      firstExitTime (net M L) (enc a σ₀) (registerActive a σ₀ t) := by
  apply occupationTime_ae_eq_firstExitTime
    (net M L) (net_hasPositiveRates M L) (enc a σ₀) (registerActive a σ₀ t)
  · intro u m n hmn hn
    exact registerActive_initialSegment a σ₀ t u.1 hmn hn
  · exact register_noExplosion_before M a σ₀ t

/-- The original expTime is the expectation of the register-machine first-exit time. -/
theorem lintegral_registerFirstExitTime (M : RM Reg Label) (a : ℕ)
    (σ₀ : RState Reg Label L) (t : ℕ) :
    (∫⁻ u, firstExitTime (net M L) (enc a σ₀) (registerActive a σ₀ t) u
      ∂timedLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀)) =
        expTime (M := M) a σ₀ t := by
  calc
    (∫⁻ u, firstExitTime (net M L) (enc a σ₀) (registerActive a σ₀ t) u
        ∂timedLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀)) =
        ∫⁻ u, registerElapsed M a σ₀ t u
          ∂timedLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀) :=
      lintegral_congr_ae (registerElapsed_ae_eq_firstExitTime M a σ₀ t).symm
    _ = expTime (M := M) a σ₀ t := lintegral_registerElapsed M a σ₀ t

/-- SCWB Theorem 3.1 with the actual stopping-time integral under the marked
exponential-clock law, retaining the original hypotheses and constant 6. -/
theorem scwb_theorem_3_1_ctmc_stop (M : RM Reg Label) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ (y₀ : Reg → ℕ) (t : ℕ), 1 ≤ t → ∃ a : ℕ,
      timedLaw (net M 1) (net_hasPositiveRates M 1)
          (enc a ((M.start, y₀), Fin.last 1))
          {u | ¬ Simulates a ((M.start, y₀), Fin.last 1) (M.start, y₀) t u.1} ≤
        ENNReal.ofReal δ ∧
      ∀ v k : ℝ, 0 < v → 0 < k →
        ENNReal.ofReal (v / k) *
          (∫⁻ u, firstExitTime (net M 1)
              (enc a ((M.start, y₀), Fin.last 1))
              (registerActive a ((M.start, y₀), Fin.last 1) t) u
            ∂timedLaw (net M 1) (net_hasPositiveRates M 1)
              (enc a ((M.start, y₀), Fin.last 1))) ≤
          ENNReal.ofReal (6 * v * t ^ 2 / (k * δ)) := by
  intro δ hδ hδ1 y₀ t ht
  obtain ⟨a, herr, htime⟩ := scwb_theorem_3_1_timed M δ hδ hδ1 y₀ t ht
  refine ⟨a, herr, ?_⟩
  intro v k hv hk
  simpa only [lintegral_registerFirstExitTime, lintegral_registerElapsed]
    using htime v k hv hk

end RegisterMachineStopping

end Ripple.sCRNUniversality.CTMCBridge
