import Ripple.sCRNUniversality.ClockedCTM.UnboundedError

/-!
# SCWB T41: physical time, five-state tick-wait algebra, and time assembly

The product-law results use the actual marked-law construction. The final
TimeClaim reducer exposes the still-unproved good-window mean estimate.
A second reducer splits that estimate into an actual volume bound and an
actual unit-rate occupation bound. Neither premise is asserted here.

No assertion of unconditional tick progress is made. The no-error progress
used in assembly is supplied by ErrorClaim, exactly on its stated event.
-/

namespace Ripple.sCRNUniversality.ClockedCTM.Unbounded.TimeAnalysis

open Stochastic Stochastic.MassAction
open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal BigOperators

variable {Q : Type} [Fintype Q] [DecidableEq Q]

private instance markedProbability (C : XCTM Q) (i : ℕ) (w : List Bool) :
    IsProbabilityMeasure (markedLaw C i w) :=
  CTMCBridge.timedLaw_isProbabilityMeasure (net C)
    (net_hasPositiveRates C) (initial C i w)

/-! ## Lemma 14.1: the actual product law and physical holding means -/

/-- Conditional mean given the entire label path. The reciprocal is extended:
a zero total propensity has infinite unit holding mean. -/
noncomputable def physicalMean (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (j : ℕ) (ω : LabelPath C) : ℝ≥0∞ :=
  CTMCBridge.meanHolding (net C) z₀ j ω *
    ENNReal.ofReal (volume (pathState (net C) z₀ ω j) / κ)

theorem physicalHolding_eq_mean_mul (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (j : ℕ) (η : TimedPath C) :
    physicalHolding C z₀ volume κ j η =
      physicalMean C z₀ volume κ j η.1 * ENNReal.ofReal (η.2 j) := by
  unfold physicalHolding CTMCBridge.holdingTime physicalMean
  ac_rfl

theorem measurable_physicalMean (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (j : ℕ) :
    Measurable (physicalMean C z₀ volume κ j) := by
  apply measurable_of_frestrictLe (net C) j
  intro ω ω' h
  have hz : pathState (net C) z₀ ω j = pathState (net C) z₀ ω' j := by
    rw [← prefixToState_eq_pathState (net C) z₀ ω j,
      ← prefixToState_eq_pathState (net C) z₀ ω' j]
    exact congrArg (prefixToState (net C) z₀ j) h
  change
    ((net C).totalPropensity (pathState (net C) z₀ ω j) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (volume (pathState (net C) z₀ ω j) / κ) =
      ((net C).totalPropensity (pathState (net C) z₀ ω' j) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (volume (pathState (net C) z₀ ω' j) / κ)
  exact congrArg (fun z : State (Sp C) =>
    ((net C).totalPropensity z : ℝ≥0∞)⁻¹ * ENNReal.ofReal (volume z / κ)) hz

/-- An exact fibre expectation, not an independence assumption. -/
theorem physicalHolding_fibre_mean (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (j : ℕ) (ω : LabelPath C) :
    (∫⁻ e, physicalHolding C z₀ volume κ j (ω, e)
      ∂CTMCBridge.unitClockLaw) = physicalMean C z₀ volume κ j ω := by
  simp_rw [physicalHolding_eq_mean_mul]
  change (∫⁻ e : ℕ → ℝ,
    physicalMean C z₀ volume κ j ω * ENNReal.ofReal (e j)
      ∂CTMCBridge.unitClockLaw) = _
  rw [lintegral_const_mul _ (measurable_pi_apply j).ennreal_ofReal,
    CTMCBridge.lintegral_unitClock, mul_one]

/-- At positive total rate the extended mean is the physical mean v/(κ B). -/
theorem physicalMean_eq_ofReal (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (j : ℕ) (ω : LabelPath C)
    (hB : 0 < (net C).totalPropensity (pathState (net C) z₀ ω j)) :
    physicalMean C z₀ volume κ j ω =
      ENNReal.ofReal
        (volume (pathState (net C) z₀ ω j) /
          (κ * CTMCBridge.totalRate (net C) (pathState (net C) z₀ ω j))) := by
  have hb : 0 < CTMCBridge.totalRate (net C) (pathState (net C) z₀ ω j) := by
    change (0 : ℝ) <
      ((net C).totalPropensity (pathState (net C) z₀ ω j) : ℝ)
    exact_mod_cast hB
  have heq :
      volume (pathState (net C) z₀ ω j) /
          (κ * CTMCBridge.totalRate (net C) (pathState (net C) z₀ ω j)) =
        (volume (pathState (net C) z₀ ω j) / κ) /
          CTMCBridge.totalRate (net C) (pathState (net C) z₀ ω j) := by ring
  rw [heq, ENNReal.ofReal_div_of_pos hb, CTMCBridge.ofReal_totalRate]
  simp only [physicalMean, CTMCBridge.meanHolding, div_eq_mul_inv, mul_comm]

/-- The actual holding variable is a scaled exponential mark. -/
theorem physicalHolding_eq_scaledClock (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (j : ℕ) (ω : LabelPath C)
    (e : ℕ → ℝ) (hκ : 0 < κ)
    (hv : 0 < volume (pathState (net C) z₀ ω j))
    (hB : 0 < (net C).totalPropensity (pathState (net C) z₀ ω j)) :
    physicalHolding C z₀ volume κ j (ω, e) =
      ENNReal.ofReal (e j /
        (κ * CTMCBridge.totalRate (net C) (pathState (net C) z₀ ω j) /
          volume (pathState (net C) z₀ ω j))) := by
  have hb : 0 < CTMCBridge.totalRate (net C) (pathState (net C) z₀ ω j) := by
    change (0 : ℝ) <
      ((net C).totalPropensity (pathState (net C) z₀ ω j) : ℝ)
    exact_mod_cast hB
  unfold physicalHolding
  rw [CTMCBridge.holdingTime_eq_ofReal_div (net C) z₀ j (ω, e) hB,
    ← ENNReal.ofReal_mul' (div_nonneg hv.le hκ.le)]
  congr 1
  field_simp [ne_of_gt hb, ne_of_gt hκ, ne_of_gt hv]
  <;> ring

/-- Exponential survival function conditional on a fixed complete label path. -/
theorem physicalHolding_fibre_tail (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (j : ℕ) (ω : LabelPath C)
    (t : ℝ) (ht : 0 ≤ t) (hκ : 0 < κ)
    (hv : 0 < volume (pathState (net C) z₀ ω j))
    (hB : 0 < (net C).totalPropensity (pathState (net C) z₀ ω j)) :
    CTMCBridge.unitClockLaw
      {e | ENNReal.ofReal t < physicalHolding C z₀ volume κ j (ω, e)} =
      ENNReal.ofReal (Real.exp
        (-((κ * CTMCBridge.totalRate (net C) (pathState (net C) z₀ ω j) /
          volume (pathState (net C) z₀ ω j)) * t))) := by
  have hb : 0 < CTMCBridge.totalRate (net C) (pathState (net C) z₀ ω j) := by
    change (0 : ℝ) <
      ((net C).totalPropensity (pathState (net C) z₀ ω j) : ℝ)
    exact_mod_cast hB
  have hr : 0 < κ * CTMCBridge.totalRate (net C)
      (pathState (net C) z₀ ω j) / volume (pathState (net C) z₀ ω j) :=
    div_pos (mul_pos hκ hb) hv
  have hset :
      {e : ℕ → ℝ | ENNReal.ofReal t < physicalHolding C z₀ volume κ j (ω, e)} =
        {e | t < e j /
          (κ * CTMCBridge.totalRate (net C) (pathState (net C) z₀ ω j) /
            volume (pathState (net C) z₀ ω j))} := by
    ext e
    change (ENNReal.ofReal t < physicalHolding C z₀ volume κ j (ω, e)) ↔ _
    rw [physicalHolding_eq_scaledClock C z₀ volume κ j ω e hκ hv hB,
      ENNReal.ofReal_lt_ofReal_iff']
    constructor
    · exact And.left
    · intro h
      exact ⟨h, ht.trans_lt h⟩
  rw [hset]
  exact CTMCBridge.unitClockLaw_div_tail j _ t hr ht

/-- Full finite-dimensional factorization of the holding variables in each fibre.
Together with the preceding tail theorem, this says independent exponentials
with the stated state-dependent rates. -/
theorem physicalHolding_fibre_cylinder (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ) (ω : LabelPath C)
    (F : Finset ℕ) (D : ℕ → Set ℝ≥0∞)
    (hD : ∀ j ∈ F, MeasurableSet (D j)) :
    CTMCBridge.unitClockLaw
      {e | ∀ j ∈ F, physicalHolding C z₀ volume κ j (ω, e) ∈ D j} =
      ∏ j ∈ F, expMeasure 1
        {v : ℝ | physicalMean C z₀ volume κ j ω * ENNReal.ofReal v ∈ D j} := by
  let B : ℕ → Set ℝ := fun j =>
    {v | physicalMean C z₀ volume κ j ω * ENNReal.ofReal v ∈ D j}
  have hB : ∀ j ∈ F, MeasurableSet (B j) := by
    intro j hj
    exact (measurable_const.mul measurable_id.ennreal_ofReal) (hD j hj)
  have hset :
      {e : ℕ → ℝ | ∀ j ∈ F,
        physicalHolding C z₀ volume κ j (ω, e) ∈ D j} =
      Set.pi (F : Set ℕ) B := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe,
      B, physicalHolding_eq_mean_mul]
  rw [hset]
  exact CTMCBridge.unitClockLaw_cylinder F B hB

/-- No-error is a label event. Its intersection with any clock cylinder factors. -/
theorem markedLaw_noError_clock_cylinder (C : XCTM Q) (i : ℕ) (w : List Bool)
    (F : Finset ℕ) (B : ℕ → Set ℝ) (hB : ∀ j ∈ F, MeasurableSet (B j)) :
    markedLaw C i w
      {η | η ∈ noErrorTimed C i w ∧ ∀ j ∈ F, η.2 j ∈ B j} =
      markedLaw C i w (noErrorTimed C i w) *
        ∏ j ∈ F, expMeasure 1 (B j) := by
  have hp := CTMCBridge.timedLaw_labels (net C) (net_hasPositiveRates C)
    (initial C i w) {ω | ¬ Error C (initial C i w) ω}
  have h := CTMCBridge.timedLaw_clock_cylinder (net C) (net_hasPositiveRates C)
    (initial C i w) {ω | ¬ Error C (initial C i w) ω} F B hB
  change markedLaw C i w (noErrorTimed C i w) =
    jumpLaw C i w {ω | ¬ Error C (initial C i w) ω} at hp
  change markedLaw C i w
      {η | η ∈ noErrorTimed C i w ∧ ∀ j ∈ F, η.2 j ∈ B j} =
    jumpLaw C i w {ω | ¬ Error C (initial C i w) ω} * _ at h
  rw [← hp] at h
  exact h

/-- The normalized clock-cylinder probabilities are unchanged on no-error.
This does not claim independence of the rate-mixed holding variables when
conditioning only on no-error rather than on the full label path. -/
theorem conditional_noError_clock_cylinder (C : XCTM Q) (i : ℕ) (w : List Bool)
    (hp : markedLaw C i w (noErrorTimed C i w) ≠ 0)
    (F : Finset ℕ) (B : ℕ → Set ℝ) (hB : ∀ j ∈ F, MeasurableSet (B j)) :
    markedLaw C i w
        {η | η ∈ noErrorTimed C i w ∧ ∀ j ∈ F, η.2 j ∈ B j} /
        markedLaw C i w (noErrorTimed C i w) =
      ∏ j ∈ F, expMeasure 1 (B j) := by
  rw [markedLaw_noError_clock_cylinder C i w F B hB]
  rw [mul_comm (markedLaw C i w (noErrorTimed C i w))]
  exact ENNReal.mul_div_cancel_right hp (measure_ne_top _ _)

/-- A stretch selected by any measurable label-path mask. Stopping-index
stretches are a special case; the clock coordinates are never inspected. -/
noncomputable def physicalStretch (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ)
    (active : ℕ → LabelPath C → Prop) (η : TimedPath C) : ℝ≥0∞ :=
  ∑' j, if active j η.1 then physicalHolding C z₀ volume κ j η else 0

noncomputable def maskedUnitCost (C : XCTM Q) (z₀ : State (Sp C))
    (active : ℕ → LabelPath C → Prop) (ω : LabelPath C) : ℝ≥0∞ :=
  ∑' j, if active j ω then CTMCBridge.meanHolding (net C) z₀ j ω else 0

theorem measurable_maskedUnitCost (C : XCTM Q) (z₀ : State (Sp C))
    (active : ℕ → LabelPath C → Prop)
    (hactive : ∀ j, MeasurableSet {ω | active j ω}) :
    Measurable (maskedUnitCost C z₀ active) := by
  simpa only [maskedUnitCost, Set.indicator_apply, Set.mem_setOf_eq] using
    (Measurable.tsum fun j =>
      (CTMCBridge.measurable_meanHolding (net C) z₀ j).indicator (hactive j))

theorem physicalStretch_eq_clockedSum (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ)
    (active : ℕ → LabelPath C → Prop) (η : TimedPath C) :
    physicalStretch C z₀ volume κ active η =
      CTMCBridge.clockedSum
        (fun j => {ω | active j ω}.indicator (physicalMean C z₀ volume κ j)) η := by
  unfold physicalStretch CTMCBridge.clockedSum
  apply tsum_congr
  intro j
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hj : active j η.1
  · simp only [if_pos hj]
    exact physicalHolding_eq_mean_mul C z₀ volume κ j η
  · simp only [if_neg hj, zero_mul]

theorem measurable_physicalStretch (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ)
    (active : ℕ → LabelPath C → Prop)
    (hactive : ∀ j, MeasurableSet {ω | active j ω}) :
    Measurable (physicalStretch C z₀ volume κ active) := by
  have heq : physicalStretch C z₀ volume κ active =
      CTMCBridge.clockedSum
        (fun j => {ω | active j ω}.indicator (physicalMean C z₀ volume κ j)) :=
    funext (physicalStretch_eq_clockedSum C z₀ volume κ active)
  rw [heq]
  exact CTMCBridge.measurable_clockedSum _
    (fun j => (measurable_physicalMean C z₀ volume κ j).indicator (hactive j))

/-- Exact Tonelli identity on the actual jump-and-hold product law.
This is the same generic bridge used by lintegral_registerElapsed. -/
theorem lintegral_physicalStretch (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ : ℝ)
    (active : ℕ → LabelPath C → Prop)
    (hactive : ∀ j, MeasurableSet {ω | active j ω}) :
    (∫⁻ η, physicalStretch C z₀ volume κ active η
      ∂CTMCBridge.timedLaw (net C) (net_hasPositiveRates C) z₀) =
      ∫⁻ ω, ∑' j, (if active j ω then physicalMean C z₀ volume κ j ω else 0)
        ∂rawLaw (net C) (net_hasPositiveRates C) z₀ := by
  simp_rw [physicalStretch_eq_clockedSum]
  have h := CTMCBridge.lintegral_clockedSum
    (rawLaw (net C) (net_hasPositiveRates C) z₀)
    (fun j => {ω | active j ω}.indicator (physicalMean C z₀ volume κ j))
    (fun j => (measurable_physicalMean C z₀ volume κ j).indicator (hactive j))
  simpa only [CTMCBridge.timedLaw, Set.indicator_apply, Set.mem_setOf_eq] using h

theorem markedLaw_physicalStretch (C : XCTM Q) (i : ℕ) (w : List Bool)
    (volume : State (Sp C) → ℝ) (κ : ℝ)
    (active : ℕ → LabelPath C → Prop)
    (hactive : ∀ j, MeasurableSet {ω | active j ω}) :
    (∫⁻ η, physicalStretch C (initial C i w) volume κ active η
      ∂markedLaw C i w) =
      ∫⁻ ω, ∑' j,
        (if active j ω then physicalMean C (initial C i w) volume κ j ω else 0)
        ∂jumpLaw C i w :=
  lintegral_physicalStretch C (initial C i w) volume κ active hactive

/-- A bound V on actual volume gives V/κ, not V/(ρ κ). -/
theorem physicalStretch_le_of_volume (C : XCTM Q) (z₀ : State (Sp C))
    (volume : State (Sp C) → ℝ) (κ V : ℝ) (hκ : 0 < κ)
    (active : ℕ → LabelPath C → Prop)
    (hactive : ∀ j, MeasurableSet {ω | active j ω})
    (hvolume : ∀ j ω, active j ω → volume (pathState (net C) z₀ ω j) ≤ V) :
    (∫⁻ η, physicalStretch C z₀ volume κ active η
      ∂CTMCBridge.timedLaw (net C) (net_hasPositiveRates C) z₀) ≤
      ENNReal.ofReal (V / κ) *
        ∫⁻ ω, maskedUnitCost C z₀ active ω
          ∂rawLaw (net C) (net_hasPositiveRates C) z₀ := by
  rw [lintegral_physicalStretch C z₀ volume κ active hactive]
  calc
    (∫⁻ ω, ∑' j, (if active j ω then physicalMean C z₀ volume κ j ω else 0)
      ∂rawLaw (net C) (net_hasPositiveRates C) z₀) ≤
        ∫⁻ ω, ENNReal.ofReal (V / κ) * maskedUnitCost C z₀ active ω
          ∂rawLaw (net C) (net_hasPositiveRates C) z₀ := by
      apply lintegral_mono
      intro ω
      simp only [maskedUnitCost]
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro j
      by_cases hj : active j ω
      · simp only [if_pos hj]
        unfold physicalMean
        calc
          CTMCBridge.meanHolding (net C) z₀ j ω *
              ENNReal.ofReal (volume (pathState (net C) z₀ ω j) / κ) ≤
            CTMCBridge.meanHolding (net C) z₀ j ω * ENNReal.ofReal (V / κ) := by
              gcongr
              exact hvolume j ω hj
          _ = _ := mul_comm _ _
      · simp only [if_neg hj, mul_zero, le_refl]
    _ = _ := lintegral_const_mul _ (measurable_maskedUnitCost C z₀ active hactive)

/-- Lemma 14.1: V is a molecule-count bound, and v(z)=|z|/ρ. -/
theorem physicalStretch_le_of_moleculeCount (C : XCTM Q) (z₀ : State (Sp C))
    (ρ κ V : ℝ) (hρ : 0 < ρ) (hκ : 0 < κ)
    (active : ℕ → LabelPath C → Prop)
    (hactive : ∀ j, MeasurableSet {ω | active j ω})
    (hvolume : ∀ j ω, active j ω →
      (moleculeCount C (pathState (net C) z₀ ω j) : ℝ) ≤ V) :
    (∫⁻ η, physicalStretch C z₀ (densityVolume C ρ) κ active η
      ∂CTMCBridge.timedLaw (net C) (net_hasPositiveRates C) z₀) ≤
      ENNReal.ofReal (V / (ρ * κ)) *
        ∫⁻ ω, maskedUnitCost C z₀ active ω
          ∂rawLaw (net C) (net_hasPositiveRates C) z₀ := by
  have h := physicalStretch_le_of_volume C z₀ (densityVolume C ρ) κ (V / ρ)
    hκ active hactive (fun j ω hj =>
      div_le_div_of_nonneg_right (hvolume j ω hj) hρ.le)
  simpa only [div_div] using h

/-! ## Lemma 14.2: the finite birth-death Poisson equations

Positions are 1,...,5; position 0 denotes the absorbing tick. The function
below is the unique solution of the backward equations. The theorem about
the expected hitting time of a concrete frozen stochastic chain is separate.
-/

noncomputable def tickWait (r f : ℝ) (c : ℕ) : ℝ :=
  (∑ i ∈ Finset.range c, ∑ j ∈ Finset.range (5 - i), r ^ j) / f

theorem tickWait_zero (r f : ℝ) : tickWait r f 0 = 0 := by
  simp [tickWait]

theorem tickWait_succ (r f : ℝ) (c : ℕ) :
    tickWait r f (c + 1) =
      tickWait r f c + (∑ j ∈ Finset.range (5 - c), r ^ j) / f := by
  simp only [tickWait, Finset.sum_range_succ, add_div]

theorem tickWait_nonneg {r f : ℝ} (hr : 0 ≤ r) (hf : 0 < f) (c : ℕ) :
    0 ≤ tickWait r f c := by
  unfold tickWait
  apply div_nonneg _ hf.le
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => pow_nonneg hr j

theorem tickWait_strict_step {r f : ℝ} (hr : 0 ≤ r) (hf : 0 < f)
    {c : ℕ} (hc : c < 5) : tickWait r f c < tickWait r f (c + 1) := by
  have hmem : 0 ∈ Finset.range (5 - c) := by simp; omega
  have hs : (1 : ℝ) ≤ ∑ j ∈ Finset.range (5 - c), r ^ j := by
    simpa only [pow_zero] using
      (Finset.single_le_sum (f := fun j : ℕ => r ^ j)
        (fun j _ => pow_nonneg hr j) hmem)
  rw [tickWait_succ]
  exact lt_add_of_pos_right _ (div_pos (zero_lt_one.trans_le hs) hf)

theorem tickWait_strictMono {r f : ℝ} (hr : 0 ≤ r) (hf : 0 < f)
    {a b : ℕ} (hab : a < b) (hb : b ≤ 5) : tickWait r f a < tickWait r f b := by
  have aux : ∀ b : ℕ, b ≤ 5 → ∀ a : ℕ, a < b → tickWait r f a < tickWait r f b := by
    intro b
    induction b with
    | zero => intro hb a hab; omega
    | succ b ih =>
        intro hb a hab
        by_cases he : a = b
        · subst a
          exact tickWait_strict_step hr hf (by omega)
        · have ha : a < b := by omega
          exact (ih (by omega) a ha).trans (tickWait_strict_step hr hf (by omega))
  exact aux b hb a hab

theorem tickWait_le_top {r f : ℝ} (hr : 0 ≤ r) (hf : 0 < f)
    {c : ℕ} (hc : c ≤ 5) : tickWait r f c ≤ tickWait r f 5 := by
  rcases lt_or_eq_of_le hc with h | h
  · exact (tickWait_strictMono hr hf h le_rfl).le
  · rw [h]

/-- f times the downward increment equals one plus a times the next increment. -/
theorem tickWait_backward {r f : ℝ} (hf : f ≠ 0)
    {c : ℕ} (hc : 1 ≤ c) (hcmax : c < 5) :
    f * (tickWait r f c - tickWait r f (c - 1)) =
      1 + (r * f) * (tickWait r f (c + 1) - tickWait r f c) := by
  interval_cases c <;>
    norm_num [tickWait, Finset.sum_range_succ] <;>
    field_simp [hf] <;> ring

theorem tickWait_reflecting {r f : ℝ} (hf : f ≠ 0) :
    f * (tickWait r f 5 - tickWait r f 4) = 1 := by
  norm_num [tickWait, Finset.sum_range_succ]
  field_simp [hf]
  <;> ring

/-- The finite backward equations determine every value, including r=1. -/
theorem tickWait_unique {r f : ℝ} (hf : f ≠ 0) (g : ℕ → ℝ)
    (hzero : g 0 = 0)
    (hstep : ∀ c, 1 ≤ c → c < 5 →
      f * (g c - g (c - 1)) = 1 + (r * f) * (g (c + 1) - g c))
    (hlast : f * (g 5 - g 4) = 1) :
    ∀ c, c ≤ 5 → g c = tickWait r f c := by
  have hdesc {c : ℕ} (hc : 1 ≤ c) (hcmax : c < 5)
      (hnext : g (c + 1) - g c = tickWait r f (c + 1) - tickWait r f c) :
      g c - g (c - 1) = tickWait r f c - tickWait r f (c - 1) := by
    apply mul_left_cancel₀ hf
    rw [hstep c hc hcmax, tickWait_backward hf hc hcmax, hnext]
  have hdLast : g 5 - g 4 = tickWait r f 5 - tickWait r f 4 :=
    mul_left_cancel₀ hf (hlast.trans (tickWait_reflecting hf).symm)
  have hdFourth := hdesc (c := 4) (by norm_num) (by norm_num) hdLast
  have hdThird := hdesc (c := 3) (by norm_num) (by norm_num) hdFourth
  have hdSecond := hdesc (c := 2) (by norm_num) (by norm_num) hdThird
  have hdFirst := hdesc (c := 1) (by norm_num) (by norm_num) hdSecond
  have hz := tickWait_zero r f
  intro c hc
  interval_cases c <;> norm_num at hdFirst hdSecond hdThird hdFourth hdLast ⊢ <;> linarith

theorem tickWait_top_polynomial (r f : ℝ) :
    tickWait r f 5 = (r ^ 4 + 2 * r ^ 3 + 3 * r ^ 2 + 4 * r + 5) / f := by
  norm_num [tickWait, Finset.sum_range_succ]
  <;> ring

/-- The geometric expression in Lemma 14.2, with the singular r=1 excluded. -/
theorem tickWait_top_geometric {r f : ℝ} (hr : r ≠ 1) (hf : f ≠ 0) :
    tickWait r f 5 =
      (1 / f) * ∑ c ∈ Finset.range 5, (r ^ (c + 1) - 1) / (r - 1) := by
  rw [tickWait_top_polynomial]
  norm_num [Finset.sum_range_succ]
  field_simp [hf, sub_ne_zero.mpr hr]
  <;> ring

theorem tickWait_top_le {r f : ℝ} (hr : 1 < r) (hf : 0 < f) :
    tickWait r f 5 ≤ r ^ 6 / ((r - 1) ^ 2 * f) := by
  have hd : 0 < (r - 1) ^ 2 := pow_pos (sub_pos.mpr hr) 2
  have hp : (r ^ 4 + 2 * r ^ 3 + 3 * r ^ 2 + 4 * r + 5) * (r - 1) ^ 2 ≤ r ^ 6 := by
    calc
      (r ^ 4 + 2 * r ^ 3 + 3 * r ^ 2 + 4 * r + 5) * (r - 1) ^ 2 =
          r ^ 6 - 6 * r + 5 := by ring
      _ ≤ r ^ 6 := by linarith
  rw [tickWait_top_polynomial]
  calc
    (r ^ 4 + 2 * r ^ 3 + 3 * r ^ 2 + 4 * r + 5) / f ≤
        (r ^ 6 / (r - 1) ^ 2) / f :=
      div_le_div_of_nonneg_right ((le_div_iff₀ hd).mpr hp) hf.le
    _ = r ^ 6 / ((r - 1) ^ 2 * f) := by rw [div_div]

/-! ## Scalar accounting in Lemmas 14.3 and 14.4 -/

theorem volume_relaxation {α : ℝ} (hα : 3 ≤ α) :
    α + 24 ≤ (27 / 4 : ℝ) * (α + 1) := by linarith

theorem work_mean_relaxation {α : ℝ} (hα : 3 ≤ α) :
    32 * α ≤ (3 / 8 : ℝ) * (α + 1) ^ 4 := by
  have hb : 0 ≤ α - 3 := sub_nonneg.mpr hα
  have hid : (3 / 8 : ℝ) * (α + 1) ^ 4 - 32 * α =
      (3 / 8 : ℝ) * (α - 3) ^ 4 + 6 * (α - 3) ^ 3 +
        36 * (α - 3) ^ 2 + 64 * (α - 3) := by ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

theorem one_window_scalar_bound {α d ρ κ : ℝ}
    (hα : 0 ≤ α + 1) (hd : 0 < d) (hρ : 0 < ρ) (hκ : 0 < κ) :
    (((27 / 4 : ℝ) * (α + 1) * d) / (ρ * κ)) *
        (((27 / 8 : ℝ) * (α + 1) ^ 4) / d) ≤
      (114 / 5 : ℝ) * (α + 1) ^ 5 / (ρ * κ) := by
  have heq :
      (((27 / 4 : ℝ) * (α + 1) * d) / (ρ * κ)) *
        (((27 / 8 : ℝ) * (α + 1) ^ 4) / d) =
      (729 / 32 : ℝ) * (α + 1) ^ 5 / (ρ * κ) := by
    field_simp [ne_of_gt hd, ne_of_gt hρ, ne_of_gt hκ]
    <;> ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ (mul_pos hρ hκ).le
  exact mul_le_mul_of_nonneg_right (by norm_num : (729 / 32 : ℝ) ≤ 114 / 5)
    (pow_nonneg hα 5)

/-! ## Actual windows stopped at the first error

The mask includes the possible erroneous tick at the end of its window.
It excludes every subsequent jump. Thus this is the actual counterpart of
D_ω times the event of a good start, not a counterfactual restarted process.
-/

def goodPrefix (C : XCTM Q) (z₀ : State (Sp C)) (n : ℕ) (ω : LabelPath C) : Prop :=
  ∀ m < n, ¬ BadTickAt C z₀ ω m

def windowActive (C : XCTM Q) (z₀ : State (Sp C)) (k n : ℕ)
    (ω : LabelPath C) : Prop :=
  tickCount C z₀ ω n = k ∧ goodPrefix C z₀ n ω

theorem measurableSet_goodPrefix (C : XCTM Q) (z₀ : State (Sp C)) (n : ℕ) :
    MeasurableSet {ω | goodPrefix C z₀ n ω} := by
  simp only [goodPrefix, Set.setOf_forall]
  exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    (measurableSet_badTickAt C z₀ m).compl

theorem measurableSet_windowActive (C : XCTM Q) (z₀ : State (Sp C)) (k n : ℕ) :
    MeasurableSet {ω | windowActive C z₀ k n ω} :=
  (measurableSet_eq_fun (measurable_tickCount C z₀ n) measurable_const).inter
    (measurableSet_goodPrefix C z₀ n)

noncomputable def goodWindowDuration (C : XCTM Q) (z₀ : State (Sp C))
    (ρ κ : ℝ) (k : ℕ) : TimedPath C → ℝ≥0∞ :=
  physicalStretch C z₀ (densityVolume C ρ) κ (windowActive C z₀ k)

noncomputable def goodWindowUnitMean (C : XCTM Q) (z₀ : State (Sp C)) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, maskedUnitCost C z₀ (windowActive C z₀ k) ω
    ∂rawLaw (net C) (net_hasPositiveRates C) z₀

theorem measurable_goodWindowDuration (C : XCTM Q) (z₀ : State (Sp C))
    (ρ κ : ℝ) (k : ℕ) : Measurable (goodWindowDuration C z₀ ρ κ k) :=
  measurable_physicalStretch C z₀ (densityVolume C ρ) κ
    (windowActive C z₀ k) (measurableSet_windowActive C z₀ k)

/-- Lemma 14.4 from its two explicit actual-law inputs. The unit-time input
is the occupation split, §13 work estimate, and terminal tick-wait estimate;
it is not proved merely by defining the scalar tickWait function. -/
theorem goodWindow_mean_le_of_estimates (C : XCTM Q) (z₀ : State (Sp C))
    (k : ℕ) (α d ρ κ : ℝ) (hα : 3 ≤ α) (hd : 0 < d)
    (hρ : 0 < ρ) (hκ : 0 < κ)
    (hLemmaFourteenThree : ∀ j ω, windowActive C z₀ k j ω →
      (moleculeCount C (pathState (net C) z₀ ω j) : ℝ) ≤ (α + 24) * d)
    (hLemmaFourteenFour_unitTime : goodWindowUnitMean C z₀ k ≤
      ENNReal.ofReal ((27 / 8 : ℝ) * (α + 1) ^ 4 / d)) :
    (∫⁻ η, goodWindowDuration C z₀ ρ κ k η
      ∂CTMCBridge.timedLaw (net C) (net_hasPositiveRates C) z₀) ≤
      ENNReal.ofReal ((114 / 5 : ℝ) * (α + 1) ^ 5 / (ρ * κ)) := by
  have hcount : ∀ j ω, windowActive C z₀ k j ω →
      (moleculeCount C (pathState (net C) z₀ ω j) : ℝ) ≤
        (27 / 4 : ℝ) * (α + 1) * d := by
    intro j ω hj
    exact (hLemmaFourteenThree j ω hj).trans
      (mul_le_mul_of_nonneg_right (volume_relaxation hα) hd.le)
  have hmean := physicalStretch_le_of_moleculeCount C z₀ ρ κ
    ((27 / 4 : ℝ) * (α + 1) * d) hρ hκ (windowActive C z₀ k)
    (measurableSet_windowActive C z₀ k) hcount
  change (∫⁻ η, goodWindowDuration C z₀ ρ κ k η
    ∂CTMCBridge.timedLaw (net C) (net_hasPositiveRates C) z₀) ≤
      ENNReal.ofReal (((27 / 4 : ℝ) * (α + 1) * d) / (ρ * κ)) *
        goodWindowUnitMean C z₀ k at hmean
  calc
    (∫⁻ η, goodWindowDuration C z₀ ρ κ k η
      ∂CTMCBridge.timedLaw (net C) (net_hasPositiveRates C) z₀) ≤
        ENNReal.ofReal (((27 / 4 : ℝ) * (α + 1) * d) / (ρ * κ)) *
          goodWindowUnitMean C z₀ k := hmean
    _ ≤ ENNReal.ofReal (((27 / 4 : ℝ) * (α + 1) * d) / (ρ * κ)) *
        ENNReal.ofReal ((27 / 8 : ℝ) * (α + 1) ^ 4 / d) := by
      gcongr
    _ = ENNReal.ofReal
        ((((27 / 4 : ℝ) * (α + 1) * d) / (ρ * κ)) *
          ((27 / 8 : ℝ) * (α + 1) ^ 4 / d)) := by
      rw [ENNReal.ofReal_mul (by positivity :
        0 ≤ ((27 / 4 : ℝ) * (α + 1) * d) / (ρ * κ))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (one_window_scalar_bound (by linarith) hd hρ hκ)

/-- Deterministic finite-hitting comparison. A missing tick is not assigned
zero duration: the existence premise is used to unfold the actual hitting time. -/
theorem physicalTickTime_le_goodWindowSum (C : XCTM Q) (z₀ : State (Sp C))
    (ρ κ : ℝ) (K : ℕ) (η : TimedPath C)
    (hNo : ¬ Error C z₀ η.1)
    (hHit : ∃ j, K ≤ tickCount C z₀ η.1 j) :
    physicalTickTime C z₀ (densityVolume C ρ) κ K η ≤
      ∑ k ∈ Finset.range K, goodWindowDuration C z₀ ρ κ k η := by
  let J := Nat.find hHit
  let F : ℕ → ℕ → ℝ≥0∞ := fun k j =>
    if windowActive C z₀ k j η.1 then physicalHolding C z₀ (densityVolume C ρ) κ j η else 0
  have hgood (j : ℕ) : goodPrefix C z₀ j η.1 := by
    intro m _ hm
    exact hNo ⟨m, hm⟩
  have hrow : ∀ j ∈ Finset.range J,
      (∑ k ∈ Finset.range K, F k j) =
        physicalHolding C z₀ (densityVolume C ρ) κ j η := by
    intro j hj
    have hjJ : j < Nat.find hHit := Finset.mem_range.mp hj
    have hc : tickCount C z₀ η.1 j < K :=
      lt_of_not_ge (Nat.find_min hHit hjJ)
    rw [Finset.sum_eq_single (tickCount C z₀ η.1 j)]
    · simp only [F, windowActive, true_and, hgood j, if_true]
    · intro k _ hk
      simp only [F, windowActive, Ne.symm hk, false_and, if_false]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hc))
  rw [physicalTickTime, dif_pos hHit]
  change (∑ j ∈ Finset.range J,
    physicalHolding C z₀ (densityVolume C ρ) κ j η) ≤ _
  calc
    (∑ j ∈ Finset.range J, physicalHolding C z₀ (densityVolume C ρ) κ j η) =
        ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K, F k j :=
      Finset.sum_congr rfl (fun j hj => (hrow j hj).symm)
    _ = ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range J, F k j := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range K, ∑' j, F k j :=
      Finset.sum_le_sum (fun k _ => ENNReal.sum_le_tsum _)
    _ = _ := rfl

theorem measurableSet_noErrorTimed (C : XCTM Q) (i : ℕ) (w : List Bool) :
    MeasurableSet (noErrorTimed C i w) :=
  (measurableSet_error C (initial C i w)).compl.preimage measurable_fst

/-- The progress supplied by ErrorClaim is transported through the label marginal. -/
theorem markedLaw_noError_progress (C : XCTM Q) (hLemmaSevenOne : ErrorClaim C)
    (i : ℕ) (w : List Bool) (δ : ℝ) (hacc : AdmissibleAccuracy w i δ) :
    ∀ᵐ η ∂markedLaw C i w,
      η ∈ noErrorTimed C i w → TickProgress C (initial C i w) η.1 := by
  have hp : ∀ᵐ ω ∂jumpLaw C i w,
      ¬ Error C (initial C i w) ω → TickProgress C (initial C i w) ω := by
    filter_upwards [(hLemmaSevenOne w i δ hacc).2.2] with ω hω hNo
    exact (hω hNo).1
  have hlabels : ∀ᵐ ω ∂(markedLaw C i w).map Prod.fst,
      ¬ Error C (initial C i w) ω → TickProgress C (initial C i w) ω := by
    change ∀ᵐ ω ∂(CTMCBridge.timedLaw (net C) (net_hasPositiveRates C)
      (initial C i w)).map Prod.fst,
      ¬ Error C (initial C i w) ω → TickProgress C (initial C i w) ω
    rw [CTMCBridge.timedLaw_map_labels]
    exact hp
  have hpull : ∀ᵐ η ∂markedLaw C i w,
      ¬ Error C (initial C i w) η.1 → TickProgress C (initial C i w) η.1 :=
    ae_of_ae_map measurable_fst.aemeasurable hlabels
  simpa only [noErrorTimed, Set.mem_setOf_eq] using hpull

/-- The numerator of the conditional mean is bounded by the actual good-window means. -/
theorem tickMean_numerator_le_windows (C : XCTM Q) (hLemmaSevenOne : ErrorClaim C)
    (i : ℕ) (w : List Bool) (δ ρ κ : ℝ) (hacc : AdmissibleAccuracy w i δ) (K : ℕ) :
    (∫⁻ η in noErrorTimed C i w,
      physicalTickTime C (initial C i w) (densityVolume C ρ) κ K η
        ∂markedLaw C i w) ≤
      ∑ k ∈ Finset.range K,
        ∫⁻ η, goodWindowDuration C (initial C i w) ρ κ k η ∂markedLaw C i w := by
  calc
    (∫⁻ η in noErrorTimed C i w,
      physicalTickTime C (initial C i w) (densityVolume C ρ) κ K η
        ∂markedLaw C i w) =
        ∫⁻ η, (noErrorTimed C i w).indicator
          (physicalTickTime C (initial C i w) (densityVolume C ρ) κ K) η
            ∂markedLaw C i w :=
      (lintegral_indicator (μ := markedLaw C i w)
        (measurableSet_noErrorTimed C i w)
        (physicalTickTime C (initial C i w) (densityVolume C ρ) κ K)).symm
    _ ≤ ∫⁻ η, ∑ k ∈ Finset.range K,
        goodWindowDuration C (initial C i w) ρ κ k η ∂markedLaw C i w := by
      apply lintegral_mono_ae
      filter_upwards [markedLaw_noError_progress C hLemmaSevenOne i w δ hacc]
        with η hη
      by_cases hNo : η ∈ noErrorTimed C i w
      · rw [Set.indicator_of_mem hNo]
        exact physicalTickTime_le_goodWindowSum C (initial C i w) ρ κ K η
          hNo ((hη hNo) K)
      · rw [Set.indicator_of_notMem hNo]
        exact bot_le
    _ = _ := lintegral_finsetSum (Finset.range K)
      (fun k _ => measurable_goodWindowDuration C (initial C i w) ρ κ k)

/-- The no-error denominator is bounded below using the actual marked-law marginal. -/
theorem noError_mass_lower (C : XCTM Q) (i : ℕ) (w : List Bool)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (herror : jumpLaw C i w {ω | Error C (initial C i w) ω} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (1 - δ) ≤ markedLaw C i w (noErrorTimed C i w) := by
  have hm : MeasurableSet {η : TimedPath C | Error C (initial C i w) η.1} :=
    (measurableSet_error C (initial C i w)).preimage measurable_fst
  change ENNReal.ofReal (1 - δ) ≤
    markedLaw C i w {η : TimedPath C | Error C (initial C i w) η.1}ᶜ
  rw [measure_compl hm (measure_ne_top _ _), measure_univ, markedLaw_error,
    ENNReal.ofReal_sub 1 hδ, ENNReal.ofReal_one]
  exact tsub_le_tsub_left herror 1

/-- Division by P(no-error), with positivity proved rather than tacitly assumed. -/
theorem conditionalTickMean_le_of_numerator (C : XCTM Q) (i : ℕ) (w : List Bool)
    (δ ρ κ A : ℝ) (K : ℕ) (hδ : 0 ≤ δ) (hδone : δ < 1) (hA : 0 ≤ A)
    (herror : jumpLaw C i w {ω | Error C (initial C i w) ω} ≤ ENNReal.ofReal δ)
    (hnum : (∫⁻ η in noErrorTimed C i w,
      physicalTickTime C (initial C i w) (densityVolume C ρ) κ K η
        ∂markedLaw C i w) ≤ ENNReal.ofReal A) :
    conditionalTickMean C i w ρ κ K ≤ ENNReal.ofReal (A / (1 - δ)) := by
  have hd : 0 < 1 - δ := sub_pos.mpr hδone
  have hp := noError_mass_lower C i w hδ herror
  have hpzero : markedLaw C i w (noErrorTimed C i w) ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos.mpr hd).trans_le hp)
  unfold conditionalTickMean
  apply (ENNReal.div_le_iff hpzero (measure_ne_top _ _)).mpr
  calc
    (∫⁻ η in noErrorTimed C i w,
      physicalTickTime C (initial C i w) (densityVolume C ρ) κ K η
        ∂markedLaw C i w) ≤ ENNReal.ofReal A := hnum
    _ = ENNReal.ofReal (A / (1 - δ)) * ENNReal.ofReal (1 - δ) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hA hd.le),
        div_mul_cancel₀ _ (ne_of_gt hd)]
    _ ≤ ENNReal.ofReal (A / (1 - δ)) *
        markedLaw C i w (noErrorTimed C i w) := by gcongr

noncomputable def windowAccuracy (i k : ℕ) : ℝ := (i : ℝ) + (k / 4 : ℕ)

noncomputable def windowPopulation (C : XCTM Q) (w : List Bool) (k : ℕ) : ℝ :=
  (stateCount (C.runT (C.start, w) (k / 4)).2.length : ℝ)

theorem windowPopulation_pos (C : XCTM Q) (w : List Bool) (k : ℕ) :
    0 < windowPopulation C w k := by
  unfold windowPopulation stateCount
  positivity

theorem windowAccuracy_ge_three (w : List Bool) (i k : ℕ) (δ : ℝ)
    (hacc : AdmissibleAccuracy w i δ) : 3 ≤ windowAccuracy i k := by
  have hlen : (w.length : ℝ) ≤ (i : ℝ) :=
    (le_max_left _ _).trans hacc.2.2.2
  have hw : (3 : ℝ) ≤ w.length := by exact_mod_cast hacc.1
  have hk : (0 : ℝ) ≤ (k / 4 : ℕ) := Nat.cast_nonneg _
  unfold windowAccuracy
  linarith

/-- Four windows per step, with the harmless rounding 22.8 ≤ 23. -/
theorem sum_window_budgets (i n : ℕ) (ρ κ : ℝ) (hρ : 0 < ρ) (hκ : 0 < κ) :
    (∑ k ∈ Finset.range (4 * n),
      ENNReal.ofReal ((114 / 5 : ℝ) * (windowAccuracy i k + 1) ^ 5 / (ρ * κ))) ≤
      ENNReal.ofReal (92 * (n : ℝ) * ((i : ℝ) + n) ^ 5 / (ρ * κ)) := by
  have hterm : ∀ k ∈ Finset.range (4 * n),
      ENNReal.ofReal ((114 / 5 : ℝ) * (windowAccuracy i k + 1) ^ 5 / (ρ * κ)) ≤
        ENNReal.ofReal (23 * ((i : ℝ) + n) ^ 5 / (ρ * κ)) := by
    intro k hk
    have hkn : k / 4 + 1 ≤ n := by
      have hk' := Finset.mem_range.mp hk
      omega
    have hknR : (k / 4 : ℕ) + (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hbase : windowAccuracy i k + 1 ≤ (i : ℝ) + n := by
      unfold windowAccuracy
      linarith
    have hbasepos : 0 ≤ windowAccuracy i k + 1 := by
      unfold windowAccuracy
      positivity
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (mul_pos hρ hκ).le
    exact mul_le_mul (by norm_num : (114 / 5 : ℝ) ≤ 23)
      (pow_le_pow_left₀ hbasepos hbase 5) (pow_nonneg hbasepos 5) (by norm_num)
  calc
    (∑ k ∈ Finset.range (4 * n),
      ENNReal.ofReal ((114 / 5 : ℝ) * (windowAccuracy i k + 1) ^ 5 / (ρ * κ))) ≤
        ∑ _k ∈ Finset.range (4 * n),
          ENNReal.ofReal (23 * ((i : ℝ) + n) ^ 5 / (ρ * κ)) :=
      Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (92 * (n : ℝ) * ((i : ℝ) + n) ^ 5 / (ρ * κ)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast (4 * n),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (4 * n))]
      congr 1
      push_cast
      ring

/-- Theorem 7.2 assembly. The remaining Lemma 14.4 estimate is exposed for
actual good-prefix window durations on the original marked law. It includes
its restart/occupation work; no independence or strong-Markov step is hidden. -/
theorem timeClaim_of_estimates (C : XCTM Q)
    (hLemmaSevenOne : ErrorClaim C)
    (hLemmaFourteenFour :
      ∀ (w : List Bool) (i : ℕ) (δ ρ κ : ℝ),
        AdmissibleAccuracy w i δ → δ < 1 → 0 < ρ → 0 < κ →
        ∀ n, BeforeHalt C w n → ∀ k, k < 4 * n →
          (∫⁻ η, goodWindowDuration C (initial C i w) ρ κ k η ∂markedLaw C i w) ≤
            ENNReal.ofReal ((114 / 5 : ℝ) * (windowAccuracy i k + 1) ^ 5 / (ρ * κ))) :
    TimeClaim C := by
  intro w i δ ρ κ hacc hδone hρ hκ n hbefore
  have herror : jumpLaw C i w {ω | Error C (initial C i w) ω} ≤ ENNReal.ofReal δ :=
    (hLemmaSevenOne w i δ hacc).1.trans
      (ENNReal.ofReal_le_ofReal (hLemmaSevenOne w i δ hacc).2.1)
  have hnum : (∫⁻ η in noErrorTimed C i w,
      physicalTickTime C (initial C i w) (densityVolume C ρ) κ (4 * n) η
        ∂markedLaw C i w) ≤
      ENNReal.ofReal (92 * (n : ℝ) * ((i : ℝ) + n) ^ 5 / (ρ * κ)) := by
    calc
      (∫⁻ η in noErrorTimed C i w,
        physicalTickTime C (initial C i w) (densityVolume C ρ) κ (4 * n) η
          ∂markedLaw C i w) ≤
          ∑ k ∈ Finset.range (4 * n),
            ∫⁻ η, goodWindowDuration C (initial C i w) ρ κ k η ∂markedLaw C i w :=
        tickMean_numerator_le_windows C hLemmaSevenOne i w δ ρ κ hacc (4 * n)
      _ ≤ ∑ k ∈ Finset.range (4 * n),
          ENNReal.ofReal ((114 / 5 : ℝ) * (windowAccuracy i k + 1) ^ 5 / (ρ * κ)) :=
        Finset.sum_le_sum (fun k hk =>
          hLemmaFourteenFour w i δ ρ κ hacc hδone hρ hκ n hbefore k
            (Finset.mem_range.mp hk))
      _ ≤ _ := sum_window_budgets i n ρ κ hρ hκ
  have h := conditionalTickMean_le_of_numerator C i w δ ρ κ
    (92 * (n : ℝ) * ((i : ℝ) + n) ^ 5 / (ρ * κ)) (4 * n)
    hacc.2.1.le hδone (by positivity) herror hnum
  have heq : (92 * (n : ℝ) * ((i : ℝ) + n) ^ 5 / (ρ * κ)) / (1 - δ) =
      92 * (n : ℝ) * ((i : ℝ) + n) ^ 5 / ((1 - δ) * ρ * κ) := by
    have hδne : (1 - δ) ≠ 0 := ne_of_gt (sub_pos.mpr hδone)
    field_simp [hδne, ne_of_gt hρ, ne_of_gt hκ]
    <;> ring
  rw [heq] at h
  exact h

/-- A more decomposed reducer: the two open quantitative hypotheses are
Lemma 14.3 and the unit-rate part of Lemma 14.4 (from Lemma 8.3, §13, and
the terminal-clock hitting-time identification). Both refer to actual paths. -/
theorem timeClaim_of_volume_and_unit_estimates (C : XCTM Q)
    (hLemmaSevenOne : ErrorClaim C)
    (hLemmaFourteenThree :
      ∀ (w : List Bool) (i : ℕ) (δ : ℝ), AdmissibleAccuracy w i δ →
        ∀ n, BeforeHalt C w n → ∀ k, k < 4 * n → ∀ j ω,
          windowActive C (initial C i w) k j ω →
          (moleculeCount C (pathState (net C) (initial C i w) ω j) : ℝ) ≤
            (windowAccuracy i k + 24) * windowPopulation C w k)
    (hLemmaFourteenFour_unitTime :
      ∀ (w : List Bool) (i : ℕ) (δ : ℝ), AdmissibleAccuracy w i δ →
        ∀ n, BeforeHalt C w n → ∀ k, k < 4 * n →
          goodWindowUnitMean C (initial C i w) k ≤
            ENNReal.ofReal ((27 / 8 : ℝ) * (windowAccuracy i k + 1) ^ 4 /
              windowPopulation C w k)) :
    TimeClaim C := by
  apply timeClaim_of_estimates C hLemmaSevenOne
  intro w i δ ρ κ hacc _hδone hρ hκ n hbefore k hk
  exact goodWindow_mean_le_of_estimates C (initial C i w) k
    (windowAccuracy i k) (windowPopulation C w k) ρ κ
    (windowAccuracy_ge_three w i k δ hacc) (windowPopulation_pos C w k) hρ hκ
    (hLemmaFourteenThree w i δ hacc n hbefore k hk)
    (hLemmaFourteenFour_unitTime w i δ hacc n hbefore k hk)

/-! ## The TM-time corollary: all numerical and encoding reductions -/

theorem accuracyIndex_admissible (w : List Bool) (δ : ℝ)
    (hw : 3 ≤ w.length) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    AdmissibleAccuracy w (accuracyIndex w.length δ) δ := by
  refine ⟨hw, hδ, hδone, max_le ?_ ?_⟩
  · exact_mod_cast (le_max_left w.length (1 + ⌈37 / Real.sqrt δ⌉₊))
  · have hceil : 37 / Real.sqrt δ ≤ (⌈37 / Real.sqrt δ⌉₊ : ℝ) := Nat.le_ceil _
    have hmax :
        ((1 + ⌈37 / Real.sqrt δ⌉₊ : ℕ) : ℝ) ≤
          (accuracyIndex w.length δ : ℝ) := by
      exact_mod_cast (le_max_right w.length (1 + ⌈37 / Real.sqrt δ⌉₊))
    push_cast at hmax
    linarith

theorem accuracyIndex_le (s : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (accuracyIndex s δ : ℝ) ≤ (s : ℝ) + 2 + 37 / Real.sqrt δ := by
  have hq : 0 ≤ 37 / Real.sqrt δ := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hc := Nat.ceil_lt_add_one hq
  unfold accuracyIndex
  rw [Nat.cast_max]
  apply max_le
  · linarith
  · push_cast
    linarith [Nat.cast_nonneg (α := ℝ) s]

/-- The exact TMTimeClaim follows from TimeClaim for xctmOf M. The paper's
552 and its precision/space polynomial are derived, not supplied as premises. -/
theorem tmTimeClaim_of_timeClaim
    {QM : Type} [Fintype QM] [DecidableEq QM]
    (M : TM.Machine QM Bool) (hTime : TimeClaim (xctmOf M)) : TMTimeClaim M := by
  intro hb s input δ ρ κ hs hi hδ hδone hρ hκ t _hactive
  let c := xInputCfg M s input
  let st := tlen (tmRun M c t).tape
  let n := xTime M c t
  let i := accuracyIndex (2 * s + 2) δ
  have hlen := xInputTape_encoding_length s input hs hi
  have hacc := accuracyIndex_admissible (xencT (xInputTape s input)) δ
    (by rw [hlen]; omega) hδ hδone.le
  rw [hlen] at hacc
  change AdmissibleAccuracy (xencT (xInputTape s input)) i δ at hacc
  have hbefore : BeforeHalt (xctmOf M) (xencT (xInputTape s input)) n := by
    intro j hj
    change (xctmOf M).mode ((xctmOf M).runT (xencC c.state c.tape) j).1 ≠ .halt
    exact xctm_no_halt_before_boundary M hb c t (Nat.le_of_lt hj)
  have hbase := hTime (xencT (xInputTape s input)) i δ ρ κ
    hacc hδone hρ hκ n hbefore
  have hn : (n : ℝ) ≤ 6 * ((st : ℝ) + 1) * (t : ℝ) := by
    have hn' : (n : ℝ) ≤ (6 * (st : ℝ) + 6) * (t : ℝ) := by
      exact_mod_cast xTime_le_linear M c t
    nlinarith
  have hi' : (i : ℝ) ≤ 37 / Real.sqrt δ + 2 * (s : ℝ) + 4 := by
    have h := accuracyIndex_le (2 * s + 2) δ hδ
    change (i : ℝ) ≤ ((2 * s + 2 : ℕ) : ℝ) + 2 + 37 / Real.sqrt δ at h
    push_cast at h
    linarith
  have hpow : ((i : ℝ) + n) ^ 5 ≤
      (37 / Real.sqrt δ + 2 * (s : ℝ) + 4 +
        6 * ((st : ℝ) + 1) * t) ^ 5 :=
    pow_le_pow_left₀ (by positivity) (add_le_add hi' hn) 5
  have hcoef : 92 * (n : ℝ) ≤ 552 * ((st : ℝ) + 1) * (t : ℝ) := by
    nlinarith
  have hden : 0 < (1 - δ) * ρ * κ := mul_pos (mul_pos (sub_pos.mpr hδone) hρ) hκ
  change conditionalTickMean (xctmOf M) i (xencT (xInputTape s input)) ρ κ (4 * n) ≤
    ENNReal.ofReal
      (552 * ((st : ℝ) + 1) * (t : ℝ) *
        (37 / Real.sqrt δ + 2 * (s : ℝ) + 4 +
          6 * ((st : ℝ) + 1) * t) ^ 5 / ((1 - δ) * ρ * κ))
  apply hbase.trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ hden.le
  exact mul_le_mul hcoef hpow (by positivity) (by positivity)

end Ripple.sCRNUniversality.ClockedCTM.Unbounded.TimeAnalysis
