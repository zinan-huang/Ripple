-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockThinningCalibrated.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinning

/-!
# Numerically specialized raw clock-contact windows

These are the two raw-time conversions in PHASE3 P10, with the numerical
lengths substituted and all probability factors retained on the original
pair-log law. The upper contact count uses a floor of 70 m^2/C, which is
slightly smaller than the paper's auxiliary 70.2 m^2/C budget.

The events concern recorded physical pairs. They are not reconstructed
from configuration transitions. This file does not construct the hour
endpoints or the front passages whose embedded tick budgets are separate
inputs to the full step-3 producer.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockThinningCalibrated

open TimeTheorem PairLog PhaseThreeClockGatedLaw
  PhaseThreeClockThinning PhaseThreeClockPrefixTails PhaseThreeScalar

variable {L K : ℕ}

noncomputable def shortHourRaw (m C : ℕ) : ℕ :=
  Nat.floor (70 * (m : ℝ) ^ 2 / (C : ℝ))

def fineRaw (m d : ℕ) : ℕ := 2000 * m * d

theorem clockMaskRate_nonneg (m C : ℕ) (hm : 2 ≤ m) :
    0 ≤ clockMaskRate m C := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  unfold clockMaskRate
  exact div_nonneg (by positivity) (mul_nonneg (by positivity) (by linarith))

theorem clockMaskRate_le_square (m C : ℕ) (hm : 2 ≤ m)
    (hC : 1 ≤ C) (hCm : C ≤ m) :
    clockMaskRate m C ≤ (C : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCmR : (C : ℝ) ≤ (m : ℝ) := by exact_mod_cast hCm
  have hmp : 0 < (m : ℝ) := by linarith
  have hsub : 0 < (m : ℝ) - 1 := by linarith
  have hden : 0 < (m : ℝ) * ((m : ℝ) - 1) := mul_pos hmp hsub
  rw [clockMaskRate_eq_real m C hC]
  apply (div_le_div_iff₀ hden (by positivity : 0 < (m : ℝ) ^ 2)).2
  have hp := mul_nonneg (by positivity : 0 ≤ (C : ℝ) * (m : ℝ))
    (sub_nonneg.mpr hCmR)
  nlinarith only [hp]

theorem fine_contact_mean (m C d : ℕ) (hm : 400 ≤ m)
    (hdensity : 6 * m ≤ 25 * C) :
    2 * (200 * (d : ℝ) * (C : ℝ)) ≤
      clockMaskRate m C * (fineRaw m d : ℝ) := by
  have hmR : (400 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdR : 6 * (m : ℝ) ≤ 25 * (C : ℝ) := by exact_mod_cast hdensity
  have hC : 1 ≤ C := by omega
  have hroom : (m : ℝ) - 1 ≤ 5 * ((C : ℝ) - 1) := by linarith
  have hp := mul_le_mul_of_nonneg_left hroom
    (by positivity : 0 ≤ 400 * (d : ℝ) * (C : ℝ) * (m : ℝ))
  rw [clockMaskRate_eq_real m C hC, div_mul_eq_mul_div]
  simp only [fineRaw, Nat.cast_mul, Nat.cast_ofNat]
  have hden : 0 < (m : ℝ) * ((m : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  apply (le_div_iff₀ hden).2
  nlinarith only [hp]

theorem short_hour_contact_mean (m C : ℕ) (hm : 2 ≤ m)
    (hC : 1 ≤ C) (hCm : C ≤ m) :
    clockMaskRate m C * (shortHourRaw m C : ℝ) ≤
      3 * ((468 / 5 : ℝ) * (C : ℝ)) / 4 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCR : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hfloor : (shortHourRaw m C : ℝ) ≤ 70 * (m : ℝ) ^ 2 / (C : ℝ) :=
    Nat.floor_le (by positivity)
  have hq := clockMaskRate_le_square m C hm hC hCm
  have hprod := mul_le_mul hq hfloor
    (by positivity : 0 ≤ (shortHourRaw m C : ℝ))
    (by positivity : 0 ≤ (C : ℝ) ^ 2 / (m : ℝ) ^ 2)
  have heq : ((C : ℝ) ^ 2 / (m : ℝ) ^ 2) *
      (70 * (m : ℝ) ^ 2 / (C : ℝ)) = 70 * (C : ℝ) := by
    field_simp [show (m : ℝ) ≠ 0 by linarith,
      show (C : ℝ) ≠ 0 by linarith] <;> ring
  rw [heq] at hprod
  linarith

/-- The contact count is measurable at the endpoint of its raw interval. -/
theorem maskTickCount_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (u N : ℕ) :
    StronglyMeasurable[pairLogFiltration L K (u + N)]
      (maskTickCount init C u N) := by
  have hI : ∀ t,
      StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u (t + 1)]
        (maskTickIndicator init C (u + t)) := by
    intro t
    simpa only [shiftedFiltration_apply, Nat.add_assoc] using
      maskTickIndicator_stronglyMeasurable init C (u + t)
  simpa only [shiftedFiltration_apply, maskTickCount] using
    bernoulliCount_stronglyMeasurable hI N

/-- Every Borel comparison of the reviewed physical contact count is
measurable at the endpoint, on a genuine prefix with a known Clock mask. -/
theorem prefix_contact_comparison_measurable {n : ℕ} (init : InputCfg n)
    (C : Finset (Fin init.card)) (S u N : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C)
    (R : ℝ → Prop) (hR : MeasurableSet {x : ℝ | R x}) :
    MeasurableSet[pairLogFiltration _ _ (u + N)]
      (E ∩ {ω | R (StageEventSpec.clockContacts init ω S u (u + N) : ℝ)}) := by
  have hEend : MeasurableSet[pairLogFiltration _ _ (u + N)] E :=
    ((pairLogFiltration _ _).mono (by omega : u ≤ u + N)) _ hE
  have heq : E ∩ {ω | R (StageEventSpec.clockContacts init ω S u (u + N) : ℝ)} =
      E ∩ {ω | R (maskTickCount init C u N ω)} := by
    ext ω
    constructor
    · rintro ⟨hω, hr⟩
      refine ⟨hω, ?_⟩
      simp only [Set.mem_setOf_eq] at hr ⊢
      rw [maskTickCount_eq_contacts, ← hmask ω hω, maskContacts_seed_eq_stageEvent]
      exact hr
    · rintro ⟨hω, hr⟩
      simp only [Set.mem_setOf_eq] at hr ⊢
      rw [maskTickCount_eq_contacts, ← hmask ω hω,
        maskContacts_seed_eq_stageEvent] at hr
      exact ⟨hω, hr⟩
  rw [heq]
  exact hEend.inter (hR.preimage (maskTickCount_stronglyMeasurable init C u N).measurable)

/-- A prefix-weighted shortage estimate at exactly 2000*m*d raw steps. -/
theorem fine_contact_prefix_tail {n : ℕ} (init : InputCfg n)
    (hm : 400 ≤ init.card) (C : Finset (Fin init.card))
    (hdensity : 6 * init.card ≤ 25 * C.card) (S u d : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C) :
    law init (E ∩ {ω |
        (StageEventSpec.clockContacts init ω S u (u + fineRaw init.card d) : ℝ) <
          200 * (d : ℝ) * (C.card : ℝ)}) ≤
      ENNReal.ofReal (Real.exp (-50 * (d : ℝ) * (C.card : ℝ))) * law init E := by
  have ht := prefix_stageEvent_clockContacts_lower_tail_ennreal init (by omega)
    C S u (fineRaw init.card d) E hE hmask
    (200 * (d : ℝ) * (C.card : ℝ)) (by positivity)
    (fine_contact_mean init.card C.card d hm hdensity)
  have heq : -(200 * (d : ℝ) * (C.card : ℝ)) / 4 =
      -50 * (d : ℝ) * (C.card : ℝ) := by ring
  simpa only [heq] using ht

/-- The contact event that prevents a 468*C/5-tick hour from fitting in
floor(70*m^2/C) raw steps. -/
theorem short_hour_contact_prefix_tail {n : ℕ} (init : InputCfg n)
    (hm : 2 ≤ init.card) (C : Finset (Fin init.card)) (hC : 1 ≤ C.card)
    (S u : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C) :
    law init (E ∩ {ω |
        (468 / 5 : ℝ) * (C.card : ℝ) ≤
          (StageEventSpec.clockContacts init ω S u
            (u + shortHourRaw init.card C.card) : ℝ)}) ≤
      ENNReal.ofReal (Real.exp (-(13 / 5 : ℝ) * (C.card : ℝ))) * law init E := by
  have hCm : C.card ≤ init.card := by simpa using Finset.card_le_univ C
  have ht := prefix_stageEvent_clockContacts_upper_tail_ennreal init hm
    C S u (shortHourRaw init.card C.card) E hE hmask
    ((468 / 5 : ℝ) * (C.card : ℝ)) (by positivity)
    (short_hour_contact_mean init.card C.card hm hC hCm)
  have heq : -((468 / 5 : ℝ) * (C.card : ℝ)) / 36 =
      -(13 / 5 : ℝ) * (C.card : ℝ) := by ring
  simpa only [heq] using ht

theorem clockContacts_mono_right {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S u v w : ℕ) (hvw : v ≤ w) :
    StageEventSpec.clockContacts init ω S u v ≤
      StageEventSpec.clockContacts init ω S u w := by
  classical
  apply Finset.card_le_card
  intro k hk
  simp only [StageEventSpec.clockContacts, Finset.mem_filter, Finset.mem_Ioc] at hk ⊢
  exact ⟨⟨hk.1.1, hk.1.2.trans hvw⟩, hk.2⟩

/-- Uniform over every proposed endpoint inside the short raw interval.
A later hour proof can use this event by a pathwise inclusion. -/
theorem short_hour_endpoint_prefix_tail {n : ℕ} (init : InputCfg n)
    (hm : 2 ≤ init.card) (C : Finset (Fin init.card)) (hC : 1 ≤ C.card)
    (S u : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C) :
    law init (E ∩ {ω | ∃ v ≤ u + shortHourRaw init.card C.card,
      (468 / 5 : ℝ) * (C.card : ℝ) ≤
        (StageEventSpec.clockContacts init ω S u v : ℝ)}) ≤
      ENNReal.ofReal (Real.exp (-(13 / 5 : ℝ) * (C.card : ℝ))) * law init E := by
  apply (measure_mono ?_).trans
    (short_hour_contact_prefix_tail init hm C hC S u E hE hmask)
  rintro ω ⟨hω, v, hv, hcount⟩
  refine ⟨hω, hcount.trans ?_⟩
  exact_mod_cast clockContacts_mono_right init ω S u v
    (u + shortHourRaw init.card C.card) hv

/-- The named numerical calibration makes both thinning errors smaller
than C^(-100). -/
theorem thinning_exponential_calibration (m C : ℕ)
    (hm : PhaseThreeModel.Numeric.populationThreshold ≤ m)
    (hdensity : (6 / 25 : ℝ) * (m : ℝ) ≤ (C : ℝ))
    (hCm : C ≤ m) :
    400 ≤ m ∧ 1 ≤ C ∧
    Real.exp (-50 * (PhaseThreeModel.Numeric.frontWidth C : ℝ) * (C : ℝ)) ≤
      (C : ℝ) ^ (-100 : ℝ) ∧
    Real.exp (-(13 / 5 : ℝ) * (C : ℝ)) ≤ (C : ℝ) ^ (-100 : ℝ) := by
  obtain ⟨hCp, hx, hxy, hyx, hxdouble, hd, hdmiddle, hdlast,
    hH, hQ, hxC, hQC, hHn, hwidth⟩ :=
    PhaseThreeModel.Numeric.numeric_calibration_core hm hdensity hCm
  have hClarge : (400 : ℝ) ≤ (C : ℝ) := by
    have h := Real.add_one_le_exp (Real.log (C : ℝ))
    rw [Real.exp_log hCp] at h
    linarith
  have hCnat : 400 ≤ C := by exact_mod_cast hClarge
  have hdR : (38 : ℝ) ≤ (PhaseThreeModel.Numeric.frontWidth C : ℝ) := by
    exact_mod_cast hd
  have hprod := mul_nonneg (sub_nonneg.mpr hdR) hCp.le
  refine ⟨hCnat.trans hCm, by omega, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hCp]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [Real.rpow_def_of_pos hCp]
    apply Real.exp_le_exp.mpr
    linarith

/-- P10's fine raw length and polynomial error, with d fixed to the
compiled Numeric.frontWidth and all numerical hypotheses discharged. -/
theorem fine_contact_prefix_calibrated {n : ℕ} (init : InputCfg n)
    (hm : PhaseThreeModel.Numeric.populationThreshold ≤ init.card)
    (C : Finset (Fin init.card))
    (hdensity : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (S u : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C) :
    law init (E ∩ {ω |
        (StageEventSpec.clockContacts init ω S u
          (u + 2000 * init.card * PhaseThreeModel.Numeric.frontWidth C.card) : ℝ) <
        (PhaseThreeModel.Numeric.fineTicks C.card : ℝ)}) ≤
      ENNReal.ofReal ((C.card : ℝ) ^ (-100 : ℝ)) * law init E := by
  have hCm : C.card ≤ init.card := by simpa using Finset.card_le_univ C
  obtain ⟨hmfour, hC, hfine, hhour⟩ :=
    thinning_exponential_calibration init.card C.card hm hdensity hCm
  have hdensityN : 6 * init.card ≤ 25 * C.card := by
    have h : 6 * (init.card : ℝ) ≤ 25 * (C.card : ℝ) := by linarith
    exact_mod_cast h
  have ht := fine_contact_prefix_tail init hmfour C hdensityN S u
    (PhaseThreeModel.Numeric.frontWidth C.card) E hE hmask
  refine le_trans ?_ (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hfine) _)
  simpa only [fineRaw, PhaseThreeModel.Numeric.fineTicks,
    Nat.cast_mul, Nat.cast_ofNat] using ht

theorem short_hour_prefix_calibrated {n : ℕ} (init : InputCfg n)
    (hm : PhaseThreeModel.Numeric.populationThreshold ≤ init.card)
    (C : Finset (Fin init.card))
    (hdensity : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (S u : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω S) = C) :
    law init (E ∩ {ω | ∃ v ≤ u + shortHourRaw init.card C.card,
      (468 / 5 : ℝ) * (C.card : ℝ) ≤
        (StageEventSpec.clockContacts init ω S u v : ℝ)}) ≤
      ENNReal.ofReal ((C.card : ℝ) ^ (-100 : ℝ)) * law init E := by
  have hCm : C.card ≤ init.card := by simpa using Finset.card_le_univ C
  obtain ⟨hmfour, hC, hfine, hhour⟩ :=
    thinning_exponential_calibration init.card C.card hm hdensity hCm
  exact (short_hour_endpoint_prefix_tail init (by omega) C hC S u E hE hmask).trans
    (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hhour) _)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockThinningCalibrated

end
