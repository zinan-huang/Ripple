-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMarkedClockRates.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockImmigrationTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSharpActivationSeed
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkCalibration

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedClockRates

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockEmbeddingBridge PhaseThreeClockPredictablePairs
  PhaseThreeClockEarlyMarks PhaseThreeClockEarlyMarkEmbedding PhaseThreeClockEarlyMarkRates
  PhaseThreeClockImmigrationTails PhaseThreeClockThinning
  PhaseThreeClockActivationLaw PhaseThreeClockActivationSeed PhaseThreeClockSeedTails
  PhaseThreeClockSmallActivation PhaseThreeClockSharpActivationSeed
  PhaseThreeClockActivationCalibration

variable {L K m : ℕ}

theorem markedCount_stronglyMeasurable (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) :
    StronglyMeasurable[pairLogFiltration L K t]
      (fun ω => ((markedAt init C ℓ cutoff s ω t).card : ℝ)) :=
  ((measurable_of_countable (fun p : (k : Finset.Iic t) → Draw L K =>
      ((markedPrefix init C ℓ cutoff s t p).card : ℝ))).comp
        (measurable_pairLog_prefix L K t)).stronglyMeasurable

theorem propagationIndicator_le_clockTick (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L K) :
    propagationIndicator init C ℓ cutoff s t ω ≤ maskTickIndicator init C t ω := by
  classical
  by_cases hp : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
      Propagation C (markedAt init C ℓ cutoff s ω t) i j
  · obtain ⟨i, j, hd, hm⟩ := hp
    have hsub := markedAt_subset_mask init C ℓ cutoff s ω t
    have hpair : i ∈ C ∧ j ∈ C := by
      rcases hm with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact ⟨hsub hi, (Finset.mem_sdiff.mp hj).1⟩
      · exact ⟨(Finset.mem_sdiff.mp hi).1, hsub hj⟩
    have htick : maskContact init C (t + 1) ω := ⟨i, j, hd, hpair⟩
    have hprop : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
        Propagation C (markedAt init C ℓ cutoff s ω t) i j := ⟨i, j, hd, hm⟩
    simp only [propagationIndicator, if_pos hprop, maskTickIndicator, if_pos htick, le_refl]
  · rw [propagationIndicator, if_neg hp]
    unfold maskTickIndicator
    split_ifs <;> norm_num

theorem immigrationIndicator_le_clockTick (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) (ω : Ω L K) :
    immigrationIndicator init C ℓ cutoff t ω ≤ maskTickIndicator init C t ω := by
  classical
  by_cases hp : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
      EarlyDrip C (virtualLabels init ω t) ℓ cutoff i j
  · obtain ⟨i, j, hd, hm⟩ := hp
    have hi := sourceSet_subset C (virtualLabels init ω t) ℓ hm.2.2.1
    have hj := sourceSet_subset C (virtualLabels init ω t) ℓ hm.2.2.2
    have htick : maskContact init C (t + 1) ω := ⟨i, j, hd, hi, hj⟩
    have himm : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
        EarlyDrip C (virtualLabels init ω t) ℓ cutoff i j := ⟨i, j, hd, hm⟩
    simp only [immigrationIndicator, if_pos himm, maskTickIndicator, if_pos htick, le_refl]
  · rw [immigrationIndicator, if_neg hp]
    unfold maskTickIndicator
    split_ifs <;> norm_num

theorem maskedImmigrationIndicator_le_immigration (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) (ω : Ω L K) :
    maskedImmigrationIndicator init C ℓ cutoff t ω ≤ immigrationIndicator init C ℓ cutoff t ω := by
  classical
  by_cases hp : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
      MaskedDrip C (virtualLabels init ω t) ℓ cutoff i j
  · obtain ⟨i, j, hd, hm⟩ := hp
    have himm : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
        EarlyDrip C (virtualLabels init ω t) ℓ cutoff i j := ⟨i, j, hd, hm.2⟩
    have hmasked : ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
        MaskedDrip C (virtualLabels init ω t) ℓ cutoff i j := ⟨i, j, hd, hm⟩
    simp only [maskedImmigrationIndicator, if_pos hmasked, immigrationIndicator,
      if_pos himm, le_refl]
  · rw [maskedImmigrationIndicator, if_neg hp]
    unfold immigrationIndicator
    split_ifs <;> norm_num

theorem maskedImmigrationIndicator_le_clockTick (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) (ω : Ω L K) :
    maskedImmigrationIndicator init C ℓ cutoff t ω ≤ maskTickIndicator init C t ω :=
  (maskedImmigrationIndicator_le_immigration init C ℓ cutoff t ω).trans
    (immigrationIndicator_le_clockTick init C ℓ cutoff t ω)

theorem propagation_clock_rate_le (N C E : ℝ)
    (hN : 2 ≤ N) (hC : 2 ≤ C) :
    2 * E * (C - E) / (N * (N - 1)) ≤
      (C * (C - 1) / (N * (N - 1))) * (2 / (C - 1)) * E := by
  have hNp : 0 < N := by linarith
  have hden : 0 < N * (N - 1) := mul_pos hNp (by linarith)
  have hCm : C - 1 ≠ 0 := by linarith
  have hNm : N - 1 ≠ 0 := by linarith
  have hid :
      (C * (C - 1) / (N * (N - 1))) * (2 / (C - 1)) * E =
        (2 * C * E) / (N * (N - 1)) := by
    field_simp [hCm, ne_of_gt hNp, hNm]
    <;> ring
  rw [hid]
  apply div_le_div_of_nonneg_right _ hden.le
  nlinarith [sq_nonneg E]

theorem immigration_clock_rate_le (N C B r : ℝ)
    (hN : 2 ≤ N) (hC : 2 ≤ C) (hr : r ≤ B ^ 2) :
    r / (N * (N - 1)) ≤
      (C * (C - 1) / (N * (N - 1))) * (2 * B ^ 2 / C ^ 2) := by
  have hNp : 0 < N := by linarith
  have hCp : 0 < C := by linarith
  have hNm : N - 1 ≠ 0 := by linarith
  have hden : 0 < N * (N - 1) := mul_pos hNp (by linarith)
  have hid :
      (C * (C - 1) / (N * (N - 1))) * (2 * B ^ 2 / C ^ 2) =
        (2 * B ^ 2 * (C - 1) / C) / (N * (N - 1)) := by
    field_simp [ne_of_gt hCp, ne_of_gt hNp, hNm]
    <;> ring
  rw [hid]
  apply div_le_div_of_nonneg_right _ hden.le
  apply hr.trans
  apply (le_div_iff₀ hCp).2
  have hprod := mul_nonneg (sq_nonneg B) (sub_nonneg.mpr hC)
  nlinarith

theorem propagation_conditional_clock_bound (init : Cfg L K) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 2 ≤ C.card) (ℓ cutoff s t : ℕ) :
    (law init)[propagationIndicator init C ℓ cutoff s t | pairLogFiltration L K t]
      ≤ᵐ[law init] fun ω =>
        clockMaskRate init.card C.card * (2 / ((C.card : ℝ) - 1)) *
          ((markedAt init C ℓ cutoff s ω t).card : ℝ) := by
  filter_upwards [propagation_conditional_law init hc C ℓ cutoff s t] with ω hω
  rw [hω, clockMaskRate_eq_real _ _ (by omega)]
  have hM := Finset.card_le_card (markedAt_subset_mask init C ℓ cutoff s ω t)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hM]
  apply propagation_clock_rate_le
  · exact_mod_cast hc
  · exact_mod_cast hC

theorem maskedImmigration_conditional_clock_bound (init : Cfg L K) (hc : 2 ≤ init.card)
    (C : Finset (Fin init.card)) (hC : 2 ≤ C.card) (ℓ cutoff t : ℕ) :
    (law init)[maskedImmigrationIndicator init C ℓ cutoff t | pairLogFiltration L K t]
      ≤ᵐ[law init] fun _ =>
        clockMaskRate init.card C.card * (2 * (cutoff : ℝ) ^ 2 / (C.card : ℝ) ^ 2) := by
  have h := prefix_pair_conditional_probability init hc t
    (fun p => MaskedDrip C (auxPrefix init virtualRule t p) ℓ cutoff)
  filter_upwards [h] with ω hω
  have hce :
      (law init)[maskedImmigrationIndicator init C ℓ cutoff t |
        pairLogFiltration L K t] ω =
      ((pairSet (MaskedDrip C (virtualLabels init ω t) ℓ cutoff)).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
    simpa only [maskedImmigrationIndicator, virtualLabels, auxLabels] using hω
  rw [hce, clockMaskRate_eq_real _ _ (by omega)]
  apply immigration_clock_rate_le
  · exact_mod_cast hc
  · exact_mod_cast hC
  · exact_mod_cast maskedDrip_pairSet_card_le C (virtualLabels init ω t) ℓ cutoff

theorem frontCount_succ_le (f : Fin m → AgentState L K) (ℓ : ℕ) :
    frontCount f (ℓ + 1) ≤ frontCount f ℓ := by
  apply Finset.card_le_card
  intro i hi
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, (Nat.le_succ ℓ).trans hi.2⟩

theorem immigrationIndicator_eq_zero_of_front_zero (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff t : ℕ) (ω : Ω L K)
    (hmask : C = clockSet (virtualLabels init ω t))
    (hz : frontCount (virtualLabels init ω t) ℓ = 0) :
    immigrationIndicator init C ℓ cutoff t ω = 0 := by
  classical
  have hcard : (sourceSet C (virtualLabels init ω t) ℓ).card ≤
      frontCount (virtualLabels init ω t) ℓ := by
    simpa only [hmask] using sourceSet_card_le_front (virtualLabels init ω t) ℓ
  have he : sourceSet C (virtualLabels init ω t) ℓ = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  have hnot : ¬ ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
      EarlyDrip C (virtualLabels init ω t) ℓ cutoff i j := by
    rintro ⟨i, j, -, hi⟩
    have hm := hi.2.2.1
    rw [he] at hm
    simpa using hm
  simp only [immigrationIndicator, if_neg hnot]

theorem propagationIndicator_eq_zero_of_marks_empty (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ) (ω : Ω L K)
    (hM : markedAt init C ℓ cutoff s ω t = ∅) :
    propagationIndicator init C ℓ cutoff s t ω = 0 := by
  classical
  simp [propagationIndicator, Propagation, hM]

variable {n : ℕ}

theorem clock_upper_from_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (s : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hmask : C = clockSet (labelsAt init ω s)) :
    25 * C.card ≤ 7 * init.card := by
  have hmain := hseed.2.role_good.2.1
  have hreserve := hseed.2.role_good.2.2.2.2
  have hsum := RoleSplitConcentration.roleCount_conservation (trace init ω s)
  rw [hseed.2.card_eq] at hsum
  have hthree :
      RoleSplitConcentration.mainCount (trace init ω s) +
        RoleSplitConcentration.reserveCount (trace init ω s) +
        RoleSplitConcentration.clockCount (trace init ω s) ≤ n := by omega
  have hthreeR :
      (RoleSplitConcentration.mainCount (trace init ω s) : ℝ) +
        (RoleSplitConcentration.reserveCount (trace init ω s) : ℝ) +
        (RoleSplitConcentration.clockCount (trace init ω s) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hthree
  have hupperR : (25 : ℝ) *
      (RoleSplitConcentration.clockCount (trace init ω s) : ℝ) ≤ 7 * (n : ℝ) := by
    linarith
  have hupper : 25 * RoleSplitConcentration.clockCount (trace init ω s) ≤ 7 * n := by
    exact_mod_cast hupperR
  rw [← clockCount_labelsAt_eq_trace init ω s] at hupper
  have hcount : clockCount (labelsAt init ω s) = C.card := by
    change (clockSet (labelsAt init ω s)).card = C.card
    rw [← hmask]
  rw [hcount] at hupper
  calc
    25 * C.card ≤ 7 * n := hupper
    _ = 7 * init.card := congrArg (fun q : ℕ => 7 * q) (seedPrefix_card_eq init ω s hseed).symm

theorem markedAt_empty_of_zero_front_from_seed (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hst : s ≤ t) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω t i).phase.val ≤ 3)
    (hz : frontCount (virtualLabels init ω t) ℓ = 0) :
    markedAt init C ℓ cutoff s ω t = ∅ := by
  have hM := markedAt_card_le_front_of_seedPrefix init ω C ℓ cutoff s t
    hseed hst hℓ hmask hcap
  have hf := frontCount_succ_le (virtualLabels init ω t) ℓ
  exact Finset.card_eq_zero.mp (by omega)

theorem zero_mark_gap_step (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s t : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hst : s ≤ t) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω t i).phase.val ≤ 3)
    (hz : frontCount (virtualLabels init ω t) ℓ = 0) :
    markedAt init C ℓ cutoff s ω t = ∅ ∧
      immigrationIndicator init C ℓ cutoff t ω = 0 ∧
      propagationIndicator init C ℓ cutoff s t ω = 0 ∧
      markedAt init C ℓ cutoff s ω (t + 1) = ∅ := by
  have hM := markedAt_empty_of_zero_front_from_seed init ω C ℓ cutoff s t
    hseed hst hℓ hmask hcap hz
  have hmaskt : C = clockSet (virtualLabels init ω t) :=
    hmask.trans (virtual_clockSet_eq_seed_of_current_phase_cap init ω s t hseed hst hcap).symm
  have hi := immigrationIndicator_eq_zero_of_front_zero init C ℓ cutoff t ω hmaskt hz
  have hp := propagationIndicator_eq_zero_of_marks_empty init C ℓ cutoff s t ω hM
  refine ⟨hM, hi, hp, ?_⟩
  have hledger := markedAt_card_step_of_seedPrefix init ω C ℓ cutoff s t
    hseed hst hℓ hmask hcap
  simp only [hM, Finset.card_empty, Nat.cast_zero, hi, hp, zero_add] at hledger
  exact Finset.card_eq_zero.mp (by exact_mod_cast hledger)

theorem markedAt_card_at_smallActivation (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3)
    (hr : 1 ≤ PhaseThreeModel.Numeric.smallActivation C.card)
    (hu : smallActivationTime init s C.card ω = (u : WithTop ℕ)) :
    (markedAt init C ℓ cutoff s ω u).card ≤
      PhaseThreeModel.Numeric.smallActivation C.card + 1 := by
  have hsu := (smallActivationTime_finite_state init s C.card u ω hu).1
  exact (markedAt_card_le_active_of_seedPrefix init ω C ℓ cutoff s u
    hseed hsu hℓ hmask hcap).trans
      (smallActivationTime_overshoot_from_seed init ω s C.card u hseed hr hu).2

theorem markedAt_card_at_smallActivation_le_order (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω u i).phase.val ≤ 3)
    (hu : smallActivationTime init s C.card ω = (u : WithTop ℕ)) :
    (markedAt init C ℓ cutoff s ω u).card ≤ PhaseThreeModel.Numeric.markOrder C.card := by
  have hcount : clockCount (labelsAt init ω s) = C.card := by
    change (clockSet (labelsAt init ω s)).card = C.card
    rw [← hmask]
  obtain ⟨hm, hlo, hCn⟩ := seed_clock_calibration_inputs init hn ω s C.card hseed hcount
  have hd := activation_calibration_data hm hlo hCn
  obtain ⟨hCp, hx, _⟩ := PhaseThreeModel.Numeric.logarithmic_inputs hm hlo hCn
  have hcut := (PhaseThreeModel.Numeric.cutoff_calibration hCp hx hCn).1
  exact (markedAt_card_at_smallActivation init ω C ℓ cutoff s u
    hseed hℓ hmask hcap hd.small_pos hu).trans hcut

theorem marks_below_threshold_before_small (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s v : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsv : s ≤ v) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω v i).phase.val ≤ 3)
    (hbefore : (v : WithTop ℕ) ≤ smallActivationTime init s C.card ω) :
    (markedAt init C ℓ cutoff s ω v).card ≤ PhaseThreeModel.Numeric.markOrder C.card ∧
      ((markedAt init C ℓ cutoff s ω v).card : ℝ) < (C.card : ℝ) ^ (1 / 3 : ℝ) := by
  have hcount : clockCount (labelsAt init ω s) = C.card := congrArg Finset.card hmask.symm
  obtain ⟨hm, hlo, hCn⟩ := seed_clock_calibration_inputs init hn ω s C.card hseed hcount
  have hd := activation_calibration_data hm hlo hCn
  have hc := PhaseThreeClockEarlyMarkCalibration.initial_mark_calibration hm hlo hCn
  have hA : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v) ≤
      PhaseThreeModel.Numeric.smallActivation C.card + 1 := by
    by_cases h : PhaseThreeModel.Numeric.smallActivation C.card ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v)
    · have hh := (smallActivationTime_le_iff init s C.card v ω).2 ⟨v, le_rfl, hsv, h⟩
      exact (smallActivationTime_overshoot_from_seed init ω s C.card v hseed hd.small_pos
        (le_antisymm hh hbefore)).2
    · omega
  have hb := (markedAt_card_le_active_of_seedPrefix init ω C ℓ cutoff s v
    hseed hsv hℓ hmask hcap).trans (hA.trans hc.2.1)
  have hbR : ((markedAt init C ℓ cutoff s ω v).card : ℝ) ≤
      (PhaseThreeModel.Numeric.markOrder C.card : ℝ) := by exact_mod_cast hb
  exact ⟨hb, hbR.trans_lt hc.2.2.1⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedClockRates

end
