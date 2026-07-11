/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Seam/work sum-budget slack

This file records the two budget-slack facts needed by the migrated 21-phase
sum-budget assembly.

* Seam epidemics can be run at Janson factor `λ = 6`, giving failure
  `≤ 1/(2 n²)` while keeping the interaction horizon `≤ 12 n (log n + 1)`.
* The current concrete work family does not have a uniform `1/(2 n²)` bound:
  slots 2/4/9 are definitionally calibrated at `1/n²`.  The honest replacement
  is a non-uniform work budget: slots 2/4/9 get `1/n²`, the other eight slots
  get `5/(16 n²)`, summing exactly to `11/(2 n²)`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamJansonDrift
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AssemblyConcrete

namespace ExactMajority
namespace SeamBudgetSlack

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

attribute [local instance] Classical.propDecidable

variable {L K : ℕ}

namespace RoleSplitConcentration

/-- Janson exponential slack at deviation factor `≥ 3`: from
`pMin * meanTime ≥ log n`, the tail is `≤ 1/(2 n²)` for `n ≥ 2`. -/
theorem jansonExp_le_half_inv_sq
    {n : ℕ} (hn : 2 ≤ n) {pm devf : ℝ}
    (hpm_nonneg : 0 ≤ pm)
    (hpm : Real.log (n : ℝ) ≤ pm)
    (hdev : 3 ≤ devf) :
    Real.exp (-pm * devf) ≤ 1 / (2 * (n : ℝ) ^ 2) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have h3 : 3 * Real.log (n : ℝ) ≤ pm * devf := by
    have hb : 3 * Real.log (n : ℝ) ≤ pm * 3 := by
      nlinarith [hpm, hlogn_nonneg]
    have hc : pm * 3 ≤ pm * devf := by
      nlinarith [hpm_nonneg, hdev]
    linarith
  have h_exp_le :
      Real.exp (-pm * devf) ≤ Real.exp (-(3 * Real.log (n : ℝ))) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have h_exp_eq :
      Real.exp (-(3 * Real.log (n : ℝ))) = ((n : ℝ) ^ 3)⁻¹ := by
    have hlog : Real.log (((n : ℝ) ^ 3)⁻¹) = -(3 * Real.log (n : ℝ)) := by
      rw [Real.log_inv, Real.log_pow]
      ring
    rw [← hlog, Real.exp_log]
    positivity
  have h_inv : ((n : ℝ) ^ 3)⁻¹ ≤ 1 / (2 * (n : ℝ) ^ 2) := by
    rw [show ((n : ℝ) ^ 3)⁻¹ = 1 / ((n : ℝ) ^ 3) by ring]
    apply one_div_le_one_div_of_le
    · positivity
    · have hn2_nonneg : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      nlinarith [hnR, hn2_nonneg]
  calc
    Real.exp (-pm * devf)
        ≤ Real.exp (-(3 * Real.log (n : ℝ))) := h_exp_le
    _ = ((n : ℝ) ^ 3)⁻¹ := h_exp_eq
    _ ≤ 1 / (2 * (n : ℝ) ^ 2) := h_inv

/-- `6 - 1 - log 6 ≥ 3`, since `log 6 ≤ 2`. -/
theorem six_sub_one_sub_log_six_ge_three :
    (3 : ℝ) ≤ 6 - 1 - Real.log 6 := by
  have hlog6 : Real.log 6 ≤ 2 := by
    have h6 : (6 : ℝ) ≤ Real.exp 2 := by
      have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      nlinarith [he1, hexp2, hpos]
    calc
      Real.log 6 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h6
      _ = 2 := Real.log_exp 2
  linarith

end RoleSplitConcentration

open SeamEpidemics
open RoleSplitConcentration

/-- The seam Janson horizon at deviation factor `λ = 6`. -/
noncomputable def seamJansonT2 (p n : ℕ) (hn : 2 ≤ n) : ℕ :=
  ⌈(6 : ℝ) *
    (SeamJansonDrift.seamMilestonePhase (L := L) (K := K) p n hn).meanTime⌉₊

/-- The `λ = 6` seam horizon is still `O(n log n)`, with literal coefficient `12`. -/
theorem seamJansonT2_le_logn (p n : ℕ) (hn : 2 ≤ n) :
    (seamJansonT2 (L := L) (K := K) p n hn : ℝ) ≤
      12 * (n : ℝ) * (Real.log n + 1) := by
  unfold seamJansonT2
  have hmt₀ := Phase2Time.meanTime_le n hn
  have hmt :
      (SeamJansonDrift.seamMilestonePhase (L := L) (K := K) p n hn).meanTime
        ≤ 2 * ((n : ℝ) - 1) * (1 + Real.log n) := by
    simpa [SeamJansonDrift.seam_meanTime_eq_epidemic (L := L) (K := K) p n hn]
      using hmt₀
  have hmtpos :
      0 ≤ (SeamJansonDrift.seamMilestonePhase
        (L := L) (K := K) p n hn).meanTime := by
    rw [SeamJansonDrift.seam_meanTime_eq_epidemic (L := L) (K := K) p n hn]
    have hmt_ge := Phase2Time.meanTime_ge n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hprod : 0 ≤ (n : ℝ) * Real.log n :=
      mul_nonneg (le_of_lt hnpos)
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    linarith
  have hceil :
      (⌈(6 : ℝ) *
          (SeamJansonDrift.seamMilestonePhase
            (L := L) (K := K) p n hn).meanTime⌉₊ : ℝ)
        ≤ 6 *
          (SeamJansonDrift.seamMilestonePhase
            (L := L) (K := K) p n hn).meanTime + 1 := by
    have := Nat.ceil_lt_add_one
      (by
        positivity :
          (0 : ℝ) ≤ 6 *
            (SeamJansonDrift.seamMilestonePhase
              (L := L) (K := K) p n hn).meanTime)
    linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  calc
    (⌈(6 : ℝ) *
        (SeamJansonDrift.seamMilestonePhase
          (L := L) (K := K) p n hn).meanTime⌉₊ : ℝ)
        ≤ 6 *
          (SeamJansonDrift.seamMilestonePhase
            (L := L) (K := K) p n hn).meanTime + 1 := hceil
    _ ≤ 6 * (2 * ((n : ℝ) - 1) * (1 + Real.log n)) + 1 := by
      nlinarith [hmt, hmtpos]
    _ ≤ 12 * (n : ℝ) * (Real.log n + 1) := by
      nlinarith [hnR, hlog0]

/-- Seam Janson exponential at `λ = 6`: tail `≤ 1/(2 n²)`. -/
theorem seam_janson_exp_le_half_inv_sq (p n : ℕ) (hn : 2 ≤ n) :
    Real.exp (-(SeamJansonDrift.seamMilestonePhase
          (L := L) (K := K) p n hn).pMin *
        (SeamJansonDrift.seamMilestonePhase
          (L := L) (K := K) p n hn).meanTime *
        (6 - 1 - Real.log 6)) ≤ 1 / (2 * (n : ℝ) ^ 2) := by
  have hpot₀ := Phase2Time.pMin_mul_meanTime_ge n hn
  have hpot :
      Real.log (n : ℝ) ≤
        (SeamJansonDrift.seamMilestonePhase
          (L := L) (K := K) p n hn).pMin *
        (SeamJansonDrift.seamMilestonePhase
          (L := L) (K := K) p n hn).meanTime := by
    simpa [SeamJansonDrift.seam_pMin_eq_epidemic (L := L) (K := K) p n hn,
      SeamJansonDrift.seam_meanTime_eq_epidemic (L := L) (K := K) p n hn]
      using hpot₀
  have hpot_nonneg :
      0 ≤
        (SeamJansonDrift.seamMilestonePhase
          (L := L) (K := K) p n hn).pMin *
        (SeamJansonDrift.seamMilestonePhase
          (L := L) (K := K) p n hn).meanTime := by
    exact le_trans (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) hpot
  simpa [mul_assoc] using
    (RoleSplitConcentration.jansonExp_le_half_inv_sq (n := n) hn
      hpot_nonneg hpot RoleSplitConcentration.six_sub_one_sub_log_six_ge_three)

/-- Seam drift with the `λ = 6` horizon and half-`1/n²` budget. -/
theorem seam_drift_janson_half (p n tseam : ℕ) (hn : 2 ≤ n)
    (hT : seamJansonT2 (L := L) (K := K) p n hn ≤ tseam)
    (c : Config (AgentState L K))
    (hPre : allPhaseGe (L := L) (K := K) p n c ∧
      advTriggered (L := L) (K := K) (p + 1) c) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c
        {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
      ≤ ((Real.toNNReal (1 / (2 * (n : ℝ) ^ 2)) : ℝ≥0) : ℝ≥0∞) := by
  set mp := SeamJansonDrift.seamMilestonePhase (L := L) (K := K) p n hn with hmp
  have hInv : mp.Inv c := by
    rw [hmp]
    exact ⟨hPre.1, (advTriggered_iff_geCount (L := L) (K := K) p c).mp hPre.2⟩
  have ht0 : (6 : ℝ) * mp.meanTime ≤
      (seamJansonT2 (L := L) (K := K) p n hn : ℝ) := by
    rw [hmp]
    unfold seamJansonT2
    exact Nat.le_ceil _
  have ht : (6 : ℝ) * mp.meanTime ≤ (tseam : ℝ) :=
    le_trans ht0 (by exact_mod_cast hT)
  have hj := mp.milestone_hitting_time_bound_on_partial c hInv 6
    (by norm_num) tseam ht
  have hexp := seam_janson_exp_le_half_inv_sq (L := L) (K := K) p n hn
  rw [← hmp] at hexp
  have htail :
      ((NonuniformMajority L K).transitionKernel ^ tseam) c {c' | ¬ mp.Post c'} ≤
        ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) :=
    le_trans hj (ENNReal.ofReal_le_ofReal hexp)
  have hcard_zero :
      ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' : Config (AgentState L K) | c'.card ≠ n} = 0 :=
    Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
      (NonuniformMajority L K) (fun c' : Config (AgentState L K) => c'.card = n)
      (fun c₀ c₁ hcard hsupp => by
        change c₁.card = n
        rw [Protocol.stepDistOrSelf_support_card_eq
          (NonuniformMajority L K) c₀ c₁ hsupp]
        exact hcard)
      c hPre.1.1 tseam
  have hsub :
      {c' : Config (AgentState L K) |
          ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
        ⊆ {c' | ¬ mp.Post c'} ∪ {c' | c'.card ≠ n} := by
    intro c' hbad
    by_cases hPost : mp.Post c'
    · right
      intro hcard
      apply hbad
      have hfin : geFinished (L := L) (K := K) p n c' := by
        rw [hmp] at hPost
        exact SeamJansonDrift.seamMilestonePhase_post_imp_geFinished
          (L := L) (K := K) p n hn c' hPost
      exact (allPhaseGe_succ_iff_geFinished
        (L := L) (K := K) p n c' hcard).mpr hfin
    · left
      exact hPost
  calc
    ((NonuniformMajority L K).transitionKernel ^ tseam) c
        {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
      ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c
          ({c' | ¬ mp.Post c'} ∪ {c' | c'.card ≠ n}) := measure_mono hsub
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c {c' | ¬ mp.Post c'} +
          ((NonuniformMajority L K).transitionKernel ^ tseam) c {c' | c'.card ≠ n} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := by
      rw [hcard_zero, add_zero]
      exact htail
    _ = ((Real.toNNReal (1 / (2 * (n : ℝ) ^ 2)) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.ofReal]

/-- Full seam `hDrift` feeder with the half-`1/n²` epidemic budget. -/
theorem seamDischarge_hDrift_janson_half (n : ℕ) (hn : 2 ≤ n)
    (seamP seamT : Fin 10 → ℕ)
    (hT : ∀ k, seamJansonT2 (L := L) (K := K) (seamP k) n hn ≤ seamT k) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ ((Real.toNNReal (1 / (2 * (n : ℝ) ^ 2)) : ℝ≥0) : ℝ≥0∞) :=
  fun k c hPre =>
    seam_drift_janson_half (L := L) (K := K) (seamP k) n (seamT k) hn
      (hT k) c hPre

theorem seamJansonT2_all_le_logn (n : ℕ) (hn : 2 ≤ n) (seamP : Fin 10 → ℕ) :
    ∀ k : Fin 10,
      (seamJansonT2 (L := L) (K := K) (seamP k) n hn : ℝ) ≤
        12 * (n : ℝ) * (Real.log n + 1) :=
  fun k => seamJansonT2_le_logn (L := L) (K := K) (seamP k) n hn

/-! ## Work-side non-uniform sum budget -/

noncomputable def invSqBudget (n : ℕ) : ℝ≥0 :=
  Real.toNNReal (1 / (n : ℝ) ^ 2)

noncomputable def freeWorkBudget (n : ℕ) : ℝ≥0 :=
  (5 / 16 : ℝ≥0) * invSqBudget n

/-- Non-uniform per-work-slot budget.  Slots 2/4/9 are the existing epidemic
slots at `1/n²`; the other eight slots are constrained to `5/(16 n²)`. -/
noncomputable def workSlotBudget (n : ℕ) : Fin 11 → ℝ≥0
  | ⟨0, _⟩ => freeWorkBudget n
  | ⟨1, _⟩ => freeWorkBudget n
  | ⟨2, _⟩ => invSqBudget n
  | ⟨3, _⟩ => freeWorkBudget n
  | ⟨4, _⟩ => invSqBudget n
  | ⟨5, _⟩ => freeWorkBudget n
  | ⟨6, _⟩ => freeWorkBudget n
  | ⟨7, _⟩ => freeWorkBudget n
  | ⟨8, _⟩ => freeWorkBudget n
  | ⟨9, _⟩ => invSqBudget n
  | ⟨10, _⟩ => freeWorkBudget n

noncomputable def workBudgetTotal (n : ℕ) : ℝ≥0 :=
  (11 / 2 : ℝ≥0) * invSqBudget n

/-- Field-level constraints for the free work-slot calibration scalars.  These
are the exact ε fields consumed by `concreteWork`; no constraint is imposed
on fixed slots 2/4/9 because their actual ε is definitionally `1/n²`. -/
structure WorkSlackCalib
    (n : ℕ) (cal : WorkConstructed.SlotCalib (L := L) (K := K) n) : Prop where
  slot0 :
    ((cal.s0stage1.ε + cal.s0stage15.ε + cal.s0stage2.ε : ℝ≥0) : ℝ≥0∞)
      ≤ (freeWorkBudget n : ℝ≥0∞)
  slot1 :
    ((cal.s1εd + cal.s1ηc + cal.s1ηs : ℝ≥0) : ℝ≥0∞)
      ≤ (freeWorkBudget n : ℝ≥0∞)
  slot3 : (cal.s3post.snap.ε : ℝ≥0∞) ≤ (freeWorkBudget n : ℝ≥0∞)
  slot5 :
    ((cal.s5εd + cal.s5ηc + cal.s5ηconf : ℝ≥0) : ℝ≥0∞)
      ≤ (freeWorkBudget n : ℝ≥0∞)
  slot6 :
    ((cal.s6εd + cal.s6ηc + cal.s6ηs : ℝ≥0) : ℝ≥0∞)
      ≤ (freeWorkBudget n : ℝ≥0∞)
  slot7 :
    ((cal.s7εd + cal.s7ηc + cal.s7ηs : ℝ≥0) : ℝ≥0∞)
      ≤ (freeWorkBudget n : ℝ≥0∞)
  slot8 :
    ((cal.s8εd + cal.s8ηc + cal.s8ηs : ℝ≥0) : ℝ≥0∞)
      ≤ (freeWorkBudget n : ℝ≥0∞)
  slot10 :
    (((1 / 2 : ℝ≥0) ^ cal.s10k : ℝ≥0) : ℝ≥0∞)
      ≤ (freeWorkBudget n : ℝ≥0∞)

/-- Actual ε of each concrete work slot is bounded by its non-uniform slot
budget, under the explicit free-slot calibration constraints. -/
theorem concreteWork_eps_le_budget {n : ℕ} (hn : 2 ≤ n)
    (cal : WorkConstructed.SlotCalib (L := L) (K := K) n)
    (hcal : WorkSlackCalib (L := L) (K := K) n cal) :
    ∀ i : Fin 11,
      ((AssemblyConcrete.concreteWork (L := L) (K := K) hn cal i).ε :
          ℝ≥0∞)
        ≤ (workSlotBudget n i : ℝ≥0∞) := by
  intro i
  fin_cases i
  · simpa [AssemblyConcrete.concreteWork, WorkConstructed.work0,
      Phase0RoleSplitDischarge.roleSplitWork0, EndpointWiring.roleSplitW_of_two_stage,
      workSlotBudget] using hcal.slot0
  · simpa [AssemblyConcrete.concreteWork, WorkConstructed.work1, workSlotBudget]
      using hcal.slot1
  · unfold AssemblyConcrete.concreteWork WorkConstructed.work2 SlotAtoms.slot2W
      PhaseConvergence.toW Phase2Convergence.phase2Convergence
      WindowConcentration.windowDrift_PhaseConvergence
    simp [workSlotBudget, invSqBudget]
  · simpa [AssemblyConcrete.concreteWork, WorkConstructed.work3, SlotAtoms.slot3W,
      workSlotBudget] using hcal.slot3
  · simp [AssemblyConcrete.concreteWork, WorkConstructed.work4,
      Phase4Convergence.phase4Convergence, workSlotBudget, invSqBudget]
  · simpa [AssemblyConcrete.concreteWork, WorkConstructed.work5, workSlotBudget]
      using hcal.slot5
  · simpa [AssemblyConcrete.concreteWork, WorkConstructed.work6,
      Capstone.slot6Faithful, workSlotBudget] using hcal.slot6
  · simpa [AssemblyConcrete.concreteWork, WorkConstructed.work7, workSlotBudget]
      using hcal.slot7
  · simpa [AssemblyConcrete.concreteWork, WorkConstructed.work8, workSlotBudget]
      using hcal.slot8
  · unfold AssemblyConcrete.concreteWork WorkConstructed.work9 SlotAtoms.slot9W
      Phase9Convergence.phase9ConvergenceW PhaseConvergence.toW
      Phase9Convergence.phase9Convergence
      WindowConcentration.windowDrift_PhaseConvergence
    simp [workSlotBudget, invSqBudget]
  · simpa [AssemblyConcrete.concreteWork, WorkConstructed.work10,
      Phase10Drop.phase10Convergence, workSlotBudget] using hcal.slot10

/-- The non-uniform work slot budgets sum to exactly `11/(2 n²)`. -/
theorem workSlotBudget_sum_eq (n : ℕ) :
    (∑ i : Fin 11, workSlotBudget n i) = workBudgetTotal n := by
  rw [show (Finset.univ : Finset (Fin 11)) =
    {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
     ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩, ⟨7, by omega⟩,
     ⟨8, by omega⟩, ⟨9, by omega⟩, ⟨10, by omega⟩} by
      ext i
      fin_cases i <;> simp]
  simp [workSlotBudget, workBudgetTotal, freeWorkBudget]
  ring_nf

/-- Sum-budget form for the actual 11 concrete work ε values. -/
theorem concreteWork_eps_sum_le_budget {n : ℕ} (hn : 2 ≤ n)
    (cal : WorkConstructed.SlotCalib (L := L) (K := K) n)
    (hcal : WorkSlackCalib (L := L) (K := K) n cal) :
    (∑ i : Fin 11,
        ((AssemblyConcrete.concreteWork (L := L) (K := K) hn cal i).ε :
          ℝ≥0∞))
      ≤ (workBudgetTotal n : ℝ≥0∞) := by
  calc
    (∑ i : Fin 11,
        ((AssemblyConcrete.concreteWork (L := L) (K := K) hn cal i).ε :
          ℝ≥0∞))
        ≤ ∑ i : Fin 11, (workSlotBudget n i : ℝ≥0∞) := by
          exact Finset.sum_le_sum
            (fun i _ => concreteWork_eps_le_budget
              (L := L) (K := K) hn cal hcal i)
    _ = ((∑ i : Fin 11, workSlotBudget n i : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_finsetSum]
    _ = (workBudgetTotal n : ℝ≥0∞) := by
          rw [workSlotBudget_sum_eq]

/-! ## Axiom audit -/

#print axioms RoleSplitConcentration.jansonExp_le_half_inv_sq
#print axioms seam_janson_exp_le_half_inv_sq
#print axioms seam_drift_janson_half
#print axioms seamDischarge_hDrift_janson_half
#print axioms concreteWork_eps_le_budget
#print axioms concreteWork_eps_sum_le_budget

end SeamBudgetSlack
end ExactMajority
