/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tight epidemic work slots

Slots 2, 4, and 9 in `WorkConstructed` used the liveness-style calibrated
geometric-potential horizon `epiHorizon`, which is quadratic in the population.
This file gives replacement weak convergence instances at the canonical rumor
epidemic scale.

The new horizon is `ceil(6 * meanTime)` for the canonical `Phase2Time` epidemic.
It is bounded by `12*n*(log n+1)` interactions, and the Janson tail is at most
`1/(2*n^2)`.  The shared `EpidemicConvergence.epidemicBudget_calibrated` is not
changed or used.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceJansonDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase4Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase9Convergence

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

attribute [local instance] Classical.propDecidable

namespace TightEpidemicWork

variable {L K : ℕ}

/-! ## Shared tight horizon and tail arithmetic. -/

/-- The tight epidemic horizon: Janson factor `λ = 6` on the canonical rumor epidemic. -/
noncomputable def epiHorizonTight (n : ℕ) (hn : 2 ≤ n) : ℕ :=
  ⌈(6 : ℝ) * (Phase2Time.epidemicMilestonePhase n hn).meanTime⌉₊

/-- The per-slot tight epidemic budget, with the half-`1/n²` slack needed by the assembly. -/
noncomputable def tightBudget (n : ℕ) : ℝ≥0 :=
  Real.toNNReal (1 / (2 * (n : ℝ) ^ 2))

/-- Janson exponential slack at deviation factor at least `3`. -/
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

/-- The tight horizon is still `O(n log n)`, with literal coefficient `12`. -/
theorem epiHorizonTight_le_logn (n : ℕ) (hn : 2 ≤ n) :
    (epiHorizonTight n hn : ℝ) ≤ 12 * (n : ℝ) * (Real.log n + 1) := by
  unfold epiHorizonTight
  have hmt := Phase2Time.meanTime_le n hn
  have hmtpos : 0 ≤ (Phase2Time.epidemicMilestonePhase n hn).meanTime := by
    have hmt_ge := Phase2Time.meanTime_ge n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hprod : 0 ≤ (n : ℝ) * Real.log n :=
      mul_nonneg (le_of_lt hnpos)
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    linarith
  have hceil :
      (⌈(6 : ℝ) * (Phase2Time.epidemicMilestonePhase n hn).meanTime⌉₊ : ℝ)
        ≤ 6 * (Phase2Time.epidemicMilestonePhase n hn).meanTime + 1 := by
    have := Nat.ceil_lt_add_one
      (by positivity : (0 : ℝ) ≤ 6 * (Phase2Time.epidemicMilestonePhase n hn).meanTime)
    linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  calc
    (⌈(6 : ℝ) * (Phase2Time.epidemicMilestonePhase n hn).meanTime⌉₊ : ℝ)
        ≤ 6 * (Phase2Time.epidemicMilestonePhase n hn).meanTime + 1 := hceil
    _ ≤ 6 * (2 * ((n : ℝ) - 1) * (1 + Real.log n)) + 1 := by
      nlinarith [hmt, hmtpos]
    _ ≤ 12 * (n : ℝ) * (Real.log n + 1) := by
      nlinarith [hnR, hlog0]

/-- A direct phase-budget fit from the tight scale statement. -/
theorem epiHorizonTight_le_ht_of_logp1 (n L : ℕ) (hn : 2 ≤ n)
    (hlogp1 : Real.log (n : ℝ) + 1 ≤ (L + 1 : ℝ)) :
    epiHorizonTight n hn ≤ 17 * n * (L + 1) := by
  have hreal₀ := epiHorizonTight_le_logn n hn
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hreal :
      (epiHorizonTight n hn : ℝ) ≤ ((17 * n * (L + 1) : ℕ) : ℝ) := by
    calc
      (epiHorizonTight n hn : ℝ)
          ≤ 12 * (n : ℝ) * (Real.log n + 1) := hreal₀
      _ ≤ 12 * (n : ℝ) * (L + 1 : ℝ) := by
        nlinarith [hnR, hlogp1]
      _ ≤ 17 * (n : ℝ) * (L + 1 : ℝ) := by
        have hL : (0 : ℝ) ≤ (L + 1 : ℝ) := by positivity
        nlinarith [hnR, hL]
      _ = ((17 * n * (L + 1) : ℕ) : ℝ) := by norm_num
  exact_mod_cast hreal

/-- The `λ = 6` Janson tail for any milestone phase with the canonical epidemic rates. -/
theorem epidemic_janson_exp_le_half_inv_sq
    {P : Protocol (AgentState L K)}
    (mp : RoleSplitConcentration.MilestonePhaseOn (L := L) (K := K) P)
    (n : ℕ) (hn : 2 ≤ n)
    (hpMin : mp.pMin = (Phase2Time.epidemicMilestonePhase n hn).pMin)
    (hMean : mp.meanTime = (Phase2Time.epidemicMilestonePhase n hn).meanTime) :
    Real.exp (-mp.pMin * mp.meanTime * (6 - 1 - Real.log 6)) ≤
      1 / (2 * (n : ℝ) ^ 2) := by
  have hpot₀ := Phase2Time.pMin_mul_meanTime_ge n hn
  have hpot : Real.log (n : ℝ) ≤ mp.pMin * mp.meanTime := by
    simpa [hpMin, hMean] using hpot₀
  have hpot_nonneg : 0 ≤ mp.pMin * mp.meanTime :=
    le_trans (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) hpot
  simpa [mul_assoc] using
    (jansonExp_le_half_inv_sq (n := n) hn hpot_nonneg hpot
      six_sub_one_sub_log_six_ge_three)

/-! ## Slot 2. -/

namespace Phase2

open Phase2Convergence

/-- Slot-2 milestone guarded by the closed Phase-2 epidemic window. -/
def milestone (U v : Fin 8) (n i : ℕ) (c : Config (AgentState L K)) : Prop :=
  SeededConsensusWin (L := L) (K := K) U v n c ∧ i + 2 ≤ informedU (L := L) (K := K) U c

noncomputable def milestonePhase (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) :
    RoleSplitConcentration.MilestonePhaseOn (L := L) (K := K) (NonuniformMajority L K) where
  k := n - 1
  milestone i c := milestone (L := L) (K := K) U v n i.val c
  p i := Phase2Time.epP n i.val
  hp_pos i := Phase2Time.epP_pos hn (by have := i.isLt; omega)
  hp_le_one i := Phase2Time.epP_le_one hn (by have := i.isLt; omega)
  milestone_monotone := by
    intro i c c' h hsupp
    exact ⟨
      SeededConsensusWin_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' h.1 hsupp,
      informedU_ge_monotone U v n (i.val + 2) hUsign hvsign hvU hUv hvv hUU
        c c' h.1.1 h.2 hsupp⟩
  Inv := SeededConsensusWin (L := L) (K := K) U v n
  inv_closed := by
    intro c hInv
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ¬ SeededConsensusWin (L := L) (K := K) U v n c'} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro c' hsupp hbad
    exact hbad (SeededConsensusWin_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hInv hsupp)
  progress_on := by
    intro i c hInv hprev hcur
    have hcount_eq : informedU (L := L) (K := K) U c = i.val + 1 := by
      have hlt_count : informedU (L := L) (K := K) U c < i.val + 2 := by
        exact Nat.lt_of_not_ge (fun hge => hcur ⟨hInv, hge⟩)
      have hge_count : i.val + 1 ≤ informedU (L := L) (K := K) U c := by
        by_cases hi0 : i.val = 0
        · rw [hi0]
          exact hInv.2
        · have hprev' := hprev ⟨i.val - 1, by omega⟩ (by
            exact Fin.mk_lt_mk.mpr (by omega))
          have hprev_cov : (i.val - 1) + 2 ≤ informedU (L := L) (K := K) U c := hprev'.2
          omega
      omega
    have hbound :=
      opinion_advance_prob U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne c hInv.1
    have heq :
        ((((informedU (L := L) (K := K) U c *
            (n - informedU (L := L) (K := K) U c) : ℕ) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1)))) = Phase2Time.epP n i.val := by
      rw [hcount_eq]
      unfold Phase2Time.epP
      have hi1_le : i.val + 1 ≤ n := by
        have := i.isLt
        omega
      rw [Nat.cast_mul]
      rw [Nat.cast_sub hi1_le]
      rw [Nat.cast_add, Nat.cast_one]
    rw [heq] at hbound
    set A := {c' : Config (AgentState L K) | i.val + 2 ≤ informedU (L := L) (K := K) U c'}
    set M := {c' : Config (AgentState L K) | milestone (L := L) (K := K) U v n i.val c'}
    have hA_le_M :
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A ≤
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
      have hsub : A ⊆ M ∪ {c' : Config (AgentState L K) | ¬ SeededConsensusWin (L := L) (K := K) U v n c'} := by
        intro x hx
        by_cases hxInv : SeededConsensusWin (L := L) (K := K) U v n x
        · left
          exact ⟨hxInv, hx⟩
        · right
          exact hxInv
      have hclosed :
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) | ¬ SeededConsensusWin (L := L) (K := K) U v n c'} = 0 := by
        rw [PMF.toMeasure_apply_eq_zero_iff
          (p := (NonuniformMajority L K).stepDistOrSelf c)
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro c' hsupp hbad
        exact hbad (SeededConsensusWin_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hInv hsupp)
      calc
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A
            ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                (M ∪ {c' : Config (AgentState L K) | ¬ SeededConsensusWin (L := L) (K := K) U v n c'}) :=
              measure_mono hsub
        _ ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M +
              ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                {c' : Config (AgentState L K) | ¬ SeededConsensusWin (L := L) (K := K) U v n c'} :=
              measure_union_le M _
        _ = ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
              rw [hclosed, add_zero]
    have hboundA : ENNReal.ofReal (Phase2Time.epP n i.val) ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
      simpa [A, hcount_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
    exact le_trans hboundA hA_le_M

theorem pMin_eq_epidemic (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) :
    (milestonePhase (L := L) (K := K) U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne).pMin =
      (Phase2Time.epidemicMilestonePhase n hn).pMin := rfl

theorem meanTime_eq_epidemic (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) :
    (milestonePhase (L := L) (K := K) U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne).meanTime =
      (Phase2Time.epidemicMilestonePhase n hn).meanTime := rfl

theorem post_imp_finished (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) (c : Config (AgentState L K))
    (hPost :
      (milestonePhase (L := L) (K := K) U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne).Post c) :
    SeededConsensusWin (L := L) (K := K) U v n c ∧ oFinished (L := L) (K := K) U n c := by
  let i : Fin ((milestonePhase (L := L) (K := K) U v n hn
      hUsign hvsign hvU hUv hvv hUU hUv_ne).k) := ⟨n - 2, by
        change n - 2 < n - 1
        omega⟩
  have hi := hPost i
  change milestone (L := L) (K := K) U v n i.val c at hi
  have hival : i.val = n - 2 := rfl
  rw [hival] at hi
  refine ⟨hi.1, ?_⟩
  unfold oFinished
  have hcov := hi.2
  have hn_eq : n - 2 + 2 = n := by omega
  rw [hn_eq] at hcov
  exact hcov

noncomputable def convergenceW (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => SeededConsensusWin (L := L) (K := K) U v n c
  Post := fun c => SeededConsensusWin (L := L) (K := K) U v n c ∧ oFinished (L := L) (K := K) U n c
  t := epiHorizonTight n hn
  ε := tightBudget n
  convergence := by
    intro c hPre
    set mp := milestonePhase (L := L) (K := K) U v n hn
      hUsign hvsign hvU hUv hvv hUU hUv_ne with hmp
    have hInv : mp.Inv c := by
      rw [hmp]
      exact hPre
    have ht : (6 : ℝ) * mp.meanTime ≤ (epiHorizonTight n hn : ℝ) := by
      rw [hmp]
      unfold epiHorizonTight
      exact Nat.le_ceil _
    have hj := mp.milestone_hitting_time_bound_on_partial c hInv 6
      (by norm_num) (epiHorizonTight n hn) ht
    have hexp :=
      epidemic_janson_exp_le_half_inv_sq (L := L) (K := K) mp n hn
        (by rw [hmp]; exact pMin_eq_epidemic U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne)
        (by rw [hmp]; exact meanTime_eq_epidemic U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne)
    have htail :
        ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
            {c' | ¬ mp.Post c'} ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) :=
      le_trans hj (ENNReal.ofReal_le_ofReal hexp)
    have hsub :
        {c' : Config (AgentState L K) |
            ¬ (SeededConsensusWin (L := L) (K := K) U v n c' ∧
              oFinished (L := L) (K := K) U n c')}
          ⊆ {c' | ¬ mp.Post c'} := by
      intro c' hbad hPost
      exact hbad (by
        rw [hmp] at hPost
        exact post_imp_finished U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne c' hPost)
    calc
      ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
          {c' | ¬ (SeededConsensusWin (L := L) (K := K) U v n c' ∧
            oFinished (L := L) (K := K) U n c')}
          ≤ ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
              {c' | ¬ mp.Post c'} := measure_mono hsub
      _ ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := htail
      _ = ((tightBudget n : ℝ≥0) : ℝ≥0∞) := by
        rw [tightBudget, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal]
        positivity

end Phase2

/-! ## Slot 4. -/

namespace Phase4

open Phase4Convergence

/-- Slot-4 non-tie milestone guarded by the closed advanced-seed window. -/
def milestone (n i : ℕ) (c : Config (AgentState L K)) : Prop :=
  SeededNonTieWin (L := L) (K := K) n c ∧ i + 2 ≤ advancedU (L := L) (K := K) c

noncomputable def milestonePhase (n : ℕ) (hn : 2 ≤ n) :
    RoleSplitConcentration.MilestonePhaseOn (L := L) (K := K) (NonuniformMajority L K) where
  k := n - 1
  milestone i c := milestone (L := L) (K := K) n i.val c
  p i := Phase2Time.epP n i.val
  hp_pos i := Phase2Time.epP_pos hn (by have := i.isLt; omega)
  hp_le_one i := Phase2Time.epP_le_one hn (by have := i.isLt; omega)
  milestone_monotone := by
    intro i c c' h hsupp
    exact ⟨
      SeededNonTieWin_absorbing n c c' h.1 hsupp,
      advancedU_ge_monotone (L := L) (K := K) (i.val + 2) c c' h.2 hsupp⟩
  Inv := SeededNonTieWin (L := L) (K := K) n
  inv_closed := by
    intro c hInv
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ¬ SeededNonTieWin (L := L) (K := K) n c'} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro c' hsupp hbad
    exact hbad (SeededNonTieWin_absorbing n c c' hInv hsupp)
  progress_on := by
    intro i c hInv hprev hcur
    have hcount_eq : advancedU (L := L) (K := K) c = i.val + 1 := by
      have hlt_count : advancedU (L := L) (K := K) c < i.val + 2 := by
        exact Nat.lt_of_not_ge (fun hge => hcur ⟨hInv, hge⟩)
      have hge_count : i.val + 1 ≤ advancedU (L := L) (K := K) c := by
        by_cases hi0 : i.val = 0
        · rw [hi0]
          exact hInv.2
        · have hprev' := hprev ⟨i.val - 1, by omega⟩ (by
            exact Fin.mk_lt_mk.mpr (by omega))
          have hprev_cov : (i.val - 1) + 2 ≤ advancedU (L := L) (K := K) c := hprev'.2
          omega
      omega
    have hbound := advanced_advance_prob (L := L) (K := K) n hn c hInv.1
    have heq :
        ((((advancedU (L := L) (K := K) c *
            (n - advancedU (L := L) (K := K) c) : ℕ) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1)))) = Phase2Time.epP n i.val := by
      rw [hcount_eq]
      unfold Phase2Time.epP
      have hi1_le : i.val + 1 ≤ n := by
        have := i.isLt
        omega
      rw [Nat.cast_mul]
      rw [Nat.cast_sub hi1_le]
      rw [Nat.cast_add, Nat.cast_one]
    rw [heq] at hbound
    set A := {c' : Config (AgentState L K) | i.val + 2 ≤ advancedU (L := L) (K := K) c'}
    set M := {c' : Config (AgentState L K) | milestone (L := L) (K := K) n i.val c'}
    have hA_le_M :
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A ≤
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
      have hsub : A ⊆ M ∪ {c' : Config (AgentState L K) | ¬ SeededNonTieWin (L := L) (K := K) n c'} := by
        intro x hx
        by_cases hxInv : SeededNonTieWin (L := L) (K := K) n x
        · left
          exact ⟨hxInv, hx⟩
        · right
          exact hxInv
      have hclosed :
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) | ¬ SeededNonTieWin (L := L) (K := K) n c'} = 0 := by
        rw [PMF.toMeasure_apply_eq_zero_iff
          (p := (NonuniformMajority L K).stepDistOrSelf c)
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro c' hsupp hbad
        exact hbad (SeededNonTieWin_absorbing n c c' hInv hsupp)
      calc
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A
            ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                (M ∪ {c' : Config (AgentState L K) | ¬ SeededNonTieWin (L := L) (K := K) n c'}) :=
              measure_mono hsub
        _ ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M +
              ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                {c' : Config (AgentState L K) | ¬ SeededNonTieWin (L := L) (K := K) n c'} :=
              measure_union_le M _
        _ = ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
              rw [hclosed, add_zero]
    have hboundA : ENNReal.ofReal (Phase2Time.epP n i.val) ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
      simpa [A, hcount_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
    exact le_trans hboundA hA_le_M

theorem pMin_eq_epidemic (n : ℕ) (hn : 2 ≤ n) :
    (milestonePhase (L := L) (K := K) n hn).pMin =
      (Phase2Time.epidemicMilestonePhase n hn).pMin := rfl

theorem meanTime_eq_epidemic (n : ℕ) (hn : 2 ≤ n) :
    (milestonePhase (L := L) (K := K) n hn).meanTime =
      (Phase2Time.epidemicMilestonePhase n hn).meanTime := rfl

theorem post_imp_finished (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hPost : (milestonePhase (L := L) (K := K) n hn).Post c) :
    SeededNonTieWin (L := L) (K := K) n c ∧ advFinished (L := L) (K := K) n c := by
  let i : Fin ((milestonePhase (L := L) (K := K) n hn).k) := ⟨n - 2, by
        change n - 2 < n - 1
        omega⟩
  have hi := hPost i
  change milestone (L := L) (K := K) n i.val c at hi
  have hival : i.val = n - 2 := rfl
  rw [hival] at hi
  refine ⟨hi.1, ?_⟩
  unfold advFinished
  have hcov := hi.2
  have hn_eq : n - 2 + 2 = n := by omega
  rw [hn_eq] at hcov
  exact hcov

noncomputable def nonTieConvergenceW (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => SeededNonTieWin (L := L) (K := K) n c
  Post := fun c => SeededNonTieWin (L := L) (K := K) n c ∧ advFinished (L := L) (K := K) n c
  t := epiHorizonTight n hn
  ε := tightBudget n
  convergence := by
    intro c hPre
    set mp := milestonePhase (L := L) (K := K) n hn with hmp
    have hInv : mp.Inv c := by
      rw [hmp]
      exact hPre
    have ht : (6 : ℝ) * mp.meanTime ≤ (epiHorizonTight n hn : ℝ) := by
      rw [hmp]
      unfold epiHorizonTight
      exact Nat.le_ceil _
    have hj := mp.milestone_hitting_time_bound_on_partial c hInv 6
      (by norm_num) (epiHorizonTight n hn) ht
    have hexp :=
      epidemic_janson_exp_le_half_inv_sq (L := L) (K := K) mp n hn
        (by rw [hmp]; exact pMin_eq_epidemic n hn)
        (by rw [hmp]; exact meanTime_eq_epidemic n hn)
    have htail :
        ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
            {c' | ¬ mp.Post c'} ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) :=
      le_trans hj (ENNReal.ofReal_le_ofReal hexp)
    have hsub :
        {c' : Config (AgentState L K) |
            ¬ (SeededNonTieWin (L := L) (K := K) n c' ∧ advFinished (L := L) (K := K) n c')}
          ⊆ {c' | ¬ mp.Post c'} := by
      intro c' hbad hPost
      exact hbad (by
        rw [hmp] at hPost
        exact post_imp_finished n hn c' hPost)
    calc
      ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
          {c' | ¬ (SeededNonTieWin (L := L) (K := K) n c' ∧
            advFinished (L := L) (K := K) n c')}
          ≤ ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
              {c' | ¬ mp.Post c'} := measure_mono hsub
      _ ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := htail
      _ = ((tightBudget n : ℝ≥0) : ℝ≥0∞) := by
        rw [tightBudget, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal]
        positivity

noncomputable def convergenceW (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => StableTie4 (L := L) (K := K) c ∨ SeededNonTieWin (L := L) (K := K) n c
  Post := fun c => StableTie4 (L := L) (K := K) c ∨ advFinished (L := L) (K := K) n c
  t := epiHorizonTight n hn
  ε := tightBudget n
  convergence := by
    intro c hPre
    set NT := nonTieConvergenceW (L := L) (K := K) n hn with hNT
    have hsubsetTie :
        {c' : Config (AgentState L K) |
            ¬ (StableTie4 (L := L) (K := K) c' ∨
              advFinished (L := L) (K := K) n c')}
          ⊆ {c' | ¬ StableTie4 (L := L) (K := K) c'} := by
      intro c' hc'
      simp only [Set.mem_setOf_eq, not_or] at hc' ⊢
      exact hc'.1
    rcases hPre with hTie | hNTpre
    · calc
        ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
            {c' | ¬ (StableTie4 (L := L) (K := K) c' ∨
              advFinished (L := L) (K := K) n c')}
            ≤ ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
                {c' | ¬ StableTie4 (L := L) (K := K) c'} := measure_mono hsubsetTie
        _ = 0 := StableTie4_pow_tail (L := L) (K := K) (epiHorizonTight n hn) c hTie
        _ ≤ ((tightBudget n : ℝ≥0) : ℝ≥0∞) := zero_le'
    · have hNTconv := NT.convergence c hNTpre
      rw [hNT] at hNTconv
      have hPostsub :
          {c' : Config (AgentState L K) |
              ¬ (StableTie4 (L := L) (K := K) c' ∨
                advFinished (L := L) (K := K) n c')}
            ⊆ {c' | ¬ (SeededNonTieWin (L := L) (K := K) n c' ∧
                advFinished (L := L) (K := K) n c')} := by
        intro c' hc'
        simp only [Set.mem_setOf_eq, not_or, not_and_or] at hc' ⊢
        right
        exact hc'.2
      calc
        ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
            {c' | ¬ (StableTie4 (L := L) (K := K) c' ∨
              advFinished (L := L) (K := K) n c')}
            ≤ ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
                {c' | ¬ (SeededNonTieWin (L := L) (K := K) n c' ∧
                  advFinished (L := L) (K := K) n c')} := measure_mono hPostsub
        _ ≤ ((tightBudget n : ℝ≥0) : ℝ≥0∞) := hNTconv

end Phase4

/-! ## Slot 9. -/

namespace Phase9

open Phase9Convergence

/-- Slot-9 milestone guarded by the closed Phase-9 epidemic window. -/
def milestone (U v : Fin 8) (n i : ℕ) (c : Config (AgentState L K)) : Prop :=
  SeededConsensusWin (L := L) (K := K) U v n c ∧ i + 2 ≤ informedU9 (L := L) (K := K) U c

noncomputable def milestonePhase (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : Phase2Convergence.singleSign U) (hvsign : Phase2Convergence.singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) :
    RoleSplitConcentration.MilestonePhaseOn (L := L) (K := K) (NonuniformMajority L K) where
  k := n - 1
  milestone i c := milestone (L := L) (K := K) U v n i.val c
  p i := Phase2Time.epP n i.val
  hp_pos i := Phase2Time.epP_pos hn (by have := i.isLt; omega)
  hp_le_one i := Phase2Time.epP_le_one hn (by have := i.isLt; omega)
  milestone_monotone := by
    intro i c c' h hsupp
    exact ⟨
      SeededConsensusWin_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' h.1 hsupp,
      informedU9_ge_monotone U v n (i.val + 2) hUsign hvsign hvU hUv hvv hUU
        c c' h.1.1 h.2 hsupp⟩
  Inv := SeededConsensusWin (L := L) (K := K) U v n
  inv_closed := by
    intro c hInv
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ¬ SeededConsensusWin (L := L) (K := K) U v n c'} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro c' hsupp hbad
    exact hbad (SeededConsensusWin_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hInv hsupp)
  progress_on := by
    intro i c hInv hprev hcur
    have hcount_eq : informedU9 (L := L) (K := K) U c = i.val + 1 := by
      have hlt_count : informedU9 (L := L) (K := K) U c < i.val + 2 := by
        exact Nat.lt_of_not_ge (fun hge => hcur ⟨hInv, hge⟩)
      have hge_count : i.val + 1 ≤ informedU9 (L := L) (K := K) U c := by
        by_cases hi0 : i.val = 0
        · rw [hi0]
          exact hInv.2
        · have hprev' := hprev ⟨i.val - 1, by omega⟩ (by
            exact Fin.mk_lt_mk.mpr (by omega))
          have hprev_cov : (i.val - 1) + 2 ≤ informedU9 (L := L) (K := K) U c := hprev'.2
          omega
      omega
    have hbound :=
      opinion_advance_prob9 U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne c hInv.1
    have heq :
        ((((informedU9 (L := L) (K := K) U c *
            (n - informedU9 (L := L) (K := K) U c) : ℕ) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1)))) = Phase2Time.epP n i.val := by
      rw [hcount_eq]
      unfold Phase2Time.epP
      have hi1_le : i.val + 1 ≤ n := by
        have := i.isLt
        omega
      rw [Nat.cast_mul]
      rw [Nat.cast_sub hi1_le]
      rw [Nat.cast_add, Nat.cast_one]
    rw [heq] at hbound
    set A := {c' : Config (AgentState L K) | i.val + 2 ≤ informedU9 (L := L) (K := K) U c'}
    set M := {c' : Config (AgentState L K) | milestone (L := L) (K := K) U v n i.val c'}
    have hA_le_M :
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A ≤
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
      have hsub : A ⊆ M ∪ {c' : Config (AgentState L K) | ¬ SeededConsensusWin (L := L) (K := K) U v n c'} := by
        intro x hx
        by_cases hxInv : SeededConsensusWin (L := L) (K := K) U v n x
        · left
          exact ⟨hxInv, hx⟩
        · right
          exact hxInv
      have hclosed :
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) | ¬ SeededConsensusWin (L := L) (K := K) U v n c'} = 0 := by
        rw [PMF.toMeasure_apply_eq_zero_iff
          (p := (NonuniformMajority L K).stepDistOrSelf c)
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro c' hsupp hbad
        exact hbad (SeededConsensusWin_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hInv hsupp)
      calc
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A
            ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                (M ∪ {c' : Config (AgentState L K) | ¬ SeededConsensusWin (L := L) (K := K) U v n c'}) :=
              measure_mono hsub
        _ ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M +
              ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                {c' : Config (AgentState L K) | ¬ SeededConsensusWin (L := L) (K := K) U v n c'} :=
              measure_union_le M _
        _ = ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
              rw [hclosed, add_zero]
    have hboundA : ENNReal.ofReal (Phase2Time.epP n i.val) ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
      simpa [A, hcount_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
    exact le_trans hboundA hA_le_M

theorem pMin_eq_epidemic (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : Phase2Convergence.singleSign U) (hvsign : Phase2Convergence.singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) :
    (milestonePhase (L := L) (K := K) U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne).pMin =
      (Phase2Time.epidemicMilestonePhase n hn).pMin := rfl

theorem meanTime_eq_epidemic (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : Phase2Convergence.singleSign U) (hvsign : Phase2Convergence.singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) :
    (milestonePhase (L := L) (K := K) U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne).meanTime =
      (Phase2Time.epidemicMilestonePhase n hn).meanTime := rfl

theorem post_imp_finished (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : Phase2Convergence.singleSign U) (hvsign : Phase2Convergence.singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) (c : Config (AgentState L K))
    (hPost :
      (milestonePhase (L := L) (K := K) U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne).Post c) :
    SeededConsensusWin (L := L) (K := K) U v n c ∧ oFinished9 (L := L) (K := K) U n c := by
  let i : Fin ((milestonePhase (L := L) (K := K) U v n hn
      hUsign hvsign hvU hUv hvv hUU hUv_ne).k) := ⟨n - 2, by
        change n - 2 < n - 1
        omega⟩
  have hi := hPost i
  change milestone (L := L) (K := K) U v n i.val c at hi
  have hival : i.val = n - 2 := rfl
  rw [hival] at hi
  refine ⟨hi.1, ?_⟩
  unfold oFinished9
  have hcov := hi.2
  have hn_eq : n - 2 + 2 = n := by omega
  rw [hn_eq] at hcov
  exact hcov

noncomputable def convergenceW (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : Phase2Convergence.singleSign U) (hvsign : Phase2Convergence.singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => SeededConsensusWin (L := L) (K := K) U v n c
  Post := fun c => SeededConsensusWin (L := L) (K := K) U v n c ∧ oFinished9 (L := L) (K := K) U n c
  t := epiHorizonTight n hn
  ε := tightBudget n
  convergence := by
    intro c hPre
    set mp := milestonePhase (L := L) (K := K) U v n hn
      hUsign hvsign hvU hUv hvv hUU hUv_ne with hmp
    have hInv : mp.Inv c := by
      rw [hmp]
      exact hPre
    have ht : (6 : ℝ) * mp.meanTime ≤ (epiHorizonTight n hn : ℝ) := by
      rw [hmp]
      unfold epiHorizonTight
      exact Nat.le_ceil _
    have hj := mp.milestone_hitting_time_bound_on_partial c hInv 6
      (by norm_num) (epiHorizonTight n hn) ht
    have hexp :=
      epidemic_janson_exp_le_half_inv_sq (L := L) (K := K) mp n hn
        (by rw [hmp]; exact pMin_eq_epidemic U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne)
        (by rw [hmp]; exact meanTime_eq_epidemic U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne)
    have htail :
        ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
            {c' | ¬ mp.Post c'} ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) :=
      le_trans hj (ENNReal.ofReal_le_ofReal hexp)
    have hsub :
        {c' : Config (AgentState L K) |
            ¬ (SeededConsensusWin (L := L) (K := K) U v n c' ∧
              oFinished9 (L := L) (K := K) U n c')}
          ⊆ {c' | ¬ mp.Post c'} := by
      intro c' hbad hPost
      exact hbad (by
        rw [hmp] at hPost
        exact post_imp_finished U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne c' hPost)
    calc
      ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
          {c' | ¬ (SeededConsensusWin (L := L) (K := K) U v n c' ∧
            oFinished9 (L := L) (K := K) U n c')}
          ≤ ((NonuniformMajority L K).transitionKernel ^ epiHorizonTight n hn) c
              {c' | ¬ mp.Post c'} := measure_mono hsub
      _ ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := htail
      _ = ((tightBudget n : ℝ≥0) : ℝ≥0∞) := by
        rw [tightBudget, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal]
        positivity

end Phase9

/-! ## Concrete wrappers matching the current work-slot witnesses. -/

/-- The `+1`-only opinion (`Fin 8` value `4`, bit pattern `b₊₁`). -/
def opU : Fin 8 := ⟨4, by decide⟩

/-- The empty opinion (`Fin 8` value `0`). -/
def opV : Fin 8 := ⟨0, by decide⟩

theorem opU_singleSign : Phase2Convergence.singleSign opU := by decide
theorem opV_singleSign : Phase2Convergence.singleSign opV := by decide
theorem op_vU : opinionsUnion opV opU = opU := by decide
theorem op_Uv : opinionsUnion opU opV = opU := by decide
theorem op_vv : opinionsUnion opV opV = opV := by decide
theorem op_UU : opinionsUnion opU opU = opU := by decide
theorem op_Uv_ne : opU ≠ opV := by decide

/-- Tight replacement for work slot 2. -/
noncomputable def work2Tight {n : ℕ} (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase2.convergenceW (L := L) (K := K) opU opV n hn
    opU_singleSign opV_singleSign op_vU op_Uv op_vv op_UU op_Uv_ne

/-- Tight replacement for work slot 4. -/
noncomputable def work4Tight {n : ℕ} (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase4.convergenceW (L := L) (K := K) n hn

/-- Tight replacement for work slot 9, using the real phase-9 clone. -/
noncomputable def work9Tight {n : ℕ} (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase9.convergenceW (L := L) (K := K) opU opV n hn
    opU_singleSign opV_singleSign op_vU op_Uv op_vv op_UU op_Uv_ne

@[simp] theorem work2Tight_t {n : ℕ} (hn : 2 ≤ n) :
    (work2Tight (L := L) (K := K) hn).t = epiHorizonTight n hn := rfl

@[simp] theorem work4Tight_t {n : ℕ} (hn : 2 ≤ n) :
    (work4Tight (L := L) (K := K) hn).t = epiHorizonTight n hn := rfl

@[simp] theorem work9Tight_t {n : ℕ} (hn : 2 ≤ n) :
    (work9Tight (L := L) (K := K) hn).t = epiHorizonTight n hn := rfl

@[simp] theorem work2Tight_epsilon {n : ℕ} (hn : 2 ≤ n) :
    (work2Tight (L := L) (K := K) hn).ε = tightBudget n := rfl

@[simp] theorem work4Tight_epsilon {n : ℕ} (hn : 2 ≤ n) :
    (work4Tight (L := L) (K := K) hn).ε = tightBudget n := rfl

@[simp] theorem work9Tight_epsilon {n : ℕ} (hn : 2 ≤ n) :
    (work9Tight (L := L) (K := K) hn).ε = tightBudget n := rfl

theorem tightBudget_le_inv_sq (n : ℕ) (hn : 2 ≤ n) :
    tightBudget n ≤ Real.toNNReal (1 / (n : ℝ) ^ 2) := by
  unfold tightBudget
  apply Real.toNNReal_mono
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsquare_pos : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hnpos.ne'
  have hden : (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  exact one_div_le_one_div_of_le hsquare_pos hden

theorem work2Tight_epsilon_le_inv_sq {n : ℕ} (hn : 2 ≤ n) :
    (work2Tight (L := L) (K := K) hn).ε ≤ Real.toNNReal (1 / (n : ℝ) ^ 2) :=
  tightBudget_le_inv_sq n hn

theorem work4Tight_epsilon_le_inv_sq {n : ℕ} (hn : 2 ≤ n) :
    (work4Tight (L := L) (K := K) hn).ε ≤ Real.toNNReal (1 / (n : ℝ) ^ 2) :=
  tightBudget_le_inv_sq n hn

theorem work9Tight_epsilon_le_inv_sq {n : ℕ} (hn : 2 ≤ n) :
    (work9Tight (L := L) (K := K) hn).ε ≤ Real.toNNReal (1 / (n : ℝ) ^ 2) :=
  tightBudget_le_inv_sq n hn

theorem work2Tight_t_le_ht {n L' : ℕ} (hn : 2 ≤ n)
    (hlogp1 : Real.log (n : ℝ) + 1 ≤ (L' + 1 : ℝ)) :
    (work2Tight (L := L) (K := K) hn).t ≤ 17 * n * (L' + 1) :=
  epiHorizonTight_le_ht_of_logp1 n L' hn hlogp1

theorem work4Tight_t_le_ht {n L' : ℕ} (hn : 2 ≤ n)
    (hlogp1 : Real.log (n : ℝ) + 1 ≤ (L' + 1 : ℝ)) :
    (work4Tight (L := L) (K := K) hn).t ≤ 17 * n * (L' + 1) :=
  epiHorizonTight_le_ht_of_logp1 n L' hn hlogp1

theorem work9Tight_t_le_ht {n L' : ℕ} (hn : 2 ≤ n)
    (hlogp1 : Real.log (n : ℝ) + 1 ≤ (L' + 1 : ℝ)) :
    (work9Tight (L := L) (K := K) hn).t ≤ 17 * n * (L' + 1) :=
  epiHorizonTight_le_ht_of_logp1 n L' hn hlogp1

#print axioms epiHorizonTight_le_logn
#print axioms epidemic_janson_exp_le_half_inv_sq
#print axioms Phase2.convergenceW
#print axioms Phase4.convergenceW
#print axioms Phase9.convergenceW
#print axioms work2Tight
#print axioms work4Tight
#print axioms work9Tight

end TightEpidemicWork

end Ripple.PopulationProtocol.ExactMajority
