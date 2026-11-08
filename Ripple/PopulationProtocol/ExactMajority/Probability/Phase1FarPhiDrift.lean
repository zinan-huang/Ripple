/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Honest Phase-1 far-mass drift

This module reconstructs the useful part of the historical `FarPhiSurvival`
argument on the satisfiable gate `Phase1PartnerFloor.Phase1GapFloorEntry`.  In particular,
the gate is phase-only and carries a Main-count floor; it never assumes that the
whole population consists of Main agents.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhi
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1PartnerFloor
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1SurvivalContracting

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical

namespace Phase1FarPhiDrift

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## The missing honest high-side partner floor. -/

/-- Mixed-role mirror of `Phase1PartnerFloor.lowMainCount_core`. -/
theorem highMainCount_core (s : Multiset (AgentState L K)) :
    (Multiset.countP (fun a : AgentState L K => a.role = Role.main) s : ℤ)
        - 4 * (Multiset.countP
            (fun a : AgentState L K => a.role = Role.main ∧ 3 ≤ a.smallBias.val) s)
      ≤ -(s.map (fun a => AveragingRate.biasZ a)).sum := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons,
      Multiset.countP_cons]
    by_cases hmain : a.role = Role.main
    · have hbias : AveragingRate.biasZ a = (a.smallBias.val : ℤ) - 3 := by
        unfold AveragingRate.biasZ
        rw [if_pos hmain]
      rw [if_pos hmain]
      by_cases hhigh : 3 ≤ a.smallBias.val
      · rw [if_pos ⟨hmain, hhigh⟩, hbias]
        have := a.smallBias.isLt
        push_cast
        omega
      · rw [if_neg (fun hp => hhigh hp.2), hbias]
        push_cast
        omega
    · have hbias : AveragingRate.biasZ a = 0 := by
        unfold AveragingRate.biasZ
        rw [if_neg hmain]
      rw [if_neg hmain, if_neg (fun hp => hmain hp.1), hbias]
      push_cast
      omega

/-- Honest high-side counting bound relative to the Main-count floor. -/
theorem four_mul_highMainCount_ge_of_phase1GapFloorEntry (n g mc : ℕ)
    (c : Config (AgentState L K))
    (h : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℤ) - (g : ℤ)
      ≤ 4 * (Multiset.countP
          (fun a : AgentState L K => a.role = Role.main ∧ 3 ≤ a.smallBias.val) c) := by
  obtain ⟨_, hbound, _⟩ := h
  have hcore := highMainCount_core (L := L) (K := K) c
  have hsum : (c.map (fun a => AveragingRate.biasZ a)).sum
      = AveragingRate.centredBiasSum c := rfl
  have hmc :
      (Multiset.countP (fun a : AgentState L K => a.role = Role.main) c : ℤ)
        = (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℤ) := by
    unfold RoleSplitConcentration.mainCount
    rfl
  rw [hsum, hmc] at hcore
  obtain ⟨hge, _⟩ := abs_le.mp hbound
  omega

/-- Count bridge for the Main high-side set. -/
theorem highSet_sum_count_eq (c : Config (AgentState L K)) :
    (AveragingRate.highSet L K).sum c.count
      = Multiset.countP
          (fun a : AgentState L K => a.role = Role.main ∧ 3 ≤ a.smallBias.val) c := by
  classical
  rw [AveragingRate.highSet]
  rw [PartnerMargin.sum_count_filter_eq_countP (fun a => AveragingRate.high a) c]
  apply Multiset.countP_congr rfl
  intro a _
  simp only [AveragingRate.high]

/-- The honest high-side partner floor, symmetric to the landed low-side floor. -/
theorem highSet_floor_of_phase1GapFloorEntry (n g mc : ℕ)
    (c : Config (AgentState L K))
    (h : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    (mc - g + 3) / 4 ≤ (AveragingRate.highSet L K).sum c.count := by
  have hcount := four_mul_highMainCount_ge_of_phase1GapFloorEntry n g mc c h
  rw [← highSet_sum_count_eq (L := L) (K := K) c] at hcount
  have hmcle : (mc : ℤ) ≤
      (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℤ) := by
    exact_mod_cast h.2.2
  have hnat : mc - g ≤ 4 * (AveragingRate.highSet L K).sum c.count := by
    by_cases hng : g ≤ mc
    · have hcast : (mc : ℤ) - (g : ℤ) = ((mc - g : ℕ) : ℤ) := by omega
      have hchain : ((mc - g : ℕ) : ℤ)
          ≤ 4 * (AveragingRate.highSet L K).sum c.count := by
        rw [← hcast]
        omega
      exact_mod_cast hchain
    · simp only [Nat.not_le] at hng
      rw [Nat.sub_eq_zero_of_le (le_of_lt hng)]
      exact Nat.zero_le _
  omega

/-! ## Strict far-mass decrease and its counted rectangle. -/

theorem Transition_farPhi_pair_drop_high (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hsv : 5 ≤ s.smallBias.val) (htv : t.smallBias.val ≤ 3) :
    ((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K)).map (fun a => Phase1FarPhi.farPhiMainN a)).sum) + 1
      ≤ ((({s, t} : Multiset (AgentState L K)).map
          (fun a => Phase1FarPhi.farPhiMainN a)).sum) := by
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs1 ht1 hsM htM]
  rw [Phase1FarPhi.farPhiMainN_pair, Phase1FarPhi.farPhiMainN_pair]
  simp only [Phase1FarPhi.farPhiMainN, hsM, htM, if_pos]
  exact Phase1FarPhi.avgFin7_farPhi_pair_drop_high s.smallBias t.smallBias hsv htv

theorem Transition_farPhi_pair_drop_low (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hsv : s.smallBias.val ≤ 1) (htv : 3 ≤ t.smallBias.val) :
    ((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K)).map (fun a => Phase1FarPhi.farPhiMainN a)).sum) + 1
      ≤ ((({s, t} : Multiset (AgentState L K)).map
          (fun a => Phase1FarPhi.farPhiMainN a)).sum) := by
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs1 ht1 hsM htM]
  rw [Phase1FarPhi.farPhiMainN_pair, Phase1FarPhi.farPhiMainN_pair]
  simp only [Phase1FarPhi.farPhiMainN, hsM, htM, if_pos]
  exact Phase1FarPhi.avgFin7_farPhi_pair_drop_low s.smallBias t.smallBias hsv htv

theorem farPhiN_stepOrSelf_drop_high (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hsH : AveragingRate.farHigh s) (htL : AveragingRate.low t) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Phase1FarPhi.farPhiN c := by
  obtain ⟨_, hphase⟩ := hInv
  obtain ⟨hsM, hsv⟩ := hsH
  obtain ⟨htM, htv⟩ := htL
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsm : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htm : t ∈ c := Multiset.mem_of_le hsub (by simp)
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hsplit : c = (c - {s, t}) + ({s, t} : Multiset (AgentState L K)) := by
    rw [Multiset.sub_add_cancel hsub]
  have hpair := Transition_farPhi_pair_drop_high s t
    (hphase s hsm) (hphase t htm) hsM htM hsv htv
  unfold Phase1FarPhi.farPhiN
  rw [hc', Multiset.map_add, Multiset.sum_add]
  have hrhs : (c.map (fun a => Phase1FarPhi.farPhiMainN a)).sum
      = ((c - {s, t}).map (fun a => Phase1FarPhi.farPhiMainN a)).sum
        + (({s, t} : Multiset (AgentState L K)).map
            (fun a => Phase1FarPhi.farPhiMainN a)).sum := by
    conv_lhs => rw [hsplit]
    rw [Multiset.map_add, Multiset.sum_add]
  omega

theorem farPhiN_stepOrSelf_drop_low (n : ℕ) (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hsL : AveragingRate.farLow s) (htH : AveragingRate.high t) :
    Phase1FarPhi.farPhiN
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Phase1FarPhi.farPhiN c := by
  obtain ⟨_, hphase⟩ := hInv
  obtain ⟨hsM, hsv⟩ := hsL
  obtain ⟨htM, htv⟩ := htH
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsm : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htm : t ∈ c := Multiset.mem_of_le hsub (by simp)
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hsplit : c = (c - {s, t}) + ({s, t} : Multiset (AgentState L K)) := by
    rw [Multiset.sub_add_cancel hsub]
  have hpair := Transition_farPhi_pair_drop_low s t
    (hphase s hsm) (hphase t htm) hsM htM hsv htv
  unfold Phase1FarPhi.farPhiN
  rw [hc', Multiset.map_add, Multiset.sum_add]
  have hrhs : (c.map (fun a => Phase1FarPhi.farPhiMainN a)).sum
      = ((c - {s, t}).map (fun a => Phase1FarPhi.farPhiMainN a)).sum
        + (({s, t} : Multiset (AgentState L K)).map
            (fun a => Phase1FarPhi.farPhiMainN a)).sum := by
    conv_lhs => rw [hsplit]
    rw [Multiset.map_add, Multiset.sum_add]
  omega

theorem farPhiN_drop_prob_rect_high (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) :
    ENNReal.ofReal
        (((AveragingRate.farHighSet L K).sum c.count *
            (AveragingRate.lowSet L K).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1FarPhi.farPhiN c' + 1 ≤ Phase1FarPhi.farPhiN c} := by
  refine Phase7Convergence.drop_prob_of_rect (fun c => Phase1FarPhi.farPhiN c)
    n hn c hInv.1
    ((AveragingRate.farHighSet L K) ×ˢ (AveragingRate.lowSet L K)) _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    simp only [AveragingRate.farHighSet, Finset.mem_filter] at hsmem
    simp only [AveragingRate.lowSet, Finset.mem_filter] at htmem
    obtain ⟨_, hsH⟩ := hsmem
    obtain ⟨_, htL⟩ := htmem
    have happ : Protocol.Applicable c s t := by
      have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
      have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
      have hne : s ≠ t := AveragingRate.farHigh_low_disjoint s
        (by simp only [AveragingRate.farHighSet, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hsH⟩) t
        (by simp only [AveragingRate.lowSet, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, htL⟩)
      exact Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact farPhiN_stepOrSelf_drop_high n c hInv s t happ hsH htL
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      AveragingRate.farHigh_low_disjoint]

theorem farPhiN_drop_prob_rect_low (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) :
    ENNReal.ofReal
        (((AveragingRate.farLowSet L K).sum c.count *
            (AveragingRate.highSet L K).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1FarPhi.farPhiN c' + 1 ≤ Phase1FarPhi.farPhiN c} := by
  refine Phase7Convergence.drop_prob_of_rect (fun c => Phase1FarPhi.farPhiN c)
    n hn c hInv.1
    ((AveragingRate.farLowSet L K) ×ˢ (AveragingRate.highSet L K)) _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    simp only [AveragingRate.farLowSet, Finset.mem_filter] at hsmem
    simp only [AveragingRate.highSet, Finset.mem_filter] at htmem
    obtain ⟨_, hsL⟩ := hsmem
    obtain ⟨_, htH⟩ := htmem
    have happ : Protocol.Applicable c s t := by
      have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
      have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
      have hne : s ≠ t := AveragingRate.farLow_high_disjoint s
        (by simp only [AveragingRate.farLowSet, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hsL⟩) t
        (by simp only [AveragingRate.highSet, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, htH⟩)
      exact Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact farPhiN_stepOrSelf_drop_low n c hInv s t happ hsL htH
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      AveragingRate.farLow_high_disjoint]

theorem farPhiN_drop_floor_high {n : ℕ} (hn : 2 ≤ n) (P : ℕ)
    (b : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n b)
    (hfar : 1 ≤ (AveragingRate.farHighSet L K).sum b.count)
    (hpart : P ≤ (AveragingRate.lowSet L K).sum b.count) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (NonuniformMajority L K).transitionKernel b
          {c' | Phase1FarPhi.farPhiN c' + 1 ≤ Phase1FarPhi.farPhiN b} := by
  change ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure _
  refine le_trans ?_ (farPhiN_drop_prob_rect_high n hn b hInv)
  have hprod : P ≤ (AveragingRate.farHighSet L K).sum b.count *
      (AveragingRate.lowSet L K).sum b.count := by
    calc
      P ≤ 1 * P := by omega
      _ ≤ (AveragingRate.farHighSet L K).sum b.count * P :=
        Nat.mul_le_mul_right _ hfar
      _ ≤ (AveragingRate.farHighSet L K).sum b.count *
          (AveragingRate.lowSet L K).sum b.count := Nat.mul_le_mul_left _ hpart
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

theorem farPhiN_drop_floor_low {n : ℕ} (hn : 2 ≤ n) (P : ℕ)
    (b : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n b)
    (hfar : 1 ≤ (AveragingRate.farLowSet L K).sum b.count)
    (hpart : P ≤ (AveragingRate.highSet L K).sum b.count) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (NonuniformMajority L K).transitionKernel b
          {c' | Phase1FarPhi.farPhiN c' + 1 ≤ Phase1FarPhi.farPhiN b} := by
  change ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure _
  refine le_trans ?_ (farPhiN_drop_prob_rect_low n hn b hInv)
  have hprod : P ≤ (AveragingRate.farLowSet L K).sum b.count *
      (AveragingRate.highSet L K).sum b.count := by
    calc
      P ≤ 1 * P := by omega
      _ ≤ (AveragingRate.farLowSet L K).sum b.count * P :=
        Nat.mul_le_mul_right _ hfar
      _ ≤ (AveragingRate.farLowSet L K).sum b.count *
          (AveragingRate.highSet L K).sum b.count := Nat.mul_le_mul_left _ hpart
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-! ## Side-free drift on the honest entry gate. -/

theorem far_mem_side (c : Config (AgentState L K)) (a : AgentState L K)
    (ha : a ∈ c) (hfar : AveragingRate.far a) :
    1 ≤ (AveragingRate.farLowSet L K).sum c.count ∨
      1 ≤ (AveragingRate.farHighSet L K).sum c.count := by
  classical
  obtain ⟨hmain, hlo | hhi⟩ := hfar
  · refine Or.inl ?_
    have hmem : a ∈ AveragingRate.farLowSet L K := by
      simp only [AveragingRate.farLowSet, Finset.mem_filter, AveragingRate.farLow]
      exact ⟨Finset.mem_univ _, hmain, hlo⟩
    calc
      (1 : ℕ) ≤ c.count a := Multiset.one_le_count_iff_mem.mpr ha
      _ ≤ (AveragingRate.farLowSet L K).sum c.count :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (c.count i)) hmem
  · refine Or.inr ?_
    have hmem : a ∈ AveragingRate.farHighSet L K := by
      simp only [AveragingRate.farHighSet, Finset.mem_filter, AveragingRate.farHigh]
      exact ⟨Finset.mem_univ _, hmain, hhi⟩
    calc
      (1 : ℕ) ≤ c.count a := Multiset.one_le_count_iff_mem.mpr ha
      _ ≤ (AveragingRate.farHighSet L K).sum c.count :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (c.count i)) hmem

theorem farMain_of_farPhiN_ge_one (c : Config (AgentState L K))
    (h : 1 ≤ Phase1FarPhi.farPhiN c) :
    ∃ a ∈ c, AveragingRate.far a := by
  classical
  by_contra hno
  push Not at hno
  have hsafe : Phase1FarPhi.MainBiasSafe (L := L) (K := K) c := by
    intro a ha hmain
    have hnfar : ¬ AveragingRate.far a := hno a ha
    unfold AveragingRate.far at hnfar
    push Not at hnfar
    have hbounds := hnfar hmain
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hz := (Phase1FarPhi.farPhiN_eq_zero_iff_mainBiasSafe c).2 hsafe
  omega

theorem farPhiN_drop_floor_of_phase1GapFloorEntry {n g mc : ℕ} (hn : 2 ≤ n)
    (b : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc b)
    (hge : 1 ≤ Phase1FarPhi.farPhiN b) :
    ENNReal.ofReal ((((mc - g + 3) / 4 : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ (NonuniformMajority L K).transitionKernel b
          {c' | Phase1FarPhi.farPhiN c' + 1 ≤ Phase1FarPhi.farPhiN b} := by
  obtain ⟨a, ha, hfar⟩ := farMain_of_farPhiN_ge_one b hge
  rcases far_mem_side b a ha hfar with hlo | hhi
  · exact farPhiN_drop_floor_low hn ((mc - g + 3) / 4) b hentry.1 hlo
      (highSet_floor_of_phase1GapFloorEntry n g mc b hentry)
  · exact farPhiN_drop_floor_high hn ((mc - g + 3) / 4) b hentry.1 hhi
      (Phase1PartnerFloor.lowSet_floor_of_phase1GapFloorEntry n g mc b hentry)

theorem farPhiN_drift_of_phase1GapFloorEntry {n g mc : ℕ} (hn : 2 ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (b : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc b)
    (hge : 1 ≤ Phase1FarPhi.farPhiN b) :
    ∫⁻ c', expDrainPot (L := L) (K := K) Phase1FarPhi.farPhiN s c'
        ∂((NonuniformMajority L K).transitionKernel b)
      ≤ contractRate (ENNReal.ofReal ((((mc - g + 3) / 4 : ℕ) : ℝ) /
            ((n : ℝ) * ((n : ℝ) - 1)))) s *
          expDrainPot (L := L) (K := K) Phase1FarPhi.farPhiN s b := by
  refine expDrainPot_drift_contracting (L := L) (K := K)
    (NonuniformMajority L K).transitionKernel Phase1FarPhi.farPhiN s hs
    (ENNReal.ofReal ((((mc - g + 3) / 4 : ℕ) : ℝ) /
      ((n : ℝ) * ((n : ℝ) - 1)))) b ?_ ?_
  · exact farPhiN_drop_floor_of_phase1GapFloorEntry hn b hentry hge
  · exact Phase1FarPhi.farPhiN_kernel_noincr_of_phase1Win n b hentry.1

/-! ## Stop the MGF exactly at the safe boundary. -/

noncomputable def stoppedFarPot (s : ℝ) :
    Config (AgentState L K) → ℝ≥0∞ :=
  fun c => if 0 < Phase1FarPhi.farPhiN c
    then ENNReal.ofReal (Real.exp (s * (Phase1FarPhi.farPhiN c : ℝ))) else 0

theorem stoppedFarPot_le (s : ℝ) (c : Config (AgentState L K)) :
    stoppedFarPot (L := L) (K := K) s c
      ≤ expDrainPot (L := L) (K := K) Phase1FarPhi.farPhiN s c := by
  unfold stoppedFarPot expDrainPot
  by_cases h : 0 < Phase1FarPhi.farPhiN c
  · rw [if_pos h]
  · rw [if_neg h]
    exact bot_le

theorem stoppedFarPot_threshold_iff (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) :
    ENNReal.ofReal (Real.exp s) ≤ stoppedFarPot (L := L) (K := K) s c
      ↔ 1 ≤ Phase1FarPhi.farPhiN c := by
  unfold stoppedFarPot
  by_cases h : 0 < Phase1FarPhi.farPhiN c
  · rw [if_pos h]
    have h1 : 1 ≤ Phase1FarPhi.farPhiN c := h
    simp only [h1, iff_true]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp]
    have hle : (1 : ℝ) ≤ (Phase1FarPhi.farPhiN c : ℝ) := by exact_mod_cast h1
    nlinarith [hle, hs]
  · rw [if_neg h]
    have hz : Phase1FarPhi.farPhiN c = 0 := by omega
    rw [hz]
    simp only [Nat.one_le_iff_ne_zero, ne_eq, not_true_eq_false, iff_false, not_le]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

theorem above_done_null_of_zero {n : ℕ} (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hz : Phase1FarPhi.farPhiN c = 0) :
    (NonuniformMajority L K).transitionKernel c
        {c' | 0 < Phase1FarPhi.farPhiN c'} = 0 := by
  refine measure_mono_null ?_
    (Phase1FarPhi.farPhiN_kernel_noincr_of_phase1Win n c hInv)
  intro c' hc'
  simp only [Set.mem_setOf_eq] at hc' ⊢
  omega

/-- Uniform stopped drift on the truthful honest-entry gate. -/
theorem stoppedFarPot_drift_of_phase1GapFloorEntry {n g mc : ℕ} (hn : 2 ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (c : Config (AgentState L K))
    (hentry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    ∫⁻ c', stoppedFarPot (L := L) (K := K) s c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ contractRate (ENNReal.ofReal ((((mc - g + 3) / 4 : ℕ) : ℝ) /
            ((n : ℝ) * ((n : ℝ) - 1)))) s *
          stoppedFarPot (L := L) (K := K) s c := by
  set ρ : ℝ≥0∞ := ENNReal.ofReal ((((mc - g + 3) / 4 : ℕ) : ℝ) /
    ((n : ℝ) * ((n : ℝ) - 1))) with hρ
  by_cases hge : 1 ≤ Phase1FarPhi.farPhiN c
  · have hpos : 0 < Phase1FarPhi.farPhiN c := hge
    have hstop : stoppedFarPot (L := L) (K := K) s c
        = expDrainPot (L := L) (K := K) Phase1FarPhi.farPhiN s c := by
      unfold stoppedFarPot expDrainPot
      rw [if_pos hpos]
    calc
      ∫⁻ c', stoppedFarPot (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ ∫⁻ c', expDrainPot (L := L) (K := K) Phase1FarPhi.farPhiN s c'
            ∂((NonuniformMajority L K).transitionKernel c) :=
          lintegral_mono (fun c' => stoppedFarPot_le s c')
      _ ≤ contractRate ρ s *
          expDrainPot (L := L) (K := K) Phase1FarPhi.farPhiN s c :=
        farPhiN_drift_of_phase1GapFloorEntry hn s hs c hentry hge
      _ = contractRate ρ s * stoppedFarPot (L := L) (K := K) s c := by rw [hstop]
  · have hz : Phase1FarPhi.farPhiN c = 0 := by omega
    have hnpos : ¬ 0 < Phase1FarPhi.farPhiN c := by omega
    have hstop : stoppedFarPot (L := L) (K := K) s c = 0 := by
      unfold stoppedFarPot
      rw [if_neg hnpos]
    have hnull := above_done_null_of_zero c hentry.1 hz
    have hae : (fun c' => stoppedFarPot (L := L) (K := K) s c') =ᵐ[
        (NonuniformMajority L K).transitionKernel c] (fun _ => 0) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{c' | 0 < Phase1FarPhi.farPhiN c'}ᶜ, ?_, ?_⟩
      · rw [mem_ae_iff, compl_compl]
        exact hnull
      · intro c' hc'
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, Nat.le_zero] at hc'
        show stoppedFarPot (L := L) (K := K) s c' = 0
        simp [stoppedFarPot, hc']
    rw [lintegral_congr_ae hae, lintegral_zero, hstop, mul_zero]

#print axioms highSet_floor_of_phase1GapFloorEntry
#print axioms Transition_farPhi_pair_drop_high
#print axioms Transition_farPhi_pair_drop_low
#print axioms farPhiN_drop_prob_rect_high
#print axioms farPhiN_drop_prob_rect_low
#print axioms farPhiN_drop_floor_of_phase1GapFloorEntry
#print axioms farPhiN_drift_of_phase1GapFloorEntry
#print axioms stoppedFarPot_threshold_iff
#print axioms stoppedFarPot_drift_of_phase1GapFloorEntry

end Phase1FarPhiDrift
end Ripple.PopulationProtocol.ExactMajority
