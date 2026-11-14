-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingPotentialService.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingIntegerPotential
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoDrainedSafety

/-!
# Full next-step potential service, including sampled gate exits

Only current-state hypotheses occur below. In particular a Clock/Clock
transition creating Phase 4 is retained in the next-step potential. This is
the form needed before replacing a sampled gate-exit logarithmic increment.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingPotentialService

open TimeTheorem P3DeterministicAlgebra AveragingMixedAlgebra
open AveragingMixedLedgers AveragingMixedPotentialTransitions AveragingIntegerPotential
open PhaseTwoActivationLocal

variable {L : ℕ}

structure PotentialAgent (a : AgentState L 256) : Prop where
  range : 1 ≤ a.phase.val ∧ a.phase.val ≤ 3
  wf : AdvanceNoOvershoot.WfAgent a
  small_carrier : a.role ≠ .main → a.smallBias.val = 3
  active_carrier : a.phase.val = 3 → a.role ≠ .main → a.bias = .zero

def PotentialDomain (c : Cfg L 256) : Prop :=
  ∀ a ∈ c, PotentialAgent a

def ReadyZero (h : ℕ) (a : AgentState L 256) : Prop :=
  a.phase.val = 3 ∧ a.role = .main ∧ a.bias = .zero ∧ h ≤ a.hour.val

theorem PotentialAgent.safe {a : AgentState L 256} (ha : PotentialAgent a) :
    a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  have hb : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4 := ha.wf.2
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem ready_phi_zero (h : ℕ) (a : AgentState L 256) (ha : ReadyZero h a) :
    augmentedAgentPhi h a = 0 := by
  simp [augmentedAgentPhi, ha.1, agentPhiAboveQ, phiBiasWeightQ, ha.2.2.1]

theorem ready_phiNat_zero (h : ℕ) (a : AgentState L 256) (ha : ReadyZero h a) :
    augmentedAgentPhiNat h a = 0 := by
  simp [augmentedAgentPhiNat, activeAgentPhiNat, ha.1, ha.2.2.1]

theorem transition_phi_pair_le_full (h : ℕ) (hh : 1 ≤ h)
    (s t : AgentState L 256) (hs : PotentialAgent s) (ht : PotentialAgent t) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      augmentedAgentPhi h s + augmentedAgentPhi h t := by
  by_cases hmax : max s.phase.val t.phase.val ≤ 2
  · have hslo : s.phase.val ≤ 2 := (le_max_left _ _).trans hmax
    have htlo : t.phase.val ≤ 2 := (le_max_right _ _).trans hmax
    have hcap := PhaseTwoDrainedSafety.transition_phase_upper_succ 2 (by omega)
      s t hs.wf ht.wf hslo htlo
    exact transition_phi_pair_le h hh s t hs.range ht.range hs.safe ht.safe
      hs.small_carrier ht.small_carrier hcap.1 hcap.2
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by
      have := hs.range
      have := ht.range
      omega
    have hcap := PhaseTwoDrainedSafety.transition_phase_upper_succ 3 (by omega)
      s t hs.wf ht.wf hs.range.2 ht.range.2
    have hep := epidemic_three_phases_of_success s t hs.range ht.range hmaxeq
      (by omega) (by omega)
    have hinit := epidemic_three_phi_le h hh s t hs.range ht.range hmaxeq
      hs.safe ht.safe hs.small_carrier ht.small_carrier
    exact (transition_phi_le_epidemic h s t hep.1 hep.2).trans
      (add_le_add hinit.1 hinit.2)

theorem pending_left_half_loss_full (h : ℕ) (hh : 1 ≤ h)
    (s t : AgentState L 256) (hs : PotentialAgent s) (ht : PotentialAgent t)
    (hsp : s.phase.val < 3) (htp : t.phase.val = 3) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      (1 / 2 : ℚ) * augmentedAgentPhi h s + augmentedAgentPhi h t := by
  have hmax : max s.phase.val t.phase.val = 3 := by
    have := hs.range
    omega
  have hcap := PhaseTwoDrainedSafety.transition_phase_upper_succ 3 (by omega)
    s t hs.wf ht.wf hs.range.2 ht.range.2
  have hep := epidemic_three_phases_of_success s t hs.range ht.range hmax
    (by omega) (by omega)
  have heq := epidemic_three_phi_eq h hh s t hs.range ht.range hmax
    hs.safe ht.safe hs.small_carrier ht.small_carrier
  have hlocal := transition_phi_le_epidemic h s t hep.1 hep.2
  simpa only [heq.1, heq.2, if_pos hsp, htp,
    show ¬ (3 : ℕ) < 3 by omega, if_false] using hlocal

theorem pending_right_half_loss_full (h : ℕ) (hh : 1 ≤ h)
    (s t : AgentState L 256) (hs : PotentialAgent s) (ht : PotentialAgent t)
    (hsp : s.phase.val = 3) (htp : t.phase.val < 3) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      augmentedAgentPhi h s + (1 / 2 : ℚ) * augmentedAgentPhi h t := by
  have hmax : max s.phase.val t.phase.val = 3 := by
    have := ht.range
    omega
  have hcap := PhaseTwoDrainedSafety.transition_phase_upper_succ 3 (by omega)
    s t hs.wf ht.wf hs.range.2 ht.range.2
  have hep := epidemic_three_phases_of_success s t hs.range ht.range hmax
    (by omega) (by omega)
  have heq := epidemic_three_phi_eq h hh s t hs.range ht.range hmax
    hs.safe ht.safe hs.small_carrier ht.small_carrier
  have hlocal := transition_phi_le_epidemic h s t hep.1 hep.2
  simpa only [heq.1, heq.2, if_pos htp, hsp,
    show ¬ (3 : ℕ) < 3 by omega, if_false] using hlocal

theorem main_transition_eq_cancelSplit (s t : AgentState L 256)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main) :
    Transition L 256 s t = phase3CancelSplit L 256 s t := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hwork : Phase3Transition L 256 s t = phase3CancelSplit L 256 s t := by
    simp [Phase3Transition, hsm, htm]
  have hph := phase3CancelSplit_phase_preserved L 256 s t
  have hlno : (phase3CancelSplit L 256 s t).1.phase.val ≠ 10 := by
    rw [hph.1, hs]
    decide
  have hrno : (phase3CancelSplit L 256 s t).2.phase.val ≠ 10 := by
    rw [hph.2, ht]
    decide
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [hwork, finishPhase10Entry_eq_self_of_after_ne_10 L 256 s _ hlno,
    finishPhase10Entry_eq_self_of_after_ne_10 L 256 t _ hrno]

theorem ready_partner_left_half_loss (h : ℕ) (hh : 1 ≤ h)
    (s t : AgentState L 256) (hs : PotentialAgent s) (ht : PotentialAgent t)
    (hready : ReadyZero h t) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      (1 / 2 : ℚ) * augmentedAgentPhi h s + augmentedAgentPhi h t := by
  have hmono := transition_phi_pair_le_full h hh s t hs ht
  by_cases hsp : s.phase.val < 3
  · exact pending_left_half_loss_full h hh s t hs ht hsp hready.1
  have hthree : s.phase.val = 3 := by have := hs.range; omega
  by_cases hsm : s.role = .main
  · cases hb : s.bias with
    | zero =>
        have hz : augmentedAgentPhi h s = 0 := by
          simp [augmentedAgentPhi, hthree, agentPhiAboveQ, phiBiasWeightQ, hb]
        simpa [hz] using hmono
    | dyadic sigma j =>
        by_cases hj : j.val < h
        · have hgt : t.hour.val > j.val := lt_of_lt_of_le hj hready.2.2.2
          have hdrop := p3_phiAbove_split_delta_right h s t sigma j hb
            hready.2.2.1 hgt hj
          have hph := phase3CancelSplit_phase_preserved L 256 s t
          rw [main_transition_eq_cancelSplit s t hthree hready.1 hsm hready.2.1]
          calc
            augmentedAgentPhi h (phase3CancelSplit L 256 s t).1 +
                augmentedAgentPhi h (phase3CancelSplit L 256 s t).2 =
                pairPhiAboveQ h (phase3CancelSplit L 256 s t).1
                  (phase3CancelSplit L 256 s t).2 := by
                    simp [augmentedAgentPhi, hph.1, hph.2, hthree, hready.1,
                      pairPhiAboveQ]
            _ ≤ pairPhiAboveQ h s t - (1 / 2 : ℚ) * 4 ^ (h - 1 - j.val) := hdrop
            _ = (1 / 2 : ℚ) * augmentedAgentPhi h s + augmentedAgentPhi h t := by
              simp [augmentedAgentPhi, hthree, hready.1, pairPhiAboveQ,
                agentPhiAboveQ, phiBiasWeightQ, hb, hready.2.2.1, hj]
              <;> ring
        · have hz : augmentedAgentPhi h s = 0 := by
            simp [augmentedAgentPhi, hthree, agentPhiAboveQ, phiBiasWeightQ, hb, hj]
          simpa [hz] using hmono
  · have hb := hs.active_carrier hthree hsm
    have hz : augmentedAgentPhi h s = 0 := by
      simp [augmentedAgentPhi, hthree, agentPhiAboveQ, phiBiasWeightQ, hb]
    simpa [hz] using hmono

theorem ready_partner_right_half_loss (h : ℕ) (hh : 1 ≤ h)
    (s t : AgentState L 256) (hs : PotentialAgent s) (ht : PotentialAgent t)
    (hready : ReadyZero h s) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      augmentedAgentPhi h s + (1 / 2 : ℚ) * augmentedAgentPhi h t := by
  have hmono := transition_phi_pair_le_full h hh s t hs ht
  by_cases htp : t.phase.val < 3
  · exact pending_right_half_loss_full h hh s t hs ht hready.1 htp
  have hthree : t.phase.val = 3 := by have := ht.range; omega
  by_cases htm : t.role = .main
  · cases hb : t.bias with
    | zero =>
        have hz : augmentedAgentPhi h t = 0 := by
          simp [augmentedAgentPhi, hthree, agentPhiAboveQ, phiBiasWeightQ, hb]
        simpa [hz] using hmono
    | dyadic sigma j =>
        by_cases hj : j.val < h
        · have hgt : s.hour.val > j.val := lt_of_lt_of_le hj hready.2.2.2
          have hdrop := p3_phiAbove_split_delta_left h s t sigma j
            hready.2.2.1 hb hgt hj
          have hph := phase3CancelSplit_phase_preserved L 256 s t
          rw [main_transition_eq_cancelSplit s t hready.1 hthree hready.2.1 htm]
          calc
            augmentedAgentPhi h (phase3CancelSplit L 256 s t).1 +
                augmentedAgentPhi h (phase3CancelSplit L 256 s t).2 =
                pairPhiAboveQ h (phase3CancelSplit L 256 s t).1
                  (phase3CancelSplit L 256 s t).2 := by
                    simp [augmentedAgentPhi, hph.1, hph.2, hthree, hready.1,
                      pairPhiAboveQ]
            _ ≤ pairPhiAboveQ h s t - (1 / 2 : ℚ) * 4 ^ (h - 1 - j.val) := hdrop
            _ = augmentedAgentPhi h s + (1 / 2 : ℚ) * augmentedAgentPhi h t := by
              simp [augmentedAgentPhi, hthree, hready.1, pairPhiAboveQ,
                agentPhiAboveQ, phiBiasWeightQ, hb, hready.2.2.1, hj]
              <;> ring
        · have hz : augmentedAgentPhi h t = 0 := by
            simp [augmentedAgentPhi, hthree, agentPhiAboveQ, phiBiasWeightQ, hb, hj]
          simpa [hz] using hmono
  · have hb := ht.active_carrier hthree htm
    have hz : augmentedAgentPhi h t = 0 := by
      simp [augmentedAgentPhi, hthree, agentPhiAboveQ, phiBiasWeightQ, hb]
    simpa [hz] using hmono

theorem phiNat_pair_le (h : ℕ) (hh : 1 ≤ h)
    (s t : AgentState L 256) (hs : PotentialAgent s) (ht : PotentialAgent t) :
    augmentedAgentPhiNat h (Transition L 256 s t).1 +
        augmentedAgentPhiNat h (Transition L 256 s t).2 ≤
      augmentedAgentPhiNat h s + augmentedAgentPhiNat h t := by
  have hh' := transition_phi_pair_le_full h hh s t hs ht
  have hcast :
      ((augmentedAgentPhiNat h (Transition L 256 s t).1 +
        augmentedAgentPhiNat h (Transition L 256 s t).2 : ℕ) : ℚ) ≤
      ((augmentedAgentPhiNat h s + augmentedAgentPhiNat h t : ℕ) : ℚ) := by
    simpa only [Nat.cast_add, augmentedAgentPhiNat_cast] using hh'
  exact_mod_cast hcast

open Classical in
def pairService (h : ℕ) (s t : AgentState L 256) : ℕ :=
  (if ReadyZero h t then augmentedAgentPhiNat h s else 0) +
    (if ReadyZero h s then augmentedAgentPhiNat h t else 0)

theorem phiNat_pair_service (h : ℕ) (hh : 1 ≤ h)
    (s t : AgentState L 256) (hs : PotentialAgent s) (ht : PotentialAgent t) :
    2 * (augmentedAgentPhiNat h (Transition L 256 s t).1 +
        augmentedAgentPhiNat h (Transition L 256 s t).2) + pairService h s t ≤
      2 * (augmentedAgentPhiNat h s + augmentedAgentPhiNat h t) := by
  classical
  have hmono := transition_phi_pair_le_full h hh s t hs ht
  have hq :
      (2 : ℚ) * (augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2) +
        (pairService h s t : ℚ) ≤
      2 * (augmentedAgentPhi h s + augmentedAgentPhi h t) := by
    by_cases hr : ReadyZero h t
    · by_cases hl : ReadyZero h s
      · simp only [pairService, if_pos hr, if_pos hl,
          ready_phiNat_zero h s hl, ready_phiNat_zero h t hr,
          Nat.cast_add, Nat.cast_zero, add_zero]
        have hz := ready_phi_zero h s hl
        have hz' := ready_phi_zero h t hr
        linarith
      · have hhalf := ready_partner_left_half_loss h hh s t hs ht hr
        simp only [pairService, if_pos hr, if_neg hl, add_zero,
          augmentedAgentPhiNat_cast]
        linarith
    · by_cases hl : ReadyZero h s
      · have hhalf := ready_partner_right_half_loss h hh s t hs ht hl
        simp only [pairService, if_neg hr, if_pos hl, zero_add,
          augmentedAgentPhiNat_cast]
        linarith
      · simp only [pairService, if_neg hr, if_neg hl, zero_add, Nat.cast_zero,
          add_zero]
        linarith
  have hcast :
      ((2 * (augmentedAgentPhiNat h (Transition L 256 s t).1 +
        augmentedAgentPhiNat h (Transition L 256 s t).2) + pairService h s t : ℕ) : ℚ) ≤
      ((2 * (augmentedAgentPhiNat h s + augmentedAgentPhiNat h t) : ℕ) : ℚ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      augmentedAgentPhiNat_cast] using hq
  exact_mod_cast hcast

theorem phiNat_add_pair (h : ℕ) (c : Cfg L 256) (s t : AgentState L 256) :
    augmentedPhiNat h (c + {s, t}) =
      augmentedPhiNat h c + (augmentedAgentPhiNat h s + augmentedAgentPhiNat h t) := by
  simp [augmentedPhiNat, Multiset.map_add, Multiset.sum_add,
    add_assoc, add_left_comm]

theorem phiNat_step_le (h : ℕ) (hh : 1 ≤ h) (c : Cfg L 256)
    (hc : PotentialDomain c) (s t : AgentState L 256) :
    augmentedPhiNat h (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      augmentedPhiNat h c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hp := phiNat_pair_le h hh s t (hc s hs) (hc t ht)
    have heq : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
        c - {s,t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsplit : c = c - {s,t} + ({s,t} : Multiset (AgentState L 256)) :=
      (Multiset.sub_add_cancel happ).symm
    rw [heq, phiNat_add_pair]
    conv_rhs => rw [hsplit]
    rw [phiNat_add_pair]
    exact add_le_add le_rfl hp
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem phiNat_draw_le (h : ℕ) (hh : 1 ≤ h) (c : Cfg L 256)
    (hc : PotentialDomain c) (o : Draw L 256) :
    augmentedPhiNat h (applyDraw c o) ≤ augmentedPhiNat h c := by
  cases o with
  | none => exact le_rfl
  | some p => exact phiNat_step_le h hh c hc p.1.1 p.2.1

theorem phiNat_step_service (h : ℕ) (hh : 1 ≤ h) (c : Cfg L 256)
    (hc : PotentialDomain c) (s t : AgentState L 256)
    (happ : Protocol.Applicable c s t) :
    2 * augmentedPhiNat h
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + pairService h s t ≤
      2 * augmentedPhiNat h c := by
  classical
  have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hp := phiNat_pair_service h hh s t (hc s hs) (hc t ht)
  have heq : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
      c - {s,t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hsplit : c = c - {s,t} + ({s,t} : Multiset (AgentState L 256)) :=
    (Multiset.sub_add_cancel happ).symm
  rw [heq, phiNat_add_pair]
  conv_rhs => rw [hsplit]
  rw [phiNat_add_pair]
  omega

theorem phiNat_step_drop_le_pair (h : ℕ) (c : Cfg L 256)
    (s t : AgentState L 256) (happ : Protocol.Applicable c s t) :
    augmentedPhiNat h c -
        augmentedPhiNat h (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      augmentedAgentPhiNat h s + augmentedAgentPhiNat h t := by
  classical
  have heq : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
      c - {s,t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hsplit : c = c - {s,t} + ({s,t} : Multiset (AgentState L 256)) :=
    (Multiset.sub_add_cancel happ).symm
  rw [heq, phiNat_add_pair]
  conv_lhs => lhs; rw [hsplit, phiNat_add_pair]
  omega

end Ripple.PopulationProtocol.ExactMajority.AveragingPotentialService

end
