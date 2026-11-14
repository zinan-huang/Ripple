import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMixedLedgers

/-!
# Actual mixed 1/2/3 monotonicity of the double-pending potential

This file includes Phase-1 averaging, the Phase-2 first-seed dispatch, epidemic
initialization, and the selected Phase-3 rule. It proves deterministic
nonincrease, not the positive-rate kernel drift.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingMixedPotentialTransitions

open TimeTheorem P3DeterministicAlgebra AveragingMixedAlgebra AveragingMixedLedgers
open PhaseTwoActivationLocal PhaseTwoProvenance

variable {L : ℕ}

theorem fresh_phi_eq_half_pending
    (h : ℕ) (hh : 1 ≤ h) (a : AgentState L 256)
    (hfresh : Phase3Pre3.Phase3EntryAgent a)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    augmentedAgentPhi h a = (1 / 2 : ℚ) * pendingPotentialWeight h a := by
  have hpos : 0 < h := by omega
  by_cases hm : a.role = .main
  · have hb := Phase3Pre3.main_bias_of_Phase3EntryAgent hfresh hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hsmall | hsmall | hsmall <;>
      simp [augmentedAgentPhi, hfresh.1, agentPhiAboveQ, phiBiasWeightQ,
        hb, Phase3Pre3.phase3BiasOfSmallBias, pendingPotentialWeight,
        AgentState.smallBiasInt, hsmall, hpos] <;> ring
  · have hb := Phase3Pre3.nonMain_bias_zero_of_Phase3EntryAgent hfresh hm
    simp [augmentedAgentPhi, hfresh.1, agentPhiAboveQ, phiBiasWeightQ,
      hb, pendingPotentialWeight, AgentState.smallBiasInt, hcarrier hm]

theorem pending_phi_le
    (h : ℕ) (hh : 1 ≤ h) (before after : AgentState L 256)
    (hb : before.phase.val ≤ 2) (ha : after.phase.val ≤ 3)
    (hrole : after.role = before.role)
    (hsmall : after.smallBias = before.smallBias)
    (hsafe : before.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : before.role ≠ .main → before.smallBias.val = 3)
    (hfresh : after.phase.val = 3 → Phase3Pre3.Phase3EntryAgent after) :
    augmentedAgentPhi h after ≤ augmentedAgentPhi h before := by
  have hbp : before.phase.val < 3 := by omega
  by_cases hp : after.phase.val = 3
  · have hsafeAfter : after.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      simpa only [hsmall] using hsafe
    have hcarrierAfter : after.role ≠ .main → after.smallBias.val = 3 := by
      intro hm
      have hmBefore : before.role ≠ .main := by simpa only [hrole] using hm
      simpa only [hsmall] using hcarrier hmBefore
    have hf := fresh_phi_eq_half_pending h hh after (hfresh hp)
      hsafeAfter hcarrierAfter
    have hw : pendingPotentialWeight h after = pendingPotentialWeight h before := by
      simp only [pendingPotentialWeight, AgentState.smallBiasInt, hsmall]
    have hn : 0 ≤ pendingPotentialWeight h before := by
      unfold pendingPotentialWeight
      positivity
    rw [hf, hw]
    simp only [augmentedAgentPhi, if_pos hbp]
    linarith
  · have hap : after.phase.val < 3 := by omega
    simp only [augmentedAgentPhi, if_pos hbp, if_pos hap,
      pendingPotentialWeight, AgentState.smallBiasInt, hsmall, le_refl]

theorem enterThree_phi_eq_initialize
    (h : ℕ) (a : AgentState L 256)
    (hp : 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    augmentedAgentPhi h (enterThree a) =
      augmentedAgentPhi h (initializeAtPhaseThree a) := by
  have hcases : a.phase.val = 1 ∨ a.phase.val = 2 := by omega
  rcases hcases with hone | htwo
  · have hlist : (List.range 11).filter
        (fun k => decide (1 < k) && decide (k ≤ 3)) = [2, 3] := by decide
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hsmall | hsmall | hsmall <;>
      cases hr : a.role <;>
      simp [enterThree, hone, runInitsBetween, hlist, initializeAtPhaseThree,
        augmentedAgentPhi, phaseInit, hr, hsmall, agentPhiAboveQ, phiBiasWeightQ]
  · have hlist : (List.range 11).filter
        (fun k => decide (2 < k) && decide (k ≤ 3)) = [3] := by decide
    simp [enterThree, htwo, runInitsBetween, hlist, initializeAtPhaseThree]

theorem enterThree_phi_eq
    (h : ℕ) (hh : 1 ≤ h) (a : AgentState L 256)
    (hp : 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    augmentedAgentPhi h (enterThree a) =
      if a.phase.val < 3 then (1 / 2 : ℚ) * augmentedAgentPhi h a
      else augmentedAgentPhi h a := by
  by_cases hthree : a.phase.val = 3
  · have hpa : a.phase = ⟨3, by decide⟩ := Fin.ext hthree
    have heq : enterThree a = a := by
      unfold enterThree
      rw [hthree, runInitsBetween_self]
      cases a
      simp_all
    simp [heq, hthree]
  · have hsafe' : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
      omega
    have hpending : a.phase.val < 3 := by omega
    rw [enterThree_phi_eq_initialize h a ⟨hp.1, by omega⟩ hsafe,
      initialize_augmentedPhi_eq_half h hh a hpending hsafe' hcarrier,
      if_pos hpending]

theorem enterThree_phi_le
    (h : ℕ) (hh : 1 ≤ h) (a : AgentState L 256)
    (hp : 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    augmentedAgentPhi h (enterThree a) ≤ augmentedAgentPhi h a := by
  rw [enterThree_phi_eq h hh a hp hsafe hcarrier]
  have hn := augmentedAgentPhi_nonneg h a
  split_ifs <;> linarith

theorem epidemic_three_phi_eq
    (h : ℕ) (hh : 1 ≤ h) (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hmax : max s.phase.val t.phase.val = 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3) :
    augmentedAgentPhi h (phaseEpidemicUpdate L 256 s t).1 =
        (if s.phase.val < 3 then (1 / 2 : ℚ) * augmentedAgentPhi h s
          else augmentedAgentPhi h s) ∧
      augmentedAgentPhi h (phaseEpidemicUpdate L 256 s t).2 =
        (if t.phase.val < 3 then (1 / 2 : ℚ) * augmentedAgentPhi h t
          else augmentedAgentPhi h t) := by
  have hmaxFin : max s.phase t.phase = ⟨3, by decide⟩ := Fin.ext hmax
  let a := enterThree s
  let b := enterThree t
  have ha := enterThree_phi_eq h hh s hs hssafe hscarrier
  have hb := enterThree_phi_eq h hh t ht htsafe htcarrier
  have haf := enter_three_fields s hs
  have hbf := enter_three_fields t ht
  have hage : 3 ≤ a.phase.val := by
    show 3 ≤ (enterThree s).phase.val
    rcases haf.2.1 with hp | hp <;> omega
  have hbge : 3 ≤ b.phase.val := by
    show 3 ≤ (enterThree t).phase.val
    rcases hbf.2.1 with hp | hp <;> omega
  have hma : augmentedAgentPhi h (phase10EpidemicEntry L 256 s a) =
      augmentedAgentPhi h a := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) s a (by omega)
    simp only [augmentedAgentPhi, if_neg (show ¬ a.phase.val < 3 by omega),
      hp, show ¬ (10 : ℕ) < 3 by omega, if_false,
      agentPhiAboveQ, phase10EpidemicEntry_bias]
  have hmb : augmentedAgentPhi h (phase10EpidemicEntry L 256 t b) =
      augmentedAgentPhi h b := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) t b (by omega)
    simp only [augmentedAgentPhi, if_neg (show ¬ b.phase.val < 3 by omega),
      hp, show ¬ (10 : ℕ) < 3 by omega, if_false,
      agentPhiAboveQ, phase10EpidemicEntry_bias]
  have hepi : phaseEpidemicUpdate L 256 s t =
      if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (a.phase.val = 10 ∨ b.phase.val = 10) then
        (phase10EpidemicEntry L 256 s a, phase10EpidemicEntry L 256 t b)
      else (a, b) := by
    unfold phaseEpidemicUpdate
    rw [hmaxFin]
    rfl
  rw [hepi]
  by_cases hc : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (a.phase.val = 10 ∨ b.phase.val = 10)
  · rw [if_pos hc]
    exact ⟨hma.trans ha, hmb.trans hb⟩
  · rw [if_neg hc]
    exact ⟨ha, hb⟩

theorem epidemic_three_phi_le
    (h : ℕ) (hh : 1 ≤ h) (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hmax : max s.phase.val t.phase.val = 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3) :
    augmentedAgentPhi h (phaseEpidemicUpdate L 256 s t).1 ≤ augmentedAgentPhi h s ∧
      augmentedAgentPhi h (phaseEpidemicUpdate L 256 s t).2 ≤ augmentedAgentPhi h t := by
  have he := epidemic_three_phi_eq h hh s t hs ht hmax
    hssafe htsafe hscarrier htcarrier
  rw [he.1, he.2]
  constructor
  · have hn := augmentedAgentPhi_nonneg h s
    split_ifs <;> linarith
  · have hn := augmentedAgentPhi_nonneg h t
    split_ifs <;> linarith

theorem phase_one_phi_pair_le
    (h : ℕ) (s t : AgentState L 256)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      augmentedAgentPhi h s + augmentedAgentPhi h t := by
  have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hs ht
  have hel : (phaseEpidemicUpdate L 256 s t).1.phase.val < 2 := by
    simpa only [hepi] using (show s.phase.val < 2 from by omega)
  have hlcap := Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (L := L) (K := 256) s t hel hlno
  have hrcap := Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (L := L) (K := 256) s t hel hrno
  have hl : (Transition L 256 s t).1.phase.val < 3 := by omega
  have hr : (Transition L 256 s t).2.phase.val < 3 := by omega
  have hm := PhaseTwoSparse.phase_one_absolute_mass s t hs ht hlno hrno
  have hscaled := mul_le_mul_of_nonneg_left hm
    (show (0 : ℚ) ≤ 2 * (4 : ℚ) ^ (h - 1) by positivity)
  simpa [augmentedAgentPhi, pendingPotentialWeight, prePhase4Mass,
    hs, ht, hl, hr, mul_add] using hscaled


/-- After a successful epidemic update to phase three, the one selected
dispatch can only reduce the sum of the already initialized contributions. -/
theorem transition_phi_le_epidemic
    (h : ℕ) (s t : AgentState L 256)
    (hel : (phaseEpidemicUpdate L 256 s t).1.phase.val = 3)
    (her : (phaseEpidemicUpdate L 256 s t).2.phase.val = 3) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      augmentedAgentPhi h (phaseEpidemicUpdate L 256 s t).1 +
        augmentedAgentPhi h (phaseEpidemicUpdate L 256 s t).2 := by
  rcases he : phaseEpidemicUpdate L 256 s t with ⟨a, b⟩
  have ha : a.phase.val = 3 := by simpa only [he] using hel
  have hb : b.phase.val = 3 := by simpa only [he] using her
  have hpa : a.phase = ⟨3, by decide⟩ := Fin.ext ha
  have hactual : Transition L 256 s t =
      (finishPhase10Entry L 256 a (Phase3Transition L 256 a b).1,
       finishPhase10Entry L 256 b (Phase3Transition L 256 a b).2) := by
    unfold Transition
    rw [he]
    simp only [hpa]
  have hmono :
      a.phase.val ≤ (Phase3Transition L 256 a b).1.phase.val ∧
        b.phase.val ≤ (Phase3Transition L 256 a b).2.phase.val :=
    Phase3Transition_phase_nondec L 256 a b
  have hnl : ¬ (Phase3Transition L 256 a b).1.phase.val < 3 := by omega
  have hnr : ¬ (Phase3Transition L 256 a b).2.phase.val < 3 := by omega
  have hdispatch := phaseThree_augmentedPhi_pair_le h a b ha hb
  rw [hactual]
  simpa only [he, augmentedAgentPhi, finishPhase10Entry_phase_val,
    if_neg hnl, if_neg hnr, agentPhiAboveQ, finishPhase10Entry_bias]
    using hdispatch

/-- The actual wrapper has one phase dispatch after its epidemic initializer.
This proof retains that order for each of the three possible dispatch phases. -/
theorem transition_phi_pair_le
    (h : ℕ) (hh : 1 ≤ h) (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3)
    (hlcap : (Transition L 256 s t).1.phase.val ≤ 3)
    (hrcap : (Transition L 256 s t).2.phase.val ≤ 3) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      augmentedAgentPhi h s + augmentedAgentPhi h t := by
  have hlno : (Transition L 256 s t).1.phase.val ≠ 10 := by omega
  have hrno : (Transition L 256 s t).2.phase.val ≠ 10 := by omega
  by_cases hones : s.phase.val = 1 ∧ t.phase.val = 1
  · exact phase_one_phi_pair_le h s t hones.1 hones.2 hlno hrno
  by_cases hmax : max s.phase.val t.phase.val ≤ 2
  · have hslo : s.phase.val ≤ 2 := (le_max_left _ _).trans hmax
    have htlo : t.phase.val ≤ 2 := (le_max_right _ _).trans hmax
    have hmaxeq : max s.phase.val t.phase.val = 2 := by omega
    have hge := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := 256) s t
    have hdispatch : 2 ≤ (phaseEpidemicUpdate L 256 s t).1.phase.val := by omega
    have hleft : (Transition L 256 s t).1.smallBias = s.smallBias :=
      (Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
        (L := L) (K := 256) s t hdispatch).trans
          (phaseEpidemicUpdate_preserves_smallBias L 256 s t).1
    have hright : (Transition L 256 s t).2.smallBias = t.smallBias :=
      (Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
        (L := L) (K := 256) s t hdispatch).trans
          (phaseEpidemicUpdate_preserves_smallBias L 256 s t).2
    have hroles := PhaseTwoSeedProfile.mixed_transition_roles s t
      ⟨hs.1, hslo⟩ ⟨ht.1, htlo⟩ hlcap hrcap
    have hfreshLeft : (Transition L 256 s t).1.phase.val = 3 →
        Phase3Pre3.Phase3EntryAgent (Transition L 256 s t).1 := by
      intro hp
      exact (first_phase_three_pair s t hslo htlo hlno hrno (Or.inl (by omega))).1.1
    have hfreshRight : (Transition L 256 s t).2.phase.val = 3 →
        Phase3Pre3.Phase3EntryAgent (Transition L 256 s t).2 := by
      intro hp
      exact (first_phase_three_pair s t hslo htlo hlno hrno (Or.inr (by omega))).2.1
    exact add_le_add
      (pending_phi_le h hh s _ hslo hlcap hroles.1 hleft hssafe hscarrier hfreshLeft)
      (pending_phi_le h hh t _ htlo hrcap hroles.2 hright htsafe htcarrier hfreshRight)
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by omega
    have hphase := epidemic_three_phases_of_success s t hs ht hmaxeq hlno hrno
    have hphi := epidemic_three_phi_le h hh s t hs ht hmaxeq
      hssafe htsafe hscarrier htcarrier
    exact (transition_phi_le_epidemic h s t hphase.1 hphase.2).trans
      (add_le_add hphi.1 hphi.2)

/-- An actual pending/active interaction pays at least half the pending
contribution before any additional selected Phase-3 cancellation or split. -/
theorem transition_pending_left_half_loss
    (h : ℕ) (hh : 1 ≤ h) (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val < 3)
    (ht : t.phase.val = 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3)
    (hlcap : (Transition L 256 s t).1.phase.val ≤ 3)
    (hrcap : (Transition L 256 s t).2.phase.val ≤ 3) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      (1 / 2 : ℚ) * augmentedAgentPhi h s + augmentedAgentPhi h t := by
  have hsr : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3 := ⟨hs.1, by omega⟩
  have htr : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3 := by omega
  have hmax : max s.phase.val t.phase.val = 3 := by omega
  have hep := epidemic_three_phases_of_success s t hsr htr hmax (by omega) (by omega)
  have heq := epidemic_three_phi_eq h hh s t hsr htr hmax
    hssafe htsafe hscarrier htcarrier
  have hlocal := transition_phi_le_epidemic h s t hep.1 hep.2
  simpa only [heq.1, heq.2, if_pos hs.2, ht,
    show ¬ (3 : ℕ) < 3 by omega, if_false] using hlocal

theorem transition_pending_right_half_loss
    (h : ℕ) (hh : 1 ≤ h) (s t : AgentState L 256)
    (hs : s.phase.val = 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val < 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3)
    (hlcap : (Transition L 256 s t).1.phase.val ≤ 3)
    (hrcap : (Transition L 256 s t).2.phase.val ≤ 3) :
    augmentedAgentPhi h (Transition L 256 s t).1 +
        augmentedAgentPhi h (Transition L 256 s t).2 ≤
      augmentedAgentPhi h s + (1 / 2 : ℚ) * augmentedAgentPhi h t := by
  have hsr : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3 := by omega
  have htr : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3 := ⟨ht.1, by omega⟩
  have hmax : max s.phase.val t.phase.val = 3 := by omega
  have hep := epidemic_three_phases_of_success s t hsr htr hmax (by omega) (by omega)
  have heq := epidemic_three_phi_eq h hh s t hsr htr hmax
    hssafe htsafe hscarrier htcarrier
  have hlocal := transition_phi_le_epidemic h s t hep.1 hep.2
  simpa only [heq.1, heq.2, if_pos ht.2, hs,
    show ¬ (3 : ℕ) < 3 by omega, if_false] using hlocal

theorem augmentedPhi_add_pair
    (h : ℕ) (c : Cfg L 256) (s t : AgentState L 256) :
    augmentedPhi h (c + {s, t}) =
      augmentedPhi h c + (augmentedAgentPhi h s + augmentedAgentPhi h t) := by
  simp [augmentedPhi, Multiset.map_add, Multiset.sum_add,
    add_assoc, add_left_comm]

theorem augmentedPhi_stepOrSelf
    (h : ℕ) (hh : 1 ≤ h) (c : Cfg L 256) (s t : AgentState L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hcap : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.phase.val ≤ 3) :
    augmentedPhi h (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      augmentedPhi h c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
        c - {s, t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hlmem : (Transition L 256 s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L 256) c s t := by rw [hstep]; simp
    have hrmem : (Transition L 256 s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L 256) c s t := by rw [hstep]; simp
    have hpair := transition_phi_pair_le h hh s t (hrange s hs) (hrange t ht)
      (hsafe s hs) (hsafe t ht) (hcarrier s hs) (hcarrier t ht)
      (hcap _ hlmem) (hcap _ hrmem)
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
    rw [hstep, augmentedPhi_add_pair]
    conv_rhs => rw [hsplit]
    rw [augmentedPhi_add_pair]
    exact add_le_add le_rfl hpair
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ] <;> exact le_rfl

theorem augmentedPhi_draw
    (h : ℕ) (hh : 1 ≤ h) (c : Cfg L 256) (d : Draw L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hcap : ∀ a ∈ applyDraw c d, a.phase.val ≤ 3) :
    augmentedPhi h (applyDraw c d) ≤ augmentedPhi h c := by
  cases d with
  | none => exact le_rfl
  | some p => exact augmentedPhi_stepOrSelf h hh c p.1.1 p.2.1 hrange hsafe hcarrier hcap

theorem trace_augmentedPhi_le
    (h : ℕ) (hh : 1 ≤ h)
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    augmentedPhi h (trace init ω t) ≤ augmentedPhi h (trace init ω s) := by
  revert hrange hsafe hcarrier
  induction t, hst using Nat.le_induction with
  | base =>
      intro _ _ _
      exact le_rfl
  | succ t hst ih =>
      intro hrange hsafe hcarrier
      have hprev := ih
        (fun u hsu hut => hrange u hsu (by omega))
        (fun u hsu hut => hsafe u hsu (by omega))
        (fun u hsu hut => hcarrier u hsu (by omega))
      have hnext : augmentedPhi h (trace init ω (t + 1)) ≤
          augmentedPhi h (trace init ω t) := by
        rw [TimeTheorem.trace_succ]
        apply augmentedPhi_draw h hh _ (ω (t + 1)) (hrange t hst (by omega))
          (hsafe t hst (by omega)) (hcarrier t hst (by omega))
        intro a ha
        have ha' : a ∈ trace init ω (t + 1) := by
          simpa only [TimeTheorem.trace_succ] using ha
        exact (hrange (t + 1) (by omega) le_rfl a ha').2
      exact hnext.trans hprev

end Ripple.PopulationProtocol.ExactMajority.AveragingMixedPotentialTransitions

end
