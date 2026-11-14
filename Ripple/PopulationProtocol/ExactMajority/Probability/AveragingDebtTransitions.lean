-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingDebtTransitions.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingDebtAlgebra

/-!
# Actual mixed-phase debt transitions and Clock service

The dispatcher ordering is epidemic initialization, one selected phase rule,
then the backup wrapper. All monotonicity statements retain the successful
pre-exit output gate. Clock service is established for either selected
orientation, including pending immigration in the sampled interaction.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingDebtTransitions

open TimeTheorem P3DeterministicAlgebra AveragingMixedAlgebra AveragingMixedLedgers
open AveragingPendingCredit AveragingDebtAlgebra
open PhaseTwoActivationLocal PhaseTwoProvenance

variable {L : ℕ}

theorem active_agentDebt_le_of_fields (α β : ℚ) (h : ℕ)
    (s u : AgentState L 256) (hs : 3 ≤ s.phase.val) (hu : 3 ≤ u.phase.val)
    (hr : u.role = s.role) (hb : u.bias = s.bias)
    (hh : s.role = .main → s.bias = .zero → s.hour.val ≤ u.hour.val) :
    agentDebt α β h u ≤ agentDebt α β h s := by
  have hns : ¬ s.phase.val < 3 := by omega
  have hnu : ¬ u.phase.val < 3 := by omega
  have hz : lowHourZeroWeight h u ≤ lowHourZeroWeight h s := by
    by_cases hlow : u.role = .main ∧ ¬ u.phase.val < 3 ∧
        u.bias = .zero ∧ u.hour.val < h
    · have hsm : s.role = .main := hr.symm.trans hlow.1
      have hsb : s.bias = .zero := hb.symm.trans hlow.2.2.1
      have hsh : s.hour.val < h := (hh hsm hsb).trans_lt hlow.2.2.2
      simp [lowHourZeroWeight, hlow, hsm, hns, hsb, hsh]
    · have hz0 : lowHourZeroWeight h u = 0 := by
        unfold lowHourZeroWeight
        exact if_neg hlow
      rw [hz0]
      exact Nat.zero_le _
  have hzq : (lowHourZeroWeight h u : ℚ) ≤ (lowHourZeroWeight h s : ℚ) := by
    exact_mod_cast hz
  simpa [agentDebt, inactiveMainWeight, hns, hnu, prePhase4Mass, hb] using
    add_le_add hzq (le_refl (massBlend α β (Bias.toRat s.bias)))

theorem phaseThree_left_main_hour (s t : AgentState L 256)
    (hs : s.role = .main) (ht : t.role ≠ .main) :
    s.hour.val ≤ (Phase3Transition L 256 s t).1.hour.val := by
  by_cases hz : s.bias = .zero <;> by_cases hc : t.role = .clock <;>
    simp [Phase3Transition, hs, ht, hz, hc]

theorem phaseThree_right_main_hour (s t : AgentState L 256)
    (hs : s.role ≠ .main) (ht : t.role = .main) :
    t.hour.val ≤ (Phase3Transition L 256 s t).2.hour.val := by
  by_cases hz : t.bias = .zero <;> by_cases hc : s.role = .clock <;>
    simp [Phase3Transition, hs, ht, hz, hc]

theorem phaseThree_debt_pair_le (α β : ℚ) (h : ℕ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hpay : (2 : ℚ) ^ h ≤ α + β)
    (s t : AgentState L 256) (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    agentDebt α β h (Phase3Transition L 256 s t).1 +
        agentDebt α β h (Phase3Transition L 256 s t).2 ≤
      agentDebt α β h s + agentDebt α β h t := by
  by_cases hm : s.role = .main ∧ t.role = .main
  · have hr := Phase5To6FuelProducer.phase3CancelSplit_roles s t
    have hp := phase3CancelSplit_phase_preserved L 256 s t
    have hl := agentDebt_eq_active α β h (phase3CancelSplit L 256 s t).1
      (hr.1.trans hm.1) (by rw [hp.1, hs])
    have hh := agentDebt_eq_active α β h (phase3CancelSplit L 256 s t).2
      (hr.2.trans hm.2) (by rw [hp.2, ht])
    have hsl := agentDebt_eq_active α β h s hm.1 (by omega)
    have htl := agentDebt_eq_active α β h t hm.2 (by omega)
    have hc := activeDebt_cancelSplit_pair_le α β h hα hβ hpay s t
    rw [← hl, ← hh, ← hsl, ← htl] at hc
    simpa [Phase3Transition, hm.1, hm.2] using hc
  · have hr := Phase5To6FuelProducer.Phase3Transition_roles s t hs ht
    have hb := Phase5To6FuelProducer.Phase3Transition_biases_of_not_both_main s t hs ht hm
    have hp :
        s.phase.val ≤ (Phase3Transition L 256 s t).1.phase.val ∧
          t.phase.val ≤ (Phase3Transition L 256 s t).2.phase.val :=
      Phase3Transition_phase_nondec L 256 s t
    apply add_le_add
    · apply active_agentDebt_le_of_fields α β h s _ (by omega) (by omega) hr.1 hb.1
      intro hsm _
      exact phaseThree_left_main_hour s t hsm (fun htm => hm ⟨hsm, htm⟩)
    · apply active_agentDebt_le_of_fields α β h t _ (by omega) (by omega) hr.2 hb.2
      intro htm _
      exact phaseThree_right_main_hour s t (fun hsm => hm ⟨hsm, htm⟩) htm

theorem pending_debt_le (α β : ℚ) (h : ℕ) (before after : AgentState L 256)
    (hb : before.phase.val ≤ 2) (ha : after.phase.val ≤ 3)
    (hrole : after.role = before.role) (hsmall : after.smallBias = before.smallBias)
    (hsafe : before.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : before.role ≠ .main → before.smallBias.val = 3)
    (hfresh : after.phase.val = 3 → Phase3Pre3.Phase3EntryAgent after) :
    agentDebt α β h after ≤ agentDebt α β h before := by
  have hbp : before.phase.val < 3 := by omega
  rw [agentDebt_eq_pending α β h before hbp]
  by_cases hp : after.phase.val = 3
  · have hsa : after.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      simpa only [hsmall] using hsafe
    have hca : after.role ≠ .main → after.smallBias.val = 3 := by
      intro hm
      have hm' : before.role ≠ .main := by simpa only [hrole] using hm
      simpa only [hsmall] using hcarrier hm'
    simpa only [hrole, hsmall] using fresh_agentDebt_le_pending α β h after (hfresh hp) hsa hca
  · have hap : after.phase.val < 3 := by omega
    rw [agentDebt_eq_pending α β h after hap, hrole, hsmall]

theorem initialize_debt_le (α β : ℚ) (h : ℕ) (s : AgentState L 256)
    (hp : s.phase.val < 3)
    (hsafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : s.role ≠ .main → s.smallBias.val = 3) :
    agentDebt α β h (initializeAtPhaseThree s) ≤ agentDebt α β h s := by
  have hfresh : Phase3Pre3.Phase3EntryAgent (initializeAtPhaseThree s) := by
    cases hr : s.role <;>
      simp [Phase3Pre3.Phase3EntryAgent, Phase3Pre3.phase3BiasOfSmallBias,
        initializeAtPhaseThree, phaseInit, hr]
  have hsmall : (initializeAtPhaseThree s).smallBias = s.smallBias := by
    cases hr : s.role <;> simp [initializeAtPhaseThree, phaseInit, hr]
  have hs' : (initializeAtPhaseThree s).smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    simpa only [hsmall] using hsafe
  have hc' : (initializeAtPhaseThree s).role ≠ .main →
      (initializeAtPhaseThree s).smallBias.val = 3 := by
    intro hm
    rw [hsmall]
    exact hcarrier (by simpa only [initializeAtPhaseThree_role] using hm)
  rw [agentDebt_eq_pending α β h s hp]
  simpa only [initializeAtPhaseThree_role, hsmall] using
    fresh_agentDebt_le_pending α β h (initializeAtPhaseThree s) hfresh hs' hc'

theorem enterThree_debt_eq_initialize (α β : ℚ) (h : ℕ)
    (s : AgentState L 256) (hp : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (hsafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    agentDebt α β h (enterThree s) = agentDebt α β h (initializeAtPhaseThree s) := by
  have hcases : s.phase.val = 1 ∨ s.phase.val = 2 := by omega
  rcases hcases with hone | htwo
  · have hlist : (List.range 11).filter
        (fun k => decide (1 < k) && decide (k ≤ 3)) = [2, 3] := by decide
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hsmall | hsmall | hsmall <;> cases hr : s.role <;>
      simp [enterThree, hone, runInitsBetween, hlist, initializeAtPhaseThree,
        agentDebt, inactiveMainWeight, lowHourZeroWeight, prePhase4Mass,
        phaseInit, hr, hsmall]
  · have hlist : (List.range 11).filter
        (fun k => decide (2 < k) && decide (k ≤ 3)) = [3] := by decide
    simp [enterThree, htwo, runInitsBetween, hlist, initializeAtPhaseThree]

theorem enterThree_debt_le (α β : ℚ) (h : ℕ) (s : AgentState L 256)
    (hp : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (hsafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : s.role ≠ .main → s.smallBias.val = 3) :
    agentDebt α β h (enterThree s) ≤ agentDebt α β h s := by
  by_cases hthree : s.phase.val = 3
  · have heq : enterThree s = s := by
      unfold enterThree
      rw [hthree, runInitsBetween_self]
      cases s
      simp_all
      exact Fin.ext (by simp [hthree])
    rw [heq]
  · rw [enterThree_debt_eq_initialize α β h s ⟨hp.1, by omega⟩ hsafe]
    exact initialize_debt_le α β h s (by omega) hsafe hcarrier

theorem epidemic_three_debt_le (α β : ℚ) (h : ℕ) (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hmax : max s.phase.val t.phase.val = 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3) :
    agentDebt α β h (phaseEpidemicUpdate L 256 s t).1 ≤ agentDebt α β h s ∧
      agentDebt α β h (phaseEpidemicUpdate L 256 s t).2 ≤ agentDebt α β h t := by
  have hmaxFin : max s.phase t.phase = ⟨3, by decide⟩ := Fin.ext hmax
  let a := enterThree s
  let b := enterThree t
  have ha : agentDebt α β h a ≤ agentDebt α β h s :=
    enterThree_debt_le α β h s hs hssafe hscarrier
  have hb : agentDebt α β h b ≤ agentDebt α β h t :=
    enterThree_debt_le α β h t ht htsafe htcarrier
  have haf := enter_three_fields s hs
  have hbf := enter_three_fields t ht
  have hage : 3 ≤ a.phase.val := by
    show 3 ≤ (enterThree s).phase.val
    rcases haf.2.1 with hp | hp <;> omega
  have hbge : 3 ≤ b.phase.val := by
    show 3 ≤ (enterThree t).phase.val
    rcases hbf.2.1 with hp | hp <;> omega
  have hma : agentDebt α β h (phase10EpidemicEntry L 256 s a) = agentDebt α β h a := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) s a (by omega)
    simp [agentDebt, inactiveMainWeight, lowHourZeroWeight, prePhase4Mass,
      hp, show ¬ a.phase.val < 3 by omega]
  have hmb : agentDebt α β h (phase10EpidemicEntry L 256 t b) = agentDebt α β h b := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) t b (by omega)
    simp [agentDebt, inactiveMainWeight, lowHourZeroWeight, prePhase4Mass,
      hp, show ¬ b.phase.val < 3 by omega]
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
  · rw [if_pos hc, hma, hmb]
    exact ⟨ha, hb⟩
  · rw [if_neg hc]
    exact ⟨ha, hb⟩

theorem phase_one_debt_pair_le (α β : ℚ) (h : ℕ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (s t : AgentState L 256)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 ≤
      agentDebt α β h s + agentDebt α β h t := by
  have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hs ht
  have hel : (phaseEpidemicUpdate L 256 s t).1.phase.val < 2 := by
    simpa only [hepi] using (show s.phase.val < 2 by omega)
  have hlcap := Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (L := L) (K := 256) s t hel hlno
  have hrcap := Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (L := L) (K := 256) s t hel hrno
  have hroles := PhaseOnlyWindows.Transition_role_phase1 s t hs ht
  rw [agentDebt_eq_pending α β h _ (by omega : (Transition L 256 s t).1.phase.val < 3),
    agentDebt_eq_pending α β h _ (by omega : (Transition L 256 s t).2.phase.val < 3),
    agentDebt_eq_pending α β h s (by omega), agentDebt_eq_pending α β h t (by omega),
    hroles.1, hroles.2]
  by_cases hm : s.role = .main ∧ t.role = .main
  · have he := Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs ht hm.1 hm.2
    have hmass := massBlend_pair_le α β
      (PhaseTwoSparse.smallValue s.smallBias) (PhaseTwoSparse.smallValue t.smallBias)
      (PhaseTwoSparse.smallValue (avgFin7 s.smallBias t.smallBias).1)
      (PhaseTwoSparse.smallValue (avgFin7 s.smallBias t.smallBias).2)
      hα hβ (avgFin7_smallValue_sum s.smallBias t.smallBias)
      (PhaseTwoSparse.averaging_absolute_mass s.smallBias t.smallBias)
    simp only [he, hm.1, hm.2, if_true]
    linarith
  · have hpair := PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main s t hm
    have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs
    have hleft : (Transition L 256 s t).1.smallBias = s.smallBias := by
      unfold Transition
      rw [hepi]
      simp only [hsp]
      rw [finishPhase10Entry_smallBias, hpair, clockCounterStep_smallBias]
    have hright : (Transition L 256 s t).2.smallBias = t.smallBias := by
      unfold Transition
      rw [hepi]
      simp only [hsp]
      rw [finishPhase10Entry_smallBias, hpair, clockCounterStep_smallBias]
    rw [hleft, hright]

theorem transition_debt_le_epidemic (α β : ℚ) (h : ℕ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hpay : (2 : ℚ) ^ h ≤ α + β)
    (s t : AgentState L 256)
    (hel : (phaseEpidemicUpdate L 256 s t).1.phase.val = 3)
    (her : (phaseEpidemicUpdate L 256 s t).2.phase.val = 3) :
    agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 ≤
      agentDebt α β h (phaseEpidemicUpdate L 256 s t).1 +
        agentDebt α β h (phaseEpidemicUpdate L 256 s t).2 := by
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
  have hdispatch := phaseThree_debt_pair_le α β h hα hβ hpay a b ha hb
  rw [hactual]
  simpa only [he, agentDebt, inactiveMainWeight, lowHourZeroWeight, prePhase4Mass,
    finishPhase10Entry_phase_val, finishPhase10Entry_role,
    finishPhase10Entry_bias, finishPhase10Entry_smallBias, finishPhase10Entry_hour,
    AgentState.smallBiasInt]
      using hdispatch

theorem transition_debt_pair_le (α β : ℚ) (h : ℕ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hpay : (2 : ℚ) ^ h ≤ α + β)
    (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3)
    (hlcap : (Transition L 256 s t).1.phase.val ≤ 3)
    (hrcap : (Transition L 256 s t).2.phase.val ≤ 3) :
    agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 ≤
      agentDebt α β h s + agentDebt α β h t := by
  have hlno : (Transition L 256 s t).1.phase.val ≠ 10 := by omega
  have hrno : (Transition L 256 s t).2.phase.val ≠ 10 := by omega
  by_cases hones : s.phase.val = 1 ∧ t.phase.val = 1
  · exact phase_one_debt_pair_le α β h hα hβ s t hones.1 hones.2 hlno hrno
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
      (pending_debt_le α β h s _ hslo hlcap hroles.1 hleft hssafe hscarrier hfreshLeft)
      (pending_debt_le α β h t _ htlo hrcap hroles.2 hright htsafe htcarrier hfreshRight)
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by omega
    have hphase := epidemic_three_phases_of_success s t hs ht hmaxeq hlno hrno
    have hdebt := epidemic_three_debt_le α β h s t hs ht hmaxeq
      hssafe htsafe hscarrier htcarrier
    exact (transition_debt_le_epidemic α β h hα hβ hpay s t hphase.1 hphase.2).trans
      (add_le_add hdebt.1 hdebt.2)

theorem totalDebt_add_pair (α β : ℚ) (h : ℕ)
    (c : Cfg L 256) (s t : AgentState L 256) :
    totalDebt α β h (c + {s, t}) =
      totalDebt α β h c + (agentDebt α β h s + agentDebt α β h t) := by
  simp [totalDebt, Config.sumOf, Multiset.map_add, Multiset.sum_add,
    add_assoc, add_left_comm]

theorem totalDebt_stepOrSelf (α β : ℚ) (h : ℕ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hpay : (2 : ℚ) ^ h ≤ α + β)
    (c : Cfg L 256) (s t : AgentState L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hcap : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.phase.val ≤ 3) :
    totalDebt α β h (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      totalDebt α β h c := by
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
    have hpair := transition_debt_pair_le α β h hα hβ hpay s t
      (hrange s hs) (hrange t ht) (hsafe s hs) (hsafe t ht)
      (hcarrier s hs) (hcarrier t ht) (hcap _ hlmem) (hcap _ hrmem)
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
    rw [hstep, totalDebt_add_pair]
    conv_rhs => rw [hsplit]
    rw [totalDebt_add_pair]
    exact add_le_add le_rfl hpair
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem totalDebt_draw (α β : ℚ) (h : ℕ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hpay : (2 : ℚ) ^ h ≤ α + β)
    (c : Cfg L 256) (d : Draw L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hcap : ∀ a ∈ applyDraw c d, a.phase.val ≤ 3) :
    totalDebt α β h (applyDraw c d) ≤ totalDebt α β h c := by
  cases d with
  | none => exact le_rfl
  | some p =>
      exact totalDebt_stepOrSelf α β h hα hβ hpay c p.1.1 p.2.1
        hrange hsafe hcarrier hcap

theorem totalDebt_trace_le (α β : ℚ) (h : ℕ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hpay : (2 : ℚ) ^ h ≤ α + β)
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    totalDebt α β h (trace init ω t) ≤ totalDebt α β h (trace init ω s) := by
  revert hrange hsafe hcarrier
  induction t, hst using Nat.le_induction with
  | base => intro _ _ _; exact le_rfl
  | succ t hst ih =>
      intro hrange hsafe hcarrier
      have hprev := ih (fun u hsu hut => hrange u hsu (by omega))
        (fun u hsu hut => hsafe u hsu (by omega))
        (fun u hsu hut => hcarrier u hsu (by omega))
      have hnext : totalDebt α β h (trace init ω (t + 1)) ≤
          totalDebt α β h (trace init ω t) := by
        rw [TimeTheorem.trace_succ]
        apply totalDebt_draw α β h hα hβ hpay _ (ω (t + 1))
          (hrange t hst (by omega)) (hsafe t hst (by omega)) (hcarrier t hst (by omega))
        intro a ha
        have ha' : a ∈ trace init ω (t + 1) := by
          simpa only [TimeTheorem.trace_succ] using ha
        exact (hrange (t + 1) (by omega) le_rfl a ha').2
      exact hnext.trans hprev

end Ripple.PopulationProtocol.ExactMajority.AveragingDebtTransitions

end
