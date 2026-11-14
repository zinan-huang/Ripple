-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingPendingCreditTransitions.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCreditCount
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMixedPotentialTransitions

/-!
# Protected credit through actual pending immigration

The initialized credit is extended by charging every pending minority small
bias. Phase-1 integer averaging increases this credit, safe Init-3 preserves
it, and the selected Phase-3 rule increases it. The real wrapper is retained:
epidemic initialization occurs before its one selected phase dispatch.

All pathwise uses keep the live mixed-phase gate. Probability arguments must
kill at its first failure; these deterministic statements do not condition on
a future success event.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingPendingCreditTransitions

open TimeTheorem AveragingMixedAlgebra AveragingMixedLedgers
open AveragingPendingCredit AveragingCreditTransitions AveragingCreditCount
open PhaseTwoActivationLocal PhaseTwoProvenance PhaseTwoSparse

variable {L : ℕ}

theorem fresh_mixed_credit_eq (σ : Sign) (ell k : ℕ) (hell : 0 < ell)
    (a : AgentState L 256) (hfresh : Phase3Pre3.Phase3EntryAgent a)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    mixedAgentCredit σ ell k a =
      -((2 : ℚ) ^ k) * minorityPart σ (smallValue a.smallBias) := by
  rw [mixedAgentCredit_eq_agentCredit σ ell k a (by have := hfresh.1; omega)]
  by_cases hm : a.role = .main
  · have hb := Phase3Pre3.main_bias_of_Phase3EntryAgent hfresh hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hv | hv | hv <;> cases σ <;>
      simp [agentCredit, hm, hb, Phase3Pre3.phase3BiasOfSmallBias, hv,
        biasCredit, signedCredit, protectedWeight, scaledWeight,
        smallValue, minorityPart, hell] <;> (try norm_num) <;> (try ring)
  · cases σ <;> simp [agentCredit, hm, smallValue, hcarrier hm, minorityPart]

theorem pending_credit_eq (σ : Sign) (ell k : ℕ) (hell : 0 < ell)
    (before after : AgentState L 256)
    (hb : before.phase.val ≤ 2) (ha : after.phase.val ≤ 3)
    (hrole : after.role = before.role) (hsmall : after.smallBias = before.smallBias)
    (hsafe : before.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : before.role ≠ .main → before.smallBias.val = 3)
    (hfresh : after.phase.val = 3 → Phase3Pre3.Phase3EntryAgent after) :
    mixedAgentCredit σ ell k after = mixedAgentCredit σ ell k before := by
  have hbp : before.phase.val < 3 := by omega
  by_cases hp : after.phase.val = 3
  · have hsa : after.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      simpa only [hsmall] using hsafe
    have hca : after.role ≠ .main → after.smallBias.val = 3 := by
      intro hm
      have hm' : before.role ≠ .main := by simpa only [hrole] using hm
      simpa only [hsmall] using hcarrier hm'
    rw [fresh_mixed_credit_eq σ ell k hell after (hfresh hp) hsa hca]
    simp only [mixedAgentCredit, if_pos hbp, hsmall]
  · have hap : after.phase.val < 3 := by omega
    simp only [mixedAgentCredit, if_pos hbp, if_pos hap, hsmall]

theorem enterThree_credit_eq_initialize (σ : Sign) (ell k : ℕ)
    (a : AgentState L 256) (hp : 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    mixedAgentCredit σ ell k (enterThree a) =
      mixedAgentCredit σ ell k (initializeAtPhaseThree a) := by
  have hcases : a.phase.val = 1 ∨ a.phase.val = 2 := by omega
  rcases hcases with hone | htwo
  · have hlist : (List.range 11).filter
        (fun k => decide (1 < k) && decide (k ≤ 3)) = [2, 3] := by decide
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hsmall | hsmall | hsmall <;> cases hr : a.role <;>
      simp [enterThree, hone, runInitsBetween, hlist, initializeAtPhaseThree,
        mixedAgentCredit, agentCredit, phaseInit, hr, hsmall]
  · have hlist : (List.range 11).filter
        (fun k => decide (2 < k) && decide (k ≤ 3)) = [3] := by decide
    simp [enterThree, htwo, runInitsBetween, hlist, initializeAtPhaseThree]

theorem enterThree_credit_eq (σ : Sign) (ell k : ℕ) (hell : 0 < ell)
    (a : AgentState L 256) (hp : 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3) :
    mixedAgentCredit σ ell k (enterThree a) = mixedAgentCredit σ ell k a := by
  by_cases hthree : a.phase.val = 3
  · have heq : enterThree a = a := by
      unfold enterThree
      rw [hthree, runInitsBetween_self]
      cases a
      simp_all
      exact Fin.ext (by simp [hthree])
    rw [heq]
  · have hsafe' : 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
      omega
    rw [enterThree_credit_eq_initialize σ ell k a ⟨hp.1, by omega⟩ hsafe]
    exact initializeAtPhaseThree_mixed_credit_eq σ ell k hell a
      (by omega) hcarrier hsafe'

theorem epidemic_three_credit_eq (σ : Sign) (ell k : ℕ) (hell : 0 < ell)
    (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hmax : max s.phase.val t.phase.val = 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3) :
    mixedAgentCredit σ ell k (phaseEpidemicUpdate L 256 s t).1 =
        mixedAgentCredit σ ell k s ∧
      mixedAgentCredit σ ell k (phaseEpidemicUpdate L 256 s t).2 =
        mixedAgentCredit σ ell k t := by
  have hmaxFin : max s.phase t.phase = ⟨3, by decide⟩ := Fin.ext hmax
  let a := enterThree s
  let b := enterThree t
  have ha : mixedAgentCredit σ ell k a = mixedAgentCredit σ ell k s :=
    enterThree_credit_eq σ ell k hell s hs hssafe hscarrier
  have hb : mixedAgentCredit σ ell k b = mixedAgentCredit σ ell k t :=
    enterThree_credit_eq σ ell k hell t ht htsafe htcarrier
  have haf := enter_three_fields s hs
  have hbf := enter_three_fields t ht
  have hage : 3 ≤ a.phase.val := by
    show 3 ≤ (enterThree s).phase.val
    rcases haf.2.1 with hp | hp <;> omega
  have hbge : 3 ≤ b.phase.val := by
    show 3 ≤ (enterThree t).phase.val
    rcases hbf.2.1 with hp | hp <;> omega
  have hma : mixedAgentCredit σ ell k (phase10EpidemicEntry L 256 s a) =
      mixedAgentCredit σ ell k a := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) s a (by omega)
    simp only [mixedAgentCredit, hp, show ¬ (10 : ℕ) < 3 by omega, if_false,
      if_neg (show ¬ a.phase.val < 3 by omega), agentCredit,
      phase10EpidemicEntry_role, phase10EpidemicEntry_bias]
  have hmb : mixedAgentCredit σ ell k (phase10EpidemicEntry L 256 t b) =
      mixedAgentCredit σ ell k b := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) t b (by omega)
    simp only [mixedAgentCredit, hp, show ¬ (10 : ℕ) < 3 by omega, if_false,
      if_neg (show ¬ b.phase.val < 3 by omega), agentCredit,
      phase10EpidemicEntry_role, phase10EpidemicEntry_bias]
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

theorem phase_one_credit_pair_mono (σ : Sign) (ell k : ℕ)
    (s t : AgentState L 256) (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    mixedAgentCredit σ ell k s + mixedAgentCredit σ ell k t ≤
      mixedAgentCredit σ ell k (Transition L 256 s t).1 +
        mixedAgentCredit σ ell k (Transition L 256 s t).2 := by
  have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hs ht
  have hel : (phaseEpidemicUpdate L 256 s t).1.phase.val < 2 := by
    simpa only [hepi] using (show s.phase.val < 2 by omega)
  have hlcap := Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (L := L) (K := 256) s t hel hlno
  have hrcap := Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (L := L) (K := 256) s t hel hrno
  have hsl : s.phase.val < 3 := by omega
  have htl : t.phase.val < 3 := by omega
  have hul : (Transition L 256 s t).1.phase.val < 3 := by omega
  have hur : (Transition L 256 s t).2.phase.val < 3 := by omega
  simp only [mixedAgentCredit, if_pos hsl, if_pos htl, if_pos hul, if_pos hur]
  by_cases hm : s.role = .main ∧ t.role = .main
  · have he := Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs ht hm.1 hm.2
    have hscaled := mul_le_mul_of_nonneg_left
      (avgFin7_minorityPart_le σ s.smallBias t.smallBias)
      (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ k)
    simp only [mul_add] at hscaled
    simp only [he]
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

theorem transition_credit_ge_epidemic (σ : Sign) (ell k : ℕ)
    (s t : AgentState L 256)
    (hel : (phaseEpidemicUpdate L 256 s t).1.phase.val = 3)
    (her : (phaseEpidemicUpdate L 256 s t).2.phase.val = 3) :
    mixedAgentCredit σ ell k (phaseEpidemicUpdate L 256 s t).1 +
        mixedAgentCredit σ ell k (phaseEpidemicUpdate L 256 s t).2 ≤
      mixedAgentCredit σ ell k (Transition L 256 s t).1 +
        mixedAgentCredit σ ell k (Transition L 256 s t).2 := by
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
  have hmono : a.phase.val ≤ (Phase3Transition L 256 a b).1.phase.val ∧
      b.phase.val ≤ (Phase3Transition L 256 a b).2.phase.val :=
    Phase3Transition_phase_nondec L 256 a b
  have hnl : ¬ (Phase3Transition L 256 a b).1.phase.val < 3 := by omega
  have hnr : ¬ (Phase3Transition L 256 a b).2.phase.val < 3 := by omega
  have hdispatch := Phase3Transition_credit_pair_mono σ ell k a b ha hb
  rw [hactual]
  simpa only [mixedAgentCredit, ha, hb, show ¬ (3 : ℕ) < 3 by omega,
    if_false, finishPhase10Entry_phase_val, if_neg hnl, if_neg hnr,
    agentCredit, finishPhase10Entry_role, finishPhase10Entry_bias] using hdispatch

/-- The complete actual dispatcher, including first-seed entry from Phase 2. -/
theorem transition_credit_pair_mono (σ : Sign) (ell k : ℕ) (hell : 0 < ell)
    (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hscarrier : s.role ≠ .main → s.smallBias.val = 3)
    (htcarrier : t.role ≠ .main → t.smallBias.val = 3)
    (hlcap : (Transition L 256 s t).1.phase.val ≤ 3)
    (hrcap : (Transition L 256 s t).2.phase.val ≤ 3) :
    mixedAgentCredit σ ell k s + mixedAgentCredit σ ell k t ≤
      mixedAgentCredit σ ell k (Transition L 256 s t).1 +
        mixedAgentCredit σ ell k (Transition L 256 s t).2 := by
  have hlno : (Transition L 256 s t).1.phase.val ≠ 10 := by omega
  have hrno : (Transition L 256 s t).2.phase.val ≠ 10 := by omega
  by_cases hones : s.phase.val = 1 ∧ t.phase.val = 1
  · exact phase_one_credit_pair_mono σ ell k s t hones.1 hones.2 hlno hrno
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
    rw [pending_credit_eq σ ell k hell s _ hslo hlcap hroles.1 hleft
        hssafe hscarrier hfreshLeft,
      pending_credit_eq σ ell k hell t _ htlo hrcap hroles.2 hright
        htsafe htcarrier hfreshRight]
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by omega
    have hphase := epidemic_three_phases_of_success s t hs ht hmaxeq hlno hrno
    have heq := epidemic_three_credit_eq σ ell k hell s t hs ht hmaxeq
      hssafe htsafe hscarrier htcarrier
    rw [← heq.1, ← heq.2]
    exact transition_credit_ge_epidemic σ ell k s t hphase.1 hphase.2

theorem mixedTotalCredit_add_pair (σ : Sign) (ell k : ℕ)
    (c : Cfg L 256) (s t : AgentState L 256) :
    mixedTotalCredit σ ell k (c + {s, t}) =
      mixedTotalCredit σ ell k c +
        (mixedAgentCredit σ ell k s + mixedAgentCredit σ ell k t) := by
  simp [mixedTotalCredit, Config.sumOf, Multiset.map_add, Multiset.sum_add,
    add_assoc, add_left_comm]

theorem mixedTotalCredit_stepOrSelf (σ : Sign) (ell k : ℕ) (hell : 0 < ell)
    (c : Cfg L 256) (s t : AgentState L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hcap : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.phase.val ≤ 3) :
    mixedTotalCredit σ ell k c ≤
      mixedTotalCredit σ ell k (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) := by
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
    have hpair := transition_credit_pair_mono σ ell k hell s t
      (hrange s hs) (hrange t ht) (hsafe s hs) (hsafe t ht)
      (hcarrier s hs) (hcarrier t ht) (hcap _ hlmem) (hcap _ hrmem)
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
    rw [hstep, mixedTotalCredit_add_pair]
    conv_lhs => rw [hsplit]
    rw [mixedTotalCredit_add_pair]
    exact add_le_add le_rfl hpair
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem mixedTotalCredit_draw (σ : Sign) (ell k : ℕ) (hell : 0 < ell)
    (c : Cfg L 256) (d : Draw L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hcap : ∀ a ∈ applyDraw c d, a.phase.val ≤ 3) :
    mixedTotalCredit σ ell k c ≤ mixedTotalCredit σ ell k (applyDraw c d) := by
  cases d with
  | none => exact le_rfl
  | some p =>
      exact mixedTotalCredit_stepOrSelf σ ell k hell c p.1.1 p.2.1
        hrange hsafe hcarrier hcap

theorem mixedTotalCredit_trace_mono (σ : Sign) (ell k : ℕ) (hell : 0 < ell)
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    mixedTotalCredit σ ell k (trace init ω s) ≤
      mixedTotalCredit σ ell k (trace init ω t) := by
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
      have hnext : mixedTotalCredit σ ell k (trace init ω t) ≤
          mixedTotalCredit σ ell k (trace init ω (t + 1)) := by
        rw [TimeTheorem.trace_succ]
        apply mixedTotalCredit_draw σ ell k hell _ (ω (t + 1))
          (hrange t hst (by omega)) (hsafe t hst (by omega))
          (hcarrier t hst (by omega))
        intro a ha
        have ha' : a ∈ trace init ω (t + 1) := by
          simpa only [TimeTheorem.trace_succ] using ha
        exact (hrange (t + 1) (by omega) le_rfl a ha').2
      exact hprev.trans hnext

/-- The initial terminal credit survives all subsequent pending immigration
through the live mixed window. The endpoint is not assumed fully active. -/
theorem terminal_credit_persists_through_pending
    (σ : Sign) (ell M : ℕ) (hell : 0 < ell)
    (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ) (hst : s ≤ t)
    (hM : RoleSplitConcentration.mainCount (trace init ω s) = M)
    (hY : AveragingTerminalDebt.debtY σ (ell + 2) (trace init ω s) ≤
      (7 / 200 : ℚ) * M)
    (hexception : (exceptionCount (ell + 2) (trace init ω s) : ℚ) ≤
      (3 / 1250 : ℚ) * M)
    (hphi : augmentedPhi ell (trace init ω s) ≤ (1 / 1000 : ℚ) * M)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hcarrier : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    (601 / 625 : ℚ) * M ≤
      mixedTotalCredit σ ell (ell + 2) (trace init ω t) := by
  exact (initial_mixed_credit_of_terminal_bounds σ ell M (trace init ω s)
      hM hY hexception hphi).trans
    (mixedTotalCredit_trace_mono σ ell (ell + 2) hell init ω s t hst
      hrange hsafe hcarrier)

end Ripple.PopulationProtocol.ExactMajority.AveragingPendingCreditTransitions

end
