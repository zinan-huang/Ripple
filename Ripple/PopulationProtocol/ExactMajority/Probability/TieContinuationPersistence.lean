-- Ripple/PopulationProtocol/ExactMajority/Probability/TieContinuationPersistence.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTieReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase4StableEndpoint

/-!
# Protected terminal-index ties through the mixed Phase-3/4 boundary

The invariant includes the actual phase and output fields. It is closed under
the full transition, including Init 4, so the no-big-bias hypothesis never
requires a future phase-survival event.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.TieContinuationPersistence

open TimeTheorem StageEventSpec
  Phase4Convergence Phase5To6FuelProducer AveragingTieReadout

variable {L K n : ℕ}

/-- The phase/output portion of the protected mixed boundary. -/
def TiePhaseAgent (a : AgentState L K) : Prop :=
  InPhase34 a ∧ (a.phase.val = 4 → a.output = Output.T)

/-- Terminal dyadic indices, zero non-Main biases, and actual Init-4 output. -/
def ProtectedTieAgent (a : AgentState L K) : Prop :=
  TiePhaseAgent a ∧ noBigBias a ∧ NonmainZero a

def ProtectedTie (c : Cfg L K) : Prop :=
  ∀ a ∈ c, ProtectedTieAgent a

theorem tiePhaseAgent_of_phase_three (a : AgentState L K)
    (ha : a.phase.val = 3) : TiePhaseAgent a := by
  refine ⟨Or.inl ha, ?_⟩
  intro hfour
  omega

theorem counter_tiePhaseAgent (a : AgentState L K)
    (ha : a.phase.val = 3) :
    TiePhaseAgent (stdCounterSubroutine L K a) := by
  classical
  unfold stdCounterSubroutine
  split_ifs with hz
  · have hlt : a.phase.val < 10 := by omega
    simp only [advancePhaseWithInit, advancePhase, dif_pos hlt]
    simp [phaseInit, ha, TiePhaseAgent, InPhase34]
  · exact tiePhaseAgent_of_phase_three _ ha

/-- Rules 2--4 of Phase 3 preserve the phase/output of Rule 1. The only
new Phase-4 endpoint is the standard counter's Init-4 endpoint. -/
theorem phaseThree_tiePhase_pair (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    TiePhaseAgent (Phase3Transition L K s t).1 ∧
      TiePhaseAgent (Phase3Transition L K s t).2 := by
  classical
  let a : AgentState L K :=
    if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
      else if hmax : s.minute.val < K * (L + 1) then
        { s with minute := ⟨s.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K s
    else s
  let b : AgentState L K :=
    if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
      else if hmax : s.minute.val < K * (L + 1) then t
      else stdCounterSubroutine L K t
    else t
  have ha : TiePhaseAgent a := by
    dsimp only [a]
    split_ifs
    · exact tiePhaseAgent_of_phase_three _ hs
    · exact tiePhaseAgent_of_phase_three _ hs
    · exact counter_tiePhaseAgent s hs
    · exact tiePhaseAgent_of_phase_three _ hs
  have hb : TiePhaseAgent b := by
    dsimp only [b]
    split_ifs
    · exact tiePhaseAgent_of_phase_three _ ht
    · exact tiePhaseAgent_of_phase_three _ ht
    · exact counter_tiePhaseAgent t ht
    · exact tiePhaseAgent_of_phase_three _ ht
  have hleft := Phase3Transition_left_output_eq_rule1 (L := L) (K := K) s t a rfl
  have hright := Phase3Transition_right_output_eq_rule1 (L := L) (K := K) s t b rfl
  constructor
  · simpa only [TiePhaseAgent, InPhase34, hleft.1, hleft.2] using ha
  · simpa only [TiePhaseAgent, InPhase34, hright.1, hright.2] using hb

theorem transition_tiePhase_pair_of_three_three (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    TiePhaseAgent (Transition L K s t).1 ∧
      TiePhaseAgent (Transition L K s t).2 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hp := phaseThree_tiePhase_pair s t hs ht
  have hleft : (Phase3Transition L K s t).1.phase.val ≠ 10 := by
    rcases hp.1.1 with h | h <;> omega
  have hright : (Phase3Transition L K s t).2.phase.val ≠ 10 := by
    rcases hp.2.1 with h | h <;> omega
  unfold Transition
  rw [hepi]
  simpa only [hsp,
    finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) _ _ hleft,
    finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) _ _ hright] using hp

theorem transition_tiePhase_pair_of_three_four (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 4)
    (htout : t.output = Output.T) (hsb : noBigBias s) (htb : noBigBias t) :
    TiePhaseAgent (Transition L K s t).1 ∧
      TiePhaseAgent (Transition L K s t).2 := by
  let a : AgentState L K := phaseInit L K ⟨4, by decide⟩ { s with phase := ⟨4, by decide⟩ }
  let b : AgentState L K := { t with phase := ⟨4, by decide⟩ }
  have hepi : phaseEpidemicUpdate L K s t = (a, b) :=
    phaseEpidemicUpdate_eq_of_three_four s t hs ht
  have ha : a.phase = ⟨4, by decide⟩ := by simp [a, phaseInit]
  have hb : b.phase = ⟨4, by decide⟩ := rfl
  have hab : noBigBias a := by simpa [a, phaseInit, noBigBias] using hsb
  have hbb : noBigBias b := by simpa [b, noBigBias] using htb
  have hdispatch := Phase4Transition_eq_self_of_noBigBias a b hab hbb
  have htrans : Transition L K s t = (a, b) := by
    unfold Transition
    rw [hepi]
    simp only [ha]
    rw [hdispatch]
    simp only [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) a a
        (by simp only [ha]; decide),
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) b b
        (by simp only [hb]; decide)]
  rw [htrans]
  constructor
  · simp [TiePhaseAgent, InPhase34, a, phaseInit]
  · simp [TiePhaseAgent, InPhase34, b, htout]

theorem transition_tiePhase_pair_of_four_three (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 3)
    (hsout : s.output = Output.T) (hsb : noBigBias s) (htb : noBigBias t) :
    TiePhaseAgent (Transition L K s t).1 ∧
      TiePhaseAgent (Transition L K s t).2 := by
  let a : AgentState L K := { s with phase := ⟨4, by decide⟩ }
  let b : AgentState L K := phaseInit L K ⟨4, by decide⟩ { t with phase := ⟨4, by decide⟩ }
  have hepi : phaseEpidemicUpdate L K s t = (a, b) :=
    phaseEpidemicUpdate_eq_of_four_three s t hs ht
  have ha : a.phase = ⟨4, by decide⟩ := rfl
  have hb : b.phase = ⟨4, by decide⟩ := by simp [b, phaseInit]
  have hab : noBigBias a := by simpa [a, noBigBias] using hsb
  have hbb : noBigBias b := by simpa [b, phaseInit, noBigBias] using htb
  have hdispatch := Phase4Transition_eq_self_of_noBigBias a b hab hbb
  have htrans : Transition L K s t = (a, b) := by
    unfold Transition
    rw [hepi]
    simp only [ha]
    rw [hdispatch]
    simp only [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) a a
        (by simp only [ha]; decide),
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) b b
        (by simp only [hb]; decide)]
  rw [htrans]
  constructor
  · simp [TiePhaseAgent, InPhase34, a, hsout]
  · simp [TiePhaseAgent, InPhase34, b, phaseInit]

theorem transition_tiePhase_pair (s t : AgentState L K)
    (hs : TiePhaseAgent s) (ht : TiePhaseAgent t)
    (hsb : noBigBias s) (htb : noBigBias t) :
    TiePhaseAgent (Transition L K s t).1 ∧
      TiePhaseAgent (Transition L K s t).2 := by
  rcases hs.1 with hsphase | hsphase <;>
    rcases ht.1 with htphase | htphase
  · exact transition_tiePhase_pair_of_three_three s t hsphase htphase
  · exact transition_tiePhase_pair_of_three_four s t hsphase htphase
      (ht.2 htphase) hsb htb
  · exact transition_tiePhase_pair_of_four_three s t hsphase htphase
      (hs.2 hsphase) hsb htb
  · have h := Transition_preserves_tie_pair s t hsphase htphase
      (hs.2 hsphase) (ht.2 htphase) hsb htb
    exact ⟨⟨Or.inr h.1.1, fun _ => h.1.2.1⟩,
      ⟨Or.inr h.2.1, fun _ => h.2.2.1⟩⟩

theorem protectedTieAgent_transition_pair (s t : AgentState L K)
    (hs : ProtectedTieAgent s) (ht : ProtectedTieAgent t) :
    ProtectedTieAgent (Transition L K s t).1 ∧
      ProtectedTieAgent (Transition L K s t).2 := by
  have hp := transition_tiePhase_pair s t hs.1 ht.1 hs.2.1 ht.2.1
  have hb := Transition_noBigBias_pair s t hs.1.1 ht.1.1 hs.2.1 ht.2.1
  have hz := Transition_nonmainZero_pair s t hs.1.1 ht.1.1 hs.2.2 ht.2.2
  exact ⟨⟨hp.1, hb.1, hz.1⟩, ⟨hp.2, hb.2, hz.2⟩⟩

/-- A generic one-draw transport permits different input/output predicates. -/
theorem agent_property_applyDraw (P Q : AgentState L K → Prop)
    (hself : ∀ a, P a → Q a)
    (hpair : ∀ s t, P s → P t →
      Q (Transition L K s t).1 ∧ Q (Transition L K s t).2)
    (c : Cfg L K) (o : Draw L K) (hc : ∀ a ∈ c, P a) :
    ∀ a ∈ applyDraw c o, Q a := by
  classical
  cases o with
  | none => exact fun a ha => hself a (hc a ha)
  | some q =>
      change ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c q.1.1 q.2.1, Q a
      by_cases happ : Protocol.Applicable c q.1.1 q.2.1
      · have hs : q.1.1 ∈ c := Multiset.mem_of_le happ (by simp)
        have ht : q.2.1 ∈ c := Multiset.mem_of_le happ (by simp)
        have hp := hpair q.1.1 q.2.1 (hc q.1.1 hs) (hc q.2.1 ht)
        have heq : Protocol.stepOrSelf (NonuniformMajority L K) c q.1.1 q.2.1 =
            c - {q.1.1, q.2.1} +
              {(Transition L K q.1.1 q.2.1).1,
                (Transition L K q.1.1 q.2.1).2} := by
          unfold Protocol.stepOrSelf
          rw [if_pos happ]
          rfl
        rw [heq]
        intro a ha
        rcases Multiset.mem_add.mp ha with ha | ha
        · exact hself a (hc a (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha))
        · have hc : a = (Transition L K q.1.1 q.2.1).1 ∨
              a = (Transition L K q.1.1 q.2.1).2 := by simpa using ha
          rcases hc with rfl | rfl
          · exact hp.1
          · exact hp.2
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
        exact fun a ha => hself a (hc a ha)

theorem protectedTie_applyDraw (c : Cfg L K) (o : Draw L K)
    (hc : ProtectedTie c) : ProtectedTie (applyDraw c o) :=
  agent_property_applyDraw ProtectedTieAgent ProtectedTieAgent (fun _ h => h)
    protectedTieAgent_transition_pair c o hc

theorem protectedTie_trace (init : Cfg L K) (ω : Ω L K)
    {s t : ℕ} (hst : s ≤ t) (hs : ProtectedTie (trace init ω s)) :
    ProtectedTie (trace init ω t) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction r with
  | zero => simpa only [Nat.add_zero] using hs
  | succ r ih =>
      rw [show s + (r + 1) = s + r + 1 by omega, TimeTheorem.trace_succ]
      exact protectedTie_applyDraw _ _ ih

/-- Protected no-big-bias is exactly terminal-index confinement for every
remaining nonzero bias. -/
theorem protectedTie_index_eq_top {c : Cfg L K} (hc : ProtectedTie c)
    (a : AgentState L K) (ha : a ∈ c) (σ : Sign) (j : Fin (L + 1))
    (hb : a.bias = Bias.dyadic σ j) : j.val = L := by
  have hno := (hc a ha).2.1
  have hj := j.isLt
  simp only [noBigBias, hb] at hno
  omega

theorem protectedTie_stableTie_of_allGE (c : Cfg L K)
    (hc : ProtectedTie c) (hphase : ∀ a ∈ c, 4 ≤ a.phase.val) :
    StableTie4 c := by
  intro a ha
  have h := hc a ha
  have heq : a.phase.val = 4 := by
    rcases h.1.1 with hp | hp
    · have hge := hphase a ha
      omega
    · exact hp
  exact ⟨heq, h.1.2 heq, h.2.1⟩

theorem noBigBias_of_tieReadout (init c : InputCfg n)
    (h : tieReadout init c) :
    ∀ a ∈ c, noBigBias a := by
  intro a ha
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero => simp only [noBigBias, hb]
    | dyadic σ j =>
        have hj := h.2.2 a ha hm σ j hb
        simp only [noBigBias, hb]
        omega
  · simp only [noBigBias, h.2.1 a ha hm]

/-- The first Phase-4 seed is reached from a genuinely homogeneous
Phase-3 predecessor. Init 4 supplies every Phase-4 output in the snapshot. -/
theorem tiePhase_at_first_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w) :
    ∀ a ∈ trace init ω ρ, TiePhaseAgent a := by
  have hTρ := (AveragingEventInterface.clockHistory_seed_lt_exit h).2
  have hpred : ρ - 1 + 1 = ρ := by omega
  have hbefore : ∀ a ∈ trace init ω (ρ - 1), a.phase.val = 3 :=
    h.all_three (ρ - 1) (by omega) (by omega)
  have hstep : trace init ω ρ =
      applyDraw (trace init ω (ρ - 1)) (ω ρ) := by
    simpa only [hpred] using TimeTheorem.trace_succ init ω (ρ - 1)
  rw [hstep]
  exact agent_property_applyDraw (fun a => a.phase.val = 3) TiePhaseAgent
    tiePhaseAgent_of_phase_three transition_tiePhase_pair_of_three_three _ _ hbefore

theorem protectedTie_at_first_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w)
    (hr : tieReadout init (trace init ω ρ)) :
    ProtectedTie (trace init ω ρ) := by
  have hp := tiePhase_at_first_exit h
  have hb := noBigBias_of_tieReadout init _ hr
  exact fun a ha => ⟨hp a ha, hb a ha, hr.2.1 a ha⟩

theorem stableDone_of_tie_spread {init : InputCfg n} {ω : InputLog n}
    {S T ρ t : ℕ} {w : ClockTimes init}
    (hn : 2 ≤ n) (hvalid : validInitial init) (hcard : init.card = n)
    (h : ClockHistory init ω S T ρ w)
    (hr : tieReadout init (trace init ω ρ)) (hρt : ρ ≤ t)
    (hspread : ∀ a ∈ trace init ω t, 4 ≤ a.phase.val) :
    trace init ω t ∈ StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init := by
  have hp := protectedTie_trace init ω hρt (protectedTie_at_first_exit h hr)
  have hcap : n ≤ 2 ^ PhaseThreeModel.Numeric.hourIndex n := by
    simpa only [PhaseThreeModel.Numeric.hourIndex] using
      (Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) n)
  apply Phase4StableEndpoint.reachable_stableTie4_mem_stableDone
    hn hcap init _ hvalid hcard
  · simpa only [TimeTheorem.trace_zero] using
      TimeTheorem.trace_reachable init ω (s := 0) (t := t) (Nat.zero_le t)
  · exact protectedTie_stableTie_of_allGE _ hp hspread

end Ripple.PopulationProtocol.ExactMajority.TieContinuationPersistence

end
