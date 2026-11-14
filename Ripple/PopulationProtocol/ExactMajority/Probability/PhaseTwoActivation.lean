import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoActivationLocal

/-!
# AdvancedProfile from an actual activation window

The only additional window field is an active-Clock minute ceiling. Inactive
Clock/Main fields are never used. The proof transports fresh Init-3 payloads,
all role counts and signed mixed mass on the original pair-log trace, and
assembles the existing AdvancedProfile and AsyncEntry structures.
-/

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoActivation

open TimeTheorem PhaseTwoProvenance PhaseTwoActivationLocal

variable {L : ℕ}

def ActivePayload (c : Cfg L 256) : Prop :=
  ∀ a ∈ c, a.phase.val = 3 → Payload (L / 16) a

def ActiveClockBelow (c : Cfg L 256) : Prop :=
  ∀ a ∈ c, a.phase.val = 3 → ClockBelow a

theorem payload_of_fresh (top : ℕ) (a : AgentState L 256)
    (h : FreshPhaseThree a) : Payload top a := by
  refine ⟨?_, ?_, ?_, h.2⟩
  · intro hm
    rw [Phase3Pre3.main_hour_zero_of_Phase3EntryAgent h.1 hm]
    exact Nat.zero_le top
  · intro hm sigma i hi
    rw [Phase3Pre3.main_bias_of_Phase3EntryAgent h.1 hm] at hi
    unfold Phase3Pre3.phase3BiasOfSmallBias at hi
    split_ifs at hi
    · injection hi with hsign hindex
      have hi_zero : i.val = 0 := by rw [← hindex]
      omega
    · injection hi with hsign hindex
      have hi_zero : i.val = 0 := by rw [← hindex]
      omega
  · exact Phase3Pre3.nonMain_bias_zero_of_Phase3EntryAgent h.1

theorem mixed_pair_payload (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hsp : s.phase.val = 3 → Payload (L / 16) s)
    (htp : t.phase.val = 3 → Payload (L / 16) t)
    (hsl : s.phase.val = 3 → ClockBelow s)
    (htl : t.phase.val = 3 → ClockBelow t)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    ((Transition L 256 s t).1.phase.val = 3 →
      Payload (L / 16) (Transition L 256 s t).1) ∧
    ((Transition L 256 s t).2.phase.val = 3 →
      Payload (L / 16) (Transition L 256 s t).2) := by
  by_cases hmax : max s.phase.val t.phase.val ≤ 2
  · have hslo : s.phase.val ≤ 2 := (le_max_left _ _).trans hmax
    have htlo : t.phase.val ≤ 2 := (le_max_right _ _).trans hmax
    constructor
    · intro hp
      exact payload_of_fresh _ _ (first_phase_three_pair s t hslo htlo hlno hrno
        (Or.inl (le_of_eq hp.symm))).1
    · intro hp
      exact payload_of_fresh _ _ (first_phase_three_pair s t hslo htlo hlno hrno
        (Or.inr (le_of_eq hp.symm))).2
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by omega
    have hdata := epidemic_three_data (L / 16) s t hs ht hmaxeq hsp htp
    have hphase := epidemic_three_phases_of_success s t hs ht hmaxeq hlno hrno
    have hla := init_data_clockBelow (L / 16) s _ hdata.1 hsl
    have hlb := init_data_clockBelow (L / 16) t _ hdata.2 htl
    have heq := transition_eq_phase_three s t hphase.1 hphase.2 hla hlb
    have hresult := phase_three_payload
      (phaseEpidemicUpdate L 256 s t).1 (phaseEpidemicUpdate L 256 s t).2
      hdata.1.2.2.1 hdata.2.2.2.1 hla hlb
    rw [heq]
    exact ⟨fun _ => hresult.1, fun _ => hresult.2⟩

theorem active_payload_step (c : Cfg L 256) (s t : AgentState L 256)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hp : ActivePayload c) (hlow : ActiveClockBelow c)
    (hno : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.phase.val ≠ 10) :
    ActivePayload (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) := by
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
    have hpair := mixed_pair_payload s t (hpre s hs) (hpre t ht)
      (hp s hs) (hp t ht) (hlow s hs) (hlow t ht)
      (hno _ hlmem) (hno _ hrmem)
    intro a ha hthree
    rcases AdvanceNoOvershoot.mem_stepOrSelf_cases c s t a happ ha with hold | rfl | rfl
    · exact hp a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold) hthree
    · exact hpair.1 hthree
    · exact hpair.2 hthree
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hp

theorem active_payload_draw (c : Cfg L 256) (d : Draw L 256)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hp : ActivePayload c) (hlow : ActiveClockBelow c)
    (hno : ∀ a ∈ applyDraw c d, a.phase.val ≠ 10) :
    ActivePayload (applyDraw c d) := by
  cases d with
  | none => exact hp
  | some p => exact active_payload_step c p.1.1 p.2.1 hpre hp hlow hno

theorem active_payload_trace (init : Cfg L 256) (ω : Ω L 256)
    (s t : ℕ) (hst : s ≤ t) (hstart : ActivePayload (trace init ω s))
    (hwindow : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hlow : ∀ u, s ≤ u → u < t → ActiveClockBelow (trace init ω u)) :
    ActivePayload (trace init ω t) := by
  revert hwindow hlow
  induction t, hst using Nat.le_induction with
  | base =>
      intro _ _
      exact hstart
  | succ t hst ih =>
      intro hwindow hlow
      have hprevious := ih (fun u hsu hut => hwindow u hsu (by omega))
        (fun u hsu hut => hlow u hsu (by omega))
      rw [TraceDrain.trace_succ]
      apply active_payload_draw _ (ω (t + 1))
        (hwindow t hst (by omega)) hprevious (hlow t hst (Nat.lt_succ_self t))
      intro a ha
      have ha' : a ∈ trace init ω (t + 1) := by
        simpa only [TraceDrain.trace_succ] using ha
      have hcap := (hwindow (t + 1) (by omega) le_rfl a ha').2
      omega

theorem activation_role_count_step (r : Role) (c : Cfg L 256)
    (s t : AgentState L 256)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hlow : ActiveClockBelow c)
    (hno : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.phase.val ≠ 10) :
    (Protocol.stepOrSelf (NonuniformMajority L 256) c s t).countP
        (fun a => a.role = r) = c.countP (fun a => a.role = r) := by
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
    have hroles := mixed_range_roles s t (hpre s hs) (hpre t ht)
      (hlow s hs) (hlow t ht) (hno _ hlmem) (hno _ hrmem)
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
    have hpair :
        ({(Transition L 256 s t).1, (Transition L 256 s t).2} :
          Multiset (AgentState L 256)).countP (fun a => a.role = r) =
        ({s, t} : Multiset (AgentState L 256)).countP (fun a => a.role = r) := by
      simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.countP_cons,
        Multiset.countP_zero, hroles.1, hroles.2.1]
    rw [hstep, Multiset.countP_add]
    conv_rhs => rw [hsplit]
    rw [Multiset.countP_add, hpair]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem activation_role_count_draw (r : Role) (c : Cfg L 256) (d : Draw L 256)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hlow : ActiveClockBelow c)
    (hno : ∀ a ∈ applyDraw c d, a.phase.val ≠ 10) :
    (applyDraw c d).countP (fun a => a.role = r) =
      c.countP (fun a => a.role = r) := by
  cases d with
  | none => rfl
  | some p => exact activation_role_count_step r c p.1.1 p.2.1 hpre hlow hno

theorem activation_role_count_trace (r : Role) (init : Cfg L 256) (ω : Ω L 256)
    (s t : ℕ) (hst : s ≤ t)
    (hwindow : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hlow : ∀ u, s ≤ u → u < t → ActiveClockBelow (trace init ω u)) :
    (trace init ω t).countP (fun a => a.role = r) =
      (trace init ω s).countP (fun a => a.role = r) := by
  revert hwindow hlow
  induction t, hst using Nat.le_induction with
  | base =>
      intro _ _
      rfl
  | succ t hst ih =>
      intro hwindow hlow
      have hno : ∀ a ∈ applyDraw (trace init ω t) (ω (t + 1)),
          a.phase.val ≠ 10 := by
        rw [← TraceDrain.trace_succ init ω t]
        intro a ha
        have hcap := (hwindow (t + 1) (by omega) le_rfl a ha).2
        omega
      rw [TraceDrain.trace_succ,
        activation_role_count_draw r _ _ (hwindow t hst (by omega))
          (hlow t hst (Nat.lt_succ_self t)) hno]
      exact ih (fun u hsu hut => hwindow u hsu (by omega))
        (fun u hsu hut => hlow u hsu (by omega))

theorem seed_active_payload {n : ℕ} (init c : InputCfg n)
    (hseed : StageEventSpec.SeedProfile n init c) : ActivePayload c := by
  intro a ha hp
  exact payload_of_fresh _ a
    ⟨hseed.fresh a ha hp, hseed.fresh_clock_counter a ha hp⟩

theorem trace_final_roles_of_range {n : ℕ} (init : InputCfg n)
    (hvalid : validInitial init) (ω : InputLog n) (t : ℕ)
    (hrange : ∀ a ∈ trace init ω t, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3) :
    StageEventSpec.finalRoles (trace init ω t) := by
  have hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init ω t) := by
    simpa only [TraceDrain.trace_zero] using
      (trace_reachable init ω (s := 0) (t := t) (Nat.zero_le t))
  have hroles := post_phase_zero_role_partition init (trace init ω t)
    hvalid hreach (fun a ha => (hrange a ha).1)
  intro a ha
  rcases hroles a ha with hm | hr | hc | hten
  · exact Or.inl hm
  · exact Or.inr (Or.inr hr)
  · exact Or.inr (Or.inl hc)
  · have hcap := (hrange a ha).2
    omega

theorem trace_mass_of_range {n : ℕ} (init : InputCfg n)
    (hvalid : validInitial init) (ω : InputLog n) (t : ℕ)
    (hrange : ∀ a ∈ trace init ω t, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3) :
    prePhase4MassSum (trace init ω t) = (initialGap init : ℚ) := by
  have hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init ω t) := by
    simpa only [TraceDrain.trace_zero] using
      (trace_reachable init ω (s := 0) (t := t) (Nat.zero_le t))
  exact reachable_prePhase4MassSum_eq_initialGap_of_phase_le_four
    init (trace init ω t) hvalid hreach (fun a ha => by
      have hcap := (hrange a ha).2
      omega)

/-- Complete deterministic endpoint readout. The active-Clock ceiling is the
only additional field beyond the successful phase window and activation. -/
theorem advanced_profile_of_window {n : ℕ}
    (init : InputCfg n) (hvalid : validInitial init) (ω : InputLog n) (s t : ℕ)
    (hst : s ≤ t) (hseed : StageEventSpec.SeedProfile n init (trace init ω s))
    (hwindow : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hheight : ∀ u, s ≤ u → u ≤ t → ActiveClockBelow (trace init ω u))
    (hall : StageEventSpec.allGE (n := n) 3 (trace init ω t)) :
    StageEventSpec.AdvancedProfile n init (trace init ω t) := by
  have hthree : ∀ a ∈ trace init ω t, a.phase.val = 3 :=
    fun a ha => Nat.le_antisymm (hwindow t hst le_rfl a ha).2 (hall a ha)
  have hpayload := active_payload_trace init ω s t hst
    (seed_active_payload init _ hseed) hwindow
    (fun u hsu hut => hheight u hsu hut.le)
  have hcounts (r : Role) :
      (trace init ω t).countP (fun a => a.role = r) =
        (trace init ω s).countP (fun a => a.role = r) :=
    activation_role_count_trace r init ω s t hst hwindow
      (fun u hsu hut => hheight u hsu hut.le)
  have hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init ω t) := by
    simpa only [TraceDrain.trace_zero] using
      (trace_reachable init ω (s := 0) (t := t) (Nat.zero_le t))
  have hroles := trace_final_roles_of_range init hvalid ω t (hwindow t hst le_rfl)
  have hlefour : ∀ a ∈ trace init ω t, a.phase.val ≤ 4 := by
    intro a ha
    rw [hthree a ha]
    decide
  refine
    { card_eq := (Protocol.reachable_card_eq (trace_reachable init ω hst)).trans
        hseed.card_eq
      final_roles := hroles
      role_good := ?_
      all_three := hthree
      safe_small := ?_
      nonmain_small := ?_
      nonmain_bias := fun a ha hm => (hpayload a ha (hthree a ha)).2.2.1 hm
      clock_counter := fun a ha hc => (hpayload a ha (hthree a ha)).2.2.2 hc
      clock_height := fun a ha hc => hheight t hst le_rfl a ha (hthree a ha) hc
      main_hour := fun a ha hm => (hpayload a ha (hthree a ha)).1 hm
      main_index := fun a ha hm => (hpayload a ha (hthree a ha)).2.1 hm
      mass_eq := trace_mass_of_range init hvalid ω t (hwindow t hst le_rfl) }
  · simpa only [RoleSplitConcentration.RoleSplitGood,
      RoleSplitConcentration.roleMCRCount, RoleSplitConcentration.mainCount,
      RoleSplitConcentration.clockCount, RoleSplitConcentration.reserveCount,
      hcounts] using hseed.role_good
  · intro a ha
    have hs := reachable_phase_ge2_smallBias_noerror_of_phases_le_four
      init (trace init ω t) hvalid hreach hlefour a ha
      (by rw [hthree a ha]; decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    change 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4
    rcases hs with hb | hb | hb <;> omega
  · intro a ha hm
    have hz := reachable_nonMain_smallBias_zero init (trace init ω t) hvalid hreach
    rcases hroles a ha with hmain | hc | hr
    · exact (hm hmain).elim
    · exact hz a ha (Or.inr hc)
    · exact hz a ha (Or.inl hr)

/-- Exact assembly of the existing actual-trace AsyncEntry. The first hits
and deadline remain the genuine ones supplied by the stopping-time producers. -/
theorem async_entry_of_window {n : ℕ}
    (init : InputCfg n) (hvalid : validInitial init) (ω : InputLog n) (s t : ℕ)
    (hseedFirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) s)
    (hallFirst : StageEventSpec.firstHit (StageEventSpec.allGE (n := n) 3)
      (trace init ω) t)
    (hst : s ≤ t) (hdeadline : t ≤ s + StageEventSpec.activationHorizon n)
    (hseed : StageEventSpec.SeedProfile n init (trace init ω s))
    (hwindow : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hheight : ∀ u, s ≤ u → u ≤ t → ActiveClockBelow (trace init ω u)) :
    StageEventSpec.AsyncEntry init ω s t := by
  have hcounts (r : Role) (u : ℕ) (hsu : s ≤ u) (hut : u ≤ t) :
      (trace init ω u).countP (fun a => a.role = r) =
        (trace init ω s).countP (fun a => a.role = r) :=
    activation_role_count_trace r init ω s u hsu
      (fun v hsv hvu => hwindow v hsv (hvu.trans hut))
      (fun v hsv hvu => hheight v hsv (hvu.le.trans hut))
  refine
    { seed_first := hseedFirst
      all_first := hallFirst
      order := hst
      deadline := hdeadline
      seed_profile := hseed
      advanced_profile := advanced_profile_of_window init hvalid ω s t hst hseed
        hwindow hheight hallFirst.1
      roles := fun u hsu hut => trace_final_roles_of_range init hvalid ω u
        (hwindow u hsu hut)
      phases := hwindow
      main_count := ?_
      clock_count := ?_
      reserve_count := ?_
      mixed_mass := fun u hsu hut => trace_mass_of_range init hvalid ω u
        (hwindow u hsu hut) }
  · intro u hsu hut
    simpa only [timeMainCount] using hcounts .main u hsu hut
  · intro u hsu hut
    simpa only [StageEventSpec.clockCount] using hcounts .clock u hsu hut
  · intro u hsu hut
    simpa only [StageEventSpec.reserveCount] using hcounts .reserve u hsu hut

/-- The successful low-clock domain closes under an actual draw. This avoids
postulating a phase window when the stochastic argument supplies only height
control and absence of backup. -/
theorem activation_range_step (c : Cfg L 256) (s t : AgentState L 256)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hlow : ActiveClockBelow c)
    (hno : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.phase.val ≠ 10) :
    ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
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
    have hpair := mixed_range_roles s t (hpre s hs) (hpre t ht)
      (hlow s hs) (hlow t ht) (hno _ hlmem) (hno _ hrmem)
    have hmono := Transition_phase_monotone (L := L) (K := 256) s t
    intro a ha
    rcases AdvanceNoOvershoot.mem_stepOrSelf_cases c s t a happ ha with hold | rfl | rfl
    · exact hpre a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
    · exact ⟨(hpre s hs).1.trans hmono.1, hpair.2.2.1⟩
    · exact ⟨(hpre t ht).1.trans hmono.2, hpair.2.2.2⟩
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hpre

theorem activation_range_draw (c : Cfg L 256) (d : Draw L 256)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hlow : ActiveClockBelow c)
    (hno : ∀ a ∈ applyDraw c d, a.phase.val ≠ 10) :
    ∀ a ∈ applyDraw c d, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
  cases d with
  | none => exact hpre
  | some p => exact activation_range_step c p.1.1 p.2.1 hpre hlow hno

theorem activation_range_trace (init : Cfg L 256) (ω : Ω L 256)
    (s t : ℕ) (hst : s ≤ t)
    (hstart : ∀ a ∈ trace init ω s, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hlow : ∀ u, s ≤ u → u < t → ActiveClockBelow (trace init ω u))
    (hno : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u, a.phase.val ≠ 10) :
    ∀ a ∈ trace init ω t, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
  revert hlow hno
  induction t, hst using Nat.le_induction with
  | base =>
      intro _ _
      exact hstart
  | succ t hst ih =>
      intro hlow hno
      have hprevious := ih (fun u hsu hut => hlow u hsu (by omega))
        (fun u hsu hut => hno u hsu (by omega))
      rw [TraceDrain.trace_succ]
      apply activation_range_draw _ (ω (t + 1)) hprevious
        (hlow t hst (Nat.lt_succ_self t))
      simpa only [TraceDrain.trace_succ] using hno (t + 1) (by omega) le_rfl

/-- Successful asynchronous entry needs only the active-Clock height window
and absence of backup, besides the genuine first-hit/deadline producers.
The intervening phase range is derived by the preceding domain induction. -/
theorem async_entry_of_low_clock_no_backup {n : ℕ}
    (init : InputCfg n) (hvalid : validInitial init) (ω : InputLog n) (s t : ℕ)
    (hseedFirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) s)
    (hallFirst : StageEventSpec.firstHit (StageEventSpec.allGE (n := n) 3)
      (trace init ω) t)
    (hst : s ≤ t) (hdeadline : t ≤ s + StageEventSpec.activationHorizon n)
    (hseed : StageEventSpec.SeedProfile n init (trace init ω s))
    (hheight : ∀ u, s ≤ u → u ≤ t → ActiveClockBelow (trace init ω u))
    (hno : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u, a.phase.val ≠ 10) :
    StageEventSpec.AsyncEntry init ω s t := by
  have hwindow : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
    intro u hsu hut
    exact activation_range_trace init ω s u hsu hseed.phase_range
      (fun v hsv hvu => hheight v hsv (hvu.le.trans hut))
      (fun v hsv hvu => hno v hsv (hvu.trans hut))
  exact async_entry_of_window init hvalid ω s t hseedFirst hallFirst hst hdeadline
    hseed hwindow hheight

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoActivation
