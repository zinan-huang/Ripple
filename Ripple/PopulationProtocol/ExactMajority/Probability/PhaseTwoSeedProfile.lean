import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoProvenance
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStopping
import Ripple.PopulationProtocol.ExactMajority.Analysis.DeterministicChain

/-!
# The existing SeedProfile at the genuine first Phase-3 hit

This file transports all role counts through the actual mixed Phase-1/2
prefix and constructs StageEventSpec.SeedProfile from the retained
PhaseOneReadyProfile. The first hit is the first occurrence of phase at
least three. The explicit absence of Phase 10 at that hit distinguishes a
successful Init-3 crossing from a backup crossing.

Signed mixed mass and initialized-agent safety use the pinned reachable
invariants. No fresh counter reserve is assumed at the drained endpoint.
-/

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoSeedProfile

open TimeTheorem PhaseTwoProvenance

variable {L K : ℕ}

theorem phase_two_advance_role (a : AgentState L K)
    (ha : a.phase.val = 2) :
    (advancePhaseWithInit L K a).role = a.role := by
  have hnext : (advancePhase L K a).phase.val = 3 := by
    simp [advancePhase, ha]
  unfold advancePhaseWithInit
  rw [phaseInit_role]
  simp [hnext]

theorem phase_two_pair_roles (s t : AgentState L K)
    (hs : s.phase.val = 2) (ht : t.phase.val = 2) :
    (Phase2Transition L K s t).1.role = s.role ∧
      (Phase2Transition L K s t).2.role = t.role := by
  unfold Phase2Transition
  dsimp only
  split_ifs
  · exact ⟨phase_two_advance_role _ hs, phase_two_advance_role _ ht⟩
  all_goals exact ⟨rfl, rfl⟩

theorem epidemic_mixed_roles (s t : AgentState L K)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 2)
    (hel : (phaseEpidemicUpdate L K s t).1.phase.val = 2)
    (her : (phaseEpidemicUpdate L K s t).2.phase.val = 2) :
    (phaseEpidemicUpdate L K s t).1.role = s.role ∧
      (phaseEpidemicUpdate L K s t).2.role = t.role := by
  by_cases hs_two : s.phase.val = 2
  · by_cases ht_two : t.phase.val = 2
    · rw [epidemic_eq_self_at_phase_two s t hs_two ht_two]
      exact ⟨rfl, rfl⟩
    · have ht_one : t.phase.val = 1 := by omega
      have hsafe := phaseEpidemicUpdate_right_smallBias_noerror_of_entered
        (L := L) (K := K) s t (by omega) her
      rw [(phaseEpidemicUpdate_preserves_smallBias L K s t).2] at hsafe
      rw [epidemic_two_one_safe s t hs_two ht_one hsafe]
      simp [phaseInit_role]
  · have hs_one : s.phase.val = 1 := by omega
    by_cases ht_two : t.phase.val = 2
    · have hsafe := phaseEpidemicUpdate_left_smallBias_noerror_of_entered
        (L := L) (K := K) s t (by omega) hel
      rw [(phaseEpidemicUpdate_preserves_smallBias L K s t).1] at hsafe
      rw [epidemic_one_two_safe s t hs_one ht_two hsafe]
      simp [phaseInit_role]
    · have ht_one : t.phase.val = 1 := by omega
      have hepi :=
        Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hs_one ht_one
      rw [hepi] at hel
      change s.phase.val = 2 at hel
      omega

/-- Both corresponding roles survive a mixed Phase-1/2 step whose outputs
remain below Phase 4. This includes the step creating the first Phase-3 pair. -/
theorem mixed_transition_roles (s t : AgentState L K)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 2)
    (hlcap : (Transition L K s t).1.phase.val ≤ 3)
    (hrcap : (Transition L K s t).2.phase.val ≤ 3) :
    (Transition L K s t).1.role = s.role ∧
      (Transition L K s t).2.role = t.role := by
  by_cases hones : s.phase.val = 1 ∧ t.phase.val = 1
  · exact PhaseOnlyWindows.Transition_role_phase1 s t hones.1 hones.2
  · have hmax : max s.phase.val t.phase.val = 2 := by omega
    have hbefore :=
      phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t
    have hleft := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
    have hright := phaseEpidemicUpdate_right_phase_ge_max (L := L) (K := K) s t
    have hel : (phaseEpidemicUpdate L K s t).1.phase.val = 2 := by
      rcases phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := K) s t hs.2 ht.2 with hlow | hten <;> omega
    have her : (phaseEpidemicUpdate L K s t).2.phase.val = 2 := by
      rcases phaseEpidemicUpdate_right_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := K) s t hs.2 ht.2 with hlow | hten <;> omega
    have hroles := epidemic_mixed_roles s t hs ht hel her
    rcases he : phaseEpidemicUpdate L K s t with ⟨a, b⟩
    have ha : a.phase.val = 2 := by simpa only [he] using hel
    have hb : b.phase.val = 2 := by simpa only [he] using her
    have hpa : a.phase = ⟨2, by decide⟩ := Fin.ext ha
    have har : a.role = s.role := by simpa only [he] using hroles.1
    have hbr : b.role = t.role := by simpa only [he] using hroles.2
    have hactual : Transition L K s t =
        (finishPhase10Entry L K a (Phase2Transition L K a b).1,
         finishPhase10Entry L K b (Phase2Transition L K a b).2) := by
      unfold Transition
      rw [he]
      simp only [hpa]
    rw [hactual]
    simpa only [finishPhase10Entry_role, har, hbr] using
      phase_two_pair_roles a b ha hb

theorem mixed_role_count_step (r : Role) (c : Cfg L K)
    (s t : AgentState L K)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (hout : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val ≤ 3) :
    (Protocol.stepOrSelf (NonuniformMajority L K) c s t).countP
        (fun a => a.role = r) =
      c.countP (fun a => a.role = r) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hlmem : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    have hrmem : (Transition L K s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hstep]
      simp
    have hroles := mixed_transition_roles s t (hpre s hs) (hpre t ht)
      (hout _ hlmem) (hout _ hrmem)
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ)]
    have hpair :
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)).countP (fun a => a.role = r) =
        ({s, t} : Multiset (AgentState L K)).countP (fun a => a.role = r) := by
      simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.countP_cons,
        Multiset.countP_zero, hroles.1, hroles.2]
    rw [hstep, Multiset.countP_add]
    conv_rhs => rw [hsplit]
    rw [Multiset.countP_add, hpair]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem mixed_role_count_draw (r : Role) (c : Cfg L K) (d : Draw L K)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (hout : ∀ a ∈ applyDraw c d, a.phase.val ≤ 3) :
    (applyDraw c d).countP (fun a => a.role = r) =
      c.countP (fun a => a.role = r) := by
  cases d with
  | none => rfl
  | some p => exact mixed_role_count_step r c p.1.1 p.2.1 hpre hout

theorem mixed_role_count_trace (r : Role)
    (init : Cfg L K) (ω : Ω L K) (u v : ℕ) (huv : u ≤ v)
    (hwindow : ∀ k, u ≤ k → k ≤ v → ∀ a ∈ trace init ω k,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hbefore : ∀ k, u ≤ k → k < v → ∀ a ∈ trace init ω k,
      a.phase.val ≤ 2) :
    (trace init ω v).countP (fun a => a.role = r) =
      (trace init ω u).countP (fun a => a.role = r) := by
  revert hwindow hbefore
  induction v, huv using Nat.le_induction with
  | base =>
      intro _ _
      rfl
  | succ v huv ih =>
      intro hwindow hbefore
      have hpre : ∀ a ∈ trace init ω v,
          1 ≤ a.phase.val ∧ a.phase.val ≤ 2 := by
        intro a ha
        exact ⟨(hwindow v huv (by omega) a ha).1,
          hbefore v huv (Nat.lt_succ_self v) a ha⟩
      have hout : ∀ a ∈ applyDraw (trace init ω v) (ω (v + 1)),
          a.phase.val ≤ 3 := by
        rw [← TraceDrain.trace_succ init ω v]
        intro a ha
        exact (hwindow (v + 1) (by omega) le_rfl a ha).2
      rw [TraceDrain.trace_succ,
        mixed_role_count_draw r (trace init ω v) (ω (v + 1)) hpre hout]
      exact ih (fun k hk hkv => hwindow k hk (by omega))
        (fun k hk hkv => hbefore k hk (by omega))

theorem first_pair_phase_range {n : ℕ} {c : Cfg L K}
    (h : FirstPhaseThreePair n c) :
    ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
  rcases h.2 with ⟨r, s, t, hc, hr, hs, ht⟩
  intro a ha
  rw [hc] at ha
  simp only [Multiset.mem_add, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at ha
  rcases ha with hold | rfl | rfl
  · have hp := hr a hold
    omega
  · have hp := hs.1.1
    omega
  · have hp := ht.1.1
    omega

theorem first_pair_fresh {n : ℕ} {c : Cfg L K}
    (h : FirstPhaseThreePair n c) (a : AgentState L K)
    (ha : a ∈ c) (hp : a.phase.val = 3) :
    FreshPhaseThree a := by
  rcases h.2 with ⟨r, s, t, hc, hr, hs, ht⟩
  rw [hc] at ha
  simp only [Multiset.mem_add, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at ha
  rcases ha with hold | rfl | rfl
  · have hcap := (hr a hold).2
    omega
  · exact hs
  · exact ht

/-- The threshold formulation also rules out a preceding backup hit. A backup
at the crossing itself is excluded explicitly by hno. -/
theorem first_pair_of_threshold_hit (n : ℕ)
    (init : Cfg L K) (ω : Ω L K) (u v : ℕ)
    (hcard : (trace init ω u).card = n)
    (hstart : ∀ a ∈ trace init ω u, a.phase.val = 1)
    (huv : u ≤ v)
    (hfirst : StageEventSpec.firstHit
      (fun c : Cfg L K => ∃ a ∈ c, 3 ≤ a.phase.val) (trace init ω) v)
    (hno : ∀ a ∈ trace init ω v, a.phase.val ≠ 10) :
    FirstPhaseThreePair n (trace init ω v) := by
  have hstrict : u < v := by
    by_contra h
    have heq : v = u := by omega
    subst v
    obtain ⟨a, ha, hge⟩ := hfirst.1
    have hp := hstart a ha
    omega
  cases v with
  | zero => omega
  | succ k =>
      have huk : u ≤ k := by omega
      have hreach := trace_reachable init ω (s := u) (t := k) huk
      have hcardpre : (trace init ω k).card = n :=
        (Protocol.reachable_card_eq hreach).trans hcard
      have hfloor := PhaseOneDrainStopping.phase_lower_reachable 1
        (trace init ω u) (trace init ω k) hreach
        (fun a ha => le_of_eq (hstart a ha).symm)
      have hpre : ∀ a ∈ trace init ω k,
          1 ≤ a.phase.val ∧ a.phase.val ≤ 2 := by
        intro a ha
        have hlt : a.phase.val < 3 := Nat.lt_of_not_ge
          (fun hge => hfirst.2 k (Nat.lt_succ_self k) ⟨a, ha, hge⟩)
        exact ⟨hfloor a ha, by omega⟩
      have hnew : ∃ a ∈ trace init ω (k + 1), 3 ≤ a.phase.val := hfirst.1
      rw [TraceDrain.trace_succ] at hno hnew ⊢
      exact first_phase_three_draw n (trace init ω k) hcardpre hpre
        (ω (k + 1)) hno hnew

/-- This constructs the existing profile and retains every role count from
the actual drained endpoint, including Main, Clock and Reserve counts. -/
theorem seed_profile_and_counts_from_phase_one {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s t : ℕ)
    (hvalid : validInitial init)
    (hcard : (trace init ω s).card = n)
    (hstart : ∀ a ∈ trace init ω s, a.phase.val = 1)
    (hsplit : RoleSplitConcentration.RoleSplitGood (1 / 25 : ℝ) n (trace init ω s))
    (hst : s ≤ t)
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) t)
    (hno : ∀ a ∈ trace init ω t, a.phase.val ≠ 10) :
    StageEventSpec.SeedProfile n init (trace init ω t) ∧
      ∀ r : Role, (trace init ω t).countP (fun a => a.role = r) =
        (trace init ω s).countP (fun a => a.role = r) := by
  have hpair := first_pair_of_threshold_hit n init ω s t hcard
    hstart hst hfirst hno
  have hrange := first_pair_phase_range hpair
  have hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init ω t) := by
    simpa only [TraceDrain.trace_zero] using
      (trace_reachable init ω (s := 0) (t := t) (Nat.zero_le t))
  have hfloor (k : ℕ) (hsk : s ≤ k) :
      ∀ a ∈ trace init ω k, 1 ≤ a.phase.val :=
    PhaseOneDrainStopping.phase_lower_reachable 1
      (trace init ω s) (trace init ω k)
      (trace_reachable init ω hsk)
      (fun a ha => le_of_eq (hstart a ha).symm)
  have hwindow : ∀ k, s ≤ k → k ≤ t → ∀ a ∈ trace init ω k,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
    intro k hsk hkt a ha
    refine ⟨hfloor k hsk a ha, ?_⟩
    exact PhaseOneDrainStopping.phase_upper_reachable 3
      (trace init ω k) (trace init ω t) (trace_reachable init ω hkt)
      (fun b hb => (hrange b hb).2) a ha
  have hbefore : ∀ k, s ≤ k → k < t → ∀ a ∈ trace init ω k,
      a.phase.val ≤ 2 := by
    intro k hsk hkt a ha
    have hlt : a.phase.val < 3 := Nat.lt_of_not_ge
      (fun hge => hfirst.2 k hkt ⟨a, ha, hge⟩)
    omega
  have hcounts (r : Role) :
      (trace init ω t).countP (fun a => a.role = r) =
        (trace init ω s).countP (fun a => a.role = r) :=
    mixed_role_count_trace r init ω s t hst hwindow hbefore
  have hpartition := post_phase_zero_role_partition init (trace init ω t)
    hvalid hreach (fun a ha => (hrange a ha).1)
  have hroles : StageEventSpec.finalRoles (trace init ω t) := by
    intro a ha
    rcases hpartition a ha with hm | hr | hc | hten
    · exact Or.inl hm
    · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl hc)
    · exact (hno a ha hten).elim
  have hlefour : ∀ a ∈ trace init ω t, a.phase.val ≤ 4 := by
    intro a ha
    have hp := (hrange a ha).2
    omega
  refine ⟨?_, hcounts⟩
  refine
    { card_eq := hpair.1
      final_roles := hroles
      role_good := ?_
      phase_range := hrange
      exactly_two := first_phase_three_count n (trace init ω t) hpair
      fresh := fun a ha hp => (first_pair_fresh hpair a ha hp).1
      fresh_clock_counter := fun a ha hp hc =>
        (first_pair_fresh hpair a ha hp).2 hc
      already_initialized_safe := ?_
      nonmain_zero := ?_
      mass_eq := reachable_prePhase4MassSum_eq_initialGap_of_phase_le_four
        init (trace init ω t) hvalid hreach hlefour }
  · simpa only [RoleSplitConcentration.RoleSplitGood,
      RoleSplitConcentration.roleMCRCount, RoleSplitConcentration.mainCount,
      RoleSplitConcentration.clockCount, RoleSplitConcentration.reserveCount,
      hcounts] using hsplit
  · intro a ha hp
    have hsafe := reachable_phase_ge2_smallBias_noerror_of_phases_le_four
      init (trace init ω t) hvalid hreach hlefour a ha hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    change 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4
    rcases hsafe with hb | hb | hb <;> omega
  · intro a ha hmain
    have hzero := reachable_nonMain_smallBias_zero
      init (trace init ω t) hvalid hreach
    rcases hroles a ha with hm | hc | hr
    · exact (hmain hm).elim
    · exact hzero a ha (Or.inr hc)
    · exact hzero a ha (Or.inl hr)

theorem seed_profile_and_counts_of_first_hit {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s t : ℕ)
    (hready : PhaseOneDrainStopping.PhaseOneReadyProfile init (trace init ω s))
    (hst : s ≤ t)
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) t)
    (hno : ∀ a ∈ trace init ω t, a.phase.val ≠ 10) :
    StageEventSpec.SeedProfile n init (trace init ω t) ∧
      ∀ r : Role, (trace init ω t).countP (fun a => a.role = r) =
        (trace init ω s).countP (fun a => a.role = r) :=
  seed_profile_and_counts_from_phase_one init ω s t hready.valid_initial
    hready.card_eq hready.all_one hready.role_good hst hfirst hno

/-- The strong branch can start at the undrained Phase-1 entry profile. -/
theorem seed_profile_of_entry_profile {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s t : ℕ)
    (hentry : PhaseZeroEntry.PhaseOneEntryProfile init ω s)
    (hst : s ≤ t)
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) t)
    (hno : ∀ a ∈ trace init ω t, a.phase.val ≠ 10) :
    StageEventSpec.SeedProfile n init (trace init ω t) := by
  have hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init ω s) := by
    simpa only [TraceDrain.trace_zero] using
      (trace_reachable init ω (s := 0) (t := s) (Nat.zero_le s))
  have hcard : (trace init ω s).card = n :=
    (Protocol.reachable_card_eq hreach).trans hinput.2.2
  exact (seed_profile_and_counts_from_phase_one init ω s t hinput.2.1 hcard
    hentry.all_one hentry.role_good hst hfirst hno).1

theorem seed_profile_of_first_hit {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s t : ℕ)
    (hready : PhaseOneDrainStopping.PhaseOneReadyProfile init (trace init ω s))
    (hst : s ≤ t)
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) t)
    (hno : ∀ a ∈ trace init ω t, a.phase.val ≠ 10) :
    StageEventSpec.SeedProfile n init (trace init ω t) :=
  (seed_profile_and_counts_of_first_hit init ω s t hready hst hfirst hno).1

theorem first_phase_seed_of_profile {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (t : ℕ)
    (hfirst : StageEventSpec.firstHit (StageEventSpec.someGE (n := n) 3)
      (trace init ω) t)
    (hp : StageEventSpec.SeedProfile n init (trace init ω t)) :
    firstPhaseSeed init 3 t ω := by
  constructor
  · obtain ⟨a, ha, hge⟩ := hfirst.1
    exact ⟨a, ha, Nat.le_antisymm (hp.phase_range a ha).2 hge⟩
  · intro u hu a ha
    exact Nat.lt_of_not_ge (fun hge => hfirst.2 u hu ⟨a, ha, hge⟩)

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoSeedProfile
