import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2EntryDispatcher

/-!
# Mixed Phase-1/2 provenance and the first Phase-3 pair

Deterministic statements.

The source invariant counts opinion bits only on agents already in Phase 2.
It is transported along the actual draw trace up to the first higher phase.
The first-Phase-3 result allows untouched Phase-1 agents and records the
fresh counter of every entering Clock separately from Phase3EntryAgent.
-/

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoProvenance

variable {L K : ℕ}

def FreshPhaseThree (a : AgentState L K) : Prop :=
  Phase3Pre3.Phase3EntryAgent a ∧
    (a.role = .clock → a.counter.val = 50 * (L + 1))

def BiasSource (sigma : Sign) (a : AgentState L K) : Prop :=
  match sigma with
  | .pos => 3 < a.smallBias.val
  | .neg => a.smallBias.val < 3

def PhaseTwoSource (sigma : Sign) (a : AgentState L K) : Prop :=
  a.phase.val = 2 ∧ BiasSource sigma a

def MixedSignOrigin (c : Config (AgentState L K)) : Prop :=
  ∀ sigma a, a ∈ c → a.phase.val = 2 →
    Phase2AdvanceEpidemic.carries sigma a → ∃ b ∈ c, PhaseTwoSource sigma b

def PhaseTwoOpinion (a : AgentState L K) : Prop :=
  Phase2Convergence.singleSign a.opinions ∧ a.opinions.val ≠ 0

def MixedOpinionPayload (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 2 → PhaseTwoOpinion a

/-- A multiset decomposition records two entering occurrences, even when the
two resulting agent states happen to be equal. -/
def FirstPhaseThreePair (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∃ r s t,
    c = r + ({s, t} : Multiset (AgentState L K)) ∧
    (∀ a ∈ r, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2) ∧
    FreshPhaseThree s ∧ FreshPhaseThree t

theorem epidemic_eq_self_at_phase_two (s t : AgentState L K)
    (hs : s.phase.val = 2) (ht : t.phase.val = 2) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hs_eq : s.phase = ⟨2, by decide⟩ := Fin.ext hs
  have ht_eq : t.phase = ⟨2, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hs_eq, ht_eq, max_self]
  simp only [runInitsBetween_self]
  cases s
  cases t
  simp_all

theorem freshPhaseThree_advance (a : AgentState L K)
    (ha : a.phase.val = 2) :
    FreshPhaseThree (advancePhaseWithInit L K a) := by
  refine ⟨Phase2AdvanceEpidemic.Phase3EntryAgent_advancePhaseWithInit_of_phase2 a ha, ?_⟩
  have hp : a.phase = ⟨2, by decide⟩ := Fin.ext ha
  rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
    hour, minute, full, opinions, counter⟩
  simp only at hp
  subst phase
  cases role <;> simp [advancePhaseWithInit, advancePhase, phaseInit]

theorem transition_phase_two_fresh (s t : AgentState L K)
    (hs : s.phase.val = 2) (ht : t.phase.val = 2)
    (hm : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hp : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    FreshPhaseThree (Transition L K s t).1 ∧
      FreshPhaseThree (Transition L K s t).2 := by
  let u := opinionsUnion s.opinions t.opinions
  let left := advancePhaseWithInit L K {s with opinions := u}
  let right := advancePhaseWithInit L K {t with opinions := u}
  have hl : FreshPhaseThree left :=
    freshPhaseThree_advance {s with opinions := u} (by simpa using hs)
  have hr : FreshPhaseThree right :=
    freshPhaseThree_advance {t with opinions := u} (by simpa using ht)
  have hlocal : Phase2Transition L K s t = (left, right) := by
    simp [Phase2Transition, hm, hp, left, right, u]
  have hlne : left.phase.val ≠ 10 := by have := hl.1.1; omega
  have hrne : right.phase.val ≠ 10 := by have := hr.1.1; omega
  have hlf := finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) s left hlne
  have hrf := finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) t right hrne
  have hphase : s.phase = ⟨2, by decide⟩ := Fin.ext hs
  have hepi := epidemic_eq_self_at_phase_two s t hs ht
  have hactual : Transition L K s t = (left, right) := by
    unfold Transition
    rw [hepi]
    simp only [hphase]
    rw [hlocal]
    simp only [hlf, hrf]
  rw [hactual]
  exact ⟨hl, hr⟩

/-- The actual dispatcher creates its first Phase-3 pair only by running
Phase 2 after epidemic initialization. Pending Phase-1 values may be outside the safe range;
the no-backup hypotheses exclude unsuccessful initialization. -/
theorem first_phase_three_pair (s t : AgentState L K)
    (hs : s.phase.val ≤ 2) (ht : t.phase.val ≤ 2)
    (hlne : (Transition L K s t).1.phase.val ≠ 10)
    (hrne : (Transition L K s t).2.phase.val ≠ 10)
    (hnew : 3 ≤ (Transition L K s t).1.phase.val ∨
      3 ≤ (Transition L K s t).2.phase.val) :
    FreshPhaseThree (Transition L K s t).1 ∧
      FreshPhaseThree (Transition L K s t).2 := by
  have hmono := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t
  have helne : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 := by
    intro h
    have hstep := hmono.1
    have hbound := (Transition L K s t).1.phase.isLt
    omega
  have herne : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10 := by
    intro h
    have hstep := hmono.2
    have hbound := (Transition L K s t).2.phase.isLt
    omega
  have helle : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 2 :=
    (phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
      (L := L) (K := K) s t hs ht).resolve_right helne
  have heq := phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
    (L := L) (K := K) s t hs ht helne herne
  have helge : 2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
    by_contra h
    have hlt : (phaseEpidemicUpdate L K s t).1.phase.val < 2 := by omega
    have hl := Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
      (L := L) (K := K) s t hlt hlne
    have hr := Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
      (L := L) (K := K) s t hlt hrne
    omega
  have hel : (phaseEpidemicUpdate L K s t).1.phase.val = 2 := by omega
  have her : (phaseEpidemicUpdate L K s t).2.phase.val = 2 := by omega
  rcases he : phaseEpidemicUpdate L K s t with ⟨a, b⟩
  have ha : a.phase.val = 2 := by simpa only [he] using hel
  have hb : b.phase.val = 2 := by simpa only [he] using her
  have hfixed := epidemic_eq_self_at_phase_two a b ha hb
  have htrans : Transition L K s t = Transition L K a b := by
    unfold Transition
    rw [he, hfixed]
  have hnew' : 3 ≤ (Transition L K a b).1.phase.val ∨
      3 ≤ (Transition L K a b).2.phase.val := by
    simpa only [htrans] using hnew
  rcases Phase2AdvanceEpidemic.Transition_phase2_singleSign_or_advance a b ha hb with
    hstay | hconf
  · rcases hnew' with h | h <;> omega
  · rw [htrans]
    exact transition_phase_two_fresh a b ha hb hconf.1 hconf.2.1

theorem first_phase_three_step (n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (s t : AgentState L K)
    (hno : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val ≠ 10)
    (hnew : ∃ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      3 ≤ a.phase.val) :
    FirstPhaseThreePair n (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s,t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hlmem : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by rw [hstep]; simp
    have hrmem : (Transition L K s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by rw [hstep]; simp
    have hpairnew : 3 ≤ (Transition L K s t).1.phase.val ∨
        3 ≤ (Transition L K s t).2.phase.val := by
      rcases hnew with ⟨a, ha, hage⟩
      rcases AdvanceNoOvershoot.mem_stepOrSelf_cases c s t a happ ha with hold | rfl | rfl
      · have hphase := (hpre a
          (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)).2
        omega
      · exact Or.inl hage
      · exact Or.inr hage
    have hfresh := first_phase_three_pair s t (hpre s hs).2 (hpre t ht).2
      (hno _ hlmem) (hno _ hrmem) hpairnew
    refine ⟨?_, c - {s,t}, (Transition L K s t).1,
      (Transition L K s t).2, hstep, ?_, hfresh.1, hfresh.2⟩
    · rw [Protocol.stepOrSelf_card_eq]
      exact hcard
    · intro a ha
      exact hpre a (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ] at hnew
    rcases hnew with ⟨a, ha, hage⟩
    have := (hpre a ha).2
    omega

theorem first_phase_three_count (n : ℕ) (c : Config (AgentState L K))
    (h : FirstPhaseThreePair n c) :
    c.countP (fun a => a.phase.val = 3) = 2 := by
  classical
  rcases h.2 with ⟨r, s, t, hc, hr, hs, ht⟩
  have hz : r.countP (fun a => a.phase.val = 3) = 0 := by
    rw [Multiset.countP_eq_zero]
    intro a ha
    have := (hr a ha).2
    omega
  rw [hc, Multiset.countP_add, hz]
  simp [← Multiset.cons_zero, Multiset.countP_cons, hs.1.1, ht.1.1]

theorem first_phase_three_draw (n : ℕ) (c : TimeTheorem.Cfg L K)
    (hcard : c.card = n)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (d : TimeTheorem.Draw L K)
    (hno : ∀ a ∈ TimeTheorem.applyDraw c d, a.phase.val ≠ 10)
    (hnew : ∃ a ∈ TimeTheorem.applyDraw c d, 3 ≤ a.phase.val) :
    FirstPhaseThreePair n (TimeTheorem.applyDraw c d) := by
  cases d with
  | none =>
      rcases hnew with ⟨a, ha, hage⟩
      have := (hpre a ha).2
      omega
  | some p =>
      exact first_phase_three_step n c hcard hpre p.1.1 p.2.1 hno hnew

theorem first_phase_three_trace (n : ℕ) (init : TimeTheorem.Cfg L K)
    (ω : TimeTheorem.Ω L K) (t : ℕ)
    (hfirst : TimeTheorem.firstPhaseSeed init 3 t ω) (hpos : 0 < t)
    (hcard : (TimeTheorem.trace init ω (t - 1)).card = n)
    (hfloor : ∀ a ∈ TimeTheorem.trace init ω (t - 1), 1 ≤ a.phase.val)
    (hno : ∀ a ∈ TimeTheorem.trace init ω t, a.phase.val ≠ 10) :
    FirstPhaseThreePair n (TimeTheorem.trace init ω t) := by
  cases t with
  | zero => omega
  | succ k =>
      have hpre : ∀ a ∈ TimeTheorem.trace init ω k,
          1 ≤ a.phase.val ∧ a.phase.val ≤ 2 := by
        intro a ha
        have hlo := hfloor a ha
        have hhi := hfirst.2 k (Nat.lt_succ_self k) a ha
        exact ⟨hlo, by omega⟩
      have hnew : ∃ a ∈ TimeTheorem.trace init ω (k + 1), 3 ≤ a.phase.val := by
        rcases hfirst.1 with ⟨a, ha, hp⟩
        exact ⟨a, ha, by omega⟩
      rw [TraceDrain.trace_succ] at hno hnew ⊢
      exact first_phase_three_draw n (TimeTheorem.trace init ω k) hcard hpre
        (ω (k + 1)) hno hnew

theorem source_left_persists (sigma : Sign) (s t : AgentState L K)
    (hs : PhaseTwoSource sigma s)
    (hout : (Transition L K s t).1.phase.val ≤ 2) :
    PhaseTwoSource sigma (Transition L K s t).1 := by
  have hmono : s.phase.val ≤ (Transition L K s t).1.phase.val :=
    (Transition_phase_monotone (L := L) (K := K) s t).1
  have hsmall := Transition_left_preserves_smallBias_of_phase_ge_two
    (L := L) (K := K) s t (by have := hs.1; omega)
  refine ⟨by have := hs.1; omega, ?_⟩
  cases sigma <;> simpa only [BiasSource, hsmall] using hs.2

theorem source_right_persists (sigma : Sign) (s t : AgentState L K)
    (ht : PhaseTwoSource sigma t)
    (hout : (Transition L K s t).2.phase.val ≤ 2) :
    PhaseTwoSource sigma (Transition L K s t).2 := by
  have hmono : t.phase.val ≤ (Transition L K s t).2.phase.val :=
    (Transition_phase_monotone (L := L) (K := K) s t).2
  have hsmall := Transition_right_preserves_smallBias_of_phase_ge_two
    (L := L) (K := K) s t (by have := ht.1; omega)
  refine ⟨by have := ht.1; omega, ?_⟩
  cases sigma <;> simpa only [BiasSource, hsmall] using ht.2

theorem source_exists_step (sigma : Sign) (c : Config (AgentState L K))
    (s t : AgentState L K) (hsource : ∃ a ∈ c, PhaseTwoSource sigma a)
    (hout : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val ≤ 2) :
    ∃ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      PhaseTwoSource sigma a := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s,t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hsplit : c = c - {s,t} + ({s,t} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel
        (show ({s,t} : Multiset (AgentState L K)) ≤ c from happ)]
    have hlmem : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by rw [hstep]; simp
    have hrmem : (Transition L K s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by rw [hstep]; simp
    rcases hsource with ⟨a, ha, hsrc⟩
    rw [hsplit] at ha
    rcases Multiset.mem_add.mp ha with hrem | hsel
    · refine ⟨a, ?_, hsrc⟩
      rw [hstep]
      exact Multiset.mem_add.mpr (Or.inl hrem)
    · have hsel' : a = s ∨ a = t := by simpa using hsel
      rcases hsel' with h | h
      · rw [h] at hsrc
        exact ⟨_, hlmem, source_left_persists sigma s t hsrc (hout _ hlmem)⟩
      · rw [h] at hsrc
        exact ⟨_, hrmem, source_right_persists sigma s t hsrc (hout _ hrmem)⟩
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hsource

theorem init_two_bit_source (sigma : Sign) (a : AgentState L K)
    (hphase : (phaseInit L K ⟨2, by decide⟩ a).phase.val = 2)
    (hbit : Phase2AdvanceEpidemic.carries sigma (phaseInit L K ⟨2, by decide⟩ a)) :
    BiasSource sigma (phaseInit L K ⟨2, by decide⟩ a) := by
  rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
    hour, minute, full, opinions, counter⟩
  cases sigma <;> fin_cases smallBias <;>
    simp [BiasSource, Phase2AdvanceEpidemic.carries, phaseInit,
      enterPhase10, phase10, hasPlusOne, hasMinusOne] at hphase hbit ⊢

theorem union_bit_sources (sigma : Sign) (s t : AgentState L K)
    (hbit : Phase2AdvanceEpidemic.carries sigma
      {s with opinions := opinionsUnion s.opinions t.opinions}) :
    Phase2AdvanceEpidemic.carries sigma s ∨ Phase2AdvanceEpidemic.carries sigma t := by
  cases sigma with
  | pos =>
      have h : ∀ u v : Fin 8, hasPlusOne (opinionsUnion u v) = true →
          hasPlusOne u = true ∨ hasPlusOne v = true := by decide
      exact h s.opinions t.opinions hbit
  | neg =>
      have h : ∀ u v : Fin 8, hasMinusOne (opinionsUnion u v) = true →
          hasMinusOne u = true ∨ hasMinusOne v = true := by decide
      exact h s.opinions t.opinions hbit

theorem clock_step_phase_two_bit_source (sigma : Sign) (a : AgentState L K)
    (ha : a.phase.val = 1)
    (hphase : (clockCounterStep L K a).phase.val = 2)
    (hbit : Phase2AdvanceEpidemic.carries sigma (clockCounterStep L K a)) :
    BiasSource sigma (clockCounterStep L K a) := by
  by_cases hc : a.role = .clock
  · simp only [clockCounterStep, if_pos hc] at hphase hbit ⊢
    by_cases hz : a.counter.val = 0
    · simp only [stdCounterSubroutine, dif_pos hz, if_pos hz] at hphase hbit ⊢
      have hpa : (advancePhase L K a).phase = ⟨2, by decide⟩ := by
        apply Fin.ext
        simp [advancePhase, ha]
      unfold advancePhaseWithInit at hphase hbit ⊢
      dsimp only at hphase hbit ⊢
      rw [hpa] at hphase hbit ⊢
      exact init_two_bit_source sigma _ hphase hbit
    · simp [stdCounterSubroutine, hz, ha] at hphase
  · simp [clockCounterStep, hc, ha] at hphase

theorem phase_one_left_bit_source (sigma : Sign) (s t : AgentState L K)
    (hs : s.phase.val = 1)
    (hphase : (Phase1Transition L K s t).1.phase.val = 2)
    (hbit : Phase2AdvanceEpidemic.carries sigma (Phase1Transition L K s t).1) :
    BiasSource sigma (Phase1Transition L K s t).1 := by
  by_cases hm : s.role = .main ∧ t.role = .main
  · have hstay : (Phase1Transition L K s t).1.phase.val = 1 := by
      simp [Phase1Transition, hm, clockCounterStep, hm.1, hs]
    omega
  · have hpair := PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main s t hm
    rw [hpair] at hphase hbit ⊢
    exact clock_step_phase_two_bit_source sigma s hs hphase hbit

theorem phase_one_right_bit_source (sigma : Sign) (s t : AgentState L K)
    (ht : t.phase.val = 1)
    (hphase : (Phase1Transition L K s t).2.phase.val = 2)
    (hbit : Phase2AdvanceEpidemic.carries sigma (Phase1Transition L K s t).2) :
    BiasSource sigma (Phase1Transition L K s t).2 := by
  by_cases hm : s.role = .main ∧ t.role = .main
  · have hstay : (Phase1Transition L K s t).2.phase.val = 1 := by
      simp [Phase1Transition, hm, clockCounterStep, hm.2, ht]
    omega
  · have hpair := PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main s t hm
    rw [hpair] at hphase hbit ⊢
    exact clock_step_phase_two_bit_source sigma t ht hphase hbit

theorem epidemic_one_two_safe (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 2)
    (hsafe : s.smallBias.val ∈ ({2,3,4} : Finset ℕ)) :
    phaseEpidemicUpdate L K s t =
      (phaseInit L K ⟨2, by decide⟩ {s with phase := ⟨2, by decide⟩}, t) := by
  have hp : s.phase = ⟨1, by decide⟩ := Fin.ext hs
  have hq : t.phase = ⟨2, by decide⟩ := Fin.ext ht
  have hinterval : (List.range 11).filter
      (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by decide
  have hempty : (List.range 11).filter
      (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by decide
  rcases s with ⟨si, so, sp, sr, sa, sb, ss, sh, sm, sf, sop, sc⟩
  rcases t with ⟨ti, tout, tp, tr, ta, tb, ts, th, tm, tf, top, tc⟩
  simp only at hp hq
  subst sp
  subst tp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
  rcases hsafe with hb | hb | hb <;>
    simp [phaseEpidemicUpdate, runInitsBetween, hinterval, hempty, phaseInit, hb]

theorem epidemic_two_one_safe (s t : AgentState L K)
    (hs : s.phase.val = 2) (ht : t.phase.val = 1)
    (hsafe : t.smallBias.val ∈ ({2,3,4} : Finset ℕ)) :
    phaseEpidemicUpdate L K s t =
      (s, phaseInit L K ⟨2, by decide⟩ {t with phase := ⟨2, by decide⟩}) := by
  have hp : s.phase = ⟨2, by decide⟩ := Fin.ext hs
  have hq : t.phase = ⟨1, by decide⟩ := Fin.ext ht
  have hinterval : (List.range 11).filter
      (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by decide
  have hempty : (List.range 11).filter
      (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by decide
  rcases s with ⟨si, so, sp, sr, sa, sb, ss, sh, sm, sf, sop, sc⟩
  rcases t with ⟨ti, tout, tp, tr, ta, tb, ts, th, tm, tf, top, tc⟩
  simp only at hp hq
  subst sp
  subst tp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
  rcases hsafe with hb | hb | hb <;>
    simp [phaseEpidemicUpdate, runInitsBetween, hinterval, hempty, phaseInit, hb]

theorem epidemic_left_bit_origin (sigma : Sign) (s t : AgentState L K)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 2)
    (he : (phaseEpidemicUpdate L K s t).1.phase.val = 2)
    (hbit : Phase2AdvanceEpidemic.carries sigma (phaseEpidemicUpdate L K s t).1) :
    (s.phase.val = 2 ∧ Phase2AdvanceEpidemic.carries sigma s) ∨
      BiasSource sigma (phaseEpidemicUpdate L K s t).1 := by
  by_cases hs_two : s.phase.val = 2
  · have hop : (phaseEpidemicUpdate L K s t).1.opinions = s.opinions := by
      rcases phaseEpidemicUpdate_left_opinions_preserved_of_phase2
        (L := L) (K := K) s t hs_two with hop | hhigh
      · exact hop
      · omega
    left
    refine ⟨hs_two, ?_⟩
    cases sigma <;> simpa only [Phase2AdvanceEpidemic.carries, hop] using hbit
  · have hs_one : s.phase.val = 1 := by omega
    have ht_two : t.phase.val = 2 := by
      by_contra h
      have ht_one : t.phase.val = 1 := by omega
      have hepi :=
        Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hs_one ht_one
      rw [hepi] at he
      change s.phase.val = 2 at he
      omega
    have hsafe := phaseEpidemicUpdate_left_smallBias_noerror_of_entered
      (L := L) (K := K) s t (by omega) he
    rw [(phaseEpidemicUpdate_preserves_smallBias L K s t).1] at hsafe
    have hepi := epidemic_one_two_safe s t hs_one ht_two hsafe
    have hinit :
        (phaseInit L K ⟨2, by decide⟩ {s with phase := ⟨2, by decide⟩}).phase.val = 2 := by
      simpa only [hepi] using he
    right
    rw [hepi] at hbit ⊢
    exact init_two_bit_source sigma _ hinit hbit

theorem epidemic_right_bit_origin (sigma : Sign) (s t : AgentState L K)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 2)
    (he : (phaseEpidemicUpdate L K s t).2.phase.val = 2)
    (hbit : Phase2AdvanceEpidemic.carries sigma (phaseEpidemicUpdate L K s t).2) :
    (t.phase.val = 2 ∧ Phase2AdvanceEpidemic.carries sigma t) ∨
      BiasSource sigma (phaseEpidemicUpdate L K s t).2 := by
  by_cases ht_two : t.phase.val = 2
  · have hop : (phaseEpidemicUpdate L K s t).2.opinions = t.opinions := by
      rcases phaseEpidemicUpdate_right_opinions_preserved_of_phase2
        (L := L) (K := K) s t ht_two with hop | hhigh
      · exact hop
      · omega
    left
    refine ⟨ht_two, ?_⟩
    cases sigma <;> simpa only [Phase2AdvanceEpidemic.carries, hop] using hbit
  · have ht_one : t.phase.val = 1 := by omega
    have hs_two : s.phase.val = 2 := by
      by_contra h
      have hs_one : s.phase.val = 1 := by omega
      have hepi :=
        Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hs_one ht_one
      rw [hepi] at he
      change t.phase.val = 2 at he
      omega
    have hsafe := phaseEpidemicUpdate_right_smallBias_noerror_of_entered
      (L := L) (K := K) s t (by omega) he
    rw [(phaseEpidemicUpdate_preserves_smallBias L K s t).2] at hsafe
    have hepi := epidemic_two_one_safe s t hs_two ht_one hsafe
    have hinit :
        (phaseInit L K ⟨2, by decide⟩ {t with phase := ⟨2, by decide⟩}).phase.val = 2 := by
      simpa only [hepi] using he
    right
    rw [hepi] at hbit ⊢
    exact init_two_bit_source sigma _ hinit hbit

/-- A carried bit is justified either by an old Phase-2 bit or by a source
among the actual successor endpoints. -/
theorem transition_bit_evidence (sigma : Sign) (Q : Prop) (s t : AgentState L K)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 2)
    (hlcap : (Transition L K s t).1.phase.val ≤ 2)
    (hrcap : (Transition L K s t).2.phase.val ≤ 2)
    (holdl : s.phase.val = 2 → Phase2AdvanceEpidemic.carries sigma s → Q)
    (holdr : t.phase.val = 2 → Phase2AdvanceEpidemic.carries sigma t → Q)
    (hnewl : PhaseTwoSource sigma (Transition L K s t).1 → Q)
    (hnewr : PhaseTwoSource sigma (Transition L K s t).2 → Q) :
    ((Transition L K s t).1.phase.val = 2 →
      Phase2AdvanceEpidemic.carries sigma (Transition L K s t).1 → Q) ∧
    ((Transition L K s t).2.phase.val = 2 →
      Phase2AdvanceEpidemic.carries sigma (Transition L K s t).2 → Q) := by
  by_cases hones : s.phase.val = 1 ∧ t.phase.val = 1
  · have hepi :=
      Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hones.1 hones.2
    have hp : s.phase = ⟨1, by decide⟩ := Fin.ext hones.1
    have htrans : Transition L K s t =
        (finishPhase10Entry L K s (Phase1Transition L K s t).1,
         finishPhase10Entry L K t (Phase1Transition L K s t).2) := by
      unfold Transition
      rw [hepi]
      simp only [hp]
    constructor
    · intro htwo hbit
      have htwo' : (Phase1Transition L K s t).1.phase.val = 2 := by
        simpa only [htrans, finishPhase10Entry_phase_val] using htwo
      have hbit' :
          Phase2AdvanceEpidemic.carries sigma (Phase1Transition L K s t).1 := by
        cases sigma <;>
          simpa only [Phase2AdvanceEpidemic.carries, htrans,
            finishPhase10Entry_opinions] using hbit
      have hsrc := phase_one_left_bit_source sigma s t hones.1 htwo' hbit'
      apply hnewl
      refine ⟨htwo, ?_⟩
      cases sigma <;>
        simpa only [BiasSource, htrans, finishPhase10Entry_smallBias] using hsrc
    · intro htwo hbit
      have htwo' : (Phase1Transition L K s t).2.phase.val = 2 := by
        simpa only [htrans, finishPhase10Entry_phase_val] using htwo
      have hbit' :
          Phase2AdvanceEpidemic.carries sigma (Phase1Transition L K s t).2 := by
        cases sigma <;>
          simpa only [Phase2AdvanceEpidemic.carries, htrans,
            finishPhase10Entry_opinions] using hbit
      have hsrc := phase_one_right_bit_source sigma s t hones.2 htwo' hbit'
      apply hnewr
      refine ⟨htwo, ?_⟩
      cases sigma <;>
        simpa only [BiasSource, htrans, finishPhase10Entry_smallBias] using hsrc
  · have hmax : max s.phase.val t.phase.val = 2 := by omega
    have hbeforel :=
      (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t).1
    have hbeforer :=
      (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t).2
    have hleft := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
    have hright := phaseEpidemicUpdate_right_phase_ge_max (L := L) (K := K) s t
    have hel : (phaseEpidemicUpdate L K s t).1.phase.val = 2 := by omega
    have her : (phaseEpidemicUpdate L K s t).2.phase.val = 2 := by omega
    rcases he : phaseEpidemicUpdate L K s t with ⟨a,b⟩
    have ha : a.phase.val = 2 := by simpa only [he] using hel
    have hb : b.phase.val = 2 := by simpa only [he] using her
    have hfixed := epidemic_eq_self_at_phase_two a b ha hb
    have htrans : Transition L K s t = Transition L K a b := by
      unfold Transition
      rw [he, hfixed]
    rcases Phase2AdvanceEpidemic.Transition_phase2_singleSign_or_advance a b ha hb with
      hstay | hconf
    · have hopl :
          (Transition L K s t).1.opinions = opinionsUnion a.opinions b.opinions := by
        rw [htrans]
        exact hstay.2.2.2.1
      have hopr :
          (Transition L K s t).2.opinions = opinionsUnion a.opinions b.opinions := by
        rw [htrans]
        exact hstay.2.2.2.2
      have hsupportl : Phase2AdvanceEpidemic.carries sigma a → Q := by
        intro hbit
        have hbit' :
            Phase2AdvanceEpidemic.carries sigma (phaseEpidemicUpdate L K s t).1 := by
          simpa only [he] using hbit
        rcases epidemic_left_bit_origin sigma s t hs ht hel hbit' with hold | hsrc
        · exact holdl hold.1 hold.2
        · apply hnewl
          refine ⟨by rw [htrans]; exact hstay.2.1, ?_⟩
          have hsmall := Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
            (L := L) (K := K) s t (by omega)
          cases sigma <;> simpa only [BiasSource, hsmall] using hsrc
      have hsupportr : Phase2AdvanceEpidemic.carries sigma b → Q := by
        intro hbit
        have hbit' :
            Phase2AdvanceEpidemic.carries sigma (phaseEpidemicUpdate L K s t).2 := by
          simpa only [he] using hbit
        rcases epidemic_right_bit_origin sigma s t hs ht her hbit' with hold | hsrc
        · exact holdr hold.1 hold.2
        · apply hnewr
          refine ⟨by rw [htrans]; exact hstay.2.2.1, ?_⟩
          have hsmall :=
            Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
              (L := L) (K := K) s t (by omega)
          cases sigma <;> simpa only [BiasSource, hsmall] using hsrc
      have hunion : Phase2AdvanceEpidemic.carries sigma
          {a with opinions := opinionsUnion a.opinions b.opinions} → Q := by
        intro hbit
        exact (union_bit_sources sigma a b hbit).elim hsupportl hsupportr
      constructor
      · intro _ hbit
        apply hunion
        cases sigma <;> simpa only [Phase2AdvanceEpidemic.carries, hopl] using hbit
      · intro _ hbit
        apply hunion
        cases sigma <;> simpa only [Phase2AdvanceEpidemic.carries, hopr] using hbit
    · have hthree : (Transition L K s t).1.phase.val = 3 := by
        rw [htrans]
        exact hconf.2.2.1
      omega

theorem mixed_origin_at_phase_one (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 1) : MixedSignOrigin c := by
  intro sigma a ha htwo hcarry
  have := hphase a ha
  omega

theorem mixed_origin_step (c : Config (AgentState L K)) (s t : AgentState L K)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (horigin : MixedSignOrigin c)
    (hout : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val ≤ 2) :
    MixedSignOrigin (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s,t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hlmem : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by rw [hstep]; simp
    have hrmem : (Transition L K s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by rw [hstep]; simp
    intro sigma a ha htwo hbit
    have hpair := transition_bit_evidence sigma
      (∃ b ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t, PhaseTwoSource sigma b)
      s t (hpre s hs) (hpre t ht) (hout _ hlmem) (hout _ hrmem)
      (fun hphase hcarry => source_exists_step sigma c s t
        (horigin sigma s hs hphase hcarry) hout)
      (fun hphase hcarry => source_exists_step sigma c s t
        (horigin sigma t ht hphase hcarry) hout)
      (fun hsrc => ⟨_, hlmem, hsrc⟩)
      (fun hsrc => ⟨_, hrmem, hsrc⟩)
    rcases AdvanceNoOvershoot.mem_stepOrSelf_cases c s t a happ ha with hold | rfl | rfl
    · exact source_exists_step sigma c s t
        (horigin sigma a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
          htwo hbit) hout
    · exact hpair.1 htwo hbit
    · exact hpair.2 htwo hbit
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact horigin

theorem mixed_origin_draw (c : TimeTheorem.Cfg L K) (d : TimeTheorem.Draw L K)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (horigin : MixedSignOrigin c)
    (hout : ∀ a ∈ TimeTheorem.applyDraw c d, a.phase.val ≤ 2) :
    MixedSignOrigin (TimeTheorem.applyDraw c d) := by
  cases d with
  | none => exact horigin
  | some p => exact mixed_origin_step c p.1.1 p.2.1 hpre horigin hout

theorem mixed_origin_trace (init : TimeTheorem.Cfg L K) (ω : TimeTheorem.Ω L K)
    (u v : ℕ) (huv : u ≤ v)
    (hstart : ∀ a ∈ TimeTheorem.trace init ω u, a.phase.val = 1)
    (hwindow : ∀ k, u ≤ k → k ≤ v → ∀ a ∈ TimeTheorem.trace init ω k,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 2) :
    MixedSignOrigin (TimeTheorem.trace init ω v) := by
  revert hwindow
  induction v, huv using Nat.le_induction with
  | base =>
      intro _
      exact mixed_origin_at_phase_one _ hstart
  | succ v huv ih =>
      intro hwindow
      have hprevious := ih (fun k hk hkv => hwindow k hk (by omega))
      rw [TraceDrain.trace_succ]
      apply mixed_origin_draw _ (ω (v + 1))
        (hwindow v huv (by omega)) hprevious
      intro a ha
      exact (hwindow (v + 1) (by omega) le_rfl a ha).2

theorem init_two_opinion (a : AgentState L K)
    (hphase : (phaseInit L K ⟨2, by decide⟩ a).phase.val = 2) :
    PhaseTwoOpinion (phaseInit L K ⟨2, by decide⟩ a) := by
  rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
    hour, minute, full, opinions, counter⟩
  fin_cases smallBias <;>
    simp [PhaseTwoOpinion, Phase2Convergence.singleSign, phaseInit,
      enterPhase10, phase10, hasPlusOne, hasMinusOne] at hphase ⊢

theorem clock_step_phase_two_opinion (a : AgentState L K)
    (ha : a.phase.val = 1)
    (hphase : (clockCounterStep L K a).phase.val = 2) :
    PhaseTwoOpinion (clockCounterStep L K a) := by
  by_cases hc : a.role = .clock
  · simp only [clockCounterStep, if_pos hc] at hphase ⊢
    by_cases hz : a.counter.val = 0
    · simp only [stdCounterSubroutine, dif_pos hz, if_pos hz] at hphase ⊢
      have hpa : (advancePhase L K a).phase = ⟨2, by decide⟩ := by
        apply Fin.ext
        simp [advancePhase, ha]
      unfold advancePhaseWithInit at hphase ⊢
      dsimp only at hphase ⊢
      rw [hpa] at hphase ⊢
      exact init_two_opinion _ hphase
    · simp [stdCounterSubroutine, hz, ha] at hphase
  · simp [clockCounterStep, hc, ha] at hphase

theorem phase_one_left_opinion (s t : AgentState L K)
    (hs : s.phase.val = 1)
    (hphase : (Phase1Transition L K s t).1.phase.val = 2) :
    PhaseTwoOpinion (Phase1Transition L K s t).1 := by
  by_cases hm : s.role = .main ∧ t.role = .main
  · have hstay : (Phase1Transition L K s t).1.phase.val = 1 := by
      simp [Phase1Transition, hm, clockCounterStep, hm.1, hs]
    omega
  · rw [PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main s t hm] at hphase ⊢
    exact clock_step_phase_two_opinion s hs hphase

theorem phase_one_right_opinion (s t : AgentState L K)
    (ht : t.phase.val = 1)
    (hphase : (Phase1Transition L K s t).2.phase.val = 2) :
    PhaseTwoOpinion (Phase1Transition L K s t).2 := by
  by_cases hm : s.role = .main ∧ t.role = .main
  · have hstay : (Phase1Transition L K s t).2.phase.val = 1 := by
      simp [Phase1Transition, hm, clockCounterStep, hm.2, ht]
    omega
  · rw [PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main s t hm] at hphase ⊢
    exact clock_step_phase_two_opinion t ht hphase

theorem transition_two_opinion (s t : AgentState L K)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 2)
    (hlcap : (Transition L K s t).1.phase.val ≤ 2)
    (hrcap : (Transition L K s t).2.phase.val ≤ 2)
    (holdl : s.phase.val = 2 → PhaseTwoOpinion s)
    (holdr : t.phase.val = 2 → PhaseTwoOpinion t) :
    ((Transition L K s t).1.phase.val = 2 →
      PhaseTwoOpinion (Transition L K s t).1) ∧
    ((Transition L K s t).2.phase.val = 2 →
      PhaseTwoOpinion (Transition L K s t).2) := by
  by_cases hones : s.phase.val = 1 ∧ t.phase.val = 1
  · have hepi :=
      Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hones.1 hones.2
    have hp : s.phase = ⟨1, by decide⟩ := Fin.ext hones.1
    have htrans : Transition L K s t =
        (finishPhase10Entry L K s (Phase1Transition L K s t).1,
         finishPhase10Entry L K t (Phase1Transition L K s t).2) := by
      unfold Transition
      rw [hepi]
      simp only [hp]
    constructor
    · intro htwo
      have htwo' : (Phase1Transition L K s t).1.phase.val = 2 := by
        simpa only [htrans, finishPhase10Entry_phase_val] using htwo
      simpa only [PhaseTwoOpinion, htrans, finishPhase10Entry_opinions] using
        (phase_one_left_opinion s t hones.1 htwo')
    · intro htwo
      have htwo' : (Phase1Transition L K s t).2.phase.val = 2 := by
        simpa only [htrans, finishPhase10Entry_phase_val] using htwo
      simpa only [PhaseTwoOpinion, htrans, finishPhase10Entry_opinions] using
        (phase_one_right_opinion s t hones.2 htwo')
  · have hmax : max s.phase.val t.phase.val = 2 := by omega
    have hbeforel :=
      (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t).1
    have hbeforer :=
      (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t).2
    have hleft := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
    have hright := phaseEpidemicUpdate_right_phase_ge_max (L := L) (K := K) s t
    have hel : (phaseEpidemicUpdate L K s t).1.phase.val = 2 := by omega
    have her : (phaseEpidemicUpdate L K s t).2.phase.val = 2 := by omega
    rcases he : phaseEpidemicUpdate L K s t with ⟨a,b⟩
    have ha : a.phase.val = 2 := by simpa only [he] using hel
    have hb : b.phase.val = 2 := by simpa only [he] using her
    have hfixed := epidemic_eq_self_at_phase_two a b ha hb
    have htrans : Transition L K s t = Transition L K a b := by
      unfold Transition
      rw [he, hfixed]
    rcases Phase2AdvanceEpidemic.Transition_phase2_singleSign_or_advance a b ha hb with
      hstay | hconf
    · have hopl :
          (Transition L K s t).1.opinions = opinionsUnion a.opinions b.opinions := by
        rw [htrans]
        exact hstay.2.2.2.1
      have hopr :
          (Transition L K s t).2.opinions = opinionsUnion a.opinions b.opinions := by
        rw [htrans]
        exact hstay.2.2.2.2
      have hne : (opinionsUnion a.opinions b.opinions).val ≠ 0 := by
        by_cases hs_two : s.phase.val = 2
        · have hop : a.opinions = s.opinions := by
            rcases phaseEpidemicUpdate_left_opinions_preserved_of_phase2
              (L := L) (K := K) s t hs_two with hop | hhigh
            · simpa only [he] using hop
            · omega
          have ha_ne : a.opinions.val ≠ 0 := by
            rw [hop]
            exact (holdl hs_two).2
          exact Phase2AdvanceEpidemic.opinionsUnion_ne_zero_of_left ha_ne
        · have ht_two : t.phase.val = 2 := by omega
          have hop : b.opinions = t.opinions := by
            rcases phaseEpidemicUpdate_right_opinions_preserved_of_phase2
              (L := L) (K := K) s t ht_two with hop | hhigh
            · simpa only [he] using hop
            · omega
          have hb_ne : b.opinions.val ≠ 0 := by
            rw [hop]
            exact (holdr ht_two).2
          have hcomm : ∀ x y : Fin 8, opinionsUnion x y = opinionsUnion y x := by decide
          rw [hcomm a.opinions b.opinions]
          exact Phase2AdvanceEpidemic.opinionsUnion_ne_zero_of_left hb_ne
      constructor
      · intro _
        simpa only [PhaseTwoOpinion, hopl] using And.intro hstay.1 hne
      · intro _
        simpa only [PhaseTwoOpinion, hopr] using And.intro hstay.1 hne
    · have hthree : (Transition L K s t).1.phase.val = 3 := by
        rw [htrans]
        exact hconf.2.2.1
      omega

theorem mixed_opinion_step (c : Config (AgentState L K)) (s t : AgentState L K)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (hpayload : MixedOpinionPayload c)
    (hout : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val ≤ 2) :
    MixedOpinionPayload (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s,t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hlmem : (Transition L K s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by rw [hstep]; simp
    have hrmem : (Transition L K s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L K) c s t := by rw [hstep]; simp
    have hpair := transition_two_opinion s t (hpre s hs) (hpre t ht)
      (hout _ hlmem) (hout _ hrmem) (hpayload s hs) (hpayload t ht)
    intro a ha htwo
    rcases AdvanceNoOvershoot.mem_stepOrSelf_cases c s t a happ ha with hold | rfl | rfl
    · exact hpayload a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold) htwo
    · exact hpair.1 htwo
    · exact hpair.2 htwo
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hpayload

theorem mixed_opinion_draw (c : TimeTheorem.Cfg L K) (d : TimeTheorem.Draw L K)
    (hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (hpayload : MixedOpinionPayload c)
    (hout : ∀ a ∈ TimeTheorem.applyDraw c d, a.phase.val ≤ 2) :
    MixedOpinionPayload (TimeTheorem.applyDraw c d) := by
  cases d with
  | none => exact hpayload
  | some p => exact mixed_opinion_step c p.1.1 p.2.1 hpre hpayload hout

theorem mixed_opinion_trace (init : TimeTheorem.Cfg L K) (ω : TimeTheorem.Ω L K)
    (u v : ℕ) (huv : u ≤ v)
    (hstart : ∀ a ∈ TimeTheorem.trace init ω u, a.phase.val = 1)
    (hwindow : ∀ k, u ≤ k → k ≤ v → ∀ a ∈ TimeTheorem.trace init ω k,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 2) :
    MixedOpinionPayload (TimeTheorem.trace init ω v) := by
  revert hwindow
  induction v, huv using Nat.le_induction with
  | base =>
      intro _
      intro a ha htwo
      have := hstart a ha
      omega
  | succ v huv ih =>
      intro hwindow
      have hprevious := ih (fun k hk hkv => hwindow k hk (by omega))
      rw [TraceDrain.trace_succ]
      apply mixed_opinion_draw _ (ω (v + 1))
        (hwindow v huv (by omega)) hprevious
      intro a ha
      exact (hwindow (v + 1) (by omega) le_rfl a ha).2

theorem pure_provenance_of_mixed_origin (init c : Config (AgentState L K))
    (n : ℕ) (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hshell : Phase2EntryDispatcher.PurePhase2Shell n c)
    (horigin : MixedSignOrigin c) :
    Phase2EntryDispatcher.PurePhase2Provenance init n c := by
  refine { toPurePhase2Shell := hshell, valid_initial := hvalid, reachable := hreach, sign_origin := ?_ }
  constructor
  · intro hp
    unfold Phase2AdvanceEpidemic.signCount at hp
    rcases Multiset.countP_pos.mp hp with ⟨a, ha, hcarry⟩
    rcases horigin .pos a ha (hshell.phase_eq a ha) hcarry with ⟨b, hb, hsrc⟩
    exact ⟨b, hb, hsrc.2⟩
  · intro hm
    unfold Phase2AdvanceEpidemic.signCount at hm
    rcases Multiset.countP_pos.mp hm with ⟨a, ha, hcarry⟩
    rcases horigin .neg a ha (hshell.phase_eq a ha) hcarry with ⟨b, hb, hsrc⟩
    exact ⟨b, hb, hsrc.2⟩

/-- At a genuine pure-Phase-2 boundary of the actual mixed history, all of
PurePhase2Provenance is produced: no shell or sign-origin hypothesis remains. -/
theorem pure_phase_two_provenance_from_history
    (init : TimeTheorem.Cfg L K) (ω : TimeTheorem.Ω L K)
    (n u v : ℕ) (hvalid : validInitial init) (huv : u ≤ v)
    (hstart : ∀ a ∈ TimeTheorem.trace init ω u, a.phase.val = 1)
    (hwindow : ∀ k, u ≤ k → k ≤ v → ∀ a ∈ TimeTheorem.trace init ω k,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 2)
    (hcard : (TimeTheorem.trace init ω v).card = n)
    (hpure : ∀ a ∈ TimeTheorem.trace init ω v, a.phase.val = 2) :
    Phase2EntryDispatcher.PurePhase2Provenance init n (TimeTheorem.trace init ω v) := by
  have hreach :
      (NonuniformMajority L K).Reachable init (TimeTheorem.trace init ω v) := by
    simpa only [TraceDrain.trace_zero] using
      (TimeTheorem.trace_reachable init ω (s := 0) (t := v) (Nat.zero_le v))
  have hop := mixed_opinion_trace init ω u v huv hstart hwindow
  have hroles := post_phase_zero_role_partition init (TimeTheorem.trace init ω v)
    hvalid hreach (fun a ha => by have := hpure a ha; omega)
  have hsafe := reachable_phase2_smallBias_noerror init (TimeTheorem.trace init ω v)
    hvalid hreach
  have hwf : AdvanceNoOvershoot.Wf (TimeTheorem.trace init ω v) := by
    intro a ha
    have hb := hsafe a ha (hpure a ha)
    have hn : a.role ≠ .mcr := by
      rcases hroles a ha with hm | hr | hc | hten
      · rw [hm]; decide
      · rw [hr]; decide
      · rw [hc]; decide
      · have := hpure a ha
        omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    exact ⟨hn, by omega, by omega⟩
  have hshell :
      Phase2EntryDispatcher.PurePhase2Shell n (TimeTheorem.trace init ω v) :=
    ⟨hcard, hpure, fun a ha => (hop a ha (hpure a ha)).1,
      hwf, fun a ha => (hop a ha (hpure a ha)).2⟩
  exact pure_provenance_of_mixed_origin init _ n hvalid hreach hshell
    (mixed_origin_trace init ω u v huv hstart hwindow)

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoProvenance
