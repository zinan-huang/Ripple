import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoProvenance
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStopping

/-!
# Reachable persistence of pure Phase-2 provenance

A still-pure successor retains source ancestry and initialized opinion payload.
A general reachable successor is either still pure with complete provenance,
or already has a phase-at-least-three seed. Phase monotonicity keeps every
agent at phase at least two, so the seeded branch is the existing
AdvancedPast2 target, including mixed Phase-2/3 populations.
-/

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoPersistence

open TimeTheorem PhaseTwoProvenance

variable {L K : ℕ}

theorem mixed_origin_of_pure_provenance
    (init c : Cfg L K) (n : ℕ)
    (h : Phase2EntryDispatcher.PurePhase2Provenance init n c) :
    MixedSignOrigin c := by
  intro sigma a ha hphase hbit
  have hcount : 1 ≤ Phase2AdvanceEpidemic.signCount sigma c := by
    unfold Phase2AdvanceEpidemic.signCount
    exact Multiset.countP_pos.mpr ⟨a, ha, hbit⟩
  cases sigma with
  | pos =>
      obtain ⟨b, hb, hsource⟩ := h.sign_origin.1 hcount
      exact ⟨b, hb, h.phase_eq b hb, hsource⟩
  | neg =>
      obtain ⟨b, hb, hsource⟩ := h.sign_origin.2 hcount
      exact ⟨b, hb, h.phase_eq b hb, hsource⟩

theorem mixed_payload_of_pure_provenance
    (init c : Cfg L K) (n : ℕ)
    (h : Phase2EntryDispatcher.PurePhase2Provenance init n c) :
    MixedOpinionPayload c := by
  intro a ha hphase
  exact ⟨h.single a ha, h.opinions_ne_zero a ha⟩

theorem pure_provenance_of_reachable_payload
    (init c : Cfg L K) (n : ℕ)
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hcard : c.card = n)
    (hpure : ∀ a ∈ c, a.phase.val = 2)
    (hpayload : MixedOpinionPayload c) (horigin : MixedSignOrigin c) :
    Phase2EntryDispatcher.PurePhase2Provenance init n c := by
  have hroles := post_phase_zero_role_partition init c hvalid hreach
    (fun a ha => by have := hpure a ha; omega)
  have hsafe := reachable_phase2_smallBias_noerror init c hvalid hreach
  have hwf : AdvanceNoOvershoot.Wf c := by
    intro a ha
    have hb := hsafe a ha (hpure a ha)
    have hn : a.role ≠ .mcr := by
      rcases hroles a ha with hm | hr | hc | hten
      · rw [hm]
        decide
      · rw [hr]
        decide
      · rw [hc]
        decide
      · have := hpure a ha
        omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    exact ⟨hn, by omega, by omega⟩
  have hshell : Phase2EntryDispatcher.PurePhase2Shell n c :=
    ⟨hcard, hpure, fun a ha => (hpayload a ha (hpure a ha)).1,
      hwf, fun a ha => (hpayload a ha (hpure a ha)).2⟩
  exact pure_provenance_of_mixed_origin init c n hvalid hreach hshell horigin

theorem pure_provenance_step_of_pure
    (init c : Cfg L K) (n : ℕ)
    (h : Phase2EntryDispatcher.PurePhase2Provenance init n c)
    (s t : AgentState L K)
    (hpure : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val = 2) :
    Phase2EntryDispatcher.PurePhase2Provenance init n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  have hstep : (NonuniformMajority L K).Reachable c
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) :=
    Protocol.reachable_stepOrSelf c s t
  have hpre : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 2 := by
    intro a ha
    have := h.phase_eq a ha
    omega
  have hout : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val ≤ 2 := fun a ha => le_of_eq (hpure a ha)
  exact pure_provenance_of_reachable_payload init _ n h.valid_initial
    (Relation.ReflTransGen.trans h.reachable hstep)
    ((Protocol.reachable_card_eq hstep).trans h.card_eq) hpure
    (mixed_opinion_step c s t hpre
      (mixed_payload_of_pure_provenance init c n h) hout)
    (mixed_origin_step c s t hpre
      (mixed_origin_of_pure_provenance init c n h) hout)

theorem pure_provenance_draw_of_pure
    (init c : Cfg L K) (n : ℕ)
    (h : Phase2EntryDispatcher.PurePhase2Provenance init n c)
    (d : Draw L K) (hpure : ∀ a ∈ applyDraw c d, a.phase.val = 2) :
    Phase2EntryDispatcher.PurePhase2Provenance init n (applyDraw c d) := by
  cases d with
  | none => exact h
  | some p => exact pure_provenance_step_of_pure init c n h p.1.1 p.2.1 hpure

theorem pure_provenance_stepRel_of_pure
    (init c c' : Cfg L K) (n : ℕ)
    (h : Phase2EntryDispatcher.PurePhase2Provenance init n c)
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hpure : ∀ a ∈ c', a.phase.val = 2) :
    Phase2EntryDispatcher.PurePhase2Provenance init n c' := by
  classical
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hdraw : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos (show Protocol.Applicable c s t from happ)] <;> rfl
  have heq : c' = Protocol.stepOrSelf (NonuniformMajority L K) c s t :=
    hc'.trans hdraw.symm
  rw [heq] at hpure ⊢
  exact pure_provenance_step_of_pure init c n h s t hpure

theorem pure_provenance_reachable_of_pure_endpoint
    (init c c' : Cfg L K) (n : ℕ)
    (h : Phase2EntryDispatcher.PurePhase2Provenance init n c)
    (hreach : (NonuniformMajority L K).Reachable c c')
    (hpure : ∀ a ∈ c', a.phase.val = 2) :
    Phase2EntryDispatcher.PurePhase2Provenance init n c' := by
  revert hpure
  induction hreach with
  | refl =>
      intro _
      exact h
  | tail hprev hstep ih =>
      rename_i b d
      intro hpure
      have hlo := PhaseOneDrainStopping.phase_lower_reachable 2 c b hprev
        (fun a ha => le_of_eq (h.phase_eq a ha).symm)
      have hhi := PhaseOneDrainStopping.phase_upper_stepRel 2 b d hstep
        (fun a ha => le_of_eq (hpure a ha))
      have hmiddle : ∀ a ∈ b, a.phase.val = 2 :=
        fun a ha => Nat.le_antisymm (hhi a ha) (hlo a ha)
      exact pure_provenance_stepRel_of_pure init b d n (ih hmiddle) hstep hpure

/-- This is the exhaustive restart split after any number of actual protocol
steps. The second branch includes mixed Phase-2/3 and backup configurations. -/
theorem pure_or_threshold_seed_reachable
    (init c c' : Cfg L K) (n : ℕ)
    (h : Phase2EntryDispatcher.PurePhase2Provenance init n c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    Phase2EntryDispatcher.PurePhase2Provenance init n c' ∨
      ∃ a ∈ c', 3 ≤ a.phase.val := by
  classical
  by_cases hseed : ∃ a ∈ c', 3 ≤ a.phase.val
  · exact Or.inr hseed
  · left
    have hlo := PhaseOneDrainStopping.phase_lower_reachable 2 c c' hreach
      (fun a ha => le_of_eq (h.phase_eq a ha).symm)
    apply pure_provenance_reachable_of_pure_endpoint init c c' n h hreach
    intro a ha
    have hlt : a.phase.val < 3 := Nat.lt_of_not_ge (fun hge => hseed ⟨a, ha, hge⟩)
    have hge := hlo a ha
    omega

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoPersistence
