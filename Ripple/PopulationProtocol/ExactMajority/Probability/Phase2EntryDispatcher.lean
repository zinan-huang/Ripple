/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-2 entry provenance and outcome dispatch

The Phase-1/2 boundary is not a single unconditional Phase-2 work input.  A
state still on the pure Phase-2 surface has four genuine outcomes: the three
fixed-verdict branches `A`, `B`, and `T`, or the mixed-sign advance branch.
An initializer error is only a Phase-10 *seed*, not `Phase10Ready`; similarly,
an arbitrary state already beyond Phase 2 is not the exact first-entry shell.

This file records those distinctions without changing the protocol or any
barrel.  The pure-shell classifier is closed.  The asynchronous entry and
already-crossed producer maps are exposed below as named residual propositions;
the recovery seed-to-ready map is discharged in `Recovery10EntryReachable`.
-/

import Ripple.PopulationProtocol.ExactMajority.Analysis.DeterministicChain
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1GapFloorEntryClosure
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2AdvanceEpidemic
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2StableEndpoint

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase2EntryDispatcher

open scoped Classical

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Pure Phase-2 surface -/

/-- The state fields consumed by the four pure Phase-2 branches.

`singleSign` and nonzero opinions are required by the mixed-sign epidemic;
`Wf` is the concrete no-initializer-error provenance. -/
structure PurePhase2Shell (n : ℕ) (c : Config (AgentState L K)) : Prop where
  card_eq : c.card = n
  phase_eq : ∀ a ∈ c, a.phase.val = 2
  single : ∀ a ∈ c, Phase2Convergence.singleSign a.opinions
  wf : AdvanceNoOvershoot.Wf c
  opinions_ne_zero : ∀ a ∈ c, a.opinions.val ≠ 0

/-- The only sign-origin fact not exported by the current deterministic API.

Opinion union can copy a sign to a neutral agent, so the useful invariant is
global: every live sign still has at least one small-bias source somewhere in
the population.  The initializer establishes this immediately; preservation
through an asynchronous Phase-2 entry run is a separate producer obligation. -/
def SignOrigin (c : Config (AgentState L K)) : Prop :=
  (1 ≤ Phase2AdvanceEpidemic.signCount Sign.pos c →
      ∃ a ∈ c, 3 < a.smallBias.val) ∧
    (1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c →
      ∃ a ∈ c, a.smallBias.val < 3)

/-- Reachable pure Phase-2 provenance.  This is exactly the data needed to
identify an `A/B/T` branch with the initial majority verdict, or to enter the
mixed-sign `Active2Concrete` branch. -/
structure PurePhase2Provenance
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K)) : Prop extends PurePhase2Shell n c where
  valid_initial : validInitial init
  reachable : (NonuniformMajority L K).Reachable init c
  sign_origin : SignOrigin c

private theorem exists_carries_of_signCount_pos
    (sigma : Sign) (c : Config (AgentState L K))
    (h : 1 ≤ Phase2AdvanceEpidemic.signCount sigma c) :
    ∃ a ∈ c, Phase2AdvanceEpidemic.carries sigma a := by
  unfold Phase2AdvanceEpidemic.signCount at h
  exact Multiset.countP_pos.mp h

private theorem not_carries_of_signCount_not_pos
    (sigma : Sign) (c : Config (AgentState L K))
    (h : ¬ 1 ≤ Phase2AdvanceEpidemic.signCount sigma c) :
    ∀ a ∈ c, ¬ Phase2AdvanceEpidemic.carries sigma a := by
  have hzero : Phase2AdvanceEpidemic.signCount sigma c = 0 := by omega
  unfold Phase2AdvanceEpidemic.signCount at hzero
  exact Multiset.countP_eq_zero.mp hzero

private theorem opinion_eq_tie_of_no_sign_nonzero
    (o : Fin 8) (hne : o.val ≠ 0)
    (hminus : ¬ hasMinusOne o = true)
    (hplus : ¬ hasPlusOne o = true) :
    o = phase2OpinionT := by
  fin_cases o <;>
    simp [hasMinusOne, hasPlusOne, phase2OpinionT] at hne hminus hplus ⊢

/-- Closed four-way classification of a pure Phase-2 shell.

The fixed-verdict constructors expose the exact existing
`Phase2BranchPre`; the fourth constructor exposes the exact existing
`Active2Concrete`. -/
inductive PureDispatch (n : ℕ) (c : Config (AgentState L K)) : Prop
  | branchA
      (h : Phase2CarrierEpidemic.Phase2BranchPre
        (L := L) (K := K) .A n c)
  | branchB
      (h : Phase2CarrierEpidemic.Phase2BranchPre
        (L := L) (K := K) .B n c)
  | branchT
      (h : Phase2CarrierEpidemic.Phase2BranchPre
        (L := L) (K := K) .T n c)
  | advance
      (h : Phase2AdvanceEpidemic.Active2Concrete
        (L := L) (K := K) n c)

/-- Every pure shell enters exactly one of the existing Phase-2 consumers.

The proof first asks whether each strict sign is live.  Both signs give the
advance branch; exactly one gives the corresponding carrier branch; neither
forces every nonzero opinion to be the tie code. -/
theorem pure_dispatch
    (n : ℕ) (c : Config (AgentState L K))
    (h : PurePhase2Shell (L := L) (K := K) n c) :
    PureDispatch (L := L) (K := K) n c := by
  classical
  by_cases hp : 1 ≤ Phase2AdvanceEpidemic.signCount Sign.pos c
  · by_cases hm : 1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c
    · exact .advance ⟨⟨⟨h.card_eq, fun a ha =>
          ⟨h.phase_eq a ha, h.single a ha⟩⟩, hp, hm⟩,
        h.wf, h.opinions_ne_zero⟩
    · apply PureDispatch.branchA
      refine ⟨h.card_eq, ?_, ?_⟩
      · intro a ha
        refine ⟨h.phase_eq a ha, ?_⟩
        unfold Phase2CarrierEpidemic.opinionCompatible
        have hnot := not_carries_of_signCount_not_pos
          Sign.neg c hm a ha
        unfold Phase2AdvanceEpidemic.carries at hnot
        cases hx : hasMinusOne a.opinions <;> simp_all
      · rcases exists_carries_of_signCount_pos Sign.pos c hp with
          ⟨a, ha, hcarry⟩
        exact ⟨a, ha, by
          simpa [Phase2CarrierEpidemic.opinionCarrier,
            Phase2AdvanceEpidemic.carries] using hcarry⟩
  · by_cases hm : 1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c
    · apply PureDispatch.branchB
      refine ⟨h.card_eq, ?_, ?_⟩
      · intro a ha
        refine ⟨h.phase_eq a ha, ?_⟩
        unfold Phase2CarrierEpidemic.opinionCompatible
        have hnot := not_carries_of_signCount_not_pos
          Sign.pos c hp a ha
        unfold Phase2AdvanceEpidemic.carries at hnot
        cases hx : hasPlusOne a.opinions <;> simp_all
      · rcases exists_carries_of_signCount_pos Sign.neg c hm with
          ⟨a, ha, hcarry⟩
        exact ⟨a, ha, by
          simpa [Phase2CarrierEpidemic.opinionCarrier,
            Phase2AdvanceEpidemic.carries] using hcarry⟩
    · apply PureDispatch.branchT
      refine ⟨h.card_eq, ?_, trivial⟩
      intro a ha
      refine ⟨h.phase_eq a ha, ?_⟩
      unfold Phase2CarrierEpidemic.opinionCompatible
      apply opinion_eq_tie_of_no_sign_nonzero a.opinions
        (h.opinions_ne_zero a ha)
      · exact not_carries_of_signCount_not_pos
          Sign.neg c hm a ha
      · exact not_carries_of_signCount_not_pos
          Sign.pos c hp a ha

/-! ## Verdict provenance for the three fixed branches -/

private theorem smallBiasSum_nonneg_of_no_negative
    (c : Config (AgentState L K))
    (hnone : ∀ a ∈ c, ¬ a.smallBias.val < 3) :
    0 ≤ smallBiasSum c := by
  induction c using Multiset.induction_on with
  | empty => simp [smallBiasSum]
  | cons a c ih =>
      have ha : 0 ≤ AgentState.smallBiasInt a := by
        unfold AgentState.smallBiasInt
        have := hnone a (Multiset.mem_cons_self a c)
        omega
      have hc : 0 ≤ smallBiasSum c :=
        ih (fun b hb hneg => hnone b (Multiset.mem_cons_of_mem hb) hneg)
      simp [smallBiasSum] at hc ⊢
      omega

private theorem smallBiasSum_nonpos_of_no_positive
    (c : Config (AgentState L K))
    (hnone : ∀ a ∈ c, ¬ 3 < a.smallBias.val) :
    smallBiasSum c ≤ 0 := by
  induction c using Multiset.induction_on with
  | empty => simp [smallBiasSum]
  | cons a c ih =>
      have ha : AgentState.smallBiasInt a ≤ 0 := by
        unfold AgentState.smallBiasInt
        have := hnone a (Multiset.mem_cons_self a c)
        omega
      have hc : smallBiasSum c ≤ 0 :=
        ih (fun b hb hpos => hnone b (Multiset.mem_cons_of_mem hb) hpos)
      simp [smallBiasSum] at hc ⊢
      omega

private theorem smallBiasSum_pos_of_source_no_negative
    (c : Config (AgentState L K))
    (hpos : ∃ a ∈ c, 3 < a.smallBias.val)
    (hnone : ∀ a ∈ c, ¬ a.smallBias.val < 3) :
    0 < smallBiasSum c := by
  induction c using Multiset.induction_on with
  | empty =>
      rcases hpos with ⟨a, ha, _⟩
      simp at ha
  | cons a c ih =>
      rcases hpos with ⟨b, hb, hbpos⟩
      have ha_nonneg : 0 ≤ AgentState.smallBiasInt a := by
        unfold AgentState.smallBiasInt
        have := hnone a (Multiset.mem_cons_self a c)
        omega
      by_cases hba : b = a
      · subst b
        have ha_pos : 0 < AgentState.smallBiasInt a := by
          unfold AgentState.smallBiasInt
          omega
        have hc_nonneg : 0 ≤ smallBiasSum c :=
          smallBiasSum_nonneg_of_no_negative c
            (fun x hx hneg => hnone x (Multiset.mem_cons_of_mem hx) hneg)
        simp [smallBiasSum] at hc_nonneg ⊢
        omega
      · have hb_tail : b ∈ c := by
          have : b = a ∨ b ∈ c := by simpa using hb
          exact this.resolve_left hba
        have hc_pos : 0 < smallBiasSum c :=
          ih ⟨b, hb_tail, hbpos⟩
            (fun x hx hneg => hnone x (Multiset.mem_cons_of_mem hx) hneg)
        simp [smallBiasSum] at hc_pos ⊢
        omega

private theorem smallBiasSum_neg_of_source_no_positive
    (c : Config (AgentState L K))
    (hneg : ∃ a ∈ c, a.smallBias.val < 3)
    (hnone : ∀ a ∈ c, ¬ 3 < a.smallBias.val) :
    smallBiasSum c < 0 := by
  induction c using Multiset.induction_on with
  | empty =>
      rcases hneg with ⟨a, ha, _⟩
      simp at ha
  | cons a c ih =>
      rcases hneg with ⟨b, hb, hbneg⟩
      have ha_nonpos : AgentState.smallBiasInt a ≤ 0 := by
        unfold AgentState.smallBiasInt
        have := hnone a (Multiset.mem_cons_self a c)
        omega
      by_cases hba : b = a
      · subst b
        have ha_neg : AgentState.smallBiasInt a < 0 := by
          unfold AgentState.smallBiasInt
          omega
        have hc_nonpos : smallBiasSum c ≤ 0 :=
          smallBiasSum_nonpos_of_no_positive c
            (fun x hx hpos => hnone x (Multiset.mem_cons_of_mem hx) hpos)
        simp [smallBiasSum] at hc_nonpos ⊢
        omega
      · have hb_tail : b ∈ c := by
          have : b = a ∨ b ∈ c := by simpa using hb
          exact this.resolve_left hba
        have hc_neg : smallBiasSum c < 0 :=
          ih ⟨b, hb_tail, hbneg⟩
            (fun x hx hpos => hnone x (Multiset.mem_cons_of_mem hx) hpos)
        simp [smallBiasSum] at hc_neg ⊢
        omega

private theorem no_negative_source_of_no_negative_sign
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hneg : ¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c) :
    ∀ a ∈ c, ¬ a.smallBias.val < 3 := by
  intro a ha hsmall
  have hsupport := reachable_phase2SignSupport
    (L := L) (K := K) init c hinit hreach a ha (hphase a ha)
  have hcarry : Phase2AdvanceEpidemic.carries Sign.neg a := by
    simpa [Phase2AdvanceEpidemic.carries] using hsupport.2 hsmall
  exact not_carries_of_signCount_not_pos Sign.neg c hneg a ha hcarry

private theorem no_positive_source_of_no_positive_sign
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hpos : ¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.pos c) :
    ∀ a ∈ c, ¬ 3 < a.smallBias.val := by
  intro a ha hsmall
  have hsupport := reachable_phase2SignSupport
    (L := L) (K := K) init c hinit hreach a ha (hphase a ha)
  have hcarry : Phase2AdvanceEpidemic.carries Sign.pos a := by
    simpa [Phase2AdvanceEpidemic.carries] using hsupport.1 hsmall
  exact not_carries_of_signCount_not_pos Sign.pos c hpos a ha hcarry

/-- On the A-only branch, sign origin and the conserved small-bias sum identify
the branch with the initial majority verdict. -/
theorem majorityVerdict_A_of_provenance
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K))
    (h : PurePhase2Provenance (L := L) (K := K) init n c)
    (hp : 1 ≤ Phase2AdvanceEpidemic.signCount Sign.pos c)
    (hm : ¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c) :
    majorityVerdict init = outputTripleOfOutput .A := by
  have hsum : 0 < smallBiasSum c :=
    smallBiasSum_pos_of_source_no_negative c
      (h.sign_origin.1 hp)
      (no_negative_source_of_no_negative_sign init c h.valid_initial
        h.reachable h.phase_eq hm)
  have hsum_eq := reachable_smallBiasSum_eq_initialGap_all_phases
    (L := L) (K := K) init c h.valid_initial h.reachable
  apply majorityVerdict_eq_A_of_initialGap_pos
  rwa [← hsum_eq]

/-- B-only counterpart of `majorityVerdict_A_of_provenance`. -/
theorem majorityVerdict_B_of_provenance
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K))
    (h : PurePhase2Provenance (L := L) (K := K) init n c)
    (hp : ¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.pos c)
    (hm : 1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c) :
    majorityVerdict init = outputTripleOfOutput .B := by
  have hsum : smallBiasSum c < 0 :=
    smallBiasSum_neg_of_source_no_positive c
      (h.sign_origin.2 hm)
      (no_positive_source_of_no_positive_sign init c h.valid_initial
        h.reachable h.phase_eq hp)
  have hsum_eq := reachable_smallBiasSum_eq_initialGap_all_phases
    (L := L) (K := K) init c h.valid_initial h.reachable
  apply majorityVerdict_eq_B_of_initialGap_neg
  rwa [← hsum_eq]

/-- With neither strict sign live, reachable sign support forces every
small-bias value to be neutral, so the initial verdict is exactly `T`. -/
theorem majorityVerdict_T_of_provenance
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K))
    (h : PurePhase2Provenance (L := L) (K := K) init n c)
    (hp : ¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.pos c)
    (hm : ¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c) :
    majorityVerdict init = outputTripleOfOutput .T := by
  have hnonneg : 0 ≤ smallBiasSum c :=
    smallBiasSum_nonneg_of_no_negative c
      (no_negative_source_of_no_negative_sign init c h.valid_initial
        h.reachable h.phase_eq hm)
  have hnonpos : smallBiasSum c ≤ 0 :=
    smallBiasSum_nonpos_of_no_positive c
      (no_positive_source_of_no_positive_sign init c h.valid_initial
        h.reachable h.phase_eq hp)
  have hzero : smallBiasSum c = 0 := le_antisymm hnonpos hnonneg
  have hsum_eq := reachable_smallBiasSum_eq_initialGap_all_phases
    (L := L) (K := K) init c h.valid_initial h.reachable
  apply majorityVerdict_eq_T_of_initialGap_zero
  rw [← hsum_eq, hzero]

/-! ## Outcome-aware pure dispatch -/

/-- A fixed-verdict Phase-2 entry together with the verdict provenance needed
by the stable-endpoint bridge. -/
structure ConsensusEntry
    (init : Config (AgentState L K)) (out : Output) (n : ℕ)
    (c : Config (AgentState L K)) : Prop where
  pre : Phase2CarrierEpidemic.Phase2BranchPre
    (L := L) (K := K) out n c
  verdict : majorityVerdict init = outputTripleOfOutput out

/-- Direct adapter to the existing A/B/T stable endpoint theorem. -/
theorem ConsensusEntry.post_mem_stableDone
    {init : Config (AgentState L K)} {out : Output} {n : ℕ}
    {c final : Config (AgentState L K)}
    (h : ConsensusEntry (L := L) (K := K) init out n c)
    (hpost : Phase2OutputCleanup.Phase2Post
      (L := L) (K := K) out n final) :
    final ∈ StableDone L K init :=
  Phase2StableEndpoint.post_mem_stableDone
    (L := L) (K := K) out n init final h.verdict hpost

/-- The four outcome-aware entries used by the Phase-2 recut.  `doneT` is an
explicit constructor; it is not folded into either signed branch. -/
inductive OutcomeDispatch
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K)) : Prop
  | doneA (h : ConsensusEntry (L := L) (K := K) init .A n c)
  | doneB (h : ConsensusEntry (L := L) (K := K) init .B n c)
  | doneT (h : ConsensusEntry (L := L) (K := K) init .T n c)
  | continue3 (h : Phase2AdvanceEpidemic.Active2Concrete
      (L := L) (K := K) n c)

private theorem signs_of_branchA
    (n : ℕ) (c : Config (AgentState L K))
    (h : Phase2CarrierEpidemic.Phase2BranchPre
      (L := L) (K := K) .A n c) :
    1 ≤ Phase2AdvanceEpidemic.signCount Sign.pos c ∧
      ¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c := by
  constructor
  · rcases h.2.2 with ⟨a, ha, hcarrier⟩
    unfold Phase2AdvanceEpidemic.signCount
    apply Multiset.countP_pos_of_mem ha
    simpa [Phase2AdvanceEpidemic.carries,
      Phase2CarrierEpidemic.opinionCarrier] using hcarrier
  · intro hm
    rcases exists_carries_of_signCount_pos Sign.neg c hm with ⟨a, ha, hcarry⟩
    have hcompat := (h.2.1 a ha).2
    simp [Phase2CarrierEpidemic.opinionCompatible] at hcompat
    simp [Phase2AdvanceEpidemic.carries, hcompat] at hcarry

private theorem signs_of_branchB
    (n : ℕ) (c : Config (AgentState L K))
    (h : Phase2CarrierEpidemic.Phase2BranchPre
      (L := L) (K := K) .B n c) :
    ¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.pos c ∧
      1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c := by
  constructor
  · intro hp
    rcases exists_carries_of_signCount_pos Sign.pos c hp with ⟨a, ha, hcarry⟩
    have hcompat := (h.2.1 a ha).2
    simp [Phase2CarrierEpidemic.opinionCompatible] at hcompat
    simp [Phase2AdvanceEpidemic.carries, hcompat] at hcarry
  · rcases h.2.2 with ⟨a, ha, hcarrier⟩
    unfold Phase2AdvanceEpidemic.signCount
    apply Multiset.countP_pos_of_mem ha
    simpa [Phase2AdvanceEpidemic.carries,
      Phase2CarrierEpidemic.opinionCarrier] using hcarrier

private theorem no_signs_of_branchT
    (n : ℕ) (c : Config (AgentState L K))
    (h : Phase2CarrierEpidemic.Phase2BranchPre
      (L := L) (K := K) .T n c) :
    (¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.pos c) ∧
      ¬ 1 ≤ Phase2AdvanceEpidemic.signCount Sign.neg c := by
  constructor
  · intro hp
    rcases exists_carries_of_signCount_pos Sign.pos c hp with ⟨a, ha, hcarry⟩
    have hop := (h.2.1 a ha).2
    simp [Phase2CarrierEpidemic.opinionCompatible] at hop
    simp [Phase2AdvanceEpidemic.carries, hop, phase2OpinionT,
      hasPlusOne] at hcarry
  · intro hm
    rcases exists_carries_of_signCount_pos Sign.neg c hm with ⟨a, ha, hcarry⟩
    have hop := (h.2.1 a ha).2
    simp [Phase2CarrierEpidemic.opinionCompatible] at hop
    simp [Phase2AdvanceEpidemic.carries, hop, phase2OpinionT,
      hasMinusOne] at hcarry

/-- Closed outcome-aware dispatch from reachable pure provenance.  The A/B/T
constructors are immediately compatible with
`ConsensusEntry.post_mem_stableDone`; the mixed constructor is exactly the
precondition of the stopped first-entry epidemic. -/
theorem outcome_dispatch
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K))
    (h : PurePhase2Provenance (L := L) (K := K) init n c) :
    OutcomeDispatch (L := L) (K := K) init n c := by
  cases pure_dispatch n c h.toPurePhase2Shell with
  | branchA hpre =>
      have hs := signs_of_branchA n c hpre
      exact .doneA ⟨hpre,
        majorityVerdict_A_of_provenance init n c h hs.1 hs.2⟩
  | branchB hpre =>
      have hs := signs_of_branchB n c hpre
      exact .doneB ⟨hpre,
        majorityVerdict_B_of_provenance init n c h hs.1 hs.2⟩
  | branchT hpre =>
      have hs := no_signs_of_branchT n c hpre
      exact .doneT ⟨hpre,
        majorityVerdict_T_of_provenance init n c h hs.1 hs.2⟩
  | advance hactive => exact .continue3 hactive

/-! ## Exact initializer shell and the Phase-1 drained reference map -/

/-- Exact pointwise payload written by a successful Phase-2 initializer. -/
def ExactInitAgent (a : AgentState L K) : Prop :=
  a.phase.val = 2 ∧
    ((a.smallBias.val = 2 ∧ a.opinions.val = 1) ∨
      (a.smallBias.val = 3 ∧ a.opinions.val = 2) ∨
      (a.smallBias.val = 4 ∧ a.opinions.val = 4))

/-- Synchronous reference image of Phase-2 initialization.  This is a
provenance object, not a claim that the asynchronous chain updates the entire
population in one protocol step. -/
def phase2InitMap (c : Config (AgentState L K)) :
    Config (AgentState L K) :=
  c.map fun a =>
    phaseInit L K ⟨2, by decide⟩ {a with phase := ⟨2, by decide⟩}

/-- Exact successful-initializer surface. -/
structure ExactInitShell (n : ℕ) (c : Config (AgentState L K)) : Prop where
  card_eq : c.card = n
  wf : AdvanceNoOvershoot.Wf c
  init_payload : ∀ a ∈ c, ExactInitAgent a

theorem exactInitShell_to_pure
    (n : ℕ) (c : Config (AgentState L K))
    (h : ExactInitShell (L := L) (K := K) n c) :
    PurePhase2Shell (L := L) (K := K) n c := by
  refine ⟨h.card_eq, ?_, ?_, h.wf, ?_⟩
  · intro a ha
    exact (h.init_payload a ha).1
  · intro a ha
    rcases (h.init_payload a ha).2 with h2 | h3 | h4
    · simp [Phase2Convergence.singleSign, hasMinusOne, hasPlusOne, h2.2]
    · simp [Phase2Convergence.singleSign, hasMinusOne, hasPlusOne, h3.2]
    · simp [Phase2Convergence.singleSign, hasMinusOne, hasPlusOne, h4.2]
  · intro a ha
    rcases (h.init_payload a ha).2 with h2 | h3 | h4 <;> omega

theorem signOrigin_of_exactInitShell
    (n : ℕ) (c : Config (AgentState L K))
    (h : ExactInitShell (L := L) (K := K) n c) :
    SignOrigin (L := L) (K := K) c := by
  constructor
  · intro hp
    rcases exists_carries_of_signCount_pos Sign.pos c hp with ⟨a, ha, hcarry⟩
    refine ⟨a, ha, ?_⟩
    rcases (h.init_payload a ha).2 with h2 | h3 | h4
    · simp [Phase2AdvanceEpidemic.carries, hasPlusOne, h2.2] at hcarry
    · simp [Phase2AdvanceEpidemic.carries, hasPlusOne, h3.2] at hcarry
    · omega
  · intro hm
    rcases exists_carries_of_signCount_pos Sign.neg c hm with ⟨a, ha, hcarry⟩
    refine ⟨a, ha, ?_⟩
    rcases (h.init_payload a ha).2 with h2 | h3 | h4
    · omega
    · simp [Phase2AdvanceEpidemic.carries, hasMinusOne, h3.2] at hcarry
    · simp [Phase2AdvanceEpidemic.carries, hasMinusOne, h4.2] at hcarry

/-- A reachable exact initializer shell supplies the complete pure provenance
record, including the globally exact sign origins. -/
theorem pureProvenance_of_exactInitShell
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (h : ExactInitShell (L := L) (K := K) n c) :
    PurePhase2Provenance (L := L) (K := K) init n c :=
  { toPurePhase2Shell := exactInitShell_to_pure n c h
    valid_initial := hinit
    reachable := hreach
    sign_origin := signOrigin_of_exactInitShell n c h }

/-- Closed A/B/T/Continue3 dispatch for any reachable exact Phase-2
initializer shell. -/
theorem outcome_dispatch_of_exactInitShell
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (h : ExactInitShell (L := L) (K := K) n c) :
    OutcomeDispatch (L := L) (K := K) init n c :=
  outcome_dispatch init n c
    (pureProvenance_of_exactInitShell init n c hinit hreach h)

private theorem role_ne_mcr_of_phase1Drained
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (n : ℕ)
    (h : Phase1GapFloorEntryClosure.Phase1Drained
      (L := L) (K := K) n c) :
    ∀ a ∈ c, a.role ≠ Role.mcr := by
  intro a ha hmcr
  have hpost : ∀ b ∈ c, b.phase.val ≥ 1 := by
    intro b hb
    have hbphase := h.1.2 b hb
    omega
  rcases post_phase_zero_role_partition
      (L := L) (K := K) init c hinit hreach hpost a ha with
    hmain | hreserve | hclock | hten
  · rw [hmcr] at hmain
    cases hmain
  · rw [hmcr] at hreserve
    cases hreserve
  · rw [hmcr] at hclock
    cases hclock
  · have hphase := h.1.2 a ha
    omega

/-- A reachable drained Phase-1 endpoint has an exact, error-free synchronous
Phase-2 initializer image.  This theorem closes the direct initializer
provenance; it does not identify the image with a fixed-time asynchronous
protocol state. -/
theorem phase1Drained_phase2InitMap_exactShell
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (n : ℕ)
    (h : Phase1GapFloorEntryClosure.Phase1Drained
      (L := L) (K := K) n c) :
    ExactInitShell (L := L) (K := K) n
      (phase2InitMap (L := L) (K := K) c) := by
  have hbias := Phase1GapFloorEntryClosure.all_bias_in234_of_phase1Drained
    (L := L) (K := K) init c hinit hreach n h
  have hrole := role_ne_mcr_of_phase1Drained init c hinit hreach n h
  refine ⟨by simpa [phase2InitMap] using h.1.1, ?_, ?_⟩
  · intro a ha
    rw [phase2InitMap] at ha
    rcases Multiset.mem_map.mp ha with ⟨b, hb, rfl⟩
    have hbias' := hbias b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbias'
    rcases hbias' with h2 | h3 | h4
    · simp [AdvanceNoOvershoot.WfAgent, phaseInit, h2, hrole b hb]
    · simp [AdvanceNoOvershoot.WfAgent, phaseInit, h3, hrole b hb]
    · simp [AdvanceNoOvershoot.WfAgent, phaseInit, h4, hrole b hb]
  · intro a ha
    rw [phase2InitMap] at ha
    rcases Multiset.mem_map.mp ha with ⟨b, hb, rfl⟩
    have hbias' := hbias b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbias'
    rcases hbias' with h2 | h3 | h4
    · refine ⟨by simp [phaseInit, h2], Or.inl ⟨?_, by simp [phaseInit, h2]⟩⟩
      rw [phaseInit_smallBias_eq]
      exact h2
    · exact ⟨by simp [phaseInit, h3], Or.inr (Or.inl
        ⟨by rw [phaseInit_smallBias_eq]; exact h3,
          by simp [phaseInit, h3]⟩)⟩
    · exact ⟨by simp [phaseInit, h4], Or.inr (Or.inr
        ⟨by rw [phaseInit_smallBias_eq]; exact h4,
          by simp [phaseInit, h4]⟩)⟩

/-! ## Error and early-crossing markers -/

/-- Exact agent-level Phase-2 initializer error payload. -/
def InitErrorAgent (a : AgentState L K) : Prop :=
  a.phase.val = 10 ∧
    a.full = true ∧
    a.smallBias.val ∉ ({2, 3, 4} : Finset ℕ)

/-- A Phase-10 initializer-error seed.  This deliberately does not claim the
all-phase-10 `Phase10Ready` precondition consumed by recovery. -/
def Recovery10Entry (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∃ a ∈ c, InitErrorAgent a

theorem initErrorAgent_phaseInit_two_of_bad
    (a : AgentState L K)
    (hbad : a.smallBias.val ∉ ({2, 3, 4} : Finset ℕ)) :
    InitErrorAgent
      (phaseInit L K ⟨2, by decide⟩ {a with phase := ⟨2, by decide⟩}) := by
  refine ⟨?_, ?_⟩
  · exact phaseInit_two_phase_ten_of_bad_smallBias
      (L := L) (K := K) {a with phase := ⟨2, by decide⟩} (by simpa using hbad)
  · constructor
    · rcases a with
        ⟨input, output, phase, role, assigned, bias, smallBias,
          hour, minute, full, opinions, counter⟩
      fin_cases smallBias <;>
        simp [phaseInit, enterPhase10] at hbad ⊢
    · rw [phaseInit_smallBias_eq]
      simpa using hbad

/-- A state has crossed Phase 2, but is not being identified with the exact
first-entry payload. -/
def PastPhase2Entry (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∃ a ∈ c, 3 ≤ a.phase.val

/-- Missing producer map for a generic already-crossed state.

The existing exact consumer is `Phase23FirstEntry`; a state that has continued
to phases 4--10 can instead be accepted only if it is already in `StableDone`.
No theorem currently turns arbitrary `PastPhase2Entry` into that disjunction. -/
def PastPhase2EntryFirstOrStable
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  PastPhase2Entry (L := L) (K := K) n c →
    Phase2AdvanceEpidemic.Phase23FirstEntry
        (L := L) (K := K) n c ∨
      c ∈ StableDone L K init

/-- Recovery-entry map kept separate from the error marker.

The present Phase-10 work consumes `Phase10Ready`, which requires an
all-phase-10 `S1/S0/Tie1plus` state.  A single initializer-error seed is not
that surface; `Recovery10EntryReachable` supplies the deterministic epidemic
bridge. -/
def Recovery10ReachesReady
    (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Recovery10Entry (L := L) (K := K) n c →
    ∃ c10, (NonuniformMajority L K).Reachable c c10 ∧
      Phase10Drop.Phase10Ready (L := L) (K := K) n c10

/-- Exact target of the asynchronous Phase-1-to-2 dispatcher.

The four-way pure result is one branch.  Initializer error, exact first Phase-3
entry, and already-stable termination remain separate constructors, so none can
be silently coerced to another consumer's precondition. -/
inductive EntryDispatch
    (init : Config (AgentState L K)) (n : ℕ)
    (c : Config (AgentState L K)) : Prop
  | pure (h : OutcomeDispatch (L := L) (K := K) init n c)
  | recovery10 (h : Recovery10Entry (L := L) (K := K) n c)
  | phase3First (h : Phase2AdvanceEpidemic.Phase23FirstEntry
      (L := L) (K := K) n c)
  | terminal (h : c ∈ StableDone L K init)

/-- Minimal producer obligation for a concrete asynchronous entry surface.

The caller supplies the actual fixed-time/support predicate `EntrySurface`.
This file does not pretend that the synchronous reference image is the real
kernel state, or that arbitrary overshoot is an exact first-entry state. -/
def EntrySurfaceDispatches
    (init : Config (AgentState L K)) (n : ℕ)
    (EntrySurface : Config (AgentState L K) → Prop) : Prop :=
  ∀ c, EntrySurface c →
    EntryDispatch (L := L) (K := K) init n c

#print axioms pure_dispatch
#print axioms majorityVerdict_A_of_provenance
#print axioms majorityVerdict_B_of_provenance
#print axioms majorityVerdict_T_of_provenance
#print axioms ConsensusEntry.post_mem_stableDone
#print axioms outcome_dispatch
#print axioms exactInitShell_to_pure
#print axioms signOrigin_of_exactInitShell
#print axioms pureProvenance_of_exactInitShell
#print axioms outcome_dispatch_of_exactInitShell
#print axioms phase1Drained_phase2InitMap_exactShell
#print axioms initErrorAgent_phaseInit_two_of_bad

end Phase2EntryDispatcher
end Ripple.PopulationProtocol.ExactMajority
