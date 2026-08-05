/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionReactionExp
import Tri.Lemma16CountedPath

/-!
# A joint physical and directional-reaction path for Lemma 17

The carrier keeps the genuine physical reveal path and its all-active
exposure counter, while a second coordinate records the two productive
active-reaction directions.  That second coordinate freezes at the first
active-gap barrier, even while the physical coordinate continues to its
activation checkpoint.

Both marginals are exact on reachable states.  An exact deterministic ledger
then decomposes the stopped active gap into the newly revealed immutable-label
gap and twice the productive-reaction count difference.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The genuine physical reveal path, its all-active exposure counter, and
the productive-reaction trace stopped at the active-gap barrier. -/
structure Lemma17CountedPathState (n : ℕ) where
  counted : Lemma16CountedPathState n
  reaction : InfectionReactionTraceState n
  reactionRevealed : List (Fin n)
  reactionXCount : ℕ
  reactionYCount : ℕ

def lemma17CountedPathInitial
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Lemma17CountedPathState n where
  counted := lemma16CountedPathInitial s
  reaction := ⟨s.coarse, 0, 0⟩
  reactionRevealed := []
  reactionXCount := 0
  reactionYCount := 0

/-- A physical record always advances the reveal path and all-active
counter.  The reaction coordinate freezes once its target or gap barrier has
been reached. -/
noncomputable def Lemma17CountedPathState.afterRecord
    {n : ℕ} (A G : ℕ)
    (q : Lemma17CountedPathState n)
    (r : InfectionRevealRecord q.counted.path.current) :
    Lemma17CountedPathState n where
  counted := q.counted.afterRecord r
  reaction :=
    if InfectionReactionTraceStop A G q.reaction then
      q.reaction
    else
      q.reaction.afterEvent r.event
  reactionRevealed :=
    if InfectionReactionTraceStop A G q.reaction then
      q.reactionRevealed
    else
      q.reactionRevealed ++ r.revealedIds
  reactionXCount :=
    if InfectionReactionTraceStop A G q.reaction then
      q.reactionXCount
    else
      q.reactionXCount +
        infectionRevealWordXCount
          q.counted.path.current.inactive.initialLabel
          r.revealedIds
  reactionYCount :=
    if InfectionReactionTraceStop A G q.reaction then
      q.reactionYCount
    else
      q.reactionYCount +
        infectionRevealWordYCount
          q.counted.path.current.inactive.initialLabel
          r.revealedIds

/-- The physical coordinate stops at its first `k` newly activated
identities; the reaction coordinate may have frozen earlier at the gap
barrier. -/
noncomputable def lemma17CountedPathStep
    (n : ℕ) (h3 : 3 ≤ n) (k A G : ℕ) :
    Lemma17CountedPathState n →
      PMF (Lemma17CountedPathState n)
  | q =>
      if InfectionRevealPhysicalFirstKReached
          k q.counted.path then
        PMF.pure q
      else
        (infectionRevealRecordPMF n h3
          q.counted.path.current).map
            (q.afterRecord A G)

def lemma17CountedPathToLemma16
    {n : ℕ} (q : Lemma17CountedPathState n) :
    Lemma16CountedPathState n :=
  q.counted

def lemma17CountedPathToReaction
    {n : ℕ} (q : Lemma17CountedPathState n) :
    InfectionReactionTraceState n :=
  q.reaction

/-- Reachable states retain the Lemma 16 physical-path invariant.  Unless
the reaction coordinate has already stopped, it agrees with the current
physical coarse state. -/
def Lemma17CountedPathInv
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (k A G : ℕ) (q : Lemma17CountedPathState n) : Prop :=
  Lemma16CountedPathInv s k q.counted ∧
    (InfectionReactionTraceStop A G q.reaction ∨
      q.reaction.current =
        q.counted.path.current.coarse) ∧
    ((A ≤ q.reaction.current.1.active →
        q.reaction.current =
          q.counted.path.current.coarse) ∧
      q.reaction.typeOneCount +
          q.reaction.typeTwoCount ≤
        q.counted.allActiveCount)

theorem lemma17CountedPathInitial_inv
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (k A G : ℕ) :
    Lemma17CountedPathInv s k A G
      (lemma17CountedPathInitial s) := by
  constructor
  · constructor
    · rfl
    · simp [lemma17CountedPathInitial,
        lemma16CountedPathInitial,
        infectionRevealPhysicalPathInitial]
  · constructor
    · right
      rfl
    · constructor
      · intro _
        rfl
      · simp [lemma17CountedPathInitial,
          lemma16CountedPathInitial]

/-- Forgetting the reaction coordinate recovers exactly the genuine
first-`k` counted physical step. -/
theorem lemma17CountedPathStep_map_lemma16
    (n : ℕ) (h3 : 3 ≤ n) (k A G : ℕ)
    (q : Lemma17CountedPathState n) :
    (lemma17CountedPathStep n h3 k A G q).map
        lemma17CountedPathToLemma16 =
      lemma16CountedPathStep n h3 k q.counted := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached
        k q.counted.path
  · unfold lemma17CountedPathStep
      lemma16CountedPathStep
    rw [if_pos hreach, if_pos hreach, PMF.pure_map]
    rfl
  · unfold lemma17CountedPathStep
      lemma16CountedPathStep
    rw [if_neg hreach, if_neg hreach, PMF.map_comp]
    rfl

/-- The physical/reaction agreement invariant survives one supported joint
step. -/
theorem lemma17CountedPathStep_inv_closed
    (n : ℕ) (h3 : 3 ≤ n) (k A G : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (q z : Lemma17CountedPathState n)
    (hq : Lemma17CountedPathInv s k A G q)
    (hz : lemma17CountedPathStep n h3 k A G q z ≠ 0) :
    Lemma17CountedPathInv s k A G z := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached
        k q.counted.path
  · have hzq : z = q := by
      unfold lemma17CountedPathStep at hz
      rw [if_pos hreach] at hz
      by_contra hne
      simp [PMF.pure_apply, hne] at hz
    simpa [hzq] using hq
  · unfold lemma17CountedPathStep at hz
    rw [if_neg hreach] at hz
    have hzmem :
        z ∈
          ((infectionRevealRecordPMF n h3
            q.counted.path.current).map
              (q.afterRecord A G)).support :=
      hz
    rw [PMF.support_map] at hzmem
    rcases hzmem with ⟨r, hr, rfl⟩
    constructor
    · constructor
      · exact hq.1.1
      · simp only [Lemma17CountedPathState.afterRecord,
          Lemma16CountedPathState.afterRecord,
          InfectionRevealPhysicalPathState.afterRecord,
          List.length_append]
        have hlt :
            q.counted.path.revealed.length < k := by
          simpa [InfectionRevealPhysicalFirstKReached]
            using hreach
        have hbatch : r.revealedIds.length ≤ 2 := by
          rw [r.revealedIds_length]
          exact
            InfectionEvent.realizedActivationInc_le_two
              q.counted.path.current.coarse.1 r.event
        omega
    · by_cases hstop :
          InfectionReactionTraceStop A G q.reaction
      · refine ⟨?_, ?_, ?_⟩
        · left
          simpa [Lemma17CountedPathState.afterRecord,
            hstop] using hstop
        · intro htarget
          have htargetBefore :
              A ≤ q.reaction.current.1.active := by
            simpa [Lemma17CountedPathState.afterRecord,
              hstop] using htarget
          have halign :
              q.reaction.current =
                q.counted.path.current.coarse :=
            hq.2.2.1 htargetBefore
          have hanchor :
              q.counted.path.anchor.coarse.1.active =
                s.coarse.1.active := by
            rw [hq.1.1]
          have hactiveLedger :=
            q.counted.path.hactiveLedger
          have htargetPhysical :
              A ≤ q.counted.path.current.coarse.1.active := by
            rw [← halign]
            exact htargetBefore
          have hreached :
              InfectionRevealPhysicalFirstKReached
                k q.counted.path := by
            simp only [
              InfectionRevealPhysicalFirstKReached]
            omega
          exact False.elim (hreach hreached)
        · simp only [Lemma17CountedPathState.afterRecord,
            hstop, if_true,
            Lemma16CountedPathState.afterRecord]
          have hcount := hq.2.2.2
          omega
      · have halign :
            q.reaction.current =
              q.counted.path.current.coarse := by
          rcases hq.2.1 with hstopped | halign
          · exact False.elim (hstop hstopped)
          · exact halign
        have hafterAlign :
            (q.afterRecord A G r).reaction.current =
              (q.afterRecord A G r).counted.path.current.coarse := by
          simp only [Lemma17CountedPathState.afterRecord,
            hstop, if_false,
            InfectionReactionTraceState.afterEvent,
            Lemma16CountedPathState.afterRecord,
            InfectionRevealPhysicalPathState.afterRecord]
          have hforget :
              r.after.coarse =
                InfectionEvent.nextState
                  q.counted.path.current.coarse r.event := by
            simpa [infectionRevealPhysicalForget] using
              r.after_forget
          rw [halign]
          exact hforget.symm
        refine ⟨Or.inr hafterAlign, ?_, ?_⟩
        · intro _
          exact hafterAlign
        · have hproductive :=
            InfectionEvent.typeOneInc_add_typeTwoInc
              r.event
          have hinc :=
            InfectionEvent.productiveActiveInc_le_allActiveInc
              r.event
          have hcount := hq.2.2.2
          simp only [Lemma17CountedPathState.afterRecord,
            hstop, if_false,
            InfectionReactionTraceState.afterEvent,
            Lemma16CountedPathState.afterRecord]
          omega

/-- At the physical checkpoint, the reaction coordinate has necessarily
stopped as well. -/
theorem lemma17_reactionStop_of_physicalReached
    (n k A G : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (q : Lemma17CountedPathState n)
    (hq : Lemma17CountedPathInv s k A G q)
    (hreach :
      InfectionRevealPhysicalFirstKReached
        k q.counted.path) :
    InfectionReactionTraceStop A G q.reaction := by
  rcases hq.2.1 with hstop | halign
  · exact hstop
  · left
    rw [halign]
    have hanchor :
        q.counted.path.anchor.coarse.1.active =
          s.coarse.1.active := by
      rw [hq.1.1]
    have hledger := q.counted.path.hactiveLedger
    simp only [InfectionRevealPhysicalFirstKReached] at hreach
    omega

/-- On the reachable invariant, projecting one joint step to the reaction
coordinate gives exactly the stopped reaction trace. -/
theorem lemma17CountedPathStep_map_reaction_on_inv
    (n : ℕ) (h3 : 3 ≤ n) (k A G : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (q : Lemma17CountedPathState n)
    (hq : Lemma17CountedPathInv s k A G q) :
    (lemma17CountedPathStep n h3 k A G q).map
        lemma17CountedPathToReaction =
      infectionReactionTraceStep n h3 A G q.reaction := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached
        k q.counted.path
  · have hstop :=
      lemma17_reactionStop_of_physicalReached
        n k A G s hanchorActive q hq hreach
    unfold lemma17CountedPathStep
      infectionReactionTraceStep
    rw [if_pos hreach, if_pos hstop, PMF.pure_map]
    rfl
  · by_cases hstop :
        InfectionReactionTraceStop A G q.reaction
    · unfold lemma17CountedPathStep
        infectionReactionTraceStep
      rw [if_neg hreach, if_pos hstop, PMF.map_comp]
      have hfun :
          lemma17CountedPathToReaction ∘
              q.afterRecord A G =
            Function.const _ q.reaction := by
        funext r
        simp [lemma17CountedPathToReaction,
          Lemma17CountedPathState.afterRecord, hstop]
      rw [hfun, PMF.map_const]
    · have halign :
          q.reaction.current =
            q.counted.path.current.coarse := by
        rcases hq.2.1 with hstopped | halign
        · exact False.elim (hstop hstopped)
        · exact halign
      unfold lemma17CountedPathStep
        infectionReactionTraceStep
      rw [if_neg hreach, if_neg hstop, PMF.map_comp]
      have hfun :
          lemma17CountedPathToReaction ∘
              q.afterRecord A G =
            q.reaction.afterEvent ∘
              InfectionRevealRecord.event := by
        funext r
        simp [lemma17CountedPathToReaction,
          Lemma17CountedPathState.afterRecord, hstop]
      rw [hfun]
      calc
        (infectionRevealRecordPMF n h3
            q.counted.path.current).map
              (q.reaction.afterEvent ∘
                InfectionRevealRecord.event) =
          ((infectionRevealRecordPMF n h3
            q.counted.path.current).map
              InfectionRevealRecord.event).map
                q.reaction.afterEvent := by
                  rw [PMF.map_comp]
        _ =
          (infectionEventPMF
            q.counted.path.current.coarse.1 _).map
              q.reaction.afterEvent := by
                rw [infectionRevealRecordPMF_map_event]
        _ =
          (infectionEventPMF q.reaction.current.1 _).map
            q.reaction.afterEvent := by
              congr 2
              exact congrArg
                (fun u : InfectionState n => u.1)
                halign.symm

/-- The Lemma 16 marginal remains exact at every horizon. -/
theorem lemma17CountedPath_iter_map_lemma16
    (n : ℕ) (h3 : 3 ≤ n) (k A G T : ℕ)
    (q : Lemma17CountedPathState n) :
    (iter (lemma17CountedPathStep n h3 k A G) T q).map
        lemma17CountedPathToLemma16 =
      iter (lemma16CountedPathStep n h3 k) T q.counted := by
  exact
    iter_map_of_step_map
      (lemma17CountedPathStep n h3 k A G)
      (lemma16CountedPathStep n h3 k)
      lemma17CountedPathToLemma16
      (lemma17CountedPathStep_map_lemma16
        n h3 k A G)
      T q

/-- The stopped reaction-trace marginal remains exact at every horizon
started from the joint initial state. -/
theorem lemma17CountedPath_iter_map_reaction
    (n : ℕ) (h3 : 3 ≤ n) (k A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A) :
    (iter (lemma17CountedPathStep n h3 k A G) T
        (lemma17CountedPathInitial s)).map
          lemma17CountedPathToReaction =
      iter (infectionReactionTraceStep n h3 A G) T
        ⟨s.coarse, 0, 0⟩ := by
  exact
    iter_map_of_step_map_on_support_invariant
      (lemma17CountedPathStep n h3 k A G)
      (infectionReactionTraceStep n h3 A G)
      lemma17CountedPathToReaction
      (Lemma17CountedPathInv s k A G)
      (fun q hq z hz =>
        lemma17CountedPathStep_inv_closed
          n h3 k A G s hanchorActive q z hq hz)
      (lemma17CountedPathStep_map_reaction_on_inv
        n h3 k A G s hanchorActive)
      T (lemma17CountedPathInitial s)
      (lemma17CountedPathInitial_inv s k A G)

/-- Every supported terminal state retains the joint path invariant. -/
theorem lemma17CountedPath_iter_inv
    (n : ℕ) (h3 : 3 ≤ n) (k A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (z : Lemma17CountedPathState n)
    (hz :
      iter (lemma17CountedPathStep n h3 k A G) T
        (lemma17CountedPathInitial s) z ≠ 0) :
    Lemma17CountedPathInv s k A G z := by
  exact
    iter_support_closed
      (lemma17CountedPathStep n h3 k A G)
      (Lemma17CountedPathInv s k A G)
      (fun q hq z hz =>
        lemma17CountedPathStep_inv_closed
          n h3 k A G s hanchorActive q z hq hz)
      T (lemma17CountedPathInitial s) z
      (lemma17CountedPathInitial_inv s k A G)
      hz

/-- Exact coarse arithmetic behind the directional active-gap ledger.  Type
(1) converts one active `Y` to `X`; type (2) converts one active `X` to `Y`.
Activation labels are recorded separately by `batchX` and `batchY`. -/
theorem InfectionEvent.gap_charge_exact_of_inactive_ledgers
    {n : ℕ} (s t : InfectionState n)
    (e : InfectionEvent) (batchX batchY : ℕ)
    (he : InfectionEvent.weight s.1 e ≠ 0)
    (ht : t = InfectionEvent.nextState s e)
    (hx : batchX + t.1.ix = s.1.ix)
    (hy : batchY + t.1.iy = s.1.iy) :
    t.1.ay + s.1.ax + batchX +
          2 * e.typeOneInc =
      t.1.ax + s.1.ay + batchY +
          2 * e.typeTwoInc := by
  subst t
  rw [InfectionEvent.nextState, dif_neg he] at hx hy ⊢
  cases e with
    | activeXXX =>
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega
    | activeXXY =>
        have hay : s.1.ay ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega
    | activeXYY =>
        have hax : s.1.ax ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).1
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega
    | activeYYY =>
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega
    | activateOneX =>
        have hix : s.1.ix ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega
    | activateOneY =>
        have hiy : s.1.iy ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega
    | activateTwoXX =>
        have hchoose : Nat.choose s.1.ix 2 ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        have hix : 2 ≤ s.1.ix :=
          Nat.choose_ne_zero_iff.mp hchoose
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega
    | activateTwoXY =>
        have hmul :
            s.1.active * s.1.ix * s.1.iy ≠ 0 := by
          simpa only [InfectionEvent.weight] using he
        have hix : s.1.ix ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp
            (Nat.mul_ne_zero_iff.mp hmul).1).2
        have hiy : s.1.iy ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp hmul).2
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega
    | activateTwoYY =>
        have hchoose : Nat.choose s.1.iy 2 ≠ 0 :=
          (Nat.mul_ne_zero_iff.mp (by
            simpa only [InfectionEvent.weight] using he)).2
        have hiy : 2 ≤ s.1.iy :=
          Nat.choose_ne_zero_iff.mp hchoose
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega
    | inactiveOnly =>
        simp [InfectionEvent.next,
          InfectionEvent.typeOneInc,
          InfectionEvent.typeTwoInc] at hx hy ⊢
        omega

/-- One genuine physical record satisfies the exact directional gap ledger. -/
theorem InfectionRevealRecord.gap_charge_exact
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s)
    (he : InfectionEvent.weight s.coarse.1 r.event ≠ 0) :
    r.after.coarse.1.ay + s.coarse.1.ax +
          infectionRevealWordXCount
            s.inactive.initialLabel r.revealedIds +
          2 * r.event.typeOneInc =
      r.after.coarse.1.ax + s.coarse.1.ay +
          infectionRevealWordYCount
            s.inactive.initialLabel r.revealedIds +
          2 * r.event.typeTwoInc := by
  apply InfectionEvent.gap_charge_exact_of_inactive_ledgers
      s.coarse r.after.coarse r.event
      (infectionRevealWordXCount
        s.inactive.initialLabel r.revealedIds)
      (infectionRevealWordYCount
        s.inactive.initialLabel r.revealedIds)
      he
  · simpa [infectionRevealPhysicalForget] using
      r.after_forget
  · simpa [r.after.hinactiveX, s.hinactiveX] using
      r.revealedX_card_add_after
  · simpa [r.after.hinactiveY, s.hinactiveY] using
      r.revealedY_card_add_after

/-- Exact active-gap identity at the (possibly early) reaction stop. -/
def Lemma17ReactionGapLedger
    {n : ℕ} (q : Lemma17CountedPathState n) : Prop :=
  q.reaction.current.1.ay +
        q.counted.path.anchor.coarse.1.ax +
        q.reactionXCount +
        2 * q.reaction.typeOneCount =
    q.reaction.current.1.ax +
        q.counted.path.anchor.coarse.1.ay +
        q.reactionYCount +
        2 * q.reaction.typeTwoCount

theorem lemma17CountedPathInitial_gapLedger
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Lemma17ReactionGapLedger
      (lemma17CountedPathInitial s) := by
  simpa [Lemma17ReactionGapLedger,
      lemma17CountedPathInitial,
      lemma16CountedPathInitial,
      infectionRevealPhysicalPathInitial] using
    Nat.add_comm s.coarse.1.ay s.coarse.1.ax

/-- Applying one record preserves the exact stopped reaction ledger. -/
theorem Lemma17ReactionGapLedger.afterRecord
    {n : ℕ} (k A G : ℕ)
    (s : InfectionRevealPhysicalState n)
    (q : Lemma17CountedPathState n)
    (r : InfectionRevealRecord q.counted.path.current)
    (he :
      InfectionEvent.weight
        q.counted.path.current.coarse.1 r.event ≠ 0)
    (hinv : Lemma17CountedPathInv s k A G q)
    (hledger : Lemma17ReactionGapLedger q) :
    Lemma17ReactionGapLedger (q.afterRecord A G r) := by
  by_cases hstop :
      InfectionReactionTraceStop A G q.reaction
  · simpa [Lemma17ReactionGapLedger,
      Lemma17CountedPathState.afterRecord, hstop]
      using hledger
  · have halign :
        q.reaction.current =
          q.counted.path.current.coarse := by
      rcases hinv.2.1 with hstopped | halign
      · exact False.elim (hstop hstopped)
      · exact halign
    have hcharge := r.gap_charge_exact he
    rw [q.counted.path.hinitialLabel] at hcharge
    unfold Lemma17ReactionGapLedger at hledger ⊢
    simp only [Lemma17CountedPathState.afterRecord,
      hstop, if_false,
      InfectionReactionTraceState.afterEvent,
      Lemma16CountedPathState.afterRecord,
      InfectionRevealPhysicalPathState.afterRecord]
    rw [q.counted.path.hinitialLabel]
    have hforget :
        r.after.coarse =
          InfectionEvent.nextState
            q.counted.path.current.coarse r.event := by
      simpa [infectionRevealPhysicalForget] using
        r.after_forget
    rw [halign] at hledger
    rw [halign, ← hforget]
    omega

/-- The exact directional ledger is closed on support of the joint step. -/
theorem lemma17CountedPathStep_gapLedger_closed
    (n : ℕ) (h3 : 3 ≤ n) (k A G : ℕ)
    (s : InfectionRevealPhysicalState n)
    (q z : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A G q)
    (hledger : Lemma17ReactionGapLedger q)
    (hz : lemma17CountedPathStep n h3 k A G q z ≠ 0) :
    Lemma17ReactionGapLedger z := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached
        k q.counted.path
  · have hzq : z = q := by
      unfold lemma17CountedPathStep at hz
      rw [if_pos hreach] at hz
      by_contra hne
      simp [PMF.pure_apply, hne] at hz
    simpa [hzq] using hledger
  · unfold lemma17CountedPathStep at hz
    rw [if_neg hreach] at hz
    have hzmem :
        z ∈
          ((infectionRevealRecordPMF n h3
            q.counted.path.current).map
              (q.afterRecord A G)).support :=
      hz
    rw [PMF.support_map] at hzmem
    rcases hzmem with ⟨r, hr, rfl⟩
    have hevent :
        r.event ∈
          ((infectionRevealRecordPMF n h3
            q.counted.path.current).map
              InfectionRevealRecord.event).support := by
      rw [PMF.support_map]
      exact ⟨r, hr, rfl⟩
    rw [infectionRevealRecordPMF_map_event] at hevent
    have heweight :
        InfectionEvent.weight
          q.counted.path.current.coarse.1 r.event ≠ 0 := by
      intro he
      apply hevent
      simp [infectionEventPMF_apply, he]
    exact
      hledger.afterRecord k A G s q r
        heweight hinv

/-- Every supported terminal state satisfies the exact reaction-stop gap
identity. -/
theorem lemma17CountedPath_iter_gapLedger
    (n : ℕ) (h3 : 3 ≤ n) (k A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (z : Lemma17CountedPathState n)
    (hz :
      iter (lemma17CountedPathStep n h3 k A G) T
        (lemma17CountedPathInitial s) z ≠ 0) :
    Lemma17ReactionGapLedger z := by
  have hboth :
      Lemma17CountedPathInv s k A G z ∧
        Lemma17ReactionGapLedger z :=
    iter_support_closed
      (lemma17CountedPathStep n h3 k A G)
      (fun q =>
        Lemma17CountedPathInv s k A G q ∧
          Lemma17ReactionGapLedger q)
      (fun q hq z hz =>
        ⟨lemma17CountedPathStep_inv_closed
            n h3 k A G s hanchorActive q z hq.1 hz,
          lemma17CountedPathStep_gapLedger_closed
            n h3 k A G s q z hq.1 hq.2 hz⟩)
      T (lemma17CountedPathInitial s) z
      ⟨lemma17CountedPathInitial_inv s k A G,
        lemma17CountedPathInitial_gapLedger s⟩
      hz
  exact hboth.2

end

end Tri

#print axioms Tri.lemma17CountedPathStep_map_lemma16
#print axioms Tri.lemma17CountedPathStep_inv_closed
#print axioms Tri.lemma17CountedPathStep_map_reaction_on_inv
#print axioms Tri.lemma17CountedPath_iter_map_lemma16
#print axioms Tri.lemma17CountedPath_iter_map_reaction
#print axioms Tri.lemma17CountedPath_iter_inv
#print axioms Tri.InfectionEvent.gap_charge_exact_of_inactive_ledgers
#print axioms Tri.InfectionRevealRecord.gap_charge_exact
#print axioms Tri.Lemma17ReactionGapLedger.afterRecord
#print axioms Tri.lemma17CountedPathStep_gapLedger_closed
#print axioms Tri.lemma17CountedPath_iter_gapLedger
