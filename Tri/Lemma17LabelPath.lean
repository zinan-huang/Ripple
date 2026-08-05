/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17StageAssembly

/-!
# The stopped Lemma 17 label word is a genuine physical prefix

The joint path caches the immutable labels revealed before its reaction
coordinate stops.  This file proves that cache is exactly a prefix of the
genuine physical reveal word, including after the physical coordinate
continues beyond an early gap stop.
-/

namespace Tri

noncomputable section

/-- The reaction label word is a prefix of the genuine physical reveal word.
Its cached label counts are exact; while the reaction coordinate is live, the
prefix is the whole physical word. -/
def Lemma17ReactionLabelInv
    {n : ℕ} (A G : ℕ)
    (q : Lemma17CountedPathState n) : Prop :=
  (∃ suffix,
      q.counted.path.revealed =
        q.reactionRevealed ++ suffix) ∧
    q.reactionXCount =
      infectionRevealWordXCount
        q.counted.path.anchor.inactive.initialLabel
        q.reactionRevealed ∧
    q.reactionYCount =
      infectionRevealWordYCount
        q.counted.path.anchor.inactive.initialLabel
        q.reactionRevealed ∧
    (¬ InfectionReactionTraceStop A G q.reaction →
      q.reactionRevealed =
        q.counted.path.revealed)

theorem lemma17CountedPathInitial_labelInv
    {n : ℕ} (A G : ℕ)
    (s : InfectionRevealPhysicalState n) :
    Lemma17ReactionLabelInv A G
      (lemma17CountedPathInitial s) := by
  refine ⟨⟨[], by simp [lemma17CountedPathInitial,
      lemma16CountedPathInitial,
      infectionRevealPhysicalPathInitial]⟩,
    ?_, ?_, ?_⟩
  · simp [lemma17CountedPathInitial,
      infectionRevealWordXCount]
  · simp [lemma17CountedPathInitial,
      infectionRevealWordYCount]
  · intro _
    rfl

/-- One physical record preserves the exact stopped label-prefix invariant. -/
theorem Lemma17ReactionLabelInv.afterRecord
    {n : ℕ} (A G : ℕ)
    (q : Lemma17CountedPathState n)
    (r : InfectionRevealRecord q.counted.path.current)
    (hq : Lemma17ReactionLabelInv A G q) :
    Lemma17ReactionLabelInv A G
      (q.afterRecord A G r) := by
  rcases hq.1 with ⟨suffix, hsuffix⟩
  by_cases hstop :
      InfectionReactionTraceStop A G q.reaction
  · refine ⟨⟨suffix ++ r.revealedIds, ?_⟩,
      ?_, ?_, ?_⟩
    · simp only [Lemma17CountedPathState.afterRecord,
        Lemma16CountedPathState.afterRecord,
        InfectionRevealPhysicalPathState.afterRecord,
        hstop, if_true]
      rw [hsuffix, List.append_assoc]
    · simpa [Lemma17CountedPathState.afterRecord,
        hstop] using hq.2.1
    · simpa [Lemma17CountedPathState.afterRecord,
        hstop] using hq.2.2.1
    · intro hlive
      exact False.elim (hlive (by
        simpa [Lemma17CountedPathState.afterRecord,
          hstop] using hstop))
  · have hfull :
        q.reactionRevealed =
          q.counted.path.revealed :=
      hq.2.2.2 hstop
    have hbatchDisjoint :
        Disjoint q.counted.path.revealed.toFinset
          r.revealedIds.toFinset :=
      q.counted.path.hdisjoint.mono_right
        r.revealedIds_toFinset_subset
    have hX :=
      infectionRevealWordXCount_append_of_disjoint
        q.counted.path.anchor.inactive.initialLabel
        q.counted.path.revealed r.revealedIds
        hbatchDisjoint
    have hY :=
      infectionRevealWordYCount_append_of_disjoint
        q.counted.path.anchor.inactive.initialLabel
        q.counted.path.revealed r.revealedIds
        hbatchDisjoint
    refine ⟨⟨[], ?_⟩, ?_, ?_, ?_⟩
    · simp [Lemma17CountedPathState.afterRecord,
        Lemma16CountedPathState.afterRecord,
        InfectionRevealPhysicalPathState.afterRecord,
        hstop, hfull]
    · simp only [Lemma17CountedPathState.afterRecord,
        Lemma16CountedPathState.afterRecord,
        InfectionRevealPhysicalPathState.afterRecord,
        hstop, if_false]
      rw [hfull, hX, ← q.counted.path.hinitialLabel]
      have hqX := hq.2.1
      rw [hfull, ← q.counted.path.hinitialLabel] at hqX
      exact congrArg
        (fun t =>
          t + infectionRevealWordXCount
            q.counted.path.current.inactive.initialLabel
            r.revealedIds)
        hqX
    · simp only [Lemma17CountedPathState.afterRecord,
        Lemma16CountedPathState.afterRecord,
        InfectionRevealPhysicalPathState.afterRecord,
        hstop, if_false]
      rw [hfull, hY, ← q.counted.path.hinitialLabel]
      have hqY := hq.2.2.1
      rw [hfull, ← q.counted.path.hinitialLabel] at hqY
      exact congrArg
        (fun t =>
          t + infectionRevealWordYCount
            q.counted.path.current.inactive.initialLabel
            r.revealedIds)
        hqY
    · intro _
      simp [Lemma17CountedPathState.afterRecord,
        Lemma16CountedPathState.afterRecord,
        InfectionRevealPhysicalPathState.afterRecord,
        hstop, hfull]

/-- The label-prefix invariant is closed on support of one joint step. -/
theorem lemma17CountedPathStep_labelInv_closed
    (n : ℕ) (h3 : 3 ≤ n) (k A G : ℕ)
    (q z : Lemma17CountedPathState n)
    (hq : Lemma17ReactionLabelInv A G q)
    (hz : lemma17CountedPathStep n h3 k A G q z ≠ 0) :
    Lemma17ReactionLabelInv A G z := by
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
    exact hq.afterRecord A G q r

/-- Every supported joint terminal state has an exact reaction label prefix. -/
theorem lemma17CountedPath_iter_labelInv
    (n : ℕ) (h3 : 3 ≤ n) (k A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (z : Lemma17CountedPathState n)
    (hz :
      iter (lemma17CountedPathStep n h3 k A G) T
        (lemma17CountedPathInitial s) z ≠ 0) :
    Lemma17ReactionLabelInv A G z := by
  exact
    iter_support_closed
      (lemma17CountedPathStep n h3 k A G)
      (Lemma17ReactionLabelInv A G)
      (fun q hq z hz =>
        lemma17CountedPathStep_labelInv_closed
          n h3 k A G q z hq hz)
      T (lemma17CountedPathInitial s) z
      (lemma17CountedPathInitial_labelInv A G s)
      hz

/-- The stopped reaction word records exactly the activations accumulated by
the reaction coordinate. -/
def Lemma17ReactionLengthInv
    {n : ℕ} (q : Lemma17CountedPathState n) : Prop :=
  q.counted.path.anchor.coarse.1.active +
      q.reactionRevealed.length =
    q.reaction.current.1.active

theorem lemma17CountedPathInitial_reactionLengthInv
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    Lemma17ReactionLengthInv
      (lemma17CountedPathInitial s) := by
  simp [Lemma17ReactionLengthInv,
    lemma17CountedPathInitial,
    lemma16CountedPathInitial,
    infectionRevealPhysicalPathInitial]

/-- One reachable joint step preserves the exact reaction-word length. -/
theorem lemma17CountedPathStep_reactionLengthInv_closed
    (n : ℕ) (h3 : 3 ≤ n) (k A G : ℕ)
    (s : InfectionRevealPhysicalState n)
    (q z : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A G q)
    (hlength : Lemma17ReactionLengthInv q)
    (hz : lemma17CountedPathStep n h3 k A G q z ≠ 0) :
    Lemma17ReactionLengthInv z := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached
        k q.counted.path
  · have hzq : z = q := by
      unfold lemma17CountedPathStep at hz
      rw [if_pos hreach] at hz
      by_contra hne
      simp [PMF.pure_apply, hne] at hz
    simpa [hzq] using hlength
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
    by_cases hstop :
        InfectionReactionTraceStop A G q.reaction
    · simpa [Lemma17ReactionLengthInv,
        Lemma17CountedPathState.afterRecord, hstop]
        using hlength
    · have halign :
          q.reaction.current =
            q.counted.path.current.coarse := by
        rcases hinv.2.1 with hstopped | halign
        · exact False.elim (hstop hstopped)
        · exact halign
      have hactive :=
        InfectionEvent.nextState_active_eq_add_realizedActivationInc
          q.reaction.current r.event
      have hinc :
          r.event.realizedActivationInc
              q.reaction.current.1 =
            r.event.realizedActivationInc
              q.counted.path.current.coarse.1 := by
        rw [halign]
      unfold Lemma17ReactionLengthInv at hlength ⊢
      simp only [Lemma17CountedPathState.afterRecord,
        hstop, if_false,
        InfectionReactionTraceState.afterEvent,
        Lemma16CountedPathState.afterRecord,
        InfectionRevealPhysicalPathState.afterRecord,
        List.length_append]
      rw [r.revealedIds_length]
      rw [← hinc]
      omega

/-- Every supported joint terminal state has the exact stopped
reaction-word length. -/
theorem lemma17CountedPath_iter_reactionLengthInv
    (n : ℕ) (h3 : 3 ≤ n) (k A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (z : Lemma17CountedPathState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hz :
      iter (lemma17CountedPathStep n h3 k A G) T
        (lemma17CountedPathInitial s) z ≠ 0) :
    Lemma17ReactionLengthInv z := by
  have hboth :
      Lemma17CountedPathInv s k A G z ∧
        Lemma17ReactionLengthInv z := by
    exact
      iter_support_closed
        (lemma17CountedPathStep n h3 k A G)
        (fun q =>
          Lemma17CountedPathInv s k A G q ∧
            Lemma17ReactionLengthInv q)
        (fun q hq z hzStep => by
          exact ⟨
            lemma17CountedPathStep_inv_closed
              n h3 k A G s hanchorActive q z
              hq.1 hzStep,
            lemma17CountedPathStep_reactionLengthInv_closed
              n h3 k A G s q z hq.1 hq.2 hzStep⟩)
        T (lemma17CountedPathInitial s) z
        ⟨lemma17CountedPathInitial_inv s k A G,
          lemma17CountedPathInitial_reactionLengthInv s⟩
        hz
  exact hboth.2

/-- If the stopped reaction coordinate agrees with the physical endpoint,
its stopped reveal word is the whole physical reveal word. -/
theorem lemma17ReactionRevealed_eq_physical_of_align
    {n : ℕ} {A G : ℕ}
    (q : Lemma17CountedPathState n)
    (hlabel : Lemma17ReactionLabelInv A G q)
    (hlength : Lemma17ReactionLengthInv q)
    (halign :
      q.reaction.current =
        q.counted.path.current.coarse) :
    q.reactionRevealed =
      q.counted.path.revealed := by
  rcases hlabel.1 with ⟨suffix, hsuffix⟩
  have hphysical := q.counted.path.hactiveLedger
  unfold Lemma17ReactionLengthInv at hlength
  have hsameLength :
      q.reactionRevealed.length =
        q.counted.path.revealed.length := by
    rw [← halign] at hphysical
    omega
  have hsuffixLength : suffix.length = 0 := by
    rw [hsuffix, List.length_append] at hsameLength
    omega
  have hsuffixNil : suffix = [] :=
    List.length_eq_zero_iff.mp hsuffixLength
  rw [hsuffix, hsuffixNil, List.append_nil]

/-- Some prefix of the genuine physical reveal word has adverse immutable
label excess larger than `D`. -/
def Lemma17PhysicalLabelBad
    {n : ℕ} (D : ℕ)
    (q : Lemma17CountedPathState n) : Prop :=
  ∃ j, j ≤ q.counted.path.revealed.length ∧
    infectionRevealWordXCount
          q.counted.path.anchor.inactive.initialLabel
          (q.counted.path.revealed.take j) + D <
      infectionRevealWordYCount
        q.counted.path.anchor.inactive.initialLabel
        (q.counted.path.revealed.take j)

noncomputable instance lemma17PhysicalLabelBadDecidable
    {n : ℕ} (D : ℕ) :
    DecidablePred (@Lemma17PhysicalLabelBad n D) :=
  Classical.decPred _

/-- A bad cached reaction-label prefix is a genuine physical prefix event. -/
theorem lemma17LabelBad_implies_physical
    {n : ℕ} (A G D : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17ReactionLabelInv A G q)
    (hbad : Lemma17LabelBad D q) :
    Lemma17PhysicalLabelBad D q := by
  rcases hinv.1 with ⟨suffix, hsuffix⟩
  let j := q.reactionRevealed.length
  have hj :
      j ≤ q.counted.path.revealed.length := by
    dsimp only [j]
    rw [hsuffix, List.length_append]
    omega
  have htake :
      q.counted.path.revealed.take j =
        q.reactionRevealed := by
    dsimp only [j]
    rw [hsuffix]
    simpa using
      (List.take_append_of_le_length
        (l₂ := suffix)
        (show q.reactionRevealed.length ≤
          q.reactionRevealed.length from le_rfl))
  refine ⟨j, hj, ?_⟩
  unfold Lemma17LabelBad at hbad
  rw [htake, ← hinv.2.1, ← hinv.2.2.1]
  exact hbad

end

end Tri

#print axioms Tri.Lemma17ReactionLabelInv.afterRecord
#print axioms Tri.lemma17CountedPathStep_labelInv_closed
#print axioms Tri.lemma17CountedPath_iter_labelInv
#print axioms Tri.lemma17CountedPathStep_reactionLengthInv_closed
#print axioms Tri.lemma17CountedPath_iter_reactionLengthInv
#print axioms Tri.lemma17ReactionRevealed_eq_physical_of_align
#print axioms Tri.lemma17LabelBad_implies_physical
