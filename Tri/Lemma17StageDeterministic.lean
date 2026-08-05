/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17JointTails

/-!
# Deterministic closure of a Lemma 17 doubling stage

The exact gap ledger turns the incoming active gap, newly revealed immutable
label gap, and productive-reaction direction gap into one additive barrier
budget.  Outside the label, all-active-exposure, and conditional directional
exceptional events, the reaction stop cannot occur at that barrier and its
coarse coordinate therefore still agrees with the genuine physical path.
-/

namespace Tri

noncomputable section

/-- The immutable labels seen before the reaction barrier have adverse
`Y-X` excess larger than `D`. -/
def Lemma17LabelBad
    {n : ℕ} (D : ℕ)
    (q : Lemma17CountedPathState n) : Prop :=
  q.reactionXCount + D < q.reactionYCount

noncomputable instance lemma17LabelBadDecidable
    {n : ℕ} (D : ℕ) :
    DecidablePred (@Lemma17LabelBad n D) :=
  Classical.decPred _

/-- The exact ledger converts the three additive budgets into an active-gap
bound at the reaction stop. -/
theorem lemma17Reaction_gap_le
    {n : ℕ}
    (s : InfectionRevealPhysicalState n)
    (k A G D₀ Dlabel M : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A G q)
    (hledger : Lemma17ReactionGapLedger q)
    (hstart :
      s.coarse.1.ay ≤ s.coarse.1.ax + D₀)
    (hlabel :
      q.reactionYCount ≤
        q.reactionXCount + Dlabel)
    (hdirection :
      q.reaction.typeTwoCount ≤
        q.reaction.typeOneCount + M) :
    q.reaction.current.1.ay ≤
      q.reaction.current.1.ax +
        D₀ + Dlabel + 2 * M := by
  unfold Lemma17ReactionGapLedger at hledger
  rw [hinv.1.1] at hledger
  omega

/-- If the three budgets fit inside `G`, the stopped reaction coordinate
cannot lie beyond the active-gap barrier. -/
theorem lemma17Reaction_not_gapStopped
    {n : ℕ}
    (s : InfectionRevealPhysicalState n)
    (k A G D₀ Dlabel M : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A G q)
    (hledger : Lemma17ReactionGapLedger q)
    (hstart :
      s.coarse.1.ay ≤ s.coarse.1.ax + D₀)
    (hlabel :
      q.reactionYCount ≤
        q.reactionXCount + Dlabel)
    (hdirection :
      q.reaction.typeTwoCount ≤
        q.reaction.typeOneCount + M)
    (hbudget : D₀ + Dlabel + 2 * M ≤ G) :
    ¬ q.reaction.current.1.ax + G <
        q.reaction.current.1.ay := by
  have hgap :=
    lemma17Reaction_gap_le s k A G
      D₀ Dlabel M q hinv hledger
      hstart hlabel hdirection
  omega

/-- A reachable reaction coordinate that is not beyond the gap barrier still
agrees with the genuine current physical state. -/
theorem lemma17Reaction_align_of_not_gapStopped
    {n : ℕ}
    (s : InfectionRevealPhysicalState n)
    (k A G : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A G q)
    (hgap :
      ¬ q.reaction.current.1.ax + G <
        q.reaction.current.1.ay) :
    q.reaction.current =
      q.counted.path.current.coarse := by
  rcases hinv.2.1 with hstop | halign
  · rcases hstop with htarget | hbarrier
    · exact hinv.2.2.1 htarget
    · exact False.elim (hgap hbarrier)
  · exact halign

/-- Outside the three exceptional events, the reaction exposure is bounded,
its directional excess is within budget, and the genuine physical state
remains below the gap barrier. -/
theorem lemma17CountedPath_gap_good_of_no_bad
    {n : ℕ}
    (s : InfectionRevealPhysicalState n)
    (k A G D₀ Dlabel M H : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A G q)
    (hledger : Lemma17ReactionGapLedger q)
    (hstart :
      s.coarse.1.ay ≤ s.coarse.1.ax + D₀)
    (hbudget : D₀ + Dlabel + 2 * M ≤ G)
    (hlabelBad : ¬ Lemma17LabelBad Dlabel q)
    (hallActiveBad :
      ¬ Lemma17AllActiveBad (H + 1) q)
    (hreactionBad :
      ¬ Lemma17ReactionBad H M q) :
    q.counted.path.current.coarse.1.ay ≤
        q.counted.path.current.coarse.1.ax + G ∧
      q.reaction.current =
        q.counted.path.current.coarse := by
  have hlabel :
      q.reactionYCount ≤
        q.reactionXCount + Dlabel := by
    unfold Lemma17LabelBad at hlabelBad
    omega
  have hallActive :
      q.counted.allActiveCount ≤ H := by
    unfold Lemma17AllActiveBad at hallActiveBad
    omega
  have hexposure :
      q.reaction.typeOneCount +
          q.reaction.typeTwoCount ≤ H :=
    hinv.2.2.2.trans hallActive
  have hdirection :
      q.reaction.typeTwoCount ≤
        q.reaction.typeOneCount + M := by
    unfold Lemma17ReactionBad at hreactionBad
    omega
  have hnotGap :=
    lemma17Reaction_not_gapStopped
      s k A G D₀ Dlabel M q hinv hledger
      hstart hlabel hdirection hbudget
  have halign :=
    lemma17Reaction_align_of_not_gapStopped
      s k A G q hinv hnotGap
  constructor
  · rw [← halign]
    omega
  · exact halign

end

end Tri

#print axioms Tri.lemma17Reaction_gap_le
#print axioms Tri.lemma17Reaction_not_gapStopped
#print axioms Tri.lemma17Reaction_align_of_not_gapStopped
#print axioms Tri.lemma17CountedPath_gap_good_of_no_bad
