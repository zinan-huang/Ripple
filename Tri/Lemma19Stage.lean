/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17StageAssembly
import Tri.Lemma17LabelPath

/-!
# Positive-gap stages for Lemma 19

After Lemma 18 the active population has a positive `X-Y` gap.  During a
later activation stage, immutable labels and productive active reactions are
the only two terms that can erode this reserve.  The exact joint-path ledger
therefore gives a subtraction-free budget

`targetGap + labelAdverse + 2 * reactionAdverse ≤ startGap`.

The reaction coordinate is stopped at loss of the active `X` majority.  The
same budget proves that this stop cannot occur outside the charged label and
reaction events.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A positive-gap activation stage reaches its active target while retaining
the requested active `X-Y` gap. -/
def Lemma19StageGood
    {n : ℕ} (A targetGap : ℕ)
    (q : Lemma17CountedPathState n) : Prop :=
  A ≤ q.counted.path.current.coarse.1.active ∧
    q.counted.path.current.coarse.1.ay + targetGap ≤
      q.counted.path.current.coarse.1.ax

noncomputable instance lemma19StageGoodDecidable
    {n : ℕ} (A targetGap : ℕ) :
    DecidablePred (@Lemma19StageGood n A targetGap) :=
  Classical.decPred _

/-- The exact ledger preserves a positive gap after charging the immutable
label and adverse-reaction budgets. -/
theorem lemma19Reaction_gap_ge
    {n : ℕ}
    (s : InfectionRevealPhysicalState n)
    (k A Dstart Dlabel M targetGap : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A 0 q)
    (hledger : Lemma17ReactionGapLedger q)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hlabel :
      q.reactionYCount ≤
        q.reactionXCount + Dlabel)
    (hdirection :
      q.reaction.typeTwoCount ≤
        q.reaction.typeOneCount + M)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart) :
    q.reaction.current.1.ay + targetGap ≤
      q.reaction.current.1.ax := by
  unfold Lemma17ReactionGapLedger at hledger
  rw [hinv.1.1] at hledger
  omega

/-- Under the positive-gap budget the reaction coordinate cannot have stopped
because the active `Y` population overtook the active `X` population. -/
theorem lemma19Reaction_not_majorityStopped
    {n : ℕ}
    (s : InfectionRevealPhysicalState n)
    (k A Dstart Dlabel M targetGap : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A 0 q)
    (hledger : Lemma17ReactionGapLedger q)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hlabel :
      q.reactionYCount ≤
        q.reactionXCount + Dlabel)
    (hdirection :
      q.reaction.typeTwoCount ≤
        q.reaction.typeOneCount + M)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart) :
    ¬ q.reaction.current.1.ax <
        q.reaction.current.1.ay := by
  have hgap :=
    lemma19Reaction_gap_ge
      s k A Dstart Dlabel M targetGap q
      hinv hledger hstart hlabel hdirection hbudget
  omega

/-- Outside the label, exposure, and direction exceptional events, the
reaction coordinate remains aligned with the genuine physical path and the
positive gap survives. -/
theorem lemma19CountedPath_gap_good_of_no_bad
    {n : ℕ}
    (s : InfectionRevealPhysicalState n)
    (k A Dstart Dlabel M targetGap H : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A 0 q)
    (hledger : Lemma17ReactionGapLedger q)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hlabelBad : ¬ Lemma17LabelBad Dlabel q)
    (hallActiveBad :
      ¬ Lemma17AllActiveBad (H + 1) q)
    (hreactionBad :
      ¬ Lemma17ReactionBad H M q) :
    q.counted.path.current.coarse.1.ay + targetGap ≤
        q.counted.path.current.coarse.1.ax ∧
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
    by_contra hnot
    exact hreactionBad ⟨hexposure, by omega⟩
  have hnotGap :=
    lemma19Reaction_not_majorityStopped
      s k A Dstart Dlabel M targetGap q
      hinv hledger hstart hlabel hdirection hbudget
  have halign :=
    lemma17Reaction_align_of_not_gapStopped
      s k A 0 q hinv (by simpa using hnotGap)
  constructor
  · rw [← halign]
    exact
      lemma19Reaction_gap_ge
        s k A Dstart Dlabel M targetGap q
        hinv hledger hstart hlabel hdirection hbudget
  · exact halign

/-- Generic one-horizon assembly for a positive-gap Lemma 19 stage. -/
theorem lemma19CountedPath_stage
    (n : ℕ) (h3 : 3 ≤ n)
    (k A T H Dstart Dlabel M targetGap : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (εClock εLabel εActive εReaction : ℝ≥0∞)
    (hclock :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (fun z =>
            A ≤ z.counted.path.current.coarse.1.active)
        ≤ εClock)
    (hlabel :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17LabelBad Dlabel z)
        ≤ εLabel)
    (hactive :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17AllActiveBad (H + 1) z)
        ≤ εActive)
    (hreaction :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17ReactionBad H M z)
        ≤ εReaction) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A 0) T
          (lemma17CountedPathInitial s))
        (Lemma19StageGood A targetGap)
      ≤
    ((εClock + εLabel) + εActive) + εReaction := by
  let K := lemma17CountedPathStep n h3 k A 0
  let q₀ := lemma17CountedPathInitial s
  let μ := iter K T q₀
  let Reached : Lemma17CountedPathState n → Prop :=
    fun z => A ≤ z.counted.path.current.coarse.1.active
  let LabelGood : Lemma17CountedPathState n → Prop :=
    fun z => ¬ Lemma17LabelBad Dlabel z
  let ActiveGood : Lemma17CountedPathState n → Prop :=
    fun z => ¬ Lemma17AllActiveBad (H + 1) z
  let ReactionGood : Lemma17CountedPathState n → Prop :=
    fun z => ¬ Lemma17ReactionBad H M z
  let Certificate : Lemma17CountedPathState n → Prop :=
    fun z =>
      ((Reached z ∧ LabelGood z) ∧ ActiveGood z) ∧
        ReactionGood z
  have hcertificate :
      ∀ z, μ z ≠ 0 → Certificate z →
        Lemma19StageGood A targetGap z := by
    intro z hzμ hzcert
    rcases hzcert with
      ⟨⟨⟨hzReached, hzLabel⟩, hzActive⟩,
        hzReaction⟩
    have hinv :
        Lemma17CountedPathInv s k A 0 z :=
      lemma17CountedPath_iter_inv
        n h3 k A 0 T s hanchorActive z
        (by simpa [μ, K, q₀] using hzμ)
    have hledger :
        Lemma17ReactionGapLedger z :=
      lemma17CountedPath_iter_gapLedger
        n h3 k A 0 T s hanchorActive z
        (by simpa [μ, K, q₀] using hzμ)
    have hgap :=
      lemma19CountedPath_gap_good_of_no_bad
        s k A Dstart Dlabel M targetGap H z
        hinv hledger hstart hbudget
        (by simpa [LabelGood] using hzLabel)
        (by simpa [ActiveGood] using hzActive)
        (by simpa [ReactionGood] using hzReaction)
    exact ⟨hzReached, hgap.1⟩
  have htarget :
      terminalFailureMass μ
          (Lemma19StageGood A targetGap) ≤
        terminalFailureMass μ Certificate := by
    unfold terminalFailureMass
    exact ENNReal.tsum_le_tsum fun z => by
      by_cases hzμ : μ z = 0
      · simp [hzμ]
      · by_cases hzCert : Certificate z
        · have hzTarget :=
            hcertificate z hzμ hzCert
          simp [hzCert, hzTarget]
        · by_cases hzTarget :
              Lemma19StageGood A targetGap z
          · simp [hzCert, hzTarget]
          · simp [hzCert, hzTarget]
  have hcertBound :
      terminalFailureMass μ Certificate ≤
        ((εClock + εLabel) + εActive) +
          εReaction := by
    calc
      terminalFailureMass μ Certificate
          ≤ terminalFailureMass μ
                (fun z =>
                  (Reached z ∧ LabelGood z) ∧
                    ActiveGood z) +
              terminalFailureMass μ ReactionGood :=
        terminalFailureMass_inter_le
          μ
          (fun z =>
            (Reached z ∧ LabelGood z) ∧ ActiveGood z)
          ReactionGood
      _ ≤
          (terminalFailureMass μ
                (fun z => Reached z ∧ LabelGood z) +
              terminalFailureMass μ ActiveGood) +
            terminalFailureMass μ ReactionGood := by
        exact add_le_add
          (terminalFailureMass_inter_le
            μ (fun z => Reached z ∧ LabelGood z)
            ActiveGood)
          le_rfl
      _ ≤
          ((terminalFailureMass μ Reached +
              terminalFailureMass μ LabelGood) +
            terminalFailureMass μ ActiveGood) +
          terminalFailureMass μ ReactionGood := by
        exact add_le_add
          (add_le_add
            (terminalFailureMass_inter_le
              μ Reached LabelGood)
            le_rfl)
          le_rfl
      _ ≤
          ((εClock + εLabel) + εActive) +
            εReaction := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (by simpa [μ, K, q₀, Reached] using hclock)
              (by simpa [μ, K, q₀, LabelGood] using hlabel))
            (by simpa [μ, K, q₀, ActiveGood] using hactive))
          (by simpa [μ, K, q₀, ReactionGood] using hreaction)
  exact htarget.trans hcertBound

end

end Tri

#print axioms Tri.lemma19Reaction_gap_ge
#print axioms Tri.lemma19Reaction_not_majorityStopped
#print axioms Tri.lemma19CountedPath_gap_good_of_no_bad
#print axioms Tri.lemma19CountedPath_stage
