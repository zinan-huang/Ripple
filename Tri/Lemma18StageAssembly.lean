/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18Deterministic
import Tri.Lemma17StageAssembly
import Tri.Lemma17LabelPath

/-!
# Assembly of the decisive Lemma 18 stage

The physical counted path is stopped at the tentative active `Y`-gap guard.
A prefix label bound and a guarded reaction-direction bound prove that this
stop cannot occur.  At the completed stage, the strong `X` excess of the new
block and the exact `48 = 14 + 32 + 2` ledger give the target active gap.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The decisive stage has reached its active target with the requested
positive `X-Y` gap. -/
def Lemma18StageGood
    {n : ℕ} (A targetGap : ℕ)
    (q : Lemma17CountedPathState n) : Prop :=
  A ≤ q.counted.path.current.coarse.1.active ∧
    q.counted.path.current.coarse.1.ay + targetGap ≤
      q.counted.path.current.coarse.1.ax

noncomputable instance lemma18StageGoodDecidable
    {n : ℕ} (A targetGap : ℕ) :
    DecidablePred (@Lemma18StageGood n A targetGap) :=
  Classical.decPred _

/-- Failure of the decisive block to supply its required immutable-label
`X` excess. -/
def Lemma18EndBlockBad
    {n : ℕ} (newBlockExcess : ℕ)
    (q : Lemma17CountedPathState n) : Prop :=
  infectionRevealWordXCount
      q.counted.path.anchor.inactive.initialLabel
      q.counted.path.revealed <
    infectionRevealWordYCount
        q.counted.path.anchor.inactive.initialLabel
        q.counted.path.revealed +
      newBlockExcess

noncomputable instance lemma18EndBlockBadDecidable
    {n : ℕ} (newBlockExcess : ℕ) :
    DecidablePred (@Lemma18EndBlockBad n newBlockExcess) :=
  Classical.decPred _

/-- Generic decisive-stage assembly on one physical horizon.  The five
probabilistic estimates are explicit inputs; all event containment and exact
gap arithmetic are discharged here. -/
theorem lemma18CountedPath_stage
    (n : ℕ) (h3 : 3 ≤ n)
    (k A G T H prefixD guardM : ℕ)
    (M : Lemma18Margins)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hprior :
      s.coarse.1.ay ≤
        s.coarse.1.ax + M.preExistingAdverse)
    (hguardBudget :
      M.preExistingAdverse + prefixD + 2 * guardM ≤ G)
    (hguardErosion :
      2 * guardM ≤ M.reactionErosion)
    (εClock εPrefix εEnd εActive εReaction : ℝ≥0∞)
    (hclock :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z =>
            A ≤ z.counted.path.current.coarse.1.active)
        ≤ εClock)
    (hprefix :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17LabelBad prefixD z)
        ≤ εPrefix)
    (hend :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z =>
            A ≤ z.counted.path.current.coarse.1.active →
              ¬ Lemma18EndBlockBad M.newBlockExcess z)
        ≤ εEnd)
    (hactive :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17AllActiveBad (H + 1) z)
        ≤ εActive)
    (hreaction :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17ReactionBad H guardM z)
        ≤ εReaction) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s))
        (Lemma18StageGood A M.targetGap)
      ≤
    (((εClock + εPrefix) + εEnd) + εActive) +
      εReaction := by
  let K := lemma17CountedPathStep n h3 k A G
  let q₀ := lemma17CountedPathInitial s
  let μ := iter K T q₀
  let Reached : Lemma17CountedPathState n → Prop :=
    fun z => A ≤ z.counted.path.current.coarse.1.active
  let PrefixGood : Lemma17CountedPathState n → Prop :=
    fun z => ¬ Lemma17LabelBad prefixD z
  let EndGood : Lemma17CountedPathState n → Prop :=
    fun z =>
      Reached z →
        ¬ Lemma18EndBlockBad M.newBlockExcess z
  let ActiveGood : Lemma17CountedPathState n → Prop :=
    fun z => ¬ Lemma17AllActiveBad (H + 1) z
  let ReactionGood : Lemma17CountedPathState n → Prop :=
    fun z => ¬ Lemma17ReactionBad H guardM z
  let Certificate : Lemma17CountedPathState n → Prop :=
    fun z =>
      ((((Reached z ∧ PrefixGood z) ∧ EndGood z) ∧
        ActiveGood z) ∧ ReactionGood z)
  have hcertificate :
      ∀ z, μ z ≠ 0 → Certificate z →
        Lemma18StageGood A M.targetGap z := by
    intro z hzμ hzcert
    rcases hzcert with
      ⟨⟨⟨⟨hzReached, hzPrefix⟩, hzEnd⟩,
        hzActive⟩, hzReaction⟩
    have hinv :
        Lemma17CountedPathInv s k A G z := by
      exact
        lemma17CountedPath_iter_inv
          n h3 k A G T s hanchorActive z
          (by simpa [μ, K, q₀] using hzμ)
    have hledger :
        Lemma17ReactionGapLedger z := by
      exact
        lemma17CountedPath_iter_gapLedger
          n h3 k A G T s hanchorActive z
          (by simpa [μ, K, q₀] using hzμ)
    have hallActive :
        z.counted.allActiveCount ≤ H := by
      unfold ActiveGood Lemma17AllActiveBad at hzActive
      omega
    have hexposure :
        z.reaction.typeOneCount +
            z.reaction.typeTwoCount ≤ H :=
      hinv.2.2.2.trans hallActive
    have hdirection :
        z.reaction.typeTwoCount ≤
          z.reaction.typeOneCount + guardM := by
      by_contra hnot
      apply hzReaction
      unfold Lemma17ReactionBad
      exact ⟨hexposure, by omega⟩
    have hprefixGood :
        z.reactionYCount ≤
          z.reactionXCount + prefixD := by
      unfold PrefixGood Lemma17LabelBad at hzPrefix
      omega
    have hnotGap :=
      lemma17Reaction_not_gapStopped
        s k A G M.preExistingAdverse prefixD guardM
        z hinv hledger hprior hprefixGood hdirection
        hguardBudget
    have halign :=
      lemma17Reaction_align_of_not_gapStopped
        s k A G z hinv hnotGap
    have hlabelInv :
        Lemma17ReactionLabelInv A G z := by
      exact
        lemma17CountedPath_iter_labelInv
          n h3 k A G T s z
          (by simpa [μ, K, q₀] using hzμ)
    have hlengthInv :
        Lemma17ReactionLengthInv z := by
      exact
        lemma17CountedPath_iter_reactionLengthInv
          n h3 k A G T s z hanchorActive
          (by simpa [μ, K, q₀] using hzμ)
    have hword :
        z.reactionRevealed =
          z.counted.path.revealed :=
      lemma17ReactionRevealed_eq_physical_of_align
        z hlabelInv hlengthInv halign
    have hX :
        z.reactionXCount =
          infectionRevealWordXCount
            z.counted.path.anchor.inactive.initialLabel
            z.counted.path.revealed := by
      rw [← hword]
      exact hlabelInv.2.1
    have hY :
        z.reactionYCount =
          infectionRevealWordYCount
            z.counted.path.anchor.inactive.initialLabel
            z.counted.path.revealed := by
      rw [← hword]
      exact hlabelInv.2.2.1
    have hnew :
        z.reactionYCount + M.newBlockExcess ≤
          z.reactionXCount := by
      have hzEnd' := hzEnd hzReached
      unfold Lemma18EndBlockBad at hzEnd'
      rw [hX, hY]
      omega
    have herosion :
        2 * z.reaction.typeTwoCount ≤
          2 * z.reaction.typeOneCount +
            M.reactionErosion := by
      omega
    refine ⟨hzReached, ?_⟩
    exact
      lemma18CountedPath_target_of_margins
        M s z hledger halign hprior hnew herosion
        hinv.1.1
  have htarget :
      terminalFailureMass μ
          (Lemma18StageGood A M.targetGap) ≤
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
              Lemma18StageGood A M.targetGap z
          · simp [hzCert, hzTarget]
          · simp [hzCert, hzTarget]
  have hcertBound :
      terminalFailureMass μ Certificate ≤
        (((εClock + εPrefix) + εEnd) + εActive) +
          εReaction := by
    calc
      terminalFailureMass μ Certificate
          ≤ terminalFailureMass μ
                (fun z =>
                  ((Reached z ∧ PrefixGood z) ∧ EndGood z) ∧
                    ActiveGood z) +
              terminalFailureMass μ ReactionGood :=
        terminalFailureMass_inter_le
          μ
          (fun z =>
            ((Reached z ∧ PrefixGood z) ∧ EndGood z) ∧
              ActiveGood z)
          ReactionGood
      _ ≤
          (terminalFailureMass μ
                (fun z =>
                  (Reached z ∧ PrefixGood z) ∧ EndGood z) +
              terminalFailureMass μ ActiveGood) +
            terminalFailureMass μ ReactionGood := by
        exact add_le_add
          (terminalFailureMass_inter_le
            μ
            (fun z =>
              (Reached z ∧ PrefixGood z) ∧ EndGood z)
            ActiveGood)
          le_rfl
      _ ≤
          ((terminalFailureMass μ
                (fun z => Reached z ∧ PrefixGood z) +
              terminalFailureMass μ EndGood) +
            terminalFailureMass μ ActiveGood) +
          terminalFailureMass μ ReactionGood := by
        exact add_le_add
          (add_le_add
            (terminalFailureMass_inter_le
              μ (fun z => Reached z ∧ PrefixGood z) EndGood)
            le_rfl)
          le_rfl
      _ ≤
          (((terminalFailureMass μ Reached +
              terminalFailureMass μ PrefixGood) +
            terminalFailureMass μ EndGood) +
          terminalFailureMass μ ActiveGood) +
          terminalFailureMass μ ReactionGood := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (terminalFailureMass_inter_le
                μ Reached PrefixGood)
              le_rfl)
            le_rfl)
          le_rfl
      _ ≤
          (((εClock + εPrefix) + εEnd) + εActive) +
            εReaction := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (add_le_add
                (by simpa [μ, K, q₀, Reached] using hclock)
                (by simpa [μ, K, q₀, PrefixGood] using hprefix))
              (by simpa [μ, K, q₀, EndGood] using hend))
            (by simpa [μ, K, q₀, ActiveGood] using hactive))
          (by simpa [μ, K, q₀, ReactionGood] using hreaction)
  exact htarget.trans hcertBound

/-- Paper-margin specialization.  The guard uses only `7D` adverse reaction
excess, leaving the endpoint's exact `32D` erosion budget intact. -/
theorem lemma18CountedPath_paper_stage
    (n : ℕ) (h3 : 3 ≤ n)
    (k A T H D : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hprior :
      s.coarse.1.ay ≤ s.coarse.1.ax + 14 * D)
    (εClock εPrefix εEnd εActive εReaction : ℝ≥0∞)
    (hclock :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A (30 * D)) T
            (lemma17CountedPathInitial s))
          (fun z =>
            A ≤ z.counted.path.current.coarse.1.active)
        ≤ εClock)
    (hprefix :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A (30 * D)) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17LabelBad D z)
        ≤ εPrefix)
    (hend :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A (30 * D)) T
            (lemma17CountedPathInitial s))
          (fun z =>
            A ≤ z.counted.path.current.coarse.1.active →
              ¬ Lemma18EndBlockBad (48 * D) z)
        ≤ εEnd)
    (hactive :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A (30 * D)) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17AllActiveBad (H + 1) z)
        ≤ εActive)
    (hreaction :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A (30 * D)) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17ReactionBad H (7 * D) z)
        ≤ εReaction) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A (30 * D)) T
          (lemma17CountedPathInitial s))
        (Lemma18StageGood A (2 * D))
      ≤
    (((εClock + εPrefix) + εEnd) + εActive) +
      εReaction := by
  apply
    lemma18CountedPath_stage
      n h3 k A (30 * D) T H D (7 * D)
      (paperLemma18Margins D) s hanchorActive
      (by simpa [paperLemma18Margins] using hprior)
      (by simp [paperLemma18Margins]; omega)
      (by simp [paperLemma18Margins]; omega)
      εClock εPrefix εEnd εActive εReaction
      hclock hprefix
  · simpa [paperLemma18Margins] using hend
  · exact hactive
  · exact hreaction

end

end Tri

#print axioms Tri.lemma18CountedPath_stage
#print axioms Tri.lemma18CountedPath_paper_stage
