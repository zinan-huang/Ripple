/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17StageDeterministic

/-!
# Deterministic closure for Lemma 18

The decisive infection stage has no deterministic constant slack:

`48 D = 14 D + 32 D + 2 D`.

The four margins are therefore kept as independent fields and meet only in
the closing inequality below.  The exact physical ledger already records the
new immutable labels and both productive reaction directions.
-/

namespace Tri

noncomputable section

/-- The four additive margins in the decisive Lemma 18 stage. -/
structure Lemma18Margins where
  newBlockExcess : ℕ
  preExistingAdverse : ℕ
  reactionErosion : ℕ
  targetGap : ℕ
  closes :
    preExistingAdverse + reactionErosion + targetGap ≤
      newBlockExcess

/-- The paper's exact `48 - 14 - 32 = 2` margin allocation. -/
def paperLemma18Margins (D : ℕ) : Lemma18Margins where
  newBlockExcess := 48 * D
  preExistingAdverse := 14 * D
  reactionErosion := 32 * D
  targetGap := 2 * D
  closes := by omega

/-- Exact additive gap closure.  Reaction erosion is measured in active-gap
units, so one adverse reaction contributes two units. -/
theorem lemma18_gap_ledger
    (M : Lemma18Margins)
    (x₀ y₀ newX newY r₁ r₂ x y : ℕ)
    (hprior :
      y₀ ≤ x₀ + M.preExistingAdverse)
    (hnew :
      newY + M.newBlockExcess ≤ newX)
    (hreaction :
      2 * r₂ ≤ 2 * r₁ + M.reactionErosion)
    (hledger :
      y + x₀ + newX + 2 * r₁ =
        x + y₀ + newY + 2 * r₂) :
    y + M.targetGap ≤ x := by
  have hclose := M.closes
  omega

/-- The exact counted-path ledger closes a decisive stage once the incoming
gap, newly activated block, and reaction-erosion certificates are present. -/
theorem lemma18CountedPath_target_of_margins
    {n : ℕ}
    (M : Lemma18Margins)
    (s : InfectionRevealPhysicalState n)
    (q : Lemma17CountedPathState n)
    (hledger : Lemma17ReactionGapLedger q)
    (halign :
      q.reaction.current =
        q.counted.path.current.coarse)
    (hprior :
      s.coarse.1.ay ≤
        s.coarse.1.ax + M.preExistingAdverse)
    (hnew :
      q.reactionYCount + M.newBlockExcess ≤
        q.reactionXCount)
    (hreaction :
      2 * q.reaction.typeTwoCount ≤
        2 * q.reaction.typeOneCount +
          M.reactionErosion)
    (hanchor :
      q.counted.path.anchor = s) :
    q.counted.path.current.coarse.1.ay +
        M.targetGap ≤
      q.counted.path.current.coarse.1.ax := by
  unfold Lemma17ReactionGapLedger at hledger
  rw [halign, hanchor] at hledger
  exact
    lemma18_gap_ledger M
      s.coarse.1.ax s.coarse.1.ay
      q.reactionXCount q.reactionYCount
      q.reaction.typeOneCount
      q.reaction.typeTwoCount
      q.counted.path.current.coarse.1.ax
      q.counted.path.current.coarse.1.ay
      hprior hnew hreaction hledger

/-- Paper constants specialized on the counted physical path. -/
theorem lemma18CountedPath_paper_target
    {n : ℕ} (D : ℕ)
    (s : InfectionRevealPhysicalState n)
    (q : Lemma17CountedPathState n)
    (hledger : Lemma17ReactionGapLedger q)
    (halign :
      q.reaction.current =
        q.counted.path.current.coarse)
    (hprior :
      s.coarse.1.ay ≤
        s.coarse.1.ax + 14 * D)
    (hnew :
      q.reactionYCount + 48 * D ≤
        q.reactionXCount)
    (hreaction :
      2 * q.reaction.typeTwoCount ≤
        2 * q.reaction.typeOneCount + 32 * D)
    (hanchor :
      q.counted.path.anchor = s) :
    q.counted.path.current.coarse.1.ay + 2 * D ≤
      q.counted.path.current.coarse.1.ax := by
  simpa [paperLemma18Margins] using
    lemma18CountedPath_target_of_margins
      (paperLemma18Margins D) s q hledger halign
      hprior hnew hreaction hanchor

end

end Tri

#print axioms Tri.lemma18_gap_ledger
#print axioms Tri.lemma18CountedPath_target_of_margins
#print axioms Tri.lemma18CountedPath_paper_target
