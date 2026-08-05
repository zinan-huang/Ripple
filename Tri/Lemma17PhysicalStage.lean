/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17PaperStage

/-!
# The paper-scale Lemma 17 stage on physical endpoints

This module resets the stage-local counters, runs the joint construction, and
projects its endpoint back to the identity-refined physical infection state.
It also converts the `19` barrier into the next stage's `14` envelope.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Reset the joint counters, run one stopped Lemma 17 stage, and retain its
physical endpoint. -/
noncomputable def lemma17PhysicalStageKernel
    (n : ℕ) (h3 : 3 ≤ n)
    (k A G T : ℕ) :
    InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun s =>
    (iter (lemma17CountedPathStep n h3 k A G) T
      (lemma17CountedPathInitial s)).map
        (fun q => q.counted.path.current)

/-- Physical endpoint form of `Lemma17StageGood`. -/
def Lemma17PhysicalStageGood
    {n : ℕ} (A G : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  A ≤ s.coarse.1.active ∧
    s.coarse.1.ay ≤ s.coarse.1.ax + G

noncomputable instance lemma17PhysicalStageGoodDecidable
    {n : ℕ} (A G : ℕ) :
    DecidablePred (@Lemma17PhysicalStageGood n A G) :=
  Classical.decPred _

theorem lemma17PhysicalStage_paper
    (n q rho a k u nu R B A cStar r : ℕ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarter : 4 * a ≤ n)
    (hquarterLabel : 4 * (k + 1) ≤ nu + 1)
    (hAupper : A ≤ 2 * a)
    (hAle : A ≤ n)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (hrho : 1 ≤ rho)
    (hbias : 38 * cStar * rho ≤ a)
    (hactiveScale : 76 * cStar * r ≤ a)
    (hmean : A ^ 3 ≤ r * n ^ 2)
    (hqa : q * (k + 1) ≤ rho ^ 2)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hmajor : R ≤ B)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hstartGap :
      s.coarse.1.ay ≤
        s.coarse.1.ax + 14 * cStar * rho)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (lemma17PhysicalStageKernel n h3 k A
          (19 * cStar * rho) (cStar * n) s)
        (Lemma17PhysicalStageGood A
          (19 * cStar * rho))
      ≤ lemma17StageError a q cStar rho r := by
  unfold lemma17PhysicalStageKernel
  rw [terminalFailureMass_map]
  simpa [Lemma17PhysicalStageGood,
      Lemma17StageGood] using
      lemma17CountedPath_paper_stage
        n q rho a k u nu R B A cStar r
        h3 ha hquarter hquarterLabel hAupper hAle
        hcStar hcTwo hrho hbias hactiveScale hmean
        hqa huk hRB hmajor s hstartActive
        hanchorActive hstartGap hx0 hy0 hk0

/-- The `19` stage barrier fits the next `14` boundary envelope whenever the
successive radii satisfy the displayed integer comparison. -/
theorem lemma17PhysicalStageGood_to_next
    {n : ℕ} (A cStar rho rhoNext : ℕ)
    (hroot : 19 * rho ≤ 14 * rhoNext)
    (s : InfectionRevealPhysicalState n)
    (hs :
      Lemma17PhysicalStageGood A
        (19 * cStar * rho) s) :
    A ≤ s.coarse.1.active ∧
      s.coarse.1.ay ≤
        s.coarse.1.ax +
          14 * cStar * rhoNext := by
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply Nat.add_le_add_left
  calc
    19 * cStar * rho =
        cStar * (19 * rho) := by ring
    _ ≤ cStar * (14 * rhoNext) :=
      Nat.mul_le_mul_left cStar hroot
    _ = 14 * cStar * rhoNext := by ring

end

end Tri

#print axioms Tri.lemma17PhysicalStage_paper
#print axioms Tri.lemma17PhysicalStageGood_to_next
