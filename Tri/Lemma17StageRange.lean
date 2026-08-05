/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.StagedKernel

/-!
# Exact endpoint range of a Lemma 17 stage

A physical reaction can reveal two identities at once.  Consequently a stopped
stage reaches its target exactly or overshoots it by one identity.  This file
adds that durable range fact to the stage success predicate.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A stage endpoint lies at its target or at the one-identity physical
overshoot. -/
def Lemma17PhysicalStageRangeGood
    {n : ℕ} (A G : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  A ≤ s.coarse.1.active ∧
    s.coarse.1.active ≤ A + 1 ∧
    s.coarse.1.ay ≤ s.coarse.1.ax + G

noncomputable instance lemma17PhysicalStageRangeGoodDecidable
    {n : ℕ} (A G : ℕ) :
    DecidablePred (@Lemma17PhysicalStageRangeGood n A G) :=
  Classical.decPred _

theorem lemma17PhysicalStageKernel_active_le
    (n : ℕ) (h3 : 3 ≤ n)
    (k A G T : ℕ)
    (s z : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hz :
      lemma17PhysicalStageKernel n h3 k A G T s z ≠ 0) :
    z.coarse.1.active ≤ A + 1 := by
  unfold lemma17PhysicalStageKernel at hz
  have hzmem :
      z ∈
        ((iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s)).map
            (fun q => q.counted.path.current)).support :=
    hz
  rw [PMF.support_map] at hzmem
  rcases hzmem with ⟨q, hq, rfl⟩
  have hinv :=
    lemma17CountedPath_iter_inv
      n h3 k A G T s hanchorActive q hq
  have hledger := q.counted.path.hactiveLedger
  rw [hinv.1.1] at hledger
  change q.counted.path.current.coarse.1.active ≤ A + 1
  calc
    q.counted.path.current.coarse.1.active =
        s.coarse.1.active +
          q.counted.path.revealed.length :=
      hledger.symm
    _ ≤ s.coarse.1.active + (k + 1) :=
      Nat.add_le_add_left hinv.1.2 _
    _ = A + 1 := by omega

/-- The paper-stage theorem strengthened by the exact one-identity endpoint
range. -/
theorem lemma17PhysicalStage_paper_range
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
        (Lemma17PhysicalStageRangeGood A
          (19 * cStar * rho))
      ≤ lemma17StageError a q cStar rho r := by
  let μ :=
    lemma17PhysicalStageKernel n h3 k A
      (19 * cStar * rho) (cStar * n) s
  have hbase :
      terminalFailureMass μ
          (Lemma17PhysicalStageGood A
            (19 * cStar * rho))
        ≤ lemma17StageError a q cStar rho r := by
    simpa [μ] using
      lemma17PhysicalStage_paper
        n q rho a k u nu R B A cStar r
        h3 ha hquarter hquarterLabel hAupper hAle
        hcStar hcTwo hrho hbias hactiveScale hmean
        hqa huk hRB hmajor s hstartActive
        hanchorActive hstartGap hx0 hy0 hk0
  have heq :
      terminalFailureMass μ
          (Lemma17PhysicalStageRangeGood A
            (19 * cStar * rho)) =
        terminalFailureMass μ
          (Lemma17PhysicalStageGood A
            (19 * cStar * rho)) := by
    unfold terminalFailureMass
    apply tsum_congr
    intro z
    by_cases hzμ : μ z = 0
    · simp [hzμ]
    · have hupper :
          z.coarse.1.active ≤ A + 1 :=
        lemma17PhysicalStageKernel_active_le
          n h3 k A (19 * cStar * rho)
          (cStar * n) s z hanchorActive
          (by simpa [μ] using hzμ)
      by_cases hgood :
          Lemma17PhysicalStageGood A
            (19 * cStar * rho) z
      · have hrange :
            Lemma17PhysicalStageRangeGood A
              (19 * cStar * rho) z :=
          ⟨hgood.1, hupper, hgood.2⟩
        simp [hgood, hrange]
      · have hnrange :
            ¬ Lemma17PhysicalStageRangeGood A
              (19 * cStar * rho) z := by
          intro hz
          exact hgood ⟨hz.1, hz.2.2⟩
        simp [hgood, hnrange]
  rw [heq]
  exact hbase

end

end Tri

#print axioms Tri.lemma17PhysicalStageKernel_active_le
#print axioms Tri.lemma17PhysicalStage_paper_range
