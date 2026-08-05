/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma19PaperStage
import Tri.Lemma17StageRange

/-!
# Physical endpoint form of positive-gap Lemma 19 stages

The counted carrier is projected back to the identity-refined physical state.
The range form also records the unavoidable one-identity overshoot of a
two-activation record.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A physical Lemma 19 stage reaches its target and retains a positive
active `X-Y` gap. -/
def Lemma19PhysicalStageGood
    {n : ℕ} (A targetGap : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  A ≤ s.coarse.1.active ∧
    s.coarse.1.ay + targetGap ≤ s.coarse.1.ax

noncomputable instance lemma19PhysicalStageGoodDecidable
    {n : ℕ} (A targetGap : ℕ) :
    DecidablePred (@Lemma19PhysicalStageGood n A targetGap) :=
  Classical.decPred _

/-- Range-strengthened positive-gap endpoint. -/
def Lemma19PhysicalStageRangeGood
    {n : ℕ} (A targetGap : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  A ≤ s.coarse.1.active ∧
    s.coarse.1.active ≤ A + 1 ∧
    s.coarse.1.ay + targetGap ≤ s.coarse.1.ax

noncomputable instance lemma19PhysicalStageRangeGoodDecidable
    {n : ℕ} (A targetGap : ℕ) :
    DecidablePred (@Lemma19PhysicalStageRangeGood n A targetGap) :=
  Classical.decPred _

/-- Project any counted positive-gap estimate to the physical endpoint. -/
theorem lemma19PhysicalStage_of_counted
    (n : ℕ) (h3 : 3 ≤ n)
    (k A targetGap T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (ε : ℝ≥0∞)
    (h :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (Lemma19StageGood A targetGap)
        ≤ ε) :
    terminalFailureMass
        (lemma17PhysicalStageKernel n h3 k A 0 T s)
        (Lemma19PhysicalStageGood A targetGap)
      ≤ ε := by
  unfold lemma17PhysicalStageKernel
  rw [terminalFailureMass_map]
  simpa [Lemma19PhysicalStageGood,
    Lemma19StageGood] using h

/-- Add the exact physical endpoint range without changing failure mass. -/
theorem lemma19PhysicalStage_range
    (n : ℕ) (h3 : 3 ≤ n)
    (k A targetGap T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (ε : ℝ≥0∞)
    (h :
      terminalFailureMass
          (lemma17PhysicalStageKernel n h3 k A 0 T s)
          (Lemma19PhysicalStageGood A targetGap)
        ≤ ε) :
    terminalFailureMass
        (lemma17PhysicalStageKernel n h3 k A 0 T s)
        (Lemma19PhysicalStageRangeGood A targetGap)
      ≤ ε := by
  let μ :=
    lemma17PhysicalStageKernel n h3 k A 0 T s
  have heq :
      terminalFailureMass μ
          (Lemma19PhysicalStageRangeGood A targetGap) =
        terminalFailureMass μ
          (Lemma19PhysicalStageGood A targetGap) := by
    unfold terminalFailureMass
    apply tsum_congr
    intro z
    by_cases hzμ : μ z = 0
    · simp [hzμ]
    · have hupper :
          z.coarse.1.active ≤ A + 1 :=
        lemma17PhysicalStageKernel_active_le
          n h3 k A 0 T s z hanchorActive
          (by simpa [μ] using hzμ)
      by_cases hgood :
          Lemma19PhysicalStageGood A targetGap z
      · have hrange :
            Lemma19PhysicalStageRangeGood
              A targetGap z :=
          ⟨hgood.1, hupper, hgood.2⟩
        simp [hgood, hrange]
      · have hnrange :
            ¬ Lemma19PhysicalStageRangeGood
              A targetGap z := by
          intro hz
          exact hgood ⟨hz.1, hz.2.2⟩
        simp [hgood, hnrange]
  rw [heq]
  exact h

/-- Physical endpoint of the instantiated positive-gap doubling stage. -/
theorem lemma19PhysicalStage_paper
    (n q rho a k u nu R B A cStar r
      Dstart targetGap M : ℕ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hquarterLabel : 4 * (k + 1) ≤ nu + 1)
    (hAeq : A = 2 * a)
    (hAle : A ≤ n)
    (hcStar : 128 ≤ cStar)
    (hmean : A ^ 3 ≤ r * n ^ 2)
    (hqa : q * (k + 1) ≤ rho ^ 2)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hmajor : R ≤ B)
    (hbudget :
      targetGap + (rho + 1) + 2 * M ≤ Dstart)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (lemma17PhysicalStageKernel
          n h3 k A 0 (cStar * n) s)
        (Lemma19PhysicalStageRangeGood A targetGap)
      ≤ lemma19StageError a q cStar r M := by
  apply
    lemma19PhysicalStage_range
      n h3 k A targetGap (cStar * n) s
      hanchorActive
      (lemma19StageError a q cStar r M)
  apply
    lemma19PhysicalStage_of_counted
      n h3 k A targetGap (cStar * n) s
      (lemma19StageError a q cStar r M)
  exact
    lemma19CountedPath_paper_stage
      n q rho a k u nu R B A cStar r
      Dstart targetGap M h3 ha hquarterClock
      hquarterLabel hAeq hAle hcStar hmean hqa
      huk hRB hmajor hbudget s hstartActive
      hanchorActive hstart hx0 hy0 hk0

end

end Tri

#print axioms Tri.lemma19PhysicalStage_of_counted
#print axioms Tri.lemma19PhysicalStage_range
#print axioms Tri.lemma19PhysicalStage_paper
