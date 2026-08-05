/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17Ladder

/-!
# A custom final landing stage for Lemma 17

The last Lemma 17 stage may stop at any target strictly above the source
scale and at most twice that scale.  The remaining number of reveals is
chosen additively from the actual physical boundary state.  If the source
has already overshot to the target, the stage is the identity kernel.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Remaining reveals to a custom target, chosen without natural-number
subtraction. -/
noncomputable def lemma17TargetRemaining
    {n : ℕ} (A : ℕ)
    (s : InfectionRevealPhysicalState n) : ℕ := by
  classical
  exact
    if h : ∃ k, s.coarse.1.active + k = A then
      Classical.choose h
    else 0

theorem lemma17TargetRemaining_spec
    {n A : ℕ}
    (s : InfectionRevealPhysicalState n)
    (hactive : s.coarse.1.active ≤ A) :
    s.coarse.1.active + lemma17TargetRemaining A s =
      A := by
  obtain ⟨k, hk⟩ :=
    Nat.exists_eq_add_of_le hactive
  have hex :
      ∃ k, s.coarse.1.active + k = A :=
    ⟨k, hk.symm⟩
  unfold lemma17TargetRemaining
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- A custom landing is pure when the input has already reached its target
and otherwise runs the ordinary physical stage to that target. -/
noncomputable def lemma17TargetLandingKernel
    (n : ℕ) (h3 : 3 ≤ n)
    (cStar A rho : ℕ) :
    InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun s =>
    if A ≤ s.coarse.1.active then
      PMF.pure s
    else
      lemma17PhysicalStageKernel n h3
        (lemma17TargetRemaining A s)
        A (19 * cStar * rho)
        (cStar * n) s

/-- A custom landing preserves every stopped-urn hitting potential.  The
target arithmetic is used only to obtain the additive reveal anchor; the
underlying stopped-urn argument is the same as for an ordinary rung. -/
theorem expect_lemma17TargetLandingKernel_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (cStar A rho : ℕ)
    (hroom : A + 4 ≤ n)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad]
    (s : InfectionRevealPhysicalState n) :
    expect
        (lemma17TargetLandingKernel
          n h3 cStar A rho s)
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  by_cases hdone : A ≤ s.coarse.1.active
  · simp [lemma17TargetLandingKernel, hdone]
  · have hactiveLe :
        s.coarse.1.active ≤ A := by
      omega
    have hanchor :
        s.coarse.1.active +
            lemma17TargetRemaining A s =
          A :=
      lemma17TargetRemaining_spec s hactiveLe
    unfold lemma17TargetLandingKernel
    rw [if_neg hdone]
    exact
      expect_lemma17PhysicalStageKernel_urnEverHit_le
        n h3 (lemma17TargetRemaining A s) A
        (19 * cStar * rho) (cStar * n)
        s hroom hanchor Bad

/-- The one-stage Lemma 17 estimate remains valid for a custom target
`A ∈ (a, 2a]`.  The possible zero-length boundary case is handled by the
pure branch and costs no error. -/
theorem lemma17GapBoundary_target_stage
    (n q cStar a A rho rhoNext r : ℕ)
    (h3 : 3 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (ha : 4 ≤ a)
    (hquarter : 4 * a ≤ n)
    (hAlo : a < A)
    (hAupper : A ≤ 2 * a)
    (hAle : A ≤ n)
    (hrho : 1 ≤ rho)
    (hroot : 19 * rho ≤ 14 * rhoNext)
    (hbias : 38 * cStar * rho ≤ a)
    (hactiveScale : 76 * cStar * r ≤ a)
    (hmean : A ^ 3 ≤ r * n ^ 2)
    (hqa : q * (a + 1) ≤ rho ^ 2)
    (hlabelRoom : 5 * (a + 1) ≤ n + 1)
    (s : InfectionRevealPhysicalState n)
    (hs : Lemma17GapBoundaryGood a cStar rho s)
    (hmajor :
      s.inactive.yIds.card ≤
        s.inactive.xIds.card) :
    terminalFailureMass
        (lemma17TargetLandingKernel
          n h3 cStar A rho s)
        (Lemma17GapBoundaryGood
          A cStar rhoNext)
      ≤ lemma17StageError a q cStar rho r := by
  by_cases hdone : A ≤ s.coarse.1.active
  · have hsourceUpper := hs.2.1
    have hactiveUpper :
        s.coarse.1.active ≤ A + 1 := by
      omega
    have hrhoLe : rho ≤ rhoNext := by
      omega
    have hgapUpper :
        s.coarse.1.ay ≤
          s.coarse.1.ax + 14 * cStar * rhoNext := by
      exact hs.2.2.trans
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left (14 * cStar) hrhoLe) _)
    have hgood :
        Lemma17GapBoundaryGood
          A cStar rhoNext s :=
      ⟨hdone, hactiveUpper, hgapUpper⟩
    simp [lemma17TargetLandingKernel,
      hdone, terminalFailureMass_pure, hgood]
  · have hactiveLe :
        s.coarse.1.active ≤ A := by
      omega
    let k := lemma17TargetRemaining A s
    let R := s.inactive.yIds.card
    let B := s.inactive.xIds.card
    let nu := R + B
    let u := lemma17PoolRemainder k R B
    have hanchor :
        s.coarse.1.active + k = A := by
      exact lemma17TargetRemaining_spec s hactiveLe
    have hkPos : 0 < k := by
      dsimp only [k] at hanchor ⊢
      omega
    have hstart := hs.1
    have hkLe : k ≤ a := by
      dsimp only [k] at hanchor ⊢
      omega
    have hkOne : k + 1 ≤ a + 1 := by
      omega
    have htotal :
        s.coarse.1.active + (R + B) = n := by
      have hlabels :=
        InfectionInactiveView.xIds_card_add_yIds_card
          s.inactive
      have hinactive := s.hinactiveCard
      have hcfg := s.coarse.2
      simp only [InfectionCfg.Inv, InfectionCfg.total] at hcfg
      dsimp only [R, B]
      omega
    have hlabelQuarter :
        4 * (k + 1) ≤ nu + 1 := by
      dsimp only [nu]
      omega
    have hkRoom : k + 1 ≤ R + B := by
      dsimp only [nu] at hlabelQuarter
      omega
    have hu : u + k + 1 = nu :=
      lemma17PoolRemainder_spec k R B hkRoom
    have hqaLocal :
        q * (k + 1) ≤ rho ^ 2 :=
      (Nat.mul_le_mul_left q hkOne).trans hqa
    let μ :=
      lemma17PhysicalStageKernel n h3 k
        A (19 * cStar * rho) (cStar * n) s
    let RangeGood :
        InfectionRevealPhysicalState n → Prop :=
      Lemma17PhysicalStageRangeGood
        A (19 * cStar * rho)
    have hrange :
        terminalFailureMass μ RangeGood ≤
          lemma17StageError a q cStar rho r := by
      exact
        lemma17PhysicalStage_paper_range
          n q rho a k u nu R B A cStar r
          h3 ha hquarter hlabelQuarter
          hAupper hAle hcStar hcTwo hrho
          hbias hactiveScale hmean hqaLocal
          hu rfl
          (by simpa [R, B] using hmajor)
          s hs.1 hanchor hs.2.2 rfl rfl hkPos
    have hnext :
        ∀ z, RangeGood z →
          Lemma17GapBoundaryGood
            A cStar rhoNext z := by
      intro z hz
      have hgap :=
        lemma17PhysicalStageGood_to_next
          A cStar rho rhoNext hroot z
          ⟨hz.1, hz.2.2⟩
      exact ⟨hgap.1, hz.2.1, hgap.2⟩
    have hresult :=
      (terminalFailureMass_mono
        μ
        (Lemma17GapBoundaryGood
          A cStar rhoNext)
        RangeGood hnext).trans hrange
    simpa [lemma17TargetLandingKernel,
      hdone, μ, k] using hresult

end

end Tri

#print axioms Tri.lemma17TargetRemaining_spec
#print axioms Tri.expect_lemma17TargetLandingKernel_urnEverHit_le
#print axioms Tri.lemma17GapBoundary_target_stage
