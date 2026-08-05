/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17FixedLanding
import Tri.Lemma16To17

/-!
# Lemma 16 through the fixed final Lemma 17 landing

The ordinary Lemma 17 prefix stops at the last dyadic predecessor.  One
custom stage then lands at the least fixed critical scale.  The final
inactive-majority anchor replaces exactly the anchor formerly paid by the
last dyadic rung.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The final custom rung occupies exactly the old last Lemma 17 error slot. -/
theorem lemma17FixedLandingError_sum_succ
    (qStage qMajor cStar mPred : ℕ)
    (scale rho r : ℕ → ℕ) :
    (∑ j ∈ Finset.range mPred,
        (lemma17StageError
            (scale j) qStage cStar (rho j) (r j) +
          lemma16UrnError qMajor)) +
        lemma16UrnError qMajor +
        lemma17StageError
          (scale mPred) qStage cStar
          (rho mPred) (r mPred)
      =
    ∑ j ∈ Finset.range (mPred + 1),
      (lemma17StageError
          (scale j) qStage cStar (rho j) (r j) +
        lemma16UrnError qMajor) := by
  rw [Finset.sum_range_succ]
  ring

/-- The custom rung also occupies exactly one ordinary raw-clock block. -/
theorem lemma17FixedLandingClock_blocks
    (mPred cStar n : ℕ) :
    mPred * (cStar * n) + cStar * n =
      (mPred + 1) * (cStar * n) := by
  ring

/-- The common stopped-urn potential survives the Lemma 16 stage, the old
dyadic prefix, and the final fixed-target landing. -/
theorem expect_lemma16_then_lemma17_fixed_target_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (k16 a16 T cStar mPred rhoLanding : ℕ)
    (scale rho : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom16 : a16 + 4 ≤ n)
    (hanchor16 : s.coarse.1.active + k16 = a16)
    (hroom17 :
      ∀ l < mPred, 2 * scale l + 4 ≤ n)
    (hroomLanding :
      theorem6FixedCriticalScale n + 4 ≤ n)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad] :
    expect
        (((lemma16PhysicalStageKernel
              n h3 k16 T s).bind
            (fun z =>
              stagedIter
                (lemma17LadderKernel
                  n h3 cStar scale rho)
                mPred z)).bind
          (lemma17TargetLandingKernel
            n h3 cStar
              (theorem6FixedCriticalScale n)
              rhoLanding))
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  let p :=
    (lemma16PhysicalStageKernel n h3 k16 T s).bind
      (fun z =>
        stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          mPred z)
  let V : InfectionRevealPhysicalState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts z.inactive)
  rw [expect_bind']
  calc
    (∑' z, p z *
        expect
          (lemma17TargetLandingKernel
            n h3 cStar
              (theorem6FixedCriticalScale n)
              rhoLanding z)
          V)
        ≤
      ∑' z, p z * V z := by
        exact ENNReal.tsum_le_tsum fun z =>
          mul_le_mul_right
            (expect_lemma17TargetLandingKernel_urnEverHit_le
              n h3 cStar
              (theorem6FixedCriticalScale n)
              rhoLanding hroomLanding Bad z)
            (p z)
    _ = expect p V := rfl
    _ ≤ V s := by
      exact
        expect_lemma16_then_lemma17_staged_urnEverHit_le
          n h3 k16 a16 T cStar mPred scale rho s
          hroom16 hanchor16 hroom17 Bad

theorem lemma16_then_lemma17_fixed_target_closed
    (n q16 qStage qMajor a16 k16 u16 nu R B rho16
      cStar mPred DMajor kMajor uMajor
      rhoLanding rLanding : ℕ)
    (scale rho r : ℕ → ℕ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q16)
    (hquarter16 : 4 * a16 ≤ n)
    (hcStar16 : 640 ≤ cStar)
    (hroot16 : a16 ^ 5 * q16 * n ≤ n ^ 5)
    (hqa16 : q16 * a16 ≤ rho16 ^ 2)
    (hqaOrder16 : q16 ≤ a16)
    (hrho16 : 1 ≤ rho16)
    (hnu : nu + 1 = n)
    (hk16 : k16 + 1 = a16)
    (hu16 : u16 + k16 + 1 = nu)
    (hRB : R + B = nu)
    (hmajor0 : R ≤ B)
    (hk16pos : 0 < k16)
    (hscale0 : scale 0 = a16)
    (hrho0 : rho 0 = rho16)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (hdouble :
      ∀ j < mPred, scale (j + 1) = 2 * scale j)
    (hroot :
      ∀ j < mPred, 19 * rho j ≤ 14 * rho (j + 1))
    (ha : ∀ j < mPred, 4 ≤ scale j)
    (hquarter :
      ∀ j < mPred, 4 * scale j ≤ n)
    (htarget :
      ∀ j < mPred, 2 * scale j ≤ n)
    (hrho : ∀ j < mPred, 1 ≤ rho j)
    (hbias :
      ∀ j < mPred, 38 * cStar * rho j ≤ scale j)
    (hactiveScale :
      ∀ j < mPred, 76 * cStar * r j ≤ scale j)
    (hmean :
      ∀ j < mPred,
        (2 * scale j) ^ 3 ≤ r j * n ^ 2)
    (hqa :
      ∀ j < mPred,
        qStage * (scale j + 1) ≤ (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < mPred,
        5 * (scale j + 1) ≤ n + 1)
    (hMajorBR :
      B + R = uMajor + kMajor + 1)
    (hMajorGap : R + DMajor ≤ B)
    (hkMajor : 0 < kMajor)
    (hMajorQa :
      qMajor * (kMajor + 1) ≤ DMajor ^ 2)
    (hMajorQuarter :
      4 * (kMajor + 1) ≤ B + R + 1)
    (hclockRoom :
      ∀ j < mPred,
        scale j + 1 ≤ (1 : ℕ) + kMajor)
    (hclockRoomFinal :
      scale mPred + 1 ≤ (1 : ℕ) + kMajor)
    (haPred : 4 ≤ scale mPred)
    (hbelow :
      theorem6FixedCStarSq * scale mPred < n)
    (habove :
      n ≤ theorem6FixedCStarSq * (2 * scale mPred))
    (hrhoPred : 1 ≤ rho mPred)
    (hrootLanding :
      19 * rho mPred ≤ 14 * rhoLanding)
    (hbiasPred :
      38 * cStar * rho mPred ≤ scale mPred)
    (hactiveScaleLanding :
      76 * cStar * rLanding ≤ scale mPred)
    (hmeanLanding :
      (theorem6FixedCriticalScale n) ^ 3 ≤
        rLanding * n ^ 2)
    (hqaLanding :
      qStage * (scale mPred + 1) ≤
        (rho mPred) ^ 2)
    (s : InfectionRevealPhysicalState n)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R) :
    terminalFailureMass
        (((lemma16PhysicalStageKernel
              n h3 k16 (cStar * q16 * n) s).bind
            (fun z =>
              stagedIter
                (lemma17LadderKernel
                  n h3 cStar scale rho)
                mPred z)).bind
          (lemma17TargetLandingKernel
            n h3 cStar
              (theorem6FixedCriticalScale n)
              (rho mPred)))
        (Lemma17GapBoundaryGood
          (theorem6FixedCriticalScale n)
          cStar rhoLanding)
      ≤
        (3 * lemma16UrnError q16 +
          ∑ j ∈ Finset.range mPred,
            (lemma17StageError
                (scale j) qStage cStar
                (rho j) (r j) +
              lemma16UrnError qMajor)) +
          lemma16UrnError qMajor +
          lemma17StageError
            (scale mPred) qStage cStar
            (rho mPred) rLanding := by
  have htotal := s.coarse.2
  simp only [InfectionCfg.Inv, InfectionCfg.total] at htotal
  have hinactive := s.hinactiveCard
  have hlabels :=
    InfectionInactiveView.xIds_card_add_yIds_card
      s.inactive
  have hstartActive : s.coarse.1.active = 1 := by
    omega
  have hanchor16 :
      s.coarse.1.active + k16 = a16 := by
    omega
  have hroom16 : a16 + 4 ≤ n := by
    omega
  let p :=
    (lemma16PhysicalStageKernel
        n h3 k16 (cStar * q16 * n) s).bind
      (fun z =>
        stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          mPred z)
  have hprefix :
      terminalFailureMass p
          (Lemma17GapBoundaryGood
            (scale mPred) cStar (rho mPred))
        ≤
          3 * lemma16UrnError q16 +
            ∑ j ∈ Finset.range mPred,
              (lemma17StageError
                  (scale j) qStage cStar
                  (rho j) (r j) +
                lemma16UrnError qMajor) := by
    simpa [p] using
      lemma16_then_lemma17_ladder_closed
        n q16 qStage qMajor a16 k16 u16 nu R B
        rho16 cStar mPred DMajor kMajor uMajor
        scale rho r h3 hlog hquarter16 hcStar16
        hroot16 hqa16 hqaOrder16 hrho16 hnu hk16
        hu16 hRB hmajor0 hk16pos hscale0 hrho0
        hcStar hcTwo hdouble hroot ha hquarter
        htarget hrho hbias hactiveScale hmean hqa
        hlabelRoom hMajorBR hMajorGap hkMajor
        hMajorQa hMajorQuarter hclockRoom s hx0 hy0
  have hroom17 :
      ∀ l < mPred, 2 * scale l + 4 ≤ n := by
    intro l hl
    have hqtr := hquarter l hl
    have hal := ha l hl
    omega
  have hclock :
      scale mPred + 1 ≤
        s.coarse.1.active + kMajor := by
    rw [hstartActive]
    exact hclockRoomFinal
  have hanchor :
      terminalFailureMass p
          (fun z =>
            Lemma17GapBoundaryGood
                (scale mPred) cStar (rho mPred) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤ lemma16UrnError qMajor := by
    simpa [p] using
      lemma16_then_lemma17_anchor_failure
        n h3 qMajor k16 a16 (cStar * q16 * n)
        cStar mPred DMajor kMajor uMajor B R
        scale rho s hroom16 hanchor16 hMajorBR
        hMajorGap hx0 hy0 hkMajor hMajorQa
        hMajorQuarter hroom17 hclock
  exact
    lemma17Prefix_then_fixed_target_closed
      n qStage cStar (scale mPred)
      (rho mPred) rhoLanding rLanding
      (3 * lemma16UrnError q16 +
        ∑ j ∈ Finset.range mPred,
          (lemma17StageError
              (scale j) qStage cStar
              (rho j) (r j) +
            lemma16UrnError qMajor))
      (lemma16UrnError qMajor) p h3 hcStar hcTwo
      haPred hbelow habove hrhoPred hrootLanding
      hbiasPred hactiveScaleLanding hmeanLanding
      hqaLanding hprefix hanchor

end

end Tri

#print axioms Tri.lemma16_then_lemma17_fixed_target_closed
#print axioms Tri.lemma17FixedLandingError_sum_succ
#print axioms Tri.lemma17FixedLandingClock_blocks
#print axioms
  Tri.expect_lemma16_then_lemma17_fixed_target_urnEverHit_le
