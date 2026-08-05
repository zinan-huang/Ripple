/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To17FixedLanding
import Tri.Lemma17To19Ladder

/-!
# The absolute-gap anchor after the fixed landing

The custom final Lemma 17 stage preserves the same stopped-urn potential as
the old dyadic ladder.  Consequently the fixed endpoint inherits the
absolute inactive-gap anchor required by the unchanged Lemma 18 launch.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A fixed multiplier large enough to absorb the one-unit predecessor loss
in the least-cover scale. -/
def theorem6FixedPoolMultiplier : ℕ :=
  2 * theorem6FixedCStarSq

/-- The additive predecessor of the fixed critical scale covers the whole
population after multiplication by `theorem6FixedPoolMultiplier`. -/
theorem theorem6FixedCriticalScale_pool_cover
    (n : ℕ)
    (hn : 0 < n)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n) :
    ∃ aPred e,
      aPred + 1 = theorem6FixedCriticalScale n ∧
      n + e =
        theorem6FixedCStarSq *
          theorem6FixedCriticalScale n ∧
      e < theorem6FixedCStarSq ∧
      n ≤ aPred * theorem6FixedPoolMultiplier := by
  obtain ⟨aPred, e, haPred, hceil, hexcess⟩ :=
    theorem6FixedCriticalScale_additive_ceiling n hn
  have haLarge :
      theorem6FixedCStarSq + 6 ≤
        theorem6FixedCriticalScale n :=
    theorem6FixedCriticalScale_lower
      n (theorem6FixedCStarSq + 6) hlarge
  have haPredPos : 1 ≤ aPred := by
    rw [← haPred] at haLarge
    omega
  have hceilN :
      n + e = 1048576 * (aPred + 1) := by
    rw [← haPred] at hceil
    simpa using hceil
  refine ⟨aPred, e, haPred, hceil, hexcess, ?_⟩
  unfold theorem6FixedPoolMultiplier
  rw [theorem6FixedCStar_sq]
  omega

/-- Every fixed landing boundary satisfies the pool-scale premise of the
unchanged Lemma 18 launch. -/
theorem fixedGapBoundary_pool_le_stageRemaining_mul
    (n cStar rho : ℕ)
    (hn : 0 < n)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (z : InfectionRevealPhysicalState n)
    (hz :
      Lemma17GapBoundaryGood
        (theorem6FixedCriticalScale n)
        cStar rho z) :
    z.inactive.ids.card ≤
      lemma17StageRemaining
          (theorem6FixedCriticalScale n) z *
        theorem6FixedPoolMultiplier := by
  obtain ⟨aPred, e, haPred, hceil, hexcess, hpool⟩ :=
    theorem6FixedCriticalScale_pool_cover n hn hlarge
  apply
    gapBoundary_pool_le_stageRemaining_mul
      n (theorem6FixedCriticalScale n)
      cStar rho theorem6FixedPoolMultiplier aPred
  · have hscaleLarge :
        theorem6FixedCStarSq + 6 ≤
          theorem6FixedCriticalScale n :=
      theorem6FixedCriticalScale_lower
        n (theorem6FixedCStarSq + 6) hlarge
    omega
  · exact haPred
  · exact hpool
  · exact hz

theorem lemma16_then_lemma17_fixed_target_absolute_gap_failure
    (n : ℕ) (h3 : 3 ≤ n)
    (qGap k16 a16 T cStar mPred
      rhoSource rhoTarget F H E k u B R : ℕ)
    (scale rho : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom16 : a16 + 4 ≤ n)
    (hanchor16 : s.coarse.1.active + k16 = a16)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hBR : B + R = u + k + 1)
    (hgap : R + (F + H) ≤ B)
    (hshrink :
      E * (B + R) ≤ H * (u + 1))
    (hk : 0 < k)
    (hqa : qGap * (k + 1) ≤ F ^ 2)
    (hquarter : 4 * (k + 1) ≤ B + R + 1)
    (hroom17 :
      ∀ l < mPred, 2 * scale l + 4 ≤ n)
    (hroomLanding :
      theorem6FixedCriticalScale n + 4 ≤ n)
    (hclockRoom :
      theorem6FixedCriticalScale n + 1 ≤
        s.coarse.1.active + k) :
    terminalFailureMass
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
              rhoSource))
        (fun z =>
          Lemma17GapBoundaryGood
              (theorem6FixedCriticalScale n)
              cStar rhoTarget z →
            z.inactive.yIds.card + E ≤
              z.inactive.xIds.card)
      ≤ lemma16UrnError qGap := by
  let Bad := Lemma16UrnWindowBad F u k B R
  let μ :=
    ((lemma16PhysicalStageKernel
          n h3 k16 T s).bind
        (fun z =>
          stagedIter
            (lemma17LadderKernel
              n h3 cStar scale rho)
            mPred z)).bind
      (lemma17TargetLandingKernel
        n h3 cStar
          (theorem6FixedCriticalScale n)
          rhoSource)
  have hmass :
      terminalFailureMass μ
          (fun z =>
            Lemma17GapBoundaryGood
                (theorem6FixedCriticalScale n)
                cStar rhoTarget z →
              z.inactive.yIds.card + E ≤
                z.inactive.xIds.card)
        ≤
      expect μ
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive)) := by
    exact
      terminalFailureMass_gapBoundary_absolute_gap_le_expect_urn
        n cStar (theorem6FixedCriticalScale n)
        rhoTarget F H E k u B R s μ hx0 hy0
        hBR hgap hshrink hk hclockRoom
  have hpotential :
      expect μ
          (fun z =>
            everHit Bad urnStopped
              (infectionInactiveCounts z.inactive))
        ≤
      everHit Bad urnStopped (B, R) := by
    have hpot :=
      expect_lemma16_then_lemma17_fixed_target_urnEverHit_le
        n h3 k16 a16 T cStar mPred rhoSource
        scale rho s hroom16 hanchor16 hroom17
        hroomLanding Bad
    have hcounts :
        infectionInactiveCounts s.inactive = (B, R) := by
      simp [infectionInactiveCounts, hx0, hy0]
    simpa [μ, hcounts] using hpot
  calc
    terminalFailureMass μ
          (fun z =>
            Lemma17GapBoundaryGood
                (theorem6FixedCriticalScale n)
                cStar rhoTarget z →
              z.inactive.yIds.card + E ≤
                z.inactive.xIds.card)
        ≤
      expect μ
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive)) :=
      hmass
    _ ≤ everHit Bad urnStopped (B, R) :=
      hpotential
    _ ≤ lemma16UrnError qGap := by
      unfold everHit
      exact
        lemma17_urn_window_tail_pool
          qGap F (k + 1) k u (B + R) B R
          hqa rfl hBR.symm rfl hquarter hk

end

end Tri

#print axioms
  Tri.lemma16_then_lemma17_fixed_target_absolute_gap_failure
#print axioms Tri.theorem6FixedCriticalScale_pool_cover
#print axioms Tri.fixedGapBoundary_pool_le_stageRemaining_mul
