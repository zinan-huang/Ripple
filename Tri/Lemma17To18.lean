/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To17
import Tri.Lemma18To19Budget

/-!
# Random-endpoint handoff from Lemma 17 to Lemma 18

The Lemma 17 ladder ends at a random physical state whose active population
is either the target or one above it.  The decisive Lemma 18 block therefore
uses an endpoint-dependent additive remaining-reveal witness.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- If the original inactive gap contains an urn-deviation reserve `F` and a
deterministic shrinkage reserve `H`, then failure of a later absolute gap `E`
forces the positive-tilt Lemma 16 urn event. -/
theorem lemma17_remaining_gap_fail_implies_urnWindowBad
    (F H E u k B R xRem yRem : ℕ)
    (hBR : B + R = u + k + 1)
    (hgap : R + (F + H) ≤ B)
    (hshrink :
      E * (B + R) ≤ H * (u + 1))
    (hclock : u + 1 ≤ xRem + yRem)
    (hfail : xRem < yRem + E)
    (hk : 0 < k) :
    Lemma16UrnWindowBad F u k B R
      (xRem, yRem) := by
  have hBRPos : 0 < B + R := by omega
  have hremPos : 0 < xRem + yRem := by omega
  have hBRPosR : (0 : ℝ) < (B : ℝ) + (R : ℝ) := by
    exact_mod_cast hBRPos
  have hremPosR :
      (0 : ℝ) < (xRem : ℝ) + (yRem : ℝ) := by
    exact_mod_cast hremPos
  have hgapR :
      (R : ℝ) + ((F : ℝ) + (H : ℝ)) ≤
        (B : ℝ) := by
    exact_mod_cast hgap
  have hshrinkR :
      (E : ℝ) * ((B : ℝ) + (R : ℝ)) ≤
        (H : ℝ) * ((u : ℝ) + 1) := by
    exact_mod_cast hshrink
  have hclockR :
      (u : ℝ) + 1 ≤
        (xRem : ℝ) + (yRem : ℝ) := by
    exact_mod_cast hclock
  have hfailR :
      (xRem : ℝ) <
        (yRem : ℝ) + (E : ℝ) := by
    exact_mod_cast hfail
  have hnum :
      (F : ℝ) *
            ((xRem : ℝ) + (yRem : ℝ)) / 2 ≤
        (B : ℝ) * (yRem : ℝ) -
          (R : ℝ) * (xRem : ℝ) := by
    nlinarith
  have hdelta :
      (F : ℝ) /
            (2 * ((B : ℝ) + (R : ℝ))) ≤
        (B : ℝ) / ((B : ℝ) + (R : ℝ)) -
          (xRem : ℝ) /
            ((xRem : ℝ) + (yRem : ℝ)) := by
    field_simp [ne_of_gt hBRPosR, ne_of_gt hremPosR]
    nlinarith [hnum]
  refine ⟨hclock, ?_⟩
  let delta : ℝ :=
    (F : ℝ) / (2 * ((B : ℝ) + (R : ℝ)))
  let A : ℝ :=
    2 * (k : ℝ) /
      (((u : ℝ) + 1) * ((B : ℝ) + (R : ℝ)))
  let lam : ℝ := 4 * delta / A
  have hkR : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    positivity
  have hlam0 : 0 ≤ lam := by
    dsimp only [lam]
    positivity
  change
    |lam| * delta ≤
      lam *
        urnM
          ((B : ℝ) / ((B : ℝ) + (R : ℝ)))
          (xRem, yRem)
  rw [abs_of_nonneg hlam0]
  unfold urnM
  exact mul_le_mul_of_nonneg_left hdelta hlam0

/-- The failure of an absolute inactive-gap condition at a gap-good ladder
boundary is bounded by the expected original-pool urn potential. -/
theorem terminalFailureMass_gapBoundary_absolute_gap_le_expect_urn
    (n cStar a rho F H E k u B R : ℕ)
    (s : InfectionRevealPhysicalState n)
    (μ : PMF (InfectionRevealPhysicalState n))
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hBR : B + R = u + k + 1)
    (hgap : R + (F + H) ≤ B)
    (hshrink :
      E * (B + R) ≤ H * (u + 1))
    (hk : 0 < k)
    (hclockRoom :
      a + 1 ≤ s.coarse.1.active + k) :
    terminalFailureMass μ
        (fun z =>
          Lemma17GapBoundaryGood a cStar rho z →
            z.inactive.yIds.card + E ≤
              z.inactive.xIds.card)
      ≤
    expect μ
      (fun z =>
        everHit
          (Lemma16UrnWindowBad F u k B R)
          urnStopped
          (infectionInactiveCounts z.inactive)) := by
  let Bad := Lemma16UrnWindowBad F u k B R
  let V : InfectionRevealPhysicalState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts z.inactive)
  let AnchorGood : InfectionRevealPhysicalState n → Prop :=
    fun z =>
      Lemma17GapBoundaryGood a cStar rho z →
        z.inactive.yIds.card + E ≤
          z.inactive.xIds.card
  have hinitialTotal :
      s.coarse.1.active + (B + R) = n := by
    have htotal := infectionReveal_active_add_inactive s
    have hlabels :=
      InfectionInactiveView.xIds_card_add_yIds_card
        s.inactive
    rw [hx0, hy0] at hlabels
    omega
  have hcontain :
      ∀ z, ¬ AnchorGood z → V z = 1 := by
    intro z hz
    have hzP :
        Lemma17GapBoundaryGood a cStar rho z := by
      by_contra hnP
      apply hz
      intro hP
      exact False.elim (hnP hP)
    have hzNotGap :
        ¬ z.inactive.yIds.card + E ≤
          z.inactive.xIds.card := by
      intro hpoolGap
      exact hz (fun _ => hpoolGap)
    have hzFail :
        z.inactive.xIds.card <
          z.inactive.yIds.card + E :=
      Nat.lt_of_not_ge hzNotGap
    have hzTotal :=
      infectionReveal_active_add_inactive z
    have hzLabels :=
      InfectionInactiveView.xIds_card_add_yIds_card
        z.inactive
    have hclock :
        u + 1 ≤
          z.inactive.xIds.card +
            z.inactive.yIds.card := by
      have hzActiveHi := hzP.2.1
      omega
    have hurn :=
      lemma17_remaining_gap_fail_implies_urnWindowBad
        F H E u k B R
        z.inactive.xIds.card z.inactive.yIds.card
        hBR hgap hshrink hclock hzFail hk
    exact
      everHit_eq_one_of_mem
        Bad urnStopped
        (infectionInactiveCounts z.inactive) hurn
  unfold terminalFailureMass expect
  exact ENNReal.tsum_le_tsum fun z => by
    change
      (if AnchorGood z then 0 else μ z) ≤ μ z * V z
    by_cases hz : AnchorGood z
    · simp [hz]
    · rw [if_neg hz, hcontain z hz, mul_one]

/-- At the final Lemma 17 boundary, failure of the absolute inactive gap is
charged to one normalized urn tail from the original pool. -/
theorem lemma16_then_lemma17_absolute_gap_failure
    (n : ℕ) (h3 : 3 ≤ n)
    (qGap k16 a16 T cStar j F H E k u B R : ℕ)
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
      ∀ l < j, 2 * scale l + 4 ≤ n)
    (hclockRoom :
      scale j + 1 ≤ s.coarse.1.active + k) :
    terminalFailureMass
        ((lemma16PhysicalStageKernel
            n h3 k16 T s).bind
          (fun z =>
            stagedIter
              (lemma17LadderKernel
                n h3 cStar scale rho)
              j z))
        (fun z =>
          Lemma17GapBoundaryGood
              (scale j) cStar (rho j) z →
            z.inactive.yIds.card + E ≤
              z.inactive.xIds.card)
      ≤ lemma16UrnError qGap := by
  let Bad := Lemma16UrnWindowBad F u k B R
  let μ :=
    (lemma16PhysicalStageKernel n h3 k16 T s).bind
      (fun z =>
        stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          j z)
  have hmass :
      terminalFailureMass μ
          (fun z =>
            Lemma17GapBoundaryGood
                (scale j) cStar (rho j) z →
              z.inactive.yIds.card + E ≤
                z.inactive.xIds.card)
        ≤
      expect μ
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive)) := by
    exact
      terminalFailureMass_gapBoundary_absolute_gap_le_expect_urn
        n cStar (scale j) (rho j) F H E k u B R
        s μ hx0 hy0 hBR hgap hshrink hk hclockRoom
  have hpotential :
      expect μ
          (fun z =>
            everHit Bad urnStopped
              (infectionInactiveCounts z.inactive))
        ≤
      everHit Bad urnStopped (B, R) := by
    have hpot :=
      expect_lemma16_then_lemma17_staged_urnEverHit_le
        n h3 k16 a16 T cStar j scale rho s
        hroom16 hanchor16 hroom17 Bad
    have hcounts :
        infectionInactiveCounts s.inactive = (B, R) := by
      simp [infectionInactiveCounts, hx0, hy0]
    simpa [μ, hcounts] using hpot
  calc
    terminalFailureMass μ
          (fun z =>
            Lemma17GapBoundaryGood
                (scale j) cStar (rho j) z →
              z.inactive.yIds.card + E ≤
                z.inactive.xIds.card)
        ≤
      expect μ
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive)) :=
      hmass
    _ ≤ everHit Bad urnStopped (B, R) := hpotential
    _ ≤ lemma16UrnError qGap := by
      unfold everHit
      exact
        lemma17_urn_window_tail_pool
          qGap F (k + 1) k u (B + R) B R
          hqa rfl hBR.symm rfl hquarter hk

/-- Start the decisive Lemma 18 block at a random Lemma 17 endpoint. -/
noncomputable def lemma18FromGapBoundaryKernel
    (n : ℕ) (h3 : 3 ≤ n)
    (a D cStar : ℕ) :
    InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun s =>
    lemma17PhysicalStageKernel
      n h3 (lemma17StageRemaining a s)
      (2 * a) (30 * D) (cStar * n) s

/-- Complete launch condition for the endpoint-dependent decisive stage. -/
def Lemma18LaunchGood
    {n : ℕ} (a cStar rho d D : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  Lemma17GapBoundaryGood a cStar rho s ∧
    s.inactive.ids.card ≤
      lemma17StageRemaining a s * d ∧
    s.inactive.yIds.card + 60 * d * D ≤
      s.inactive.xIds.card

noncomputable instance lemma18LaunchGoodDecidable
    {n : ℕ} (a cStar rho d D : ℕ) :
    DecidablePred (@Lemma18LaunchGood n a cStar rho d D) :=
  Classical.decPred _

/-- Combine the ladder endpoint bound and the aggregate strong inactive-gap
anchor bound into the launch condition for Lemma 18. -/
theorem terminalFailureMass_lemma18LaunchGood
    {n : ℕ} (a cStar rho d D : ℕ)
    (μ : PMF (InfectionRevealPhysicalState n))
    (εBoundary εGap : ℝ≥0∞)
    (hBoundary :
      terminalFailureMass μ
          (Lemma17GapBoundaryGood a cStar rho)
        ≤ εBoundary)
    (hGap :
      terminalFailureMass μ
          (fun z =>
            Lemma17GapBoundaryGood a cStar rho z →
              z.inactive.yIds.card + 60 * d * D ≤
                z.inactive.xIds.card)
        ≤ εGap)
    (hPoolScale :
      ∀ z : InfectionRevealPhysicalState n,
        Lemma17GapBoundaryGood a cStar rho z →
        z.inactive.ids.card ≤
          lemma17StageRemaining a z * d) :
    terminalFailureMass μ
        (Lemma18LaunchGood a cStar rho d D)
      ≤ εBoundary + εGap := by
  let P : InfectionRevealPhysicalState n → Prop :=
    Lemma17GapBoundaryGood a cStar rho
  let Q : InfectionRevealPhysicalState n → Prop :=
    fun z =>
      P z →
        z.inactive.yIds.card + 60 * d * D ≤
          z.inactive.xIds.card
  have hnext :
      ∀ z, P z ∧ Q z →
        Lemma18LaunchGood a cStar rho d D z := by
    intro z hz
    exact ⟨hz.1, hPoolScale z hz.1, hz.2 hz.1⟩
  exact
    (terminalFailureMass_mono
      μ
      (Lemma18LaunchGood a cStar rho d D)
      (fun z => P z ∧ Q z)
      hnext).trans
    ((terminalFailureMass_inter_le μ P Q).trans
      (add_le_add
        (by simpa [P] using hBoundary)
        (by simpa [P, Q] using hGap)))

/-- A good final Lemma 17 boundary, together with the two pool conditions
used by the paper, starts the fully quantitative physical Lemma 18 stage.
All stage-local pool sizes are chosen by additive witnesses. -/
theorem lemma18PhysicalEntry_paper_from_gapBoundary
    (n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
      a cStar rho r : ℕ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hstageRoom : 2 * a + 4 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hpriorRadius : cStar * rho ≤ D)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hendRadius : rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (a + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (a + 1) ≤ rhoEnd ^ 2)
    (hmajorQa :
      qMajor * (a + 2) ≤
        (60 * d * D) ^ 2)
    (hlabelRoom : 5 * a + 8 ≤ n)
    (hmeanActive :
      (2 * a) ^ 3 ≤ r * n ^ 2)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale :
      1200 * cStar * r ≤ 7 * a)
    (s : InfectionRevealPhysicalState n)
    (hs : Lemma17GapBoundaryGood a cStar rho s)
    (hpoolScale :
      s.inactive.ids.card ≤
        lemma17StageRemaining a s * d)
    (hpoolGap :
      s.inactive.yIds.card + 60 * d * D ≤
        s.inactive.xIds.card) :
    terminalFailureMass
        (lemma18FromGapBoundaryKernel
          n h3 a D cStar s)
        (Lemma18PhysicalEntryGood
          (2 * a) (2 * D))
      ≤
        lemma18StageError
            qPrefix qEnd a cStar r D +
          lemma16UrnError qMajor := by
  let k := lemma17StageRemaining a s
  let R := s.inactive.yIds.card
  let B := s.inactive.xIds.card
  let nu := R + B
  let u := lemma17PoolRemainder k R B
  let uMajor := lemma17PoolRemainder (k + 1) R B
  have hanchor :
      s.coarse.1.active + k = 2 * a := by
    exact
      lemma17StageRemaining_spec
        a s (by omega) hs.1 hs.2.1
  have hkLe : k ≤ a := by
    have hactiveLo := hs.1
    dsimp only [k] at hanchor ⊢
    omega
  have hkOne : k + 1 ≤ a + 1 := by
    omega
  have hkTwo : k + 2 ≤ a + 2 := by
    omega
  have hkPos : 0 < k := by
    have hactiveHi := hs.2.1
    dsimp only [k] at hanchor ⊢
    omega
  have htotal :
      s.coarse.1.active + (R + B) = n := by
    have hcoarse := s.coarse.2
    simp only [InfectionCfg.Inv, InfectionCfg.total] at hcoarse
    have hinactive := s.hinactiveCard
    have hlabels :=
      InfectionInactiveView.xIds_card_add_yIds_card
        s.inactive
    dsimp only [R, B]
    omega
  have hnu :
      s.inactive.ids.card = nu := by
    have hlabels :=
      InfectionInactiveView.xIds_card_add_yIds_card
        s.inactive
    dsimp only [nu, R, B]
    omega
  have hkPool : k + 1 ≤ R + B := by
    have hactiveHi := hs.2.1
    dsimp only [R, B]
    omega
  have hkMajorPool : (k + 1) + 1 ≤ R + B := by
    have hactiveHi := hs.2.1
    dsimp only [R, B]
    omega
  have hu :
      u + k + 1 = nu := by
    exact lemma17PoolRemainder_spec k R B hkPool
  have huMajor :
      uMajor + (k + 1) + 1 = nu := by
    exact
      lemma17PoolRemainder_spec
        (k + 1) R B hkMajorPool
  have hquarterPool :
      4 * (k + 1) ≤ nu + 1 := by
    have hactiveHi := hs.2.1
    dsimp only [nu, R, B]
    omega
  have hmajorQuarter :
      4 * ((k + 1) + 1) ≤ nu + 1 := by
    have hactiveHi := hs.2.1
    dsimp only [nu, R, B]
    omega
  have hprefixQaLocal :
      qPrefix * (k + 1) ≤ rhoPrefix ^ 2 :=
    (Nat.mul_le_mul_left qPrefix hkOne).trans hprefixQa
  have hendQaLocal :
      qEnd * (k + 1) ≤ rhoEnd ^ 2 :=
    (Nat.mul_le_mul_left qEnd hkOne).trans hendQa
  have hmajorQaLocal :
      qMajor * ((k + 1) + 1) ≤
        (60 * d * D) ^ 2 := by
    exact
      (Nat.mul_le_mul_left qMajor hkTwo).trans hmajorQa
  have hprior :
      s.coarse.1.ay ≤
        s.coarse.1.ax + 14 * D := by
    have hmul :
        14 * cStar * rho ≤ 14 * D := by
      calc
        14 * cStar * rho = 14 * (cStar * rho) := by
          ring
        _ ≤ 14 * D :=
          Nat.mul_le_mul_left 14 hpriorRadius
    exact hs.2.2.trans
      (Nat.add_le_add_left hmul s.coarse.1.ax)
  have hpoolScaleLocal : nu ≤ k * d := by
    rw [← hnu]
    exact hpoolScale
  have hpoolGapLocal :
      R + 60 * d * D ≤ B := by
    exact hpoolGap
  simpa [lemma18FromGapBoundaryKernel, k] using
    lemma18PhysicalEntry_paper
      n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
      a k u nu uMajor R B (2 * a) cStar r
      h3 ha hquarterClock rfl hstageRoom hcStar
      hprefixRadius hendRadius
      hprefixQaLocal hendQaLocal hmajorQaLocal
      hu huMajor rfl hquarterPool hmajorQuarter
      hpoolScaleLocal hpoolGapLocal hmeanActive
      hguardScale hreactionScale s hs.1 hanchor
      hprior rfl rfl hkPos

/-- Lemma 18 and the positive-gap Lemma 19 continuation, both started from
one random final Lemma 17 boundary. -/
theorem lemma18_then_lemma19_positive_gap_from_gapBoundary
    (n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
      a cStar rho r Dlabel M targetGap clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hstageRoom : 2 * a + 4 ≤ n)
    (hquarterLate : n ≤ 4 * (2 * a))
    (hcStar : 128 ≤ cStar)
    (hpriorRadius : cStar * rho ≤ D)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hendRadius : rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (a + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (a + 1) ≤ rhoEnd ^ 2)
    (hmajorQa :
      qMajor * (a + 2) ≤
        (60 * d * D) ^ 2)
    (hlabelRoom : 5 * a + 8 ≤ n)
    (hmeanActive :
      (2 * a) ^ 3 ≤ r * n ^ 2)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale :
      1200 * cStar * r ≤ 7 * a)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (s : InfectionRevealPhysicalState n)
    (hs : Lemma17GapBoundaryGood a cStar rho s)
    (hpoolScale :
      s.inactive.ids.card ≤
        lemma17StageRemaining a s * d)
    (hpoolGap :
      s.inactive.yIds.card + 60 * d * D ≤
        s.inactive.xIds.card) :
    terminalFailureMass
        ((lemma18FromGapBoundaryKernel
            n h3 a D cStar s).bind
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        (lemma18StageError
              qPrefix qEnd a cStar r D +
            lemma16UrnError qMajor) +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget M targetGap L := by
  let k := lemma17StageRemaining a s
  let p :=
    lemma18FromGapBoundaryKernel
      n h3 a D cStar s
  have hanchor :
      s.coarse.1.active + k = 2 * a := by
    exact
      lemma17StageRemaining_spec
        a s (by omega) hs.1 hs.2.1
  have hpre :
      terminalFailureMass p
          (Lemma18PhysicalEntryGood
            (2 * a) (2 * D))
        ≤
          lemma18StageError
              qPrefix qEnd a cStar r D +
            lemma16UrnError qMajor := by
    simpa [p] using
      lemma18PhysicalEntry_paper_from_gapBoundary
        n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
        a cStar rho r h3 ha hquarterClock hstageRoom
        hcStar hpriorRadius hprefixRadius hendRadius
        hprefixQa hendQa hmajorQa hlabelRoom
        hmeanActive hguardScale hreactionScale
        s hs hpoolScale hpoolGap
  have hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ 2 * a + 1 := by
    intro z hz
    exact
      lemma17PhysicalStageKernel_active_le
        n h3 k (2 * a) (30 * D) (cStar * n)
        s z hanchor (by
          simpa [p, lemma18FromGapBoundaryKernel, k]
            using hz)
  simpa [p] using
    lemma18Endpoint_then_full_activation_positive_gap_closed
      n (2 * a) D Dlabel M targetGap clockBudget L
      h3 (by omega) hstageRoom hquarterLate hbudget
      hgap0 hgapn hDlabel hL hscale p
      (lemma18StageError
          qPrefix qEnd a cStar r D +
        lemma16UrnError qMajor)
      hpre hupper

/-- A random final Lemma 17 endpoint continues through Lemmas 18 and 19 once
its boundary failure and strong inactive-gap anchor failure are controlled in
aggregate. -/
theorem lemma17Endpoint_then_lemma18_19_positive_gap_closed
    (n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
      a cStar rho r Dlabel M targetGap clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hstageRoom : 2 * a + 4 ≤ n)
    (hquarterLate : n ≤ 4 * (2 * a))
    (hcStar : 128 ≤ cStar)
    (hpriorRadius : cStar * rho ≤ D)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hendRadius : rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (a + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (a + 1) ≤ rhoEnd ^ 2)
    (hmajorQa :
      qMajor * (a + 2) ≤
        (60 * d * D) ^ 2)
    (hlabelRoom : 5 * a + 8 ≤ n)
    (hmeanActive :
      (2 * a) ^ 3 ≤ r * n ^ 2)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale :
      1200 * cStar * r ≤ 7 * a)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (p : PMF (InfectionRevealPhysicalState n))
    (εBoundary εGap : ℝ≥0∞)
    (hBoundary :
      terminalFailureMass p
          (Lemma17GapBoundaryGood a cStar rho)
        ≤ εBoundary)
    (hGap :
      terminalFailureMass p
          (fun z =>
            Lemma17GapBoundaryGood a cStar rho z →
              z.inactive.yIds.card + 60 * d * D ≤
                z.inactive.xIds.card)
        ≤ εGap)
    (hPoolScale :
      ∀ z : InfectionRevealPhysicalState n,
        Lemma17GapBoundaryGood a cStar rho z →
        z.inactive.ids.card ≤
          lemma17StageRemaining a z * d) :
    terminalFailureMass
        (p.bind
          (fun z =>
            (lemma18FromGapBoundaryKernel
                n h3 a D cStar z).bind
              (lemma19FullActivationBudgetKernel
                n h3 clockBudget)))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        (εBoundary + εGap) +
          ((lemma18StageError
                qPrefix qEnd a cStar r D +
              lemma16UrnError qMajor) +
            lemma19FullActivationPositiveGapUniformError
              n clockBudget M targetGap L) := by
  let Launch : InfectionRevealPhysicalState n → Prop :=
    Lemma18LaunchGood a cStar rho d D
  let K : InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
    fun z =>
      (lemma18FromGapBoundaryKernel
          n h3 a D cStar z).bind
        (lemma19FullActivationBudgetKernel
          n h3 clockBudget)
  have hlaunch :
      terminalFailureMass p Launch ≤
        εBoundary + εGap := by
    exact
      terminalFailureMass_lemma18LaunchGood
        a cStar rho d D p εBoundary εGap
        hBoundary hGap hPoolScale
  apply
    terminalFailureMass_bind_le_add_of_support
      p K Launch
      (Lemma19PhysicalStageRangeGood n targetGap)
      (εBoundary + εGap)
      ((lemma18StageError
            qPrefix qEnd a cStar r D +
          lemma16UrnError qMajor) +
        lemma19FullActivationPositiveGapUniformError
          n clockBudget M targetGap L)
      hlaunch
  intro z hzp hz
  exact
    lemma18_then_lemma19_positive_gap_from_gapBoundary
      n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
      a cStar rho r Dlabel M targetGap clockBudget L
      h3 ha hquarterClock hstageRoom hquarterLate
      hcStar hpriorRadius hprefixRadius hendRadius
      hprefixQa hendQa hmajorQa hlabelRoom
      hmeanActive hguardScale hreactionScale
      hbudget hgap0 hgapn hDlabel hL hscale
      z hz.1 hz.2.1 hz.2.2

end

end Tri

#print axioms Tri.lemma18PhysicalEntry_paper_from_gapBoundary
#print axioms Tri.lemma18_then_lemma19_positive_gap_from_gapBoundary
#print axioms Tri.lemma17_remaining_gap_fail_implies_urnWindowBad
#print axioms Tri.terminalFailureMass_gapBoundary_absolute_gap_le_expect_urn
#print axioms Tri.lemma16_then_lemma17_absolute_gap_failure
#print axioms Tri.terminalFailureMass_lemma18LaunchGood
#print axioms Tri.lemma17Endpoint_then_lemma18_19_positive_gap_closed
