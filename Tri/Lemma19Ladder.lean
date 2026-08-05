/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma19PhysicalStage
import Tri.Lemma17Ladder
import Tri.Lemma18PhysicalStage

/-!
# Positive-gap doubling ladder for Lemma 19

The decisive Lemma 18 stage ends well before one quarter of the population is
active.  The late full-pool Lemma 19 kernel therefore cannot start
immediately.  This module composes the missing positive-gap doubling stages.

The active-gap condition is propagated pointwise.  The random inactive-pool
majority is an anchored auxiliary event and is charged separately at every
split time, just as in the Lemma 17 gap ladder.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Active-count range and retained positive gap at a Lemma 19 boundary. -/
def Lemma19BoundaryGood
    {n : ℕ} (a targetGap : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  a ≤ s.coarse.1.active ∧
    s.coarse.1.active ≤ a + 1 ∧
    s.coarse.1.ay + targetGap ≤ s.coarse.1.ax

noncomputable instance lemma19BoundaryGoodDecidable
    {n : ℕ} (a targetGap : ℕ) :
    DecidablePred (@Lemma19BoundaryGood n a targetGap) :=
  Classical.decPred _

/-- Physical positive-gap block at ladder rung `j`. -/
noncomputable def lemma19LadderKernel
    (n : ℕ) (h3 : 3 ≤ n)
    (cStar : ℕ) (scale : ℕ → ℕ) :
    ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun j s =>
    lemma17PhysicalStageKernel n h3
      (lemma17StageRemaining (scale j) s)
      (2 * scale j) 0 (cStar * n) s

/-- The positive-gap ladder preserves every stopped-urn hitting potential.
This is the zero active-gap-radius instance of the Lemma 17 preservation
theorem. -/
theorem expect_lemma19Ladder_staged_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (cStar j : ℕ)
    (scale : ℕ → ℕ)
    (hroom :
      ∀ l < j, 2 * scale l + 4 ≤ n)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad]
    (s : InfectionRevealPhysicalState n) :
    expect
        (stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          j s)
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  let zeroRadius : ℕ → ℕ := fun _ => 0
  simpa [lemma19LadderKernel, lemma17LadderKernel,
    zeroRadius] using
    expect_lemma17Ladder_staged_urnEverHit_le
      n h3 cStar j scale zeroRadius hroom Bad s

/-- One positive-gap doubling rung with a dynamic additive reveal-count
witness. -/
theorem lemma19Boundary_stage
    (n q cStar a targetGap targetGapNext rho r M : ℕ)
    (h3 : 3 ≤ n)
    (hcStar : 128 ≤ cStar)
    (ha : 4 ≤ a)
    (hquarter : 4 * a ≤ n)
    (htarget : 2 * a ≤ n)
    (hmean : (2 * a) ^ 3 ≤ r * n ^ 2)
    (hqa : q * (a + 1) ≤ rho ^ 2)
    (hlabelRoom : 5 * (a + 1) ≤ n + 1)
    (hbudget :
      targetGapNext + (rho + 1) + 2 * M ≤
        targetGap)
    (s : InfectionRevealPhysicalState n)
    (hs : Lemma19BoundaryGood a targetGap s)
    (hmajor :
      s.inactive.yIds.card ≤
        s.inactive.xIds.card) :
    terminalFailureMass
        (lemma17PhysicalStageKernel n h3
          (lemma17StageRemaining a s)
          (2 * a) 0 (cStar * n) s)
        (Lemma19BoundaryGood
          (2 * a) targetGapNext)
      ≤ lemma19StageError a q cStar r M := by
  unfold Lemma19BoundaryGood at hs
  let k := lemma17StageRemaining a s
  let R := s.inactive.yIds.card
  let B := s.inactive.xIds.card
  let nu := R + B
  let u := lemma17PoolRemainder k R B
  have hanchor :
      s.coarse.1.active + k = 2 * a := by
    exact
      lemma17StageRemaining_spec a s
        (by omega) hs.1 hs.2.1
  have hkLe : k ≤ a := by
    dsimp only [k] at hanchor ⊢
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
    dsimp only [k] at hkLe
    omega
  have hkRoom : k + 1 ≤ R + B := by
    dsimp only [nu] at hlabelQuarter
    omega
  have hu : u + k + 1 = nu :=
    lemma17PoolRemainder_spec k R B hkRoom
  have hqaLocal :
      q * (k + 1) ≤ rho ^ 2 := by
    exact
      (Nat.mul_le_mul_left q (by omega)).trans hqa
  have hstage :=
    lemma19PhysicalStage_paper
      n q rho a k u nu R B (2 * a)
      cStar r targetGap targetGapNext M
      h3 ha hquarter hlabelQuarter rfl htarget
      hcStar hmean hqaLocal hu rfl
      (by simpa [R, B] using hmajor)
      hbudget s hs.1 hanchor hs.2.2 rfl rfl
      (by
        dsimp only [k] at hanchor ⊢
        omega)
  simpa [Lemma19BoundaryGood,
    Lemma19PhysicalStageRangeGood] using hstage

/-- The conditional inactive-majority anchor at any positive-gap ladder split
is bounded by the same single initial-pool urn tail used for Lemma 17. -/
theorem lemma19_ladder_anchor_failure
    (n : ℕ) (h3 : 3 ≤ n)
    (qMajor cStar j D k u B R : ℕ)
    (scale targetGap : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk : 0 < k)
    (hqa : qMajor * (k + 1) ≤ D ^ 2)
    (hquarter : 4 * (k + 1) ≤ B + R + 1)
    (hstageRoom :
      ∀ l < j, 2 * scale l + 4 ≤ n)
    (hclockRoom :
      scale j + 1 ≤ s.coarse.1.active + k) :
    terminalFailureMass
        (stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          j s)
        (fun z =>
          Lemma19BoundaryGood
              (scale j) (targetGap j) z →
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤ lemma16UrnError qMajor := by
  let zeroRadius : ℕ → ℕ := fun _ => 0
  let μ :=
    stagedIter
      (lemma17LadderKernel
        n h3 cStar scale zeroRadius)
      j s
  have h17 :
      terminalFailureMass μ
          (fun z =>
            Lemma17GapBoundaryGood
                (scale j) cStar (zeroRadius j) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤ lemma16UrnError qMajor := by
    exact
      lemma17_ladder_anchor_failure
        n h3 qMajor cStar j D k u B R
        scale zeroRadius s hBR hgap hx0 hy0 hk
        hqa hquarter hstageRoom hclockRoom
  have hmono :
      terminalFailureMass μ
          (fun z =>
            Lemma19BoundaryGood
                (scale j) (targetGap j) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤
      terminalFailureMass μ
          (fun z =>
            Lemma17GapBoundaryGood
                (scale j) cStar (zeroRadius j) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card) := by
    apply terminalFailureMass_mono
    intro z hz hboundary
    apply hz
    unfold Lemma17GapBoundaryGood
    unfold Lemma19BoundaryGood at hboundary
    dsimp only [zeroRadius]
    exact
      ⟨hboundary.1, hboundary.2.1, by omega⟩
  have hresult := hmono.trans h17
  simpa [μ, zeroRadius, lemma17LadderKernel,
    lemma19LadderKernel] using hresult

/-- A finite positive-gap ladder, with inactive-majority failures supplied as
anchored split-time estimates. -/
theorem lemma19_positive_gap_ladder_of_anchors
    (n q cStar m : ℕ)
    (h3 : 3 ≤ n)
    (scale targetGap rho r M : ℕ → ℕ)
    (δ : ℕ → ℝ≥0∞)
    (hcStar : 128 ≤ cStar)
    (hdouble :
      ∀ j < m, scale (j + 1) = 2 * scale j)
    (ha : ∀ j < m, 4 ≤ scale j)
    (hquarter :
      ∀ j < m, 4 * scale j ≤ n)
    (htarget :
      ∀ j < m, 2 * scale j ≤ n)
    (hmean :
      ∀ j < m,
        (2 * scale j) ^ 3 ≤ r j * n ^ 2)
    (hqa :
      ∀ j < m,
        q * (scale j + 1) ≤ (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m,
        5 * (scale j + 1) ≤ n + 1)
    (hbudget :
      ∀ j < m,
        targetGap (j + 1) + (rho j + 1) +
            2 * M j ≤ targetGap j)
    (s : InfectionRevealPhysicalState n)
    (hs :
      Lemma19BoundaryGood
        (scale 0) (targetGap 0) s)
    (hanchor :
      ∀ j < m,
        terminalFailureMass
          (stagedIter
            (lemma19LadderKernel
              n h3 cStar scale)
            j s)
          (fun z =>
            Lemma19BoundaryGood
                (scale j) (targetGap j) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
          ≤ δ j) :
    terminalFailureMass
        (stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          m s)
        (Lemma19BoundaryGood
          (scale m) (targetGap m))
      ≤
    ∑ j ∈ Finset.range m,
      (lemma19StageError
        (scale j) q cStar (r j) (M j) +
        δ j) := by
  apply
    terminalFailureMass_stagedIter_of_anchors
      (lemma19LadderKernel n h3 cStar scale)
      (fun j =>
        Lemma19BoundaryGood
          (scale j) (targetGap j))
      (fun j z =>
        Lemma19BoundaryGood
            (scale j) (targetGap j) z →
          z.inactive.yIds.card ≤
            z.inactive.xIds.card)
      (fun j =>
        lemma19StageError
          (scale j) q cStar (r j) (M j))
      δ m s hs
  · intro j hj z hzP hzAnchor
    have hstage :=
      lemma19Boundary_stage
        n q cStar (scale j) (targetGap j)
        (targetGap (j + 1)) (rho j) (r j) (M j)
        h3 hcStar (ha j hj) (hquarter j hj)
        (htarget j hj) (hmean j hj) (hqa j hj)
        (hlabelRoom j hj) (hbudget j hj)
        z hzP (hzAnchor hzP)
    simpa [lemma19LadderKernel, hdouble j hj]
      using hstage
  · exact hanchor

/-- Add the final inactive-majority anchor while retaining the endpoint's
active-count range. -/
theorem lemma19_positive_gap_ladder_range_entry
    (n q cStar m : ℕ)
    (h3 : 3 ≤ n)
    (scale targetGap rho r M : ℕ → ℕ)
    (δ : ℕ → ℝ≥0∞)
    (hcStar : 128 ≤ cStar)
    (hdouble :
      ∀ j < m, scale (j + 1) = 2 * scale j)
    (ha : ∀ j < m, 4 ≤ scale j)
    (hquarter :
      ∀ j < m, 4 * scale j ≤ n)
    (htarget :
      ∀ j < m, 2 * scale j ≤ n)
    (hmean :
      ∀ j < m,
        (2 * scale j) ^ 3 ≤ r j * n ^ 2)
    (hqa :
      ∀ j < m,
        q * (scale j + 1) ≤ (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m,
        5 * (scale j + 1) ≤ n + 1)
    (hbudget :
      ∀ j < m,
        targetGap (j + 1) + (rho j + 1) +
            2 * M j ≤ targetGap j)
    (s : InfectionRevealPhysicalState n)
    (hs :
      Lemma19BoundaryGood
        (scale 0) (targetGap 0) s)
    (hanchor :
      ∀ j ≤ m,
        terminalFailureMass
          (stagedIter
            (lemma19LadderKernel
              n h3 cStar scale)
            j s)
          (fun z =>
            Lemma19BoundaryGood
                (scale j) (targetGap j) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
          ≤ δ j) :
    terminalFailureMass
        (stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          m s)
        (fun z =>
          Lemma19BoundaryGood
              (scale m) (targetGap m) z ∧
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤
        (∑ j ∈ Finset.range m,
          (lemma19StageError
            (scale j) q cStar (r j) (M j) +
            δ j)) +
          δ m := by
  let μ :=
    stagedIter
      (lemma19LadderKernel n h3 cStar scale)
      m s
  have hgap :=
    lemma19_positive_gap_ladder_of_anchors
      n q cStar m h3 scale targetGap rho r M δ
      hcStar hdouble ha hquarter htarget hmean
      hqa hlabelRoom hbudget s hs
      (fun j hj => hanchor j hj.le)
  have hmajor :
      terminalFailureMass μ
          (fun z =>
            Lemma19BoundaryGood
                (scale m) (targetGap m) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤ δ m := by
    simpa [μ] using hanchor m le_rfl
  have hinter :=
    terminalFailureMass_inter_le
      μ
      (Lemma19BoundaryGood
        (scale m) (targetGap m))
      (fun z =>
        Lemma19BoundaryGood
            (scale m) (targetGap m) z →
          z.inactive.yIds.card ≤
            z.inactive.xIds.card)
  have hcombined :
      terminalFailureMass μ
          (fun z =>
            Lemma19BoundaryGood
                (scale m) (targetGap m) z ∧
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤
      terminalFailureMass μ
          (fun z =>
            Lemma19BoundaryGood
                (scale m) (targetGap m) z ∧
              (Lemma19BoundaryGood
                  (scale m) (targetGap m) z →
                z.inactive.yIds.card ≤
                  z.inactive.xIds.card)) := by
    apply terminalFailureMass_mono
    intro z hz
    exact ⟨hz.1, hz.2 hz.1⟩
  exact hcombined.trans
    (hinter.trans (add_le_add hgap hmajor))

/-- The positive-gap ladder with every conditional inactive-majority anchor
discharged from one initial-pool urn estimate. -/
theorem lemma19_positive_gap_ladder_closed
    (n q qMajor cStar m : ℕ)
    (h3 : 3 ≤ n)
    (scale targetGap rho r M : ℕ → ℕ)
    (hcStar : 128 ≤ cStar)
    (hdouble :
      ∀ j < m, scale (j + 1) = 2 * scale j)
    (ha : ∀ j < m, 4 ≤ scale j)
    (hquarter :
      ∀ j < m, 4 * scale j ≤ n)
    (htarget :
      ∀ j < m, 2 * scale j ≤ n)
    (hmean :
      ∀ j < m,
        (2 * scale j) ^ 3 ≤ r j * n ^ 2)
    (hqa :
      ∀ j < m,
        q * (scale j + 1) ≤ (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m,
        5 * (scale j + 1) ≤ n + 1)
    (hbudget :
      ∀ j < m,
        targetGap (j + 1) + (rho j + 1) +
            2 * M j ≤ targetGap j)
    (s : InfectionRevealPhysicalState n)
    (hs :
      Lemma19BoundaryGood
        (scale 0) (targetGap 0) s)
    (D k u B R : ℕ)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk : 0 < k)
    (hMajorQa : qMajor * (k + 1) ≤ D ^ 2)
    (hMajorQuarter : 4 * (k + 1) ≤ B + R + 1)
    (hclockRoom :
      ∀ j ≤ m,
        scale j + 1 ≤ s.coarse.1.active + k) :
    terminalFailureMass
        (stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          m s)
        (fun z =>
          Lemma19BoundaryGood
              (scale m) (targetGap m) z ∧
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤
        (∑ j ∈ Finset.range m,
          (lemma19StageError
            (scale j) q cStar (r j) (M j) +
            lemma16UrnError qMajor)) +
          lemma16UrnError qMajor := by
  apply
    lemma19_positive_gap_ladder_range_entry
      n q cStar m h3 scale targetGap rho r M
      (fun _ => lemma16UrnError qMajor)
      hcStar hdouble ha hquarter htarget hmean
      hqa hlabelRoom hbudget s hs
  intro j hj
  apply
    lemma19_ladder_anchor_failure
      n h3 qMajor cStar j D k u B R
      scale targetGap s hBR hgap hx0 hy0 hk
      hMajorQa hMajorQuarter
  · intro l hl
    have hlm : l < m := hl.trans_le hj
    have hqtr := hquarter l hlm
    have hal := ha l hlm
    omega
  · exact hclockRoom j hj

/-- Forgetting the endpoint upper range gives the ordinary Lemma 18 entry
predicate consumed by later interfaces. -/
theorem lemma19_positive_gap_ladder_entry
    (n q cStar m : ℕ)
    (h3 : 3 ≤ n)
    (scale targetGap rho r M : ℕ → ℕ)
    (δ : ℕ → ℝ≥0∞)
    (hcStar : 128 ≤ cStar)
    (hdouble :
      ∀ j < m, scale (j + 1) = 2 * scale j)
    (ha : ∀ j < m, 4 ≤ scale j)
    (hquarter :
      ∀ j < m, 4 * scale j ≤ n)
    (htarget :
      ∀ j < m, 2 * scale j ≤ n)
    (hmean :
      ∀ j < m,
        (2 * scale j) ^ 3 ≤ r j * n ^ 2)
    (hqa :
      ∀ j < m,
        q * (scale j + 1) ≤ (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m,
        5 * (scale j + 1) ≤ n + 1)
    (hbudget :
      ∀ j < m,
        targetGap (j + 1) + (rho j + 1) +
            2 * M j ≤ targetGap j)
    (s : InfectionRevealPhysicalState n)
    (hs :
      Lemma19BoundaryGood
        (scale 0) (targetGap 0) s)
    (hanchor :
      ∀ j ≤ m,
        terminalFailureMass
          (stagedIter
            (lemma19LadderKernel
              n h3 cStar scale)
            j s)
          (fun z =>
            Lemma19BoundaryGood
                (scale j) (targetGap j) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
          ≤ δ j) :
    terminalFailureMass
        (stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          m s)
        (Lemma18PhysicalEntryGood
          (scale m) (targetGap m))
      ≤
        (∑ j ∈ Finset.range m,
          (lemma19StageError
            (scale j) q cStar (r j) (M j) +
            δ j)) +
          δ m := by
  let μ :=
    stagedIter
      (lemma19LadderKernel n h3 cStar scale)
      m s
  have hrange :=
    lemma19_positive_gap_ladder_range_entry
      n q cStar m h3 scale targetGap rho r M δ
      hcStar hdouble ha hquarter htarget hmean
      hqa hlabelRoom hbudget s hs hanchor
  have hmono :=
    terminalFailureMass_mono
      μ
      (Lemma18PhysicalEntryGood
        (scale m) (targetGap m))
      (fun z =>
        Lemma19BoundaryGood
            (scale m) (targetGap m) z ∧
          z.inactive.yIds.card ≤
            z.inactive.xIds.card)
      (fun z hz =>
        ⟨⟨hz.1.1, hz.1.2.2⟩, hz.2⟩)
  exact hmono.trans hrange

end

end Tri

#print axioms Tri.lemma19Boundary_stage
#print axioms Tri.expect_lemma19Ladder_staged_urnEverHit_le
#print axioms Tri.lemma19_ladder_anchor_failure
#print axioms Tri.lemma19_positive_gap_ladder_of_anchors
#print axioms Tri.lemma19_positive_gap_ladder_range_entry
#print axioms Tri.lemma19_positive_gap_ladder_closed
#print axioms Tri.lemma19_positive_gap_ladder_entry
