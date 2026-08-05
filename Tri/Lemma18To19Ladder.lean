/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma19Ladder
import Tri.Lemma18To19Budget
import Tri.Lemma17To18

/-!
# Corrected Lemma 18 to Lemma 19 composition

Lemma 18 ends before the late-activation regime begins.  These adapters insert
the positive-gap doubling ladder and retain its final active-count range until
the existing late full-activation kernel is invoked.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Failure monotonicity when the predicate implication is required only on
the support of the law. -/
theorem terminalFailureMass_mono_on_support
    {α : Type*}
    (p : PMF α)
    (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ z, p z ≠ 0 → Q z → P z) :
    terminalFailureMass p P ≤
      terminalFailureMass p Q := by
  unfold terminalFailureMass
  exact ENNReal.tsum_le_tsum fun z => by
    by_cases hp : p z = 0
    · simp [hp]
    · by_cases hq : Q z
      · have hpred : P z := hPQ z hp hq
        simp [hq, hpred]
      · by_cases hpred : P z <;> simp [hq, hpred]

/-- The stopped-urn potential from before Lemma 18 survives both the decisive
stage and every prefix of the subsequent positive-gap ladder. -/
theorem expect_lemma18ThenLemma19Ladder_staged_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (a D cStar j : ℕ)
    (scale : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom18 : 2 * a + 4 ≤ n)
    (hanchor18 :
      s.coarse.1.active +
          lemma17StageRemaining a s =
        2 * a)
    (hroom19 :
      ∀ l < j, 2 * scale l + 4 ≤ n)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad] :
    expect
        ((lemma18FromGapBoundaryKernel
            n h3 a D cStar s).bind
          (fun z =>
            stagedIter
              (lemma19LadderKernel
                n h3 cStar scale)
              j z))
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  let V : InfectionRevealPhysicalState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts z.inactive)
  rw [expect_bind]
  calc
    (∑' z,
        lemma18FromGapBoundaryKernel
            n h3 a D cStar s z *
          expect
            (stagedIter
              (lemma19LadderKernel
                n h3 cStar scale)
              j z)
            V)
        ≤
      ∑' z,
        lemma18FromGapBoundaryKernel
            n h3 a D cStar s z *
          V z := by
      exact ENNReal.tsum_le_tsum fun z =>
        mul_le_mul_left'
          (expect_lemma19Ladder_staged_urnEverHit_le
            n h3 cStar j scale hroom19 Bad z) _
    _ =
        expect
          (lemma18FromGapBoundaryKernel
            n h3 a D cStar s)
          V := rfl
    _ ≤ V s := by
      unfold lemma18FromGapBoundaryKernel
      exact
        expect_lemma17PhysicalStageKernel_urnEverHit_le
          n h3 (lemma17StageRemaining a s)
          (2 * a) (30 * D) (cStar * n) s
          hroom18 hanchor18 Bad

/-- A conditional inactive-majority failure at a combined Lemma-18/19
boundary is contained in the original inactive-pool urn event whenever the
combined law preserves that stopped-urn potential. -/
theorem terminalFailureMass_lemma19BoundaryMajority_le_urn_of_expect
    (n j Durn k u B R : ℕ)
    (scale targetGap : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (μ : PMF (InfectionRevealPhysicalState n))
    (hBR : B + R = u + k + 1)
    (hgap : R + Durn ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk : 0 < k)
    (hclockRoom :
      scale j + 1 ≤ s.coarse.1.active + k)
    (hpotential :
      expect μ
          (fun z =>
            everHit
              (Lemma16UrnWindowBad Durn u k B R)
              urnStopped
              (infectionInactiveCounts z.inactive))
        ≤
      everHit
        (Lemma16UrnWindowBad Durn u k B R)
        urnStopped
        (infectionInactiveCounts s.inactive)) :
    terminalFailureMass μ
        (fun z =>
          Lemma19BoundaryGood
              (scale j) (targetGap j) z →
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤
        everHit
          (Lemma16UrnWindowBad Durn u k B R)
          urnStopped (B, R) := by
  let Bad := Lemma16UrnWindowBad Durn u k B R
  let V : InfectionRevealPhysicalState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts z.inactive)
  let AnchorGood : InfectionRevealPhysicalState n → Prop :=
    fun z =>
      Lemma19BoundaryGood
          (scale j) (targetGap j) z →
        z.inactive.yIds.card ≤
          z.inactive.xIds.card
  have hinitialTotal :
      s.coarse.1.active + (B + R) = n := by
    have htotal :=
      infectionReveal_active_add_inactive s
    have hlabels :=
      InfectionInactiveView.xIds_card_add_yIds_card
        s.inactive
    omega
  have hcontain :
      ∀ z, ¬ AnchorGood z → V z = 1 := by
    intro z hz
    have hzP :
        Lemma19BoundaryGood
          (scale j) (targetGap j) z := by
      by_contra hnP
      apply hz
      intro hP
      exact False.elim (hnP hP)
    have hzNotMajor :
        ¬ z.inactive.yIds.card ≤
          z.inactive.xIds.card := by
      intro hmajor
      exact hz (fun _ => hmajor)
    have hzFail :
        z.inactive.xIds.card <
          z.inactive.yIds.card :=
      Nat.lt_of_not_ge hzNotMajor
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
      lemma17_remaining_majority_fail_implies_urnWindowBad
        Durn u k B R
        z.inactive.xIds.card z.inactive.yIds.card
        hBR hgap hclock hzFail hk
    exact
      everHit_eq_one_of_mem
        Bad urnStopped
        (infectionInactiveCounts z.inactive) hurn
  have hmass :
      terminalFailureMass μ AnchorGood ≤
        expect μ V := by
    unfold terminalFailureMass expect
    exact ENNReal.tsum_le_tsum fun z => by
      by_cases hz : AnchorGood z
      · simp [hz]
      · rw [hcontain z hz]
        simp [hz]
  have hcounts :
      infectionInactiveCounts s.inactive = (B, R) := by
    simp [infectionInactiveCounts, hx0, hy0]
  calc
    terminalFailureMass μ AnchorGood
        ≤ expect μ V := hmass
    _ ≤ V s := by
      simpa [V, Bad] using hpotential
    _ =
        everHit Bad urnStopped (B, R) := by
      simpa [V, Bad] using
        congrArg (everHit Bad urnStopped) hcounts

/-- Every combined decisive-stage/positive-gap prefix anchor is controlled by
one initial-pool Lemma 16 urn estimate. -/
theorem lemma18ThenLemma19Ladder_anchor_failure
    (n : ℕ) (h3 : 3 ≤ n)
    (qMajor a Ddec cStar j Durn k u B R : ℕ)
    (scale targetGap : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom18 : 2 * a + 4 ≤ n)
    (hanchor18 :
      s.coarse.1.active +
          lemma17StageRemaining a s =
        2 * a)
    (hstageRoom :
      ∀ l < j, 2 * scale l + 4 ≤ n)
    (hBR : B + R = u + k + 1)
    (hgap : R + Durn ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk : 0 < k)
    (hqa : qMajor * (k + 1) ≤ Durn ^ 2)
    (hquarter : 4 * (k + 1) ≤ B + R + 1)
    (hclockRoom :
      scale j + 1 ≤ s.coarse.1.active + k) :
    terminalFailureMass
        ((lemma18FromGapBoundaryKernel
            n h3 a Ddec cStar s).bind
          (fun z =>
            stagedIter
              (lemma19LadderKernel
                n h3 cStar scale)
              j z))
        (fun z =>
          Lemma19BoundaryGood
              (scale j) (targetGap j) z →
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤ lemma16UrnError qMajor := by
  let Bad := Lemma16UrnWindowBad Durn u k B R
  let μ :=
    (lemma18FromGapBoundaryKernel
        n h3 a Ddec cStar s).bind
      (fun z =>
        stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          j z)
  have hpotential :
      expect μ
          (fun z =>
            everHit Bad urnStopped
              (infectionInactiveCounts z.inactive))
        ≤
      everHit Bad urnStopped
        (infectionInactiveCounts s.inactive) := by
    simpa [μ, Bad] using
      expect_lemma18ThenLemma19Ladder_staged_urnEverHit_le
        n h3 a Ddec cStar j scale s hroom18
        hanchor18 hstageRoom Bad
  calc
    terminalFailureMass μ
        (fun z =>
          Lemma19BoundaryGood
              (scale j) (targetGap j) z →
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
        ≤
      everHit Bad urnStopped (B, R) := by
        exact
          terminalFailureMass_lemma19BoundaryMajority_le_urn_of_expect
            n j Durn k u B R scale targetGap s μ
            hBR hgap hx0 hy0 hk hclockRoom
            (by simpa [Bad] using hpotential)
    _ ≤ lemma16UrnError qMajor := by
      unfold Bad everHit
      exact
        lemma17_urn_window_tail_pool
          qMajor Durn (k + 1) k u (B + R) B R
          hqa rfl hBR.symm rfl hquarter hk

/-- The decisive Lemma 18 law followed by the missing positive-gap ladder,
with every random inactive-majority anchor controlled from the decisive
stage's original inactive pool. -/
theorem lemma18FromGapBoundary_then_positive_gap_ladder_range_closed
    (n q qMajor a Ddec cStar m Durn k u B R : ℕ)
    (h3 : 3 ≤ n)
    (scale targetGap rho r M : ℕ → ℕ)
    (hcStar : 128 ≤ cStar)
    (hscale0 : scale 0 = 2 * a)
    (hgap0 : targetGap 0 = 2 * Ddec)
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
    (hroom18 : 2 * a + 4 ≤ n)
    (hanchor18 :
      s.coarse.1.active +
          lemma17StageRemaining a s =
        2 * a)
    (εpre : ℝ≥0∞)
    (hpre :
      terminalFailureMass
          (lemma18FromGapBoundaryKernel
            n h3 a Ddec cStar s)
          (Lemma18PhysicalEntryGood
            (2 * a) (2 * Ddec))
        ≤ εpre)
    (hBR : B + R = u + k + 1)
    (hgap : R + Durn ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk : 0 < k)
    (hMajorQa :
      qMajor * (k + 1) ≤ Durn ^ 2)
    (hMajorQuarter :
      4 * (k + 1) ≤ B + R + 1)
    (hclockRoom :
      ∀ j ≤ m,
        scale j + 1 ≤ s.coarse.1.active + k) :
    terminalFailureMass
        ((lemma18FromGapBoundaryKernel
            n h3 a Ddec cStar s).bind
          (fun z =>
            stagedIter
              (lemma19LadderKernel
                n h3 cStar scale)
              m z))
        (fun z =>
          Lemma19BoundaryGood
              (scale m) (targetGap m) z ∧
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤
        (εpre +
          ∑ j ∈ Finset.range m,
            (lemma19StageError
                (scale j) q cStar (r j) (M j) +
              lemma16UrnError qMajor)) +
          lemma16UrnError qMajor := by
  classical
  let p :=
    lemma18FromGapBoundaryKernel
      n h3 a Ddec cStar s
  let K :=
    lemma19LadderKernel
      n h3 cStar scale
  let P : ℕ → InfectionRevealPhysicalState n → Prop :=
    fun j =>
      Lemma19BoundaryGood
        (scale j) (targetGap j)
  let Anchor : ℕ → InfectionRevealPhysicalState n → Prop :=
    fun j z =>
      P j z →
        z.inactive.yIds.card ≤
          z.inactive.xIds.card
  have hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ 2 * a + 1 := by
    intro z hz
    exact
      lemma17PhysicalStageKernel_active_le
        n h3 (lemma17StageRemaining a s)
        (2 * a) (30 * Ddec) (cStar * n)
        s z hanchor18 (by
          simpa [p, lemma18FromGapBoundaryKernel]
            using hz)
  have hadapt :
      ∀ z, p z ≠ 0 →
        Lemma18PhysicalEntryGood
            (2 * a) (2 * Ddec) z →
          P 0 z := by
    intro z hzp hz
    dsimp only [P]
    rw [hscale0, hgap0]
    exact ⟨hz.1.1, hupper z hzp, hz.1.2⟩
  have hpreP :
      terminalFailureMass p (P 0) ≤ εpre := by
    exact
      (terminalFailureMass_mono_on_support
        p (P 0)
        (Lemma18PhysicalEntryGood
          (2 * a) (2 * Ddec))
        hadapt).trans (by simpa [p] using hpre)
  have hstage :
      ∀ j < m, ∀ z, P j z → Anchor j z →
        terminalFailureMass (K j z) (P (j + 1))
          ≤
        lemma19StageError
          (scale j) q cStar (r j) (M j) := by
    intro j hj z hzP hzA
    have hstep :=
      lemma19Boundary_stage
        n q cStar (scale j) (targetGap j)
        (targetGap (j + 1)) (rho j) (r j) (M j)
        h3 hcStar (ha j hj) (hquarter j hj)
        (htarget j hj) (hmean j hj) (hqa j hj)
        (hlabelRoom j hj) (hbudget j hj)
        z hzP (hzA hzP)
    simpa [K, P, lemma19LadderKernel,
      hdouble j hj] using hstep
  have hanchor :
      ∀ j ≤ m,
        terminalFailureMass
          (p.bind (fun z => stagedIter K j z))
          (Anchor j)
        ≤ lemma16UrnError qMajor := by
    intro j hj
    have hstageRoom :
        ∀ l < j, 2 * scale l + 4 ≤ n := by
      intro l hl
      have hlm : l < m := hl.trans_le hj
      have hqtr := hquarter l hlm
      have hal := ha l hlm
      omega
    simpa [p, K, P, Anchor] using
      lemma18ThenLemma19Ladder_anchor_failure
        n h3 qMajor a Ddec cStar j Durn k u B R
        scale targetGap s hroom18 hanchor18
        hstageRoom hBR hgap hx0 hy0 hk
        hMajorQa hMajorQuarter (hclockRoom j hj)
  have hboundary :
      terminalFailureMass
          (p.bind (fun z => stagedIter K m z))
          (P m)
        ≤
          εpre +
            ∑ j ∈ Finset.range m,
              (lemma19StageError
                  (scale j) q cStar (r j) (M j) +
                lemma16UrnError qMajor) := by
    exact
      terminalFailureMass_bind_stagedIter_of_anchors
        p K P Anchor εpre
        (fun j =>
          lemma19StageError
            (scale j) q cStar (r j) (M j))
        (fun _ => lemma16UrnError qMajor)
        m hpreP hstage
        (fun j hj => hanchor j hj.le)
  let μ :=
    p.bind (fun z => stagedIter K m z)
  have hanchorM :
      terminalFailureMass μ (Anchor m)
        ≤ lemma16UrnError qMajor := by
    simpa [μ] using hanchor m le_rfl
  have hinter :=
    terminalFailureMass_inter_le μ (P m) (Anchor m)
  have hcombined :
      terminalFailureMass μ
          (fun z =>
            Lemma19BoundaryGood
                (scale m) (targetGap m) z ∧
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤
      terminalFailureMass μ
          (fun z => P m z ∧ Anchor m z) := by
    apply terminalFailureMass_mono
    intro z hz
    exact ⟨hz.1, hz.2 hz.1⟩
  exact hcombined.trans
    (hinter.trans (add_le_add hboundary hanchorM))

/-- Compose an arbitrary decisive Lemma 18 endpoint law with the missing
positive-gap doubling ladder. -/
theorem lemma18Endpoint_then_positive_gap_ladder
    (n q cStar m A D : ℕ)
    (h3 : 3 ≤ n)
    (scale targetGap rho r M : ℕ → ℕ)
    (δ : ℕ → ℝ≥0∞)
    (hcStar : 128 ≤ cStar)
    (hscale0 : scale 0 = A)
    (hgap0 : targetGap 0 = 2 * D)
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
    (p : PMF (InfectionRevealPhysicalState n))
    (εpre : ℝ≥0∞)
    (hpre :
      terminalFailureMass p
          (Lemma18PhysicalEntryGood A (2 * D))
        ≤ εpre)
    (hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ A + 1)
    (hanchor :
      ∀ z, p z ≠ 0 →
        Lemma18PhysicalEntryGood A (2 * D) z →
        ∀ j ≤ m,
          terminalFailureMass
            (stagedIter
              (lemma19LadderKernel
                n h3 cStar scale)
              j z)
            (fun y =>
              Lemma19BoundaryGood
                  (scale j) (targetGap j) y →
                y.inactive.yIds.card ≤
                  y.inactive.xIds.card)
            ≤ δ j) :
    terminalFailureMass
        (p.bind
          (fun z =>
            stagedIter
              (lemma19LadderKernel
                n h3 cStar scale)
              m z))
        (fun z =>
          Lemma19BoundaryGood
              (scale m) (targetGap m) z ∧
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤
        εpre +
          ((∑ j ∈ Finset.range m,
            (lemma19StageError
              (scale j) q cStar (r j) (M j) +
              δ j)) +
            δ m) := by
  apply
    terminalFailureMass_bind_le_add_of_support
      p
      (fun z =>
        stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          m z)
      (Lemma18PhysicalEntryGood A (2 * D))
      (fun z =>
        Lemma19BoundaryGood
            (scale m) (targetGap m) z ∧
          z.inactive.yIds.card ≤
            z.inactive.xIds.card)
      εpre
      ((∑ j ∈ Finset.range m,
        (lemma19StageError
          (scale j) q cStar (r j) (M j) +
          δ j)) +
        δ m)
      hpre
  intro z hzp hz
  have hs :
      Lemma19BoundaryGood
        (scale 0) (targetGap 0) z := by
    unfold Lemma19BoundaryGood
    rw [hscale0, hgap0]
    exact ⟨hz.1.1, hupper z hzp, hz.1.2⟩
  exact
    lemma19_positive_gap_ladder_range_entry
      n q cStar m h3 scale targetGap rho r M δ
      hcStar hdouble ha hquarter htarget hmean
      hqa hlabelRoom hbudget z hs
      (hanchor z hzp hz)

/-- A range-strengthened positive-gap ladder endpoint can enter the existing
late full-activation kernel without any separate support assumption. -/
theorem lemma19RangeEntry_then_full_activation_positive_gap_closed
    (n A D Dlabel M targetGap clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hA : 4 ≤ A)
    (hstageRoom : A + 4 ≤ n)
    (hquarterA : n ≤ 4 * A)
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
    (εpre : ℝ≥0∞)
    (hpre :
      terminalFailureMass p
          (fun z =>
            Lemma19BoundaryGood A (2 * D) z ∧
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤ εpre) :
    terminalFailureMass
        (p.bind
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        εpre +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget M targetGap L := by
  apply
    terminalFailureMass_bind_le_add_of_support
      p
      (lemma19FullActivationBudgetKernel
        n h3 clockBudget)
      (fun z =>
        Lemma19BoundaryGood A (2 * D) z ∧
          z.inactive.yIds.card ≤
            z.inactive.xIds.card)
      (Lemma19PhysicalStageRangeGood n targetGap)
      εpre
      (lemma19FullActivationPositiveGapUniformError
        n clockBudget M targetGap L)
      hpre
  intro z _ hz
  have hpool3 : 3 ≤ z.inactive.ids.card := by
    have htotal :=
      infectionReveal_active_add_inactive z
    have hactiveUpper := hz.1.2.1
    omega
  exact
    lemma18PhysicalEntry_full_activation_positive_gap_closed
      n A D Dlabel M targetGap clockBudget L
      h3 hA hquarterA hbudget hgap0 hgapn
      hDlabel hL hscale z
      ⟨⟨hz.1.1, hz.1.2.2⟩, hz.2⟩
      hpool3

/-- The complete corrected Lemma 18--19 handoff: first traverse the missing
positive-gap doubling ladder, then spend a separate late-stage reserve in the
full-activation kernel. -/
theorem lemma18Endpoint_then_ladder_then_full_activation_positive_gap_closed
    (n q cStar m A Ddec Dlate Dlabel Mlate
      targetGapLate clockBudget : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (scale targetGap rho r M : ℕ → ℕ)
    (δ : ℕ → ℝ≥0∞)
    (hcStar : 128 ≤ cStar)
    (hscale0 : scale 0 = A)
    (hgap0 : targetGap 0 = 2 * Ddec)
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
    (hAfinal : 4 ≤ scale m)
    (hstageRoomFinal : scale m + 4 ≤ n)
    (hquarterFinal : n ≤ 4 * scale m)
    (hfinalGap : targetGap m = 2 * Dlate)
    (hbudgetLate :
      targetGapLate + Dlabel + 2 * Mlate ≤
        2 * Dlate)
    (hgapLate0 : 0 < targetGapLate)
    (hgapLaten : targetGapLate < n)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscaleLate :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (p : PMF (InfectionRevealPhysicalState n))
    (εpre : ℝ≥0∞)
    (hpre :
      terminalFailureMass p
          (Lemma18PhysicalEntryGood A (2 * Ddec))
        ≤ εpre)
    (hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ A + 1)
    (hanchor :
      ∀ z, p z ≠ 0 →
        Lemma18PhysicalEntryGood A (2 * Ddec) z →
        ∀ j ≤ m,
          terminalFailureMass
            (stagedIter
              (lemma19LadderKernel
                n h3 cStar scale)
              j z)
            (fun y =>
              Lemma19BoundaryGood
                  (scale j) (targetGap j) y →
                y.inactive.yIds.card ≤
                  y.inactive.xIds.card)
            ≤ δ j) :
    terminalFailureMass
        ((p.bind
          (fun z =>
            stagedIter
              (lemma19LadderKernel
                n h3 cStar scale)
              m z)).bind
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood
          n targetGapLate)
      ≤
        (εpre +
          ((∑ j ∈ Finset.range m,
            (lemma19StageError
              (scale j) q cStar (r j) (M j) +
              δ j)) +
            δ m)) +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget Mlate targetGapLate L := by
  let μ :=
    p.bind
      (fun z =>
        stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          m z)
  have hμ :
      terminalFailureMass μ
          (fun z =>
            Lemma19BoundaryGood
                (scale m) (targetGap m) z ∧
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤
          εpre +
            ((∑ j ∈ Finset.range m,
              (lemma19StageError
                (scale j) q cStar (r j) (M j) +
                δ j)) +
              δ m) := by
    simpa [μ] using
      lemma18Endpoint_then_positive_gap_ladder
        n q cStar m A Ddec h3 scale targetGap
        rho r M δ hcStar hscale0 hgap0 hdouble
        ha hquarter htarget hmean hqa hlabelRoom
        hbudget p εpre hpre hupper hanchor
  have hμLate :
      terminalFailureMass μ
          (fun z =>
            Lemma19BoundaryGood
                (scale m) (2 * Dlate) z ∧
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤
          εpre +
            ((∑ j ∈ Finset.range m,
              (lemma19StageError
                (scale j) q cStar (r j) (M j) +
                δ j)) +
              δ m) := by
    simpa [hfinalGap] using hμ
  simpa [μ] using
    lemma19RangeEntry_then_full_activation_positive_gap_closed
      n (scale m) Dlate Dlabel Mlate
      targetGapLate clockBudget L h3 hAfinal
      hstageRoomFinal hquarterFinal hbudgetLate
      hgapLate0 hgapLaten hDlabel hL hscaleLate
      μ
      (εpre +
        ((∑ j ∈ Finset.range m,
          (lemma19StageError
            (scale j) q cStar (r j) (M j) +
            δ j)) +
          δ m))
      hμLate

end

end Tri

#print axioms Tri.lemma18Endpoint_then_positive_gap_ladder
#print axioms Tri.lemma19RangeEntry_then_full_activation_positive_gap_closed
#print axioms Tri.lemma18Endpoint_then_ladder_then_full_activation_positive_gap_closed
#print axioms Tri.terminalFailureMass_mono_on_support
#print axioms Tri.expect_lemma18ThenLemma19Ladder_staged_urnEverHit_le
#print axioms Tri.terminalFailureMass_lemma19BoundaryMajority_le_urn_of_expect
#print axioms Tri.lemma18ThenLemma19Ladder_anchor_failure
#print axioms Tri.lemma18FromGapBoundary_then_positive_gap_ladder_range_closed
