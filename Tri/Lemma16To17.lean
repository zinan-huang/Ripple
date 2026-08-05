/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16CountedPath
import Tri.Lemma17Ladder

/-!
# Physical handoff from Lemma 16 to Lemma 17

Lemma 16 runs on a counted physical path.  This module forgets the path-local
counter and exposes exactly the active-count and active-gap boundary consumed
by the Lemma 17 ladder.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Run the stopped Lemma 16 path and retain its physical endpoint. -/
noncomputable def lemma16PhysicalStageKernel
    (n : ℕ) (h3 : 3 ≤ n) (k T : ℕ) :
    InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun s =>
    (iter (lemma16CountedPathStep n h3 k) T
      (lemma16CountedPathInitial s)).map
        (fun z => z.path.current)

/-- The strengthened counted-path endpoint is a valid first Lemma 17
gap boundary. -/
theorem lemma16CountedPathGood_to_gapBoundary
    {n a rho cStar : ℕ}
    (z : Lemma16CountedPathState n)
    (hz : Lemma16CountedPathGood a rho cStar z) :
    Lemma17GapBoundaryGood a cStar rho z.path.current := by
  refine ⟨hz.1, hz.2.1, ?_⟩
  exact hz.2.2.trans
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right rho
        (Nat.mul_le_mul_right cStar (by omega)))
      z.path.current.coarse.1.ax)

/-- Physical Lemma 16 endpoint in the exact form consumed by the closed
Lemma 17 ladder. -/
theorem lemma16PhysicalStage_normalized
    (n q a k u nu R B rho cStar : ℕ)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q)
    (hquarter : 4 * a ≤ n)
    (hcStar : 640 ≤ cStar)
    (hroot : a ^ 5 * q * n ≤ n ^ 5)
    (hqa : q * a ≤ rho ^ 2)
    (hqaOrder : q ≤ a)
    (hrho : 1 ≤ rho)
    (hnu : nu + 1 = n)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hmajor : R ≤ B)
    (s : InfectionRevealPhysicalState n)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (lemma16PhysicalStageKernel
          n h3 k (cStar * q * n) s)
        (Lemma17GapBoundaryGood a cStar rho)
      ≤ 3 * lemma16UrnError q := by
  let μ :=
    iter (lemma16CountedPathStep n h3 k)
      (cStar * q * n)
      (lemma16CountedPathInitial s)
  have hcounted :
      terminalFailureMass μ
          (Lemma16CountedPathGood a rho cStar)
        ≤ 3 * lemma16UrnError q := by
    simpa [μ] using
      lemma16CountedPath_normalized
        n q a k u nu R B rho cStar
        h3 hlog hquarter hcStar hroot hqa hqaOrder
        hrho hnu hk huk hRB hmajor s hx0 hy0 hk0
  rw [show
    lemma16PhysicalStageKernel
        n h3 k (cStar * q * n) s =
      μ.map (fun z => z.path.current) by
        rfl]
  rw [terminalFailureMass_map]
  exact
    (terminalFailureMass_mono
      μ
      (fun z =>
        Lemma17GapBoundaryGood
          a cStar rho z.path.current)
      (Lemma16CountedPathGood a rho cStar)
      (fun z hz =>
        lemma16CountedPathGood_to_gapBoundary z hz)).trans
      hcounted

/-- A reachable Lemma 16 counted path whose target leaves four molecules of
room still has at least three inactive identities. -/
theorem lemma16CountedPathInv_inactive_three
    (n k a : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom : a + 4 ≤ n)
    (hanchorActive : s.coarse.1.active + k = a)
    (z : Lemma16CountedPathState n)
    (hz : Lemma16CountedPathInv s k z) :
    ∃ m, m + 3 = z.path.current.inactive.ids.card := by
  have hanchor : z.path.anchor = s := hz.1
  have hlength : z.path.revealed.length ≤ k + 1 := hz.2
  have hledger := z.path.hactiveLedger
  rw [hanchor] at hledger
  have hactive :
      z.path.current.coarse.1.active ≤ a + 1 := by
    omega
  have htotal :=
    infectionReveal_active_add_inactive z.path.current
  have hthree :
      3 ≤ z.path.current.inactive.ids.card := by
    omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hthree
  exact ⟨m, by omega⟩

/-- One stopped Lemma 16 counted step preserves every stopped-urn hitting
potential of the current inactive counts. -/
theorem expect_lemma16CountedPathStep_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (k a : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom : a + 4 ≤ n)
    (hanchorActive : s.coarse.1.active + k = a)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad]
    (z : Lemma16CountedPathState n)
    (hz : Lemma16CountedPathInv s k z) :
    expect
        (lemma16CountedPathStep n h3 k z)
        (fun y =>
          everHit Bad urnStopped
            (infectionInactiveCounts
              y.path.current.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts
            z.path.current.inactive) := by
  by_cases hreach :
      InfectionRevealPhysicalFirstKReached k z.path
  · unfold lemma16CountedPathStep
    rw [if_pos hreach, expect_pure]
  · obtain ⟨m, hm⟩ :=
      lemma16CountedPathInv_inactive_three
        n k a s hroom hanchorActive z hz
    let W : InfectionRevealPhysicalState n → ℝ≥0∞ :=
      fun y =>
        everHit Bad urnStopped
          (infectionInactiveCounts y.inactive)
    calc
      expect
          (lemma16CountedPathStep n h3 k z)
          (fun y => W y.path.current) =
        expect
          ((lemma16CountedPathStep n h3 k z).map
            (fun y => y.path.current))
          W := by
            exact
              (expect_map
                (lemma16CountedPathStep n h3 k z)
                (fun y => y.path.current) W).symm
      _ =
        expect
          (infectionRevealPhysicalStep n h3
            z.path.current)
          W := by
            congr 1
            unfold lemma16CountedPathStep
              infectionRevealPhysicalStep
            rw [if_neg hreach, PMF.map_comp]
            rfl
      _ ≤ W z.path.current :=
        expect_infectionRevealPhysicalStep_urnEverHit_le
          n h3 z.path.current hm Bad

/-- The complete physical Lemma 16 stage preserves the same initial-pool urn
potential later used at every Lemma 17 ladder anchor. -/
theorem expect_lemma16PhysicalStageKernel_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (k a T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom : a + 4 ≤ n)
    (hanchorActive : s.coarse.1.active + k = a)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad] :
    expect
        (lemma16PhysicalStageKernel n h3 k T s)
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  let K := lemma16CountedPathStep n h3 k
  let P := Lemma16CountedPathInv s k
  let V : Lemma16CountedPathState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts
          z.path.current.inactive)
  have hclosed :
      ∀ z, P z → ∀ y, K z y ≠ 0 → P y := by
    intro z hz y hy
    exact
      lemma16CountedPathStep_inv_closed
        n h3 k s z y hz hy
  have hstep :
      ∀ z, P z → expect (K z) V ≤ V z := by
    intro z hz
    exact
      expect_lemma16CountedPathStep_urnEverHit_le
        n h3 k a s hroom hanchorActive Bad z hz
  have hinitial :
      P (lemma16CountedPathInitial s) := by
    constructor
    · rfl
    · simp [lemma16CountedPathInitial,
        infectionRevealPhysicalPathInitial]
  have hiter :=
    expect_iter_le_of_support_invariant
      K P V 1 hclosed
      (fun z hz => by simpa using hstep z hz)
      T (lemma16CountedPathInitial s) hinitial
  unfold lemma16PhysicalStageKernel
  rw [expect_map]
  simpa [K, P, V, lemma16CountedPathInitial,
    infectionRevealPhysicalPathInitial] using hiter

/-- A common stopped-urn potential survives Lemma 16 followed by any finite
prefix of the Lemma 17 ladder. -/
theorem expect_lemma16_then_lemma17_staged_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (k a T cStar j : ℕ)
    (scale rho : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom16 : a + 4 ≤ n)
    (hanchorActive : s.coarse.1.active + k = a)
    (hroom17 :
      ∀ l < j, 2 * scale l + 4 ≤ n)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad] :
    expect
        ((lemma16PhysicalStageKernel n h3 k T s).bind
          (fun z =>
            stagedIter
              (lemma17LadderKernel
                n h3 cStar scale rho)
              j z))
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  let p := lemma16PhysicalStageKernel n h3 k T s
  let V : InfectionRevealPhysicalState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts z.inactive)
  rw [expect_bind']
  calc
    (∑' z, p z *
        expect
          (stagedIter
            (lemma17LadderKernel
              n h3 cStar scale rho)
            j z)
          V)
        ≤
      ∑' z, p z * V z := by
        exact ENNReal.tsum_le_tsum fun z =>
          mul_le_mul_right
            (expect_lemma17Ladder_staged_urnEverHit_le
              n h3 cStar j scale rho
              hroom17 Bad z)
            (p z)
    _ = expect p V := rfl
    _ ≤ V s := by
      exact
        expect_lemma16PhysicalStageKernel_urnEverHit_le
          n h3 k a T s hroom16 hanchorActive Bad

/-- Failure of an inactive-majority ladder anchor is bounded by the expected
initial-pool urn potential under any physical-state law. -/
theorem terminalFailureMass_gapBoundary_anchor_le_expect_urn
    (n cStar a rho D k u B R : ℕ)
    (s : InfectionRevealPhysicalState n)
    (μ : PMF (InfectionRevealPhysicalState n))
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hk : 0 < k)
    (hclockRoom :
      a + 1 ≤ s.coarse.1.active + k) :
    terminalFailureMass μ
        (fun z =>
          Lemma17GapBoundaryGood a cStar rho z →
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤
    expect μ
      (fun z =>
        everHit
          (Lemma16UrnWindowBad D u k B R)
          urnStopped
          (infectionInactiveCounts z.inactive)) := by
  let Bad := Lemma16UrnWindowBad D u k B R
  let V : InfectionRevealPhysicalState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts z.inactive)
  let AnchorGood : InfectionRevealPhysicalState n → Prop :=
    fun z =>
      Lemma17GapBoundaryGood a cStar rho z →
        z.inactive.yIds.card ≤
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
        D u k B R
        z.inactive.xIds.card z.inactive.yIds.card
        hBR hgap hclock hzFail hk
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

/-- Every Lemma 17 anchor after the Lemma 16 stage is charged to the same
urn event in the original inactive pool. -/
theorem lemma16_then_lemma17_anchor_failure_le_urn
    (n : ℕ) (h3 : 3 ≤ n)
    (k16 a16 T cStar j D k u B R : ℕ)
    (scale rho : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom16 : a16 + 4 ≤ n)
    (hanchor16 : s.coarse.1.active + k16 = a16)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk : 0 < k)
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
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤
        everHit
          (Lemma16UrnWindowBad D u k B R)
          urnStopped (B, R) := by
  let Bad := Lemma16UrnWindowBad D u k B R
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
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤
      expect μ
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive)) := by
    exact
      terminalFailureMass_gapBoundary_anchor_le_expect_urn
        n cStar (scale j) (rho j) D k u B R
        s μ hx0 hy0 hBR hgap hk hclockRoom
  have hpotential :
      expect μ
          (fun z =>
            everHit Bad urnStopped
              (infectionInactiveCounts z.inactive))
        ≤
      everHit Bad urnStopped
        (infectionInactiveCounts s.inactive) := by
    exact
      expect_lemma16_then_lemma17_staged_urnEverHit_le
        n h3 k16 a16 T cStar j scale rho s
        hroom16 hanchor16 hroom17 Bad
  have hcounts :
      infectionInactiveCounts s.inactive = (B, R) := by
    simp [infectionInactiveCounts, hx0, hy0]
  calc
    terminalFailureMass μ
          (fun z =>
            Lemma17GapBoundaryGood
                (scale j) cStar (rho j) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤
      expect μ
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive)) :=
      hmass
    _ ≤
      everHit Bad urnStopped
        (infectionInactiveCounts s.inactive) :=
      hpotential
    _ = everHit Bad urnStopped (B, R) := by
      simpa using congrArg (everHit Bad urnStopped) hcounts

/-- The common original-pool urn event gives the normalized exponential
bound for every post-Lemma-16 ladder anchor. -/
theorem lemma16_then_lemma17_anchor_failure
    (n : ℕ) (h3 : 3 ≤ n)
    (qMajor k16 a16 T cStar j D k u B R : ℕ)
    (scale rho : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (hroom16 : a16 + 4 ≤ n)
    (hanchor16 : s.coarse.1.active + k16 = a16)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk : 0 < k)
    (hqa : qMajor * (k + 1) ≤ D ^ 2)
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
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤ lemma16UrnError qMajor := by
  calc
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
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤
        everHit
          (Lemma16UrnWindowBad D u k B R)
          urnStopped (B, R) :=
      lemma16_then_lemma17_anchor_failure_le_urn
        n h3 k16 a16 T cStar j D k u B R
        scale rho s hroom16 hanchor16 hBR hgap
        hx0 hy0 hk hroom17 hclockRoom
    _ ≤ lemma16UrnError qMajor := by
      unfold everHit
      exact
        lemma17_urn_window_tail_pool
          qMajor D (k + 1) k u (B + R) B R
          hqa rfl hBR.symm rfl hquarter hk

/-- End-to-end normalized handoff from the one-active Lemma 16 stage through
the closed Lemma 17 doubling ladder.  All inactive-majority anchors use one
urn event in the original inactive pool. -/
theorem lemma16_then_lemma17_ladder_closed
    (n q16 qStage qMajor a16 k16 u16 nu R B rho16
      cStar m DMajor kMajor uMajor : ℕ)
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
      ∀ j < m, scale (j + 1) = 2 * scale j)
    (hroot :
      ∀ j < m, 19 * rho j ≤ 14 * rho (j + 1))
    (ha : ∀ j < m, 4 ≤ scale j)
    (hquarter :
      ∀ j < m, 4 * scale j ≤ n)
    (htarget :
      ∀ j < m, 2 * scale j ≤ n)
    (hrho : ∀ j < m, 1 ≤ rho j)
    (hbias :
      ∀ j < m, 38 * cStar * rho j ≤ scale j)
    (hactiveScale :
      ∀ j < m, 76 * cStar * r j ≤ scale j)
    (hmean :
      ∀ j < m,
        (2 * scale j) ^ 3 ≤ r j * n ^ 2)
    (hqa :
      ∀ j < m,
        qStage * (scale j + 1) ≤ (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m, 5 * (scale j + 1) ≤ n + 1)
    (hMajorBR :
      B + R = uMajor + kMajor + 1)
    (hMajorGap : R + DMajor ≤ B)
    (hkMajor : 0 < kMajor)
    (hMajorQa :
      qMajor * (kMajor + 1) ≤ DMajor ^ 2)
    (hMajorQuarter :
      4 * (kMajor + 1) ≤ B + R + 1)
    (hclockRoom :
      ∀ j < m,
        scale j + 1 ≤
          (1 : ℕ) + kMajor)
    (s : InfectionRevealPhysicalState n)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R) :
    terminalFailureMass
        ((lemma16PhysicalStageKernel
            n h3 k16 (cStar * q16 * n) s).bind
          (fun z =>
            stagedIter
              (lemma17LadderKernel
                n h3 cStar scale rho)
              m z))
        (Lemma17GapBoundaryGood
          (scale m) cStar (rho m))
      ≤
        3 * lemma16UrnError q16 +
          ∑ j ∈ Finset.range m,
            (lemma17StageError
                (scale j) qStage cStar
                (rho j) (r j) +
              lemma16UrnError qMajor) := by
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
    lemma16PhysicalStageKernel
      n h3 k16 (cStar * q16 * n) s
  let K :=
    lemma17LadderKernel
      n h3 cStar scale rho
  let P : ℕ → InfectionRevealPhysicalState n → Prop :=
    fun j => Lemma17GapBoundaryGood
      (scale j) cStar (rho j)
  let Anchor : ℕ → InfectionRevealPhysicalState n → Prop :=
    fun j z =>
      P j z →
        z.inactive.yIds.card ≤ z.inactive.xIds.card
  have hpre :
      terminalFailureMass p (P 0) ≤
        3 * lemma16UrnError q16 := by
    simpa [p, P, hscale0, hrho0] using
      lemma16PhysicalStage_normalized
        n q16 a16 k16 u16 nu R B rho16 cStar
        h3 hlog hquarter16 hcStar16 hroot16 hqa16
        hqaOrder16 hrho16 hnu hk16 hu16 hRB hmajor0
        s hx0 hy0 hk16pos
  have hstage :
      ∀ j < m, ∀ z, P j z → Anchor j z →
        terminalFailureMass (K j z) (P (j + 1)) ≤
          lemma17StageError
            (scale j) qStage cStar (rho j) (r j) := by
    intro j hj z hzP hzA
    have hlocal :=
      lemma17GapBoundary_stage
        n qStage cStar (scale j) (rho j)
        (rho (j + 1)) (r j) h3 hcStar hcTwo
        (ha j hj) (hquarter j hj) (htarget j hj)
        (hrho j hj) (hroot j hj)
        (hbias j hj) (hactiveScale j hj)
        (hmean j hj) (hqa j hj)
        (hlabelRoom j hj) z hzP (hzA hzP)
    have hnext := hdouble j hj
    simpa [K, P, hnext] using hlocal
  have hanchor :
      ∀ j < m,
        terminalFailureMass
          (p.bind (fun z => stagedIter K j z))
          (Anchor j) ≤ lemma16UrnError qMajor := by
    intro j hj
    have hroom17 :
        ∀ l < j, 2 * scale l + 4 ≤ n := by
      intro l hl
      have hlm := hl.trans hj
      have hal := ha l hlm
      have hqtr := hquarter l hlm
      omega
    have hclock :
        scale j + 1 ≤
          s.coarse.1.active + kMajor := by
      rw [hstartActive]
      exact hclockRoom j hj
    simpa [p, K, Anchor, P] using
      lemma16_then_lemma17_anchor_failure
        n h3 qMajor k16 a16 (cStar * q16 * n)
        cStar j DMajor kMajor uMajor B R
        scale rho s hroom16 hanchor16 hMajorBR
        hMajorGap hx0 hy0 hkMajor hMajorQa
        hMajorQuarter hroom17 hclock
  exact
    terminalFailureMass_bind_stagedIter_of_anchors
      p K P Anchor
      (3 * lemma16UrnError q16)
      (fun j =>
        lemma17StageError
          (scale j) qStage cStar (rho j) (r j))
      (fun _ => lemma16UrnError qMajor)
      m hpre hstage hanchor

end

end Tri

#print axioms Tri.lemma16CountedPathGood_to_gapBoundary
#print axioms Tri.lemma16PhysicalStage_normalized
#print axioms Tri.lemma16CountedPathInv_inactive_three
#print axioms Tri.expect_lemma16CountedPathStep_urnEverHit_le
#print axioms Tri.expect_lemma16PhysicalStageKernel_urnEverHit_le
#print axioms Tri.expect_lemma16_then_lemma17_staged_urnEverHit_le
#print axioms Tri.terminalFailureMass_gapBoundary_anchor_le_expect_urn
#print axioms Tri.lemma16_then_lemma17_anchor_failure_le_urn
#print axioms Tri.lemma16_then_lemma17_anchor_failure
#print axioms Tri.lemma16_then_lemma17_ladder_closed
