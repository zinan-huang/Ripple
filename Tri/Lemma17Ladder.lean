/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17StagePotential
import Tri.Lemma17InactiveMajorityTail

/-!
# Composition of Lemma 17 doubling stages

The active count at a physical checkpoint is either the target or one above
it.  Additive witnesses choose the remaining local block and pool sizes
without exposing natural subtraction.  Heterogeneous stage kernels then
compose by a union bound.  The next-anchor inactive-majority term remains an
explicit input, ready for the recentred Lemma 15 window estimate.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Remaining reveals to the exact target `2a`, chosen without exposing
natural subtraction. -/
noncomputable def lemma17StageRemaining
    {n : ℕ} (a : ℕ)
    (s : InfectionRevealPhysicalState n) : ℕ := by
  classical
  exact
    if h : ∃ k, s.coarse.1.active + k = 2 * a then
      Classical.choose h
    else 0

theorem lemma17StageRemaining_spec
    {n : ℕ} (a : ℕ)
    (s : InfectionRevealPhysicalState n)
    (ha : 1 ≤ a)
    (hlo : a ≤ s.coarse.1.active)
    (hhi : s.coarse.1.active ≤ a + 1) :
    s.coarse.1.active +
        lemma17StageRemaining a s =
      2 * a := by
  have hle : s.coarse.1.active ≤ 2 * a := by
    omega
  obtain ⟨k, hk⟩ :=
    Nat.exists_eq_add_of_le hle
  have hex :
      ∃ k, s.coarse.1.active + k = 2 * a :=
    ⟨k, hk.symm⟩
  unfold lemma17StageRemaining
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- Remaining inactive identities after a local block, again represented by
an additive witness rather than natural subtraction. -/
noncomputable def lemma17PoolRemainder
    (k R B : ℕ) : ℕ := by
  classical
  exact
    if h : ∃ u, u + k + 1 = R + B then
      Classical.choose h
    else 0

theorem lemma17PoolRemainder_spec
    (k R B : ℕ)
    (hroom : k + 1 ≤ R + B) :
    lemma17PoolRemainder k R B + k + 1 =
      R + B := by
  obtain ⟨u, hu⟩ :=
    Nat.exists_eq_add_of_le hroom
  have hex : ∃ u, u + k + 1 = R + B := by
    refine ⟨u, ?_⟩
    omega
  unfold lemma17PoolRemainder
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- The reusable boundary invariant between consecutive Lemma 17 stages. -/
def Lemma17BoundaryGood
    {n : ℕ} (a cStar rho : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  a ≤ s.coarse.1.active ∧
    s.coarse.1.active ≤ a + 1 ∧
    s.coarse.1.ay ≤
      s.coarse.1.ax + 14 * cStar * rho ∧
    s.inactive.yIds.card ≤ s.inactive.xIds.card

noncomputable instance lemma17BoundaryGoodDecidable
    {n : ℕ} (a cStar rho : ℕ) :
    DecidablePred (@Lemma17BoundaryGood n a cStar rho) :=
  Classical.decPred _

/-- The physical block kernel used at ladder rung `j`. -/
noncomputable def lemma17LadderKernel
    (n : ℕ) (h3 : 3 ≤ n)
    (cStar : ℕ) (scale rho : ℕ → ℕ) :
    ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun j s =>
    lemma17PhysicalStageKernel n h3
      (lemma17StageRemaining (scale j) s)
      (2 * scale j)
      (19 * cStar * rho j)
      (cStar * n) s

/-- A finite sequence of paper-scale stages composes.  The only remaining
external stage event is preservation of the inactive-label majority; its
failure mass is exposed explicitly for discharge by the recentred Lemma 15
window theorem. -/
theorem lemma17_ladder
    (n q cStar m : ℕ)
    (h3 : 3 ≤ n)
    (scale rho r : ℕ → ℕ)
    (εMajor : ℕ → ℝ≥0∞)
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
        q * (scale j + 1) ≤ (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m, 5 * (scale j + 1) ≤ n + 1)
    (hmajorTail :
      ∀ j < m,
        ∀ s,
          Lemma17BoundaryGood
              (scale j) cStar (rho j) s →
          terminalFailureMass
              (lemma17LadderKernel
                n h3 cStar scale rho j s)
              (fun z =>
                z.inactive.yIds.card ≤
                  z.inactive.xIds.card)
            ≤ εMajor j)
    (s : InfectionRevealPhysicalState n)
    (hs :
      Lemma17BoundaryGood
        (scale 0) cStar (rho 0) s) :
    terminalFailureMass
        (stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          m s)
        (Lemma17BoundaryGood
          (scale m) cStar (rho m))
      ≤
    ∑ j ∈ Finset.range m,
      (lemma17StageError
        (scale j) q cStar (rho j) (r j) +
        εMajor j) := by
  apply terminalFailureMass_stagedIter
    (lemma17LadderKernel n h3 cStar scale rho)
    (fun j =>
      Lemma17BoundaryGood
        (scale j) cStar (rho j))
    (fun j =>
      lemma17StageError
        (scale j) q cStar (rho j) (r j) +
        εMajor j)
    m
  · intro j hj s hs
    let a := scale j
    let rhoj := rho j
    let rj := r j
    let k := lemma17StageRemaining a s
    let R := s.inactive.yIds.card
    let B := s.inactive.xIds.card
    let nu := R + B
    let u := lemma17PoolRemainder k R B
    have hanchor :
        s.coarse.1.active + k = 2 * a := by
      exact
        lemma17StageRemaining_spec
          a s
          (by simpa [a] using
            (ha j hj).trans' (by omega))
          (by simpa [a] using hs.1)
          (by simpa [a] using hs.2.1)
    have hkLe : k ≤ a := by
      have hstart := hs.1
      dsimp only [k, a] at hanchor ⊢
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
      have hroomj := hlabelRoom j hj
      have hactiveHi := hs.2.1
      dsimp only [a] at hkOne hactiveHi hroomj ⊢
      omega
    have hkRoom : k + 1 ≤ R + B := by
      dsimp only [nu] at hlabelQuarter
      omega
    have hu : u + k + 1 = nu := by
      exact lemma17PoolRemainder_spec k R B hkRoom
    have hqaLocal :
        q * (k + 1) ≤ rhoj ^ 2 := by
      calc
        q * (k + 1) ≤ q * (a + 1) :=
          Nat.mul_le_mul_left q hkOne
        _ ≤ rhoj ^ 2 := by
          simpa [a, rhoj] using hqa j hj
    let μ :=
      lemma17LadderKernel
        n h3 cStar scale rho j s
    let RangeGood :
        InfectionRevealPhysicalState n → Prop :=
      Lemma17PhysicalStageRangeGood
        (2 * a) (19 * cStar * rhoj)
    let MajorityGood :
        InfectionRevealPhysicalState n → Prop :=
      fun z =>
        z.inactive.yIds.card ≤
          z.inactive.xIds.card
    have hrange :
        terminalFailureMass μ RangeGood ≤
          lemma17StageError a q cStar rhoj rj := by
      dsimp only [μ, lemma17LadderKernel]
      exact
        lemma17PhysicalStage_paper_range
          n q rhoj a k u nu R B (2 * a)
          cStar rj h3
          (by simpa [a] using ha j hj)
          (by simpa [a] using hquarter j hj)
          hlabelQuarter le_rfl
          (by simpa [a] using htarget j hj)
          hcStar hcTwo
          (by simpa [rhoj] using hrho j hj)
          (by simpa [a, rhoj] using hbias j hj)
          (by simpa [a, rj] using hactiveScale j hj)
          (by simpa [a, rj] using hmean j hj)
          hqaLocal
          hu rfl
          (by simpa [R, B] using hs.2.2.2)
          s
          (by simpa [a] using hs.1)
          hanchor
          (by simpa [a, rhoj] using hs.2.2.1)
          rfl rfl
          (by
            have haj := ha j hj
            have hhi := hs.2.1
            dsimp only [k, a] at hanchor ⊢
            omega)
    have hmajor :
        terminalFailureMass μ MajorityGood ≤
          εMajor j := by
      simpa [μ, MajorityGood] using
        hmajorTail j hj s hs
    have hinter :
        terminalFailureMass μ
            (fun z => RangeGood z ∧ MajorityGood z)
          ≤ lemma17StageError a q cStar rhoj rj +
              εMajor j :=
      (terminalFailureMass_inter_le
        μ RangeGood MajorityGood).trans
        (add_le_add hrange hmajor)
    have hnext :
        ∀ z, RangeGood z ∧ MajorityGood z →
          Lemma17BoundaryGood
            (scale (j + 1)) cStar (rho (j + 1)) z := by
      intro z hz
      have hscaleNext := hdouble j hj
      have hgap :=
        lemma17PhysicalStageGood_to_next
          (2 * a) cStar rhoj (rho (j + 1))
          (by simpa [rhoj] using hroot j hj)
          z ⟨hz.1.1, hz.1.2.2⟩
      unfold Lemma17BoundaryGood
      refine ⟨?_, ?_, ?_, hz.2⟩
      · simpa [a, hscaleNext] using hgap.1
      · simpa [a, hscaleNext] using hz.1.2.1
      · simpa [a, rhoj, hscaleNext] using hgap.2
    exact
      (terminalFailureMass_mono
        μ
        (Lemma17BoundaryGood
          (scale (j + 1)) cStar (rho (j + 1)))
        (fun z => RangeGood z ∧ MajorityGood z)
        hnext).trans hinter
  · exact hs

/-- The active-count and active-gap boundary, without imposing a pointwise
condition on the random inactive anchor. -/
def Lemma17GapBoundaryGood
    {n : ℕ} (a cStar rho : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  a ≤ s.coarse.1.active ∧
    s.coarse.1.active ≤ a + 1 ∧
    s.coarse.1.ay ≤
      s.coarse.1.ax + 14 * cStar * rho

noncomputable instance lemma17GapBoundaryGoodDecidable
    {n : ℕ} (a cStar rho : ℕ) :
    DecidablePred (@Lemma17GapBoundaryGood n a cStar rho) :=
  Classical.decPred _

/-- One dynamic-overshoot stage from a good active-gap boundary and a good
random inactive-majority anchor. -/
theorem lemma17GapBoundary_stage
    (n q cStar a rho rhoNext r : ℕ)
    (h3 : 3 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (ha : 4 ≤ a)
    (hquarter : 4 * a ≤ n)
    (htarget : 2 * a ≤ n)
    (hrho : 1 ≤ rho)
    (hroot : 19 * rho ≤ 14 * rhoNext)
    (hbias : 38 * cStar * rho ≤ a)
    (hactiveScale : 76 * cStar * r ≤ a)
    (hmean : (2 * a) ^ 3 ≤ r * n ^ 2)
    (hqa : q * (a + 1) ≤ rho ^ 2)
    (hlabelRoom : 5 * (a + 1) ≤ n + 1)
    (s : InfectionRevealPhysicalState n)
    (hs : Lemma17GapBoundaryGood a cStar rho s)
    (hmajor :
      s.inactive.yIds.card ≤ s.inactive.xIds.card) :
    terminalFailureMass
        (lemma17PhysicalStageKernel n h3
          (lemma17StageRemaining a s)
          (2 * a) (19 * cStar * rho)
          (cStar * n) s)
        (Lemma17GapBoundaryGood
          (2 * a) cStar rhoNext)
      ≤ lemma17StageError a q cStar rho r := by
  let k := lemma17StageRemaining a s
  let R := s.inactive.yIds.card
  let B := s.inactive.xIds.card
  let nu := R + B
  let u := lemma17PoolRemainder k R B
  have hanchor :
      s.coarse.1.active + k = 2 * a :=
    lemma17StageRemaining_spec
      a s (by omega) hs.1 hs.2.1
  have hkLe : k ≤ a := by
    have hstart := hs.1
    dsimp only [k] at hanchor ⊢
    omega
  have hkOne : k + 1 ≤ a + 1 := by omega
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
      q * (k + 1) ≤ rho ^ 2 := by
    exact
      (Nat.mul_le_mul_left q hkOne).trans hqa
  let μ :=
    lemma17PhysicalStageKernel n h3 k
      (2 * a) (19 * cStar * rho)
      (cStar * n) s
  let RangeGood :
      InfectionRevealPhysicalState n → Prop :=
    Lemma17PhysicalStageRangeGood
      (2 * a) (19 * cStar * rho)
  have hrange :
      terminalFailureMass μ RangeGood ≤
        lemma17StageError a q cStar rho r := by
    exact
      lemma17PhysicalStage_paper_range
        n q rho a k u nu R B (2 * a)
        cStar r h3 ha hquarter hlabelQuarter
        le_rfl htarget hcStar hcTwo hrho
        hbias hactiveScale hmean hqaLocal
        hu rfl (by simpa [R, B] using hmajor)
        s hs.1 hanchor hs.2.2 rfl rfl
        (by
          have hhi := hs.2.1
          dsimp only [k] at hanchor ⊢
          omega)
  have hnext :
      ∀ z, RangeGood z →
        Lemma17GapBoundaryGood
          (2 * a) cStar rhoNext z := by
    intro z hz
    have hgap :=
      lemma17PhysicalStageGood_to_next
        (2 * a) cStar rho rhoNext hroot z
        ⟨hz.1, hz.2.2⟩
    exact ⟨hgap.1, hz.2.1, hgap.2⟩
  exact
    (terminalFailureMass_mono
      μ
      (Lemma17GapBoundaryGood
        (2 * a) cStar rhoNext)
      RangeGood hnext).trans hrange

/-- Every ladder kernel preserves a common stopped-urn hitting potential as
long as its target leaves four molecules of room.  Off the arithmetic target
range, the additive remaining-reveal witness is zero and the stage is the
identity kernel. -/
theorem expect_lemma17LadderKernel_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (cStar : ℕ) (scale rho : ℕ → ℕ)
    (j : ℕ)
    (hroom : 2 * scale j + 4 ≤ n)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad]
    (s : InfectionRevealPhysicalState n) :
    expect
        (lemma17LadderKernel
          n h3 cStar scale rho j s)
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  let k := lemma17StageRemaining (scale j) s
  by_cases hex :
      ∃ t, s.coarse.1.active + t = 2 * scale j
  · have hanchor :
        s.coarse.1.active + k = 2 * scale j := by
      dsimp only [k]
      unfold lemma17StageRemaining
      rw [dif_pos hex]
      exact Classical.choose_spec hex
    unfold lemma17LadderKernel
    exact
      expect_lemma17PhysicalStageKernel_urnEverHit_le
        n h3 k (2 * scale j)
        (19 * cStar * rho j) (cStar * n)
        s hroom hanchor Bad
  · have hk : k = 0 := by
      dsimp only [k]
      unfold lemma17StageRemaining
      rw [dif_neg hex]
    unfold lemma17LadderKernel
    rw [show
      lemma17StageRemaining (scale j) s = 0 by
        exact hk]
    rw [lemma17PhysicalStageKernel_zero, expect_pure]

/-- A common stopped-urn hitting potential survives every earlier ladder
stage. -/
theorem expect_lemma17Ladder_staged_urnEverHit_le
    (n : ℕ) (h3 : 3 ≤ n)
    (cStar j : ℕ)
    (scale rho : ℕ → ℕ)
    (hroom :
      ∀ l < j, 2 * scale l + 4 ≤ n)
    (Bad : ℕ × ℕ → Prop) [DecidablePred Bad]
    (s : InfectionRevealPhysicalState n) :
    expect
        (stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          j s)
        (fun z =>
          everHit Bad urnStopped
            (infectionInactiveCounts z.inactive))
      ≤
        everHit Bad urnStopped
          (infectionInactiveCounts s.inactive) := by
  apply
    expect_stagedIter_le_of_lt
      (lemma17LadderKernel n h3 cStar scale rho)
      (fun z =>
        everHit Bad urnStopped
          (infectionInactiveCounts z.inactive))
      j
  intro l hl z
  exact
    expect_lemma17LadderKernel_urnEverHit_le
      n h3 cStar scale rho l (hroom l hl) Bad z

/-- At any gap-good ladder anchor, loss of the inactive majority is contained
in the single urn event centred at the ladder's initial inactive pool. -/
theorem lemma17_ladder_anchor_failure_le_urn
    (n : ℕ) (h3 : 3 ≤ n)
    (cStar j D k u B R : ℕ)
    (scale rho : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk : 0 < k)
    (hstageRoom :
      ∀ l < j, 2 * scale l + 4 ≤ n)
    (hclockRoom :
      scale j + 1 ≤ s.coarse.1.active + k) :
    terminalFailureMass
        (stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          j s)
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
  let V : InfectionRevealPhysicalState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts z.inactive)
  let μ :=
    stagedIter
      (lemma17LadderKernel
        n h3 cStar scale rho)
      j s
  let AnchorGood : InfectionRevealPhysicalState n → Prop :=
    fun z =>
      Lemma17GapBoundaryGood
          (scale j) cStar (rho j) z →
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
        Lemma17GapBoundaryGood
          (scale j) cStar (rho j) z := by
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
  have hmass :
      terminalFailureMass μ AnchorGood ≤
        expect μ V := by
    unfold terminalFailureMass expect
    exact ENNReal.tsum_le_tsum fun z => by
      by_cases hz : AnchorGood z
      · simp [hz]
      · rw [hcontain z hz]
        simp [hz]
  have hpotential :
      expect μ V ≤ V s := by
    exact
      expect_lemma17Ladder_staged_urnEverHit_le
        n h3 cStar j scale rho hstageRoom Bad s
  have hcounts :
      infectionInactiveCounts s.inactive = (B, R) := by
    simp [infectionInactiveCounts, hx0, hy0]
  calc
    terminalFailureMass μ AnchorGood
        ≤ expect μ V := hmass
    _ ≤ V s := hpotential
    _ =
        everHit Bad urnStopped (B, R) := by
          simpa [V] using
            congrArg (everHit Bad urnStopped) hcounts

/-- The aggregate ladder-anchor failure inherits the arbitrary-pool Lemma 16
exponential tail. -/
theorem lemma17_ladder_anchor_failure
    (n : ℕ) (h3 : 3 ≤ n)
    (qMajor cStar j D k u B R : ℕ)
    (scale rho : ℕ → ℕ)
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
          (lemma17LadderKernel
            n h3 cStar scale rho)
          j s)
        (fun z =>
          Lemma17GapBoundaryGood
              (scale j) cStar (rho j) z →
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
      ≤ lemma16UrnError qMajor := by
  calc
    terminalFailureMass
        (stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          j s)
        (fun z =>
          Lemma17GapBoundaryGood
              (scale j) cStar (rho j) z →
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
        ≤
      everHit
        (Lemma16UrnWindowBad D u k B R)
        urnStopped (B, R) :=
      lemma17_ladder_anchor_failure_le_urn
        n h3 cStar j D k u B R scale rho s
        hBR hgap hx0 hy0 hk hstageRoom hclockRoom
    _ ≤ lemma16UrnError qMajor := by
      unfold everHit
      exact
        lemma17_urn_window_tail_pool
          qMajor D (k + 1) k u (B + R) B R
          hqa rfl hBR.symm rfl hquarter hk

/-- Lemma 17 ladder with the random inactive-majority anchors charged only in
aggregate at their split times. -/
theorem lemma17_ladder_of_anchor_failures
    (n q cStar m : ℕ)
    (h3 : 3 ≤ n)
    (scale rho r : ℕ → ℕ)
    (εMajor : ℕ → ℝ≥0∞)
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
        q * (scale j + 1) ≤ (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m, 5 * (scale j + 1) ≤ n + 1)
    (s : InfectionRevealPhysicalState n)
    (hs :
      Lemma17GapBoundaryGood
        (scale 0) cStar (rho 0) s)
    (hanchor :
      ∀ j < m,
        terminalFailureMass
          (stagedIter
            (lemma17LadderKernel
              n h3 cStar scale rho)
            j s)
          (fun z =>
            Lemma17GapBoundaryGood
                (scale j) cStar (rho j) z →
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤ εMajor j) :
    terminalFailureMass
        (stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          m s)
        (Lemma17GapBoundaryGood
          (scale m) cStar (rho m))
      ≤
    ∑ j ∈ Finset.range m,
      (lemma17StageError
        (scale j) q cStar (rho j) (r j) +
        εMajor j) := by
  apply
    terminalFailureMass_stagedIter_of_anchors
      (lemma17LadderKernel n h3 cStar scale rho)
      (fun j =>
        Lemma17GapBoundaryGood
          (scale j) cStar (rho j))
      (fun j z =>
        Lemma17GapBoundaryGood
            (scale j) cStar (rho j) z →
          z.inactive.yIds.card ≤
            z.inactive.xIds.card)
      (fun j =>
        lemma17StageError
          (scale j) q cStar (rho j) (r j))
      εMajor m s hs
  · intro j hj z hzP hzA
    have hstage :=
      lemma17GapBoundary_stage
        n q cStar (scale j) (rho j)
        (rho (j + 1)) (r j) h3 hcStar hcTwo
        (ha j hj) (hquarter j hj) (htarget j hj)
        (hrho j hj) (hroot j hj)
        (hbias j hj) (hactiveScale j hj)
        (hmean j hj) (hqa j hj)
        (hlabelRoom j hj) z hzP (hzA hzP)
    have hnext := hdouble j hj
    simpa [lemma17LadderKernel, hnext] using hstage
  · exact hanchor

/-- Lemma 17's doubling ladder with every random inactive-majority anchor
discharged from one initial-pool urn tail. -/
theorem lemma17_ladder_closed
    (n q qMajor cStar m : ℕ)
    (h3 : 3 ≤ n)
    (scale rho r : ℕ → ℕ)
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
        q * (scale j + 1) ≤ (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m, 5 * (scale j + 1) ≤ n + 1)
    (s : InfectionRevealPhysicalState n)
    (hs :
      Lemma17GapBoundaryGood
        (scale 0) cStar (rho 0) s)
    (D k u B R : ℕ)
    (hBR : B + R = u + k + 1)
    (hgap : R + D ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk : 0 < k)
    (hMajorQa : qMajor * (k + 1) ≤ D ^ 2)
    (hMajorQuarter : 4 * (k + 1) ≤ B + R + 1)
    (hclockRoom :
      ∀ j < m,
        scale j + 1 ≤ s.coarse.1.active + k) :
    terminalFailureMass
        (stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          m s)
        (Lemma17GapBoundaryGood
          (scale m) cStar (rho m))
      ≤
    ∑ j ∈ Finset.range m,
      (lemma17StageError
        (scale j) q cStar (rho j) (r j) +
        lemma16UrnError qMajor) := by
  apply
    lemma17_ladder_of_anchor_failures
      n q cStar m h3 scale rho r
      (fun _ => lemma16UrnError qMajor)
      hcStar hcTwo hdouble hroot ha hquarter
      htarget hrho hbias hactiveScale hmean hqa
      hlabelRoom s hs
  intro j hj
  apply
    lemma17_ladder_anchor_failure
      n h3 qMajor cStar j D k u B R
      scale rho s hBR hgap hx0 hy0 hk
      hMajorQa hMajorQuarter
  · intro l hl
    have hlm : l < m := hl.trans hj
    have hqtr := hquarter l hlm
    have hal := ha l hlm
    omega
  · exact hclockRoom j hj

end

end Tri

#print axioms Tri.lemma17StageRemaining_spec
#print axioms Tri.lemma17PoolRemainder_spec
#print axioms Tri.lemma17_ladder
#print axioms Tri.lemma17GapBoundary_stage
#print axioms Tri.expect_lemma17LadderKernel_urnEverHit_le
#print axioms Tri.expect_lemma17Ladder_staged_urnEverHit_le
#print axioms Tri.lemma17_ladder_anchor_failure_le_urn
#print axioms Tri.lemma17_ladder_anchor_failure
#print axioms Tri.lemma17_ladder_of_anchor_failures
#print axioms Tri.lemma17_ladder_closed
