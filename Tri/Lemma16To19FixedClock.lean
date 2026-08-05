/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17CustomLandingClock
import Tri.Lemma16To19CorrectedClock

/-!
# Raw physical schedule through the fixed Lemma 17 landing

There are `mPred` ordinary Lemma 17 blocks, one custom landing block, the
decisive Lemma 18 block, `m19` positive-gap blocks, and the capped final
block.  The custom landing replaces the last ordinary Lemma 17 block and
therefore uses the corrected horizon with `m17 = mPred + 1`.
-/

namespace Tri

open scoped ENNReal

noncomputable section

def lemma16To19FixedBlockHorizon
    (n q16 cStar mPred m19 clockBudget : ℕ) : ℕ → ℕ :=
  lemma16To19CorrectedBlockHorizon
    n q16 cStar (mPred + 1) m19 clockBudget

noncomputable def lemma16To19FixedBlockRemaining
    {n : ℕ} (k16 mPred m19 targetA : ℕ)
    (scale17 scale19 : ℕ → ℕ) :
    ℕ → InfectionRevealPhysicalState n → ℕ
  | 0, _ => k16
  | j + 1, s =>
      if j < mPred then
        lemma17StageRemaining (scale17 j) s
      else if j = mPred then
        lemma17TargetRemaining targetA s
      else if j = mPred + 1 then
        lemma17StageRemaining targetA s
      else
        let l := additiveTailIndex (mPred + 2) j
        if l < m19 then
          lemma17StageRemaining (scale19 l) s
        else
          s.inactive.ids.card

def lemma16To19FixedBlockCheckpoint
    {n : ℕ} (k16 mPred m19 targetA : ℕ)
    (scale17 scale19 : ℕ → ℕ)
    (j : ℕ) (anchor current : InfectionRevealPhysicalState n) : Prop :=
  PhysicalActivationCheckpoint anchor
    (lemma16To19FixedBlockRemaining
      k16 mPred m19 targetA scale17 scale19 j anchor)
    current

noncomputable instance
    lemma16To19FixedBlockCheckpointDecidable
    {n : ℕ} (k16 mPred m19 targetA : ℕ)
    (scale17 scale19 : ℕ → ℕ)
    (j : ℕ) (anchor : InfectionRevealPhysicalState n) :
    DecidablePred
      (lemma16To19FixedBlockCheckpoint
        k16 mPred m19 targetA scale17 scale19 j anchor) :=
  Classical.decPred _

noncomputable def lemma16To19FixedCappedScheduleKernel
    (n : ℕ) (h3 : 3 ≤ n)
    (q16 k16 cStar mPred m19 targetA
      rhoSource D clockBudget : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ) :
    ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n)
  | 0 =>
      lemma16PhysicalStageKernel
        n h3 k16 (cStar * q16 * n)
  | j + 1 =>
      if j < mPred then
        lemma17LadderKernel n h3 cStar scale17 rho17 j
      else if j = mPred then
        lemma17TargetLandingKernel
          n h3 cStar targetA rhoSource
      else if j = mPred + 1 then
        lemma18FromGapBoundaryKernel
          n h3 targetA D cStar
      else
        let l := additiveTailIndex (mPred + 2) j
        if l < m19 then
          lemma19LadderKernel n h3 cStar scale19 l
        else
          lemma19FullActivationCappedKernel
            n h3 clockBudget

theorem lemma16To19FixedCappedScheduleKernel_eq_block
    (n : ℕ) (h3 : 3 ≤ n)
    (q16 k16 cStar mPred m19 targetA
      rhoSource D clockBudget : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ)
    (j : ℕ) :
    lemma16To19FixedCappedScheduleKernel
        n h3 q16 k16 cStar mPred m19 targetA
        rhoSource D clockBudget scale17 rho17 scale19 j =
      StagedFreezeControl.block
        (infectionRevealPhysicalStep n h3)
        (lemma16To19FixedBlockCheckpoint
          k16 mPred m19 targetA scale17 scale19)
        (lemma16To19FixedBlockHorizon
          n q16 cStar mPred m19 clockBudget)
        j := by
  funext s
  cases j with
  | zero =>
      simpa [lemma16To19FixedCappedScheduleKernel,
        StagedFreezeControl.block,
        lemma16To19FixedBlockCheckpoint,
        lemma16To19FixedBlockRemaining,
        lemma16To19FixedBlockHorizon,
        lemma16To19CorrectedBlockHorizon] using
        lemma16PhysicalStageKernel_eq_frozenPhysical
          n h3 k16 (cStar * q16 * n) s
  | succ j =>
      by_cases hjPred : j < mPred
      · have hclock :
            j < (mPred + 1) + m19 + 1 := by
          omega
        have hcheckpoint :
            lemma16To19FixedBlockCheckpoint
                k16 mPred m19 targetA scale17 scale19
                (j + 1) s =
              PhysicalActivationCheckpoint s
                (lemma17StageRemaining (scale17 j) s) := by
          funext current
          simp [lemma16To19FixedBlockCheckpoint,
            lemma16To19FixedBlockRemaining, hjPred]
        have hfreeze :=
          physicalFreeze_congr
            (infectionRevealPhysicalStep n h3)
            (lemma16To19FixedBlockCheckpoint
              k16 mPred m19 targetA scale17 scale19
              (j + 1) s)
            (PhysicalActivationCheckpoint s
              (lemma17StageRemaining (scale17 j) s))
            (fun current => by rw [hcheckpoint])
        unfold StagedFreezeControl.block
        rw [hfreeze]
        simpa [lemma16To19FixedCappedScheduleKernel,
          lemma16To19FixedBlockHorizon,
          lemma16To19CorrectedBlockHorizon,
          lemma17LadderKernel, hjPred, hclock] using
          lemma17PhysicalStageKernel_eq_frozenPhysical
            n h3
            (lemma17StageRemaining (scale17 j) s)
            (2 * scale17 j) (19 * cStar * rho17 j)
            (cStar * n) s
      · by_cases hjLanding : j = mPred
        · subst j
          have hclock :
              mPred < (mPred + 1) + m19 + 1 := by
            omega
          have hcheckpoint :
              lemma16To19FixedBlockCheckpoint
                  k16 mPred m19 targetA scale17 scale19
                  (mPred + 1) s =
                PhysicalActivationCheckpoint s
                  (lemma17TargetRemaining targetA s) := by
            funext current
            simp [lemma16To19FixedBlockCheckpoint,
              lemma16To19FixedBlockRemaining]
          have hfreeze :=
            physicalFreeze_congr
              (infectionRevealPhysicalStep n h3)
              (lemma16To19FixedBlockCheckpoint
                k16 mPred m19 targetA scale17 scale19
                (mPred + 1) s)
              (PhysicalActivationCheckpoint s
                (lemma17TargetRemaining targetA s))
              (fun current => by rw [hcheckpoint])
          unfold StagedFreezeControl.block
          rw [hfreeze]
          simpa [lemma16To19FixedCappedScheduleKernel,
            lemma16To19FixedBlockHorizon,
            lemma16To19CorrectedBlockHorizon,
            hclock] using
            lemma17TargetLandingKernel_eq_frozenPhysical
              n h3 cStar targetA rhoSource s
        · by_cases hjDecisive : j = mPred + 1
          · subst j
            have hclock :
                mPred + 1 <
                  (mPred + 1) + m19 + 1 := by
              omega
            have hcheckpoint :
                lemma16To19FixedBlockCheckpoint
                    k16 mPred m19 targetA scale17 scale19
                    (mPred + 1 + 1) s =
                  PhysicalActivationCheckpoint s
                    (lemma17StageRemaining targetA s) := by
              funext current
              simp [lemma16To19FixedBlockCheckpoint,
                lemma16To19FixedBlockRemaining]
            have hfreeze :=
              physicalFreeze_congr
                (infectionRevealPhysicalStep n h3)
                (lemma16To19FixedBlockCheckpoint
                  k16 mPred m19 targetA scale17 scale19
                  (mPred + 1 + 1) s)
                (PhysicalActivationCheckpoint s
                  (lemma17StageRemaining targetA s))
                (fun current => by rw [hcheckpoint])
            unfold StagedFreezeControl.block
            rw [hfreeze]
            simpa [lemma16To19FixedCappedScheduleKernel,
              lemma16To19FixedBlockHorizon,
              lemma16To19CorrectedBlockHorizon,
              lemma18FromGapBoundaryKernel,
              hclock] using
              lemma17PhysicalStageKernel_eq_frozenPhysical
                n h3
                (lemma17StageRemaining targetA s)
                (2 * targetA) (30 * D)
                (cStar * n) s
          · have hjTail : mPred + 2 ≤ j := by
              omega
            let l := additiveTailIndex (mPred + 2) j
            have hlSpec : mPred + 2 + l = j :=
              additiveTailIndex_spec
                (mPred + 2) j hjTail
            by_cases hl : l < m19
            · have hclock :
                  j < (mPred + 1) + m19 + 1 := by
                omega
              have hcheckpoint :
                  lemma16To19FixedBlockCheckpoint
                      k16 mPred m19 targetA scale17 scale19
                      (j + 1) s =
                    PhysicalActivationCheckpoint s
                      (lemma17StageRemaining
                        (scale19 l) s) := by
                funext current
                simp [lemma16To19FixedBlockCheckpoint,
                  lemma16To19FixedBlockRemaining,
                  hjPred, hjLanding, hjDecisive, l, hl]
              have hfreeze :=
                physicalFreeze_congr
                  (infectionRevealPhysicalStep n h3)
                  (lemma16To19FixedBlockCheckpoint
                    k16 mPred m19 targetA scale17 scale19
                    (j + 1) s)
                  (PhysicalActivationCheckpoint s
                    (lemma17StageRemaining
                      (scale19 l) s))
                  (fun current => by rw [hcheckpoint])
              unfold StagedFreezeControl.block
              rw [hfreeze]
              simpa [lemma16To19FixedCappedScheduleKernel,
                lemma16To19FixedBlockHorizon,
                lemma16To19CorrectedBlockHorizon,
                lemma19LadderKernel,
                hjPred, hjLanding, hjDecisive,
                l, hl, hclock] using
                lemma17PhysicalStageKernel_eq_frozenPhysical
                  n h3
                  (lemma17StageRemaining (scale19 l) s)
                  (2 * scale19 l) 0 (cStar * n) s
            · have hclock :
                  ¬ j < (mPred + 1) + m19 + 1 := by
                omega
              have hcheckpoint :
                  lemma16To19FixedBlockCheckpoint
                      k16 mPred m19 targetA scale17 scale19
                      (j + 1) s =
                    PhysicalActivationCheckpoint s
                      s.inactive.ids.card := by
                funext current
                simp [lemma16To19FixedBlockCheckpoint,
                  lemma16To19FixedBlockRemaining,
                  hjPred, hjLanding, hjDecisive, l, hl]
              have hfreeze :=
                physicalFreeze_congr
                  (infectionRevealPhysicalStep n h3)
                  (lemma16To19FixedBlockCheckpoint
                    k16 mPred m19 targetA scale17 scale19
                    (j + 1) s)
                  (PhysicalActivationCheckpoint s
                    s.inactive.ids.card)
                  (fun current => by rw [hcheckpoint])
              unfold StagedFreezeControl.block
              rw [hfreeze]
              simpa [lemma16To19FixedCappedScheduleKernel,
                lemma16To19FixedBlockHorizon,
                lemma16To19CorrectedBlockHorizon,
                lemma19FullActivationCappedKernel,
                hjPred, hjLanding, hjDecisive,
                l, hl, hclock] using
                lemma17PhysicalStageKernel_eq_frozenPhysical
                  n h3 s.inactive.ids.card n 0
                  (lemma19FullActivationClockCap
                    n clockBudget) s

theorem lemma16To19FixedCappedScheduleKernel_stagedIter
    (n : ℕ) (h3 : 3 ≤ n)
    (q16 k16 cStar mPred m19 targetA
      rhoSource D clockBudget : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n) :
    stagedIter
        (lemma16To19FixedCappedScheduleKernel
          n h3 q16 k16 cStar mPred m19 targetA
          rhoSource D clockBudget scale17 rho17 scale19)
        (mPred + m19 + 4) s =
      (((((lemma16PhysicalStageKernel
                  n h3 k16 (cStar * q16 * n) s).bind
                (fun z =>
                  stagedIter
                    (lemma17LadderKernel
                      n h3 cStar scale17 rho17)
                    mPred z)).bind
              (lemma17TargetLandingKernel
                n h3 cStar targetA rhoSource)).bind
            (lemma18FromGapBoundaryKernel
              n h3 targetA D cStar)).bind
          (fun z =>
            stagedIter
              (lemma19LadderKernel
                n h3 cStar scale19)
              m19 z)).bind
        (lemma19FullActivationCappedKernel
          n h3 clockBudget) := by
  let K0 :=
    lemma16PhysicalStageKernel
      n h3 k16 (cStar * q16 * n)
  let Old :=
    lemma17LadderKernel
      n h3 cStar scale17 rho17
  let Landing :=
    lemma17TargetLandingKernel
      n h3 cStar targetA rhoSource
  let Decisive :=
    lemma18FromGapBoundaryKernel
      n h3 targetA D cStar
  let New :=
    lemma19LadderKernel
      n h3 cStar scale19
  let Final :=
    lemma19FullActivationCappedKernel
      n h3 clockBudget
  let Rest : ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n)
    | j =>
        if j < mPred then
          Old j
        else if j = mPred then
          Landing
        else if j = mPred + 1 then
          Decisive
        else
          let l := additiveTailIndex (mPred + 2) j
          if l < m19 then New l else Final
  have hcons :
      lemma16To19FixedCappedScheduleKernel
          n h3 q16 k16 cStar mPred m19 targetA
          rhoSource D clockBudget scale17 rho17 scale19 =
        fun
        | 0 => K0
        | j + 1 => Rest j := by
    funext j
    cases j <;> rfl
  rw [hcons]
  have hhead :
      stagedIter
          (fun
            | 0 => K0
            | j + 1 => Rest j)
          (mPred + m19 + 4) s =
        (K0 s).bind
          (stagedIter Rest (mPred + m19 + 3)) := by
    simpa only [Nat.add_assoc] using
      stagedIter_cons K0 Rest (mPred + m19 + 3) s
  rw [hhead]
  have hprefix :
      stagedIter Rest mPred =
        stagedIter Old mPred := by
    apply stagedIter_congr_lt
    intro j hj
    funext z
    simp [Rest, hj]
  let Core : ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n)
    | 0 => Decisive
    | j + 1 => if j < m19 then New j else Final
  let Shift : ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n)
    | 0 => Landing
    | j + 1 => Core j
  have hshift :
      (fun j => Rest (mPred + j)) = Shift := by
    funext j
    cases j with
    | zero =>
        simp [Rest, Shift]
    | succ j =>
        cases j with
        | zero =>
            simp [Rest, Shift, Core]
        | succ j =>
            have hnotlt :
                ¬ mPred + (j + 1 + 1) < mPred := by
              omega
            have hidx :
                additiveTailIndex
                    (mPred + 2)
                    (mPred + (j + 1 + 1)) = j := by
              have hspec :=
                additiveTailIndex_spec
                  (mPred + 2)
                  (mPred + (j + 1 + 1))
                  (by omega)
              omega
            simp [Rest, Shift, Core, hnotlt, hidx]
  have hcore :
      stagedIter Core (m19 + 2) =
        fun z =>
          ((Decisive z).bind
            (fun y => stagedIter New m19 y)).bind Final := by
    funext z
    exact
      stagedIter_head_body_tail
        Decisive New Final m19 z
  have hshiftIter :
      stagedIter Shift (m19 + 3) =
        fun z =>
          (Landing z).bind
            (fun y =>
              ((Decisive y).bind
                (fun w => stagedIter New m19 w)).bind
              Final) := by
    funext z
    change
      stagedIter
          (fun
            | 0 => Landing
            | j + 1 => Core j)
          (m19 + 3) z =
        _
    have hconsLanding :=
      stagedIter_cons Landing Core (m19 + 2) z
    rw [hcore] at hconsLanding
    simpa only [Nat.add_assoc] using hconsLanding
  change
    (K0 s).bind
        (stagedIter Rest (mPred + m19 + 3)) =
      (((((K0 s).bind
              (fun z => stagedIter Old mPred z)).bind
            Landing).bind
          Decisive).bind
        (fun z => stagedIter New m19 z)).bind
      Final
  rw [show mPred + m19 + 3 =
      mPred + (m19 + 3) by omega]
  have hsplit :
      stagedIter Rest (mPred + (m19 + 3)) =
        fun z =>
          (stagedIter Rest mPred z).bind
            (stagedIter
              (fun j => Rest (mPred + j))
              (m19 + 3)) := by
    funext z
    exact stagedIter_add Rest mPred (m19 + 3) z
  rw [hsplit, hprefix, hshift, hshiftIter]
  simp only [PMF.bind_bind]

theorem lemma16To19FixedBlockHorizon_pos
    (n q16 cStar mPred m19 clockBudget : ℕ)
    (hn : 0 < n) (hq16 : 0 < q16) (hcStar : 0 < cStar) :
    ∀ j < mPred + m19 + 4,
      0 <
        lemma16To19FixedBlockHorizon
          n q16 cStar mPred m19 clockBudget j := by
  intro j hj
  exact
    lemma16To19CorrectedBlockHorizon_pos
      n q16 cStar (mPred + 1) m19 clockBudget
      hn hq16 hcStar j (by omega)

/-- The custom landing replaces one ordinary Lemma 17 clock block. -/
def lemma16To19FixedRawClock
    (n q16 cStar mPred m19 clockBudget : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (mPred + m19 + 4),
    lemma16To19FixedBlockHorizon
      n q16 cStar mPred m19 clockBudget j

theorem lemma16To19FixedRawClock_eq_corrected
    (n q16 cStar mPred m19 clockBudget : ℕ) :
    lemma16To19FixedRawClock
        n q16 cStar mPred m19 clockBudget =
      lemma16To19CorrectedRawClock
        n q16 cStar (mPred + 1) m19 clockBudget := by
  unfold lemma16To19FixedRawClock
    lemma16To19CorrectedRawClock
    lemma16To19FixedBlockHorizon
  rw [show mPred + m19 + 4 =
      mPred + 1 + m19 + 3 by omega]

/-- Flatten the fixed-landing physical schedule to one raw frozen iterate. -/
theorem lemma16To19_fixed_physical_clock_failure_le
    (n q16 k16 cStar mPred m19 targetA
      rhoSource D clockBudget targetGap : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ)
    (h3 : 3 ≤ n)
    (hq16 : 0 < q16)
    (hcStar : 0 < cStar)
    (s : InfectionRevealPhysicalState n) :
    terminalFailureMass
        (iter
          (freeze
            (Lemma19PhysicalStageRangeGood n targetGap)
            (infectionRevealPhysicalStep n h3))
          (lemma16To19FixedRawClock
            n q16 cStar mPred m19 clockBudget)
          s)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    terminalFailureMass
        ((((lemma16PhysicalStageKernel
                  n h3 k16 (cStar * q16 * n) s).bind
                (fun z =>
                  stagedIter
                    (lemma17LadderKernel
                      n h3 cStar scale17 rho17)
                    mPred z)).bind
              (lemma17TargetLandingKernel
                n h3 cStar targetA rhoSource)).bind
          (fun z =>
            ((lemma18FromGapBoundaryKernel
                  n h3 targetA D cStar z).bind
                (fun y =>
                  stagedIter
                    (lemma19LadderKernel
                      n h3 cStar scale19)
                    m19 y)).bind
              (lemma19FullActivationBudgetKernel
                n h3 clockBudget)))
        (Lemma19PhysicalStageRangeGood n targetGap) := by
  let K :=
    lemma16To19FixedCappedScheduleKernel
      n h3 q16 k16 cStar mPred m19 targetA
      rhoSource D clockBudget scale17 rho17 scale19
  have hclock :=
    StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
      (Lemma19PhysicalStageRangeGood n targetGap)
      (infectionRevealPhysicalStep n h3)
      (lemma16To19FixedBlockCheckpoint
        k16 mPred m19 targetA scale17 scale19)
      (lemma16To19FixedBlockHorizon
        n q16 cStar mPred m19 clockBudget)
      (mPred + m19 + 4)
      (lemma16To19FixedBlockHorizon_pos
        n q16 cStar mPred m19 clockBudget
        (by omega) hq16 hcStar)
      s
  have hblocks :
      StagedFreezeControl.block
          (infectionRevealPhysicalStep n h3)
          (lemma16To19FixedBlockCheckpoint
            k16 mPred m19 targetA scale17 scale19)
          (lemma16To19FixedBlockHorizon
            n q16 cStar mPred m19 clockBudget) =
        K := by
    funext j
    exact
      (lemma16To19FixedCappedScheduleKernel_eq_block
        n h3 q16 k16 cStar mPred m19 targetA
        rhoSource D clockBudget
        scale17 rho17 scale19 j).symm
  rw [hblocks] at hclock
  rw [show stagedIter K (mPred + m19 + 4) s =
      (((((lemma16PhysicalStageKernel
                  n h3 k16 (cStar * q16 * n) s).bind
                (fun z =>
                  stagedIter
                    (lemma17LadderKernel
                      n h3 cStar scale17 rho17)
                    mPred z)).bind
              (lemma17TargetLandingKernel
                n h3 cStar targetA rhoSource)).bind
            (lemma18FromGapBoundaryKernel
              n h3 targetA D cStar)).bind
          (fun z =>
            stagedIter
              (lemma19LadderKernel
                n h3 cStar scale19)
              m19 z)).bind
        (lemma19FullActivationCappedKernel
          n h3 clockBudget) by
      exact
        lemma16To19FixedCappedScheduleKernel_stagedIter
          n h3 q16 k16 cStar mPred m19 targetA
          rhoSource D clockBudget
          scale17 rho17 scale19 s] at hclock
  have hcapped :=
    terminalFailureMass_bind_capped_final_le
      n h3 clockBudget targetGap
      (((((lemma16PhysicalStageKernel
                  n h3 k16 (cStar * q16 * n) s).bind
                (fun z =>
                  stagedIter
                    (lemma17LadderKernel
                      n h3 cStar scale17 rho17)
                    mPred z)).bind
              (lemma17TargetLandingKernel
                n h3 cStar targetA rhoSource)).bind
            (lemma18FromGapBoundaryKernel
              n h3 targetA D cStar)).bind
        (fun z =>
          stagedIter
            (lemma19LadderKernel
              n h3 cStar scale19)
            m19 z))
  simpa only [lemma16To19FixedRawClock,
    PMF.bind_bind] using hclock.trans hcapped

end

end Tri

#print axioms
  Tri.lemma16To19FixedCappedScheduleKernel_eq_block
#print axioms
  Tri.lemma16To19FixedCappedScheduleKernel_stagedIter
#print axioms Tri.lemma16To19FixedBlockHorizon_pos
#print axioms Tri.lemma16To19FixedRawClock_eq_corrected
#print axioms
  Tri.lemma16To19_fixed_physical_clock_failure_le
