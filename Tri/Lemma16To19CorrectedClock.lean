/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Clock
import Tri.Lemma16To19Corrected

/-!
# Raw physical clock for the corrected Lemma 16--19 route

The corrected route inserts a finite positive-gap ladder between the decisive
Lemma 18 block and the capped late-activation block.  This file gives that
route one subtraction-free fixed schedule and flattens it to the genuine raw
identity-refined infection clock.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Canonical additive tail index.  It is used only after `offset ≤ j`. -/
noncomputable def additiveTailIndex
    (offset j : ℕ) : ℕ := by
  classical
  exact
    if h : ∃ l, offset + l = j then
      Classical.choose h
    else 0

theorem additiveTailIndex_spec
    (offset j : ℕ) (h : offset ≤ j) :
    offset + additiveTailIndex offset j = j := by
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le h
  have hex : ∃ l, offset + l = j := ⟨l, hl.symm⟩
  unfold additiveTailIndex
  rw [dif_pos hex]
  exact Classical.choose_spec hex

@[simp] theorem additiveTailIndex_add
    (offset l : ℕ) :
    additiveTailIndex offset (offset + l) = l := by
  have hspec :=
    additiveTailIndex_spec offset (offset + l)
      (Nat.le_add_right offset l)
  omega

/-- Fixed horizon of every corrected schedule block. -/
def lemma16To19CorrectedBlockHorizon
    (n q16 cStar m17 m19 clockBudget : ℕ) : ℕ → ℕ
  | 0 => cStar * q16 * n
  | j + 1 =>
      if j < m17 + m19 + 1 then cStar * n
      else lemma19FullActivationClockCap n clockBudget

/-- Endpoint-dependent reveal count used by each corrected schedule block. -/
noncomputable def lemma16To19CorrectedBlockRemaining
    {n : ℕ} (k16 m17 m19 : ℕ)
    (scale17 scale19 : ℕ → ℕ) :
    ℕ → InfectionRevealPhysicalState n → ℕ
  | 0, _ => k16
  | j + 1, s =>
      if j < m17 then
        lemma17StageRemaining (scale17 j) s
      else if j = m17 then
        lemma17StageRemaining (scale17 m17) s
      else
        let l := additiveTailIndex (m17 + 1) j
        if l < m19 then
          lemma17StageRemaining (scale19 l) s
        else
          s.inactive.ids.card

/-- Anchored physical checkpoint family for the corrected schedule. -/
def lemma16To19CorrectedBlockCheckpoint
    {n : ℕ} (k16 m17 m19 : ℕ)
    (scale17 scale19 : ℕ → ℕ)
    (j : ℕ) (anchor current : InfectionRevealPhysicalState n) : Prop :=
  PhysicalActivationCheckpoint anchor
    (lemma16To19CorrectedBlockRemaining
      k16 m17 m19 scale17 scale19 j anchor)
    current

noncomputable instance
    lemma16To19CorrectedBlockCheckpointDecidable
    {n : ℕ} (k16 m17 m19 : ℕ)
    (scale17 scale19 : ℕ → ℕ)
    (j : ℕ) (anchor : InfectionRevealPhysicalState n) :
    DecidablePred
      (lemma16To19CorrectedBlockCheckpoint
        k16 m17 m19 scale17 scale19 j anchor) :=
  Classical.decPred _

/-- Corrected physical schedule with the last random late clock padded to its
uniform cap. -/
noncomputable def lemma16To19CorrectedCappedScheduleKernel
    (n : ℕ) (h3 : 3 ≤ n)
    (q16 k16 cStar m17 m19 D clockBudget : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ) :
    ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n)
  | 0 =>
      lemma16PhysicalStageKernel
        n h3 k16 (cStar * q16 * n)
  | j + 1 =>
      if j < m17 then
        lemma17LadderKernel n h3 cStar scale17 rho17 j
      else if j = m17 then
        lemma18FromGapBoundaryKernel
          n h3 (scale17 m17) D cStar
      else
        let l := additiveTailIndex (m17 + 1) j
        if l < m19 then
          lemma19LadderKernel n h3 cStar scale19 l
        else
          lemma19FullActivationCappedKernel
            n h3 clockBudget

theorem lemma16To19CorrectedCappedScheduleKernel_eq_block
    (n : ℕ) (h3 : 3 ≤ n)
    (q16 k16 cStar m17 m19 D clockBudget : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ)
    (j : ℕ) :
    lemma16To19CorrectedCappedScheduleKernel
        n h3 q16 k16 cStar m17 m19 D clockBudget
        scale17 rho17 scale19 j =
      StagedFreezeControl.block
        (infectionRevealPhysicalStep n h3)
        (lemma16To19CorrectedBlockCheckpoint
          k16 m17 m19 scale17 scale19)
        (lemma16To19CorrectedBlockHorizon
          n q16 cStar m17 m19 clockBudget)
        j := by
  funext s
  cases j with
  | zero =>
      simpa [lemma16To19CorrectedCappedScheduleKernel,
        StagedFreezeControl.block,
        lemma16To19CorrectedBlockCheckpoint,
        lemma16To19CorrectedBlockRemaining,
        lemma16To19CorrectedBlockHorizon] using
        lemma16PhysicalStageKernel_eq_frozenPhysical
          n h3 k16 (cStar * q16 * n) s
  | succ j =>
      by_cases hj17 : j < m17
      · have hclock : j < m17 + m19 + 1 := by omega
        have hcheckpoint :
            lemma16To19CorrectedBlockCheckpoint
                k16 m17 m19 scale17 scale19 (j + 1) s =
              PhysicalActivationCheckpoint s
                (lemma17StageRemaining (scale17 j) s) := by
          funext current
          simp [lemma16To19CorrectedBlockCheckpoint,
            lemma16To19CorrectedBlockRemaining, hj17]
        have hfreeze :=
          physicalFreeze_congr
            (infectionRevealPhysicalStep n h3)
            (lemma16To19CorrectedBlockCheckpoint
              k16 m17 m19 scale17 scale19 (j + 1) s)
            (PhysicalActivationCheckpoint s
              (lemma17StageRemaining (scale17 j) s))
            (fun current => by rw [hcheckpoint])
        unfold StagedFreezeControl.block
        rw [hfreeze]
        simpa [lemma16To19CorrectedCappedScheduleKernel,
          lemma16To19CorrectedBlockHorizon,
          lemma17LadderKernel, hj17, hclock] using
          lemma17PhysicalStageKernel_eq_frozenPhysical
            n h3
            (lemma17StageRemaining (scale17 j) s)
            (2 * scale17 j) (19 * cStar * rho17 j)
            (cStar * n) s
      · by_cases hjEq : j = m17
        · subst j
          have hclock : m17 < m17 + m19 + 1 := by omega
          have hcheckpoint :
              lemma16To19CorrectedBlockCheckpoint
                  k16 m17 m19 scale17 scale19
                  (m17 + 1) s =
                PhysicalActivationCheckpoint s
                  (lemma17StageRemaining
                    (scale17 m17) s) := by
            funext current
            simp [lemma16To19CorrectedBlockCheckpoint,
              lemma16To19CorrectedBlockRemaining]
          have hfreeze :=
            physicalFreeze_congr
              (infectionRevealPhysicalStep n h3)
              (lemma16To19CorrectedBlockCheckpoint
                k16 m17 m19 scale17 scale19
                (m17 + 1) s)
              (PhysicalActivationCheckpoint s
                (lemma17StageRemaining
                  (scale17 m17) s))
              (fun current => by rw [hcheckpoint])
          unfold StagedFreezeControl.block
          rw [hfreeze]
          simpa [lemma16To19CorrectedCappedScheduleKernel,
            lemma16To19CorrectedBlockHorizon,
            lemma18FromGapBoundaryKernel, hclock] using
            lemma17PhysicalStageKernel_eq_frozenPhysical
              n h3
              (lemma17StageRemaining (scale17 m17) s)
              (2 * scale17 m17) (30 * D)
              (cStar * n) s
        · have hjTail : m17 + 1 ≤ j := by omega
          let l := additiveTailIndex (m17 + 1) j
          have hlSpec : m17 + 1 + l = j := by
            exact additiveTailIndex_spec
              (m17 + 1) j hjTail
          by_cases hl : l < m19
          · have hclock : j < m17 + m19 + 1 := by omega
            have hcheckpoint :
                lemma16To19CorrectedBlockCheckpoint
                    k16 m17 m19 scale17 scale19
                    (j + 1) s =
                  PhysicalActivationCheckpoint s
                    (lemma17StageRemaining
                      (scale19 l) s) := by
              funext current
              simp [lemma16To19CorrectedBlockCheckpoint,
                lemma16To19CorrectedBlockRemaining,
                hj17, hjEq, l, hl]
            have hfreeze :=
              physicalFreeze_congr
                (infectionRevealPhysicalStep n h3)
                (lemma16To19CorrectedBlockCheckpoint
                  k16 m17 m19 scale17 scale19
                  (j + 1) s)
                (PhysicalActivationCheckpoint s
                  (lemma17StageRemaining
                    (scale19 l) s))
                (fun current => by rw [hcheckpoint])
            unfold StagedFreezeControl.block
            rw [hfreeze]
            simpa [lemma16To19CorrectedCappedScheduleKernel,
              lemma16To19CorrectedBlockHorizon,
              lemma19LadderKernel, hj17, hjEq,
              l, hl, hclock] using
              lemma17PhysicalStageKernel_eq_frozenPhysical
                n h3
                (lemma17StageRemaining (scale19 l) s)
                (2 * scale19 l) 0 (cStar * n) s
          · have hclock :
                ¬ j < m17 + m19 + 1 := by
              omega
            have hcheckpoint :
                lemma16To19CorrectedBlockCheckpoint
                    k16 m17 m19 scale17 scale19
                    (j + 1) s =
                  PhysicalActivationCheckpoint s
                    s.inactive.ids.card := by
              funext current
              simp [lemma16To19CorrectedBlockCheckpoint,
                lemma16To19CorrectedBlockRemaining,
                hj17, hjEq, l, hl]
            have hfreeze :=
              physicalFreeze_congr
                (infectionRevealPhysicalStep n h3)
                (lemma16To19CorrectedBlockCheckpoint
                  k16 m17 m19 scale17 scale19
                  (j + 1) s)
                (PhysicalActivationCheckpoint s
                  s.inactive.ids.card)
                (fun current => by rw [hcheckpoint])
            unfold StagedFreezeControl.block
            rw [hfreeze]
            simpa [lemma16To19CorrectedCappedScheduleKernel,
              lemma16To19CorrectedBlockHorizon,
              lemma19FullActivationCappedKernel,
              hj17, hjEq, l, hl, hclock] using
              lemma17PhysicalStageKernel_eq_frozenPhysical
                n h3 s.inactive.ids.card n 0
                (lemma19FullActivationClockCap
                  n clockBudget) s

/-- Split a staged schedule after an additive number of blocks. -/
theorem stagedIter_add
    {α : Type*}
    (K : ℕ → α → PMF α)
    (m l : ℕ) (s : α) :
    stagedIter K (m + l) s =
      (stagedIter K m s).bind
        (stagedIter (fun j => K (m + j)) l) := by
  induction l with
  | zero =>
      simp [stagedIter, PMF.bind_pure]
  | succ l ih =>
      rw [Nat.add_succ]
      change
        (stagedIter K (m + l) s).bind (K (m + l)) =
          (stagedIter K m s).bind
            (fun z =>
              (stagedIter
                (fun j => K (m + j)) l z).bind
                  (K (m + l)))
      rw [ih, PMF.bind_bind]

/-- A head block, `m` body blocks, and a final block compose in that order. -/
theorem stagedIter_head_body_tail
    {α : Type*}
    (K0 : α → PMF α)
    (K : ℕ → α → PMF α)
    (Klast : α → PMF α)
    (m : ℕ) (s : α) :
    stagedIter
        (fun
          | 0 => K0
          | j + 1 => if j < m then K j else Klast)
        (m + 2) s =
      ((K0 s).bind (stagedIter K m)).bind Klast := by
  let Rest : ℕ → α → PMF α :=
    fun j => if j < m then K j else Klast
  have hcons :
      (fun
        | 0 => K0
        | j + 1 => if j < m then K j else Klast) =
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
          (m + 2) s =
        (K0 s).bind (stagedIter Rest (m + 1)) := by
    simpa only [Nat.add_assoc] using
      stagedIter_cons K0 Rest (m + 1) s
  rw [hhead]
  have hprefix :
      stagedIter Rest m = stagedIter K m := by
    apply stagedIter_congr_lt
    intro j hj
    funext z
    simp [Rest, hj]
  change
    (K0 s).bind (stagedIter Rest (m + 1)) =
      ((K0 s).bind (stagedIter K m)).bind Klast
  have hrest :
      stagedIter Rest (m + 1) =
        fun z => (stagedIter Rest m z).bind (Rest m) := by
    rfl
  rw [hrest, hprefix]
  have hlast : Rest m = Klast := by
    funext z
    simp [Rest]
  rw [hlast, PMF.bind_bind]

theorem lemma16To19CorrectedCappedScheduleKernel_stagedIter
    (n : ℕ) (h3 : 3 ≤ n)
    (q16 k16 cStar m17 m19 D clockBudget : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n) :
    stagedIter
        (lemma16To19CorrectedCappedScheduleKernel
          n h3 q16 k16 cStar m17 m19 D clockBudget
          scale17 rho17 scale19)
        (m17 + m19 + 3) s =
      ((((lemma16PhysicalStageKernel
                n h3 k16 (cStar * q16 * n) s).bind
              (fun z =>
                stagedIter
                  (lemma17LadderKernel
                    n h3 cStar scale17 rho17)
                  m17 z)).bind
            (lemma18FromGapBoundaryKernel
              n h3 (scale17 m17) D cStar)).bind
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
  let Decisive :=
    lemma18FromGapBoundaryKernel
      n h3 (scale17 m17) D cStar
  let New :=
    lemma19LadderKernel
      n h3 cStar scale19
  let Final :=
    lemma19FullActivationCappedKernel
      n h3 clockBudget
  let Rest : ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n)
    | j =>
        if j < m17 then
          Old j
        else if j = m17 then
          Decisive
        else
          let l := additiveTailIndex (m17 + 1) j
          if l < m19 then New l else Final
  have hcons :
      lemma16To19CorrectedCappedScheduleKernel
          n h3 q16 k16 cStar m17 m19 D clockBudget
          scale17 rho17 scale19 =
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
          (m17 + m19 + 3) s =
        (K0 s).bind
          (stagedIter Rest (m17 + m19 + 2)) := by
    simpa only [Nat.add_assoc] using
      stagedIter_cons K0 Rest (m17 + m19 + 2) s
  rw [hhead]
  have hprefix :
      stagedIter Rest m17 = stagedIter Old m17 := by
    apply stagedIter_congr_lt
    intro j hj
    funext z
    simp [Rest, hj]
  let Shift :
      ℕ → InfectionRevealPhysicalState n →
        PMF (InfectionRevealPhysicalState n)
    | 0 => Decisive
    | j + 1 => if j < m19 then New j else Final
  have hshift :
      (fun j => Rest (m17 + j)) = Shift := by
    funext j
    cases j with
    | zero =>
        simp [Rest, Shift]
    | succ j =>
        have hnotlt : ¬ m17 + (j + 1) < m17 := by
          omega
        have hidx :
            additiveTailIndex
                (m17 + 1) (m17 + (j + 1)) = j := by
          have hspec :=
            additiveTailIndex_spec
              (m17 + 1) (m17 + (j + 1))
              (by omega)
          omega
        simp [Rest, Shift, hnotlt, hidx]
  change
    (K0 s).bind
        (stagedIter Rest (m17 + m19 + 2)) =
      ((((K0 s).bind
              (fun z => stagedIter Old m17 z)).bind
            Decisive).bind
          (fun z => stagedIter New m19 z)).bind
        Final
  rw [show m17 + m19 + 2 = m17 + (m19 + 2) by
    omega]
  have hsplit :
      stagedIter Rest (m17 + (m19 + 2)) =
        fun z =>
          (stagedIter Rest m17 z).bind
            (stagedIter
              (fun j => Rest (m17 + j))
              (m19 + 2)) := by
    funext z
    exact stagedIter_add Rest m17 (m19 + 2) z
  rw [hsplit]
  rw [hprefix, hshift]
  rw [show stagedIter Shift (m19 + 2) =
      fun z =>
        ((Decisive z).bind
          (fun y => stagedIter New m19 y)).bind Final by
    funext z
    exact stagedIter_head_body_tail
      Decisive New Final m19 z]
  simp only [PMF.bind_bind]

theorem lemma16To19CorrectedBlockHorizon_pos
    (n q16 cStar m17 m19 clockBudget : ℕ)
    (hn : 0 < n) (hq16 : 0 < q16) (hcStar : 0 < cStar) :
    ∀ j < m17 + m19 + 3,
      0 <
        lemma16To19CorrectedBlockHorizon
          n q16 cStar m17 m19 clockBudget j := by
  intro j hj
  cases j with
  | zero =>
      simp [lemma16To19CorrectedBlockHorizon,
        hn, hq16, hcStar]
  | succ j =>
      by_cases hstage : j < m17 + m19 + 1
      · simpa [lemma16To19CorrectedBlockHorizon,
          hstage] using Nat.mul_pos hcStar hn
      · have hcap :
            0 <
              1024 * n *
                (3 * clockBudget +
                  Nat.log 2 n + 1) := by
          positivity
        simpa [lemma16To19CorrectedBlockHorizon,
          hstage, lemma19FullActivationClockCap] using hcap

/-- Exact fixed raw clock of the corrected physical schedule. -/
def lemma16To19CorrectedRawClock
    (n q16 cStar m17 m19 clockBudget : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m17 + m19 + 3),
    lemma16To19CorrectedBlockHorizon
      n q16 cStar m17 m19 clockBudget j

/-- Flatten the corrected Lemma 16, Lemma 17 ladder, decisive Lemma 18,
positive-gap Lemma 19 ladder, and capped late block to one raw frozen
physical iterate. -/
theorem lemma16To19_corrected_physical_clock_failure_le
    (n q16 k16 cStar m17 m19 D clockBudget
      targetGap : ℕ)
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
          (lemma16To19CorrectedRawClock
            n q16 cStar m17 m19 clockBudget)
          s)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    terminalFailureMass
        (((lemma16PhysicalStageKernel
              n h3 k16 (cStar * q16 * n) s).bind
            (fun z =>
              stagedIter
                (lemma17LadderKernel
                  n h3 cStar scale17 rho17)
                m17 z)).bind
          (fun z =>
            ((lemma18FromGapBoundaryKernel
                  n h3 (scale17 m17) D cStar z).bind
                (fun y =>
                  stagedIter
                    (lemma19LadderKernel
                      n h3 cStar scale19)
                    m19 y)).bind
              (lemma19FullActivationBudgetKernel
                n h3 clockBudget)))
        (Lemma19PhysicalStageRangeGood n targetGap) := by
  let K :=
    lemma16To19CorrectedCappedScheduleKernel
      n h3 q16 k16 cStar m17 m19 D clockBudget
      scale17 rho17 scale19
  have hclock :=
    StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
      (Lemma19PhysicalStageRangeGood n targetGap)
      (infectionRevealPhysicalStep n h3)
      (lemma16To19CorrectedBlockCheckpoint
        k16 m17 m19 scale17 scale19)
      (lemma16To19CorrectedBlockHorizon
        n q16 cStar m17 m19 clockBudget)
      (m17 + m19 + 3)
      (lemma16To19CorrectedBlockHorizon_pos
        n q16 cStar m17 m19 clockBudget
        (by omega) hq16 hcStar)
      s
  have hblocks :
      StagedFreezeControl.block
          (infectionRevealPhysicalStep n h3)
          (lemma16To19CorrectedBlockCheckpoint
            k16 m17 m19 scale17 scale19)
          (lemma16To19CorrectedBlockHorizon
            n q16 cStar m17 m19 clockBudget) =
        K := by
    funext j
    exact
      (lemma16To19CorrectedCappedScheduleKernel_eq_block
        n h3 q16 k16 cStar m17 m19 D clockBudget
        scale17 rho17 scale19 j).symm
  rw [hblocks] at hclock
  rw [show stagedIter K (m17 + m19 + 3) s =
      ((((lemma16PhysicalStageKernel
                n h3 k16 (cStar * q16 * n) s).bind
              (fun z =>
                stagedIter
                  (lemma17LadderKernel
                    n h3 cStar scale17 rho17)
                  m17 z)).bind
            (lemma18FromGapBoundaryKernel
              n h3 (scale17 m17) D cStar)).bind
          (fun z =>
            stagedIter
              (lemma19LadderKernel
                n h3 cStar scale19)
              m19 z)).bind
        (lemma19FullActivationCappedKernel
          n h3 clockBudget) by
      exact
        lemma16To19CorrectedCappedScheduleKernel_stagedIter
          n h3 q16 k16 cStar m17 m19 D clockBudget
          scale17 rho17 scale19 s] at hclock
  have hcapped :=
    terminalFailureMass_bind_capped_final_le
      n h3 clockBudget targetGap
      ((((lemma16PhysicalStageKernel
              n h3 k16 (cStar * q16 * n) s).bind
            (fun z =>
              stagedIter
                (lemma17LadderKernel
                  n h3 cStar scale17 rho17)
                m17 z)).bind
          (lemma18FromGapBoundaryKernel
            n h3 (scale17 m17) D cStar)).bind
        (fun z =>
          stagedIter
            (lemma19LadderKernel
              n h3 cStar scale19)
            m19 z))
  simpa only [lemma16To19CorrectedRawClock,
    PMF.bind_bind] using hclock.trans hcapped

end

end Tri

#print axioms Tri.additiveTailIndex_spec
#print axioms Tri.lemma16To19CorrectedCappedScheduleKernel_eq_block
#print axioms Tri.stagedIter_add
#print axioms Tri.stagedIter_head_body_tail
#print axioms Tri.lemma16To19CorrectedCappedScheduleKernel_stagedIter
#print axioms Tri.lemma16To19CorrectedBlockHorizon_pos
#print axioms Tri.lemma16To19_corrected_physical_clock_failure_le
