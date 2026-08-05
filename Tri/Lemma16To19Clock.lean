/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PhysicalStageClock

/-!
# Raw physical clock for the Lemma 16--19 schedule

The endpoint-dependent final activation horizon is padded to a uniform cap.
Every counted block is then flattened into a fixed-length lazy schedule, so
the full physical Lemma 16--19 estimate transfers to the genuine raw
identity-refined infection clock.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Frozen kernels agree for extensionally equivalent checkpoints. -/
theorem physicalFreeze_congr
    {α : Type*}
    (K : α → PMF α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ s, P s ↔ Q s) :
    freeze P K = freeze Q K := by
  funext s
  by_cases hP : P s
  · rw [freeze_of_mem s hP,
      freeze_of_mem s ((h s).1 hP)]
  · rw [freeze_of_not_mem s hP,
      freeze_of_not_mem s
        (fun hQ => hP ((h s).2 hQ))]

/-- Uniform deterministic cap for the endpoint-dependent Lemma 19 clock. -/
def lemma19FullActivationClockCap
    (n clockBudget : ℕ) : ℕ :=
  1024 * n *
    (3 * clockBudget + Nat.log 2 n + 1)

theorem infectionLateBudgetHorizon_le_fullActivationClockCap
    (n clockBudget : ℕ)
    (s : InfectionRevealPhysicalState n) :
    infectionLateBudgetHorizon
        n clockBudget s.inactive.ids.card ≤
      lemma19FullActivationClockCap n clockBudget := by
  have hpool : s.inactive.ids.card ≤ n := by
    have htotal := infectionReveal_active_add_inactive s
    omega
  calc
    infectionLateBudgetHorizon
        n clockBudget s.inactive.ids.card
        ≤
      1024 * n *
        (3 * clockBudget +
          infectionLateStages s.inactive.ids.card) :=
      infectionLateBudgetHorizon_le
        n clockBudget s.inactive.ids.card
    _ ≤
      1024 * n *
        (3 * clockBudget + Nat.log 2 n + 1) := by
      apply Nat.mul_le_mul_left
      have hstage :=
        infectionLateStages_le_log_succ
          s.inactive.ids.card
      have hlog :=
        Nat.log_mono_right (b := 2) hpool
      omega

/-- Fixed-cap version of the endpoint-dependent final activation block. -/
noncomputable def lemma19FullActivationCappedKernel
    (n : ℕ) (h3 : 3 ≤ n) (clockBudget : ℕ) :
    InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun s =>
    lemma17PhysicalStageKernel
      n h3 s.inactive.ids.card n 0
      (lemma19FullActivationClockCap n clockBudget) s

theorem lemma19FullActivationCappedKernel_failure_le_budget
    (n : ℕ) (h3 : 3 ≤ n)
    (clockBudget targetGap : ℕ)
    (s : InfectionRevealPhysicalState n) :
    terminalFailureMass
        (lemma19FullActivationCappedKernel
          n h3 clockBudget s)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    terminalFailureMass
        (lemma19FullActivationBudgetKernel
          n h3 clockBudget s)
        (Lemma19PhysicalStageRangeGood n targetGap) := by
  let A : InfectionRevealPhysicalState n → Prop :=
    Lemma19PhysicalStageRangeGood n targetGap
  let B : InfectionRevealPhysicalState n → Prop :=
    PhysicalActivationCheckpoint s s.inactive.ids.card
  have hsubset : ∀ z, A z → B z := by
    intro z hz
    have htotal := infectionReveal_active_add_inactive s
    unfold A at hz
    unfold Lemma19PhysicalStageRangeGood at hz
    unfold B PhysicalActivationCheckpoint
    omega
  have htime :=
    infectionLateBudgetHorizon_le_fullActivationClockCap
      n clockBudget s
  unfold lemma19FullActivationCappedKernel
    lemma19FullActivationBudgetKernel
  rw [lemma17PhysicalStageKernel_eq_frozenPhysical,
    lemma17PhysicalStageKernel_eq_frozenPhysical]
  exact
    terminalFailureMass_iter_freeze_antitone_of_subset
      A B (infectionRevealPhysicalStep n h3)
      hsubset
      (infectionLateBudgetHorizon
        n clockBudget s.inactive.ids.card)
      (lemma19FullActivationClockCap n clockBudget)
      htime s

theorem terminalFailureMass_bind_capped_final_le
    (n : ℕ) (h3 : 3 ≤ n)
    (clockBudget targetGap : ℕ)
    (p : PMF (InfectionRevealPhysicalState n)) :
    terminalFailureMass
        (p.bind
          (lemma19FullActivationCappedKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    terminalFailureMass
        (p.bind
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood n targetGap) := by
  rw [terminalFailureMass_bind, terminalFailureMass_bind]
  unfold expect
  exact ENNReal.tsum_le_tsum fun s =>
    mul_le_mul_right
      (lemma19FullActivationCappedKernel_failure_le_budget
        n h3 clockBudget targetGap s)
      (p s)

/-- Fixed horizon assigned to each block in the Lemma 16--19 schedule. -/
def lemma16To19BlockHorizon
    (n q16 cStar m clockBudget : ℕ) : ℕ → ℕ
  | 0 => cStar * q16 * n
  | j + 1 =>
      if j ≤ m then cStar * n
      else lemma19FullActivationClockCap n clockBudget

/-- Endpoint-dependent activation count remaining in each fixed block. -/
noncomputable def lemma16To19BlockRemaining
    {n : ℕ} (k16 m : ℕ) (scale : ℕ → ℕ) :
    ℕ → InfectionRevealPhysicalState n → ℕ
  | 0, _ => k16
  | j + 1, s =>
      if j < m then
        lemma17StageRemaining (scale j) s
      else if j = m then
        lemma17StageRemaining (scale m) s
      else
        s.inactive.ids.card

/-- Frozen checkpoint family underlying the complete fixed schedule. -/
def lemma16To19BlockCheckpoint
    {n : ℕ} (k16 m : ℕ) (scale : ℕ → ℕ)
    (j : ℕ) (anchor current : InfectionRevealPhysicalState n) : Prop :=
  PhysicalActivationCheckpoint anchor
    (lemma16To19BlockRemaining k16 m scale j anchor)
    current

noncomputable instance lemma16To19BlockCheckpointDecidable
    {n : ℕ} (k16 m : ℕ) (scale : ℕ → ℕ)
    (j : ℕ) (anchor : InfectionRevealPhysicalState n) :
    DecidablePred
      (lemma16To19BlockCheckpoint k16 m scale j anchor) :=
  Classical.decPred _

/-- Original physical block kernels with the final random clock replaced by
its fixed cap. -/
noncomputable def lemma16To19CappedScheduleKernel
    (n : ℕ) (h3 : 3 ≤ n)
    (q16 k16 cStar m D clockBudget : ℕ)
    (scale rho : ℕ → ℕ) :
    ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n)
  | 0 =>
      lemma16PhysicalStageKernel
        n h3 k16 (cStar * q16 * n)
  | j + 1 =>
      if j < m then
        lemma17LadderKernel n h3 cStar scale rho j
      else if j = m then
        lemma18FromGapBoundaryKernel
          n h3 (scale m) D cStar
      else
        lemma19FullActivationCappedKernel
          n h3 clockBudget

theorem lemma16To19CappedScheduleKernel_eq_block
    (n : ℕ) (h3 : 3 ≤ n)
    (q16 k16 cStar m D clockBudget : ℕ)
    (scale rho : ℕ → ℕ)
    (j : ℕ) :
    lemma16To19CappedScheduleKernel
        n h3 q16 k16 cStar m D clockBudget
        scale rho j =
      StagedFreezeControl.block
        (infectionRevealPhysicalStep n h3)
        (lemma16To19BlockCheckpoint k16 m scale)
        (lemma16To19BlockHorizon
          n q16 cStar m clockBudget)
        j := by
  funext s
  cases j with
  | zero =>
      simpa [lemma16To19CappedScheduleKernel,
        StagedFreezeControl.block,
        lemma16To19BlockCheckpoint,
        lemma16To19BlockRemaining,
        lemma16To19BlockHorizon] using
        lemma16PhysicalStageKernel_eq_frozenPhysical
          n h3 k16 (cStar * q16 * n) s
  | succ j =>
      by_cases hj : j < m
      · have hcheckpoint :
            lemma16To19BlockCheckpoint
                k16 m scale (j + 1) s =
              PhysicalActivationCheckpoint s
                (lemma17StageRemaining (scale j) s) := by
          funext current
          simp [lemma16To19BlockCheckpoint,
            lemma16To19BlockRemaining, hj]
        have hfreeze :=
          physicalFreeze_congr
            (infectionRevealPhysicalStep n h3)
            (lemma16To19BlockCheckpoint
              k16 m scale (j + 1) s)
            (PhysicalActivationCheckpoint s
              (lemma17StageRemaining (scale j) s))
            (fun current => by rw [hcheckpoint])
        unfold StagedFreezeControl.block
        rw [hfreeze]
        simpa [lemma16To19CappedScheduleKernel,
          lemma16To19BlockCheckpoint,
          lemma16To19BlockRemaining,
          lemma16To19BlockHorizon,
          lemma17LadderKernel, hj,
          Nat.le_of_lt hj, hcheckpoint] using
          lemma17PhysicalStageKernel_eq_frozenPhysical
            n h3
            (lemma17StageRemaining (scale j) s)
            (2 * scale j) (19 * cStar * rho j)
            (cStar * n) s
      · by_cases hjm : j = m
        · subst j
          have hcheckpoint :
              lemma16To19BlockCheckpoint
                  k16 m scale (m + 1) s =
                PhysicalActivationCheckpoint s
                  (lemma17StageRemaining (scale m) s) := by
            funext current
            simp [lemma16To19BlockCheckpoint,
              lemma16To19BlockRemaining]
          have hfreeze :=
            physicalFreeze_congr
              (infectionRevealPhysicalStep n h3)
              (lemma16To19BlockCheckpoint
                k16 m scale (m + 1) s)
              (PhysicalActivationCheckpoint s
                (lemma17StageRemaining (scale m) s))
              (fun current => by rw [hcheckpoint])
          unfold StagedFreezeControl.block
          rw [hfreeze]
          simpa [lemma16To19CappedScheduleKernel,
            lemma16To19BlockCheckpoint,
            lemma16To19BlockRemaining,
            lemma16To19BlockHorizon,
            lemma18FromGapBoundaryKernel,
            hcheckpoint] using
            lemma17PhysicalStageKernel_eq_frozenPhysical
              n h3
              (lemma17StageRemaining (scale m) s)
              (2 * scale m) (30 * D)
              (cStar * n) s
        · have hmj : ¬ j ≤ m := by omega
          have hcheckpoint :
              lemma16To19BlockCheckpoint
                  k16 m scale (j + 1) s =
                PhysicalActivationCheckpoint s
                  s.inactive.ids.card := by
            funext current
            simp [lemma16To19BlockCheckpoint,
              lemma16To19BlockRemaining, hj, hjm]
          have hfreeze :=
            physicalFreeze_congr
              (infectionRevealPhysicalStep n h3)
              (lemma16To19BlockCheckpoint
                k16 m scale (j + 1) s)
              (PhysicalActivationCheckpoint s
                s.inactive.ids.card)
              (fun current => by rw [hcheckpoint])
          unfold StagedFreezeControl.block
          rw [hfreeze]
          simpa [lemma16To19CappedScheduleKernel,
            lemma16To19BlockCheckpoint,
            lemma16To19BlockRemaining,
            lemma16To19BlockHorizon,
            lemma19FullActivationCappedKernel,
            hj, hjm, hmj, hcheckpoint] using
            lemma17PhysicalStageKernel_eq_frozenPhysical
              n h3 s.inactive.ids.card n 0
              (lemma19FullActivationClockCap
                n clockBudget) s

theorem stagedIter_congr_lt
    {α : Type*}
    (K L : ℕ → α → PMF α)
    (m : ℕ)
    (h : ∀ j < m, K j = L j) :
    stagedIter K m = stagedIter L m := by
  funext s
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      change
        (stagedIter K m s).bind (K m) =
          (stagedIter L m s).bind (L m)
      rw [ih (fun j hj =>
        h j (hj.trans (Nat.lt_succ_self m)))]
      rw [h m (Nat.lt_succ_self m)]

theorem stagedIter_cons
    {α : Type*}
    (K0 : α → PMF α)
    (K : ℕ → α → PMF α)
    (m : ℕ) (s : α) :
    stagedIter (fun
      | 0 => K0
      | j + 1 => K j) (m + 1) s =
      (K0 s).bind (stagedIter K m) := by
  induction m with
  | zero =>
      simp [stagedIter, PMF.bind_pure]
  | succ m ih =>
      change
        (stagedIter (fun
          | 0 => K0
          | j + 1 => K j) (m + 1) s).bind (K m) =
        (K0 s).bind (stagedIter K (m + 1))
      rw [ih, show stagedIter K (m + 1) =
        fun z => (stagedIter K m z).bind (K m) from rfl]
      exact PMF.bind_bind _ _ _

theorem lemma16To19CappedScheduleKernel_stagedIter
    (n : ℕ) (h3 : 3 ≤ n)
    (q16 k16 cStar m D clockBudget : ℕ)
    (scale rho : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n) :
    stagedIter
        (lemma16To19CappedScheduleKernel
          n h3 q16 k16 cStar m D clockBudget
          scale rho)
        (m + 3) s =
      (((lemma16PhysicalStageKernel
              n h3 k16 (cStar * q16 * n) s).bind
            (fun z =>
              stagedIter
                (lemma17LadderKernel
                  n h3 cStar scale rho)
                m z)).bind
          (lemma18FromGapBoundaryKernel
            n h3 (scale m) D cStar)).bind
        (lemma19FullActivationCappedKernel
          n h3 clockBudget) := by
  let K0 :=
    lemma16PhysicalStageKernel
      n h3 k16 (cStar * q16 * n)
  let Rest : ℕ → InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n)
    | j =>
        if j < m then
          lemma17LadderKernel
            n h3 cStar scale rho j
        else if j = m then
          lemma18FromGapBoundaryKernel
            n h3 (scale m) D cStar
        else
          lemma19FullActivationCappedKernel
            n h3 clockBudget
  have hcons :
      lemma16To19CappedScheduleKernel
          n h3 q16 k16 cStar m D clockBudget
          scale rho =
        fun
        | 0 => K0
        | j + 1 => Rest j := by
    funext j
    cases j <;> rfl
  rw [hcons]
  rw [show m + 3 = (m + 2) + 1 by omega]
  rw [stagedIter_cons K0 Rest (m + 2) s]
  have hprefix :
      stagedIter Rest m =
        stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho) m := by
    apply stagedIter_congr_lt
    intro j hj
    funext z
    simp [Rest, hj]
  change
    (K0 s).bind (stagedIter Rest (m + 2)) =
      (((K0 s).bind
          (fun z =>
            stagedIter
              (lemma17LadderKernel
                n h3 cStar scale rho) m z)).bind
        (lemma18FromGapBoundaryKernel
          n h3 (scale m) D cStar)).bind
      (lemma19FullActivationCappedKernel
        n h3 clockBudget)
  have hrest :
      stagedIter Rest (m + 2) =
        fun z =>
          ((stagedIter Rest m z).bind (Rest m)).bind
            (Rest (m + 1)) := by
    rfl
  rw [hrest]
  rw [hprefix]
  have hRestM :
      Rest m =
        lemma18FromGapBoundaryKernel
          n h3 (scale m) D cStar := by
    funext z
    simp [Rest]
  have hRestNext :
      Rest (m + 1) =
        lemma19FullActivationCappedKernel
          n h3 clockBudget := by
    funext z
    simp [Rest]
  rw [hRestM, hRestNext]
  simp only [PMF.bind_bind]

theorem lemma16To19BlockHorizon_pos
    (n q16 cStar m clockBudget : ℕ)
    (hn : 0 < n) (hq16 : 0 < q16) (hcStar : 0 < cStar) :
    ∀ j < m + 3,
      0 <
        lemma16To19BlockHorizon
          n q16 cStar m clockBudget j := by
  intro j hj
  cases j with
  | zero =>
      simp [lemma16To19BlockHorizon,
        hn, hq16, hcStar]
  | succ j =>
      by_cases hjm : j ≤ m
      · simpa [lemma16To19BlockHorizon, hjm] using
          Nat.mul_pos hcStar hn
      · have hcap :
            0 <
              1024 * n *
                (3 * clockBudget + Nat.log 2 n + 1) := by
          positivity
        simpa [lemma16To19BlockHorizon, hjm,
          lemma19FullActivationClockCap] using hcap

theorem lemma16To19_physical_clock_failure_le
    (n q16 k16 cStar m D clockBudget targetGap : ℕ)
    (scale rho : ℕ → ℕ)
    (h3 : 3 ≤ n)
    (hq16 : 0 < q16)
    (hcStar : 0 < cStar)
    (s : InfectionRevealPhysicalState n) :
    terminalFailureMass
        (iter
          (freeze
            (Lemma19PhysicalStageRangeGood n targetGap)
            (infectionRevealPhysicalStep n h3))
          (∑ j ∈ Finset.range (m + 3),
            lemma16To19BlockHorizon
              n q16 cStar m clockBudget j)
          s)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
    terminalFailureMass
        (((lemma16PhysicalStageKernel
              n h3 k16 (cStar * q16 * n) s).bind
            (fun z =>
              stagedIter
                (lemma17LadderKernel
                  n h3 cStar scale rho)
                m z)).bind
          (fun z =>
            (lemma18FromGapBoundaryKernel
                n h3 (scale m) D cStar z).bind
              (lemma19FullActivationBudgetKernel
                n h3 clockBudget)))
        (Lemma19PhysicalStageRangeGood n targetGap) := by
  let K :=
    lemma16To19CappedScheduleKernel
      n h3 q16 k16 cStar m D clockBudget scale rho
  have hclock :=
    StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
      (Lemma19PhysicalStageRangeGood n targetGap)
      (infectionRevealPhysicalStep n h3)
      (lemma16To19BlockCheckpoint k16 m scale)
      (lemma16To19BlockHorizon
        n q16 cStar m clockBudget)
      (m + 3)
      (lemma16To19BlockHorizon_pos
        n q16 cStar m clockBudget
        (by omega) hq16 hcStar)
      s
  have hblocks :
      StagedFreezeControl.block
          (infectionRevealPhysicalStep n h3)
          (lemma16To19BlockCheckpoint k16 m scale)
          (lemma16To19BlockHorizon
            n q16 cStar m clockBudget) =
        K := by
    funext j
    exact
      (lemma16To19CappedScheduleKernel_eq_block
        n h3 q16 k16 cStar m D clockBudget
        scale rho j).symm
  rw [hblocks] at hclock
  rw [show stagedIter K (m + 3) s =
      (((lemma16PhysicalStageKernel
              n h3 k16 (cStar * q16 * n) s).bind
            (fun z =>
              stagedIter
                (lemma17LadderKernel
                  n h3 cStar scale rho)
                m z)).bind
          (lemma18FromGapBoundaryKernel
            n h3 (scale m) D cStar)).bind
        (lemma19FullActivationCappedKernel
          n h3 clockBudget) by
      exact lemma16To19CappedScheduleKernel_stagedIter
        n h3 q16 k16 cStar m D clockBudget
        scale rho s] at hclock
  have hcapped :=
    terminalFailureMass_bind_capped_final_le
      n h3 clockBudget targetGap
      ((lemma16PhysicalStageKernel
            n h3 k16 (cStar * q16 * n) s).bind
        (fun z =>
          stagedIter
            (lemma17LadderKernel
              n h3 cStar scale rho)
            m z) |>.bind
        (lemma18FromGapBoundaryKernel
          n h3 (scale m) D cStar))
  simpa only [PMF.bind_bind] using hclock.trans hcapped

end

end Tri

#print axioms Tri.infectionLateBudgetHorizon_le_fullActivationClockCap
#print axioms Tri.lemma19FullActivationCappedKernel_failure_le_budget
#print axioms Tri.terminalFailureMass_bind_capped_final_le
#print axioms Tri.lemma16To19CappedScheduleKernel_eq_block
#print axioms Tri.lemma16To19CappedScheduleKernel_stagedIter
#print axioms Tri.lemma16To19_physical_clock_failure_le
#print axioms Tri.physicalFreeze_congr
