/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19CorrectedClock
import Tri.InfectionPhysicalClockProjection

/-!
# Coarse raw-clock form of the corrected activation route

The corrected physical schedule is projected to the ordinary infection chain,
and its exact block sum is bounded by the same linear headline clock after
counting both finite ladders.
-/

namespace Tri

open scoped ENNReal

noncomputable section

theorem lemma16To19CorrectedRawClock_pos
    (n q16 cStar m17 m19 clockBudget : ℕ)
    (hn : 0 < n) (hq16 : 0 < q16) (hcStar : 0 < cStar) :
    0 <
      lemma16To19CorrectedRawClock
        n q16 cStar m17 m19 clockBudget := by
  unfold lemma16To19CorrectedRawClock
  apply Finset.sum_pos'
  · intro j hj
    exact Nat.zero_le _
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    exact
      lemma16To19CorrectedBlockHorizon_pos
        n q16 cStar m17 m19 clockBudget
        hn hq16 hcStar 0 (by omega)

theorem lemma16To19CorrectedRawClock_eq
    (n q16 cStar m17 m19 clockBudget : ℕ) :
    lemma16To19CorrectedRawClock
        n q16 cStar m17 m19 clockBudget =
      cStar * q16 * n +
        (m17 + m19 + 1) * (cStar * n) +
        lemma19FullActivationClockCap n clockBudget := by
  let f :=
    lemma16To19CorrectedBlockHorizon
      n q16 cStar m17 m19 clockBudget
  let b := m17 + m19 + 1
  have hmiddle :
      (∑ j ∈ Finset.range b, f (j + 1)) =
        b * (cStar * n) := by
    calc
      (∑ j ∈ Finset.range b, f (j + 1)) =
          ∑ _j ∈ Finset.range b, cStar * n := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjb : j < m17 + m19 + 1 := by
          simpa [b] using Finset.mem_range.mp hj
        simp [f, lemma16To19CorrectedBlockHorizon,
          hjb]
      _ = b * (cStar * n) := by simp
  unfold lemma16To19CorrectedRawClock
  rw [show m17 + m19 + 3 = (b + 1) + 1 by
    simp [b]]
  rw [Finset.sum_range_succ']
  change
    (∑ j ∈ Finset.range (b + 1), f (j + 1)) +
        f 0 = _
  rw [Finset.sum_range_succ, hmiddle]
  simp [f, b, lemma16To19CorrectedBlockHorizon]
  ring

/-- Linear headline envelope with both ladder counts included. -/
theorem lemma16To19CorrectedRawClock_le_two_budget
    (n q16 cStar m17 m19 clockBudget : ℕ)
    (hq16 : 1 ≤ q16)
    (hm : m17 + m19 + 1 ≤ q16)
    (hbudget : clockBudget ≤ 2 * q16)
    (hlog : Nat.log 2 n ≤ q16) :
    lemma16To19CorrectedRawClock
        n q16 cStar m17 m19 clockBudget ≤
      (2 * cStar + 8192) * q16 * n := by
  have hmiddle :
      (m17 + m19 + 1) * (cStar * n) ≤
        q16 * (cStar * n) :=
    Nat.mul_le_mul_right (cStar * n) hm
  have hcapInner :
      3 * clockBudget + Nat.log 2 n + 1 ≤
        8 * q16 := by
    omega
  have hcap :
      lemma19FullActivationClockCap n clockBudget ≤
        1024 * n * (8 * q16) := by
    unfold lemma19FullActivationClockCap
    exact Nat.mul_le_mul_left (1024 * n) hcapInner
  rw [lemma16To19CorrectedRawClock_eq]
  calc
    cStar * q16 * n +
          (m17 + m19 + 1) * (cStar * n) +
          lemma19FullActivationClockCap n clockBudget
        ≤
      cStar * q16 * n +
          q16 * (cStar * n) +
          1024 * n * (8 * q16) :=
      add_le_add (add_le_add le_rfl hmiddle) hcap
    _ = (2 * cStar + 8192) * q16 * n := by
      ring

/-- A corrected composed physical estimate transfers to the coarse infection
chain at the exact corrected raw clock. -/
theorem lemma16To19_corrected_coarse_clock_failure_le_of_schedule
    (n q16 k16 cStar m17 m19 D clockBudget
      targetGap : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ)
    (h3 : 3 ≤ n)
    (hq16 : 0 < q16)
    (hcStar : 0 < cStar)
    (s : InfectionRevealPhysicalState n)
    (ε : ℝ≥0∞)
    (hschedule :
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
          (Lemma19PhysicalStageRangeGood n targetGap)
        ≤ ε) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          (lemma16To19CorrectedRawClock
            n q16 cStar m17 m19 clockBudget)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap)
      ≤ ε := by
  rw [← infectionRevealPhysicalStep_iter_freeze_failure_eq
    n h3 targetGap
      (lemma16To19CorrectedRawClock
        n q16 cStar m17 m19 clockBudget) s]
  exact
    (lemma16To19_corrected_physical_clock_failure_le
      n q16 k16 cStar m17 m19 D clockBudget
      targetGap scale17 rho17 scale19
      h3 hq16 hcStar s).trans hschedule

/-- Pad the exact corrected clock to the advertised linear raw clock. -/
theorem lemma16To19_corrected_coarse_headline_failure_le_of_schedule
    (n q16 k16 cStar m17 m19 D clockBudget
      targetGap : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ)
    (h3 : 3 ≤ n)
    (hq16 : 1 ≤ q16)
    (hm : m17 + m19 + 1 ≤ q16)
    (hbudget : clockBudget ≤ 2 * q16)
    (hlog : Nat.log 2 n ≤ q16)
    (hcStar : 0 < cStar)
    (s : InfectionRevealPhysicalState n)
    (ε : ℝ≥0∞)
    (hschedule :
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
          (Lemma19PhysicalStageRangeGood n targetGap)
        ≤ ε) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          ((2 * cStar + 8192) * q16 * n)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap)
      ≤ ε := by
  have hexact :=
    lemma16To19_corrected_coarse_clock_failure_le_of_schedule
      n q16 k16 cStar m17 m19 D clockBudget
      targetGap scale17 rho17 scale19
      h3 (by omega) hcStar s ε hschedule
  have hclock :=
    lemma16To19CorrectedRawClock_le_two_budget
      n q16 cStar m17 m19 clockBudget
      hq16 hm hbudget hlog
  exact
    (terminalFailureMass_iter_freeze_antitone_of_subset
      (InfectionActivationGapRangeGood n targetGap)
      (InfectionActivationGapRangeGood n targetGap)
      (infectionStateStep n h3)
      (fun _ hz => hz)
      (lemma16To19CorrectedRawClock
        n q16 cStar m17 m19 clockBudget)
      ((2 * cStar + 8192) * q16 * n)
      hclock
      (infectionRevealPhysicalForget s)).trans
        hexact

end

end Tri

#print axioms Tri.lemma16To19CorrectedRawClock_pos
#print axioms Tri.lemma16To19CorrectedRawClock_eq
#print axioms Tri.lemma16To19CorrectedRawClock_le_two_budget
#print axioms Tri.lemma16To19_corrected_coarse_clock_failure_le_of_schedule
#print axioms Tri.lemma16To19_corrected_coarse_headline_failure_le_of_schedule
