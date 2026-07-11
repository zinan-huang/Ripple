/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `TransitionClockPairBound` — the window-leg `AllPhaseClockPairBound`, assembled.

Combines the per-phase dispatch bounds (`TransitionClockDispatch`, all 11 phases) with
Layers 1/2 (`TransitionClockLayers`) and the landed phase-0 pair bound
(`Phase0Window.clockSummand_pair_le`) into `ClockDriftCardWindow.AllPhaseClockPairBound`
— closing the C0 window leg's last field.

Structure: `Transition r₁ r₂ = finishPhase10Entry … (dispatch (phaseEpidemicUpdate r₁ r₂))`.
* If both inputs are at phase 0, `clockSummand_pair_le` gives the bound directly.
* Otherwise `phaseEpidemicUpdate` lifts both to `max ≥ 1`, the dispatch is some
  `PhaseNTransition` with `N ≥ 1` (no fresh clock), bounded per-phase via
  `pair_le_of_components`; Layer 1 makes `finishPhase10Entry` transparent and Layer 2
  bounds `phaseEpidemicUpdate` outputs by the inputs.

All axiom-clean.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TransitionClockDispatch

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace TransitionClockPairBound

open Phase0Window AllPhaseClockPairBoundProof TransitionClockLayers
open TransitionClockDispatch ClockDriftCardWindow Phase0PrefixTailDischarge

variable {L K : ℕ}

-- The 11-arm dispatch case split (`interval_cases` over the 10 active phases,
-- each reducing a large `PhaseNTransition` match) exceeds the default budget.
set_option maxHeartbeats 2000000 in
/-- The window-leg per-pair clock-summand bound, fully assembled. -/
theorem allPhaseClockPairBound : ClockDriftCardWindow.AllPhaseClockPairBound (L := L) (K := K) where
  hpair := by
    intro r₁ r₂
    by_cases h0 : r₁.phase.val = 0 ∧ r₂.phase.val = 0
    · -- Both inputs at phase 0: the landed phase-0 pair bound is exactly the goal.
      simpa [phase0AffineB] using
        clockSummand_pair_le (L := L) (K := K) 1 (by norm_num) r₁ r₂ h0.1 h0.2
    · -- Not both at phase 0: `phaseEpidemicUpdate` lifts to `max ≥ 1`; dispatch is `PhaseN`, `N ≥ 1`.
      rcases hpe : phaseEpidemicUpdate L K r₁ r₂ with ⟨s', t'⟩
      have hL2s : clockSummand (L := L) (K := K) 1 s' ≤ clockSummand (L := L) (K := K) 1 r₁ := by
        have h := clockSummand_phaseEpidemicUpdate_le_left (L := L) (K := K) r₁ r₂
        rw [hpe] at h; simpa using h
      have hL2t : clockSummand (L := L) (K := K) 1 t' ≤ clockSummand (L := L) (K := K) 1 r₂ := by
        have h := clockSummand_phaseEpidemicUpdate_le_right (L := L) (K := K) r₁ r₂
        rw [hpe] at h; simpa using h
      have hmax : 1 ≤ s'.phase.val := by
        have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) r₁ r₂
        rw [hpe] at hge
        refine le_trans ?_ hge
        rcases Nat.eq_zero_or_pos r₁.phase.val with h1 | h1
        · rcases Nat.eq_zero_or_pos r₂.phase.val with h2 | h2
          · exact absurd ⟨h1, h2⟩ h0
          · exact le_trans h2 (le_max_right _ _)
        · exact le_trans h1 (le_max_left _ _)
      -- Layer 1 + per-phase dispatch bound, then Layer 2.
      have key : clockSummand (L := L) (K := K) 1 (Transition L K r₁ r₂).1
            + clockSummand (L := L) (K := K) 1 (Transition L K r₁ r₂).2
          ≤ ENNReal.ofReal (Real.exp 1)
              * (clockSummand (L := L) (K := K) 1 s' + clockSummand (L := L) (K := K) 1 t')
            + phase0AffineB L := by
        unfold Transition
        rw [hpe]
        simp only [clockSummand_finishPhase10Entry_eq]
        rcases hph : s'.phase with ⟨n, hn⟩
        rw [hph] at hmax
        change 1 ≤ n at hmax
        interval_cases n <;> dsimp only <;>
          first
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase1_fst_le _ _) (clockSummand_Phase1_snd_le _ _)
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase2_fst_le _ _) (clockSummand_Phase2_snd_le _ _)
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase3_fst_le _ _) (clockSummand_Phase3_snd_le _ _)
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase4_fst_le _ _) (clockSummand_Phase4_snd_le _ _)
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase5_fst_le _ _) (clockSummand_Phase5_snd_le _ _)
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase6_fst_le _ _) (clockSummand_Phase6_snd_le _ _)
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase7_fst_le _ _) (clockSummand_Phase7_snd_le _ _)
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase8_fst_le _ _) (clockSummand_Phase8_snd_le _ _)
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase9_fst_le _ _) (clockSummand_Phase9_snd_le _ _)
            | exact pair_le_of_components s' t' _ _
                (clockSummand_Phase10_fst_le _ _) (clockSummand_Phase10_snd_le _ _)
      refine le_trans key ?_
      gcongr

/-- The C0 window-leg atom, now UNCONDITIONAL: with `allPhaseClockPairBound`
discharging the formerly-carried `A : AllPhaseClockPairBound`, the slot-0
clock-zero prefix tail follows from the bare regime numerics. -/
theorem phase0ClockZeroPrefixTail_unconditional
    {n t : ℕ}
    (hn : 1 ≤ n)
    (ht : t ≤ n * (L + 1))
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) :
    Slot0HtailAssembly.Phase0ClockZeroPrefixTail (L := L) (K := K) n t :=
  ClockWindowFields.phase0ClockZeroPrefixTail_closed
    (L := L) (K := K) hn ht hlog allPhaseClockPairBound

end TransitionClockPairBound

end ExactMajority
