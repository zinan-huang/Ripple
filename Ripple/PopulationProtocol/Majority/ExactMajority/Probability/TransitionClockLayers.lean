/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `TransitionClockLayers` — Layer-1/Layer-2 clock-summand facts for the pair bound.

`Transition` = `phaseEpidemicUpdate` then per-phase dispatch then `finishPhase10Entry`.
This file proves the two OUTER layers are clock-summand-tame, reducing the pair
bound `AllPhaseClockPairBound` to the per-phase dispatch bounds:

* LAYER 1 — `finishPhase10Entry`/`enterPhase10`/`phase10EpidemicEntry` preserve the
  clock-summand (they only touch `phase`/`output`, never `role`/`counter`).
* LAYER 2 — `phaseEpidemicUpdate` is NON-INCREASING on the clock-summand per agent
  (it sets `phase := max` — clock-summand-invariant — then folds `phaseInit`, each
  step non-increasing via `clockSummand_phaseInit_le_self`).

All axiom-clean.  Builds on the landed per-agent ledger `AllPhaseClockPairBoundProof`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AllPhaseClockPairBoundProof

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace TransitionClockLayers

open Phase0Window
open AllPhaseClockPairBoundProof

variable {L K : ℕ}

/-! ## Layer 1 — `phase`/`output`-only updates preserve the clock-summand. -/

/-- Setting `phase` leaves the clock-summand unchanged (reads only `role`/`counter`). -/
@[simp] theorem clockSummand_phase_set (a : AgentState L K) (p : Fin 11) :
    clockSummand (L := L) (K := K) 1 ({ a with phase := p } : AgentState L K)
      = clockSummand (L := L) (K := K) 1 a := rfl

/-- `enterPhase10` preserves the clock-summand. -/
@[simp] theorem clockSummand_enterPhase10_eq (a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (enterPhase10 L K a)
      = clockSummand (L := L) (K := K) 1 a := by
  unfold clockSummand
  rw [enterPhase10_role, enterPhase10_counter]

/-- `phase10EpidemicEntry` preserves the clock-summand. -/
@[simp] theorem clockSummand_phase10EpidemicEntry_eq (b a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (phase10EpidemicEntry L K b a)
      = clockSummand (L := L) (K := K) 1 a := by
  unfold clockSummand
  rw [phase10EpidemicEntry_role, phase10EpidemicEntry_counter]

/-- `finishPhase10Entry` preserves the clock-summand (it preserves `role`+`counter`). -/
@[simp] theorem clockSummand_finishPhase10Entry_eq (b a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (finishPhase10Entry L K b a)
      = clockSummand (L := L) (K := K) 1 a := by
  unfold clockSummand
  rw [finishPhase10Entry_role, finishPhase10Entry_counter]

/-! ## Layer 2 — `runInitsBetween`/`phaseEpidemicUpdate` are non-increasing. -/

/-- `runInitsBetween` (a `phaseInit` fold) never increases the clock-summand. -/
theorem clockSummand_runInitsBetween_le
    (oldP newP : ℕ) (a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (runInitsBetween L K oldP newP a)
      ≤ clockSummand (L := L) (K := K) 1 a := by
  unfold runInitsBetween
  set lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP) with hlst
  have h_ind : ∀ (a' : AgentState L K),
      clockSummand (L := L) (K := K) 1
          (lst.foldl (fun (acc : AgentState L K) (k : ℕ) =>
            if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a')
        ≤ clockSummand (L := L) (K := K) 1 a' := by
    clear hlst
    induction lst with
    | nil => exact fun a' => le_refl _
    | cons k l IH =>
        intro a'
        by_cases hk : k < 11
        · have hstep :
              clockSummand (L := L) (K := K) 1 (phaseInit L K ⟨k, hk⟩ a')
                ≤ clockSummand (L := L) (K := K) 1 a' :=
            clockSummand_phaseInit_le_self (L := L) (K := K) ⟨k, hk⟩ a'
          have hrest := IH (phaseInit L K ⟨k, hk⟩ a')
          simp only [List.foldl_cons, dif_pos hk]
          exact le_trans hrest hstep
        · have hrest := IH a'
          simp only [List.foldl_cons, dif_neg hk]
          exact hrest
  exact h_ind a

/-- `phaseEpidemicUpdate` never increases the left agent's clock-summand. -/
theorem clockSummand_phaseEpidemicUpdate_le_left (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (phaseEpidemicUpdate L K s t).1
      ≤ clockSummand (L := L) (K := K) 1 s := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  have hrun :
      clockSummand (L := L) (K := K) 1
          (runInitsBetween L K s.phase.val p.val ({ s with phase := p } : AgentState L K))
        ≤ clockSummand (L := L) (K := K) 1 s := by
    refine le_trans (clockSummand_runInitsBetween_le (L := L) (K := K) _ _ _) ?_
    rw [clockSummand_phase_set]
  by_cases hcond :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L K s.phase.val p.val ({ s with phase := p } : AgentState L K)).phase.val = 10 ∨
          (runInitsBetween L K t.phase.val p.val ({ t with phase := p } : AgentState L K)).phase.val = 10)
  · rw [if_pos hcond]
    simpa using hrun
  · rw [if_neg hcond]
    simpa using hrun

/-- `phaseEpidemicUpdate` never increases the right agent's clock-summand. -/
theorem clockSummand_phaseEpidemicUpdate_le_right (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (phaseEpidemicUpdate L K s t).2
      ≤ clockSummand (L := L) (K := K) 1 t := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  have hrun :
      clockSummand (L := L) (K := K) 1
          (runInitsBetween L K t.phase.val p.val ({ t with phase := p } : AgentState L K))
        ≤ clockSummand (L := L) (K := K) 1 t := by
    refine le_trans (clockSummand_runInitsBetween_le (L := L) (K := K) _ _ _) ?_
    rw [clockSummand_phase_set]
  by_cases hcond :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L K s.phase.val p.val ({ s with phase := p } : AgentState L K)).phase.val = 10 ∨
          (runInitsBetween L K t.phase.val p.val ({ t with phase := p } : AgentState L K)).phase.val = 10)
  · rw [if_pos hcond]
    simpa using hrun
  · rw [if_neg hcond]
    simpa using hrun

end TransitionClockLayers

end ExactMajority
