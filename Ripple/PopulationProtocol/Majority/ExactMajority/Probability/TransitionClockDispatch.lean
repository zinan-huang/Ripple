/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `TransitionClockDispatch` — per-phase clock-summand dispatch bounds (Layer 3, part).

For the window-leg `AllPhaseClockPairBound`, after Layers 1/2 reduce to the per-phase
`PhaseNTransition` dispatch, this file proves the COMPONENTWISE bound
`clockSummand (PhaseNTransition s t).1 ≤ exp 1 · clockSummand s` (and `.2`/`t`) for the
phases that do not create fresh clocks (every output clock is a `≤ exp 1`-scaled
transform of the matching input clock).  These compose to the pair bound via
`pair_le_of_components`.

Covered here (verified): Phases 1, 2, 4, 9, 10.  The remaining phases (0 — fresh
clock via Rule 4, handled by the landed phase-0 pair bound; 3, 5, 6, 7, 8) are the
genuinely-clock-active dispatch cases.

`clockSummand` reads only `role`+`counter`, so any record update of other fields is
summand-invariant (by `rfl`); `advancePhase`/`clockCounterStep`/`advancePhaseWithInit`
scale it by `≤ exp 1` via the landed per-agent ledger.  All axiom-clean.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TransitionClockLayers

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace TransitionClockDispatch

open Phase0Window AllPhaseClockPairBoundProof TransitionClockLayers
open Phase0PrefixTailDischarge ClockDriftCardWindow

variable {L K : ℕ}

/-- The exp-1 multiplier. -/
noncomputable abbrev E : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1)

/-- A clock summand is `≤ exp 1` times itself. -/
theorem clockSummand_le_E_self (a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 a ≤ E * clockSummand (L := L) (K := K) 1 a :=
  le_mul_of_one_le_left zero_le' one_le_exp1_ennreal

/-- Componentwise `≤ exp 1` bounds compose to the pair bound (with the `+ phase0AffineB`
slack). -/
theorem pair_le_of_components (s t o₁ o₂ : AgentState L K)
    (h₁ : clockSummand (L := L) (K := K) 1 o₁ ≤ E * clockSummand (L := L) (K := K) 1 s)
    (h₂ : clockSummand (L := L) (K := K) 1 o₂ ≤ E * clockSummand (L := L) (K := K) 1 t) :
    clockSummand (L := L) (K := K) 1 o₁ + clockSummand (L := L) (K := K) 1 o₂
      ≤ E * (clockSummand (L := L) (K := K) 1 s + clockSummand (L := L) (K := K) 1 t)
        + phase0AffineB L := by
  rw [mul_add]
  exact le_add_right (add_le_add h₁ h₂)

/-! ## Phase 4 — `advancePhase` (clock-summand invariant). -/

theorem clockSummand_Phase4_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase4Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s := by
  have h : clockSummand (L := L) (K := K) 1 (Phase4Transition L K s t).1
      = clockSummand (L := L) (K := K) 1 s := by
    unfold Phase4Transition
    simp only [apply_ite
      (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.1),
      apply_ite
      (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.2),
      clockSummand_advancePhase_eq, ite_self]
  rw [h]; exact clockSummand_le_E_self s

theorem clockSummand_Phase4_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase4Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t := by
  have h : clockSummand (L := L) (K := K) 1 (Phase4Transition L K s t).2
      = clockSummand (L := L) (K := K) 1 t := by
    unfold Phase4Transition
    simp only [apply_ite
      (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.1),
      apply_ite
      (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.2),
      clockSummand_advancePhase_eq, ite_self]
  rw [h]; exact clockSummand_le_E_self t

/-! ## Phase 1 — `clockCounterStep` after a `smallBias`-only update. -/

theorem clockSummand_Phase1_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase1Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s := by
  unfold Phase1Transition
  refine le_trans
    (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split <;> exact le_of_eq rfl

theorem clockSummand_Phase1_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase1Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t := by
  unfold Phase1Transition
  refine le_trans
    (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split <;> exact le_of_eq rfl

/-! ## Phase 10 — only `output`/`full` change (clock-summand invariant). -/

theorem clockSummand_Phase10_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase10Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s := by
  have hrole : (Phase10Transition L K s t).1.role = s.role := by
    simp only [Phase10Transition]; split_ifs <;> rfl
  have hctr : (Phase10Transition L K s t).1.counter = s.counter := by
    simp only [Phase10Transition]; split_ifs <;> rfl
  have h : clockSummand (L := L) (K := K) 1 (Phase10Transition L K s t).1
      = clockSummand (L := L) (K := K) 1 s := by
    unfold clockSummand; rw [hrole, hctr]
  rw [h]; exact clockSummand_le_E_self s

theorem clockSummand_Phase10_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase10Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t := by
  have hrole : (Phase10Transition L K s t).2.role = t.role := by
    simp only [Phase10Transition]; split_ifs <;> rfl
  have hctr : (Phase10Transition L K s t).2.counter = t.counter := by
    simp only [Phase10Transition]; split_ifs <;> rfl
  have h : clockSummand (L := L) (K := K) 1 (Phase10Transition L K s t).2
      = clockSummand (L := L) (K := K) 1 t := by
    unfold clockSummand; rw [hrole, hctr]
  rw [h]; exact clockSummand_le_E_self t

/-! ## Phase 2 / Phase 9 — `advancePhaseWithInit` or `output`-only (≤ exp 1). -/

theorem clockSummand_Phase2_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase2Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s := by
  unfold Phase2Transition
  refine le_trans ?_ (clockSummand_le_E_self s)
  simp only [apply_ite (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.1)]
  split_ifs <;>
    first
    | exact clockSummand_advancePhaseWithInit_le_self (L := L) (K := K) _
    | exact le_of_eq rfl

theorem clockSummand_Phase2_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase2Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t := by
  unfold Phase2Transition
  refine le_trans ?_ (clockSummand_le_E_self t)
  simp only [apply_ite (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.2)]
  split_ifs <;>
    first
    | exact clockSummand_advancePhaseWithInit_le_self (L := L) (K := K) _
    | exact le_of_eq rfl

theorem clockSummand_Phase9_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase9Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s :=
  clockSummand_Phase2_fst_le (L := L) (K := K) s t

theorem clockSummand_Phase9_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase9Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t :=
  clockSummand_Phase2_snd_le (L := L) (K := K) s t

/-! ## Phases 7, 8 — `cancelSplit`/`absorbConsume` (bias-only) then `clockCounterStep`. -/

/-- `cancelSplit` changes only `bias`, so it preserves the clock-summand. -/
private theorem clockSummand_cancelSplit_fst_eq (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (cancelSplit L K s t).1
      = clockSummand (L := L) (K := K) 1 s := by
  have hc : (cancelSplit L K s t).1.counter = s.counter := by
    unfold cancelSplit; split <;> (try split_ifs) <;> rfl
  unfold clockSummand; rw [cancelSplit_role_fst, hc]

private theorem clockSummand_cancelSplit_snd_eq (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (cancelSplit L K s t).2
      = clockSummand (L := L) (K := K) 1 t := by
  have hc : (cancelSplit L K s t).2.counter = t.counter := by
    unfold cancelSplit; split <;> (try split_ifs) <;> rfl
  unfold clockSummand; rw [cancelSplit_role_snd, hc]

/-- `absorbConsume` changes only `bias`/`full`, so it preserves the clock-summand. -/
private theorem clockSummand_absorbConsume_fst_eq (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (absorbConsume L K s t).1
      = clockSummand (L := L) (K := K) 1 s := by
  have hc : (absorbConsume L K s t).1.counter = s.counter := by
    unfold absorbConsume; split <;> (try split_ifs) <;> rfl
  unfold clockSummand; rw [absorbConsume_role_fst, hc]

private theorem clockSummand_absorbConsume_snd_eq (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (absorbConsume L K s t).2
      = clockSummand (L := L) (K := K) 1 t := by
  have hc : (absorbConsume L K s t).2.counter = t.counter := by
    unfold absorbConsume; split <;> (try split_ifs) <;> rfl
  unfold clockSummand; rw [absorbConsume_role_snd, hc]

theorem clockSummand_Phase7_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase7Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s := by
  unfold Phase7Transition
  refine le_trans (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split <;> simp [clockSummand_cancelSplit_fst_eq]

theorem clockSummand_Phase7_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase7Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t := by
  unfold Phase7Transition
  refine le_trans (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split <;> simp [clockSummand_cancelSplit_snd_eq]

theorem clockSummand_Phase8_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase8Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s := by
  unfold Phase8Transition
  refine le_trans (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split <;> simp [clockSummand_absorbConsume_fst_eq]

theorem clockSummand_Phase8_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase8Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t := by
  unfold Phase8Transition
  refine le_trans (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split <;> simp [clockSummand_absorbConsume_snd_eq]

/-! ## Phase 5 — `doSample` (hour-only) then `clockCounterStep`. -/

theorem clockSummand_Phase5_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase5Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s := by
  unfold Phase5Transition
  refine le_trans (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split_ifs <;>
    simp only [clockSummand,
      apply_ite (fun p : AgentState L K × AgentState L K => p.1),
      apply_ite (fun p : AgentState L K × AgentState L K => p.2)] <;>
    split_ifs <;> rfl

theorem clockSummand_Phase5_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase5Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t := by
  unfold Phase5Transition
  refine le_trans (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split_ifs <;>
    simp only [clockSummand,
      apply_ite (fun p : AgentState L K × AgentState L K => p.1),
      apply_ite (fun p : AgentState L K × AgentState L K => p.2)] <;>
    split_ifs <;> rfl

/-! ## Phase 6 — `doSplit` (reserve→main on `.1`, bias-only on `.2`) then `clockCounterStep`. -/

/-- `doSplit`'s first output is `Main` or the unchanged first input; on a non-clock
first input it is never a clock, so its clock-summand is `0`. -/
private theorem clockSummand_doSplit_fst_eq_zero
    (r m : AgentState L K) (hr : r.role ≠ .clock) :
    clockSummand (L := L) (K := K) 1 (doSplit L K r m).1 = 0 := by
  unfold clockSummand
  rw [if_neg]
  unfold doSplit
  split
  · split_ifs <;> simp_all <;> exact fun h => by rw [h] at hr; exact hr rfl
  · simpa using hr

/-- `doSplit` changes only `bias` on its second output, preserving the clock-summand. -/
private theorem clockSummand_doSplit_snd_eq (r m : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (doSplit L K r m).2
      = clockSummand (L := L) (K := K) 1 m := by
  have hc : (doSplit L K r m).2.counter = m.counter := by
    unfold doSplit; split <;> (try split_ifs) <;> rfl
  unfold clockSummand; rw [doSplit_role_snd, hc]

theorem clockSummand_Phase6_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase6Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s := by
  unfold Phase6Transition
  refine le_trans (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split_ifs with g1 g2
  · obtain ⟨hres, _⟩ := g1
    rw [clockSummand_doSplit_fst_eq_zero _ _ (by rw [hres]; decide)]
    exact zero_le'
  · rw [clockSummand_doSplit_snd_eq]
  · exact le_of_eq rfl

theorem clockSummand_Phase6_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase6Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t := by
  unfold Phase6Transition
  refine le_trans (clockSummand_clockCounterStep_le_exp_mul (L := L) (K := K) _) ?_
  gcongr
  split_ifs with g1 g2
  · rw [clockSummand_doSplit_snd_eq]
  · obtain ⟨hres, _⟩ := g2
    rw [clockSummand_doSplit_fst_eq_zero _ _ (by rw [hres]; decide)]
    exact zero_le'
  · exact le_of_eq rfl

/-! ## Phase 3 — clock-minute / hour-drag (multi-layer; `phase3CancelSplit` bias/hour-only). -/

/-- `phase3CancelSplit` changes only `bias`/`hour`, preserving the clock-summand. -/
private theorem clockSummand_phase3CancelSplit_fst_eq (s2 t2 : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (phase3CancelSplit L K s2 t2).1
      = clockSummand (L := L) (K := K) 1 s2 := by
  have hr : (phase3CancelSplit L K s2 t2).1.role = s2.role := by
    unfold phase3CancelSplit; split <;> (try split_ifs) <;> rfl
  have hc : (phase3CancelSplit L K s2 t2).1.counter = s2.counter := by
    unfold phase3CancelSplit; split <;> (try split_ifs) <;> rfl
  unfold clockSummand; rw [hr, hc]

private theorem clockSummand_phase3CancelSplit_snd_eq (s2 t2 : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (phase3CancelSplit L K s2 t2).2
      = clockSummand (L := L) (K := K) 1 t2 := by
  have hr : (phase3CancelSplit L K s2 t2).2.role = t2.role := by
    unfold phase3CancelSplit; split <;> (try split_ifs) <;> rfl
  have hc : (phase3CancelSplit L K s2 t2).2.counter = t2.counter := by
    unfold phase3CancelSplit; split <;> (try split_ifs) <;> rfl
  unfold clockSummand; rw [hr, hc]

set_option maxHeartbeats 4000000 in
theorem clockSummand_Phase3_fst_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase3Transition L K s t).1
      ≤ E * clockSummand (L := L) (K := K) 1 s := by
  simp only [Phase3Transition]
  split_ifs <;>
    simp only [apply_ite (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.1),
      apply_ite (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.2),
      clockSummand_phase3CancelSplit_fst_eq, clockSummand_phase3CancelSplit_snd_eq, ite_self] <;>
    first
      | exact clockSummand_le_E_self s
      | (refine le_trans (le_of_eq (by unfold clockSummand; rfl))
          (clockSummand_stdCounterSubroutine_le_exp_mul (L := L) (K := K) s))

set_option maxHeartbeats 4000000 in
theorem clockSummand_Phase3_snd_le (s t : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (Phase3Transition L K s t).2
      ≤ E * clockSummand (L := L) (K := K) 1 t := by
  simp only [Phase3Transition]
  split_ifs <;>
    simp only [apply_ite (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.1),
      apply_ite (fun p : AgentState L K × AgentState L K => clockSummand (L := L) (K := K) 1 p.2),
      clockSummand_phase3CancelSplit_fst_eq, clockSummand_phase3CancelSplit_snd_eq, ite_self] <;>
    first
      | exact clockSummand_le_E_self t
      | (refine le_trans (le_of_eq (by unfold clockSummand; rfl))
          (clockSummand_stdCounterSubroutine_le_exp_mul (L := L) (K := K) t))

end TransitionClockDispatch

end ExactMajority
