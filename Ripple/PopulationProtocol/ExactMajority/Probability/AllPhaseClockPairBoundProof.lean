/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

# AllPhaseClockPairBoundProof

Final deterministic interface for `ClockDriftCardWindow.AllPhaseClockPairBound`.

This file records the exact all-phase transition ledger needed by the C0 clock-window
leg and turns it into the landed `AllPhaseClockPairBound`.

The remaining proof obligation is purely deterministic: a case split over
`Transition L K r₁ r₂`.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ClockWindowFields

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace AllPhaseClockPairBoundProof

open Phase0Window
open ClockDriftCardWindow
open Phase0CardAffineTail

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- `E = ofReal(exp 1)` is at least one. -/
theorem one_le_exp1_ennreal :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp 1) := by
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  exact ENNReal.ofReal_le_ofReal
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1))

/-- Every clock counter value is at most the full reset value `50*(L+1)`. -/
theorem counter_val_le_full (a : AgentState L K) :
    a.counter.val ≤ 50 * (L + 1) := by
  have hlt : a.counter.val < 50 * (L + 1) + 1 := a.counter.2
  omega

/-- A clock at any counter has summand at least the full-reset summand. -/
theorem phase0AffineB_le_clockSummand_of_clock
    (a : AgentState L K) (ha : a.role = .clock) :
    phase0AffineB L
      ≤ clockSummand (L := L) (K := K) 1 a := by
  unfold phase0AffineB clockSummand
  rw [if_pos ha]
  simp only [one_mul]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h : (a.counter.val : ℝ) ≤ (50 * (L + 1) : ℕ) := by
    exact_mod_cast counter_val_le_full (L := L) (K := K) a
  linarith

/-- Any clock summand is at most `1`. -/
theorem clockSummand_le_one (a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 a ≤ 1 := by
  unfold clockSummand
  by_cases hrole : a.role = .clock
  · rw [if_pos hrole]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_one_iff.mpr
    have hc : (0 : ℝ) ≤ 1 * (a.counter.val : ℝ) := by positivity
    linarith
  · rw [if_neg hrole]
    exact zero_le'

/-- `phaseInit` never turns a non-clock into a clock. -/
private theorem phaseInit_role_ne_clock
    (p : Fin 11) (a : AgentState L K) (ha : a.role ≠ .clock) :
    (phaseInit L K p a).role ≠ .clock := by
  rcases a with ⟨_, _, _, role, _, _, _, _, _, _, _, _⟩
  fin_cases p <;> cases role <;>
    simp_all [phaseInit, enterPhase10] <;>
    (repeat' split_ifs) <;> simp_all [enterPhase10]

/-- `phaseInit` on a clock never decreases its counter (it resets to `50(L+1)` ≥
the old value, or keeps it). -/
private theorem phaseInit_clock_counter_ge
    (p : Fin 11) (a : AgentState L K) (ha : a.role = .clock) :
    a.counter.val ≤ (phaseInit L K p a).counter.val := by
  have hle : a.counter.val ≤ 50 * (L + 1) := counter_val_le_full (L := L) (K := K) a
  fin_cases p <;>
    simp [phaseInit, enterPhase10, ha, apply_ite (fun s : AgentState L K => s.counter.val),
      ite_self] <;>
    omega

/-- `phaseInit` never increases the clock-counter summand. -/
theorem clockSummand_phaseInit_le_self
    (p : Fin 11) (a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (phaseInit L K p a)
      ≤ clockSummand (L := L) (K := K) 1 a := by
  by_cases ha : a.role = .clock
  · have hout : (phaseInit L K p a).role = .clock :=
      phaseInit_clock_role_eq L K p a ha
    have hctr : a.counter.val ≤ (phaseInit L K p a).counter.val :=
      phaseInit_clock_counter_ge (L := L) (K := K) p a ha
    unfold clockSummand
    rw [if_pos hout, if_pos ha]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hr : (a.counter.val : ℝ) ≤ ((phaseInit L K p a).counter.val : ℝ) := by
      exact_mod_cast hctr
    linarith
  · have hout : (phaseInit L K p a).role ≠ .clock :=
      phaseInit_role_ne_clock (L := L) (K := K) p a ha
    unfold clockSummand
    rw [if_neg hout, if_neg ha]

/-- `advancePhase` preserves the clock-counter summand. -/
theorem clockSummand_advancePhase_eq
    (a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (advancePhase L K a)
      = clockSummand (L := L) (K := K) 1 a := by
  unfold advancePhase clockSummand
  split <;> simp

/-- `advancePhaseWithInit` does not increase the clock-counter summand. -/
theorem clockSummand_advancePhaseWithInit_le_self
    (a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (advancePhaseWithInit L K a)
      ≤ clockSummand (L := L) (K := K) 1 a := by
  unfold advancePhaseWithInit
  calc
    clockSummand (L := L) (K := K) 1
        (phaseInit L K (advancePhase L K a).phase (advancePhase L K a))
        ≤ clockSummand (L := L) (K := K) 1 (advancePhase L K a) :=
          clockSummand_phaseInit_le_self (L := L) (K := K) _ _
    _ = clockSummand (L := L) (K := K) 1 a :=
          clockSummand_advancePhase_eq (L := L) (K := K) a

/-- A nonzero counter decrement scales the summand by exactly `exp 1`. -/
theorem clockSummand_decrement_le_exp_mul
    (a : AgentState L K)
    (hrole : a.role = .clock)
    (hctr : a.counter.val ≠ 0) :
    clockSummand (L := L) (K := K) 1
        ({ a with counter := ⟨a.counter.val - 1, by omega⟩ } : AgentState L K)
      ≤ ENNReal.ofReal (Real.exp 1)
          * clockSummand (L := L) (K := K) 1 a := by
  unfold clockSummand
  rw [if_pos hrole]
  simp only
  rw [if_pos (by simp [hrole])]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  apply le_of_eq
  congr 2
  have h1 : 1 ≤ a.counter.val := Nat.one_le_iff_ne_zero.mpr hctr
  have hcast : ((a.counter.val - 1 : ℕ) : ℝ) = (a.counter.val : ℝ) - 1 := by
    rw [Nat.cast_sub h1]
    norm_num
  rw [hcast]
  ring

/-- `stdCounterSubroutine` maps one agent's clock summand to at most `exp 1` times
its old summand. -/
theorem clockSummand_stdCounterSubroutine_le_exp_mul
    (a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (stdCounterSubroutine L K a)
      ≤ ENNReal.ofReal (Real.exp 1)
          * clockSummand (L := L) (K := K) 1 a := by
  unfold stdCounterSubroutine
  by_cases hzero : a.counter.val = 0
  · rw [dif_pos hzero]
    by_cases hclock : a.role = .clock
    · calc
        clockSummand (L := L) (K := K) 1 (advancePhaseWithInit L K a)
            ≤ clockSummand (L := L) (K := K) 1 a :=
              clockSummand_advancePhaseWithInit_le_self (L := L) (K := K) a
        _ ≤ ENNReal.ofReal (Real.exp 1)
              * clockSummand (L := L) (K := K) 1 a := by
              exact le_mul_of_one_le_left zero_le' one_le_exp1_ennreal
    · have hsrc : clockSummand (L := L) (K := K) 1 a = 0 := by
        unfold clockSummand
        rw [if_neg hclock]
      have hout : clockSummand (L := L) (K := K) 1 (advancePhaseWithInit L K a) = 0 :=
        le_antisymm
          (hsrc ▸ clockSummand_advancePhaseWithInit_le_self (L := L) (K := K) a)
          zero_le'
      rw [hsrc, hout, mul_zero]
  · rw [dif_neg hzero]
    by_cases hclock : a.role = .clock
    · exact clockSummand_decrement_le_exp_mul
        (L := L) (K := K) a hclock hzero
    · unfold clockSummand
      rw [if_neg hclock]
      simp [hclock]

/-- `clockCounterStep` is bounded by the same one-agent `exp 1` multiplier. -/
theorem clockSummand_clockCounterStep_le_exp_mul
    (a : AgentState L K) :
    clockSummand (L := L) (K := K) 1 (clockCounterStep L K a)
      ≤ ENNReal.ofReal (Real.exp 1)
          * clockSummand (L := L) (K := K) 1 a := by
  unfold clockCounterStep
  by_cases hclock : a.role = .clock
  · rw [if_pos hclock]
    exact clockSummand_stdCounterSubroutine_le_exp_mul (L := L) (K := K) a
  · rw [if_neg hclock]
    exact le_mul_of_one_le_left zero_le' one_le_exp1_ennreal

/--
The exact deterministic transition ledger still to paste/prove.

This is deliberately factored out: it is the pure 11-phase case split.  It should be
proved by combining the helper lemmas above with per-phase facts:

* Phase 0: existing clocks are decremented/carried, and Rule 4 creates one fresh
  full-counter clock plus one reserve.
* Phases 1,5,6,7,8: non-clock work preserves role/counter, then clocks run
  `stdCounterSubroutine`.
* Phases 2 and 9: opinion updates preserve role/counter; any advancing branch goes
  through `advancePhaseWithInit`.
* Phase 3: clock-minute logic either preserves the clock counter or runs
  `stdCounterSubroutine`; main logic does not create clocks.
* Phase 4: `advancePhase` preserves counter/role.
* Phase 10: only output/full changes, so clock summands are preserved.
-/
structure TransitionClockLedger : Prop where
  hpair :
    ∀ r₁ r₂ : AgentState L K,
      clockSummand (L := L) (K := K) 1 (Transition L K r₁ r₂).1
        + clockSummand (L := L) (K := K) 1 (Transition L K r₁ r₂).2
      ≤ ENNReal.ofReal (Real.exp 1)
          * (clockSummand (L := L) (K := K) 1 r₁
              + clockSummand (L := L) (K := K) 1 r₂)
        + phase0AffineB L

/-- Convert the deterministic transition ledger into the landed field value. -/
def allPhaseClockPairBound_of_transitionLedger
    (H : TransitionClockLedger (L := L) (K := K)) :
    AllPhaseClockPairBound (L := L) (K := K) where
  hpair := H.hpair

#print axioms one_le_exp1_ennreal
#print axioms counter_val_le_full
#print axioms phase0AffineB_le_clockSummand_of_clock
#print axioms clockSummand_le_one
#print axioms clockSummand_phaseInit_le_self
#print axioms clockSummand_advancePhase_eq
#print axioms clockSummand_advancePhaseWithInit_le_self
#print axioms clockSummand_decrement_le_exp_mul
#print axioms clockSummand_stdCounterSubroutine_le_exp_mul
#print axioms clockSummand_clockCounterStep_le_exp_mul
#print axioms allPhaseClockPairBound_of_transitionLedger

end AllPhaseClockPairBoundProof

end Ripple.PopulationProtocol.ExactMajority
