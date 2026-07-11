/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue D-lynch-3 — discharging `hmono_mix` (deterministic `rBeyond (T+1)` monotonicity)

`ClockRealMixed.rSeedPot_contracts_mixed` carries a structural hypothesis

  `hmono_mix : ∀ c c', Q_mix n mC T c →
       c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
       rBeyond (T+1) c ≤ rBeyond (T+1) c'`

(the count of clock-role agents at minute `≥ T+1` never drops in one step).  It is
DETERMINISTIC and TRUE — and this file DISCHARGES it from the transition lemmas, it
does NOT re-assume it.

## Why it is true (the genuine proof)
`rBeyond (T+1) c = countP (clock ∧ minute ≥ T+1) c`.  A one-step transition removes
the ordered pair `(r₁, r₂)` and inserts the two outputs `(δ₁, δ₂)`, leaving all
other agents fixed.  The count does not drop because EVERY removed agent that was
counted (clock ∧ minute ≥ T+1) maps to a post-state that is STILL counted:

* **Clock role is permanent AND a phase-3 clock's minute never drops.**  Both are
  bundled into `transition_{left,right}_clock_minute_ge` (Part 2): when one agent is
  a clock at phase exactly 3, its corresponding `Transition` output is a clock with
  `minute ≥` its input minute, for an ARBITRARY partner.  Role permanence is read off
  the PUBLIC per-phase `Phase k Transition_…_preserves_clock_role` lemmas and the
  PUBLIC `phaseEpidemicUpdate_…_preserves_clock_role` (used via the Part-1 per-phase
  helpers).  The `private` `DeterministicChain` copies and
  `Phase0Transition_preserves_clock_role_…` are NOT needed (the dispatch on a
  phase-`≥3` clock never reaches Phase 0); no existing file is edited or un-privated.

  Under `Q_mix`, every clock-role agent sits at phase EXACTLY 3.  The `minute` field
  is written ONLY by `phaseInit` at
  phase-3 entry (`= 0`, the sole RESET) and by the Phase-3 drip/sync (`+1` / `max`,
  upward).  A clock already at phase 3 is dragged UP by the epidemic
  (`runInitsBetween` from `oldP = 3`, which inits only phases `≥ 4 ≠ 3`, so no
  reset — `runInitsBetween_clock_minute`), then the dispatched per-phase rule on a
  phase-`≥3` clock reduces to `stdCounterSubroutine`/identity/opinion-edits
  (minute kept) or the Phase-3 drip (minute up), and `finishPhase10Entry` keeps
  `minute`.  Hence the clock's output minute is `≥` its input minute — for an
  ARBITRARY partner (the partner is never constrained).

This is the only change vs the all-clocks `rBeyond_stepOrSelf_ge`
(`ClockRealKernel`): there the justification was `AllClockGE3` (every agent a
clock); here it is clock-role permanence + minute non-decrease for a single
phase-3 clock with arbitrary partner.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockMonoDischarge

open ClockRealKernel ClockRealMixed

variable {L K : ℕ}

/-! ## Part 1 — minute non-decrease for a phase-3 clock with ARBITRARY partner.

The decisive new content vs the all-clocks file: when ONE of the two agents is a
clock at phase exactly 3, its corresponding `Transition` output has `minute ≥` its
input minute, with NO constraint on the partner.  Every minute-touching operation
on a phase-`≥3` clock is `minute`-non-decreasing:
* the epidemic drag (`runInitsBetween` from `oldP = 3`, then the
  `phase10EpidemicEntry` wrapper) keeps the clock's `minute`;
* the per-phase dispatch on a phase-`≥3` clock is `stdCounterSubroutine`/identity
  (Phases 4–8, 10) / opinion-edits (Phase 9) / drip-or-sync (Phase 3), each
  `minute`-non-decreasing;
* `finishPhase10Entry` keeps `minute`. -/

/-- The epidemic stage keeps a phase-3 clock's role and `minute`, raising its
phase to `≥ 3`.  ARBITRARY partner.  (Left component.) -/
private theorem epidemic_left_clock_phase3 (s t : AgentState L K)
    (hs_clock : s.role = .clock) (hs_phase : s.phase.val = 3) :
    (phaseEpidemicUpdate L K s t).1.role = .clock ∧
      (phaseEpidemicUpdate L K s t).1.minute = s.minute ∧
      3 ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
  refine ⟨phaseEpidemicUpdate_first_preserves_clock_role (L := L) (K := K) s t hs_clock,
    ?_, ?_⟩
  · -- the epidemic first output's minute equals s.minute.
    unfold phaseEpidemicUpdate
    set p := max s.phase t.phase with hp
    have hp3 : 3 ≤ p.val := by
      have : s.phase.val ≤ p.val := by
        exact_mod_cast (le_max_left s.phase t.phase : s.phase ≤ max s.phase t.phase)
      omega
    -- runInitsBetween from oldP = s.phase.val = 3 keeps role + minute.
    have hbase : ({ s with phase := p } : AgentState L K).minute = s.minute := rfl
    have hbase_clock : ({ s with phase := p } : AgentState L K).role = .clock := hs_clock
    have hrun := runInitsBetween_clock_minute (L := L) (K := K) s.phase.val p.val
      (by omega) ({ s with phase := p }) hbase_clock
    by_cases hbr : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L K s.phase.val p.val { s with phase := p }).phase.val = 10 ∨
         (runInitsBetween L K t.phase.val p.val { t with phase := p }).phase.val = 10)
    · rw [if_pos hbr]
      change (phase10EpidemicEntry L K s
        (runInitsBetween L K s.phase.val p.val { s with phase := p })).minute = s.minute
      rw [phase10EpidemicEntry_minute, hrun.2, hbase]
    · rw [if_neg hbr]
      change (runInitsBetween L K s.phase.val p.val { s with phase := p }).minute = s.minute
      rw [hrun.2, hbase]
  · have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    have : s.phase.val ≤ max s.phase.val t.phase.val := le_max_left _ _
    omega

/-- Right-component version of `epidemic_left_clock_phase3`. -/
private theorem epidemic_right_clock_phase3 (s t : AgentState L K)
    (ht_clock : t.role = .clock) (ht_phase : t.phase.val = 3) :
    (phaseEpidemicUpdate L K s t).2.role = .clock ∧
      (phaseEpidemicUpdate L K s t).2.minute = t.minute ∧
      3 ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  refine ⟨phaseEpidemicUpdate_second_preserves_clock_role (L := L) (K := K) s t ht_clock,
    ?_, ?_⟩
  · unfold phaseEpidemicUpdate
    set p := max s.phase t.phase with hp
    have hp3 : 3 ≤ p.val := by
      have : t.phase.val ≤ p.val := by
        exact_mod_cast (le_max_right s.phase t.phase : t.phase ≤ max s.phase t.phase)
      omega
    have hbase : ({ t with phase := p } : AgentState L K).minute = t.minute := rfl
    have hbase_clock : ({ t with phase := p } : AgentState L K).role = .clock := ht_clock
    have hrun := runInitsBetween_clock_minute (L := L) (K := K) t.phase.val p.val
      (by omega) ({ t with phase := p }) hbase_clock
    by_cases hbr : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L K s.phase.val p.val { s with phase := p }).phase.val = 10 ∨
         (runInitsBetween L K t.phase.val p.val { t with phase := p }).phase.val = 10)
    · rw [if_pos hbr]
      change (phase10EpidemicEntry L K t
        (runInitsBetween L K t.phase.val p.val { t with phase := p })).minute = t.minute
      rw [phase10EpidemicEntry_minute, hrun.2, hbase]
    · rw [if_neg hbr]
      change (runInitsBetween L K t.phase.val p.val { t with phase := p }).minute = t.minute
      rw [hrun.2, hbase]
  · have hge := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
    have : t.phase.val ≤ max s.phase.val t.phase.val := le_max_right _ _
    omega

/-! ### Per-phase LEFT minute non-decrease (s a clock at phase `≥ 3`, t arbitrary).

For a clock first agent at phase `≥ 3`, each dispatched per-phase rule's FIRST
output is `minute`-non-decreasing; the partner `t` is unconstrained because the
first output never reads `t.minute` (the only `minute` writes are in Phase 3
drip/sync, which only RAISE, and `stdCounterSubroutine`/`advancePhase`, which keep
`minute`). -/

/-- Phase 4 left: `advancePhase s` keeps `minute`. -/
private theorem phase4_left_min (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase4Transition L K s t).1.role = .clock ∧
      s.minute.val ≤ (Phase4Transition L K s t).1.minute.val := by
  unfold Phase4Transition
  dsimp only
  have hadv_role : (advancePhase L K s).role = .clock := by
    unfold advancePhase; split_ifs <;> simp [hs]
  have hadv_min : (advancePhase L K s).minute = s.minute := by
    unfold advancePhase; split_ifs <;> rfl
  split_ifs
  · exact ⟨hadv_role, by rw [hadv_min]⟩
  · exact ⟨hs, le_refl _⟩

/-- Phase 4 right: `advancePhase t` keeps `minute`. -/
private theorem phase4_right_min (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase4Transition L K s t).2.role = .clock ∧
      t.minute.val ≤ (Phase4Transition L K s t).2.minute.val := by
  unfold Phase4Transition
  dsimp only
  have hadv_role : (advancePhase L K t).role = .clock := by
    unfold advancePhase; split_ifs <;> simp [ht]
  have hadv_min : (advancePhase L K t).minute = t.minute := by
    unfold advancePhase; split_ifs <;> rfl
  split_ifs
  · exact ⟨hadv_role, by rw [hadv_min]⟩
  · exact ⟨ht, le_refl _⟩

/-- Phases 5–8 left: a clock first agent reduces to `stdCounterSubroutine s`,
which keeps role and `minute` (phase `≥ 3`).  The `s1`-defining branches require
`s.role ∈ {reserve, main}`, which fail for a clock, so `s1 = s`. -/
private theorem phase5_left_min (s t : AgentState L K) (hs : s.role = .clock)
    (hps : 3 ≤ s.phase.val) :
    (Phase5Transition L K s t).1.role = .clock ∧
      s.minute.val ≤ (Phase5Transition L K s t).1.minute.val := by
  have hc := stdCounterSubroutine_clock_minute (L := L) (K := K) s hs hps
  unfold Phase5Transition
  simp only [hs, reduceCtorEq, false_and, and_false, if_false, if_true]
  exact ⟨hc.1, by rw [hc.2]⟩

private theorem phase6_left_min (s t : AgentState L K) (hs : s.role = .clock)
    (hps : 3 ≤ s.phase.val) :
    (Phase6Transition L K s t).1.role = .clock ∧
      s.minute.val ≤ (Phase6Transition L K s t).1.minute.val := by
  have hc := stdCounterSubroutine_clock_minute (L := L) (K := K) s hs hps
  unfold Phase6Transition
  simp only [hs, reduceCtorEq, false_and, and_false, if_false, if_true]
  exact ⟨hc.1, by rw [hc.2]⟩

private theorem phase7_left_min (s t : AgentState L K) (hs : s.role = .clock)
    (hps : 3 ≤ s.phase.val) :
    (Phase7Transition L K s t).1.role = .clock ∧
      s.minute.val ≤ (Phase7Transition L K s t).1.minute.val := by
  have hc := stdCounterSubroutine_clock_minute (L := L) (K := K) s hs hps
  unfold Phase7Transition
  simp only [hs, reduceCtorEq, false_and, if_false, if_true]
  exact ⟨hc.1, by rw [hc.2]⟩

private theorem phase8_left_min (s t : AgentState L K) (hs : s.role = .clock)
    (hps : 3 ≤ s.phase.val) :
    (Phase8Transition L K s t).1.role = .clock ∧
      s.minute.val ≤ (Phase8Transition L K s t).1.minute.val := by
  have hc := stdCounterSubroutine_clock_minute (L := L) (K := K) s hs hps
  unfold Phase8Transition
  simp only [hs, reduceCtorEq, false_and, if_false, if_true]
  exact ⟨hc.1, by rw [hc.2]⟩

/-- Phases 5–8 right: a clock second agent reduces to `stdCounterSubroutine t`. -/
private theorem phase5_right_min (s t : AgentState L K) (ht : t.role = .clock)
    (hpt : 3 ≤ t.phase.val) :
    (Phase5Transition L K s t).2.role = .clock ∧
      t.minute.val ≤ (Phase5Transition L K s t).2.minute.val := by
  have hc := stdCounterSubroutine_clock_minute (L := L) (K := K) t ht hpt
  unfold Phase5Transition
  simp only [ht, reduceCtorEq, false_and, and_false, if_false, if_true]
  exact ⟨hc.1, by rw [hc.2]⟩

private theorem phase6_right_min (s t : AgentState L K) (ht : t.role = .clock)
    (hpt : 3 ≤ t.phase.val) :
    (Phase6Transition L K s t).2.role = .clock ∧
      t.minute.val ≤ (Phase6Transition L K s t).2.minute.val := by
  have hc := stdCounterSubroutine_clock_minute (L := L) (K := K) t ht hpt
  unfold Phase6Transition
  simp only [ht, reduceCtorEq, false_and, and_false, if_false, if_true]
  exact ⟨hc.1, by rw [hc.2]⟩

private theorem phase7_right_min (s t : AgentState L K) (ht : t.role = .clock)
    (hpt : 3 ≤ t.phase.val) :
    (Phase7Transition L K s t).2.role = .clock ∧
      t.minute.val ≤ (Phase7Transition L K s t).2.minute.val := by
  have hc := stdCounterSubroutine_clock_minute (L := L) (K := K) t ht hpt
  unfold Phase7Transition
  simp only [ht, reduceCtorEq, and_false, if_false, if_true]
  exact ⟨hc.1, by rw [hc.2]⟩

private theorem phase8_right_min (s t : AgentState L K) (ht : t.role = .clock)
    (hpt : 3 ≤ t.phase.val) :
    (Phase8Transition L K s t).2.role = .clock ∧
      t.minute.val ≤ (Phase8Transition L K s t).2.minute.val := by
  have hc := stdCounterSubroutine_clock_minute (L := L) (K := K) t ht hpt
  unfold Phase8Transition
  simp only [ht, reduceCtorEq, and_false, if_false, if_true]
  exact ⟨hc.1, by rw [hc.2]⟩

/-! ### Phase 3 LEFT/RIGHT minute non-decrease (clock at phase 3, arbitrary partner).

For a clock first agent `s` at phase 3, `Phase3Transition L K s t` keeps its first
output a clock with `minute ≥ s.minute`, for ARBITRARY `t`.  Rule 1 (`s1`) either
leaves `s` unchanged (`t` not a clock) or drips/syncs it upward; Rule 2 (`s2`)
never modifies the clock `s1` (a clock is not a Main, and the Main-hour-drag branch
returns `s1` unchanged); Rules 3+4 fire only when `s2` is a Main, so the result is
`(s1, t1)`. -/

/-- `Phase3Transition` first output role+minute for a clock first agent at phase 3,
ARBITRARY partner.  Mirrors `Phase3Transition_left_output_eq_rule1`'s `set` proof;
the cancel/split (Rules 3+4) branch is impossible because the clock first component
`s2` is not a Main. -/
private theorem phase3_left_min (s t : AgentState L K) (hs : s.role = .clock)
    (hps : s.phase.val = 3) :
    (Phase3Transition L K s t).1.role = .clock ∧
      s.minute.val ≤ (Phase3Transition L K s t).1.minute.val := by
  classical
  have hsc := stdCounterSubroutine_clock_minute (L := L) (K := K) s hs (by omega)
  unfold Phase3Transition
  dsimp only
  set t1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then t
      else stdCounterSubroutine L K t
    else t) with ht1def
  set s1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then
        { s with minute := ⟨s.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K s
    else s) with hs1def
  set s2 : AgentState L K :=
    (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
        { s1 with hour :=
            ⟨max s1.hour.val (min L (t1.minute.val / K)), by
              exact (Nat.max_lt).mpr
                ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
      else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
      else s1) with hs2def
  set t2 : AgentState L K :=
    (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
      else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
        { t1 with hour :=
            ⟨max t1.hour.val (min L (s1.minute.val / K)), by
              exact (Nat.max_lt).mpr
                ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
      else t1) with ht2def
  -- s1 is role-clock with minute ≥ s.minute (Rule 1).
  have hs1_role : s1.role = .clock := by
    rw [hs1def]; split_ifs <;> first | exact hs | exact hsc.1
  have hs1_min : s.minute.val ≤ s1.minute.val := by
    rw [hs1def]; split_ifs with h1 h2
    · change s.minute.val ≤ (max s.minute t.minute).val
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]; exact h
      · rw [max_eq_left h]
    · change s.minute.val ≤ s.minute.val + 1; omega
    · rw [hsc.2]
    · exact le_refl _
  -- s2 keeps s1's role and minute (the hour-drag branch edits only `hour`).
  have hs2_role : s2.role = s1.role := by rw [hs2def]; split_ifs <;> rfl
  have hs2_min : s2.minute = s1.minute := by rw [hs2def]; split_ifs <;> rfl
  -- the cancel/split branch needs s2.role = main; s2 is a clock.
  have hnm : ¬ (s2.role = .main ∧ t2.role = .main) := by
    rintro ⟨h, _⟩; rw [hs2_role, hs1_role] at h; exact absurd h (by decide)
  change (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).1.role = .clock ∧
    s.minute.val ≤ (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).1.minute.val
  rw [if_neg hnm]
  refine ⟨?_, ?_⟩
  · change s2.role = .clock; rw [hs2_role, hs1_role]
  · change s.minute.val ≤ s2.minute.val; rw [hs2_min]; exact hs1_min

/-- Phase 3 right output role+minute for a clock SECOND agent at phase 3, ARBITRARY
partner.  Mirror of `phase3_left_min` on the second projection. -/
private theorem phase3_right_min (s t : AgentState L K) (ht : t.role = .clock)
    (hpt : t.phase.val = 3) :
    (Phase3Transition L K s t).2.role = .clock ∧
      t.minute.val ≤ (Phase3Transition L K s t).2.minute.val := by
  classical
  have htc := stdCounterSubroutine_clock_minute (L := L) (K := K) t ht (by omega)
  unfold Phase3Transition
  dsimp only
  set s1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then
        { s with minute := ⟨s.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K s
    else s) with hs1def
  set t1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then t
      else stdCounterSubroutine L K t
    else t) with ht1def
  set s2 : AgentState L K :=
    (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
        { s1 with hour :=
            ⟨max s1.hour.val (min L (t1.minute.val / K)), by
              exact (Nat.max_lt).mpr
                ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
      else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
      else s1) with hs2def
  set t2 : AgentState L K :=
    (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
      else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
        { t1 with hour :=
            ⟨max t1.hour.val (min L (s1.minute.val / K)), by
              exact (Nat.max_lt).mpr
                ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
      else t1) with ht2def
  -- t1 is role-clock with minute ≥ t.minute (Rule 1).
  have ht1_role : t1.role = .clock := by
    rw [ht1def]; split_ifs <;> first | exact ht | exact htc.1
  have ht1_min : t.minute.val ≤ t1.minute.val := by
    rw [ht1def]; split_ifs with h1 h2
    · change t.minute.val ≤ (max s.minute t.minute).val
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]
      · rw [max_eq_left h]; exact h
    · exact le_refl _
    · rw [htc.2]
    · exact le_refl _
  -- t2 keeps t1's role and minute (the hour-drag branch edits only `hour`).
  have ht2_role : t2.role = t1.role := by rw [ht2def]; split_ifs <;> rfl
  have ht2_min : t2.minute = t1.minute := by rw [ht2def]; split_ifs <;> rfl
  have hs2_role : s2.role = s1.role := by rw [hs2def]; split_ifs <;> rfl
  have hnm : ¬ (s2.role = .main ∧ t2.role = .main) := by
    rintro ⟨_, h⟩; rw [ht2_role, ht1_role] at h; exact absurd h (by decide)
  change (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).2.role = .clock ∧
    t.minute.val ≤ (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).2.minute.val
  rw [if_neg hnm]
  refine ⟨?_, ?_⟩
  · change t2.role = .clock; rw [ht2_role, ht1_role]
  · change t.minute.val ≤ t2.minute.val; rw [ht2_min]; exact ht1_min

/-! ### Phase 9 LEFT/RIGHT minute non-decrease (Phase 9 = Phase 2).

`Phase9Transition = Phase2Transition`.  A clock agent's first/second output is the
opinion-updated agent possibly run through `advancePhaseWithInit` (advancing
branch) or an output-edit (non-advancing branches), both role/`minute`-safe at
phase `≥ 3`. -/

private theorem phase9_left_min (s t : AgentState L K) (hs : s.role = .clock)
    (hps : 3 ≤ s.phase.val) :
    (Phase9Transition L K s t).1.role = .clock ∧
      s.minute.val ≤ (Phase9Transition L K s t).1.minute.val := by
  have hadv := advancePhaseWithInit_clock_minute (L := L) (K := K)
    ({ s with opinions := opinionsUnion s.opinions t.opinions }) hs hps
  unfold Phase9Transition Phase2Transition
  dsimp only
  split_ifs <;>
    first
    | exact ⟨hadv.1, by rw [hadv.2]⟩
    | exact ⟨hs, le_refl _⟩

private theorem phase9_right_min (s t : AgentState L K) (ht : t.role = .clock)
    (hpt : 3 ≤ t.phase.val) :
    (Phase9Transition L K s t).2.role = .clock ∧
      t.minute.val ≤ (Phase9Transition L K s t).2.minute.val := by
  have hadv := advancePhaseWithInit_clock_minute (L := L) (K := K)
    ({ t with opinions := opinionsUnion s.opinions t.opinions }) ht hpt
  unfold Phase9Transition Phase2Transition
  dsimp only
  split_ifs <;>
    first
    | exact ⟨hadv.1, by rw [hadv.2]⟩
    | exact ⟨ht, le_refl _⟩

/-! ### Phase 10 LEFT/RIGHT minute non-decrease.

`Phase10Transition` edits only `output`/`full`, never `role` or `minute`. -/

private theorem phase10_left_min (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase10Transition L K s t).1.role = .clock ∧
      s.minute.val ≤ (Phase10Transition L K s t).1.minute.val := by
  unfold Phase10Transition
  dsimp only
  split_ifs <;> exact ⟨by simp [hs], by simp⟩

private theorem phase10_right_min (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase10Transition L K s t).2.role = .clock ∧
      t.minute.val ≤ (Phase10Transition L K s t).2.minute.val := by
  unfold Phase10Transition
  dsimp only
  split_ifs <;> exact ⟨by simp [ht], by simp⟩

/-! ## Part 2 — the assembled single-clock minute non-decrease.

For a clock first (resp. second) agent at phase EXACTLY 3, the `Transition` first
(resp. second) output is a clock whose minute is `≥` the input minute, for an
ARBITRARY partner.  Mirrors `ClockRealKernel.Transition_clock_pair`, but only one
side is constrained (the partner is free): the epidemic keeps the clock's minute
and raises its phase to `≥ 3`, the dispatched per-phase rule's corresponding output
is `minute`-non-decreasing (Part 1), and `finishPhase10Entry` keeps `minute`. -/

private theorem transition_left_clock_minute_ge (s t : AgentState L K)
    (hs_clock : s.role = .clock) (hs_phase : s.phase.val = 3) :
    (Transition L K s t).1.role = .clock ∧
      s.minute.val ≤ (Transition L K s t).1.minute.val := by
  classical
  have hepi := epidemic_left_clock_phase3 (L := L) (K := K) s t hs_clock hs_phase
  set s' := (phaseEpidemicUpdate L K s t).1 with hs'
  set t' := (phaseEpidemicUpdate L K s t).2 with ht'
  have hs'clock : s'.role = .clock := hepi.1
  have hs'min : s'.minute = s.minute := hepi.2.1
  have hs'phase : 3 ≤ s'.phase.val := hepi.2.2
  -- dispatched per-phase rule (first output) keeps role and minute ≥ s'.minute.
  set out := match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t') with hout
  have hdispatch : out.1.role = .clock ∧ s'.minute.val ≤ out.1.minute.val := by
    rw [hout]
    rcases hpv : s'.phase with ⟨pv, hpvlt⟩
    have hpv3 : 3 ≤ pv := by have := hs'phase; rw [hpv] at this; exact this
    interval_cases pv
    · have h := phase3_left_min s' t' hs'clock (by rw [hpv])
      simpa [hpv] using h
    · have h := phase4_left_min s' t' hs'clock
      simpa [hpv] using h
    · have h := phase5_left_min s' t' hs'clock (by rw [hpv]; omega)
      simpa [hpv] using h
    · have h := phase6_left_min s' t' hs'clock (by rw [hpv]; omega)
      simpa [hpv] using h
    · have h := phase7_left_min s' t' hs'clock (by rw [hpv]; omega)
      simpa [hpv] using h
    · have h := phase8_left_min s' t' hs'clock (by rw [hpv]; omega)
      simpa [hpv] using h
    · have h := phase9_left_min s' t' hs'clock (by rw [hpv]; omega)
      simpa [hpv] using h
    · have h := phase10_left_min s' t' hs'clock
      simpa [hpv] using h
  have hTeq : Transition L K s t =
      (finishPhase10Entry L K s' out.1, finishPhase10Entry L K t' out.2) := by
    conv_lhs => unfold Transition
    rfl
  rw [hTeq]
  have hfin_role : (finishPhase10Entry L K s' out.1).role = .clock := by
    unfold finishPhase10Entry canonicalPhase10Entry
    split_ifs <;> simp [enterPhase10, hdispatch.1]
  have hfin_min : (finishPhase10Entry L K s' out.1).minute = out.1.minute := by
    unfold finishPhase10Entry canonicalPhase10Entry
    split_ifs <;> simp [enterPhase10]
  refine ⟨hfin_role, ?_⟩
  rw [hfin_min]
  have : s.minute.val = s'.minute.val := by rw [hs'min]
  omega

private theorem transition_right_clock_minute_ge (s t : AgentState L K)
    (ht_clock : t.role = .clock) (ht_phase : t.phase.val = 3) :
    (Transition L K s t).2.role = .clock ∧
      t.minute.val ≤ (Transition L K s t).2.minute.val := by
  classical
  have hepi := epidemic_right_clock_phase3 (L := L) (K := K) s t ht_clock ht_phase
  set s' := (phaseEpidemicUpdate L K s t).1 with hs'
  set t' := (phaseEpidemicUpdate L K s t).2 with ht'
  have ht'clock : t'.role = .clock := hepi.1
  have ht'min : t'.minute = t.minute := hepi.2.1
  have ht'phase : 3 ≤ t'.phase.val := hepi.2.2
  -- the dispatch fires on `s'.phase`; we need `3 ≤ s'.phase` to land in Phases 3–10.
  -- s'.phase ≥ max s.phase t.phase ≥ t.phase = 3.
  have hs'phase : 3 ≤ s'.phase.val := by
    have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    have hmax : t.phase.val ≤ max s.phase.val t.phase.val := le_max_right _ _
    rw [← hs'] at hge; omega
  set out := match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t') with hout
  -- when the dispatch fires Phase 3 (s'.phase = 3), the partner clock t' is also at
  -- phase 3 (the epidemic drags both to the common max; s'.phase = 3 forces max = 3,
  -- and t' was dragged from phase 3).
  have ht'phase3_of_s'3 : s'.phase.val = 3 → t'.phase.val = 3 := by
    intro h3
    -- p = max s.phase t.phase has p ≤ s'.phase = 3 (s' ≥ max) and p ≥ t.phase = 3.
    have hge : max s.phase.val t.phase.val ≤ s'.phase.val := by
      have := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
      rw [← hs'] at this; exact this
    have hmaxle : max s.phase.val t.phase.val ≤ 3 := by omega
    have hp3 : (max s.phase t.phase).val = 3 := by
      have hp_ge : 3 ≤ (max s.phase t.phase).val := by
        have : t.phase.val ≤ (max s.phase t.phase).val := by
          exact_mod_cast (le_max_right s.phase t.phase : t.phase ≤ max s.phase t.phase)
        omega
      have hp_le : (max s.phase t.phase).val ≤ 3 := by
        have : (max s.phase t.phase).val = max s.phase.val t.phase.val := rfl
        omega
      omega
    -- t' = runInitsBetween from oldP = t.phase.val = 3 to newP = 3 = identity on phase,
    -- with no phase-10 entry (s'.phase = 3 ≠ 10 rules out the error branch), so t'.phase = 3.
    set p := max s.phase t.phase with hpdef
    have hrun_phase :
        (runInitsBetween L K t.phase.val p.val { t with phase := p }).phase.val = 3 := by
      have hempty : (List.range 11).filter (fun k => t.phase.val < k ∧ k ≤ p.val) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro k hk hcond
        simp only [decide_eq_true_eq] at hcond
        rw [ht_phase, hp3] at hcond; omega
      unfold runInitsBetween
      rw [hempty]; simp [hp3]
    by_cases hbr : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L K s.phase.val p.val { s with phase := p }).phase.val = 10 ∨
         (runInitsBetween L K t.phase.val p.val { t with phase := p }).phase.val = 10)
    · -- impossible: in this branch `s'.phase` = (phase10EpidemicEntry ...).phase, which is
      -- 10 (if s.phase < 10) or s.phase ≥ 10 (impossible, s.phase ≤ p = 3); both ≠ 3 = `h3`.
      exfalso
      have hs'val : s'.phase.val =
          (phase10EpidemicEntry L K s
            (runInitsBetween L K s.phase.val p.val { s with phase := p })).phase.val := by
        rw [hs']; unfold phaseEpidemicUpdate; rw [if_pos hbr]
      rw [hs'val] at h3
      by_cases hslt : s.phase.val < 10
      · rw [phase10EpidemicEntry_phase_val_of_before_lt_10 (L := L) (K := K) s _ hslt] at h3; omega
      · have hsle : s.phase.val ≤ p.val := by
          have hle : s.phase.val ≤ max s.phase.val t.phase.val := le_max_left _ _
          have hpv : (max s.phase t.phase).val = max s.phase.val t.phase.val := rfl
          rw [hpdef]; omega
        omega
    · -- non-error branch: t' = runInitsBetween (right), phase = 3.
      have : t'.phase.val =
          (runInitsBetween L K t.phase.val p.val { t with phase := p }).phase.val := by
        rw [ht']; unfold phaseEpidemicUpdate; rw [if_neg hbr]
      rw [this, hrun_phase]
  have hdispatch : out.2.role = .clock ∧ t'.minute.val ≤ out.2.minute.val := by
    rw [hout]
    rcases hpv : s'.phase with ⟨pv, hpvlt⟩
    have hpv3 : 3 ≤ pv := by have := hs'phase; rw [hpv] at this; exact this
    interval_cases pv
    · have ht'3 : t'.phase.val = 3 := ht'phase3_of_s'3 (by rw [hpv])
      have h := phase3_right_min s' t' ht'clock ht'3
      simpa [hpv] using h
    · have h := phase4_right_min s' t' ht'clock
      simpa [hpv] using h
    · have h := phase5_right_min s' t' ht'clock ht'phase
      simpa [hpv] using h
    · have h := phase6_right_min s' t' ht'clock ht'phase
      simpa [hpv] using h
    · have h := phase7_right_min s' t' ht'clock ht'phase
      simpa [hpv] using h
    · have h := phase8_right_min s' t' ht'clock ht'phase
      simpa [hpv] using h
    · have h := phase9_right_min s' t' ht'clock ht'phase
      simpa [hpv] using h
    · have h := phase10_right_min s' t' ht'clock
      simpa [hpv] using h
  have hTeq : Transition L K s t =
      (finishPhase10Entry L K s' out.1, finishPhase10Entry L K t' out.2) := by
    conv_lhs => unfold Transition
    rfl
  rw [hTeq]
  have hfin_role : (finishPhase10Entry L K t' out.2).role = .clock := by
    unfold finishPhase10Entry canonicalPhase10Entry
    split_ifs <;> simp [enterPhase10, hdispatch.1]
  have hfin_min : (finishPhase10Entry L K t' out.2).minute = out.2.minute := by
    unfold finishPhase10Entry canonicalPhase10Entry
    split_ifs <;> simp [enterPhase10]
  refine ⟨hfin_role, ?_⟩
  rw [hfin_min]
  have : t.minute.val = t'.minute.val := by rw [ht'min]
  omega

/-! ## Part 3 — the per-pair count monotonicity and the discharged theorem.

The per-pair `clockBeyondP (T+1)` count does not drop: a removed agent counted at
level `T+1` (a clock at minute `≥ T+1`) sits at phase 3 (it is a clock in `c`, so
`Q_mix.clockPhase3`), hence its `Transition` output is a clock with minute `≥ T+1`
(Part 2) — still counted.  This is the mixed-regime replacement for
`ClockRealKernel.rBeyond_pair_mono` (which needed both agents to be clocks). -/

/-- For a removed ordered pair `(r₁, r₂)` of agents present in `c` (a `Q_mix` config),
the `clockBeyondP (T+1)` count over the two outputs is at least the count over the
two inputs.  Mirrors `rBeyond_pair_mono`, but the partner is unconstrained: a
counted clock at phase 3 keeps its membership through `Transition` (Part 2). -/
private theorem mixed_pair_countP_mono (n mC T : ℕ) (c : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC T c)
    (r₁ r₂ : AgentState L K) (hr₁ : r₁ ∈ c) (hr₂ : r₂ ∈ c) :
    Multiset.countP (fun a => clockBeyondP (T + 1) a)
        ({r₁, r₂} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => clockBeyondP (T + 1) a)
          ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K)) := by
  classical
  rw [countP_pair, countP_pair]
  -- left: if r₁ counted (clock ∧ minute ≥ T+1) then so is (Transition r₁ r₂).1.
  have hleft : (if clockBeyondP (T + 1) r₁ then (1:ℕ) else 0)
      ≤ (if clockBeyondP (T + 1) (Transition L K r₁ r₂).1 then 1 else 0) := by
    by_cases hc1 : clockBeyondP (T + 1) r₁
    · have hr1clock : r₁.role = .clock := hc1.1
      have hr1min : T + 1 ≤ r₁.minute.val := hc1.2
      have hr1phase : r₁.phase.val = 3 := hQ.clockPhase3 r₁ hr₁ hr1clock
      have hout := transition_left_clock_minute_ge r₁ r₂ hr1clock hr1phase
      have : clockBeyondP (T + 1) (Transition L K r₁ r₂).1 :=
        ⟨hout.1, le_trans hr1min hout.2⟩
      rw [if_pos hc1, if_pos this]
    · rw [if_neg hc1]; omega
  -- right: if r₂ counted then so is (Transition r₁ r₂).2.
  have hright : (if clockBeyondP (T + 1) r₂ then (1:ℕ) else 0)
      ≤ (if clockBeyondP (T + 1) (Transition L K r₁ r₂).2 then 1 else 0) := by
    by_cases hc2 : clockBeyondP (T + 1) r₂
    · have hr2clock : r₂.role = .clock := hc2.1
      have hr2min : T + 1 ≤ r₂.minute.val := hc2.2
      have hr2phase : r₂.phase.val = 3 := hQ.clockPhase3 r₂ hr₂ hr2clock
      have hout := transition_right_clock_minute_ge r₁ r₂ hr2clock hr2phase
      have : clockBeyondP (T + 1) (Transition L K r₁ r₂).2 :=
        ⟨hout.1, le_trans hr2min hout.2⟩
      rw [if_pos hc2, if_pos this]
    · rw [if_neg hc2]; omega
  omega

/-- `rBeyond (T+1)` is non-decreasing under any chosen-pair update, on a `Q_mix`
config.  Mirrors `rBeyond_stepOrSelf_ge`, using `mixed_pair_countP_mono` (per-pair,
arbitrary partner) in place of `rBeyond_pair_mono` (all-clocks). -/
private theorem rBeyond_stepOrSelf_ge_mixed (n mC T : ℕ) (c : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC T c) (r₁ r₂ : AgentState L K) :
    rBeyond (L := L) (K := K) (T + 1) c
      ≤ rBeyond (L := L) (K := K) (T + 1)
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    unfold rBeyond
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => clockBeyondP (T + 1) a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => clockBeyondP (T + 1) a) c :=
      Multiset.countP_le_of_le _ hsub
    have hmono := mixed_pair_countP_mono n mC T c hQ r₁ r₂ hmem1 hmem2
    rw [hδ]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- **`hmono_mix_discharged` — the carried mixed-regime monotonicity, PROVEN.**
On any `Q_mix n mC T` config, `rBeyond (T+1)` (the count of clock-role agents at
minute `≥ T+1`) is non-decreasing on the one-step kernel support.  Discharged from
the transition lemmas (clock-role permanence + minute non-decrease for a phase-3
clock with arbitrary partner) — NOT assumed.  This is exactly the `hmono` hypothesis
carried by `ClockRealMixed.rSeedPot_contracts_mixed`. -/
theorem hmono_mix_discharged (n mC T : ℕ) :
    ∀ c c' : Config (AgentState L K), Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      rBeyond (L := L) (K := K) (T + 1) c ≤ rBeyond (L := L) (K := K) (T + 1) c' := by
  classical
  intro c c' hQ hc'
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact rBeyond_stepOrSelf_ge_mixed n mC T c hQ r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact le_refl _

end ClockMonoDischarge

end ExactMajority
