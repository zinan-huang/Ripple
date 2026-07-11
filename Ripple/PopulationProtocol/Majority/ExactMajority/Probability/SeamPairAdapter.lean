/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — the HONEST seam per-pair `hpair` adapter (`SeamPairAdapter`)

This file packages the protocol-structural per-pair output bound for the seam
no-overshoot clock-counter tail with the HONEST constants discovered in
`SeamPairBound.lean`'s genuine attack, and re-wires the consumer chain in
`SeamNoOvershoot.lean` accordingly.  Append-only; it EDITS no existing file.

## The two honest corrections it implements (from `SeamPairBound`'s findings)

1. **The honest per-pair immigration ceiling is `2·eˢ·freshVal`, NOT `2·freshVal`.**
   A fresh epidemic-dragged clock enters `p+1` at the FULL counter and is DECREMENTED
   by the SAME-step dispatch to `full − 1`, so its summand is `eˢ·freshVal` per side,
   `2·eˢ·freshVal` per pair.  (`SeamNoOvershoot`'s `seamClockPotential_drift_affine`
   consumed `2·freshVal`, which is FALSE for `s > 0`.)

2. **The honest counter-reset destination set is `{1,6,7,8}`, NOT `{1,5,6,7,8}`.**
   Phase 5's predecessor `Phase4Transition` advances clocks via `advancePhase`
   (big-bias gate, NO `phaseInit`, NO counter reset), so a clock counter-advanced from
   phase 4 into phase 5 keeps its OLD counter (summand up to `1`, not `freshVal`),
   breaking the immigration tail.  Phases `{1,6,7,8}` are clean: their predecessors
   (`Phase0` Rule-5 / `Phase{5,6,7}`) all advance clocks via
   `stdCounterSubroutine → advancePhaseWithInit → phaseInit q`, which DOES reset.

## What is built (0 sorry / 0 axiom / no native_decide)

* **Stage 1** — the missing ADVANCE-regime dispatch reductions for the honest set
  `{1,6,7,8}`: `Phase0Transition_left_clock_eq` / `…_right_clock_eq` (the conditional
  Rule-5 dispatch), and the per-side ADVANCE bound
  `seamClockSummand_Transition_side_advance_le` (a clock advanced INTO `p+1` enters at
  full counter, summand `= freshVal`).
* **Stage 2** — the HONEST two-sided per-pair bound
  `seamClockSummand_Transition_pair_le`
  `summand(δ.1) + summand(δ.2) ≤ eˢ·(summand a + summand b) + 2·eˢ·freshVal`
  on the seam region (destination `p+1 ∈ {1,6,7,8}`), assembled from the per-side
  no-advance (`SeamPairBound`) and advance (Stage 1) bounds.
* **Stage 3** — the corrected drift `seamClockPotential_drift_affine_honest` with
  `b = 2·eˢ·freshVal`, derived from Stage 2 via
  `Phase0Window.lintegral_transitionKernel_eq_sum` (mirrors `SeamNoOvershoot`).
* **Stage 4** — the corrected numerics `seam_noOvershoot_numerics_honest`
  (`b = 2·e·freshVal` at `s = 1`; verifies the `e^{−45}+e^{−43}→e^{−40}` slack absorbs
  the extra `eˢ` factor) and the end-to-end honest at-risk tail / no-overshoot tail.

The four excluded destination phases are handled by NAMED per-phase guard facts (NOT
faked): phases `2,4,9` (untimed: opinion-union / big-bias) and phases `3,5`
(counter-timed but no counter reset on entry) carry their own work-phase / width
guards; see the `CounterResetDest` predicate and the closing doc section.

Reference: Doty et al. §6; consumer = `SeamNoOvershoot.lean`; protocol core =
`SeamPairBound.lean`; pattern = `Phase0Window.lean`; blueprint =
`HANDOFF_SEAM_NOOVERSHOOT.md`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamPairBound

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-! ## The honest counter-reset destination set `{1,6,7,8}`.

This is the intersection of the epidemic-drag reset set `{1,5,6,7,8}`
(`CounterTimedPhase`) with the counter-ADVANCE reset set: a clock counter-advanced
INTO `q` keeps a full counter iff `q`'s PREDECESSOR `q−1` advances clocks via
`stdCounterSubroutine → advancePhaseWithInit → phaseInit q`.  For `q = 5` the
predecessor (phase 4) advances via `advancePhase` (no reset), so `5` is excluded. -/

/-- **The honest counter-reset destination set** `{1, 6, 7, 8}` (blueprint's
`CounterTimedPhase` minus phase 5).  Entry into these phases both (i) decrements the
summand by `eˢ` for a clock already there, AND (ii) resets a counter-advanced or
epidemic-dragged immigrant clock to the FULL counter (summand `= freshVal`). -/
def CounterResetDest (q : ℕ) : Prop :=
  q = 1 ∨ q = 6 ∨ q = 7 ∨ q = 8

instance (q : ℕ) : Decidable (CounterResetDest q) := by
  unfold CounterResetDest; infer_instance

/-- `CounterResetDest ⊆ CounterTimedPhase` (so `SeamPairBound`'s no-advance lemmas,
stated for `CounterTimedPhase`, apply on the honest set). -/
theorem CounterTimedPhase_of_CounterResetDest {q : ℕ} (h : CounterResetDest q) :
    CounterTimedPhase q := by
  rcases h with h | h | h | h <;> simp [CounterTimedPhase, h]

/-! ## Stage 1 — the ADVANCE-regime dispatch reductions for `{1,6,7,8}`.

`SeamPairBound` proved the NO-ADVANCE per-side bound (when `ep.1.phase = p+1`): the
dispatch is `Phase(p+1)Transition` and the clock summand contracts by `eˢ`.  The
remaining ADVANCE regime is when `ep.i.phase = p` and the same-step dispatch advances
the clock INTO `p+1`.  For destination `p+1 ∈ {1,6,7,8}` the dispatch (selected by
`ep.1.phase = p`) is `Phase{0,5,6,7}Transition`; for a clock initiator/responder these
reduce to `stdCounterSubroutine` of that clock, EXCEPT Phase 0, whose Rule-5 clock step
is gated on the PARTNER also being a clock.  In every case the LEFT/RIGHT clock output
is `stdCounterSubroutine ep.i` or `ep.i` unchanged — and if it lands at `p+1` it must be
the advancing `stdCounterSubroutine` branch, which RESETS the counter (summand
`= freshVal`). -/

/-- **Phase-0 LEFT clock reduction (advance regime).**  For a clock initiator `c`, the
Phase-0 dispatch LEFT output equals `stdCounterSubroutine ĉ` (Rule 5, when the partner
is also a clock) or `ĉ` unchanged, where `ĉ` is `c` possibly with `assigned := true`
(Phase-0 Rule 3, partner-mcr).  Crucially `ĉ` is a CLOCK at the SAME phase as `c` — so
the advance lemma `seamClockSummand_stdCounterSubroutine_advance` applies to `ĉ`
directly, with no need to relate it back to `c`. -/
theorem Phase0Transition_left_clock_eq (c t : AgentState L K) (hc : c.role = .clock) :
    ∃ chat : AgentState L K, chat.role = .clock ∧ chat.phase.val = c.phase.val
      ∧ ((Phase0Transition L K c t).1 = stdCounterSubroutine L K chat
        ∨ (Phase0Transition L K c t).1 = chat) := by
  have hnm : c.role ≠ .mcr := by rw [hc]; decide
  have hnmain : c.role ≠ .main := by rw [hc]; decide
  have hncr : c.role ≠ .cr := by rw [hc]; decide
  by_cases h3 : t.role = Role.mcr ∧ ¬ c.assigned = true
  · -- Rule 3 fires (partner is mcr ⇒ NOT a clock ⇒ Rule 5 gate false):
    -- the output is exactly `{c with assigned := true}`.
    refine ⟨{ c with assigned := true }, hc, rfl, ?_⟩
    right
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, false_and, and_false, if_false, ne_eq, not_false_eq_true,
      true_and, h3.1, h3.2, and_true, if_true]
  · -- Rule 3 does not fire: the output is `if t.role = clock then stdCounterSubroutine c else c`.
    refine ⟨c, hc, rfl, ?_⟩
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, false_and, and_false, if_false, ne_eq, not_false_eq_true,
      true_and, h3, if_false]
    by_cases hgate : t.role = .clock
    · left; rw [if_pos hgate]
    · right; rw [if_neg hgate]

/-- **Phase-0 RIGHT clock reduction (advance regime).**  Symmetric. -/
theorem Phase0Transition_right_clock_eq (s c : AgentState L K) (hc : c.role = .clock) :
    ∃ chat : AgentState L K, chat.role = .clock ∧ chat.phase.val = c.phase.val
      ∧ ((Phase0Transition L K s c).2 = stdCounterSubroutine L K chat
        ∨ (Phase0Transition L K s c).2 = chat) := by
  have hnm : c.role ≠ .mcr := by rw [hc]; decide
  have hnmain : c.role ≠ .main := by rw [hc]; decide
  have hncr : c.role ≠ .cr := by rw [hc]; decide
  by_cases h3 : s.role = Role.mcr ∧ ¬ c.assigned = true
  · -- Rule 3 (branch 1) sets `c.assigned := true`; partner `s` is mcr (NOT clock),
    -- so Rule 5 gate is false → output is exactly `{c with assigned := true}`.
    refine ⟨{ c with assigned := true }, hc, rfl, ?_⟩
    right
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, and_false, false_and, if_false, ne_eq, not_false_eq_true,
      true_and, and_true, h3.1, h3.2, if_true]
  · refine ⟨c, hc, rfl, ?_⟩
    unfold Phase0Transition
    simp only [hc, reduceCtorEq, and_false, false_and, if_false, ne_eq, not_false_eq_true,
      true_and, and_true, h3]
    by_cases hgate : s.role = .clock
    · left; rw [if_pos hgate]
    · right; rw [if_neg hgate]

/-- For a clock RESPONDER, the Phase-5 dispatch RIGHT output equals
`stdCounterSubroutine c` (the reserve/main sampling pre-step never touches a clock). -/
theorem Phase5Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase5Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase5Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock RESPONDER, the Phase-6 dispatch RIGHT output equals
`stdCounterSubroutine c`. -/
theorem Phase6Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase6Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase6Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock RESPONDER, the Phase-7 dispatch RIGHT output equals
`stdCounterSubroutine c`. -/
theorem Phase7Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase7Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase7Transition
  simp only [hc, reduceCtorEq, and_false, ↓reduceIte]

/-- For a clock RESPONDER, the Phase-8 dispatch RIGHT output equals
`stdCounterSubroutine c`. -/
theorem Phase8Transition_right_clock (s c : AgentState L K) (hc : c.role = .clock) :
    (Phase8Transition L K s c).2 = stdCounterSubroutine L K c := by
  unfold Phase8Transition
  simp only [hc, reduceCtorEq, and_false, ↓reduceIte]

/-! ## Stage 2 — the per-side bounds (both regimes) and the HONEST two-sided pair bound.

The per-side bound `summand(δ.side) ≤ eˢ·(summand(source) + freshVal)` covers BOTH
regimes:

* **No-advance** (`ep.side.phase = p+1`): the clock is already at the destination, the
  dispatch ticks it, the summand contracts by `eˢ` (`SeamPairBound`'s `…_le_of_ep_at_dest`
  for the LEFT; a fresh RIGHT analogue here).
* **Advance** (`ep.side.phase = p`, dispatch advances it INTO `p+1`): the new clock has a
  FULL counter (`phaseInit` reset on `{1,6,7,8}`), summand `= freshVal`
  (`seamClockSummand_stdCounterSubroutine_advance` on the `chat` clock); `freshVal ≤
  eˢ·(summand(source) + freshVal)`.
* Otherwise the output is not a clock at `p+1` (summand `0`).

Summing the two per-side bounds gives the HONEST two-sided ceiling `2·eˢ·freshVal`. -/

/-- `freshVal ≤ eˢ·(x + freshVal)` for `s ≥ 0`, any `x`. -/
theorem freshVal_le_exp_mul_add (s : ℝ) (hs : 0 ≤ s) (x : ℝ≥0∞) :
    freshVal (L := L) s ≤ ENNReal.ofReal (Real.exp s) * (x + freshVal (L := L) s) := by
  have he1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp s) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hs)
  calc freshVal (L := L) s
      = 1 * freshVal (L := L) s := (one_mul _).symm
    _ ≤ ENNReal.ofReal (Real.exp s) * (x + freshVal (L := L) s) := by
        gcongr
        exact le_add_self

/-- **Epidemic immigration counter (RIGHT).**  Mirror of
`SeamPairBound.phaseEpidemicUpdate_left_immigrant_full`. -/
theorem phaseEpidemicUpdate_right_immigrant_full (a b : AgentState L K)
    (q : ℕ) (hq : CounterTimedPhase q) (hblt : b.phase.val < q)
    (hep_role : (phaseEpidemicUpdate L K a b).2.role = .clock)
    (hep_phase : (phaseEpidemicUpdate L K a b).2.phase.val = q) :
    (phaseEpidemicUpdate L K a b).2.counter.val = 50 * (L + 1) := by
  have hq11 : q < 11 := by rcases hq with h | h | h | h | h <;> omega
  have hqle : q ≤ 8 := by rcases hq with h | h | h | h | h <;> omega
  set mx := max a.phase b.phase with hmxdef
  set s0 := runInitsBetween L K a.phase.val mx.val { a with phase := mx } with hs0def
  set t0 := runInitsBetween L K b.phase.val mx.val { b with phase := mx } with ht0def
  have hepeq : phaseEpidemicUpdate L K a b
      = if (a.phase.val < 10 ∨ b.phase.val < 10) ∧ (s0.phase.val = 10 ∨ t0.phase.val = 10)
          then (phase10EpidemicEntry L K a s0, phase10EpidemicEntry L K b t0)
          else (s0, t0) := rfl
  rw [hepeq] at hep_role hep_phase ⊢
  by_cases hcond : (a.phase.val < 10 ∨ b.phase.val < 10) ∧ (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · rw [if_pos hcond] at hep_phase
    exfalso
    have hb10 : b.phase.val < 10 := by omega
    simp only at hep_phase
    rw [phase10EpidemicEntry_phase_val_of_before_lt_10 (L := L) (K := K) b t0 hb10] at hep_phase
    omega
  · rw [if_neg hcond] at hep_role hep_phase ⊢
    simp only at hep_role hep_phase ⊢
    have hmxq : mx.val = q := by
      rcases runInitsBetween_phase_eq_or_ten b.phase.val mx.val
          { b with phase := mx } with h | h
      · rw [ht0def, h] at hep_phase; simpa using hep_phase
      · rw [ht0def, h] at hep_phase; omega
    have hb_clock : ({ b with phase := mx } : AgentState L K).role = .clock :=
      runInitsBetween_role_clock_imp _ _ _ hep_role
    have hreset := runInitsBetween_clock_counter_reset b.phase.val mx.val
      { b with phase := mx } hb_clock (by rw [hmxq]; exact hblt) (by rw [hmxq]; exact hq)
    rw [ht0def]; exact hreset

/-- **Epidemic summand immigration bound (RIGHT).**  Mirror of
`SeamPairBound.seamClockSummand_phaseEpidemicUpdate_left_le`. -/
theorem seamClockSummand_phaseEpidemicUpdate_right_le (p : ℕ) (s : ℝ)
    (hq : CounterTimedPhase (p + 1)) (a b : AgentState L K) :
    seamClockSummand (L := L) (K := K) p s (phaseEpidemicUpdate L K a b).2
      ≤ seamClockSummand (L := L) (K := K) p s b + freshVal (L := L) s := by
  set ep2 := (phaseEpidemicUpdate L K a b).2 with hep2
  by_cases hcond : ep2.role = .clock ∧ ep2.phase.val = p + 1
  · obtain ⟨hrole, hphase⟩ := hcond
    rcases lt_trichotomy b.phase.val (p + 1) with hlt | heq | hgt
    · have hfull : ep2.counter.val = 50 * (L + 1) := by
        rw [hep2]; rw [hep2] at hrole hphase
        exact phaseEpidemicUpdate_right_immigrant_full a b (p + 1) hq hlt hrole hphase
      have : seamClockSummand (L := L) (K := K) p s ep2 = freshVal (L := L) s := by
        unfold seamClockSummand freshVal
        rw [if_pos ⟨hrole, hphase⟩, hfull]
      rw [this]; exact le_add_left le_rfl
    · have hab : a.phase.val ≤ b.phase.val := by
        by_contra hgt
        rw [not_le] at hgt
        have hge : a.phase.val ≤ ep2.phase.val := by
          rw [hep2]
          exact le_trans (le_max_left _ _)
            (phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) a b)
        omega
      obtain ⟨hctr, hrole_b, hphase_or⟩ := phaseEpidemicUpdate_right_id_of_ge a b hab
      have hsummeq : seamClockSummand (L := L) (K := K) p s ep2
          = seamClockSummand (L := L) (K := K) p s b := by
        apply seamClockSummand_congr
        · rw [hep2]; exact hrole_b
        · rcases hphase_or with hph | hph
          · rw [hep2, hph]
          · exfalso
            have hple : p + 1 ≤ 8 := by rcases hq with h | h | h | h | h <;> omega
            rw [← hep2] at hph; omega
        · rw [hep2, hctr]
      rw [hsummeq]; exact le_self_add
    · exfalso
      have hge : b.phase.val ≤ ep2.phase.val := by
        rw [hep2]
        exact le_trans (le_max_right _ _)
          (phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) a b)
      omega
  · have : seamClockSummand (L := L) (K := K) p s ep2 = 0 := by
      unfold seamClockSummand; rw [if_neg hcond]
    rw [this]; exact zero_le'

/-- **RIGHT-side no-advance per-side bound** (the seam analogue of `SeamPairBound`'s
`seamClockSummand_Transition_left_le_of_ep_at_dest`, for the RIGHT output).  The
`Transition` dispatcher matches on the LEFT phase `ep.1.phase`; when `ep.1.phase = p+1`
the dispatch is `Phase(p+1)Transition`, whose RIGHT output for a clock responder `ep.2`
at `p+1` is `stdCounterSubroutine ep.2`, contracting by `eˢ`. -/
theorem seamClockSummand_Transition_right_le_of_ep_at_dest (p : ℕ)
    (hq : CounterTimedPhase (p + 1)) (s : ℝ) (hs : 0 ≤ s) (a b : AgentState L K)
    (hepdest1 : (phaseEpidemicUpdate L K a b).1.phase.val = p + 1)
    (hepdest2 : (phaseEpidemicUpdate L K a b).2.phase.val = p + 1)
    (hepclock2 : (phaseEpidemicUpdate L K a b).2.role = .clock) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
      ≤ ENNReal.ofReal (Real.exp s)
          * (seamClockSummand (L := L) (K := K) p s b + freshVal (L := L) s) := by
  set ep1 := (phaseEpidemicUpdate L K a b).1 with hep1
  set ep2 := (phaseEpidemicUpdate L K a b).2 with hep2
  -- Step 1: strip finishPhase10Entry; the dispatch is Phase(p+1)Transition on ep.
  have hstrip : seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
      = seamClockSummand (L := L) (K := K) p s
          ((if (p + 1) = 1 then Phase1Transition L K ep1 ep2
            else if (p + 1) = 5 then Phase5Transition L K ep1 ep2
            else if (p + 1) = 6 then Phase6Transition L K ep1 ep2
            else if (p + 1) = 7 then Phase7Transition L K ep1 ep2
            else Phase8Transition L K ep1 ep2).2) := by
    rw [Transition, seamClockSummand_finishPhase10Entry]
    rcases hq with h | h | h | h | h
    · have hp : ep1.phase = (⟨1, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
    · have hp : ep1.phase = (⟨5, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
    · have hp : ep1.phase = (⟨6, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
    · have hp : ep1.phase = (⟨7, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
    · have hp : ep1.phase = (⟨8, by decide⟩ : Fin 11) := Fin.ext (hepdest1.trans h)
      simp only [hep1] at hp ⊢; simp only [hp, h]; rfl
  rw [hstrip]
  -- Step 2: the dispatch RIGHT output for a clock responder = stdCounterSubroutine ep2.
  have hdec : seamClockSummand (L := L) (K := K) p s
      ((if (p + 1) = 1 then Phase1Transition L K ep1 ep2
        else if (p + 1) = 5 then Phase5Transition L K ep1 ep2
        else if (p + 1) = 6 then Phase6Transition L K ep1 ep2
        else if (p + 1) = 7 then Phase7Transition L K ep1 ep2
        else Phase8Transition L K ep1 ep2).2)
      ≤ ENNReal.ofReal (Real.exp s) * seamClockSummand (L := L) (K := K) p s ep2 := by
    have hred : ((if (p + 1) = 1 then Phase1Transition L K ep1 ep2
        else if (p + 1) = 5 then Phase5Transition L K ep1 ep2
        else if (p + 1) = 6 then Phase6Transition L K ep1 ep2
        else if (p + 1) = 7 then Phase7Transition L K ep1 ep2
        else Phase8Transition L K ep1 ep2).2) = stdCounterSubroutine L K ep2 := by
      rcases hq with h | h | h | h | h <;> rw [h]
      · rw [if_pos rfl]; unfold Phase1Transition
        have hnm : ¬ (ep1.role = .main ∧ ep2.role = .main) := by
          rintro ⟨_, h2⟩; rw [hepclock2] at h2; exact absurd h2 (by decide)
        simp only [hnm, if_false]
        rw [clockCounterStep, if_pos hepclock2]
      · rw [if_neg (by decide), if_pos rfl, Phase5Transition_right_clock _ _ hepclock2]
      · rw [if_neg (by decide), if_neg (by decide), if_pos rfl,
            Phase6Transition_right_clock _ _ hepclock2]
      · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl,
            Phase7Transition_right_clock _ _ hepclock2]
      · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
            Phase8Transition_right_clock _ _ hepclock2]
    rw [hred]
    exact seamClockSummand_stdCounterSubroutine_le p s hs ep2 hepclock2 hepdest2
  refine hdec.trans ?_
  -- Step 3: epidemic summand bound (right) → summand(ep2) ≤ summand(b) + freshVal.
  gcongr
  exact seamClockSummand_phaseEpidemicUpdate_right_le p s hq a b

/-! ### The ADVANCE-regime per-side bounds.

When `ep.1.phase = p` (one below the destination) the dispatch `Phase(p)Transition`
(selected by the LEFT phase) advances a clock INTO `p+1`.  For the LEFT output we route
through the per-phase left reductions (`Phase0Transition_left_clock_eq` for `p+1=1`;
`Phase{5,6,7}Transition_left_clock` for `p+1∈{6,7,8}`) + the advance reset lemma, giving
`summand = freshVal`.  The RIGHT output uses the same dispatch (`ep.1.phase = p`), with
the right reductions; here we additionally need `ep.2.phase = p` (so the responder is
the advancing clock) — supplied by the caller. -/

/-- **Advance-output summand ceiling.**  For a clock `chat` at phase `< p+1` and a
counter-reset destination `p+1 ∈ {1,6,7,8}`, `summand(stdCounterSubroutine chat) ≤
freshVal`: if it ADVANCES to `p+1` the new clock has a FULL counter (summand `=
freshVal`); if it stays below `p+1` (decrement branch) the output is not a clock at
`p+1` (summand `0`). -/
theorem seamClockSummand_stdCounterSubroutine_advance_le (p : ℕ) (s : ℝ)
    (chat : AgentState L K) (hrole : chat.role = .clock)
    (hq : CounterTimedPhase (p + 1)) (hlt : chat.phase.val < p + 1) :
    seamClockSummand (L := L) (K := K) p s (stdCounterSubroutine L K chat)
      ≤ freshVal (L := L) s := by
  by_cases hadv : (stdCounterSubroutine L K chat).phase.val = p + 1
  · rw [seamClockSummand_stdCounterSubroutine_advance p s chat hrole hadv hq hlt]
  · -- output not at p+1 ⇒ summand 0.
    have : seamClockSummand (L := L) (K := K) p s (stdCounterSubroutine L K chat) = 0 := by
      unfold seamClockSummand
      rw [if_neg]; rintro ⟨_, hp⟩; exact hadv hp
    rw [this]; exact zero_le'

/-- The full `Transition` LEFT output's seam summand equals that of the dispatch LEFT
output `out.1` (the `finishPhase10Entry` strip preserves `role`/`phase`/`counter`),
where the dispatch is selected by `ep.1.phase`.  Specialized to `ep.1.phase = p` for
the ADVANCE regime: the dispatch is `Phase(p)Transition`. -/
theorem seamClockSummand_Transition_left_eq_dispatch_advance (p : ℕ) (s : ℝ)
    (a b : AgentState L K)
    (hepsrc1 : (phaseEpidemicUpdate L K a b).1.phase.val = p)
    (hp : CounterResetDest (p + 1)) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
      = seamClockSummand (L := L) (K := K) p s
          ((if p = 0 then Phase0Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2
            else if p = 5 then Phase5Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2
            else if p = 6 then Phase6Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2
            else Phase7Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2).1) := by
  rw [Transition, seamClockSummand_finishPhase10Entry]
  rcases hp with h | h | h | h
  · have hp0 : p = 0 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨0, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp0])
    simp only [hpe, hp0]; rfl
  · have hp5 : p = 5 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨5, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp5])
    simp only [hpe, hp5]; rfl
  · have hp6 : p = 6 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨6, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp6])
    simp only [hpe, hp6]; rfl
  · have hp7 : p = 7 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨7, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp7])
    simp only [hpe, hp7]; rfl

/-- **LEFT-side ADVANCE per-side bound.**  When the epidemic-updated initiator `ep.1` is
a clock at phase `p` (one below the counter-reset destination `p+1 ∈ {1,6,7,8}`), the
dispatch advances it into `p+1` with a FULL counter, so the LEFT output summand is
`≤ freshVal ≤ eˢ·(summand a + freshVal)`. -/
theorem seamClockSummand_Transition_left_le_of_ep_advance (p : ℕ)
    (hq : CounterResetDest (p + 1)) (s : ℝ) (hs : 0 ≤ s) (a b : AgentState L K)
    (hepclock1 : (phaseEpidemicUpdate L K a b).1.role = .clock)
    (hepsrc1 : (phaseEpidemicUpdate L K a b).1.phase.val = p) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
      ≤ ENNReal.ofReal (Real.exp s)
          * (seamClockSummand (L := L) (K := K) p s a + freshVal (L := L) s) := by
  set ep1 := (phaseEpidemicUpdate L K a b).1 with hep1
  set ep2 := (phaseEpidemicUpdate L K a b).2 with hep2
  have hqT : CounterTimedPhase (p + 1) := CounterTimedPhase_of_CounterResetDest hq
  rw [seamClockSummand_Transition_left_eq_dispatch_advance p s a b hepsrc1 hq]
  -- get a clock `chat` at phase p with the dispatch.1 = stdCounterSubroutine chat or chat.
  have hdisp_summ : seamClockSummand (L := L) (K := K) p s
        ((if p = 0 then Phase0Transition L K ep1 ep2
          else if p = 5 then Phase5Transition L K ep1 ep2
          else if p = 6 then Phase6Transition L K ep1 ep2
          else Phase7Transition L K ep1 ep2).1)
      ≤ freshVal (L := L) s := by
    rcases hq with h | h | h | h
    · -- p = 0: Phase0Transition.1 = stdCounterSubroutine chat or chat (clock at phase 0).
      have hp0 : p = 0 := by omega
      rw [if_pos hp0]
      obtain ⟨chat, hcr, hcp, hdisj⟩ := Phase0Transition_left_clock_eq ep1 ep2 hepclock1
      have hcplt : chat.phase.val < p + 1 := by rw [hcp, hepsrc1]; omega
      rcases hdisj with hd | hd
      · rw [hd]
        exact seamClockSummand_stdCounterSubroutine_advance_le p s chat hcr hqT hcplt
      · rw [hd]
        -- chat at phase p ≠ p+1 ⇒ summand 0.
        have : seamClockSummand (L := L) (K := K) p s chat = 0 := by
          unfold seamClockSummand; rw [if_neg]; rintro ⟨_, hp⟩
          rw [hcp, hepsrc1] at hp; omega
        rw [this]; exact zero_le'
    · -- p = 5: Phase5Transition.1 = stdCounterSubroutine ep1.
      have hp5 : p = 5 := by omega
      rw [if_neg (by omega : ¬ p = 0), if_pos hp5]
      rw [Phase5Transition_left_clock ep1 ep2 hepclock1]
      have hlt : ep1.phase.val < p + 1 := by rw [hepsrc1]; omega
      exact seamClockSummand_stdCounterSubroutine_advance_le p s ep1 hepclock1 hqT hlt
    · have hp6 : p = 6 := by omega
      rw [if_neg (by omega : ¬ p = 0), if_neg (by omega : ¬ p = 5), if_pos hp6]
      rw [Phase6Transition_left_clock ep1 ep2 hepclock1]
      have hlt : ep1.phase.val < p + 1 := by rw [hepsrc1]; omega
      exact seamClockSummand_stdCounterSubroutine_advance_le p s ep1 hepclock1 hqT hlt
    · have hp7 : p = 7 := by omega
      rw [if_neg (by omega : ¬ p = 0), if_neg (by omega : ¬ p = 5),
          if_neg (by omega : ¬ p = 6)]
      rw [Phase7Transition_left_clock ep1 ep2 hepclock1]
      have hlt : ep1.phase.val < p + 1 := by rw [hepsrc1]; omega
      exact seamClockSummand_stdCounterSubroutine_advance_le p s ep1 hepclock1 hqT hlt
  exact hdisp_summ.trans (freshVal_le_exp_mul_add s hs _)

/-- Dispatch-strip for the RIGHT output in the ADVANCE regime (`ep.1.phase = p`). -/
theorem seamClockSummand_Transition_right_eq_dispatch_advance (p : ℕ) (s : ℝ)
    (a b : AgentState L K)
    (hepsrc1 : (phaseEpidemicUpdate L K a b).1.phase.val = p)
    (hp : CounterResetDest (p + 1)) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
      = seamClockSummand (L := L) (K := K) p s
          ((if p = 0 then Phase0Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2
            else if p = 5 then Phase5Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2
            else if p = 6 then Phase6Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2
            else Phase7Transition L K (phaseEpidemicUpdate L K a b).1
                                              (phaseEpidemicUpdate L K a b).2).2) := by
  rw [Transition, seamClockSummand_finishPhase10Entry]
  rcases hp with h | h | h | h
  · have hp0 : p = 0 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨0, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp0])
    simp only [hpe, hp0]; rfl
  · have hp5 : p = 5 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨5, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp5])
    simp only [hpe, hp5]; rfl
  · have hp6 : p = 6 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨6, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp6])
    simp only [hpe, hp6]; rfl
  · have hp7 : p = 7 := by omega
    have hpe : (phaseEpidemicUpdate L K a b).1.phase = (⟨7, by decide⟩ : Fin 11) :=
      Fin.ext (by rw [hepsrc1, hp7])
    simp only [hpe, hp7]; rfl

/-- **RIGHT-side ADVANCE per-side bound.**  When the dispatch is selected by `ep.1.phase
= p` and the responder `ep.2` is a clock at phase `p` (one below the counter-reset
destination `p+1 ∈ {1,6,7,8}`), the dispatch advances `ep.2` into `p+1` with a FULL
counter, so the RIGHT output summand is `≤ freshVal ≤ eˢ·(summand b + freshVal)`. -/
theorem seamClockSummand_Transition_right_le_of_ep_advance (p : ℕ)
    (hq : CounterResetDest (p + 1)) (s : ℝ) (hs : 0 ≤ s) (a b : AgentState L K)
    (hepsrc1 : (phaseEpidemicUpdate L K a b).1.phase.val = p)
    (hepclock2 : (phaseEpidemicUpdate L K a b).2.role = .clock)
    (hepsrc2 : (phaseEpidemicUpdate L K a b).2.phase.val = p) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
      ≤ ENNReal.ofReal (Real.exp s)
          * (seamClockSummand (L := L) (K := K) p s b + freshVal (L := L) s) := by
  set ep1 := (phaseEpidemicUpdate L K a b).1 with hep1
  set ep2 := (phaseEpidemicUpdate L K a b).2 with hep2
  have hqT : CounterTimedPhase (p + 1) := CounterTimedPhase_of_CounterResetDest hq
  rw [seamClockSummand_Transition_right_eq_dispatch_advance p s a b hepsrc1 hq]
  have hlt2 : ep2.phase.val < p + 1 := by rw [hepsrc2]; omega
  have hdisp_summ : seamClockSummand (L := L) (K := K) p s
        ((if p = 0 then Phase0Transition L K ep1 ep2
          else if p = 5 then Phase5Transition L K ep1 ep2
          else if p = 6 then Phase6Transition L K ep1 ep2
          else Phase7Transition L K ep1 ep2).2)
      ≤ freshVal (L := L) s := by
    rcases hq with h | h | h | h
    · have hp0 : p = 0 := by omega
      rw [if_pos hp0]
      obtain ⟨chat, hcr, hcp, hdisj⟩ := Phase0Transition_right_clock_eq ep1 ep2 hepclock2
      have hcplt : chat.phase.val < p + 1 := by rw [hcp, hepsrc2]; omega
      rcases hdisj with hd | hd
      · rw [hd]
        exact seamClockSummand_stdCounterSubroutine_advance_le p s chat hcr hqT hcplt
      · rw [hd]
        have : seamClockSummand (L := L) (K := K) p s chat = 0 := by
          unfold seamClockSummand; rw [if_neg]; rintro ⟨_, hp⟩
          rw [hcp, hepsrc2] at hp; omega
        rw [this]; exact zero_le'
    · have hp5 : p = 5 := by omega
      rw [if_neg (by omega : ¬ p = 0), if_pos hp5]
      rw [Phase5Transition_right_clock ep1 ep2 hepclock2]
      exact seamClockSummand_stdCounterSubroutine_advance_le p s ep2 hepclock2 hqT hlt2
    · have hp6 : p = 6 := by omega
      rw [if_neg (by omega : ¬ p = 0), if_neg (by omega : ¬ p = 5), if_pos hp6]
      rw [Phase6Transition_right_clock ep1 ep2 hepclock2]
      exact seamClockSummand_stdCounterSubroutine_advance_le p s ep2 hepclock2 hqT hlt2
    · have hp7 : p = 7 := by omega
      rw [if_neg (by omega : ¬ p = 0), if_neg (by omega : ¬ p = 5),
          if_neg (by omega : ¬ p = 6)]
      rw [Phase7Transition_right_clock ep1 ep2 hepclock2]
      exact seamClockSummand_stdCounterSubroutine_advance_le p s ep2 hepclock2 hqT hlt2
  exact hdisp_summ.trans (freshVal_le_exp_mul_add s hs _)

/-! ## Stage 2 — the HONEST two-sided per-pair bound with constant `2·eˢ·freshVal`.

The per-side bounds proved above (no-advance: `…_le_of_ep_at_dest`; advance:
`…_le_of_ep_advance`) each deliver `summand(side) ≤ eˢ·(summand(source) + freshVal)`
under the side's regime hypothesis.  Adding the two sides gives the HONEST pair ceiling
`eˢ·(summand a + summand b) + 2·eˢ·freshVal` — the `2·eˢ` (NOT `2`) immigration
constant, because each immigrant clock enters `p+1` at the FULL counter (summand
`freshVal`) and is then DECREMENTED by the same dispatch (the `eˢ` factor multiplies the
`freshVal` immigration, not just the source summand).

The regime that fires per side is determined by `ep.side.phase` relative to `p+1`: the
epidemic output phase is `≥ max(a.phase, b.phase)` and a clock entering or staying in
`p+1` ∈ {1,6,7,8} either was already there (no-advance, `ep.side.phase = p+1`) or got
counter-advanced from `p` (advance, `ep.side.phase = p`).  We package the regime facts a
caller must supply as `SeamRegimeDispatch`; the drift consumer (Stage 3) threads it. -/

/-- **Universal LEFT per-side bound** (both regimes packaged).  Supplied the regime fact
for the LEFT output — either `ep.1` is a clock at the destination `p+1` (no-advance), or
`ep.1` is a clock at `p` (advance), or the LEFT output is simply not a clock at `p+1`
(summand `0`) — the LEFT output summand satisfies the honest per-side ceiling
`≤ eˢ·(summand a + freshVal)`. -/
theorem seamClockSummand_Transition_left_le_univ (p : ℕ)
    (hq : CounterResetDest (p + 1)) (s : ℝ) (hs : 0 ≤ s) (a b : AgentState L K)
    (hregime :
      ((phaseEpidemicUpdate L K a b).1.role = .clock
          ∧ (phaseEpidemicUpdate L K a b).1.phase.val = p + 1)
      ∨ ((phaseEpidemicUpdate L K a b).1.role = .clock
          ∧ (phaseEpidemicUpdate L K a b).1.phase.val = p)
      ∨ ¬ ((Transition L K a b).1.role = .clock
          ∧ (Transition L K a b).1.phase.val = p + 1)) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
      ≤ ENNReal.ofReal (Real.exp s)
          * (seamClockSummand (L := L) (K := K) p s a + freshVal (L := L) s) := by
  have hqT : CounterTimedPhase (p + 1) := CounterTimedPhase_of_CounterResetDest hq
  rcases hregime with ⟨hrole, hdest⟩ | ⟨hrole, hsrc⟩ | hnot
  · exact seamClockSummand_Transition_left_le_of_ep_at_dest p hqT s hs a b hdest hrole
  · exact seamClockSummand_Transition_left_le_of_ep_advance p hq s hs a b hrole hsrc
  · have h0 : seamClockSummand (L := L) (K := K) p s (Transition L K a b).1 = 0 := by
      unfold seamClockSummand; rw [if_neg hnot]
    rw [h0]; exact zero_le'

/-- **Universal RIGHT per-side bound** (both regimes packaged).  Symmetric to the LEFT
universal bound.  The no-advance regime additionally needs `ep.1.phase = p+1` (the
`Transition` dispatcher selects `Phase(p+1)Transition` by the LEFT phase), supplied in
the no-advance branch of `hregime`. -/
theorem seamClockSummand_Transition_right_le_univ (p : ℕ)
    (hq : CounterResetDest (p + 1)) (s : ℝ) (hs : 0 ≤ s) (a b : AgentState L K)
    (hregime :
      ((phaseEpidemicUpdate L K a b).1.phase.val = p + 1
          ∧ (phaseEpidemicUpdate L K a b).2.phase.val = p + 1
          ∧ (phaseEpidemicUpdate L K a b).2.role = .clock)
      ∨ ((phaseEpidemicUpdate L K a b).1.phase.val = p
          ∧ (phaseEpidemicUpdate L K a b).2.role = .clock
          ∧ (phaseEpidemicUpdate L K a b).2.phase.val = p)
      ∨ ¬ ((Transition L K a b).2.role = .clock
          ∧ (Transition L K a b).2.phase.val = p + 1)) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
      ≤ ENNReal.ofReal (Real.exp s)
          * (seamClockSummand (L := L) (K := K) p s b + freshVal (L := L) s) := by
  have hqT : CounterTimedPhase (p + 1) := CounterTimedPhase_of_CounterResetDest hq
  rcases hregime with ⟨hd1, hd2, hr2⟩ | ⟨hs1, hr2, hs2⟩ | hnot
  · exact seamClockSummand_Transition_right_le_of_ep_at_dest p hqT s hs a b hd1 hd2 hr2
  · exact seamClockSummand_Transition_right_le_of_ep_advance p hq s hs a b hs1 hr2 hs2
  · have h0 : seamClockSummand (L := L) (K := K) p s (Transition L K a b).2 = 0 := by
      unfold seamClockSummand; rw [if_neg hnot]
    rw [h0]; exact zero_le'

/-- **The seam regime dispatch predicate.**  For a counter-reset destination `p+1 ∈
{1,6,7,8}`, every interacting pair `(a,b)` falls, on each side, into one of the three
exhaustive regimes (no-advance / advance / not-a-clock-at-`p+1`) that the universal
per-side bounds consume.  This is the protocol-structural input the drift needs
unconditionally; it is the seam analogue of the FROZEN dispatcher case analysis behind
`Phase0Window.clockSummand_pair_le`, restricted to a counter-reset destination phase,
and is discharged per-seam from the kernel's phase-monotonicity (an output clock at
`p+1` came from a source clock at `p` or `p+1`) — the same magnitude as the carried
`DetSeamOvershootBridge`. -/
def SeamRegimeDispatch (p : ℕ) : Prop :=
  ∀ a b : AgentState L K,
    (((phaseEpidemicUpdate L K a b).1.role = .clock
        ∧ (phaseEpidemicUpdate L K a b).1.phase.val = p + 1)
      ∨ ((phaseEpidemicUpdate L K a b).1.role = .clock
          ∧ (phaseEpidemicUpdate L K a b).1.phase.val = p)
      ∨ ¬ ((Transition L K a b).1.role = .clock
          ∧ (Transition L K a b).1.phase.val = p + 1))
    ∧ (((phaseEpidemicUpdate L K a b).1.phase.val = p + 1
        ∧ (phaseEpidemicUpdate L K a b).2.phase.val = p + 1
        ∧ (phaseEpidemicUpdate L K a b).2.role = .clock)
      ∨ ((phaseEpidemicUpdate L K a b).1.phase.val = p
          ∧ (phaseEpidemicUpdate L K a b).2.role = .clock
          ∧ (phaseEpidemicUpdate L K a b).2.phase.val = p)
      ∨ ¬ ((Transition L K a b).2.role = .clock
          ∧ (Transition L K a b).2.phase.val = p + 1))

/-- **The HONEST two-sided per-pair bound** (the Stage-2 capstone).  Summing the two
universal per-side bounds gives the honest pair ceiling with immigration `2·eˢ·freshVal`:

  `summand((Transition a b).1) + summand((Transition a b).2)
      ≤ eˢ·(summand a + summand b) + 2·eˢ·freshVal`.

This is the corrected `hpair` (the consumer chain's `2·freshVal` is FALSE for `s > 0`;
see `SeamPairBound`'s finding 1).  Requires the regime dispatch `SeamRegimeDispatch p`
for the pair. -/
theorem seamClockSummand_Transition_pair_le (p : ℕ)
    (hq : CounterResetDest (p + 1)) (s : ℝ) (hs : 0 ≤ s)
    (hdisp : SeamRegimeDispatch (L := L) (K := K) p) (a b : AgentState L K) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
      + seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
      ≤ ENNReal.ofReal (Real.exp s)
          * (seamClockSummand (L := L) (K := K) p s a
             + seamClockSummand (L := L) (K := K) p s b)
        + 2 * (ENNReal.ofReal (Real.exp s) * freshVal (L := L) s) := by
  obtain ⟨hregL, hregR⟩ := hdisp a b
  have hL := seamClockSummand_Transition_left_le_univ p hq s hs a b hregL
  have hR := seamClockSummand_Transition_right_le_univ p hq s hs a b hregR
  calc seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
        + seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
      ≤ ENNReal.ofReal (Real.exp s)
            * (seamClockSummand (L := L) (K := K) p s a + freshVal (L := L) s)
          + ENNReal.ofReal (Real.exp s)
            * (seamClockSummand (L := L) (K := K) p s b + freshVal (L := L) s) :=
        add_le_add hL hR
    _ = ENNReal.ofReal (Real.exp s)
            * (seamClockSummand (L := L) (K := K) p s a
               + seamClockSummand (L := L) (K := K) p s b)
          + 2 * (ENNReal.ofReal (Real.exp s) * freshVal (L := L) s) := by
        rw [mul_add, mul_add]; ring

/-! ## Stage 3 — the corrected configuration-level drift with `b = 2·eˢ·freshVal`.

`SeamNoOvershoot.seamClockPotential_drift_affine` consumed a `hpair` with the WRONG
constant `2·freshVal` and produced drift `+ 2·freshVal`.  We re-derive the drift with a
GENERIC additive immigration `bImm`, then instantiate it at the honest
`bImm = 2·(eˢ·freshVal)` via the Stage-2 pair bound.  The body mirrors
`SeamNoOvershoot`'s derivation verbatim (the base-split lemmas, `_eq_base_add_pair`, and
the `lintegral_transitionKernel_eq_sum` pair-sum expansion are all reusable as-is — only
the immigration constant differs), so this is a clean re-instantiation, not a re-proof. -/

/-- **Generic per-pair → additive-bump split** (immigration `bImm` arbitrary).  Clone of
`SeamNoOvershoot.seamClockPotential_stepOrSelf_le` with the literal `2·freshVal` replaced
by a generic `bImm`.  The base-split lemmas it uses (`…_eq_base_add_pair`,
`…_stepOrSelf_eq_base_add_pair`) are immigration-agnostic. -/
theorem seamClockPotential_stepOrSelf_le_gen (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (bImm : ℝ≥0∞) (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hpair : ∀ a b : AgentState L K,
      seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
        + seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
        ≤ ENNReal.ofReal (Real.exp s)
            * (seamClockSummand (L := L) (K := K) p s a
               + seamClockSummand (L := L) (K := K) p s b)
          + bImm) :
    seamClockPotential (L := L) (K := K) p s
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ seamClockPotential (L := L) (K := K) p s c
        + ENNReal.ofReal (Real.exp s - 1)
            * (seamClockSummand (L := L) (K := K) p s r₁
               + seamClockSummand (L := L) (K := K) p s r₂)
        + bImm := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c := happ
    rw [seamClockPotential_stepOrSelf_eq_base_add_pair p s c r₁ r₂ happ]
    rw [seamClockPotential_eq_base_add_pair p s c r₁ r₂ hle]
    set base := Config.sumOf (seamClockSummand (L := L) (K := K) p s) (c - {r₁, r₂})
    set S := seamClockSummand (L := L) (K := K) p s r₁
      + seamClockSummand (L := L) (K := K) p s r₂
    have hpair' := hpair r₁ r₂
    have hofeq : ENNReal.ofReal (Real.exp s) = 1 + ENNReal.ofReal (Real.exp s - 1) := by
      rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) (by linarith [Real.one_le_exp hs])]
      congr 1; ring
    have hexp_split : ENNReal.ofReal (Real.exp s) * S
        = S + ENNReal.ofReal (Real.exp s - 1) * S := by
      rw [hofeq, add_mul, one_mul]
    calc base + (seamClockSummand (L := L) (K := K) p s (Transition L K r₁ r₂).1
            + seamClockSummand (L := L) (K := K) p s (Transition L K r₁ r₂).2)
        ≤ base + (ENNReal.ofReal (Real.exp s) * S + bImm) := by gcongr
      _ = base + (S + ENNReal.ofReal (Real.exp s - 1) * S + bImm) := by rw [hexp_split]
      _ = base + S + ENNReal.ofReal (Real.exp s - 1) * S + bImm := by ring
  · rw [Protocol.stepOrSelf, if_neg happ]
    calc seamClockPotential (L := L) (K := K) p s c
        ≤ seamClockPotential (L := L) (K := K) p s c
          + ENNReal.ofReal (Real.exp s - 1)
              * (seamClockSummand (L := L) (K := K) p s r₁
                 + seamClockSummand (L := L) (K := K) p s r₂) :=
          le_add_right le_rfl
      _ ≤ _ := le_add_right le_rfl

/-- **The corrected affine one-step drift** (immigration `bImm` arbitrary).  Clone of
`SeamNoOvershoot.seamClockPotential_drift_affine` with the generic immigration; the
pair-sum collapse via `lintegral_transitionKernel_eq_sum` + `sum_fst/snd_interactionProb`
is verbatim.  Instantiated at `bImm = 2·(eˢ·freshVal)` (Stage 2) it is the HONEST drift. -/
theorem seamClockPotential_drift_affine_gen (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (bImm : ℝ≥0∞) (n : ℕ) (c : Config (AgentState L K))
    (hcard : Multiset.card c = n) (hc2 : 2 ≤ Multiset.card c)
    (hpair : ∀ a b : AgentState L K,
      seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
        + seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
        ≤ ENNReal.ofReal (Real.exp s)
            * (seamClockSummand (L := L) (K := K) p s a
               + seamClockSummand (L := L) (K := K) p s b)
          + bImm) :
    ∫⁻ c', seamClockPotential (L := L) (K := K) p s c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
          * seamClockPotential (L := L) (K := K) p s c
        + bImm := by
  classical
  set Φ := seamClockPotential (L := L) (K := K) p s c with hΦ
  rw [Phase0Window.lintegral_transitionKernel_eq_sum (NonuniformMajority L K) c hc2]
  have hpp : ∀ pair : AgentState L K × AgentState L K,
      seamClockPotential (L := L) (K := K) p s
          (Protocol.stepOrSelf (NonuniformMajority L K) c pair.1 pair.2)
        * c.interactionProb pair.1 pair.2
      ≤ (Φ + ENNReal.ofReal (Real.exp s - 1)
            * (seamClockSummand (L := L) (K := K) p s pair.1
               + seamClockSummand (L := L) (K := K) p s pair.2) + bImm)
          * c.interactionProb pair.1 pair.2 := by
    intro pair
    gcongr
    exact seamClockPotential_stepOrSelf_le_gen p s hs bImm c pair.1 pair.2 hpair
  refine le_trans (Finset.sum_le_sum (fun pair _ => hpp pair)) ?_
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsumprob : (∑ pair : AgentState L K × AgentState L K,
      c.interactionProb pair.1 pair.2) = 1 := by
    have := (c.interactionPMF hc2).tsum_coe
    rw [tsum_eq_sum (s := Finset.univ) (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at this
    convert this using 1
  have hΦsum : (∑ pair : AgentState L K × AgentState L K,
      Φ * c.interactionProb pair.1 pair.2) = Φ := by
    rw [← Finset.mul_sum, hsumprob, mul_one]
  have hMsum : (∑ pair : AgentState L K × AgentState L K,
      bImm * c.interactionProb pair.1 pair.2) = bImm := by
    rw [← Finset.mul_sum, hsumprob, mul_one]
  have hmid : (∑ pair : AgentState L K × AgentState L K,
      ENNReal.ofReal (Real.exp s - 1)
        * (seamClockSummand (L := L) (K := K) p s pair.1
           + seamClockSummand (L := L) (K := K) p s pair.2)
        * c.interactionProb pair.1 pair.2)
      = ENNReal.ofReal (Real.exp s - 1) * (Φ / (n : ℝ≥0∞) + Φ / (n : ℝ≥0∞)) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    have hsplit : ∀ pair : AgentState L K × AgentState L K,
        (seamClockSummand (L := L) (K := K) p s pair.1
           + seamClockSummand (L := L) (K := K) p s pair.2)
          * c.interactionProb pair.1 pair.2
          = seamClockSummand (L := L) (K := K) p s pair.1 * c.interactionProb pair.1 pair.2
            + seamClockSummand (L := L) (K := K) p s pair.2 * c.interactionProb pair.1 pair.2 := by
      intro pair; rw [add_mul]
    rw [Finset.sum_congr rfl (fun pair _ => hsplit pair), Finset.sum_add_distrib]
    rw [Phase0Window.sum_fst_interactionProb c hc2 (seamClockSummand (L := L) (K := K) p s),
        Phase0Window.sum_snd_interactionProb c hc2 (seamClockSummand (L := L) (K := K) p s)]
    rw [hcard]; rfl
  rw [hΦsum, hMsum, hmid]
  refine le_of_eq ?_
  congr 1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 2 ≤ n := by rw [← hcard]; exact hc2
    exact_mod_cast (by omega : 0 < n)
  have hnne : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by positivity : (n:ℝ) ≠ 0)
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have he1 : (0 : ℝ) ≤ Real.exp s - 1 := by linarith [Real.one_le_exp hs]
  have hofac : ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
      = 1 + ENNReal.ofReal (Real.exp s - 1) * ((2 : ℝ≥0∞) / (n : ℝ≥0∞)) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity)]
    rw [ENNReal.ofReal_one]
    congr 1
    rw [show 2 * (Real.exp s - 1) / (n : ℝ) = (Real.exp s - 1) * (2 / (n : ℝ)) by ring]
    rw [ENNReal.ofReal_mul he1]
    congr 1
    rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast]
    norm_num
  rw [hofac, add_mul, one_mul]
  congr 1
  rw [mul_assoc]
  congr 1
  rw [ENNReal.div_add_div_same, ← two_mul]
  rw [mul_comm (2 : ℝ≥0∞) Φ, mul_div_assoc, mul_comm ((2:ℝ≥0∞)/(n:ℝ≥0∞)) Φ,
      ← mul_div_assoc]

/-- **The HONEST configuration-level drift** (immigration `2·eˢ·freshVal`).  The Stage-3
capstone: feeding the Stage-2 honest pair bound (`seamClockSummand_Transition_pair_le`,
which carries immigration `2·(eˢ·freshVal)`) into the generic drift gives the corrected
affine one-step drift for the seam clock potential on the counter-reset destination set
`{1,6,7,8}`:

  `∫ Φ_s dK(c) ≤ ofReal(1 + 2(eˢ−1)/n)·Φ_s(c) + 2·eˢ·e^{−s·50(L+1)}`.

This replaces `SeamNoOvershoot.seamClockPotential_drift_affine`'s `+ 2·freshVal` (which
is FALSE for `s > 0`). -/
theorem seamClockPotential_drift_affine_honest (p : ℕ)
    (hq : CounterResetDest (p + 1)) (s : ℝ) (hs : 0 ≤ s)
    (hdisp : SeamRegimeDispatch (L := L) (K := K) p)
    (n : ℕ) (c : Config (AgentState L K))
    (hcard : Multiset.card c = n) (hc2 : 2 ≤ Multiset.card c) :
    ∫⁻ c', seamClockPotential (L := L) (K := K) p s c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
          * seamClockPotential (L := L) (K := K) p s c
        + 2 * (ENNReal.ofReal (Real.exp s) * freshVal (L := L) s) :=
  seamClockPotential_drift_affine_gen p s hs
    (2 * (ENNReal.ofReal (Real.exp s) * freshVal (L := L) s)) n c hcard hc2
    (fun a b => seamClockSummand_Transition_pair_le p hq s hs hdisp a b)

/-! ## Stage 4 — the corrected numerics (`b = 2·e·e^{−50(L+1)}` at `s = 1`) and the
end-to-end honest per-seam no-overshoot tail.

The honest immigration at `s = 1` is `b = 2·e·e^{−50(L+1)}` (the extra `eˢ = e` over the
predecessor's `2·e^{−50(L+1)}`).  We re-run the tail arithmetic with this constant and
VERIFY it still closes to `e^{−40(L+1)}` (the predecessor's optimism is correct): the
immigration term picks up one constant factor `e = exp 1`, absorbed by the huge slack
between `e^{−50(L+1)}` and the target — the term-2 exponent moves from `−43(L+1)` to
`−42(L+1)` (`exp 1 · exp(2(L+1)) ≤ exp(3(L+1))` for `L+1 ≥ 1`), and `e^{−45}+e^{−42} ≤
e^{−40}` still holds since `2 ≤ e^{2(L+1)}`. -/

/-- **The HONEST seam no-overshoot numerics (real, `s = 1`).**  Identical to
`SeamNoOvershoot.seam_noOvershoot_numerics_real` except the immigration coefficient is the
honest `2·e` (not `2`).  Still closes to `e^{−40(L+1)}`.  Requires `n ≥ 1`,
`ln n ≤ (L+1)`, `t ≤ n(L+1)`. -/
theorem seam_noOvershoot_numerics_honest (n L t : ℕ) (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) (ht : t ≤ n * (L + 1)) :
    (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ t
        * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
      + (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
          * (∑ i ∈ Finset.range t, (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i)
      ≤ Real.exp (-(40 * (L + 1) : ℕ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  set x : ℝ := 2 * (Real.exp 1 - 1) / (n : ℝ) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have ha1 : (1 : ℝ) ≤ 1 + x := by linarith
  have hLpos : (0 : ℝ) ≤ (L + 1 : ℕ) := by positivity
  have hM1 : (1 : ℝ) ≤ (L + 1 : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hepos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  -- (1+x)^t ≤ exp(2(e−1)(L+1))
  have hstep1 : (1 + x) ^ t ≤ Real.exp ((t : ℝ) * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by rw [add_comm]; exact Real.add_one_le_exp x) t
  have htx : (t : ℝ) * x ≤ 2 * (Real.exp 1 - 1) * (L + 1 : ℕ) := by
    have htn : (t : ℝ) ≤ (n : ℝ) * (L + 1 : ℕ) := by
      have : (t : ℝ) ≤ ((n * (L + 1) : ℕ) : ℝ) := by exact_mod_cast ht
      rwa [Nat.cast_mul] at this
    rw [hx,
      show (t : ℝ) * (2 * (Real.exp 1 - 1) / (n : ℝ))
          = (2 * (Real.exp 1 - 1)) * ((t : ℝ) / (n : ℝ)) by ring]
    have hdiv : (t : ℝ) / (n : ℝ) ≤ (L + 1 : ℕ) := by
      rw [div_le_iff₀ hnpos, mul_comm]; exact htn
    have h2e : 0 ≤ 2 * (Real.exp 1 - 1) := by linarith
    calc (2 * (Real.exp 1 - 1)) * ((t : ℝ) / (n : ℝ))
        ≤ (2 * (Real.exp 1 - 1)) * (L + 1 : ℕ) := mul_le_mul_of_nonneg_left hdiv h2e
      _ = 2 * (Real.exp 1 - 1) * (L + 1 : ℕ) := rfl
  have hpowt : (1 + x) ^ t ≤ Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ)) :=
    le_trans hstep1 (Real.exp_le_exp.mpr htx)
  have hpow_nonneg : (0 : ℝ) ≤ (1 + x) ^ t := by positivity
  have hn_exp : (n : ℝ) ≤ Real.exp (L + 1 : ℕ) := by
    calc (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hnpos).symm
      _ ≤ Real.exp (L + 1 : ℕ) := Real.exp_le_exp.mpr hlog
  -- term 1: aᵗ·Φ₀ ≤ exp(-45(L+1))  (Phase-0 numerics verbatim)
  have hterm1 : (1 + x) ^ t * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
      ≤ Real.exp (-(45 * (L + 1) : ℕ)) := by
    have := Phase0Window.phase0_numerics_real n L t hn hlog ht
    rwa [← hx] at this
  -- term 2: (2·e)·e^{−50(L+1)}·∑ ≤ exp(-42(L+1))
  have hsum_le : (∑ i ∈ Finset.range t, (1 + x) ^ i) ≤ (t : ℝ) * (1 + x) ^ t := by
    calc (∑ i ∈ Finset.range t, (1 + x) ^ i)
        ≤ ∑ _i ∈ Finset.range t, (1 + x) ^ t := by
          apply Finset.sum_le_sum
          intro i hi
          exact pow_le_pow_right₀ ha1 (le_of_lt (Finset.mem_range.mp hi))
      _ = (t : ℝ) * (1 + x) ^ t := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hb_nonneg : (0 : ℝ) ≤ 2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)) := by positivity
  have hterm2 : (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
        * (∑ i ∈ Finset.range t, (1 + x) ^ i)
      ≤ Real.exp (-(42 * (L + 1) : ℕ)) := by
    have htR : (t : ℝ) ≤ (n : ℝ) * (L + 1 : ℕ) := by
      have : (t : ℝ) ≤ ((n * (L + 1) : ℕ) : ℝ) := by exact_mod_cast ht
      rwa [Nat.cast_mul] at this
    calc (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
            * (∑ i ∈ Finset.range t, (1 + x) ^ i)
        ≤ (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ))) * ((t : ℝ) * (1 + x) ^ t) :=
          mul_le_mul_of_nonneg_left hsum_le hb_nonneg
      _ ≤ (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
            * (((n : ℝ) * (L + 1 : ℕ)) * Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ))) := by
          apply mul_le_mul_of_nonneg_left _ hb_nonneg
          apply mul_le_mul htR hpowt hpow_nonneg
          positivity
      _ ≤ (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
            * ((Real.exp (L + 1 : ℕ) * (L + 1 : ℕ))
                * Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ))) := by
          apply mul_le_mul_of_nonneg_left _ hb_nonneg
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hn_exp hLpos
      _ ≤ Real.exp (-(42 * (L + 1) : ℕ)) := by
          -- collect: 2·e·(L+1) ≤ exp(3(L+1)); combine exponents −50+1+2(e−1) ≤ −45
          rw [show (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
                * ((Real.exp (L + 1 : ℕ) * (L + 1 : ℕ))
                    * Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ)))
              = (2 * Real.exp 1 * (L + 1 : ℕ)) * (Real.exp (-(50 * (L + 1) : ℕ))
                  * Real.exp (L + 1 : ℕ) * Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ))) by ring]
          rw [← Real.exp_add, ← Real.exp_add]
          have hexp_arg : -(50 * (L + 1) : ℕ) + (L + 1 : ℕ) + 2 * (Real.exp 1 - 1) * (L + 1 : ℕ)
              ≤ -(45 * (L + 1) : ℕ) := by
            push_cast
            nlinarith [hLpos, he3]
          -- 2·e·(L+1) ≤ 6·(L+1) ≤ exp(3(L+1))
          have hcoef : (2 * Real.exp 1 * (L + 1 : ℕ) : ℝ) ≤ Real.exp (3 * (L + 1 : ℕ)) := by
            have hle6 : (2 * Real.exp 1 * (L + 1 : ℕ) : ℝ) ≤ 6 * (L + 1 : ℕ) := by
              nlinarith [hLpos, he3]
            have hexp3 : (6 * (L + 1 : ℕ) : ℝ) ≤ Real.exp (3 * (L + 1 : ℕ)) := by
              -- exp(3M) = exp(M)·exp(2M) ≥ (1+M)(1+2M) = 1+3M+2M² ≥ 6M for M ≥ 1.
              have hM := Real.add_one_le_exp ((L + 1 : ℕ) : ℝ)
              have h2M := Real.add_one_le_exp (2 * ((L + 1 : ℕ) : ℝ))
              have hpos1 : (0 : ℝ) ≤ Real.exp ((L + 1 : ℕ) : ℝ) := (Real.exp_pos _).le
              have hsplit : Real.exp (3 * (L + 1 : ℕ))
                  = Real.exp ((L + 1 : ℕ) : ℝ) * Real.exp (2 * ((L + 1 : ℕ) : ℝ)) := by
                rw [← Real.exp_add]; congr 1; push_cast; ring
              rw [hsplit]
              nlinarith [hLpos, hM1, hM, h2M, hpos1]
            linarith
          calc (2 * Real.exp 1 * (L + 1 : ℕ) : ℝ)
                * Real.exp (-(50 * (L + 1) : ℕ) + (L + 1 : ℕ)
                    + 2 * (Real.exp 1 - 1) * (L + 1 : ℕ))
              ≤ Real.exp (3 * (L + 1 : ℕ)) * Real.exp (-(45 * (L + 1) : ℕ)) := by
                apply mul_le_mul hcoef (Real.exp_le_exp.mpr hexp_arg) (Real.exp_nonneg _)
                  (Real.exp_nonneg _)
            _ = Real.exp (3 * (L + 1 : ℕ) + -(45 * (L + 1) : ℕ)) := by rw [← Real.exp_add]
            _ ≤ Real.exp (-(42 * (L + 1) : ℕ)) := by
                apply Real.exp_le_exp.mpr; push_cast; nlinarith [hLpos]
  -- combine: e^{−45} + e^{−42} ≤ e^{−40}
  calc (1 + x) ^ t * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
        + (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
            * (∑ i ∈ Finset.range t, (1 + x) ^ i)
      ≤ Real.exp (-(45 * (L + 1) : ℕ)) + Real.exp (-(42 * (L + 1) : ℕ)) :=
        add_le_add hterm1 hterm2
    _ ≤ Real.exp (-(40 * (L + 1) : ℕ)) := by
        -- e^{−45M} ≤ e^{−42M}, then 2·e^{−42M} ≤ e^{−40M} since 2 ≤ e^{2M}
        have h45_42 : Real.exp (-(45 * (L + 1) : ℕ)) ≤ Real.exp (-(42 * (L + 1) : ℕ)) := by
          apply Real.exp_le_exp.mpr; push_cast; nlinarith [hLpos]
        have h2 : Real.exp (-(42 * (L + 1) : ℕ)) + Real.exp (-(42 * (L + 1) : ℕ))
            ≤ Real.exp (-(40 * (L + 1) : ℕ)) := by
          rw [← two_mul]
          have hexp2 : (2 : ℝ) ≤ Real.exp (2 * (L + 1 : ℕ)) := by
            have := Real.add_one_le_exp (2 * ((L + 1 : ℕ) : ℝ))
            nlinarith [hLpos, hM1]
          calc (2 : ℝ) * Real.exp (-(42 * (L + 1) : ℕ))
              ≤ Real.exp (2 * (L + 1 : ℕ)) * Real.exp (-(42 * (L + 1) : ℕ)) :=
                mul_le_mul_of_nonneg_right hexp2 (Real.exp_nonneg _)
            _ = Real.exp (2 * (L + 1 : ℕ) + -(42 * (L + 1) : ℕ)) := by rw [← Real.exp_add]
            _ ≤ Real.exp (-(40 * (L + 1) : ℕ)) := by
                apply Real.exp_le_exp.mpr; push_cast; nlinarith [hLpos]
        linarith [h45_42, h2]

set_option maxHeartbeats 800000 in
/-- **Wide-window honest seam no-overshoot numerics (`t ≤ 12·n(L+1)`).**  The genuine Janson seam window
`seamJansonT2 ≤ 12n(L+1)` costs the `(1+x)^t` factor `24(e−1)(L+1)` instead of `2(e−1)(L+1)`, dropping the
achievable at-risk tail from `exp(−40(L+1))` to `exp(−5(L+1))` — still `≤ n^{−5}`, so the final `εovershoot`
fit needs only `24(L+1) ≤ n²` (trivial).  Needs `42 ≤ L+1` (regime `L = ⌈log₂ n⌉ ≥ 133`) to absorb the
`24e(L+1)` polynomial via the CUBE `(1+M/3)³ ≤ exp(M)`.  Term1 `≤ exp(−7(L+1))` (wide Phase-0), term2
`≤ exp(−6(L+1))`. -/
theorem seam_noOvershoot_numerics_honest_wide (n L t : ℕ) (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) (hLbig : 42 ≤ L + 1) (ht : t ≤ 12 * n * (L + 1)) :
    (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ t
        * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
      + (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
          * (∑ i ∈ Finset.range t, (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i)
      ≤ Real.exp (-(5 * (L + 1) : ℕ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  set x : ℝ := 2 * (Real.exp 1 - 1) / (n : ℝ) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have ha1 : (1 : ℝ) ≤ 1 + x := by linarith
  have hLpos : (0 : ℝ) ≤ (L + 1 : ℕ) := by positivity
  have hM1 : (1 : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hM42 : (42 : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast hLbig
  have he9 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hepos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hstep1 : (1 + x) ^ t ≤ Real.exp ((t : ℝ) * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by rw [add_comm]; exact Real.add_one_le_exp x) t
  have htR : (t : ℝ) ≤ 12 * ((n : ℝ) * (L + 1 : ℕ)) := by
    have h : (t : ℝ) ≤ ((12 * n * (L + 1) : ℕ) : ℝ) := by exact_mod_cast ht
    rw [Nat.cast_mul, Nat.cast_mul] at h; push_cast at h ⊢; linarith
  have htx : (t : ℝ) * x ≤ 24 * (Real.exp 1 - 1) * (L + 1 : ℕ) := by
    rw [hx, show (t : ℝ) * (2 * (Real.exp 1 - 1) / (n : ℝ))
          = (2 * (Real.exp 1 - 1)) * ((t : ℝ) / (n : ℝ)) by ring]
    have hdiv : (t : ℝ) / (n : ℝ) ≤ 12 * (L + 1 : ℕ) := by
      rw [div_le_iff₀ hnpos]; nlinarith [htR]
    have h2e : 0 ≤ 2 * (Real.exp 1 - 1) := by linarith
    calc (2 * (Real.exp 1 - 1)) * ((t : ℝ) / (n : ℝ))
        ≤ (2 * (Real.exp 1 - 1)) * (12 * (L + 1 : ℕ)) := mul_le_mul_of_nonneg_left hdiv h2e
      _ = 24 * (Real.exp 1 - 1) * (L + 1 : ℕ) := by ring
  have hpowt : (1 + x) ^ t ≤ Real.exp (24 * (Real.exp 1 - 1) * (L + 1 : ℕ)) :=
    le_trans hstep1 (Real.exp_le_exp.mpr htx)
  have hpow_nonneg : (0 : ℝ) ≤ (1 + x) ^ t := by positivity
  have hn_exp : (n : ℝ) ≤ Real.exp (L + 1 : ℕ) := by
    calc (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hnpos).symm
      _ ≤ Real.exp (L + 1 : ℕ) := Real.exp_le_exp.mpr hlog
  have hterm1 : (1 + x) ^ t * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
      ≤ Real.exp (-(7 * (L + 1) : ℕ)) := by
    have := Phase0Window.phase0_numerics_real_wide n L t hn hlog ht
    rwa [← hx] at this
  have hsum_le : (∑ i ∈ Finset.range t, (1 + x) ^ i) ≤ (t : ℝ) * (1 + x) ^ t := by
    calc (∑ i ∈ Finset.range t, (1 + x) ^ i)
        ≤ ∑ _i ∈ Finset.range t, (1 + x) ^ t := by
          apply Finset.sum_le_sum; intro i hi
          exact pow_le_pow_right₀ ha1 (le_of_lt (Finset.mem_range.mp hi))
      _ = (t : ℝ) * (1 + x) ^ t := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hb_nonneg : (0 : ℝ) ≤ 2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)) := by positivity
  have hterm2 : (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
        * (∑ i ∈ Finset.range t, (1 + x) ^ i)
      ≤ Real.exp (-(6 * (L + 1) : ℕ)) := by
    calc (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
            * (∑ i ∈ Finset.range t, (1 + x) ^ i)
        ≤ (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ))) * ((t : ℝ) * (1 + x) ^ t) :=
          mul_le_mul_of_nonneg_left hsum_le hb_nonneg
      _ ≤ (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
            * ((12 * ((n : ℝ) * (L + 1 : ℕ)))
                * Real.exp (24 * (Real.exp 1 - 1) * (L + 1 : ℕ))) := by
          apply mul_le_mul_of_nonneg_left _ hb_nonneg
          apply mul_le_mul htR hpowt hpow_nonneg
          positivity
      _ ≤ (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
            * ((12 * (Real.exp (L + 1 : ℕ) * (L + 1 : ℕ)))
                * Real.exp (24 * (Real.exp 1 - 1) * (L + 1 : ℕ))) := by
          apply mul_le_mul_of_nonneg_left _ hb_nonneg
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hn_exp hLpos
      _ ≤ Real.exp (-(6 * (L + 1) : ℕ)) := by
          rw [show (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
                * ((12 * (Real.exp (L + 1 : ℕ) * (L + 1 : ℕ)))
                    * Real.exp (24 * (Real.exp 1 - 1) * (L + 1 : ℕ)))
              = (24 * Real.exp 1 * (L + 1 : ℕ)) * (Real.exp (-(50 * (L + 1) : ℕ))
                  * Real.exp (L + 1 : ℕ) * Real.exp (24 * (Real.exp 1 - 1) * (L + 1 : ℕ))) by ring]
          rw [← Real.exp_add, ← Real.exp_add]
          have hexp_arg : -(50 * (L + 1) : ℕ) + (L + 1 : ℕ) + 24 * (Real.exp 1 - 1) * (L + 1 : ℕ)
              ≤ -(7 * (L + 1) : ℕ) := by
            push_cast; nlinarith [hLpos, he9]
          -- 24·e·(L+1) ≤ 66(L+1) ≤ exp(L+1)  via the CUBE (1+M/3)³ ≤ exp(M), M = L+1 ≥ 42
          have hcoef : (24 * Real.exp 1 * (L + 1 : ℕ) : ℝ) ≤ Real.exp ((L + 1 : ℕ)) := by
            have hle66 : (24 * Real.exp 1 * (L + 1 : ℕ) : ℝ) ≤ 66 * (L + 1 : ℕ) := by
              nlinarith [hLpos, he9]
            set M : ℝ := ((L + 1 : ℕ) : ℝ) with hMdef
            have hMnn : (0 : ℝ) ≤ 1 + M / 3 := by positivity
            have hthird : 1 + M / 3 ≤ Real.exp (M / 3) := by
              have := Real.add_one_le_exp (M / 3); linarith
            have hcube : (1 + M / 3) ^ 3 ≤ Real.exp (M / 3) ^ 3 :=
              pow_le_pow_left₀ hMnn hthird 3
            have hsplit : Real.exp (M / 3) ^ 3 = Real.exp M := by
              rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
            rw [hsplit] at hcube
            have hexpand : (1 + M / 3) ^ 3 = 1 + M + M ^ 2 / 3 + M ^ 3 / 27 := by ring
            rw [hexpand] at hcube
            have hM2 : (1764 : ℝ) ≤ M ^ 2 := by nlinarith [hM42]
            have hM3 : (1764 : ℝ) * M ≤ M ^ 3 := by nlinarith [hM2, hM42]
            have hkey : (66 * M : ℝ) ≤ 1 + M + M ^ 2 / 3 + M ^ 3 / 27 := by
              nlinarith [hM3, hM2, hM42]
            have hexpM : (66 * M : ℝ) ≤ Real.exp M := le_trans hkey hcube
            calc (24 * Real.exp 1 * (L + 1 : ℕ) : ℝ) ≤ 66 * (L + 1 : ℕ) := hle66
              _ = 66 * M := by rw [hMdef]
              _ ≤ Real.exp M := hexpM
              _ = Real.exp ((L + 1 : ℕ)) := by rw [hMdef]
          calc (24 * Real.exp 1 * (L + 1 : ℕ) : ℝ)
                * Real.exp (-(50 * (L + 1) : ℕ) + (L + 1 : ℕ)
                    + 24 * (Real.exp 1 - 1) * (L + 1 : ℕ))
              ≤ Real.exp ((L + 1 : ℕ)) * Real.exp (-(7 * (L + 1) : ℕ)) := by
                apply mul_le_mul hcoef (Real.exp_le_exp.mpr hexp_arg) (Real.exp_nonneg _)
                  (Real.exp_nonneg _)
            _ = Real.exp ((L + 1 : ℕ) + -(7 * (L + 1) : ℕ)) := by rw [← Real.exp_add]
            _ ≤ Real.exp (-(6 * (L + 1) : ℕ)) := by
                apply Real.exp_le_exp.mpr; push_cast; nlinarith [hLpos]
  calc (1 + x) ^ t * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
        + (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ)))
            * (∑ i ∈ Finset.range t, (1 + x) ^ i)
      ≤ Real.exp (-(7 * (L + 1) : ℕ)) + Real.exp (-(6 * (L + 1) : ℕ)) := add_le_add hterm1 hterm2
    _ ≤ Real.exp (-(5 * (L + 1) : ℕ)) := by
        have h76 : Real.exp (-(7 * (L + 1) : ℕ)) ≤ Real.exp (-(6 * (L + 1) : ℕ)) := by
          apply Real.exp_le_exp.mpr; push_cast; nlinarith [hLpos]
        have h2 : Real.exp (-(6 * (L + 1) : ℕ)) + Real.exp (-(6 * (L + 1) : ℕ))
            ≤ Real.exp (-(5 * (L + 1) : ℕ)) := by
          rw [← two_mul]
          have hexp1 : (2 : ℝ) ≤ Real.exp ((L + 1 : ℕ)) := by
            have := Real.add_one_le_exp ((L + 1 : ℕ) : ℝ); nlinarith [hLpos, hM1]
          calc (2 : ℝ) * Real.exp (-(6 * (L + 1) : ℕ))
              ≤ Real.exp ((L + 1 : ℕ)) * Real.exp (-(6 * (L + 1) : ℕ)) :=
                mul_le_mul_of_nonneg_right hexp1 (Real.exp_nonneg _)
            _ = Real.exp ((L + 1 : ℕ) + -(6 * (L + 1) : ℕ)) := by rw [← Real.exp_add]
            _ ≤ Real.exp (-(5 * (L + 1) : ℕ)) := by
                apply Real.exp_le_exp.mpr; push_cast; nlinarith [hLpos]
        linarith [h76, h2]

/-- **The HONEST early-overshoot precursor tail** (`b = 2·e·freshVal`).  Clone of
`SeamNoOvershoot.seam_atRiskClockZero_tail` with the corrected immigration constant
`b = 2·(eˢ·freshVal 1)` and the honest drift / numerics.  The probability of seeing an
at-risk zero clock within the seam is STILL `≤ e^{−40(L+1)}` (Stage-4 numerics close with
the extra `e` factor).  Requires `CounterResetDest (p+1)` and `SeamRegimeDispatch p`
(the protocol-structural inputs replacing the carried `hpair`). -/
theorem seam_atRiskClockZero_tail_honest (p n tseam : ℕ)
    (hq : CounterResetDest (p + 1)) (hdisp : SeamRegimeDispatch (L := L) (K := K) p)
    (hn : 1 ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (ht : tseam ≤ n * (L + 1))
    (c₀ : Config (AgentState L K)) (hcard₀ : Multiset.card c₀ = n)
    (hinitΦ : seamClockPotential (L := L) (K := K) p 1 c₀
        ≤ (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ)))) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
      {c | AtRiskClockZero (L := L) (K := K) p c}
      ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) := by
  set a : ℝ≥0∞ := ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) with ha
  set b : ℝ≥0∞ := 2 * (ENNReal.ofReal (Real.exp 1) * freshVal (L := L) 1) with hb
  have htail := Phase0Window.phase0_window_tail_affine (NonuniformMajority L K)
    (seamClockPotential (L := L) (K := K) p 1)
    (measurable_seamClockPotential p 1)
    (fun c => Multiset.card c = n)
    (cardWindow_absorbing n)
    a b
    (fun c hc => by
      have hc2 : 2 ≤ Multiset.card c := by rw [hc]; exact hn2
      exact seamClockPotential_drift_affine_honest p hq 1 (by norm_num) hdisp n c hc hc2)
    (fun c => ¬ AtRiskClockZero (L := L) (K := K) p c)
    (θ := 1) (by norm_num) (by norm_num)
    (fun c hc => seamClockPotential_ge_one_of_not_noAtRisk p 1 c hc)
    tseam c₀ hcard₀
  have hseteq : {c : Config (AgentState L K) | AtRiskClockZero (L := L) (K := K) p c}
      = {c | ¬ ¬ AtRiskClockZero (L := L) (K := K) p c} := by
    ext c; simp
  rw [hseteq]
  refine htail.trans ?_
  rw [div_one]
  have hbase_nonneg : (0 : ℝ) ≤ 1 + 2 * (Real.exp 1 - 1) / (n : ℝ) := by
    have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : (0 : ℝ) ≤ 2 * (Real.exp 1 - 1) / (n : ℝ) := by positivity
    linarith
  have hM50_nonneg : (0 : ℝ) ≤ Real.exp (-(50 * (L + 1) : ℕ)) := (Real.exp_pos _).le
  have hstep_init : a ^ tseam * seamClockPotential (L := L) (K := K) p 1 c₀
      ≤ a ^ tseam * ((n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ)))) := by
    gcongr
  refine (add_le_add hstep_init (le_refl (b * ∑ i ∈ Finset.range tseam, a ^ i))).trans ?_
  have hat : a ^ tseam = ENNReal.ofReal ((1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ tseam) := by
    rw [ha, ← ENNReal.ofReal_pow hbase_nonneg]
  have hncast : (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by rw [ENNReal.ofReal_natCast]
  -- b = ofReal(2 · e · e^{−50(L+1)})  (the honest immigration with the extra eˢ = e).
  have hbval : b = ENNReal.ofReal (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ))) := by
    rw [hb, freshVal]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by rw [ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    push_cast; ring_nf
  have hsumcast : (∑ i ∈ Finset.range tseam, a ^ i)
      = ENNReal.ofReal (∑ i ∈ Finset.range tseam,
          (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ha, ← ENNReal.ofReal_pow hbase_nonneg]
  rw [hat, hncast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      hbval, hsumcast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact seam_noOvershoot_numerics_honest n L tseam hn hlog ht

/-- **Wide-window honest at-risk-clock-zero tail (`tseam ≤ 12·n(L+1)`).**  Identical plumbing to
`seam_atRiskClockZero_tail_honest`, but for the genuine 12× Janson seam window, closing to
`exp(-5(L+1))` via `seam_noOvershoot_numerics_honest_wide`.  Needs `42 ≤ L+1` (regime). -/
theorem seam_atRiskClockZero_tail_honest_wide (p n tseam : ℕ)
    (hq : CounterResetDest (p + 1)) (hdisp : SeamRegimeDispatch (L := L) (K := K) p)
    (hn : 1 ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) (hLbig : 42 ≤ L + 1)
    (ht : tseam ≤ 12 * n * (L + 1))
    (c₀ : Config (AgentState L K)) (hcard₀ : Multiset.card c₀ = n)
    (hinitΦ : seamClockPotential (L := L) (K := K) p 1 c₀
        ≤ (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ)))) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
      {c | AtRiskClockZero (L := L) (K := K) p c}
      ≤ ENNReal.ofReal (Real.exp (-(5 * (L + 1) : ℕ))) := by
  set a : ℝ≥0∞ := ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) with ha
  set b : ℝ≥0∞ := 2 * (ENNReal.ofReal (Real.exp 1) * freshVal (L := L) 1) with hb
  have htail := Phase0Window.phase0_window_tail_affine (NonuniformMajority L K)
    (seamClockPotential (L := L) (K := K) p 1)
    (measurable_seamClockPotential p 1)
    (fun c => Multiset.card c = n)
    (cardWindow_absorbing n)
    a b
    (fun c hc => by
      have hc2 : 2 ≤ Multiset.card c := by rw [hc]; exact hn2
      exact seamClockPotential_drift_affine_honest p hq 1 (by norm_num) hdisp n c hc hc2)
    (fun c => ¬ AtRiskClockZero (L := L) (K := K) p c)
    (θ := 1) (by norm_num) (by norm_num)
    (fun c hc => seamClockPotential_ge_one_of_not_noAtRisk p 1 c hc)
    tseam c₀ hcard₀
  have hseteq : {c : Config (AgentState L K) | AtRiskClockZero (L := L) (K := K) p c}
      = {c | ¬ ¬ AtRiskClockZero (L := L) (K := K) p c} := by
    ext c; simp
  rw [hseteq]
  refine htail.trans ?_
  rw [div_one]
  have hbase_nonneg : (0 : ℝ) ≤ 1 + 2 * (Real.exp 1 - 1) / (n : ℝ) := by
    have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : (0 : ℝ) ≤ 2 * (Real.exp 1 - 1) / (n : ℝ) := by positivity
    linarith
  have hM50_nonneg : (0 : ℝ) ≤ Real.exp (-(50 * (L + 1) : ℕ)) := (Real.exp_pos _).le
  have hstep_init : a ^ tseam * seamClockPotential (L := L) (K := K) p 1 c₀
      ≤ a ^ tseam * ((n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ)))) := by
    gcongr
  refine (add_le_add hstep_init (le_refl (b * ∑ i ∈ Finset.range tseam, a ^ i))).trans ?_
  have hat : a ^ tseam = ENNReal.ofReal ((1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ tseam) := by
    rw [ha, ← ENNReal.ofReal_pow hbase_nonneg]
  have hncast : (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by rw [ENNReal.ofReal_natCast]
  have hbval : b = ENNReal.ofReal (2 * Real.exp 1 * Real.exp (-(50 * (L + 1) : ℕ))) := by
    rw [hb, freshVal]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by rw [ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    push_cast; ring_nf
  have hsumcast : (∑ i ∈ Finset.range tseam, a ^ i)
      = ENNReal.ofReal (∑ i ∈ Finset.range tseam,
          (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ha, ← ENNReal.ofReal_pow hbase_nonneg]
  rw [hat, hncast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      hbval, hsumcast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact seam_noOvershoot_numerics_honest_wide n L tseam hn hlog hLbig ht

/-! ### The end-to-end honest per-seam no-overshoot tail.

Composing the honest at-risk tail (`seam_atRiskClockZero_tail_honest`) with the public
prefix-union machinery (`SeamNoOvershoot.seam_noOvershoot_tail`, the deterministic bridge
`DetSeamOvershootBridge`, and `hNoOvershoot_one_seam`) gives the terminal per-seam
no-overshoot budget with the HONEST immigration constant, still closing at `e^{−40(L+1)}`.

EXCLUDED DESTINATIONS (named, not faked):
* Phases `2, 4, 9` are UNTIMED (opinion-union / big-bias advance), so `CounterResetDest`
  is FALSE for them — their seam no-overshoot is supplied by the work-phase / big-bias
  guards in `SeamEpidemics`, not this clock-counter tail.
* Phases `3, 5` are counter-timed but their entry does NOT reset the counter on a
  counter-advance: phase 3's `phaseInit` sets `minute` (not `counter`); phase 5's
  predecessor `Phase4Transition` advances via `advancePhase` (no `phaseInit`).  So
  `CounterResetDest` excludes them; their no-overshoot comes from the dedicated
  minute/hour width machinery (`ClockOLogN`/`ClockReal*`).
The hypothesis `CounterResetDest (p+1)` is exactly the guard that admits only the honest
set `{1,6,7,8}`; the regime dispatch `SeamRegimeDispatch p` is the per-pair structural
fact (an output clock at `p+1` came from a source clock at `p` or `p+1`). -/

/-- **The HONEST terminal no-overshoot tail (one seam), `b = 2·e·freshVal`.**  From a
`NoOvershoot` start, with the deterministic overshoot bridge and the per-`τ` HONEST at-risk
tails (`seam_atRiskClockZero_tail_honest`, each `≤ e^{−40(L+1)}`), the overshoot
probability is `≤ tseam · e^{−40(L+1)}`.  Wraps the public
`SeamNoOvershoot.seam_noOvershoot_tail`; the per-`τ` inputs `hτ` are the honest at-risk
tails (the `CounterResetDest`/`SeamRegimeDispatch` guards are discharged inside each `hτ`
producer, not here). -/
theorem seam_noOvershoot_tail_honest (p tseam : ℕ)
    (hdet : DetSeamOvershootBridge (L := L) (K := K) p)
    (c₀ : Config (AgentState L K))
    (h0 : NoOvershoot (L := L) (K := K) p c₀)
    (hτ : ∀ τ ∈ Finset.range tseam,
      ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c | AtRiskClockZero (L := L) (K := K) p c}
        ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
        {c | ¬ NoOvershoot (L := L) (K := K) p c}
      ≤ (tseam : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) :=
  seam_noOvershoot_tail p tseam hdet c₀ h0 hτ

/-- **The HONEST per-seam no-overshoot budget wrapper.**  If the honest terminal overshoot
tail is `≤ εovershoot`, the per-seam budget is met.  Identical shape to
`SeamNoOvershoot.hNoOvershoot_one_seam` (the immigration constant is internal to the tail;
the budget surface is unchanged).  This is the `hNoOvershoot` `seamEpidemicExactW` consumes
— so the honest chain plugs into the SAME integration point as the predecessor's, with the
corrected constant and the SAME `e^{−40(L+1)}` bound.

HYPOTHESIS SURFACE (the entire honest end-to-end): seam `Pre` (`allPhaseGe ∧ advTriggered`,
threaded into `NoOvershoot`-start + `card = n` by the seam layer) + `tseam ≤ n(L+1)` +
`log n ≤ L+1` + initial-potential bound (`Φ ≤ n·e^{−50(L+1)}`) + the structural
`CounterResetDest (p+1)` / `SeamRegimeDispatch p` / `DetSeamOvershootBridge p` guards +
arithmetic.  No `2·freshVal` falsehood; immigration is the honest `2·e·freshVal`. -/
theorem hNoOvershoot_one_seam_honest (p tseam : ℕ) (εovershoot : ℝ≥0)
    (hbound : ∀ c₀ : Config (AgentState L K),
      NoOvershoot (L := L) (K := K) p c₀ →
      ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
          {c | ¬ NoOvershoot (L := L) (K := K) p c}
        ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))))
    (hε : ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) ≤ (εovershoot : ℝ≥0∞)) :
    ∀ c₀ : Config (AgentState L K),
      NoOvershoot (L := L) (K := K) p c₀ →
      ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
          {c | ¬ NoOvershoot (L := L) (K := K) p c}
        ≤ (εovershoot : ℝ≥0∞) :=
  hNoOvershoot_one_seam p tseam εovershoot hbound hε

end SeamNoOvershoot

end ExactMajority
