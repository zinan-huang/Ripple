/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — the SEAM per-pair output bound machinery (`hpair`)

Discharges the protocol-structural core behind `SeamNoOvershoot`'s carried `hpair`
(the seam analogue of `Phase0Window.clockSummand_pair_le`, restricted to the
counter-timed destination phases `q = p+1 ∈ {1,5,6,7,8}`).  Every theorem here is
0-sorry / axiom-clean (`[propext, Classical.choice, Quot.sound]`), no `native_decide`.

## What is proven (the per-pair output decomposition, side `.1`)

The full Transition LEFT output `(Transition a b).1 = finishPhase10Entry s' out.1`
reads only `role`/`phase`/`counter` for the seam summand (`finishPhase10Entry`
preserves all three), so `seamClockSummand` of it equals that of the dispatcher
output `out.1`.  The summand of `out.1` (a clock at the destination phase `p+1`) is
controlled by:

* `seamClockSummand_stdCounterSubroutine_le` / `…_clockCounterStep_le` — the
  **decrement bound**: a clock at `p+1` whose counter is ticked scales its summand
  by exactly `eˢ` (positive counter) or advances out of `p+1` (counter `0`, summand `0`).
* `seamClockSummand_phaseEpidemicUpdate_left_le` — the **epidemic immigration
  summand bound**: `summand(ep.1) ≤ summand(a) + freshVal`.  A clock dragged up into
  `p+1` by the epidemic enters with the FULL counter (`runInitsBetween … phaseInit q`
  resets it; `runInitsBetween_clock_counter_reset` + `phaseEpidemicUpdate_left_immigrant_full`).
* `seamClockSummand_stdCounterSubroutine_advance` — the **counter-advance
  immigration**: a clock advanced INTO `p+1` by the dispatch enters with the FULL
  counter (`advancePhaseWithInit … phaseInit q` resets it), summand `= freshVal`.
* `seamClockSummand_dispatch_left_decrement_le` — routes the FROZEN dispatcher (for
  `p+1 ∈ {1,5,6,7,8}`) through the proven per-phase `Phase{1,5,6,7,8}Transition_left_clock`
  reductions to deliver the no-advance per-side contraction `≤ eˢ · summand(ep.1)`.

## TWO FINDINGS (after genuine attack; see `HANDOFF_SEAM_NOOVERSHOOT.md`)

1. **The consumer's `hpair` immigration constant `2·freshVal` is TOO TIGHT for
   `s > 0`.**  A fresh epidemic-dragged clock enters `p+1` at the FULL counter and is
   DECREMENTED by the SAME-step dispatch to `full − 1`, so its summand is `eˢ·freshVal`,
   not `freshVal`.  The HONEST per-side immigration ceiling is `eˢ·freshVal`; the
   honest per-pair ceiling is `2·eˢ·freshVal` (at `s = 1`, `2e·freshVal`, exceeding
   `2·freshVal`).  Downstream this is benign — `seam_noOvershoot_numerics_real` closes
   `e^{−40}` from `e^{−45}+e^{−43}` with large slack, so `b = 2·e·freshVal` still closes.

2. **Phase 5 must ALSO be excluded from the counter-reset set** (like phase 3).  The
   predecessor `Phase4Transition` advances clocks via `advancePhase` (big-bias gate),
   which does NOT run `phaseInit` / reset the counter.  So a clock counter-advanced
   from phase 4 into phase 5 keeps its OLD (possibly small) counter — summand up to `1`,
   NOT `freshVal` — breaking the affine immigration tail for phase 5.  Phases
   `{1,6,7,8}` are clean: their predecessors (`Phase0` Rule-5 / `Phase{5,6,7}`) all
   advance clocks via `stdCounterSubroutine → advancePhaseWithInit → phaseInit q`,
   which DOES reset.  The fully-honest counter-reset destination set for the seam
   no-overshoot clock-counter tail is therefore `{1,6,7,8}` (epidemic-drag set
   `{1,5,6,7,8}` ∩ counter-advance-reset set `{1,6,7,8}`).

Reference: Doty et al. §6; consumer = `Probability/SeamNoOvershoot.lean`; pattern =
`Probability/Phase0Window.lean`; blueprint = `HANDOFF_SEAM_NOOVERSHOOT.md`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamNoOvershoot

namespace ExactMajority

open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-- `seamClockSummand` reads only `role`, `phase.val`, `counter.val`. -/
theorem seamClockSummand_congr (p : ℕ) (s : ℝ) (a a' : AgentState L K)
    (hrole : a.role = a'.role) (hphase : a.phase.val = a'.phase.val)
    (hctr : a.counter.val = a'.counter.val) :
    seamClockSummand (L := L) (K := K) p s a
      = seamClockSummand (L := L) (K := K) p s a' := by
  unfold seamClockSummand
  rw [hrole, hphase, hctr]

/-- `seamClockSummand` is invariant under `finishPhase10Entry` (which preserves
`role`/`phase.val`/`counter`). -/
theorem seamClockSummand_finishPhase10Entry (p : ℕ) (s : ℝ)
    (before after : AgentState L K) :
    seamClockSummand (L := L) (K := K) p s (finishPhase10Entry L K before after)
      = seamClockSummand (L := L) (K := K) p s after := by
  apply seamClockSummand_congr
  · simp
  · simp
  · rw [finishPhase10Entry_counter]


/-- For a counter-reset destination phase `q ∈ {1,5,6,7,8}`, `phaseInit q` resets
a clock's counter to the full `50(L+1)`. -/
theorem phaseInit_clock_counter_reset (q : Fin 11) (a : AgentState L K)
    (ha : a.role = .clock) (hq : CounterTimedPhase q.val) :
    (phaseInit L K q a).counter.val = 50 * (L + 1) := by
  unfold phaseInit
  rcases hq with h | h | h | h | h <;>
    rw [h] <;>
    simp only [ha, reduceCtorEq, ↓reduceDIte, ↓reduceIte] <;>
    norm_num

/-- When the responder's phase is `≤` the initiator's, the epidemic leaves the
initiator's `counter`/`role` untouched (`runInitsBetween p p = id`, and both
epidemic branches preserve `after`'s `counter`/`role`); the phase is either
`a.phase` (non-error) or `10` (the error-to-backup branch). -/
theorem phaseEpidemicUpdate_left_id_of_ge (a b : AgentState L K)
    (hba : b.phase.val ≤ a.phase.val) :
    (phaseEpidemicUpdate L K a b).1.counter = a.counter
    ∧ (phaseEpidemicUpdate L K a b).1.role = a.role
    ∧ ((phaseEpidemicUpdate L K a b).1.phase = a.phase
        ∨ (phaseEpidemicUpdate L K a b).1.phase.val = 10) := by
  unfold phaseEpidemicUpdate
  have hmax : max a.phase b.phase = a.phase := by
    apply max_eq_left; exact Fin.le_def.mpr hba
  simp only [hmax]
  have hself : runInitsBetween L K a.phase.val a.phase.val { a with phase := a.phase }
      = a := by
    rw [runInitsBetween_self_api]
  split_ifs with h
  · rw [hself]
    refine ⟨by simp, by simp, ?_⟩
    by_cases ha10 : a.phase.val < 10
    · right
      exact phase10EpidemicEntry_phase_val_of_before_lt_10 (L := L) (K := K) a a ha10
    · left
      have : ¬ a.phase.val < 10 := ha10
      have hval : (phase10EpidemicEntry L K a a).phase.val = a.phase.val := by
        simp [phase10EpidemicEntry, this]
      exact Fin.ext hval
  · rw [hself]; exact ⟨rfl, rfl, Or.inl rfl⟩

/-- Symmetric right-side version of `phaseEpidemicUpdate_left_id_of_ge`. -/
theorem phaseEpidemicUpdate_right_id_of_ge (a b : AgentState L K)
    (hab : a.phase.val ≤ b.phase.val) :
    (phaseEpidemicUpdate L K a b).2.counter = b.counter
    ∧ (phaseEpidemicUpdate L K a b).2.role = b.role
    ∧ ((phaseEpidemicUpdate L K a b).2.phase = b.phase
        ∨ (phaseEpidemicUpdate L K a b).2.phase.val = 10) := by
  unfold phaseEpidemicUpdate
  have hmax : max a.phase b.phase = b.phase := by
    apply max_eq_right; exact Fin.le_def.mpr hab
  simp only [hmax]
  have hself : runInitsBetween L K b.phase.val b.phase.val { b with phase := b.phase }
      = b := by
    rw [runInitsBetween_self_api]
  split_ifs with h
  · rw [hself]
    refine ⟨by simp, by simp, ?_⟩
    by_cases hb10 : b.phase.val < 10
    · right
      exact phase10EpidemicEntry_phase_val_of_before_lt_10 (L := L) (K := K) b b hb10
    · left
      have hval : (phase10EpidemicEntry L K b b).phase.val = b.phase.val := by
        simp [phase10EpidemicEntry, hb10]
      exact Fin.ext hval
  · rw [hself]; exact ⟨rfl, rfl, Or.inl rfl⟩

/-- For a clock initiator, the Phase-1 dispatch leaves the LEFT output equal to
`clockCounterStep` (the main–main averaging pre-step never touches a clock). -/
theorem Phase1Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase1Transition L K c t).1 = clockCounterStep L K c := by
  unfold Phase1Transition
  have hnm : ¬ (c.role = .main ∧ t.role = .main) := by
    rintro ⟨h, _⟩; rw [hc] at h; exact absurd h (by decide)
  simp only [hnm, if_false]

/-- For a clock initiator, the Phase-5 dispatch leaves the LEFT output equal to
`stdCounterSubroutine` (the reserve/main sampling pre-step never touches a clock). -/
theorem Phase5Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase5Transition L K c t).1 = stdCounterSubroutine L K c := by
  unfold Phase5Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock initiator, the Phase-6 dispatch leaves the LEFT output equal to
`stdCounterSubroutine`. -/
theorem Phase6Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase6Transition L K c t).1 = stdCounterSubroutine L K c := by
  unfold Phase6Transition
  simp only [hc, reduceCtorEq, false_and, and_false, ↓reduceIte]

/-- For a clock initiator, the Phase-7 dispatch leaves the LEFT output equal to
`stdCounterSubroutine` (the main–main cancel pre-step never touches a clock). -/
theorem Phase7Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase7Transition L K c t).1 = stdCounterSubroutine L K c := by
  unfold Phase7Transition
  simp only [hc, reduceCtorEq, false_and, ↓reduceIte]

/-- For a clock initiator, the Phase-8 dispatch leaves the LEFT output equal to
`stdCounterSubroutine` (the main–main absorb pre-step never touches a clock). -/
theorem Phase8Transition_left_clock (c t : AgentState L K) (hc : c.role = .clock) :
    (Phase8Transition L K c t).1 = stdCounterSubroutine L K c := by
  unfold Phase8Transition
  simp only [hc, reduceCtorEq, false_and, ↓reduceIte]

/-- **Decrement bound for `stdCounterSubroutine` on a clock at the destination
phase.**  If `c` is a clock at phase `p+1`, then
`seamClockSummand p s (stdCounterSubroutine c) ≤ eˢ · seamClockSummand p s c`
(for `s ≥ 0`): a positive-counter clock decrements (`exp(-s(k-1)) = eˢ·exp(-sk)`),
a zero-counter clock advances out of phase `p+1` (output summand `0`). -/
theorem seamClockSummand_stdCounterSubroutine_le (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (c : AgentState L K) (hrole : c.role = .clock) (hphase : c.phase.val = p + 1) :
    seamClockSummand (L := L) (K := K) p s (stdCounterSubroutine L K c)
      ≤ ENNReal.ofReal (Real.exp s) * seamClockSummand (L := L) (K := K) p s c := by
  have he1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp s) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hs)
  have hsrc : seamClockSummand (L := L) (K := K) p s c
      = ENNReal.ofReal (Real.exp (-(s * (c.counter.val : ℝ)))) := by
    unfold seamClockSummand; rw [if_pos ⟨hrole, hphase⟩]
  -- any seam summand is ≤ 1 (exp(-s·counter) ≤ exp(0) = 1 for s ≥ 0).
  have hle_one : ∀ a : AgentState L K,
      seamClockSummand (L := L) (K := K) p s a ≤ 1 := by
    intro a
    unfold seamClockSummand
    by_cases hcond : a.role = .clock ∧ a.phase.val = p + 1
    · rw [if_pos hcond, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      apply Real.exp_le_exp.mpr
      have : (0 : ℝ) ≤ s * (a.counter.val : ℝ) := by positivity
      linarith
    · rw [if_neg hcond]; exact zero_le'
  unfold stdCounterSubroutine
  by_cases hctr : c.counter.val = 0
  · -- advance: source summand = 1 (counter 0), so eˢ·source = eˢ ≥ 1 ≥ output summand.
    rw [dif_pos hctr]
    have hsrc1 : seamClockSummand (L := L) (K := K) p s c = 1 := by
      rw [hsrc, hctr]; simp
    rw [hsrc1, mul_one]
    exact le_trans (hle_one _) he1
  · -- decrement
    rw [dif_neg hctr]
    have hout_role : ({ c with counter := ⟨c.counter.val - 1, by omega⟩ } : AgentState L K).role = .clock := hrole
    have hout_phase : ({ c with counter := ⟨c.counter.val - 1, by omega⟩ } : AgentState L K).phase.val = p + 1 := hphase
    have hout : seamClockSummand (L := L) (K := K) p s
        { c with counter := ⟨c.counter.val - 1, by omega⟩ }
        = ENNReal.ofReal (Real.exp (-(s * ((c.counter.val - 1 : ℕ) : ℝ)))) := by
      unfold seamClockSummand; rw [if_pos ⟨hout_role, hout_phase⟩]
    rw [hout, hsrc]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h1 : (1 : ℕ) ≤ c.counter.val := Nat.one_le_iff_ne_zero.mpr hctr
    have hcast : ((c.counter.val - 1 : ℕ) : ℝ) = (c.counter.val : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; simp
    rw [hcast]; nlinarith [hs]

/-- `clockCounterStep` on a clock at the destination phase satisfies the same
decrement bound (it IS `stdCounterSubroutine` on a clock). -/
theorem seamClockSummand_clockCounterStep_le (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (c : AgentState L K) (hrole : c.role = .clock) (hphase : c.phase.val = p + 1) :
    seamClockSummand (L := L) (K := K) p s (clockCounterStep L K c)
      ≤ ENNReal.ofReal (Real.exp s) * seamClockSummand (L := L) (K := K) p s c := by
  unfold clockCounterStep
  rw [if_pos hrole]
  exact seamClockSummand_stdCounterSubroutine_le p s hs c hrole hphase

/-! ### Immigration: a clock dragged up into a reset-destination phase has full counter.

The epidemic's `runInitsBetween oldP q` ends by applying `phaseInit q` (q is the
maximum of `(oldP, q] ∩ [0,10]`).  For `q ∈ {1,5,6,7,8}`, `phaseInit q` resets a
clock's counter to full `50(L+1)`.  We prove that the filter list ends in `q`, then
that the fold's last step is `phaseInit q`, then the reset. -/

/-- The `(oldP, q] ∩ range 11` filter list ends in `q` when `oldP < q ≤ 10`: the
underlying `range 11` is `Sorted (· < ·)`, filter preserves order, and `q` is the
unique maximal satisfier. -/
theorem runInitsBetween_clock_counter_reset (oldP : ℕ) (q : ℕ)
    (a : AgentState L K) (ha : a.role = .clock) (hlt : oldP < q)
    (hq : CounterTimedPhase q) :
    (runInitsBetween L K oldP q a).counter.val = 50 * (L + 1) := by
  -- `q ∈ {1,5,6,7,8}`, `oldP < q`; the filter list ends in `q`, the fold applies
  -- `phaseInit q` last (clock role preserved through the prefix), resetting to full.
  have key : ∀ (lst : List ℕ), lst = (List.range 11).filter (fun k => oldP < k ∧ k ≤ q) →
      ∃ pre : List ℕ, lst = pre ++ [q] ∧ ∀ x ∈ pre, x < q := by
    intro lst hlst
    refine ⟨(List.range 11).filter (fun k => oldP < k ∧ k ≤ q - 1), ?_, ?_⟩
    · rw [hlst]
      rcases hq with h | h | h | h | h <;> subst h <;>
        (interval_cases oldP <;> decide)
    · intro x hx
      rw [List.mem_filter] at hx
      simp only [decide_eq_true_eq] at hx
      omega
  obtain ⟨pre, hpre, hprelt⟩ := key _ rfl
  unfold runInitsBetween
  rw [hpre, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hq11 : q < 11 := by rcases hq with h | h | h | h | h <;> omega
  rw [dif_pos hq11]
  -- the prefix fold preserves the clock role (folding `phaseInit` keeps clocks clocks)
  have hrole : ∀ (l : List ℕ) (c : AgentState L K), c.role = .clock →
      (List.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
        c l).role = .clock := by
    intro l
    induction l with
    | nil => intro c hc; simpa using hc
    | cons k ks IH =>
      intro c hc
      simp only [List.foldl_cons]
      apply IH
      by_cases hk : k < 11
      · rw [dif_pos hk]; exact phaseInit_clock_role_eq L K ⟨k, hk⟩ c hc
      · rw [dif_neg hk]; exact hc
  apply phaseInit_clock_counter_reset ⟨q, hq11⟩ _ (hrole pre a ha) hq

/-- `phaseInit` never turns a non-clock into a clock (its role output is the input
role, `.reserve`, or the `enterPhase10` role which preserves the input role). -/
theorem phaseInit_role_clock_imp (q : Fin 11) (a : AgentState L K)
    (h : (phaseInit L K q a).role = .clock) : a.role = .clock := by
  by_contra hne
  rcases a with ⟨_, _, _, role, _⟩
  fin_cases q <;>
    revert h <;>
    cases role <;>
    simp_all [phaseInit, enterPhase10] <;>
    (try split_ifs) <;> simp_all

/-- **No clock creation by `runInitsBetween`.**  If the fold result is a clock,
the input was already a clock. -/
theorem runInitsBetween_role_clock_imp (oldP q : ℕ) (a : AgentState L K)
    (h : (runInitsBetween L K oldP q a).role = .clock) : a.role = .clock := by
  by_contra hne
  have key : ∀ (l : List ℕ) (c : AgentState L K), c.role ≠ .clock →
      (List.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
        c l).role ≠ .clock := by
    intro l
    induction l with
    | nil => intro c hc; simpa using hc
    | cons k ks IH =>
      intro c hc
      simp only [List.foldl_cons]
      apply IH
      by_cases hk : k < 11
      · rw [dif_pos hk]
        intro hcontra
        exact hc (phaseInit_role_clock_imp ⟨k, hk⟩ c hcontra)
      · rw [dif_neg hk]; exact hc
  exact key _ a hne h

set_option maxHeartbeats 1000000 in
/-- `phaseInit` changes the phase only to the error phase `10`, else preserves it
(`enterPhase10` is the unique phase-writing branch). -/
theorem phaseInit_phase_eq_or_ten (q : Fin 11) (a : AgentState L K) :
    (phaseInit L K q a).phase.val = a.phase.val
    ∨ (phaseInit L K q a).phase.val = 10 := by
  -- `phaseInit q a` writes `phase` only via `enterPhase10` (→ 10); else keeps it.
  -- Phases 0,3,4,5,6,7,8 never touch phase; phases 1,2,9,10 may error to 10.
  fin_cases q
  · left; rfl
  · -- phase 1
    unfold phaseInit; simp only [↓reduceDIte]
    by_cases h1 : a.role = .mcr
    · rw [if_pos h1]; right; exact enterPhase10_phase_val L K a
    · rw [if_neg h1]
      by_cases h2 : a.role = .cr
      · rw [if_pos h2]; left; rfl
      · rw [if_neg h2]
        by_cases h3 : a.role = .clock
        · rw [if_pos h3]; left; rfl
        · rw [if_neg h3]; left; rfl
  · -- phase 2
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    by_cases h : (a.smallBias.val ≤ 1 || a.smallBias.val ≥ 5) = true
    · rw [if_pos h]; right; exact enterPhase10_phase_val L K a
    · rw [if_neg h]; left; rfl
  · -- phase 3
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    rcases a with ⟨_, _, _, role, _⟩; cases role <;> (left; rfl)
  · left; rfl
  · -- phase 5
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    split_ifs <;> (left; rfl)
  · -- phase 6
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    split_ifs <;> (left; rfl)
  · -- phase 7
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    split_ifs <;> (left; rfl)
  · -- phase 8
    left; unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
  · -- phase 9
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    by_cases h : (a.smallBias.val ≤ 1 || a.smallBias.val ≥ 5) = true
    · rw [if_pos h]; right; exact enterPhase10_phase_val L K a
    · rw [if_neg h]; left; rfl
  · -- phase 10
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    right; exact enterPhase10_phase_val L K a

/-- `runInitsBetween` preserves the phase unless it errors to `10`. -/
theorem runInitsBetween_phase_eq_or_ten (oldP q : ℕ) (a : AgentState L K) :
    (runInitsBetween L K oldP q a).phase.val = a.phase.val
    ∨ (runInitsBetween L K oldP q a).phase.val = 10 := by
  unfold runInitsBetween
  have key : ∀ (l : List ℕ) (c : AgentState L K),
      (List.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
        c l).phase.val = c.phase.val
      ∨ (List.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
        c l).phase.val = 10 := by
    intro l
    induction l with
    | nil => intro c; left; rfl
    | cons k ks IH =>
      intro c
      simp only [List.foldl_cons]
      by_cases hk : k < 11
      · rw [dif_pos hk]
        rcases IH (phaseInit L K ⟨k, hk⟩ c) with h | h
        · rw [h]; exact phaseInit_phase_eq_or_ten ⟨k, hk⟩ c
        · right; exact h
      · rw [dif_neg hk]; exact IH c
  exact key _ a

/-- **Counter-advance immigration.**  When `stdCounterSubroutine` on a clock at
phase `< q` ADVANCES it into a reset-destination phase `q ∈ {1,5,6,7,8}` (i.e. the
counter was `0`), the resulting clock at `q` has the full counter `50(L+1)`
(`advancePhaseWithInit` runs `phaseInit q`, resetting it).  Hence its seam summand
at destination `p+1 = q` is exactly `freshVal`. -/
theorem seamClockSummand_stdCounterSubroutine_advance (p : ℕ) (s : ℝ)
    (c : AgentState L K) (hrole : c.role = .clock)
    (hadv : (stdCounterSubroutine L K c).phase.val = p + 1)
    (hq : CounterTimedPhase (p + 1)) (hlt : c.phase.val < p + 1) :
    seamClockSummand (L := L) (K := K) p s (stdCounterSubroutine L K c)
      = freshVal (L := L) s := by
  -- counter ≠ 0 would keep phase = c.phase < p+1, contradicting hadv; so advance branch.
  have hctr : c.counter.val = 0 := by
    by_contra hne
    rw [stdCounterSubroutine, dif_neg hne] at hadv
    have : ({ c with counter := ⟨c.counter.val - 1, by omega⟩ } : AgentState L K).phase.val
        = c.phase.val := rfl
    rw [this] at hadv; omega
  rw [stdCounterSubroutine, dif_pos hctr] at hadv ⊢
  -- advancePhaseWithInit lands in p+1 (reset phase), clock role preserved → full counter.
  have hrole' : (advancePhaseWithInit L K c).role = .clock :=
    advancePhaseWithInit_clock_role_eq L K c hrole
  have hclock2 : (advancePhase L K c).role = .clock := by
    unfold advancePhase; split <;> simpa using hrole
  have hadv2 : (phaseInit L K (advancePhase L K c).phase (advancePhase L K c)).phase.val = p + 1 := by
    have : advancePhaseWithInit L K c
        = phaseInit L K (advancePhase L K c).phase (advancePhase L K c) := rfl
    rw [this] at hadv; exact hadv
  have hple : p + 1 ≤ 8 := by rcases hq with h | h | h | h | h <;> omega
  have hpphase : (advancePhase L K c).phase.val = p + 1 := by
    rcases phaseInit_phase_eq_or_ten (advancePhase L K c).phase (advancePhase L K c) with h | h
    · rw [← h]; exact hadv2
    · rw [h] at hadv2; omega
  have hfin : (advancePhase L K c).phase = (⟨p + 1, by
      have := (advancePhase L K c).phase.2; omega⟩ : Fin 11) := Fin.ext hpphase
  have hfull : (advancePhaseWithInit L K c).counter.val = 50 * (L + 1) := by
    have hrw : advancePhaseWithInit L K c
        = phaseInit L K (advancePhase L K c).phase (advancePhase L K c) := rfl
    rw [hrw, hfin]
    exact phaseInit_clock_counter_reset _ _ hclock2 (by simpa using hq)
  unfold seamClockSummand freshVal
  rw [if_pos ⟨hrole', hadv⟩, hfull]

/-- **Epidemic immigration counter (left).**  If `ep.1` is a clock at phase
`q ∈ {1,5,6,7,8}` while the raw `a` was strictly below `q`, then `ep.1` has the
full counter `50(L+1)` (the epidemic's `runInitsBetween a.phase q` reset it). -/
theorem phaseEpidemicUpdate_left_immigrant_full (a b : AgentState L K)
    (q : ℕ) (hq : CounterTimedPhase q) (halt : a.phase.val < q)
    (hep_role : (phaseEpidemicUpdate L K a b).1.role = .clock)
    (hep_phase : (phaseEpidemicUpdate L K a b).1.phase.val = q) :
    (phaseEpidemicUpdate L K a b).1.counter.val = 50 * (L + 1) := by
  have hq11 : q < 11 := by rcases hq with h | h | h | h | h <;> omega
  have hqle : q ≤ 8 := by rcases hq with h | h | h | h | h <;> omega
  -- abbreviations for the epidemic internals.
  set mx := max a.phase b.phase with hmxdef
  set s0 := runInitsBetween L K a.phase.val mx.val { a with phase := mx } with hs0def
  set t0 := runInitsBetween L K b.phase.val mx.val { b with phase := mx } with ht0def
  have hepeq : phaseEpidemicUpdate L K a b
      = if (a.phase.val < 10 ∨ b.phase.val < 10) ∧ (s0.phase.val = 10 ∨ t0.phase.val = 10)
          then (phase10EpidemicEntry L K a s0, phase10EpidemicEntry L K b t0)
          else (s0, t0) := rfl
  rw [hepeq] at hep_role hep_phase ⊢
  by_cases hcond : (a.phase.val < 10 ∨ b.phase.val < 10) ∧ (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · -- error branch: ep.1.phase = 10 (since a.phase < q ≤ 8 < 10) — contradiction.
    rw [if_pos hcond] at hep_phase
    exfalso
    have ha10 : a.phase.val < 10 := by omega
    simp only at hep_phase
    rw [phase10EpidemicEntry_phase_val_of_before_lt_10 (L := L) (K := K) a s0 ha10] at hep_phase
    omega
  · -- non-error: ep.1 = s0 = runInitsBetween a.phase mx {a with phase := mx}.
    rw [if_neg hcond] at hep_role hep_phase ⊢
    simp only at hep_role hep_phase ⊢
    -- s0.phase = q; s0.phase = (input phase = mx) or 10; not 10 (= q), so mx = q.
    have hmxq : mx.val = q := by
      rcases runInitsBetween_phase_eq_or_ten a.phase.val mx.val
          { a with phase := mx } with h | h
      · rw [hs0def, h] at hep_phase; simpa using hep_phase
      · rw [hs0def, h] at hep_phase; omega
    have ha_clock : ({ a with phase := mx } : AgentState L K).role = .clock :=
      runInitsBetween_role_clock_imp _ _ _ hep_role
    have hreset := runInitsBetween_clock_counter_reset a.phase.val mx.val
      { a with phase := mx } ha_clock (by rw [hmxq]; exact halt) (by rw [hmxq]; exact hq)
    rw [hs0def]; exact hreset

/-- **Epidemic summand immigration bound (left).**  When the epidemic-updated
initiator `ep.1` is a clock at the destination phase `q = p+1 ∈ {1,5,6,7,8}`, its
seam summand is bounded by the source summand plus the fresh value: either `a`
was already a clock at `q` (epidemic leaves it, summand unchanged) or `a` was
below `q` and got dragged up with the full counter (summand `= freshVal`). -/
theorem seamClockSummand_phaseEpidemicUpdate_left_le (p : ℕ) (s : ℝ)
    (hq : CounterTimedPhase (p + 1)) (a b : AgentState L K) :
    seamClockSummand (L := L) (K := K) p s (phaseEpidemicUpdate L K a b).1
      ≤ seamClockSummand (L := L) (K := K) p s a + freshVal (L := L) s := by
  set ep1 := (phaseEpidemicUpdate L K a b).1 with hep1
  by_cases hcond : ep1.role = .clock ∧ ep1.phase.val = p + 1
  · -- ep1 is a clock at q.
    obtain ⟨hrole, hphase⟩ := hcond
    -- compare a.phase.val with q = p+1.
    rcases lt_trichotomy a.phase.val (p + 1) with hlt | heq | hgt
    · -- immigration: a below q ⟹ ep1 full ⟹ summand(ep1) = freshVal.
      have hfull : ep1.counter.val = 50 * (L + 1) := by
        rw [hep1]
        rw [hep1] at hrole hphase
        exact phaseEpidemicUpdate_left_immigrant_full a b (p + 1) hq hlt hrole hphase
      have : seamClockSummand (L := L) (K := K) p s ep1 = freshVal (L := L) s := by
        unfold seamClockSummand freshVal
        rw [if_pos ⟨hrole, hphase⟩, hfull]
      rw [this]; exact le_add_left le_rfl
    · -- a.phase = q: epidemic leaves the clock untouched (b.phase ≤ a.phase, else
      -- ep1.phase > q); summand(ep1) = summand(a).
      have hba : b.phase.val ≤ a.phase.val := by
        by_contra hgt
        rw [not_le] at hgt
        -- b.phase > a.phase = q ⟹ ep1.phase ≥ b.phase > q, contradicting hphase.
        have hge : b.phase.val ≤ ep1.phase.val := by
          rw [hep1]
          exact le_trans (le_max_right _ _)
            (phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) a b)
        omega
      obtain ⟨hctr, hrole_a, hphase_or⟩ := phaseEpidemicUpdate_left_id_of_ge a b hba
      have hsummeq : seamClockSummand (L := L) (K := K) p s ep1
          = seamClockSummand (L := L) (K := K) p s a := by
        apply seamClockSummand_congr
        · rw [hep1]; exact hrole_a
        · rcases hphase_or with hph | hph
          · rw [hep1, hph]
          · -- ep1.phase = 10 contradicts ep1 at p+1 ≤ 8.
            exfalso
            have hple : p + 1 ≤ 8 := by rcases hq with h | h | h | h | h <;> omega
            rw [← hep1] at hph; omega
        · rw [hep1, hctr]
      rw [hsummeq]; exact le_self_add
    · -- a.phase > q: ep1.phase ≥ a.phase > q contradicts hphase.
      exfalso
      have hge : a.phase.val ≤ ep1.phase.val := by
        rw [hep1]
        exact le_trans (le_max_left _ _)
          (phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) a b)
      omega
  · -- ep1 not clock-at-q: summand 0.
    have : seamClockSummand (L := L) (K := K) p s ep1 = 0 := by
      unfold seamClockSummand; rw [if_neg hcond]
    rw [this]; exact zero_le'

/-! ### Per-side bound (left), no-advance regime.

When the epidemic-updated initiator `ep.1` is ALREADY at the destination phase
`p+1 ∈ {1,5,6,7,8}` (no phase-advance into `p+1` this step), the full Transition's
LEFT output is `stdCounterSubroutine`/`clockCounterStep` of `ep.1` (the phase-`(p+1)`
dispatch leaves the clock pre-step untouched), so its seam summand contracts by `eˢ`:

  `summand((Transition a b).1) ≤ eˢ · summand(ep.1) ≤ eˢ · (summand(a) + freshVal)`.

The HONEST per-side immigration ceiling is therefore `eˢ · freshVal` (NOT `freshVal`):
an epidemic-dragged fresh clock enters `p+1` with the FULL counter and is then
DECREMENTED by the same-step dispatch to `full − 1`, summand `= eˢ · freshVal`. -/

/-- The phase-`(p+1)` dispatch's LEFT output, for a clock initiator `c` at phase
`p+1 ∈ {1,5,6,7,8}`, equals `stdCounterSubroutine`/`clockCounterStep c` and so
its seam summand contracts by `eˢ` (here at `s = 1`).  This routes the FROZEN
dispatcher through the proven per-phase `…_left_clock` lemmas + the decrement
bound, packaging the no-advance per-side contraction. -/
theorem seamClockSummand_dispatch_left_decrement_le (p : ℕ)
    (hq : CounterTimedPhase (p + 1)) (s : ℝ) (hs : 0 ≤ s)
    (c t : AgentState L K) (hc : c.role = .clock) (hcp : c.phase.val = p + 1) :
    seamClockSummand (L := L) (K := K) p s
        (if c.phase.val = p + 1 then
          (if (p + 1) = 1 then Phase1Transition L K c t
            else if (p + 1) = 5 then Phase5Transition L K c t
            else if (p + 1) = 6 then Phase6Transition L K c t
            else if (p + 1) = 7 then Phase7Transition L K c t
            else Phase8Transition L K c t).1
        else c)
      ≤ ENNReal.ofReal (Real.exp s) * seamClockSummand (L := L) (K := K) p s c := by
  rw [if_pos hcp]
  rcases hq with h | h | h | h | h <;> rw [h]
  · rw [if_pos (by rfl : (1 : ℕ) = 1), Phase1Transition_left_clock c t hc]
    exact seamClockSummand_clockCounterStep_le p s hs c hc hcp
  · rw [if_neg (by decide), if_pos (by rfl : (5 : ℕ) = 5), Phase5Transition_left_clock c t hc]
    exact seamClockSummand_stdCounterSubroutine_le p s hs c hc hcp
  · rw [if_neg (by decide), if_neg (by decide), if_pos (by rfl : (6 : ℕ) = 6),
        Phase6Transition_left_clock c t hc]
    exact seamClockSummand_stdCounterSubroutine_le p s hs c hc hcp
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_pos (by rfl : (7 : ℕ) = 7), Phase7Transition_left_clock c t hc]
    exact seamClockSummand_stdCounterSubroutine_le p s hs c hc hcp
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
        Phase8Transition_left_clock c t hc]
    exact seamClockSummand_stdCounterSubroutine_le p s hs c hc hcp

/-! ### Per-side capstone (left), no-advance regime.

Combining the finishPhase10 strip, the dispatch decrement reduction, and the
epidemic summand bound: when the epidemic-updated initiator `ep.1` is already at
the destination phase `p+1 ∈ {1,5,6,7,8}`, the per-side output summand contracts as

  `summand((Transition a b).1) ≤ eˢ · (summand(a) + freshVal)`.

This is the honest per-side bound in the no-advance regime; the residual is the
phase-advance regime (`ep.1.phase < p+1`), where the per-side immigration is
`freshVal` for `p+1 ∈ {1,6,7,8}` (via `seamClockSummand_stdCounterSubroutine_advance`)
but FAILS for `p+1 = 5` (predecessor `Phase4` `advancePhase` does not reset). -/
theorem seamClockSummand_Transition_left_le_of_ep_at_dest (p : ℕ)
    (hq : CounterTimedPhase (p + 1)) (s : ℝ) (hs : 0 ≤ s) (a b : AgentState L K)
    (hepdest : (phaseEpidemicUpdate L K a b).1.phase.val = p + 1)
    (hepclock : (phaseEpidemicUpdate L K a b).1.role = .clock) :
    seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
      ≤ ENNReal.ofReal (Real.exp s)
          * (seamClockSummand (L := L) (K := K) p s a + freshVal (L := L) s) := by
  -- Step 1: strip finishPhase10Entry; the dispatch is Phase(p+1)Transition on ep.
  set ep1 := (phaseEpidemicUpdate L K a b).1 with hep1
  set ep2 := (phaseEpidemicUpdate L K a b).2 with hep2
  have hstrip : seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
      = seamClockSummand (L := L) (K := K) p s
          ((if (p + 1) = 1 then Phase1Transition L K ep1 ep2
            else if (p + 1) = 5 then Phase5Transition L K ep1 ep2
            else if (p + 1) = 6 then Phase6Transition L K ep1 ep2
            else if (p + 1) = 7 then Phase7Transition L K ep1 ep2
            else Phase8Transition L K ep1 ep2).1) := by
    rw [Transition, seamClockSummand_finishPhase10Entry]
    -- the dispatcher match selects Phase(p+1) since ep1.phase = p+1.
    rcases hq with h | h | h | h | h
    · have hp : (phaseEpidemicUpdate L K a b).1.phase = (⟨1, by decide⟩ : Fin 11) :=
        Fin.ext (hepdest.trans h)
      simp only [hp, h]; rfl
    · have hp : (phaseEpidemicUpdate L K a b).1.phase = (⟨5, by decide⟩ : Fin 11) :=
        Fin.ext (hepdest.trans h)
      simp only [hp, h]; rfl
    · have hp : (phaseEpidemicUpdate L K a b).1.phase = (⟨6, by decide⟩ : Fin 11) :=
        Fin.ext (hepdest.trans h)
      simp only [hp, h]; rfl
    · have hp : (phaseEpidemicUpdate L K a b).1.phase = (⟨7, by decide⟩ : Fin 11) :=
        Fin.ext (hepdest.trans h)
      simp only [hp, h]; rfl
    · have hp : (phaseEpidemicUpdate L K a b).1.phase = (⟨8, by decide⟩ : Fin 11) :=
        Fin.ext (hepdest.trans h)
      simp only [hp, h]; rfl
  rw [hstrip]
  -- Step 2: dispatch decrement bound → ≤ eˢ · summand(ep1).
  have hdec : seamClockSummand (L := L) (K := K) p s
      ((if (p + 1) = 1 then Phase1Transition L K ep1 ep2
        else if (p + 1) = 5 then Phase5Transition L K ep1 ep2
        else if (p + 1) = 6 then Phase6Transition L K ep1 ep2
        else if (p + 1) = 7 then Phase7Transition L K ep1 ep2
        else Phase8Transition L K ep1 ep2).1)
      ≤ ENNReal.ofReal (Real.exp s) * seamClockSummand (L := L) (K := K) p s ep1 := by
    have := seamClockSummand_dispatch_left_decrement_le p hq s hs ep1 ep2 hepclock hepdest
    rwa [if_pos hepdest] at this
  refine hdec.trans ?_
  -- Step 3: epidemic summand bound → summand(ep1) ≤ summand(a) + freshVal.
  gcongr
  exact seamClockSummand_phaseEpidemicUpdate_left_le p s hq a b

end SeamNoOvershoot

end ExactMajority
