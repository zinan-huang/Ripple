/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — discharging the deterministic seam overshoot bridge (`SeamOvershootBridge`)

This file PROVES `SeamNoOvershoot.DetSeamOvershootBridge p` — the deterministic
first-overshoot bridge that `SeamNoOvershoot.lean` / `SeamPairAdapter.lean` carry as a
named structural guard `hdet`.  The bridge says:

> from a `NoOvershoot p` config (every agent at phase `< p+2`), a single scheduled
> interaction that creates an agent at phase `≥ p+2` forces a SOURCE clock at phase
> `p+1` with `counter = 0` (a witness to `AtRiskClockZero p c`).

## The obstruction and the well-formedness fix `W`

The bridge is FALSE without a well-formedness side condition (see
`HANDOFF_SEAM_NOOVERSHOOT.md` finding 2): `phaseInit 1` sends an `mcr` agent to phase
`10` (`enterPhase10`), and `phaseInit {2,9}` send an out-of-range-`smallBias` agent to
phase `10`.  An `mcr` agent epidemic-dragged into phase `1` therefore overshoots (to
phase `10 ≥ 2 = p+2` at the `p = 0` seam) with NO counter-`0` clock involved.

The MINIMAL well-formedness predicate that closes EVERY `phaseInit` error-to-`10` path
on the seam region is, per agent,

  `WfAgent a := a.role ≠ .mcr ∧ 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4`.

`phaseInit q a = enterPhase10 …` (phase `10`) for `q ≤ 9` happens ONLY when `q = 1 ∧
role = mcr`, or `q ∈ {2,9} ∧ (smallBias ≤ 1 ∨ smallBias ≥ 5)` (verified against the
FROZEN `phaseInit`); `WfAgent` excludes all three.  `phaseInit 10` always errors but is
never invoked on a seam to `p+1 ≤ 8` (`runInitsBetween` only runs `phaseInit q` for
`q ≤ max source phase ≤ p+1 ≤ 8`).

`Wf c := ∀ a ∈ c, WfAgent a` is the config-level predicate.

### Provenance and preservation

`WfAgent` is PRESERVED by every protocol step on the seam region:

* `phaseInit` preserves `smallBias` (`phaseInit_smallBias_eq`) and never creates an
  `mcr` (its only role write is `cr → reserve`), so the epidemic prefix preserves
  `WfAgent`.
* the per-phase dispatcher (for the seam phases) preserves `smallBias` and never
  creates `mcr` either.

Provenance: at the phase-0 EXIT (`RoleSplitConcentration.RoleSplitStage2Good`), `mcr`
count is `0`, and the carrier `smallBias` invariant `{2,3,4}` holds; no rule creates an
`mcr` or pushes `smallBias` out of `{2,3,4}` afterward, so `Wf` holds on the whole seam
region.  We expose `Wf` + its one-step preservation here; the seam layer threads it
from the Analysis-layer reachability invariants.

## The bridge proof (Stage 3)

Under `Wf` and `CounterResetDest (p+1)` (the honest counter-reset destination set
`{1,6,7,8}` the seam tail uses), the per-side case analysis is:

* `finishPhase10Entry` preserves phase, so `(Transition a b).1.phase = out.1.phase`.
* the epidemic output `ep.1.phase = max(a.phase, b.phase) ≤ p+1` (no error under `Wf`).
* the dispatcher at `ep.1.phase = q ≤ p+1` advances by at most `+1`, reaching `p+2`
  ONLY when `q = p+1` and the agent is a CLOCK whose counter is `0` (the
  `stdCounterSubroutine` advance branch).
* an epidemic-dragged clock enters `p+1` with the FULL (reset) counter `≠ 0`, so the
  zero-counter source clock is `a` itself, ALREADY at phase `p+1` with `counter = 0` —
  a witness to `AtRiskClockZero p c`.

Reference: Doty et al. §6; consumer = `SeamNoOvershoot.lean` / `SeamPairAdapter.lean`;
protocol core = `Protocol/Transition.lean` (FROZEN); reusable pieces =
`SeamPairBound.lean`; blueprint = `HANDOFF_SEAM_NOOVERSHOOT.md`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamPairAdapter

namespace ExactMajority

open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-! ## Stage 1 — the well-formedness predicate `W`, its provenance and preservation. -/

/-- **Per-agent seam well-formedness.**  Exactly enough to forbid every `phaseInit`
error-to-`10` branch on the seam region: no `mcr` role (phase-1 error), and `smallBias`
in the carrier range `{2,3,4}` (phase-`{2,9}` error needs `smallBias ≤ 1 ∨ ≥ 5`). -/
def WfAgent (a : AgentState L K) : Prop :=
  a.role ≠ .mcr ∧ 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4

/-- **Config-level seam well-formedness.** -/
def Wf (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, WfAgent (L := L) (K := K) a

instance (a : AgentState L K) : Decidable (WfAgent (L := L) (K := K) a) := by
  unfold WfAgent; infer_instance

instance (c : Config (AgentState L K)) : Decidable (Wf (L := L) (K := K) c) := by
  unfold Wf; infer_instance

/-- `phaseInit q a` never errors to phase `10` for a well-formed agent at a non-error
init phase `q ≤ 9`: the only error branches are `q = 1 ∧ mcr`, `q ∈ {2,9} ∧ bad
smallBias`, all excluded by `WfAgent`. -/
theorem phaseInit_phase_eq_of_wf (q : Fin 11) (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hq : q.val ≤ 9) :
    (phaseInit L K q a).phase.val = a.phase.val := by
  obtain ⟨hmcr, hlo, hhi⟩ := hwf
  -- smallBias ∈ {2,3,4} ⟹ ¬(smallBias ≤ 1 ∨ smallBias ≥ 5)
  have hbias : ¬ (a.smallBias.val ≤ 1 || a.smallBias.val ≥ 5) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le]
    constructor <;> omega
  fin_cases q
  · rfl
  · -- phase 1
    unfold phaseInit; simp only [↓reduceDIte]
    rw [if_neg hmcr]
    by_cases h2 : a.role = .cr
    · rw [if_pos h2]
    · rw [if_neg h2]
      by_cases h3 : a.role = .clock
      · rw [if_pos h3]
      · rw [if_neg h3]
  · -- phase 2
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    rw [if_neg hbias]
  · -- phase 3
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    rcases a with ⟨_, _, _, role, _⟩; cases role <;> rfl
  · rfl
  · -- phase 5
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    split_ifs <;> rfl
  · -- phase 6
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    split_ifs <;> rfl
  · -- phase 7
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    split_ifs <;> rfl
  · -- phase 8
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
  · -- phase 9
    unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    rw [if_neg hbias]
  · -- phase 10 excluded by hq
    exact absurd hq (by decide)

/-- `phaseInit` preserves `WfAgent` (preserves `smallBias`; never creates an `mcr`). -/
theorem phaseInit_preserves_wf (q : Fin 11) (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) :
    WfAgent (L := L) (K := K) (phaseInit L K q a) := by
  obtain ⟨hmcr, hlo, hhi⟩ := hwf
  refine ⟨?_, ?_, ?_⟩
  · -- role ≠ mcr : phaseInit's only role write is cr → reserve (and enterPhase10 keeps role)
    intro hcontra
    rcases a with ⟨_, _, _, role, _⟩
    fin_cases q <;>
      revert hcontra <;>
      cases role <;>
      simp_all [phaseInit, enterPhase10] <;>
      (try split_ifs) <;> simp_all
  · rw [phaseInit_smallBias_eq]; exact hlo
  · rw [phaseInit_smallBias_eq]; exact hhi

/-- `runInitsBetween` preserves `WfAgent`. -/
theorem runInitsBetween_preserves_wf (oldP q : ℕ) (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) :
    WfAgent (L := L) (K := K) (runInitsBetween L K oldP q a) := by
  unfold runInitsBetween
  have key : ∀ (l : List ℕ) (c : AgentState L K), WfAgent (L := L) (K := K) c →
      WfAgent (L := L) (K := K)
        (List.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
          c l) := by
    intro l
    induction l with
    | nil => intro c hc; simpa using hc
    | cons k ks IH =>
      intro c hc
      simp only [List.foldl_cons]
      apply IH
      by_cases hk : k < 11
      · rw [dif_pos hk]; exact phaseInit_preserves_wf ⟨k, hk⟩ c hc
      · rw [dif_neg hk]; exact hc
  exact key _ a hwf

/-! ## Stage 2 — the epidemic no-error phase identity and the per-side overshoot
case analysis.

Under `Wf`, the epidemic does NOT error to phase `10` on the seam region (`runInitsBetween`
only runs `phaseInit q` for `q ≤ max source phase ≤ 9`, and a well-formed agent's
`phaseInit q` preserves the phase for `q ≤ 9`).  Hence the epidemic output phase equals
the source max, and the dispatcher's per-side overshoot is forced into the clock-counter
advance branch. -/

/-- `runInitsBetween oldP newP` preserves the phase of a well-formed agent when the
destination `newP ≤ 9` (every `phaseInit q` in the fold runs at `q ≤ newP ≤ 9`, none of
which error under `WfAgent`; and `WfAgent` is fold-invariant). -/
theorem runInitsBetween_phase_eq_of_wf (oldP newP : ℕ) (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hnew : newP ≤ 9) :
    (runInitsBetween L K oldP newP a).phase.val = a.phase.val := by
  unfold runInitsBetween
  -- every k in the filter list has k ≤ newP ≤ 9
  have key : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ 9) →
      ∀ (c : AgentState L K), WfAgent (L := L) (K := K) c →
      (List.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
        c l).phase.val = c.phase.val := by
    intro l
    induction l with
    | nil => intro _ c _; rfl
    | cons k ks IH =>
      intro hbound c hc
      simp only [List.foldl_cons]
      by_cases hk : k < 11
      · rw [dif_pos hk]
        have hk9 : (⟨k, hk⟩ : Fin 11).val ≤ 9 := hbound k (List.mem_cons_self ..)
        rw [IH (fun x hx => hbound x (List.mem_cons_of_mem k hx))
              (phaseInit L K ⟨k, hk⟩ c) (phaseInit_preserves_wf ⟨k, hk⟩ c hc)]
        exact phaseInit_phase_eq_of_wf ⟨k, hk⟩ c hc hk9
      · rw [dif_neg hk]
        exact IH (fun x hx => hbound x (List.mem_cons_of_mem k hx)) c hc
  apply key
  · intro x hx
    rw [List.mem_filter] at hx
    have := hx.2
    simp only [decide_eq_true_eq] at this
    omega
  · exact hwf

/-- **The epidemic no-error phase identity (left).**  Under `WfAgent a` and `WfAgent b`,
if both source phases are `≤ 9`, the left epidemic output phase equals the source max
(no error to `10` from either side). -/
theorem phaseEpidemicUpdate_left_phase_eq_max_of_wf (a b : AgentState L K)
    (hwfa : WfAgent (L := L) (K := K) a) (hwfb : WfAgent (L := L) (K := K) b)
    (ha9 : a.phase.val ≤ 9) (hb9 : b.phase.val ≤ 9) :
    (phaseEpidemicUpdate L K a b).1.phase.val = max a.phase.val b.phase.val := by
  unfold phaseEpidemicUpdate
  set p := max a.phase b.phase with hp
  have hpval : p.val = max a.phase.val b.phase.val := by rw [hp]; rfl
  have hp9 : p.val ≤ 9 := by rw [hpval]; omega
  have hwfa' : WfAgent (L := L) (K := K) ({ a with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfa; exact ⟨h1, h2, h3⟩
  have hwfb' : WfAgent (L := L) (K := K) ({ b with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfb; exact ⟨h1, h2, h3⟩
  have hs' : (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val
      = p.val :=
    runInitsBetween_phase_eq_of_wf a.phase.val p.val _ hwfa' hp9
  have ht' : (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val
      = p.val :=
    runInitsBetween_phase_eq_of_wf b.phase.val p.val _ hwfb' hp9
  -- the error branch needs s'.phase = 10 ∨ t'.phase = 10; both are p.val ≤ 9 — false.
  have herr_false :
      ¬ ((a.phase.val < 10 ∨ b.phase.val < 10) ∧
        ((runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = 10 ∨
          (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val = 10)) := by
    rintro ⟨-, hor⟩
    rcases hor with h | h
    · rw [hs'] at h; omega
    · rw [ht'] at h; omega
  simp only [herr_false, if_false]
  exact hs'

/-! ### The phase-advancing primitives advance by at most `+1` (under `Wf` for the
`phaseInit` step). -/

/-- `phaseInit q` preserves the phase of a CLOCK for target `q ∉ {2,9,10}` (the only
`enterPhase10` branches for a clock are phases `2`, `9`, `10`, which check `smallBias`
or always error; phases `1,3,4,5,6,7,8` keep a clock's phase). -/
theorem phaseInit_phase_eq_of_clock (q : Fin 11) (a : AgentState L K)
    (ha : a.role = .clock) (hq : q.val ≠ 2 ∧ q.val ≠ 9 ∧ q.val ≤ 9) :
    (phaseInit L K q a).phase.val = a.phase.val := by
  obtain ⟨hq2, hq9, hq10⟩ := hq
  fin_cases q
  · rfl
  · unfold phaseInit; simp only [↓reduceDIte]
    rw [if_neg (by rw [ha]; decide), if_neg (by rw [ha]; decide), if_pos ha]
  · exact absurd rfl hq2
  · unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
    rcases a with ⟨_, _, _, role, _⟩; cases role <;> rfl
  · rfl
  · unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]; split_ifs <;> rfl
  · unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]; split_ifs <;> rfl
  · unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]; split_ifs <;> rfl
  · unfold phaseInit; simp only [↓reduceDIte, Nat.reduceEqDiff]
  · exact absurd rfl hq9
  · exact absurd hq10 (by decide)

/-- `advancePhase` advances the phase by at most `+1`. -/
theorem advancePhase_phase_le_succ (a : AgentState L K) :
    (advancePhase L K a).phase.val ≤ a.phase.val + 1 := by
  unfold advancePhase
  split
  · simp
  · omega

/-- `advancePhaseWithInit` advances a well-formed agent's phase by at most `+1` when the
result phase is `≤ 9` (so `phaseInit` does not error): `advancePhase` adds at most `1`,
then `phaseInit` preserves it. -/
theorem advancePhaseWithInit_phase_le_succ_of_wf (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (advancePhaseWithInit L K a).phase.val ≤ a.phase.val + 1 := by
  unfold advancePhaseWithInit
  -- WfAgent is preserved by advancePhase (role/smallBias untouched)
  have hwf' : WfAgent (L := L) (K := K) (advancePhase L K a) := by
    obtain ⟨h1, h2, h3⟩ := hwf
    refine ⟨?_, ?_, ?_⟩ <;> (unfold advancePhase; split <;> simp_all)
  have hadv : (advancePhase L K a).phase.val ≤ a.phase.val + 1 := advancePhase_phase_le_succ a
  have hadv9 : (advancePhase L K a).phase.val ≤ 9 := by omega
  rw [phaseInit_phase_eq_of_wf (advancePhase L K a).phase (advancePhase L K a) hwf' hadv9]
  exact hadv

/-- `stdCounterSubroutine` advances a well-formed agent's phase by at most `+1` (when
`phase ≤ 8`): decrement keeps the phase; counter-`0` advance is `advancePhaseWithInit`,
`≤ +1`. -/
theorem stdCounterSubroutine_phase_le_succ_of_wf (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (stdCounterSubroutine L K a).phase.val ≤ a.phase.val + 1 := by
  unfold stdCounterSubroutine
  split_ifs with h
  · exact advancePhaseWithInit_phase_le_succ_of_wf a hwf hle
  · simp

/-- `clockCounterStep` advances a well-formed agent's phase by at most `+1`. -/
theorem clockCounterStep_phase_le_succ_of_wf (a : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (clockCounterStep L K a).phase.val ≤ a.phase.val + 1 := by
  unfold clockCounterStep
  split_ifs
  · exact stdCounterSubroutine_phase_le_succ_of_wf a hwf hle
  · simp

/-- `stdCounterSubroutine` on a CLOCK advances the phase by `≤ +1` when its current
phase `∉ {1,8}` (so the advance target `phase+1 ∉ {2,9,10}` is `enterPhase10`-free for a
clock): the counter-`0` advance is `advancePhase` (`+1`) then an `enterPhase10`-free
`phaseInit`.  No `WfAgent` is needed — a clock never triggers a `phaseInit` error at
these targets. -/
theorem stdCounterSubroutine_phase_le_succ_of_clock (a : AgentState L K)
    (ha : a.role = .clock) (h1 : a.phase.val ≠ 1) (h8 : a.phase.val ≠ 8)
    (hle : a.phase.val ≤ 8) :
    (stdCounterSubroutine L K a).phase.val ≤ a.phase.val + 1 := by
  unfold stdCounterSubroutine
  split_ifs with hctr
  · unfold advancePhaseWithInit
    have hadv : (advancePhase L K a).phase.val ≤ a.phase.val + 1 := advancePhase_phase_le_succ a
    have hadvrole : (advancePhase L K a).role = .clock := by
      unfold advancePhase; split <;> simp [ha]
    have hadveq : (advancePhase L K a).phase.val = a.phase.val + 1 ∨ a.phase.val = 10 := by
      unfold advancePhase; split_ifs with hlt
      · left; simp
      · right; have := a.phase.2; omega
    rcases hadveq with heq | h10
    · have hq : (advancePhase L K a).phase.val ≠ 2 ∧ (advancePhase L K a).phase.val ≠ 9
          ∧ (advancePhase L K a).phase.val ≤ 9 := by rw [heq]; omega
      rw [phaseInit_phase_eq_of_clock (advancePhase L K a).phase (advancePhase L K a)
            hadvrole hq]
      exact hadv
    · omega
  · simp

/-! ### Per-phase left-output `+1` bound (under `Wf`).

Every per-phase rule's LEFT output advances the phase ONLY through
`stdCounterSubroutine` / `clockCounterStep` / `advancePhaseWithInit` applied to a
well-formed agent (the role/smallBias-touching pre-steps set `role` to a non-`mcr` value
and preserve `smallBias`), so the advance is `≤ +1`.  We prove the bound phase-by-phase
for the phases the seam can dispatch (`q ≤ 8`). -/

/-- Phase 1 left output advances by `≤ +1` (it is `clockCounterStep` of a well-formed
agent, modulo a `smallBias`-only averaging pre-step). -/
theorem Phase1Transition_left_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (Phase1Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  by_cases hmain : a.role = .main ∧ b.role = .main
  · -- main–main: the averaged agent has role = main ≠ clock, so clockCounterStep is id.
    obtain ⟨ha, hb⟩ := hmain
    have hval : (Phase1Transition L K a b).1.phase.val = a.phase.val := by
      simp [Phase1Transition, ha, hb, clockCounterStep]
    omega
  · have hval : (Phase1Transition L K a b).1 = clockCounterStep L K a := by
      unfold Phase1Transition
      rw [if_neg hmain]
    rw [hval]
    exact clockCounterStep_phase_le_succ_of_wf a hwf hle

/-- Phase 4 left output advances by `≤ +1` (`advancePhase` or identity). -/
theorem Phase4Transition_left_phase_le_succ (a b : AgentState L K) :
    (Phase4Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  unfold Phase4Transition; dsimp
  split_ifs
  · exact advancePhase_phase_le_succ a
  · exact Nat.le_succ _

/-- Phase 0 left output advances by `≤ +1` when the agent is at phase `0` (the only
phase that dispatches `Phase0Transition`): the 5-rule cascade preserves the phase up to
`s4`, and the final Rule-5 `stdCounterSubroutine` (on a clock `s4` at phase `0`) advances
by `≤ +1`. -/
theorem Phase0Transition_left_phase_le_succ_of_phase0 (a b : AgentState L K)
    (h0 : a.phase.val = 0) :
    (Phase0Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  -- replicate the cascade of Phase0Transition_phase_nondec, tracking the LEFT phase
  let s1 := if a.role = .mcr ∧ b.role = .mcr then
    { a with role := .main, smallBias := addSmallBias a.smallBias b.smallBias } else a
  let t1 := if a.role = .mcr ∧ b.role = .mcr then
    { b with role := .cr, smallBias := ⟨3, by decide⟩ } else b
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
    else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  have hs1 : a.phase.val = s1.phase.val := by dsimp [s1]; split_ifs <;> rfl
  have hs2 : s1.phase.val = s2.phase.val := by dsimp [s2]; split_ifs <;> rfl
  have hs3 : s2.phase.val = s3.phase.val := by dsimp [s3]; split_ifs <;> rfl
  have hs3' : s3.phase.val = s3'.phase.val := by dsimp [s3']
  have hs4 : s3'.phase.val = s4.phase.val := by dsimp [s4]; split_ifs <;> rfl
  have hs4phase : s4.phase.val = 0 := by rw [← hs4, ← hs3', ← hs3, ← hs2, ← hs1, h0]
  have hs5 : s5.phase.val ≤ s4.phase.val + 1 := by
    dsimp [s5]; split_ifs with hcl
    · exact stdCounterSubroutine_phase_le_succ_of_clock s4 hcl.1
        (by rw [hs4phase]; decide) (by rw [hs4phase]; decide) (by rw [hs4phase]; decide)
    · omega
  show s5.phase.val ≤ a.phase.val + 1
  omega

/-- Phase 3 left output advances by at most one when the agent is at phase 3 (the only
phase that dispatches Phase3Transition): Rule 1's `stdCounterSubroutine` on a clock at
phase 3 advances by at most one; the minute/hour-drag and `phase3CancelSplit`
pre/post-steps preserve the phase. -/
theorem Phase3Transition_left_phase_le_succ_of_phase3 (a b : AgentState L K)
    (h3 : a.phase.val = 3) :
    (Phase3Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  -- `Phase3Transition.1.phase = s1.phase` (Rule 1); s1 is a minute-drag (phase-preserving)
  -- or `stdCounterSubroutine` on a clock at phase 3 (≤ +1).
  set s1 : AgentState L K :=
    (if a.role = .clock ∧ b.role = .clock then
      if a.minute ≠ b.minute then { a with minute := max a.minute b.minute }
      else if _h : a.minute.val < K * (L + 1) then
        { a with minute := ⟨a.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K a
    else a) with hs1def
  have hphaseeq : (Phase3Transition L K a b).1.phase = s1.phase :=
    (Phase3Transition_left_output_eq_rule1 (L := L) (K := K) a b s1 hs1def).2
  have hs1 : s1.phase.val ≤ a.phase.val + 1 := by
    rw [hs1def]
    split_ifs with hcl hmin hlt
    · exact le_trans (le_of_eq (show ({ a with minute := max a.minute b.minute }
        : AgentState L K).phase.val = a.phase.val from rfl)) (Nat.le_succ _)
    · exact le_trans (le_of_eq (show ({ a with minute := ⟨a.minute.val + 1, by omega⟩ }
        : AgentState L K).phase.val = a.phase.val from rfl)) (Nat.le_succ _)
    · exact stdCounterSubroutine_phase_le_succ_of_clock a hcl.1
        (by rw [h3]; decide) (by rw [h3]; decide) (by rw [h3]; decide)
    · exact Nat.le_succ _
  have : (Phase3Transition L K a b).1.phase.val = s1.phase.val := by rw [hphaseeq]
  omega

/-- Phase 2 left output advances by `≤ +1` (`advancePhaseWithInit` of the
opinions-updated — hence still well-formed — agent, or an output-only change). -/
theorem Phase2Transition_left_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (Phase2Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  have hwf' : WfAgent (L := L) (K := K)
      ({ a with opinions := opinionsUnion a.opinions b.opinions } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwf; exact ⟨h1, h2, h3⟩
  have hle' : ({ a with opinions := opinionsUnion a.opinions b.opinions }
      : AgentState L K).phase.val ≤ 8 := hle
  unfold Phase2Transition
  dsimp only
  split_ifs
  · -- advancePhaseWithInit on the opinions-updated agent (same phase as a)
    exact advancePhaseWithInit_phase_le_succ_of_wf _ hwf' hle'
  · exact Nat.le_succ _
  · exact Nat.le_succ _
  · exact Nat.le_succ _
  · exact Nat.le_succ _

/-- Phase 5 left output advances by `≤ +1`.  For a clock initiator it is
`stdCounterSubroutine` (`Phase5Transition_left_clock`); otherwise the role-preserving
`doSample` pre-step keeps the agent a non-clock, so the final counter `if` is identity
and the phase is preserved. -/
theorem Phase5Transition_left_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (Phase5Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  by_cases hc : a.role = .clock
  · rw [Phase5Transition_left_clock a b hc]
    exact stdCounterSubroutine_phase_le_succ_of_wf a hwf hle
  · have hval : (Phase5Transition L K a b).1.phase.val = a.phase.val := by
      simp only [Phase5Transition]
      split_ifs with h1 h2 <;> simp_all
    omega

/-- `doSplit` preserves the LEFT phase (it writes only `role`/`bias`). -/
theorem doSplit_phase_fst (a b : AgentState L K) :
    (doSplit L K a b).1.phase.val = a.phase.val := by
  unfold doSplit
  match b.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

/-- `doSplit` preserves the RIGHT phase. -/
theorem doSplit_phase_snd (a b : AgentState L K) :
    (doSplit L K a b).2.phase.val = b.phase.val := by
  unfold doSplit
  match b.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

/-- `doSplit` sets the LEFT role to `main` on its active branch. -/
theorem doSplit_role_fst_ne_clock (a b : AgentState L K) (ha : a.role ≠ .clock) :
    (doSplit L K a b).1.role ≠ .clock := by
  unfold doSplit
  match b.bias with
  | Bias.zero => simpa using ha
  | Bias.dyadic _ _ => simp; split_ifs <;> first | (intro h; exact absurd h (by decide)) | simpa using ha

/-- `cancelSplit` preserves the LEFT phase (it writes only `bias`). -/
theorem cancelSplit_phase_fst (a b : AgentState L K) :
    (cancelSplit L K a b).1.phase.val = a.phase.val := by
  unfold cancelSplit
  match a.bias, b.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

/-- `absorbConsume` preserves the LEFT phase (it writes only `bias`/`full`). -/
theorem absorbConsume_phase_fst (a b : AgentState L K) :
    (absorbConsume L K a b).1.phase.val = a.phase.val := by
  unfold absorbConsume
  match a.bias, b.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos i, .dyadic .neg j => simp; split_ifs <;> simp
  | .dyadic .neg i, .dyadic .pos j => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

/-- `cancelSplit` preserves the RIGHT phase. -/
theorem cancelSplit_phase_snd (a b : AgentState L K) :
    (cancelSplit L K a b).2.phase.val = b.phase.val := by
  unfold cancelSplit
  match a.bias, b.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

/-- `absorbConsume` preserves the RIGHT phase. -/
theorem absorbConsume_phase_snd (a b : AgentState L K) :
    (absorbConsume L K a b).2.phase.val = b.phase.val := by
  unfold absorbConsume
  match a.bias, b.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos i, .dyadic .neg j => simp; split_ifs <;> simp
  | .dyadic .neg i, .dyadic .pos j => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

/-- Phase 6 left output advances by `≤ +1` (`stdCounterSubroutine` for a clock; the
`doSplit` pre-step sets a non-clock role, so the counter `if` is identity otherwise). -/
theorem Phase6Transition_left_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (Phase6Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  by_cases hc : a.role = .clock
  · rw [Phase6Transition_left_clock a b hc]
    exact stdCounterSubroutine_phase_le_succ_of_wf a hwf hle
  · -- ¬clock: s1 = a or doSplit.1 (role main) or doSplit.2 (role = a.role); s1.role ≠ clock.
    have hval : (Phase6Transition L K a b).1.phase.val = a.phase.val := by
      have hs1role : (if a.role = .reserve ∧ b.role = .main ∧ (b.bias ≠ .zero) then
            (doSplit L K a b).1
          else if b.role = .reserve ∧ a.role = .main ∧ (a.bias ≠ .zero) then
            (doSplit L K b a).2
          else a).role ≠ .clock := by
        split_ifs
        · exact doSplit_role_fst_ne_clock a b hc
        · rw [doSplit_role_snd]; exact hc
        · exact hc
      have hs1phase : (if a.role = .reserve ∧ b.role = .main ∧ (b.bias ≠ .zero) then
            (doSplit L K a b).1
          else if b.role = .reserve ∧ a.role = .main ∧ (a.bias ≠ .zero) then
            (doSplit L K b a).2
          else a).phase.val = a.phase.val := by
        split_ifs
        · exact doSplit_phase_fst a b
        · exact doSplit_phase_snd b a
        · rfl
      show (if _ then stdCounterSubroutine L K _ else _).phase.val = a.phase.val
      rw [if_neg hs1role, hs1phase]
    omega

/-- Phase 7 left output advances by `≤ +1` (`stdCounterSubroutine` for a clock; the
role-preserving `cancelSplit` pre-step keeps a non-clock a non-clock otherwise). -/
theorem Phase7Transition_left_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (Phase7Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  by_cases hc : a.role = .clock
  · rw [Phase7Transition_left_clock a b hc]
    exact stdCounterSubroutine_phase_le_succ_of_wf a hwf hle
  · have hval : (Phase7Transition L K a b).1.phase.val = a.phase.val := by
      have hs1role : (if a.role = .main ∧ b.role = .main then
            (cancelSplit L K a b).1 else a).role ≠ .clock := by
        split_ifs
        · rw [cancelSplit_role_fst]; exact hc
        · exact hc
      have hs1phase : (if a.role = .main ∧ b.role = .main then
            (cancelSplit L K a b).1 else a).phase.val = a.phase.val := by
        split_ifs
        · exact cancelSplit_phase_fst a b
        · rfl
      show (if _ then stdCounterSubroutine L K _ else _).phase.val = a.phase.val
      rw [if_neg hs1role, hs1phase]
    omega

/-- Phase 8 left output advances by `≤ +1` (`stdCounterSubroutine` for a clock; the
role-preserving `absorbConsume` pre-step keeps a non-clock a non-clock otherwise). -/
theorem Phase8Transition_left_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) a) (hle : a.phase.val ≤ 8) :
    (Phase8Transition L K a b).1.phase.val ≤ a.phase.val + 1 := by
  by_cases hc : a.role = .clock
  · rw [Phase8Transition_left_clock a b hc]
    exact stdCounterSubroutine_phase_le_succ_of_wf a hwf hle
  · have hval : (Phase8Transition L K a b).1.phase.val = a.phase.val := by
      have hs1role : (if a.role = .main ∧ b.role = .main then
            (absorbConsume L K a b).1 else a).role ≠ .clock := by
        split_ifs
        · rw [absorbConsume_role_fst]; exact hc
        · exact hc
      have hs1phase : (if a.role = .main ∧ b.role = .main then
            (absorbConsume L K a b).1 else a).phase.val = a.phase.val := by
        split_ifs
        · exact absorbConsume_phase_fst a b
        · rfl
      show (if _ then stdCounterSubroutine L K _ else _).phase.val = a.phase.val
      rw [if_neg hs1role, hs1phase]
    omega

/-! ### Stage 2 capstone — the dispatcher one-step `+1` bound and the advance
characterization. -/

/-- The left epidemic output is well-formed under `Wf` on both inputs (and both phases
`≤ 9`): no error, so `ep.1 = runInitsBetween … { a with phase := max }`, which preserves
`WfAgent` (`runInitsBetween_preserves_wf`). -/
theorem phaseEpidemicUpdate_left_preserves_wf (a b : AgentState L K)
    (hwfa : WfAgent (L := L) (K := K) a) (hwfb : WfAgent (L := L) (K := K) b)
    (ha9 : a.phase.val ≤ 9) (hb9 : b.phase.val ≤ 9) :
    WfAgent (L := L) (K := K) (phaseEpidemicUpdate L K a b).1 := by
  unfold phaseEpidemicUpdate
  set p := max a.phase b.phase with hp
  have hpval : p.val = max a.phase.val b.phase.val := by rw [hp]; rfl
  have hp9 : p.val ≤ 9 := by rw [hpval]; omega
  have hwfa' : WfAgent (L := L) (K := K) ({ a with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfa; exact ⟨h1, h2, h3⟩
  have hwfb' : WfAgent (L := L) (K := K) ({ b with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfb; exact ⟨h1, h2, h3⟩
  have hs' : (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = p.val :=
    runInitsBetween_phase_eq_of_wf a.phase.val p.val _ hwfa' hp9
  have ht' : (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val = p.val :=
    runInitsBetween_phase_eq_of_wf b.phase.val p.val _ hwfb' hp9
  have herr_false :
      ¬ ((a.phase.val < 10 ∨ b.phase.val < 10) ∧
        ((runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = 10 ∨
          (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val = 10)) := by
    rintro ⟨-, hor⟩
    rcases hor with h | h
    · rw [hs'] at h; omega
    · rw [ht'] at h; omega
  simp only [herr_false, if_false]
  exact runInitsBetween_preserves_wf a.phase.val p.val _ hwfa'

/-- The right epidemic output phase equals the source max under `Wf` (no error). -/
theorem phaseEpidemicUpdate_right_phase_eq_max_of_wf (a b : AgentState L K)
    (hwfa : WfAgent (L := L) (K := K) a) (hwfb : WfAgent (L := L) (K := K) b)
    (ha9 : a.phase.val ≤ 9) (hb9 : b.phase.val ≤ 9) :
    (phaseEpidemicUpdate L K a b).2.phase.val = max a.phase.val b.phase.val := by
  unfold phaseEpidemicUpdate
  set p := max a.phase b.phase with hp
  have hpval : p.val = max a.phase.val b.phase.val := by rw [hp]; rfl
  have hp9 : p.val ≤ 9 := by rw [hpval]; omega
  have hwfa' : WfAgent (L := L) (K := K) ({ a with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfa; exact ⟨h1, h2, h3⟩
  have hwfb' : WfAgent (L := L) (K := K) ({ b with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfb; exact ⟨h1, h2, h3⟩
  have hs' : (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = p.val :=
    runInitsBetween_phase_eq_of_wf a.phase.val p.val _ hwfa' hp9
  have ht' : (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val = p.val :=
    runInitsBetween_phase_eq_of_wf b.phase.val p.val _ hwfb' hp9
  have herr_false :
      ¬ ((a.phase.val < 10 ∨ b.phase.val < 10) ∧
        ((runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = 10 ∨
          (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val = 10)) := by
    rintro ⟨-, hor⟩
    rcases hor with h | h
    · rw [hs'] at h; omega
    · rw [ht'] at h; omega
  simp only [herr_false, if_false]
  exact ht'

/-- The right epidemic output is well-formed under `Wf` (no error). -/
theorem phaseEpidemicUpdate_right_preserves_wf (a b : AgentState L K)
    (hwfa : WfAgent (L := L) (K := K) a) (hwfb : WfAgent (L := L) (K := K) b)
    (ha9 : a.phase.val ≤ 9) (hb9 : b.phase.val ≤ 9) :
    WfAgent (L := L) (K := K) (phaseEpidemicUpdate L K a b).2 := by
  unfold phaseEpidemicUpdate
  set p := max a.phase b.phase with hp
  have hpval : p.val = max a.phase.val b.phase.val := by rw [hp]; rfl
  have hp9 : p.val ≤ 9 := by rw [hpval]; omega
  have hwfa' : WfAgent (L := L) (K := K) ({ a with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfa; exact ⟨h1, h2, h3⟩
  have hwfb' : WfAgent (L := L) (K := K) ({ b with phase := p } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwfb; exact ⟨h1, h2, h3⟩
  have hs' : (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = p.val :=
    runInitsBetween_phase_eq_of_wf a.phase.val p.val _ hwfa' hp9
  have ht' : (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val = p.val :=
    runInitsBetween_phase_eq_of_wf b.phase.val p.val _ hwfb' hp9
  have herr_false :
      ¬ ((a.phase.val < 10 ∨ b.phase.val < 10) ∧
        ((runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = 10 ∨
          (runInitsBetween L K b.phase.val p.val ({ b with phase := p })).phase.val = 10)) := by
    rintro ⟨-, hor⟩
    rcases hor with h | h
    · rw [hs'] at h; omega
    · rw [ht'] at h; omega
  simp only [herr_false, if_false]
  exact runInitsBetween_preserves_wf b.phase.val p.val _ hwfb'

/-- **Dispatcher one-step `+1` bound (left).**  Under `Wf` on both inputs with both
phases `≤ p+1` (`≤ 8`), the left `Transition` output phase is at most `max(a,b)+1`:
`finishPhase10Entry` preserves the phase, so it equals the phase-`q` dispatch output on
`ep.1` (`q = ep.1.phase = max(a,b) ≤ p+1 ≤ 8`), which is `≤ q+1` by the per-phase
bounds. -/
theorem Transition_left_phase_le_ep_succ_of_wf (a b : AgentState L K)
    (hwfa : WfAgent (L := L) (K := K) a) (hwfb : WfAgent (L := L) (K := K) b)
    (ha8 : a.phase.val ≤ 8) (hb8 : b.phase.val ≤ 8) :
    (Transition L K a b).1.phase.val ≤ max a.phase.val b.phase.val + 1 := by
  -- ep.1.phase = max(a,b) ≤ 8; ep.1 is well-formed.
  have hepphase : (phaseEpidemicUpdate L K a b).1.phase.val = max a.phase.val b.phase.val :=
    phaseEpidemicUpdate_left_phase_eq_max_of_wf a b hwfa hwfb (by omega) (by omega)
  have hepwf : WfAgent (L := L) (K := K) (phaseEpidemicUpdate L K a b).1 :=
    phaseEpidemicUpdate_left_preserves_wf a b hwfa hwfb (by omega) (by omega)
  have hep8 : (phaseEpidemicUpdate L K a b).1.phase.val ≤ 8 := by rw [hepphase]; omega
  -- Transition.1.phase = dispatch output phase (finishPhase10Entry preserves phase)
  set s' := (phaseEpidemicUpdate L K a b).1 with hs'def
  set t' := (phaseEpidemicUpdate L K a b).2 with ht'def
  have hdisp : (Transition L K a b).1.phase.val ≤ s'.phase.val + 1 := by
    rw [show (Transition L K a b).1 = finishPhase10Entry L K s'
          (match s'.phase with
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
            | _ => (s', t')).1 from rfl]
    rw [finishPhase10Entry_phase_val]
    rcases hphase : s'.phase with ⟨n, hn⟩
    have hn8 : n ≤ 8 := by rw [hphase] at hep8; exact hep8
    have hs'wf : WfAgent (L := L) (K := K) s' := hepwf
    have hns' : s'.phase.val = n := by rw [hphase]
    match n, hn, hn8 with
    | 0, _, _ => simp only [hphase]
                 have := Phase0Transition_left_phase_le_succ_of_phase0 s' t' hns'; omega
    | 1, _, _ => simp only [hphase]
                 have := Phase1Transition_left_phase_le_succ_of_wf s' t' hs'wf (by rw [hns']; omega)
                 omega
    | 2, _, _ => simp only [hphase]
                 have := Phase2Transition_left_phase_le_succ_of_wf s' t' hs'wf (by rw [hns']; omega)
                 omega
    | 3, _, _ => simp only [hphase]
                 have := Phase3Transition_left_phase_le_succ_of_phase3 s' t' hns'; omega
    | 4, _, _ => simp only [hphase]
                 have := Phase4Transition_left_phase_le_succ s' t'; omega
    | 5, _, _ => simp only [hphase]
                 have := Phase5Transition_left_phase_le_succ_of_wf s' t' hs'wf (by rw [hns']; omega)
                 omega
    | 6, _, _ => simp only [hphase]
                 have := Phase6Transition_left_phase_le_succ_of_wf s' t' hs'wf (by rw [hns']; omega)
                 omega
    | 7, _, _ => simp only [hphase]
                 have := Phase7Transition_left_phase_le_succ_of_wf s' t' hs'wf (by rw [hns']; omega)
                 omega
    | 8, _, _ => simp only [hphase]
                 have := Phase8Transition_left_phase_le_succ_of_wf s' t' hs'wf
                   (le_of_eq hns')
                 omega
    | n + 9, hn, hn8 => omega
  rw [← hepphase]; exact hdisp

/-! ### The per-side advance characterization for the counter-reset destinations. -/

/-- `stdCounterSubroutine` keeps the phase unless `counter = 0` (the decrement branch
preserves the phase). -/
theorem stdCounterSubroutine_phase_eq_of_counter_ne_zero (a : AgentState L K)
    (hctr : a.counter.val ≠ 0) :
    (stdCounterSubroutine L K a).phase.val = a.phase.val := by
  unfold stdCounterSubroutine; rw [dif_neg hctr]

/-- Phase 1 keeps a non-clock LEFT initiator's phase (`clockCounterStep` is identity off
clocks; the main–main averaging pre-step is `smallBias`-only). -/
theorem Phase1Transition_left_phase_eq_of_not_clock (e f : AgentState L K)
    (hc : e.role ≠ .clock) :
    (Phase1Transition L K e f).1.phase.val = e.phase.val := by
  by_cases hmain : e.role = .main ∧ f.role = .main
  · simp [Phase1Transition, hmain.1, hmain.2, clockCounterStep]
  · have : (Phase1Transition L K e f).1 = clockCounterStep L K e := by
      unfold Phase1Transition; rw [if_neg hmain]
    rw [this]; unfold clockCounterStep; rw [if_neg hc]

/-- Phase 6 keeps a non-clock LEFT initiator's phase. -/
theorem Phase6Transition_left_phase_eq_of_not_clock (e f : AgentState L K)
    (hc : e.role ≠ .clock) :
    (Phase6Transition L K e f).1.phase.val = e.phase.val := by
  simp only [Phase6Transition]
  have hs1role : (if e.role = .reserve ∧ f.role = .main ∧ (f.bias ≠ .zero) then
        (doSplit L K e f).1
      else if f.role = .reserve ∧ e.role = .main ∧ (e.bias ≠ .zero) then
        (doSplit L K f e).2 else e).role ≠ .clock := by
    split_ifs
    · exact doSplit_role_fst_ne_clock e f hc
    · rw [doSplit_role_snd]; exact hc
    · exact hc
  have hs1phase : (if e.role = .reserve ∧ f.role = .main ∧ (f.bias ≠ .zero) then
        (doSplit L K e f).1
      else if f.role = .reserve ∧ e.role = .main ∧ (e.bias ≠ .zero) then
        (doSplit L K f e).2 else e).phase.val = e.phase.val := by
    split_ifs
    · exact doSplit_phase_fst e f
    · exact doSplit_phase_snd f e
    · rfl
  show (if _ then stdCounterSubroutine L K _ else _).phase.val = e.phase.val
  rw [if_neg hs1role, hs1phase]

/-- Phase 7 keeps a non-clock LEFT initiator's phase. -/
theorem Phase7Transition_left_phase_eq_of_not_clock (e f : AgentState L K)
    (hc : e.role ≠ .clock) :
    (Phase7Transition L K e f).1.phase.val = e.phase.val := by
  simp only [Phase7Transition]
  have hs1role : (if e.role = .main ∧ f.role = .main then
        (cancelSplit L K e f).1 else e).role ≠ .clock := by
    split_ifs
    · rw [cancelSplit_role_fst]; exact hc
    · exact hc
  have hs1phase : (if e.role = .main ∧ f.role = .main then
        (cancelSplit L K e f).1 else e).phase.val = e.phase.val := by
    split_ifs
    · exact cancelSplit_phase_fst e f
    · rfl
  show (if _ then stdCounterSubroutine L K _ else _).phase.val = e.phase.val
  rw [if_neg hs1role, hs1phase]

/-- Phase 8 keeps a non-clock LEFT initiator's phase. -/
theorem Phase8Transition_left_phase_eq_of_not_clock (e f : AgentState L K)
    (hc : e.role ≠ .clock) :
    (Phase8Transition L K e f).1.phase.val = e.phase.val := by
  simp only [Phase8Transition]
  have hs1role : (if e.role = .main ∧ f.role = .main then
        (absorbConsume L K e f).1 else e).role ≠ .clock := by
    split_ifs
    · rw [absorbConsume_role_fst]; exact hc
    · exact hc
  have hs1phase : (if e.role = .main ∧ f.role = .main then
        (absorbConsume L K e f).1 else e).phase.val = e.phase.val := by
    split_ifs
    · exact absorbConsume_phase_fst e f
    · rfl
  show (if _ then stdCounterSubroutine L K _ else _).phase.val = e.phase.val
  rw [if_neg hs1role, hs1phase]

/-- The phase-`q` LEFT dispatch output `PhaseQTransition.1.phase` for a clock initiator at
a counter-reset destination `q ∈ {1,6,7,8}` is `stdCounterSubroutine`'s phase (phase 1 =
`clockCounterStep`, identical on clocks). -/
theorem dispatch_left_clock_eq_std (e f : AgentState L K) (q : ℕ)
    (hq : CounterResetDest q) (heq : e.phase.val = q) (hc : e.role = .clock) :
    ((match e.phase with
        | ⟨1, _⟩ => Phase1Transition L K e f
        | ⟨6, _⟩ => Phase6Transition L K e f
        | ⟨7, _⟩ => Phase7Transition L K e f
        | ⟨8, _⟩ => Phase8Transition L K e f
        | _ => (e, f)).1).phase.val = (stdCounterSubroutine L K e).phase.val := by
  rcases hq with h | h | h | h <;>
    (have hfe : e.phase = (⟨q, by rcases h with rfl <;> omega⟩ : Fin 11) := Fin.ext heq
     rw [hfe]; subst h; simp only)
  · rw [Phase1Transition_left_clock e f hc]; unfold clockCounterStep; rw [if_pos hc]
  · rw [Phase6Transition_left_clock e f hc]
  · rw [Phase7Transition_left_clock e f hc]
  · rw [Phase8Transition_left_clock e f hc]

/-- The phase-`q` LEFT dispatch output keeps a NON-clock initiator's phase, for a
counter-reset destination `q ∈ {1,6,7,8}`. -/
theorem dispatch_left_not_clock_phase_eq (e f : AgentState L K) (q : ℕ)
    (hq : CounterResetDest q) (heq : e.phase.val = q) (hc : e.role ≠ .clock) :
    ((match e.phase with
        | ⟨1, _⟩ => Phase1Transition L K e f
        | ⟨6, _⟩ => Phase6Transition L K e f
        | ⟨7, _⟩ => Phase7Transition L K e f
        | ⟨8, _⟩ => Phase8Transition L K e f
        | _ => (e, f)).1).phase.val = q := by
  rcases hq with h | h | h | h
  · have hfe : e.phase = (⟨1, by omega⟩ : Fin 11) := Fin.ext (by rw [heq, h])
    rw [hfe]; simp only
    rw [show (Phase1Transition L K e f).1.phase.val = e.phase.val from
      Phase1Transition_left_phase_eq_of_not_clock e f hc, heq, h]
  · have hfe : e.phase = (⟨6, by omega⟩ : Fin 11) := Fin.ext (by rw [heq, h])
    rw [hfe]; simp only
    rw [show (Phase6Transition L K e f).1.phase.val = e.phase.val from
      Phase6Transition_left_phase_eq_of_not_clock e f hc, heq, h]
  · have hfe : e.phase = (⟨7, by omega⟩ : Fin 11) := Fin.ext (by rw [heq, h])
    rw [hfe]; simp only
    rw [show (Phase7Transition L K e f).1.phase.val = e.phase.val from
      Phase7Transition_left_phase_eq_of_not_clock e f hc, heq, h]
  · have hfe : e.phase = (⟨8, by omega⟩ : Fin 11) := Fin.ext (by rw [heq, h])
    rw [hfe]; simp only
    rw [show (Phase8Transition L K e f).1.phase.val = e.phase.val from
      Phase8Transition_left_phase_eq_of_not_clock e f hc, heq, h]

/-- **Left advance ⟹ source clock with zero counter (counter-reset destination).**  Under
`Wf` on both inputs (and the no-overshoot phase ceiling `≤ p+1`), if `ep.1.phase = p+1 ∈
{1,6,7,8}` and the LEFT `Transition` output advances beyond `p+1`, then `ep.1` is a CLOCK
with `counter = 0`. -/
theorem Transition_left_advance_imp_ep_clock_zero (a b : AgentState L K) (p : ℕ)
    (hq : CounterResetDest (p + 1))
    (hwfa : WfAgent (L := L) (K := K) a) (hwfb : WfAgent (L := L) (K := K) b)
    (ha : a.phase.val ≤ p + 1) (hb : b.phase.val ≤ p + 1)
    (hepphase : (phaseEpidemicUpdate L K a b).1.phase.val = p + 1)
    (hadv : (Transition L K a b).1.phase.val > p + 1) :
    (phaseEpidemicUpdate L K a b).1.role = .clock ∧
      (phaseEpidemicUpdate L K a b).1.counter.val = 0 := by
  set e := (phaseEpidemicUpdate L K a b).1 with hedef
  set f := (phaseEpidemicUpdate L K a b).2 with hfdef
  have hp1le8 : p + 1 ≤ 8 := by rcases hq with h | h | h | h <;> omega
  -- Transition.1.phase = dispatch output phase
  have hdispval : (Transition L K a b).1.phase.val =
      ((match e.phase with
        | ⟨1, _⟩ => Phase1Transition L K e f
        | ⟨6, _⟩ => Phase6Transition L K e f
        | ⟨7, _⟩ => Phase7Transition L K e f
        | ⟨8, _⟩ => Phase8Transition L K e f
        | _ => (e, f)).1).phase.val := by
    -- only the {1,6,7,8} arms are reachable since e.phase = p+1 ∈ {1,6,7,8}
    rw [show (Transition L K a b).1 = finishPhase10Entry L K e
          (match e.phase with
            | ⟨0, _⟩ => Phase0Transition L K e f
            | ⟨1, _⟩ => Phase1Transition L K e f
            | ⟨2, _⟩ => Phase2Transition L K e f
            | ⟨3, _⟩ => Phase3Transition L K e f
            | ⟨4, _⟩ => Phase4Transition L K e f
            | ⟨5, _⟩ => Phase5Transition L K e f
            | ⟨6, _⟩ => Phase6Transition L K e f
            | ⟨7, _⟩ => Phase7Transition L K e f
            | ⟨8, _⟩ => Phase8Transition L K e f
            | ⟨9, _⟩ => Phase9Transition L K e f
            | ⟨10, _⟩ => Phase10Transition L K e f
            | _ => (e, f)).1 from rfl]
    rw [finishPhase10Entry_phase_val]
    rcases hq with h | h | h | h
    · rw [show e.phase = (⟨1, by omega⟩ : Fin 11) from Fin.ext (by rw [hepphase, h])]
    · rw [show e.phase = (⟨6, by omega⟩ : Fin 11) from Fin.ext (by rw [hepphase, h])]
    · rw [show e.phase = (⟨7, by omega⟩ : Fin 11) from Fin.ext (by rw [hepphase, h])]
    · rw [show e.phase = (⟨8, by omega⟩ : Fin 11) from Fin.ext (by rw [hepphase, h])]
  rw [hdispval] at hadv
  by_cases hc : e.role = .clock
  · -- clock: output = std e; advance ⟹ counter 0
    refine ⟨hc, ?_⟩
    by_contra hctr
    rw [dispatch_left_clock_eq_std e f (p + 1) hq hepphase hc] at hadv
    rw [stdCounterSubroutine_phase_eq_of_counter_ne_zero e hctr, hepphase] at hadv
    omega
  · -- non-clock: phase preserved at p+1, contradicting the advance
    exfalso
    rw [dispatch_left_not_clock_phase_eq e f (p + 1) hq hepphase hc] at hadv
    omega

/-- **Source-tracing (left).**  If the left epidemic output `ep.1` is a clock at phase
`p+1 ∈ {1,6,7,8}` with `counter = 0`, then the SOURCE `a` is already a clock at phase
`p+1` with `counter = 0`.  (An epidemic-dragged immigrant clock would be reset to the
FULL counter `≠ 0`; so `ep.1` with `counter = 0` was not dragged — `a.phase = p+1` and the
epidemic left `a`'s clock untouched.) -/
theorem ep_left_clock_zero_imp_source (a b : AgentState L K) (p : ℕ)
    (hq : CounterResetDest (p + 1))
    (hrole : (phaseEpidemicUpdate L K a b).1.role = .clock)
    (hphase : (phaseEpidemicUpdate L K a b).1.phase.val = p + 1)
    (hctr : (phaseEpidemicUpdate L K a b).1.counter.val = 0) :
    a.role = .clock ∧ a.phase.val = p + 1 ∧ a.counter.val = 0 := by
  have hqT : CounterTimedPhase (p + 1) := CounterTimedPhase_of_CounterResetDest hq
  have hple : p + 1 ≤ 8 := by rcases hq with h | h | h | h <;> omega
  set ep1 := (phaseEpidemicUpdate L K a b).1 with hep1
  rcases lt_trichotomy a.phase.val (p + 1) with hlt | heq | hgt
  · -- immigrant ⟹ full counter ≠ 0, contradicting hctr
    exfalso
    have hfull := phaseEpidemicUpdate_left_immigrant_full a b (p + 1) hqT hlt hrole hphase
    rw [← hep1] at hfull; omega
  · -- a.phase = p+1: epidemic leaves a's clock untouched.
    have hba : b.phase.val ≤ a.phase.val := by
      by_contra hgt
      rw [not_le] at hgt
      have hge : b.phase.val ≤ ep1.phase.val := by
        rw [hep1]
        exact le_trans (le_max_right _ _)
          (phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) a b)
      rw [hphase] at hge; omega
    obtain ⟨hctra, hrolea, hphase_or⟩ := phaseEpidemicUpdate_left_id_of_ge a b hba
    refine ⟨?_, heq, ?_⟩
    · rw [← hrolea]; exact hrole
    · rw [show a.counter.val = ep1.counter.val from by rw [hctra], hctr]
  · -- a.phase > p+1 contradicts ep1.phase = p+1 ≥ a.phase (epidemic non-decreasing).
    exfalso
    have hge : a.phase.val ≤ ep1.phase.val := by
      rw [hep1]
      exact le_trans (le_max_left _ _)
        (phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) a b)
    rw [hphase] at hge; omega

/-! ## Stage 3 (right side) — the mirror per-phase `+1` bounds, not-clock phase
preservation, and the right dispatch/advance/source-trace.  Structure identical to the
left; the right-clock reductions live in `SeamPairAdapter`. -/

/-- Phase 1 RIGHT output advances by `≤ +1` (`clockCounterStep` of the averaged
responder). -/
theorem Phase1Transition_right_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) b) (hle : b.phase.val ≤ 8) :
    (Phase1Transition L K a b).2.phase.val ≤ b.phase.val + 1 := by
  by_cases hmain : a.role = .main ∧ b.role = .main
  · obtain ⟨ha, hb⟩ := hmain
    have hval : (Phase1Transition L K a b).2.phase.val = b.phase.val := by
      simp [Phase1Transition, ha, hb, clockCounterStep]
    omega
  · have hval : (Phase1Transition L K a b).2 = clockCounterStep L K b := by
      unfold Phase1Transition; rw [if_neg hmain]
    rw [hval]
    exact clockCounterStep_phase_le_succ_of_wf b hwf hle

theorem Phase1Transition_right_phase_eq_of_not_clock (a b : AgentState L K)
    (hc : b.role ≠ .clock) :
    (Phase1Transition L K a b).2.phase.val = b.phase.val := by
  by_cases hmain : a.role = .main ∧ b.role = .main
  · simp [Phase1Transition, hmain.1, hmain.2, clockCounterStep]
  · have : (Phase1Transition L K a b).2 = clockCounterStep L K b := by
      unfold Phase1Transition; rw [if_neg hmain]
    rw [this]; unfold clockCounterStep; rw [if_neg hc]

/-- Phase 2 RIGHT output advances by `≤ +1`. -/
theorem Phase2Transition_right_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) b) (hle : b.phase.val ≤ 8) :
    (Phase2Transition L K a b).2.phase.val ≤ b.phase.val + 1 := by
  have hwf' : WfAgent (L := L) (K := K)
      ({ b with opinions := opinionsUnion a.opinions b.opinions } : AgentState L K) := by
    obtain ⟨h1, h2, h3⟩ := hwf; exact ⟨h1, h2, h3⟩
  have hle' : ({ b with opinions := opinionsUnion a.opinions b.opinions }
      : AgentState L K).phase.val ≤ 8 := hle
  unfold Phase2Transition
  dsimp only
  split_ifs
  · exact advancePhaseWithInit_phase_le_succ_of_wf _ hwf' hle'
  · exact Nat.le_succ _
  · exact Nat.le_succ _
  · exact Nat.le_succ _
  · exact Nat.le_succ _

/-- Phase 4 RIGHT output advances by `≤ +1`. -/
theorem Phase4Transition_right_phase_le_succ (a b : AgentState L K) :
    (Phase4Transition L K a b).2.phase.val ≤ b.phase.val + 1 := by
  unfold Phase4Transition; dsimp
  split_ifs
  · exact advancePhase_phase_le_succ b
  · exact Nat.le_succ _

/-- Phase 5 RIGHT output advances by `≤ +1`. -/
theorem Phase5Transition_right_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) b) (hle : b.phase.val ≤ 8) :
    (Phase5Transition L K a b).2.phase.val ≤ b.phase.val + 1 := by
  by_cases hc : b.role = .clock
  · rw [Phase5Transition_right_clock a b hc]
    exact stdCounterSubroutine_phase_le_succ_of_wf b hwf hle
  · have hval : (Phase5Transition L K a b).2.phase.val = b.phase.val := by
      simp only [Phase5Transition]
      split_ifs with h1 h2 <;> simp_all
    omega

/-- Phase 6 RIGHT output advances by `≤ +1`. -/
theorem Phase6Transition_right_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) b) (hle : b.phase.val ≤ 8) :
    (Phase6Transition L K a b).2.phase.val ≤ b.phase.val + 1 := by
  by_cases hc : b.role = .clock
  · rw [Phase6Transition_right_clock a b hc]
    exact stdCounterSubroutine_phase_le_succ_of_wf b hwf hle
  · have hval : (Phase6Transition L K a b).2.phase.val = b.phase.val := by
      simp only [Phase6Transition]
      have hs1role : (if a.role = .reserve ∧ b.role = .main ∧ (b.bias ≠ .zero) then
            (doSplit L K a b).2
          else if b.role = .reserve ∧ a.role = .main ∧ (a.bias ≠ .zero) then
            (doSplit L K b a).1 else b).role ≠ .clock := by
        split_ifs
        · rw [doSplit_role_snd]; exact hc
        · exact doSplit_role_fst_ne_clock b a hc
        · exact hc
      have hs1phase : (if a.role = .reserve ∧ b.role = .main ∧ (b.bias ≠ .zero) then
            (doSplit L K a b).2
          else if b.role = .reserve ∧ a.role = .main ∧ (a.bias ≠ .zero) then
            (doSplit L K b a).1 else b).phase.val = b.phase.val := by
        split_ifs
        · exact doSplit_phase_snd a b
        · exact doSplit_phase_fst b a
        · rfl
      show (if _ then stdCounterSubroutine L K _ else _).phase.val = b.phase.val
      rw [if_neg hs1role, hs1phase]
    omega

/-- Phase 7 RIGHT output advances by `≤ +1`. -/
theorem Phase7Transition_right_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) b) (hle : b.phase.val ≤ 8) :
    (Phase7Transition L K a b).2.phase.val ≤ b.phase.val + 1 := by
  by_cases hc : b.role = .clock
  · rw [Phase7Transition_right_clock a b hc]
    exact stdCounterSubroutine_phase_le_succ_of_wf b hwf hle
  · have hval : (Phase7Transition L K a b).2.phase.val = b.phase.val := by
      simp only [Phase7Transition]
      have hs1role : (if a.role = .main ∧ b.role = .main then
            (cancelSplit L K a b).2 else b).role ≠ .clock := by
        split_ifs
        · rw [cancelSplit_role_snd]; exact hc
        · exact hc
      have hs1phase : (if a.role = .main ∧ b.role = .main then
            (cancelSplit L K a b).2 else b).phase.val = b.phase.val := by
        split_ifs
        · exact cancelSplit_phase_snd a b
        · rfl
      show (if _ then stdCounterSubroutine L K _ else _).phase.val = b.phase.val
      rw [if_neg hs1role, hs1phase]
    omega

/-- Phase 8 RIGHT output advances by `≤ +1`. -/
theorem Phase8Transition_right_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) b) (hle : b.phase.val ≤ 8) :
    (Phase8Transition L K a b).2.phase.val ≤ b.phase.val + 1 := by
  by_cases hc : b.role = .clock
  · rw [Phase8Transition_right_clock a b hc]
    exact stdCounterSubroutine_phase_le_succ_of_wf b hwf hle
  · have hval : (Phase8Transition L K a b).2.phase.val = b.phase.val := by
      simp only [Phase8Transition]
      have hs1role : (if a.role = .main ∧ b.role = .main then
            (absorbConsume L K a b).2 else b).role ≠ .clock := by
        split_ifs
        · rw [absorbConsume_role_snd]; exact hc
        · exact hc
      have hs1phase : (if a.role = .main ∧ b.role = .main then
            (absorbConsume L K a b).2 else b).phase.val = b.phase.val := by
        split_ifs
        · exact absorbConsume_phase_snd a b
        · rfl
      show (if _ then stdCounterSubroutine L K _ else _).phase.val = b.phase.val
      rw [if_neg hs1role, hs1phase]
    omega

/-- Phase 0 RIGHT output advances by `≤ +1` when at phase `0`. -/
theorem Phase0Transition_right_phase_le_succ_of_phase0 (a b : AgentState L K)
    (h0 : b.phase.val = 0) :
    (Phase0Transition L K a b).2.phase.val ≤ b.phase.val + 1 := by
  let s1 := if a.role = .mcr ∧ b.role = .mcr then
    { a with role := .main, smallBias := addSmallBias a.smallBias b.smallBias } else a
  let t1 := if a.role = .mcr ∧ b.role = .mcr then
    { b with role := .cr, smallBias := ⟨3, by decide⟩ } else b
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
    else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  have ht1 : b.phase.val = t1.phase.val := by dsimp [t1]; split_ifs <;> rfl
  have ht2 : t1.phase.val = t2.phase.val := by dsimp [t2]; split_ifs <;> rfl
  have ht3 : t2.phase.val = t3.phase.val := by dsimp [t3]; split_ifs <;> rfl
  have ht3' : t3.phase.val = t3'.phase.val := by dsimp [t3']
  have ht4 : t3'.phase.val = t4.phase.val := by dsimp [t4]; split_ifs <;> rfl
  have ht4phase : t4.phase.val = 0 := by rw [← ht4, ← ht3', ← ht3, ← ht2, ← ht1, h0]
  have ht5 : t5.phase.val ≤ t4.phase.val + 1 := by
    dsimp [t5]; split_ifs with hcl
    · exact stdCounterSubroutine_phase_le_succ_of_clock t4 hcl.2
        (by rw [ht4phase]; decide) (by rw [ht4phase]; decide) (by rw [ht4phase]; decide)
    · omega
  show t5.phase.val ≤ b.phase.val + 1
  omega

/-- Phase 3 RIGHT output advances by `≤ +1` (Rule 1 `stdCounterSubroutine` on a clock
responder; minute-drag preserves the phase). -/
theorem Phase3Transition_right_phase_le_succ_of_wf (a b : AgentState L K)
    (hwf : WfAgent (L := L) (K := K) b) (hle : b.phase.val ≤ 8) :
    (Phase3Transition L K a b).2.phase.val ≤ b.phase.val + 1 := by
  set t1 : AgentState L K :=
    (if a.role = .clock ∧ b.role = .clock then
      if a.minute ≠ b.minute then { b with minute := max a.minute b.minute }
      else if _h : a.minute.val < K * (L + 1) then b
      else stdCounterSubroutine L K b
    else b) with ht1def
  have hphaseeq : (Phase3Transition L K a b).2.phase = t1.phase :=
    (Phase3Transition_right_output_eq_rule1 (L := L) (K := K) a b t1 ht1def).2
  have ht1 : t1.phase.val ≤ b.phase.val + 1 := by
    rw [ht1def]
    split_ifs with hcl hmin hlt
    · exact le_trans (le_of_eq (show ({ b with minute := max a.minute b.minute }
        : AgentState L K).phase.val = b.phase.val from rfl)) (Nat.le_succ _)
    · exact Nat.le_succ _
    · exact stdCounterSubroutine_phase_le_succ_of_wf b hwf hle
    · exact Nat.le_succ _
  have : (Phase3Transition L K a b).2.phase.val = t1.phase.val := by rw [hphaseeq]
  omega

/-- Phase 6 RIGHT keeps a non-clock responder's phase. -/
theorem Phase6Transition_right_phase_eq_of_not_clock (a b : AgentState L K)
    (hc : b.role ≠ .clock) :
    (Phase6Transition L K a b).2.phase.val = b.phase.val := by
  simp only [Phase6Transition]
  have hs1role : (if a.role = .reserve ∧ b.role = .main ∧ (b.bias ≠ .zero) then
        (doSplit L K a b).2
      else if b.role = .reserve ∧ a.role = .main ∧ (a.bias ≠ .zero) then
        (doSplit L K b a).1 else b).role ≠ .clock := by
    split_ifs
    · rw [doSplit_role_snd]; exact hc
    · exact doSplit_role_fst_ne_clock b a hc
    · exact hc
  have hs1phase : (if a.role = .reserve ∧ b.role = .main ∧ (b.bias ≠ .zero) then
        (doSplit L K a b).2
      else if b.role = .reserve ∧ a.role = .main ∧ (a.bias ≠ .zero) then
        (doSplit L K b a).1 else b).phase.val = b.phase.val := by
    split_ifs
    · exact doSplit_phase_snd a b
    · exact doSplit_phase_fst b a
    · rfl
  show (if _ then stdCounterSubroutine L K _ else _).phase.val = b.phase.val
  rw [if_neg hs1role, hs1phase]

/-- Phase 7 RIGHT keeps a non-clock responder's phase. -/
theorem Phase7Transition_right_phase_eq_of_not_clock (a b : AgentState L K)
    (hc : b.role ≠ .clock) :
    (Phase7Transition L K a b).2.phase.val = b.phase.val := by
  simp only [Phase7Transition]
  have hs1role : (if a.role = .main ∧ b.role = .main then
        (cancelSplit L K a b).2 else b).role ≠ .clock := by
    split_ifs
    · rw [cancelSplit_role_snd]; exact hc
    · exact hc
  have hs1phase : (if a.role = .main ∧ b.role = .main then
        (cancelSplit L K a b).2 else b).phase.val = b.phase.val := by
    split_ifs
    · exact cancelSplit_phase_snd a b
    · rfl
  show (if _ then stdCounterSubroutine L K _ else _).phase.val = b.phase.val
  rw [if_neg hs1role, hs1phase]

/-- Phase 8 RIGHT keeps a non-clock responder's phase. -/
theorem Phase8Transition_right_phase_eq_of_not_clock (a b : AgentState L K)
    (hc : b.role ≠ .clock) :
    (Phase8Transition L K a b).2.phase.val = b.phase.val := by
  simp only [Phase8Transition]
  have hs1role : (if a.role = .main ∧ b.role = .main then
        (absorbConsume L K a b).2 else b).role ≠ .clock := by
    split_ifs
    · rw [absorbConsume_role_snd]; exact hc
    · exact hc
  have hs1phase : (if a.role = .main ∧ b.role = .main then
        (absorbConsume L K a b).2 else b).phase.val = b.phase.val := by
    split_ifs
    · exact absorbConsume_phase_snd a b
    · rfl
  show (if _ then stdCounterSubroutine L K _ else _).phase.val = b.phase.val
  rw [if_neg hs1role, hs1phase]

/-- Phase 1 RIGHT keeps a non-clock responder's phase. -/
theorem Phase1Transition_right_phase_eq_of_not_clock' (a b : AgentState L K)
    (hc : b.role ≠ .clock) :
    (Phase1Transition L K a b).2.phase.val = b.phase.val :=
  Phase1Transition_right_phase_eq_of_not_clock a b hc

/-- **Right dispatch `+1` bound.**  Under `Wf` on both inputs with both phases `≤ 8`, the
right `Transition` output phase is at most `ep.2.phase + 1` (the dispatch — branching on
`ep.1.phase` — applies the phase-`q` rule to BOTH outputs; the right output advances `ep.2`
by `≤ +1`). -/
theorem Transition_right_phase_le_ep_succ_of_wf (a b : AgentState L K)
    (hwfa : WfAgent (L := L) (K := K) a) (hwfb : WfAgent (L := L) (K := K) b)
    (ha8 : a.phase.val ≤ 8) (hb8 : b.phase.val ≤ 8) :
    (Transition L K a b).2.phase.val ≤ (phaseEpidemicUpdate L K a b).2.phase.val + 1 := by
  have hepphase : (phaseEpidemicUpdate L K a b).1.phase.val = max a.phase.val b.phase.val :=
    phaseEpidemicUpdate_left_phase_eq_max_of_wf a b hwfa hwfb (by omega) (by omega)
  have hep1wf : WfAgent (L := L) (K := K) (phaseEpidemicUpdate L K a b).1 :=
    phaseEpidemicUpdate_left_preserves_wf a b hwfa hwfb (by omega) (by omega)
  have hep2wf : WfAgent (L := L) (K := K) (phaseEpidemicUpdate L K a b).2 :=
    phaseEpidemicUpdate_right_preserves_wf a b hwfa hwfb (by omega) (by omega)
  have hep18 : (phaseEpidemicUpdate L K a b).1.phase.val ≤ 8 := by rw [hepphase]; omega
  have hep28 : (phaseEpidemicUpdate L K a b).2.phase.val ≤ 8 := by
    rw [phaseEpidemicUpdate_right_phase_eq_max_of_wf a b hwfa hwfb (by omega) (by omega)]; omega
  set s' := (phaseEpidemicUpdate L K a b).1 with hs'def
  set t' := (phaseEpidemicUpdate L K a b).2 with ht'def
  have hdisp : (Transition L K a b).2.phase.val ≤ t'.phase.val + 1 := by
    rw [show (Transition L K a b).2 = finishPhase10Entry L K t'
          (match s'.phase with
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
            | _ => (s', t')).2 from rfl]
    rw [finishPhase10Entry_phase_val]
    rcases hphase : s'.phase with ⟨n, hn⟩
    have hn8 : n ≤ 8 := by rw [hphase] at hep18; exact hep18
    have htwf : WfAgent (L := L) (K := K) t' := hep2wf
    have hnt' : t'.phase.val ≤ 8 := hep28
    -- ep.2.phase ≤ ep.1.phase = n (epidemic outputs share the source max)
    have ht'le : t'.phase.val ≤ s'.phase.val := by
      rw [phaseEpidemicUpdate_right_phase_eq_max_of_wf a b hwfa hwfb (by omega) (by omega),
          ← hepphase]
    have ht'n : t'.phase.val ≤ n := by rw [hphase] at ht'le; exact ht'le
    match n, hn, hn8 with
    | 0, _, _ => simp only [hphase]
                 have hb0 : t'.phase.val = 0 := by omega
                 have := Phase0Transition_right_phase_le_succ_of_phase0 s' t' hb0; omega
    | 1, _, _ => simp only [hphase]
                 have := Phase1Transition_right_phase_le_succ_of_wf s' t' htwf hnt'; omega
    | 2, _, _ => simp only [hphase]
                 have := Phase2Transition_right_phase_le_succ_of_wf s' t' htwf hnt'; omega
    | 3, _, _ => simp only [hphase]
                 have := Phase3Transition_right_phase_le_succ_of_wf s' t' htwf hnt'; omega
    | 4, _, _ => simp only [hphase]
                 have := Phase4Transition_right_phase_le_succ s' t'; omega
    | 5, _, _ => simp only [hphase]
                 have := Phase5Transition_right_phase_le_succ_of_wf s' t' htwf hnt'; omega
    | 6, _, _ => simp only [hphase]
                 have := Phase6Transition_right_phase_le_succ_of_wf s' t' htwf hnt'; omega
    | 7, _, _ => simp only [hphase]
                 have := Phase7Transition_right_phase_le_succ_of_wf s' t' htwf hnt'; omega
    | 8, _, _ => simp only [hphase]
                 have := Phase8Transition_right_phase_le_succ_of_wf s' t' htwf hnt'; omega
    | n + 9, hn, hn8 => omega
  exact hdisp

/-- **Source-tracing (right).**  If the right epidemic output `ep.2` is a clock at phase
`p+1 ∈ {1,6,7,8}` with `counter = 0`, then the SOURCE `b` is already a clock at phase
`p+1` with `counter = 0`. -/
theorem ep_right_clock_zero_imp_source (a b : AgentState L K) (p : ℕ)
    (hq : CounterResetDest (p + 1))
    (hrole : (phaseEpidemicUpdate L K a b).2.role = .clock)
    (hphase : (phaseEpidemicUpdate L K a b).2.phase.val = p + 1)
    (hctr : (phaseEpidemicUpdate L K a b).2.counter.val = 0) :
    b.role = .clock ∧ b.phase.val = p + 1 ∧ b.counter.val = 0 := by
  have hqT : CounterTimedPhase (p + 1) := CounterTimedPhase_of_CounterResetDest hq
  have hple : p + 1 ≤ 8 := by rcases hq with h | h | h | h <;> omega
  set ep2 := (phaseEpidemicUpdate L K a b).2 with hep2
  rcases lt_trichotomy b.phase.val (p + 1) with hlt | heq | hgt
  · exfalso
    have hfull := phaseEpidemicUpdate_right_immigrant_full a b (p + 1) hqT hlt hrole hphase
    rw [← hep2] at hfull; omega
  · have hab : a.phase.val ≤ b.phase.val := by
      by_contra hgt
      rw [not_le] at hgt
      have hge : a.phase.val ≤ ep2.phase.val := by
        rw [hep2]
        exact le_trans (le_max_left _ _)
          (phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) a b)
      rw [hphase] at hge; omega
    obtain ⟨hctrb, hroleb, hphase_or⟩ := phaseEpidemicUpdate_right_id_of_ge a b hab
    refine ⟨?_, heq, ?_⟩
    · rw [← hroleb]; exact hrole
    · rw [show b.counter.val = ep2.counter.val from by rw [hctrb], hctr]
  · exfalso
    have hge : b.phase.val ≤ ep2.phase.val := by
      rw [hep2]
      exact le_trans (le_max_right _ _)
        (phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) a b)
    rw [hphase] at hge; omega

/-- The phase-`q` RIGHT dispatch output for a clock responder at a counter-reset
destination `q ∈ {1,6,7,8}` is `stdCounterSubroutine`'s phase (phase 1 = `clockCounterStep`). -/
theorem dispatch_right_clock_eq_std (e f : AgentState L K) (q : ℕ)
    (hq : CounterResetDest q) (heq : e.phase.val = q) (hc : f.role = .clock) :
    ((match e.phase with
        | ⟨1, _⟩ => Phase1Transition L K e f
        | ⟨6, _⟩ => Phase6Transition L K e f
        | ⟨7, _⟩ => Phase7Transition L K e f
        | ⟨8, _⟩ => Phase8Transition L K e f
        | _ => (e, f)).2).phase.val = (stdCounterSubroutine L K f).phase.val := by
  rcases hq with h | h | h | h <;>
    (have hfe : e.phase = (⟨q, by rcases h with rfl <;> omega⟩ : Fin 11) := Fin.ext heq
     rw [hfe]; subst h; simp only)
  · -- phase 1 right = clockCounterStep f (f is a clock, so not main; main–main branch off)
    have hmain : ¬ (e.role = .main ∧ f.role = .main) := by
      rintro ⟨-, h⟩; rw [hc] at h; exact absurd h (by decide)
    rw [show (Phase1Transition L K e f).2 = clockCounterStep L K f from by
      unfold Phase1Transition; rw [if_neg hmain]]
    unfold clockCounterStep; rw [if_pos hc]
  · rw [Phase6Transition_right_clock e f hc]
  · rw [Phase7Transition_right_clock e f hc]
  · rw [Phase8Transition_right_clock e f hc]

/-- The phase-`q` RIGHT dispatch output keeps a NON-clock responder's phase. -/
theorem dispatch_right_not_clock_phase_eq (e f : AgentState L K) (q : ℕ)
    (hq : CounterResetDest q) (heq : e.phase.val = q) (hc : f.role ≠ .clock) :
    ((match e.phase with
        | ⟨1, _⟩ => Phase1Transition L K e f
        | ⟨6, _⟩ => Phase6Transition L K e f
        | ⟨7, _⟩ => Phase7Transition L K e f
        | ⟨8, _⟩ => Phase8Transition L K e f
        | _ => (e, f)).2).phase.val = f.phase.val := by
  rcases hq with h | h | h | h
  · have hfe : e.phase = (⟨1, by omega⟩ : Fin 11) := Fin.ext (by rw [heq, h])
    rw [hfe]; simp only
    exact Phase1Transition_right_phase_eq_of_not_clock e f hc
  · have hfe : e.phase = (⟨6, by omega⟩ : Fin 11) := Fin.ext (by rw [heq, h])
    rw [hfe]; simp only
    exact Phase6Transition_right_phase_eq_of_not_clock e f hc
  · have hfe : e.phase = (⟨7, by omega⟩ : Fin 11) := Fin.ext (by rw [heq, h])
    rw [hfe]; simp only
    exact Phase7Transition_right_phase_eq_of_not_clock e f hc
  · have hfe : e.phase = (⟨8, by omega⟩ : Fin 11) := Fin.ext (by rw [heq, h])
    rw [hfe]; simp only
    exact Phase8Transition_right_phase_eq_of_not_clock e f hc

/-- **Right advance ⟹ source clock with zero counter (counter-reset destination).** -/
theorem Transition_right_advance_imp_source (a b : AgentState L K) (p : ℕ)
    (hq : CounterResetDest (p + 1))
    (hwfa : WfAgent (L := L) (K := K) a) (hwfb : WfAgent (L := L) (K := K) b)
    (ha : a.phase.val ≤ p + 1) (hb : b.phase.val ≤ p + 1)
    (hadv : (Transition L K a b).2.phase.val > p + 1) :
    b.role = .clock ∧ b.phase.val = p + 1 ∧ b.counter.val = 0 := by
  have hp1le8 : p + 1 ≤ 8 := by rcases hq with h | h | h | h <;> omega
  -- right +1 bound ⟹ ep.2.phase ≥ p+1; ep.2.phase ≤ ep.1.phase = max ≤ p+1 ⟹ = p+1.
  have hr1 := Transition_right_phase_le_ep_succ_of_wf a b hwfa hwfb (by omega) (by omega)
  have hep1max : (phaseEpidemicUpdate L K a b).1.phase.val = max a.phase.val b.phase.val :=
    phaseEpidemicUpdate_left_phase_eq_max_of_wf a b hwfa hwfb (by omega) (by omega)
  have hep2max : (phaseEpidemicUpdate L K a b).2.phase.val = max a.phase.val b.phase.val :=
    phaseEpidemicUpdate_right_phase_eq_max_of_wf a b hwfa hwfb (by omega) (by omega)
  have hep2 : (phaseEpidemicUpdate L K a b).2.phase.val = p + 1 := by
    rw [hep2max]; omega
  have hep1 : (phaseEpidemicUpdate L K a b).1.phase.val = p + 1 := by
    rw [hep1max]; omega
  set e := (phaseEpidemicUpdate L K a b).1 with hedef
  set f := (phaseEpidemicUpdate L K a b).2 with hfdef
  -- Transition.2.phase = dispatch RIGHT output phase
  have hdispval : (Transition L K a b).2.phase.val =
      ((match e.phase with
        | ⟨1, _⟩ => Phase1Transition L K e f
        | ⟨6, _⟩ => Phase6Transition L K e f
        | ⟨7, _⟩ => Phase7Transition L K e f
        | ⟨8, _⟩ => Phase8Transition L K e f
        | _ => (e, f)).2).phase.val := by
    rw [show (Transition L K a b).2 = finishPhase10Entry L K f
          (match e.phase with
            | ⟨0, _⟩ => Phase0Transition L K e f
            | ⟨1, _⟩ => Phase1Transition L K e f
            | ⟨2, _⟩ => Phase2Transition L K e f
            | ⟨3, _⟩ => Phase3Transition L K e f
            | ⟨4, _⟩ => Phase4Transition L K e f
            | ⟨5, _⟩ => Phase5Transition L K e f
            | ⟨6, _⟩ => Phase6Transition L K e f
            | ⟨7, _⟩ => Phase7Transition L K e f
            | ⟨8, _⟩ => Phase8Transition L K e f
            | ⟨9, _⟩ => Phase9Transition L K e f
            | ⟨10, _⟩ => Phase10Transition L K e f
            | _ => (e, f)).2 from rfl]
    rw [finishPhase10Entry_phase_val]
    rcases hq with h | h | h | h
    · rw [show e.phase = (⟨1, by omega⟩ : Fin 11) from Fin.ext (by rw [hep1, h])]
    · rw [show e.phase = (⟨6, by omega⟩ : Fin 11) from Fin.ext (by rw [hep1, h])]
    · rw [show e.phase = (⟨7, by omega⟩ : Fin 11) from Fin.ext (by rw [hep1, h])]
    · rw [show e.phase = (⟨8, by omega⟩ : Fin 11) from Fin.ext (by rw [hep1, h])]
  rw [hdispval] at hadv
  -- f advances ⟹ f clock counter 0; then source-trace.
  have hfcz : f.role = .clock ∧ f.counter.val = 0 := by
    by_cases hc : f.role = .clock
    · refine ⟨hc, ?_⟩
      by_contra hctr
      rw [dispatch_right_clock_eq_std e f (p + 1) hq hep1 hc] at hadv
      rw [stdCounterSubroutine_phase_eq_of_counter_ne_zero f hctr, hep2] at hadv
      omega
    · exfalso
      rw [dispatch_right_not_clock_phase_eq e f (p + 1) hq hep1 hc, hep2] at hadv
      omega
  -- source-trace the right side
  obtain ⟨hfrole, hfctr⟩ := hfcz
  exact ep_right_clock_zero_imp_source a b p hq hfrole hep2 hfctr

/-! ## Stage 4 — the bridge under `Wf` and the wire-up. -/

/-- A membership fact: an agent in the one-step update is either an unchanged agent of
`c` (a member of `c - {r₁,r₂}`, hence of `c`) or one of the two transition outputs. -/
theorem mem_stepOrSelf_cases (c : Config (AgentState L K)) (r₁ r₂ x : AgentState L K)
    (happ : Protocol.Applicable c r₁ r₂)
    (hx : x ∈ Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) :
    x ∈ c - {r₁, r₂} ∨ x = (Transition L K r₁ r₂).1 ∨ x = (Transition L K r₁ r₂).2 := by
  rw [Protocol.stepOrSelf, if_pos happ] at hx
  rw [Multiset.mem_add] at hx
  rcases hx with h | h
  · exact Or.inl h
  · -- x ∈ {T.1, T.2}
    have : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    rw [this] at h
    rcases Multiset.mem_cons.mp h with h | h
    · exact Or.inr (Or.inl h)
    · rw [Multiset.mem_singleton] at h; exact Or.inr (Or.inr h)

/-- **The honest deterministic seam overshoot bridge** (counter-reset destination, under
`Wf`).  Under config well-formedness `Wf c` and `CounterResetDest (p+1)`, a one-step
update out of `NoOvershoot p` that creates an agent at phase `≥ p+2` forces an
`AtRiskClockZero p c`.  This DISCHARGES `DetSeamOvershootBridge p` from the well-formedness
side condition the obstruction (`HANDOFF_SEAM_NOOVERSHOOT.md` finding 2) requires. -/
theorem det_seam_overshoot_bridge_of_wf (p : ℕ)
    (hq : CounterResetDest (p + 1))
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hwf : Wf (L := L) (K := K) c)
    (hno : NoOvershoot (L := L) (K := K) p c)
    (hexit : ¬ NoOvershoot (L := L) (K := K) p
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)) :
    AtRiskClockZero (L := L) (K := K) p c := by
  have hp8 : p + 1 ≤ 8 := by rcases hq with h | h | h | h <;> omega
  -- Applicable, else stepOrSelf = c and ¬NoOvershoot c, contradicting hno.
  by_cases happ : Protocol.Applicable c r₁ r₂
  · -- r₁, r₂ ∈ c: well-formed and phase ≤ p+1.
    have hr1mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
    have hr2mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
    have hwf1 : WfAgent (L := L) (K := K) r₁ := hwf r₁ hr1mem
    have hwf2 : WfAgent (L := L) (K := K) r₂ := hwf r₂ hr2mem
    have hr1le : r₁.phase.val ≤ p + 1 := by have := hno r₁ hr1mem; omega
    have hr2le : r₂.phase.val ≤ p + 1 := by have := hno r₂ hr2mem; omega
    -- the overshooting agent
    obtain ⟨x, hxmem, hxphase⟩ := by
      rw [NoOvershoot] at hexit; push_neg at hexit; exact hexit
    rcases mem_stepOrSelf_cases c r₁ r₂ x happ hxmem with hxc | hxT1 | hxT2
    · -- x unchanged: x ∈ c ⟹ phase < p+2, contradiction
      exfalso
      have : x ∈ c := Multiset.mem_of_le (Multiset.sub_le_self _ _) hxc
      have := hno x this; omega
    · -- x = T.1: left advance ⟹ r₁ clock at p+1 counter 0
      subst hxT1
      have hadv : (Transition L K r₁ r₂).1.phase.val > p + 1 := by omega
      have hep1 : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val = max r₁.phase.val r₂.phase.val :=
        phaseEpidemicUpdate_left_phase_eq_max_of_wf r₁ r₂ hwf1 hwf2 (by omega) (by omega)
      have hle1 := Transition_left_phase_le_ep_succ_of_wf r₁ r₂ hwf1 hwf2 (by omega) (by omega)
      have hepeq : (phaseEpidemicUpdate L K r₁ r₂).1.phase.val = p + 1 := by
        rw [hep1]; omega
      have hcz := Transition_left_advance_imp_ep_clock_zero r₁ r₂ p hq hwf1 hwf2 hr1le hr2le
        hepeq hadv
      obtain ⟨hrole, hph, hctr⟩ :=
        ep_left_clock_zero_imp_source r₁ r₂ p hq hcz.1 hepeq hcz.2
      exact ⟨r₁, hr1mem, hrole, hph, hctr⟩
    · -- x = T.2: right advance ⟹ r₂ clock at p+1 counter 0
      subst hxT2
      have hadv : (Transition L K r₁ r₂).2.phase.val > p + 1 := by omega
      obtain ⟨hrole, hph, hctr⟩ :=
        Transition_right_advance_imp_source r₁ r₂ p hq hwf1 hwf2 hr1le hr2le hadv
      exact ⟨r₂, hr2mem, hrole, hph, hctr⟩
  · -- not applicable: stepOrSelf = c, so ¬NoOvershoot c, contradicting hno.
    rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ] at hexit
    exact absurd hno hexit

/-- **Wire-up: discharge `DetSeamOvershootBridge p` from the seam-region well-formedness.**
For a counter-reset destination `p+1 ∈ {1,6,7,8}`, if every configuration in the seam
region is well-formed (`Wf` — no `mcr`, in-range biases; supplied by the `Analysis`-layer
reachability invariants `reachable_preserves_well_formed_agent_quota` / the phase-0 EXIT
`RoleSplitStage2Good`, both preserved on the seam), then the deterministic overshoot bridge
`DetSeamOvershootBridge p` holds — exactly the `hdet` that `SeamNoOvershoot`'s and
`SeamPairAdapter`'s no-overshoot tails carry as a guard. -/
theorem detSeamOvershootBridge_of_wf (p : ℕ)
    (hq : CounterResetDest (p + 1))
    (hWf : ∀ c : Config (AgentState L K), Wf (L := L) (K := K) c) :
    DetSeamOvershootBridge (L := L) (K := K) p :=
  fun c r₁ r₂ hno hexit =>
    det_seam_overshoot_bridge_of_wf p hq c r₁ r₂ (hWf c) hno hexit

/-- **The fully-discharged honest per-seam no-overshoot budget** (counter-reset
destination, under seam-region `Wf`).  This is `hNoOvershoot_one_seam_honest` with the
carried bridge `hdet` ELIMINATED — discharged by `detSeamOvershootBridge_of_wf` from the
well-formedness invariant.  The remaining surface is: seam timing/initial-potential (folded
into `hbound`) + `Wf`-region + `CounterResetDest (p+1)` + the budget inequality `hε`. -/
theorem hNoOvershoot_one_seam_wf (p tseam : ℕ) (εovershoot : ℝ≥0)
    (hq : CounterResetDest (p + 1))
    (hWf : ∀ c : Config (AgentState L K), Wf (L := L) (K := K) c)
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
