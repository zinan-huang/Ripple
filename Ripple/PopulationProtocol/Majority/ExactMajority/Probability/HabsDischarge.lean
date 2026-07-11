/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `habs_mix` — discharging the deterministic fields of the mixed-window closure;
# scoping the phase-3 front-shape synchronization.

`ClockRealMixed.clock_real_advance_mixed` carries the structural hypothesis

  `habs_mix : ∀ c c', Q_mix n mC T c →
       c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q_mix n mC T c'`

(one-step support closure of the mixed window).  `Q_mix n mC T` bundles FOUR
fields:

  * `card`        — `c.card = n` (total population size);
  * `clockPhase3` — every clock-role agent is at phase EXACTLY 3;
  * `clockSize`   — `clockCount c = mC` (the clock population size);
  * `crossedT`    — `9·mC/10 ≤ rBeyond T c` (the level-`T` 0.9 seed floor).

This file DISCHARGES the deterministic fields and PRECISELY SCOPES the hard one:

## What is discharged here (genuine, no new axiom / no `sorry`)

1. **`qmix_card_closed`** — `card` is preserved on the support.  Clean: total
   card is a reachability invariant (`Protocol.stepDistOrSelf_support_card_eq`).

2. **`qmix_crossedT_closed`** — the level-`T` 0.9 floor `9·mC/10 ≤ rBeyond T` is
   preserved (for `1 ≤ T`).  Clean: `rBeyond T` is NON-DECREASING on the kernel
   support, REUSING `ClockMonoDischarge.hmono_mix_discharged` (already proven —
   `rBeyond (T'+1)` non-decreasing on any `Q_mix n mC T'` window).  We instantiate
   it at level `T' = T-1`: a `Q_mix n mC T` config is also a `Q_mix n mC (T-1)`
   config (the only `T`-dependent field, `crossedT`, only weakens under decreasing
   the threshold, since `rBeyond` is antitone in its threshold), so the proven
   monotonicity transports verbatim and gives `rBeyond T c ≤ rBeyond T c'`.

3. **`qmix_clockSize_closed`** — `clockCount = mC` is preserved, UNDER the added
   invariant `allPhaseGE3` (every agent at phase `≥ 3`, i.e. the Phase-0/1/2
   clock-creation stage is complete).  This invariant is GENUINELY NEEDED and is
   NOT implied by bare `Q_mix`: clock role is CREATED only in `Phase0Transition`
   (Rule 4, two `.cr` agents → one Clock), which fires only when the dispatched
   phase is `0`.  `Q_mix` leaves NON-clock phases free, so a `.cr`/`.cr` pair at
   phase `0` could spawn a fresh clock and break `clockCount = mC`.  Under
   `allPhaseGE3` the epidemic raises the dispatched phase to `≥ 3 > 0`, so no
   creation fires; combined with clock-role permanence the count is conserved.
   `allPhaseGE3` is itself one-step closed (`allPhaseGE3_closed`): every per-phase
   transition is phase-non-decreasing (`Transition_phase_nondec`).

## The hard residual — `clockPhase3` (SCOPED, not faked)

`clockPhase3` (clocks at phase EXACTLY 3) is NOT one-step closed by any
phase-only invariant, BY DESIGN of the protocol:

  * a phase-3 clock pair AT THE CAP with a ZERO counter ADVANCES to phase 4
    (`Transition_phase3_clock_done_counter_zero_advances`) — this is the clock
    finishing its run;
  * the epidemic pulls a phase-3 clock UP to the partner's phase if any agent is
    at phase `> 3`.

So `clockPhase3` is preserved one step ONLY under the combined invariant

  `Q_mix ∧ noPhaseAbove3 ∧ allClocksCounterPos`

where `noPhaseAbove3 := ∀ a ∈ c, a.phase.val ≤ 3` (no epidemic drag-up) and
`allClocksCounterPos := ∀ a ∈ c, a.role = .clock → 0 < a.counter.val` (no
cap-completion advance).  Under these, a phase-3 clock pair stays at phase 3:
below the cap the Phase-3 rule edits only `minute`; at the cap with positive
counters the counter merely decrements
(`Transition_phase3_clock_done_positive_preserves_and_decreases`).

The OBSTRUCTION is the closure of `allClocksCounterPos`: the counter decrements
only at the cap, and it must stay `≥ 1` until the clock genuinely completes — this
is exactly Doty's FRONT-SHAPE SYNCHRONIZATION fact (the clocks reach the cap
TOGETHER at the end of their run, the counter does not hit 0 early).  That is a
multi-step REACHABILITY invariant, NOT a one-step closure, and it is the single
precisely-named sub-lemma that remains.  See the explicit named sub-lemma
`ClockPhase3_remaining_synchronization` at the end of this file.

NEW file; no existing file is edited; no `sorry`/`admit`/`axiom`/`native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockMonoDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace HabsDischarge

open ClockRealKernel ClockRealMixed ClockMonoDischarge

variable {L K : ℕ}

/-! ## Part 0 — threshold antitonicity of `rBeyond` (a clean count fact). -/

/-- `rBeyond` is ANTITONE in its threshold: a larger minute threshold counts no
more clock agents.  (`{minute ≥ T₂} ⊆ {minute ≥ T₁}` when `T₁ ≤ T₂`.) -/
theorem rBeyond_antitone_threshold (T₁ T₂ : ℕ) (hT : T₁ ≤ T₂)
    (c : Config (AgentState L K)) :
    rBeyond (L := L) (K := K) T₂ c ≤ rBeyond (L := L) (K := K) T₁ c := by
  unfold rBeyond
  apply countP_mono_pred
  intro a ha
  exact ⟨ha.1, le_trans hT ha.2⟩

/-! ## Part 1 — DETERMINISTIC field 1: `card` is preserved. -/

/-- **`qmix_card_closed`.**  The total population size `c.card = n` is preserved on
the one-step kernel support.  Clean: total card is a reachability invariant. -/
theorem qmix_card_closed (n mC T : ℕ)
    (c c' : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    c'.card = n := by
  rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']
  exact hQ.card

/-! ## Part 2 — DETERMINISTIC field 2: `crossedT` (the 0.9 seed floor) is preserved.

REUSES `ClockMonoDischarge.hmono_mix_discharged` (proven): on any `Q_mix n mC T'`
window, `rBeyond (T'+1)` is non-decreasing on the support.  We transport it to
the level-`T` floor by instantiating `T' = T-1` and observing a `Q_mix n mC T`
config is also a `Q_mix n mC (T-1)` config. -/

/-- A `Q_mix n mC T` config (with `1 ≤ T`) is also a `Q_mix n mC (T-1)` config:
all fields except `crossedT` are `T`-independent, and `crossedT` only WEAKENS when
the threshold drops (`rBeyond` is antitone in its threshold). -/
theorem Q_mix_pred (n mC T : ℕ) (hT : 1 ≤ T) (c : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC T c) :
    Q_mix (L := L) (K := K) n mC (T - 1) c := by
  refine ⟨hQ.card, hQ.clockPhase3, hQ.clockSize, ?_⟩
  -- 9·mC/10 ≤ rBeyond T c ≤ rBeyond (T-1) c.
  exact le_trans hQ.crossedT (rBeyond_antitone_threshold (T - 1) T (by omega) c)

/-- `rBeyond T` is NON-DECREASING on the kernel support over the `Q_mix n mC T`
window (for `1 ≤ T`).  REUSES `hmono_mix_discharged n mC (T-1)`
(`rBeyond ((T-1)+1) = rBeyond T` non-decreasing), applied to the `Q_mix n mC (T-1)`
view of `c` from `Q_mix_pred`. -/
theorem rBeyond_T_mono (n mC T : ℕ) (hT : 1 ≤ T)
    (c c' : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    rBeyond (L := L) (K := K) T c ≤ rBeyond (L := L) (K := K) T c' := by
  have hQpred : Q_mix (L := L) (K := K) n mC (T - 1) c := Q_mix_pred n mC T hT c hQ
  have hmono := hmono_mix_discharged (L := L) (K := K) n mC (T - 1) c c' hQpred hc'
  have heq : T - 1 + 1 = T := by omega
  rw [heq] at hmono
  exact hmono

/-- **`qmix_crossedT_closed`.**  The level-`T` 0.9 seed floor `9·mC/10 ≤ rBeyond T`
is preserved on the support (for `1 ≤ T`).  Clean: it is monotone via
`rBeyond_T_mono` (reusing the proven `hmono_mix_discharged`). -/
theorem qmix_crossedT_closed (n mC T : ℕ) (hT : 1 ≤ T)
    (c c' : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    9 * mC / 10 ≤ rBeyond (L := L) (K := K) T c' :=
  le_trans hQ.crossedT (rBeyond_T_mono n mC T hT c c' hQ hc')

/-! ## Part 3 — DETERMINISTIC field 3: `clockSize` (clockCount = mC), under
`allPhaseGE3`.

`allPhaseGE3 c := ∀ a ∈ c, 3 ≤ a.phase.val` — every agent has reached phase `≥ 3`,
i.e. the Phase-0/1/2 clock-CREATION stage is complete.  This is GENUINELY needed:
`clockCount` is exactly preserved iff no clock is created, and clock role is
created only in `Phase0Transition`.  Under `allPhaseGE3` the dispatched phase is
`≥ 3 > 0`, so no creation fires.  Combined with clock-role permanence this gives
`clockCount = mC`. -/

/-- The added invariant: every agent is at phase `≥ 3`. -/
def allPhaseGE3 (c : Config (AgentState L K)) : Prop := ∀ a ∈ c, 3 ≤ a.phase.val

/-- Global per-pair phase non-decrease: both `Transition` outputs are at phase `≥`
their respective inputs.  Assembled from the epidemic phase-raise
(`phaseEpidemicUpdate_*_phase_ge_max_api`, which dominates each input phase) and
the dispatched per-phase rule phase-non-decrease
(`phaseEpidemicUpdate_phase_le_Transition_phase`). -/
theorem Transition_phase_nondec_local (s t : AgentState L K) :
    s.phase.val ≤ (Transition L K s t).1.phase.val ∧
      t.phase.val ≤ (Transition L K s t).2.phase.val := by
  have hepi := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t
  have hge1 := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
  have hge2 := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
  have hsle : s.phase.val ≤ max s.phase.val t.phase.val := le_max_left _ _
  have htle : t.phase.val ≤ max s.phase.val t.phase.val := le_max_right _ _
  exact ⟨by omega, by omega⟩

/-- `allPhaseGE3` is one-step closed on the kernel support: every per-phase
transition is phase-non-decreasing, so a config all of whose agents are at phase
`≥ 3` maps to one all of whose agents are at phase `≥ 3`. -/
theorem allPhaseGE3_closed (c c' : Config (AgentState L K))
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    allPhaseGE3 (L := L) (K := K) c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    simp only [Protocol.scheduledStep]
    -- c' = stepOrSelf c r₁ r₂.
    by_cases happ : Protocol.Applicable c r₁ r₂
    · have hmem1 : r₁ ∈ c := mem_of_applicable_left happ
      have hmem2 : r₂ ∈ c := mem_of_applicable_right happ
      have h1ge : 3 ≤ r₁.phase.val := hge r₁ hmem1
      have h2ge : 3 ≤ r₂.phase.val := hge r₂ hmem2
      have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
      -- both outputs are at phase ≥ 3 (phase-non-decrease).
      have hphase := Transition_phase_nondec_local r₁ r₂
      have hout1 : 3 ≤ (Transition L K r₁ r₂).1.phase.val := le_trans h1ge hphase.1
      have hout2 : 3 ≤ (Transition L K r₁ r₂).2.phase.val := le_trans h2ge hphase.2
      intro a ha
      rw [hc'eq] at ha
      rcases Multiset.mem_add.mp ha with hin | hin
      · -- a survives from c (minus the consumed pair): still at phase ≥ 3.
        exact hge a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hin)
      · -- a is one of the two outputs.
        rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hin
        rcases Multiset.mem_cons.mp hin with rfl | hin
        · exact hout1
        · rcases Multiset.mem_cons.mp hin with rfl | hin
          · exact hout2
          · simp at hin
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact hge
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact hge

/-! ### No clock CREATION away from Phase 0 (the upper-bound half of `clockCount`).

Clock role is created only in `Phase0Transition` (Rule 4).  When the dispatched
phase is `≥ 3` (guaranteed under `allPhaseGE3` after the epidemic), every per-phase
rule maps a non-clock to a non-clock.  We prove the REFLECTING direction: a clock
OUTPUT can only come from a clock INPUT.  Phases 4–10 change roles only via
role-preserving helpers (`advancePhase`, `cancelSplit`, `absorbConsume`,
`doSplit`'s second output, output/opinion edits), and `stdCounterSubroutine` fires
only on clocks; Phase 3 changes roles only via `phase3CancelSplit` (role
preserved). -/

/-- Reflection helper: `phaseInit` at phase `≥ 4` preserves role (only the `p = 1`
init changes role: `cr → reserve`, `mcr → enterPhase10`). -/
private lemma phaseInit_role_eq_of_ge_four (p : Fin 11) (a : AgentState L K)
    (hp : 4 ≤ p.val) :
    (phaseInit L K p a).role = a.role := by
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit] <;> split_ifs <;> simp [enterPhase10]

/-- `advancePhaseWithInit` on a phase-`≥3` agent preserves role (it advances to
phase `≥ 4`, whose init preserves role). -/
private lemma apwi_role_eq_ge3 (a : AgentState L K) (hge : 3 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).role = a.role := by
  unfold advancePhaseWithInit advancePhase
  split_ifs with hlt
  · exact phaseInit_role_eq_of_ge_four ⟨a.phase.val + 1, by omega⟩ _ (by simp; omega)
  · show (phaseInit L K a.phase a).role = a.role
    exact phaseInit_role_eq_of_ge_four a.phase a (by omega)

/-- `stdCounterSubroutine` REFLECTS clock role at phase `≥ 3`: its output is a clock
only if the input was a clock.  (For a non-clock the subroutine is the identity.) -/
private lemma scs_role_clock_refl (a : AgentState L K) (hge : 3 ≤ a.phase.val)
    (h : (stdCounterSubroutine L K a).role = .clock) : a.role = .clock := by
  unfold stdCounterSubroutine at h
  split_ifs at h with hc
  · rwa [apwi_role_eq_ge3 a hge] at h
  · exact h

/-- The guard wrapper `if a.role = clock then stdCounterSubroutine a else a` reflects
clock role: its output is a clock only if `a` was a clock. -/
private lemma scs_guard_refl (a : AgentState L K)
    (h : (if a.role = .clock then stdCounterSubroutine L K a else a).role = .clock) :
    a.role = .clock := by
  split_ifs at h with hh
  · exact hh
  · exact h

/-- `doSplit`'s first output reflects clock role (it is either `r` or `{r with
role := .main}`). -/
private lemma doSplit_role_fst_refl (r m : AgentState L K)
    (h : (doSplit L K r m).1.role = .clock) : r.role = .clock := by
  unfold doSplit at h
  match hm : m.bias with
  | Bias.zero => simpa [hm] using h
  | Bias.dyadic sgn j => simp only [hm] at h; split_ifs at h <;> simp_all

/-- `phase3CancelSplit` preserves the first role (all branches are record updates
that keep `role`). -/
private lemma p3cs_role_fst (s2 t2 : AgentState L K) :
    (phase3CancelSplit L K s2 t2).1.role = s2.role := by
  unfold phase3CancelSplit
  match s2.bias, t2.bias with
  | Bias.zero, Bias.zero => simp
  | Bias.zero, Bias.dyadic _ _ => simp; split_ifs <;> simp
  | Bias.dyadic _ _, Bias.zero => simp; split_ifs <;> simp
  | Bias.dyadic .pos _, Bias.dyadic .pos _ => simp
  | Bias.dyadic .pos _, Bias.dyadic .neg _ => simp; split_ifs <;> simp
  | Bias.dyadic .neg _, Bias.dyadic .pos _ => simp; split_ifs <;> simp
  | Bias.dyadic .neg _, Bias.dyadic .neg _ => simp

/-- `phase3CancelSplit` preserves the second role. -/
private lemma p3cs_role_snd (s2 t2 : AgentState L K) :
    (phase3CancelSplit L K s2 t2).2.role = t2.role := by
  unfold phase3CancelSplit
  match s2.bias, t2.bias with
  | Bias.zero, Bias.zero => simp
  | Bias.zero, Bias.dyadic _ _ => simp; split_ifs <;> simp
  | Bias.dyadic _ _, Bias.zero => simp; split_ifs <;> simp
  | Bias.dyadic .pos _, Bias.dyadic .pos _ => simp
  | Bias.dyadic .pos _, Bias.dyadic .neg _ => simp; split_ifs <;> simp
  | Bias.dyadic .neg _, Bias.dyadic .pos _ => simp; split_ifs <;> simp
  | Bias.dyadic .neg _, Bias.dyadic .neg _ => simp

/-! #### Per-phase first/second clock REFLECTIONS (Phases 3–10). -/

private lemma Phase4_first_refl (s t : AgentState L K)
    (h : (Phase4Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase4Transition at h; dsimp at h
  split_ifs at h with hb
  · rwa [advancePhase_role] at h
  · exact h

private lemma Phase4_second_refl (s t : AgentState L K)
    (h : (Phase4Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase4Transition at h; dsimp at h
  split_ifs at h with hb
  · rwa [advancePhase_role] at h
  · exact h

private lemma Phase5_first_refl (s t : AgentState L K)
    (h : (Phase5Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase5Transition at h; dsimp only at h
  set s1 := (if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ Bias.zero) then
      (if s.hour.val = L then ({ s with hour := exponentOf L t.bias }, t) else (s, t)).1
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ Bias.zero) then
      (if t.hour.val = L then ({ t with hour := exponentOf L s.bias }, s) else (t, s)).2
    else s) with hs1
  have hs1cl : s1.role = .clock := scs_guard_refl s1 (by simpa [hs1] using h)
  rw [hs1] at hs1cl
  split_ifs at hs1cl with h1 hh1 h2 hh2
  · exact absurd (by simpa using hs1cl : s.role = Role.clock) (by rw [h1.1]; simp)
  · exact absurd (by simpa using hs1cl : s.role = Role.clock) (by rw [h1.1]; simp)
  · exact absurd (by simpa using hs1cl : s.role = Role.clock) (by rw [h2.2.1]; simp)
  · exact absurd (by simpa using hs1cl : s.role = Role.clock) (by rw [h2.2.1]; simp)
  · exact hs1cl

private lemma Phase5_second_refl (s t : AgentState L K)
    (h : (Phase5Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase5Transition at h; dsimp only at h
  set t1 := (if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ Bias.zero) then
      (if s.hour.val = L then ({ s with hour := exponentOf L t.bias }, t) else (s, t)).2
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ Bias.zero) then
      (if t.hour.val = L then ({ t with hour := exponentOf L s.bias }, s) else (t, s)).1
    else t) with ht1
  have ht1cl : t1.role = .clock := scs_guard_refl t1 (by simpa [ht1] using h)
  rw [ht1] at ht1cl
  split_ifs at ht1cl with h1 hh1 h2 hh2
  · exact absurd (by simpa using ht1cl : t.role = Role.clock) (by rw [h1.2.1]; simp)
  · exact absurd (by simpa using ht1cl : t.role = Role.clock) (by rw [h1.2.1]; simp)
  · exact absurd (by simpa using ht1cl : t.role = Role.clock) (by rw [h2.1]; simp)
  · exact absurd (by simpa using ht1cl : t.role = Role.clock) (by rw [h2.1]; simp)
  · exact ht1cl

private lemma Phase6_first_refl (s t : AgentState L K)
    (h : (Phase6Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase6Transition at h
  set s1 := (if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ Bias.zero) then (doSplit L K s t).1
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ Bias.zero) then (doSplit L K t s).2
    else s) with hs1
  have hs1cl : s1.role = .clock := scs_guard_refl s1 (by simpa [hs1] using h)
  rw [hs1] at hs1cl
  split_ifs at hs1cl with h1 h2
  · exact (by rw [doSplit_role_fst_refl s t hs1cl] at h1; exact absurd h1.1 (by simp))
  · rw [doSplit_role_snd] at hs1cl; rw [hs1cl] at h2; exact absurd h2.2.1 (by simp)
  · exact hs1cl

private lemma Phase6_second_refl (s t : AgentState L K)
    (h : (Phase6Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase6Transition at h
  set t1 := (if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ Bias.zero) then (doSplit L K s t).2
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ Bias.zero) then (doSplit L K t s).1
    else t) with ht1
  have ht1cl : t1.role = .clock := scs_guard_refl t1 (by simpa [ht1] using h)
  rw [ht1] at ht1cl
  split_ifs at ht1cl with h1 h2
  · rw [doSplit_role_snd] at ht1cl; rw [ht1cl] at h1; exact absurd h1.2.1 (by simp)
  · exact (by rw [doSplit_role_fst_refl t s ht1cl] at h2; exact absurd h2.1 (by simp))
  · exact ht1cl

private lemma Phase7_first_refl (s t : AgentState L K)
    (h : (Phase7Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase7Transition at h
  set s1 := (if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).1 else s) with hs1
  have hs1cl : s1.role = .clock := scs_guard_refl s1 (by simpa [hs1] using h)
  rw [hs1] at hs1cl; split_ifs at hs1cl with h1
  · rw [cancelSplit_role_fst] at hs1cl; exact absurd hs1cl (by rw [h1.1]; simp)
  · exact hs1cl

private lemma Phase7_second_refl (s t : AgentState L K)
    (h : (Phase7Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase7Transition at h
  set t1 := (if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).2 else t) with ht1
  have ht1cl : t1.role = .clock := scs_guard_refl t1 (by simpa [ht1] using h)
  rw [ht1] at ht1cl; split_ifs at ht1cl with h1
  · rw [cancelSplit_role_snd] at ht1cl; exact absurd ht1cl (by rw [h1.2]; simp)
  · exact ht1cl

private lemma Phase8_first_refl (s t : AgentState L K)
    (h : (Phase8Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase8Transition at h
  set s1 := (if s.role = .main ∧ t.role = .main then (absorbConsume L K s t).1 else s) with hs1
  have hs1cl : s1.role = .clock := scs_guard_refl s1 (by simpa [hs1] using h)
  rw [hs1] at hs1cl; split_ifs at hs1cl with h1
  · rw [absorbConsume_role_fst] at hs1cl; exact absurd hs1cl (by rw [h1.1]; simp)
  · exact hs1cl

private lemma Phase8_second_refl (s t : AgentState L K)
    (h : (Phase8Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase8Transition at h
  set t1 := (if s.role = .main ∧ t.role = .main then (absorbConsume L K s t).2 else t) with ht1
  have ht1cl : t1.role = .clock := scs_guard_refl t1 (by simpa [ht1] using h)
  rw [ht1] at ht1cl; split_ifs at ht1cl with h1
  · rw [absorbConsume_role_snd] at ht1cl; exact absurd ht1cl (by rw [h1.2]; simp)
  · exact ht1cl

private lemma Phase10_first_refl (s t : AgentState L K)
    (h : (Phase10Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase10Transition at h; dsimp only at h
  split_ifs at h <;> simp_all

private lemma Phase10_second_refl (s t : AgentState L K)
    (h : (Phase10Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase10Transition at h; dsimp only at h
  split_ifs at h <;> simp_all

/-- Phase 9 (= Phase 2) first output reflects clock role at phase `≥ 3` (the
advancing branch fires `advancePhaseWithInit`, role-preserving via `apwi_role_eq_ge3`;
other branches only edit `output`/`opinions`). -/
private lemma Phase9_first_refl (s t : AgentState L K) (hge : 3 ≤ s.phase.val)
    (h : (Phase9Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase9Transition Phase2Transition at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4
  · rw [apwi_role_eq_ge3 _ (by simpa using hge)] at h; simpa using h
  · simpa using h
  · simpa using h
  · simpa using h
  · simpa using h

private lemma Phase9_second_refl (s t : AgentState L K) (hge : 3 ≤ t.phase.val)
    (h : (Phase9Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase9Transition Phase2Transition at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4
  · rw [apwi_role_eq_ge3 _ (by simpa using hge)] at h; simpa using h
  · simpa using h
  · simpa using h
  · simpa using h
  · simpa using h

/-- Phase 3 first output reflects clock role: the `s1`-clock branches all live
under the guard `s.role = clock ∧ t.role = clock`, and `s2`/the cancel-split keep
role. -/
private lemma Phase3_first_refl (s t : AgentState L K)
    (h : (Phase3Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase3Transition at h
  dsimp only at h
  set s1 := (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then
        { s with minute := ⟨s.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K s else s) with hs1
  set t1 := (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then t
      else stdCounterSubroutine L K t else t) with ht1
  set s2 := (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
      { s1 with hour := ⟨max s1.hour.val (min L (t1.minute.val / K)), by
          exact (Nat.max_lt).mpr ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
    else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1 else s1) with hs2
  set t2 := (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
    else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
      { t1 with hour := ⟨max t1.hour.val (min L (s1.minute.val / K)), by
          exact (Nat.max_lt).mpr ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
    else t1) with ht2
  change (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).1.role = .clock at h
  have hs2cl : s2.role = .clock := by
    split_ifs at h with hm
    · rw [p3cs_role_fst] at h; exact h
    · exact h
  have hs1cl : s1.role = .clock := by
    rw [hs2] at hs2cl; split_ifs at hs2cl <;> first | exact hs2cl | simpa using hs2cl
  rw [hs1] at hs1cl
  split_ifs at hs1cl with hboth
  · exact hboth.1
  · exact hboth.1
  · exact hboth.1
  · exact hs1cl

/-- Phase 3 second output reflects clock role. -/
private lemma Phase3_second_refl (s t : AgentState L K)
    (h : (Phase3Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase3Transition at h
  dsimp only at h
  set s1 := (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then
        { s with minute := ⟨s.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K s else s) with hs1
  set t1 := (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then t
      else stdCounterSubroutine L K t else t) with ht1
  set s2 := (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
      { s1 with hour := ⟨max s1.hour.val (min L (t1.minute.val / K)), by
          exact (Nat.max_lt).mpr ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
    else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1 else s1) with hs2
  set t2 := (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
    else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
      { t1 with hour := ⟨max t1.hour.val (min L (s1.minute.val / K)), by
          exact (Nat.max_lt).mpr ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
    else t1) with ht2
  change (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).2.role = .clock at h
  have ht2cl : t2.role = .clock := by
    split_ifs at h with hm
    · rw [p3cs_role_snd] at h; exact h
    · exact h
  have ht1cl : t1.role = .clock := by
    rw [ht2] at ht2cl; split_ifs at ht2cl <;> first | exact ht2cl | simpa using ht2cl
  rw [ht1] at ht1cl
  split_ifs at ht1cl with hboth
  · exact hboth.2
  · exact hboth.2
  · exact hboth.2
  · exact ht1cl

/-! #### Epidemic-stage role REFLECTION at phase `≥ 3`.

The epidemic stage runs `runInitsBetween` over phases strictly between the input
phase and the common max.  When the input is at phase `≥ 3`, every inited phase is
`≥ 4`, whose `phaseInit` PRESERVES role; the `phase10EpidemicEntry` wrapper also
preserves role.  Hence the epidemic output role EQUALS the input role. -/

/-- `runInitsBetween` from a phase `≥ 3` start preserves role (all inited phases are
`≥ 4`, and `phaseInit` changes role only at phase `1`). -/
private lemma foldl_phaseInit_role_eq (l : List ℕ) (hmem : ∀ k ∈ l, 4 ≤ k)
    (a : AgentState L K) :
    (l.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a).role
      = a.role := by
  induction l generalizing a with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    rw [ih (fun k' hk' => hmem k' (List.mem_cons_of_mem k hk'))]
    have hk4 : 4 ≤ k := hmem k List.mem_cons_self
    by_cases hk : k < 11
    · rw [dif_pos hk]; exact phaseInit_role_eq_of_ge_four ⟨k, hk⟩ a (by simpa using hk4)
    · rw [dif_neg hk]

private lemma runInitsBetween_role_eq_of_old_ge3 (oldP newP : ℕ) (h3 : 3 ≤ oldP)
    (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).role = a.role := by
  unfold runInitsBetween
  apply foldl_phaseInit_role_eq
  intro k hk; rw [List.mem_filter] at hk; simp only [decide_eq_true_eq] at hk; omega

/-- The epidemic FIRST output role equals the input role, when the input is at
phase `≥ 3`. -/
private lemma epidemic_first_role_eq_ge3 (s t : AgentState L K) (hs : 3 ≤ s.phase.val) :
    (phaseEpidemicUpdate L K s t).1.role = s.role := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  have hp3 : 3 ≤ p.val := by
    have : s.phase.val ≤ p.val := by
      exact_mod_cast (le_max_left s.phase t.phase : s.phase ≤ max s.phase t.phase)
    omega
  have hbase : ({ s with phase := p } : AgentState L K).role = s.role := rfl
  have hrun := runInitsBetween_role_eq_of_old_ge3 s.phase.val p.val (by omega)
    ({ s with phase := p })
  by_cases hbr : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      ((runInitsBetween L K s.phase.val p.val { s with phase := p }).phase.val = 10 ∨
       (runInitsBetween L K t.phase.val p.val { t with phase := p }).phase.val = 10)
  · rw [if_pos hbr]
    show (phase10EpidemicEntry L K s
      (runInitsBetween L K s.phase.val p.val { s with phase := p })).role = s.role
    rw [phase10EpidemicEntry_role, hrun, hbase]
  · rw [if_neg hbr]
    show (runInitsBetween L K s.phase.val p.val { s with phase := p }).role = s.role
    rw [hrun, hbase]

/-- The epidemic SECOND output role equals the input role, when the input is at
phase `≥ 3`. -/
private lemma epidemic_second_role_eq_ge3 (s t : AgentState L K) (ht : 3 ≤ t.phase.val) :
    (phaseEpidemicUpdate L K s t).2.role = t.role := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  have hp3 : 3 ≤ p.val := by
    have : t.phase.val ≤ p.val := by
      exact_mod_cast (le_max_right s.phase t.phase : t.phase ≤ max s.phase t.phase)
    omega
  have hbase : ({ t with phase := p } : AgentState L K).role = t.role := rfl
  have hrun := runInitsBetween_role_eq_of_old_ge3 t.phase.val p.val (by omega)
    ({ t with phase := p })
  by_cases hbr : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      ((runInitsBetween L K s.phase.val p.val { s with phase := p }).phase.val = 10 ∨
       (runInitsBetween L K t.phase.val p.val { t with phase := p }).phase.val = 10)
  · rw [if_pos hbr]
    show (phase10EpidemicEntry L K t
      (runInitsBetween L K t.phase.val p.val { t with phase := p })).role = t.role
    rw [phase10EpidemicEntry_role, hrun, hbase]
  · rw [if_neg hbr]
    show (runInitsBetween L K t.phase.val p.val { t with phase := p }).role = t.role
    rw [hrun, hbase]

/-! #### Assembled `Transition` clock-role reflection at dispatch phase `≥ 3`. -/

/-- A clock first OUTPUT of `Transition` comes only from a clock first INPUT, when
both inputs are at phase `≥ 3`.  (No clock is created away from Phase 0.)  Assembled
through the epidemic stage and the `interval_cases` dispatch (Phases 3–10), mirroring
`Transition_preserves_clock_role_of_phase_ge_1` in the reflecting direction. -/
theorem Transition_first_no_clock_creation_of_phase_ge_3 (s t : AgentState L K)
    (hs : 3 ≤ s.phase.val) (_ht : 3 ≤ t.phase.val)
    (hns : s.role ≠ .clock) :
    (Transition L K s t).1.role ≠ .clock := by
  classical
  intro hcl
  apply hns
  -- epidemic stage REFLECTS clock role: if (epidemic).1 is a clock, so is s.
  have hepi_phase : 3 ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
    have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    have : s.phase.val ≤ max s.phase.val t.phase.val := le_max_left _ _
    omega
  set s' := (phaseEpidemicUpdate L K s t).1 with hs'
  set t' := (phaseEpidemicUpdate L K s t).2 with ht'
  -- reduce the dispatch.
  have hTeq : (Transition L K s t).1 = finishPhase10Entry L K s'
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
        | _ => (s', t')).1 := by
    conv_lhs => unfold Transition
    rfl
  rw [hTeq, finishPhase10Entry_role_eq] at hcl
  -- the dispatched output is a clock ⟹ s' is a clock ⟹ s is a clock.
  have hs'cl : s'.role = .clock := by
    rcases hpv : s'.phase with ⟨pv, hpvlt⟩
    have hpv3 : 3 ≤ pv := by have := hepi_phase; rw [hpv] at this; exact this
    rw [hpv] at hcl
    interval_cases pv
    · exact Phase3_first_refl s' t' (by simpa using hcl)
    · exact Phase4_first_refl s' t' (by simpa using hcl)
    · exact Phase5_first_refl s' t' (by simpa using hcl)
    · exact Phase6_first_refl s' t' (by simpa using hcl)
    · exact Phase7_first_refl s' t' (by simpa using hcl)
    · exact Phase8_first_refl s' t' (by simpa using hcl)
    · have h9 : 3 ≤ s'.phase.val := by rw [hpv]; omega
      exact Phase9_first_refl s' t' h9 (by simpa using hcl)
    · exact Phase10_first_refl s' t' (by simpa using hcl)
  -- epidemic first output role EQUALS s.role (phase ≥ 3): so s' clock ⟹ s clock.
  rw [hs'] at hs'cl
  rwa [epidemic_first_role_eq_ge3 s t hs] at hs'cl

/-- Second-output version of `Transition_first_no_clock_creation_of_phase_ge_3`. -/
theorem Transition_second_no_clock_creation_of_phase_ge_3 (s t : AgentState L K)
    (hs : 3 ≤ s.phase.val) (ht : 3 ≤ t.phase.val)
    (hnt : t.role ≠ .clock) :
    (Transition L K s t).2.role ≠ .clock := by
  classical
  intro hcl
  apply hnt
  have hs'_phase : 3 ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
    have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    have : s.phase.val ≤ max s.phase.val t.phase.val := le_max_left _ _
    omega
  have ht'_phase : 3 ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
    have hge := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
    have : t.phase.val ≤ max s.phase.val t.phase.val := le_max_right _ _
    omega
  set s' := (phaseEpidemicUpdate L K s t).1 with hs'
  set t' := (phaseEpidemicUpdate L K s t).2 with ht'
  have hTeq : (Transition L K s t).2 = finishPhase10Entry L K t'
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
        | _ => (s', t')).2 := by
    conv_lhs => unfold Transition
    rfl
  rw [hTeq, finishPhase10Entry_role_eq] at hcl
  have ht'cl : t'.role = .clock := by
    rcases hpv : s'.phase with ⟨pv, hpvlt⟩
    have hpv3 : 3 ≤ pv := by have := hs'_phase; rw [hpv] at this; exact this
    rw [hpv] at hcl
    interval_cases pv
    · exact Phase3_second_refl s' t' (by simpa using hcl)
    · exact Phase4_second_refl s' t' (by simpa using hcl)
    · exact Phase5_second_refl s' t' (by simpa using hcl)
    · exact Phase6_second_refl s' t' (by simpa using hcl)
    · exact Phase7_second_refl s' t' (by simpa using hcl)
    · exact Phase8_second_refl s' t' (by simpa using hcl)
    · exact Phase9_second_refl s' t' ht'_phase (by simpa using hcl)
    · exact Phase10_second_refl s' t' (by simpa using hcl)
  rw [ht'] at ht'cl
  rwa [epidemic_second_role_eq_ge3 s t ht] at ht'cl

/-! #### Exact per-pair clock-count conservation and `clockSize` closure. -/

/-- Per-pair EXACT clock-count conservation at phase `≥ 3`: the produced pair has
the same number of clock-role agents as the consumed pair.  Combines clock-role
PERMANENCE (`Transition_*_preserves_clock_role_of_phase_ge_1`) with NO clock
CREATION (`Transition_*_no_clock_creation_of_phase_ge_3`). -/
theorem clockCount_pair_eq (r₁ r₂ : AgentState L K)
    (h1ge : 3 ≤ r₁.phase.val) (h2ge : 3 ≤ r₂.phase.val) :
    Multiset.countP (fun a => a.role = .clock)
        ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
          : Multiset (AgentState L K))
      = Multiset.countP (fun a => a.role = .clock)
          ({r₁, r₂} : Multiset (AgentState L K)) := by
  classical
  have hpairP : ∀ x y : AgentState L K,
      Multiset.countP (fun a => a.role = .clock) ({x, y} : Multiset (AgentState L K))
        = (if x.role = .clock then 1 else 0) + (if y.role = .clock then 1 else 0) := by
    intro x y
    rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl,
        Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    by_cases hx : x.role = .clock <;> by_cases hy : y.role = .clock <;> simp [hx, hy]
  rw [hpairP, hpairP]
  have hleft : (if (Transition L K r₁ r₂).1.role = .clock then (1:ℕ) else 0)
      = (if r₁.role = .clock then 1 else 0) := by
    by_cases h1 : r₁.role = .clock
    · have hout : (Transition L K r₁ r₂).1.role = .clock :=
        Transition_preserves_clock_role_of_phase_ge_1 (L := L) (K := K) r₁ r₂
          (by omega) (by omega) h1
      rw [if_pos h1, if_pos hout]
    · have hout : (Transition L K r₁ r₂).1.role ≠ .clock :=
        Transition_first_no_clock_creation_of_phase_ge_3 r₁ r₂ h1ge h2ge h1
      rw [if_neg h1, if_neg hout]
  have hright : (if (Transition L K r₁ r₂).2.role = .clock then (1:ℕ) else 0)
      = (if r₂.role = .clock then 1 else 0) := by
    by_cases h2 : r₂.role = .clock
    · have hout : (Transition L K r₁ r₂).2.role = .clock :=
        Transition_second_preserves_clock_role_of_phase_ge_1 (L := L) (K := K) r₁ r₂
          (by omega) (by omega) h2
      rw [if_pos h2, if_pos hout]
    · have hout : (Transition L K r₁ r₂).2.role ≠ .clock :=
        Transition_second_no_clock_creation_of_phase_ge_3 r₁ r₂ h1ge h2ge h2
      rw [if_neg h2, if_neg hout]
  rw [hleft, hright]

/-- **`qmix_clockSize_closed`.**  `clockCount = mC` is preserved on the support,
UNDER the added invariant `allPhaseGE3` (clock-creation stage complete).  Genuine:
exact per-pair clock-count conservation (`clockCount_pair_eq`) lifts to the whole
config — every consumed pair is at phase `≥ 3`, so no clock is created or destroyed. -/
theorem qmix_clockSize_closed (n mC T : ℕ)
    (c c' : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    clockCount (L := L) (K := K) c' = mC := by
  classical
  rw [← hQ.clockSize]
  -- it suffices: clockCount c' = clockCount c.
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    simp only [Protocol.scheduledStep]
    by_cases happ : Protocol.Applicable c r₁ r₂
    · have hmem1 : r₁ ∈ c := mem_of_applicable_left happ
      have hmem2 : r₂ ∈ c := mem_of_applicable_right happ
      have h1ge : 3 ≤ r₁.phase.val := hge r₁ hmem1
      have h2ge : 3 ≤ r₂.phase.val := hge r₂ hmem2
      have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
      unfold clockCount
      rw [hc'eq, Multiset.countP_add, Multiset.countP_sub hsub,
          clockCount_pair_eq r₁ r₂ h1ge h2ge]
      -- countP over the consumed pair ≤ countP over c (since the pair ≤ c).
      have hle : Multiset.countP (fun a => a.role = .clock)
          ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => a.role = .clock) c :=
        Multiset.countP_le_of_le _ hsub
      omega
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    rfl

/-! ## Part 4 — the assembled deterministic closure and the SCOPED hard residual.

The three deterministic fields are now discharged (under the honestly-named added
invariant `allPhaseGE3` for `clockSize`, with `allPhaseGE3` itself closed).  We
package the closure of the augmented window `Q_mix ∧ allPhaseGE3` MINUS the
`clockPhase3` field, i.e. the deterministic skeleton of `habs_mix`. -/

/-- **The deterministic skeleton of `habs_mix`.**  On a config satisfying
`Q_mix n mC T ∧ allPhaseGE3` (with `1 ≤ T`), every successor on the support
satisfies `card = n`, `clockCount = mC`, `crossedT`, and `allPhaseGE3` — i.e. ALL
of `Q_mix` EXCEPT the `clockPhase3` field, plus the closed added invariant.  The
remaining `clockPhase3` field is the SCOPED hard residual (see below). -/
theorem habs_mix_deterministic_skeleton (n mC T : ℕ) (hT : 1 ≤ T)
    (c c' : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    c'.card = n ∧
      clockCount (L := L) (K := K) c' = mC ∧
      9 * mC / 10 ≤ rBeyond (L := L) (K := K) T c' ∧
      allPhaseGE3 (L := L) (K := K) c' :=
  ⟨qmix_card_closed n mC T c c' hQ hc',
   qmix_clockSize_closed n mC T c c' hQ hge hc',
   qmix_crossedT_closed n mC T hT c c' hQ hc',
   allPhaseGE3_closed c c' hge hc'⟩

/-! ### The remaining `clockPhase3` synchronization sub-lemma (NAMED, not proven).

`clockPhase3` (clocks at phase EXACTLY 3) is preserved one step ONLY under the
combined invariant `Q_mix ∧ noPhaseAbove3 ∧ allClocksCounterPos`:

  * `noPhaseAbove3 c := ∀ a ∈ c, a.phase.val ≤ 3` — so the epidemic never drags a
    phase-3 clock UP to a higher-phase partner;
  * `allClocksCounterPos c := ∀ a ∈ c, a.role = .clock → 0 < a.counter.val` — so a
    clock at the cap does NOT advance 3 → 4
    (`Transition_phase3_clock_done_positive_preserves_and_decreases` keeps phase 3
    when both counters are positive; `Transition_phase3_clock_done_counter_zero_advances`
    advances to phase 4 when a counter is 0).

`noPhaseAbove3` together with `allPhaseGE3` pins ALL agents at phase EXACTLY 3, and
under positive counters the Phase-3 rule keeps every clock at phase 3 (below the cap
it edits only `minute`; at the cap it merely decrements the counter).  THAT step is
fully covered by the already-proven kernel lemmas.

The OBSTRUCTION is the one-step closure of `allClocksCounterPos`: the counter
decrements only at the cap and must remain `≥ 1` until the clock genuinely completes
its run — exactly the FRONT-SHAPE SYNCHRONIZATION fact (the clocks reach the cap
TOGETHER at the END of the run; the counter does not hit 0 early).  This is a
multi-step REACHABILITY invariant, NOT a one-step support-closure, and it is the
SINGLE precisely-named sub-lemma that remains to fully discharge `habs_mix`.

We RECORD it as a `def`-level statement (the named obligation), deliberately NOT
proving it (it is beyond one-step closure).  Discharging it — together with
`habs_mix_deterministic_skeleton` and the kernel positive-counter lemmas above —
would give full `Q_mix` one-step closure, i.e. `habs_mix`. -/

/-- No clock is at phase strictly above 3 (the epidemic cannot drag a phase-3 clock
up). -/
def noPhaseAbove3 (c : Config (AgentState L K)) : Prop := ∀ a ∈ c, a.phase.val ≤ 3

/-- Every clock still has a strictly positive counter (its run is not yet complete).
-/
def allClocksCounterPos (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .clock → 0 < a.counter.val

/-- **THE REMAINING SYNCHRONIZATION SUB-LEMMA (named, not proven here).**  One-step
closure of `allClocksCounterPos` on the `Q_mix ∧ allPhaseGE3 ∧ noPhaseAbove3`
window.  This is Doty's front-shape synchronization: clocks reach the cap together
at the END of the run, so the per-clock counter stays `≥ 1` until completion and
does not hit `0` early.  It is a MULTI-STEP reachability invariant; once supplied,
it closes `clockPhase3` and hence (with `habs_mix_deterministic_skeleton`) all of
`habs_mix`.  Stated as a `Prop`-valued obligation, NOT asserted. -/
def ClockPhase3_remaining_synchronization (n mC T : ℕ) : Prop :=
  ∀ c c' : Config (AgentState L K),
    Q_mix (L := L) (K := K) n mC T c →
    allPhaseGE3 (L := L) (K := K) c →
    noPhaseAbove3 (L := L) (K := K) c →
    allClocksCounterPos (L := L) (K := K) c →
    c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
    allClocksCounterPos (L := L) (K := K) c'

end HabsDischarge

end ExactMajority
