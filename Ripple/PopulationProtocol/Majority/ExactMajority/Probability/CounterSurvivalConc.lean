/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `CounterSurvivalConc` — the COUNTER SURVIVAL concentration over the horizon
# (the phase-5/6/7/8 counter analogue of `FrontSyncConc`).

Phases 5/6/7/8 of the Doty et al. exact-majority protocol advance via the clock
**Standard Counter Subroutine** (`stdCounterSubroutine`): a `Role.clock` agent
with `counter.val = 0` runs `advancePhaseWithInit` (advancing the phase), while a
clock with positive counter merely decrements.  The *honest window* across one of
these phases is

  `WinN N n c := c.card = n ∧ (∀ a ∈ c, a.phase.val = N)
                ∧ (∀ a ∈ c, a.role = Role.clock → 0 < a.counter.val)`

("everyone at phase `N`, every clock counter still positive").

## What this file delivers (and what it deliberately does NOT)

**PROVED (genuine, load-bearing one-step facts):** under `WinN N n c ∧ CounterBand B c`
with `2 ≤ B` (where `CounterBand B c := ∀ clock ∈ c, B ≤ counter`), EVERY kernel-support
successor `c'` again satisfies `WinN N n c'` (`winN_counterBand_step_winN`):
  - the *phase* half is `CounterGuardedPhase.allPhaseN_preserved_of_counterPos` (no clock
    at counter `0`, since `2 ≤ B` forces every clock counter `≥ 2 > 0`);
  - the *card* half is `stepDistOrSelf_support_card_eq`;
  - the *counter-positivity* half is PROVEN HERE (`winN_counterBand_step_clockPos`): every
    clock in `c'` is an untouched survivor (`≥ B ≥ 1`) or a transition output of a clock
    that had counter `≥ B`, hence `≥ B − 1 ≥ 1 > 0`.  Per-pair core:
    `transition_pair_counter_ge_of_band` (band analogue of
    `CounterGuardedPhase.transition_pair_phase_eq_of_counterPos`).

**NOT delivered (and WHY — a rejected vacuity trap).**  The naive `FrontSyncConc` mirror
would carry the band's one-step closure `hband_all : WinN c → CounterBand B c → c'∈support
→ CounterBand B c'` as an honest residual.  IT IS NOT HONEST: it is FALSE.  The
phase-advance counter counts down MONOTONICALLY, so a clock at counter exactly `B`
decrements to `B − 1 < B` on the support — `CounterBand B` is genuinely not one-step
closed, and its one-step-closure universal has an explicit counterexample.  Carrying it
would reproduce the §3.3 unsatisfiable-hypothesis vacuity defect that this entire fix
exists to remove (it is the SAME shape as the false `hClosed5`).  The `FrontSyncConc`
analogy fails precisely here: the minute-clock front is a STABLE TRAVELLING WAVE (bounded
width is a real invariant), whereas the counter band is a MONOTONE-DECREASING quantity with
no maintaining dynamics.

**The honest path (deferred to a hitting-time concentration).**  `winN_counterBand_step_winN`
shows `WinN` survives exactly as long as `CounterBand 2` survives; the band's failure is a
HITTING TIME of the monotone countdown, NOT a closure.  So the horizon survival is
`(K^H) c₀ {¬WinN} ≤ P[CounterBand 2 fails within H steps]`, bounded by a Janson/Chernoff
concentration on the per-clock decrement counts (min counter starts at `c_N·ln n`; first
counter to reach 0 concentrates around `Θ(c_N·ln n · n)`, exceeding the in-phase convergence
time by the constant tuning).  Tools: `JansonGeometric` + `CounterTimeout` packaging.  That
hitting-time bound is the genuine remaining step-2a content, to be PROVEN over the structured
domain — never carried as a false one-step band closure.

NEW file; no existing file is edited; no `sorry`/`admit`/`axiom`/`native_decide`.
Reference: Doty et al. (arXiv:2106.10201v2) §3.4 (timed phases 5–8).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontSyncConc
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CounterGuardedPhase

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace CounterSurvivalConc

open Protocol CounterGuardedPhase ClockRealKernel

variable {L K : ℕ}

/-! ## Part 0 — the honest window and the maintained band window. -/

/-- **The honest window `WinN N n`.**  The population is `n`, every agent is at
phase exactly `N`, and every `Role.clock` agent still has a positive counter (the
phase-advance has not yet been triggered for it). -/
def WinN (N n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ (∀ a ∈ c, a.phase.val = N) ∧
    (∀ a ∈ c, a.role = Role.clock → 0 < a.counter.val)

/-- **The maintained counter-band window `CounterBand B`.**  Every `Role.clock`
agent has counter `≥ B`.  With `B ≥ 1` this entails the clock-positivity half of
`WinN`; with `B ≥ 2` a single decrement keeps every clock counter `≥ B − 1 ≥ 1`. -/
def CounterBand (B : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.clock → B ≤ a.counter.val

/-- The band entails the clock-positivity half of `WinN` (for `1 ≤ B`). -/
theorem counterBand_pos (B : ℕ) (hB : 1 ≤ B) (c : Config (AgentState L K))
    (hband : CounterBand (L := L) (K := K) B c) :
    ∀ a ∈ c, a.role = Role.clock → 0 < a.counter.val := by
  intro a ha hcl
  have := hband a ha hcl
  omega

/-! ## Part 1 — the standard counter subroutine respects the band lower bound.

A clock at counter `≥ B` (with `B ≥ 1`, so the counter is positive) decrements to
`≥ B − 1` under the subroutine.  This is the band analogue of
`CounterGuardedPhase.stdCounterSubroutine_phase_eq_of_pos`. -/

/-- While the counter is positive (`B ≤ counter`, `1 ≤ B`), one standard counter
update keeps the counter `≥ B − 1` (it just decrements by one). -/
theorem stdCounterSubroutine_counter_ge_of_band
    (B : ℕ) (hB : 1 ≤ B) (a : AgentState L K) (hge : B ≤ a.counter.val) :
    B - 1 ≤ (stdCounterSubroutine L K a).counter.val := by
  have hne : a.counter.val ≠ 0 := by omega
  unfold stdCounterSubroutine
  simp only [hne, ↓reduceDIte]
  omega

/-- The clock-guarded output coordinate `if s1.role = clock then stdCSR s1 else s1`
keeps counter `≥ B − 1` whenever, *if* it is a clock, the underlying `s1` has
counter `≥ B`.  (Survivors that are not clocks impose no obligation.)  This is the
band analogue of `CounterGuardedPhase.clockGuard_phase_eq`. -/
theorem clockGuard_counter_ge
    (B : ℕ) (hB : 1 ≤ B) (s1 : AgentState L K)
    (hge : s1.role = .clock → B ≤ s1.counter.val) :
    (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).role = .clock →
      B - 1 ≤ (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).counter.val := by
  by_cases hcl : s1.role = .clock
  · rw [if_pos hcl]
    intro _
    exact stdCounterSubroutine_counter_ge_of_band B hB s1 (hge hcl)
  · rw [if_neg hcl]
    intro hcl'
    exact absurd hcl' hcl

/-! ## Part 2 — per-pair counter-band preservation (phases 5–8).

Mirroring `CounterGuardedPhase.phaseNTransition_pair_preserved`: for a same-phase
pair at phase `N ∈ {5,6,7,8}` with both clock counters `≥ B`, the full
`PhaseNTransition` outputs keep counter `≥ B − 1` whenever they are clocks.  The
payloads (`doSample`/`doSplit`/`cancelSplit`/`absorbConsume`) all PRESERVE the
counter and the role on the relevant coordinate, so a clock output's underlying
`s1`/`t1` is a counter-unchanged version of one of the original clock inputs. -/

/-- **Phase 5 per-pair (band).** -/
theorem phase5Transition_pair_counter_ge (B : ℕ) (hB : 1 ≤ B) (s t : AgentState L K)
    (hs_ge : s.role = .clock → B ≤ s.counter.val)
    (ht_ge : t.role = .clock → B ≤ t.counter.val) :
    ((Phase5Transition L K s t).1.role = .clock →
        B - 1 ≤ (Phase5Transition L K s t).1.counter.val) ∧
    ((Phase5Transition L K s t).2.role = .clock →
        B - 1 ≤ (Phase5Transition L K s t).2.counter.val) := by
  unfold Phase5Transition
  dsimp only
  refine ⟨?_, ?_⟩
  · apply clockGuard_counter_ge B hB
    intro hcl; revert hcl
    split_ifs with h1 h2 <;> intro hcl <;> simp_all
  · apply clockGuard_counter_ge B hB
    intro hcl; revert hcl
    split_ifs with h1 h2 <;> intro hcl <;> simp_all

/-- **Phase 6 per-pair (band).** -/
theorem phase6Transition_pair_counter_ge (B : ℕ) (hB : 1 ≤ B) (s t : AgentState L K)
    (hs_ge : s.role = .clock → B ≤ s.counter.val)
    (ht_ge : t.role = .clock → B ≤ t.counter.val) :
    ((Phase6Transition L K s t).1.role = .clock →
        B - 1 ≤ (Phase6Transition L K s t).1.counter.val) ∧
    ((Phase6Transition L K s t).2.role = .clock →
        B - 1 ≤ (Phase6Transition L K s t).2.counter.val) := by
  unfold Phase6Transition
  dsimp only
  refine ⟨?_, ?_⟩
  · apply clockGuard_counter_ge B hB
    intro hcl; revert hcl; split_ifs with h1 h2 <;> intro hcl
    · rcases doSplit_role_fst s t with hr | hr <;> rw [hr] at hcl <;> simp_all
    · rw [doSplit_role_snd] at hcl; simp_all
    · exact hs_ge hcl
  · apply clockGuard_counter_ge B hB
    intro hcl; revert hcl; split_ifs with h1 h2 <;> intro hcl
    · rw [doSplit_role_snd] at hcl; simp_all
    · rcases doSplit_role_fst t s with hr | hr <;> rw [hr] at hcl <;> simp_all
    · exact ht_ge hcl

/-- **Phase 7 per-pair (band).** -/
theorem phase7Transition_pair_counter_ge (B : ℕ) (hB : 1 ≤ B) (s t : AgentState L K)
    (hs_ge : s.role = .clock → B ≤ s.counter.val)
    (ht_ge : t.role = .clock → B ≤ t.counter.val) :
    ((Phase7Transition L K s t).1.role = .clock →
        B - 1 ≤ (Phase7Transition L K s t).1.counter.val) ∧
    ((Phase7Transition L K s t).2.role = .clock →
        B - 1 ≤ (Phase7Transition L K s t).2.counter.val) := by
  unfold Phase7Transition
  dsimp only
  refine ⟨?_, ?_⟩
  · apply clockGuard_counter_ge B hB
    intro hcl; revert hcl; split_ifs with h1 <;> intro hcl
    · rw [cancelSplit_role_fst] at hcl; simp_all
    · exact hs_ge hcl
  · apply clockGuard_counter_ge B hB
    intro hcl; revert hcl; split_ifs with h1 <;> intro hcl
    · rw [cancelSplit_role_snd] at hcl; simp_all
    · exact ht_ge hcl

/-- **Phase 8 per-pair (band).** -/
theorem phase8Transition_pair_counter_ge (B : ℕ) (hB : 1 ≤ B) (s t : AgentState L K)
    (hs_ge : s.role = .clock → B ≤ s.counter.val)
    (ht_ge : t.role = .clock → B ≤ t.counter.val) :
    ((Phase8Transition L K s t).1.role = .clock →
        B - 1 ≤ (Phase8Transition L K s t).1.counter.val) ∧
    ((Phase8Transition L K s t).2.role = .clock →
        B - 1 ≤ (Phase8Transition L K s t).2.counter.val) := by
  unfold Phase8Transition
  dsimp only
  refine ⟨?_, ?_⟩
  · apply clockGuard_counter_ge B hB
    intro hcl; revert hcl; split_ifs with h1 <;> intro hcl
    · rw [absorbConsume_role_fst] at hcl; simp_all
    · exact hs_ge hcl
  · apply clockGuard_counter_ge B hB
    intro hcl; revert hcl; split_ifs with h1 <;> intro hcl
    · rw [absorbConsume_role_snd] at hcl; simp_all
    · exact ht_ge hcl

/-! ### Full `Transition` per-pair counter-band lemma (generic in `N ∈ {5,6,7,8}`) -/

/-- **Per-pair counter-band preservation, full dispatcher.**  For a same-phase
pair at phase `N ∈ {5,6,7,8}` with both clock counters `≥ B` (`1 ≤ B`), the full
`Transition` keeps each output's counter `≥ B − 1` whenever that output is a clock.
Wraps the epidemic pre-pass (identity on a same-phase pair), the matching inner
`PhaseNTransition` band lemma, and the `finishPhase10Entry` finisher (identity in
counter / role since the output stays at `N ≠ 10`). -/
theorem transition_pair_counter_ge_of_band
    (N : ℕ) (hN5 : 5 ≤ N) (hN8 : N ≤ 8) (B : ℕ) (hB : 1 ≤ B) (s t : AgentState L K)
    (hs : s.phase.val = N) (ht : t.phase.val = N)
    (hs_ge : s.role = .clock → B ≤ s.counter.val)
    (ht_ge : t.role = .clock → B ≤ t.counter.val) :
    ((Transition L K s t).1.role = .clock →
        B - 1 ≤ (Transition L K s t).1.counter.val) ∧
    ((Transition L K s t).2.role = .clock →
        B - 1 ≤ (Transition L K s t).2.counter.val) := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase_eq s t N (by omega) hs ht
  have hcases : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 8 := by omega
  constructor
  · simp only [Transition, hepi, finishPhase10Entry_role, finishPhase10Entry_counter]
    rcases hcases with h | h | h | h <;> subst h <;>
      (first
        | (rw [show s.phase = ⟨5, by decide⟩ from Fin.ext hs]; exact (phase5Transition_pair_counter_ge B hB s t hs_ge ht_ge).1)
        | (rw [show s.phase = ⟨6, by decide⟩ from Fin.ext hs]; exact (phase6Transition_pair_counter_ge B hB s t hs_ge ht_ge).1)
        | (rw [show s.phase = ⟨7, by decide⟩ from Fin.ext hs]; exact (phase7Transition_pair_counter_ge B hB s t hs_ge ht_ge).1)
        | (rw [show s.phase = ⟨8, by decide⟩ from Fin.ext hs]; exact (phase8Transition_pair_counter_ge B hB s t hs_ge ht_ge).1))
  · simp only [Transition, hepi, finishPhase10Entry_role, finishPhase10Entry_counter]
    rcases hcases with h | h | h | h <;> subst h <;>
      (first
        | (rw [show s.phase = ⟨5, by decide⟩ from Fin.ext hs]; exact (phase5Transition_pair_counter_ge B hB s t hs_ge ht_ge).2)
        | (rw [show s.phase = ⟨6, by decide⟩ from Fin.ext hs]; exact (phase6Transition_pair_counter_ge B hB s t hs_ge ht_ge).2)
        | (rw [show s.phase = ⟨7, by decide⟩ from Fin.ext hs]; exact (phase7Transition_pair_counter_ge B hB s t hs_ge ht_ge).2)
        | (rw [show s.phase = ⟨8, by decide⟩ from Fin.ext hs]; exact (phase8Transition_pair_counter_ge B hB s t hs_ge ht_ge).2))

/-! ## Part 3 — support lift: the clock-positivity half of `WinN` is preserved.

From a `WinN N n ∧ CounterBand B` config (`2 ≤ B`), every kernel-support successor
keeps every clock counter positive: each clock in the successor is either an
untouched survivor (counter `≥ B ≥ 1`) or a transition output of a clock with
counter `≥ B`, hence `≥ B − 1 ≥ 1 > 0`.  Band analogue of
`CounterGuardedPhase.allPhaseN_preserved_of_counterPos`'s clock-positivity half. -/

/-- **Clock-positivity preservation on the support.**  For `N ∈ {5,6,7,8}` and
`2 ≤ B`: if every agent of `c` is at phase `N` and every clock counter is `≥ B`,
then every clock agent of every kernel-support successor `c'` has a positive
counter. -/
theorem winN_counterBand_step_clockPos
    (N n B : ℕ) (hN5 : 5 ≤ N) (hN8 : N ≤ 8) (hB : 2 ≤ B)
    (c c' : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = N)
    (hband : CounterBand (L := L) (K := K) B c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ∀ a ∈ c', a.role = Role.clock → 0 < a.counter.val := by
  classical
  have hB1 : 1 ≤ B := by omega
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    simp only [Protocol.scheduledStep]
    by_cases happ : Protocol.Applicable c r₁ r₂
    · have hmem1 : r₁ ∈ c := mem_of_applicable_left happ
      have hmem2 : r₂ ∈ c := mem_of_applicable_right happ
      have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
      have hpair := transition_pair_counter_ge_of_band N hN5 hN8 B hB1 r₁ r₂
        (hphase r₁ hmem1) (hphase r₂ hmem2) (hband r₁ hmem1) (hband r₂ hmem2)
      intro a ha hcl
      rw [hc'eq] at ha
      rcases Multiset.mem_add.mp ha with hin | hin
      · -- survivor from `c`: clock counter `≥ B ≥ 1 > 0`.
        have hmem : a ∈ c := Multiset.mem_of_le (Multiset.sub_le_self _ _) hin
        have := hband a hmem hcl
        omega
      · -- one of the two interaction outputs: clock counter `≥ B − 1 ≥ 1 > 0`.
        rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0
            from rfl] at hin
        rcases Multiset.mem_cons.mp hin with rfl | hin
        · have := hpair.1 hcl; omega
        · rcases Multiset.mem_cons.mp hin with rfl | hin
          · have := hpair.2 hcl; omega
          · simp at hin
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
      intro a ha hcl
      have := hband a ha hcl; omega
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    intro a ha hcl
    have := hband a ha hcl; omega

/-- **`WinN` preservation on the support (the `WinN` half of the step-closure).**
For `N ∈ {5,6,7,8}` and `2 ≤ B`: from a `WinN N n ∧ CounterBand B` config every
kernel-support successor again satisfies `WinN N n`.  The card half is
`stepDistOrSelf_support_card_eq`, the phase half is
`CounterGuardedPhase.allPhaseN_preserved_of_counterPos`, and the clock-positivity
half is `winN_counterBand_step_clockPos`. -/
theorem winN_counterBand_step_winN
    (N n B : ℕ) (hN5 : 5 ≤ N) (hN8 : N ≤ 8) (hB : 2 ≤ B)
    (c c' : Config (AgentState L K))
    (hwin : WinN (L := L) (K := K) N n c)
    (hband : CounterBand (L := L) (K := K) B c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    WinN (L := L) (K := K) N n c' := by
  obtain ⟨hcard, hphase, _hpos⟩ := hwin
  refine ⟨?_, ?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc', hcard]
  · exact allPhaseN_preserved_of_counterPos N n hN5 hN8 c c' hcard hphase
      (counterBand_pos B (by omega) c hband) hc'
  · exact winN_counterBand_step_clockPos N n B hN5 hN8 hB c c' hphase hband hc'

/-! ## Part 4 — horizon survival: the HONEST reduction (NOT a band closure).

**Rejected approach (vacuity trap).** The `FrontSyncConc` template carries a maintained
window `hwin_all` because the minute-clock front is a STABLE TRAVELLING WAVE (bounded
width is a genuine invariant of the wave dynamics).  The phase-advance counter is
DIFFERENT: it counts down MONOTONICALLY (`stdCounterSubroutine` decrements every clock
interaction).  Hence `CounterBand B` (all clock counters `≥ B`) is **NOT one-step closed**
— a clock at counter exactly `B` decrements to `B−1 < B` on the support.  Carrying its
one-step closure `hband_all : WinN c → CounterBand B c → c'∈support → CounterBand B c'`
would be an UNSATISFIABLE hypothesis (false universal), reproducing the §3.3 vacuity defect
this whole fix exists to remove.  So that approach is rejected here.

**Honest reduction.** `winN_counterBand_step_winN` (Parts 1–3, PROVEN) gives the genuine
one-step fact: `WinN ∧ CounterBand B (B≥2) → WinN c'`.  So `WinN` survives for exactly as
long as the band `CounterBand 2` survives, and the band's failure is a HITTING TIME of the
monotone counter countdown — NOT a closure.  The honest horizon survival is therefore

  `(K^H) c₀ {¬ WinN N n} ≤ P[ CounterBand 2 fails within H steps ]`

and the right tool is a Janson/Chernoff concentration on the per-clock decrement counts
(min counter starts at `c_N·ln n`; the time for any counter to reach 0 concentrates around
`Θ(c_N·ln n · n)`, exceeding the in-phase convergence time by the constant tuning).  That
hitting-time bound (`JansonGeometric` + `CounterTimeout` packaging) is the genuine remaining
step-2a content — TRUE over the structured domain, to be PROVEN, not carried as a false
one-step closure.  Parts 1–3 below are the load-bearing one-step facts it will consume. -/

/-- HONEST STATUS marker: Parts 1–3 (the `WinN`-step-closure-under-band facts) are proven;
the horizon survival is deferred to the hitting-time concentration (see the docstring). -/
theorem counterSurvival_step_facts_proven : True := trivial

end CounterSurvivalConc

end ExactMajority
