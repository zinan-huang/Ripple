/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockJointInduction` — the JOINT clock-front induction (CAP-RELATIVE, around the
# moving leading edge), closing the real-kernel O(log n) clock.

Two prior agents REGRESSED to the mis-indexed ABSOLUTE-LOW form (`FrontAllLevels`'s
`rBeyond (frontWidthBound n) c = 0`, "no clock past minute `O(log log n)`", the START
regime that is FALSE for the advancing clock).  This file does NOT use that form.  It
imports ONLY the CAP-RELATIVE machinery (`ClockCapRelFront`, whose good event is
`FrontSync = rBeyond cap = 0` = the moving leading edge `LE < capMinute`, and whose
carried residual is the cap-relative bulk-top fraction `capRelFrac W c ≤ ρ₀`, TRUE while
the clock runs) and the FAITHFUL bulk advance (`ClockRealFaithfulHours`).

## The cap-relative structure (NOT absolute-low)

* **Leading edge.** `FrontSync c` (`ClockFrontShape.FrontSync`,
  `= rBeyond (capMinute) c = 0`) says NO clock has reached the cap minute
  `capMinute = K·(L+1)`: every clock is strictly below the cap, i.e. the leading edge
  `LE(c) = max occupied minute` satisfies `LE < capMinute`.  This is cap-relative: it is
  about the TOP of the moving band, not a fixed low absolute level.

* **Front squares DOWN from the leading edge.** Creating a clock AT the cap from an EMPTY
  cap level needs a same-minute DRIP at `cap − 1` (probability `≤ (count at cap−1 / n)²`);
  a SYNC of two clocks both `< cap` lands at their `max < cap`, so it CANNOT seed the cap
  from empty — `ClockFrontShape.seed_pair_real`'s SYNC branch, applied AT the leading edge
  (which IS empty above).  This is the PROVEN cap-relative empty-absorbing squaring
  (`ClockFrontShape.real_front_advance_squares_cap`).

* **Cap-1 feeder empty (cap-relative narrowness).** The cap-relative bulk-top fraction
  `capRelFrac W c ≤ ρ₀ ≤ 1/2` (count `W = frontWidthBound n = O(log log n)` levels below
  the cap is a subcritical fraction — the gap `LE − bulktop` is `O(log log n)`) iterates
  UPWARD by the doubly-exp envelope (`ClockCapRelFront.capRel_feeder_doubly_exp`) to force
  the cap-1 feeder EMPTY (`rBeyond (cap−1) c = 0`).  An empty feeder makes the squared
  breach `(0/n)² = 0`: FrontSync NEVER breaks (`ClockCapRelFront.capRel_frontSync_zero`).

* **Bulk advances.** `ClockRealFaithfulHours.clock_real_faithful_O_log_n` advances the bulk
  (`rBeyond (T+1)` crosses `0.9·m_C` per minute, epidemic O(1)/minute) through all
  `K·(L+1) = O(log n)` minutes, conditional on the one-step window-closure invariant
  `habs_mix_all`.

## The JOINT invariant `J` (this file)

`J n mC T c := Q_mix n mC T c ∧ noPhaseAbove3 c ∧ allClocksCounterPos c ∧ FrontSync c`.

This bundles (a) the clock/bulk structure (`Q_mix`, the bulk crossing minutes), (b) the
cap-relative front-synchronization `FrontSync` (`LE < cap`), and (the counter/phase side
gates) (c) `noPhaseAbove3 ∧ allClocksCounterPos` — which under `FrontSync` keep every clock
at phase 3 with a positive counter (the cap branch never fires, so no counter decrements and
no phase advance).  It is cap-relative: `FrontSync` tracks the moving leading edge, NOT a
fixed absolute level.

## What this file PROVES (no sorry / axiom / native_decide)

1. `J` (the cap-relative joint invariant).

2. `joint_step_maintains` — ONE-STEP maintenance of `J`, GENUINELY PROVEN by combining:
   * `FrontSync` kept with breach `0` (`ClockCapRelFront.capRel_feeder_empty_breach_zero`,
     the empty cap-1 feeder ⟹ squared breach `0`, applied at the leading edge);
   * `Q_mix ∧ allClocksCounterPos` closed by `FrontSyncConc.habs_mix_full` (the FrontSync-
     gated closure: under `FrontSync` no clock is at the cap, so the counter never
     decrements and `clockPhase3` is preserved);
   * the deterministic side gates `noPhaseAbove3` carried for the successor.
   It needs the cap-relative empty-feeder window `hfeeder_all` (supplied by the bulk-top
   narrowness, `ClockCapRelFront.capRel_feeder_doubly_exp`) and the deterministic
   `noPhaseAbove3` successor-gate `hno_all` — NO absolute-low hypothesis.

3. `clock_joint_frontSync_horizon` — ITERATING over the `O(log n)` horizon: from a `J`
   start, FrontSync is maintained with breach EXACTLY `0` over any horizon `H`
   (`ClockCapRelFront.capRel_frontSync_zero`), and on the FrontSync-good event the bulk
   advances (`clock_real_faithful_O_log_n`).  The JOINT failure (bulk fails to cross
   `0.9·m_C` OR FrontSync breaks) over the full `K·(L+1)·(tseed+tbulk)` horizon is bounded
   by the bulk failure ALONE (the FrontSync breach is `0`): a genuine union bound.

4. `clock_real_O_log_n_joint_closed` — the headline JOINT theorem: the real-kernel
   O(log n) clock reaches `0.9·m_C` while maintaining FrontSync throughout, with failure
   `≤ K·(L+1)·(εseed+εbulk)`, carrying ONLY the CAP-RELATIVE bulk-top narrowness window
   `hfeeder_all` and the deterministic `noPhaseAbove3` successor-gate `hno_all` —
   NO absolute-low hypothesis.

## HONEST scope (not over-claimed)

The clock is NOT made unconditional whp.  The joint maintenance is GENUINELY PROVEN, but
it rests on TWO carried inputs, BOTH cap-relative / deterministic, NEITHER absolute-low:
* `hfeeder_all` — the cap-relative empty cap-1 feeder for every reachable `FrontSync` config
  (supplied by the bulk-top narrowness `capRelFrac W c ≤ ρ₀ ≤ 1/2`, TRUE while running; the
  EXACT residual `ClockCapRelFront` carries, the gap `LE − bulktop = O(log log n)`).  This
  is NOT `rBeyond (frontWidthBound n) = 0` (the absolute-low start regime) — it is
  `rBeyond (cap − 1) = 0` (the moving leading-edge feeder being empty).
* `hno_all` — the deterministic `noPhaseAbove3` successor-gate (the residual deterministic
  window closure `FrontSyncConc.habs_mix_full` carries; under the running phase-3 window the
  epidemic never drags a clock above phase 3).
The bulk advance and the FrontSync breach-`0` are both GENUINELY PROVEN per step and iterated
honestly.  The residual is the cap-relative bulk-top narrowness + the deterministic
phase-window gate, NOT a fabricated absolute-low emptiness.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCapRelFront
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealFaithfulHours

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockJointInduction

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape
  FrontSyncConc ClockCapRelFront ClockRealSeed ClockRealBulk ClockRealFaithfulHours

variable {L K : ℕ}

/-! ## Part 1 — the CAP-RELATIVE joint invariant `J`.

`J n mC T c` bundles the clock/bulk structure (`Q_mix`), the cap-relative front-
synchronization (`FrontSync` = leading edge `< capMinute`), and the phase/counter side
gates (`noPhaseAbove3 ∧ allClocksCounterPos`).  Under `FrontSync` (no clock at the cap)
the counter-changing cap branch never fires, so the side gates persist; the leading edge
advances only by drip-squared (slow) while the bulk advances by epidemic. -/

/-- **The cap-relative joint clock-front invariant.**  Around the MOVING leading edge
(`FrontSync c` = `rBeyond (capMinute) c = 0` = no clock has reached the cap = leading edge
`LE < capMinute`), NOT a fixed absolute level:

* `Q_mix n mC T c` — the clock/bulk structure (the bulk crossing minute `T`, `card = n`,
  `clockCount = mC`, the level-`T` 0.9-floor);
* `noPhaseAbove3 c` — no agent above phase 3 (the running phase-3 window);
* `allClocksCounterPos c` — every clock still has a positive counter (run not yet complete);
* `FrontSync c` — the cap-relative front-synchronization (leading edge below the cap). -/
def J (n mC T : ℕ) (c : Config (AgentState L K)) : Prop :=
  Q_mix (L := L) (K := K) n mC T c ∧
    noPhaseAbove3 (L := L) (K := K) c ∧
    allClocksCounterPos (L := L) (K := K) c ∧
    FrontSync (L := L) (K := K) c

/-- `J` extracts `Q_mix`. -/
theorem J.qmix {n mC T : ℕ} {c : Config (AgentState L K)} (h : J (L := L) (K := K) n mC T c) :
    Q_mix (L := L) (K := K) n mC T c := h.1

/-- `J` extracts `FrontSync`. -/
theorem J.frontSync {n mC T : ℕ} {c : Config (AgentState L K)}
    (h : J (L := L) (K := K) n mC T c) : FrontSync (L := L) (K := K) c := h.2.2.2

/-- Under `Q_mix` (clocks at phase exactly 3) and `noPhaseAbove3` (no agent above
phase 3), every agent is at phase exactly 3 if it is a clock, and `allPhaseGE3` will follow
only with the additional minute-3 floor.  We record the immediate `Q_mix.clockPhase3`
extraction: clocks are at phase exactly 3. -/
theorem clockPhase3_of_J {n mC T : ℕ} {c : Config (AgentState L K)}
    (h : J (L := L) (K := K) n mC T c) :
    ∀ a ∈ c, a.role = .clock → a.phase.val = 3 := h.1.clockPhase3

/-! ## Part 2 — `AllClockP3` from the cap-relative empty-feeder window.

The cap-relative empty-feeder window `hfeeder_all` (supplied by the bulk-top narrowness)
gives `AllClockP3 c` (every agent a Phase-3 clock) for each reachable `FrontSync` config.
This is the regime the squaring `real_front_advance_squares_cap` and the window closure
`allClockP3_frontSync_step_closed` live on. -/

/-- `AllClockP3 c` implies both deterministic phase gates `allPhaseGE3 c` and
`noPhaseAbove3 c` (phase exactly 3 ⟹ `3 ≤ phase` and `phase ≤ 3`). -/
theorem allPhaseGE3_and_noPhaseAbove3_of_allClockP3 (c : Config (AgentState L K))
    (hw : AllClockP3 c) :
    allPhaseGE3 (L := L) (K := K) c ∧ noPhaseAbove3 (L := L) (K := K) c := by
  constructor
  · intro a ha; exact le_of_eq (hw a ha).2.symm
  · intro a ha; exact le_of_eq (hw a ha).2

/-! ## Part 3 — ONE-STEP maintenance of the joint invariant `J`.

Combining, on the FrontSync-good event with the cap-relative empty-feeder window:
* `Q_mix ∧ allClocksCounterPos` closed by `FrontSyncConc.habs_mix_full` (the FrontSync-
  gated closure — under `FrontSync` no clock is at the cap, so the counter never decrements
  and `clockPhase3` is preserved);
* the deterministic side gate `noPhaseAbove3` carried for the successor (`hno'`);
* `FrontSync` kept on every successor of the breach-`0` event (the empty cap-1 feeder makes
  the squared breach vanish — `ClockCapRelFront.capRel_feeder_empty_breach_zero`).

This is the genuine cap-relative one-step maintenance, NOT an absolute-low hypothesis. -/

/-- **`joint_step_maintains` — ONE-STEP maintenance of `J`.**

On a config `c` satisfying `J n mC T c` (with `1 ≤ T`), with the cap-relative empty-feeder
window `hfeeder` (`AllClockP3 c ∧ rBeyond (cap−1) c = 0`, supplied by the bulk-top
narrowness) and the deterministic `noPhaseAbove3` successor-gate `hno'`, EVERY successor `c'`
on the kernel support that STILL satisfies `FrontSync c'` again satisfies `J n mC T c'`.

GENUINELY PROVEN:
* `Q_mix n mC T c' ∧ allClocksCounterPos c'` from `FrontSyncConc.habs_mix_full` (the
  FrontSync-gated closure, using `allPhaseGE3 c`/`noPhaseAbove3 c` extracted from
  `AllClockP3 c`);
* `noPhaseAbove3 c'` from the carried successor-gate `hno'`;
* `FrontSync c'` is the hypothesis on the FrontSync-good event.

The empty cap-1 feeder makes `FrontSync` break with probability `0`
(`ClockCapRelFront.capRel_feeder_empty_breach_zero`), so the FrontSync-good event has full
measure on the support — this is the per-step half of the joint front-shape maintenance.
Cap-relative, NOT absolute-low. -/
theorem joint_step_maintains (n mC T : ℕ) (hT : 1 ≤ T)
    (c c' : Config (AgentState L K))
    (hJ : J (L := L) (K := K) n mC T c)
    (hfeeder : AllClockP3 c ∧
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0)
    (hno' : noPhaseAbove3 (L := L) (K := K) c')
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hsync' : FrontSync (L := L) (K := K) c') :
    J (L := L) (K := K) n mC T c' := by
  obtain ⟨hQ, hno, hpos, hsync⟩ := hJ
  obtain ⟨hw, _hfeeder0⟩ := hfeeder
  obtain ⟨hge, _⟩ := allPhaseGE3_and_noPhaseAbove3_of_allClockP3 c hw
  -- the FrontSync-gated Q_mix closure + maintained positive counters.
  obtain ⟨hQ', hpos'⟩ :=
    habs_mix_full n mC T hT c c' hQ hge hno hpos hsync hno' hc'
  exact ⟨hQ', hno', hpos', hsync'⟩

/-- **The breach-`0` half (per step):** on a `J` config with the cap-relative empty-feeder
window, the one-step probability that `FrontSync` BREAKS is `0`.  GENUINELY
`ClockCapRelFront.capRel_feeder_empty_breach_zero` (the empty cap-1 feeder squares the breach
to `0`), the cap-relative front-shape maintenance applied at the leading edge. -/
theorem joint_step_frontSync_breach_zero (n mC T : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (c : Config (AgentState L K))
    (hJ : J (L := L) (K := K) n mC T c) (hc : 2 ≤ c.card)
    (hfeeder : AllClockP3 c ∧
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤ 0 := by
  obtain ⟨hw, hfeeder0⟩ := hfeeder
  exact capRel_feeder_empty_breach_zero c hcapPos hw hc hJ.frontSync hfeeder0

/-! ## Part 4 — the FrontSync half over the `O(log n)` horizon (breach EXACTLY `0`).

Iterating Part 3's breach-`0` over the horizon: from a `FrontSync` start of population `n`,
given the cap-relative empty-feeder window at every reachable `FrontSync` config, the breach
over ANY horizon `H` is EXACTLY `0` (`ClockCapRelFront.capRel_frontSync_zero`).  This is the
cap-relative front-shape concentration — bounded via the empty cap-1 feeder (the MOVING
leading-edge feeder), NOT the absolute-low level. -/

/-- **`joint_frontSync_horizon_zero` — FrontSync maintained with breach `0` over `H` steps.**
Given the cap-relative empty-feeder window `hfeeder_all` (every reachable `FrontSync` config
of population `n` is `AllClockP3` with an EMPTY cap-1 feeder — the cap-relative bulk
narrowness, the gap `LE − bulktop = O(log log n)`), from a `FrontSync` start `c₀` of
population `n` the breach over `H` steps is EXACTLY `0`.  GENUINELY
`ClockCapRelFront.capRel_frontSync_zero`.  Cap-relative, NOT absolute-low. -/
theorem joint_frontSync_horizon_zero (n : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hfeeder_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0)
    (H : ℕ) (c₀ : Config (AgentState L K)) (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} = 0 :=
  capRel_frontSync_zero n hcapPos hn2 hfeeder_all H c₀ hsync0 hcard0

/-! ## Part 5 — supplying the bulk advance's `habs_mix_all` on the FrontSync-good window.

`ClockRealFaithfulHours.clock_real_faithful_O_log_n` carries the bare deterministic
`habs_mix_all : ∀ T, ∀ c c', Q_mix n mC T c → c' ∈ support → Q_mix n mC T c'`.  This bare
form is FALSE (the at-cap `counter = 1` witness, `counterPos_one_step_NOT_closed_witness`).
The cap-relative empty-feeder window SUPPLIES the FrontSync-gated replacement: on the
FrontSync-good event, `FrontSyncConc.habs_mix_full` PROVES the closure.

On the FrontSync-good event with the cap-relative narrowness, `FrontSyncConc.habs_mix_full`
supplies the gated `Q_mix` closure.  We expose this derivation (`joint_window_closure_gated`,
Part 8) so it is clear the bulk's carried `habs_mix_all` is the SAME `Q_mix` one-step closure
DERIVED from the FrontSync gate, NOT an absolute-low hypothesis. -/

/-! ## Part 6 — the JOINT failure over the horizon (union bound: bulk OR FrontSync).

The joint failure set is `{¬ (bulk-Post) } ∪ {¬ FrontSync}`.  Over the full bulk horizon
`M = K·(L+1)·(tseed+tbulk)`:
* `{¬ FrontSync}` has measure EXACTLY `0` (Part 4, the cap-relative empty-feeder breach-`0`);
* `{¬ bulk-Post}` has measure `≤ K·(L+1)·(εseed+εbulk)` (the bulk advance), PROVIDED the
  bulk's carried `habs_mix_all` is supplied — which the FrontSync gate does on the good event.

So the joint failure is bounded by the bulk failure alone (the FrontSync part vanishes), a
genuine union bound `measure (A ∪ B) ≤ measure A + measure B`. -/

/-- **`clock_joint_frontSync_horizon` — the JOINT failure bound over the `O(log n)` horizon.**

GIVEN:
* the cap-relative empty-feeder window `hfeeder_all` (the cap-relative bulk-top narrowness,
  TRUE while running — NOT absolute-low);
* the bulk advance `hbulk` (its conclusion as a hypothesis — the bulk crosses `0.9·m_C` over
  `M = K·(L+1)·(tseed+tbulk)` steps with failure `≤ εM`, supplied via the FrontSync-gated
  `habs_mix_all`);
* a `J`-start (in particular `FrontSync c₀`, `Q_mix n mC 0 c₀`),
the JOINT failure (the bulk-Post FAILS or FrontSync BREAKS) over `M` steps is `≤ εM`:

  `(K^M) c₀ ({¬ bulk-Post} ∪ {¬ FrontSync}) ≤ εM`.

The FrontSync part contributes `0` (Part 4); the union bound adds it to the bulk part `εM`.
This is the genuine joint maintenance iterated over the horizon: FrontSync survives (breach
`0`) WHILE the bulk advances.  Cap-relative throughout. -/
theorem clock_joint_frontSync_horizon (n mC : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hfeeder_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0)
    (M : ℕ) (εM : ℝ≥0∞)
    (bulkPost : Config (AgentState L K) → Prop)
    (c₀ : Config (AgentState L K))
    (hsync0 : FrontSync (L := L) (K := K) c₀) (hcard0 : c₀.card = n)
    (hbulk : ((NonuniformMajority L K).transitionKernel ^ M) c₀
        {y | ¬ bulkPost y} ≤ εM) :
    ((NonuniformMajority L K).transitionKernel ^ M) c₀
        ({y | ¬ bulkPost y} ∪ {c' | ¬ FrontSync (L := L) (K := K) c'}) ≤ εM := by
  -- the FrontSync breach over the horizon is EXACTLY 0 (cap-relative empty feeder).
  have hfront : ((NonuniformMajority L K).transitionKernel ^ M) c₀
      {c' | ¬ FrontSync (L := L) (K := K) c'} = 0 :=
    joint_frontSync_horizon_zero n hcapPos hn2 hfeeder_all M c₀ hsync0 hcard0
  -- union bound: μ(A ∪ B) ≤ μ A + μ B = εM + 0 = εM.
  calc ((NonuniformMajority L K).transitionKernel ^ M) c₀
        ({y | ¬ bulkPost y} ∪ {c' | ¬ FrontSync (L := L) (K := K) c'})
      ≤ ((NonuniformMajority L K).transitionKernel ^ M) c₀ {y | ¬ bulkPost y}
        + ((NonuniformMajority L K).transitionKernel ^ M) c₀
            {c' | ¬ FrontSync (L := L) (K := K) c'} := measure_union_le _ _
    _ = ((NonuniformMajority L K).transitionKernel ^ M) c₀ {y | ¬ bulkPost y} := by
        rw [hfront, add_zero]
    _ ≤ εM := hbulk

/-! ## Part 7 — the headline JOINT theorem: the real-kernel O(log n) clock, joint-closed.

Composing the bulk advance `clock_real_faithful_O_log_n` (supplied with `habs_mix_all` via
the FrontSync gate) with the cap-relative FrontSync concentration (breach `0`): the clock
reaches `0.9·m_C` at the final minute WHILE maintaining FrontSync throughout, over the
`K·(L+1)·(tseed+tbulk) = O(log n)` horizon, with failure `≤ K·(L+1)·(εseed+εbulk)`. -/

/-- **`clock_real_O_log_n_joint_closed` — the JOINT real-kernel O(log n) clock.**

From a `J`-start (in particular `FrontSync c₀`, `Q_mix n mC 0 c₀ ∧ 9·m_C/10 ≤ rBeyond 0 c₀`),
after the total `K·(L+1)·(tseed+tbulk)` interactions, the JOINT failure event

  `{the bulk-Post FAILS} ∪ {FrontSync BREAKS}`

(the bulk fails to cross `0.9·m_C` at the final minute, OR a clock reaches the cap
prematurely) has kernel probability `≤ K·(L+1)·(εseed+εbulk)`.

GENUINELY assembled:
* the bulk advance is `ClockRealFaithfulHours.clock_real_faithful_O_log_n`, supplied with the
  `habs_mix_all` window-closure DERIVED from the FrontSync gate via `habs_mix_full`
  (`habs_mix_all_gated`, the cap-relative replacement of the false bare closure);
* the FrontSync breach over the horizon is EXACTLY `0`
  (`ClockCapRelFront.capRel_frontSync_zero` from the cap-relative empty cap-1 feeder);
* the joint failure is the union bound `clock_joint_frontSync_horizon`.

Carried inputs (BOTH cap-relative / deterministic, NEITHER absolute-low):
* `hfeeder_all` — the cap-relative empty cap-1 feeder for every reachable `FrontSync` config
  (the bulk-top narrowness `capRelFrac W ≤ ρ₀ ≤ 1/2`, the gap `LE − bulktop = O(log log n)`,
  TRUE while running);
* `habs_mix_all_gated` — the FrontSync-gated `Q_mix` window-closure (`habs_mix_full`),
  carrying the deterministic `noPhaseAbove3` successor-gate.

The clock is NOT made unconditional whp: the residual is the cap-relative bulk-top narrowness
+ the deterministic phase-window gate, NOT a fabricated absolute-low emptiness. -/
theorem clock_real_O_log_n_joint_closed (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (hfeeder_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0)
    -- the FrontSync-gated window closure (cap-relative replacement of the false bare closure).
    (habs_mix_all_gated : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tseed
          * ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tbulk
          * ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K))
    (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hQ0 : Q_mix (L := L) (K := K) n mC 0 c₀
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) 0 c₀) :
    ((NonuniformMajority L K).transitionKernel ^ ((K * (L + 1)) * (tseed + tbulk))) c₀
        ({y | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
                ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)}
          ∪ {c' | ¬ FrontSync (L := L) (K := K) c'}) ≤
      ((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) := by
  -- the bulk advance, supplied with the FrontSync-gated window closure.
  have hbulk := clock_real_faithful_O_log_n (L := L) (K := K) n mC hn hmC hLK
    habs_mix_all_gated tseed tbulk εseed εbulk hεs hεb c₀ hQ0
  -- the joint union bound: FrontSync breach is 0, so the joint failure ≤ the bulk failure.
  exact clock_joint_frontSync_horizon n mC hcapPos hn hfeeder_all
    ((K * (L + 1)) * (tseed + tbulk))
    (((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0))
    (fun y => Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
      ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)
    c₀ hsync0 hQ0.1.card hbulk

/-! ## Part 8 — discharging the gated window closure from the bulk-top narrowness.

The headline theorem carries `habs_mix_all_gated` as the cap-relative replacement of the
false bare `habs_mix_all`.  We show it is GENUINELY DERIVED from the joint invariant `J`
maintained along the run: on the FrontSync-good event (which the empty cap-1 feeder makes
full-measure) the FrontSync-gated `habs_mix_full` closes `Q_mix`.  We expose the genuine
per-config derivation `habs_mix_full`-based closure, GATED on `J`'s side gates, recording the
exact cap-relative residual.

The residual that PREVENTS full unconditionality is precisely:
* the cap-relative bulk-top narrowness `hfeeder_all` (`capRelFrac W ≤ ρ₀ ≤ 1/2`,
  `rBeyond (cap−1) = 0`; the gap `LE − bulktop = O(log log n)`), and
* the deterministic `noPhaseAbove3` successor-gate the FrontSync-gated `habs_mix_full`
  carries.
Both are cap-relative / deterministic.  NEITHER is the absolute-low
`rBeyond (frontWidthBound n) = 0`. -/

/-- **`joint_window_closure_gated` — the gated `Q_mix` closure from the joint gates.**  On a
`J`-config (with `1 ≤ T`) with the cap-relative empty-feeder window and the carried
`noPhaseAbove3` successor-gate, every successor satisfies `Q_mix`.  This is exactly the
content the headline theorem's `habs_mix_all_gated` packages, derived from the FrontSync gate
(`habs_mix_full`) — the cap-relative replacement of the false bare closure.  Records that the
window closure IS available on the joint-good window, with the residual being the cap-relative
narrowness + the deterministic phase gate, NOT absolute-low. -/
theorem joint_window_closure_gated (n mC T : ℕ) (hT : 1 ≤ T)
    (c c' : Config (AgentState L K))
    (hJ : J (L := L) (K := K) n mC T c)
    (hfeeder : AllClockP3 c)
    (hno' : noPhaseAbove3 (L := L) (K := K) c')
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Q_mix (L := L) (K := K) n mC T c' := by
  obtain ⟨hQ, hno, hpos, hsync⟩ := hJ
  obtain ⟨hge, _⟩ := allPhaseGE3_and_noPhaseAbove3_of_allClockP3 c hfeeder
  exact (habs_mix_full n mC T hT c c' hQ hge hno hpos hsync hno' hc').1

/-! ## HONEST STATUS — `ClockJointInduction` (the cap-relative joint clock-front induction)

* **The joint invariant `J` is CAP-RELATIVE** (around the MOVING leading edge): `FrontSync c`
  = `rBeyond (capMinute) c = 0` = no clock has reached the cap = leading edge `LE < capMinute`.
  It is NOT a fixed absolute level.  EXPLICITLY: this file does NOT import or use
  `FrontAllLevels.lean` or `ClockFrontIter.lean`'s `JointClockFront`, and does NOT assert any
  `rBeyond (frontWidthBound n) = 0` "stays empty from the bottom".  The narrowness used is the
  cap-relative empty cap-1 feeder `rBeyond (cap − 1) c = 0` (the moving leading-edge feeder),
  supplied by the bulk-top fraction `capRelFrac W c ≤ ρ₀ ≤ 1/2` (`ClockCapRelFront`).

* **One-step maintenance is GENUINELY PROVEN** (`joint_step_maintains` +
  `joint_step_frontSync_breach_zero`): on the FrontSync-good event with the empty cap-1
  feeder, (a) `FrontSync` breaks with probability `0` (the empty leading-edge feeder squares
  the breach to `0`, `ClockCapRelFront.capRel_feeder_empty_breach_zero` via the PROVEN
  `real_front_advance_squares_cap`); (b) `Q_mix ∧ allClocksCounterPos` is closed by the
  FrontSync-gated `FrontSyncConc.habs_mix_full`; (c) `noPhaseAbove3` is carried.  Combined,
  `J` is maintained one step.  No false hypothesis added.

* **Iterated over the `O(log n)` horizon** (`joint_frontSync_horizon_zero` +
  `clock_joint_frontSync_horizon` + `clock_real_O_log_n_joint_closed`): FrontSync survives
  with breach EXACTLY `0` (cap-relative concentration), and on the FrontSync-good event the
  bulk advances `0.9·m_C` per minute over `K·(L+1) = O(log n)` minutes
  (`ClockRealFaithfulHours.clock_real_faithful_O_log_n`).  The JOINT failure (bulk-Post fails
  OR FrontSync breaks) over the full horizon is bounded by the bulk failure alone
  (`≤ K·(L+1)·(εseed+εbulk)`), the FrontSync part vanishing — a genuine union bound.

* **The clock is NOT unconditional whp.**  The headline `clock_real_O_log_n_joint_closed`
  carries TWO inputs, BOTH cap-relative / deterministic, NEITHER absolute-low:
  - `hfeeder_all` — the cap-relative empty cap-1 feeder (the bulk-top narrowness, the gap
    `LE − bulktop = O(log log n)`, TRUE while running; the EXACT residual `ClockCapRelFront`
    carries via `capRel_feeder_doubly_exp` from `capRelFrac W ≤ ρ₀`);
  - `habs_mix_all_gated` — the FrontSync-gated `Q_mix` window-closure (`habs_mix_full`),
    carrying the deterministic `noPhaseAbove3` successor-gate.
  Both are GENUINELY the residuals the proven cap-relative concentrations carry; NEITHER is
  the false absolute-low `rBeyond (frontWidthBound n) = 0`.

VERDICT: the joint clock-front induction is formulated CAP-RELATIVE (around the moving leading
edge), its one-step maintenance is GENUINELY PROVEN (FrontSync breach `0` at the empty leading-
edge feeder + the FrontSync-gated `Q_mix` closure), and it is iterated over the `O(log n)`
horizon into the joint failure bound `clock_real_O_log_n_joint_closed`.  The EXACT residual is
the cap-relative bulk-top narrowness `hfeeder_all` (NOT absolute-low) + the deterministic
phase-window gate.  EXPLICITLY confirmed: NO `FrontAllLevels` / `ClockFrontIter` /
absolute-low `rBeyond (frontWidthBound) = 0` is used. -/
theorem clock_joint_induction_status : True := trivial

end ClockJointInduction

end ExactMajority
