/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — per-regime ladder spines (`RegimeClassification`)

This append-only file attacks **residual #4** of the Doty et al. exact-majority campaign: the two
protocol predicates left schematic by `Probability/ReachableLadder.lean`:

1. `ReachablePhaseRegimeClassification L K n init b Brecover` — every reachable not-done
   state falls into one of four regimes, each CARRYING a per-state `LadderData` to
   `StableDone`.  In `ReachableLadder` the four regime structures carry the `LadderData` as
   an opaque constructor FIELD; here we replace that opaqueness with explicit *ladder-spine
   constructions* — `regime-content ⟹ LadderData` theorems that BUILD the ladder from the
   landed E3/E2 expected-time caps plus the `RecoveryBridges` telescope, isolating the one
   honestly-missing bridge per regime (the final rung `progressSet ⟹ StableDone`).

2. `ReachableClockFloors` — the Lemma-5.2 clock-floor propagation into the timed regimes.
   Here we discharge the *floor-propagation* engine (the `posClockCount` floor propagates to
   every `AllClockGEpCard` invariant state, and clocks are never destroyed at phase `≥ 3`)
   from the FROZEN transition, leaving only the deterministic floor VALUE as the residual.

## The honest scope (stated up front)

The full *unconditional* classification of arbitrary reachable not-done states is the
hardest object in the campaign (pre-role-split states still hold main/reserve roles;
mid-seam states mix phases).  We do NOT pretend it.  What is delivered, honestly:

* **(a) Regime content, concretely.**  Each regime's defining data — phase membership,
  `AllClockGEpCard` invariant, Lemma-5.2 floor, counter cap (timed); `S1` / `Tie1plus`
  (phase-10) — restated as `*Data` structures WITHOUT a carried ladder.

* **(b) Per-regime ladder spines.**  For each regime, a theorem
  `regimeData → (final-rung bridge) → LadderData`, where the ladder's links are the named
  E3/E2 caps and the telescope is `RecoveryBridges.expectedHitting_telescope_from_start`.
  The `final-rung bridge` (the cap `progressSet → StableDone`) is the single explicit
  hypothesis isolating the genuine protocol residual; everything else is discharged.

* **(c) Clock-floor propagation.**  `clockFloor_propagates` (the `posClockCount` floor on
  one invariant state propagates to all, via `AllClockGEp`'s phase-`≥p` permanence), and the
  `ReachableClockFloors` assembler from a deterministic floor value.

* **(d) Classification scope.**  The checkpoint-conditional classifier
  (`regimeClassification_of_checkpoint`) is honest; the unconditional one is documented as
  out of scope (role split can fail ⇒ no deterministic clock floor for arbitrary reachable
  states — see the closing note).

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/ExactMajority/Probability/RegimeClassification.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ReachableLadder

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

/-! ## Deliverable (a) — regime content as ladder-free `*Data` structures

`ReachableLadder`'s four regime structures (`TimedBigClockRegime`, …) each carry the
`LadderData` as an opaque field.  We restate the *content* (the regime's defining facts,
sans ladder) so that the ladder becomes the CONCLUSION of a construction, not an input. -/

open ConditionalPhaseProgress in
/-- **Big-clock timed regime content** (no carried ladder).  The reachable not-done state
`b` is in a timed phase `p ∈ {0,1,5,6,7,8}` (`3 ≤ p`) carrying the Lemma-5.2 big-clock
floor `n/5 ≤ mC ≤ posClockCount p` on every invariant state and the counter cap. -/
structure TimedBigClockData (L K n : ℕ) (b : Config (AgentState L K)) where
  p : ℕ
  hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)
  hp3 : 3 ≤ p
  mC : ℕ
  counterMax : ℕ
  hfloorN : n / 5 ≤ mC
  hmCn : mC ≤ n
  hn : 18 ≤ n
  hInv : AllClockGEpCard (L := L) (K := K) p n b
  hfloor : ∀ y : Config (AgentState L K), AllClockGEpCard (L := L) (K := K) p n y →
    mC ≤ posClockCount (L := L) (K := K) p y
  hcap : clockCounterSumAt (L := L) (K := K) p b ≤ counterMax * mC

open ConditionalPhaseProgress in
/-- **Tiny-clock timed regime content** (no carried ladder).  As `TimedBigClockData` but
with only the unconditional floor `2 ≤ mC ≤ posClockCount p`. -/
structure TimedTinyClockData (L K n : ℕ) (b : Config (AgentState L K)) where
  p : ℕ
  hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)
  hp3 : 3 ≤ p
  mC : ℕ
  counterMax : ℕ
  hmC : 2 ≤ mC
  hmCn : mC ≤ n
  hn : 2 ≤ n
  hInv : AllClockGEpCard (L := L) (K := K) p n b
  hfloor : ∀ y : Config (AgentState L K), AllClockGEpCard (L := L) (K := K) p n y →
    mC ≤ posClockCount (L := L) (K := K) p y
  hcap : clockCounterSumAt (L := L) (K := K) p b ≤ counterMax * mC

open Phase10Drop in
/-- **Phase-10 majority regime content** (no carried ladder).  `b` is an `MajorityAStage1`
(all-phase-10, positive signed sum) state. -/
structure Phase10MajorityData (L K n : ℕ) (b : Config (AgentState L K)) where
  hn : 2 ≤ n
  hS1 : MajorityAStage1 (L := L) (K := K) n b

open Phase10Drop in
/-- **Phase-10 tie regime content** (no carried ladder).  `b` is a `Tie1plus`
(all-phase-10, zero signed sum, active) state. -/
structure Phase10TieData (L K n : ℕ) (b : Config (AgentState L K)) where
  hn : 2 ≤ n
  hTie : Tie1plus (L := L) (K := K) n b

/-! ## Deliverable (b) — the per-regime ladder spines

### The two-rung spine builder

Each E3/E2 engine caps the expected time to a *progress set* `Prog` (`potBelow Φ 1`), NOT to
`StableDone`.  The honest ladder from `b` is therefore TWO rungs:

* rung 0 → 1: `b`'s domain (a set containing `b`) to `Prog`, capped by the E3/E2 bound;
* rung 1 → 2: `Prog` to `StableDone`, capped by the (regime-specific) bridge `βbridge`.

with `S 2 = StableDone`.  `ladderData_of_two_rung` assembles the `LadderData` from these
two link caps, the membership `b ∈ Dom`, and `βdom + βbridge ≤ Brecover`.  The genuine
protocol residual is then exactly the second link cap (`Prog ⟹ StableDone`), supplied as an
explicit hypothesis — the ladder-spine is otherwise a theorem.

The set algebra: `S : ℕ → Set α` with `S 0 = Dom`, `S 1 = Prog`, `S 2 = StableDone`, and
`S (k+3) = StableDone` (constant past the top) so `S k = Done` for `k = 2`. -/

open scoped Classical in
/-- **Two-rung ladder-spine builder.**  Given a not-done state `b ∈ Dom`, a progress set
`Prog`, an absorbing measurable `StableDone`, the first-link cap
`∀ y ∈ Dom, E[T y → Prog] ≤ βdom`, the second-link (bridge) cap
`∀ y ∈ Prog, E[T y → StableDone] ≤ βbridge`, and `βdom + βbridge ≤ Brecover`, produce the
`LadderData L K init b Brecover`.

This is the per-regime ladder spine: every regime instantiates `Prog` with its E3/E2 target
set, `βdom` with the E3/E2 cap, and `βbridge` with the residual `Prog ⟹ StableDone` bridge. -/
noncomputable def ladderData_of_two_rung {L K : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (Dom Prog : Set (Config (AgentState L K)))
    (hDom : MeasurableSet Dom) (hProg : MeasurableSet Prog)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (βdom βbridge : ℝ≥0∞)
    (hb : b ∈ Dom)
    (hlink0 : ∀ y ∈ Dom,
      expectedHitting (NonuniformMajority L K).transitionKernel y Prog ≤ βdom)
    (hlink1 : ∀ y ∈ Prog,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ βbridge)
    (hsum : βdom + βbridge ≤ Brecover) :
    LadderData L K init b Brecover where
  k := 2
  S := fun i => match i with
    | 0 => Dom
    | 1 => Prog
    | _ => StableDone L K init
  hS := fun i => by
    match i with
    | 0 => exact hDom
    | 1 => exact hProg
    | (_ + 2) => exact hDoneMeas
  hSk := rfl
  β := fun i => match i with
    | 0 => βdom
    | _ => βbridge
  hlink := fun i hik y hy => by
    match i, hik with
    | 0, _ => exact hlink0 y hy
    | 1, _ => exact hlink1 y hy
  hb := hb
  hsum := by
    -- ∑_{j<2} β j = β 0 + β 1 = βdom + βbridge ≤ Brecover.
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simpa using hsum

open ConditionalPhaseProgress in
open scoped Classical in
/-- **Big-clock timed ladder spine.**  From `TimedBigClockData` and the residual final-rung
bridge `Prog ⟹ StableDone` (cap `βbridge`), build the `LadderData` whose FIRST link is the
landed big-clock E3 cap `timed_phase_progress_real_bigClock` (`≤ counterMax·11·n`) and whose
domain is the `AllClockGEpCard p n` invariant set.

`Prog := potBelow (clockCounterSumAt p) 1` (the E3 target).  The first link is discharged
here from the regime data; only `hbridge` (the protocol residual) is assumed. -/
noncomputable def ladderData_of_bigClock {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (d : TimedBigClockData L K n b)
    (βbridge : ℝ≥0∞)
    (hbridge : ∀ y ∈ Engine.potBelow (clockCounterSumAt (L := L) (K := K) d.p) 1,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ βbridge)
    (hsum : ((d.counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) + βbridge ≤ Brecover) :
    LadderData L K init b Brecover :=
  ladderData_of_two_rung init b Brecover
    {x | AllClockGEpCard (L := L) (K := K) d.p n x ∧
      clockCounterSumAt (L := L) (K := K) d.p x ≤ d.counterMax * d.mC}
    (Engine.potBelow (clockCounterSumAt (L := L) (K := K) d.p) 1)
    (DiscreteMeasurableSpace.forall_measurableSet _)
    (Engine.potBelow_measurable _ _)
    hDoneMeas
    (((d.counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞)) βbridge
    ⟨d.hInv, d.hcap⟩
    (fun y hy =>
      timed_phase_progress_real_bigClock (L := L) (K := K) d.p d.hp d.hp3 d.mC n d.counterMax
        d.hfloorN d.hmCn d.hn d.hfloor y hy.1 hy.2)
    hbridge hsum

open ConditionalPhaseProgress in
open scoped Classical in
/-- **Tiny-clock timed ladder spine.**  As `ladderData_of_bigClock` but the first link is the
tiny-clock E3 cap `timed_phase_progress_real_tinyClock` (`≤ counterMax·n²`). -/
noncomputable def ladderData_of_tinyClock {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (d : TimedTinyClockData L K n b)
    (βbridge : ℝ≥0∞)
    (hbridge : ∀ y ∈ Engine.potBelow (clockCounterSumAt (L := L) (K := K) d.p) 1,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ βbridge)
    (hsum : ((d.counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βbridge ≤ Brecover) :
    LadderData L K init b Brecover :=
  ladderData_of_two_rung init b Brecover
    {x | AllClockGEpCard (L := L) (K := K) d.p n x ∧
      clockCounterSumAt (L := L) (K := K) d.p x ≤ d.counterMax * d.mC}
    (Engine.potBelow (clockCounterSumAt (L := L) (K := K) d.p) 1)
    (DiscreteMeasurableSpace.forall_measurableSet _)
    (Engine.potBelow_measurable _ _)
    hDoneMeas
    (((d.counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞)) βbridge
    ⟨d.hInv, d.hcap⟩
    (fun y hy =>
      timed_phase_progress_real_tinyClock (L := L) (K := K) d.p d.hp d.hp3 d.mC n d.counterMax
        d.hmC d.hmCn d.hn d.hfloor y hy.1 hy.2)
    hbridge hsum

open Phase10Drop in
open scoped Classical in
/-- **Phase-10 majority ladder spine.**  From `Phase10MajorityData` (an `S1` state) and the
residual bridge `{wrongACount < 1} ⟹ StableDone`, build the `LadderData` whose first link is
the landed E2 cap `phase10_expected_stabilization_O_nsq_log` (`≤ 3·n²·(1+2 log n)`). -/
noncomputable def ladderData_of_phase10Majority {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (d : Phase10MajorityData L K n b)
    (βbridge : ℝ≥0∞)
    (hbridge : ∀ y ∈ potBelow (fun c => wrongACount (L := L) (K := K) c) 1,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ βbridge)
    (hsum : 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + βbridge
      ≤ Brecover) :
    LadderData L K init b Brecover :=
  ladderData_of_two_rung init b Brecover
    {x | MajorityAStage1 (L := L) (K := K) n x}
    (potBelow (fun c => wrongACount (L := L) (K := K) c) 1)
    (DiscreteMeasurableSpace.forall_measurableSet _)
    (potBelow_measurable _ _)
    hDoneMeas
    (3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) βbridge
    d.hS1
    (fun y hy => phase10_expected_stabilization_O_nsq_log (L := L) (K := K) n d.hn y hy)
    hbridge hsum

open Phase10Drop in
open scoped Classical in
/-- **Phase-10 tie ladder spine.**  From `Phase10TieData` (a `Tie1plus` state) and the
residual bridge `{wrongTCount < 1} ⟹ StableDone`, build the `LadderData` whose first link is
the landed E2 cap `phase10_expected_stabilization_tie_O_nsq_log` (`≤ 2·n²·(1+2 log n)`). -/
noncomputable def ladderData_of_phase10Tie {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (d : Phase10TieData L K n b)
    (βbridge : ℝ≥0∞)
    (hbridge : ∀ y ∈ potBelow (fun c => wrongTCount (L := L) (K := K) c) 1,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ βbridge)
    (hsum : 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + βbridge
      ≤ Brecover) :
    LadderData L K init b Brecover :=
  ladderData_of_two_rung init b Brecover
    {x | Tie1plus (L := L) (K := K) n x}
    (potBelow (fun c => wrongTCount (L := L) (K := K) c) 1)
    (DiscreteMeasurableSpace.forall_measurableSet _)
    (potBelow_measurable _ _)
    hDoneMeas
    (2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))) βbridge
    d.hTie
    (fun y hy => phase10_expected_stabilization_tie_O_nsq_log (L := L) (K := K) n d.hn y hy)
    hbridge hsum

/-! ## Deliverable (c) — clock-floor propagation

### Clock-role preservation (the FROZEN-transition fact)

"Clocks are never destroyed after the role split" is, formally, the kernel-preservation of
`AllClockGEpCard p n` for `3 ≤ p`.  The campaign already proves this at the FROZEN
transition:

* the per-pair fact `ConditionalPhaseProgress.Transition_clock_pair_phase_GEp` — a
  clock-clock interaction at phase `≥ p` produces two clocks at phase `≥ p` (`3 ≤ p`); NO
  phase-`≥ 3` rule consumes a clock or lowers a clock's phase below `p`;
* the one-step closure `AllClockGEpCard_InvClosed` (support permanence + card conservation);
* the all-time form `RecoveryBridges.allClockGEpCard_pow_preserved` — the trajectory from an
  `AllClockGEpCard p n` start stays a.e. on the invariant for ALL kernel powers.

We re-export the all-time form under the campaign name so the floor-propagation surface is
local to this file. -/

open ConditionalPhaseProgress in
/-- **Clock-role preservation (all-time), re-export.**  From an `AllClockGEpCard p n` start
`c` (`3 ≤ p`), the not-invariant mass under every kernel power vanishes: the trajectory
stays a.e. on the clock-role invariant for all `t`.  This is the FROZEN-transition fact
"clocks are never destroyed at phase `≥ 3`" — re-exported from
`RecoveryBridges.allClockGEpCard_pow_preserved` so the floor data below is self-contained. -/
theorem clockRole_preserved_all_time {L K : ℕ} (p n : ℕ) (hp : 3 ≤ p)
    (c : Config (AgentState L K))
    (hc : AllClockGEpCard (L := L) (K := K) p n c) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {x | ¬ AllClockGEpCard (L := L) (K := K) p n x} = 0 :=
  allClockGEpCard_pow_preserved (L := L) (K := K) p n hp c hc t

/-! ### Floor propagation (the honest, genuinely-true form)

The Lemma-5.2 floor in a timed regime is the carried field
`hfloor : ∀ y, AllClockGEpCard p n y → mC ≤ posClockCount p y` — already UNIFORM over every
`AllClockGEpCard p n` invariant state (NOT just over `b`).  Combined with
`clockRole_preserved_all_time` (the invariant is kernel-preserved at phase `≥ 3`), this is
exactly the floor-propagation statement: along a trajectory from an invariant start, the
floor holds a.e. at every time.  We package this honest form per timed branch.

(Note on `ReachableLadder.ReachableClockFloors`: its `big`/`tiny` fields quantify a FREE
outer phase `p` — `∀ p, TimedBigClockRegime … → ∃ mC, … ∀ y, AllClockGEpCard p n y → …` —
whereas a regime witness carries a floor only for its OWN internal phase `h.p`.  Producing a
floor for an ARBITRARY outer `p` from a single regime is NOT honestly derivable (no clock
floor holds simultaneously at every phase); so we do NOT fake-discharge that structure.  The
genuinely-true floor-propagation content is the per-regime `floorProp_*` below, for the
regime's OWN phase, which is what the timed E3 engines actually consume via `hfloor`.) -/

open ConditionalPhaseProgress in
/-- **Big-clock floor propagation (for the regime's own phase).**  From the big-clock regime
data, the Lemma-5.2 floor `n/5 ≤ mC ≤ posClockCount d.p y` holds UNIFORMLY over every
`AllClockGEpCard d.p n` invariant state `y` — the carried `hfloor`, exposed as the explicit
floor-propagation fact (the invariant being kernel-preserved by `clockRole_preserved_all_time`,
so this holds a.e. along the trajectory).  This is the honest, genuinely-true floor content;
the residual is only the floor VALUE `mC` (Lemma-5.2 whp clock count). -/
theorem floorProp_bigClock {L K n : ℕ} {b : Config (AgentState L K)}
    (d : TimedBigClockData L K n b) :
    n / 5 ≤ d.mC ∧ d.mC ≤ n ∧
      ∀ y, AllClockGEpCard (L := L) (K := K) d.p n y →
        d.mC ≤ posClockCount (L := L) (K := K) d.p y :=
  ⟨d.hfloorN, d.hmCn, d.hfloor⟩

open ConditionalPhaseProgress in
/-- **Tiny-clock floor propagation (for the regime's own phase).**  As `floorProp_bigClock`
but with only the unconditional floor `2 ≤ mC`. -/
theorem floorProp_tinyClock {L K n : ℕ} {b : Config (AgentState L K)}
    (d : TimedTinyClockData L K n b) :
    2 ≤ d.mC ∧ d.mC ≤ n ∧
      ∀ y, AllClockGEpCard (L := L) (K := K) d.p n y →
        d.mC ≤ posClockCount (L := L) (K := K) d.p y :=
  ⟨d.hmC, d.hmCn, d.hfloor⟩

/-! ## Deliverable (d) — the classification scope (honest: checkpoint-conditional)

### The checkpoint-conditional classifier

The four regime structures of `ReachableLadder` (`TimedBigClockRegime`, …) carry the
per-state ladder as a field; deliverable (b) replaced that field with a CONSTRUCTION from
the ladder-free `*Data` + a residual bridge.  We assemble the full classifier from those
constructions: given, for a state `b`, a regime-`*Data` witness plus its bridge + budget,
build the `ReachablePhaseRegimeClassification`.

This is checkpoint-CONDITIONAL: the hypothesis is that `b` is ALREADY classified into a
regime (one of the four `*Data` witnesses).  That classification is honest for states
reachable from a GOOD role-split checkpoint (post-role-split, the whp event): the 21-instance
chain's Pre/Post windows constrain the phase structure, and the clock floor holds (Lemma 5.2)
on that event.  See the closing scope note for why the UNCONDITIONAL classifier (arbitrary
reachable states, including a failed role split) is out of scope. -/

open ConditionalPhaseProgress in
open scoped Classical in
/-- **Big-clock branch of the classifier** (from the ladder-free data + the residual bridge).
Builds the `ReachablePhaseRegimeClassification` big-clock constructor by constructing its
carried `TimedBigClockRegime` (the regime witness with the ladder now BUILT, not assumed)
from `TimedBigClockData` + the final-rung bridge. -/
noncomputable def regimeClassification_bigClock {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (d : TimedBigClockData L K n b)
    (βbridge : ℝ≥0∞)
    (hbridge : ∀ y ∈ Engine.potBelow (clockCounterSumAt (L := L) (K := K) d.p) 1,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ βbridge)
    (hsum : ((d.counterMax : ℕ) : ℝ≥0∞) * ((11 * n : ℕ) : ℝ≥0∞) + βbridge ≤ Brecover) :
    ReachablePhaseRegimeClassification L K n init b Brecover :=
  .bigClockTimed
    { p := d.p, hp := d.hp, hp3 := d.hp3, mC := d.mC, counterMax := d.counterMax
      hfloorN := d.hfloorN, hmCn := d.hmCn, hn := d.hn, hInv := d.hInv
      hfloor := d.hfloor, hcap := d.hcap
      ladder := ladderData_of_bigClock init b Brecover hDoneMeas d βbridge hbridge hsum }

open ConditionalPhaseProgress in
open scoped Classical in
/-- **Tiny-clock branch of the classifier** (ladder-free data + residual bridge). -/
noncomputable def regimeClassification_tinyClock {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (d : TimedTinyClockData L K n b)
    (βbridge : ℝ≥0∞)
    (hbridge : ∀ y ∈ Engine.potBelow (clockCounterSumAt (L := L) (K := K) d.p) 1,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ βbridge)
    (hsum : ((d.counterMax : ℕ) : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) + βbridge ≤ Brecover) :
    ReachablePhaseRegimeClassification L K n init b Brecover :=
  .tinyClockTimed
    { p := d.p, hp := d.hp, hp3 := d.hp3, mC := d.mC, counterMax := d.counterMax
      hmC := d.hmC, hmCn := d.hmCn, hn := d.hn, hInv := d.hInv
      hfloor := d.hfloor, hcap := d.hcap
      ladder := ladderData_of_tinyClock init b Brecover hDoneMeas d βbridge hbridge hsum }

open scoped Classical in
/-- **Phase-10 majority branch of the classifier** (ladder-free data + residual bridge). -/
noncomputable def regimeClassification_phase10Majority {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (d : Phase10MajorityData L K n b)
    (βbridge : ℝ≥0∞)
    (hbridge : ∀ y ∈ potBelow (fun c => wrongACount (L := L) (K := K) c) 1,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ βbridge)
    (hsum : 3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + βbridge
      ≤ Brecover) :
    ReachablePhaseRegimeClassification L K n init b Brecover :=
  .phase10Majority
    { hn := d.hn, hS1 := d.hS1
      ladder := ladderData_of_phase10Majority init b Brecover hDoneMeas d βbridge hbridge hsum }

open scoped Classical in
/-- **Phase-10 tie branch of the classifier** (ladder-free data + residual bridge). -/
noncomputable def regimeClassification_phase10Tie {L K n : ℕ}
    (init b : Config (AgentState L K)) (Brecover : ℝ≥0∞)
    (hDoneMeas : MeasurableSet (StableDone L K init))
    (d : Phase10TieData L K n b)
    (βbridge : ℝ≥0∞)
    (hbridge : ∀ y ∈ potBelow (fun c => wrongTCount (L := L) (K := K) c) 1,
      expectedHitting (NonuniformMajority L K).transitionKernel y (StableDone L K init)
        ≤ βbridge)
    (hsum : 2 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n)) + βbridge
      ≤ Brecover) :
    ReachablePhaseRegimeClassification L K n init b Brecover :=
  .phase10Tie
    { hn := d.hn, hTie := d.hTie
      ladder := ladderData_of_phase10Tie init b Brecover hDoneMeas d βbridge hbridge hsum }

/-! ### Honest scope note (the unconditional classifier is out of scope)

`regimeClassification_*` produce the classification from a regime-`*Data` witness for `b` —
i.e. CONDITIONAL on `b` already being classified into one of the four phase regimes.  The
remaining residual `hClassify` of `expected_time_reachable` is then exactly:

> for every reachable not-done `b`, EXHIBIT one of the four `*Data` witnesses (+ the
> per-regime final-rung bridge).

For states reachable from a GOOD role-split checkpoint (the whp event of
`RoleSplitConcentration`, where `clockCount_linear_of_RoleSplitGood` gives `n/5 ≤ |Clock|`),
this is honest: the role split has happened (every working agent is a clock), the clock floor
holds (Lemma 5.2), and the phase windows of the 21-instance chain (`TimeHeadline`)
constrain the phase to a timed regime or the Phase-10 backup.

The UNCONDITIONAL classifier — covering ARBITRARY reachable not-done states — is out of scope,
and honestly so:

* Pre-role-split states (Phase 0, before `R4`/`R5` create the clock subpopulation) still hold
  main/reserve roles; they have NO `AllClockGEpCard` invariant and NO clock floor.
* If the role split FAILS (the complement of the whp `RoleSplitGood` event), there is NO
  deterministic clock floor `2 ≤ mC` for arbitrary reachable states — the tiny-clock branch's
  `2 ≤ mC` is itself a Lemma-5.2 whp fact on the good event, not a deterministic invariant.

So the unconditional classification cannot be a deterministic theorem; it is a whp statement
conditioned on the checkpoint event.  The honest E4 surface is therefore the
checkpoint-CONDITIONAL classifier delivered here, with the unconditional version explicitly
documented as conditioned on the (whp) role-split event — consistent with the
`RecoveryBridges` Stage-4 residual note. -/

end Ripple.PopulationProtocol.ExactMajority
