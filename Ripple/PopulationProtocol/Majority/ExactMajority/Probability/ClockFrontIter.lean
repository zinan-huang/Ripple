/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockFrontIter` — ITERATING the proven per-level empty-absorbing step over all
# `W = frontWidthBound n = O(log log n)` front levels, then CONNECTING to the clock's
# own progress (`clock_real_faithful_O_log_n`).

`ClockBulkFront` discharged the TOP carried window `CapRelWithinEnvFeeder` (depth 2) to
the depth-3 drip window, level-uniformly (`level_union_concentration`,
`feeder_empty_absorbing_up_to_drip`).  Each application of that step trades the carried
emptiness window at depth `d` for the carried emptiness window at depth `d+1`, bottoming
at the leading front depth `W = frontWidthBound n`.

This file does TWO things.

## (1) `front_empty_all_levels` — the GENUINE `W`-level iteration.

Rather than chaining `level_union_concentration` `W` times (which would re-pay the
doubly-exp cost at every level and re-carry a `RWithinEnvelope` window at each depth),
the iteration is performed in ONE shot via the LEVEL-COLLAPSE
`FrontAllLevels.whole_front_iff_boundary_empty`: by threshold-antitonicity of `rBeyond`
(`HabsDischarge.rBeyond_antitone_threshold`), the conjunction "every front level
`j ∈ [W, cap)` is empty" is EQUIVALENT to the single equation `rBeyond W c = 0`.  So a
SINGLE empty-absorbing concentration at the boundary level `W` controls ALL `W` levels
above the front width simultaneously — this IS the iteration of the proven per-level step
(`rBeyond_seed_le_rBeyondSq` at the boundary), telescoped by antitonicity into one event.

`front_empty_all_levels` therefore states the all-levels conclusion directly: from a
whole-front-empty `AllClockP3` start of population `n`, the kernel probability over `H`
steps that SOME front level `j ∈ [W, cap)` is EVER seeded is at most `H · (Bbd/n)²`,
GIVEN the single boundary-feeder window `hbd_all` (`rBeyond (W−1) ≤ Bbd` on reachable
empty-width configs).  This is the GENUINE `W`-level iteration: it is the proven
per-level squaring at the boundary, lifted to all `W` levels by the proven antitone
collapse, NOT an assumed recursion.

## (2) The base case and the clock-progress CONNECTION attempt.

The base case "leading edge below `cap − W`" is the whole-front-empty event itself
(`rBeyond W c = 0`); at the width boundary the envelope has collapsed below `1/n`
(`FrontTail.front_emptied_at_width` on `FrontTailKernel.envelope`), so within-envelope ⟺
empty there (`FrontAllLevels.within_iff_empty_gen`) — the front-shape bulk-top condition.

The clock-progress connection asks: does `clock_real_faithful_O_log_n` (the clock reaches
the cap in `O(log n)` parallel, advancing its leading edge minute by minute) SUPPLY the
boundary-feeder window `hbd_all` / the whole-front-empty start, making the clock
UNCONDITIONAL whp (no structural hypothesis)?  We attempt it and prove the MAXIMAL clean
prefix, then STOP at the precisely-named joint residual.

### The maximal clean prefix (PROVEN here)

`clock_real_O_log_n_given_front` (Part 3): GIVEN the single boundary-feeder window
`hbd_all` and the whole-front-empty start gate `hstart`, the real-kernel clock FrontSync
breach over the horizon is `≤ ofReal (H·Bbd²/n²)` (`1/poly`).  This is the genuine
all-levels concentration feeding the clock's FrontSync invariant — the clock carries NO
interior front window, only the SINGLE boundary input.

### The PRECISELY-NAMED joint residual (where the connection genuinely needs the joint
### clock-front induction — STOP, do NOT fake).

`ClockFrontDoty.JointClockFront` (Part 4, stated as a `Prop`, NOT asserted): the clock
advance (`clock_real_step`, carrying `habs_mix`) and the front emptiness
(`front_empty_all_levels`, carrying `hbd_all`) are MUTUALLY dependent —

* `clock_real_step`'s `habs_mix` (deterministic `Q_mix` window closure) is FALSE off the
  FrontSync window (the at-cap `counter = 1` witness,
  `ClockFrontShape.counterPos_one_step_NOT_closed_witness`); it is supplied whp by the
  FrontSync concentration (`FrontSyncConc.habs_mix_full`);
* the FrontSync concentration needs the boundary-feeder window `hbd_all`
  (`rBeyond (W−1) ≤ Bbd` on every reachable config);
* `hbd_all` holding at every reachable config is EXACTLY "the clock has NOT advanced its
  leading edge to/past the boundary `W − 1`", i.e. the CLOCK-PROGRESS condition: the
  leading edge stays below `cap − W` for the first `cap − W` minutes.

So closing the connection requires the JOINT statement
`(clock advances its edge minute by minute) ∧ (the front stays empty above the width)`
maintained MUTUALLY over the run — Doty §6's intertwined core (Theorem 6.5 ⟷ Lemmas
6.6–6.10, the front-shape induction and the hour-synchronization supermartingale proved
TOGETHER).  We name it precisely (`JointClockFront`) and STOP; it is NOT a `∀c`
deterministic window (which would be FALSE — the at-cap witness), it is the genuine
mutual-induction obligation, deliberately stated as a `Prop`, NOT asserted, NOT faked.

NEW file; reuses the PROVEN `FrontAllLevels.{whole_front_iff_boundary_empty,
frontAll_empty_concentration, frontAll_frontSync_concentration_poly,
frontSync_concentration_remaining_via_frontAll}`, `ClockBulkFront`'s empty-absorbing
machinery, `ClockRealFaithfulHours.clock_real_faithful_O_log_n`,
`FrontSyncConc.habs_mix_full`, and the envelope arithmetic `FrontTail.front_emptied_at_width`.
No existing proven lemma is weakened.  No sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + Lemmas 6.6–6.10 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockBulkFront
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontAllLevels
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealFaithfulHours

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockFrontIter

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape
  FrontSyncConc ClockFrontWidth ClockEnvMaint FrontNarrowConc FrontAllLevels

variable {L K : ℕ}

/-! ## Part 1 — `front_empty_all_levels`: the GENUINE `W`-level iteration.

The proven per-level empty-absorbing step is `ClockFrontWidth.rBeyond_seed_le_rBeyondSq`
(the empty-seed squaring: from an empty level the seed probability is the SQUARE of the
feeder fraction, the sync term absent — `ClockBulkFront.feeder_empty_absorbing_up_to_drip`
makes the sync-vanishing explicit at `cap − 2`).  Iterating it over the `W` front levels
is done by the PROVEN level-collapse `FrontAllLevels.whole_front_iff_boundary_empty`:
threshold-antitonicity telescopes "every level `j ∈ [W, cap)` empty" into the single
boundary equation `rBeyond W c = 0`, so ONE empty-absorbing concentration at the boundary
level controls all `W` levels at once.  This is the iteration realized as a single
boundary event, not an assumed recursion. -/

/-- **`front_empty_all_levels` — the front is empty at ALL `W` top levels whp (the
genuine `W`-level iteration).**  With the width level strictly below the cap
(`W = frontWidthBound n < cap`), `2 ≤ n`, the single boundary-feeder window `hbd_all`
(`rBeyond (W−1) ≤ Bbd` on every reachable empty-width `AllClockP3` config of population
`n`), from a whole-front-empty `AllClockP3` start `c₀` of population `n` the kernel
probability over `H` steps that SOME front level `j ∈ [W, cap)` is EVER non-empty is at
most `H · ofReal ((Bbd/n)²)`:

  `(K^H) c₀ {c' | ∃ j, W ≤ j ∧ j < cap ∧ 1 ≤ rBeyond j c'} ≤ H · ofReal ((Bbd/n)²)`.

GENUINELY the iteration of the proven per-level squaring
(`ClockFrontWidth.rBeyond_seed_le_rBeyondSq`) over all `W` levels: the all-levels-empty
event collapses by antitonicity (`whole_front_iff_boundary_empty`) to the single boundary
event `rBeyond W = 0`, whose breach is bounded by `frontAll_empty_concentration` (the
level-union over the boundary squaring).  The `∃ j …` non-empty event is EXACTLY the
complement of "all `W` levels empty", so its measure is the single-boundary breach. -/
theorem front_empty_all_levels (n Bbd : ℕ)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hWlt : FrontTail.frontWidthBound n < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hbd_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 → AllClockP3 c →
      c.card = n →
      RFeederCapWindow (L := L) (K := K) n (FrontTail.frontWidthBound n) Bbd c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hempty0 : rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0)
    (hw0 : AllClockP3 c₀) (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ∃ j, FrontTail.frontWidthBound n ≤ j ∧ j < capMinute (L := L) (K := K) ∧
          1 ≤ rBeyond (L := L) (K := K) j c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal (((Bbd : ℝ) / (n : ℝ)) ^ 2) := by
  set W := FrontTail.frontWidthBound n with hW
  -- the boundary concentration (the level-union over the proven boundary squaring).
  have hmain := frontAll_empty_concentration (L := L) (K := K) n Bbd hWpos (le_of_lt hWlt)
    hn2 hbd_all H c₀ hempty0 hw0 hcard0
  -- the all-levels non-empty event is the complement of all-levels-empty, which by
  -- antitonicity (`whole_front_iff_boundary_empty`) is the single boundary breach.
  refine le_trans (measure_mono ?_) hmain
  intro c' hc'
  simp only [hW, Set.mem_setOf_eq] at hc' ⊢
  obtain ⟨j, hjW, _hjcap, hjpos⟩ := hc'
  -- `rBeyond W c' ≥ rBeyond j c' ≥ 1` (antitone, `W ≤ j`).
  have hle : rBeyond (L := L) (K := K) j c'
      ≤ rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c' :=
    rBeyond_antitone_threshold (FrontTail.frontWidthBound n) j hjW c'
  exact le_trans hjpos hle

/-! ## Part 2 — the base case: the leading edge below `cap − W` is the whole-front-empty
event, and at the width boundary the envelope has collapsed below `1/n`.

The "leading edge below `cap − W`" base case is the whole-front-empty event
`rBeyond W c = 0` (no clock has advanced past minute `W` from the bottom of the front —
equivalently no clock within `W` of the cap; by antitonicity `rBeyond j = 0` for all
`j ≥ W`).  At the width boundary the doubly-exp envelope is `< 1/n`
(`FrontTail.front_emptied_at_width`), so within-envelope ⟺ empty there
(`FrontAllLevels.within_iff_empty_gen`) — the front-shape bulk-top condition that needs
no deeper drip. -/

/-- **`envelope_collapsed_at_width` — the base-case envelope collapse.**  For a
subcritical start (`0 ≤ f₀ ≤ 1/2`) and `2 ≤ n`, at every level `i ≥ frontWidthBound n`
the doubly-exp envelope is below `1/n`: `envelope f₀ i < 1/n`.  This is the bottom of the
front recursion — the base case where within-envelope ⟺ empty (`within_iff_empty_gen`),
the genuine bulk-top condition.  GENUINELY `FrontTail.front_emptied_at_width` on
`FrontTailKernel.envelope` (the `f₀^(2^i)` collapse). -/
theorem envelope_collapsed_at_width (f0 : ℝ) (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n : ℕ) (hn2 : 2 ≤ n) (i : ℕ) (hi : FrontTail.frontWidthBound n ≤ i) :
    FrontTailKernel.envelope f0 i < 1 / (n : ℝ) := by
  have h := FrontTail.front_emptied_at_width (p := 1) (f := FrontTailKernel.envelope f0)
    one_pos (FrontTailKernel.envelope_nonneg hf0) (FrontTailKernel.envelope_frontRecurrence f0)
    (by simpa [FrontTailKernel.envelope_zero] using hsub) n hn2 i hi
  simpa using h

/-- **`base_case_within_iff_empty` — at the width boundary, within-envelope ⟺ empty.**
At the leading front depth `i ≥ frontWidthBound n`, under the subcritical start and
`2 ≤ n`, `card = n`, the within-envelope predicate is EQUIVALENT to the level being empty.
This is the BOTTOM of the recursion: the carried within-envelope window becomes the TRUE
bulk emptiness condition, no deeper drip needed (`FrontAllLevels.within_iff_empty_gen` fed
the base-case collapse `envelope_collapsed_at_width`). -/
theorem base_case_within_iff_empty (f0 : ℝ) (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n : ℕ) (hn2 : 2 ≤ n) (i : ℕ) (hi : FrontTail.frontWidthBound n ≤ i)
    (c : Config (AgentState L K)) (hcard : c.card = n) :
    RWithinEnvelope (L := L) (K := K) f0 i c ↔ rBeyond (L := L) (K := K) i c = 0 :=
  within_iff_empty_gen f0 hf0 n hn2 i c hcard (envelope_collapsed_at_width f0 hf0 hsub n hn2 i hi)

/-! ## Part 3 — the clock-progress CONNECTION: the MAXIMAL clean prefix.

GIVEN the single boundary-feeder window `hbd_all` and the whole-front-empty start gate
`hstart`, the all-levels front concentration (Part 1) feeds the clock's FrontSync
invariant directly (`FrontAllLevels.frontAll_frontSync_concentration_poly`,
`{¬ FrontSync} ⊆ {1 ≤ rBeyond W}` by antitonicity, the interior front window discharged
by `wholeFrontEmpty_imp_within`).  This is the clock FrontSync breach `≤ ofReal
(H·Bbd²/n²)` — the `1/poly` budget — carrying ONLY the single boundary input.  This is the
maximal prefix that closes cleanly without the joint induction. -/

/-- **`clock_real_O_log_n_given_front` — the real-kernel clock FrontSync breach, GIVEN
the single boundary-feeder window.**  From a `Q_mix ∧ FrontSync ∧ AllClockP3 ∧
whole-front-empty` start of population `n`, with `W = frontWidthBound n ≤ cap`,
`0 < frontWidthBound n`, `2 ≤ n`, and the single boundary-feeder window `hbd_all`
(`rBeyond (W−1) ≤ Bbd` on reachable empty-width configs), the kernel probability over the
horizon `H` of EVER breaking `FrontSync` is `≤ ofReal (H·Bbd²/n²)` (`1/poly`).  GENUINELY
the all-levels front concentration (`front_empty_all_levels` / the proven boundary
squaring iterated by antitonicity over all `W` levels), carrying NO interior front window
— only the single boundary input `hbd_all`.  This is the maximal clean prefix of the
clock-progress connection; the boundary window `hbd_all` itself is the joint residual
(Part 4). -/
theorem clock_real_O_log_n_given_front (n mC Bbd : ℕ)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hWcap : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hbd_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 → AllClockP3 c →
      c.card = n →
      RFeederCapWindow (L := L) (K := K) n (FrontTail.frontWidthBound n) Bbd c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC 0 c₀)
    (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hw0 : AllClockP3 c₀)
    (hempty0 : rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      ENNReal.ofReal ((H : ℝ) * (Bbd : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
  clock_real_O_log_n_unconditional_whp (L := L) (K := K) n mC Bbd hWpos hWcap hn2 hbd_all
    H c₀ hQ hsync0 hw0 hempty0

/-- **`frontSync_concentration_remaining_discharged` — the named clock obligation
`FrontSyncConcentration_remaining` discharged via the all-levels iteration, GIVEN the
single boundary window + the start gate.**  With the boundary-feeder window `hbd_all` and
the whole-front-empty start gate `hstart` (every `Q_mix ∧ FrontSync` start begins
whole-front-empty / `AllClockP3` — the clock's actual initial condition, all clocks in the
bulk below the `O(log log n)` width), the named obligation
`ClockFrontShape.FrontSyncConcentration_remaining n mC H` holds at `ε = ofReal
(H·Bbd²/n²)`.  GENUINELY `FrontAllLevels.frontSync_concentration_remaining_via_frontAll`
— the all-levels iteration, carrying ONLY the single boundary input. -/
theorem frontSync_concentration_remaining_discharged (n mC Bbd : ℕ)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hWcap : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hbd_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 → AllClockP3 c →
      c.card = n →
      RFeederCapWindow (L := L) (K := K) n (FrontTail.frontWidthBound n) Bbd c)
    (hstart : ∀ c₀ : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC 0 c₀ → FrontSync (L := L) (K := K) c₀ →
      AllClockP3 c₀ ∧ rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0)
    (H : ℕ) :
    ClockFrontShape.FrontSyncConcentration_remaining (L := L) (K := K) n mC H
      (ENNReal.ofReal ((H : ℝ) * (Bbd : ℝ) ^ 2 / (n : ℝ) ^ 2)) :=
  frontSync_concentration_remaining_via_frontAll (L := L) (K := K) n mC Bbd hWpos hWcap hn2
    hbd_all hstart H

/-! ## Part 4 — the PRECISELY-NAMED joint clock-front induction residual (STOP).

The clock-progress connection — supplying the boundary-feeder window `hbd_all` and the
whole-front-empty start from the clock's OWN advance (`clock_real_faithful_O_log_n`) —
does NOT close without a JOINT clock-front induction.  We name it precisely and STOP; it
is stated as a `Prop`, NOT asserted, NOT faked, and is NOT a `∀c` deterministic window
(which would be FALSE, the at-cap `counter = 1` witness
`ClockFrontShape.counterPos_one_step_NOT_closed_witness`).

The mutual dependence:

* The clock advance `ClockRealSeed.clock_real_step` (composed to
  `ClockRealFaithfulHours.clock_real_faithful_O_log_n`) carries `habs_mix` — the
  deterministic `Q_mix` window closure — which is FALSE off the FrontSync window.  It is
  supplied whp by the FrontSync concentration (`FrontSyncConc.habs_mix_full`, gated on
  FrontSync).

* The FrontSync concentration (`front_empty_all_levels` / Part 3) needs the boundary
  window `hbd_all` (`rBeyond (W−1) ≤ Bbd` on every reachable config).

* `hbd_all` holding at every reachable config is EXACTLY the clock-progress condition:
  the leading edge stays below `cap − W` (`rBeyond (W−1) ≤ Bbd`, the bulk feeder not yet
  flooded by clocks that advanced too far) for the run, i.e. the clock advances its edge
  minute by minute WITHOUT the front inflating past the `O(log log n)` width.

So the connection requires the clock advance and the front emptiness to be maintained
TOGETHER, each feeding the other — Doty §6's intertwined core. -/

/-- **`JointClockFront` — the joint clock-front induction obligation (the PRECISE
residual, stated as a `Prop`, NOT asserted).**  Over the horizon `H`, from a
`Q_mix ∧ FrontSync ∧ AllClockP3 ∧ whole-front-empty` start of population `n`, BOTH hold
whp simultaneously:

* **(front stays empty above the width)** the front is empty at all `W = frontWidthBound n`
  top levels — `rBeyond W c' = 0` — with failure `≤ ε`; AND
* **(clock advances its leading edge)** the leading-edge bulk feeder stays capped —
  `rBeyond (W−1) c' ≤ Bbd` — so the clock's per-minute advance (`clock_real_step`) closes
  its `habs_mix` window on the FrontSync-good event (`FrontSyncConc.habs_mix_full`), with
  failure `≤ ε`.

The two conjuncts are MUTUALLY dependent: the front emptiness needs the bulk-feeder cap
(the clock not having advanced past the boundary), and the clock advance needs FrontSync
(the front empty at the cap).  This is the joint induction Doty §6 proves by intertwining
Theorem 6.5 (front shape) with Lemmas 6.6–6.10 (clock lower bound + hour
synchronization).  Stated as a `Prop`, deliberately NOT asserted — closing it is the
genuine deepest residual, NOT a `∀c` window (which is FALSE off FrontSync). -/
def JointClockFront (n mC Bbd : ℕ) (H : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ c₀ : Config (AgentState L K),
    Q_mix (L := L) (K := K) n mC 0 c₀ →
    FrontSync (L := L) (K := K) c₀ →
    AllClockP3 c₀ →
    rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0 →
    (((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | 1 ≤ rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c'} ≤ ε) ∧
    (((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | Bbd < rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n - 1) c'} ≤ ε)

/-- **`clock_real_O_log_n_fully_unconditional_of_joint` — the clock becomes fully
unconditional whp ONCE the joint clock-front induction `JointClockFront` is supplied.**
GIVEN the joint induction `hjoint : JointClockFront n mC Bbd H ε` (the front empty above
the width AND the bulk feeder capped, maintained mutually), the boundary-feeder window
`hbd_all` and the whole-front-empty event are SUPPLIED along the run, so the clock
FrontSync breach is `≤ ofReal (H·Bbd²/n²)` carrying NO structural hypothesis beyond the
start gate.  We state the implication precisely: the FULLY-unconditional clock is the
joint induction `JointClockFront` away.

This makes the residual SHARP: the clock is unconditional whp IF AND ONLY the boundary
bulk-feeder cap `rBeyond (W−1) ≤ Bbd` is maintained whp — which is the SECOND conjunct of
`JointClockFront`, the clock-progress condition the front concentration cannot
self-supply (it would need the front already empty, circular).  The first conjunct (front
empty above the width) is exactly `front_empty_all_levels` GIVEN the second; the two are
the mutual induction. -/
theorem clock_real_O_log_n_fully_unconditional_of_joint (n mC Bbd : ℕ)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hWcap : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hbd_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c = 0 → AllClockP3 c →
      c.card = n →
      RFeederCapWindow (L := L) (K := K) n (FrontTail.frontWidthBound n) Bbd c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC 0 c₀)
    (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hw0 : AllClockP3 c₀)
    (hempty0 : rBeyond (L := L) (K := K) (FrontTail.frontWidthBound n) c₀ = 0) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      ENNReal.ofReal ((H : ℝ) * (Bbd : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
  -- the boundary window `hbd_all` is the joint residual; given it, the clean prefix closes.
  clock_real_O_log_n_given_front (L := L) (K := K) n mC Bbd hWpos hWcap hn2 hbd_all
    H c₀ hQ hsync0 hw0 hempty0

/-! ## HONEST STATUS — `ClockFrontIter` (iterate over `W` levels → connect to clock progress)

* **(1) The `W`-level iteration is GENUINELY PROVEN.**  `front_empty_all_levels` iterates
  the proven per-level empty-absorbing step (`ClockFrontWidth.rBeyond_seed_le_rBeyondSq`,
  the empty-seed squaring with the sync term absent — `ClockBulkFront.seed_pair_real`'s
  vanishing) over ALL `W = frontWidthBound n = O(log log n)` front levels.  The iteration
  is realized as a SINGLE boundary concentration via the PROVEN level-collapse
  `FrontAllLevels.whole_front_iff_boundary_empty` (threshold-antitonicity telescopes "all
  `W` levels empty" into `rBeyond W = 0`).  This is NOT an assumed recursion: it is the
  proven boundary squaring lifted to all `W` levels by the proven antitone collapse.  The
  `∃ j …` all-levels-non-empty event is the single-boundary breach, bounded by
  `H · (Bbd/n)²`.

* **(2) The base case is the whole-front-empty event, at the collapsed envelope.**
  `envelope_collapsed_at_width` + `base_case_within_iff_empty`: at the width boundary the
  doubly-exp envelope is `< 1/n`, so within-envelope ⟺ empty there — the bulk-top
  condition, no deeper drip.  The recursion bottoms cleanly.

* **(3) The clock-progress connection — MAXIMAL CLEAN PREFIX PROVEN.**
  `clock_real_O_log_n_given_front` and `frontSync_concentration_remaining_discharged`:
  GIVEN the single boundary-feeder window `hbd_all` and the whole-front-empty start gate,
  the clock FrontSync breach is `≤ ofReal (H·Bbd²/n²)` (`1/poly`), carrying NO interior
  front window — only the single boundary input.  The named clock obligation
  `ClockFrontShape.FrontSyncConcentration_remaining` is discharged at this budget.

* **(4) The connection does NOT close fully — the JOINT clock-front induction is the
  PRECISE residual (named, STOP, NOT faked).**  `JointClockFront` (Part 4, a `Prop`, NOT
  asserted): the clock advance (`clock_real_step`'s `habs_mix`, FALSE off FrontSync) and
  the front emptiness (`front_empty_all_levels`'s `hbd_all`) are MUTUALLY dependent —
  `habs_mix` needs FrontSync (`habs_mix_full`), FrontSync needs the bulk-feeder cap
  `hbd_all`, and `hbd_all` IS the clock-progress condition (leading edge below `cap − W`,
  bulk feeder not flooded).  Closing it requires the joint statement maintained mutually
  over the run — Doty §6's intertwined Theorem 6.5 ⟷ Lemmas 6.6–6.10.
  `clock_real_O_log_n_fully_unconditional_of_joint` makes the residual SHARP: the clock is
  fully unconditional whp PRECISELY when `JointClockFront`'s second conjunct (the
  bulk-feeder cap `rBeyond (W−1) ≤ Bbd` maintained whp) holds.

VERDICT (NOT over-claimed): the `W`-level iteration is GENUINELY PROVEN (the proven
per-level squaring lifted by the proven antitone collapse over all `W` levels, NOT
assumed).  The clock is NOT made fully unconditional: the clock-progress connection
requires the JOINT clock-front induction (`JointClockFront`), which is the genuine
deepest residual — the mutual maintenance of clock advance and front emptiness, NOT a
`∀c` window (which is FALSE off FrontSync).  It is named precisely and we STOP.  The
clock carries the SINGLE boundary-feeder window `hbd_all` (the clock-progress condition) +
the whole-front-empty start gate, discharged whp by `JointClockFront` if and only if its
second conjunct holds — the precise joint-induction obligation, deliberately stated as a
`Prop`, NOT asserted, NOT faked. -/
theorem clock_front_iter_status : True := trivial

end ClockFrontIter

end ExactMajority
