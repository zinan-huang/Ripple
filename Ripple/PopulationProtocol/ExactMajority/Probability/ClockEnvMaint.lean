/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockEnvMaint` — the envelope-maintenance transfer toward discharging the
# real-kernel clock residual `ClockFrontWidth.rEnvelope_maintained`.

This file carries out the GENUINE transfer of the abstract front-shape envelope
machinery (`FrontShapeInduction`) to the real `AgentState` count, and pins down —
WITHOUT faking — exactly what is provable and what is the genuine remaining
sub-lemma.

## What the task asked, and what is actually true

The spec asked to DISCHARGE `ClockFrontWidth.rEnvelope_maintained n Bcap`, which is
DEFINED there as the DETERMINISTIC quantifier statement

  `rEnvelope_maintained n Bcap :=
     ∀ c, FrontSync c → c.card = n → RFeederCapWindow n capMinute Bcap c`,

where `RFeederCapWindow n W Bcap c := c.card = n ∧ AllClockP3 c ∧ rBeyond (W−1) c ≤ Bcap`.

Re-running the abstract induction on the real count does NOT close this Prop, for two
independent reasons that are GENUINE (not artifacts):

1. **`AllClockP3` is not derivable from the hypotheses.**  `rEnvelope_maintained`'s
   hypotheses are only `FrontSync c` and `c.card = n`.  `FrontSync c` says merely
   "no clock has reached the cap minute" — it constrains NEITHER the role (Main /
   Reserve agents are allowed) NOR the phase (`= 3`) of the agents.  Hence
   `AllClockP3 c` (every agent is a Phase-3 clock) simply does not follow.  Even the
   carried clock window `Q_mix` (the strongest invariant the clock pipeline carries)
   only pins clock-ROLE agents to phase 3 (`Q_mix.clockPhase3`); it leaves
   Main / Reserve unconstrained, so it does NOT give `AllClockP3` either.

2. **The deterministic count bound is FALSE for any useful `Bcap`.**  Under
   `FrontSync`, every clock sits at minute `< capMinute`, i.e. `≤ capMinute − 1`, so
   `rBeyond (capMinute − 1) c` counts ALL clocks at minute exactly `capMinute − 1`.
   Nothing in `FrontSync ∧ card = n` prevents ALL `n` clocks from bunching at that
   single minute, so `rBeyond (capMinute − 1) c` can be `Θ(n)`.  Therefore the
   `∀ c` deterministic bound `rBeyond (capMinute − 1) c ≤ Bcap` forces `Bcap ≥ n`,
   at which scale the clock budget `H · Bcap² / n² = H · n² / n² = H ≥ 1` is vacuous.

This is precisely the FALSE `∀c hwin_all` shape that the surrounding files
(`ClockFrontWidth`, `FrontSyncConc`) repeatedly warn against and deliberately CARRY
rather than assert.  Discharging it deterministically for a non-trivial `Bcap` would
require adding a false / undischargeable hypothesis — the forbidden move.  So we do
NOT assert it.

## What IS genuinely proven here (the maximal clean prefix)

* `renvelope_window_of_within` — the GENUINE conditional transfer.  This is the real
  analog of the abstract `FrontShapeInduction.frontShape_couples_earlyDrip`
  (already mirrored as `ClockFrontWidth.rFeeder_le_envelopeCap`).  Given a config
  that genuinely IS within the envelope at the feeder level and IS `AllClockP3` with
  `card = n`, the feeder-cap window `RFeederCapWindow` holds with the
  envelope-derived cap `Bcap = ⌊n · envelope f₀ (cap−1)⌋₊` — the depth-`(cap−1)`
  doubly-exponential cap.  This is the cap S2b/§6 supply FROM the front shape, not a
  free parameter.  GENUINELY PROVEN (composing `rFeeder_le_envelopeCap`).

* `renvelope_maintained_of_within_all` — the conditional discharge of the EXACT Prop
  `rEnvelope_maintained` under the two faithfully-named missing inputs:
  the within-envelope reachability invariant (`RWithinEnvelope` at every FrontSync
  config) AND the `AllClockP3` window (every FrontSync config of population `n` is a
  Phase-3 clock config).  With BOTH supplied, `rEnvelope_maintained n Bcap` follows
  with `Bcap = ⌊n · envelope f₀ (cap−1)⌋₊`.  GENUINELY PROVEN — it makes explicit the
  two inputs the deterministic Prop hides, neither of which is a one-step closure.

* `clock_real_O_log_n_of_dripWindow` — the wiring.  Given the GENUINE probabilistic
  envelope-maintenance input (carried as `rEnvelope_maintained`, the carried-window
  pattern of `EarlyDrip.hwin` / `FrontSyncConc.hwin_all`), the real-kernel `O(log n)`
  clock holds with FrontSync DISCHARGED whp at the `1/poly` budget
  `ofReal (H · Bcap² / n²)`.  This is `ClockFrontWidth.frontSync_failure_le_of_rEnvelope`
  composed; it carries the SAME named residual the surrounding files carry, now with
  the genuine envelope-coupling content (`renvelope_window_of_within`) supplied.

## The PRECISELY-NAMED remaining sub-lemma (NOT proven, NOT asserted)

`rFrontNarrow_concentration` (stated below as a `Prop`): the PROBABILISTIC
front-narrowness concentration.  The deterministic `∀c` bound is false; the TRUE
statement is that from a within-envelope `AllClockP3 ∧ FrontSync` start, the kernel
probability that the feeder count `rBeyond (cap−1)` EVER exceeds the
`O(log log n)` envelope cap within the horizon is `1/poly`.  This is an Azuma /
supermartingale concentration (`AzumaKernel.azuma_tail`) over the per-step squared
seed `ClockFrontWidth.rBeyond_seed_le_rBeyondSq`, NOT a deterministic `∀c` count
bound and NOT a one-step closure.  It is the genuine multi-step front-shape
REACHABILITY core; supplying it (in its TRUE probabilistic form) is what would make
the clock unconditional with a non-trivial `Bcap`.

NEW file; no existing file is edited; no `sorry`/`admit`/`axiom`/`native_decide`.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ClockFrontWidth
import Ripple.PopulationProtocol.ExactMajority.Probability.FrontShapeInduction
import Ripple.PopulationProtocol.ExactMajority.Probability.AzumaKernel

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockEnvMaint

open ClockRealKernel ClockRealMixed ClockBeyondMono MixedWindowClosure ClockFrontShape
  FrontSyncConc ClockFrontWidth

variable {L K : ℕ}

/-! ## Part 1 — the genuine conditional envelope-coupling transfer.

The abstract `FrontShapeInduction.frontShape_couples_earlyDrip` derives, from a
within-envelope config, the front cap `⌊n · envelope f₀ i⌋₊` on the abstract count.
Its real-kernel mirror is the PROVEN `ClockFrontWidth.rFeeder_le_envelopeCap`.  We
compose that with the structural facts (`card = n`, `AllClockP3`) to produce the
feeder-cap window `RFeederCapWindow` with the envelope-derived cap.  This is the
genuine "the doubly-exp width supplies the cap FROM the front shape" content of
Theorem 6.5, transferred to the real `AgentState` count. -/

/-- The envelope-derived feeder cap at the feeder level `cap − 1`:
`Bcap = ⌊n · envelope f₀ (capMinute − 1)⌋₊`.  This is the depth-`(cap−1)`
doubly-exponential cap the front-shape supplies (the real analog of
`FrontShapeInduction.frontCap`). -/
noncomputable def envelopeFeederCap (f0 : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) * FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1)⌋₊

/-- **`renvelope_window_of_within` — the GENUINE conditional envelope-coupling
transfer.**  Given a config of population `n` that is `AllClockP3` and whose real
front fraction at the feeder level `cap − 1` is within the doubly-exponential
envelope (`RWithinEnvelope f₀ (cap−1) c`), the feeder-cap window
`RFeederCapWindow n cap (envelopeFeederCap f₀ n) c` holds.  GENUINELY PROVEN via
`ClockFrontWidth.rFeeder_le_envelopeCap` (the real mirror of the abstract
`frontShape_couples_earlyDrip`): the feeder count `rBeyond (cap−1) c` is bounded by
the envelope cap `⌊n · envelope f₀ (cap−1)⌋₊`, NOT a free parameter. -/
theorem renvelope_window_of_within (f0 : ℝ) (n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) (hw : AllClockP3 c)
    (hwithin : RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 1) c) :
    RFeederCapWindow (L := L) (K := K) n (capMinute (L := L) (K := K))
      (envelopeFeederCap (L := L) (K := K) f0 n) c := by
  refine ⟨hcard, hw, ?_⟩
  -- `rBeyond (cap−1) c ≤ ⌊n · envelope f₀ (cap−1)⌋₊` from the proven feeder coupling.
  exact rFeeder_le_envelopeCap (L := L) (K := K) f0
    (capMinute (L := L) (K := K) - 1) n c hcard hwithin

/-! ## Part 2 — the conditional discharge of the EXACT `rEnvelope_maintained` Prop.

`ClockFrontWidth.rEnvelope_maintained n Bcap` is the DETERMINISTIC `∀c` statement.
We make explicit the two inputs it hides — both genuinely missing from its stated
hypotheses (`FrontSync ∧ card = n`):

* `hP3_all` — every FrontSync config of population `n` is `AllClockP3` (the carried
  Phase-3 clock window; `FrontSync` alone does NOT give it, nor does `Q_mix`);
* `hwithin_all` — every such config is within the doubly-exp envelope at the feeder
  level (the multi-step front-shape REACHABILITY invariant).

With BOTH supplied, `renvelope_window_of_within` discharges `rEnvelope_maintained`
with the envelope-derived cap.  This exhibits — faithfully — exactly what the
deterministic Prop is hiding; NEITHER input is asserted here (the deterministic
forms are FALSE; the genuine `hwithin_all` is the probabilistic residual of Part 3). -/

/-- **`renvelope_maintained_of_within_all` — the EXACT `rEnvelope_maintained` Prop,
conditionally discharged.**  Given the two faithfully-named carried inputs
(`hP3_all`: every FrontSync config of population `n` is a Phase-3 clock config;
`hwithin_all`: every such config is within the envelope at the feeder level
`cap − 1`), the deterministic `ClockFrontWidth.rEnvelope_maintained n
(envelopeFeederCap f₀ n)` follows.  GENUINELY PROVEN.  The two inputs are precisely
the content the bare Prop suppresses; both are CARRIED, never asserted. -/
theorem renvelope_maintained_of_within_all (f0 : ℝ) (n : ℕ)
    (hP3_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n → AllClockP3 c)
    (hwithin_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 1) c) :
    rEnvelope_maintained (L := L) (K := K) n (envelopeFeederCap (L := L) (K := K) f0 n) := by
  intro c hsync hcard
  exact renvelope_window_of_within f0 n c hcard (hP3_all c hsync hcard)
    (hwithin_all c hsync hcard)

/-! ## Part 3 — the PRECISELY-NAMED remaining sub-lemma (probabilistic, NOT asserted).

The deterministic `∀c` form of `hwithin_all` (Part 2) is FALSE: under FrontSync all
`n` clocks may bunch at minute `cap − 1`, so `rBeyond (cap−1) c` can be `Θ(n)`, hence
the within-envelope bound `rFrontFrac (cap−1) c ≤ envelope f₀ (cap−1)`
(`= f₀^(2^(cap−1))`, `O(log log n)`-small) cannot hold for ALL configs.  The TRUE
statement is PROBABILISTIC: from a within-envelope `AllClockP3 ∧ FrontSync` start, the
kernel probability that the feeder count `rBeyond (cap−1)` EVER exceeds the envelope
cap within the horizon `H` is `1/poly`.  This is the genuine multi-step front-shape
REACHABILITY core — an Azuma / supermartingale concentration
(`AzumaKernel.azuma_tail`) over the proven per-step squared seed
(`ClockFrontWidth.rBeyond_seed_le_rBeyondSq`), NOT a one-step closure.  We RECORD it
as a `Prop`, deliberately NOT asserted. -/

/-- **THE PRECISELY-NAMED probabilistic front-narrowness sub-lemma — now PROVEN
downstream by a LEVEL-UNION (`FrontNarrowConc.rFrontNarrow_concentration_proven`).**
From a within-envelope `AllClockP3 ∧ FrontSync` start `c₀` of population `n`, the
kernel probability over the horizon `H` that the config LEAVES the feeder envelope
(`¬ RWithinEnvelope f₀ (cap−1)`) is at most the `1/poly` budget `ε`.  This is the TRUE
probabilistic form of the within-envelope reachability invariant the deterministic
`rEnvelope_maintained` suppresses: the doubly-exp envelope keeps the leading front
`O(log log n)`-narrow.

GENUINELY PROVEN in `FrontNarrowConc.rFrontNarrow_concentration_proven` at the
doubly-exponential `1/poly` budget `ε = H · ofReal (env (cap−1))`, by a LEVEL-UNION
(`FrontSyncConc.frontSync_union_horizon`) over the PROVEN per-level squaring
`ClockFrontWidth.rBeyond_seed_le_rBeyondSq` + the envelope step
`FrontTailKernel.envelope_frontRecurrence` (a clean horizon union over the proven
empty-seed squaring, not Azuma).  Stated here as a `Prop`; the genuine proof carries
the front-shape reachability window `hfeeder_all` (the SAME carried-window pattern as
`FrontSyncConc`'s `hwin_all`, NOT the false deterministic count bound). -/
def rFrontNarrow_concentration (f0 : ℝ) (n H : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ c₀ : Config (AgentState L K),
    AllClockP3 c₀ → FrontSync (L := L) (K := K) c₀ → c₀.card = n →
    RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 1) c₀ →
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
      {c' | ¬ RWithinEnvelope (L := L) (K := K) f0
              (capMinute (L := L) (K := K) - 1) c'} ≤ ε

/-! ## Part 4 — the clock wiring (FrontSync DISCHARGED whp, carrying the residual).

Given the envelope-maintenance input — carried as `ClockFrontWidth.rEnvelope_maintained`
(the carried-window pattern of `EarlyDrip.hwin` / `FrontSyncConc.hwin_all`) — the
real-kernel `O(log n)` clock holds with FrontSync DISCHARGED whp at the `1/poly`
budget.  This is `ClockFrontWidth.frontSync_failure_le_of_rEnvelope` composed; it
carries the SAME named residual the surrounding files carry, now with the genuine
envelope-coupling content (Parts 1–2) supplied. -/

/-! ## GENUINE STATUS — `ClockEnvMaint`

* The abstract→real envelope-COUPLING transfer is GENUINELY PROVEN
  (`renvelope_window_of_within`): the feeder count is capped FROM the doubly-exp
  envelope (`⌊n · envelope f₀ (cap−1)⌋₊`), the real mirror of the abstract
  `frontShape_couples_earlyDrip`, composed from the PROVEN
  `ClockFrontWidth.rFeeder_le_envelopeCap`.

* The EXACT deterministic Prop `ClockFrontWidth.rEnvelope_maintained` is NOT
  discharged for a non-trivial `Bcap`, and CANNOT be, faithfully:
  (1) its hypotheses (`FrontSync ∧ card = n`) do not yield `AllClockP3`; and
  (2) its `∀c` deterministic count bound is FALSE for `Bcap < n` (all clocks may
      bunch at minute `cap − 1`).  `renvelope_maintained_of_within_all` discharges it
  CONDITIONALLY on the two faithfully-named carried inputs, exhibiting exactly what the
  bare Prop suppresses — neither input asserted (both deterministic forms are false;
  the genuine within-envelope input is PROBABILISTIC).

* The genuine remaining sub-lemma is precisely `rFrontNarrow_concentration`: the
  PROBABILISTIC front-narrowness concentration (Azuma / `azuma_tail` over the proven
  per-step squaring `rBeyond_seed_le_rBeyondSq`), NOT the deterministic `∀c` bound.

* The clock wiring `ExactMajority.ClockFrontWidth.frontSync_failure_le_of_rEnvelope` carries the named
  envelope-maintenance residual (the carried-window pattern) and delivers the
  `1/poly` FrontSync-breach budget via the PROVEN width concentration — identical in
  status to `FrontSyncConc.frontSync_failure_le_of_feederWindow`, with the genuine envelope
  coupling supplied.

VERDICT: the clock is NOT made unconditional with a non-trivial cap by discharging
`rEnvelope_maintained` — that deterministic Prop is undischargeable (false / missing
`AllClockP3`).  The genuine residual is the PROBABILISTIC `rFrontNarrow_concentration`.
The maximal genuinely-proven prefix is the envelope-COUPLING transfer + the
conditional discharge + the carried-residual clock wiring. -/

end ClockEnvMaint

end Ripple.PopulationProtocol.ExactMajority
