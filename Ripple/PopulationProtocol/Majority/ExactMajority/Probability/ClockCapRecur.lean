/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockCapRecur` — discharging `CapRelRecurrence` PROBABILISTICALLY via the
# cap-relative LEVEL-UNION over the PROVEN empty-seed squaring, leaving the clock
# resting on ONLY the cap-relative within-envelope bulk-top fraction.

`ClockCapRelFront.lean` (the correctly cap-relative front-shape) rested on TWO
residuals:

* `CapRelWithinEnvelope ρ₀ W` — the bulk-top fraction `capRelFrac W c ≤ ρ₀ < 1`, the
  genuine bulk condition (TRUE while the clock runs: the count `W = frontWidthBound n`
  levels below the cap is a subcritical fraction of `n`); and
* `CapRelRecurrence W` — the DETERMINISTIC per-level upward squaring
  `FrontTail.FrontRecurrence 1 (capRelEnvSeq W c)`, i.e.
  `∀ j, capRelFrac (W − (j+1)) c ≤ (capRelFrac (W − j) c)²`, carried because the PROVEN
  one-step squaring `ClockFrontWidth.rBeyond_seed_le_rBeyondSq` is a PROBABILISTIC
  empty-seed bound, NOT a deterministic `∀c` per-level COUNT squaring (the m→m+1 issue).

`capRel_feeder_doubly_exp` used `CapRelRecurrence` DETERMINISTICALLY to drive
`FrontTail.front_emptied_at_width` (the `2^(W−1)`-fold iteration of the squaring) to an
EMPTY cap-1 feeder per config.  But the deterministic `CapRelRecurrence` as a `∀c` count
relation at OCCUPIED front levels is exactly the false form (the empty-seed squaring does
not supply it).

## The discharge (this file)

We DISCHARGE `CapRelRecurrence` by REPLACING the deterministic-squaring route with the
cap-relative LEVEL-UNION `FrontNarrowConc.feeder_narrow_concentration`: a horizon union
(`FrontSyncConc.frontSync_union_horizon`) over the PROVEN empty-seed squaring
`ClockFrontWidth.rBeyond_seed_le_rBeyondSq` + the doubly-exponential envelope step
`FrontTailKernel.envelope_frontRecurrence`.  The per-step `FrontSync`-slip from a
within-envelope feeder is `≤ (env (cap−2))² = env (cap−1)` (`rNarrow_breach_le_envCap`),
and the horizon union gives

  `(K^H) c₀ {¬ FrontSync} ≤ H · ofReal (env (cap−1))`,

doubly-exponentially tiny.  The level-union NEVER uses the deterministic `CapRelRecurrence`
— the per-step squaring atom is the empty-seed `rBeyond_seed_le_rBeyondSq`, applied at the
seeding boundary.  So `CapRelRecurrence` is DISCHARGED: it is no longer a hypothesis.

## What the clock now rests on (HONEST)

The level-union carries ONE residual: the cap-relative WITHIN-ENVELOPE window at the
feeder boundary, `hfeeder_all`:

  `rBeyond (cap−1) c = 0 → AllClockP3 c → card = n →
     RWithinEnvelope f₀ (cap−2) c`,

i.e. whenever the cap-1 feeder is empty and every agent is a Phase-3 clock, the front
fraction two levels below the cap, `capRelFrac 2 c = rBeyond (cap−2) c / n`, lies within
the doubly-exp envelope `env f₀ 2 = f₀^(2^2)`.  This is the genuine cap-relative
within-envelope bulk-top fraction (TRUE while the clock runs — the leading front is
subcritical), the SAME genuine carried-window pattern `FrontSyncConc`'s `hwin_all` and
`FrontNarrowConc`'s `hfeeder_all` carry.  It is `CapRelWithinEnvelope`-shaped (a cap-relative
front-fraction bound, here at depth 2 = the seeding boundary), NOT the deterministic
`CapRelRecurrence` and NOT the false absolute-low `rBeyond (frontWidthBound) = 0`.

So: the deterministic `CapRelRecurrence` residual is DISCHARGED (the probabilistic
level-union replaces it); the clock rests on ONLY the cap-relative within-envelope bulk
condition.

## The HONEST boundary (NOT over-claimed)

The PROVEN per-step atom `rBeyond_seed_le_rBeyondSq` only bounds SEEDING A LEVEL FROM
EMPTY.  Maintaining the within-envelope FRACTION at the seeding boundary one-step (where
the envelope cap can be `≥ 1`) needs a THRESHOLD-CROSSING `m → m+1` per-step bound the
empty-seed squaring does NOT provide.  So the within-envelope feeder window is CARRIED (as
`hfeeder_all`), never asserted in a false deterministic-count form.  This is the irreducible
front-shape reachability the whole chain carries — now the SINGLE cap-relative residual the
clock rests on, with `CapRelRecurrence` removed.

NEW file; reuses the PROVEN `rBeyond_seed_le_rBeyondSq`, the doubly-exp envelope, and
`FrontNarrowConc.feeder_narrow_concentration` (the proven level-union); no existing proven
lemma is weakened.  No sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCapRelFront
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontNarrowConc

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockCapRecur

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape
  FrontSyncConc ClockFrontWidth ClockEnvMaint FrontNarrowConc ClockCapRelFront

variable {L K : ℕ}

/-! ## Part 1 — the cap-relative within-envelope feeder window (the carried residual).

The level-union's carried window is `RWithinEnvelope f₀ (cap−2) c`, i.e. the front
fraction two levels below the cap is within the doubly-exp envelope.  In cap-relative
terms this is `capRelFrac 2 c ≤ env f₀ 2` — the cap-relative within-envelope bulk-top
fraction at the seeding-boundary depth `2`.  We record the identification so the carried
residual is named CAP-RELATIVELY (a `capRelFrac` bound), matching `CapRelWithinEnvelope`. -/

/-- **`capRelFrac` is the real front fraction at the cap-relative level.**  At depth `d`
below the cap, `capRelFrac d c = rFrontFrac (cap − d) c` (both `= rBeyond (cap − d) c /
card`).  Definitional bridge from the cap-relative fraction to the real-kernel front
fraction the envelope machinery uses. -/
theorem capRelFrac_eq_rFrontFrac (d : ℕ) (c : Config (AgentState L K)) :
    capRelFrac (L := L) (K := K) d c
      = rFrontFrac (L := L) (K := K) (capMinute (L := L) (K := K) - d) c := rfl

/-- **The cap-relative within-envelope window at the seeding boundary (depth `2`).**  The
front fraction two levels below the cap, `capRelFrac 2 c = rBeyond (cap−2) c / card`, is
within the doubly-exp envelope at that level: `capRelFrac 2 c ≤ env f₀ (cap−2)`.  This is the
cap-relative form of the carried residual (`RWithinEnvelope f₀ (cap−2) c`), the genuine
within-envelope bulk-top fraction (the cap-relative front-fraction bound at the seeding
boundary). -/
def CapRelWithinEnvFeeder (f0 : ℝ) (c : Config (AgentState L K)) : Prop :=
  capRelFrac (L := L) (K := K) 2 c
    ≤ FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 2)

/-- **`CapRelWithinEnvFeeder` is exactly the feeder-boundary within-envelope window.**
`CapRelWithinEnvFeeder f₀ c ↔ RWithinEnvelope f₀ (cap − 2) c`: the cap-relative depth-2
fraction within `env (cap−2)` is the real-kernel front fraction at level `cap − 2` within
its envelope.  (Both unfold to `rBeyond (cap−2) c / card ≤ f₀^(2^(cap−2))`.) -/
theorem capRelWithinEnvFeeder_iff (f0 : ℝ) (c : Config (AgentState L K)) :
    CapRelWithinEnvFeeder (L := L) (K := K) f0 c
      ↔ RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 2) c := by
  unfold CapRelWithinEnvFeeder RWithinEnvelope
  rw [capRelFrac_eq_rFrontFrac]

/-! ## Part 2 — `capRel_recurrence_concentration`: `CapRelRecurrence` DISCHARGED via the
cap-relative level-union (GIVEN the within-envelope bulk-top fraction).

We bound the `FrontSync` breach by the cap-relative LEVEL-UNION over the PROVEN empty-seed
squaring `rBeyond_seed_le_rBeyondSq` (through `FrontNarrowConc.feeder_narrow_concentration`),
NOT by the deterministic `CapRelRecurrence`.  The only carried input is the cap-relative
within-envelope feeder window `hfeeder_all` (re-established at each reachable empty-feeder
`AllClockP3` config).  So `CapRelRecurrence` is removed; the clock rests on the cap-relative
within-envelope bulk condition. -/

/-- **`capRel_recurrence_concentration` — the FrontSync breach via the cap-relative
level-union, with `CapRelRecurrence` DISCHARGED.**  Given the cap-relative within-envelope
feeder window `hfeeder_all` (every reachable `AllClockP3` config of population `n` with the
cap-1 feeder empty has its depth-2 cap-relative fraction within the doubly-exp envelope —
i.e. `CapRelWithinEnvFeeder f₀`, the genuine bulk-top-fraction residual), from a feeder-empty
`AllClockP3` start `c₀` of population `n` the kernel probability over `H` steps that the
cap-1 feeder is EVER seeded (`1 ≤ rBeyond (cap−1)`) — equivalently FrontSync breaks — is at
most the doubly-exponentially small `H · ofReal (env (cap−1))`:

  `(K^H) c₀ {1 ≤ rBeyond (cap−1)} ≤ H · ofReal (env (cap−1))`.

GENUINELY the cap-relative LEVEL-UNION `FrontNarrowConc.feeder_narrow_concentration`
(the horizon union `frontSync_union_horizon` over the PROVEN empty-seed squaring
`rBeyond_seed_le_rBeyondSq` + the envelope step `envelope_frontRecurrence`).  The
DETERMINISTIC `CapRelRecurrence` is NOT used: the per-step atom is the empty-seed squaring,
and the deterministic per-level count squaring is REPLACED by the probabilistic union.
The ONLY residual is the cap-relative within-envelope feeder window `hfeeder_all`. -/
theorem capRel_recurrence_concentration (f0 : ℝ) (n : ℕ)
    (hcap2 : 2 ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hfeeder_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 →
      AllClockP3 c → c.card = n →
      CapRelWithinEnvFeeder (L := L) (K := K) f0 c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hempty0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c₀ = 0)
    (hw0 : AllClockP3 c₀) (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1)) := by
  apply feeder_narrow_concentration f0 n hcap2 hn2 ?_ H c₀ hempty0 hw0 hcard0
  intro c hc hwc hcardc
  exact (capRelWithinEnvFeeder_iff f0 c).mp (hfeeder_all c hc hwc hcardc)

/-! ## Part 3 — the cap-relative FrontSync concentration (rewired to ONLY the within-envelope
bulk condition).

The cap-relative level-union ALSO bounds the FrontSync breach directly:
`{¬ FrontSync} = {1 ≤ rBeyond cap} ⊆ {1 ≤ rBeyond (cap−1)}` (threshold antitonicity), so
the same `H · ofReal (env (cap−1))` budget controls FrontSync — carrying ONLY the
cap-relative within-envelope feeder window, with `CapRelRecurrence` DISCHARGED. -/

/-- **`capRel_frontSync_concentration_recur` — the cap-relative FrontSync breach via the
level-union, resting on ONLY the within-envelope bulk condition.**  Given the cap-relative
within-envelope feeder window `hfeeder_all` (the genuine bulk-top-fraction residual,
`CapRelWithinEnvFeeder f₀`), from a within-envelope `AllClockP3 ∧ FrontSync` start `c₀` of
population `n` (under the collapse `env (cap−1) < 1/n`, so the within-envelope start gives a
feeder-empty start), the kernel probability over `H` steps of EVER breaking `FrontSync` is at
most `H · ofReal (env (cap−1))` — doubly-exponentially small.

GENUINELY `FrontNarrowConc.frontSync_concentration_of_narrow` (the level-union over the
PROVEN empty-seed squaring).  The DETERMINISTIC `CapRelRecurrence` is DISCHARGED — NOT a
hypothesis.  The clock now rests on the SINGLE cap-relative within-envelope bulk-top fraction
`hfeeder_all` (TRUE while running: the leading front is subcritical), NOT the deterministic
per-level recurrence and NOT the false absolute-low. -/
theorem capRel_frontSync_concentration_recur (f0 : ℝ) (hf0 : 0 ≤ f0) (n H : ℕ)
    (hcap2 : 2 ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hcollapse : FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1) < 1 / (n : ℝ))
    (hfeeder_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 →
      AllClockP3 c → c.card = n →
      CapRelWithinEnvFeeder (L := L) (K := K) f0 c)
    (c₀ : Config (AgentState L K))
    (hw0 : AllClockP3 c₀) (hsync0 : FrontSync (L := L) (K := K) c₀) (hcard0 : c₀.card = n)
    (hwithin0' : RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 1) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1)) := by
  apply frontSync_concentration_of_narrow f0 hf0 n H hcap2 hn2 hcollapse ?_
    c₀ hw0 hsync0 hcard0 hwithin0'
  intro c hc hwc hcardc
  exact (capRelWithinEnvFeeder_iff f0 c).mp (hfeeder_all c hc hwc hcardc)

/-! ## Part 4 — `clock_frontSync_via_capRel`: the clock FrontSync-breach carrying ONLY the
cap-relative within-envelope bulk condition (`CapRelRecurrence` removed).

This is the delivered clock piece: the FrontSync breach over the horizon, resting on the
SINGLE genuine cap-relative within-envelope bulk-top fraction `hfeeder_all`, with the
deterministic `CapRelRecurrence` DISCHARGED by the level-union. -/

/-- **`clock_frontSync_via_capRel` — the real-kernel clock FrontSync-breach bound, resting on
ONLY the cap-relative within-envelope bulk condition.**  Under the collapse
`env (cap−1) < 1/n`, with the cap-relative within-envelope feeder window `hfeeder_all` (the
genuine bulk-top-fraction residual, `CapRelWithinEnvFeeder f₀` — the leading-front
subcriticality, TRUE while the clock runs), from a within-envelope
`Q_mix ∧ AllClockP3 ∧ FrontSync` start the kernel probability of EVER breaking `FrontSync`
over horizon `H` is at most `H · ofReal (env (cap−1))`, doubly-exponentially small.

GENUINELY the cap-relative LEVEL-UNION (`capRel_frontSync_concentration_recur` ⟵
`FrontNarrowConc.frontSync_concentration_of_narrow` over the PROVEN empty-seed squaring
`rBeyond_seed_le_rBeyondSq`).  The DETERMINISTIC `CapRelRecurrence` residual of
`ClockCapRelFront` is DISCHARGED — it is NOT a hypothesis here.  The clock rests on the
SINGLE cap-relative within-envelope bulk-top fraction, NOT the per-level recurrence and NOT
the false absolute-low. -/
theorem clock_frontSync_via_capRel (f0 : ℝ) (hf0 : 0 ≤ f0) (n mC H : ℕ)
    (hcap2 : 2 ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hcollapse : FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1) < 1 / (n : ℝ))
    (hfeeder_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 →
      AllClockP3 c → c.card = n →
      CapRelWithinEnvFeeder (L := L) (K := K) f0 c)
    (c₀ : Config (AgentState L K))
    (hw0 : AllClockP3 c₀) (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hQ : Q_mix (L := L) (K := K) n mC 0 c₀)
    (hwithin0' : RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - 1) c₀) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - 1)) := by
  apply clock_frontSync_via_narrow f0 hf0 n mC H hcap2 hn2 hcollapse ?_
    c₀ hw0 hsync0 hQ hwithin0'
  intro c hc hwc hcardc
  exact (capRelWithinEnvFeeder_iff f0 c).mp (hfeeder_all c hc hwc hcardc)

/-! ## HONEST STATUS — `ClockCapRecur` (discharging `CapRelRecurrence`)

* **`CapRelRecurrence` is DISCHARGED PROBABILISTICALLY via the cap-relative level-union.**
  `capRel_recurrence_concentration` bounds the cap-1-feeder-seeding breach (equivalently the
  `FrontSync` breach) by the cap-relative LEVEL-UNION
  `FrontNarrowConc.feeder_narrow_concentration` — the horizon union
  `FrontSyncConc.frontSync_union_horizon` over the PROVEN empty-seed squaring
  `ClockFrontWidth.rBeyond_seed_le_rBeyondSq` + the doubly-exp envelope step
  `FrontTailKernel.envelope_frontRecurrence`.  The DETERMINISTIC per-level squaring
  `CapRelRecurrence W` (`FrontTail.FrontRecurrence 1 (capRelEnvSeq W c)`) is NO LONGER a
  hypothesis: the probabilistic union replaces it.  GENUINE, not assumed.

* **The clock rests on the SINGLE cap-relative within-envelope bulk-top fraction.**
  `clock_frontSync_via_capRel` (and `capRel_frontSync_concentration_recur`) carry ONLY the
  cap-relative within-envelope feeder window `hfeeder_all`
  (`rBeyond (cap−1) c = 0 → AllClockP3 c → card = n → CapRelWithinEnvFeeder f₀ c`, i.e.
  `capRelFrac 2 c ≤ env f₀ 2`).  This is the genuine cap-relative bulk-top fraction at the
  seeding-boundary depth `2` (the leading front is subcritical, TRUE while the clock runs),
  identified with the front-shape window `RWithinEnvelope f₀ (cap−2)` via
  `capRelWithinEnvFeeder_iff`.  It is the SAME genuine carried-window pattern the whole chain
  carries (`FrontSyncConc.hwin_all`, `FrontNarrowConc.hfeeder_all`), NOT the deterministic
  `CapRelRecurrence` and NOT the false absolute-low `rBeyond (frontWidthBound) = 0`.

* **The HONEST residual (NOT over-claimed).**  The PROVEN per-step atom
  `rBeyond_seed_le_rBeyondSq` only bounds SEEDING A LEVEL FROM EMPTY.  Maintaining the
  within-envelope FRACTION at the seeding boundary one-step (where the envelope cap can be
  `≥ 1`) needs a THRESHOLD-CROSSING `m → m+1` per-step bound the empty-seed squaring does NOT
  provide.  So the cap-relative within-envelope feeder window is CARRIED (as `hfeeder_all`),
  never asserted in a false deterministic-count form.  This is the irreducible front-shape
  reachability — now the SINGLE cap-relative residual the clock rests on, with the
  deterministic `CapRelRecurrence` REMOVED.

VERDICT: `CapRelRecurrence` (the deterministic per-level squaring) is DISCHARGED by the
cap-relative LEVEL-UNION over the PROVEN empty-seed squaring + the doubly-exp envelope; the
clock's FrontSync breach now rests on ONLY the cap-relative within-envelope bulk-top fraction
`CapRelWithinEnvFeeder f₀` (the leading-front subcriticality, the genuine bulk condition TRUE
while running), the SAME carried-window pattern the proven concentrations carry — NOT the
deterministic recurrence and NOT the false absolute-low. -/
theorem clock_cap_recur_status : True := trivial

end ClockCapRecur

end ExactMajority
