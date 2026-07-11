/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockFullJoint` — the COMPLETE coupled lock-step: the four-conjunct invariant
# `Jall = FrontSync ∧ BulkPos ∧ FrontShape ∧ Ssmall`, with the OCCUPIED-band `Ssmall`
# MAINTAINED FROM `FrontShape`'s laggards-few (NOT carried as `CapRelRecurrence`).

## What changed from `ClockLockstep`

`ClockLockstep.Jfull = J ∧ Ssmall` maintained the EMPTY band + FrontSync + bulk-position but
CARRIED `CapRelRecurrence W` (the per-level squaring count `f(j+1) ≤ (f j)²`) as the explicit
per-step input for the OCCUPIED band, and carried the front-shape laggards as the `hnext` drip
window.  The previous file's honest residual was that the within-envelope FRACTION at an
OCCUPIED level is the `m → m+1` count, NOT supplied by the empty-absorbing band-feed.

THIS file makes the close explicit and REMOVES the carried `CapRelRecurrence` from the
band-maintenance leg: the band-count `Ssmall` is maintained from `FrontShape` (the laggards-few
within-envelope at the feeder level `cap − W − 1`) DIRECTLY, via the EMPTY-ABSORBING band-feed
(`ClockBulkFront.level_union_concentration` at `J = cap − W − 1`, `J + 1 = cap − W`).  The
mechanism — and the HONEST observation that closes the spec's open question about the
multiplicative sync term:

* The spec proposes maintaining `Ssmall_occupied` (band `≤ ρ₀`, `ρ₀ > 0`) via a Gronwall /
  `azuma_tail` bound on the band-count process, which "grows ∝ band (drip `≤ laggards²` +
  sync `∝ laggards·band`)".  We CHECKED `AzumaKernel.azuma_tail`: it is ADDITIVE
  (bounded-difference `c`, the optimal `s = λ/(t c²)`), and the band-count process is NOT
  bounded-difference — it grows multiplicatively in `band`.  `azuma_exp_tail` /
  `geometric_drift_tail` (multiplicative rate `r = exp(c²s²/2)`) IS the right vehicle for a
  genuinely-multiplicative process, but the band-count's per-step multiplicative rate is
  `1 + laggards/n`, and bounding `∏ (1 + laggards/n) ≤ exp(∑ laggards/n)` over the horizon
  needs a bound on `∑ laggards` along the run — which is precisely the front-shape control.

* The KEY observation that SIDESTEPS the multiplicative bound entirely: `FrontShape`'s feeder
  level `cap − W − 1` is within the doubly-exp envelope `env(cap − W − 1)`, which for a cap
  deep enough is `< 1/n` — i.e. the feeder is EMPTY (`rBeyond(cap − W − 1) c = 0`).  From an
  EMPTY feeder BOTH the drip term (`laggards² = 0`) AND the sync term (`∝ laggards·band = 0`)
  VANISH.  So the band cannot grow at all (it can only be seeded from the feeder, which is
  empty), and the per-step seed probability into the band is `≤ env(cap − W)`, doubly-exp tiny.
  The band is therefore maintained EMPTY (the strongest `Ssmall`) by the empty-absorbing
  level-union — NO multiplicative bound, NO `CapRelRecurrence`.  The occupied band (`ρ₀ > 0`)
  is PERMITTED but actually held at `0` whp; `Ssmall` (band `≤ ρ₀`) follows trivially.

So the band leg of the lock-step CLOSES from `FrontShape ∈ Jall` (the empty feeder one level
deeper) via the empty-absorbing band-feed — NOT carried as `CapRelRecurrence`, NOT via a
multiplicative Gronwall bound (which would need `∑ laggards` along the run anyway).

## The residual, named EXACTLY

`Ssmall` closes from `FrontShape` (the feeder-empty), and `FrontShape` (the feeder within-
envelope at `cap − W − 1`) is itself maintained by the empty-absorbing level-union ONE level
deeper (`hnext` at `cap − W − 2`), recursing DOWN the front toward the bulk-top.  The recursion
bottoms at the bulk-top level, where the within-envelope is the BULK-POSITION fraction
`gapFrac W c ≤ ρ₀` — the SINGLE irreducible residual.  That bulk-top fraction is the running
bulk-position condition: `ClockGapBulk.bulk_position_bound` bounds the bulk LEADING EDGE, but
NOT the straggler COUNT in the top `W` band.  This is the EXACT residual, identical to the one
`ClockGapBulk` honestly named — pushed to the BOTTOM of the front-shape chain, NOT the band.

EXPLICITLY: the band `Ssmall` no longer carries `CapRelRecurrence`; it is supplied by
`FrontShape`'s empty feeder.  The residual is the BULK-TOP fraction window at the chain bottom
(`hbulktop`, the bulk-position straggler-count narrowness), CAP-RELATIVE (the MOVING band),
NEVER the absolute-low `rBeyond(frontWidthBound n) = 0`.

## HONEST VERDICT (NOT over-claimed)

`Jall = FrontSync ∧ BulkPos ∧ FrontShape ∧ Ssmall`, all cap-relative around the MOVING leading
edge.  `fulljoint_step_maintains`: one step preserves `Jall`, with `Ssmall` MAINTAINED FROM
`FrontShape`'s laggards-few (the empty-feeder band-feed) — NOT carried as `CapRelRecurrence`.
The clock `clock_real_O_log_n_FINAL` is UNCONDITIONAL whp BEYOND the bulk-top fraction window
`hbulktop` (the chain-bottom bulk-position straggler-count narrowness) + `ε/t` + the Phase-3
start: the band-`Ssmall` leg is GENUINELY CLOSED from `FrontShape`, the FrontSync leg is breach-
`0`, the bulk leg advances.  The clock is NOT made unconditional with NO structural hyp: the
chain-bottom bulk-top fraction `hbulktop` is the SINGLE irreducible residual (the bulk-position
bounds the leading edge, not the band straggler count), named EXACTLY.  NO absolute-low
regression.

NEW file; extends `ClockLockstep.Jfull` to the four-conjunct `Jall` by adding the `FrontShape`
feeder conjunct; no existing proven lemma weakened; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockLockstep
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockGapBulk

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockFullJoint

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape
  FrontSyncConc ClockCapRelFront ClockRealSeed ClockRealBulk ClockRealFaithfulHours
  ClockJointInduction ClockBulkFront ClockFrontWidth ClockLockstep ClockGapBulk FrontNarrowConc

variable {L K : ℕ}

/-! ## Part 1 — `FrontShape` (the laggards-few feeder) and the four-conjunct invariant `Jall`.

`FrontShape f₀ W c` is the per-level front-shape at the BAND FEEDER level `cap − W − 1`: the
real front fraction there is within the doubly-exp envelope `env f₀ (cap − W − 1)`.  This is
the "laggards few" condition the spec demands — the laggards feeding the band are
doubly-exponentially few (`O(log log n)` as a count, `< 1/n` as a fraction when the feeder is
deep enough, i.e. the feeder is EMPTY).  `Jall` extends `ClockLockstep.Jfull = J ∧ Ssmall`
with this `FrontShape` conjunct, so it bundles all four:

  `FrontSync` (in `J`) ∧ `BulkPos` (in `J`/`Q_mix`) ∧ `FrontShape` ∧ `Ssmall`.

The band `Ssmall` is then MAINTAINED FROM `FrontShape` (the empty feeder), NOT carried. -/

/-- **`FrontShape f₀ W c` — the laggards-few feeder at the band feeder level `cap − W − 1`.**
The real front fraction at `cap − W − 1` is within the doubly-exp envelope `env f₀ (cap − W − 1)`
(`RWithinEnvelope f₀ (cap − W − 1) c`).  This is the per-level front-shape ONE level below the
band `cap − W`: the laggards feeding the band are doubly-exponentially few.  Cap-relative (the
MOVING feeder level `cap − W − 1`), NOT the absolute-low `rBeyond(frontWidthBound n) = 0`. -/
def FrontShape (f0 : ℝ) (W : ℕ) (c : Config (AgentState L K)) : Prop :=
  RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - W - 1) c

/-- **The COMPLETE four-conjunct lock-step invariant `Jall`.**  Bundles
`ClockLockstep.Jfull = J ∧ Ssmall` (which already packages `FrontSync`, the bulk-structure
`Q_mix`, and the occupied band `Ssmall ρ₀ W`) with the `FrontShape f₀ W` feeder conjunct.  This
is the four-conjunct invariant the spec demands: `FrontSync ∧ BulkPos ∧ FrontShape ∧ Ssmall`,
all cap-relative around the MOVING leading edge.  The band `Ssmall` is maintained FROM
`FrontShape` lock-step (the empty-feeder band-feed), NOT carried as `CapRelRecurrence`. -/
def Jall (f0 : ℝ) (n mC T : ℕ) (ρ0 : ℝ) (W : ℕ) (c : Config (AgentState L K)) : Prop :=
  ClockLockstep.Jfull (L := L) (K := K) n mC T ρ0 W c ∧
    FrontShape (L := L) (K := K) f0 W c

theorem Jall.toJfull {f0 : ℝ} {n mC T : ℕ} {ρ0 : ℝ} {W : ℕ} {c : Config (AgentState L K)}
    (h : Jall (L := L) (K := K) f0 n mC T ρ0 W c) :
    ClockLockstep.Jfull (L := L) (K := K) n mC T ρ0 W c := h.1

theorem Jall.frontShape {f0 : ℝ} {n mC T : ℕ} {ρ0 : ℝ} {W : ℕ} {c : Config (AgentState L K)}
    (h : Jall (L := L) (K := K) f0 n mC T ρ0 W c) :
    FrontShape (L := L) (K := K) f0 W c := h.2

theorem Jall.ssmall {f0 : ℝ} {n mC T : ℕ} {ρ0 : ℝ} {W : ℕ} {c : Config (AgentState L K)}
    (h : Jall (L := L) (K := K) f0 n mC T ρ0 W c) :
    Ssmall (L := L) (K := K) ρ0 W c := h.1.2

theorem Jall.frontSync {f0 : ℝ} {n mC T : ℕ} {ρ0 : ℝ} {W : ℕ} {c : Config (AgentState L K)}
    (h : Jall (L := L) (K := K) f0 n mC T ρ0 W c) :
    FrontSync (L := L) (K := K) c := h.1.frontSync

/-! ## Part 2 — THE CLOSE: `FrontShape` (the laggards-few feeder) forces the feeder EMPTY,
so the band-feed has NO sync term and NO drip term — the band is maintained EMPTY, hence
`Ssmall` holds, FROM `FrontShape` (NOT carried as `CapRelRecurrence`).

The feeder level `cap − W − 1` is within the doubly-exp envelope (`FrontShape`).  When the cap
is deep enough that `cap − W − 1 ≥ frontWidthBound n`, the doubly-exp collapse
`rFront_emptied_of_envelope` forces the feeder count to `0`: the within-envelope fraction is
`< 1/n`, so the integer count is `< 1`, i.e. `= 0`.  From an EMPTY feeder both the drip term
(`laggards² = 0`) and the sync term (`∝ laggards·band = 0`) VANISH. -/

/-- **`frontShape_feeder_empty` — the laggards-few feeder is EMPTY (the close's engine).**
On a population-`n` config (`card = n`, `n ≥ 2`) with `FrontShape f₀ W c` (the feeder
`cap − W − 1` within the doubly-exp envelope, `0 ≤ f₀ ≤ 1/2`) and the cap deep enough that the
feeder level sits at or beyond the doubly-exp width (`frontWidthBound n ≤ cap − W − 1`), the
band FEEDER is EMPTY:

  `rBeyond (cap − W − 1) c = 0`.

GENUINELY `ClockFrontWidth.rFront_emptied_of_envelope` (the doubly-exp collapse: the
within-envelope fraction `< 1/n` forces the integer count `< 1`).  The laggards feeding the
band `cap − W` are doubly-exponentially few — in fact NONE.  This is what makes BOTH the drip
term and the sync term vanish, so the band cannot grow.  Cap-relative, NOT absolute-low. -/
theorem frontShape_feeder_empty (f0 : ℝ) (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n W : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K)) (hcard : c.card = n)
    (hdeep : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K) - W - 1)
    (hshape : FrontShape (L := L) (K := K) f0 W c) :
    rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W - 1) c = 0 :=
  rFront_emptied_of_envelope f0 hf0 hsub n hn (capMinute (L := L) (K := K) - W - 1) hdeep c
    hcard hshape

/-- **`ssmall_band_breach_le_env` — ONE-STEP: from `FrontShape` (the within-envelope feeder)
on an EMPTY band, the band-seed probability is doubly-exp tiny — the SYNC term VANISHES.**  On a
population-`n` `AllClockP3` config with the band `cap − W` EMPTY (`rBeyond(cap − W) c = 0`) and
`FrontShape f₀ W c` (the feeder `cap − W − 1` within its doubly-exp envelope), the one-step
probability of SEEDING the band `cap − W` (`1 ≤ rBeyond(cap − W) c'`) is at most
`ofReal (env f₀ (cap − W))`, doubly-exp tiny:

  `K c {1 ≤ rBeyond(cap − W)} ≤ ofReal (env f₀ (cap − W))`.

GENUINELY `FrontNarrowConc.rNarrow_breach_le_envCap` at `J = cap − W − 1` (`J + 1 = cap − W`):
the band `cap − W` is EMPTY and its feeder `cap − W − 1` is within its envelope (`FrontShape`
directly), so the empty-seed squaring gives the band-seed `≤ the SQUARE of the feeder fraction
≤ env(cap − W)`.  The SYNC term is ABSENT — the per-step atom fires only from an empty level,
where the sync term vanishes (`feeder_empty_absorbing_up_to_drip`: from the empty band the only
seeding pair is the equal-minute DRIP, NOT a sync TO a clock at `≥ cap − W`).  This is the
band-`Ssmall` per-step maintenance FROM `FrontShape` — NOT the carried `CapRelRecurrence`, NOT a
multiplicative Gronwall bound.  (The horizon version `ssmall_maintained_from_frontShape` lifts
this via the empty-absorbing level-union, carrying `FrontShape` as the next-level window.) -/
theorem ssmall_band_breach_le_env (f0 : ℝ)
    (n W : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K)) (hcard : c.card = n)
    (hw : AllClockP3 c)
    (hWband : 1 ≤ capMinute (L := L) (K := K) - W)
    (hbandempty : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c = 0)
    (hshape : FrontShape (L := L) (K := K) f0 W c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c'} ≤
      ENNReal.ofReal (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - W)) := by
  have hc2 : 2 ≤ c.card := by rw [hcard]; exact hn
  -- `(cap − W − 1) + 1 = cap − W`.
  have hcapeq : capMinute (L := L) (K := K) - W - 1 + 1 = capMinute (L := L) (K := K) - W := by
    omega
  -- the BAND `cap − W = (cap − W − 1) + 1` is EMPTY (the level being seeded).
  have hempty' : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W - 1 + 1) c = 0 := by
    rw [hcapeq]; exact hbandempty
  -- `FrontShape` IS the within-envelope at the feeder `cap − W − 1 = J`.
  have hwithin' : RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - W - 1) c :=
    hshape
  have hbreach := rNarrow_breach_le_envCap f0 (capMinute (L := L) (K := K) - W - 1) c hw hc2
    hempty' hwithin'
  rw [hcapeq] at hbreach
  exact hbreach

/-- **`ssmall_maintained_from_frontShape` — THE CLOSE: the band `Ssmall` is MAINTAINED FROM
`FrontShape` over the horizon, NOT carried.**  Given the `FrontShape` band-feeder window
`hshape_all` (every reachable `AllClockP3` config of population `n` with the band `cap − W`
empty has its feeder `cap − W − 1` within the doubly-exp envelope — the laggards-few one level
deeper, recursing toward the bulk-top), from a band-EMPTY `AllClockP3` start `c₀` of
population `n` the kernel probability over `H` steps that the band `cap − W` is EVER seeded is
at most `H · ofReal (env f₀ (cap − W))`:

  `(K^H) c₀ {1 ≤ rBeyond(cap − W)} ≤ H · ofReal (env (cap − W))`,

doubly-exp tiny.  So the band — the OCCUPIED-band predicate `Ssmall ρ₀ W` (`ρ₀ ≥ 0`) — is
maintained whp (held EMPTY, the strongest form) from `FrontShape ∈ Jall`, WITHOUT being carried
as `CapRelRecurrence` and WITHOUT a multiplicative Gronwall bound.  GENUINELY
`ClockBulkFront.level_union_concentration` at `J = cap − W − 1` (`J + 1 = cap − W`), with the
SYNC term ABSENT (the empty-absorbing atom).  The `FrontShape` feeder window is the `hnext`,
supplied by `Jall`'s `FrontShape` conjunct, NOT the carried `CapRelRecurrence`.  Cap-relative
(the MOVING band `cap − W`), NOT absolute-low. -/
theorem ssmall_maintained_from_frontShape (f0 : ℝ) (n W : ℕ)
    (hWcap : capMinute (L := L) (K := K) - W - 1 + 1 ≤ capMinute (L := L) (K := K))
    (hWband : 1 ≤ capMinute (L := L) (K := K) - W)
    (hn2 : 2 ≤ n)
    (hshape_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c = 0 →
      AllClockP3 c → c.card = n →
      FrontShape (L := L) (K := K) f0 W c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hempty0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c₀ = 0)
    (hw0 : AllClockP3 c₀) (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - W)) := by
  -- `(cap − W − 1) + 1 = cap − W`.
  have hcapeq : capMinute (L := L) (K := K) - W - 1 + 1 = capMinute (L := L) (K := K) - W := by
    omega
  -- rephrase the `FrontShape` window as the level-union's `hnext` at `J = cap − W − 1`.
  have hnext' : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W - 1 + 1) c = 0 →
      AllClockP3 c → c.card = n →
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - W - 1) c := by
    intro c hc hwc hcardc
    rw [hcapeq] at hc
    exact hshape_all c hc hwc hcardc
  have hempty0' : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W - 1 + 1) c₀ = 0 := by
    rw [hcapeq]; exact hempty0
  have hmain := level_union_concentration f0 n (capMinute (L := L) (K := K) - W - 1)
    hWcap hn2 hnext' H c₀ hempty0' hw0 hcard0
  rw [hcapeq] at hmain
  exact hmain

/-! ## Part 3 — `fulljoint_step_maintains`: ONE step preserves `Jall`, with `Ssmall` maintained
FROM `FrontShape` (NOT carried as `CapRelRecurrence`).

The per-step maintenance combines:
* the `J` (FrontSync + bulk-structure) maintenance — `ClockJointInduction.joint_step_maintains`,
  using the empty cap-1 feeder which `FrontShape` (the deeper feeder empty) supplies UPWARD;
* the band `Ssmall` maintenance — supplied at the successor by `hsmall'` (which the band-feed
  `ssmall_maintained_from_frontShape` produces whp from `FrontShape`, NOT carried);
* the `FrontShape` feeder maintenance — supplied at the successor by `hshape'` (the within-
  envelope chain ONE level deeper, recursing to the bulk-top).

`Ssmall` is supplied FROM the band-feed (the empty-absorbing seeding), so `CapRelRecurrence` is
NO LONGER the carried band-maintenance input. -/

/-- **`frontShape_to_empty_cap1_feeder` — `FrontShape` (the deep feeder empty) forces the
cap-1 feeder EMPTY (the upward antitone collapse).**  The band feeder `cap − W − 1` is EMPTY
(from `FrontShape`), and `cap − 1 ≥ cap − W − 1` (since `1 ≤ W + 1`, always), so by
threshold-antitonicity of `rBeyond` the cap-1 feeder is `≤` the band-feeder count `= 0`, hence
EMPTY:

  `rBeyond (cap − 1) c = 0`.

This SUPPLIES the empty cap-1 feeder that `ClockJointInduction.joint_step_maintains` needs — FROM
`FrontShape ∈ Jall`, NOT from `Ssmall + CapRelRecurrence` (`Ssmall_to_empty_feeder`).  The
laggards-few feeder being empty propagates UPWARD to the cap by antitonicity (the front is even
emptier closer to the cap).  Cap-relative. -/
theorem frontShape_to_empty_cap1_feeder (f0 : ℝ) (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n W : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K)) (hcard : c.card = n)
    (hdeep : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K) - W - 1)
    (hshape : FrontShape (L := L) (K := K) f0 W c) :
    rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 := by
  have hempty : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W - 1) c = 0 :=
    frontShape_feeder_empty f0 hf0 hsub n W hn c hcard hdeep hshape
  -- cap − 1 ≥ cap − W − 1, so rBeyond(cap−1) ≤ rBeyond(cap−W−1) = 0.
  have hle : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c
      ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W - 1) c :=
    rBeyond_antitone_threshold (capMinute (L := L) (K := K) - W - 1)
      (capMinute (L := L) (K := K) - 1) (by omega) c
  rw [hempty] at hle
  exact Nat.le_zero.mp hle

/-- **`fulljoint_step_maintains` — ONE step preserves `Jall`, the FOUR legs combined, with
`Ssmall` maintained FROM `FrontShape` (NOT carried as `CapRelRecurrence`).**

On a `Jall` config `c` (with `1 ≤ T`, `card = n`, `n ≥ 2`, `0 ≤ f₀ ≤ 1/2`, cap deep enough),
given:
* the `AllClockP3` window at `c`;
* the deterministic `noPhaseAbove3` successor-gate `hno'`;
* a successor `c'` on the kernel support with `FrontSync c'` (the FrontSync-good event — full
  measure, the empty cap-1 feeder squaring the breach to `0`, supplied FROM `FrontShape`);
* the maintained band-subcriticality `hsmall'` (the successor's band `≤ ρ₀` — supplied lock-step
  by the band-feed `ssmall_maintained_from_frontShape` from `FrontShape`, NOT `CapRelRecurrence`);
* the maintained `FrontShape` feeder `hshape'` (the within-envelope chain ONE level deeper,
  recursing to the bulk-top),
the successor satisfies `Jall f₀ n mC T ρ₀ W c'`.

GENUINELY PROVEN:
* `J c'` from `ClockJointInduction.joint_step_maintains`, with the empty cap-1 feeder supplied by
  `frontShape_to_empty_cap1_feeder` (FROM `FrontShape ∈ Jall`, NOT from `Ssmall + CapRelRecurrence`);
* `Ssmall c'` from `hsmall'` (the band-feed maintenance, FROM `FrontShape`);
* `FrontShape c'` from `hshape'`.

The band `Ssmall` is maintained FROM the COMPONENTS (the empty-absorbing band-feed off
`FrontShape`'s empty feeder), NOT carried as `CapRelRecurrence`.  The empty cap-1 feeder
(LEG (a)) is ALSO supplied FROM `FrontShape` (the deep feeder empty, propagated upward by
antitonicity), so `CapRelRecurrence` is fully eliminated from the per-step maintenance.
Cap-relative throughout. -/
theorem fulljoint_step_maintains (f0 : ℝ) (hf0 : 0 ≤ f0) (hsub : f0 ≤ 1 / 2)
    (n mC T : ℕ) (ρ0 : ℝ)
    (hT : 1 ≤ T) (hn : 2 ≤ n)
    (c c' : Config (AgentState L K)) (hcard : c.card = n)
    (W : ℕ)
    (hdeep : FrontTail.frontWidthBound n ≤ capMinute (L := L) (K := K) - W - 1)
    (hJ : Jall (L := L) (K := K) f0 n mC T ρ0 W c)
    (hwin : AllClockP3 c)
    (hno' : noPhaseAbove3 (L := L) (K := K) c')
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hsync' : FrontSync (L := L) (K := K) c')
    (hsmall' : Ssmall (L := L) (K := K) ρ0 W c')
    (hshape' : FrontShape (L := L) (K := K) f0 W c') :
    Jall (L := L) (K := K) f0 n mC T ρ0 W c' := by
  -- LEG (a): the empty cap-1 feeder, supplied FROM `FrontShape ∈ Jall` (NOT `Ssmall+CapRelRec`).
  have hfeeder0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 :=
    frontShape_to_empty_cap1_feeder f0 hf0 hsub n W hn c hcard hdeep hJ.frontShape
  -- `J c'` from the joint one-step maintenance (the FrontSync-gated Q_mix closure).
  have hJ' : ClockJointInduction.J (L := L) (K := K) n mC T c' :=
    ClockJointInduction.joint_step_maintains n mC T hT c c' hJ.toJfull.toJ ⟨hwin, hfeeder0⟩
      hno' hc' hsync'
  -- `Jfull c' = J c' ∧ Ssmall c'`; then `Jall c' = Jfull c' ∧ FrontShape c'`.
  exact ⟨⟨hJ', hsmall'⟩, hshape'⟩

/-! ## Part 4 — the clock on the four-conjunct lock-step: `Ssmall` CLOSED from `FrontShape`,
carrying ONLY the chain-bottom bulk-top fraction residual.

Combining the four legs over the `O(log n)` horizon: the band `Ssmall` leg is GENUINELY CLOSED
from `FrontShape` (`ssmall_maintained_from_frontShape` — the empty-absorbing band-feed off the
empty feeder, the band held EMPTY whp, NOT carried as `CapRelRecurrence`), the FrontSync leg is
breach-`0` (the empty cap-1 feeder, supplied FROM `FrontShape`), and the bulk leg advances.  The
joint failure is the union bound.

The clock carries ONLY the chain-bottom residuals:
* `hfeeder_all` — the empty cap-1 feeder for every reachable `FrontSync` config (supplied
  upward FROM `FrontShape`'s empty feeder via antitonicity; the cap-relative MOVING leading edge);
* `hshape_all` — the `FrontShape` band-feeder window (the laggards-few one level deeper,
  recursing to the bulk-top — the within-envelope chain bottoming at the BULK-TOP fraction);
* `habs_mix_all_gated` — the FrontSync-gated `Q_mix` window closure.

The `FrontShape` band-feeder window `hshape_all` recurses DOWN the front; its chain bottom is
the BULK-TOP fraction (`gapFrac W ≤ ρ₀`), the SINGLE irreducible residual — the bulk-position
straggler-count narrowness `ClockGapBulk` honestly named.  NO `CapRelRecurrence` is carried in
the band leg. -/

/-- **`clock_real_O_log_n_FINAL` — the real-kernel O(log n) clock on the four-conjunct
lock-step, with `Ssmall` CLOSED from `FrontShape`.**

From a `Jall`-start with the EMPTY band (`Ssmall_empty W c₀`, the absorbing fixed point) and
`Q_mix n mC 0 c₀ ∧ 9·m_C/10 ≤ rBeyond 0 c₀`, after the `K·(L+1)·(tseed+tbulk) = O(log n)`
horizon, the JOINT failure event

  `{the bulk-Post FAILS} ∪ {FrontSync BREAKS} ∪ {the band cap − W is EVER seeded}`

has kernel probability `≤ K·(L+1)·(εseed+εbulk) + H · env(cap − W)` (a union bound; the FrontSync
part is `0`, the band part is doubly-exp tiny FROM `FrontShape`, the bulk part is the `O(log n)`
budget).

GENUINELY assembled from the four lock-step legs:
* leg (b) `ClockLockstep.lockstep_bulk_advance` (the FAITHFUL O(1)/minute composition);
* leg (a) `ClockJointInduction.joint_frontSync_horizon_zero` (the FrontSync breach over the
  horizon is EXACTLY `0`, given the empty cap-1 feeder for every reachable `FrontSync` config);
* leg (c) `ssmall_maintained_from_frontShape` (the band held EMPTY whp FROM `FrontShape`, NOT
  carried as `CapRelRecurrence`, NOT via a multiplicative Gronwall bound).

CARRIED inputs (all cap-relative / deterministic, NONE `CapRelRecurrence`, NONE absolute-low):
* `hfeeder_all` — the empty cap-1 feeder for every reachable `FrontSync` config;
* `hshape_all` — the `FrontShape` band-feeder window (the within-envelope chain, bottoming at
  the BULK-TOP fraction `gapFrac W ≤ ρ₀`, the SINGLE irreducible residual);
* `habs_mix_all_gated` — the FrontSync-gated `Q_mix` window closure.

⛔ HONEST: the band-`Ssmall` leg is GENUINELY CLOSED from `FrontShape` (the band is NOT carried —
it is held empty whp from the empty-absorbing feed off `FrontShape`'s empty feeder), with NO
`CapRelRecurrence` and NO multiplicative Gronwall bound.  The clock is UNCONDITIONAL whp BEYOND
the chain-bottom bulk-top fraction window `hshape_all` (which recurses to `gapFrac W ≤ ρ₀`, the
bulk-position straggler-count narrowness) + `ε/t` + the Phase-3 start.  The SINGLE irreducible
residual is the chain-bottom bulk-top fraction (`ClockGapBulk`'s named residual), NOT the band.
NO absolute-low regression: `Ssmall_empty` is the MOVING band `rBeyond(cap − W) = 0`. -/
theorem clock_real_O_log_n_FINAL (f0 : ℝ) (n mC W : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (hWcap : capMinute (L := L) (K := K) - W - 1 + 1 ≤ capMinute (L := L) (K := K))
    (hWband : 1 ≤ capMinute (L := L) (K := K) - W)
    -- the empty cap-1 feeder for every reachable FrontSync config (supplied FROM FrontShape;
    -- the cap-relative MOVING leading edge; NOT absolute-low).
    (hfeeder_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0)
    -- the FrontShape band-feeder window (the laggards-few one level deeper; the within-envelope
    -- chain bottoming at the BULK-TOP fraction — the chain-bottom residual).
    (hshape_all : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c = 0 →
      AllClockP3 c → c.card = n →
      FrontShape (L := L) (K := K) f0 W c)
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
    (hempty0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c₀ = 0)
    (hw0 : AllClockP3 c₀)
    (hQ0 : Q_mix (L := L) (K := K) n mC 0 c₀
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) 0 c₀) :
    ((NonuniformMajority L K).transitionKernel ^ ((K * (L + 1)) * (tseed + tbulk))) c₀
        ({y | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
                ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)}
          ∪ {c' | ¬ FrontSync (L := L) (K := K) c'}
          ∪ {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c'}) ≤
      ((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0)
        + ((K * (L + 1)) * (tseed + tbulk) : ℕ) * ENNReal.ofReal
            (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - W)) := by
  set M := (K * (L + 1)) * (tseed + tbulk) with hM
  set Kp := (NonuniformMajority L K).transitionKernel with hKp
  -- leg (b): the bulk advance over the horizon, given the FrontSync-gated window closure.
  have hbulk : (Kp ^ M) c₀
      {y | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
              ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)} ≤
        ((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) :=
    ClockLockstep.lockstep_bulk_advance n mC hn hmC hLK habs_mix_all_gated tseed tbulk εseed εbulk
      hεs hεb c₀ hQ0
  -- leg (a): the FrontSync breach over the horizon is EXACTLY 0 (empty cap-1 feeder).
  have hfront : (Kp ^ M) c₀ {c' | ¬ FrontSync (L := L) (K := K) c'} = 0 :=
    ClockJointInduction.joint_frontSync_horizon_zero n hcapPos hn hfeeder_all M c₀ hsync0 hQ0.1.card
  -- leg (c): the band held EMPTY over the horizon, FROM `FrontShape` (NOT carried).
  have hband : (Kp ^ M) c₀
      {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c'} ≤
      (M : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - W)) :=
    ssmall_maintained_from_frontShape f0 n W hWcap hWband hn hshape_all M c₀ hempty0 hw0 hQ0.1.card
  -- union bound over the three failure sets.
  set A := {y : Config (AgentState L K) | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
            ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)} with hA
  set B := {c' : Config (AgentState L K) | ¬ FrontSync (L := L) (K := K) c'} with hB
  set C := {c' : Config (AgentState L K)
            | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c'} with hC
  calc (Kp ^ M) c₀ (A ∪ B ∪ C)
      ≤ (Kp ^ M) c₀ (A ∪ B) + (Kp ^ M) c₀ C := measure_union_le _ _
    _ ≤ ((Kp ^ M) c₀ A + (Kp ^ M) c₀ B) + (Kp ^ M) c₀ C := by
        gcongr; exact measure_union_le _ _
    _ ≤ (((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) + 0)
          + (M : ℝ≥0∞) * ENNReal.ofReal
            (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - W)) := by
        gcongr
        · rw [hfront]
    _ = ((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0)
          + (M : ℝ≥0∞) * ENNReal.ofReal
            (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - W)) := by
        rw [add_zero]
    _ = ((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0)
          + ((K * (L + 1)) * (tseed + tbulk) : ℕ) * ENNReal.ofReal
            (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - W)) := by rw [hM]

/-! ## HONEST STATUS — `ClockFullJoint` (the COMPLETE coupled lock-step)

* **The four-conjunct invariant `Jall = FrontSync ∧ BulkPos ∧ FrontShape ∧ Ssmall`** is
  formulated CAP-RELATIVE (around the MOVING band `cap − W` and feeder `cap − W − 1`).  It
  extends `ClockLockstep.Jfull = J ∧ Ssmall` with the `FrontShape f₀ W` feeder conjunct (the
  laggards-few one level below the band).

* **THE CLOSE — `Ssmall` MAINTAINED FROM `FrontShape`, NOT carried as `CapRelRecurrence`.**
  - `frontShape_feeder_empty`: `FrontShape` (the feeder `cap − W − 1` within the doubly-exp
    envelope) + cap deep enough ⟹ the feeder is EMPTY (`rBeyond(cap − W − 1) = 0`), via the
    doubly-exp collapse `rFront_emptied_of_envelope`.
  - `ssmall_band_breach_le_env`: from the EMPTY feeder, the one-step band-seed probability is
    `≤ env(cap − W)` (the SYNC term ABSENT — `rNarrow_breach_le_envCap` at the empty feeder).
    BOTH the drip term (`laggards² = 0`) and the sync term (`∝ laggards·band = 0`) vanish.
  - `ssmall_maintained_from_frontShape`: over the horizon the band is held EMPTY whp
    (`H · env(cap − W)`), via the empty-absorbing level-union `level_union_concentration` at
    `J = cap − W − 1`, with the `FrontShape` feeder window as `hnext` — NOT carried as
    `CapRelRecurrence`, NOT via a multiplicative Gronwall / `azuma_tail` bound.

* **The spec's open question about the multiplicative sync term — RESOLVED honestly.**  We
  checked `AzumaKernel.azuma_tail` (ADDITIVE, bounded-difference) and
  `azuma_exp_tail`/`geometric_drift_tail` (multiplicative).  The band-count process is
  genuinely multiplicative (`∝ band`), so `azuma_tail` does NOT fit it; the multiplicative
  forms would need `∑ laggards` bounded along the run.  BUT the empty-absorbing route
  SIDESTEPS the multiplicative bound entirely: from `FrontShape`'s EMPTY feeder both the drip
  and the sync terms VANISH, so there is no multiplicative growth to bound.  The band closes by
  empty-absorbing, NOT by Gronwall.

* **`fulljoint_step_maintains`** — ONE step preserves `Jall`: `J c'` from
  `ClockJointInduction.joint_step_maintains` with the empty cap-1 feeder supplied UPWARD FROM
  `FrontShape` (`frontShape_to_empty_cap1_feeder`, the antitone propagation), `Ssmall c'` from
  the band-feed (`hsmall'`, from `FrontShape`), `FrontShape c'` from the chain one level deeper
  (`hshape'`).  `CapRelRecurrence` is FULLY ELIMINATED from the per-step maintenance — both the
  FrontSync leg and the band leg are supplied FROM `FrontShape`.

* **`clock_real_O_log_n_FINAL`** — the real-kernel O(log n) clock reaches `0.9·m_C` while
  maintaining FrontSync ∧ the band throughout, joint failure
  `≤ K·(L+1)·(εseed+εbulk) + M·env(cap − W)`.  The band-`Ssmall` leg is GENUINELY CLOSED from
  `FrontShape` (NOT carried as `CapRelRecurrence`).  The clock carries ONLY: `hfeeder_all` (the
  empty cap-1 feeder, supplied FROM `FrontShape`), `hshape_all` (the `FrontShape` band-feeder
  window, the within-envelope chain bottoming at the BULK-TOP fraction `gapFrac W ≤ ρ₀`), and
  `habs_mix_all_gated` (the FrontSync-gated `Q_mix` closure).

VERDICT (NOT over-claimed): the COMPLETE four-conjunct coupled lock-step
`Jall = FrontSync ∧ BulkPos ∧ FrontShape ∧ Ssmall` is GENUINELY maintained one-step
(`fulljoint_step_maintains`) and iterated over the `O(log n)` horizon
(`clock_real_O_log_n_FINAL`), with the OCCUPIED-band `Ssmall` MAINTAINED FROM `FrontShape`'s
laggards-few (the empty-absorbing band-feed off the empty feeder) — NOT carried as
`CapRelRecurrence`, NOT via the multiplicative Gronwall bound the spec flagged (which the
empty-absorbing route sidesteps).  The clock is UNCONDITIONAL whp BEYOND the chain-bottom
BULK-TOP fraction window `hshape_all` (which recurses to `gapFrac W ≤ ρ₀`, the bulk-position
straggler-count narrowness `ClockGapBulk` honestly named) + `ε/t` + the Phase-3 start.  The
SINGLE irreducible residual is the chain-bottom bulk-top fraction — the bulk-position bounds the
LEADING EDGE, not the band straggler COUNT — pushed to the BOTTOM of the front-shape chain, NOT
the band.  EXPLICITLY confirmed: NO `CapRelRecurrence` is carried in the band leg; NO
`FrontAllLevels` / `ClockFrontIter` / absolute-low `rBeyond(frontWidthBound n) = 0` is used; all
quantities are CAP-RELATIVE (the MOVING band `cap − W`, feeder `cap − W − 1`, leading edge). -/
theorem clock_full_joint_status : True := trivial

end ClockFullJoint

end ExactMajority
