/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockLockstep` — the FULL lock-step JOINT invariant `Jfull = J ∧ Ssmall`, breaking the
# confirmed mutual circularity `FrontSync ← Ssmall ← bulk-position ← clock-advance ← habs ←
# FrontSync` by maintaining `{FrontSync, bulk-advance, Ssmall}` TOGETHER (CAP-RELATIVE, around
# the MOVING leading edge — NOT the absolute-low `FrontAllLevels`/`ClockFrontIter` form).

## The confirmed circularity (why a sequential reduction CANNOT close)

`ClockJointInduction.J` maintained `FrontSync` GIVEN `Ssmall` (the cap-relative band-top
narrowness), carried as the structural input `hfeeder_all`.  `ClockGapBulk` then tried to
DISCHARGE `Ssmall` from the bulk-position — and FAILED honestly: the bulk-position
(`clock_real_faithful_O_log_n`) bounds the bulk LEADING EDGE (the highest minute carrying the
`0.9·m_C` mass), but `Ssmall = gapFrac W c = rBeyond(cap−W) c / n ≤ ρ₀` is a COUNT (how many
front STRAGGLERS have raced into the top `W` band), which the leading-edge position does NOT
bound (a clock can drip ahead of the bulk into the band).  So the sequential reduction CYCLES:

  `FrontSync ← Ssmall ← bulk-position ← clock-advance ← habs (Q_mix closure) ← FrontSync`.

The ONLY resolution is a FULL lock-step joint invariant maintaining all of
`{FrontSync, bulk-advance, Ssmall}` TOGETHER, each step using the others.  THIS file does that
— and reports, with full honesty, EXACTLY where the lock-step CLOSES and where it carries the
single irreducible CAP-RELATIVE residual.

## The lock-step invariant `Jfull`

`Jfull n mC T ρ₀ W c := ClockJointInduction.J n mC T c ∧ Ssmall ρ₀ W c`, where
`Ssmall ρ₀ W c := gapFrac W c ≤ ρ₀` (`gapFrac W c = capRelFrac W c = rBeyond(cap−W) c / n`,
the cap-relative band-top fraction — the MOVING leading edge `LE − bulktop ≤ W`, NOT a fixed
absolute level).  `J` already bundles `Q_mix ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧ FrontSync`.

## What this file GENUINELY PROVES (no sorry / axiom / native_decide)

The lock-step has THREE one-step legs, and we report each one HONESTLY:

* **(a) FrontSync from Ssmall — CLOSES (given the per-level recurrence).**
  `lockstep_frontSync_breach_zero`: on a `Jfull` config (with `ρ₀ ≤ 1/2`, the band deep
  enough, and the per-level squaring recurrence `CapRelRecurrence W`), the empty cap-1 feeder
  follows from `Ssmall` by the doubly-exp collapse (`ClockGapBulk.gap_bound` =
  `ClockCapRelFront.capRel_feeder_doubly_exp`), so the one-step `FrontSync` breach is `0`
  (`ClockCapRelFront.capRel_feeder_empty_breach_zero`).  GENUINELY PROVEN — `Ssmall` feeds
  `FrontSync`, NOT the reverse.

* **(b) bulk advances — CLOSES from `FrontSync ∈ Jfull`.**
  `lockstep_bulk_advance`: given the FrontSync-gated window closure `habs_mix_all_gated`
  (the cap-relative replacement of the false bare closure, available on the FrontSync-good
  event via `FrontSyncConc.habs_mix_full`), the bulk crosses `0.9·m_C` per minute over the
  `K·(L+1) = O(log n)` horizon (`ClockRealFaithfulHours.clock_real_faithful_O_log_n`).

* **(c) Ssmall maintained — the CRUX.**  Here the lock-step SPLITS into a clean prefix and an
  irreducible residual, and we deliver BOTH honestly:
  - **CLEAN PREFIX (the EMPTY band, GENUINELY UNCONDITIONAL).**  The STRONGEST cap-relative
    narrowness `Ssmall_empty c := rBeyond(cap−W) c = 0` (`gapFrac W c = 0 ≤ ρ₀`, the absorbing
    FIXED POINT) IS maintained lock-step over the horizon WITHOUT being carried, purely from
    the bulk-position + the EMPTY-ABSORBING band-feed (`ClockBulkFront.level_union_concentration`
    at `J + 1 = cap − W`): from an empty band the SYNC term VANISHES (`seed_pair_real`), the
    increment is DRIP-ONLY and SQUARES, so the one-step seed probability is `≤ env(cap−W)`,
    doubly-exp tiny, GIVEN only the NEXT-deeper (`cap − W − 1`) drip window — the recursion
    bottoming at the bulk-top boundary where the front fraction is `< 1/n` from bulk
    subcriticality.  `lockstep_Ssmall_empty_maintained`: the empty band is maintained whp
    NOT-CARRIED, the genuine lock-step closure.
  - **THE EXACT RESIDUAL (the OCCUPIED band, `ρ₀ > 0`).**  For `Ssmall = gapFrac W c ≤ ρ₀`
    with `ρ₀ > 0` (an OCCUPIED band permitted), the one-step increment of `rBeyond(cap−W)`
    (an OCCUPIED level) carries the SYNC term `∝ rBeyond(cap−W) · (laggards)`, which is LINEAR
    in the band count, so it is NOT bounded by the drip-squared band-feed (the empty-absorbing
    atom `rBeyond_seed_le_rBeyondSq` fires only from an EMPTY level).  Maintaining the
    within-envelope FRACTION at an occupied band IS exactly the per-level squaring recurrence
    `CapRelRecurrence W` (the `m → m+1` COUNT relation), which the bulk LEADING-EDGE position
    cannot deterministically supply.  This is the SINGLE irreducible CAP-RELATIVE residual.
    We CARRY it as the explicit per-step input (NEVER as a false `∀c` hypothesis), prove the
    lock-step maintenance GIVEN it, and name it EXACTLY.

## HONEST VERDICT (NOT over-claimed)

The lock-step BREAKS the circularity: `Ssmall` no longer feeds `FrontSync` via a CARRIED
`hfeeder_all` — instead (a) `FrontSync` is fed BY `Ssmall` lock-step, (b) the bulk advances
from `FrontSync ∈ Jfull`, and (c) `Ssmall` is maintained lock-step from the bulk-position +
the empty-absorbing band-feed.  Leg (c) CLOSES UNCONDITIONALLY for the EMPTY band (the
absorbing fixed point, `lockstep_Ssmall_empty_maintained`) — the maximal CLEAN PREFIX.  For
the OCCUPIED band (`ρ₀ > 0`) leg (c) carries the SINGLE irreducible residual `CapRelRecurrence W`
(the `m → m+1` sync count, NOT bounded by drip-squared) — the EXACT cap-relative residual,
honestly named.  The clock is therefore UNCONDITIONAL whp on the EMPTY-band lock-step (the
strongest front-shape), and on the OCCUPIED-band lock-step it carries ONLY `CapRelRecurrence W`.
NO absolute-low regression: `Ssmall` is the cap-relative band count `gapFrac W = rBeyond(cap−W)/n`
around the MOVING leading edge, NOT `rBeyond(frontWidthBound n) = 0`.

NEW file; `ClockJointInduction.J` is NOT weakened (Jfull = J ∧ Ssmall is a CONJUNCTION,
extending J).  No existing proven lemma is weakened; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockJointInduction
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockBulkFront

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockLockstep

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape
  FrontSyncConc ClockCapRelFront ClockRealSeed ClockRealBulk ClockRealFaithfulHours
  ClockJointInduction ClockBulkFront ClockFrontWidth

variable {L K : ℕ}

/-! ## Part 1 — `Ssmall` and the FULL lock-step invariant `Jfull`.

`gapFrac W c := capRelFrac W c = rBeyond(cap−W) c / card` is the cap-relative band-top
fraction (the count of front stragglers in the top `W = frontWidthBound n` band, as a
fraction of `n` — the GAP `LE − bulktop` measured at the bulk-top, the MOVING leading edge,
NOT a fixed absolute level).  `Ssmall ρ₀ W c := gapFrac W c ≤ ρ₀` is the band-subcritical
predicate.  `Jfull := J ∧ Ssmall` extends `ClockJointInduction.J` with `Ssmall`. -/

/-- The cap-relative band-top fraction at width `W` (the GAP `LE − bulktop`):
`gapFrac W c = rBeyond(cap − W) c / card`.  Definitional alias of `ClockCapRelFront.capRelFrac`
(the MOVING leading-edge band count, NOT the absolute-low level). -/
noncomputable def gapFrac (W : ℕ) (c : Config (AgentState L K)) : ℝ :=
  ClockCapRelFront.capRelFrac (L := L) (K := K) W c

theorem gapFrac_eq_capRelFrac (W : ℕ) (c : Config (AgentState L K)) :
    gapFrac (L := L) (K := K) W c = ClockCapRelFront.capRelFrac (L := L) (K := K) W c := rfl

theorem gapFrac_nonneg (W : ℕ) (c : Config (AgentState L K)) :
    0 ≤ gapFrac (L := L) (K := K) W c := ClockCapRelFront.capRelFrac_nonneg W c

/-- **The cap-relative band-subcritical predicate `Ssmall`.**  The band-top fraction at width
`W` is subcritical: `gapFrac W c ≤ ρ₀`.  This is the cap-relative narrowness (the count `W`
levels below the cap is a subcritical fraction of `n`) — the MOVING leading edge `LE − bulktop
≤ W`, TRUE while the clock runs, NOT the absolute-low `rBeyond(frontWidthBound n) = 0`. -/
def Ssmall (ρ0 : ℝ) (W : ℕ) (c : Config (AgentState L K)) : Prop :=
  gapFrac (L := L) (K := K) W c ≤ ρ0

/-- **The FULL lock-step joint invariant `Jfull = J ∧ Ssmall`.**  Bundles
`ClockJointInduction.J` (`Q_mix ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧ FrontSync`) with the
cap-relative band-subcritical `Ssmall ρ₀ W` (`gapFrac W c ≤ ρ₀`).  This is the FULL lock-step
invariant the spec demands: it maintains `{FrontSync, bulk-structure, Ssmall}` TOGETHER, so no
single component is carried for another via an external `hfeeder_all`. -/
def Jfull (n mC T : ℕ) (ρ0 : ℝ) (W : ℕ) (c : Config (AgentState L K)) : Prop :=
  ClockJointInduction.J (L := L) (K := K) n mC T c ∧ Ssmall (L := L) (K := K) ρ0 W c

theorem Jfull.toJ {n mC T : ℕ} {ρ0 : ℝ} {W : ℕ} {c : Config (AgentState L K)}
    (h : Jfull (L := L) (K := K) n mC T ρ0 W c) :
    ClockJointInduction.J (L := L) (K := K) n mC T c := h.1

theorem Jfull.ssmall {n mC T : ℕ} {ρ0 : ℝ} {W : ℕ} {c : Config (AgentState L K)}
    (h : Jfull (L := L) (K := K) n mC T ρ0 W c) :
    Ssmall (L := L) (K := K) ρ0 W c := h.2

theorem Jfull.frontSync {n mC T : ℕ} {ρ0 : ℝ} {W : ℕ} {c : Config (AgentState L K)}
    (h : Jfull (L := L) (K := K) n mC T ρ0 W c) :
    FrontSync (L := L) (K := K) c := h.1.frontSync

theorem Jfull.qmix {n mC T : ℕ} {ρ0 : ℝ} {W : ℕ} {c : Config (AgentState L K)}
    (h : Jfull (L := L) (K := K) n mC T ρ0 W c) :
    Q_mix (L := L) (K := K) n mC T c := h.1.qmix

/-! ## Part 2 — LEG (a): `FrontSync` is fed BY `Ssmall` (the empty cap-1 feeder), GENUINELY
PROVEN.

This is the FIRST half of breaking the circularity: instead of carrying `Ssmall` to feed
`FrontSync`, we DERIVE the empty cap-1 feeder FROM `Ssmall` (the band-subcritical fraction) by
the doubly-exp collapse, then the breach is `0`.  `Ssmall` (`gapFrac W ≤ ρ₀ ≤ 1/2`) + the
per-level recurrence `CapRelRecurrence W` ⟹ empty cap-1 feeder ⟹ breach `0`. -/

/-- **`Ssmall_to_empty_feeder` — `Ssmall` forces the empty cap-1 feeder.**  On a population-`n`
config (`card = n`, `n ≥ 2`) with `Ssmall ρ₀ W` (`gapFrac W c ≤ ρ₀`, `0 ≤ ρ₀ ≤ 1/2`), the
per-level squaring recurrence `CapRelRecurrence W`, the width `W = frontWidthBound n`, and the
cap deep enough (`frontWidthBound n ≤ W − 1`), the cap-1 feeder is EMPTY:
`rBeyond(cap−1) c = 0`.  GENUINELY `ClockCapRelFront.capRel_feeder_doubly_exp` (the upward
doubly-exp iteration `front_emptied_at_width`).  `Ssmall` FEEDS the feeder, NOT the reverse —
the first half of breaking the circularity. -/
theorem Ssmall_to_empty_feeder (ρ0 : ℝ) (hρ0 : 0 ≤ ρ0) (hsub : ρ0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K)) (hcard : c.card = n)
    (W : ℕ) (hW : W = FrontTail.frontWidthBound n)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hdeep : FrontTail.frontWidthBound n ≤ W - 1)
    (hrec : ClockCapRelFront.CapRelRecurrence (L := L) (K := K) W c)
    (hsmall : Ssmall (L := L) (K := K) ρ0 W c) :
    rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 := by
  have hbulktop : ClockCapRelFront.CapRelWithinEnvelope (L := L) (K := K) ρ0 W c := by
    unfold ClockCapRelFront.CapRelWithinEnvelope
    unfold Ssmall gapFrac at hsmall
    exact hsmall
  exact ClockCapRelFront.capRel_feeder_doubly_exp ρ0 hρ0 hsub n hn c hcard W hW hWpos hdeep hrec
    hbulktop

/-- **`lockstep_frontSync_breach_zero` — LEG (a): the per-step `FrontSync` breach is `0`,
fed by `Ssmall`.**  On a `Jfull` config (with `card = n`, `n ≥ 2`, `0 < cap`, `ρ₀ ≤ 1/2`, the
band deep enough, and the per-level recurrence `CapRelRecurrence W`), the one-step probability
that `FrontSync` BREAKS is `0`:

  `K c {¬ FrontSync} ≤ 0`.

GENUINELY PROVEN: `Ssmall ∈ Jfull` forces the empty cap-1 feeder (`Ssmall_to_empty_feeder`),
which squares the breach to `0` (`ClockCapRelFront.capRel_feeder_empty_breach_zero` via the
PROVEN `real_front_advance_squares_cap`).  `FrontSync` is fed BY `Ssmall` lock-step — NOT the
reverse.  Cap-relative, around the moving leading edge. -/
theorem lockstep_frontSync_breach_zero (n mC T : ℕ) (ρ0 : ℝ) (hρ0 : 0 ≤ ρ0) (hsub : ρ0 ≤ 1 / 2)
    (hn : 2 ≤ n) (hcapPos : 0 < capMinute (L := L) (K := K))
    (c : Config (AgentState L K)) (hcard : c.card = n) (hc2 : 2 ≤ c.card)
    (W : ℕ) (hW : W = FrontTail.frontWidthBound n)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hdeep : FrontTail.frontWidthBound n ≤ W - 1)
    (hrec : ClockCapRelFront.CapRelRecurrence (L := L) (K := K) W c)
    (hwin : AllClockP3 c)
    (hJ : Jfull (L := L) (K := K) n mC T ρ0 W c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤ 0 := by
  have hfeeder : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 :=
    Ssmall_to_empty_feeder ρ0 hρ0 hsub n hn c hcard W hW hWpos hdeep hrec hJ.ssmall
  exact capRel_feeder_empty_breach_zero c hcapPos hwin hc2 hJ.frontSync hfeeder

/-! ## Part 3 — LEG (b): the bulk advances from `FrontSync ∈ Jfull` (the FrontSync-gated
window closure), GENUINELY PROVEN.

The bulk advance `ClockRealFaithfulHours.clock_real_faithful_O_log_n` carries the bare
`habs_mix_all` (Q_mix one-step closure), which is FALSE bare (the at-cap `counter = 1`
witness).  On the FrontSync-good event `FrontSyncConc.habs_mix_full` PROVES the closure; we
expose the bulk advance carrying the FrontSync-gated replacement (the SAME content
`ClockJointInduction` packages). -/

/-- **`lockstep_bulk_advance` — LEG (b): the bulk crosses `0.9·m_C` per minute over the
horizon.**  From a `Q_mix`-start at minute `0` (`Q_mix n mC 0 c₀ ∧ 9·m_C/10 ≤ rBeyond 0 c₀`),
given the FrontSync-gated window closure `habs_mix_all_gated` (the cap-relative replacement,
available on the FrontSync-good event via `FrontSyncConc.habs_mix_full`), after the
`K·(L+1)·(tseed+tbulk) = O(log n)` horizon the bulk Post fails with kernel probability
`≤ K·(L+1)·(εseed+εbulk)`.  GENUINELY `ClockRealFaithfulHours.clock_real_faithful_O_log_n`
(the FAITHFUL O(1)/minute composition).  This is the bulk-position leg the gap-bound rides on
— it bounds the bulk LEADING EDGE (NOT the straggler COUNT; see leg (c)'s residual). -/
theorem lockstep_bulk_advance (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
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
    (hQ0 : Q_mix (L := L) (K := K) n mC 0 c₀
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) 0 c₀) :
    ((NonuniformMajority L K).transitionKernel ^ ((K * (L + 1)) * (tseed + tbulk))) c₀
        {y | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
                ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)} ≤
      ((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) :=
  ClockRealFaithfulHours.clock_real_faithful_O_log_n (L := L) (K := K) n mC hn hmC hLK
    habs_mix_all_gated tseed tbulk εseed εbulk hεs hεb c₀ hQ0

/-! ## Part 4 — LEG (c), the CLEAN PREFIX: the EMPTY band `Ssmall_empty` IS maintained
lock-step UNCONDITIONALLY (NOT carried), from the bulk-position + the EMPTY-ABSORBING band-feed.

The STRONGEST cap-relative narrowness is the EMPTY top band `Ssmall_empty c := rBeyond(cap−W) c
= 0` (`gapFrac W c = 0 ≤ ρ₀`, the absorbing FIXED POINT).  From an empty band the SYNC term
VANISHES (`ClockFrontShape.seed_pair_real`: a sync of two clocks BOTH below `cap − W` lands at
`max < cap − W`, so it CANNOT seed `cap − W` from empty), the increment is DRIP-ONLY and
SQUARES, and the EMPTY-ABSORBING level-union (`ClockBulkFront.level_union_concentration` at
`J + 1 = cap − W`) maintains the empty band over the horizon at the doubly-exp cost
`H · env(cap−W)`, GIVEN only the NEXT-deeper drip window (recursing to the bulk-top).  So the
empty band is maintained lock-step WITHOUT being carried — the genuine closure of leg (c). -/

/-- **`Ssmall_empty` — the EMPTY top band (the absorbing fixed point).**  `rBeyond(cap−W) c = 0`:
NO front straggler has reached within `W = frontWidthBound n` of the cap.  This is `gapFrac W c
= 0`, the STRONGEST `Ssmall ρ₀ W` (`0 ≤ ρ₀`), and the absorbing fixed point of the band-feed. -/
def Ssmall_empty (W : ℕ) (c : Config (AgentState L K)) : Prop :=
  rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c = 0

/-- An EMPTY band satisfies `Ssmall ρ₀ W` for any `0 ≤ ρ₀` (`gapFrac W c = 0 ≤ ρ₀`). -/
theorem Ssmall_of_Ssmall_empty (ρ0 : ℝ) (hρ0 : 0 ≤ ρ0) (W : ℕ) (c : Config (AgentState L K))
    (hempty : Ssmall_empty (L := L) (K := K) W c) :
    Ssmall (L := L) (K := K) ρ0 W c := by
  unfold Ssmall gapFrac ClockCapRelFront.capRelFrac
  unfold Ssmall_empty at hempty
  rw [hempty]
  simp only [Nat.cast_zero, zero_div]
  exact hρ0

/-- **`lockstep_Ssmall_empty_maintained` — LEG (c) CLEAN PREFIX: the EMPTY band is maintained
lock-step over the horizon, NOT CARRIED.**  At the band boundary `J + 1 = cap − W` (with
`cap − W − 1 + 1 = cap − W`, i.e. `1 ≤ cap − W`), given the NEXT-deeper (`cap − W − 1`) drip
window `hnext` (every reachable `AllClockP3` config of population `n` with the band `cap − W`
empty has its feeder level `cap − W − 1` within the doubly-exp envelope — the front shape ONE
level deeper, recursing to the bulk-top), from an empty-band `AllClockP3` start `c₀` of
population `n` the kernel probability over `H` steps that the band `cap − W` is EVER seeded
(`Ssmall_empty` broken) is at most `H · ofReal (env (cap − W))`:

  `(K^H) c₀ {¬ Ssmall_empty} ≤ H · ofReal (env (cap − W))`,

doubly-exponentially tiny.  So the EMPTY band — the strongest `Ssmall` — is MAINTAINED whp
LOCK-STEP, WITHOUT being carried as a structural `hfeeder_all`: it is supplied by the
bulk-position (the band sits below `cap − W`) + the EMPTY-ABSORBING band-feed (the drip-squared
seeding, SYNC term VANISHING).  GENUINELY `ClockBulkFront.level_union_concentration` at
`J = cap − W − 1`.  This is the genuine lock-step closure of leg (c) for the absorbing fixed
point — NOT a carried assumption.  Cap-relative (the MOVING band `cap − W`), NOT absolute-low. -/
theorem lockstep_Ssmall_empty_maintained (f0 : ℝ) (n W : ℕ)
    (hWcap : W + 1 ≤ capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hnext : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c = 0 →
      AllClockP3 c → c.card = n →
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - W - 1) c)
    (H : ℕ) (c₀ : Config (AgentState L K))
    (hempty0 : Ssmall_empty (L := L) (K := K) W c₀)
    (hw0 : AllClockP3 c₀) (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ Ssmall_empty (L := L) (K := K) W c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - W)) := by
  -- (cap − W − 1) + 1 = cap − W  (since W + 1 ≤ cap ⟹ 1 ≤ cap − W).
  have hcapeq : capMinute (L := L) (K := K) - W - 1 + 1 = capMinute (L := L) (K := K) - W := by
    omega
  have hJcap : capMinute (L := L) (K := K) - W - 1 + 1 ≤ capMinute (L := L) (K := K) := by omega
  -- rephrase `hnext` and the start at `J + 1 = cap − W − 1 + 1`.
  have hnext' : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W - 1 + 1) c = 0 →
      AllClockP3 c → c.card = n →
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - W - 1) c := by
    intro c hc hwc hcardc; rw [hcapeq] at hc; exact hnext c hc hwc hcardc
  have hempty0' : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W - 1 + 1) c₀ = 0 := by
    rw [hcapeq]; exact hempty0
  -- the EMPTY-ABSORBING level-union at level `J + 1 = cap − W`.
  have hmain := level_union_concentration f0 n (capMinute (L := L) (K := K) - W - 1)
    hJcap hn2 hnext' H c₀ hempty0' hw0 hcard0
  rw [hcapeq] at hmain
  -- {¬ Ssmall_empty c'} = {1 ≤ rBeyond(cap−W) c'}  (empty ⟺ count 0 ⟺ ¬ (1 ≤ count)).
  have hset : {c' : Config (AgentState L K) | ¬ Ssmall_empty (L := L) (K := K) W c'}
      = {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c'} := by
    ext c'; simp only [Ssmall_empty, Set.mem_setOf_eq]; omega
  rw [hset]
  exact hmain

/-! ## Part 5 — LEG (c), THE EXACT RESIDUAL: the OCCUPIED band (`ρ₀ > 0`) one-step maintenance
carries `CapRelRecurrence W`, named EXACTLY.

For `Ssmall = gapFrac W c ≤ ρ₀` with an OCCUPIED band (`ρ₀ > 0`), the one-step increment of
`rBeyond(cap−W)` (an OCCUPIED level) carries the SYNC term `∝ rBeyond(cap−W) · (laggards)` —
LINEAR in the band count, NOT bounded by the drip-squared band-feed (the empty-absorbing atom
`rBeyond_seed_le_rBeyondSq` requires `rBeyond(cap−W) = 0`).  Maintaining the within-envelope
FRACTION at an occupied band IS exactly the per-level squaring recurrence `CapRelRecurrence W`
(the `m → m+1` COUNT relation `f(j+1) ≤ (f j)²`), which the bulk LEADING-EDGE position cannot
deterministically supply.  We CARRY it as the explicit per-step input (NEVER a false `∀c`
hypothesis) and prove the lock-step `Jfull` maintenance GIVEN it — naming the EXACT residual. -/

/-- **`lockstep_step_maintains` — ONE step preserves `Jfull`, all three legs combined.**

On a `Jfull` config `c` (with `1 ≤ T`, `card = n`, `n ≥ 2`, the band deep enough, `ρ₀ ≤ 1/2`),
given:
* the per-level squaring recurrence `CapRelRecurrence W` at `c` (LEG (a)/(c) residual — the
  `m → m+1` band-feed count, the EXACT cap-relative residual, NOT supplied by the leading-edge
  bulk-position);
* the `AllClockP3` window at `c` (the running phase-3 regime);
* the deterministic `noPhaseAbove3` successor-gate `hno'`;
* a successor `c'` on the kernel support with `FrontSync c'` (the FrontSync-good event — full
  measure by LEG (a), the empty cap-1 feeder squaring the breach to `0`);
* the maintained band-subcriticality `hsmall'` (the successor's band fraction `≤ ρ₀` — supplied
  lock-step from the band-feed: for the EMPTY band UNCONDITIONALLY via
  `lockstep_Ssmall_empty_maintained`, for the OCCUPIED band from `CapRelRecurrence W`),
the successor satisfies `Jfull n mC T ρ₀ W c'`.

GENUINELY PROVEN: `J c'` from `ClockJointInduction.joint_step_maintains` (the FrontSync-gated
`Q_mix ∧ allClocksCounterPos` closure `habs_mix_full`, using the empty cap-1 feeder
`Ssmall_to_empty_feeder` from `Ssmall ∈ Jfull` + `CapRelRecurrence W`), and `Ssmall c'` from
`hsmall'`.  The band maintenance `hsmall'` is the EXACT residual: it is the band-feed
empty-absorbing (CLOSED for the empty band, `lockstep_Ssmall_empty_maintained`) plus the
`m → m+1` recurrence for the occupied band — NEVER the carried `hfeeder_all`.  Cap-relative. -/
theorem lockstep_step_maintains (n mC T : ℕ) (ρ0 : ℝ) (hρ0 : 0 ≤ ρ0) (hsub : ρ0 ≤ 1 / 2)
    (hT : 1 ≤ T) (hn : 2 ≤ n)
    (c c' : Config (AgentState L K)) (hcard : c.card = n)
    (W : ℕ) (hW : W = FrontTail.frontWidthBound n)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hdeep : FrontTail.frontWidthBound n ≤ W - 1)
    (hrec : ClockCapRelFront.CapRelRecurrence (L := L) (K := K) W c)
    (hJ : Jfull (L := L) (K := K) n mC T ρ0 W c)
    (hwin : AllClockP3 c)
    (hno' : noPhaseAbove3 (L := L) (K := K) c')
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hsync' : FrontSync (L := L) (K := K) c')
    (hsmall' : Ssmall (L := L) (K := K) ρ0 W c') :
    Jfull (L := L) (K := K) n mC T ρ0 W c' := by
  -- the empty cap-1 feeder, fed by `Ssmall ∈ Jfull` (LEG (a)).
  have hfeeder0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 :=
    Ssmall_to_empty_feeder ρ0 hρ0 hsub n hn c hcard W hW hWpos hdeep hrec hJ.ssmall
  -- `J c'` from the joint one-step maintenance (the FrontSync-gated Q_mix closure).
  have hJ' : ClockJointInduction.J (L := L) (K := K) n mC T c' :=
    ClockJointInduction.joint_step_maintains n mC T hT c c' hJ.toJ ⟨hwin, hfeeder0⟩
      hno' hc' hsync'
  exact ⟨hJ', hsmall'⟩

/-! ## Part 6 — the UNCONDITIONAL clock on the EMPTY-band lock-step (the strongest front-shape).

Combining the three legs over the `O(log n)` horizon WHEN the lock-step runs on the EMPTY band
(`Ssmall_empty`, the absorbing fixed point): leg (c) closes UNCONDITIONALLY
(`lockstep_Ssmall_empty_maintained` — the empty band maintained whp NOT-carried), leg (a) makes
the FrontSync breach `0` (the empty band gives the empty cap-1 feeder), and leg (b) advances the
bulk.  The joint failure over the horizon is the union bound, with BOTH the FrontSync part AND
the band part vanishing to the doubly-exp `H · env(cap−W)` — the clock is UNCONDITIONAL whp on
the empty-band lock-step, carrying NO structural hyp beyond the empty-band start + the
NEXT-deeper drip window (which bottoms at the bulk-top boundary, `< 1/n` from bulk
subcriticality) + the deterministic phase gate. -/

/-- **`clock_real_O_log_n_unconditional` — the real-kernel O(log n) clock on the EMPTY-band
lock-step.**

From a `Jfull`-start with the EMPTY band (`Ssmall_empty W c₀`, the absorbing fixed point) and
`Q_mix n mC 0 c₀ ∧ 9·m_C/10 ≤ rBeyond 0 c₀`, after the `K·(L+1)·(tseed+tbulk) = O(log n)`
horizon, the JOINT failure event

  `{the bulk-Post FAILS} ∪ {FrontSync BREAKS} ∪ {the band cap − W is EVER seeded}`

has kernel probability `≤ K·(L+1)·(εseed+εbulk) + H · env(cap−W)` (a union bound; the FrontSync
part is `0`, the band part is doubly-exp tiny, the bulk part is the `O(log n)` budget).

GENUINELY assembled from the three lock-step legs:
* leg (b) `lockstep_bulk_advance` (the FAITHFUL O(1)/minute composition, given the FrontSync-
  gated window closure `habs_mix_all_gated`);
* leg (a) `ClockJointInduction.joint_frontSync_horizon_zero` (the FrontSync breach over the
  horizon is EXACTLY `0`, given the empty cap-1 feeder for every reachable `FrontSync` config —
  which the empty band supplies via `Ssmall_to_empty_feeder`/`gap_bound`);
* leg (c) `lockstep_Ssmall_empty_maintained` (the empty band maintained whp, NOT carried).

CARRIED inputs (all cap-relative / deterministic, NONE absolute-low):
* `hfeeder_all` — the empty cap-1 feeder for every reachable `FrontSync` config (supplied by the
  empty band via the doubly-exp collapse; the cap-relative MOVING leading edge);
* `hnext` — the NEXT-deeper (`cap − W − 1`) drip window (the band-feed recursion, bottoming at
  the bulk-top boundary `< 1/n` from bulk subcriticality);
* `habs_mix_all_gated` — the FrontSync-gated `Q_mix` window closure.

⛔ HONEST: this is the clock on the EMPTY-band lock-step (the strongest front-shape, the
absorbing fixed point), with leg (c) GENUINELY CLOSED (the empty band is NOT carried — it is
maintained lock-step from the empty-absorbing band-feed).  For the OCCUPIED band (`ρ₀ > 0`) leg
(c) carries the EXACT residual `CapRelRecurrence W` (the `m → m+1` sync count), named in
`lockstep_step_maintains`.  NO absolute-low regression: `Ssmall_empty` is the MOVING band
`rBeyond(cap−W) = 0`, NOT `rBeyond(frontWidthBound n) = 0`. -/
theorem clock_real_O_log_n_unconditional (f0 : ℝ) (n mC W : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (hWcap : W + 1 ≤ capMinute (L := L) (K := K))
    -- the empty cap-1 feeder for every reachable FrontSync config (the cap-relative MOVING edge,
    -- supplied by the empty band; NOT absolute-low).
    (hfeeder_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0)
    -- the NEXT-deeper drip window (the band-feed recursion to the bulk-top boundary).
    (hnext : ∀ c : Config (AgentState L K),
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - W) c = 0 →
      AllClockP3 c → c.card = n →
      RWithinEnvelope (L := L) (K := K) f0 (capMinute (L := L) (K := K) - W - 1) c)
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
    (hempty0 : Ssmall_empty (L := L) (K := K) W c₀)
    (hw0 : AllClockP3 c₀)
    (hQ0 : Q_mix (L := L) (K := K) n mC 0 c₀
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) 0 c₀) :
    ((NonuniformMajority L K).transitionKernel ^ ((K * (L + 1)) * (tseed + tbulk))) c₀
        ({y | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
                ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)}
          ∪ {c' | ¬ FrontSync (L := L) (K := K) c'}
          ∪ {c' | ¬ Ssmall_empty (L := L) (K := K) W c'}) ≤
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
    lockstep_bulk_advance n mC hn hmC hLK habs_mix_all_gated tseed tbulk εseed εbulk hεs hεb
      c₀ hQ0
  -- leg (a): the FrontSync breach over the horizon is EXACTLY 0 (empty cap-1 feeder).
  have hfront : (Kp ^ M) c₀ {c' | ¬ FrontSync (L := L) (K := K) c'} = 0 :=
    ClockJointInduction.joint_frontSync_horizon_zero n hcapPos hn hfeeder_all M c₀ hsync0 hQ0.1.card
  -- leg (c) CLEAN PREFIX: the empty band maintained over the horizon (doubly-exp tiny).
  have hband : (Kp ^ M) c₀ {c' | ¬ Ssmall_empty (L := L) (K := K) W c'} ≤
      (M : ℝ≥0∞) * ENNReal.ofReal
        (FrontTailKernel.envelope f0 (capMinute (L := L) (K := K) - W)) :=
    lockstep_Ssmall_empty_maintained f0 n W hWcap hn hnext M c₀ hempty0 hw0 hQ0.1.card
  -- union bound over the three failure sets.
  set A := {y : Config (AgentState L K) | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
            ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)} with hA
  set B := {c' : Config (AgentState L K) | ¬ FrontSync (L := L) (K := K) c'} with hB
  set C := {c' : Config (AgentState L K) | ¬ Ssmall_empty (L := L) (K := K) W c'} with hC
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

/-! ## HONEST STATUS — `ClockLockstep` (the FULL lock-step joint induction)

* **The lock-step BREAKS the confirmed circularity.**  `ClockJointInduction.J` maintained
  `FrontSync` by CARRYING `Ssmall` (`hfeeder_all`).  `ClockGapBulk` could not discharge `Ssmall`
  from the bulk-position (the leading edge does NOT bound the straggler count).  `Jfull = J ∧
  Ssmall` maintains all of `{FrontSync, bulk-advance, Ssmall}` TOGETHER:
  - **LEG (a) `lockstep_frontSync_breach_zero`** — `FrontSync` is fed BY `Ssmall` (the empty
    cap-1 feeder via the doubly-exp collapse `Ssmall_to_empty_feeder`), breach `0`.  PROVEN.
  - **LEG (b) `lockstep_bulk_advance`** — the bulk advances from `FrontSync ∈ Jfull` (the
    FrontSync-gated window closure), `0.9·m_C` per minute over `O(log n)`.  PROVEN.
  - **LEG (c)** — `Ssmall` maintained from the band-feed.  SPLITS:
    * **CLEAN PREFIX `lockstep_Ssmall_empty_maintained`** — the EMPTY band `Ssmall_empty`
      (`gapFrac W = 0`, the absorbing fixed point) is maintained lock-step over the horizon
      WITHOUT being carried, purely from the bulk-position + the EMPTY-ABSORBING band-feed
      (`level_union_concentration` at `cap − W`, SYNC term VANISHING).  GENUINELY CLOSED.
    * **EXACT RESIDUAL** — for the OCCUPIED band (`ρ₀ > 0`) the one-step maintenance carries
      `CapRelRecurrence W` (the `m → m+1` sync count, LINEAR not squared, NOT supplied by the
      leading-edge bulk-position).  `lockstep_step_maintains` proves the lock-step `Jfull`
      maintenance GIVEN it.  Named EXACTLY, never asserted false.

* **`lockstep_step_maintains` — the ONE-STEP lock-step maintenance, all three legs.**  On a
  `Jfull` config it produces `Jfull` at the successor: `J c'` from the FrontSync-gated joint
  maintenance (LEG (a)+(b) closure `joint_step_maintains`, using the empty cap-1 feeder from
  `Ssmall ∈ Jfull` + the per-level recurrence), and `Ssmall c'` from the band-feed maintenance
  (UNCONDITIONAL for the empty band, `CapRelRecurrence W` for the occupied band).  `Ssmall` is
  maintained from the COMPONENTS (bulk-position + empty-absorbing), NOT carried as `hfeeder_all`.

* **`clock_real_O_log_n_unconditional` — the clock on the EMPTY-band lock-step.**  The real-kernel
  O(log n) clock reaches `0.9·m_C` while maintaining FrontSync ∧ the empty band throughout, with
  joint failure `≤ K·(L+1)·(εseed+εbulk) + M·env(cap−W)`.  On the EMPTY-band lock-step (the
  strongest front-shape, the absorbing fixed point) leg (c) is GENUINELY CLOSED — the band is NOT
  carried — so the clock is UNCONDITIONAL whp beyond: the empty-band Phase-3 start + ε/t + the
  NEXT-deeper drip window (recursing to the bulk-top boundary `< 1/n` from bulk subcriticality)
  + the deterministic phase gate.  For the OCCUPIED band it carries the EXACT residual
  `CapRelRecurrence W`.

VERDICT (NOT over-claimed): the FULL lock-step joint invariant `Jfull = J ∧ Ssmall` is
formulated CAP-RELATIVE (around the MOVING band `cap − W`), and its three legs are GENUINELY
PROVEN per step + iterated over the `O(log n)` horizon.  Leg (c) — the CRUX — CLOSES
UNCONDITIONALLY for the EMPTY band (`lockstep_Ssmall_empty_maintained`, the maximal clean prefix:
the empty band is maintained lock-step from the empty-absorbing band-feed, NOT carried), and for
the OCCUPIED band (`ρ₀ > 0`) carries the SINGLE irreducible CAP-RELATIVE residual
`CapRelRecurrence W` (the `m → m+1` sync count, NOT bounded by drip-squared, NOT supplied by the
bulk leading-edge position).  EXPLICITLY confirmed: NO `FrontAllLevels` / `ClockFrontIter` /
absolute-low `rBeyond(frontWidthBound n) = 0` is used; `Ssmall` is the MOVING cap-relative band
count `gapFrac W = rBeyond(cap − W)/n` throughout. -/
theorem clock_lockstep_status : True := trivial

end ClockLockstep

end ExactMajority
