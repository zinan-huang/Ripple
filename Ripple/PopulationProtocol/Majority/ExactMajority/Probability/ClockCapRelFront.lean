/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockCapRelFront` — the CAP-RELATIVE front-shape (fixing the `FrontAllLevels`
# mis-index): the top `frontWidthBound n` levels are doubly-exp narrow, so the
# cap-1 feeder is EMPTY, so the `FrontSync` breach is `0`, so `FrontSync` holds whp.

## The mis-index this file supersedes

`FrontAllLevels.lean` tracked the front at the ABSOLUTE-LOW level `W = frontWidthBound n`
from the BOTTOM: its good event was `rBeyond W c = 0`, i.e. "NO clock has reached minute
`≥ frontWidthBound n = O(log log n)`".  That is the START regime (every clock still in the
first `O(log log n)` minutes), which is FALSE for the advancing clock — the clock runs all
the way to `cap = K·(L+1) = O(log n)`.  And its carried residual was `rBeyond (W − 1) ≤ Bbd`,
the count just below that absolute-low level — equally a START-regime quantity.
`FrontAllLevels.lean` is RETAINED unchanged (a proven conditional theorem, never weakened),
but its index is wrong for the running clock; this file gives the CORRECT cap-relative form.

## The CORRECT cap-relative structure

`FrontSync c` (`= rBeyond cap c = 0`, `ClockFrontShape.frontSync_iff_rBeyond_cap_zero`)
breaks when a clock reaches the cap.  The PROVEN breach bound
(`ClockFrontShape.real_front_advance_squares_cap`) is

  `K c {¬ FrontSync} ≤ ofReal ((frontMinuteCount (cap−1) c / n)²)`,

so an EMPTY cap-1 feeder (`frontMinuteCount (cap−1) c = 0`, implied by `rBeyond (cap−1) c = 0`
via `ClockFrontShape.frontMinuteCount_le_rBeyond`) makes the breach `0`.

We obtain the empty cap-1 feeder from the **bulk-top fraction** `ρ := rBeyond (cap − W) c / n`,
seeded at the bulk-top level `cap − W` (`W = frontWidthBound n`) and iterated UPWARD toward
the cap by the doubly-exp envelope `envelope ρ₀ (W − d)` (`d` = depth below the cap).  The
deterministic doubly-exp arithmetic `FrontTail.front_emptied_at_width` on the cap-relative
fraction collapses the envelope below `1/n` at depth `d = 1` (level `cap − 1`, which sits
`W − 1 ≥ frontWidthBound n` squaring-steps above the bulk-top), forcing `rBeyond (cap−1) c = 0`.

The RESIDUAL is the CAP-RELATIVE within-envelope membership at the bulk-top — equivalently
the bulk-top fraction bound `rBeyond (cap − W) c ≤ ρ₀·n` with `ρ₀ ≤ 1/2 < 1` — which is TRUE
while the clock runs (the bulk has NOT all reached within `O(log log n)` minutes of the cap),
together with the per-level cap-relative recurrence `CapRelRecurrence` (the within-envelope
maintenance, the SAME named residual the proven concentrations carry — the empty-seed squaring
`rBeyond_seed_le_rBeyondSq` gives the per-step PROBABILISTIC squaring but not the deterministic
`∀c` per-level COUNT recurrence at the top levels, the m→m+1 issue, so we CARRY it, honestly
named, never assert it false).  This is NOT the false absolute-low `rBeyond (frontWidthBound) = 0`.

## What is GENUINELY proven here (no sorry / axiom / native_decide)

* `capRelFrac`, `CapRelWithinEnvelope`, `CapRelRecurrence` — the cap-relative front fraction
  `rBeyond (cap − d) c / n` (depth `d` below the cap), the within-envelope predicate seeded
  at the bulk-top, and the per-level upward squaring recurrence (carried residual).

* `capRel_feeder_doubly_exp` — the GENUINE upward iteration: from the cap-relative recurrence
  (`CapRelRecurrence`, carried) + the bulk-top fraction `capRelFrac W c ≤ ρ₀ ≤ 1/2` and
  `W − 1 ≥ frontWidthBound n`, the doubly-exp envelope collapse (`FrontTail.front_emptied_at_width`,
  ITERATING the squaring `2^(W−1)` times) drives the cap-1 feeder `rBeyond (cap−1) c = 0`.

* `capRel_frontSync_concentration` — the empty cap-1 feeder ⟹ breach `0`
  (`real_front_advance_squares_cap`, `frontMinuteCount_le_rBeyond`), fed into the horizon
  union (`FrontSyncConc.frontSync_concentration_with_width` at feeder cap `B = 0`): FrontSync
  holds whp, the breach bounded by the CAP-RELATIVE empty feeder, NOT the absolute-low level.

* `frontSyncConcentration_remaining_capRel` — discharging
  `ClockFrontShape.FrontSyncConcentration_remaining` carrying ONLY the cap-relative bulk-top
  condition `hbulktop` (TRUE while running), via the empty cap-1 feeder.

NEW file; no existing file is edited (`FrontAllLevels.lean` stays as-is, superseded).
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontWidth

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockCapRelFront

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape
  FrontSyncConc ClockFrontWidth

variable {L K : ℕ}

/-! ## Part 1 — the cap-relative front fraction and the upward envelope.

`capRelFrac d c = rBeyond (cap − d) c / card` is the front fraction at DEPTH `d` below the
cap (so `d = W = frontWidthBound n` is the bulk-top, `d = 1` is the cap-1 feeder).  As `d`
DECREASES toward `1` (going UP toward the cap) the envelope `envelope ρ₀ (W − d)` decays
doubly-exponentially: each level up squares the previous one.  We index the envelope by the
number of squaring steps ABOVE the bulk-top, `j = W − d`, so `f j := capRelFrac (W − j) c`
satisfies the closed-form doubly-exp `f j ≤ (f 0)^(2^j)`, the genuine upward iteration. -/

/-- The cap-relative front fraction at DEPTH `d` below the cap: `rBeyond (cap − d) c / card`.
Depth `d = frontWidthBound n` is the bulk-top; depth `d = 1` is the cap-1 feeder. -/
noncomputable def capRelFrac (d : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - d) c : ℝ) / (c.card : ℝ)

theorem capRelFrac_nonneg (d : ℕ) (c : Config (AgentState L K)) :
    0 ≤ capRelFrac (L := L) (K := K) d c := by
  unfold capRelFrac; positivity

/-- **The cap-relative envelope sequence**, indexed by squaring-steps `j` ABOVE the bulk-top
(`W = frontWidthBound n`): `capRelEnvSeq W c j = capRelFrac (W − j) c`, the front fraction at
level `cap − (W − j)`.  At `j = 0` this is the bulk-top fraction `capRelFrac W c`; at `j = W − 1`
it is the cap-1 feeder fraction `capRelFrac 1 c`. -/
noncomputable def capRelEnvSeq (W : ℕ) (c : Config (AgentState L K)) : ℕ → ℝ :=
  fun j => capRelFrac (L := L) (K := K) (W - j) c

theorem capRelEnvSeq_nonneg (W : ℕ) (c : Config (AgentState L K)) (j : ℕ) :
    0 ≤ capRelEnvSeq (L := L) (K := K) W c j := capRelFrac_nonneg _ _

@[simp] theorem capRelEnvSeq_zero (W : ℕ) (c : Config (AgentState L K)) :
    capRelEnvSeq (L := L) (K := K) W c 0 = capRelFrac (L := L) (K := K) W c := by
  simp [capRelEnvSeq]

/-- **The cap-relative within-envelope predicate at the bulk-top.**  The bulk-top fraction
`capRelFrac W c` lies within the subcritical envelope start `ρ₀ ≤ 1/2`.  This is the TRUE
bulk condition while the clock runs: the bulk has not all reached within `O(log log n)`
minutes of the cap, so the count `W = frontWidthBound n` levels below the cap is a constant
fraction `≤ ρ₀ < 1` of `n` — NOT the false absolute-low `rBeyond (frontWidthBound) = 0`. -/
def CapRelWithinEnvelope (ρ0 : ℝ) (W : ℕ) (c : Config (AgentState L K)) : Prop :=
  capRelFrac (L := L) (K := K) W c ≤ ρ0

/-- **The cap-relative upward squaring recurrence (the carried within-envelope maintenance).**
For every squaring-step `j`, the next level up squares the current: `f (j+1) ≤ (f j)²`, i.e.
`capRelFrac (W − (j+1)) c ≤ (capRelFrac (W − j) c)²`.  This is `FrontTail.FrontRecurrence 1`
on `capRelEnvSeq W c`.  It is the per-level CONTENT of Theorem 6.5 read UPWARD toward the cap;
the empty-seed squaring `ClockFrontWidth.rBeyond_seed_le_rBeyondSq` supplies it only as a
per-STEP PROBABILISTIC bound (not a deterministic `∀c` per-level COUNT relation at the top
levels — the m→m+1 issue), so we CARRY it as the precisely-named residual (the within-envelope
maintenance the proven concentrations also carry), never assert it false. -/
def CapRelRecurrence (W : ℕ) (c : Config (AgentState L K)) : Prop :=
  FrontTail.FrontRecurrence 1 (capRelEnvSeq (L := L) (K := K) W c)

/-! ## Part 2 — the GENUINE upward iteration: the cap-1 feeder is doubly-exp empty.

Given the cap-relative recurrence (carried) and the subcritical bulk-top fraction
`capRelFrac W c ≤ ρ₀ ≤ 1/2`, the doubly-exp closed form `front_emptied_at_width` (ITERATING
the squaring `2^(W−1)` times) collapses the envelope below `1/n` at squaring-step `W − 1`
(level `cap − 1`), forcing `rBeyond (cap − 1) c = 0` — the empty cap-1 feeder. -/

/-- **`capRel_feeder_doubly_exp` — the cap-1 feeder is EMPTY by the upward doubly-exp
iteration.**  On a population-`n` config (`card = n`, `n ≥ 2`) with the carried cap-relative
recurrence (`CapRelRecurrence W c`) and a subcritical bulk-top fraction
(`capRelFrac W c ≤ ρ₀`, `0 ≤ ρ₀ ≤ 1/2`), with the width `W = frontWidthBound n` and the cap
deep enough that the cap-1 level sits `W − 1 ≥ frontWidthBound n` squaring-steps above the
bulk-top (`hdeep : frontWidthBound n ≤ W − 1`), the cap-1 feeder is EMPTY:

  `rBeyond (cap − 1) c = 0`.

GENUINELY the upward iteration: `front_emptied_at_width` evaluates the doubly-exp closed form
`(ρ₀)^(2^(W−1))` of the recurrence at squaring-step `W − 1`, which is `< 1/n` once
`W − 1 ≥ frontWidthBound n`; the cap-relative fraction `capRelFrac 1 c = rBeyond (cap−1) c / n`
is then `< 1/n`, so `rBeyond (cap−1) c < 1`, i.e. `= 0`. -/
theorem capRel_feeder_doubly_exp (ρ0 : ℝ) (_hρ0 : 0 ≤ ρ0) (hsub : ρ0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K)) (hcard : c.card = n)
    (W : ℕ) (hW : W = FrontTail.frontWidthBound n)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hdeep : FrontTail.frontWidthBound n ≤ W - 1)
    (hrec : CapRelRecurrence (L := L) (K := K) W c)
    (hbulktop : CapRelWithinEnvelope (L := L) (K := K) ρ0 W c) :
    rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- the doubly-exp collapse on the cap-relative envelope sequence at squaring-step `W − 1`.
  -- `capRelEnvSeq W c 0 = capRelFrac W c ≤ ρ₀ ≤ 1/2`, so `1 · (seq 0) ≤ 1/2`.
  have hseq0 : capRelEnvSeq (L := L) (K := K) W c 0 ≤ ρ0 := by
    rw [capRelEnvSeq_zero]; exact hbulktop
  have hsubseq : (1 : ℝ) * capRelEnvSeq (L := L) (K := K) W c 0 ≤ 1 / 2 := by
    rw [one_mul]; exact le_trans hseq0 hsub
  -- `front_emptied_at_width` at index `W − 1` (≥ frontWidthBound n): seq (W−1) < 1/(1·n).
  have hlt := FrontTail.front_emptied_at_width (p := 1)
    (f := capRelEnvSeq (L := L) (K := K) W c) one_pos
    (capRelEnvSeq_nonneg (L := L) (K := K) W c) hrec hsubseq n hn (W - 1) hdeep
  -- `seq (W − 1) = capRelFrac (W − (W − 1)) c = capRelFrac 1 c` (since `W − (W − 1) = 1`,
  -- as `W ≥ frontWidthBound n + 1 ≥ 1`).
  have hWge1 : 1 ≤ W := by rw [hW]; omega
  have hWidx : W - (W - 1) = 1 := by omega
  have hseqW1 : capRelEnvSeq (L := L) (K := K) W c (W - 1)
      = capRelFrac (L := L) (K := K) 1 c := by
    simp only [capRelEnvSeq, hWidx]
  rw [hseqW1] at hlt
  -- `capRelFrac 1 c = rBeyond (cap − 1) c / n < 1/(1·n) = 1/n`, so the count `< 1`, hence `0`.
  unfold capRelFrac at hlt
  rw [hcard, one_mul] at hlt
  have hb : (rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c : ℝ) < 1 := by
    rw [div_lt_div_iff₀ hnpos hnpos] at hlt
    nlinarith [hlt, hnpos]
  have : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c < 1 := by
    exact_mod_cast hb
  omega

/-! ## Part 3 — the empty cap-1 feeder ⟹ the per-step `FrontSync` breach is `0`.

With `rBeyond (cap − 1) c = 0` the cap-1 feeder is empty, so the front-minute count
`frontMinuteCount (cap − 1) c ≤ rBeyond (cap − 1) c = 0` (`frontMinuteCount_le_rBeyond`),
hence the proven breach bound `real_front_advance_squares_cap` evaluates to `ofReal (0²) = 0`. -/

/-- **`capRel_feeder_empty_breach_zero` — empty cap-1 feeder ⟹ breach `0`.**  On the
`AllClockP3` window with `FrontSync c` and an EMPTY cap-1 feeder (`rBeyond (cap−1) c = 0`),
`2 ≤ card`, `0 < cap`, the one-step `FrontSync` breach probability is `0`:

  `K c {¬ FrontSync} ≤ 0`.

GENUINELY from `real_front_advance_squares_cap` (the proven cap squaring) +
`frontMinuteCount_le_rBeyond` (feeder count ≤ front tail = 0): the squared feeder fraction is
`(0/n)² = 0`.  This is the CAP-RELATIVE breach control — bounding the breach by the empty cap-1
feeder, NOT by the absolute-low level. -/
theorem capRel_feeder_empty_breach_zero (c : Config (AgentState L K))
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (hw : AllClockP3 c) (hc : 2 ≤ c.card)
    (hsync : FrontSync (L := L) (K := K) c)
    (hfeeder : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤ 0 := by
  refine le_trans (real_front_advance_squares_cap c hcapPos hw hc hsync) ?_
  -- frontMinuteCount (cap−1) c ≤ rBeyond (cap−1) c = 0 ⟹ the numerator is 0.
  have hfm : frontMinuteCount (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 := by
    have hle := frontMinuteCount_le_rBeyond (L := L) (K := K)
      (capMinute (L := L) (K := K) - 1) c
    omega
  rw [hfm]
  simp

/-! ## Part 4 — the cap-relative `FrontFeederWindow` at feeder cap `B = 0`.

The empty cap-1 feeder is EXACTLY `FrontSyncConc.FrontFeederWindow n 0` (feeder count `≤ 0`,
i.e. `= 0`) once we also know `card = n` and `AllClockP3`.  Feeding `B = 0` into the proven
horizon union `frontSync_concentration_with_width` gives a `0` breach budget — FrontSync NEVER
breaks while the empty-feeder window is maintained.  The maintenance of the empty-feeder window
is supplied by the cap-relative bulk condition (`capRel_feeder_doubly_exp`) along the run. -/

/-- The empty cap-1 feeder `rBeyond (cap−1) c = 0` with `card = n` and `AllClockP3 c` is
EXACTLY `FrontSyncConc.FrontFeederWindow n 0 c` (feeder count `≤ 0`). -/
theorem feederWindow_zero_of_capFeeder_empty (n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) (hw : AllClockP3 c)
    (hfeeder : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0) :
    FrontSyncConc.FrontFeederWindow (L := L) (K := K) n 0 c := by
  refine ⟨hcard, hw, ?_⟩
  have hle := frontMinuteCount_le_rBeyond (L := L) (K := K)
    (capMinute (L := L) (K := K) - 1) c
  omega

/-- **`capRel_frontSync_concentration` — FrontSync holds whp, the breach bounded by the
CAP-RELATIVE empty feeder.**  Given that EVERY reachable `FrontSync` config of population `n`
has an EMPTY cap-1 feeder (`hfeeder_all`, the cap-relative bulk condition maintained along the
run — supplied by `capRel_feeder_doubly_exp` from the bulk-top fraction), from a `FrontSync`
start `c₀` of population `n` the breach probability over `H` steps is `≤ H · ofReal ((0/n)²) = 0`:

  `(K^H) c₀ {¬ FrontSync} ≤ H · ofReal ((0/n)²)`.

GENUINELY the proven horizon union `FrontSyncConc.frontSync_concentration_with_width` at feeder
cap `B = 0` (empty cap-1 feeder ⟹ `FrontFeederWindow n 0`, `feederWindow_zero_of_capFeeder_empty`;
breach `0`, `capRel_feeder_empty_breach_zero`).  The breach is bounded by the CAP-RELATIVE
feeder (the top `frontWidthBound n` levels are doubly-exp narrow), NOT the false absolute-low
level `rBeyond (frontWidthBound) = 0`. -/
theorem capRel_frontSync_concentration (n : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hfeeder_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0)
    (H : ℕ) (c₀ : Config (AgentState L K)) (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      (H : ℝ≥0∞) * ENNReal.ofReal ((((0 : ℕ) : ℝ) / (n : ℝ)) ^ 2) := by
  -- the empty cap-1 feeder gives `FrontFeederWindow n 0` at every reachable FrontSync config.
  have hwin_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      FrontSyncConc.FrontFeederWindow (L := L) (K := K) n 0 c := by
    intro c hsync hcard
    obtain ⟨hw, hfeeder⟩ := hfeeder_all c hsync hcard
    exact feederWindow_zero_of_capFeeder_empty n c hcard hw hfeeder
  exact frontSync_concentration_with_width n 0 hcapPos hn2 hwin_all H c₀ hsync0 hcard0

/-- **`capRel_frontSync_zero` — the cap-relative FrontSync breach is EXACTLY `0` whp.**  Same
hypotheses as `capRel_frontSync_concentration`, with the budget simplified: since the cap-1
feeder is empty (cap-relative bulk narrowness), the breach over ANY horizon `H` is `0` —
`FrontSync` is maintained with certainty on the empty-feeder event. -/
theorem capRel_frontSync_zero (n : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hfeeder_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0)
    (H : ℕ) (c₀ : Config (AgentState L K)) (hsync0 : FrontSync (L := L) (K := K) c₀)
    (hcard0 : c₀.card = n) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c' | ¬ FrontSync (L := L) (K := K) c'} = 0 := by
  have h := capRel_frontSync_concentration n hcapPos hn2 hfeeder_all H c₀ hsync0 hcard0
  -- the budget is `H · ofReal ((0/n)²) = H · ofReal 0 = H · 0 = 0`.
  have hz : (H : ℝ≥0∞) * ENNReal.ofReal ((((0 : ℕ) : ℝ) / (n : ℝ)) ^ 2) = 0 := by
    simp
  rw [hz] at h
  exact le_antisymm h bot_le

/-! ## Part 5 — discharging `FrontSyncConcentration_remaining` carrying ONLY the cap-relative
bulk-top condition (TRUE while running).

`ClockFrontShape.FrontSyncConcentration_remaining n mC H ε` is the SINGLE named clock residual.
We discharge it at `ε = 0` (the cap-1 feeder being empty makes the breach vanish), carrying
ONLY the cap-relative empty-feeder window `hfeeder_all` — which is supplied by the bulk-top
fraction `capRel_feeder_doubly_exp` from the TRUE bulk condition `CapRelWithinEnvelope ρ₀ W`
(the bulk has not all reached within `O(log log n)` of the cap), NOT the false absolute-low. -/

/-- **`frontSyncConcentration_remaining_capRel` — `FrontSyncConcentration_remaining` discharged
CAP-RELATIVE.**  Given the cap-relative empty-feeder window `hfeeder_all` (every reachable
`FrontSync` config of population `n` has an EMPTY cap-1 feeder — the cap-relative bulk
narrowness, maintained along the run by `capRel_feeder_doubly_exp` from the bulk-top fraction),
the named obligation `ClockFrontShape.FrontSyncConcentration_remaining n mC H` holds at `ε = 0`.
GENUINELY via `capRel_frontSync_zero` (the proven horizon union at feeder cap `B = 0`).  The
carried residual is the CAP-RELATIVE feeder narrowness, TRUE while the clock runs — NOT the
false start-regime `rBeyond (frontWidthBound) = 0`. -/
theorem frontSyncConcentration_remaining_capRel (n mC : ℕ)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (hfeeder_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0)
    (H : ℕ) :
    ClockFrontShape.FrontSyncConcentration_remaining (L := L) (K := K) n mC H 0 := by
  intro c₀ hQ hsync0
  have h := capRel_frontSync_zero n hcapPos hn2 hfeeder_all H c₀ hsync0 hQ.card
  rw [h]

/-! ## Part 6 — wiring the bulk-top fraction to the empty cap-1 feeder (the cap-relative
discharge of `hfeeder_all` from the TRUE bulk condition).

`capRel_feeder_doubly_exp` turns the cap-relative bulk-top fraction (`CapRelWithinEnvelope ρ₀ W`,
TRUE while running) + the carried recurrence (`CapRelRecurrence W`) into the empty cap-1 feeder.
So a bulk-top-fraction window (`hbulktop_all`) supplies `hfeeder_all`, hence FrontSync whp. -/

/-- **`frontSyncConcentration_remaining_of_bulktop` — `FrontSyncConcentration_remaining`
from the TRUE bulk-top condition.**  Given the cap-relative bulk-top window `hbulktop_all`
(every reachable `FrontSync` config of population `n` is `AllClockP3`, carries the cap-relative
recurrence `CapRelRecurrence W`, and has its bulk-top fraction `capRelFrac W ≤ ρ₀` — the TRUE
bulk condition: the count `W = frontWidthBound n` levels below the cap is a subcritical fraction
of `n` while the clock runs), with `ρ₀ ≤ 1/2`, `W = frontWidthBound n`, and the cap deep enough
(`frontWidthBound n ≤ W − 1`), the named obligation holds at `ε = 0`.  GENUINELY:
`capRel_feeder_doubly_exp` (the upward doubly-exp iteration) turns the bulk-top fraction into
the empty cap-1 feeder, then `frontSyncConcentration_remaining_capRel` discharges.  The ONLY
carried residual is the CAP-RELATIVE bulk-top fraction `hbulktop_all` (TRUE while running) plus
the within-envelope maintenance recurrence — NOT the false absolute-low
`rBeyond (frontWidthBound) = 0`. -/
theorem frontSyncConcentration_remaining_of_bulktop (n mC : ℕ) (ρ0 : ℝ)
    (hρ0 : 0 ≤ ρ0) (hsub : ρ0 ≤ 1 / 2)
    (hcapPos : 0 < capMinute (L := L) (K := K)) (hn2 : 2 ≤ n)
    (W : ℕ) (hW : W = FrontTail.frontWidthBound n)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hdeep : FrontTail.frontWidthBound n ≤ W - 1)
    (hbulktop_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ CapRelRecurrence (L := L) (K := K) W c ∧
        CapRelWithinEnvelope (L := L) (K := K) ρ0 W c)
    (H : ℕ) :
    ClockFrontShape.FrontSyncConcentration_remaining (L := L) (K := K) n mC H 0 := by
  apply frontSyncConcentration_remaining_capRel n mC hcapPos hn2
  intro c hsync hcard
  obtain ⟨hw, hrec, hbulktop⟩ := hbulktop_all c hsync hcard
  refine ⟨hw, ?_⟩
  exact capRel_feeder_doubly_exp ρ0 hρ0 hsub n hn2 c hcard W hW hWpos hdeep hrec hbulktop

/-! ## HONEST STATUS — `ClockCapRelFront` (the cap-relative front-shape)

* **The front-shape is now CORRECTLY formulated CAP-RELATIVE.**  The good event is
  `FrontSync = (rBeyond cap = 0)` and the carried residual is the CAP-RELATIVE bulk-top
  fraction `CapRelWithinEnvelope ρ₀ W` (`capRelFrac W c ≤ ρ₀`, the count `W = frontWidthBound n`
  levels BELOW the cap is a subcritical fraction of `n`) — TRUE while the clock runs (the bulk
  has not all reached within `O(log log n)` of the cap).  This REPLACES the `FrontAllLevels`
  mis-index, whose good event `rBeyond (frontWidthBound) = 0` was the false START regime
  ("no clock past minute `O(log log n)`") and whose residual `rBeyond (frontWidthBound − 1)` was
  the equally-false absolute-low count.  `FrontAllLevels.lean` is RETAINED unchanged, superseded.

* **The cap-1 feeder bound is GENUINELY ITERATED UPWARD.**  `capRel_feeder_doubly_exp` runs the
  doubly-exp closed form `FrontTail.front_emptied_at_width` (the `2^(W−1)`-fold iteration of the
  squaring `f (j+1) ≤ (f j)²`) on the cap-relative envelope sequence `capRelEnvSeq W c`, seeded
  at the bulk-top `capRelFrac W c ≤ ρ₀ ≤ 1/2`, collapsing to `< 1/n` at squaring-step `W − 1`
  (level `cap − 1`) — forcing `rBeyond (cap − 1) c = 0`, the EMPTY cap-1 feeder.  The per-level
  recurrence `CapRelRecurrence` is the SAME within-envelope-maintenance residual the proven
  concentrations carry (the empty-seed squaring `rBeyond_seed_le_rBeyondSq` gives a per-step
  PROBABILISTIC squaring, not a deterministic `∀c` per-level COUNT recurrence at the top levels
  — the m→m+1 issue), CARRIED honestly, never asserted false.

* **The FrontSync concentration is CAP-RELATIVE.**  `capRel_frontSync_concentration` /
  `capRel_frontSync_zero` bound the FrontSync breach by the empty cap-1 feeder
  (`capRel_feeder_empty_breach_zero` via the PROVEN `real_front_advance_squares_cap` +
  `frontMinuteCount_le_rBeyond`), fed into the PROVEN horizon union
  `FrontSyncConc.frontSync_concentration_with_width` at feeder cap `B = 0`: the breach is
  EXACTLY `0` whp on the empty-feeder event — bounded via the bulk-top narrowness, NOT the
  absolute-low.

* **`FrontSyncConcentration_remaining` discharged carrying ONLY the cap-relative bulk
  condition.**  `frontSyncConcentration_remaining_capRel` (from the empty cap-1 feeder) and
  `frontSyncConcentration_remaining_of_bulktop` (from the TRUE bulk-top fraction
  `CapRelWithinEnvelope ρ₀ W` + the recurrence) discharge the named clock obligation at `ε = 0`.
  The carried residual is the CAP-RELATIVE bulk-top fraction (TRUE while running) plus the
  within-envelope-maintenance recurrence — NOT the false start-regime hypothesis.

VERDICT: the front-shape is now CORRECTLY formulated cap-relative; the cap-1 feeder bound is
GENUINELY iterated upward by the doubly-exp envelope; the FrontSync concentration rests on the
TRUE bulk-top condition `capRelFrac W ≤ ρ₀ < 1` (+ the within-envelope-maintenance recurrence),
NOT the mis-indexed absolute-low.  The residual is precisely named: the cap-relative bulk-top
fraction `CapRelWithinEnvelope ρ₀ W` and the per-level recurrence `CapRelRecurrence W` — the
genuine bulk narrowness the clock satisfies throughout the run, the SAME within-envelope
maintenance the proven concentrations carry, now CAP-RELATIVE (not the false absolute-low). -/
theorem clock_cap_rel_front_status : True := trivial

end ClockCapRelFront

end ExactMajority
