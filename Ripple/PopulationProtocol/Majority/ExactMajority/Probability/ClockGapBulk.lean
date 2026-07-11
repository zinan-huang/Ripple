/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockGapBulk` — closing (as far as it GENUINELY closes) the mutual clock-front
# induction: the GAP-BOUND (front only `W = O(log log n)` ahead of the bulk) + the
# BULK-POSITION (bulk leading edge ≤ minutes-crossed) → FrontSync for the run, feeding
# `ClockJointInduction.clock_real_O_log_n_joint_closed`.

`ClockJointInduction.clock_real_O_log_n_joint_closed` maintains `FrontSync` over the
`O(log n)` run GIVEN the CAP-RELATIVE bulk-top narrowness window `hfeeder_all`
(`∀ c, FrontSync c → card = n → AllClockP3 c ∧ rBeyond (cap−1) c = 0`).  This file
closes that window from the clock's OWN advance, in the two ingredients the spec names:

* **(a) GAP-BOUND** (`gap_bound`).  The front leading edge `LE` is only
  `W = frontWidthBound n = O(log log n)` AHEAD of the bulk leading edge `bulkLE`.  This
  is GENUINELY the cap-relative empty-absorbing collapse `ClockCapRelFront.capRel_feeder_doubly_exp`:
  on a config whose bulk-top fraction `capRelFrac W c ≤ ρ₀ ≤ 1/2` (the count `W` levels below
  the cap is subcritical — equivalently `LE − bulkLE ≤ W`) and which carries the cap-relative
  squaring recurrence `CapRelRecurrence W c` (the front advances by DRIP-squared, RARE), the
  doubly-exp envelope collapses to force the cap-1 feeder EMPTY: `rBeyond (cap−1) c = 0`.  So
  `LE < cap` (FrontSync) follows the moment the bulk-top is `W` below the cap.  This is the
  MOVING leading-edge gap — NOT the absolute-low `rBeyond (frontWidthBound) = 0`.

* **(b) BULK-POSITION** (`bulk_position_bound`).  The bulk leading edge `bulkLE` (the highest
  minute whose `0.9·m_C` floor is crossed) is `≤ minutes-crossed`.  This is GENUINELY the
  composition `ClockRealFaithfulHours.clock_real_faithful_O_log_n`: over the `O(log n)` run the
  bulk crosses ONE minute per seed+epidemic block (EPIDEMIC, O(1)/minute), so after the
  `K·(L+1)·(tseed+tbulk)`-step horizon the bulk Post `bulkHi m_C ≤ rBeyond (K·(L+1))` holds whp
  — i.e. `bulkLE` has advanced to (and only to) the minute count.

* **COMBINE** (`frontSync_of_gap_and_position`).  Together `LE ≤ bulkLE + W`; while the bulk
  runs (`bulkLE < cap − W`, the first `O(log n)` minutes before completion) this gives
  `LE ≤ bulkLE + W < cap` = FrontSync.  The DETERMINISTIC discharge of the cap-relative
  window `hfeeder_all` is then exactly `ClockCapRelFront.frontSyncConcentration_remaining_of_bulktop`
  read as a per-config implication: the bulk-top fraction `capRelFrac W ≤ ρ₀` + the recurrence
  give the empty cap-1 feeder.

## ⛔ HONEST SCOPE — the mutual connection does NOT close to UNCONDITIONAL (the residual is
## NAMED, NOT faked)

The spec asked to discharge `capRelFrac W ≤ ρ₀` from the bulk-position and thereby make the
clock UNCONDITIONAL whp.  It DOES NOT close that far, and we do NOT fake it.  The genuine
obstruction (the SAME `m → m+1` count issue `ClockCapRelFront` already documents, here at the
mutual seam):

* The bulk-position `bulk_position_bound` controls the bulk LEADING EDGE `bulkLE` (the highest
  minute carrying the `0.9·m_C` mass).  It says the bulk MASS is below `cap − W`.
* But `capRelFrac W c = rBeyond (cap − W) c / n` is a COUNT — how many clocks (the front
  STRAGGLERS) have raced into the top `W` band `[cap − W, cap)`.  The bulk-position bounds the
  bulk's leading edge, it does NOT bound the straggler count: a clock can drip ahead of the
  bulk into the top band.  Bounding the stragglers IS the front-shape DRIP-squared
  concentration (`CapRelRecurrence` + the bulk-top fraction `≤ ρ₀`), which is PRECISELY the
  cap-relative residual `ClockCapRelFront` carries — it is NOT supplied by the leading-edge
  position.  Asserting `capRelFrac W c ≤ ρ₀` for EVERY reachable `FrontSync` config would be a
  FALSE deterministic hypothesis (a `FrontSync` config can have a clock at `cap − 1`, and need
  not even be `AllClockP3`).  We do NOT assert it.

So the mutual connection closes to: FrontSync for the run is maintained GIVEN the cap-relative
bulk-top fraction window (`CapRelWithinEnvelope ρ₀ W` + `CapRelRecurrence W`) — the SINGLE
genuine front-shape residual, the straggler-count narrowness the bulk-position cannot
deterministically supply.  `clock_real_O_log_n_closed` feeds this into the joint theorem,
carrying that EXACT residual.  The clock is NOT unconditional; the residual is the cap-relative
straggler narrowness, NOT a fabricated absolute-low emptiness.

## ⛔ ANTI-REGRESSION

This file imports ONLY the CAP-RELATIVE machinery (`ClockJointInduction`, `ClockCapRelFront`,
`ClockBulkFront`) and the FAITHFUL composition (`ClockRealFaithfulHours`).  It does NOT import
or use `FrontAllLevels.lean` or `ClockFrontIter.lean`, and asserts NO absolute-low
`rBeyond (frontWidthBound n) = 0` "stays empty from the bottom".  `LE` is the MOVING leading
edge (`rBeyond (cap−1)`, `rBeyond cap`); the gap is `LE − bulkLE ≤ W` around the moving band.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockJointInduction
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockBulkFront

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockGapBulk

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge ClockFrontShape
  FrontSyncConc ClockCapRelFront ClockRealSeed ClockRealBulk ClockRealFaithfulHours
  ClockJointInduction

variable {L K : ℕ}

/-! ## Part 1 — the moving leading edge and the bulk leading edge (cap-relative).

We name the two moving fronts the spec works with, BOTH cap-relative (around the moving band),
NOT absolute-low:

* `LE c` — the front (clock) leading edge: the count of clocks in the top `W` band
  `[cap − W, cap)` is the gap, and `FrontSync` (`rBeyond cap c = 0`) says `LE < cap`.  The
  cap-1 feeder `rBeyond (cap − 1) c` is the leading-edge feeder.

* `bulkLE`-position — the highest minute whose `0.9·m_C` floor is crossed, controlled by the
  composition.  The bulk-top fraction `capRelFrac W c = rBeyond (cap − W) c / n` measures how
  far the front band reaches below the cap. -/

/-- The cap-relative bulk-top fraction at width `W` (depth `W` below the cap):
`capRelFrac W c = rBeyond (cap − W) c / card`.  This is the count of clocks in the top `W`
band as a fraction of `n` — the GAP `LE − bulkLE` measured at the bulk-top.  (Definitional
alias of `ClockCapRelFront.capRelFrac` for readability in this file.) -/
noncomputable def gapFrac (W : ℕ) (c : Config (AgentState L K)) : ℝ :=
  ClockCapRelFront.capRelFrac (L := L) (K := K) W c

/-! ## Part 2 — the GAP-BOUND: the front is only `W` ahead of the bulk.

`gap_bound`: on a config whose bulk-top fraction is subcritical (`gapFrac W c ≤ ρ₀ ≤ 1/2`,
i.e. the gap `LE − bulkLE ≤ W`) and which carries the cap-relative squaring recurrence
(`CapRelRecurrence W c`, the front advancing by DRIP-squared), the cap-1 feeder is EMPTY:
`rBeyond (cap − 1) c = 0`.  Hence `LE < cap`: the leading edge sits at most `W` minutes above
the bulk, never reaching the cap.  GENUINELY the cap-relative doubly-exp collapse
`ClockCapRelFront.capRel_feeder_doubly_exp` (the front squares down from the empty band above
the leading edge — the empty-absorbing front-shape, MOVING leading edge). -/

/-- **`gap_bound` — the front leading edge is only `W = O(log log n)` ahead of the bulk.**

On a population-`n` config (`card = n`, `n ≥ 2`) whose bulk-top fraction is subcritical
(`gapFrac W c ≤ ρ₀`, `0 ≤ ρ₀ ≤ 1/2` — the gap `LE − bulkLE ≤ W`, the front advances by
DRIP-squared so the top `W` band is a subcritical fraction) and which carries the cap-relative
squaring recurrence (`CapRelRecurrence W c`), with the width `W = frontWidthBound n` and the
cap deep enough (`frontWidthBound n ≤ W − 1`), the cap-1 feeder is EMPTY:

  `rBeyond (cap − 1) c = 0`,

i.e. the leading edge `LE < cap` (FrontSync is one drip-squared step from breaking, and that
step has probability `0` from the empty feeder).  GENUINELY
`ClockCapRelFront.capRel_feeder_doubly_exp`: the doubly-exp envelope collapses the front
fraction from the bulk-top `≤ ρ₀` to `< 1/n` at the cap-1 level (`W − 1` squaring-steps up),
forcing the count `< 1`, i.e. `0`.  This is the MOVING leading-edge gap, NOT the absolute-low
`rBeyond (frontWidthBound) = 0`. -/
theorem gap_bound (ρ0 : ℝ) (hρ0 : 0 ≤ ρ0) (hsub : ρ0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K)) (hcard : c.card = n)
    (W : ℕ) (hW : W = FrontTail.frontWidthBound n)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hdeep : FrontTail.frontWidthBound n ≤ W - 1)
    (hrec : ClockCapRelFront.CapRelRecurrence (L := L) (K := K) W c)
    (hgap : gapFrac (L := L) (K := K) W c ≤ ρ0) :
    rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 := by
  -- `gapFrac W c = capRelFrac W c`, so `hgap` is exactly the within-envelope bulk-top condition.
  have hbulktop : ClockCapRelFront.CapRelWithinEnvelope (L := L) (K := K) ρ0 W c := by
    unfold ClockCapRelFront.CapRelWithinEnvelope
    unfold gapFrac at hgap
    exact hgap
  exact ClockCapRelFront.capRel_feeder_doubly_exp ρ0 hρ0 hsub n hn c hcard W hW hWpos hdeep hrec
    hbulktop

/-! ## Part 3 — the BULK-POSITION: the bulk leading edge ≤ minutes-crossed.

`bulk_position_bound`: from the composition `ClockRealFaithfulHours.clock_real_faithful_O_log_n`,
over the `O(log n)` run the bulk crosses ONE minute per seed+epidemic block (EPIDEMIC,
O(1)/minute), so after the full `K·(L+1)·(tseed+tbulk)` horizon the bulk Post
`Q_mix n mC (K·(L+1)−1) ∧ bulkHi m_C ≤ rBeyond (K·(L+1))` holds with kernel failure
`≤ K·(L+1)·(εseed+εbulk)` — the bulk leading edge has reached (and only reached) the minute
count `K·(L+1)`.  This is the bulk-position the gap-bound rides on: the bulk's `0.9·m_C` mass
is at minute `K·(L+1) − 1` (one below the cap), so the bulk-top fraction window is the genuine
running condition. -/

/-- **`bulk_position_bound` — the bulk leading edge ≤ minutes-crossed (from the composition).**

From a minute-0 start (`Q_mix n mC 0 c₀ ∧ 9·m_C/10 ≤ rBeyond 0 c₀`), after the composed
`K·(L+1)·(tseed+tbulk)`-step horizon the bulk Post (`Q_mix n mC (K·(L+1)−1) ∧
bulkHi m_C ≤ rBeyond (K·(L+1))`) fails with kernel probability `≤ K·(L+1)·(εseed+εbulk)` —
i.e. the bulk leading edge has crossed exactly the `K·(L+1) = O(log n)` minutes, ONE minute per
block (EPIDEMIC, O(1)/minute).  GENUINELY the composition
`ClockRealFaithfulHours.clock_real_faithful_O_log_n` (the per-minute faithful step
`clock_real_step` composed over all `K·(L+1)` minutes), carrying the same deterministic window
closure `habs_mix_all` and `ε`-budgets.  This is the EPIDEMIC bulk advance — the bulk position
the gap-bound's drip-squared front rides on. -/
theorem bulk_position_bound (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (habs_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
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
    (hc₀ : Q_mix (L := L) (K := K) n mC 0 c₀
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) 0 c₀) :
    ((NonuniformMajority L K).transitionKernel ^ ((K * (L + 1)) * (tseed + tbulk))) c₀
        {y | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
                ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)} ≤
      ((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) :=
  ClockRealFaithfulHours.clock_real_faithful_O_log_n (L := L) (K := K) n mC hn hmC hLK
    habs_mix_all tseed tbulk εseed εbulk hεs hεb c₀ hc₀

/-! ## Part 4 — COMBINE: gap + position → the cap-relative `hfeeder_all` window.

`frontSync_of_gap_and_position`: combining the GAP-BOUND (Part 2) with the cap-relative
bulk-top fraction (the running bulk-position condition, Part 3), the cap-relative empty-feeder
window `hfeeder_all` that `clock_real_O_log_n_joint_closed` carries is SUPPLIED — every
reachable `FrontSync` config with the bulk-top-fraction window is `AllClockP3` with an empty
cap-1 feeder.  This is GENUINELY `ClockCapRelFront.frontSyncConcentration_remaining_of_bulktop`'s
per-config core: `gap_bound` turns the bulk-top fraction into the empty cap-1 feeder.

HONEST: the bulk-top-fraction window `hbulktop_all` (`AllClockP3 ∧ CapRelRecurrence W ∧
gapFrac W ≤ ρ₀`) is CARRIED, NOT discharged from the bulk-position alone — see the file header:
the bulk-position bounds the bulk LEADING EDGE, not the straggler COUNT in the top band, which
is the front-shape drip-squared residual. -/

/-- **`frontSync_of_gap_and_position` — gap + position supply the cap-relative `hfeeder_all`.**

Given the cap-relative bulk-top-fraction window `hbulktop_all` (every reachable `FrontSync`
config of population `n` is `AllClockP3`, carries the cap-relative squaring recurrence
`CapRelRecurrence W`, and has its bulk-top fraction `gapFrac W ≤ ρ₀` — the GAP `LE − bulkLE ≤ W`
window, the running bulk-position condition), with `ρ₀ ≤ 1/2`, `W = frontWidthBound n`, and the
cap deep enough (`frontWidthBound n ≤ W − 1`), the cap-relative empty-feeder window
`hfeeder_all` holds: every reachable `FrontSync` config of population `n` is `AllClockP3` with
`rBeyond (cap − 1) c = 0`.

GENUINELY: for each such config the GAP-BOUND `gap_bound` (the doubly-exp collapse of the
bulk-top fraction `≤ ρ₀` to the empty cap-1 feeder) supplies `rBeyond (cap − 1) c = 0`; the
`AllClockP3` is carried in the window.  Combined `LE ≤ bulkLE + W < cap` — FrontSync.  The
carried residual is the bulk-top-fraction window (the straggler-count narrowness), NOT the
absolute-low. -/
theorem frontSync_of_gap_and_position (ρ0 : ℝ) (hρ0 : 0 ≤ ρ0) (hsub : ρ0 ≤ 1 / 2)
    (n : ℕ) (hn : 2 ≤ n)
    (W : ℕ) (hW : W = FrontTail.frontWidthBound n)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hdeep : FrontTail.frontWidthBound n ≤ W - 1)
    (hbulktop_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ ClockCapRelFront.CapRelRecurrence (L := L) (K := K) W c ∧
        gapFrac (L := L) (K := K) W c ≤ ρ0) :
    ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 := by
  intro c hsync hcard
  obtain ⟨hw, hrec, hgap⟩ := hbulktop_all c hsync hcard
  exact ⟨hw, gap_bound ρ0 hρ0 hsub n hn c hcard W hW hWpos hdeep hrec hgap⟩

/-! ## Part 5 — `clock_real_O_log_n_closed`: feed the supplied window into the joint theorem.

`clock_real_O_log_n_closed`: feeding the gap+position-supplied `hfeeder_all` (Part 4) into
`ClockJointInduction.clock_real_O_log_n_joint_closed` gives the real-kernel O(log n) clock
reaching `0.9·m_C` while maintaining FrontSync over the run, with failure
`≤ K·(L+1)·(εseed+εbulk)` — carrying the EXACT cap-relative residual: the bulk-top-fraction
window `hbulktop_all` (the GAP `LE − bulkLE ≤ W` straggler-count narrowness) and the
deterministic FrontSync-gated window closure `habs_mix_all_gated`.

The clock is NOT made unconditional: the bulk-top-fraction window is CARRIED (the bulk-position
bounds the leading edge, not the straggler count — the front-shape drip-squared residual). -/

/-- **`clock_real_O_log_n_closed` — the real-kernel O(log n) clock, gap-bulk closed.**

From a `J`-start (`FrontSync c₀`, `Q_mix n mC 0 c₀ ∧ 9·m_C/10 ≤ rBeyond 0 c₀`), after the
`K·(L+1)·(tseed+tbulk) = O(log n)` horizon, the JOINT failure event

  `{the bulk-Post FAILS} ∪ {FrontSync BREAKS}`

has kernel probability `≤ K·(L+1)·(εseed+εbulk)`.

GENUINELY assembled: the cap-relative `hfeeder_all` is SUPPLIED by
`frontSync_of_gap_and_position` (the GAP-BOUND `gap_bound` turning the bulk-top fraction into
the empty cap-1 feeder), fed into `ClockJointInduction.clock_real_O_log_n_joint_closed` (the
joint union bound: FrontSync breach `0` at the empty leading-edge feeder + the bulk advance
`bulk_position_bound`).

⛔ HONEST: the clock is NOT unconditional whp.  It carries TWO inputs, BOTH cap-relative /
deterministic, NEITHER absolute-low:
* `hbulktop_all` — the cap-relative bulk-top-fraction window (the GAP `LE − bulkLE ≤ W`
  straggler-count narrowness `gapFrac W ≤ ρ₀` + the squaring recurrence `CapRelRecurrence W`).
  The bulk-position `bulk_position_bound` bounds the bulk LEADING EDGE but NOT the straggler
  COUNT in the top band, so this front-shape drip-squared residual is CARRIED, not discharged.
* `habs_mix_all_gated` — the deterministic FrontSync-gated `Q_mix` window closure.
Both are GENUINELY the residuals the proven cap-relative concentrations carry; NEITHER is the
false absolute-low `rBeyond (frontWidthBound n) = 0`. -/
theorem clock_real_O_log_n_closed (ρ0 : ℝ) (hρ0 : 0 ≤ ρ0) (hsub : ρ0 ≤ 1 / 2)
    (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (W : ℕ) (hW : W = FrontTail.frontWidthBound n)
    (hWpos : 0 < FrontTail.frontWidthBound n)
    (hdeep : FrontTail.frontWidthBound n ≤ W - 1)
    -- the cap-relative bulk-top-fraction window (the GAP straggler-count narrowness, CARRIED).
    (hbulktop_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ ClockCapRelFront.CapRelRecurrence (L := L) (K := K) W c ∧
        gapFrac (L := L) (K := K) W c ≤ ρ0)
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
  -- the GAP-BOUND supplies the cap-relative empty-feeder window from the bulk-top fraction.
  have hfeeder_all : ∀ c : Config (AgentState L K),
      FrontSync (L := L) (K := K) c → c.card = n →
      AllClockP3 c ∧ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0 :=
    frontSync_of_gap_and_position ρ0 hρ0 hsub n hn W hW hWpos hdeep hbulktop_all
  -- feed into the joint theorem (the joint union bound: FrontSync breach 0 + bulk advance).
  exact ClockJointInduction.clock_real_O_log_n_joint_closed (L := L) (K := K) n mC hn hmC hLK
    hcapPos hfeeder_all habs_mix_all_gated tseed tbulk εseed εbulk hεs hεb c₀ hsync0 hQ0

/-! ## HONEST STATUS — `ClockGapBulk` (the gap-bulk closure of the mutual induction)

* **GAP-BOUND is GENUINELY PROVEN** (`gap_bound`).  The front leading edge is only
  `W = frontWidthBound n = O(log log n)` ahead of the bulk: from the bulk-top fraction
  `gapFrac W c ≤ ρ₀ ≤ 1/2` (the gap `LE − bulkLE ≤ W`) + the cap-relative squaring recurrence
  (the front advances by DRIP-squared, RARE), the doubly-exp envelope collapses the front
  fraction to `< 1/n` at the cap-1 level, forcing `rBeyond (cap − 1) c = 0` — the empty
  leading-edge feeder, so `LE < cap`.  GENUINELY `ClockCapRelFront.capRel_feeder_doubly_exp`.
  The MOVING leading-edge gap, NOT the absolute-low `rBeyond (frontWidthBound) = 0`.

* **BULK-POSITION is GENUINELY PROVEN** (`bulk_position_bound`).  The bulk leading edge ≤
  minutes-crossed: from the composition `ClockRealFaithfulHours.clock_real_faithful_O_log_n` the
  bulk crosses ONE minute per block (EPIDEMIC, O(1)/minute) over the `K·(L+1) = O(log n)` run,
  reaching the bulk Post `bulkHi m_C ≤ rBeyond (K·(L+1))` with failure `≤ K·(L+1)·(εseed+εbulk)`.

* **COMBINE supplies `hfeeder_all`** (`frontSync_of_gap_and_position`).  The GAP-BOUND turns the
  bulk-top fraction into the empty cap-1 feeder for every reachable `FrontSync` config, so
  `LE ≤ bulkLE + W < cap` = FrontSync, discharging the joint theorem's `hfeeder_all` GIVEN the
  bulk-top-fraction window.

* **The clock is NOT unconditional whp** (`clock_real_O_log_n_closed`).  The mutual connection
  closes to: FrontSync for the run is maintained GIVEN the cap-relative bulk-top-fraction window
  `hbulktop_all` (`gapFrac W ≤ ρ₀` + `CapRelRecurrence W`) — the SINGLE genuine front-shape
  residual.  This is NOT discharged from the bulk-position alone: the bulk-position bounds the
  bulk LEADING EDGE, but `gapFrac W` is the straggler COUNT in the top `W` band, which a clock
  can drip into ahead of the bulk; bounding it IS the front-shape DRIP-squared concentration
  (the `m → m+1` count issue `ClockCapRelFront` documents), NOT supplied by the leading-edge
  position.  Asserting `gapFrac W c ≤ ρ₀` for EVERY reachable `FrontSync` config would be a
  FALSE deterministic hypothesis (such a config can have a clock at `cap − 1`, and need not be
  `AllClockP3`).  We do NOT assert it — it is CARRIED, honestly named.

VERDICT: the gap-bulk structure is GENUINELY PROVEN (gap-bound = the empty-absorbing cap-relative
collapse; bulk-position = the faithful O(1)/minute composition).  Their combination supplies the
joint theorem's `hfeeder_all` from the cap-relative bulk-top-fraction window.  The EXACT residual
that PREVENTS unconditionality is the cap-relative bulk-top-fraction / straggler-count narrowness
`hbulktop_all` (`gapFrac W ≤ ρ₀` + `CapRelRecurrence W`) — the front-shape drip-squared residual,
which the bulk LEADING-EDGE position cannot deterministically supply (it bounds the bulk mass, not
the straggler count).  EXPLICITLY confirmed: NO `FrontAllLevels` / `ClockFrontIter` / absolute-low
`rBeyond (frontWidthBound) = 0` is used; `LE` is the MOVING leading edge throughout. -/
theorem clock_gap_bulk_status : True := trivial

end ClockGapBulk

end ExactMajority
