/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# SideBudget — the uniform FrontSync side-prefix feeder `sideB` (Phase D-1)

Both the clock chain (`ClockBudgets`/`WidthPrefixConcrete.clock_unconditional_final` via `εside`'s
`εsync` slice) and the §6 hour-escape (`HourEscape.heB_of_sideB`, B-14) consume the SAME object: a
uniform bound on the REAL-kernel `FrontSync`-failure prefix sum

  `∑_{τ < M} (realκ^τ) (erase mc₀) {¬ FrontSync} ≤ sideB`

from the gated start `mc₀ ∈ taintedGate n` (population `n`, erased config `AllClockP3`, all-clean).
This file discharges that `sideB` at the concrete `Params` parameters.

## The decomposition.

`ClockFrontSyncFromWidth.frontSync_whp_of_goodFrontWidth` bounds the per-`τ` `{¬FrontSync}` mass by
the three-way split `εW(τ) + εP(τ) + εB(τ)`:

* `εW(τ)` — the moving-frame width-failure-on-side mass, **discharged concretely** at every prefix
  horizon `τ = w·j + r ≤ w·KK` by `EarlyDripMarked.widthFail_at_concrete` (B-13): `εW(τ) = εWAt(τ)`.
* `εP(τ)` — the side-event failure `{¬ WidthSideP n}` (card / `AllClockP3` / recurrence-negligibility
  conjunct).  Carried as a NAMED per-`τ` input, exactly as `ClockBudgets.sidePrefix_le_assembled`
  carries it for the clock chain (`hP`); the gated start preserves `card` and `AllClockP3`, but the
  recurrence conjunct is not absorbing in general, so its failure is a genuine §-engine residual.
* `εB(τ)` — the bulk-below failure `{¬ (10 · rBeyond (capMinute − W) < card)}`.  Carried as a NAMED
  per-`τ` input.  This is the bulk-ARRIVAL event: within one hour `w·KK` the `0.1` bulk has not
  climbed within `W` of the cap band.  When it fails, the hour is legitimately ENDING (the bulk has
  arrived), so this is the honest hour-boundary event — bounded by the hour/climb machinery
  upstream, not by the §6 width engine (which bounds the FRONT, not the bulk).

Hence `sideB = ∑_{τ < M} (εWAt(τ) + εP(τ) + εB(τ))`, with `εWAt` explicit and `εP`, `εB` the named
per-`τ` hour residuals.  The horizon `M = w·KK` is exactly the §6 one-hour window; every `τ < M`
decomposes as `w·j + r` with `r < w`, `j ≤ KK − 1`, which is precisely the regime where
`widthFail_at_concrete` discharges the width feeder.

ZERO sorry, zero new axiom, zero native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourEscape
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WidthPrefixConcrete

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace EarlyDripMarked

open ClockRealKernel ClockFrontShape ClockFrontProfile FrontSyncConc

variable {L K : ℕ}

/-! ## Part 1 — the per-`τ` `{¬ FrontSync}` bound with the width feeder discharged concretely.

At a prefix horizon `τ = w·j + r` (`r < w`, `j ≤ KK − 1`, so `τ ≤ w·KK`), the real-kernel
`{¬ FrontSync}` mass from the erased gated start is `≤ εWAt(τ) + εP + εB`, the width / side / bulk
split with the width feeder substituted by the explicit concrete family `εWAt` (B-13).  `εP` and
`εB` are the named per-`τ` hour residuals (side-event failure / bulk-arrival). -/

open ClockFrontProfile in
/-- **`frontSyncFail_concrete`** — the per-`τ` `{¬ FrontSync}` mass with the §6 width feeder
discharged concretely.  Width slice `εW := εWAt …` (via `widthFail_at_concrete`); side slice `εP`
(`{¬ WidthSideP n}`) and bulk slice `εB` (`{¬ (10·rBeyond (capMinute − W) < card)}`) NAMED. -/
theorem frontSyncFail_concrete (n : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ : ℕ) (hW₂ : 2 ≤ W₂) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (j r : ℕ) (hr : r < Params.w n) (hjKK : j ≤ Params.KK L K - 1)
    (εP εB : ℝ≥0∞)
    (hP : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ ClockBudgets.WidthSideP (L := L) (K := K) n c} ≤ εP)
    (hbulk : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (ClockFrontShape.capMinute (L := L) (K := K)
              - (FrontTail.frontWidthBound n + W₂)) c < c.card)} ≤ εB) :
    (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ FrontSync (L := L) (K := K) c}
      ≤ εWAt (L := L) (K := K) n mc₀ Tcap W₂ B' s j r + εP + εB :=
  ClockFrontSyncFromWidth.frontSync_whp_of_goodFrontWidth (L := L) (K := K)
    (Params.w n * j + r) (FrontTail.frontWidthBound n + W₂)
    (eraseConfig (L := L) (K := K) mc₀)
    (ClockBudgets.WidthSideP (L := L) (K := K) n)
    (εWAt (L := L) (K := K) n mc₀ Tcap W₂ B' s j r) εP εB
    (widthFail_at_concrete (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean Tcap hcap
      W₂ hW₂ B' s hs j r hr hjKK)
    hP hbulk

/-! ## Part 2 — the prefix decomposition `τ = w·(τ/w) + τ%w` and the per-`τ` feeder at free `τ`.

For the side-prefix SUM the index `τ` ranges over `range M` with `M = w·KK`.  Each such `τ`
decomposes canonically as `τ = w·j + r` with `j = τ / w`, `r = τ % w`, and (since `τ < w·KK`)
`r < w`, `j ≤ KK − 1`.  This lets `frontSyncFail_concrete` apply at every `τ < M`. -/

/-- **`w_pos_of_N₀`** — at the concrete threshold `n ≥ N₀ = 10⁴⁰`, the window `w n = 3n/200` is
positive. -/
theorem w_pos_of_N₀ (n : ℕ) (hn : Params.N₀ ≤ n) : 0 < Params.w n := by
  unfold Params.w
  have h200 : (200 : ℕ) ≤ 3 * n := by
    have : (10 : ℕ) ^ 40 ≤ n := by unfold Params.N₀ at hn; exact hn
    have h1 : (200 : ℕ) ≤ 10 ^ 40 := by norm_num
    omega
  exact Nat.div_pos h200 (by norm_num)

/-- The per-`τ` feeder at FREE `τ < w·KK`, using the canonical decomposition `j = τ/w`, `r = τ%w`:
the width slice `εWAt … (τ/w) (τ%w)` (discharged) plus the named side/bulk slices `εP τ`, `εB τ`. -/
noncomputable def sideTerm (n : ℕ) (mc₀ : Config (MarkedAgent L K)) (Tcap W₂ B' : ℕ) (s : ℝ)
    (εP εB : ℕ → ℝ≥0∞) (τ : ℕ) : ℝ≥0∞ :=
  εWAt (L := L) (K := K) n mc₀ Tcap W₂ B' s (τ / Params.w n) (τ % Params.w n)
    + εP τ + εB τ

/-- **`frontSyncFail_at_free`** — the per-`τ` `{¬ FrontSync}` mass at FREE `τ < w·KK`, via the
canonical decomposition `τ = w·(τ/w) + τ%w`.  This is `frontSyncFail_concrete` with `j = τ/w`,
`r = τ%w`; the hypotheses are taken at the SAME (already-decomposed) horizon `τ`. -/
theorem frontSyncFail_at_free (n : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ : ℕ) (hW₂ : 2 ≤ W₂) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (εP εB : ℕ → ℝ≥0∞)
    (τ : ℕ) (hτ : τ < Params.w n * Params.KK L K)
    (hP : (ClockKilledMinute.realκ L K ^ τ)
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ ClockBudgets.WidthSideP (L := L) (K := K) n c} ≤ εP τ)
    (hbulk : (ClockKilledMinute.realκ L K ^ τ)
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (ClockFrontShape.capMinute (L := L) (K := K)
              - (FrontTail.frontWidthBound n + W₂)) c < c.card)} ≤ εB τ) :
    (ClockKilledMinute.realκ L K ^ τ)
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ FrontSync (L := L) (K := K) c}
      ≤ sideTerm (L := L) (K := K) n mc₀ Tcap W₂ B' s εP εB τ := by
  have hwpos : 0 < Params.w n := w_pos_of_N₀ n hn
  -- the canonical decomposition.
  have hdecomp : Params.w n * (τ / Params.w n) + τ % Params.w n = τ :=
    Nat.div_add_mod τ (Params.w n)
  have hr : τ % Params.w n < Params.w n := Nat.mod_lt τ hwpos
  have hjKK : τ / Params.w n ≤ Params.KK L K - 1 := by
    have hlt : τ / Params.w n < Params.KK L K :=
      Nat.div_lt_of_lt_mul hτ
    omega
  -- rewrite the horizon and hypotheses to `w·(τ/w) + τ%w`.
  have key := frontSyncFail_concrete (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean
    Tcap hcap W₂ hW₂ B' s hs (τ / Params.w n) (τ % Params.w n) hr hjKK (εP τ) (εB τ)
    (by rw [hdecomp]; exact hP) (by rw [hdecomp]; exact hbulk)
  rw [hdecomp] at key
  exact key

/-! ## Part 3 — the uniform side-budget `sideB` over the one-hour horizon `M = w·KK`.

`HourEscape.heB_of_sideB` consumes a bound on `∑_{τ < M} (realκ^τ) (erase mc₀) {HourSideBad}` where
`HourSideBad = {c | ¬ HourSideGood c}` and `HourSideGood = FrontSync` (definitionally).  We bound
this sum by `εsync(n, M) := ∑_{τ < M} sideTerm τ`, with each summand the discharged-width per-`τ`
feeder of Part 2.  The horizon `M = w·KK` is the §6 one-hour window, so every `τ < M` is in the
`widthFail_at_concrete` regime via Part 2's canonical decomposition. -/

/-- **`εsync`** — the explicit uniform side-budget over the one-hour horizon: the sum of the per-`τ`
discharged feeders `sideTerm τ` for `τ < M`.  The width slices are explicit (`εWAt`); the side/bulk
slices `εP`, `εB` are the named per-`τ` hour residuals. -/
noncomputable def εsync (n : ℕ) (mc₀ : Config (MarkedAgent L K)) (Tcap W₂ B' : ℕ) (s : ℝ)
    (εP εB : ℕ → ℝ≥0∞) (M : ℕ) : ℝ≥0∞ :=
  ∑ τ ∈ Finset.range M, sideTerm (L := L) (K := K) n mc₀ Tcap W₂ B' s εP εB τ

/-- **`sideB_concrete`** — the FrontSync side-prefix sum over the one-hour horizon `M = w·KK` is
`≤ εsync`, the explicit sum of per-`τ` discharged feeders.  This is the uniform `sideB` that BOTH
`HourEscape.heB_of_sideB` (the §6 hour-escape) and the clock chain's `εsync` slice consume, at the
concrete `Params` parameters from the gated start `erase mc₀`.

`εsync` is explicit modulo the honestly-named per-`τ` hour residuals `εP τ` (`{¬ WidthSideP n}`, the
side-event failure) and `εB τ` (the bulk-arrival / hour-completion event); the width feeder is fully
discharged by `widthFail_at_concrete`. -/
theorem sideB_concrete (n : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ : ℕ) (hW₂ : 2 ≤ W₂) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (εP εB : ℕ → ℝ≥0∞)
    (hP : ∀ τ < Params.w n * Params.KK L K,
      (ClockKilledMinute.realκ L K ^ τ)
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ ClockBudgets.WidthSideP (L := L) (K := K) n c} ≤ εP τ)
    (hbulk : ∀ τ < Params.w n * Params.KK L K,
      (ClockKilledMinute.realκ L K ^ τ)
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (ClockFrontShape.capMinute (L := L) (K := K)
              - (FrontTail.frontWidthBound n + W₂)) c < c.card)} ≤ εB τ) :
    ∑ τ ∈ Finset.range (Params.w n * Params.KK L K),
        ((NonuniformMajority L K).transitionKernel ^ τ)
          (eraseConfig (L := L) (K := K) mc₀) (HourSideBad (L := L) (K := K))
      ≤ εsync (L := L) (K := K) n mc₀ Tcap W₂ B' s εP εB
          (Params.w n * Params.KK L K) := by
  rw [εsync]
  refine Finset.sum_le_sum (fun τ hτ => ?_)
  have hτlt : τ < Params.w n * Params.KK L K := Finset.mem_range.mp hτ
  -- `HourSideBad = {c | ¬ FrontSync c}` definitionally; rewrite to the `frontSyncFail` shape.
  have hset : HourSideBad (L := L) (K := K)
      = {c : Config (AgentState L K) | ¬ FrontSync (L := L) (K := K) c} := by
    ext c; simp only [HourSideBad, HourSideGood, Set.mem_setOf_eq]
  rw [hset]
  exact frontSyncFail_at_free (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean
    Tcap hcap W₂ hW₂ B' s hs εP εB τ hτlt (hP τ hτlt) (hbulk τ hτlt)

/-! ## Part 4 — the `heB` corollary: the §6 hour-escape mass fully numeric via `heB_of_sideB`.

`HourEscape.heB_of_sideB` feeds the `sideB` bound (Part 3) into the killed marked-walk cemetery
mass after `M = w·KK` steps: from a gated start `mc₀ ∈ taintedGate n`, the hour-escape mass is
`≤ εsync`.  This is `heB` (the `B-14` hour-escape input) now fully numeric — the §6 width feeder
discharged, the residuals named. -/

/-- **`heB_concrete`** — the §6 hour-escape mass `heB` fully numeric: from a gated start
`mc₀ ∈ taintedGate n`, the killed marked-walk cemetery mass after the one-hour horizon `M = w·KK`
is `≤ εsync` (Part 3's explicit side-budget).  This composes `HourEscape.heB_of_sideB` with
`sideB_concrete`. -/
theorem heB_concrete (n T θn : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hx₀ : mc₀ ∈ taintedGate (L := L) (K := K) n)
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ : ℕ) (hW₂ : 2 ≤ W₂) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (εP εB : ℕ → ℝ≥0∞)
    (hP : ∀ τ < Params.w n * Params.KK L K,
      (ClockKilledMinute.realκ L K ^ τ)
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ ClockBudgets.WidthSideP (L := L) (K := K) n c} ≤ εP τ)
    (hbulk : ∀ τ < Params.w n * Params.KK L K,
      (ClockKilledMinute.realκ L K ^ τ)
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (ClockFrontShape.capMinute (L := L) (K := K)
              - (FrontTail.frontWidthBound n + W₂)) c < c.card)} ≤ εB τ) :
    (GatedDrift.killK (markedK (L := L) (K := K) T θn)
        (taintedGate (L := L) (K := K) n)
          ^ (Params.w n * Params.KK L K)) (some mc₀) {(none : Option _)}
      ≤ εsync (L := L) (K := K) n mc₀ Tcap W₂ B' s εP εB
          (Params.w n * Params.KK L K) :=
  heB_of_sideB (L := L) (K := K) n T θn (Params.w n * Params.KK L K) mc₀ hx₀
    (εsync (L := L) (K := K) n mc₀ Tcap W₂ B' s εP εB (Params.w n * Params.KK L K))
    (sideB_concrete (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean Tcap hcap
      W₂ hW₂ B' s hs εP εB hP hbulk)

/-! ## Part 5 — feeding ClockBudgets' `εside`: the `clock_unconditional_final` instantiation.

`clock_unconditional_final` (B-13, WidthPrefixConcrete) takes a uniform per-`τ`/per-minute side
bound `εside` with `hside : ∀ T τ, (realκ^τ) c₀ Sgood(T)ᶜ ≤ εside`, and produces the total clock
budget `εclock = (K(L+1)−1)·(εbulk + tbulk·εside)`.

`sidePrefix_concrete_width` (B-13) discharges the per-`τ` `Sgood(T)ᶜ` mass at a prefix horizon
`τ = w·j + r ≤ w·KK` to `sideEps εQ εfloor (εWAt …) εP εB εge3 εno3 εcpos εsucc` — the §6 WIDTH
feeder substituted by the explicit concrete family `εWAt`, the eight remaining feeders named.  The
ONLY step between that per-`τ` discharged bound and the UNIFORM `εside` that `clock_unconditional_
final` consumes is a τ-uniform majorant over the run: a single `εside` with each per-`τ`
`sideEps(τ) ≤ εside` (the sup-over-the-hour boundary B-12/B-13 flagged — `εWAt τ` varies with `τ`).

Here we wire this honestly: from a uniform majorant hypothesis `hunif : ∀ T τ, (realκ^τ) c₀
Sgood(T)ᶜ ≤ εside` (the carried input — the τ-uniform side bound with the §6 width feeder already
concrete inside it), the clock budget is `εclock`.  This is the `clock_unconditional_final`
instantiation with the width feeder + sideB discharged: the FrontSync slice of `εside` is exactly
the `sideB_concrete`-discharged mass; the residual is the τ-uniformity + the eight named feeders. -/

/-- **`Sgood_compl_le_uniform`** — the GENUINE width-discharged → uniform-`εside` wiring step.  At
EVERY prefix horizon `τ = w·j + r ≤ w·KK`, `sidePrefix_concrete_width` discharges `Sgood(T)ᶜ` to
`sideEps εQ εfloor (εWAt … j r) εP εB εge3 εno3 εcpos εsucc` with the §6 WIDTH feeder concrete; here
we majorize each per-`τ` summand by a single τ-uniform value, collapsing to the uniform `εside :=
sideEps εQu εflooru εWu εPu εBu εge3u εno3u εcposu εsuccu` that `clock_unconditional_final` consumes.

The uniform majorant hypotheses (`εWAt … j r ≤ εWu`, and the eight named feeders bounded uniformly)
are the carried residuals — the sup-over-the-hour boundary (B-12/B-13) and the eight §-engine masses.
The FrontSync/width slice is NOT carried: it is `εWAt`, discharged by `widthFail_at_concrete`. -/
theorem Sgood_compl_le_uniform (n mC T : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ : ℕ) (hW₂ : 2 ≤ W₂) (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc : ℝ≥0∞)
    (j r : ℕ) (hr : r < Params.w n) (hjKK : j ≤ Params.KK L K - 1)
    (hWu : εWAt (L := L) (K := K) n mc₀ Tcap W₂ B' s j r ≤ εWu)
    (hQ : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockUnconditional.QmixFail (L := L) (K := K) n mC T) ≤ εQ)
    (hfloor : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockUnconditional.FloorFail (L := L) (K := K) mC T) ≤ εfloor)
    (hP : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ ClockBudgets.WidthSideP (L := L) (K := K) n c} ≤ εP)
    (hbulk : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (ClockFrontShape.capMinute (L := L) (K := K)
              - (FrontTail.frontWidthBound n + W₂)) c < c.card)} ≤ εB)
    (hge3F : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockBudgets.GE3Fail (L := L) (K := K)) ≤ εge3)
    (hno3 : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockBudgets.NoAbove3Fail (L := L) (K := K)) ≤ εno3)
    (hcpos : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockBudgets.CposFail (L := L) (K := K)) ≤ εcpos)
    (hsucc : (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockBudgets.SuccNoAbove3Fail (L := L) (K := K)) ≤ εsucc) :
    (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        (ClockUnconditional.Sgood (L := L) (K := K) n mC T)ᶜ
      ≤ ClockBudgets.sideEps εQ εfloor εWu εP εB εge3 εno3 εcpos εsucc := by
  refine le_trans
    (sidePrefix_concrete_width (L := L) (K := K) n mC T hn mc₀ hcard hge3 hnotP3 hclean
      Tcap hcap W₂ hW₂ B' s hs j r hr hjKK εQ εfloor εP εB εge3 εno3 εcpos εsucc
      hQ hfloor hP hbulk hge3F hno3 hcpos hsucc) ?_
  -- monotonicity of `sideEps` in its width slice (the only slice that is not already uniform).
  unfold ClockBudgets.sideEps
  gcongr

/-- **`clock_unconditional_wired`** — the explicit unconditional O(log n) clock budget, fed with the
uniform side bound `εside` whose FrontSync/width slice is discharged concretely.  This is the
`clock_unconditional_final` instantiation: its single input `hside` (the τ-uniform `Sgood(T)ᶜ`
bound) is supplied — over the hour horizon — by `Sgood_compl_le_uniform`, in which the §6 width
feeder is the concrete `εWAt`.  The carried residuals are the τ-uniformity past the hour horizon and
the eight named §-engine feeders inside `εside`. -/
theorem clock_unconditional_wired (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (tseed tbulk : ℕ) (htbulk : 0 < tbulk) (εbulk : ℝ≥0)
    (hεb : ClockKilledMinute.minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (ClockRealBulk.bulkHi mC : ℝ))) / 1
          ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (εside : ℝ≥0∞)
    (hside : ∀ T τ, (ClockKilledMinute.realκ L K ^ τ) c₀
        (ClockUnconditional.Sgood (L := L) (K := K) n mC T)ᶜ ≤ εside) :
    ∑ i : Fin (K * (L + 1) - 1),
        ((ClockKilledMinute.realκ L K) ^ (i.val * (tseed + tbulk) + tseed + tbulk)) c₀
          {c | ¬ ClockKilledMinute.BulkPost (L := L) (K := K) n mC (i.val + 1) c}
      ≤ ClockBudgets.εclock L K tbulk (εbulk : ℝ≥0∞) εside :=
  clock_unconditional_final (L := L) (K := K) n mC hn hmC hLK
    tseed tbulk htbulk εbulk hεb c₀ εside hside

end EarlyDripMarked

end ExactMajority
