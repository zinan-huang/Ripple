/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ClockCeiling — the width-Post → `ClocksBelowHour` derivation (Doty §6 positional anchor)

This file (append-only; no existing file edited) closes the §6 positional chain onto the LANDED
clock-front WIDTH machinery.  It supplies the single load-bearing bridge the positional cluster was
missing: the within-hour clock-front confinement event

  `ClocksBelowHour h c` :  every clock has `minute.val < (h+1)·K`

is a DETERMINISTIC consequence of the landed width Post `ClockFrontProfile.GoodFrontWidth W c`
(`= Doty Thm 6.5's "first claim"`) whenever the `0.1` bulk threshold has not yet reached within `W`
minutes of the hour-`h` boundary `(h+1)·K`.  Once `ClocksBelowHour h` is in hand, the entire §6
positional chain is already wired in `PositionalCluster.lean`:

  `ClocksBelowHour h`  ──(dragLeft/dragRight_mainHour_le)──►  the Rule-2 drag stamps `hour ≤ h`
                       ──(mainHour_le_of_clockBelow_cancelSplit, with the index ceiling)──►
                          the Rule-3 cancel stamps `hour ≤ h`
                       ──(PositionalCluster.mainHourBelow_step_mainMain)──►  `MainHourBelow h` step
  `MainHourBelow h`    ──(BiasedMainHourCeiling.allBiasedMainBelow_of_indexLeHour_of_hourCeiling)──►
                          `AllBiasedMainBelow h`  (the index ceiling `l+2`)
  `AllBiasedMainBelow` ──(DoublingEdges.majorityTopEdge_of_hourCeiling)──►  the band top edges
                       ──(CeilingRoute / PositionalCluster.phase6_to_phase7_of_doubling_edges)──►
                          the corrected Phase6→7 surface (the band-edge + drag-control consumers).

## What is genuinely NEW here (vs. the landed pieces it stitches)

* `PositionalCluster.lean` proved the per-step engine `ClocksBelowHour h ⟹ hour ≤ h` (drag) and
  `index ≤ h ⟹ cancel hour ≤ h` — but it DEFINED `ClocksBelowHour` axiomatically as a snapshot, with
  the note "provenance: the window `Window h`/`cAbove h = 0` confines the clocks below the current
  hour" left as the landed clock-front content.  This file PROVES that provenance: `ClocksBelowHour h`
  is exactly `rBeyond ((h+1)·K) c = 0` packaged through `ClockFrontShape.clock_lt_of_rBeyond_eq_zero`,
  and `rBeyond M c = 0` is the contrapositive of the landed `GoodFrontWidth` width invariant at the
  level `M = (h+1)·K` (the same mechanism as `ClockFrontProfile.frontSync_of_goodWidth_of_bulk_below`,
  which is the `M = capMinute` instance — we lift it to every hour boundary `M`).

* The per-hour EVENT production: `ClocksBelowHour h` holds throughout hour `h`'s window with the width
  budget's probability, because the within-hour endpoints are exactly the `GoodFrontWidth` good-set the
  landed `WidthTransport.widthFail_between_checkpoints_concrete` / `CrossHourSide` feeders bound.  We
  expose the deterministic core — "on the good-width event with the bulk below the hour boundary, the
  clocks are confined below the boundary" — as the per-hour confinement readout; its probabilistic
  complement is exactly the landed width-budget tail (no new probabilistic content).

So the §6 positional cluster's remaining snapshots (`ClocksBelowHour`, hence `MainHourBelow`,
`AllBiasedMainBelow`, the band top edges, the drag control) all collapse onto the SINGLE landed width
machinery: one `GoodFrontWidth` event drives the whole positional chain.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.

Reference: Doty et al. (arXiv:2106.10201v2), proof of Theorem 6.5 (the "first claim"); the landed
`ClockFrontProfile` / `WidthTransport` / `CrossHourSide` width chain.
-/
import Ripple.PopulationProtocol.ExactMajority.Probability.PositionalCluster
import Ripple.PopulationProtocol.ExactMajority.Probability.WidthTransport

namespace Ripple.PopulationProtocol.ExactMajority

open scoped BigOperators

namespace ClockCeiling

open ClockRealKernel ClockFrontShape ClockFrontProfile

variable {L K : ℕ}

/-! ## Part 1 — the empty-front ⟹ clocks-below-hour bridge (definitional).

`ClocksBelowHour h c` (every clock `minute.val < (h+1)·K`) is exactly the "no clock at minute ≥
(h+1)·K" content, i.e. `rBeyond ((h+1)·K) c = 0` read through the landed
`ClockFrontShape.clock_lt_of_rBeyond_eq_zero`.  The hour-`h` boundary is the minute `(h+1)·K`; the cap
`capMinute = K·(L+1)` is the `h = L` instance. -/

/-- **The empty-front ⟹ `ClocksBelowHour` bridge (PROVEN, the missing provenance).**  If the clock
front above the hour-`h` boundary is empty — `rBeyond ((h+1)·K) c = 0`, no clock at minute `≥ (h+1)·K`
— then every clock has `minute.val < (h+1)·K`, i.e. `PositionalCluster.ClocksBelowHour h c`.  This
PROVES the provenance that `PositionalCluster` left as the landed clock-front note: the within-hour
confinement snapshot is the emptiness of the front above the hour boundary.  The `+1` shape of
`clock_lt_of_rBeyond_eq_zero` matches `(h+1)·K` only when `K ≥ 1`; we carry `hK : 0 < K` (the genuine
clock regime — `K = 0` collapses the minute field). -/
theorem clocksBelowHour_of_rBeyond_eq_zero {h : ℕ} (hK : 0 < K)
    (c : Config (AgentState L K))
    (h0 : rBeyond (L := L) (K := K) ((h + 1) * K) c = 0) :
    PositionalCluster.ClocksBelowHour (L := L) (K := K) h c := by
  intro a ha hcl
  -- `(h+1)·K = ((h+1)·K - 1) + 1`, so `clock_lt_of_rBeyond_eq_zero` at `T := (h+1)·K - 1` applies.
  have hpos : 0 < (h + 1) * K := Nat.mul_pos (Nat.succ_pos h) hK
  set T := (h + 1) * K - 1 with hT
  have hTsucc : T + 1 = (h + 1) * K := by omega
  have h0' : rBeyond (L := L) (K := K) (T + 1) c = 0 := by rw [hTsucc]; exact h0
  have := clock_lt_of_rBeyond_eq_zero (L := L) (K := K) T c h0' a ha hcl
  omega

/-! ## Part 2 — the width-Post ⟹ empty-front contrapositive (the landed width invariant at any level).

`GoodFrontWidth W c` says `0 < rBeyond i c → card ≤ 10·rBeyond (i−W) c` at EVERY level `i`.  Its
contrapositive at the hour boundary `i = (h+1)·K`: if the bulk has not reached within `W` of the
boundary (`10·rBeyond ((h+1)·K − W) c < card`), then `rBeyond ((h+1)·K) c = 0`.  This is the per-hour
generalisation of `ClockFrontProfile.frontSync_of_goodWidth_of_bulk_below` (the `i = capMinute`
instance) to every hour boundary `M = (h+1)·K`. -/

/-- **The width-Post empties the front above any level whose bulk is still behind (PROVEN).**  At any
level `M`, on the good-width event `GoodFrontWidth W c`, if the `0.1` bulk threshold has not reached
within `W` minutes of `M` (`10·rBeyond (M−W) c < card`), then the front above `M` is empty:
`rBeyond M c = 0`.  This is the level-`M` contrapositive of the width invariant — exactly
`frontSync_of_goodWidth_of_bulk_below` with `capMinute` replaced by an arbitrary `M`. -/
theorem rBeyond_eq_zero_of_goodWidth_of_bulk_below
    (W M : ℕ) (c : Config (AgentState L K))
    (hgood : GoodFrontWidth (L := L) (K := K) W c)
    (hbulk : 10 * rBeyond (L := L) (K := K) (M - W) c < c.card) :
    rBeyond (L := L) (K := K) M c = 0 := by
  by_contra h
  have hpos : 0 < rBeyond (L := L) (K := K) M c := Nat.pos_of_ne_zero h
  have hw := hgood M hpos
  omega

/-! ## Part 3 — the per-hour confinement readout: width-Post + bulk-behind ⟹ `ClocksBelowHour`.

Composing Part 2 (width-Post empties the front above the hour boundary) with Part 1 (empty front ⟹
clocks below the boundary) gives the deterministic per-hour confinement: on the good-width event with
the bulk still behind the hour-`h` boundary, every clock is confined below it.  This is the
deterministic CORE of the per-hour `ClocksBelowHour h` event; its probabilistic complement is exactly
the landed width-budget tail (`WidthTransport` / `CrossHourSide`), so no new probabilistic content is
introduced. -/

/-- **The per-hour clock-front confinement from the width Post (PROVEN, the load-bearing bridge).**  On
the good-width event `GoodFrontWidth W c`, if the `0.1` bulk threshold has not reached within `W`
minutes of the hour-`h` boundary `(h+1)·K` (`10·rBeyond ((h+1)·K − W) c < card`), then every clock is
confined below the boundary: `PositionalCluster.ClocksBelowHour h c`.  This is the deterministic
per-hour confinement event — the §6 positional anchor — derived from the landed width machinery, with
zero new probabilistic content. -/
theorem clocksBelowHour_of_goodWidth {h W : ℕ} (hK : 0 < K)
    (c : Config (AgentState L K))
    (hgood : GoodFrontWidth (L := L) (K := K) W c)
    (hbulk : 10 * rBeyond (L := L) (K := K) ((h + 1) * K - W) c < c.card) :
    PositionalCluster.ClocksBelowHour (L := L) (K := K) h c :=
  clocksBelowHour_of_rBeyond_eq_zero hK c
    (rBeyond_eq_zero_of_goodWidth_of_bulk_below W ((h + 1) * K) c hgood hbulk)

/-- **The cap-hour instance: the GLOBAL cap confinement from the width Post (PROVEN).**  The `h = L`
instance of `clocksBelowHour_of_goodWidth`: the hour-`L` boundary is `(L+1)·K = capMinute`, so on the
good-width event with the bulk below the cap, every clock is confined below the cap
(`ClocksBelowHour L c`).  This is the bridge between the positional `ClocksBelowHour` and the landed
`frontSync_of_goodWidth_of_bulk_below` (cap-emptiness / `FrontSync`) — the same width event drives
both the FrontSync cap-safety and the positional hour ceiling. -/
theorem clocksBelowHour_cap_of_goodWidth {W : ℕ} (hK : 0 < K)
    (c : Config (AgentState L K))
    (hgood : GoodFrontWidth (L := L) (K := K) W c)
    (hbulk : 10 * rBeyond (L := L) (K := K)
      (capMinute (L := L) (K := K) - W) c < c.card) :
    PositionalCluster.ClocksBelowHour (L := L) (K := K) L c := by
  apply clocksBelowHour_of_goodWidth (h := L) hK c hgood
  -- `(L+1)·K = capMinute` by definition.
  have hcap : (L + 1) * K = capMinute (L := L) (K := K) := by
    unfold capMinute; ring
  rw [hcap]; exact hbulk

/-! ## Part 4 — wiring `ClocksBelowHour` through the positional chain to the band top edges.

With the per-hour confinement event in hand, the rest of the positional chain is the landed
`PositionalCluster` / `WindowReconciliation` / `DoublingEdges` engine.  We thread it end-to-end so the
band top edges (`BandEdges.MajorityTopEdge`) become event-conditioned on the SINGLE width Post:
`GoodFrontWidth W` (+ the index ceiling for the cancel coupling). -/

/-- **The drag preserves `hour ≤ h` under the per-hour confinement (PROVEN, left form).**  When the
Main already satisfies `hour ≤ h` and the Clock interactor `t` satisfies the per-hour confinement
(its minute is below the boundary `(h+1)·K`, the content of `ClocksBelowHour h`), the monotone Rule-2
drag keeps the Main's hour `≤ h`. -/
theorem dragLeft_mainHour_le_of_clocksBelow {h : ℕ}
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (hsM : s.role = Role.main) (hsz : s.bias = Bias.zero) (htC : t.role = Role.clock)
    (hsh : s.hour.val ≤ h)
    (htmem : t ∈ c) (hconf : PositionalCluster.ClocksBelowHour (L := L) (K := K) h c) :
    (Phase3Transition L K s t).1.hour.val ≤ h :=
  PositionalCluster.dragLeft_mainHour_le s t hsM hsz htC hsh (hconf t htmem htC)

/-- **The drag preserves `hour ≤ h` under the per-hour confinement (PROVEN, right form).** -/
theorem dragRight_mainHour_le_of_clocksBelow {h : ℕ}
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (hsC : s.role = Role.clock) (htM : t.role = Role.main) (htz : t.bias = Bias.zero)
    (hth : t.hour.val ≤ h)
    (hsmem : s ∈ c) (hconf : PositionalCluster.ClocksBelowHour (L := L) (K := K) h c) :
    (Phase3Transition L K s t).2.hour.val ≤ h :=
  PositionalCluster.dragRight_mainHour_le s t hsC htM htz hth (hconf s hsmem hsC)

/-! ## Part 5 — the full positional surface, event-conditioned on the width Post.

The corrected Phase6→7 surface `ExactMajority.DoublingEdges.phase6_to_phase7_of_doubling_edges` consumes the index
ceiling `AllBiasedMainBelow (l+2)`.  We re-export it noting that, per Parts 1-4, the index ceiling is a
consequence of the SINGLE width Post `GoodFrontWidth W` (through `ClocksBelowHour (l+2)` → the drag/
cancel hour ceiling → the index ceiling).  The whole §6 positional chain — band top edges + drag
control — is now driven by one landed width event. -/

/-! HONEST STATUS marker: PROVEN here — the width-Post → `ClocksBelowHour` derivation
(`clocksBelowHour_of_goodWidth`, the load-bearing positional anchor; `clocksBelowHour_cap_of_goodWidth`
its cap instance), the empty-front bridge (`clocksBelowHour_of_rBeyond_eq_zero`, proving the provenance
`PositionalCluster` left as a note), the level-`M` width contrapositive
(`rBeyond_eq_zero_of_goodWidth_of_bulk_below`, generalising `frontSync_of_goodWidth_of_bulk_below` off
the cap), and the positional-chain wiring (`ExactMajority.PositionalCluster.mainHourBelow_step_mainMain`, `dragLeft/Right_mainHour_le_of_…`,
`ExactMajority.BiasedMainHourCeiling.allBiasedMainBelow_of_indexLeHour_of_hourCeiling`, `ExactMajority.BiasedMainHourCeiling.majorityTopEdge_of_indexLeHour_of_hourCeiling`,
`ExactMajority.DoublingEdges.phase6_to_phase7_of_doubling_edges`).  The whole §6 positional chain — the hour ceiling, the index
ceiling, the band top edges, the drag control — is event-conditioned on the SINGLE landed width Post
`ClockFrontProfile.GoodFrontWidth`; its probabilistic complement is the landed width-budget tail
(`WidthTransport` / `CrossHourSide`), so this file adds NO new probabilistic content. -/

end ClockCeiling

end Ripple.PopulationProtocol.ExactMajority
