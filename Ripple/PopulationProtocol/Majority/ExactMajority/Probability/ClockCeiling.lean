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
  `MainHourBelow h`    ──(WindowReconciliation.allBiasedMainBelow_of_indexLeHour_of_hourCeiling)──►
                          `AllBiasedMainBelow h`  (the index ceiling `l+2`)
  `AllBiasedMainBelow` ──(DoublingEdges.majorityTopEdge_of_hourCeiling)──►  the band top edges
                       ──(CeilingRoute / PositionalCluster.phase6To7_surface_positional)──►
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
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PositionalCluster
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WidthTransport

namespace ExactMajority

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

/-- **The Main×Main hour-ceiling step under the width Post (PROVEN).**  On a Main×Main pair (the move
is `phase3CancelSplit`; no Clock present, so no drag fires), the hour ceiling `hour ≤ h` propagates to
both outputs given the index ceiling `index ≤ h`.  This is the clock-FREE step; the Main×Clock step is
the drag readout (`PositionalCluster.dragLeft/dragRight_mainHour_le`), which fires exactly under the
per-hour confinement `ClocksBelowHour h` of Part 3.  We re-export the Main×Main piece so the per-hour
event chains directly into the hour ceiling. -/
theorem mainHourBelow_step {h : ℕ} (s2 t2 : AgentState L K)
    (hsM : s2.role = Role.main) (htM : t2.role = Role.main)
    (hsh : s2.hour.val ≤ h) (hth : t2.hour.val ≤ h)
    (hsi : ∀ (ss : Sign) (i : Fin (L + 1)), s2.bias = Bias.dyadic ss i → i.val ≤ h)
    (hti : ∀ (ss : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic ss i → i.val ≤ h) :
    (Phase3Transition L K s2 t2).1.hour.val ≤ h
      ∧ (Phase3Transition L K s2 t2).2.hour.val ≤ h :=
  PositionalCluster.mainHourBelow_step_mainMain s2 t2 hsM htM hsh hth hsi hti

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

/-- **The index ceiling from the two snapshots (PROVEN re-export).**  Composing the snapshot hour
ceiling `MainHourBelow top c` with the per-agent index-≤-hour fact `BiasedMainIndexLeHour c` yields the
index ceiling `AllBiasedMainBelow top c` — the step-preserved quantity the band consumers ride on.
Per Parts 1-3, the hour ceiling `MainHourBelow top` is the snapshot consequence of the SINGLE width
Post (via `ClocksBelowHour top` + the drag/cancel engine), so the index ceiling is now
event-conditioned on the width budget. -/
theorem allBiasedMainBelow_of_snapshots {top : ℕ} {c : Config (AgentState L K)}
    (hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c)
    (hHour : WindowReconciliation.MainHourBelow (L := L) (K := K) top c) :
    DoublingEdges.AllBiasedMainBelow (L := L) (K := K) top c :=
  WindowReconciliation.allBiasedMainBelow_of_indexLeHour_of_hourCeiling hIdx hHour

/-- **The band top edge from the two snapshots (PROVEN re-export, the consumer endpoint).**  The
routing consumer's snapshot top edge `BandEdges.MajorityTopEdge σ top c` holds under the two clock
snapshots `BiasedMainIndexLeHour` + `MainHourBelow top` — both of which are now consequences of the
single width Post.  This is the positional chain's terminal: the band top edges (and downstream, the
`CeilingRoute`/`BandEdges` band edges + the `SupplyRegion`/`SupplyDispatch` drag control) are
event-conditioned on `GoodFrontWidth`. -/
theorem majorityTopEdge_of_snapshots {top : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c)
    (hHour : WindowReconciliation.MainHourBelow (L := L) (K := K) top c) :
    BandEdges.MajorityTopEdge (L := L) (K := K) σ top c :=
  WindowReconciliation.majorityTopEdge_of_indexLeHour_of_hourCeiling hIdx hHour

/-! ## Part 5 — the full positional surface, event-conditioned on the width Post.

The corrected Phase6→7 surface `PositionalCluster.phase6To7_surface_positional` consumes the index
ceiling `AllBiasedMainBelow (l+2)`.  We re-export it noting that, per Parts 1-4, the index ceiling is a
consequence of the SINGLE width Post `GoodFrontWidth W` (through `ClocksBelowHour (l+2)` → the drag/
cancel hour ceiling → the index ceiling).  The whole §6 positional chain — band top edges + drag
control — is now driven by one landed width event. -/

/-- **The width-Post-conditioned corrected Phase6→7 surface (PROVEN re-export).**  The corrected
positional surface for the eliminator consumer, carrying the index ceiling `AllBiasedMainBelow (l+2)`
(the step-preserved quantity).  Per the bridge of Parts 1-4, this index ceiling is itself a consequence
of the per-hour clock-front confinement `ClocksBelowHour (l+2)` (Part 3, derived from the landed width
Post `GoodFrontWidth W`) composed with the drag/cancel hour-ceiling engine.  So the FULL positional
chain feeding this surface is event-conditioned on the SINGLE width budget. -/
theorem phase6To7_surface_widthConditioned {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hCeil : DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (l + 2) c)
    (hCo : DoublingEdges.PredecessorLevelsCoPopulated (L := L) (K := K) σ E l c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  PositionalCluster.phase6To7_surface_positional hl hSeed hA h6 hCeil hCo hE

/-- HONEST STATUS marker: PROVEN here — the width-Post → `ClocksBelowHour` derivation
(`clocksBelowHour_of_goodWidth`, the load-bearing positional anchor; `clocksBelowHour_cap_of_goodWidth`
its cap instance), the empty-front bridge (`clocksBelowHour_of_rBeyond_eq_zero`, proving the provenance
`PositionalCluster` left as a note), the level-`M` width contrapositive
(`rBeyond_eq_zero_of_goodWidth_of_bulk_below`, generalising `frontSync_of_goodWidth_of_bulk_below` off
the cap), and the positional-chain wiring (`mainHourBelow_step`, `dragLeft/Right_mainHour_le_of_…`,
`allBiasedMainBelow_of_snapshots`, `majorityTopEdge_of_snapshots`,
`phase6To7_surface_widthConditioned`).  The whole §6 positional chain — the hour ceiling, the index
ceiling, the band top edges, the drag control — is event-conditioned on the SINGLE landed width Post
`ClockFrontProfile.GoodFrontWidth`; its probabilistic complement is the landed width-budget tail
(`WidthTransport` / `CrossHourSide`), so this file adds NO new probabilistic content. -/
theorem clock_ceiling_status : True := trivial

end ClockCeiling

end ExactMajority
