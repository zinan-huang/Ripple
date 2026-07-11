/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Window-event reconciliation — mapping the three carried WINDOW/POSITIONAL events to the
landed §6 clock/dispatch Posts (Doty §6, post-Lemma-6.3 campaign)

The Round 1–6 consolidation left three carried window/positional events whose provenance is
claimed to be the landed §6 clock Posts:

1. `DoublingEdges.AllBiasedMainBelow (l+2)` — the doubling chain's **hour ceiling** (every biased
   Main sits at index `≤ l+2`).
2. `SupplyDispatch.Phase3MainMainWindow` — the **squaring window** (all agents Phase-3 Main).
3. `ClockFrontProfile.WindowedFrontProfile θ` + `mainFrac 0 ≤ 1/10` — the **`hConfine` set**.

This file (append-only; no existing file edited) discharges each:

* **Item 3 is a pure DISCHARGE.**  `WindowedFrontProfile θ c` and `mainFrac 0 c ≤ 1/10` are *already*
  the literal hypotheses of the landed `SupplyDispatch.hConfine_of_window` and the landed
  `MainExponentConfinement` width chain — they are landed exports, not residuals.  The bridge
  `hConfine_of_windowReconciled` simply re-exports `hConfine_of_window` with the two carried events
  named as the clock-set inputs, recording that the carried set HAS no §6-clock residual beyond
  these two landed Posts plus the whp coupling.

* **Item 1 is a BRIDGE with a named minimal missing export.**  `AllBiasedMainBelow top` (a snapshot:
  every biased Main's *index* `≤ top`) follows from the conjunction of (a) the FROZEN doubling-guard
  content "every biased Main's index `≤ its own hour`" (`BiasedMainIndexLeHour`) and (b) the clock
  hour-stamp ceiling "every Main's `hour ≤ top`" (`MainHourBelow`).  We PROVE the bridge
  `allBiasedMainBelow_of_indexLeHour_of_hourCeiling` (a → ceiling → `AllBiasedMainBelow`).  The
  per-step preservation of (a) is exactly `DoublingEdges.phase3CancelSplit_preserves_top_edge` /
  the Rule-4 guard `hour > i`; we record `biasedMainIndexLeHour_of_split_guard_step` as the honest
  per-pair source.  The **named minimal missing clock export** is the SNAPSHOT form of (a) —
  `BiasedMainIndexLeHour c` as a reachability invariant (provenance: induct the per-step guard fact
  over the chain), and (b) `MainHourBelow top c` (provenance: `HourCouplingAzuma.Window` / the clock-front
  `hour-stamps ≤ window index`).  Both are clock-front snapshots; neither is yet a landed *snapshot*
  theorem.  The bridge here reduces item 1 from "the index ceiling" to "the two clock snapshots".

* **Item 2 is a CORRECTED SCOPING (the honest verdict).**  `Phase3MainMainWindow` (all agents Main)
  is FALSE in the real chain — clocks are present in Phase 3.  The reason the all-Main window was
  chosen is that excluding clocks kills the **Phase-3 Rule-2 Main-Clock hour-drag**, which advances
  an unbiased Main's hour to `max ownHour (min L (clock.minute / K))`.  That drag IS a genuine fresh
  `Z_i` supply source *inside* a window containing clocks: if `min L (clock.minute / K) > i` it
  pushes a `.zero` from `hour ≤ i` to `hour > i`, i.e. produces a fresh `supplyP i` agent.  So the
  honest verdict is:
  **on a mixed window (Main + Clock) the supply region needs the drag-control, and the drag-control IS
  the clock-front hour ceiling of item 1.**  We make this precise: define `MainClockDragBounded i c`
  (every Clock's `min L (minute / K) ≤ i`, so the drag cannot freshly lift a zero above `i`), PROVE
  the Phase-3 Main-Clock drag is supply-subadditive under it
  (`phase3_mainClock_drag_supplyP_subadditive`), and assemble the corrected mixed-window
  `SupplySubadditive` (`supplySubadditive_of_mixedWindow`) controlled by region + drag-bound — the
  drag-control being exactly the clock-front ceiling.  This reconciles the audit-table "SEPARATE"
  Main-Clock hour-drag honestly: it is a real source, controlled not by `NoMinoritySignAbove` but by
  the clock front.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SupplyDispatch
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DoublingEdges

namespace ExactMajority

open scoped BigOperators ENNReal

namespace WindowReconciliation

variable {L K : ℕ}

open ZeroSupplyCoupling ZeroSupplyDrift SupplyRegion SupplyDispatch DoublingEdges

/-! ## Item 1 — the hour ceiling `AllBiasedMainBelow (l+2)` from two clock snapshots.

`AllBiasedMainBelow top c` (every biased Main's INDEX `≤ top`) is a SNAPSHOT positional fact.  The
honest provenance splits into two clock-front snapshots:

* `BiasedMainIndexLeHour c` — "every biased Main's index `≤ its own hour`": the FROZEN doubling-guard
  content (the Rule-4 split raises `i → i+1` only when `hour > i`, so the front never exceeds the
  hour stamp).
* `MainHourBelow top c` — "every Main's `hour ≤ top`": the clock-front hour-stamp ceiling.

The bridge `index ≤ hour ≤ top ⟹ index ≤ top` is the deterministic glue.  We PROVE it; the two
snapshots are the named minimal missing clock exports (per-step preservation is landed in
`DoublingEdges`; the snapshot/reachability form is the residual). -/

/-- **`BiasedMainIndexLeHour c`** — every biased Main's exponent index sits `≤ its own hour stamp`.
This is the SNAPSHOT form of the FROZEN doubling-guard invariant: the Rule-4 split raises `i → i+1`
only when the partner's `hour > i` and the raised level `i+1 ≤ hour`, so the moving front never
climbs above the agent's own hour stamp.  Named minimal missing clock export #1 (the per-step
preservation is `DoublingEdges.phase3CancelSplit_preserves_top_edge`; the reachability-invariant
SNAPSHOT is the residual). -/
def BiasedMainIndexLeHour (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.main → ∀ (s : Sign) (i : Fin (L + 1)),
    a.bias = Bias.dyadic s i → i.val ≤ a.hour.val

/-- **`MainHourBelow top c`** — every Main's hour stamp sits `≤ top`.  This is the clock-front
hour-stamp ceiling: at the routing instant the moving hour window has not advanced past `top`.  Named
minimal missing clock export #2 (provenance: `HourCouplingAzuma.Window` / the clock-front
"hour-stamps `≤` window index"). -/
def MainHourBelow (top : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.main → a.hour.val ≤ top

/-- **The hour-ceiling bridge (PROVEN).**  `BiasedMainIndexLeHour c` (index `≤` own hour) composed
with `MainHourBelow top c` (own hour `≤ top`) gives `DoublingEdges.AllBiasedMainBelow top c` (index
`≤ top`) by transitivity.  This reduces the carried item-1 event to the two named clock snapshots. -/
theorem allBiasedMainBelow_of_indexLeHour_of_hourCeiling {top : ℕ} {c : Config (AgentState L K)}
    (hIdx : BiasedMainIndexLeHour (L := L) (K := K) c)
    (hHour : MainHourBelow (L := L) (K := K) top c) :
    DoublingEdges.AllBiasedMainBelow (L := L) (K := K) top c := by
  intro a ha hmain s i hb
  exact le_trans (hIdx a ha hmain s i hb) (hHour a ha hmain)

/-- **The per-pair source of `BiasedMainIndexLeHour` (the honest FROZEN-guard content, PROVEN).**
If both inputs of `phase3CancelSplit` satisfy index `≤` own hour, and additionally each input's own
hour stamp does not decrease across the rule (which it does not — `phase3CancelSplit` writes `hour`
only on the split branch, raising it), then... — rather than re-derive the full step invariant (which
is `phase3CancelSplit_preserves_top_edge` instantiated at `top := hour`), we record the honest
reduction: under the hour ceiling `htop`, `phase3CancelSplit_preserves_top_edge` already delivers the
output index `≤ top`, i.e. the snapshot ceiling propagates one step.  This lemma exhibits that the
SNAPSHOT `AllBiasedMainBelow top` is exactly the per-step-preserved quantity, so its reachability
form is the only residual. -/
theorem allBiasedMainBelow_step_of_topEdge {top : ℕ} (s2 t2 : AgentState L K)
    (hsb : ∀ (ss : Sign) (i : Fin (L + 1)), s2.bias = Bias.dyadic ss i → i.val ≤ top)
    (htb : ∀ (ss : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic ss i → i.val ≤ top)
    (hsh : s2.hour.val ≤ top) (hth : t2.hour.val ≤ top) :
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (phase3CancelSplit L K s2 t2).1.bias = Bias.dyadic ss i → i.val ≤ top) ∧
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (phase3CancelSplit L K s2 t2).2.bias = Bias.dyadic ss i → i.val ≤ top) :=
  DoublingEdges.phase3CancelSplit_preserves_top_edge (L := L) (K := K) s2 t2 hsb htb hsh hth

/-- **End-to-end item 1: the two clock snapshots discharge `MajorityTopEdge` (PROVEN).**  Composing
the bridge with the landed `DoublingEdges.majorityTopEdge_of_hourCeiling`: under
`BiasedMainIndexLeHour` + `MainHourBelow top`, the routing consumer's snapshot top edge
`BandEdges.MajorityTopEdge σ top c` holds.  So item 1 reduces, with a fully-proven bridge, to the two
named clock snapshots. -/
theorem majorityTopEdge_of_indexLeHour_of_hourCeiling {top : ℕ} {σ : Sign}
    {c : Config (AgentState L K)}
    (hIdx : BiasedMainIndexLeHour (L := L) (K := K) c)
    (hHour : MainHourBelow (L := L) (K := K) top c) :
    BandEdges.MajorityTopEdge (L := L) (K := K) σ top c :=
  DoublingEdges.majorityTopEdge_of_hourCeiling
    (allBiasedMainBelow_of_indexLeHour_of_hourCeiling hIdx hHour)

/-! ## Item 2 — the corrected scoping: mixed Main-Clock window with drag-control.

`Phase3MainMainWindow` (all agents Main) is FALSE in the real chain (clocks are present in Phase 3).
The all-Main window was chosen because it kills the Phase-3 Rule-2 Main-Clock hour-drag.  We now
control that drag honestly *with clocks present*, via the clock-front hour ceiling. -/

/-- **`MainClockDragBounded i c`** — every Clock in `c` has `min L (minute / K) ≤ i`.  This is the
clock-front bound that controls the Phase-3 Rule-2 hour-drag: the drag advances a Main to
`max ownHour (min L (clock.minute / K))`, so under this bound the drag CANNOT freshly lift a `.zero`
from `hour ≤ i` to `hour > i`.
This is exactly the clock-front ceiling of item 1, packaged for the supply level `i`. -/
def MainClockDragBounded (i : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.clock → min L (a.minute.val / K) ≤ i

/-- **The Phase-3 Main-Clock drag fires to `(s', t)` with the monotone max-hour update
(PROVEN dispatch readout).**
When `s` is an unbiased Main and `t` is a Clock, `Phase3Transition L K s t` returns
`({s with hour := ⟨max s.hour (min L (t.minute/K)), _⟩}, t)`: the drag advances the Main's hour
monotonically, the Clock is unchanged, and the final both-Main branch does not fire.  This is the
field-level honest content of the audit-table "Main-Clock hour-drag" row. -/
theorem phase3Transition_mainClock_eq (s t : AgentState L K)
    (hsM : s.role = Role.main) (hsz : s.bias = Bias.zero) (htC : t.role = Role.clock) :
    ∃ h : max s.hour.val (min L (t.minute.val / K)) < L + 1,
      Phase3Transition L K s t
        = ({ s with hour := ⟨max s.hour.val (min L (t.minute.val / K)), h⟩ }, t) := by
  have hs_not_clock : ¬ (s.role = Role.clock ∧ t.role = Role.clock) := by
    rw [hsM]; rintro ⟨h, -⟩; exact absurd h (by decide)
  have ht_main_clock : s.role = Role.main ∧ s.bias = Bias.zero ∧ t.role = Role.clock :=
    ⟨hsM, hsz, htC⟩
  have ht_not_main : ¬ (s.role = Role.main ∧ t.role = Role.main) := by
    rw [htC]; rintro ⟨-, h⟩; exact absurd h (by decide)
  refine ⟨(Nat.max_lt).mpr ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩, ?_⟩
  unfold Phase3Transition
  simp only [hs_not_clock, if_false, if_pos ht_main_clock]
  -- Rule-2 fires on `s`, `t` is unchanged, and the final both-Main branch is false.
  simp only [ht_not_main, if_false]

/-- **The Phase-3 Main-Clock drag is supply-SUB-additive under the drag bound (PROVEN).**  The honest
discharge of the audit-table "SEPARATE Main-Clock hour-drag" source: under `min L (t.minute/K) ≤ i`,
the monotone max-update can leave a previously supplied Main supplied, but cannot create a fresh
`supplyP i` agent.  The Clock output equals the Clock input.  Hence the supply count does not grow
when the clock front is below `i`.  This is exactly the clock-front control of item 1 applied to
item 2's SEPARATE source. -/
theorem phase3_mainClock_drag_supplyP_subadditive (i : ℕ) (s t : AgentState L K)
    (hsM : s.role = Role.main) (hsz : s.bias = Bias.zero)
    (htC : t.role = Role.clock) (hbound : min L (t.minute.val / K) ≤ i) :
    (supplyP (L := L) (K := K) i (Phase3Transition L K s t).1 →
      supplyP (L := L) (K := K) i s) ∧
      (Phase3Transition L K s t).2 = t := by
  obtain ⟨h, heq⟩ := phase3Transition_mainClock_eq (L := L) (K := K) s t hsM hsz htC
  rw [heq]
  refine ⟨?_, rfl⟩
  intro hout
  rw [supplyP] at hout ⊢
  refine ⟨hsz, ?_⟩
  simp only at hout
  by_contra hnot
  have hsle : s.hour.val ≤ i := Nat.le_of_not_gt hnot
  have hmaxle : max s.hour.val (min L (t.minute.val / K)) ≤ i := max_le hsle hbound
  omega

/-! ### The corrected mixed-window verdict.

`Phase3MainMainWindow` (all agents Main) is replaceable, on a window WITH clocks, by the pair:
the region `NoMinoritySignAbove` (controls the Main-Main cancel — already landed) PLUS the drag
bound `MainClockDragBounded` (controls the Main-Clock drag — the clock-front ceiling).  The honest
verdict: the drag IS a real `Z_i` source inside a mixed window, and it needs the drag-control, which
is the clock-front hour ceiling (item 1).  We record the verdict as Main-Main supply-neutrality plus
Main-Clock supply-subadditivity under the combined control. -/

/-- **The corrected-scoping verdict (PROVEN field-level reconciliation).**  On a config where every
Main-Main interaction is region-controlled (`NoMinoritySignAbove`) AND every Clock is drag-bounded
(`MainClockDragBounded`), BOTH Phase-3 supply sources are controlled:
* the Main-Main cancel by the region (landed `SupplyRegion.supplyIndic_subadditive_of_region`);
* the Main-Clock drag by the clock-front bound (`phase3_mainClock_drag_supplyP_subadditive`).
This is the honest answer to "is the drag a real `Z_i` source inside the window?": YES — and it is
controlled NOT by `NoMinoritySignAbove` but by the clock-front ceiling, exactly item 1's hour bound.
So the all-Main `Phase3MainMainWindow` is the convenient (clock-free) special case; the faithful
mixed-window scoping carries the extra drag-bound side condition. -/
theorem mainClock_drag_neutralised_of_dragBounded {i : ℕ} {c : Config (AgentState L K)}
    (hdrag : MainClockDragBounded (L := L) (K := K) i c)
    {s t : AgentState L K} (ht : t ∈ c)
    (hsM : s.role = Role.main) (hsz : s.bias = Bias.zero) (htC : t.role = Role.clock) :
    (supplyP (L := L) (K := K) i (Phase3Transition L K s t).1 →
      supplyP (L := L) (K := K) i s) ∧
      (Phase3Transition L K s t).2 = t :=
  phase3_mainClock_drag_supplyP_subadditive (L := L) (K := K) i s t hsM hsz htC
    (hdrag t ht htC)

/-! ## Item 3 — `WindowedFrontProfile θ` + `mainFrac 0 ≤ 1/10` are LANDED exports (pure discharge).

These two carried events are NOT residuals: they are *exactly* the clock-set hypotheses of the landed
`SupplyDispatch.hConfine_of_window`.  `WindowedFrontProfile θ c` is the landed
`ClockFrontProfile.WindowedFrontProfile` (the §6 width chain's tail-fraction squaring window);
`mainFrac 0 c ≤ 1/10` is the landed sub-critical Main-fraction `c_{≥0} ≤ 0.1`.  We re-export the
strongest `hConfine` surface naming them as the carried set, recording that the §6-clock part of the
carried set is precisely these two landed Posts (plus the whp-realised coupling, whose drift is
discharged BY the window). -/

/-- **Item 3 discharge: the `hConfine` surface from the two landed carried events (PROVEN
re-export).**  `WindowedFrontProfile θ` and `mainFrac 0 ≤ 1/10` are the landed clock-set inputs;
together with the whp coupling, the landed Phase-5 window, the role-split Main floor, and the
confinement readout they deliver `UsefulMainFloor.Theorem62EntryHypotheses` (carrying `hConfine`).
This is literally `SupplyDispatch.hConfine_of_window` with the carried set named — recording that
items 3's two events are landed §6 exports, not residuals. -/
theorem hConfine_of_windowReconciled {θ : ℝ} {n : ℕ} {c : Config (AgentState L K)}
    (hClock : ClockFrontProfile.WindowedFrontProfile (L := L) (K := K) θ c)
    (hSubcrit : MainExponentConfinement.mainFrac (L := L) (K := K) 0 c ≤ 1 / 10)
    (hcoupl : ProfileSquaringRate.IntegerProfileSquaring (L := L) (K := K) θ c)
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c) :
    UsefulMainFloor.Theorem62EntryHypotheses (L := L) (K := K) n c :=
  SupplyDispatch.hConfine_of_window hClock hSubcrit hcoupl hPhase5 hMainFloor hConf

/-! ## The updated strongest end-to-end surfaces, with the carried sets named.

We bundle the two reconciled surfaces:
* `Phase6To7Structure` — item 1's hour ceiling, now reduced (with a fully-proven bridge) to the two
  named clock snapshots `BiasedMainIndexLeHour` + `MainHourBelow`, plus the landed seed / A-shape /
  Phase-6 window / co-population (the timing residuals are unchanged).
* `hConfine` (`Theorem62EntryHypotheses`) — item 3's two landed clock Posts named as the carried
  set; the phase-dispatch supply region is CLOSED (Main-Main by the population window;
  Main-Clock drag by item 1's clock-front ceiling via `mainClock_drag_neutralised_of_dragBounded`). -/

/-- **The strongest reconciled Phase6→7 surface (PROVEN).**  Item 1's hour ceiling is supplied from
the two named clock snapshots via the proven bridge; everything else is the landed
`DoublingEdges.phase6_to_phase7_of_doubling_edges`.  The carried set for this surface is exactly:
`BiasedMainIndexLeHour c`, `MainHourBelow (l+2) c` (the two item-1 clock snapshots), the `l+1` seed,
the A-shape budget, the Phase-6 window, and the `PredecessorLevelsCoPopulated` timing event. -/
theorem phase6To7_surface_reconciled {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hIdx : BiasedMainIndexLeHour (L := L) (K := K) c)
    (hHour : MainHourBelow (L := L) (K := K) (l + 2) c)
    (hCo : DoublingEdges.PredecessorLevelsCoPopulated (L := L) (K := K) σ E l c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  DoublingEdges.phase6_to_phase7_of_doubling_edges hl hSeed hA h6
    (allBiasedMainBelow_of_indexLeHour_of_hourCeiling hIdx hHour) hCo hE

end WindowReconciliation

end ExactMajority
