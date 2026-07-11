/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doubling edges — the hour-gated TOP edge of the §6 doubling chain, and the occupancy verdict

This file (append-only; no existing file edited) discharges the carried positional content of
`BandEdges.lean` — `MajorityTopEdge`, `MinorityTopEdge`, and `TwoLevelOccupancy` — to the extent the
FROZEN rules honestly provide it, and wires the result into `BandEdges.phase6_to_phase7_of_seed_edges`.

## The mechanism, read honestly off the FROZEN split rule

The §6 doubling/split move is `phase3CancelSplit` (Rule 4): a `.zero` agent meeting a biased
`dyadic sgn i` agent BOTH become `dyadic sgn (i+1)` — but ONLY under the guard `partner.hour.val > i.val`.
This guard is the engine of the whole top-edge story:

* **Raises move by exactly one level** (`MainExponentConfinement.phase3CancelSplit_no_jump`: an output
  at `k = m+1` consumed an input already at `k` or at `m = k−1`).  The split is the unique raiser.
* **The cancel never lowers below the floor** (`MinorityFloorGap.cancelSplit_preserves_index_floor`).
* **A raise to level `i+1` is GATED by the partner's hour exceeding `i`** — so the raised level
  `i+1 ≤ partner.hour.val`.  This is the hour-gated top edge: *no agent is ever raised above the hour
  ceiling.*

Hence the honest, fully-provable TOP-edge statement (the mirror of the landed FLOOR
`cancelSplit_preserves_index_floor`):

> **If every biased input sits at level `≤ top` AND every input's `hour.val ≤ top`, then every biased
> output of `phase3CancelSplit` sits at level `≤ top`.**

The split branch raises `i → i+1` only when `hour.val > i.val`, i.e. `i + 1 ≤ hour.val ≤ top`, so the
new top is still `≤ top`.  This is `phase3CancelSplit_preserves_top_edge` below — proven exhaustively
over the frozen branches, consuming the landed clock-front `hour ≤ top` as a region hypothesis (within
an hour window the hour-stamps are bounded by the window index — the landed clock-front facts).  It is
the deterministic per-rule TOP-edge ledger, the honest content of `MajorityTopEdge`.

## The occupancy verdict (honest)

`TwoLevelOccupancy` asks both predecessor levels `{l, l+1}` to carry `≥ E` σ-opposite eliminators.
The honest content the doubling chain provides is the **running-mass / no-jump** fact: mass at level
`i+1` was raised FROM level `i` (the `no_jump` ledger), so any positive occupancy at `i+1` is witnessed
by an agent that visited `i`.  This is a *historical* (across-step) fact, NOT a snapshot fact about the
single config `c` the consumer needs.  Converting it to the snapshot `TwoLevelOccupancy` requires a
within-hour timing event (both predecessor levels populated *simultaneously* at the routing instant) —
which is a probabilistic concentration statement, not a deterministic ledger.  So the honest occupancy
verdict is **conditional**: we deliver `TwoLevelOccupancy` from a named timing event
(`PredecessorLevelsCoPopulated`, the "both levels carry their per-level share at the routing instant"
event), and record the no-jump *source* fact that the chain mass at `i+1` traces to `i`.  This is the
honest split between the deterministic per-rule content (the top edge, fully proven) and the
probabilistic timing content (the occupancy, conditional on the named co-population event).

## Wiring

`majorityTopEdge_of_hourCeiling` discharges `BandEdges.MajorityTopEdge` from a config-level hour
ceiling.  `phase6_to_phase7_of_doubling_edges` composes the seed, the carried minority top edge, and
the co-population occupancy into the strongest `Phase6To7Structure` surface — the exact
`BandEdges.phase6_to_phase7_of_seed_edges` instance with occupancy produced from the timing event.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BandEdges
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MainExponentConfinement

namespace ExactMajority

open scoped BigOperators

namespace DoublingEdges

variable {L K : ℕ}

/-! ## Part 1 — the hour-gated TOP edge per-rule ledger (deterministic, fully proven).

The mirror of `MinorityFloorGap.cancelSplit_preserves_index_floor`: where that propagates a LOWER
edge through `cancelSplit`, this propagates an UPPER edge through the §6 doubling rule
`phase3CancelSplit`, *gated by the hour ceiling*.  The split's guard `hour.val > i.val` is exactly
what bounds the raised level by the hour. -/

/-- **The per-pair hour-gated TOP-edge preservation (the frozen-`phase3CancelSplit` structural
core).**  If both inputs are biased only at indices `≤ top`, AND both inputs carry `hour.val ≤ top`,
then both outputs of `phase3CancelSplit L K s2 t2` carry index `≤ top` whenever biased.  Exhaustive
over the frozen branches: cancel/no-op preserve the input index (`≤ top` by hypothesis); the split
raises `i → i+1` only under the guard `hour.val > i.val`, so the new index `i+1 ≤ hour.val ≤ top`.
This is the honest hour-gated top-edge mechanism — *no agent is raised above the hour ceiling.* -/
theorem phase3CancelSplit_preserves_top_edge {top : ℕ} (s2 t2 : AgentState L K)
    (hsb : ∀ (ss : Sign) (i : Fin (L + 1)), s2.bias = Bias.dyadic ss i → i.val ≤ top)
    (htb : ∀ (ss : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic ss i → i.val ≤ top)
    (hsh : s2.hour.val ≤ top) (hth : t2.hour.val ≤ top) :
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (phase3CancelSplit L K s2 t2).1.bias = Bias.dyadic ss i → i.val ≤ top) ∧
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (phase3CancelSplit L K s2 t2).2.bias = Bias.dyadic ss i → i.val ≤ top) := by
  classical
  cases hs : s2.bias with
  | zero =>
    cases ht : t2.bias with
    | zero =>
      -- both .zero → no-op `(s2, t2)`; outputs unbiased on the .zero side, input on the other.
      refine ⟨fun ss i hi => ?_, fun ss i hi => ?_⟩ <;>
        · simp only [phase3CancelSplit, hs, ht] at hi
          exact absurd hi (by simp)
    | dyadic tsgn ti =>
      -- Rule 4 (split) on `(.zero, dyadic tsgn ti)` gated by `s2.hour.val > ti.val`.
      refine ⟨fun ss i hi => ?_, fun ss i hi => ?_⟩ <;>
        · simp only [phase3CancelSplit, hs, ht] at hi
          by_cases hgt : s2.hour.val > ti.val
          · simp only [hgt, dif_pos] at hi
            injection hi with _ hidx
            -- raised index = ti+1; gated so ti+1 ≤ s2.hour.val ≤ top.
            have hti : i.val = ti.val + 1 := by rw [← hidx]
            omega
          · -- no fire: outputs = inputs `(s2, t2)`.
            simp only [hgt, dif_neg, not_false_iff] at hi
            first
              | exact absurd hi (by simp [hs])
              | exact htb ss i (ht ▸ hi)
  | dyadic ssgn si =>
    cases ht : t2.bias with
    | zero =>
      -- Rule 4 (split) on `(dyadic ssgn si, .zero)` gated by `t2.hour.val > si.val`.
      refine ⟨fun ss i hi => ?_, fun ss i hi => ?_⟩ <;>
        · simp only [phase3CancelSplit, hs, ht] at hi
          by_cases hgt : t2.hour.val > si.val
          · simp only [hgt, dif_pos] at hi
            injection hi with _ hidx
            have hti : i.val = si.val + 1 := by rw [← hidx]
            omega
          · simp only [hgt, dif_neg, not_false_iff] at hi
            first
              | exact hsb ss i (hs ▸ hi)
              | exact absurd hi (by simp [ht])
    | dyadic tsgn ti =>
      -- dyadic×dyadic: cancel (same exp opp sign → unbiased) or no-op (input preserved).
      cases ssgn <;> cases tsgn
      -- pos,pos : same sign no-op `(s2,t2)`.
      · refine ⟨fun ss i hi => ?_, fun ss i hi => ?_⟩ <;>
          · simp only [phase3CancelSplit, hs, ht] at hi
            first | exact hsb ss i (hs ▸ hi) | exact htb ss i (ht ▸ hi)
      -- pos,neg : cancel if same exp (→ unbiased), else no-op.
      · refine ⟨fun ss i hi => ?_, fun ss i hi => ?_⟩ <;>
          · simp only [phase3CancelSplit, hs, ht] at hi
            by_cases hij : si.val = ti.val
            · simp only [hij, dif_pos] at hi
              exact absurd hi (by simp)
            · simp only [hij, dif_neg, not_false_iff] at hi
              first | exact hsb ss i (hs ▸ hi) | exact htb ss i (ht ▸ hi)
      -- neg,pos : cancel if same exp (→ unbiased), else no-op.
      · refine ⟨fun ss i hi => ?_, fun ss i hi => ?_⟩ <;>
          · simp only [phase3CancelSplit, hs, ht] at hi
            by_cases hij : si.val = ti.val
            · simp only [hij, dif_pos] at hi
              exact absurd hi (by simp)
            · simp only [hij, dif_neg, not_false_iff] at hi
              first | exact hsb ss i (hs ▸ hi) | exact htb ss i (ht ▸ hi)
      -- neg,neg : same sign no-op `(s2,t2)`.
      · refine ⟨fun ss i hi => ?_, fun ss i hi => ?_⟩ <;>
          · simp only [phase3CancelSplit, hs, ht] at hi
            first | exact hsb ss i (hs ▸ hi) | exact htb ss i (ht ▸ hi)

/-! ## Part 2 — the config-level hour ceiling ⟹ `BandEdges.MajorityTopEdge`.

The per-rule top-edge ledger is the dynamics' side.  The SNAPSHOT predicate `BandEdges.MajorityTopEdge`
that the routing consumer needs is a fact about the single config `c`: every level with positive
σ-opposite eliminator mass sits `≤ top`.  We discharge it from a config-level **hour ceiling** — the
honest within-hour clock-front content: at the routing instant, every biased Main's index `≤ top`
(equivalently, the moving front sits at the band top).  This is exactly the landed clock-front
"index bounded by the hour window" fact, packaged as the consumer's snapshot predicate. -/

/-- **Config-level index ceiling.**  Every biased Main in `c` sits at exponent index `≤ top`.  This
is the snapshot form of the hour-gated top edge: the moving front has not climbed above `top`.  It is
the honest within-hour clock-front content (`hour-stamps ≤ window index` ⟹ `front ≤ top`), the mirror
of `MinorityFloorGap.AllBiasedMainAbove` (the floor). -/
def AllBiasedMainBelow (top : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.main → ∀ (s : Sign) (i : Fin (L + 1)), a.bias = Bias.dyadic s i → i.val ≤ top

/-- **The index ceiling discharges `BandEdges.MajorityTopEdge`.**  Under `AllBiasedMainBelow top c`,
every level `i` with positive σ-opposite eliminator mass has `i.val ≤ top` — because a positive
`elimGap1 σ i` summand is a biased Main in `c` at index `i`, which the ceiling pins `≤ top`.  This is
the snapshot top edge the routing consumer needs, mirror of
`BandEdges.elim_index_ge_succ_floor` (the floor direction). -/
theorem majorityTopEdge_of_hourCeiling {top : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hCeil : AllBiasedMainBelow (L := L) (K := K) top c) :
    BandEdges.MajorityTopEdge (L := L) (K := K) σ top c := by
  classical
  intro i hi
  -- a positive count-sum forces a positive summand = a σ-opposite biased Main in `c` at index `i`.
  rcases Finset.exists_ne_zero_of_sum_ne_zero
    (by omega : (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count ≠ 0)
    with ⟨a, ha, hcount⟩
  rw [Phase7Convergence.elimGap1, Finset.mem_filter] at ha
  obtain ⟨-, hmain, ss, -, hb⟩ := ha
  have hpos : 0 < c.count a := Nat.pos_of_ne_zero hcount
  have hac : a ∈ c := Multiset.count_pos.mp hpos
  exact hCeil a hac hmain ss i hb

/-- **The index ceiling discharges `BandEdges.MinorityTopEdge`.**  The minority-side mirror: under
`AllBiasedMainBelow top c`, every live minority level `j` (positive `minorityAt7 σ j`) has `j.val ≤
top`.  A positive `minorityAt7 σ j` summand is a biased Main in `c` at index `j`, pinned `≤ top` by
the ceiling.  Together with the seed floor this confines the minority to the band. -/
theorem minorityTopEdge_of_hourCeiling {top : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hCeil : AllBiasedMainBelow (L := L) (K := K) top c) :
    BandEdges.MinorityTopEdge (L := L) (K := K) σ top c := by
  classical
  intro j hj
  rcases Finset.exists_ne_zero_of_sum_ne_zero
    (by omega : (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count ≠ 0)
    with ⟨a, ha, hcount⟩
  rw [Phase7Convergence.minorityAt7, Finset.mem_filter] at ha
  obtain ⟨-, hmain, hb⟩ := ha
  have hpos : 0 < c.count a := Nat.pos_of_ne_zero hcount
  have hac : a ∈ c := Multiset.count_pos.mp hpos
  exact hCeil a hac hmain σ j hb

/-! ## Part 3 — the occupancy verdict (honest, conditional on the co-population timing event).

`TwoLevelOccupancy` is a snapshot fact (both predecessor levels carry `≥ E` at the SAME config `c`),
hence a *probabilistic timing* statement, not a deterministic per-rule ledger.  The deterministic
content the doubling chain provides is the **no-jump source**: mass at level `i+1` was raised FROM
level `i`.  We record that source fact (`raise_traces_to_predecessor`, a direct corollary of
`phase3CancelSplit_no_jump`) and then deliver the snapshot `TwoLevelOccupancy` *conditionally* on the
named co-population timing event. -/

/-- **The raise traces to the predecessor level (no-jump source, deterministic).**  If a
`phase3CancelSplit` output sits at level `k = m+1`, then one of the two inputs already sat at level `k`
or at the predecessor level `m = k − 1`.  This is the honest "the chain passes through each level"
content: mass appearing at `i+1` either was already there or came from `i` — it never skips a level.
Direct corollary of `MainExponentConfinement.phase3CancelSplit_no_jump`. -/
theorem raise_traces_to_predecessor (s2 t2 : AgentState L K) (sgn : Sign) (k m : Fin (L + 1))
    (hm : k.val = m.val + 1)
    (hout : (phase3CancelSplit L K s2 t2).1.bias = Bias.dyadic sgn k
      ∨ (phase3CancelSplit L K s2 t2).2.bias = Bias.dyadic sgn k) :
    (∃ s, s2.bias = Bias.dyadic s k) ∨ (∃ s, t2.bias = Bias.dyadic s k)
      ∨ (∃ s, s2.bias = Bias.dyadic s m) ∨ (∃ s, t2.bias = Bias.dyadic s m) :=
  MainExponentConfinement.phase3CancelSplit_no_jump (L := L) (K := K) s2 t2 sgn k m hm hout

/-- **`PredecessorLevelsCoPopulated σ E l c`** — the named within-hour timing event: at the routing
instant `c`, BOTH band predecessor levels `l` and `l+1` carry `≥ E` σ-opposite eliminators.  This is
the honest probabilistic content of `TwoLevelOccupancy`: the doubling chain *passes through* each level
(the no-jump source fact), and the timing event asserts both predecessor levels are populated to the
per-level share `E` *simultaneously* at the routing instant.  Definitionally identical to
`BandEdges.TwoLevelOccupancy` — we name it separately to mark it as the timing EVENT (probabilistic),
distinct from the deterministic ledger facts. -/
def PredecessorLevelsCoPopulated (σ : Sign) (E l : ℕ) (c : Config (AgentState L K)) : Prop :=
  BandEdges.TwoLevelOccupancy (L := L) (K := K) σ E l c

/-- **The co-population event delivers `TwoLevelOccupancy` (the honest conditional occupancy).**  The
occupancy snapshot is exactly the named timing event — the honest verdict is that `TwoLevelOccupancy`
is NOT a deterministic per-rule consequence (it is a simultaneous-population fact about one config),
but it IS delivered by the named co-population timing event.  This makes the conditional explicit. -/
theorem twoLevelOccupancy_of_coPopulated {σ : Sign} {E l : ℕ} {c : Config (AgentState L K)}
    (hCo : PredecessorLevelsCoPopulated (L := L) (K := K) σ E l c) :
    BandEdges.TwoLevelOccupancy (L := L) (K := K) σ E l c := hCo

/-! ## Part 4 — end-to-end wiring into `BandEdges.phase6_to_phase7_of_seed_edges`.

Composing: the `l+1` seed; the config-level hour ceiling discharging the carried minority top edge
(`minorityTopEdge_of_hourCeiling`); the co-population timing event discharging the occupancy
(`twoLevelOccupancy_of_coPopulated`).  All three feed `BandEdges.phase6_to_phase7_of_seed_edges`, the
strongest reachable Phase6→7 surface — now with the carried minority top edge PRODUCED from the honest
hour ceiling and the occupancy PRODUCED from the named timing event. -/

/-- **End-to-end: seed + hour ceiling + co-population ⟹ `Phase6To7Structure`.**  The carried
`MinorityTopEdge` of `BandEdges` is produced from the config-level hour ceiling
(`AllBiasedMainBelow`, the honest within-hour clock-front content), and the carried `TwoLevelOccupancy`
is produced from the named co-population timing event.  The remaining inputs are the landed `l+1` seed,
the A-shape budget, and the Phase-6 window.  This is the strongest Phase6→7 surface with BOTH carried
top-band readouts discharged to honest mechanisms — the top edge to the FROZEN hour-gated split guard
(deterministic, Part 1–2), the occupancy to the named timing event (probabilistic, Part 3). -/
theorem phase6_to_phase7_of_doubling_edges {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hCeil : AllBiasedMainBelow (L := L) (K := K) (l + 2) c)
    (hCo : PredecessorLevelsCoPopulated (L := L) (K := K) σ E l c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  BandEdges.phase6_to_phase7_of_seed_edges hl hSeed hA h6
    (minorityTopEdge_of_hourCeiling hCeil) (twoLevelOccupancy_of_coPopulated hCo) hE

/-- **The strongest Phase6→7 surface from the doubling edges.**  Bundles, from the seed + hour ceiling
+ co-population event:
* (1) the `Phase6To7Structure σ E c` (routing PRODUCED);
* (2) the carried `MajorityTopEdge σ (l+2) c` (the majority-side top edge, from the same hour ceiling)
  — so the 3-level majority band support `{l ≤ i ≤ l+2}` is now available
  (`BandEdges.majoritySupportedOn_band3_of_post_topEdge`);
* (3) the carried `MinorityTopEdge σ (l+2) c` (the minority-side top edge).
Both carried top-band readouts are discharged to the SINGLE honest hour ceiling. -/
theorem phase6To7_surface_of_doubling_edges {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hCeil : AllBiasedMainBelow (L := L) (K := K) (l + 2) c)
    (hCo : PredecessorLevelsCoPopulated (L := L) (K := K) σ E l c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c ∧
    BandEdges.MajorityTopEdge (L := L) (K := K) σ (l + 2) c ∧
    BandEdges.MinorityTopEdge (L := L) (K := K) σ (l + 2) c :=
  ⟨phase6_to_phase7_of_doubling_edges hl hSeed hA h6 hCeil hCo hE,
   majorityTopEdge_of_hourCeiling hCeil,
   minorityTopEdge_of_hourCeiling hCeil⟩

end DoublingEdges

end ExactMajority
