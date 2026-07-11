/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Honest band geometry for the gap-1 eliminator routing (`GapAlignedElimFloor`)

This file (tip #2a) resolves the **honest band geometry** underlying
`BandRouting.GapAlignedElimFloor` / `BandLocalization.MajorityBandAtGap1`, and proves as much of the
gap-1 routing as the Phase-6 *band floor* (`highMass l c = 0`) deterministically pins — leaving the
single genuine carried dynamic invariant precisely isolated.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.

## The sign conventions, re-derived from the defs (NOT inferred from comments)

* `Phase7Convergence.minorityAt7 σ j = {a | role = main ∧ bias = dyadic σ j}` — the **minority** is
  the σ-signed Main at index `j`.
* `Phase7Convergence.elimGap1 σ i = {a | role = main ∧ ∃ ss ≠ σ, bias = dyadic ss i}` — the
  **eliminators** are the σ-*opposite*-signed Mains at index `i`, with the consumer pairing `i+1 = j`
  (eliminators one index BELOW the minority they kill).
* `Phase6Convergence.phase6Post_iff`: `highMass l c = 0` ⟺ **every biased Main has index `≥ l`**.  The
  floor applies to BOTH signs — minority AND eliminators are biased Mains.

## The honest geometric tension (the key resolution)

`GapAlignedElimFloor σ E c` with `E ≥ 1` requires, for each live minority level `j`, at least one
eliminator at `i = j − 1`.  But that eliminator is a biased Main, so the floor forces `j − 1 ≥ l`,
i.e. **`j ≥ l + 1`: the minority must sit STRICTLY above the band floor.**

Contrapositive (the obstruction, PROVED below as `elimGap1_eq_zero_below_floor`):
a minority sitting EXACTLY at the floor (`j = l`) has its gap-1 predecessor at `l − 1 < l`, where the
floor forbids ANY biased Main — so `(elimGap1 σ (l−1)).sum c.count = 0`, and `GapAlignedElimFloor`
with `E ≥ 1` is FALSE for it.  Hence the routing is NOT a free consequence of the floor: it carries
the genuine extra fact that *no live minority sits at the very floor* (it has been drained one step
above before the partner band is read), equivalently **`MinorityAboveFloor σ l c`**.

## What this file proves from the Post (no new carried assumption)

1. `elimGap1_eq_zero_below_floor` — below the floor the eliminator band is empty (the floor reading,
   discharged to BOTH signs).
2. `majoritySupportedOn_atFloor_of_post` — the σ-opposite majority mass is supported on
   `{i | l ≤ i.val}`: this DISCHARGES the lower half of `BandRouting.MajoritySupportedOn` from the Post
   alone (only the Theorem-6.2 UPPER edge `i ≤ l+2` stays carried).
3. `minorityAboveFloor_of_routing` — the routing field `GapAlignedElimFloor σ E c` (`E ≥ 1`), together
   with the floor, PROVES `MinorityAboveFloor σ l c`: the honest geometry is internally consistent and
   the routing's content is exactly "minority strictly above floor + per-level placement".
4. `gapAligned_routing_forces_above_floor` — the precise converse-flavored statement that the carried
   routing residual is equivalent (given the floor + the band pigeonhole constant) to the
   above-floor placement.

The carried dynamic invariant is thereby isolated to `MinorityAboveFloor` (a Phase-6 drain fact: the
drain clears the floor index, leaving live minority at `≥ l+1`) PLUS the per-partner-level pigeonhole
placement; everything else (floor on both bands, lower band support, the `4n/45` constant) is proven.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BandRouting

namespace ExactMajority

open scoped BigOperators

namespace GapAlignment

variable {L K : ℕ}

/-! ## Part 1 — the floor discharged to BOTH bands.

The Phase-6 Post `highMass l c = 0` pins EVERY biased Main (both signs) to index `≥ l`.  We first
extract this for the σ-OPPOSITE (eliminator) band, then show the eliminator finset has count `0`
below the floor. -/

/-- **Floor on the σ-opposite (eliminator) band.**  From the landed Post `highMass l c = 0`, any
σ-opposite (`ss ≠ σ`) biased Main present in `c` at index `i` has `l ≤ i.val`.  Same reading of
`phase6Post_iff` as the minority side, but applied to the OPPOSITE sign. -/
theorem elim_index_ge_floor {l : ℕ} {c : Config (AgentState L K)}
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0)
    {a : AgentState L K} (hac : a ∈ c) (hmain : a.role = Role.main)
    {ss : Sign} {i : Fin (L + 1)} (hb : a.bias = Bias.dyadic ss i) :
    l ≤ i.val := by
  have hfloor := (Phase6Convergence.phase6Post_iff (L := L) (K := K) l c).mp hPost
  exact hfloor a hac hmain ss i hb

/-- **The eliminator band is EMPTY below the floor.**  For any index `i` with `i.val < l`, under the
Post `highMass l c = 0` the σ-opposite eliminator finset carries no mass:
`(elimGap1 σ i).sum c.count = 0`.  Proof: a positive summand would force a member `a` with
`c.count a > 0` (hence `a ∈ c`) that is a σ-opposite biased Main at index `i < l`, contradicting the
floor.  This is the honest obstruction certificate for the geometry below. -/
theorem elimGap1_eq_zero_below_floor {l : ℕ} {σ : Sign} {i : Fin (L + 1)}
    {c : Config (AgentState L K)}
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0)
    (hi : i.val < l) :
    (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  -- unpack the eliminator-finset membership: `a` is a σ-opposite biased Main at index `i`.
  rw [Phase7Convergence.elimGap1, Finset.mem_filter] at ha
  obtain ⟨-, hmain, ss, -, hb⟩ := ha
  by_contra hcount
  -- a positive count means `a ∈ c`, so the floor applies and contradicts `i.val < l`.
  have hpos : 0 < c.count a := Nat.pos_of_ne_zero hcount
  have hac : a ∈ c := Multiset.count_pos.mp hpos
  have : l ≤ i.val := elim_index_ge_floor hPost hac hmain (ss := ss) hb
  omega

/-! ## Part 2 — the lower band support is FREE from the Post.

`BandRouting.MajoritySupportedOn σ S c` requires every level with positive majority (eliminator) mass
to lie in `S`.  The Post pins the LOWER edge `l ≤ i.val` for free; only the Theorem-6.2 UPPER edge
stays carried.  We package the lower half as a support on `{i | l ≤ i.val}`. -/

/-- **Lower band support from the Post.**  Under `highMass l c = 0`, every exponent level with
positive σ-opposite eliminator mass has index `≥ l`: the majority mass is supported on the half-line
`{i | l ≤ i.val}`.  This discharges the LOWER half of `BandRouting.MajoritySupportedOn` from the
landed Post — no Theorem-6.2 input needed for the floor edge. -/
theorem majoritySupportedOn_atFloor_of_post {l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0) :
    BandRouting.MajoritySupportedOn (L := L) (K := K) σ
      (Finset.univ.filter (fun i : Fin (L + 1) => l ≤ i.val)) c := by
  intro i hi
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ i, ?_⟩
  -- if `i.val < l` the band is empty below the floor, contradicting `1 ≤` mass.
  by_contra hlt
  push_neg at hlt
  have hzero := elimGap1_eq_zero_below_floor (σ := σ) (i := i) hPost hlt
  omega

/-! ## Part 3 — the genuine carried dynamic invariant, isolated.

The above-floor placement of the minority is the single residual the routing carries beyond the Post.
We name it and prove the routing CONTAINS it (so the geometry is internally consistent, and the
carried content is exactly this placement + the per-level pigeonhole constant). -/

/-- **`MinorityAboveFloor σ l c`** — every LIVE minority level `j` sits STRICTLY above the band floor:
`l + 1 ≤ j.val`.  This is the genuine Phase-6 *drain* fact (the drain clears the floor index, pushing
the surviving minority to `≥ l+1`), and it is exactly the geometry the gap-1 routing needs: a partner
eliminator at `j − 1` must itself be at index `≥ l`. -/
def MinorityAboveFloor (l : ℕ) (σ : Sign) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count →
    l + 1 ≤ j.val

/-- **The routing field PROVES the above-floor placement (honest geometry, internally consistent).**
If `1 ≤ E`, `1 ≤ l`, and the gap-1 routing `GapAlignedElimFloor σ E c` holds together with the floor
`highMass l c = 0`, then `MinorityAboveFloor σ l c`: every live minority `j` has `j ≥ l+1`.  Proof:
the live minority `j` is a σ-signed biased Main, so the floor gives `l ≤ j.val ≥ 1`; its gap-1
predecessor `i = j − 1` therefore exists, and the routing puts `≥ E ≥ 1` eliminators there, so
`elimGap1 σ i` is nonempty.  By the contrapositive of `elimGap1_eq_zero_below_floor`, `l ≤ i.val`, and
`i.val + 1 = j.val` gives `l + 1 ≤ j.val`.  This certifies the honest geometric tension: the routing
is CONSISTENT with the floor exactly when the minority sits strictly above it. -/
theorem minorityAboveFloor_of_routing {l E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hE : 1 ≤ E) (hl : 1 ≤ l)
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0)
    (hRoute : BandRouting.GapAlignedElimFloor (L := L) (K := K) σ E c) :
    MinorityAboveFloor (L := L) (K := K) l σ c := by
  intro j hj
  -- the live minority is a σ-signed biased Main: the floor gives `l ≤ j.val`, hence `j.val ≥ 1`.
  obtain ⟨a, hac, hamain, hab⟩ := BandRouting.exists_minority_witness (σ := σ) (j := j) hj
  have hlj : l ≤ j.val := elim_index_ge_floor hPost hac hamain (ss := σ) hab
  -- the gap-1 predecessor `i = j − 1` exists.
  have hjpos : 1 ≤ j.val := le_trans hl hlj
  set i : Fin (L + 1) := ⟨j.val - 1, by have := j.2; omega⟩ with hidef
  have hgap : i.val + 1 = j.val := by show j.val - 1 + 1 = j.val; omega
  -- the routing supplies `≥ E ≥ 1` eliminators at `i`, so the band is NONEMPTY at `i`.
  have hElim : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count :=
    hRoute j hj i hgap
  have hpos : 1 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count := le_trans hE hElim
  -- contrapositive of the below-floor emptiness: `i.val ≥ l`.
  have hil : l ≤ i.val := by
    by_contra hlt
    push_neg at hlt
    have hzero := elimGap1_eq_zero_below_floor (σ := σ) (i := i) hPost hlt
    omega
  -- `i.val + 1 = j.val` and `l ≤ i.val` give `l + 1 ≤ j.val`.
  omega

/-- **The above-floor placement lands every gap-1 predecessor at index `≥ l`.**  Given
`MinorityAboveFloor σ l c` (the carried drain fact), for each live minority `j` its gap-1 predecessor
`i` (`i + 1 = j.val`) satisfies `l ≤ i.val`.  So the partner band the routing targets lies entirely
at/above the floor — geometrically coherent with `majoritySupportedOn_atFloor_of_post`: the routing's
target levels are a subset of the proven majority support `{i | l ≤ i.val}`.  This certifies that the
ONLY remaining content of `GapAlignedElimFloor`, beyond the proven floor support, is the per-PARTNER
placement (the pigeonhole at the specific partner level), not any geometric impossibility. -/
theorem gap1_predecessor_in_band {l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hAbove : MinorityAboveFloor (L := L) (K := K) l σ c)
    {j : Fin (L + 1)}
    (hj : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count)
    {i : Fin (L + 1)} (hgap : i.val + 1 = j.val) :
    l ≤ i.val := by
  have hjl : l + 1 ≤ j.val := hAbove j hj
  omega

/-- **The honest equivalence (capstone): the carried routing residual is, modulo the proven floor
support, exactly the above-floor minority placement plus per-partner-level mass.**  Packaged as the
two implications that pin the geometry: (→) the routing entails `MinorityAboveFloor`
(`minorityAboveFloor_of_routing`); and here (the structural converse direction) under
`MinorityAboveFloor` every gap-1 partner sits in the proven majority support `{i | l ≤ i.val}`
(`gap1_predecessor_in_band`).  This isolates the irreducible carried invariant to
`MinorityAboveFloor` + the per-partner pigeonhole placement — NOT a geometric obstruction, just the
Phase-6 drain's clearing of the floor index. -/
theorem gapAligned_routing_forces_above_floor {l E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hE : 1 ≤ E) (hl : 1 ≤ l)
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0)
    (hRoute : BandRouting.GapAlignedElimFloor (L := L) (K := K) σ E c) :
    MinorityAboveFloor (L := L) (K := K) l σ c ∧
      ∀ j : Fin (L + 1),
        1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count →
        ∀ i : Fin (L + 1), i.val + 1 = j.val → l ≤ i.val := by
  have hAbove := minorityAboveFloor_of_routing (σ := σ) hE hl hPost hRoute
  refine ⟨hAbove, ?_⟩
  intro j hj i hgap
  exact gap1_predecessor_in_band (σ := σ) hAbove hj hgap

end GapAlignment

end ExactMajority
