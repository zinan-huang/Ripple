/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Band edges — the honest two-edge band statement and the per-partner gap-1 placement

This file (append-only; no existing file edited) closes the two remaining Theorem-6.2-band facts of
the Phase-6→7 routing, and — crucially — states the **honest** band geometry the landed facts
actually export, rather than the paper's headline "3-level band `{l, l+1, l+2}`".

## The honest band statement (survey result, NOT the paper headline)

What does the landed §6 collapse actually pin?  We surveyed `MainExponentConfinement` and
`UsefulMainFloor`:

* `MainExponentConfinement.mainProfile_collapse` drives the Main above-cap profile fraction
  `mainFrac` below `θ ≥ 1/n` within `frontWidthBound n = O(log log n)` hours — the
  doubly-exponential descent of `FrontTail.windowed_floor_crossing`.  Its readout
  (`MainProfileConfinedToUseful`) is `0.92·|M| ≤ #usefulMains` where `usefulMains` is the **CAP**
  `index < L` (`Phase5Convergence.biasedMainLtL`), NOT a 3-level band.
* So the landed collapse exports the *cap* `i < L` (the moving front has descended past the cap),
  with mass concentrated above the moving front.  The 3-level band `{−l, −(l+1), −(l+2)}` is the
  paper's *claim*; the landed `usefulMains` floor only certifies `index < L`.

Hence the HONEST `MajoritySupportedOn` support is the **two-edge band `{l ≤ i ≤ L}`**: the LOWER edge
`l ≤ i` is proven from the Phase-6 Post (`GapAlignment.majoritySupportedOn_atFloor_of_post`), the
UPPER edge `i ≤ L` is FREE (every `i : Fin (L+1)` has `i.val ≤ L`).  With the `l+1` seed the lower
edge sharpens to `l+1 ≤ i`.  That is the honest band statement: a two-edge floor/cap band, whose
width is `L − l + 1 = O(log n)` in general — NOT a constant 3-level band from the landed facts.

The genuine 3-level band requires ONE additional named upper-edge predicate (`MajorityTopEdge`,
the doubling-collapse top-band readout), exactly analogous to how `MainProfileConfinedToUseful`
carries the collapse readout.  We define it, prove it sharpens the support to the 3-level band, and
record the honest pigeonhole arithmetic against the consumers' `E` for BOTH the honest cap band and
the carried 3-level band.

## The per-partner placement (task #2), honest reduction

With the `l+1` seed, `GapAlignment.MinorityAboveFloor σ l c` holds: every live minority `j ≥ l+1`.
Adding a carried minority TOP edge (`MinorityTopEdge`, `j ≤ l+2`, the seed-floor's mirror upper
band) confines the minority to `{l+1, l+2}` — 2 levels.  Each minority `j ∈ {l+1, l+2}` has gap-1
predecessor `j − 1 ∈ {l, l+1}` — so the predecessor SET is exactly `{l, l+1}`, 2 levels.  The honest
placement is then NOT "the pigeonhole level happens to align" but **occupancy of BOTH band
predecessor levels**: if levels `l` and `l+1` each carry `≥ E` σ-opposite eliminators, then EVERY
live minority's gap-1 predecessor carries `≥ E` — `GapAlignedElimFloor` holds.  This is
`gapAlignedElimFloor_of_twoLevel_occupancy`.

The honest arithmetic against the consumer (`E ≤ 4n/15`, `BandRouting.phase6_to_phase7_of_post`):
the global budget `majorityProfileMass ≥ 4n/15` over the 2-level predecessor set `{l, l+1}` gives,
by pigeonhole, SOME level `≥ 4n/30 = 2n/15`; occupancy of BOTH at `≥ 2n/15` is the honest band
content the doubling chain provides (the chain passes through each level on its way down).  Both
`2n/15` and the 3-level `4n/45` are `≤ 4n/15`, so any are compatible with the consumer.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedExport

namespace ExactMajority

open scoped BigOperators

namespace BandEdges

variable {L K : ℕ}

/-! ## Part 1 — the honest two-edge band support (`{l ≤ i ≤ L}`), with the seed sharpening.

`GapAlignment.majoritySupportedOn_atFloor_of_post` already discharges the LOWER half of
`BandRouting.MajoritySupportedOn` on `{i | l ≤ i.val}` from the bare Post.  We strengthen it two ways:

1. The UPPER edge `i ≤ L` is FREE (`Fin (L+1)`), so the support lands on the explicit two-edge band
   `{i | l ≤ i.val ∧ i.val ≤ L}` — the honest band statement (a floor/cap band, NOT a 3-level band).
2. With the `l+1` seed (`SeedExport.post_of_seed` gives `highMass l = 0`, but the seed ALSO gives the
   sharper floor `l+1` on the σ-opposite band), the lower edge sharpens to `l+1 ≤ i`. -/

/-- **The honest two-edge majority band support (from the bare Post).**  Every exponent level with
positive σ-opposite (majority) eliminator mass lies in the explicit floor/cap band
`{i | l ≤ i.val ∧ i.val ≤ L}`.  The lower edge `l ≤ i` is the Phase-6 Post floor
(`GapAlignment.majoritySupportedOn_atFloor_of_post`); the upper edge `i.val ≤ L` is FREE for
`Fin (L+1)`.  This is the honest band statement the landed facts give — a band of width `L − l + 1`,
NOT a constant 3-level band. -/
theorem majoritySupportedOn_twoEdge_of_post {l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0) :
    BandRouting.MajoritySupportedOn (L := L) (K := K) σ
      (Finset.univ.filter (fun i : Fin (L + 1) => l ≤ i.val ∧ i.val ≤ L)) c := by
  intro i hi
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ i, ?_, ?_⟩
  · -- lower edge from the Post floor.
    have hsupp := GapAlignment.majoritySupportedOn_atFloor_of_post (σ := σ) hPost i hi
    rw [Finset.mem_filter] at hsupp
    exact hsupp.2
  · -- upper edge is free: `i.val ≤ L` for `Fin (L+1)`.
    have := i.2; omega

/-- **The σ-opposite (eliminator) band has the `l+1` floor under the seed.**  Under
`AllBiasedMainAbove (l+1) c` (every biased Main at index `≥ l+1`), any σ-opposite biased Main at
index `i` with positive mass has `l + 1 ≤ i.val`.  This sharpens the lower band edge by one notch
beyond the bare Post (which only gives `l ≤ i`).  Proof: a positive `elimGap1 σ i` summand is a
σ-opposite biased Main in `c`, which the seed pins to index `≥ l+1`. -/
theorem elim_index_ge_succ_floor {l : ℕ} {σ : Sign} {i : Fin (L + 1)}
    {c : Config (AgentState L K)}
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hi : 1 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count) :
    l + 1 ≤ i.val := by
  classical
  -- a positive count-sum forces a positive summand = a σ-opposite biased Main in `c` at index `i`.
  rcases Finset.exists_ne_zero_of_sum_ne_zero
    (by omega : (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count ≠ 0)
    with ⟨a, ha, hcount⟩
  rw [Phase7Convergence.elimGap1, Finset.mem_filter] at ha
  obtain ⟨-, hmain, ss, -, hb⟩ := ha
  have hpos : 0 < c.count a := Nat.pos_of_ne_zero hcount
  have hac : a ∈ c := Multiset.count_pos.mp hpos
  exact hSeed a hac hmain ss i hb

/-- **The honest two-edge majority band support, SEED-sharpened (`{l+1 ≤ i ≤ L}`).**  Under the
`l+1` seed, the σ-opposite majority mass is supported on the sharpened band
`{i | l + 1 ≤ i.val ∧ i.val ≤ L}` — lower edge `l+1` (from `elim_index_ge_succ_floor`), upper edge
`L` (free).  This is the honest seed band: a floor/cap band one notch above the bare-Post band. -/
theorem majoritySupportedOn_twoEdge_of_seed {l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c) :
    BandRouting.MajoritySupportedOn (L := L) (K := K) σ
      (Finset.univ.filter (fun i : Fin (L + 1) => l + 1 ≤ i.val ∧ i.val ≤ L)) c := by
  intro i hi
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ i, elim_index_ge_succ_floor (σ := σ) hSeed hi, by have := i.2; omega⟩

/-! ## Part 2 — the carried 3-level top edge, and the 3-level band support.

The honest two-edge band of Part 1 has width `L − l` (generic), NOT a constant.  The genuine 3-level
band `{l, l+1, l+2}` of the paper's Theorem 6.2 requires ONE additional named upper-edge predicate —
the doubling-collapse TOP-band readout (the moving front pins mass within `O(log log n)` of the
front, and the front sits at the band top).  We name it `MajorityTopEdge` and prove it sharpens the
support to the 3-level band, recording the honest pigeonhole constant `4n/45`. -/

/-- **`MajorityTopEdge σ top c`** — every level with positive σ-opposite (majority) eliminator mass
sits at index `≤ top`.  This is the carried doubling-collapse TOP-band readout: the moving front of
the `mainProfile_collapse` descent confines the surviving majority mass within `O(log log n)` of the
front, and `top = l + 2` is the paper's 3-level top.  Carried as ONE named field (analogous to
`MainExponentConfinement.MainProfileConfinedToUseful`, the cap readout), since the landed `usefulMains`
floor certifies the CAP `< L` but not this sharp 3-level top. -/
def MajorityTopEdge (σ : Sign) (top : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : Fin (L + 1),
    1 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count → i.val ≤ top

/-- **The 3-level majority band support (Post floor + carried top edge).**  Combining the bare-Post
floor (`l ≤ i`) with the carried top edge (`i ≤ l+2`), the σ-opposite majority mass is supported on
the 3-level band `{i | l ≤ i.val ∧ i.val ≤ l+2}`.  This is the paper's Theorem-6.2 band — the floor
half is PROVEN, the top half is the single carried `MajorityTopEdge` readout. -/
theorem majoritySupportedOn_band3_of_post_topEdge {l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0)
    (hTop : MajorityTopEdge (L := L) (K := K) σ (l + 2) c) :
    BandRouting.MajoritySupportedOn (L := L) (K := K) σ
      (Finset.univ.filter (fun i : Fin (L + 1) => l ≤ i.val ∧ i.val ≤ l + 2)) c := by
  intro i hi
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ i, ?_, hTop i hi⟩
  have hsupp := GapAlignment.majoritySupportedOn_atFloor_of_post (σ := σ) hPost i hi
  rw [Finset.mem_filter] at hsupp
  exact hsupp.2

/-- **The 3-level band has card `≤ 3`.**  The filter band `{i : Fin (L+1) | l ≤ i.val ∧ i.val ≤ l+2}`
has at most `3` elements: the map `i ↦ i.val` is injective into the 3-element interval
`{l, l+1, l+2}`. -/
theorem band3_card_le_three {l : ℕ} :
    (Finset.univ.filter (fun i : Fin (L + 1) => l ≤ i.val ∧ i.val ≤ l + 2)).card ≤ 3 := by
  classical
  -- inject into `Finset.Icc l (l+2)` (card 3) via `Fin.val`.
  have hsub : (Finset.univ.filter (fun i : Fin (L + 1) => l ≤ i.val ∧ i.val ≤ l + 2)).image
      (fun i : Fin (L + 1) => i.val) ⊆ Finset.Icc l (l + 2) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨i, ⟨hl, hu⟩, rfl⟩ := hx
    exact Finset.mem_Icc.mpr ⟨hl, hu⟩
  have hinj : (Finset.univ.filter (fun i : Fin (L + 1) => l ≤ i.val ∧ i.val ≤ l + 2)).card
      = ((Finset.univ.filter (fun i : Fin (L + 1) => l ≤ i.val ∧ i.val ≤ l + 2)).image
        (fun i : Fin (L + 1) => i.val)).card := by
    rw [Finset.card_image_of_injective _ Fin.val_injective]
  rw [hinj]
  calc _ ≤ (Finset.Icc l (l + 2)).card := Finset.card_le_card hsub
    _ = 3 := by rw [Nat.card_Icc]; omega

/-- **The honest 3-level `4n/45` per-partner floor (capstone of Part 2).**  From the A-shape budget
`hA` (`majorityProfileMass ≥ 4n/15`) and the carried 3-level band (Post floor + `MajorityTopEdge`),
SOME band level `i ∈ {l, l+1, l+2}` carries `≥ 4n/45` σ-opposite eliminators.  This is the paper's
Theorem-6.2 pigeonhole constant — `BandRouting.exists_band_level_floor_4n45` instantiated at the
honest 3-level band.  The constant `4n/45 ≤ 4n/15 = E`, so it is consumer-compatible. -/
theorem exists_band3_level_floor_4n45 {l n : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0)
    (hTop : MajorityTopEdge (L := L) (K := K) σ (l + 2) c)
    (hne : (Finset.univ.filter (fun i : Fin (L + 1) => l ≤ i.val ∧ i.val ≤ l + 2)).Nonempty) :
    ∃ i ∈ Finset.univ.filter (fun i : Fin (L + 1) => l ≤ i.val ∧ i.val ≤ l + 2),
      (4 : ℝ) * (n : ℝ) / 45
        ≤ (((Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count : ℕ) : ℝ) :=
  BandRouting.exists_band_level_floor_4n45 hA hne band3_card_le_three
    (majoritySupportedOn_band3_of_post_topEdge hPost hTop)

/-! ## Part 3 — the per-partner gap-1 placement via two-level band occupancy (task #2).

The genuine routing residual `GapAlignedElimFloor` asks for `≥ E` eliminators at the SPECIFIC gap-1
predecessor of EACH live minority — pigeonhole-at-one-level (Part 2) does NOT give that.  The honest
reduction: with the seed's `MinorityAboveFloor` (minority `≥ l+1`) and a carried minority TOP edge
(`≤ l+2`), the minority is confined to `{l+1, l+2}`, so its predecessor set is exactly `{l, l+1}` —
TWO levels.  Occupancy of BOTH levels covers every minority partner. -/

/-- **`MinorityTopEdge σ top c`** — every LIVE minority level `j` sits at index `≤ top`.  The mirror
of `GapAlignment.MinorityAboveFloor` (the floor): the carried upper band of the minority.  With
`top = l + 2` and the seed floor `l + 1`, the minority is confined to `{l+1, l+2}`.  Carried as ONE
named field (the doubling-collapse top-band readout on the minority side). -/
def MinorityTopEdge (σ : Sign) (top : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count → j.val ≤ top

/-- **Two-level occupancy predicate.**  Both band predecessor levels `l` and `l+1` carry `≥ E`
σ-opposite eliminators.  This is the honest "the doubling chain passes through EACH level" occupancy
fact: as the chain descends, mass occupies each band level, so BOTH predecessor levels are populated
to the per-level share `E`.  When the minority is confined to `{l+1, l+2}` (seed floor + top edge),
this occupancy covers every minority's gap-1 predecessor. -/
def TwoLevelOccupancy (σ : Sign) (E l : ℕ) (c : Config (AgentState L K)) : Prop :=
  (∀ i : Fin (L + 1), i.val = l →
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count) ∧
  (∀ i : Fin (L + 1), i.val = l + 1 →
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count)

/-- **The per-partner placement (task #2, honest reduction).**  Given:
* `hAbove : MinorityAboveFloor σ l c` (the seed gives this — minority `≥ l+1`),
* `hTop : MinorityTopEdge σ (l+2) c` (the carried minority top edge — minority `≤ l+2`),
* `hOcc : TwoLevelOccupancy σ E l c` (BOTH predecessor levels `{l, l+1}` carry `≥ E`),

the gap-1 routing `GapAlignedElimFloor σ E c` holds.  Proof: a live minority `j` has
`l+1 ≤ j.val ≤ l+2` (floor + top), and its gap-1 predecessor `i` (`i + 1 = j`) has `i.val = j − 1 ∈
{l, l+1}`; the corresponding occupancy clause supplies `≥ E` at `i`.  This is the honest occupancy
reduction — NOT a pigeonhole alignment, but EVERY band predecessor level populated. -/
theorem gapAlignedElimFloor_of_twoLevel_occupancy {l E : ℕ} {σ : Sign}
    {c : Config (AgentState L K)}
    (hAbove : GapAlignment.MinorityAboveFloor (L := L) (K := K) l σ c)
    (hTop : MinorityTopEdge (L := L) (K := K) σ (l + 2) c)
    (hOcc : TwoLevelOccupancy (L := L) (K := K) σ E l c) :
    BandRouting.GapAlignedElimFloor (L := L) (K := K) σ E c := by
  intro j hj i hgap
  -- the live minority sits in `{l+1, l+2}`.
  have hlo : l + 1 ≤ j.val := hAbove j hj
  have hhi : j.val ≤ l + 2 := hTop j hj
  -- the predecessor index is `j − 1 ∈ {l, l+1}`.
  have hival : i.val = l ∨ i.val = l + 1 := by omega
  rcases hival with hi | hi
  · exact hOcc.1 i hi
  · exact hOcc.2 i hi

/-- **The two-level occupancy honest arithmetic against the consumer `E ≤ 4n/15`.**  The global
budget `majorityProfileMass ≥ 4n/15` over the 2-level predecessor set `{l, l+1}` gives, by
pigeonhole, SOME level `≥ 4n/30 = 2n/15`.  Occupancy of BOTH at the per-level share `E ≤ 2n/15` is
the honest band content (the doubling chain passes through each level).  We record the constant: if
`E ≤ 2n/15` then `E ≤ 4n/15` (consumer-compatible), and the 2-level pigeonhole bound `2n/15` is
strictly tighter than the 3-level `4n/45`.  Pure arithmetic certificate. -/
theorem twoLevel_constant_le_consumer {n E : ℕ}
    (hE : (E : ℝ) ≤ (2 : ℝ) * (n : ℝ) / 15) :
    (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-! ## Part 4 — end-to-end: the seed + carried edges ⟹ `GapAlignedElimFloor` ⟹ `Phase6To7Structure`.

Composing: the `l+1` seed (`SeedExport`) supplies the bare Post AND `MinorityAboveFloor`; the carried
minority top edge plus two-level occupancy supply `GapAlignedElimFloor` (Part 3); `BandRouting`
wires it to `Phase6To7Structure`.  This closes the routing with the carried residual reduced to
exactly the two named TOP-band readouts + the two-level occupancy (the honest doubling-collapse
content), with the FLOOR halves PROVEN from the landed drain. -/

/-- **`GapAlignedElimFloor` from the seed + carried minority top edge + two-level occupancy.**  The
seed `AllBiasedMainAbove (l+1)` discharges `MinorityAboveFloor` (`SeedExport.verdict_of_seed`); the
carried minority top edge confines the minority to `{l+1, l+2}`; two-level occupancy populates the
predecessor set `{l, l+1}`.  Together they give the per-partner routing `GapAlignedElimFloor σ E c`. -/
theorem gapAlignedElimFloor_of_seed {l E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hTop : MinorityTopEdge (L := L) (K := K) σ (l + 2) c)
    (hOcc : TwoLevelOccupancy (L := L) (K := K) σ E l c) :
    BandRouting.GapAlignedElimFloor (L := L) (K := K) σ E c :=
  gapAlignedElimFloor_of_twoLevel_occupancy
    ((SeedExport.verdict_of_seed hSeed).1 σ) hTop hOcc

/-- **End-to-end (seed + carried edges + occupancy ⟹ `Phase6To7Structure`).**  From the `l+1` seed,
the A-shape budget `hA`, the Phase-6 window `h6`, the carried minority top edge, and two-level
occupancy, the full Phase-6→7 eliminator-margin structure follows — the routing field
`GapAlignedElimFloor` is now PRODUCED from the seed + the named top-band readouts, no longer assumed.
The carried residual is reduced to exactly `MinorityTopEdge` + `TwoLevelOccupancy` (the honest
doubling-collapse top-band content), with every FLOOR half proven from the landed drain. -/
theorem phase6_to_phase7_of_seed_edges {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hTop : MinorityTopEdge (L := L) (K := K) σ (l + 2) c)
    (hOcc : TwoLevelOccupancy (L := L) (K := K) σ E l c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  SeedExport.phase6_to_phase7_of_seed hl hSeed hA h6
    (gapAlignedElimFloor_of_seed hSeed hTop hOcc) hE

/-- **The strongest Phase6→7 surface from the seed + carried edges.**  Bundles, from the SINGLE seed
plus the two carried top-band readouts and the two-level occupancy:
* (1) the standard `Phase6To7Structure σ E c` (routing PRODUCED, not assumed);
* (2) `MinorityAboveFloor l σ c` for EVERY sign (the seed's floor placement);
* (3) the `cancelSplit` step-stability of the `l+1` floor.
This is the strongest reachable Phase6→7 form with the routing field discharged. -/
theorem phase6To7_surface_of_seed_edges {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hTop : MinorityTopEdge (L := L) (K := K) σ (l + 2) c)
    (hOcc : TwoLevelOccupancy (L := L) (K := K) σ E l c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c ∧
    (∀ τ : Sign, GapAlignment.MinorityAboveFloor (L := L) (K := K) l τ c) ∧
    (∀ {s t : AgentState L K}, s ∈ c → t ∈ c → s.role = Role.main → t.role = Role.main →
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).1.bias = Bias.dyadic ss i → l + 1 ≤ i.val) ∧
      (∀ (ss : Sign) (i : Fin (L + 1)),
          (cancelSplit L K s t).2.bias = Bias.dyadic ss i → l + 1 ≤ i.val)) :=
  ⟨phase6_to_phase7_of_seed_edges hl hSeed hA h6 hTop hOcc hE,
   (SeedExport.verdict_of_seed hSeed).1, (SeedExport.verdict_of_seed hSeed).2⟩

end BandEdges

end ExactMajority
