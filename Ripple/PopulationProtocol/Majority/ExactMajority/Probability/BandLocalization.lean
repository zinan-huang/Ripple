/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Band localization — the per-level B/C localizations as deterministic band bookkeeping

Per `HANDOFF_PERLEVEL.md` (ChatGPT Pro blueprint, 2026-06-10), the residual B and C are NOT
counting questions — the global `4n/15` majority-eliminator budget is already proved deterministically
in `MarginLedgers.majorityProfileMass_floor`.  What is missing is a **band-position / Phase-6 Post**
fact: the majority eliminators must sit at the specific gap-1 predecessor level of each live minority
level.  The blueprint's short verdict:

> For B, the missing fact is not "there are many majority eliminators globally"
> (`majorityProfileMass_floor` already proves that).  The remaining localization is a band-position /
> Phase-6 Post export: the majority mass must be located at the gap-1 predecessor level of each live
> minority level.  This is exactly the carried field `MarginLedgers.Phase6HighMassDrained`.
>
> For C, gap-2 does NOT create an obstruction; under the frozen `cancelSplit`, gap-2 preserves or
> increases the σ-opposite eliminator supply.  The only genuine eliminator loss is same-level
> cancellation.  So C is deterministic transition bookkeeping once B and the Phase-7 survival bounds
> are present; it is not a new probability tail.

This file delivers, ALL append-only (no existing file edited):

1. **The band-position structure** (the majority-band predicate + minority-confinement predicate),
   defined as honest `Prop`s with documented provenance pointing at the Phase-6 high-mass drain.
2. **The localization derivations**: band-position ⟹ `MarginLedgers.Phase6HighMassDrained`
   (deterministic gap-1 band bookkeeping); and the C-side `cancelSplit` eliminator-spend reading
   (same-level is the only loss; gap-1/gap-2 preserve or grow σ-opposite supply) lifted to
   `MarginLedgers.Phase7SurvivalUpperBounds`.
3. **Wiring** into the landed consumers `MarginLedgers.phase6_to_phase7_eliminator_margin_of_confinement`
   and `phase7_to_phase8_eliminator_margin_of_phase7`, filling their carried
   `Phase6HighMassDrained` / `Phase7SurvivalUpperBounds` fields from the band predicates.

### Definitional bridges used throughout (verified against the landed files)

* `MarginLedgers.majorityAtExp σ i` (`{a | role=main ∧ ∃ s≠σ, bias=dyadic s i}`) is DEFINITIONALLY
  EQUAL to `Phase7Convergence.elimGap1 σ i` (same filter).  So the σ-opposite (majority) eliminator
  mass at level `i` IS the gap-1 eliminator mass the `Phase6HighMassDrained` field counts.
* `MarginLedgers.minorityAtExp σ j = mainAtExp σ j = Phase7Convergence.minorityAt7 σ j
    = Phase8Convergence.minorityAt σ j` (all the same filter, `MarginLedgers.mainAtExp_eq_*`).

The band predicates remain the named residual pointing at Phase 6's convergence proof; §"What
Phase 6 must export" documents precisely the additional Post.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarginLedgers

namespace ExactMajority

open scoped BigOperators

namespace BandLocalization

variable {L K : ℕ}

/-! ## Part 1 — the band-position structure.

After the Phase-6 high-mass drain has run, the biased Mains have been split downward in magnitude
(index `i` increases under `doSplit`, `Phase6Convergence` "Index INCREASES `j → j+1` (magnitude
halves)").  The drain drives `highMass l → 0`, i.e. NO biased Main survives at index `< l`: every
surviving biased Main sits at index `≥ l`.  This is the band floor.

The blueprint's structural claim is then a TWO-band-alignment fact:

* the **majority eliminator band** (σ-opposite Mains) occupies the levels at/above the floor, and in
  particular every gap-1 predecessor level of a live minority carries the full per-level share `E`;
* the **live minority band** sits one index above the eliminators it is paired against, so each live
  minority level `j` has its gap-1 predecessor `i = j − 1` INSIDE the majority eliminator band.

We capture exactly these two facts as honest `Prop`s, phrased directly on the `Phase7`-entry
per-level finsets that the downstream `Phase6HighMassDrained` consumer reads
(`Phase7Convergence.elimGap1` = `MarginLedgers.majorityAtExp`, and
`Phase7Convergence.minorityAt7` = `MarginLedgers.minorityAtExp`). -/

/-- **Majority-band predicate (band-position fact).**  Every gap-1 predecessor level `i = j − 1` of a
LIVE minority level `j` carries at least the per-level eliminator share `E` of σ-opposite (majority)
eliminators.  Provenance: after the Phase-6 high-mass drain, the σ-opposite eliminator profile
mass — globally `≥ 4n/15` by `MarginLedgers.majorityProfileMass_floor` — is concentrated at the
band one index below the minority it is paired against (the `doSplit` magnitude-halving routes
eliminators to the partner band).  `MarginLedgers.majorityAtExp σ i = Phase7Convergence.elimGap1 σ i`
definitionally, so this is the σ-opposite mass at level `i`. -/
def MajorityBandAtGap1 (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count →
    ∀ i : Fin (L + 1), i.val + 1 = j.val →
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count

/-- **Minority-confinement predicate (band-position fact).**  Every LIVE minority level `j` has a
gap-1 predecessor index in range, i.e. `j.val ≥ 1` and the index `j − 1` exists as a `Fin (L + 1)`.
Provenance: the Phase-6 drain leaves the minority band strictly above the absorbing floor (the
eliminand exponents are never at the bottom index `0` once the high-mass drain has separated the two
bands by one step), so the gap-1 reach to the predecessor level is always available.  This is the
"minority levels sit ≤ the band's gap-1 reach" confinement: a live minority at level `j` reaches its
partner eliminators at `j − 1`. -/
def MinorityConfinedGap1 (σ : Sign) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count →
    ∃ i : Fin (L + 1), i.val + 1 = j.val

/-- **The full Phase-6 band-position facts (bundle).**  Packages the two band predicates the
Phase-6 Post must export: minority confinement (every live minority has a gap-1 predecessor level)
and the majority band (that predecessor level carries `≥ E` eliminators).  This is the precise
deterministic content the blueprint identifies as the residual — definitionally assembling into
`MarginLedgers.Phase6HighMassDrained`. -/
structure Phase6BandPositionFacts (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop where
  /-- Every live minority level has a gap-1 predecessor index in range. -/
  hConfined : MinorityConfinedGap1 (L := L) (K := K) σ c
  /-- That predecessor level carries `≥ E` σ-opposite (majority) eliminators. -/
  hBand : MajorityBandAtGap1 (L := L) (K := K) σ E c

/-! ## Part 2 — the B-side localization derivation.

Band-position ⟹ `Phase6HighMassDrained`.  This is the deterministic gap-1 band bookkeeping the
blueprint describes: for each live minority level `j`, minority-confinement supplies the predecessor
`i = j − 1`, and the majority-band fact supplies `≥ E` eliminators there.  No global counting is
re-done; the `4n/15` budget is already in `MarginLedgers.majorityProfileMass_floor` (consumed by the
landed adapter `phase6_to_phase7_eliminator_margin_of_confinement` as consistency). -/

/-- **B-localization (deterministic band bookkeeping).**  The band-position facts deterministically
discharge `MarginLedgers.Phase6HighMassDrained`: for each live minority level `j`, the confinement
gives a gap-1 predecessor `i = j − 1`, and the majority-band fact gives `≥ E` σ-opposite eliminators
at `i`. -/
theorem phase6HighMassDrained_of_bandPosition {σ : Sign} {E : ℕ} {c : Config (AgentState L K)}
    (hBand : Phase6BandPositionFacts (L := L) (K := K) σ E c) :
    MarginLedgers.Phase6HighMassDrained (L := L) (K := K) σ E c := by
  intro j hj
  obtain ⟨i, hgap⟩ := hBand.hConfined j hj
  exact ⟨i, hgap, hBand.hBand j hj i hgap⟩

/-- **B end-to-end (band-position + A-shape global budget ⟹ `Phase6To7Structure`).**  Wires the
B-localization into the landed `MarginLedgers.phase6_to_phase7_eliminator_margin_of_confinement`:
the A-shape confinement profile `hA` certifies the global `≥ 4n/15` budget (consistency for
`E ≤ 4n/15`), the Phase-6 window `h6` is the structural Pre, and the band-position facts supply the
carried per-level `Phase6HighMassDrained` — yielding `EliminatorMargins.Phase6To7Structure σ E c`. -/
theorem phase6_to_phase7_of_bandPosition {n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hBand : Phase6BandPositionFacts (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  MarginLedgers.phase6_to_phase7_eliminator_margin_of_confinement hA h6
    (phase6HighMassDrained_of_bandPosition hBand) hE

/-! ## Part 3 — the C-side: the `cancelSplit` eliminator-spend reading and the survival band.

The blueprint's §2 verdict, verified against the FROZEN `cancelSplit` (Transition.lean
:1228-1258): the three opposite-sign gap cases are

* **same-level** (`i = j`): both Mains go `bias := .zero` — one σ-opposite eliminator SPENT, one
  σ-minority drained;
* **gap-1** (`i + 1 = j` or `j + 1 = i`): the SMALLER-index agent's exponent increments (keeps its
  sign), the LARGER-index agent goes `.zero` — one σ-minority drained, the eliminator PRESERVED
  (moved up one level);
* **gap-2** (`i + 2 = j` or `j + 2 = i`): the smaller-index agent increments (keeps its sign), the
  larger-index agent takes the SMALLER-index agent's SIGN at level `i+1`/`j+1` — so the σ-opposite
  supply is PRESERVED OR GROWS (the gap-2 subtlety the blueprint flags: it never reduces the
  eliminator supply).

So the only eliminator LOSS is same-level cancellation, charged to one σ-minority drained.  The
per-level survival ledger is therefore deterministic once B (the Phase-7-entry margins) and the
landed minority-survival UPPER bounds are present.  Below we phrase the survival band exactly on the
`Phase8`-entry per-level finsets the consumer reads (`Phase8Convergence.minorityAt` /
`elimAbove`). -/

/-- **The frozen `cancelSplit` same-level spend reading (deterministic, paper-faithful).**  Reading
the FROZEN `cancelSplit`: when the two opposite-sign Mains share an exponent (`i = j`) both
go `.zero`, so exactly one σ-opposite eliminator is spent against one σ-minority drained; in every
other branch (gap-1, gap-2, identity, same-sign, zero-bias) the σ-opposite supply is preserved or
grows.  We record this as the per-pair fact that gap-1 PRESERVES the smaller-index eliminator (it
re-emerges at the incremented index, same sign).  This is the deterministic transition fact under-
pinning the C survival ledger; the global subtraction "spent ≤ drained" is its aggregate. -/
theorem cancelSplit_gap1_preserves_smaller_sign (s t : AgentState L K)
    (sgn_s sgn_t : Sign) (i j : Fin (L + 1))
    (hs : s.bias = Bias.dyadic sgn_s i) (ht : t.bias = Bias.dyadic sgn_t j)
    (hne : sgn_s ≠ sgn_t) (hg1 : i.val + 1 = j.val) :
    ∃ k : Fin (L + 1), k.val = i.val + 1 ∧
      (cancelSplit L K s t).1.bias = Bias.dyadic sgn_s k := by
  unfold cancelSplit
  rw [hs, ht]
  have hineq : ¬ (i.val = j.val) := by omega
  simp only [if_pos hne, dif_neg hineq, dif_pos hg1]
  exact ⟨⟨i.val + 1, by have hj : j.val < L + 1 := j.2; omega⟩, rfl, rfl⟩

/-- **Survival-band predicate (band-position fact, C-side).**  At Phase-8 entry, after the Phase-7
`cancelSplit` trajectory, every LIVE minority level `i` still has `≥ E` σ-opposite eliminators
strictly above it.  Provenance: B delivers the Phase-7-ENTRY above-level eliminator margins; the
Phase-7 trajectory only SPENDS eliminators on same-level cancels (`cancelSplit` same-level branch),
each charged to one minority drained (gap-1/gap-2 preserve or grow the σ-opposite supply per
`cancelSplit_gap1_preserves_smaller_sign` and the gap-2 sign-takeover above).  So the surviving
above-level supply stays `≥ E`.  `Phase8Convergence.elimAbove σ i` is the non-`full` σ-opposite
mass strictly above `i`. -/
def SurvivalBandAbove (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : Fin (L + 1),
    1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count →
    E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count

/-- **C-localization (deterministic survival bookkeeping).**  The survival-band predicate IS
`MarginLedgers.Phase7SurvivalUpperBounds` (definitionally — both quantify the same per-level
`elimAbove ≥ E` over live `minorityAt` levels).  This makes explicit that the C residual is the
honest deterministic survival band, not a new stochastic tail. -/
theorem phase7SurvivalUpperBounds_of_survivalBand {σ : Sign} {E : ℕ} {c : Config (AgentState L K)}
    (hSurv : SurvivalBandAbove (L := L) (K := K) σ E c) :
    MarginLedgers.Phase7SurvivalUpperBounds (L := L) (K := K) σ E c :=
  hSurv

/-- **C end-to-end (Phase-7-entry margins + survival band ⟹ `Phase7To8Structure`).**  Wires the
C-localization into the landed `MarginLedgers.phase7_to_phase8_eliminator_margin_of_phase7`:
`hStart` is B's Phase-7-entry margin, `h7win` the Phase-7 all-Main window, and the survival band
supplies the carried `Phase7SurvivalUpperBounds` — yielding
`EliminatorMargins.Phase7To8Structure σ E c`. -/
theorem phase7_to_phase8_of_survivalBand {n E : ℕ} {σ : Sign} {c c_start : Config (AgentState L K)}
    (hStart : EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c_start)
    (h7win : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    (hSurv : SurvivalBandAbove (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5) :
    EliminatorMargins.Phase7To8Structure (L := L) (K := K) σ E c :=
  MarginLedgers.phase7_to_phase8_eliminator_margin_of_phase7 hStart h7win
    (phase7SurvivalUpperBounds_of_survivalBand hSurv) hE

/-! ## What Phase 6 (and Phase 7) must export — the precise named residual.

The band predicates above are deterministic GIVEN the band-position facts; the band-position facts
themselves are the residual that points at Phase 6's convergence proof.  Precisely:

**Phase-6 Post must export `Phase6BandPositionFacts σ E c`**, i.e. both:

1. `MinorityConfinedGap1 σ c` — every live minority level `j` has `j.val ≥ 1` (a gap-1 predecessor
   index exists).  Phase 6's high-mass drain (`highMass l → 0`, `Phase6Convergence`) separates the
   two bands by one step, so no live minority sits at the bottom index `0`.  This is a
   band-FLOOR fact: the drain leaves the eliminand band strictly above the absorbing floor.

2. `MajorityBandAtGap1 σ E c` — the gap-1 predecessor level `i = j − 1` carries `≥ E` σ-opposite
   eliminators (`= MarginLedgers.majorityAtExp σ i`, the per-level majority mass).  The GLOBAL
   `≥ 4n/15` budget is already proved (`majorityProfileMass_floor`); what the drain must additionally
   export is the PER-LEVEL ROUTING: that the `doSplit` magnitude-halving deposits the eliminators at
   the partner band one index below each minority, not at a useless exponent.

`phase6HighMassDrained_of_bandPosition` shows these two are definitionally exactly
`MarginLedgers.Phase6HighMassDrained` (the blueprint's B.1: `Phase6BandPositionFacts` is
definitionally the same as `Phase6HighMassDrained`).

**Phase-7 Post must export `SurvivalBandAbove σ E c`** — the surviving above-level eliminator LOWER
bound after the bounded same-level spend.  The landed `Invariants.lemma_7_5/7_6` are minority-survival
UPPER bounds, NOT eliminator-survival LOWER bounds; the gap-2 non-obstruction
(`cancelSplit_gap1_preserves_smaller_sign` + the gap-2 sign-takeover) means no new probability tail
is needed — only the deterministic per-level spend accounting that Phase-7's convergence proof must
carry through. -/

end BandLocalization

end ExactMajority
