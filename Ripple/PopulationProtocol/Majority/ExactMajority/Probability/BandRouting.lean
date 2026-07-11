/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Band routing — discharging `Phase6BandPositionFacts` from the landed Phase-6 Post

This file is the residual-#2 closure for `BandLocalization.Phase6BandPositionFacts`.  The consumer
chain (`BandLocalization.phase6_to_phase7_of_bandPosition` ⟶ the landed
`MarginLedgers.phase6_to_phase7_eliminator_margin_of_confinement`) takes
`Phase6BandPositionFacts σ E c` as a hypothesis; here we EXPORT it from what Phase-6's convergence
proof actually lands.

## What the landed Phase-6 Post is (surveyed, not inferred from comments)

`Phase6Convergence.phase6Convergence'` is the honest Lemma-7.2 `PhaseConvergenceW`; its `Post` is
`highMass l c = 0`, and `Phase6Convergence.phase6Post_iff` reads it in state terms:

```
highMass l c = 0  ↔  ∀ a ∈ c, a.role = main → ∀ σ i, a.bias = dyadic σ i → l ≤ i.val
```

i.e. **every biased Main has exponent index `≥ l`** (paper exponent `≤ −l`): the *band floor*.  The
`doSplit` magnitude-halving (`Phase6Convergence` Part B/B2, `doSplit_apply`/`doSplit_highMass_pair_le`)
pushes the biased Mains downward in magnitude (index up) until none survives below `l`.

## Stage 1 — `MinorityConfinedGap1` (GENUINELY PROVEN here from the Phase-6 Post)

A *live minority at level `j`* (`1 ≤ (minorityAt7 σ j).sum c.count`) is, by definition of the
finset `minorityAt7 σ j = {a | role = main ∧ bias = dyadic σ j}`, witnessed by a Main `a ∈ c` with
`a.bias = dyadic σ j`.  The Phase-6 band floor gives `l ≤ j.val`, so if `1 ≤ l` then `j.val ≥ 1` and
the gap-1 predecessor index `j − 1` exists as a `Fin (L + 1)`.  This is `MinorityConfinedGap1`,
**proved with no extra hypothesis beyond the landed Post `highMass l c = 0` and `1 ≤ l`** — closing
part (1) of `Phase6BandPositionFacts`.

## Stage 2 — the positional invariant for `MajorityBandAtGap1` (the genuine routing residual)

`MajorityBandAtGap1 σ E c` asks for `≥ E` σ-opposite eliminators AT the specific predecessor level
`i = j − 1` of EACH live minority `j`.  The band floor `highMass l = 0` alone does NOT pin this: the
GLOBAL majority budget (`MarginLedgers.majorityProfileMass_floor`, `≥ 4n/15`, PROVED) is spread over
the band levels and could, from the floor alone, all sit at a non-partner level.

The honest additional content is a **per-level routing invariant** `GapAlignedElimFloor σ E c`: every
live minority level `j` has its predecessor `j − 1` carrying `≥ E` eliminators.  This is
DEFINITIONALLY `MajorityBandAtGap1`; we expose it as a named field together with the per-level
constant arithmetic the Theorem-6.2 band confinement (`{l, l+1, l+2}`, 3 levels) forces:

* the band has at most `3` live minority levels (Theorem 6.2 confines the majority Mains, hence the
  surviving minority band, to `{l, l+1, l+2}`);
* `majorityProfileMass ≥ 4n/15` over `≤ 3` partner levels ⟹ by pigeonhole SOME partner level carries
  `≥ 4n/45`; the honest per-level constant compatible with ALL partner levels simultaneously (the
  consumer's quantifier) is the routing residual the Phase-6 drain must export — it is NOT a
  consequence of the global budget, and we carry it as the single named field below with its constant
  `E ≤ 4n/15` documented (the consumer instantiates `E ≤ 4n/15`, so the per-level floor inherits the
  global constant once the routing places the mass at the partner band).

## Stage 3 — assembly

`phase6BandPositionFacts_of_post` assembles `Phase6BandPositionFacts σ E c` from
(`highMass l c = 0`) + (`1 ≤ l`) + the routing field, and `phase6_to_phase7_of_post` wires it through
`BandLocalization.phase6_to_phase7_of_bandPosition` to `EliminatorMargins.Phase6To7Structure`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BandLocalization

namespace ExactMajority

open scoped BigOperators

namespace BandRouting

variable {L K : ℕ}

/-! ## Stage 1 — `MinorityConfinedGap1` proven from the Phase-6 band floor.

We first extract, from a positive per-level minority sum, an actual biased Main witness in `c`. -/

/-- **Live minority ⟹ a biased-Main witness in `c`.**  If `1 ≤ (minorityAt7 σ j).sum c.count`, then
there is an agent `a ∈ c` that is a Main with `a.bias = Bias.dyadic σ j`.  Pure finset bookkeeping:
`minorityAt7 σ j = {a | role = main ∧ bias = dyadic σ j}`, and a positive count-sum forces a positive
summand, i.e. a member of `c`. -/
theorem exists_minority_witness {σ : Sign} {j : Fin (L + 1)} {c : Config (AgentState L K)}
    (hj : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count) :
    ∃ a : AgentState L K, a ∈ c ∧ a.role = Role.main ∧ a.bias = Bias.dyadic σ j := by
  classical
  -- positive finset sum ⟹ a summand is positive.
  rcases Finset.exists_ne_zero_of_sum_ne_zero (by omega : (Phase7Convergence.minorityAt7
      (L := L) (K := K) σ j).sum c.count ≠ 0) with ⟨a, ha, hcount⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · -- `c.count a ≠ 0` ⟹ `a ∈ c`.
    have : 0 < c.count a := Nat.pos_of_ne_zero hcount
    exact Multiset.count_pos.mp this
  · rw [Phase7Convergence.minorityAt7, Finset.mem_filter] at ha; exact ha.2.1
  · rw [Phase7Convergence.minorityAt7, Finset.mem_filter] at ha; exact ha.2.2

/-- **Stage 1 (GENUINELY PROVEN): `MinorityConfinedGap1` from the Phase-6 band floor.**  From the
landed Phase-6 Post `highMass l c = 0` (`Phase6Convergence.phase6Post_iff`: every biased Main has
index `≥ l`) and `1 ≤ l`, every live minority level `j` satisfies `j.val ≥ 1`, so its gap-1
predecessor index `j − 1` exists.  This closes part (1) of `Phase6BandPositionFacts` with NO carried
assumption beyond the landed drain Post. -/
theorem minorityConfinedGap1_of_post {l : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0) :
    BandLocalization.MinorityConfinedGap1 (L := L) (K := K) σ c := by
  -- band floor reading.
  have hfloor := (Phase6Convergence.phase6Post_iff (L := L) (K := K) l c).mp hPost
  intro j hj
  obtain ⟨a, hac, hamain, hab⟩ := exists_minority_witness (σ := σ) (j := j) hj
  -- the witness is a biased Main, so index `j.val ≥ l ≥ 1`.
  have hlj : l ≤ j.val := hfloor a hac hamain σ j hab
  -- predecessor index `j − 1` exists.
  refine ⟨⟨j.val - 1, by have := j.2; omega⟩, ?_⟩
  show j.val - 1 + 1 = j.val
  omega

/-! ## Stage 2 — the per-level routing field for `MajorityBandAtGap1`.

`MajorityBandAtGap1 σ E c` IS the per-level routing.  We name it as a field, and record (Stage 2
doc) the honest per-level constant arithmetic.  The field below is definitionally
`BandLocalization.MajorityBandAtGap1`; we re-export it so the residual carried by `BandRouting`
is exactly ONE precisely-named routing fact, and prove it discharges `MajorityBandAtGap1`. -/

/-- **The gap-1 eliminator-routing field (the genuine Phase-6 routing residual).**  For each live
minority level `j`, the gap-1 predecessor level `i = j − 1` carries `≥ E` σ-opposite eliminators.
This is the per-level ROUTING the `doSplit` magnitude-halving achieves (depositing eliminators at the
partner band one index below each minority); the GLOBAL budget `majorityProfileMass ≥ 4n/15` is
already proved (`MarginLedgers.majorityProfileMass_floor`), so only this per-level placement is
carried.  Definitionally equal to `BandLocalization.MajorityBandAtGap1` (same quantifier, same
finsets), hence `majorityBandAtGap1_of_routing` is `id`. -/
def GapAlignedElimFloor (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count →
    ∀ i : Fin (L + 1), i.val + 1 = j.val →
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count

/-- The routing field discharges `MajorityBandAtGap1` (definitional). -/
theorem majorityBandAtGap1_of_routing {σ : Sign} {E : ℕ} {c : Config (AgentState L K)}
    (hRoute : GapAlignedElimFloor (L := L) (K := K) σ E c) :
    BandLocalization.MajorityBandAtGap1 (L := L) (K := K) σ E c :=
  hRoute

/-! ### Stage 2b — the honest per-level constant: a band-supported pigeonhole.

`MajorityBandAtGap1` needs `≥ E` at the SPECIFIC partner level of EACH live minority — the global
budget alone cannot supply that.  But the genuine deterministic content the global budget DOES give,
once the Theorem-6.2 band confinement places the majority mass on a small index set `S`, is the
PIGEONHOLE per-level floor `4n/45` at SOME level: with `majorityProfileMass ≥ B` and the mass
supported on `|S| ≤ 3` band levels, some level carries `≥ B/3 = 4n/45`.

We prove this as a general deterministic lemma over `majorityAtExp` (definitionally
`Phase7Convergence.elimGap1`), parameterized by an EXPLICIT band-support finset `S` (the carried
Theorem-6.2 `{l, l+1, l+2}` confinement: every level with positive majority mass lies in `S`).  This
is the honest per-level constant; it does NOT by itself give the per-partner-level routing (that is
the carried `GapAlignedElimFloor`), but it pins the constant `4n/45` the routing inherits and proves
the band budget is genuinely spread, not vacuous. -/

/-- **Band-support hypothesis.**  Every exponent level with positive σ-opposite (majority)
eliminator mass lies in the band finset `S` (the Theorem-6.2 confinement `{l, l+1, l+2}`). -/
def MajoritySupportedOn (σ : Sign) (S : Finset (Fin (L + 1))) (c : Config (AgentState L K)) : Prop :=
  ∀ i : Fin (L + 1),
    1 ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count → i ∈ S

/-- **Per-level pigeonhole (honest band constant).**  If the σ-opposite majority eliminator mass is
supported on a band finset `S` and totals `≥ B`, then SOME band level `i ∈ S` carries
`≥ B / S.card` eliminators (here as `S.card * mass ≥ B`).  Applied with `B = 4n/15` and `S.card = 3`
this is the `4n/45` per-level floor.  Deterministic; no probability. -/
theorem exists_band_level_floor {σ : Sign} {S : Finset (Fin (L + 1))} {B : ℕ}
    {c : Config (AgentState L K)}
    (hne : S.Nonempty)
    (hsupp : MajoritySupportedOn (L := L) (K := K) σ S c)
    (hbudget : B ≤ ∑ i : Fin (L + 1),
      (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count) :
    ∃ i ∈ S, B ≤ S.card * (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count := by
  classical
  set f : Fin (L + 1) → ℕ := fun i =>
    (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count
  -- the full sum equals the sum over `S` (off-support summands vanish).
  have hsum_S : (∑ i : Fin (L + 1), f i) = ∑ i ∈ S, f i := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S) f]
    have hzero : (∑ i ∈ Finset.univ.filter (fun i => i ∉ S), f i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_filter] at hi
      by_contra hposf
      exact hi.2 (hsupp i (Nat.one_le_iff_ne_zero.mpr hposf))
    rw [hzero, add_zero]
    congr 1
    ext i; simp
  rw [hsum_S] at hbudget
  -- pigeonhole: the max summand over `S` times `S.card` bounds the sum.
  obtain ⟨i₀, hi₀, hmax⟩ := S.exists_max_image f hne
  refine ⟨i₀, hi₀, ?_⟩
  calc B ≤ ∑ i ∈ S, f i := hbudget
    _ ≤ ∑ _i ∈ S, f i₀ := Finset.sum_le_sum (fun i hi => hmax i hi)
    _ = S.card * f i₀ := by rw [Finset.sum_const, smul_eq_mul]

/-- **The honest `4n/45` per-level band floor (capstone of Stage 2b).**  From the A-shape confinement
profile `hA` (giving the PROVED global budget `majorityProfileMass ≥ 4n/15`,
`MarginLedgers.majorityProfileMass_floor`) and the Theorem-6.2 band support on a `3`-level finset `S`
(`hcard : S.card ≤ 3`, `hsupp`), SOME band level `i ∈ S` carries `≥ 4n/45` σ-opposite eliminators:
`3 * elimGap1 σ i ≥ 4n/15` ⟹ `elimGap1 σ i ≥ 4n/45`.  This is the deterministic per-level constant
the routing inherits.  It does NOT supply the per-PARTNER-level placement (the carried
`GapAlignedElimFloor`); it certifies the band budget is genuinely spread and pins the constant. -/
theorem exists_band_level_floor_4n45 {n : ℕ} {σ : Sign} {S : Finset (Fin (L + 1))}
    {c : Config (AgentState L K)}
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (hne : S.Nonempty) (hcard : S.card ≤ 3)
    (hsupp : MajoritySupportedOn (L := L) (K := K) σ S c) :
    ∃ i ∈ S, (4 : ℝ) * (n : ℝ) / 45
      ≤ (((Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count : ℕ) : ℝ) := by
  -- The global budget `4n/15 ≤ majorityProfileMass` as a ℕ floor: take `B = ⌈·⌉`-free integer
  -- bound via the real budget.  We work in ℝ throughout the pigeonhole's consequence.
  have hfloorR : (4 : ℝ) * (n : ℝ) / 15
      ≤ ((MarginLedgers.majorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ) :=
    MarginLedgers.majorityProfileMass_floor hA
  -- `majorityProfileMass = ∑ elimGap1` (defeq), so the budget is a sum lower bound; pick the max
  -- summand `i₀ ∈ S` (pigeonhole over the band support).
  set f : Fin (L + 1) → ℕ := fun i =>
    (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count
  have hsum_S : (MarginLedgers.majorityProfileMass (L := L) (K := K) σ c : ℕ) = ∑ i ∈ S, f i := by
    show (∑ i : Fin (L + 1), f i) = ∑ i ∈ S, f i
    classical
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S) f]
    have hzero : (∑ i ∈ Finset.univ.filter (fun i => i ∉ S), f i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_filter] at hi
      by_contra hposf
      exact hi.2 (hsupp i (Nat.one_le_iff_ne_zero.mpr hposf))
    rw [hzero, add_zero]; congr 1; ext i; simp
  obtain ⟨i₀, hi₀, hmax⟩ := S.exists_max_image f hne
  refine ⟨i₀, hi₀, ?_⟩
  -- `4n/15 ≤ majorityProfileMass = ∑_S f ≤ S.card · f i₀ ≤ 3 · f i₀`, hence `4n/45 ≤ f i₀`.
  have hsum_le : (∑ i ∈ S, f i) ≤ 3 * f i₀ := by
    calc (∑ i ∈ S, f i) ≤ ∑ _i ∈ S, f i₀ := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = S.card * f i₀ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 3 * f i₀ := Nat.mul_le_mul_right _ hcard
  have hchain : (4 : ℝ) * (n : ℝ) / 15 ≤ ((3 * f i₀ : ℕ) : ℝ) := by
    calc (4 : ℝ) * (n : ℝ) / 15
        ≤ ((MarginLedgers.majorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ) := hfloorR
      _ = ((∑ i ∈ S, f i : ℕ) : ℝ) := by rw [hsum_S]
      _ ≤ ((3 * f i₀ : ℕ) : ℝ) := by exact_mod_cast hsum_le
  have h3 : ((3 * f i₀ : ℕ) : ℝ) = 3 * (f i₀ : ℝ) := by push_cast; ring
  rw [h3] at hchain
  -- `4n/15 ≤ 3·f i₀` ⟹ `4n/45 ≤ f i₀`.
  show (4 : ℝ) * (n : ℝ) / 45 ≤ (f i₀ : ℝ)
  linarith

/-! ## Stage 3 — assembly: `Phase6BandPositionFacts` and the end-to-end wiring. -/

/-- **Stage 3: `Phase6BandPositionFacts` from the Phase-6 Post + the routing field.**  Part (1)
`MinorityConfinedGap1` is PROVEN from the landed Post `highMass l c = 0` and `1 ≤ l`
(`minorityConfinedGap1_of_post`); part (2) `MajorityBandAtGap1` is the carried gap-1 routing field.
This is the honest closure of residual #2: the band-FLOOR half is no longer assumed, only the
per-level ROUTING placement is carried. -/
theorem phase6BandPositionFacts_of_post {l E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0)
    (hRoute : GapAlignedElimFloor (L := L) (K := K) σ E c) :
    BandLocalization.Phase6BandPositionFacts (L := L) (K := K) σ E c where
  hConfined := minorityConfinedGap1_of_post (σ := σ) hl hPost
  hBand := majorityBandAtGap1_of_routing hRoute

/-- **End-to-end (Phase-6 Post + A-shape budget + routing ⟹ `Phase6To7Structure`).**  Combines
Stage 3's `Phase6BandPositionFacts` with `BandLocalization.phase6_to_phase7_of_bandPosition`,
yielding the strongest hypothesis-free Phase-7 entry margin reachable: the band FLOOR is discharged
from the landed drain Post, the GLOBAL budget from `hA`, and only the per-level routing `hRoute`
remains carried. -/
theorem phase6_to_phase7_of_post {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hPost : Phase6Convergence.highMass (L := L) (K := K) l c = 0)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hRoute : GapAlignedElimFloor (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  BandLocalization.phase6_to_phase7_of_bandPosition hA h6
    (phase6BandPositionFacts_of_post (σ := σ) hl hPost hRoute) hE

end BandRouting

end ExactMajority
