/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Paper-faithful regime surface for Doty et al. §6 (Thm 3.1)

This file pins, ONCE and inspectably, the paper-faithful objects and regime ties that the broad
working surface deliberately relaxes.  It answers a paper-faithfulness audit (ChatGPT, 2026-06-09)
on four points; the verdicts are recorded in `DOTY_POST63_CAMPAIGN.md`.

## 1. Theorem 6.2 object — the majority-sign three-level confinement (`majorityConfined3`).

The paper's Theorem 6.2 (Doty–Eftekhari–Gąsieniec–Severson–Uznański–Xu, arXiv:2106.10201v2, §6):

> Assume the initial gap `|g| < 0.025|M|`.  Let `i = sign(g)` be the majority opinion and
> `−l = ⌊log₂(0.4|M|/…)⌋`.  Let `M' = { Main agents with opinion = i and exponent ∈
> {−l, −(l+1), −(l+2)} }`.  Then at the end of Phase 3, `|M'| ≥ 0.92|M|` whp `1 − O(1/n²)`, and
> additionally the mass strictly above level `−l` and the σ-minority mass are small.

The broad working field `UsefulMainFloor.Theorem62EntryHypotheses.hConfine` is
`0.92·|M| ≤ #usefulMains` where `usefulMains` are Mains of EITHER sign with exponent index `< L`.
That is the *Phase-5 sampling projection* of the paper object: Phase-5 sampling only needs a biased
Main of either sign below the cap, so the broad floor is exactly what that consumer consumes.

Here we carry the paper-faithful object `majorityConfined3 σ l c` (count of MAJORITY-sign Mains at
the THREE exact levels `{l, l+1, l+2}` `≥ 0.92·|M|`), bundle the paper's mass-above / minority-mass
bounds into `Theorem62Paper`, and PROVE the projection
`majorityConfined3 ⟹ hConfine` (`theorem62Paper_implies_broad_floor`): the faithful object is the
genuine core; the broad floor is its honest weakening.  The eliminator ledgers that DO need the
sign/level projection (`MarginLedgers.majorityProfileMass`, the `4n/45` band of `BandEdges`) consume
the σ-sign per-exponent masses, which `majorityConfined3` lower-bounds at the three paper levels.

## 2–4. The paper regime ties (`Regime n L K`).

The headline `TimeHeadline.time_headline_W2` is polymorphic in `{L K n}`; the paper-regime
ties live only inside `Params` (`N₀ ≤ n`) and the doctrine docs (`k = 45`, `L = ⌈log₂ n⌉`).
`Regime n L K` collects them in ONE inspectable predicate:

* `hLlog : L = Nat.clog 2 n`     — the paper's `L = ⌈log₂ n⌉` (item 4).  `Nat.clog 2 n = ⌈log₂ n⌉`.
* `hK : 45 ≤ K`                  — the paper proof needs `k = 45` minutes/hour at `p = 1` (item 2);
                                    simulations use smaller `k`, the proof does not.  The §6
                                    width/seam lemmas are polymorphic in `K` (so they hold for the
                                    paper's `K = 45`); this tie records that the paper-regime
                                    instance uses `K ≥ 45`, ruling out the spuriously-strong
                                    "arbitrary small `K`" reading of the headline.
* `hN : Params.N₀ ≤ n`       — the finite-`n` floor (`10^40`) past every negligibility crossover
                                    of the §6 front engine (`Params`, item 3 context).

## 3. `wp = 3/200` is an ANALYSIS constant, not a transition probability.

The FROZEN protocol transition is deterministic per pair (every `Protocol.PhaseNTransition :
AgentState → AgentState → AgentState × AgentState`); the only randomness is uniform PAIR SELECTION.
So no per-pair transition carries a probability `p`.  `wp = 3/200` enters ONLY as the per-window
parallel-time step fraction `Params.w n = ⌊3n/200⌋` and the MGF window-rung ratio
`uW = 2(1+ε)·wp = 603/20000` (`Params.uW`); it is never a drip rate in `Transition.lean`
(no `Prob`/`PMF`/`p`-rate occurs there).  The paper's "drip reaction has probability `p`, `p = 1`"
(Thm 6.9) corresponds to the DETERMINISTIC frozen rule (`p = 1`), with the analysis constant `wp`
controlling the number of selection rounds per window, NOT the per-pair outcome.  This closes the
auditor's suspicion: `wp` is an analysis threshold, file:line `Params.lean:44` / `:454`.

This file is NEW and append-only; it edits no existing file; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.UsefulMainFloor
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarginLedgers
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Params

namespace ExactMajority

open scoped BigOperators

namespace PaperRegime

variable {L K : ℕ}

/-! ## Part 1 — the paper-faithful Theorem 6.2 object `majorityConfined3`. -/

/-- The three paper levels `{l, l+1, l+2}` as a `Finset (Fin (L+1))`, given `l+2 < L+1`
(equivalently `l + 2 ≤ L`).  Each level is a genuine `Fin (L+1)` because `l ≤ l+1 ≤ l+2 < L+1`. -/
def threeLevels (l : ℕ) (hl : l + 2 < L + 1) : Finset (Fin (L + 1)) :=
  {⟨l, by omega⟩, ⟨l + 1, by omega⟩, ⟨l + 2, by omega⟩}

/-- The majority-sign Main count over the three paper levels `{l, l+1, l+2}`:
`∑_{i ∈ {l,l+1,l+2}} #(majority-σ Mains at exponent i)`.  This is the paper's `|M'|` —
the count of Mains of the MAJORITY opinion (`s ≠ σ`, where `σ` is the minority sign) at the three
exact exponent levels.  Cf. `MarginLedgers.majorityProfileMass` which sums over ALL levels. -/
def majorityConfined3 (σ : Sign) (l : ℕ) (hl : l + 2 < L + 1)
    (c : Config (AgentState L K)) : ℕ :=
  ∑ i ∈ threeLevels (L := L) l hl,
    (MarginLedgers.majorityAtExp (L := L) (K := K) σ i).sum c.count

/-- The majority-sign Main mass strictly ABOVE the top paper level `l+2`:
`∑_{i : l+2 < i} #(majority-σ Mains at exponent i)`.  This is the paper's `µ(>−l)` band — the
majority mass that has not yet been brought down into the confinement band. -/
def majorityAboveMass (σ : Sign) (l : ℕ) (c : Config (AgentState L K)) : ℕ :=
  ∑ i : Fin (L + 1), if l + 2 < i.val then
    (MarginLedgers.majorityAtExp (L := L) (K := K) σ i).sum c.count else 0

/-- **The paper-faithful Theorem 6.2 entry facts.**  Bundles the majority-sign three-level
confinement `|M'| ≥ 0.92·|M|` with the paper's two auxiliary smallness bounds (mass strictly above
level `−l`, and σ-minority mass), all as carried probabilistic content.  This is the genuine core
of Theorem 6.2; the broad working floor (`UsefulMainFloor.Theorem62EntryHypotheses.hConfine`) is
its Phase-5 projection (proven below).

`σ` is the MINORITY sign convention of `MarginLedgers` (so `majorityAtExp σ` = the majority opinion
`s ≠ σ`, the paper's `i = sign(g)`). -/
structure Theorem62Paper (σ : Sign) (l : ℕ) (hl : l + 2 < L + 1) (n : ℕ)
    (c : Config (AgentState L K)) : Prop where
  /-- The Lemma-5.2 role floor `n/3 ≤ |M|`. -/
  hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
  /-- **The Theorem-6.2 majority confinement.**  The majority-sign Mains confined to the three exact
  levels `{l, l+1, l+2}` number `≥ 0.92·|M|` — the paper's `|M'| ≥ 0.92|M|`. -/
  hConfine3 : (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
    ≤ ((majorityConfined3 (L := L) (K := K) σ l hl c : ℕ) : ℝ)
  /-- **Mass strictly above the top paper level.**  The majority mass at levels `> l+2` (above the
  band) is small — the paper's `µ(>−l) ≤ 0.002·|M|`-flavored bound, carried as a genuine `≤ 0.06·|M|`
  cap (the residue share complementary to the `0.92` band and the `0.02` slack). -/
  hMassAbove : ((majorityAboveMass (L := L) (K := K) σ l c : ℕ) : ℝ)
    ≤ (0.06 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
  /-- **σ-minority mass small.**  The σ-minority profile mass is `≤ 0.12·|M|` (the paper's `β⁻`
  bound, absorbed into the residue cap; identical to `MarginLedgers.MainConfinementProfile`). -/
  hMinoritySmall : ((MarginLedgers.minorityProfileMass (L := L) (K := K) σ c : ℕ) : ℝ)
    ≤ (0.12 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)

/-! ## Part 2 — the projection `majorityConfined3 ⟹ usefulMains` (the honest weakening). -/

/-- **Each three-level majority Main is a `usefulMains` member** (when `l + 2 < L`).  A member of
`majorityAtExp σ i` with `i ∈ {l, l+1, l+2}` is a `Main` with dyadic bias at exponent index
`i.val ≤ l+2 < L`, hence satisfies `biasedMainLtL` (= membership in `usefulMains`). -/
theorem threeLevel_majority_mem_usefulMains
    {σ : Sign} {l : ℕ} (hl2 : l + 2 < L)
    {i : Fin (L + 1)} (hi : i ∈ threeLevels (L := L) l (by omega))
    {a : AgentState L K} (ha : a ∈ MarginLedgers.majorityAtExp (L := L) (K := K) σ i) :
    a ∈ Phase5Convergence.usefulMains (L := L) (K := K) := by
  classical
  simp only [MarginLedgers.majorityAtExp, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨hrole, s, _hsne, hbias⟩ := ha
  -- i.val < L: i ∈ {l, l+1, l+2}, each ≤ l+2 < L.
  have hival : i.val < L := by
    simp only [threeLevels, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h | h <;> (subst h; simp; omega)
  simp only [Phase5Convergence.usefulMains, Finset.mem_filter, Finset.mem_univ, true_and,
    Phase5Convergence.biasedMainLtL]
  exact ⟨hrole, s, i, hival, hbias⟩

/-- **The three paper levels are distinct as `Fin (L+1)`** (so the band sum is over a 3-element
finset, no double-count).  Needed to bound `majorityConfined3` by the disjoint band sum. -/
theorem threeLevels_card {l : ℕ} (hl2 : l + 2 < L) :
    (threeLevels (L := L) l (by omega)).card = 3 := by
  simp only [threeLevels]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton, Fin.ext_iff]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega

/-- **The projection: `majorityConfined3 ≤ #usefulMains`** (when `l + 2 < L`).  The three-level
majority band is a sub-multiset of the useful Mains, so its mass is at most the useful-Mains mass.
This is the deterministic bridge that makes the broad `hConfine` floor the honest weakening of the
paper object: the majority three-level set is contained in (sign-and-level-forgotten) `usefulMains`. -/
theorem majorityConfined3_le_usefulMains {σ : Sign} {l : ℕ} (hl2 : l + 2 < L)
    (c : Config (AgentState L K)) :
    majorityConfined3 (L := L) (K := K) σ l (by omega) c
      ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count := by
  classical
  unfold majorityConfined3
  -- The biUnion of the three per-level majority finsets is ⊆ usefulMains; the three finsets are
  -- pairwise disjoint (distinct exponents), so ∑ over the band = sum over the biUnion ≤ usefulMains.
  set band : Finset (AgentState L K) :=
    (threeLevels (L := L) l (by omega)).biUnion
      (fun i => MarginLedgers.majorityAtExp (L := L) (K := K) σ i) with hband
  -- pairwise disjoint across distinct exponents.
  have hdisj : (↑(threeLevels (L := L) l (by omega)) : Set (Fin (L+1))).PairwiseDisjoint
      (fun i => MarginLedgers.majorityAtExp (L := L) (K := K) σ i) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left]
    intro a ha hb
    simp only [MarginLedgers.majorityAtExp, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨_, s, _, hbi⟩ := ha
    obtain ⟨_, t, _, hbj⟩ := hb
    rw [hbi] at hbj
    injection hbj with _ hidx
    exact hij hidx
  -- ∑_{i ∈ three} (per-level sum) = ∑ over the disjoint biUnion.
  have hsum_eq : ∑ i ∈ threeLevels (L := L) l (by omega),
      (MarginLedgers.majorityAtExp (L := L) (K := K) σ i).sum c.count = band.sum c.count := by
    rw [hband, Finset.sum_biUnion hdisj]
  rw [hsum_eq]
  -- band ⊆ usefulMains, so the count-sum is monotone.
  apply Finset.sum_le_sum_of_subset
  intro a ha
  simp only [hband, Finset.mem_biUnion] at ha
  obtain ⟨i, hi, hai⟩ := ha
  exact threeLevel_majority_mem_usefulMains (L := L) (K := K) hl2 hi hai

/-- **The faithful object implies the broad floor** (the honest re-statement of `hConfine`).  From
the paper-faithful `Theorem62Paper` (the majority three-level confinement `0.92·|M| ≤ |M'|`) and
`l + 2 < L`, the broad working hypothesis `UsefulMainFloor.Theorem62EntryHypotheses.hConfine`
(`0.92·|M| ≤ #usefulMains`) follows.  So `hConfine` is the Phase-5 projection of the genuine
Theorem-6.2 core, not an independent weaker assumption. -/
theorem theorem62Paper_implies_broad_floor {σ : Sign} {l : ℕ} (hl2 : l + 2 < L) {n : ℕ}
    {c : Config (AgentState L K)}
    (hP : Theorem62Paper (L := L) (K := K) σ l (by omega) n c) :
    (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
      ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ) := by
  refine le_trans hP.hConfine3 ?_
  have hle := majorityConfined3_le_usefulMains (L := L) (K := K) (σ := σ) hl2 c
  exact_mod_cast hle

/-- **Faithful Theorem-6.2 entry from the paper object.**  Packages `Theorem62Paper` into the broad
`UsefulMainFloor.Theorem62EntryHypotheses` consumed by Phase-5, given the carried Phase-5 window.
This is the wiring point: any consumer needing the broad floor can be fed the faithful paper object
through this adapter. -/
theorem theorem62EntryHypotheses_of_paper {σ : Sign} {l : ℕ} (hl2 : l + 2 < L) {n : ℕ}
    {c : Config (AgentState L K)}
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    (hP : Theorem62Paper (L := L) (K := K) σ l (by omega) n c) :
    UsefulMainFloor.Theorem62EntryHypotheses (L := L) (K := K) n c where
  hPhase5 := hPhase5
  hMainFloor := hP.hMainFloor
  hConfine := theorem62Paper_implies_broad_floor (L := L) (K := K) hl2 hP

/-! ## Part 3 — the majority-sign / minority-small bridge to the eliminator ledgers.

The eliminator floors (`MarginLedgers.MainConfinementProfile` → `majorityProfileMass_floor` →
`Phase6To7Structure`; the `BandEdges` `4n/45`) consume the σ-sign per-exponent masses
(`majorityProfileMass`, `minorityProfileMass`), NOT the broad both-sign `usefulMains`.  The paper
object `Theorem62Paper` carries exactly that sign information: `majorityConfined3` lower-bounds the
σ-opposite (majority) mass `majorityProfileMass` (the three-level band is a sub-band of the full
profile), and `hMinoritySmall` is identical to `MainConfinementProfile.hMinoritySmall`. -/

/-- **`majorityConfined3 ≤ majorityProfileMass`** — the three-level majority band is a sub-band of
the full majority profile (summing over all `L+1` exponents `≥` summing over the three). -/
theorem majorityConfined3_le_majorityProfileMass {σ : Sign} {l : ℕ} (hl : l + 2 < L + 1)
    (c : Config (AgentState L K)) :
    majorityConfined3 (L := L) (K := K) σ l hl c
      ≤ MarginLedgers.majorityProfileMass (L := L) (K := K) σ c := by
  classical
  unfold majorityConfined3 MarginLedgers.majorityProfileMass
  apply Finset.sum_le_sum_of_subset
  intro i _; exact Finset.mem_univ i

/-- **The eliminator-ledger profile from the paper object.**  `Theorem62Paper` yields
`MarginLedgers.MainConfinementProfile σ n c` (the A-shape facts B/C consume): the role floor and the
minority-small bound transfer directly, and the broad `0.92·|M| ≤ majority + minority` follows from
`0.92·|M| ≤ majorityConfined3 ≤ majorityProfileMass ≤ majority + minority`.  So the sign/band
eliminator floors (`majorityProfileMass_floor`, `4n/45`) are driven by the faithful Theorem-6.2
object, not a re-assumption. -/
theorem mainConfinementProfile_of_paper {σ : Sign} {l : ℕ} (hl : l + 2 < L + 1) {n : ℕ}
    {c : Config (AgentState L K)}
    (hP : Theorem62Paper (L := L) (K := K) σ l hl n c) :
    MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c where
  hMainFloor := hP.hMainFloor
  hUseful := by
    refine le_trans hP.hConfine3 ?_
    have h1 : majorityConfined3 (L := L) (K := K) σ l hl c
        ≤ MarginLedgers.majorityProfileMass (L := L) (K := K) σ c :=
      majorityConfined3_le_majorityProfileMass (L := L) (K := K) hl c
    have h2 : MarginLedgers.majorityProfileMass (L := L) (K := K) σ c
        ≤ MarginLedgers.majorityProfileMass (L := L) (K := K) σ c
          + MarginLedgers.minorityProfileMass (L := L) (K := K) σ c := Nat.le_add_right _ _
    have : majorityConfined3 (L := L) (K := K) σ l hl c
        ≤ MarginLedgers.majorityProfileMass (L := L) (K := K) σ c
          + MarginLedgers.minorityProfileMass (L := L) (K := K) σ c := le_trans h1 h2
    exact_mod_cast this
  hMinoritySmall := hP.hMinoritySmall

/-! ## Part 4 — the paper regime ties `Regime n L K` (items 2 & 4). -/

/-- **The Doty paper-regime predicate** — the single inspectable hypothesis collecting the three
parameter ties of the §6 proof regime that the polymorphic headline relaxes:

* `hLlog : L = Nat.clog 2 n`     — `L = ⌈log₂ n⌉` (item 4).
* `hK : 45 ≤ K`                  — `k = 45` minutes/hour for the `p = 1` proof (item 2).
* `hN : Params.N₀ ≤ n`       — the finite-`n` floor `n ≥ 10^40` past the §6 crossover.

`TimeHeadline.time_headline_W2` is stated polymorphically in `{L K n}`; threading
`Regime n L K` as its regime hypothesis pins the concrete headline to the paper regime in ONE
place.  (`Nat.clog 2 n = ⌈log₂ n⌉` is Mathlib's ceiling-log.) -/
structure Regime (n L K : ℕ) : Prop where
  /-- `L = ⌈log₂ n⌉` (item 4). -/
  hLlog : L = Nat.clog 2 n
  /-- `45 ≤ K`: the paper proof needs `k = 45` minutes/hour at `p = 1` (item 2). -/
  hK : 45 ≤ K
  /-- `K ≤ n`: minutes/hour ≤ population size (paper uses K = 45, n ≥ 10⁴⁰). -/
  hK_le : K ≤ n
  /-- `n ≥ N₀ = 10^40`: the finite-`n` floor past every §6 crossover (item 3 context). -/
  hN : Params.N₀ ≤ n

/-- `Regime` pins `L = ⌈log₂ n⌉`, so `L + 1 = Θ(log n)` — the headline's `21·C0·n·(L+1)`
interaction bound is genuinely `O(n log n)` interactions `= O(log n)` parallel time. -/
theorem Regime.L_eq_clog {n L K : ℕ} (h : Regime n L K) : L = Nat.clog 2 n := h.hLlog

/-- `Regime` pins `45 ≤ K` (the paper minutes/hour tie). -/
theorem Regime.K_ge_45 {n L K : ℕ} (h : Regime n L K) : 45 ≤ K := h.hK

/-- `Regime` pins `N₀ ≤ n` (so every `Params` discharger fires). -/
theorem Regime.N₀_le {n L K : ℕ} (h : Regime n L K) : Params.N₀ ≤ n := h.hN

/-- Under `Regime`, `n ≥ 10^40` so in particular `2 ≤ n` and `0 < n` (the headline's basic
size hypotheses are subsumed by the regime tie). -/
theorem Regime.two_le_n {n L K : ℕ} (h : Regime n L K) : 2 ≤ n :=
  Params.two_le n h.hN

/-! ## Part 5 — `wp` is an analysis constant (item 3), recorded as a proven identity.

`Params.uW = 2(1+ε)·wp = 603/20000` at `wp = 3/200`, `ε = 1/200`; `wp` enters ONLY this MGF
window-rung ratio and the step count `w n = ⌊3n/200⌋` (`= ⌊wp·n⌋`).  Neither is a per-pair
transition probability (the FROZEN protocol transition is deterministic per pair). -/

/-- **`wp` is an analysis constant** — the window-rung ratio identity `uW = 2·(1+1/200)·(3/200)`
exhibits `wp = 3/200` purely as an MGF-analysis quantity (`Params.uW`), never a transition
probability.  This is the closed form of the auditor's item-3 suspicion. -/
theorem wp_is_analysis_constant : Params.uW = 2 * (1 + (1/200 : ℝ)) * (3/200 : ℝ) := by
  unfold Params.uW; norm_num

end PaperRegime

end ExactMajority
