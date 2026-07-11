# HANDOFF: four floors (family3 letter, task c954c370, 2026-06-10)

Source: ChatGPT Pro (family3, Ripple connector). 16,998 B via network. Verbatim below.

---

## STATUS (2026-06-10, post-delivery)

- **Phase-5 Theorem-6.2 useful-Main floor** — DELIVERED (see `DOTY_POST63_CAMPAIGN.md`
  "Theorem 6.2 useful-Main floor" section). Structure `Theorem62EntryHypotheses` carries the
  `0.92·|M|` confinement; headline + wiring landed.
- **Phase-7/8 eliminator-margin floor package** — DELIVERED in NEW `Probability/EliminatorMargins.lean`
  (0-sorry, axioms ⊆ [propext, Classical.choice, Quot.sound]). Full record in
  `DOTY_POST63_CAMPAIGN.md` "Phase-7/8 eliminator-margin floor package" section. Summary:
  - Deterministic adapters (priority 1) — CLOSED: `exists_minorityAt_of_minorityU_pos`,
    `exists_minorityAt7_of_minorityU_pos`, `exists_minorityAt7_of_classMassN_pos` (mass form),
    `phase1_pullPos_floor_of_mainCount_and_saturated_bound`.
  - §3 `lemma7_4_phase7_elimGap1_floor` + §4 `lemma7_6_phase8_elimAbove_floor` — minority-witness
    half PROVED from landed potentials (`classMassN` / `minorityU` witness extraction); the
    eliminator-count LOWER bound is carried as honest named fields of `Phase6To7Structure` /
    `Phase7To8Structure` (the blueprint's placeholders, now concrete predicates). The landed
    `Invariants.lemma_7_5/7_6` are survival UPPER bounds and do NOT export these counts (verified).
  - §3/§4 wirings `phase7_hdrop_wired_from_lemma7_4` / `phase8_hdrop_wired_from_lemma7_6` — CLOSED.
    The Phase-7/8 drop rectangles were already landed, so no new transition-probability content was
    needed (confirms the blueprint "count-structure theorem, rectangle already landed").
- **Phase-1 saturated-side averaging floor** (§1) — DELIVERED in NEW
  `Probability/AveragingCollapse.lean` (0-sorry, axioms ⊆ [propext, Classical.choice, Quot.sound];
  single-file `lake env lean` EXIT_0). Full record in `DOTY_POST63_CAMPAIGN.md`
  "Phase-1 averaging collapse floor" section. Summary of the HONEST self-contained route taken
  (no [45] import): the FROZEN `avgFin7` rule contracts the SECOND MOMENT. The exact Fin-7 integer
  ledger (computed over all 49 pairs, both parities): centred at the encoding origin 3,
  `(x−3)²+(y−3)² − (x'−3)²−(y'−3)² = ⌊(x−y)²/2⌋ ≥ 0` (even: `(Δ)²/2`; odd: `((Δ)²−1)/2`). So
  `Φ = secondMomentN = Σ_{Mains}(smallBias.val−3)²` is **deterministically** non-increasing — the
  variance literally never rises, a per-step ℕ-monotone (NOT merely a supermartingale), plugging
  straight into the same `OneSidedCancel` level engine `extremeU` uses.
  - CLOSED (proven, axiom-clean): the exact per-rule ledger (`avgFin7_sqDist3_pair_le` /
    `avgFin7_sqDist3_pair_drop`, exhaustive `decide`); the config-kernel `PotNonincrOn` for
    `secondMomentN` (`potNonincrOn_secondMomentN`, mirroring `extremeU`); the EXACT saturated-count
    conversion `4·#saturatedPos ≤ secondMomentN` (`four_mul_saturatedPos_le_secondMoment` — a
    saturated value `≥ 5` is at squared distance `≥ 4` from origin 3, so the "what is the mean µ"
    design question dissolves: centring at the fixed origin needs no mean estimate); the whp level
    tail (`secondMoment_level_tail`); `mainCount = n` on the window; and the WIRED floor
    `phase1_pullPos_floor_whp` → `EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound`
    → `PhaseFloors.phase1_hdrop_wired`.
  - CARRIED (exactly one named quantitative input, paper provenance): the per-level second-moment
    drain rate `q : ℕ → ℝ≥0∞` (the `hdrop` hypothesis). This is the SAME atom
    `Phase1Convergence.phase1Convergence` carries for `extremeU` — the per-interaction probability
    that a distant pair averages strictly inward, the content the paper imports from reference [45]
    (Mocquard et al., Corollary 1). Exposed as a hypothesis exactly as Phases 1/7/8 expose theirs;
    everything structural around it is discharged.

- **Phase-1 averaging DRAIN RATE** (§1 residual #5 — the carried `q` atom) — DELIVERED in NEW
  `Probability/AveragingRate.lean` (0-sorry, axioms ⊆ [propext, Classical.choice, Quot.sound];
  single-file `lake env lean` EXIT_0; all 11 headlines audited). This discharges the structural
  content behind the `hdrop` slot `AveragingCollapse` carried — the rate is no longer free, it is
  the far × centre strict-drop rectangle, derived honestly from the FROZEN `avgFin7` rule (NO [45]
  import), via the SAME pair-counting the landed `extremeU` chain uses
  (`Phase7Convergence.drop_prob_of_rect`).
  - HONESTY TRAP resolved: a naive "`secondMomentN ≥ θ ⟹ gap-2 pair`" is FALSE — a config whose
    Mains all sit in a width-1 stall window `{a,a+1}` has zero per-step drop yet `secondMomentN` up
    to `9·|M|` (e.g. window `{0,1}`/`{5,6}`). The genuine escape is the **window `{2,3,4}`
    second-moment ceiling**: a Main with `val ∈ {2,3,4}` is at squared distance `≤ 1` from origin 3
    (`sqDist3N_le_one_of_not_far`, exhaustive `decide`), so NO far Main (`val ≤ 1` or `val ≥ 5`)
    ⟹ `secondMomentN ≤ |M| = n` (`secondMomentN_le_card_of_no_far`). Contrapositive (the structure
    lemma `farExists_of_secondMoment_gt_n`): `secondMomentN c > n ⟹ a far Main exists`, and every
    far Main has a gap-≥2 partner on the centre side.
  - STAGE 1 (sum invariant): `centredBiasSum c = Σ_{Mains}(smallBias.val − 3)` is `avgFin7`-conserved
    (`centredBiasSum_stepOrSelf_eq`, lifting `avgFin7_preserves_sum`); the honest entry predicate
    `SumPinned n c` (`|S₀| ≤ n`, true at entry since each Main encodes a ±1 opinion) is `K`-closed
    (`invClosed_sumPinned`). The sum invariant is what excludes the `{0,1}`/`{5,6}` stall windows
    (they force `|S₀| ≥ 2n`); the `{2,3,4}` ceiling is the per-step conversion mechanism.
  - STAGE 2/3 (rate): two strict-drop rectangles `farHighSet(val≥5) ×ˢ lowSet(val≤3)` and
    `farLowSet(val≤1) ×ˢ highSet(val≥3)` — each cell has `val`-gap `≥ 2` so drop `= ⌊gap²/2⌋ ≥ 2`
    (`avgFin7_sqDist3_pair_drop_high/_low`, exhaustive `decide`) — thread through `drop_prob_of_rect`
    (`secondMomentN_drop_prob_rect_high/_low`) to the per-level `hdrop`
    `secondMomentN_hdrop_of_struct_high/_low` at `q m = 1 − ofReal(P/(n(n−1)))`, P the partner margin.
  - STAGE 4 (wiring): `phase1_pullPos_floor_whp_of_struct` feeds the derived `q` into
    `AveragingCollapse.phase1_pullPos_floor_whp`; `hdrop_realizable_high` exhibits the rate as the
    concrete rectangle floor (constructive, not free).
  - TIME BUDGET (documented in file): consumer needs the floor at level `m = 4(n−P)+1`; level-tail
    gives failure `≤ (1 − P/(n(n−1)))^t`. With a **single far witness** (P=1) the rate is
    `1 − 1/(n(n−1))`, horizon `t = Θ(n²·log n)` for `O(1/n²)` failure (crude regime). With a
    **constant-fraction partner floor** (P=Θ(n), the carried centre-mass content [45] Cor.1 supplies)
    the rate is `1 − Θ(1/n)`, horizon `t = Θ(n·log n)` — paper-faithful Lemma 5.3. The partner floor
    `P` is the ONLY remaining carried atom (same status as the `extremeU` chain's `hpull`).

- **Phase-1 partner-margin Θ(n) FLOOR** (§1 residual — the carried `P'` atom of `AveragingRate`) —
  DELIVERED in NEW `Probability/PartnerMargin.lean` (0-sorry, axioms ⊆ [propext, Classical.choice,
  Quot.sound]; single-file build EXIT_0 on uisai2). This discharges the LAST carried atom of the
  §1 averaging chain: the partner margin `P` is no longer free — it is `(n − g + 3)/4 = Θ(n)`,
  derived HONESTLY from the conserved SUM INVARIANT of `AveragingRate` (no [45] import). With `P` now
  `Θ(n)`, the rate is the paper-faithful `q = 1 − Θ(1/n)` and the horizon is `Θ(n·log n)`.
  - THE BRIEFING-ERROR CAUGHT AND FIXED: the naive pigeonhole `#low < δn ⟹ S > n` does NOT close at
    `|S| ≤ n` — `S ≥ n − 4·#low ≤ n` gives NO contradiction. The honest fix is the SHARPER entry sum
    bound `|S| ≤ g` (`g = εn`, the initial opinion gap; each Main encodes ±1 so `S = #plus − #minus
    = gap`, conserved by `avgFin7`). THEN `n − g ≤ 4·#low` closes (division-free, in ℤ).
  - STAGE A (`EntrySumPinned n g c` := `Phase1AllMain ∧ |centredBiasSum| ≤ g`): refines
    `AveragingRate.SumPinned` (the `g = n` case) to the honest gap `g`; `K`-closed
    (`EntrySumPinned_support_closed` / `invClosed_entrySumPinned`), via `AveragingRate`'s landed
    `centredBiasSum_eq_on_support`.
  - STAGE B (the honest pigeonhole, ℤ, division-free): the pointwise bias bounds `biasZ_ge_low`
    (`4·[val≥4] − 3 ≤ biasZ`) / `biasZ_le_high`, summed by direct multiset induction
    (`lowCount_core` / `highCount_core`: `card − 4·#{val≤3} ≤ S ≤ card − 4·#{val≥3}`). Combined with
    `|S| ≤ g`: `four_mul_lowCount_ge_of_entry` / `_highCount_` give `(n:ℤ) − g ≤ 4·countP`. The
    `countP`-↔-`Finset.sum count` bridge (`sum_count_filter_eq_countP`, generic re-derivation of the
    `EarlyDripMarked` lemma for `AgentState`) + the all-Main role-conjunct collapse
    (`lowSet_sum_count_eq_countP` / `high`) convert to the consumer's count shape:
    `lowSet_floor_of_entry` / `highSet_floor_of_entry` = `(n − g + 3)/4 ≤ (lowSet/highSet).sum count`.
  - STAGE C (instantiate `AveragingRate`'s `P'` slot): `secondMomentN_hdrop_of_entry_high/_low` feed
    `P = (n − g + 3)/4` into `AveragingRate.secondMomentN_hdrop_of_struct_high/_low`. The only
    config-dependent input left is the far witness `1 ≤ farHighSet/farLowSet .sum count` — the SIDE
    `farExists_of_secondMoment_gt_n` leaves open (it supplies *a* far Main; *which* side is the
    per-config datum the rectangle pairs against the opposite-side partner floor; both orientations
    delivered).
  - STAGE D (final floor surface): `phase1_pullPos_floor_whp_of_entry` instantiates
    `AveragingRate.phase1_pullPos_floor_whp_of_struct` with `P = (n − g + 3)/4`. Inputs: the protocol
    window `Phase1AllMain`, the honest entry gap `g`, and the rate family `q` (discharged structurally
    by Stage C). HORIZON arithmetic documented in-file: `q m = 1 − Θ(1/n)` ⟹ `(q m)^t ≤
    exp(−Θ(t/n))` ⟹ `t = Θ(n·log n)` for `O(1/n²)` failure (paper-faithful Lemma 5.3 / [45] Cor.1).

---

[intro]
I’ll inspect the new floor-wiring file first, then trace each consumer back through the drain lemmas and existing invariant/phase posts to classify “adapter only” versus genuinely new probability.

I found the key classification encoded in `PhaseFloors`: Phase 6 is already fully wired; Phase 1 has a real arithmetic adapter but still needs a saturated-side bound; Phases 5/7/8 are still missing the actual lower-bound provenance theorem, not just wiring. Next I’ll verify the landed “opposite-shape” invariant facts so we don’t mistake a survival upper bound for an eliminator floor.

[answer]
## Executive classification

There are **four named floor gaps**, but not all four are equally “new probability.”

| Floor | Current status | Honest classification |
|---|---:|---|
| Phase 1 `pullPosSet ≥ P` | adapter from `mainCount` exists; saturated-side bound missing | **genuinely new / imported averaging theorem** |
| Phase 5 `usefulMains ≥ P` | no landed theorem | **genuinely new Theorem 6.2 floor** |
| Phase 7 `elimGap1 ≥ E` | no landed theorem; not complement of survival upper bound | **genuinely new Lemma 7.4 eliminator floor** |
| Phase 8 `elimAbove ≥ E` plus `minorityAt ≥ 1` | `minorityAt ≥1` is deterministic once minority remains; `elimAbove ≥E` missing | **one adapter + one genuinely new Lemma 7.4–7.6 eliminator-margin floor** |

Phase 6 is already fully wired from the Phase-5 `ReserveSampleGood` post: `phase6_reserve_floor_of_phase5Post` extracts `K₀ ≤ reserveAtHour6 i .sum count`, and `phase6_hdrop_wired` consumes it. fileciteturn45file0L82 argument is

The relevant paper provenance is Lemma 5.3 / Phase 1 averaging. The repository’s Phase-1 file explicitly records the paper’s actual technique: two Main agents replace their small biases by the floor/ceil average; the global sum is preserved; the paper imports the quantitative collapse from reference [45], saying all Main biases converge to `{μ−1, μ, μ+1}` in `O(log n)` time whp. file-repo Phase-1 development deliberately does **not** prove that full collapse. It proves the weaker, honest monotone fact that saturated **extremes** `smallBias.val = 0 or 6` are never created by averaging, and packages `extremeU` as the potential. fileciteturn58file0L43-L63

### What is already landed

`PhaseFloors.lean` already proves the key adapter:

```lean
theorem mainCount_eq_pullPos_add_saturatedPos {L K : ℕ} (c : Config (AgentState L K)) :
    RoleSplitConcentration.mainCount (L := L) (K := K) c
      = (DrainThreading.pullPosSet L K).sum c.count
        + (saturatedPosSet L K).sum c.count
```

This decomposes all Mains into the partner pool `pullPosSet` (`smallBias.val ≤ 4`) plus the saturated-positive side `smallBias.val ≥ 5`. filecite is:

```lean
theorem phase1_hdrop_wired ... 
    (hpull : P ≤ (DrainThreading.pullPosSet L K).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
```

fileciteturn46file0 a `+3` extreme averaged with a Main of `smallBias.val ≤ 4` strictly reduces `extremeU`. fileciteturn48file0L58-L74

### Missing theorem

This is not a pure adapter anymore. The missing fact is:

```lean
/-- Phase-1 saturated positive side is small enough to expose a pull partner floor. -/
theorem phase1_pullPos_floor_of_mainCount_and_saturated_bound
    {L K n P : ℕ} {c : Config (AgentState L K)}
    (hmain : (n : ℝ) / 3 ≤
      (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ))
    (hsat : (saturatedPosSet L K).sum c.count ≤ n / 3 - P) :
    P ≤ (DrainThreading.pullPosSet L K).sum c.count := by
  -- use `mainCount_eq_pullPos_add_saturatedPos`
  sorry
```

But the real missing probability is the saturated-side bound:

```lean
/-- The Phase-1 averaging theorem needed by the drain floor. -/
theorem phase1_saturatedPos_floor_whp
    {L K n t : ℕ} {c₀ : Config (AgentState L K)}
    (hpre : Phase1Convergence.Phase1AllMain n c₀)
    (hroleSplitMain : (n : ℝ) / 3 ≤
      (RoleSplitConcentration.mainCount (L := L) (K := K) c₀ : ℝ))
    (P : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
      {c | ¬ P ≤ (DrainThreading.pullPosSet L K).sum c.count}
      ≤ ENNReal.ofReal (1 / ((n : ℝ)^2)) := by
  -- honest route: prove/import the averaging collapse;
  -- weaker existing `extremeU` only controls `smallBias = 0 or 6`,
  -- not the `smallBias = 5` part of `saturatedPos`.
  sorry
```

The engine choice is **not** the one-sided drain engine alone. It needs either the external discrete-averaging theorem recorded in `Phase1Convergence.lean`, or a new cosh/variance/exponential-potential averaging proof over the bounded `Fin 7` small-bias values.

---

## 2. Phase 5 floor: `usefulMains ≥ P`

### What the paper argument is

This is the Theorem 6.2 floor: by Phase-5 entry, a large constant fraction of Mains have useful biased exponents, i.e. exponent index `< L`. `PhaseFloors.lean` states the intended shape as

```text
biasedMainLtL ≥ 0.92·mainCount ≥ 23n/75
```

and records that no such count-lower-bound theorem is landed. fileciteturn46file0 Phase 5 samples the static biased-Main exponent profile. Main bias is frozen throughout Phase 5, so Reserve sampling is an epidemic/coupon/concentration problem over a **static** class profile. But the existence of enough useful biased Mains at entry is not proved by Phase 5 itself. file consumer

`phase5_hdrop_wired` consumes:

```lean
(hmain : P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count)
```

and produces the one-step drain floor for `unsampledReserveU`. file is already threaded in `DrainThreading`:

```lean
theorem phase5_drop_floor_of_struct ...
    (hres : 1 ≤ (Phase5Convergence.unsampledReserves ...).sum c.count)
    (hmain : P ≤ (Phase5Convergence.usefulMains ...).sum c.count) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ReserveSampling.unsampledReserveU ... c' + 1 ≤ ... c}
```

fileciteturn49file0L70-L93

### Missing theorem

This one is genuinely new. It should be stated as a Phase-5 entry theorem, not inside Phase 5:

```lean
/-- Theorem 6.2 useful-Main floor at Phase-5 entry. -/
theorem theorem6_2_usefulMains_floor
    {L K n : ℕ} {c : Config (AgentState L K)}
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    -- whatever Phase-3/4 postcondition currently chains into Phase5AllWin:
    (hT62 : Theorem62EntryHypotheses (L := L) (K := K) n c)
    (P : ℕ)
    (hP : (P : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75) :
    P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count := by
  sorry
```

The placeholder `Theorem62EntryHypotheses` should be replaced by the actual chain post that proves the §6 distribution result—likely the Phase-3/4 post shape already carried into `Phase5AllWin`.

Engine classification: **not coupon sampling**; coupon sampling is already Phase 5’s job after this floor. This is a §6 distribution/count theorem and likely wants the Phase-3/clock/front machinery, not `ReserveSampling`.

### STATUS — DELIVERED (2026-06-10, `Probability/UsefulMainFloor.lean`)

The Phase-5 floor is now delivered in the blueprint shape. Single-file `lake env lean` EXIT_0;
all 5 headlines axiom-clean (`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`); no
sorry/admit/axiom/native_decide.

**What the landed chain ACTUALLY exports about exponent confinement: NOTHING.** Audit:
- `ReserveSampling.Phase5AllWin n c = c.card = n ∧ ∀ a ∈ c, a.phase.val = 5` — a PURE PHASE
  window, carries no bias/exponent profile.
- Phase-3/4 `Post`s (`advFinished` / `StableTie4`) are phase-advance + tie facts (`noBigBias` for
  ALL agents — the OPPOSITE extreme, every biased agent at the cap index `= L`); neither is a
  count LOWER bound on big-bias (`index < L`) Mains. Theorem 6.2 is the NON-tie branch.
- `RoleSplitConcentration.mainCount_lower_of_RoleSplitGood` gives `n/3 ≤ mainCount` only (Lemma
  5.2 role split), nothing about the exponent distribution within Mains.
- The landed §6 width machinery (`ClockFrontProfile` Thm 6.5, `WidthTransport`/`CrossHourSide`/
  `FrontTailDecay` Thm 6.9/6.12) concentrates the CLOCK minute field (`O(log log n)` front width),
  the ENABLING mechanism — NOT a count over Main bias exponents. Genuine attack performed (see
  file header): deriving `0.92·|M| ≤ #usefulMains` from those exports alone is not possible; it
  needs the full Phase-3 bias-ledger collapse (Thm 6.5 squaring on the Main exponent profile +
  total-mass-above/minority-mass bounds, union-bounded over `O(log n)` hours).

**Split: closed vs carried.**
- CLOSED (proven, axiom-clean): the partition arithmetic `mainCount = #usefulMains + #satExpMains`
  (`mainCount_eq_usefulMains_add_satExp`, the Phase-5 analogue of
  `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos`); and the conversion
  `Theorem62EntryHypotheses + (P ≤ 23n/75) ⟹ P ≤ #usefulMains` via
  `23n/75 = 0.92·(n/3) ≤ 0.92·|M| ≤ #usefulMains` (`theorem6_2_usefulMains_floor`).
- CARRIED (ONE precisely-stated named fact with paper provenance): the Theorem-6.2 confinement
  `0.92·|M| ≤ #usefulMains`, bundled as the `hConfine` field of the structure
  `Theorem62EntryHypotheses`. Paper provenance: arXiv:2106.10201v2 Theorem 6.2 (`|M'| ≥ 0.92|M|`
  whp, with `M' = {majority Mains at exponents −l,−(l+1),−(l+2)} ⊆ usefulMains` since `l+2 < L`).

**Wired adapter:** `phase5_hdrop_wired_from_theorem6_2` supplies the `PhaseFloors.phase5_hdrop_wired`
`hmain` floor directly from `Theorem62EntryHypotheses` + `P ≤ 23n/75`. The blueprint's
`Theorem62EntryHypotheses` placeholder is now a concrete `structure` (fields `hPhase5`,
`hMainFloor`, `hConfine`), with the mapping to the landed chain documented in the file header.

---

## 3. Phase 7 floor: `elimGap1 ≥ E`

### What the paper argument is

This is the Lemma 7.4 eliminator-majority floor. The Phase-7 file explains the intended structure: after Phase 6, many majority-sign Mains remain; minority agents are confined to a small exponent band; Phase 7 uses gap-0/1/2 cancellation, and the carried floor is the `0.8|M|` eliminator supply. fileciteturn54file0 A survival upper bound after Phase 7 does not imply the pre-Phase-7 fact that enough majority eliminators existed at each gap-1 level. You need a pre-drain floor.

### Current consumer

`phase7_hdrop_wired` consumes:

```lean
(hmin : 1 ≤ (Phase7Convergence.minorityAt7 ... σ j).sum b.count)
(helim : E ≤ (Phase7Convergence.elimGap1 ... σ i).sum b.count)
```

and threads them through the already-proved rectangle. fileciteturn7_drop_floor_of_struct ...
    (hmin : 1 ≤ (Phase7Convergence.minorityAt7 ... σ j).sum c.count)
    (helim : E ≤ (Phase7Convergence.elimGap1 ... σ i).sum c.count) :
    ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.classMassN σ c' + 1 ≤ Phase7Convergence.classMassN σ c}
```

fileciteturn48file0L4-L24

### Missing theorem

The correct target is existential over the witness level pair, because the drain proof only needs a witness level with minority mass and enough gap-1 eliminators:

```lean
/-- Lemma 7.4 floor for Phase 7: every nonzero minority level has a large gap-1 eliminator supply. -/
theorem lemma7_4_phase7_elimGap1_floor
    {L K n : ℕ} (σ : Sign)
    {c : Config (AgentState L K)}
    (hb7 : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    -- actual Phase-6 post / Lemma-7.3 structural input:
    (hPhase6Post : Phase6To7Structure (L := L) (K := K) σ n c)
    (hminor : 1 ≤ Phase7Convergence.classMassN (L := L) (K := K) σ c)
    (E : ℕ)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    ∃ i j : Fin (L + 1),
      i.val + 1 = j.val ∧
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count ∧
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count := by
  sorry
```

Then add the adapter:

```lean
theorem phase7_hdrop_wired_from_lemma7_4
    {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb7 : Phase7Convergence.Phase7AllMain n b)
    (hbm : Phase7Convergence.classMassN σ b = m)
    (hmpos : 1 ≤ m)
    (E : ℕ)
    (hfloor : ∃ i j : Fin (L + 1),
      i.val + 1 = j.val ∧
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  rcases hfloor with ⟨i, j, hg1, hmin, helim⟩
  exact PhaseFloors.phase7_hdrop_wired σ n m hn b hb7 hbm i j hg1 E hmin helim
```

Engine classification: this is a **count-structure theorem**, probably from the Phase-6 output plus mass/sign/exponent partition identities. It is not a new transition-probability rectangle; that rectangle is already landed.

---

## 4. Phase 8 floor: `elimAbove ≥ E` and `minorityAt ≥ 1`

### What the paper argument is

Phase 8 consumes remaining minority agents using `absorbConsume`. The Phase-8 file explains that the eliminator pool shrinks because consumers become `full`, but the carried invariant should maintain enough non-full majority eliminators above the remaining minority level; this is the Lemma 7.6-style margin. fileciteturn65file new probability

`hmin : 1 ≤ minorityAt σ i` is mostly an adapter. If `minorityU σ c = m` and `1 ≤ m`, then some minority agent has some exponent index `i`; therefore `minorityAt σ i ≥ 1`.

So add:

```lean
/-- Deterministic witness: nonzero minority mass gives a level with a minority. -/
theorem exists_minorityAt_of_minorityU_pos
    {L K : ℕ} (σ : Sign) (c : Config (AgentState L K))
    (hm : 1 ≤ Phase7Convergence.minorityU (L := L) (K := K) σ c) :
    ∃ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count := by
  -- unfold `minorityU`, extract a witness from countP > 0,
  -- unpack `minoritySt σ a = role=main ∧ ∃ i, bias=dyadic σ i`,
  -- use that same `i` in `minorityAt`.
  sorry
```

The genuine missing theorem is `elimAbove ≥ E` at that chosen level.

### Current consumer

`phase8_hdrop_wired` consumes exactly:

```lean
(hmin : 1 ≤ (Phase8Convergence.minorityAt ... σ i).sum b.count)
(helim : E ≤ (Phase8Convergence.elimAbove ... σ i).sum b.count)
```

and produces the drain floor. file-level rectangle adapter is already landed:

```lean
theorem phase8_drop_floor_of_struct ...
    (hmin : 1 ≤ (Phase8Convergence.minorityAt ... σ i).sum c.count)
    (helim : E ≤ (Phase8Convergence.elimAbove ... σ i).sum c.count) :
    ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ c}
```

fileciteturn47file0L73-L97-8 eliminator-margin floor. -/
theorem lemma7_6_phase8_elimAbove_floor
    {L K n : ℕ} (σ : Sign)
    {c : Config (AgentState L K)}
    (hb8 : Phase8Convergence.Phase8AllMain (L := L) (K := K) n c)
    -- actual Phase-7 post / Lemma-7.5-7.6 structural input:
    (hPhase7Post : Phase7To8Structure (L := L) (K := K) σ n c)
    (i : Fin (L + 1))
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count)
    (E : ℕ)
    (hE : (E : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5) :
    E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count := by
  sorry
```

Then the adapter:

```lean
theorem phase8_hdrop_wired_from_lemma7_6
    {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb8 : Phase8Convergence.Phase8AllMain n b)
    (hbm : Phase7Convergence.minorityU σ b = m)
    (hmpos : 1 ≤ m)
    (E : ℕ)
    (hexists :
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
        E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  rcases hexists with ⟨i, hmin, helim⟩
  exact PhaseFloors.phase8_hdrop_wired σ n m hn b hb8 hbm i E hmin helim
```

Engine classification: the `minorityAt` part is deterministic; `elimAbove` is a genuine structural floor, but probably a **deterministic adapter from the true Lemma 7.6 post**, not a fresh scheduler tail. The current files have the transition rectangles and non-increase machinery; they do not yet have the count-margin theorem.

---

## Are Phase 7/8 floors complements of the landed survival upper bounds?

No. The audit in `PhaseFloors.lean` is right.

For Phase 7, the landed facts mentioned in `Invariants.lean` are survival/elimination **outcomes**; the floor needed by `DrainThreading` is a **pre-step rectangle lower bound** on an eliminator class. A statement like “minority survivors eventually ≤ X” cannot by itself produce “at every level with a minority, there are ≥ E gap-1 eliminators now.” The rectangle needs the actual count product before the random pair is drawn.

For Phase 8, the `minorityAt ≥ 1` witness is deterministic from `minorityU > 0`, but `elimAbove ≥ E` is still not a survival-complement. It is a currently-live non-full eliminator margin needed to make the next interaction likely.

---

## Engine mapping

| Floor | Best engine / proof family |
|---|---|
| Phase 1 saturated side | Discrete averaging concentration. Existing `Phase1Convergence.extremeU` is too weak for `smallBias=5`; use imported [45]-style theorem or a new bounded averaging/cosh potential proof. |
| Phase 5 useful Mains | Theorem 6.2 structural distribution theorem from Phase 3/4 outputs; not Reserve sampling. Once useful floor holds, Phase 5’s coupon/sampling engine is already landed. |
| Phase 7 elimGap1 | Count-structure theorem from Phase-6/7 post; rectangle already landed via `phase7_drop_floor_of_struct`. |
| Phase 8 elimAbove | Deterministic `minorityAt` witness + count-margin theorem from Phase-7/8 post; rectangle already landed via `phase8_drop_floor_of_struct`. |
| Phase 6 reserve floor | Already fully wired from `ReserveSampleGood`; no new probability. |

TopSplit/Azuma/cosh and killed-affine are probably **not** the main tools for Phases 5/7/8 floors. Those floors are count-structure consequences of earlier phase posts. The main new probabilistic burden is Phase 1 if you want to avoid importing the [45] averaging theorem; otherwise it is a theorem import/adapter.

---

## Priority order

1. **Do the deterministic adapters first.**  
   Add `exists_minorityAt_of_minorityU_pos` for Phase 8 and the “from main decomposition to `pullPosSet`” arithmetic wrapper. These are small and immediately reduce the visible missing surface.

2. **Phase 5 Theorem 6.2 useful-Main floor.**  
   This unblocks the Phase-5 drain and, through the already landed `ReserveSampleGood`, supports the Phase-6 chain. It is the highest leverage missing count theorem.

3. **Phase 7 and Phase 8 eliminator floors together.**  
   They share the Lemma 7.4–7.6 structural story: majority eliminator supply versus minority bands. Prove them as a common partition/margin package rather than two unrelated probability lemmas.

4. **Phase 1 saturated-side floor.**  
   This is early in the chain but conceptually separate. If you accept the paper’s [45] averaging theorem as an imported probabilistic theorem, it becomes an adapter. If not, it is the most mathematically self-contained new concentration proof: bounded pairwise averaging, likely by a cosh/variance contraction potential.
