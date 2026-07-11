# HANDOFF: RoleSplitWindows via top-split (family3 letter, task 59da8aae, 2026-06-10)

Source: ChatGPT Pro (family3 channel, GitHub connector on xiangyazi24/Ripple
opus-wip). Auto-capture truncated at 181 B; full text manually pasted by Xiang.
This file is the verbatim-faithful blueprint record.

## Bottom line (ChatGPT's verdict)

Do NOT formalize `RoleSplitWindows` as "Chernoff on the number of R1 fires."
That is not what the paper's proof needs, and is not stable under the Lean
encoding where R4 can fire concurrently. Minimal route:

1. Formalize the **Lemma 5.1 top-split balance**: `Main` vs "ever-produced
   RoleCR mass" is `n/2 ± δn` whp.
2. Reuse existing Stage-2 CR-drain/Janson machinery to convert most RoleCR
   mass into balanced `Clock`/`Reserve`.
3. Deterministic lemma: `TopSplitWindow δ` + `CRDrainWindow δ` +
   `ClockReserveBalanced` + conservation ⟹ `RoleSplitWindows η`, δ = η/4.

Constants: final η = 1/25, internal δ = 1/100. Satisfies
`clockCount_linear_of_RoleSplitGood` (expects η ≤ 1/25, gives clockCount ≥ n/5).

## What Lemma 5.2 actually bounds

Paper Lemma 5.2: whp 1 − O(1/n²), by end of Phase 0: no RoleMCR; Main count
n/2(1±ε); Clock and Reserve each ≥ n/4(1−ε). The top-level split is Lemma 5.1
with U = RoleMCR, M = Main, S = RoleCR; only AFTER that does it analyze the
RoleCR→Clock/Reserve split (U,U → R,C plus U → R at phase end). By Lemma 5.1,
after 12.5 ln n time, produced RoleCR count s satisfies n/3 ≤ s ≤ 2n/3 w.p. 1
and s = n/2(1±ε₀) whp; second-level split yields Clock,Reserve ≥ n/4(1−4ε₀) whp.

The Chernoff part is NOT "#R1 near its mean." The key balance process is
|m − s| (m = #Main, s = #RoleCR in top split). The invariant `sf + 2st = mf + 2mt`
implies: when s > m then sf > mf, so the next reaction changing s − m is more
likely to decrease it; |m−s| is stochastically dominated by a sum of independent
coin flips → Chernoff gives |m−s| ≤ εn.

Honest event probabilities, top split:
- R1: MCR+MCR, raw ordered ≈ u(u−1)/(n(n−1))
- R2/R3 combined: MCR+assignable, one-oriented lower bound u·assignable/(n(n−1))
  (full two-oriented paper rate ≈ 2u·assignable/(n(n−1)))

Repo already proves (reuse these): `phase0_mcrCount_decrease_prob_oneSided`,
`phase0_mcrCount_decrease_prob_combined`, `phase0_mcrCount_decrease_prob_floor`.

Conditional R1 probability among the single-oriented good rectangle:
p_R1(u,A) = (u−1)/(u−1+A), A = assignableCount = sf+mf — NOT uniformly bounded
away from 0 over the whole run. Early (u ≥ 2n/3) the paper bounds the top
reaction ≥ 1/2 among non-null; later it uses the assignable-floor rate, not R1.

## Target Lean surface

### A. New defs

```lean
/-- Total mass descended from the top-level S = RoleCR split. -/
def topCRMass (c : Config (AgentState L K)) : ℕ :=
  crCount c + clockCount c + reserveCount c

def TopSplitWindow (δ : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  |(mainCount c : ℝ) - (topCRMass c : ℝ)| ≤ δ * n

def CRDrainWindow (δ : ℝ) (c : Config (AgentState L K)) : Prop :=
  (crCount c : ℝ) ≤ δ * (topCRMass c : ℝ)
```

topCRMass (not crCount alone) because R4 moves RoleCR into Clock+Reserve
without changing the top-level Main-vs-S balance (ΔX = 0 for R1 and R4).

### B. Deterministic conversion (pure algebra, no probability)

```lean
theorem RoleSplitWindows_of_topSplit_crDrain
    {η δ : ℝ} {n : ℕ} {c : Config (AgentState L K)}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hδ : δ = η / 4)
    (hcard : Multiset.card c = n)
    (hmcr0 : roleMCRCount c = 0)
    (hbal : ClockReserveBalanced c)
    (htop : TopSplitWindow δ n c)
    (hdrain : CRDrainWindow δ c) :
    RoleSplitWindows η n c
```

Arithmetic: conservation + hmcr0 ⟹ mainCount + topCRMass = n; htop ⟹
mainCount ∈ [(1−δ)n/2, (1+δ)n/2] (δ ≤ η gives Main window); hbal ⟹
topCRMass = crCount + 2·clockCount; hdrain ⟹ clockCount = reserveCount
≥ (1−δ)·topCRMass/2 ≥ (1−δ)²n/4 ≥ (1−η)n/4 (with δ=η/4: (1−1/100)²/4 =
0.9801/4 > 0.96/4 = (1−1/25)/4). Uses existing `roleCount_conservation`,
`balanced_conservation`.

### C. Probabilistic top-split tail (the real residual)

```lean
theorem topSplitWindow_whp
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 2 ≤ n)
    {c₀ : Config (AgentState L K)} (hinit : Phase0Initial n c₀) (tTop : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ tTop) c₀
      {c | ¬ TopSplitWindow δ n c} ≤ ENNReal.ofReal (((n:ℝ)^2)⁻¹)
```

Proof via inward-drift for X c = mainCount c − topCRMass c (NOT R1-count
concentration). One-step sign-drift from the paper invariant sf+2st = mf+2mt.

### D. Abstract sign-drift Chernoff brick (fits existing engines)

```lean
theorem signDrift_abs_chernoff
    (K : Kernel α α) [IsMarkovKernel K] (X : α → ℤ) (G : Set α)
    (T : ℕ) (x₀ : α) (a : ℝ)
    (hX0 : X x₀ = 0)
    (hjump : ∀ x ∈ G, ∀ y ∈ (K x).support, |((X y:ℝ) - (X x:ℝ))| ≤ 1)
    (h_inward : <if X>0 downward prob ≥ upward; if X<0 upward ≥ downward>)
    (hgate_tail : (killK K G ^ T) (some x₀) {none} ≤ ofReal ((n:ℝ)²)⁻¹) :
    (K ^ T) x₀ {x | a ≤ |(X x : ℝ)|} ≤
      gate_escape + ENNReal.ofReal (2 * Real.exp (-(a*a)/(2*T)))
```

Use `stepIndexed_gated_tail` with Φ_j x = exp(s·|X x| + correction_j). If the
window is genuinely support-closed use `windowDrift_tail`; otherwise the
killed-kernel version.

### E. Final assembly

```lean
theorem roleSplitWindows_whp
    {n : ℕ} (hn : 100 ≤ n) {c₀} (hinit : Phase0Initial n c₀) (tRole : ℕ) :
    (K' ^ tRole) c₀ {c | ¬ RoleSplitWindows (1/25 : ℝ) n c}
      ≤ ENNReal.ofReal (3 * ((n:ℝ)^2)⁻¹)
```

Union bound: (1) topSplitWindow_whp δ=1/100; (2) existing
`phase0_roleSplit_whp_two_stage` (Stage-1/1.5/2 composition, Post =
`RoleSplitStage2Good` = mcr=0 ∧ crCount ≤ 1); (3) deterministic conversion B.
Insertion point: `phase0_roleSplit_whp_assembled_stage2` already takes
(hstage2, hbal, hwin) — `roleSplitWindows_whp` is the last clean named input.

## Status

- [x] A+B (defs + deterministic conversion) — DONE 2026-06-10, 0-sorry axiom-clean.
      `Probability/TopSplit.lean`: `topCRMass`/`TopSplitWindow`/`CRDrainWindow` +
      `RoleSplitWindows_of_topSplit_crDrain` (δ=η/4, η=1/25, δ=1/100). Pure algebra via
      `roleCount_conservation` + `balanced_conservation`. Commit 37066f79.
- [x] D (abstract sign-drift brick) — DONE 2026-06-10, 0-sorry axiom-clean. RESHAPED to fit the
      EXISTING `AzumaKernel.azuma_tail` engine (Φ=|X|, c=1), NOT `stepIndexed_gated_tail`: the
      blueprint's schematic `h_inward` IS the downward |X|-supermartingale drift `∫|X|dK≤|X|`;
      `hjump` gives `||X y|-|X x||≤1` by reverse triangle. No killed-kernel escape term (drift
      global in the abstract brick; region-restriction folded into the named `hdrift` at
      instantiation). `signDrift_abs_chernoff`: `(K^T)x₀{a≤|X|}≤exp(-a²/(2T))`. Commit 07c9c9ba.
- [x] C (instantiate for X = mainCount − topCRMass) — DONE 2026-06-10 as NAMED-HYPOTHESIS version
      (the one-step inward `|X|`-drift `hdrift` + bounded jump `hjump` are the documented protocol
      residuals; `topSplit_X_init_zero` PROVEN from `Phase0Initial`). Genuine attack on `hdrift`
      documented in-file (reduces to #decreasing-pairs ≥ #increasing-pairs, the
      `phase0_mcrCount_decrease_prob` rectangle + the `sf+2st=mf+2mt` invariant thread = the
      C-1 gap). `topSplitWindow_whp`. Commit 07c9c9ba.
- [x] E (union-bound assembly) — DONE 2026-06-10, 0-sorry axiom-clean. `roleSplitWindows_whp`:
      `{¬RoleSplitWindows (1/25) n} ⊆ {¬TopSplitWindow (1/100)} ∪ ({RestLedgerBad} ∪ {card≠n})`
      (contrapositive of B), union bound εtop (Stage-C) + εrest (named Stage-2 drain/balance/mcr0
      slice). Commit 39bb769a. All 4 headlines `#print axioms ⊆ [propext,Classical.choice,Quot.sound]`.

## Residual discharge — `Probability/TopSplitDrift.lean` (2026-06-10, 0-sorry axiom-clean)

Stage C carried `hjump`/`hdrift` as named hypotheses. `TopSplitDrift.lean` discharges them HONESTLY,
finding and fixing TWO faithfulness traps in the Stage-C interface:

- **Stage 1 (ledger).** TRUE invariant = the existing `mainCount + topCRMass = n`. The paper's
  `sf + 2·st = mf + 2·mt` does NOT map literally onto the Lean encoding — computing ΔX per rule shows
  X = mainCount−topCRMass moves ONLY by R2 (−1: mcr+unassigned-Main→cr) and R3 (+1: mcr+unassigned-
  (cr/clock/reserve)→Main); R1/R4/R5 give ΔX=0. Honest ledger = per-agent weight
  `topW = [main] − [cr∨clock∨reserve]` with `topSplitXZ = Config.sumOf topW`. The free pools driving
  drift are `#unassigned-Main` (R2 targets) vs `#unassigned-(cr/clock/reserve)` (R3 targets).
- **Stage 2 (hjump).** `topW_pair_delta_abs_le_one_of_phase0`: |ΔX|≤1 FULLY PROVEN (finite role/assigned
  case check; R5 clock–clock split off via `stdCounterSubroutine_clock_role_eq`). The true bound is 1.
- **Stage 3 (hdrift) — TRAP FOUND + FIXED.** The Stage-C `hdrift : ∫|X|dK ≤ |X|` is **FALSE at X=0**
  (from a balanced config |X|=0 but R2/R3 push to ±1, so ∫|X|dK > 0 = |X|). Feeding it would be a
  VACUOUS-conditional theorem (unsatisfiable premise; `#print axioms` cannot detect this). HONEST FIX =
  the cosh MGF: `InwardResidual s c := sinh(sX)·E[sinh(sΔ)] ≤ 0`, which is BOUNDARY-FREE (sinh 0 = 0 at
  X=0). `coshExpVal_drift_real` proves `∫cosh(sX')dK ≤ cosh(s)·cosh(sX)` (multiplicative, no
  immigration). `coshPot_drift` lifts to ℝ≥0∞.
- **Stage 4 (tail + wire-up).** `topSplitWindow_whp_cosh[_clean]` feeds `WindowConcentration.
  windowDrift_tail` on absorbing `Q` (carrying allPhase0 + InwardResidual), threshold cosh(s·δn):
  `(K^T)c₀{¬TopSplitWindow δ n} ≤ (cosh s)^T/cosh(s·δn)` at the balanced start (`coshPot_init_one`).
  This RESTATES the Stage-C conclusion shape (TopSplit.lean unedited). The two genuine protocol residuals
  carried (both boundary-free): `Q` absorbing (the documented `Q ⊆ allPhase0` witness, also the
  Phase0Window gap) + `InwardResidual` on `Q` (the honest Lemma-5.1 symmetric pair-count comparison).
  Commits f475aedd / 87271ca4 / 7760b01 / 7e9e3a6d (opus-wip mirror).

## InwardResidual discharge — `Probability/TopSplitInward.lean` (2026-06-10, 0-sorry axiom-clean)

`TopSplitDrift.lean` carried `InwardResidual s c := sinh(sX)·E[sinh(sΔ)] ≤ 0` as the one honest
protocol residual. `TopSplitInward.lean` DISCHARGES it down to a single, precisely-stated,
sign-verified R2/R3 mass-counting identity, with the genuinely-new assigned-balance ledger and the
full boundary-free reduction PROVEN. All 8 headlines `#print axioms ⊆ [propext,Classical.choice,Quot.sound]`.

- **Stage 1 — the assigned-balance ledger (THE new content).** Tracking the FOUR pools `Mf`=#unasg-Main,
  `Ma`=#asg-Main, `Sf`=#unasg-CR-side, `Sa`=#asg-CR-side against FROZEN `Phase0Transition`: every rule has
  `Δ(Mf−Sf) = 2·ΔX` (R2: −2/−1, R3: +2/+1, R1/R4/R5: 0/0). Per-agent weight
  `freeW = [main∧¬asg] − [(cr∨clock∨reserve)∧¬asg]`; `ledgerW_Phase0_pair_conserved` proves the per-pair
  conservation of `freeW − 2·topW` (finite role/assigned case check, R5 clock–clock split off via
  `stdCounterSubroutine` preserving role+assigned — `phaseInit_assigned_eq`). The Lean-faithful counterpart
  of the paper's `sf+2st=mf+2mt`. CAVEAT FOUND: conservation FAILS for `assigned-mcr` inputs (an unreachable
  corner — rules only CONSUME mcr, never assign/produce it); carried as the `NotAssignedMcr` side-condition.
- **Stage 1b — global invariant `LedgerInv c := freeDiff c = 2·topSplitXZ c`.** Proven preserved by
  `stepOrSelf` (`LedgerInv_stepOrSelf`, additive lift) on allPhase0 ∧ NoAssignedMcrConfig, and holds at the
  start (`LedgerInv_init`). `NoAssignedMcrConfig_stepOrSelf`: assigned-mcr never created.
  HONEST SPEC GAP: `Phase0Initial` pins only role/phase, NOT `assigned=false`, so `NoAssignedMcrConfig c₀`
  is true-of-the-real-start but not derivable from the abstract `Phase0Initial` — carried explicitly.
- **Stage 2 — sign comparison** (`freeDiff_sign_of_topSplit`): `Mf−Sf=2X`, so `X>0 ⟹ Sf<Mf` (more free
  Mains than free CR-side, the inward bias).
- **Stage 3a — boundary-free sinh collapse** (`inwardResidual_of_expectedDeltaX_sign`): `Δ_pair ∈ {−1,0,1}`
  ⟹ `sinh(s·Δ_pair) = Δ_pair·sinh s` ⟹ `E[sinh(sΔ)] = sinh s·E[ΔX]`, and `InwardResidual ⟸ X·E[ΔX] ≤ 0`
  (FULLY PROVEN; `X=0 ⟹ sinh 0 = 0` ⟹ boundary-free).
- **Stage 3b — ledger ⟹ sign** (`expectedDeltaX_sign_of_ledger`): under `LedgerInv` + the named
  `RectangleResidual c := totalPairs·E[ΔX] = −2·mcrCount·freeDiff`, `X·E[ΔX] = −4·mcr·X²/tp ≤ 0`.
  `inwardResidual_of_ledger` packages InwardResidual on the ledger region.
- **Stage 4 — tail wire-up** (`topSplitWindow_whp_inward`): feeds `topSplitWindow_whp_cosh_clean`; residual
  = region `Q` carrying allPhase0+card+LedgerInv+RectangleResidual; tail `(cosh s)^T/cosh(s·δn)`.

THE ONE REMAINING RESIDUAL = `RectangleResidual` (the R2/R3 mass identity). GENUINE ATTACK documented
in-file: reduces to the JOINT double-marginal `∑_{s₁,s₂} interactionCount·pairDelta = 2·mcr·(Sf−Mf)`,
where `pairDelta ∈ {−1,0,1}` is the proven `topW`-block delta. The repo has only SEPARABLE per-coordinate
marginal collapse (`sum_fst/snd_interactionProb`, e.g. `clockCounterPotential_drift_affine`); the joint
double-`Multiset.count` rectangle is the precise missing lemma. Isolated as the named residual; everything
consuming it (the inward sign + the full cosh tail) is discharged.
Commits 86f2083e / 666babd4 / 1c7e2fde / e454d342.

## RectangleResidual DISCHARGED — `Probability/RectangleResidualProof.lean` (2026-06-10, 0-sorry axiom-clean)

The LAST named protocol residual of `TopSplitInward.lean` is now a THEOREM. The joint double-marginal
`∑_{s₁,s₂} interactionCount·pairDelta = 2·mcr·(Sf−Mf)` is proven; `rectangleResidual_of_allPhase0` supplies
`RectangleResidual c` from `allPhase0 c ∧ card ≥ 2` alone. All headlines
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`.

- **`pairDeltaZ s₁ s₂`** = role-determined `topW`-block delta of `Phase0Transition`. `pairDeltaZ_eq_table`
  (finite 5×5×2×2 check, R5 clock–clock split off): `pairDeltaZ = indR3 − indR2`, i.e. `−1` on R2 pairs
  (mcr ↔ unassigned-Main, EITHER orientation), `+1` on R3 pairs (mcr ↔ unassigned-CR-side), `0` else.
- **ORIENTATION accounting (verified vs FROZEN Transition):** `Phase0Transition` dispatches R2/R3 with an
  explicit TWO-branch table — `(s=mcr,t=target)` AND mirror `(t=mcr,s=target)` — both giving the SAME block
  delta, so `pairDelta` is symmetric. The ordered-pair sum therefore counts both `(mcr,uMain)` and
  `(uMain,mcr)`: R2 = `−2·mcr·Mf`, R3 = `+2·mcr·Sf`. The FACTOR 2 in `2·mcr·(Sf−Mf)` IS the two orientations.
- **DIAGONAL accounting:** R2/R3 pairs are `mcr × non-mcr` (different roles), so `s₁ ≠ s₂` always — proven
  explicitly (`mcr_uMain_disjoint`, `mcr_uCR_disjoint`); `interactionCount` never hits its self-pair `−1`
  correction on these blocks, so each oriented rectangle collapses to the CLEAN product `count·count`.
- **Joint disjoint-class rectangle** (`sum_iCount_rectangle_disjoint`): the missing JOINT marginal — for
  disjoint Bool classes P,Q, `∑_{s₁,s₂} [P s₁][Q s₂]·interactionCount = (∑_P count)(∑_Q count)`. This is the
  joint generalization of `sum_interactionCount_mcr_assign`; the earlier gap note (separable-only) is closed.
- **`sum_iCount_pairDeltaZ`** = the integer rectangle identity `∑ iCount·pairDeltaZ = 2·mcr·(Sf−Mf)`.
- **Real connection** (`totalPairs_expectedDeltaX_eq`): `totalPairs·E[ΔX] = ((∑ iCount·pairDeltaZ : ℤ):ℝ)`;
  on positive-count pairs (⟹ applicable ⟹ phase 0 under allPhase0) `topSplitStepDelta = (pairDeltaZ:ℝ)`
  via `topSplitStepDeltaZ_eq_pairDeltaZ_of_applicable` (the `topSplitXZ` localization), zero-count pairs vanish.
- **`freeDiff_eq_Mf_sub_Sf`**: `freeDiff = Mf − Sf` (`freeW = [uMain] − [uCR]`, multiset induction).
- **HEADLINE `rectangleResidual_of_allPhase0`** (`card≥2 ∧ allPhase0 ⟹ RectangleResidual`): assembles
  real-connection + integer-rectangle + `freeDiff=Mf−Sf` ⟹ `totalPairs·E[ΔX] = −2·mcr·freeDiff`.
- **`topSplitWindow_whp_rectFree`**: `topSplitWindow_whp_inward` with `hQ_rect` DROPPED (supplied internally).
  Final hypothesis surface: `Phase0Initial` + absorbing region `Q` carrying `allPhase0`/`card≥2`/`LedgerInv`
  (all protocol-provable: `LedgerInv` via `LedgerInv_init`/`LedgerInv_stepOrSelf`). NO counting residual left.

STATUS: the top-split balance (Doty §5.1 inward drift) is now hypothesis-free modulo the absorbing-region
construction of `Q` (which is itself protocol-provable from `Phase0Initial` + `NoAssignedMcrConfig`).

---

## ABSORBING-Q DISCHARGE via the killed engine — `Probability/KilledAffineTail.lean` (2026-06-10, 0-sorry axiom-clean)

`topSplitWindow_whp_rectFree` carries an absorbing `Q` (allPhase0, card≥2, LedgerInv).  The new
generic killed-affine engine removes the absorbing-window requirement:

- **`RoleSplitConcentration.topGate n := allPhase0 ∩ {card=n} ∩ NoAssignedMcrConfig ∩ LedgerInv`** —
  the killed gate.  All four conjuncts are one-step preserved: `allPhase0` (killed exit, via
  `det_phase0_exit`), `card` (`stepOrSelf_card_eq`), `NoAssignedMcrConfig`
  (`NoAssignedMcrConfig_stepOrSelf`), `LedgerInv` (`LedgerInv_stepOrSelf`).
- **`topGate_exit_bridge`** — the q=0 deterministic exit bridge: from a gate config whose CLOCK
  potential `Φ_clock < 1` (hence `noClockAtZero`), the real kernel cannot leave `topGate` (all four
  conjuncts preserved), so the `Gᶜ` mass is `0`.  EXIT threshold is the clock-potential threshold
  (a DIFFERENT potential from `coshPot`), i.e. the escape is exactly the Phase-0 clock-zero window.
- **`top_killed_cosh_tail`** — the b=0 killed MULTIPLICATIVE cosh tail
  `(killK_now^T)(some c₀){θ≤killΦ coshPot} ≤ (cosh s)^T·coshPot(c₀)/θ`, drift supplied by
  `coshPot_drift` + `inwardResidual_of_ledger` + `rectangleResidual_of_allPhase0` on `topGate`.  NO
  absorbing Q.  (b=0 is the clean special case of `killed_now_affine_tail`.)

Wire-up to a fully hypothesis-free `topSplitWindow` whp: compose `top_killed_cosh_tail`
(in-gate tail) with `real_le_killed_affine_tail_add_escape` (real ≤ killed + escape) and bound the
escape by the Phase-0 clock-zero window (Consumer 1 of the same file).  This is a mechanical re-cut
of the `windowDrift_tail` call-site — no new protocol math.  STATUS: engine + adapters DELIVERED
0-sorry axiom-clean; the call-site re-cut is the remaining packaging step.
