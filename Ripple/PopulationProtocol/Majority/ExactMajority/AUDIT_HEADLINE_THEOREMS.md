# Doty exact-majority (arXiv:2106.10201v2) — headline-theorem formalization audit

Status convention:
- ✅ **landed** — fully proven in Lean, 0-sorry, no un-discharged carried hypothesis.
- 🟡 **wired-partial** — the deterministic / structural half is proven; a per-step rate or numeric
  floor is carried as a SATISFIABLE hypothesis (not false ∀c).
- 🔴 **carried-core** — the genuine probabilistic concentration is carried as a hypothesis; the proof
  inside is the union-bound / drift shell only.

Global fact: the ExactMajority `.lean` tree has **0 `sorry`/`admit`/`axiom`/`native_decide`**. So
"formalized" here means: the theorem is STATED and its proof has no sorry — but the headline theorems
are CONDITIONAL on the carried atoms below. This audit is the worklist to make them unconditional.

---

## The headline theorems (the paper's main results)

| # | Paper result | Lean theorem | Status |
|---|---|---|---|
| H1 | **Thm 3.1 — O(log n) time + correctness whp** (`E[T] ≤ 369 n(L+1)`, whp `T ≤ 21 C0 n(L+1)`, err `≤ 21/n²`) | `FinalAssemblyV7.doty_theorem_3_1_expected_v7` / `_whp_v7` | 🔴 conditional on `DotyResidualAtoms` |
| H2 | **O(log n) states (space)** | structural (`AgentState L K`, O(L) states by construction) | ✅ by construction (no separate thm needed) |
| H3 | **Stability (correctness w.p. 1 at the limit)** | inside H1 (`majorityStableEndpoint`, `StableDone` absorbing) | 🔴 conditional on the leak/endgame atoms |

H1 is THE headline. Its proof (`FinalAssemblyV51`→`V7`) is a verified assembly; everything below is its
carried hypothesis surface (`DotyResidualAtoms`).

---

## The carried surface of H1 — the cleanup worklist (the `DotyResidualAtoms` atoms)

### A. The 11 per-phase WORK-slot atoms (`WorkInputsV51`)

| Phase | Paper lemma | Lean field(s) | Status | Discharge path |
|---|---|---|---|---|
| 0 | Lemma 5.1 — role-split εfloor Chernoff | `work0` | 🔴 carried-core | `RoleSplitConcentration.phase0_roleSplit_whp_two_stage` lands det. count; the `FloorPrefix` Chernoff (`∑_τ P(assignableCount<a₀)`) is the carried core (concurrent Rule-4 −2 drain). |
| 1 | Lemma 5.3 / Mocquard avg-drain | `hescW1,hext1H,hpull1H,hpt1,hescε1` | 🟡 wired-partial | `Phase1SurvivalContracting` + `AveragingRate`/`PartnerMargin`; partner-pool floor carried. |
| 2,9 | Phase-2 opinion-window epidemic | `work2,work9` | 🟡 wired-partial | `WindowConcentration.windowDrift` (rate proved inside the carried instance). |
| 3 | **§6 CLOCK** (Thm 6.9) | `work3` (`HourComposition.phase3Convergence`) | 🔴 carried-core | **THIS SESSION**: reduced to `clock_real_faithful_honest`'s 3 inputs (hH/hfloor/hQ). The clock-front C-A is BUILT; wiring honest-clock → work3 atom is the cleanup. |
| 4 | Phase-4 advance epidemic tail | `hε4` (s4,t4,ε4) | 🟡 wired-partial | `Epidemic`/`EpidemicTime` numeric, proved inside. |
| 5 | Lemma 7.1 sampled-class + Thm 6.2 bias-ledger + reserve drain | `hstep5,hConc,hConfine` | 🔴 carried-core | `SampledClassTail` MGF drift landed; rise-floor `hrfloor` + clock-timing escape carried. `Theorem62Paper` 3 whp fields feed `hConfine`. |
| 6 | Lemma 7.2 band per-level | `hdrop6` | ✅ landed | floor FULLY landed from the Phase-5 Post. |
| 7 | Lemma 7.4 gap-1 eliminator | `hstep7,hPhase6Post7` | 🟡 wired-partial | minority-witness half PROVED; eliminator-count lower bound carried (`slot7_levels_hdrop`). |
| 8 | Lemma 7.6 above-level eliminator | `hstep8,hPhase7Post8` | 🟡 wired-partial | likewise; honest survival re-cut α₈'=14/75 (`BranchAndBudget`). |
| 10 | Phase-10 block-geometric | `hsB10` | ✅ landed | proved inside `Phase10Drop`. |

### B. The seam feeders (10 inter-phase advance/no-overshoot guards)

| Field | What | Status |
|---|---|---|
| `hDrift` (advance-epidemic) | seam phase k→k+1 opinion/clock epidemic | 🟡 WIRED for seams {1,6,7,8} (`SeamPairAdapter`); 🔴 carried for {2,3,4,5,9} |
| `hNoOvershoot` | seam doesn't skip past target phase | 🟡 same: {1,6,7,8} wired, {2,3,4,5,9} carried |
| `hSeedStep`, `hWorkPostToWindow`, `hWindowToWorkPre` | structural window bridges | 🟡 mostly wired (`SeedTrigWiring`/`AssemblyBridges`) |

### C. Leak / endgame / Phase-5 reserve (H1 + H3)

| Field | What | Status |
|---|---|---|
| `hLeak` | `∑_t P(off-good ∩ not-done) ≤ Bleak` | 🔴 carried-core (the recovery-leak concentration) |
| `hOnGood`, `hDoneAbs` | on-good-slot classifier + StableDone absorbing | 🟡 structural, partly wired |
| `hPhase5,hMainFloor,hConf,hP5` | reserve sampling / main-count concentration | 🔴 carried-core (`ReserveSampling`/`MainExponentConfinement`) |

---

## Cleanup order (tractable → hard)

1. **Wire the ✅-landed atoms that aren't yet connected** (slot 6 `hdrop6`, slot 10 `hsB10`) — confirm they need no carried input.
2. **§6 clock (slot 3)** — connect this session's `clock_real_faithful_honest` to the `work3` atom (the honest clock is built; this is wiring + discharging its 3 inputs hH/hfloor/hQ via the seed engine + the front-shape concentration).
3. **The 🟡 wired-partial atoms** (phases 1,2,4,7,8 + seams {1,6,7,8}) — discharge the carried per-step rate / numeric floor (each a single Chernoff/MGF tail).
4. **The 🔴 carried-cores** (phase 0 Lemma 5.1, phase 5 Lemma 7.1 + Thm 6.2, the leak, the reserve sampling, seams {2,3,4,5,9}) — the genuinely-hard concentration proofs; the deepest remaining content.

Each = one commit, verified on uisai2 (`lake build <module>`), `#print axioms` clean.

---

## REFINEMENT after verifying the fields (2026-06-14)

A `WorkInputs` field is one of THREE kinds — only the third is real work:
1. **Parameter-choice conditions** (`hsB10 : 6n²(1+2log n) ≤ s10`, `hs10`, the `t*/s*/ε*/η*`
   scalars + their `hescε*`/`hpt*` budget inequalities). Satisfiable BY CONSTRUCTION — the user picks
   the horizon/budget large enough; discharges by `norm_num`/`positivity`. NOT carried cores. The
   ✅-landed slots (6, 10) and most 🟡 budget fields are this kind once their probabilistic supplier
   is in place.
2. **Structural window bridges** (`hWorkPostToWindow`, `hWindowToWorkPre`, `hSeedStep`,
   `hPost2Win`/`hWin2Pre`) — deterministic phase-pin facts; mostly wired (`AssemblyBridges`,
   `SeedTrigWiring`), the rest are finite case-checks.
3. **The genuine probabilistic CORES** (the only real remaining math) — these are the worklist:

   | Core | Paper | Lean carrier | Note |
   |---|---|---|---|
   | C0 | Lemma 5.1 role-split εfloor Chernoff | `work0`'s `FloorPrefix` | concurrent Rule-4 −2 drain |
   | C3 | **§6 clock (Thm 6.9)** | `work3` | **honest reduction BUILT this session** → `clock_real_faithful_honest`(hH/hfloor/hQ); hfloor/hQ ⟸ seed engine, hH ⟸ front-shape (items 1/2 + gate-exit, the C-A files) |
   | C5a | Lemma 7.1 sampled-class | `hConc` | `SampledClassTail` rise-floor `hrfloor` |
   | C5b | Thm 6.2 bias-ledger | `hConfine` | `Theorem62Paper` 3 whp fields |
   | C5c | reserve sampling | `hPhase5,hMainFloor,hConf,hP5` | `ReserveSampling`/`MainExponentConfinement` |
   | CL | recovery leak | `hLeak` | `∑_t P(off-good ∩ ¬done)` |
   | CS | seam epidemics {2,3,4,5,9} | `hDrift,hNoOvershoot` | per-seam advance-epidemic tail (`SeamEpidemics`/`Epidemic`) |

   ~7 genuine cores. Everything else is parameter-choice or structural (mechanically dischargeable).
   C3 is the most advanced (honest reduction done this session); CS and C5a/b are single Chernoff/MGF
   tails; C0, CL, C5c are the deepest. THIS is the precise "逐个清理" worklist.

---

## CLEANUP PROGRESS (2026-06-14, plan: C3+CS+C5a/b mine, C0/C5c/CL dispatched)

- **C3 §6 clock — hside bridge DONE + VERIFIED** (`ClockPhase3Hside.phase3_hside_from_feeders`):
  `phase3Convergence`'s only real carried core, `hside : ∀ T τ, (realκ^τ) Sgood(T)ᶜ ≤ εside`, is now
  discharged to the four C-A feeders via `sidePrefix_le` (εsync/εphase ⟵ `sync_phase_via_union` ⟵ the
  C-A front-shape; εfloor ⟵ `FloorFail_horizon_le`; εQ ⟵ `qmixFail_le`). The §6 clock atom now routes
  to this session's verified front-shape. REMAINING for C3 = the feeders' own leaf inputs (per-step qE,
  W-maintenance, per-level εWindow) = the C-A concentration content (items 1/2 + gate-exit, carried
  satisfiable) + phase3Convergence's numeric hεb/hεtot (norm_num).
- NEXT: CS seam epidemics (mine, single tails), C5a/b (mine), and the deep-core dispatches C0/C5c/CL
  (ChatGPT/Codex per direction — precise briefs to be prepared: each is a full paper-lemma
  concentration over the connector repo).

## CLEANUP PROGRESS (2026-06-14 cont.) — CS already-done + CL leaf VERIFIED

- **CS seam epidemics — ALREADY DISCHARGED (audit was stale).**  Verified `SeamDischarge.lean`:
  `seamDischarge_hDrift` builds the WHOLE `∀ (k : Fin 10)` drift field at the genuine `1/n²` epidemic
  budget (`seam_drift_inv_sq` ← `SeamEpidemics.seam_drift` Phase-4 clone + `epidemicBudget_calibrated`),
  inputs = per-seam rate `s k > 0` + Θ(log n) horizon fit only — NO `{2,3,4,5,9}` special-casing.
  `seamDischarge_hNoOvershoot` builds the `∀ k` no-overshoot field from four HONEST satisfiable carries
  (`DetSeamOvershootBridge` = FROZEN-protocol structural fact; `hPreToNoOvershoot` = the timing-
  separation start carry the `≥`-window genuinely does not supply, instantiated from the real seam-entry
  trajectory — NOT a false ∀c; `hτ` Stage-4 at-risk tails; `hε` norm_num).  The monotone-decreasing
  clock-counter closure trap is AVOIDED via the cumulative prefix-union (hitting-time style).  Consumed
  by `FaithfulWitness → buildSeamHalf`.  The audit's "carried {2,3,4,5,9}" referred to the OLDER
  `FinalAssembly.lean` (`DotyAssembly'`) path, which the `SeamDischarge`/Faithful route supersedes.
- **CL recovery leak — honest leaf BUILT + VERIFIED + axiom-clean** (`OffEventEndgameReachable.lean`).
  The per-block `hLeak : ∀ b ∈ Doneᶜ, …` in `doty_theorem_3_1_expected_v4` is OFF-SUPPORT (the
  `OnGoodSlotClassifier` is honest only on the reachable good slice).  Replaced by the REACHABLE-relative
  leak at explicit `η = 1/4 < 1/2`: `hLeak_quarter_from_reachable_suffix_budget` reduces the genuine
  probabilistic content to ONE satisfiable carry `hRecoverToGood` (reachable-only recovery-to-good
  suffix concentration), via the CK lift `block_escape_of_suffix_escape_on` (Chapman–Kolmogorov +
  `reachableFrom_kernel_closed` + `pow_compl_inv_eq_zero_eh`/`bad_antitone_le_on`) and the reachable
  block combiner `leaky_block_half_on_reachable`.  `lake env lean` EXIT 0 on uisai2; `#print axioms` =
  {propext, Classical.choice, Quot.sound} only.  REMAINING for CL = (a) supply `hRecoverToGood` (the
  one real recovery concentration), (b) re-thread the endgame consumer to the reachable-relative shape
  (swap `leaky_block_half_on` → `leaky_block_half_on_reachable`).
- IN FLIGHT: deep-core dispatches — CL (family3) DELIVERED (this leaf).  C5c (family2) re-emitted the
  EXISTING C-A gate-exit work (tab carries heavy C-A context) + 4 new gate-failure decomposition hooks
  (`ampActive/active63/ghostActive_compl_subset` + monotone variant) staged for a later C3-wiring pass.
  C0 (family1, Lemma 5.1 role-split Chernoff) still cooking.

## CLEANUP PROGRESS (2026-06-14 cont.2) — C3 hooks + C5c Brick-A/B VERIFIED

- **C3 gate-failure hooks — BUILT + VERIFIED** (`ClockGateFailureSplit.lean`): `ampActive_compl_subset`,
  `active63_compl_subset`, `ghostActive_compl_subset` route the gate-exit `εExit` (from
  `ClockStoppedTransfer`'s first-exit/prefix-union) to the NAMED Layer-C state-local failures
  (`¬ClockP3`/`¬Aux`/`X<θ`/`ρ<X`/`η<Dfrac`/clean-cap/card/count).  Pure set-inclusions; the never-built
  `not_le`/contradiction mismatches in the ChatGPT draft fixed.  axiom-clean.
- **C5c — STRUCTURE FULLY DISCHARGED** (family3 task f31c7abd, audited):
  - **CK keystone** (`CKChainBound.lean`): `ck_bad_extend` (one CK extension step) + `ck_chain_bad_bound`
    /`_lt` (finite gated-window union).  The honest backbone — `Phase5AllWin` is NOT kernel-closed
    (`Phase5ClosureFalse`), so the closes are CK unions over good gates, not pointwise.  axiom-clean.
  - **Brick A** (`MainConfinementHours.lean`): discharges Theorem-6.2's carried `hHourTail` —
    `MainHourSquaringAtom` (per-hour MGF squaring, `hdrift`/`hbudget` gated on the hour-local `Q`) →
    `hour_tail_of_squaring_atom` (via landed `main_profile_hour_squaring`) →
    `main_confinement_tail_from_hour_atoms` (iterate the `O(L)` hours via `ck_chain_bad_bound_lt`) →
    `theorem6_2_main_confinement_whp_from_hours` (end-to-end into the existing headline).  This is C5b
    (Thm 6.2 confinement) too.  axiom-clean.
  - **Brick B** (`MainCountFloor.lean`): the honest `hMainFloor` —
    `mainFloor_tail_from_roleSplit_and_survival` composes the landed role-split tail with the Main-floor
    survival via `ck_bad_extend`; `MainFloorSurvival` reduces to one `MainFloorBennettAtom` (one-sided
    Main-loss MGF, gated on `Gate ⊇ RoleSplitGood`) via `windowDrift_tail`.  axiom-clean.
  - REMAINING for C5c = the irreducible atom fields (`MainHourSquaringAtom.hdrift/hbudget`,
    `MainFloorBennettAtom.hdrift/hbudget`) — the genuine per-step MGF/Bennett contractions, now honestly
    isolated as GATED satisfiable carries (the same tier as CL `hRecoverToGood` / C5a
    `clockSeparationEscape`).  The reserve-sampling side (`hPhase5`) was already wired via `OneSidedCancel`.
- **family2 — DEAD for dispatch** (C-A-locked tab): 3 attempts incl. hard reset all answered C-A; latest
  drip-immigration draft carries an `exact le_rfl` stub in `imm_bennett_exp_drift` — NOT adopted.
- NET: every genuine core is now either fully discharged (C3, CS, C5c-structure, CL-structure) or honestly
  reduced to a NAMED gated satisfiable concentration carry (C0 dispatched; the MGF/Bennett atom fields;
  CL `hRecoverToGood`; C5a `clockSeparationEscape`).  No axiom/sorry anywhere.

---

## ⚠️ FORMAL-STATEMENT BUG (2026-06-15) — `Phase0Initial` is too weak (C0 audit) — ✅ RESOLVED

**Status: CONFIRMED bug in the Lean formalization (not the paper); ¬-theorem + fix BOTH LANDED and
verified axiom-clean (commits `8948103e`, `aa006a54`). Headline was always sound; gap now closed at the
statement level too.**

### The bug
`RoleSplitConcentration.lean:166`:
```lean
def Phase0Initial (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Multiset.card c = n ∧ ∀ a ∈ c, a.phase = 0 ∧ a.role = .mcr
```
constrains `phase` and `role` but **OMITS the freshness field** `∀ a ∈ c, a.assigned = false`.
Doty et al. Lemma 5.1 initializes every agent genuinely fresh (`assigned = false`); the paper is
correct — the Lean initializer dropped that constraint.

### Why it's a soundness gap (mechanism, verified)
- Rule 2 (`Transition.lean:365`) fires only on `… ∧ ¬ t1.assigned`; Rule 3 (`:379`) only on
  `… ∧ ¬ t2.assigned` — the one-sided MCR-absorption rules REQUIRE an unassigned partner.
- Rule 1 (`:358`, two MCR → Main + CR) PRESERVES the input `assigned` flags.
- ⇒ from an all-`assigned = true` start, after Rule 1 fires once the config is stuck at
  `{assignedMain, assignedCR, assignedMCR}`: the lone remaining MCR can never be absorbed (every
  partner is assigned), so `roleMCRCount ≥ 1` forever, and `RoleSplitGood` (which demands
  `roleMCRCount = 0`) is UNREACHABLE.

### Consequence
The intended UNCONDITIONAL C0 bound `roleSplitTail η n tRole c₀ ≤ 1/n²` over `Phase0Initial` is
**provably FALSE**: the witness `poisonedCfg3` (three `role=.mcr, assigned=true` agents) satisfies
`Phase0Initial 3` yet has `roleSplitTail η 3 t poisonedCfg3 = 1 > 1/9` for all `t`.

### Scope — the assembled headline is NOT unsound (the REAL start IS fresh)
The headline's actual initial-config predicate is `validInitial` (`Analysis/MainTheorem.lean:101`),
which **DOES enforce** `a.assigned = false` (line 103) — alongside `phase = 0`, `role = .mcr`,
`opinions = 0`, and the input→smallBias map. So the real protocol start is genuinely fresh and the
assembled headline is **sound**.

The bug is precisely the **lossy bridge** `validInitial c₀ → Phase0Initial n c₀`
(`FaithfulDischargeTierA.lean:139`): it WEAKENS the strong `validInitial` down to the too-weak
`Phase0Initial`, **discarding the `assigned = false` fact**, so the C0 atom's `Pre` (= `Phase0Initial`)
no longer remembers freshness. `phase0_roleSplit_whp` then carries `(hbudget : roleSplitTail ≤ εRole)`
as a hypothesis over the weak `Phase0Initial` — fine for the *conditional* assembly, but the
*unconditional discharge* of that hypothesis over `Phase0Initial` is the false thing. The formalization
caught it BEFORE any false lemma was proved (the honest "证不过去先查定义" outcome).

Because `validInitial` already has `assigned = false`, the fix is clean and provable:
`validInitial → Phase0InitialFresh` holds trivially, so re-stating the C0 atom's `Pre` / the bridge over
`Phase0InitialFresh` (instead of `Phase0Initial`) closes the gap with NO soundness change to the
assembled theorem.

### Fix (decided 2026-06-15: formalize the ¬-theorem + strengthen) — ✅ LANDED, both files VERIFIED axiom-clean

1. **Counterexample formalized** — `RoleSplitPhase0Counterexample.lean` (commit `8948103e`):
   `poisonedCfg3_never_good (η t : …) : (K^t) poisonedCfg3 {¬RoleSplitGood η 3 ·} = 1` (absorbing-invariant
   proof: a `PoisonedAuditQ` step-closed invariant + `Protocol.ae_of_stepDistOrSelf_support_preserved`) and
   `phase0Initial_too_weak : ∃ c₀ η t, Phase0Initial 3 c₀ ∧ ofReal(1/9) < roleSplitTail η 3 t c₀` (witness
   `poisonedCfg3`, `t=1`, tail `= 1`). Both `#print axioms = {propext, Classical.choice, Quot.sound}`.
   Permanent documentation of the gap (parallels `¬Cf24BasinEntry`, PP→NAP `StrictNoSelfProduction`).

2. **Initializer strengthened** — `Phase0InitialFresh.lean` (commit `aa006a54`), purely additive (the FROZEN
   `Phase0Initial` interface and its ~40 consumers are untouched — `TopSplitInward:638` deliberately chose
   not to strengthen it):
   - `Phase0InitialFresh n c := Phase0Initial n c ∧ ∀ a ∈ c, a.assigned = false`, with the forgetful
     `.toPhase0Initial` projection (every weak-`Phase0Initial` lemma still fires from the fresh start).
   - `phase0InitialFresh_of_validInitial` — the real Doty start (`validInitial`, which pins `assigned=false`)
     satisfies it: the freshness-PRESERVING replacement for the lossy `FaithfulDischargeTierA.lean:139`.
   - `noAssignedMcrConfig_of_phase0InitialFresh` — the PAYOFF: `NoAssignedMcrConfig` (carried explicitly
     throughout `TopSplitInward`/`KilledTailConsumers` *because* it does not follow from the weak
     `Phase0Initial`) is now a one-line consequence of the strengthened start.
   All three `#print axioms = [propext]` only.

The genuine remaining C0 concentration work (unchanged by this fix) is the two probabilistic inputs the
file already isolates: the `assignableCount` floor under the concurrent Rule-4 −2 drain, and
`RoleSplitWindows` (Main ∈ (1±η)n/2, Clock/Reserve ≥ (1−η)n/4) — no shortcut.

Provenance: surfaced by the C0 dispatch (family, task 14ce41dd — which had been silently queued to the
non-existent channel `family1` until re-fired to `family`); proofs drafted by ChatGPT (family, tasks
14ce41dd/bfaeb583), audited + repaired against the real defs (docstring/`set_option` ordering, `countP`
cons-form evaluation, `IsMarkovKernel` via `CKChainBound.isMarkov_pow`, multiset `add_tsub_cancel_left`,
bridge destructuring) before adoption.
