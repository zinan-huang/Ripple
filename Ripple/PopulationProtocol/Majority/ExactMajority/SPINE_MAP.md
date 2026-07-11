# ExactMajority — THE SPINE MAP (脉络)

_What we are proving, the live thread, and the dead code. Authored 2026-06-16 during consolidation._

## 0. THE GOAL (one sentence)

Doty et al. **Theorem 3.1**: the `NonuniformMajority` population protocol, from any valid
initial config of `n` agents (Doty regime), reaches a **stable, correct-majority endpoint**
(`majorityStableEndpoint`) with probability **≥ 1 − 21/n²** within **T = O(n log n)** steps.

`majorityStableEndpoint init c` ⇒ `output = majorityVerdict init ∧ IsStable c`
(`StableEndpoints.stable_output_of_majorityStableEndpoint`).

## 1. THE AUTHORITATIVE HEADLINE

**`FaithfulCoreDischarge.doty_theorem_3_1_fully_unconditional`** — the SOUND one.
It conditions only on `DotyRegime` + `validInitial c₀` + `card c₀ = n` + `FaithfulWorkSeamCore`
+ the per-phase calibration fits (`hT`/`ht`/`hε`). Conclusion = the 21/n² bound + the two
O(n log n) time bounds.

RETIRE (vacuous — carry the FALSE universal `hReach10 : ∀ c, Phase10Post c → Reachable c₀ c`):
- `FaithfulWitness.doty_theorem_3_1_unconditional`
- `DotyMinimalCapstone.doty_theorem_3_1_minimal`

The skeleton is PROVEN: the `∑ε ≤ 21/n²` fold, the `O(n log n)` time, and
`reachable-post ⇒ majorityStableEndpoint` (chain-restricted, no false universal).

## 2. THE CONTRACT — `DotyAssembly'` (SeedTrigWiring), 21 phases

`dotyPhases' = [work₀, seam₀, work₁, seam₁, …, work₉, seam₉, work₁₀]`
= **11 work atoms** (`work : Fin 11 → PhaseConvergenceW`) + **10 seam atoms**
(`seamP/seamT/εepidemic/εovershoot/hDrift/hNoOvershoot` + bridges).

**THE MISSING FINAL WIRING**: no concrete `DotyAssembly'` is assembled and plugged into the
headline. The `FinalAssembly*` files thread an *abstract* `work` field. Completing the proof =
build ONE concrete `DotyAssembly'` (pick one discharger per atom) → feed the headline.

## 3. ATOM DISCHARGERS (consolidate to ONE per atom)

**Work layer — `WorkConstructed.lean` has the COMPLETE `work0`–`work10`** (the intended single
source). Each still CARRIES the convergence residuals `hClock`/`hHdrift`/`hStruct`/`hLeak` as
hypotheses — those are what layer-4 discharges.
DUPLICATE FRAGMENTS to prune: `ClockStructGateDischarge` (work1/5/6/7/8_clockstruct_gated),
`BudgetGateDischarge` (work1/5/6/7/8_gated), `PkgFAtoms` (work0/2/3/9_*), `Slot24Discharge`
(work2/4_expBudget), `WorkInputsV51Slots24910` (work2/4/9/10_*).

**Seam layer** — `SeamDischarge.buildSeamHalf` + `SeedTrigWiring.seamWithSeed` (epidemic +
no-overshoot, genuine 1/n²). One source.

## 4. RESIDUAL DISCHARGERS (what fills hClock/hHdrift/hStruct/hLeak per work atom)

| atom | Doty phase | residual source (live) | status |
|------|-----------|------------------------|--------|
| work0 | 0 role-split | CascadePhase01 / RoleSplit* | — |
| work1 | 1 | Phase1SurvivalContracting | drift ok; clock tail = §clock |
| work2,4,9 | 2,4,9 epidemic | EpidemicConvergence (1/n²) | calibrated |
| work3 | 3 | (phase-3 bounded) | — |
| work5 | 5 reserve-sample | GatedDrainContracting + Phase5 | drain ok; clock tail = §clock |
| work6 | 6 reserve-split | Phase6SurvivalContracting + **Phase6ShiftedDrainDrift** (drain m=0 DONE) | clock tail = §clock |
| work7,8 | 7,8 | Phase78SurvivalContracting | clock tail = §clock |
| work10 | 10 sign/majority | Phase10SignResolved | — |
| seams 0–9 | inter-phase epidemic | SeamDischarge | 1/n² |

**§clock (cross-cutting hClock)** = the per-phase clock-positivity tail. AUTHORITATIVE route =
`ClockDepletionCoupling.mgf_depletion_tail_uniform` → `ClockCounterSurvival.survival_union_bound`
(per-clock Chernoff + union, genuine sub-unit). The honest clock theorem =
`ClockRealFaithfulHonest.clock_real_faithful_honest`, assembled from 4 side-prefix terms
(`ClockUnconditional`: Sgoodᶜ = QmixFail ∪ FloorFail ∪ SyncFail ∪ PhaseGateFail). The C-A
front-shape frontier (HANDOFF_CA: Bennett immigration / MGF amplification / FloorFail seed-leg /
Layer-D first-exit) discharges the SyncFail term.

## 5. DEAD / TO PRUNE (after the wiring is fixed)

- 7 superseded final assemblies: `FinalAssemblyV2,V3,V4,V5,V51,V6,V7` (~5–6k lines; entangled by
  incidental lemma reuse → refactor-extract then delete).
- The 2 vacuous capstones (§1).
- The `counterDepthMass` clock-tail DETOUR (hollow trivial-escape η=2): `CounterDepthJump`,
  `CounterDepthDrift`, `CounterDepthGatedTail`, `Slot6HClockClosed`, `Slot6SurvivalAssembled`
  (the last two authored this session before the route was found hollow) — superseded by §clock.
- Duplicate work-constructor fragments (§3).

## 6. THE ONE NEXT STEP

Build `DotyAssemblyConcrete.lean`: assemble `WorkConstructed.work0..work10` (residuals discharged
by layer-4) + `SeamDischarge` seams into a concrete `DotyAssembly'`, feed
`doty_theorem_3_1_fully_unconditional`. That single file DEFINES the live spine and EXPOSES
everything in §5 as deletable. Cleanup-by-finishing.

## 7. §3.3 VACUITY FINDING (2026-06-16) — the "reduced headline" rests on a FALSE hyp

`hPreToNoOvershoot : ∀ k c, (allPhaseGe (seamP k) n c ∧ advTriggered (seamP k+1) c) → NoOvershoot (seamP k) c`
is **FALSE as a blanket-∀** (REFUTED, my cross-check). NoOvershoot p c = ∀a∈c, phase<p+2. Counterexample:
c with all agents phase ≥ seamP k, one at seamP k+1 (advTriggered ✓), ONE overshot agent at phase
seamP k+3 → gate holds, NoOvershoot fails. Same shape as the retired-false hReach10.
⟹ DotyHeadlineConcrete / DotyHeadlineReduced are CURRENTLY VACUOUS through this carried hyp.
FIX: chain-restrict to reachable configs (∀ c, Reachable init c → gate c → NoOvershoot c) — true because
on reachable configs no agent jumps 2 phases inside a seam window (clock advances only at counter 0, just
reset). Mirror FaithfulCoreDischarge.reach10_chain_restricted. [family3 building PreToNoOvershootDischarge.]
OTHER SUSPECTS under audit: hreset (synchronized reset — not reachable as exact-R; weaken to counter≤R
band, family4), + the full carried-hyp set (adversarial audit on family). The carried-hyp SATISFIABILITY
audit is the real remaining hard work, NOT wiring. "sorry-free + axiom-clean" ≠ non-vacuous.

## 8. ADVERSARIAL AUDIT VERDICTS (ChatGPT family + my cross-check, 2026-06-16) — the REAL remaining work

The carried-hyp satisfiability audit found ~8 FALSE-as-stated blanket-∀ traps. The concrete-headline
chain (DotyHeadlineConcrete/Reduced) is VACUOUS through several. Repair = chain-restrict each to
reachable/support-local configs (mirror FaithfulCoreDischarge.reach10_chain_restricted).

FALSE (must repair):
- hPreToNoOvershoot — gate ⇏ NoOvershoot (overshot-config CE). → reachable first-exit no-overshoot.
- hAtRisk — τ=0 at-risk clock ⟹ (K^0)=1 > exp(-40(L+1)). → first-exit/stopped concentration.
- hdet (p=0) — phaseInit 1 sends mcr→phase10; missing WellFormedNoError premise. → add side cond.
- Phase6ClockTail.hcap (∀c count≤m) — refuted by m+1 copies. → support-local (card=n ⟹ ≤n).
- Phase6ClockTail.hcover (¬WinN ⊆ ⋃ depleted) — ¬WinN has card/phase failures. → reachable-horizon.
- Phase6ClockTail.hcard (∀c 2≤card→card=n) — refuted by card n+1. → support card-preservation.
- DotyAssemblyConcrete.hSeedStep, hWindowToWorkPre — pointwise from bare Post/exact-phase. → reachable
  seam-entry distributions / strengthen work Post.
- FloorFailSeedLeg.hPersist — range H incl pre-seed τ=0 (FloorFail=1). → window Ico tseed H.
- Phase6ClockTail.hreset — async entry gives positivity/band, not common-R. → counter-band start.
SATISFIABLE (ok): hTdrift, hStatic, hCross, hFloor, hSync, hSeedEnd, hFront, hBulk, hWindowMass,
hsmall, hLeak, hcoverDrain (per-slot), hClock (with band handoff).
REPAIR PRIORITY: (1) seam layer (hPreToNoOvershoot+hAtRisk first-exit, hdet well-formedness),
(2) Phase6ClockTail hcover/hcap/hcard → support-local + hreset → band, (3) DotyAssemblyConcrete
bridges → reachable. This needs the Reachable/support-local infra; it is the genuine hard math.

## 9. CODEX FINAL-AUDIT VERDICT (2026-06-16) — headline NOT sound; the genuine remaining work

doty_theorem_3_1_fully_migrated builds axiom-clean BUT is VACUOUS / carries hidden false universals
(Codex full-strength adversarial audit; my "no live blanket ∀c" grep was insufficient — the false
universals are inside the residual DEFINITIONS, and there are budget/timescale CONTRADICTIONS my grep
never checked). 实事求是: the individual repairs landed as files, but the headline integration is NOT
a sound non-vacuous theorem.

HARD CONTRADICTIONS (unsatisfiable hyp sets → vacuously true → worthless):
1. hε vs seam: concreteAsmSeamMigrated fixes εepidemic=1/n²; seam ε = εepidemic+εovershoot; hε wants each
   phase ε ≤ 1/n² → forces εovershoot=0. But hRatePos+hTdrift force seamT>0 → εovershoot>0. UNSAT.
   (HeadlineSeamMigrated:267, SeedTrigWiring:246, HeadlineBridgesMigrated:160)
2. hTdrift vs hShort: hTdrift ⟹ seamT ≥ 2n·log n; hShort wants seamT ≤ n(L+1); regime L+1 < 2 ln n →
   impossible. Independent of #1.

HIDDEN FALSE UNIVERSALS (the "reachable" residuals lack reachability guards):
3. hReachPost/hReachWindow: false GLOBAL reachability covers — upgrade reachable residuals back to
   all-config (every work.Post c reachable). AssemblyBridgesReachable lists these as UN-solved extra
   assumptions, not facts. (AssemblyBridgesReachable:340)
4. SeamBridgeFailureZeroWindowResidual: quantifies all seam-pre c, NO Reachable guard → malformed c gives
   (K^0)c=1, gate fails. (ConcreteResidualsMigrated:22)
5. SeamTriggerEntryResidual: derives NoOvershoot from allPhaseGe∧advTriggered, NO reachability guard →
   same overshot-config CE as original hPreToNoOvershoot. (ConcreteResidualsMigrated:16)
6. hReset: CounterResetDest allows q∈{1,6,7,8} only; standard seamP k=k needs {2,3,4,5,9} too → doesn't
   match the actual 10-seam chain. (SeamPairAdapter:76)

GENUINE REMAINING WORK (structural, careful, Codex-driven — NOT parallel spraying):
- Fix the εovershoot/(1/n²) budget split (separate seam ε accounting so εovershoot>0 fits).
- Reconcile the seamT timescale (hTdrift gives Ω(n log n), hShort wants ≤ n(L+1); the constants/scale
  are inconsistent — likely the seam horizon vs the per-phase budget needs re-derivation).
- Add genuine Reachable guards to SeamTriggerEntryResidual + SeamBridgeFailureZeroWindowResidual (chain-
  restrict like reach10), supplied by DetBridgeWellFormed.bridgeFailureSource_mass_eq_zero_family on the
  reachable image only.
- REMOVE hReachPost/hReachWindow (the global reachability cover); the headline closing map must use the
  chain-restricted reachability (FaithfulCoreDischarge.reach10_chain_restricted pattern), not a carried
  global cover.
- Split reset/non-reset seams (the hReset schedule).
LESSON: "axiom-clean + no-literal-∀c-in-the-theorem-signature" is NOT non-vacuity. Must unfold every
carried residual DEFINITION + check the carried-hyp set for joint SATISFIABILITY (no contradictions).
The individual landed repair files (ClockTailNoSync, AtRiskFirstExit, PreToNoOvershootDischarge, etc.)
are still genuine; the FAILURE is in the headline INTEGRATION (the migrated wrappers).

## 10. INDEPENDENT ANALYSIS of the two contradictions (parallel to Codex investigation)

Numbers verified from source: C0_numeral = 17 (AtomsV2:167); epiAlpha(s) = 1 − e^{−s} < 1 always
(EpidemicConvergence:93); hShort caps seamT ≤ n(L+1) — DROPS the C0=17 factor the real per-phase
budget (ht) carries (17·n(L+1)). seam phase ε = εepidemic+εovershoot (SeedTrigWiring:247,291),
εepidemic pinned 1/n² (HeadlineSeamMigrated:267).

#1 (ε budget): FIXABLE by budget-split. Halve εepidemic → 1/(2n²); εovershoot=seamT·e^{−40(L+1)}
   ≈ n log n·n^{−40c} ≪ 1/(2n²) fits; 21-phase union bound still ≤ 21/n². Need to recheck the
   epidemic drift hDrift still holds under 1/(2n²) (quantitative, likely yes). Real re-accounting.

#2 (timescale): NOT simple re-accounting — a genuine drift-bound issue. Because epiAlpha ≤ 1, the
   2 log n term ALONE forces seamT ≥ (n/epiAlpha)·2 log n ≥ 2n log n; and minimizing
   (n/epiAlpha(s))·(s(n−1)+2 log n) over the rate s gives Θ(n²) (small s: epiAlpha≈s ⟹ n/epiAlpha·2logn
   = Θ(n²); s=Θ(1): rate·(n−1) numerator ⟹ Θ(n²)). hShort wants Θ(n log n); even the full 17·n(L+1)
   ≈ 24.5 n log n budget can't absorb a Θ(n²) lower bound. ROOT CAUSE: hTdrift's formalized epidemic
   drift is Θ(n²), but a one-way epidemic on n agents is Θ(n log n) INTERACTIONS — the EpidemicConvergence
   drift lemma over-estimates (the rate·(n−1)/epiAlpha structure is the wrong scaling). FIX is in the
   epidemic-convergence layer (tighten the drift bound to n log n), NOT a constant tweak in the headline.
   => the headline is salvageable for #1 by re-accounting, but #2 needs a real epidemic-drift fix first.

## 11. CONVERGED VERDICT (Codex investigation + independent analysis agree) — 2026-06-16

#1 ε-budget: FIXABLE. Underlying doty_time_composition_W2 / BudgetTightening.doty_time_headline_W2_tight
   are SUM budgets (∑phaseε ≤ C/n²). The migrated wrapper (HeadlineBridgesMigrated:160,
   FaithfulCoreDischarge:272) needlessly specialized to per-phase ≤ 1/n² AND locked all slots at full
   1/n² (no slack for seam εovershoot). FIX: carry aggregate ∑δᵢ ≤ 21/n² (or bump final C/n²), don't max
   every slot — seam positive overshoot absorbed by slack. Tactical wrapper rewrite, the lemma exists.

#2 seam-epidemic timescale: GENUINE DESIGN PROBLEM (not re-accounting). Both hTdrift & hShort are
   sequential interaction counts on the same seamT (NOT a parallel/interaction unit confusion).
   hTdrift = (n/epiAlpha s)·(s(n−1)+2 log n) (SeamDischarge:80), epiAlpha=1−e^{−s}≤1 ⟹ seamT ≥ 2n ln n;
   s(n−1) term ⟹ Θ(n²) min. hShort (no-overshoot tail window, NOT the loose 17n(L+1) cap) wants
   seamT ≤ n(L+1) ≈ 1.44 n ln n. Order-incompatible. ROOT: the formalized seam-epidemic drift bound
   over-estimates convergence as Θ(n²) when the paper's one-way epidemic is Θ(n log n) interactions.
   SALVAGE ROUTES (Xiang's strategic call — a seam-layer redesign, escalated):
   (A) tighten the seam-epidemic drift (EpidemicConvergence/SeamDischarge) to a paper-faithful
       O(n log n)-interaction tail with constants that fit the no-overshoot window; OR
   (B) prove the no-overshoot tail over the LARGER actual seam horizon (~Θ(n²) or the real drift time),
       i.e. don't force seamT ≤ n(L+1) — re-derive εovershoot over the true horizon.
   Route A is paper-faithful (the protocol IS O(n log n)) and the right target; Route B salvages the
   current drift lemma but inflates the total time bound above O(n log n) (breaks the headline's
   T ≤ 21·C0·n·(L+1) claim) — so A is the real fix, B is a fallback that weakens the time theorem.

CAMPAIGN STATE: the §3.3 vacuity audit is COMPLETE and successful as an AUDIT — it found, and the
verify-discipline confirmed, that the headline is not yet a sound non-vacuous theorem. The individual
repair files are genuine. The remaining work is now PINPOINTED to two concrete obstructions (#1 tactical,
#2 a named epidemic-drift redesign), not a vague "hard". That is the honest culmination.

## 12. INTEGRATION revealed 2 more foundation lemmas (Codex honest block, NOT faked) — 2026-06-16

doty_theorem_3_1_janson_integrated NOT written — Codex found the integration needs 2 foundation layers
first (correct decomposition, no faking). Caught an error in my "relax hShort" claim:
- seamJansonT ≤ 11n(ln n+1) but n(L+1) ≈ 1.44 n ln n → Janson window is ~7.6× longer than n(L+1).
- Extending the seam window to ~11n ln n BREAKS clock-survival no-overshoot: the clock counter (sized
  for n(L+1) steps) depletes in the longer window. Codex numerics: log-ratio ≈6580 at t=17n(L+1), s=1.
  I only checked εovershoot (tiny); MISSED that clock-survival also depends on window length. Codex right.
- Also: sum-budget can't discharge from current SlotCalib — work-phase ε are arbitrary fields
  (WorkConstructed:388,536), no proven "work ε ≤ 1/n²" / work-slack theorem.

TWO FOUNDATION LEMMAS (next single lines, independent):
(A) small-rate C0-horizon no-overshoot CLOCK-TAIL: clock survives the ~11n(ln n+1) Janson window
    (redo seam_noOvershoot_numerics_honest with small clock rate s / larger counter; current hard-codes
    t≤n(L+1) at HeadlineSeamMigrated:80, ClockZeroTail:147, SeamPairAdapter:892).
(B) Janson seam tail at ≤1/(2n²) (slightly larger constant horizon, still O(n ln n)) + a work-slack
    budget lemma (actual work ε ≤ 1/(2n²) or the real per-slot bounds) so ∑δ ≤ 21/n² genuinely holds.
THEN (C) wire seamDischarge_hDrift_janson + (A) + (B) into the integrated headline.
STATUS: #2 order obstruction SOLVED (Route A landed). #2 constant/window + #1 budget now reduced to (A)+(B).

## 13. 统筹 ChatGPT-Pro round (2 of 4 back) — STEERS, verified by Codex↔ChatGPT convergence — 2026-06-16

family (Chernoff clock sizing): R = Θ((m+1)·(L+1)). For the natural per-agent clock m=O(1): R ≈ 65(L+1)
   (70(L+1) with O(n)-clock union), Θ(log n) scaling — a CONSTANT enlargement from the protocol's 50(L+1),
   NOT Θ(log²n). EXACTLY matches Codex's proven fifty_depth_too_small. => clock-survival fix = enlarge
   seamCounterDepth 50→~70(L+1) (constant calibration) + support-local Chernoff (ReachableClockTail/
   Phase6ClockTailSupport). Tractable. Caveat: bigger counter → longer clock-fire time; constant, likely
   absorbed by C0=17 slack (10 seams·35n(L+1) ≈ 350n(L+1) < 357n(L+1) total budget — tight, recheck).

family3 (#3/#5 reachable-guards): the reach10_chain_restricted MIRROR is INSUFFICIENT. The gate
   allPhaseGe(p)∧advTriggered(p+1) is ONE-SIDED + PERSISTENT → "Reachable + gate" still includes POST-seam
   states. Two reachable CEs (cite phaseInit/stdCounterSubroutine/advancePhaseWithInit): (i) decremented
   counter kills SeamEntryFullCounter; (ii) counter→0 then advancePhaseWithInit makes a phase-(p+2) agent,
   killing NoOvershoot. => #3/#5 need a TIME-SLICED FIRST-ENTRY seam invariant (just-entered p+1, no agent
   yet at p+2, counter just reset), maintained by a window argument — NOT reachable+gate. Matches Codex's
   earlier SeamGatedNoOvershoot first-exit finding. Saves a doomed reach10-mirror dispatch.

PENDING: family2 (ComponentFits budget↔time), family4 (#6 reset/non-reset seam split).

## 14. MAJOR SCOPE FINDING (family2, VERIFIED against source) — Θ(n²) epidemic is NOT seam-only — 2026-06-16

family2 (ComponentFits) → verified at WorkConstructed.lean:24,101: the WORK epidemic slots 2/4/9 use
epiHorizon = ⌈(n/α)(s(n−1)+2 log n)⌉ = Θ(n²) (s=1 ⟹ ≈1.58n²) via epi_budget_fit. This CATASTROPHICALLY
violates ht ≤ 17n(L+1)=O(n log n) (1.58n² ≫ 2278n at n=10^40). So the headline's TIME bound was vacuous
on the WORK side too — not just the seams. The ENTIRE headline (ε AND time) was vacuous, all from one
Θ(n²) epiHorizon pervading work slots + (pre-Route-A) seams.

ALSO (family2 quantitative): tightening a slot's failure from 1/n² to (1/3)/n² costs an extra
(n/α)log 3 ≈ 1.74n interactions per epidemic slot — same order, absorbed by C0=17 slack (1.74n ≪ 2278n),
so ComponentFits's CONSTANT extra time is fine ONCE the underlying horizon is O(n log n).

FIX (uniform, mirrors Route A): re-point slots 2/4/9 from epiHorizon (Θ(n²)) to the tight O(n log n)
Phase2TimeConvergence (11n(log n+1)) epidemic — already built. Then slot time fits ht, and the +1.74n
ComponentFits cost is absorbed. The Θ(n²) epiHorizon and EpidemicConvergence.epidemicBudget_calibrated
(the MGF-uniform-1/n feeder) are the single root of the time vacuity EVERYWHERE.

REVISED repair tree: #2 (order) is the DOMINANT defect, pervading seams AND work slots 2/4/9. Route A
solved the seams; the SAME tight-epidemic re-point closes the work slots. Plus: clock-depth enlarge 50→70
(§13), time-sliced first-entry seam invariant for #3/#5 (§13, reach10-mirror INSUFFICIENT), #6 reset split.

## 15. #6 reset-schedule (family4, source-grounded) — SPLIT the seams — 2026-06-16

hReset : ∀k CounterResetDest(seamP k+1) is the WRONG abstraction. The natural seam schedule does NOT
reset all seams. Two distinct sets:
 - phaseInit resets counter at {1,5,6,7,8}; BUT phase 5 is DECEPTIVE — phase4→5 uses raw advancePhase
   (not advancePhaseWithInit), so phaseInit 5 doesn't run → clock CARRIES old counter. So usable
   fresh-full-counter resets = CounterResetDest = {1,6,7,8} (SeamPairAdapter:78-84).
 - non-reset destinations {2,3,4,5,9,10} carry the counter → need a CARRY-OVER no-overshoot argument,
   NOT the fresh-full-counter tail.
FIX: split the 10 seams — reset-seams {1,6,7,8} use the fresh-full-counter Chernoff tail; non-reset
{2,3,4,5,9,10} use a carry-over invariant (epidemic completes before the carried counter depletes).
Dovetails with #3/#5 (§13): the seam first-entry invariant must track whether the counter was reset.

=== COMPLETE VERIFIED REPAIR TREE (统筹 round, all 4 source-grounded) ===
ROOT: Θ(n²) epiHorizon + epidemicBudget_calibrated (MGF-uniform-1/n) — the single order defect.
#2 (DOMINANT): re-point ALL epidemic consumers (seams DONE via Route A; work slots 2/4/9 TODO) to tight
   O(n log n) Phase2TimeConvergence/Janson. [Codex A building]
clock: support-local Chernoff + counter 50→70(L+1) (Θ(log n), constant). [Codex B building]
#1 budget: ComponentFits satisfiable, +1.74n/slot absorbed by C0=17, ONCE epidemic is O(n log n).
#3/#5: time-sliced FIRST-ENTRY seam invariant (reach10-mirror insufficient; gate one-sided/persistent).
#6: split reset {1,6,7,8} (fresh tail) vs non-reset {2,3,4,5,9,10} (carry-over invariant).

## 16. #3/#5 first-entry invariant DESIGNED (family, source-grounded) — 2026-06-16

The fix is a TIME-SLICED ENTRY (transition/edge + endpoint shape), NOT a persistent Config predicate
(which always includes post-seam states). Two predicates:
 - SeamFirstEntryShape p n B c: card=n; all agents phase ∈ {p, p+1}; ≥1 at p+1; ≤2 at p+1 (one
   interaction changes ≤2 agents → 1-2 leaders, "exactly one" too strong); NO agent ≥ p+2; every p+1
   clock counter ≥ B; well-formed.
 - SeamFirstEntryEdge p n B c c': c is work-exit (allPhaseEq p, ¬advTriggered(p+1), well-formed); c' is
   one-step successor; advTriggered(p+1) c'; SeamFirstEntryShape p n B c'.
NoOvershoot holds AT entry by shape (none ≥p+2); MAINTAINED over the O(n log n) window by FIRST-EXIT:
overshoot to p+2 is clock-counter-DRIVEN (epidemic maxing alone can't create p+2 — SeamNoOvershoot states
this), and the clock survives the window (Codex B enlarged-counter Chernoff). SeamGatedNoOvershoot already
packages the first-exit. Compose with FaithfulCoreDischarge reachable-split (non-reachable mass 0).
=> #3/#5 discharge = define the shape/edge + prove NoOvershoot maintained via first-exit×clock-survival.
This UNIFIES #3/#5 (first-entry) + clock (Codex B) + #6 (B = reset 70(L+1) or carried lower bound).

## 17. #6 carry-over REFINED (family2, source-grounded) — split BY MECHANISM, not reset/non-reset — 2026-06-16

NO uniform "carried counter ≥ B>0" invariant exists. Non-reset seams split by MECHANISM:
 - RESET seams {1,6,7,8}: fresh-full-counter Chernoff tail (SeamEntryFullCounter, ClockZeroTail:83-118).
 - COUNTER-BLIND seams (most non-reset, e.g. 1→2, 2→3): the phase advances by its OWN mechanism not the
   counter — phase 2 by opinion-union "both signs" branch (Phase2Transition, counter floor B=0 harmless);
   phase 3 runs minute/hour first, stdCounterSubroutine only after minute threshold. No-overshoot guard =
   the work/opinion guard, NOT a carried-counter tail.
 - phase4→5 seam: THE genuine obstruction — carried counter can be 0 AND phase 5 runs the counter
   subroutine → real overshoot risk. Needs a dedicated argument (carried-counter-zero handling at 4→5).
=> #6 = per-mechanism classification: reset-tail {1,6,7,8} + counter-blind-guard {2,3,4,9,10} +
   phase4→5 special case. NOT a uniform reset/non-reset split.
NOTE: family4 (work-slot epidemic coverage x-check) TRUNCATED by bridge intro-only bug (384 B) — rely on
Codex A's own slot analysis instead.

## 18. TIME THEOREM — paper-faithful formulation (family, cites Doty Thm 3.1 + Lemma 7.7) — 2026-06-16
DECISION (Xiang): follow the paper. The paper's Thm 3.1 is a RANDOM STOPPING-TIME theorem, NOT a
worst-case phase sum. "stably computes majority in O(log n) stabilization time, in expectation AND w.h.p."
(time = PARALLEL time = interactions/n; O(log n) parallel = O(n log n) interactions).
 - W.h.p.: prob 1−O(1/n²) the FAST path (phases 0-9 + seams) stabilizes in O(log n) parallel time WITHOUT
   entering phase 10 (majority→stable by phase 9; tie→phase 4).
 - Backup (phase 10): Lemma 7.7 — stabilizes in O(n log n) parallel time, but entered w.p. O(1/n²) →
   expected contribution O(1/n²)·O(n log n) = o(1).
=> The Lean T = Σ over ALL 21 phases phase.t (always incl. phase 10's Θ(n²log n) interactions) is NOT
paper-faithful — it's a deterministic worst-case schedule-length artifact. The current ht (∀i phase.t ≤
C0·n(L+1)) is INHERENTLY FALSE for phase 10 and should not be carried.
FIX (time half of headline): reformulate as TWO paper-faithful statements:
 (i) W.H.P.: P[fast path stabilizes in ≤ C·n·log n interactions, not entering phase 10] ≥ 1 − 21/n²
     (the SAME 21/n² failure event as correctness — backup entry ⊆ failure event).
 (ii) EXPECTED: E[interactions to stabilize] ≤ C·n·log n + (21/n²)·O(n²log n) = O(n·log n).
 NOT a per-phase ht over all 21 incl. backup. Phase 10's time only enters via the rare-entry o(1) weight.
The FAILURE-PROB half (≤21/n²) is unaffected — it already IS the backup-entry event bound. The time and
correctness halves separate cleanly: correctness ≤21/n² always; time O(n log n) on the ≥1−21/n² fast event.

## 19. PIVOT — instantiate the EXISTING expected-time framework (Xiang caught it) + slots audit — 2026-06-16

KEY REALIZATION (Xiang's question): the time-complexity + phase proofs EXIST and are ASSEMBLED, but as
GENERIC frameworks carrying ht/hε as hypotheses, NEVER instantiated with phases satisfying ht (epiHorizon
made ht false for 2/4/9). The PAPER-FAITHFUL one to target: DotyExpectedTime.doty_expected_time_concrete
(E[hitting] ≤ (21C0+4Cbad)n(L+1), backup in the RECOVERY term Brecover via seam_rung_expectedHitting_le_nsq
≤n², NOT the phase sum). My tightening work (WorkSlotsTightEpidemic, Route A) is exactly what discharges ht.
=> CAMPAIGN PIVOT: stop targeting the worst-case-sum headline; INSTANTIATE doty_expected_time_concrete with
the tight, reachability-guarded concrete phases.

REMAINING ht GAP (family4 slots audit):
 - slots 2/4/9: tight DONE (WorkSlotsTightEpidemic, ≤17n(L+1)).
 - slot 0: O(n log n) — 3-stage role split via landed Janson (⌈5·meanTime⌉, n⁻² tail). Fits IF instantiated
   with the landed role-split machinery.
 - slot 3: O(n(L+1)) — phase3Horizon = O(log n)·n IF tseed+tbulk = O(n). Fits.
 - slots 1/5/6/7/8 (contracting drains on extremeU/reserve/highMass/classMassN/minorityU): NOT CERTIFIED
   O(n log n) — arbitrary sXT SlotCalib inputs; drain bounds may need m-DEPENDENT (population-proportional)
   rate to be O(n log n), else hide Θ(n²)/Θ(n²log n). SAME defect class as epiHorizon. HIGH RISK slot 6.
 - slot 10: genuinely Θ(n²log n) backup → lives in RECOVERY, not ht (paper-faithful).
NEXT: verify/tighten slots 1/5/6/7/8 drains to O(n log n) (m-dependent rate) + instantiate
doty_expected_time_concrete with the full tight guarded assembly.

## 20. CORE FAITHFULNESS FINDING (family2, VERIFIED Transition.lean:1044) — phase4→5 skips Phase-5 Init — 2026-06-16
Phase4Transition advances 4→5 via raw (advancePhase s, advancePhase t) (Transition.lean:1050, big-bias
branch) — does NOT call advancePhaseWithInit, so phaseInit 5 (counter ← 50(L+1), line 166, EXISTS) is
never invoked. Clock carries its old (possibly 0) counter into phase 5. The formalization is internally
consistent (SeamPairAdapter excludes 5 from CounterResetDest={1,6,7,8}) but the PAPER's Phase-5 Init
resets the counter (c5 ln n), essential for Lemma 7.1 (reserves sample biased Main agents BEFORE clocks
advance). So Lean is UNFAITHFUL at 4→5 — OR a deliberate modeling choice with carry-over handled elsewhere.
DECISION NEEDED (Xiang): (A) fix Phase4Transition to advancePhaseWithInit (faithful; makes phase 5 a RESET
seam → #6 phase4→5 obstruction dissolves to the standard fresh-counter tail; matches paper correctness),
or (B) raw advancePhase is deliberate → need the carry-over argument (family2: no honest carried-counter
floor exists → would need a global clock-budget argument). (A) is paper-faithful + simpler. Affects both
#6 no-overshoot AND the phase-5 correctness analysis (reserve sampling).

## 21. PRECISE RESIDUAL LIST for doty_expected_time_INSTANTIATED (with discharge paths) — 2026-06-16
The expected-time skeleton is built (≤369n(L+1), paper-faithful, axiom-clean). Carried residuals + how each discharges:
 - hDone (StableDone measurable): TRIVIAL — DiscreteMeasurableSpace.forall_measurableSet (config space discrete).
 - hc₀Reach (init reachable): TRIVIAL — Reachable.refl (ReachableClockTail:245 pattern).
 - hDoneAbs (StableDone absorbing): GENUINE — majorityStableEndpoint = phase2Consensus ∨ phase4Tie ∨
   phase9Consensus ∨ phase10Majority (StableEndpoints:3197); need each of the 4 endpoint types proven
   kernel-absorbing (one-step (K x StableDoneᶜ=0)). Iterated version exists FinalAssemblyV5:441.
 - Aggregate ht (∀i phase.t ≤ Cphase·n(L+1)): slots 2/4/9 DONE (WorkSlotsTightEpidemic), seams DONE
   (seamJansonT2), slots 0/3 O(n log n) via landed machinery (need exposure), slots 1/5/6/7/8 via
   ContractingDrainTight m-dependent rate (slot-5 proven; full Janson drain wiring + 1/6/7/8 = codex_drainwire RUNNING).
 - Aggregate hε (∀i ε ≤ δ): from SeamBudgetSlack + WorkSlackCalibWitness + WorkSlotsTightEpidemic (slots 2/4/9
   ε≤1/(2n²)); same assembly shape as ht.
 - hClassify (reachable recovery classification): GENUINE §3.3 — every reachable not-done config → RecoveryClass
   branch (phase-10 backup reachable+draining). codex_classify design RUNNING. Phase-10 drains PROVEN (≤3n²log n).
 - Structural no-overshoot/bridge carries: the first-entry seam invariant (§16 DESIGNED: SeamFirstEntryShape/Edge)
   + the §20 phase4→5 faithfulness DECISION (pending Xiang: advancePhaseWithInit makes phase5 a reset seam).
STATUS: skeleton + dominant fixes DONE; residuals are a finite named list, 2 trivial, the rest with concrete
discharge paths (2 in flight: drainwire, classify). The campaign is instantiation work, not open math.

## 22. HONEST CALIBRATION — the two big residuals are GENUINE work, not wiring (drainwire + classify blocks) — 2026-06-16
Both Codex (drainwire) and ChatGPT (classify) honestly BLOCKED — the aggregate ht and hClassify are real
proof work, not mechanical instantiation. My earlier "mostly mechanical" framing was too optimistic.

AGGREGATE ht (drainwire block, per-slot, file:line precise):
 - slot 5: m·P rate proven (ContractingDrainTight:37); needs ARBITRARY-START partial-MGF Janson (drain from
   Φ≤M₀ with lower milestones reached). milestone_hitting_time_bound_on_partial exists → wireable.
 - slot 1: extremeU counts BOTH ends (val 0 and 6); only +3 side rectangle formalized (DrainThreading:225)
   → need negative side.
 - slots 6/7: highMass/classMassN are DYADIC WEIGHTED MASS, not population counts (Phase6:250, Phase7:1243);
   slot7 cap = n·2^L=Θ(n²), m·E/n² can EXCEED 1 → the m·P count rate is FALSE here. Need a DYADIC-LEVEL drain
   argument (L rounds × O(n)/round → O(n log n)), NOT the count rate. THE DEEPEST ht piece.
 - slot 8: union-of-disjoint-minority-rectangles over live levels (Phase8:588 only fixed-level) — assemblable.
 - slots 0/3: O(n log n) TRUE but ≤17n(L+1) upper bound NOT exposed (RoleSplitConcentration:370 only proves
   5·meanTime≤horizon lower bound; DotySlot035Expose stores t/ε/htail, no upper-bound field) → expose it.

hClassify (classify block): NOT a trivial phase-coverage lemma. Need every reachable not-stable b ∈ a recovery
regime (S1 majority backup / Tie1plus tie backup / phase-progress). RegimeClassification.lean ITSELF states
"full unconditional classification of arbitrary reachable not-done states is the HARDEST remaining object."

HONEST END-STATE: skeleton (doty_expected_time_INSTANTIATED, ≤369n(L+1), paper-faithful, axiom-clean) + the
dominant ORDER defect (Route A) + clock + budget are DONE. Remaining: aggregate ht (per-slot drains, slots 6/7
dyadic the deepest) + hClassify (the hardest object) = GENUINE substantial proof work, deserving focused
effort, not depth-exhausted spraying. NOT near-complete; the hard intellectual core (order defect) IS solved.

## 23. SLOTS 6/7 dyadic drain — GENUINE HARD BLOCK (Codex, honest, file:line) — 2026-06-16
The dyadic-level drain for slots 6/7 does NOT close at 17n(L+1) via the existing per-level count rectangle:
 - Per-level rate is count-rate Θ(m/n) (Phase6:1423 #reserveAtHour6·#mainAt6/(n²); Phase7:799 #elimGap1·
   #minorityAt7/(n²)). DrainCalibration.rect_pow_le_budget:58 requires T ≥ (3/α)(n/m)log n to push a level's
   failure to 1/(M₀n²); the LAST count (m=1) needs Θ(n log n). So (L+1) levels SEQUENTIALLY → Θ(n(L+1)log n)
   = Θ(n log²n), EXCEEDS 17n(L+1)=O(n log n) by a log factor.
 - STRUCTURAL: slot6 Phase6Win NOT a closed invariant (clock pushes agents to phase 7, Phase6:1666); slot7
   global count potential NON-MONOTONE under current invariant — counterexample theorem at Phase7:1126,1141.
ROOT: the real protocol drains all dyadic levels SIMULTANEOUSLY (one O(n log n) process), but the
formalization's rectangle is per-level SEQUENTIAL (×L overhead) + the last-agent coupon Θ(n log n). To
formalize O(n log n) for 6/7 needs a NEW simultaneous-multi-level drain argument (not the existing rectangle)
AND a monotone slot-7 potential. This is the deepest remaining ht piece — genuine new formalization, not wiring.

AGGREGATE ht STATUS: slots 2/4/9 ✅ (WorkSlotsTightEpidemic), seams ✅ (Route A), slots 0/3/5 ✅ (HtTractableSlots),
slots 1/8 SHAPED (drain engine + rate residual), slots 6/7 HARD-BLOCKED (simultaneous-drain + monotonicity).
hDoneAbs ✅ (StableDoneAbsorbing). hClassify = global reachable invariant (hardest). The order defect (Route A)
is solved; slots 6/7 + hClassify are the genuine remaining hard objects.

## 27. WHP TIME THEOREM architecture (ChatGPT via Xiang, paper-faithful) — 2026-06-16
The WHP half of Thm 3.1 ("O(log n) time w.h.p.") must be a FAST-PATH STOPPING-TIME theorem, NOT an endpoint
over the deterministic 21-atom sum (which would pay for the backup always — the §18 artifact). Stopping times
τ10 = inf{t | ∃ agent phase=10}, τstab = inf{t | majorityStableEndpoint c₀ X_t}. Target:
  Pr[τstab ≤ Tfast ∧ τ10 > τstab] ≥ 1 − 21/n².
DO NOT use (K^Tfast)c₀{stable} ≥ 1−21/n² alone — the endpoint set doesn't remember if phase 10 was entered.
ENCODING (Lean-clean): MARKED KERNEL fastK on FastState = Config × Bool (seen10):
  (c,seen10) ↦ c'~K c; (c', seen10 ∨ HasPhase10 c'). Bad event = {x | x.seen10 ∨ ¬majorityStableEndpoint c₀ x.cfg}.
  Prove ((fastK)^Tfast)(c₀,false) FastBad ≤ 21/n². (The paper's "backup entered only on rare failure".)
Tfast = ∑_{i<10} work_i.t + ∑ seam_k.t (EXCLUDE work10 = backup). Constant: 10·17 + 10·11 = 280 (or 269 if
seam9 excluded). UNION BOUND: {τ10≤Tfast} ⊆ FastFail AND {¬stable at Tfast} ⊆ FastFail → one Pr[FastFail]≤21/n²
pays for both. ARCHITECTURE: build a PARALLEL FastAssembly (marked kernel), do NOT retrofit DotyAssembly'.
The backup/phase-10 atom goes ONLY in the expected-time theorem (cost × backup-entry prob), never in Tfast.

RELATION: TWO halves of Thm 3.1, BOTH gated on the aggregate ht (slots 6/7, b7tr2c952 attacking):
 - EXPECTED: doty_expected_time_INSTANTIATED (E[stab] ≤ 369n(L+1), backup in recovery) — built, ht residual.
 - WHP: fast_path_stabilizes_whp (this §27 marked-kernel design) — TODO once ht closes.
Both need ∀ fast phase, t ≤ 17n(L+1) — the same slots-6/7 weighted-drift lemma gates both.

## 28. RECOVERY + hClassify design (2 ChatGPT via Xiang) — restrict to FAST-FAILURE SUPPORT — 2026-06-16
THE KEY INSIGHT (unifies §27 WHP + expected recovery): hClassify should classify ONLY the FAST-FAILURE
CHECKPOINT SUPPORT (configs reachable AFTER the fast path fails = the 21/n² bad event), NOT all reachable
configs. Classifying every reachable config is too broad (early fast-path states, mid-seam mixtures aren't
in any recovery branch). The FastFail event is the SAME for both halves: WHP failure = entry into recovery.

RECOVERY (hRecover/Brecover): the UNRESTRICTED ∀ b∈StableDoneᶜ is NOT paper-faithful (garbage configs lack
clocks). RIGHT shape = REACHABLE-relative (doty_expected_time_reachable', which DotyExpectedTimeInstantiated
ALREADY uses). Brecover = O(n²log n), ASSEMBLED FROM LANDED pieces:
 - phase10Majority_drain_to_stableDone_le ≤ 3n²(1+2log n); phase10Tie ≤ 2n²(1+2log n).
 - entry_to_S1_le_nsq ≤ n²; chainEnd_majority_total_le ≤ n²+3n²(1+2log n).
 - TimedChainRungs per-rung ≤ n² (to next-phase entry, telescoped via RecoveryBridges ladder).
 - ReachableFrom kernel-closed (ReachableLadder). ChainEndRecut: restricted final rung on
   S1 (gap>0) / Tie1plus (gap=0+active) reachable slices.
doty_recovery_expected_bound is a PROJECTION (RecoveryClass→bound), NOT a full recovery proof.

hClassify RESIDUAL (the hard part): 5 recovery regimes (RecoveryEligible) — timed big-clock, timed tiny-clock,
chain-end-seeded (AllClockGEpCard 9 ∧ geCount 10≥1), phase10-majority (S1), phase10-tie (Tie1plus); each
carries ReachableFrom. Steps: (1) RecoveryEligible→RecoveryClass [mostly LANDED: RegimeClassification +
TimedChainRungs + ChainEndAssembly + ChainEndRecut + Phase10ExpectedTime]; (2) THE RESIDUAL =
FastFailureSupportClassified: ∀ b, ReachableFrom init b → b∈FastFailureSupport → b∉StableDone → RecoveryEligible.
The fast-failure-support restriction is what makes this tractable (vs the intractable all-reachable version).
Key invariant: reachable + all-phase-10 + conserved gap-sign → S1 ∨ Tie1plus.

=== COMPLETE Thm 3.1 ARCHITECTURE (both halves, paper-faithful) ===
WHP: fast_path_stabilizes_whp — marked kernel (§27), ((fastK)^Tfast)(c₀,false){seen10∨¬stable}≤21/n².
EXPECTED: doty_expected_time_INSTANTIATED (reachable variant) — E[stab]≤369n(L+1), recovery on fast-failure
  support. Shared FastFail event (21/n²).
BOTH gated on: (i) aggregate ht (slots 6/7 weighted drift, b7tr2c952) — the per-fast-phase time; (ii)
FastFailureSupportClassified — the recovery classification on the fast-failure support. Everything else
(branch bounds, marked-kernel composition, WHP union) is design-clear with landed pieces.

## 29-30. slots 6/7 SPLIT + the ONE remaining input: eliminator linearity E ≥ Ω(n) — 2026-06-16
SLOT 7 (WeightedDriftDrain67): weighted multiplicative drift PROVEN conditional on E[weightedDropSum] ≥ (c0/n)M.
The union gives weightedDropSum ≥ (E7/(n(n-1)))·M, so the drift β=c0/n REQUIRES E7 ≥ c·n (LINEAR eliminator
count). MISSING: Phase6To7Structure only E≤elimGap1 (param, no lower bound); FinalAssemblyV2:406 only E7≤4n/15
(upper); slot8 interface (HtTractableSlots:1225) only 1≤E≤n-1. So slot8's earlier "closure" ALSO carries
E≥Ω(n) (over-stated as closed). V7ResidualClear:108 already flagged this — "not pure arithmetic, can't
manufacture". If E=1: drift Θ(1/n²) → tail Θ(n²log M0), NOT 17n(L+1).
SLOT 6 (WeightedDriftDrain67): highMass CONSERVED by interior split (no drift). Separately investigated
(bz07vamtf, clock-driven hypothesis: phase 6 advances when clock fires at O(n log n), highMass only confined).

=== THE ONE REMAINING TIME-COMPLEXITY INPUT ===
slots 6/7/8 weighted-drift drain ALL reduce to: ELIMINATOR/RESERVE count E ≥ c·n (Θ(n) fraction) on the
reachable invariant. This is a CONCENTRATION/structural fact (reserves sampled phase 5, persist Θ(n); they
CATALYZE cancellation, don't deplete). Doty: reserves are a constant fraction. Provable from reserve-sampling
concentration. THIS is the last input gating the O(n log n) time bound (+ slot 6's clock-driven resolution).
Everything else: aggregate ht slots 0/1/2/3/4/5/9 + seams ✓, hDoneAbs ✓, WHP marked kernel design ✓ (§27),
expected recovery design ✓ (§28), the drift bridges ✓ (WeightedDriftDrain67). Gated on E≥Ω(n) + slot6 + FastFailureSupportClassified.

## 36. slots 6/7 UNIFIED to the per-hour reserve floor + hour-union (xhigh slot-6 + slot-7) — 2026-06-16
Both slots 6/7 reduce to the SAME residual: the φ-drift / classMassN-drift hdrop (β·Φ ≤ weightedDropSum) needs
a reserve floor at the SPLITTABLE HOUR h (l-1<h<L), i.e. ReserveSampleGood i K₀ (PhaseFloors:83) — a PER-HOUR
floor, NOT the total pool. ReservePoolFloor proves only TOTAL reservePool ≥ n/5 (RoleSplitGood). The total
doesn't give a positive β at a fixed hour.
slot-6 xhigh: HONEST BLOCK (no file — refused to fake the hdrop). Obstructions 2/3 handleable (Phase6Win
leak-gate Slot6SurvivalAssembled:56; Cphase adjustable). #4 (per-hour β) is the block.
slot-7: produced work7Tight (carries hdrop) — but intermediate state had sorryAx; judge on completion.
RESOLUTION (the final shared piece): reserves spread across hours (~n/L each from phase-5 sampling), but the
SUM over compatible hours h>l is Θ(n) → UNION the drop rectangles over compatible hours (like slot 8's
live-level union) → total split rate ≥ Θ(M/n) = the drift β. So the residual = ReserveSampleGood (per-hour
distribution from phase-5 sampling) + the hour-union. This is the LAST shared structural input for slots 6/7/8.
Total pool ✓ proven; per-hour distribution + union = remaining. The time bound's final residual.

## 37. CHATGPT PRO CORRECTION (Xiang consulted) — Doty Lemma 7.2/7.3, FIXED-LEVEL floor not per-hour-union — 2026-06-17
My per-hour-union (reservePoolAbove) model was WRONG (b01mvjlf0 stopped). Doty's ACTUAL mechanism (verified
against source):
 - ReserveSampleGood i K₀ = ReserveSampled ∧ sampledFloor i K₀ (Phase5Convergence:1098) — a FIXED-LEVEL floor
   at level i, ALREADY established by phase5Convergence via the in-house MGF-Chernoff hConc (= Doty Lemma 7.2
   concentration, already formalized as the slot-5 Post). Phase 5 samples r.hour ← m.exponent (exponent-COUPLED,
   Transition:1100), so R at level i ∝ biased Main count at i.
 - SLOT 6 (Lemma 7.2): need R_{-ℓ} ≥ 0.04n at ONE fixed compatible level (-ℓ or -(ℓ+1)), compatible with EVERY
   high agent exponent > -ℓ. Case 1: enough majority at -ℓ → |R_{-ℓ}|≥0.18|R|≥0.045n, minus consumption
   ≤0.002|M| (splitWork, PROVEN) → ≥0.04n. Case 2: |A_{-(ℓ+1)}|>0.59|M| → R_{-(ℓ+1)} large. So a SINGLE level's
   reserves serve ALL high agents — NO hour-union needed. (Warning: Lemma 7.2 case-2 prose/notation slip on
   R_{-ℓ} vs R_{-(ℓ+1)}; formalize the intended accounting, ε in Lemma 5.2 small for slack.)
 - SLOT 7 (Lemma 7.3/7.4): partner is NOT reserves — it's the MAJORITY-MAIN BLOCK at {-ℓ,-(ℓ+1),-(ℓ+2)};
   phase 7 cancels opposite opinions exponent-gap ≤ 2. So slot 7's floor = majority-Main count (Lemma 7.3/7.4),
   a DIFFERENT floor than slot 6's reserves.
 - DRIFT (both): split prob ≥0.08/n, φ halves → E[φ']≤(1-0.04/n)φ → 75n ln n → O(n log n) (Markov).
=> REDIRECT: slot 6 uses the FIXED-LEVEL R_{-ℓ} reserve floor (slot-5 ReserveSampleGood + Lemma 7.2 majority-
location case) NOT per-hour-union; slot 7 uses the majority-Main block (Lemma 7.3/7.4). The reserve floor is a
slot-5 OUTPUT, much closer than the per-hour chase suggested. [Xiang-proxy: 统筹 — ChatGPT's Lemma 7.2/7.3 insight redirected off the wrong abstraction]

## 38. Lemma 7.2 EXACT case-2 ledger (family2) — the slot-6 reserve-floor constants — 2026-06-17
Prose slip resolved: case-2 prose's R_{-ℓ} should all read R_{-(ℓ+1)} (reservoir switches to -(ℓ+1)).
Lemma 5.2 (whp): |M| ≤ (1+ε)n/2, |R| ≥ (1-ε)n/4; numeric: r=|R|/n > 0.24, m=|M|/n < 0.51.
CASE 1 (|A_{-ℓ}|>0.19|M|): |R_{-ℓ}(0)|≥0.18|R|; consumption ≤0.002|M| → |R_{-ℓ}(t)|≥0.18|R|-0.002|M|≥0.04n.
CASE 2 (|A_{-ℓ}|≤0.19|M| ⟹ |A_{-(ℓ+1)}|>0.59|M|):
 - initial |R_{-(ℓ+1)}(0)| ≥ 0.58|R| (Chernoff, 1pp slack off 0.59).
 - consumption = 0.004|M| (mass >-ℓ pushed through -(ℓ+1): μ_{>-ℓ}≤0.002|M|2^{-ℓ}, /2^{-(ℓ+1)}=0.004|M|)
   + 0.19|M| (A_{-ℓ} splitting once) = 0.194|M|.
 - net |R_{-(ℓ+1)}(t)| ≥ 0.58|R|-0.194|M| = n(0.58r-0.194m) > 0.58·0.24-0.194·0.51 = 0.0403n > 0.04n.
ε in Lemma 5.2 small enough that r>0.24,m<0.51 hold (the slack 0.0403-0.04=0.0003 needs tight ε; or use
slightly looser drift coeff). Consume in doSplit: reserve sample<m.exponent → reserve→Main, both →exponent-1.
=> slot 6 v2 (bxvnan609) uses these exact constants: R_s≥0.04n at s∈{-ℓ,-(ℓ+1)} → β=0.04/n drift. Reference ledger ready.

## 39. slot-6 obstructions RESOLVED (family4) — drain domain "above -l" + clock-sized window — 2026-06-17
TOP-INDEX (#1) DISSOLVES: Phase 6 NEVER splits Lean index L (= paper exponent -L, minimum mass); split guard
r.sample<m.exponent can't fire there (no sample below -L); Phase 4 treats all-at-(-L) as tie-terminal. The
φ-DRAIN DOMAIN is the "above -l" mass (exponent > -l), NOT all highMass, NOT index L. not_doSplitApplicable_
top_index is IRRELEVANT once the drain is restricted to exponent > -l. Phase-6 target = bring all exponent > -l
down to ≤ -l (Lemma 7.2), Theorem 6.2: most majority in {-l,-(l+1),-(l+2)}, mass above -l small.
PHASE6WIN LEAK (#2): real but handled by CLOCK SIZING. Lemma 7.2 ends: phase 6 finishes in 75 ln n parallel
time, and for counter constant c₆ this happens BEFORE any clock advances → no leak during the drain window.
This is exactly SeamClockSurvivalLong (clock survives the O(n log n) window, PROVEN). Carry the clock-survival
as the gate.
=> slot 6 v2: drain Φ = φ-mass ABOVE -l (not all highMass); top-index excluded by domain; leak excluded by
clock-survival; reserve floor R_s≥0.04n (§38); β=0.04/n drift → 75 ln n → O(n log n). Both obstructions clear.
(WHP half: fast path stabilizes by phase 9 (majority)/phase 4 (tie) BEFORE phase-10 entry; "stabilize by Tfast
w/o phase 10" = complement of 21/n² per-phase failure union — confirms §27 marked-kernel event algebra.)

## 40. RECOVERY classifier design (family3) — SUPPORT-LOCAL, 3 regimes — 2026-06-17
FastFailureSupportClassified (the §28 residual, correctness-side expected-time): do NOT prove the global
"reachable ∧ ¬StableDone ⟹ RecoveryRegime". Prove the SUPPORT-LOCAL:
  FastFailureSupport(c) ∧ reachable(init,c) ∧ ¬StableDone ⟹ RecoveryEligible(init,c).
RecoveryEligible := TimedClockRecover ∨ UntimedDecisionOrAdvance ∨ Phase10Recover.
 - Timed phases {0,1,3,5,6,7,8}: ≥2 clock agents (from phase 0) → counter eventually advances.
 - Untimed {2,4,9}: stabilized OR the check detects the advance condition (phase 9 detects both opinions
   remain → proceed to phase 10).
 - Phase 10: conserved active signed-sum → S1 (gap≠0) / Tie1plus (gap=0+active).
Then RecoveryEligible ⟹ E[T_stable] ≤ Brecover = O(n²log n) (branch bounds LANDED: phase10 drains, TimedChain-
Rungs ≤n², ChainEndRecut). A failed config does NOT always immediately enter phase 10; the 3-regime split
covers all cases. KEY: the support restriction imports the fast-path phase-window/clock/card facts, avoiding
the intractable global reachability theorem. This is the cleanest hClassify discharge.

=== COMPLETE BLUEPRINT STATUS (4-channel ChatGPT 统筹) ===
slot 6: §38 (R_s≥0.04n exact constants) + §39 (drain above -l, clock gate) = COMPLETE recipe.
slot 7: pending family (majority-Main floor, Lemma 7.3/7.4).
recovery: §40 (support-local 3-regime classifier).
WHP: §39 (marked-kernel event algebra confirmed; fast stabilizes phase 9/4 before phase 10).
Codex grinding slot 6 v2 (bxvnan609) + slot 7 (b6vb6z1wy). Blueprints ready to plug in.

## 41. slot-7 majority-Main floor (family, Lemma 7.3/7.4) — COMPLETES the blueprint — 2026-06-17
Slot 7 partner = MAJORITY-MAIN BLOCK G(t) = {majority Mains at exponent ∈ {-ℓ,-(ℓ+1),-(ℓ+2)}}, NOT reserves.
Floor: |G(t)| ≥ 0.8|M| throughout phase 7 (a PREFIX bound — deterministic given the good start, randomness only
in establishing the start).
 - Lemma 7.3 (start): |G(end phase6)| ≥ 0.87|M| whp (Theorem 6.2 0.92|M| block − phase-6 reserve-split losses).
 - Lemma 7.4 (depletion): minority-mass budget. Th6.2: β_- ≤ 0.004|M|·2^{-ℓ}; minority units at exponent ≥
   -(ℓ+4) ≤ 0.064|M|; a block agent changes only by cancel within gap 2 (minority exponent ≥ -(ℓ+4));
   0.87 - 0.064 ≥ 0.8. So |G(t)| ≥ 0.8|M| throughout.
 - DRIFT: minority at -(ℓ+j), j∈{0,1,2}, compatible with EVERY G agent (gap≤2) → partner count ≥0.8mn →
   per-step cancel ≥ c·minorityCount/n → E[minMass']≤(1-c/n)minMass → O(n log n).
slot-7 hdrop floor = |G(t)|≥0.8mn (majority-Main block, prefix bound, minority-budget conserved). NOT reserves.

=== 4-CHANNEL 统筹 COMPLETE: full paper-faithful blueprint for the ENTIRE remaining proof ===
slot 6: §38 (R_s≥0.04n exact) + §39 (drain above -l, clock gate). slot 7: §41 (|G|≥0.8mn majority block).
recovery: §40 (support-local 3-regime). WHP: §39 (marked-kernel algebra). EVERY leaf now has Doty's exact
mechanism + constants. Codex grinding slot 6 v2 (bxvnan609) + slot 7 (b6vb6z1wy) — re-dispatch w/ blueprints
if they hit a now-resolved obstruction. The architecture was fixed; the leaves are now fully specified.

## 44. CONSUMPTION TRACE ledger (family3) — slot-6 source fact #3 — 2026-06-17 (Codex credit-limited; ChatGPT blueprinting)
CLEAN INVARIANT: |R_s(t)| = |R_s(0)| - consumed_s(t), consumed_s(t) = # phase-6 doSplit reactions whose
reserve operand had sample=s. No reserve creation in phase 6; sample fixed from phase 5 → exact equality.
Consumers of R_s = biased Mains with exponent > s (STRICT guard r.sample<m.exponent; a Main at exactly s
CANNOT consume R_s). Bound = SPLIT-TREE COUNT: agents of mass μ(>s) split down through s → reactions ≤
μ(>s)/2^s. Uses Theorem 6.2 mass-above bound μ(>-ℓ) ≤ 0.002|M|·2^{-ℓ} (paper: 0.001|M|2^{-ℓ+1}).
 CASE 1 (R_{-ℓ}): consumed ≤ μ(>-ℓ)/2^{-ℓ} ≤ 0.002|M| → |R_{-ℓ}(t)| ≥ 0.18|R|-0.002|M| = n(0.18r-0.002m) ≥
   0.04n (r>0.24).
 CASE 2 (R_{-(ℓ+1)}): two consumer sources — (1) mass above -ℓ split one extra level to -(ℓ+1): ≤0.004|M|;
   (2) A_{-ℓ} agents splitting once: ≤0.19|M|; total ≤0.194|M| → |R_{-(ℓ+1)}(t)| ≥ 0.58|R|-0.194|M| > 0.04n.
FORMALIZE: consumed_s = # doSplit with reserve sample=s ≤ split-tree work of agents through s ≤ massAbove(s)/
2^{-s}. Needs Theorem 6.2 mass-above (μ(>-ℓ)≤0.002|M|2^{-ℓ}) as input. This is slot-6 source fact #3.
Source facts status: #1 A_{ℓ+2}≤0.13|M| (family bj9xhyik6 pending); #2 two-level sampling (family2 b3zzwadz4
pending); #3 consumption ledger §44 (DONE). When Codex resets, formalize all 3 → dichotomy → reserve floor → work6Tight.

## 45. BRANCH-SELECTING SAMPLING (family2) — slot-6 source fact #2 — 2026-06-17
Sampling is COUNT-proportional, NOT mass-weighted: R_i ≈ (B_i/B)·R where B_i=#{biased Main at exponent i},
B=#{biased Main}, R_i=#{Reserve with sample=i}. Reserve stores first-met biased Main's exponent (NO 2^{-i}).
CLEAN EVENT: SampleGoodAll := ∀ i, R_i ≥ (B_i/B - 0.01)·R (all-level lower-tail; union over ≤L+1 levels folds
into budget). COROLLARY for Lemma 7.2: A_i ≥ p|M| ⟹ R_i ≥ (p-0.01)|R| (A_i≤B_i, B≤|M|). Branches:
A_{-ℓ}>0.19|M|⟹R_{-ℓ}≥0.18|R|; A_{-(ℓ+1)}>0.59|M|⟹R_{-(ℓ+1)}≥0.58|R| (paper constants 0.19→0.18, 0.59→0.58).
KEY: the Lean Phase5Convergence MGF-Chernoff ALREADY gives this (sampled class_i ~ class_i/biasedTotal vs the
static biasedMainClassU profile) — just RESTATE ReserveSampleGood as the ∀i SampleGoodAll event, not single i.
Then dichotomy (§43+#1) selects s, apply corollary. Slot-6 source fact #2 blueprinted.
Source facts: #1 A_{ℓ+2}≤0.13|M| (family pending); #2 sampling §45 (DONE); #3 consumption §44 (DONE).
2 of 3 blueprinted; the φ-drift+producer+packager+dichotomy-arithmetic all WIRED+VERIFIED. When Codex resets:
formalize SampleGoodAll (restate existing Chernoff ∀i) + consumed_s ledger + A_{ℓ+2} cap → work6Tight.

## 46. ⚠️ POTENTIAL GAP IN DOTY'S PAPER — Lemma 7.2 case 2 (family/ChatGPT, NEEDS VERIFICATION) — 2026-06-17
ChatGPT correction: the slot-6 dichotomy |A_{-ℓ}|>0.19|M| ∨ |A_{-(ℓ+1)}|>0.59|M| is NOT derivable from
Theorem 6.2 as stated. My §42-43 reduction (dichotomy ← A_{ℓ+2}≤0.13|M|) was WRONG on TWO counts:
 (1) Theorem 6.2 does NOT bound A_{-(ℓ+2)} (the 0.13 I saw is ρ_{ℓ-3}=0.13, a MASS-induction constant in
     Lemma 6.16, not a per-level count cap; a mass bound gives only vacuous A_{ℓ+2}≤3.23|M|).
 (2) Theorem 6.2 gives ONLY: 3-level count ≥0.92|M|; mass-above μ(>-ℓ)≤0.002|M|2^{-ℓ}; minority β_-≤0.004|M|2^{-ℓ};
     gap 0.4|M|≤g_ℓ<0.8|M|. NO top-two concentration, NO A_{ℓ+2} cap.
COUNTEREXAMPLE (Theorem 6.2 holds, dichotomy FAILS): A_{-ℓ}=0.19, A_{-(ℓ+1)}=0.064, A_{-(ℓ+2)}=0.666 (|M|=1):
3-level=0.92 ✓, majority mass 0.19+0.032+0.1665+...≈0.40 ≥ 0.4 threshold ✓, but A_{-(ℓ+1)}=0.064 ≪ 0.59. So
case 2's claim is NOT forced by Theorem 6.2.
DOTY'S PRINTED Lemma 7.2 case 2: uses mass-max 0.59·2^{-(ℓ+1)}+0.41·2^{-(ℓ+2)}=0.3975·2^{-ℓ} to force
A_{-(ℓ+1)}>0.59 — but this treats all non-A_{-(ℓ+1)} Mains as at -(ℓ+2) (weight 1/4) while the case permits
0.19|M| at -ℓ (weight 1). The printed argument appears INCOMPLETE.
=> SLOT 6 needs EITHER (a) a NEW phase-3 top-two/no-over-splitting lemma (majority concentrates in {-ℓ,-(ℓ+1)},
NOT given by Theorem 6.2), OR (b) a REPAIRED Lemma 7.2 with different reserve-depletion accounting. This is a
RESEARCH-LEVEL finding (potential gap in a published FOCS proof), surfaced by the formalization. NEEDS
VERIFICATION (could be a prose slip with the real argument elsewhere in the paper; or a genuine gap). The
φ-drift+producer+packager+dichotomy-ARITHMETIC are all still PROVEN; the gap is in the dichotomy's HYPOTHESIS.

=== §47: CAPSTONE ASSEMBLY VACUITY AUDIT (family4 R1, citation-backed) ===
Forward-looking guard for instantiating doty_time_headline / doty_expected_time. Paper is asymptotically
sound; the Lean CAPSTONE has 4 concrete must-fix traps (NOT bugs in landed per-slot files — assembly-level):

(1) BRANCHING (not linear chain): Thm 3.1 branches — large-gap→Phase2 stable; tie→Phase4 stable;
    small-nonzero-gap→3,5,6,7,8→Phase9 stable. A plain Postᵢ⇒Preᵢ₊₁ is FALSE (Post2 is stable consensus,
    not Phase-3 entry; Post4 is stable tie, not Phase-5 entry). FIX: Postᵢ := StableFast ∨ Preᵢ₊₁, OR the
    seen10 marked kernel ALSO marks/stops at stableFast. Composition must be branch-aware.
(2) BUDGET: εᵢ≤1/(2n²) × 21 events = 21/(2n²) ≠ 1/n². FIX: per-event ≤1/(2·Nbad·n²) or ≤1/n³; AND the
    Θ(L)=Θ(log n) per-hour/per-level internal events must be BUNDLED into ONE phase theorem (Doty bundles:
    Th6.2=Phase3 hours, Lemma7.5=Phase7 levels, Lemma7.6=Phase8) — charge ONE phase-level ε AFTER internal
    union bounds paid. Else Σ = (log n)/n², not O(1/n²).
(3) CONSTANT: Phase 6 alone = 75n ln n ≈ 52nL (75·ln2≈52, ARITHMETIC CONFIRMED). The 17n(L+1) cap
    (WorkSlotsTightEpidemic, for EPIDEMIC slots 2/4/9) is ~3× too small for Phase 6. FIX (already in design):
    slot 6 carries its OWN ≥52n(L+1) constant; do NOT apply 17n(L+1) universally. Phase7<20 ln n, Phase8
    ≤8.5 ln n (both < Phase6). UNIT TRAP: clock t=70(L+1) must be sequential-kernel-steps (or ×n factor);
    369n(L+1) headline must sum ALL phases in the SAME unit.
(4) EXPECTED-TIME needs QUANTITATIVE Lemma 7.7 (Phase10 O(n log n) parallel, expectation+whp), NOT mere
    finite-expectation correctness. Pr[backup]≤C/n² × E[Phase10|trig]≤C'n log n → O(log n). A bare
    "stable_majority_correct: finite expectation" is INSUFFICIENT (could be arbitrarily large in n). [family4 R2
    bqild1wcv investigating exact Lemma 7.7 statement+constant.]
EXTRA: (a) timed-phase windows NOT kernel-closed (counter advances) → need Post ∨ EarlyExitFailure charged
    (matches our leak gates). (b) seen10 in bad-event algebra: prove CONTAINMENT {¬StableFastByT ∨ seen10_T}
    ⊆ ⋃badᵢ, do NOT force definitional equality. VERIFY when assembling: doty_expected_time_INSTANTIATED's
    internal ε-budget + that its backup carries a QUANTITATIVE (not just-correctness) time bound.

=== §48: RESERVE-FLOOR LEAF RESOLVED (family2 R1, citation-backed) — Codex-dispatchable, §46-independent parts ===
The phase-5 reserve floor decomposes cleanly. KEY REFRAME: the right object is the COMPATIBLE-HOUR UNION
reservePoolAbove(j) = Σ_{h>j} R_h (ALREADY defined @ ReservePerHourFloor:40), NOT a fixed single level.
Split guard = r.sample < m.exponent (a Main at exp -j splits with ANY reserve sampled at hour h>j).

DECOMPOSITION (parts a/b/c are §46-INDEPENDENT, dischargeable NOW):
(a) PER-LEVEL CHERNOFF: ∀i, B_i/B ≥ p ⟹ R_i ≥ (p−0.01)|R| whp, failure exp(−Ω(n)) ≫ 1/n². [Phase-5 samples
    by COUNT B_i/B, NO 2^{-i} weight — pseudocode: reserve sets sample←m.exponent on first biased-Main meet.
    §45 SampleGoodAll; Phase5Convergence MGF-Chernoff ALREADY proves the single-(i,K₀) form — extend to ∀i.]
(b) ADAPTER: A_i ≥ p|M| ⟹ B_i/B ≥ p. TRIVIAL (A_i ≤ B_i, B ≤ |M|).
(c) UNION-FLOOR: s>j ∧ R_s ≥ 0.04n ⟹ reservePoolAbove(j) ≥ 0.04n. TRIVIAL (R_s is one term of Σ_{h>j}).
(d) BRANCH SELECTION (§46-GATED): dichotomy A_{-ℓ}>0.19|M| ∨ A_{-(ℓ+1)}>0.59|M| picks s∈{-ℓ,-(ℓ+1)}; both
    compatible with every high agent (exp>-ℓ ⟹ j<ℓ). Lemma 7.2 split prob = 2·0.04n/n² = 0.08/n (the UNION
    R_{-ℓ}∪R_{-(ℓ+1)}). This dichotomy on A is the §46 contested piece.
BUDGET NOTE (matches §47): do NOT give 1/n² to each of L+1 levels (→(L+1)/n²). Use the exp Chernoff tail
unioned over L+1 levels (still exp small), OR per-level 1/((L+1)n²) / 1/n³.
CASE CONSTANTS (Lemma 7.2): case1 R_{-ℓ}≥0.18|R|−0.002|M|≥0.04n; case2 R_{-(ℓ+1)}≥0.58|R|−0.004|M|−0.19|M|≥0.04n.
GAP-IF-ONLY-TOTAL: |R|≥n/5 ALONE is useless (reserves could all sample incompatible hours) — the sampling
CONCENTRATION (a) is essential; Doty does NOT route around it.
=> ACTION: Codex-dispatch (a)+(b)+(c) into ReserveSampleGoodDischarge.lean / ReservePerHourFloor.lean once
slot7v2 frees (single-line Codex). (d) awaits family2 R2 (bp6khlkru: does the floor need the A-dichotomy at
all?) + the §46 decision. If family2 R2 says floor follows from sampling+|R|+consumption WITHOUT the
A-dichotomy, slot 6 closes §46-FREE.

=== §49: SLOT-7 MAJORITY-MAIN FLOOR — CROSS-CHECKED & CORRECTED (family3 R1, citation-backed) ===
slot-7 is §46-INDEPENDENT (2nd confirmation): uses Theorem 6.2 AGGREGATE |G_end3|≥0.92|M|, NOT the per-level
dichotomy. Corrects §41 in 3 ways:

(A) START (Lemma 7.3) |G_end6|≥0.87|M|: the 0.05|M| loss is NOT "phase-6 split work" — it is the count of
    BAD-SAMPLE reserves (r.sample ∉ {-ℓ,-(ℓ+1),-(ℓ+2)}) ≤ 0.09|R| ≤ 0.05|M| (via |R|<5/9|M|). A block agent
    leaves only by being pushed below -(ℓ+2), which consumes a below-(-ℓ+2)-sample reserve; reserve consumed
    once, removes ≤1 block agent. FORMAL: |G_end6| ≥ |G_end3| − #{r.sample ∉ protected-3-level}.
(B) FLOOR (Lemma 7.4) 0.87−0.064=0.806≥0.8: formalize as CUMULATIVE MASS-BUDGET, NOT instantaneous count.
    Each Phase-7 G-removing reaction decreases β_- by ≥ 2^{-(ℓ+4)} (deepest compatible minority = -(ℓ+2)−2);
    β_- nonincreasing, starts ≤ 0.004|M|2^{-ℓ} ⟹ total G-removals ≤ 0.004·16·|M| = 0.064|M|. (Naive "≤0.064
    minorities initially so ≤0.064 cancels" is UNSAFE — gap-2 reactions change the count distribution.)
(C) DRIFT: my E[mass']≤(1−c/n)mass is valid-but-not-cleanest. Doty does SEQUENTIAL COUNT ELIMINATION: drain
    B_{-ℓ}(≤0.004|M|, t₁≤6.41 ln n) → B_{-(ℓ+1)}(≤0.008|M|, t₂≤6.45) → B_{-(ℓ+2)}(≤0.016|M|, t₃≤6.51), total
    <20 ln n, via Lemma 4.6 (two-sided 5 ln n/[2(a−b)]) / Lemma 4.7 (one-sided 5 ln n/(2a)). The WEIGHTED-mass
    supermartingale route (slot7v2 Codex, WeightedDriftDrain67) is SOUND (minority dyadic mass decreases on
    every cancellation) but needs a weaker constant. [family3 R2 bgex0dsav verifying supermartingale
    monotonicity under gap-2 + the Lemma 4.6/4.7 hitting-time tool.]
TAIL (matches §47): paper gives 1−O(1/n²); literal ≤1/(2n²) after 3-level union needs a LARGER phase-7
horizon constant (or larger λ). O(log n) parallel unaffected.
=> 3 recommended lemmas: (1) Phase-6 block-loss |G_end6|≥|G_end3|−#bad-sample; (2) Phase-7 mass-budget
#{G-removals}≤β_-(0)/2^{-(ℓ+4)}≤0.064|M|; (3) sequential elimination |B_s|'≤|B_s|−1 on B_s-G interaction,
prob 2|G||B_s|/(n(n−1)). VERIFY slot7v2 on return: does it use the robust cumulative-budget (B) or naive count?

=== §50: §46 GAP CONFIRMED REAL (family R1, 910s, citation-backed, independent) + §46-FREE UNION ROUTE ===
VERDICT: Doty Lemma 7.2 case-2 (p.42) has a REAL ARITHMETIC GAP. CONFIRMED independent of my analysis.
- Theorem 6.2 gives ONLY: x+y+z≥0.92|M| (x=A_{-ℓ},y=A_{-(ℓ+1)},z=A_{-(ℓ+2)}), μ(>-ℓ)≤0.002|M|2^{-ℓ},
  β_-≤0.004|M|2^{-ℓ}. NO count cap on z, NO x+y≥0.79|M|.
- 0.13 = ρ_{ℓ-3} (Lemma 6.16, dyadic MASS μ(end_h)≤ρ_h|M|2^{-h}; ρ_{ℓ-2}=0.212,ρ_{ℓ-1}=0.408,ρ_ℓ=0.808),
  NOT a count cap. My §42-43 diagnosis CONFIRMED.
- Lemma 7.2 case-2 flaw: its mass-maximization "put remaining 0.41|M| at -(ℓ+2)" IGNORES that ≤0.19|M| sit at
  -ℓ (weight 2^{-ℓ} not 2^{-(ℓ+2)}). NOT salvageable. Counterexample to postconditions: x=0.19,y=0.064,z=0.746
  (aggregate=1, majority-mass=0.4085≥0.4, BUT both branches fail).
- NO hidden Phase-3 top-two lemma: 6.11(below-window count), 6.15(mass-above), 6.17(minority β_-≤0.004),
  6.18(3-level: ≥0.96|M| at end_{ℓ+2}, ≥0.92|M| later; proof only gives WEAK x+y≥0.19|M|, off 4× from 0.79).
  Phase-3 dynamics PUSH mass into -(ℓ+2) (hour-ℓ+2 splitting), so a third-level count cap is "likely FALSE as a
  simple reachable invariant."
- Min closing assumption: z≤0.13|M| (COUNT) ⟹ y≥0.92−0.19−0.13=0.60>0.59. But NOT a Doty §6 lemma.
THREE OPTIONS (XIANG'S CALL — method-flexibility on a published-paper finding, ESCALATED):
 (1) carry z≤0.13|M| as unproven assumption; (2) prove new Phase-3 top-two lemma (likely false); (3) replace
 Lemma 7.2 with a new reserve analysis using ALL 3 levels' reserves.
=> §46-FREE UNION ROUTE (option 3, EMERGING — family R2 ba2bd8ria + family2 R2 bp6khlkru verifying): the φ-drift
needs only reservePoolAbove(j)=Σ_{h>j}R_h ≥ 0.04n (split guard r.sample<m.exponent ⟹ a high agent at -j, j<ℓ,
splits with reserves at ANY of -ℓ/-(ℓ+1)/-(ℓ+2), all <-j). Aggregate sampling: reserves into the 3-level union
≥ 0.92|M|/B·|R| ≥ 0.92|R| ≥ 0.92·n/5 ≈ 0.18n (B≤|M|), minus consumption ≤ highMass. If this stays ≥0.04n
throughout AND the φ-contraction needs only the UNION (not level selection), slot 6 closes WITHOUT the
dichotomy — the gap is in Doty's single-level EXPOSITION, not the protocol. PENDING verification + Xiang's call.
SLOT 7 unaffected (§49: uses aggregate, §46-independent — confirmed twice).

=== §51: EXPECTED-TIME BACKUP CAPSTONE (family4 R2, citation-backed) — §46-independent ===
Lemma 7.7 is ASYMPTOTIC ONLY: O(n log n) parallel (=O(n² log n) seq), expectation AND whp, NO explicit
constant. FORMALIZE PARAMETERIZED (∃C c n₀, E[T10_par]≤Cn log n ∧ Pr[T10_par>Cn log n]≤c/n²); do NOT hardcode
a paper constant for the backup. [Our doty_expected_time_INSTANTIATED ≤369n(L+1) is the FAST-path concrete
const — VERIFY its backup leg is quantitative-parameterized, not mere-correctness.]
PROOF DECOMP (Phase 10 = 6-state backup, STANDALONE: uses only output←input, active←True, ignores fast fields):
 majority: cancel B (Lemma 4.6, Janson λ=5) → convert T (coupon-collector, next-hit≥2k/(n(n-1))) → convert
 passive (coupon). tie: cancel n/2 A/B pairs (i²/n² rate, E[par]=O(n)) → T propagates (coupon). Primitives =
 Lemma 4.6 + coupon-collector — SAME as slot-7 (reuse family3 R2's 4.6/4.7).
COMPOSITION: E[S] ≤ E[fast;goodClock] + Pr[backup]·E[T10] + Pr[smallClock]·Tpoly.
 · backup term = O(1/n²)·O(n log n) = o(1).
 · SMALL-CLOCK term (subtle): |C|≥0.24n whp (Lemma 5.2); if |C| sublinear (≥2) counter bounds only poly(n)
   BUT Pr[smallClock]=n^{-ω(1)} (super-poly, NOT 1−O(1/n²)) ⟹ n^{-ω(1)}·n^{O(1)}=o(1). Uses "very high prob."
4 FACTS capstone consumes: (1) fast Pr[StableFast∧¬seen10]≥1−Cfast/n²; (2) Phase10 standalone E[T10]≤C10 n log n,
 tail≤C10'/n²; (3) ENTRY WRAPPER (BIGGEST TRAP): Lemma 7.7 is about Phase10 ONCE RUNNING, not the first moment
 phase=10 — need phase-max rumor epidemic (seen10 → all initialized in O(log n) par); NOT silently assumable;
 (4) small-clock Pr=n^{-ω(1)}, poly conditional → negligible.
TRIGGER seen10: controlled by the SAME fast-path failure union (GoodFastRun⊆¬seen10∧StableFast), NOT a separate
 estimate, NOT from role-split alone. Examples: Phase1 RoleMCR→10, Phase2 |bias|>1→10, Phase9 failed-consensus→10.
[family4 R3 bchxxyfzx now doing the WHP marked-kernel twin half.]

=== §52: family2 R2 — §46-FREE SINGLE-LEVEL ROUTE FAILS; exact depletion; role-split correction ===
DECISIVE: the SINGLE-LEVEL case-2 floor R_{-(ℓ+1)}≥0.58|R| does NOT bypass the dichotomy — it REQUIRES
A_{-(ℓ+1)}>0.59|M| (reserves sample by biased-Main exponent; total |R| says nothing about R_s). The
AGGREGATE-UNION route (reservePoolAbove from aggregate 0.92|M|) remains the open §46-free hope (family R2).
EXACT DEPLETION TERMS (corrects §49): 0.004|M| = mass-above-(-ℓ) μ(>-ℓ)≤0.001|M|2^{-ℓ+1} pushed to -(ℓ+1) →
count ≤0.004|M| (NOT minority budget). 0.19|M| = count of A_{-ℓ} agents each consuming ≤1 R_{-(ℓ+1)} reserve
(Phase-6 guard r.sample<m.exp lets A_{-ℓ} split using -(ℓ+1) reserves). Notation slip CONFIRMED: case-2 text
says R_{-ℓ}, displayed ineq is R_{-(ℓ+1)} — intended reservoir R_{-(ℓ+1)}.
ROLE-SPLIT (Lemma 5.2): |M|≈n/2 (m<0.51), |C|,|R|≥(1-ε)n/4 (r>0.24). [CORRECTION: |M|≈n/2 NOT n/4.]
ARITH CLOSES given dichotomy: 0.58·0.24−0.194·0.51=0.0403>0.04; symbolic needs ε≤0.033 (ε<0.02 safe).
Ledger UNIT-CONSISTENT conditional on A_{-(ℓ+1)} large; only the dichotomy DERIVATION is the gap (confirms §50).
New counterexample: A=(0.19,0.11,0.62) mass=0.40 exactly, A_{-(ℓ+1)}≪0.59.
CONSUMPTION IS TINY: μ(>-ℓ)≤0.002|M| ⟹ high-agent count ≈0.001n ≪ 0.04n floor ⟹ throughout-phase-6 floor
holds with huge margin (the union route's consumption side is robust). [family2 R3 bq5gskhtu: exact Phase-5
sampling concentration statement for the floor producer.]

=== §53: SLOT-7 WEIGHTED-MASS ROUTE COMPLETE (family3 R2, citation-backed) — formalization-ready ===
Φ_- = Σ_minority 2^exp NONINCREASING under EVERY phase-7 reaction (exact ΔΦ_-=2^{min(e_i,e_j)}):
 gap-0 −2^e (annihilate); gap-1 −2^{min} (low erased OR high halves); gap-2 −2^{e_i-2} (low adopts majority OR
 high moves down + lower becomes minority, net −¼ high weight). G-removing reaction drops Φ_-≥2^{-(ℓ+4)} →
 0.064|M| budget (β_-≤0.004|M|2^{-ℓ} ÷ 2^{-(ℓ+4)}).
DRIFT CORRECTION (vs my 1.6m/n): for WEIGHTED mass, gap-2 gives only ¼ drop ⟹ robust β=0.4m/n (4× weaker).
 Target = HIGH-BAND Φ_hi (minority at {-ℓ,-(ℓ+1),-(ℓ+2)}) ONLY — NOT all Φ_- (deeper minorities <-(ℓ+2) not
 G-compatible). E[Φ_hi'|c] ≤ (1−0.4m/(n−1))Φ_hi on |G|≥0.8mn.
HORIZON+TAIL (worked): Φ_hi(0)≤0.004mn2^{-ℓ}, Φ_hi≥2^{-(ℓ+2)} if >0, ratio≤0.016mn. τ=20 ln n, m≥0.49 ⟹
 Pr[∃ high-band minority]≤0.016n^{-2.92}≤1/(2n²) ∀n≥1. General τ≥(λ+1)/(0.4m_min)·ln n.
LEMMA 4.6 (2-sided cancel |A|=an,|B|=bn,b<a): complete B-elim whp t≤5 ln n/[2(a−b)], Janson Thm4.3 λ=5
 (λ−1−ln λ>2→n^{-2}). LEMMA 4.7 (1-sided |A|≥an,|B|=b₁n→b₂n): t≤5 ln n/(2a). Lemma 7.5 uses 4.7 with A=G,
 B=B_{-ℓ}/B_{-(ℓ+1)}/B_{-(ℓ+2)} → 6.41/6.45/6.51 ln n, Σ<20 ln n.
⚠️ LEAN PITFALL: gap-2 update uses OLD high exponent (SIMULTANEOUS assignment); mutate i.exponent then compute
 j.exponent BREAKS the mass invariant + paper example (+1/4,-1/16→+1/8,+1/16).
4 lemmas: (1) branch-local Φ_- monotonicity ΔΦ_-=2^{min}; (2) high-band drift (1−0.4m/(n−1)); (3) Φ_hi(0)≤
 0.004mn2^{-ℓ} & Φ_hi≥2^{-(ℓ+2)} if>0; (4) tail after 20n ln n ⟹ Pr≤1/(2n²) (m≥0.49).
=> VERIFY slot7v2 ON RETURN: must target Φ_hi (high-band) with coeff ≤0.4m/n, NOT all-Φ_- with 1.6m/n
 (unsound for weighted mass per Q1 caveat). [family3 R3 bqhp6dgmx: Phase-8 deep-minority consumption.]

=== §54: WHP CAPSTONE (family4 R3) — branch-aware stopped kernel ===
3 cases on gap: |g|≥0.025|M|→Phase2 (Lemma 5.3); 0<|g|<0.025|M|→Phase9 (Th6.2+7.2+7.6); g=0→Phase4 (Th6.1).
CLEAN LEAN FORM: stopped marked kernel, Postᵢ=StableFast∨Preᵢ₊₁, + separate `bad` mark for early timed-phase
exits. Statement: Pr[StableFast∧¬seen10∧¬bad]≥1−C/n²; prove CONTAINMENT {¬StableFast∨seen10}⊆⋃badᵢ (NOT
definitional eq). 13 charged events (role-split, Ph1, tie-Ph3, smallgap-Ph3, Ph5, Ph6, Ph6-preserv/7.3,
Ph7-floor/7.4, Ph7-elim/7.5, Ph8/7.6, Ph9-epidemic, seam-epidemics, early-clock-exit×4 for Ph5/6/7/8). Early-exit
is a CHARGED FAILURE EVENT (path/stopping-time shaped WorkPost-before-EarlyExit), not a precondition. WHP+expected
combine DISJOINTLY: E[τ]≤Tfast·Pr[GoodFast]+E[τ;¬GoodFast], no double-count.

=== §55: slot7v2 §3.3 VACUITY CATCH (work7Tight OVER-STRONG) — corrected v3 dispatched ===
slot7v2's work7Tight is AXIOM-CLEAN but carries a GENERICALLY-FALSE invariant: MajorityBlockReady.mass_le_block
(classMassN ≤ minorityBlockMass) ≡ "no σ-minority below level l+2" (inThreeBlock=l≤i≤l+2, 3 levels). classMassN
is TOTAL mass; Post classMassN=0 = ALL minority gone. But Ph6 leaves DEEP minorities (>l+2) — exactly Phase 8's
job. So work7Tight COLLAPSED phases 7+8 + patched the total-mass drift with the false no-deep-tail assumption.
Load-bearing (drift needs both-in-block via gap_le_two_of_inThreeBlock). §3.3 trap (clean #print axioms misses
it; matches [[feedback_carried_closure_satisfiability]]). NOT banked as a close.
CORRECTED (slot7v3, Codex xhigh grinding): Post = minorityBlockMass=0 (HIGH-band only), drift on Φ_hi (block
mass), β=0.4m/n (gap-2 ¼ drop, NOT 1.6/n), carry ONLY the satisfiable block floor (drop mass_le_block); deep
tail → Phase 8. REUSE the correct lemmas (quarter-drop, floor arithmetic, disjointness — those are right).

=== §56: §46 RESOLVED — §6-DERIVABLE UNION REPAIR (family R2 DECIDER, citation-backed) ===
The union route WORKS but NOT 3-level (the low block A_{-ℓ}/A_{-(ℓ+1)} consumes R_{-(ℓ+2)} via guard
r.sample<m.exp; concrete obstruction x=0.12,y=0.24,z=0.64 drives 3-level union to R_{-ℓ}=0.0288n<0.04n).
THE CLEAN REPAIR (bypasses the broken count dichotomy entirely):
 · TWO-level union P(t)=R_{-ℓ}∪R_{-(ℓ+1)} (both compatible with every high agent at exp>-ℓ).
 · WEIGHTED inequality 3x+y ≥ 0.592 (x=A_{-ℓ}/|M|, y=A_{-(ℓ+1)}/|M|) — DERIVABLE from Th6.2:
   β_+≥0.4|M|2^{-ℓ}, mass-above≤0.002, rest at exp≤-(ℓ+2) ⟹ 0.4≤0.002+x+y/2+(1-x-y)/4 ⟹ 3x+y≥0.592.
   (VERIFIED algebra: 0.4≤0.252+0.75x+0.25y ⟹ 0.148≤0.75x+0.25y ⟹ ×4 ⟹ 0.592≤3x+y.) This is what Doty's
   broken case-2 SHOULD have used (weighted-MASS constraint, NOT a count dichotomy).
 · Live floor |P(t)|≥0.02n throughout (min subject to 3x+y≥0.592, role r>0.24,m<0.51), consumption per level
   bounded (R_{-ℓ}←high-tail ≤0.002|M|; R_{-(ℓ+1)}←high-tail+A_{-ℓ}-splits+minority ≤0.004|M|).
 · Drift (1−0.02/n)φ → horizon ~150 ln n (Ph6 const bigger than printed 75 ln n), still O(n log n).
=> Doty's published case-2 EXPOSITION is genuinely WRONG (count dichotomy not derivable); the THEOREM SURVIVES
via this union-floor + weighted-inequality repair. NEW lemma, not Doty's printed Lemma 7.2 — XIANG'S CALL to
adopt (option 3, now concrete). [family R3 bb0whrlk9 making 3x+y≥0.592 + the 0.02n floor formalization-rigorous.]
slot 6 then closes §46-FREE via this repair (NO unproven dichotomy assumption).

=== §57: Ph5 SAMPLING FLOOR PRODUCER (family2 R3) — §46-independent, Codex-ready ===
SampleGoodPair_ℓ(0.01): B_i≥pB ⟹ R_i≥(p-0.01)|R|, at the 2 levels {-ℓ,-(ℓ+1)} (or SampleGoodAll ∀i). Model:
(R_i)~Multinomial(|R|;B_i/B) conditional on static Ph5-start biased-Main profile (Ph5 writes only samples; Ph4
doesn't change exponents → B_i = Th6.2 end-Ph3 profile, B_i≥A_i, B≤|M|). Tail: R_i~Binomial(|R|,q_i), Hoeffding
Pr[R_i<(p-0.01)|R|]≤exp(-2·0.01²|R|)=exp(-|R|/5000)≤exp(-6n/125000) (r>0.24). 2-level fail ≤2e^{-|R|/5000};
all-level ≤(L+1)e^{-|R|/5000} (≪1/n²). Lean route: indep-indicator Hoeffding (or sequential martingale/Azuma if
multinomial coupling too costly — conditional sample prob stays B_i/B since profile static).

=== §58: PHASE 8 (family3 R3, Lemma 7.6) — count-based two-sided, §46-independent ===
Mechanism: larger-exp biased Main i consumes smaller-exp opposite Main j, i.full←True (ONE-USE), j.opinion←0.
NO gap restriction. Consuming pop = G with full=False (ONE-USE resource, NOT static 0.8|M|). Use Lemma 4.6
two-sided a=0.8m,b=0.2m: track A_t(usable G), B_t(minority), both −1/interaction, INVARIANT A_t−B_t≥0.6mn.
Per-step prob ≥2·0.6mn·B_t/(n(n−1)). Budget STRUCTURAL: B_0≤|M|−|G|≤0.2|M| (NOT from dyadic mass — deep tail =
many tiny-mass agents). Constant: t≤5 ln n/[2·0.6m]=5 ln n/(1.2m); m≥0.495 ⟹ 8.418≤8.5 ln n. ⚠️ m≥0.49 gives
8.503>8.5 — need m≥0.495 (Lemma 5.2 ε=0.005) or use 8.6 ln n.

=== §59: ⚠️ CLOCK CONSTANT DOMINATES — honest headline (family4 R4, Theorem 6.9) ===
Theorem 6.9 (parallel time, ×n for seq): per-hour UPPER (2.11k+2.2)/c²=97.15/c² (k=45); LOWER (0.45k-3.1)/c²
=17.15/c². k=45 essentially TIGHT (within-hour work 2/c+47/m≤49/c≤17/c² needs 0.45k-3.1≥17 ⟹ k≥44.67).
⚠️ Doty's "290/c" shortcut is ARITHMETICALLY INVALID (173.7/c²<290/c needs c>0.599 not 0.2) — DO NOT use as a
formal bound; use 97.15/c². c_min=0.24 (Lemma 5.2) ⟹ clock envelope ≈1686.63(L+1) parallel; c=0.2 ⟹ 2428.75.
INTEGRATION: clock is the ENVELOPE inside Phase 3 (T_Ph3=clock envelope, work fits inside the synchronous hour,
NOT additive); ACROSS phases SUM envelopes along longest branch. THE CLOCK DOMINATES Phase 6 (1687L vs 52L).
HONEST Cfast: ≈1700 (c=0.24) / ≈2500 (c=0.2) for T_fast,seq≤Cfast·n(L+1) — NOT 17/52/369 (those were too small;
ORDER O(log n) parallel is right, CONSTANT must be ~1700 OR state PARAMETRICALLY in proved clock const Uclk +
prove a tighter clock theorem). Structural floor 17/c²≈295/hour at c=0.24 unless within-hour work is also tightened.

=== §60: §46 REPAIR FORMALIZATION-READY (family R3, rigorous, 4 lemmas) — Codex-ready on Xiang's approval ===
The complete replacement for the gapped Lemma 7.2 case split (faithful to Algorithm 6's strict guard
r.sample<m.exponent; NO modified transition rule):
LEMMA A (weighted top-two): from β_+≥0.4|M|2^{-ℓ} (Lemma 6.18) + μ(>-ℓ)≤0.002|M|2^{-ℓ} + all remaining majority
  at exp≤-(ℓ+2) (weight ≤1/4): 0.4 ≤ 0.002+x+y/2+(1-x-y)/4 ⟹ 3x+y ≥ 0.592 (TIGHT for this relaxation; a
  weighted-MASS inequality, NOT a count concentration). Lean form: 0.4≤0.002+x+y/2+(1-x-y)/4 ⟹ 3x+y≥0.592.
LEMMA B (Ph5 sampling floor): |R_{-ℓ}(0)|≥(x-0.01)|R|, |R_{-(ℓ+1)}(0)|≥(y-0.01)|R| (clip at 0); with r>0.24:
  ≥(0.24x-0.0024)n, ≥(0.24y-0.0024)n.
LEMMA C (live floor): consumption — R_{-ℓ} consumable ONLY by high-origin (strict guard -ℓ≮-ℓ) ≤0.004|M|;
  R_{-(ℓ+1)} by high-origin + initial-(-ℓ) [majority x|M| + minority ≤0.004|M|, each splits once moving to
  -(ℓ+1)]. |P(t)| ≥ |R_{-ℓ}(0)| + max(|R_{-(ℓ+1)}(0)|-(x+0.004)|M|,0) - 0.004|M|. Arithmetic sublemma:
  3x+y≥0.592 ⟹ F(x,y)=0.24x-0.0024+[0.24y-0.0024-0.51(x+0.004)]_+-0.00204 ≥ 0.02. EXACT min = 0.0224166 at
  x=1147/10250, y=2627/10250 (bracket=0 there). USE 0.02n as the named invariant. Holds for ALL Phase-6 prefix.
LEMMA D (drift): |P(t)|≥0.02n ⟹ per high agent split prob ≥2·0.02n/n²=0.04/n, ½-potential drop ⟹
  E[φ']≤(1-0.02/n)φ. φ(start)≤0.001|M|; after 150 ln n parallel time E[φ]≤0.001n^{-2}, Markov ⟹ Pr[φ>0]<1/(2n²).
=> slot 6 closes §46-FREE via Lemmas A-D (NO unproven dichotomy). The ONLY new obligation vs Doty's exposition is
the A/C arithmetic+consumption (uses the protocol's 2 compatible levels, not a modified rule). HOLD Codex dispatch
until Xiang approves adopting the union route (new lemma, diverges from printed Lemma 7.2 = method-flexibility call).
BLUEPRINT NOW COMPLETE END-TO-END: slots 6(§56/60)/7(§53,corrected v3)/8(§58), reserve floor(§48/52/57), WHP(§54),
expected backup(§51), clock const(§59). Every leaf has Doty's exact mechanism + verified constants + paper cites.

=== §61: SLOT 7 CLOSED (work7Tight, corrected high-band, VERIFIED axiom-clean uisai2) ===
Slot7CloseV2.work7Tight : PhaseConvergenceW — #print axioms = [propext, Classical.choice, Quot.sound], NO sorryAx
(independently re-verified, uisai2 3750-job build). Post = Inv7Sum ∧ minorityBlockMass σ l = 0 (HIGH band only;
deep tail → Phase 8). Drift on minorityBlockMass (block potential), gap-2 quarter-drop. §46-INDEPENDENT.
CARRIES 2 SATISFIABLE reachable obligations (the legit discharge targets, audited NON-vacuous):
 · ReachableMajorityBlockReady (block floor |G|≥0.8|M| for all reachable y) = Doty Lemma 7.4 deterministic
   prefix bound (0.87−0.064≥0.8, family3 R1/R2 cumulative-mass-budget). SATISFIABLE.
 · ReachableBlockMassNonincr (minorityBlockMass nonincreasing per phase-7 step) = TRUE monotonicity (every
   gap-0/1/2 reaction decreases block mass: within-block −2^{min}, block→below removes mass, boundary net <0;
   family3 R2 per-branch ΔΦ_- verified). DISCHARGEABLE by case analysis on the cancelSplit rule.
The v1 over-strong mass_le_block (§55) is GONE. Reusable correct lemmas retained.
Build-graph fix: Slot7Close.lean (shared bridge defs) now tracked; ExactMajority.lean imports Slot7CloseV2 (closure
build bo6lxk1yc confirming). REMAINING slot-7 work = discharge the 2 carried obligations (Lemma 7.4 floor +
block-mass monotonicity) — both true/satisfiable, standard carried-hypothesis discharge.

=== §62: SHARP MINORITY-MASS BOUND β⁻≤0.004|M|2^{−ℓ} IS THE UN-LANDED SHARED INPUT (slots 7/8 floors) ===
Codex (honest, no-fake) + independent grep CONFIRM: the sharp Doty per-level minority dyadic-mass bound
β⁻ ≤ 0.004|M|2^{−ℓ} (Lemma 6.17 / Theorem 6.2 minority output) is NOT CARRIED ANYWHERE (campaign's own
BranchAndBudget.lean:326/371/384 survey says so explicitly). The landed surface has only the COARSE unweighted
count minorityProfileMass ≤ 0.12|M| (MarginLedgers:73/264, PaperRegime:122) — too weak: the phase-7 depletion
needs the sharp dyadic β⁻ to get ≤0.064|M| (=16·0.004), giving |G|≥0.87−0.064=0.806≥0.8; the coarse 0.12 gives
only 0.87−0.12=0.75 < 0.8.
CONSEQUENCE: slot-7 ReachableMajorityBlockReady (|G|≥0.8|M|) AND slot-8 two-count (B₀≤0.2|M| via |G|≥0.8) both
carry floors that are SATISFIABLE (Doty proves β⁻) but DISCHARGE-BLOCKED on landing the sharp β⁻ bound. slots 7/8
remain valid CONDITIONAL closes; the sharp β⁻ is the shared remaining un-landed structural input.
DISCHARGE PATH = Doty Lemma 6.17 phase-3 minority-mass induction (per-hour dyadic decay, analog of the landed
majority confinement Lemma 6.16 ρ_h chain). [family3 R4 b91tvnc9h scoping: derivable from landed majority
confinement + conservation, or needs a separate minority induction? + slack c≤0.0044 for a coarser dyadic bound.]
Note: Lemma 7.4 floor discharge (codex_lemma74floor) correctly REPORTED this gap, did NOT fake (refused to disguise
the missing dyadic input as a new hypothesis) — §3.3 discipline working.

=== §63: LEMMA 6.17 SCOPED (family3 R4) — separate phase-3 minority induction, Codex dispatched ===
β⁻≤0.004|M|2^{−ℓ} is NOT derivable from majority confinement (total-mass route → only ≈0.2|M|2^{−ℓ}, 50× weak;
+ paper graph circular: 6.18 USES 6.17). It is a SEPARATE 6-row phase-3 hour induction (h∈{ℓ-5..ℓ}), β⁻(end_h)≤
ξ_h|M|2^{−h}, ξ chain 0.04375/0.0375/0.0267/0.0145/0.0056/0.004. MECHANISM = SAME-EXPONENT CANCELLATION (splits
preserve μ; cancels reduce β⁻). Recurrence ξ_h≥2ξ_{h-1}−d_h/m via Lemma 4.6 (=chernoff_two_sided_hoeffding) per-row
table (a_h,b_h,d_h); inputs gap α_h=0.4·2^{h-ℓ}, Lemma 6.11 below-leak ≤0.0012|M|2^{−h}, Lemma 6.15 above ≤
0.002|M|2^{−h}. SLACK c_max=0.004375 (0.87−16c≥0.8); can't stop early (ξ_{ℓ-1} alone → 0.78); may relax LAST row
to 0.004375. REUSE MainConfinementHours/HourCoupling + chernoff_two_sided_hoeffding. Codex dispatched (lemma617).
LANDS β⁻ → discharges slots 7/8 floors → near-unconditional work-side.

=== §64: LEMMA 6.17 BLOCKED ON CANCELLATION-CONCENTRATION ENGINE (Codex honest no-fake, 2nd) — drift-route scoping ===
Codex (honest, no shell) located the precise STRUCTURAL gap for the sharp β⁻ bound:
 · No β⁻ sharp-dyadic object exists; landed = coarse unweighted minorityProfileMass ≤ 0.12|M| (MarginLedgers:263,
   PaperRegime:120). Th6.2 entry surface (UsefulMainFloor:189) exports only hConfine, not β⁻/per-level rows
   (UsefulMainFloor:45 explicitly says the full bias-ledger β⁻≤0.004|M|2^{−ℓ} is NOT carried here).
 · The existing HourInduction (HourInduction:371) proves a BandConfined floor via a generic MGF interface
   (MainConfinementHours:41 MainHourSquaringAtom Φ/Q/Post), NOT the same-exponent cancellation count for β⁻.
 · chernoff_two_sided_hoeffding (Concentration:168, = Lemma 4.6) is available BUT needs iIndepFun independent
   [0,1] trials; NO bridge from the phase-3 Markov-scheduler same-exponent cancellation window to iIndepFun exists.
 · Campaign audits already flag this: BranchAndBudget:370, SurvivalAccounting:388.
=> Lemma 6.17 (sharp β⁻) genuinely needs a NEW cancellation-concentration engine. Codex correctly refused the
"assume the per-row cancellation table → β⁻" SHELL (fake landing).
ALTERNATIVE ATTACK VECTOR (not a new avenue — a different tactic): slots 7/8 drove their potentials down via
OneSidedCancel.geometric_drift_tail ON THE MARKOV KERNEL (no iIndepFun). Reformulate Lemma 6.17 as a per-hour β⁻
MULTIPLICATIVE DRIFT (1−c_h/n) using that SAME engine — same-exponent cancellation vs the gap surplus α_h, composed
over the 6 hours. [family3 R5 b2ll9ou9z scoping: viable, or does the small surplus genuinely need the two-sided
Lemma-4.6 hitting-time?]
STATUS: slots 7/8 remain VALID conditional closes (floors satisfiable, Doty-proven). FULLY-unconditional work-side
hinges on the sharp β⁻, which is the genuine deep frontier — either the drift reformulation (reuses landed engine)
or building the iIndepFun cancellation bridge. ESCALATE the invest-vs-accept-conditional decision to Xiang.

=== §65: β⁻ ROUTE PRECISELY SCOPED (family3 R5) — needs kernel-native two-sided cancellation engine ===
RAW drift-reuse (E[β⁻']≤(1−c_h/n)β⁻ + slot-7/8 geometric_drift_tail) does NOT work for Lemma 6.17:
 · β⁻ drift is LOCAL/AFFINE (only minority AT exponent −h cancellable by the hour-h same-exp majority pool; above
   still splitting down, below untouched) — E[Δβ⁻|c] = −2^{−h}·2A_h B_h/(n(n−1)), NOT global −(c_h/n)β⁻ without an
   additive leak floor (subtract Lemma 6.15 above ≤0.002|M|2^{−h} + Lemma 6.11 below ≤0.0012|M|2^{−h}).
 · Each hour = CONSTANT parallel time; goal = CONSTANT-FACTOR count drop at 1−O(n^{−2}). geometric_drift_tail works
   for slots 7/8 only because they run Θ(log n) time to a tiny threshold (Φ_0/θ poly ⟹ e^{−Θ(log n)} = n^{−Θ(1)}).
   A one-sided static-floor drift needs ~7.19/m > the paper's 6/m cancel subwindow; Markov-tail gives only constant
   failure for a constant-factor target unless run Θ(log n)× longer (breaks O(log n) over O(log n) hours).
MINIMAL ENGINE (§46-independent, NO iIndepFun): a KERNEL-NATIVE TWO-SIDED CANCELLATION CONCENTRATION lemma —
 A_t,B_t counts, one-step success prob ≥ 2(an−C_t)(bn−C_t)/(n(n−1)) until C_T = dn cancellations; for T ≥
 (1+ε)n·[ln b−ln a−ln(b−d)+ln(a−d)]/[2(a−b)], Pr[C_T<dn] ≤ exp(−Ω(n)). Prove via Doob/Freedman/Azuma on the
 cumulative cancellation count (the paper uses Azuma in §4/Lemma 6.15, so consistent). This is the SIBLING of the
 landed one-sided OneSidedCancel engine (slots 7/8 used one-sided).
THEN Lemma 6.17 = clean 6-row induction: per row, Lemma 6.15/6.11 isolate A_h,B_h at exponent −h, the two-sided
 engine gives d_h|M| cancellations → ξ_h ≤ 2ξ_{h-1}−d_h/m; union 6 row-failures; condition on prev good event (NO
 inter-row independence needed). Table (a_h,b_h,d_h,ξ_h) in §63.
=> DECISION #3 (Xiang, escalated, NOW PRECISELY SCOPED): build the kernel-native two-sided cancellation engine
(substantial foundational theorem — the one-sided sibling exists) → Lemma 6.17 → discharge slots 7/8 floors →
fully-unconditional work-side. VS accept slots 7/8 as valid conditional closes (Doty-proven satisfiable floors).
NOT launching the engine build unilaterally (it pre-empts the accept-conditional option = Xiang's call).

=== §66: CANCELLATION ENGINE — formalization-ready (family3 R6) ===
The kernel-native two-sided cancellation concentration (Lemma-4.6 analogue, NO iIndepFun, NO Freedman):
INTEGRATED INVERSE-RATE CLOCK H(k)=Σ_{i<k}1/q_i, q_i=2(A₀−i)(B₀−i)/(n(n−1)). Stopped Z_t=H(C_{t∧τ_D})−(t∧τ_D)
is a SUBMARTINGALE (E[ΔH|F_t]≥q_i·(1/q_i)=1; time term −1 ⟹ E[ΔZ]≥0). Bounded incr |ΔZ|≤L=max(1,max(1/q_i−1)).
Azuma lower-tail: ∀T≥H(D), (K^T)x₀{C<D} ≤ exp(−(T−H(D))²/(2TL²)). Constant-fraction drop (D=⌊dn⌋, d<b<a const)
⟹ q_min=Θ(1), L=O(1), H(D)=Θ(n) ⟹ exp(−Ω(n)) ≫ 1/(2n²). RAW fixed-min compensator is TOO WEAK (gives 0.0237mn
< 0.05mn target); the inverse-rate clock captures that early cancellations are fast (A,B large). Azuma suffices
(not Freedman). Core lemma: abstract K,C,D,q with H1 C(x₀)=0 / H2 monotone unit incr / H3 K{C=i+1}≥q_i → tail.
Two-sided instantiation: q_i from count floors A(x)≥A₀−i, B(x)≥B₀−i + uniform pair scheduling. Codex dispatched
(cancelengine, abstract reusable). This is the engine for Lemma 6.17's minority rows.

=== §67: CONVERGENCE — BOTH decisions need the WEIGHTED-MASS Theorem 6.2 surface (2 honest no-fake Codex reports) ===
slot-6 §46-repair Codex ALSO honestly refused to fake: Lemma A (3x+y≥0.592) needs the WEIGHTED dyadic-mass outputs
β⁺≥0.4|M|2^{−ℓ} + μ(>−ℓ)≤0.002|M|2^{−ℓ}, but the landed surface has only COUNT bounds (hMassAbove = count cap
0.06|M|, NOT the weighted 0.002 cap; Theorem62Dichotomy:16 already notes the aggregate+count surface insufficient).
So BOTH Xiang-decisions converge on the SHARED FOUNDATION = the WEIGHTED-MASS Theorem 6.2 bias-ledger surface:
 (a) majority mass β⁺ ≥ 0.4|M|2^{−ℓ} (gap lower bound)  — needed by #1 (§46 repair, Lemma A)
 (b) weighted mass-above μ(>−ℓ) ≤ 0.002|M|2^{−ℓ}        — needed by #1
 (c) minority β⁻ ≤ 0.004|M|2^{−ℓ} (Lemma 6.17)           — needed by #3 (β⁻ unconditional), via the §66 engine
The landed Theorem62Paper exports COUNTS, not weighted masses. BUILD PLAN (Xiang approved adopt #1 + do #3 uncond):
 1. §66 cancellation engine (Codex in flight) — foundation for (c).
 2. (a)+(b) majority/mass-above weighted bounds [family R4 weightedmass scoping: derivable from conserved gap +
    count confinement + choice of ℓ, or need phase-3 mass induction (Lemma 6.15/6.16)?].
 3. (c) Lemma 6.17 minority rows via the engine.
 → unblocks slot-6 §46 repair (#1) + makes slots 7/8 floors dischargeable (#3). Both honest no-fake reports point
 here: the weighted-mass Theorem 6.2 surface is THE shared deep foundation for the unconditional work-side.

=== §68: WEIGHTED-MASS FOUNDATION — build plan refined (family R4) ===
The §46-repair (decision #1) weighted inputs factor cleanly BY ENGINE:
 (a) majority mass β⁺ ≥ 0.4|M|2^{−ℓ}: SHORT conserved-gap lemma. g=β⁺−β⁻ (signed-bias invariant), ℓ chosen so
     0.4|M| ≤ g·2^ℓ < 0.8|M|; β⁻≥0 ⟹ β⁺=g+β⁻ ≥ g ≥ 0.4|M|2^{−ℓ}. NO phase-3 induction. Lean: gapMassLower
     (g=β⁺−β⁻ ∧ β⁻≥0 ∧ 0.4|M|≤g·2^ℓ ⟹ β⁺≥0.4|M|2^{−ℓ}). (neg-majority case: |g|, sign(g).)
 (b) mass-above μ(>−ℓ) ≤ 0.002|M|2^{−ℓ}: NOT derivable from counts (it's the UPPER/heavy tail, exponents >−ℓ with
     large dyadic weights; small count can carry huge mass — e.g. 0.02|M| at −(ℓ−1) = 0.04|M|2^{−ℓ} ≫ 0.002). It is
     the h=ℓ endpoint of Lemma 6.15 = a base-4 φ(>−ℓ) POTENTIAL DROP via O_h split partners + log supermartingale/
     Azuma. SAME drift-tail shape as the LANDED phase-6 φ-drift (ONE-SIDED, NOT the two-sided cancel engine) — likely
     REUSES that engine, stopped at a POSITIVE threshold 0.001|M| (easier than →0). [family R5 scoping the reuse +
     the O_h partner floor + minimal input set.]
 (c) minority β⁻ ≤ 0.004|M|2^{−ℓ} (decision #3): Lemma 6.17 via the §66 two-sided cancellation engine (Codex in
     flight) + the 6-row induction.
BUILD ORDER (serialized on uisai2:Ripple): §66 engine (in flight) → (a) gapMassLower [short] → (b) Lemma 6.15
mass-above [reuse φ-drift engine, family R5] → §46 repair (#1) closes with (a)+(b) → (c) Lemma 6.17 [§66 engine] →
slots 7/8 floors discharge (#3). Once (a)+(b) land, slot-6 §46 repair (codex_slot6adopt) reruns + closes.

=== §69: (b) Lemma 6.15 SCOPED (family R5) — chains the phase-3 weighted-mass induction; honest scope ===
Lemma 6.15 (mass-above μ(>−ℓ)≤0.002|M|2^{−ℓ}) reuses the φ(>−ℓ) base-4 potential (same as landed phase-6) BUT a
DIFFERENT wrapper: NOT Markov-to-zero (needs Θ(log n) time), but a LOG-SUPERMARTINGALE constant-factor drop
(Φ=ln φ, Azuma) in the constant 41/m hour window. Details:
 · Partner floor O_ℓ ≥ 0.15|M| (Lemma 6.13 |O_h|≥(0.97−2ρ_{h-1})|M|, Thm 6.12 τ_ℓ≥0.15). Log drift E[ΔΦ]≤−0.15m/n.
 · STARTING bound φ(>−ℓ)(t₀) ≤ 0.412|M| = ρ_{ℓ-1}(0.408, Lemma 6.16 h=ℓ-1) + 4·0.001 — CHAINS to the previous-hour
   total-mass bound. NOT a crude O(n4^L) start.
 · Bounded increments |ΔΦ| ≤ 4^{q-1}/(0.002|M|) = O(n^{-0.53}) from Lemma 6.14 (max exponent ≤ −h+q, q=⌊ln n/3⌋).
   Azuma → failure small. Markov-to-zero gives a USELESS 0.877 failure (E[φ_T]≈0.000877|M| barely under 0.001).
 · Expected log drop 6.15 ≥ needed ln(412)≈6.02 (slack 0.12) over T=41n/m interactions.
HONEST SCOPE (no over-claim): the "weighted-mass Theorem 6.2 surface" both decisions need is NOT a couple of endpoint
lemmas — it is the PHASE-3 WEIGHTED-MASS BIAS-LEDGER INDUCTION (Lemmas 6.13 O_h floor, 6.14 max-exponent, 6.15
mass-above φ-log-drift, 6.16 total-mass cancel ρ_h chain, 6.17 minority β⁻). A substantial phase-3 sub-campaign.
Reuses: landed hour-window machinery + landed φ-drift potential; NEEDS: a log-supermartingale Azuma wrapper (for
6.15) + the §66 two-sided cancel engine (for 6.17) + the count→mass conversions.
ENGINE UNIFICATION: (b) [6.15, log-φ Azuma] and (c) [6.17, cancel-clock Azuma] are SIBLINGS — both Azuma
constant-factor-drop-in-constant-time wrappers (different potentials), NOT the Markov-to-zero geometric tail. The
§66 engine (Codex in flight) is (c)'s; (b) needs the log-φ sibling. Only (a) gapMassLower is short/standalone.
BUILD: §66 cancel engine (in flight) → log-φ Azuma wrapper → 6.13/6.14 floors → 6.15 → 6.16 ρ-chain → 6.17 →
(a) gap → §46 repair (#1) → slots 7/8 discharge (#3). The genuine deep foundation, Xiang-approved (adopt+uncond).

=== §70: COMPLETE REMAINING FRONTIER for FULL unconditionality (work-side assembled, mapped 2026-06-17) ===
Everything else (correctness + time, both decisions, the entire phase-3 mass induction 6.13-6.17 + consumption +
the §46-free repair + the cancellation engine) is PROVEN + verified axiom-clean in the full ExactMajority closure.
The remaining un-discharged leaves form a FINITE NAMED SET:
(1) TWO §6 clock-Main POINTWISE snapshots (deepest; PROVED to need the clock chain, 2 non-invariance refutations
    phase3_local_perAgent_route_false + biasedMainIndexLeHour_not_phase3_step_invariant):
    · hIdx = WindowReconciliation.BiasedMainIndexLeHour (biased dyadic index ≤ clock hour).
    · hNoMainAbove = HourCoupling.mAbove (h+1) c = 0 (no Main above hour h+1).
    (ClockFrontSnapshots.SnapshotLeaves names them; clockFrontSnapshots_of_reachable consumes them →
     AllBiasedMainBelow → Phase3ActiveBand → MassToCount → Lemma613OFloor O_ℓ floor → 6.15.)
(2) Clock reached-fraction hReach (≥0.97·M Mains at hour h) — Lemma613OFloor's other carried input; clock-chain.
(3) 6.15 Azuma ingredients: the Jensen-lift (multiplicative φ-drift → log-supermartingale hdrift) + the numerical
    n≥n₀ tail (exp(-Θ(n^0.06)) ≤ 1/(2n²)).
(4) Lemma 5.2 role split (|M|≈n/2, |R|/|C|≥n/4, m≥0.495, r>0.24) — the shared foundational concentration leaf.
(5) small count-gaps: mainLevelCount ≤ majorityLevelCount (6.17 successor); dominant-level choice hdom (gapMassLower).
The clock-chain leaves (1)(2) DOMINATE: they are the §6 clock-Main coupling's pointwise content, itself built-
modulo-its-own per-step concentrations (Lemma610Potential/StoppedAzuma, FrontShapeInduction frontShapeAt_holds,
ClockCeiling). FULL closure = closing the clock chain to its leaves. The whole proof is assembled; this set is all
that separates conditional from fully-unconditional.

=== §71: FRONTIER REFINED — both subsystems reduce to per-step concentration leaves (2026-06-17) ===
The work-side carried leaves (§70) connect to TWO foundational subsystems, BOTH "built-modulo-their-own-per-step
concentrations":
 · §6 CLOCK chain: hIdx/hNoMainAbove/hReach ⟵ front-shape ceiling (beyond(T+1)=0, a carried hyp of
   frontShapeAt_holds) ⟵ FrontShapeInduction per-minute SEEDING concentrations. (Lemma610Potential/StoppedAzuma,
   ClockCeiling are the landed coupling; the leaves are the front-seeding tails.)
 · PHASE-0 ROLE SPLIT (Lemma 5.2): RoleSplitGood-whp ⟵ not_RoleSplitGood_subset_not_mile_union_post_residual
   (Phase0RoleSplitRealTail:250) ⟵ the per-MILE concentration residuals.
6.15 Azuma ingredients: hdrift DISCHARGED (Phase3JensenLift.phiLog_drift_of_multiplicative, tangent-line Jensen);
remaining = hdiff (⟵ Lemma 6.14 max-exp ⟵ clock front) + htail (numerical exp(-Θ(n^0.076))≤1/(2n²), n≥n₀ arith).
=> STRUCTURAL END-STATE: the ENTIRE proof (correctness + time, both decisions, phase-3 mass induction, §46 repair,
consumption) is ASSEMBLED + verified axiom-clean. Remaining un-discharged = the per-step concentration leaves of
the clock front-shape induction + the phase-0 role split (foundational probabilistic primitives, each
built-modulo-leaves), PLUS the self-contained arithmetic leaves (htail, count-gaps mainLevelCount/hdom). A precise,
finite, deep set. Full closure = closing the two subsystems' per-step concentrations.

=== §72: DEEPEST RESIDUALS — the dependency tree bottomed out (2026-06-17) ===
The ENTIRE exact-majority Theorem 3.1 proof (correctness + time, both decisions, phase-3 mass induction 6.13-6.17,
§46 repair, consumption, the cancellation engine, the bridges) is ASSEMBLED + verified axiom-clean in the full
closure. Tracing every carried obligation to the bottom yields TWO foundational probabilistic residuals + a small
self-contained set:
TWO DEEPEST RESIDUALS (both probabilistic-tail→pointwise gaps in built-modulo-their-leaves subsystems):
 (A) JOINT CLOCK-FRONT INDUCTION (pointwise): WindowReconciliation.MainHourBelow (h+1) c [pointwise] + hIdx
     (BiasedMainIndexLeHour). The clock front-shape is PROVEN (frontShape_step/front_width_at, "not assumed") and
     Lemma610StoppedAzuma.lemma610_honest gives a PROBABILISTIC stopped-Azuma tail — but NOT the POINTWISE zero the
     active-band needs. The gap = the joint clock-front induction / boundary-feeder cap (pointwise content). Readout
     mAbove_eq_zero_of_mainHourBelow + the snapshot consumers all WIRED; only the pointwise MainHourBelow + hIdx remain.
 (B) PHASE-0 ROLE SPLIT per-mile concentration: RoleSplitGood-whp ⟵ not_RoleSplitGood_subset_not_mile_union_post_
     residual ⟵ the per-mile concentration residuals (Lemma 5.2's foundational tail).
SELF-CONTAINED REMAINDER (smaller): hdom (needs the ℓ:=⌈log₂(g/0.4|M|)⌉ formal construction + threading, a refactor);
mainLevelCount ≤ majorityLevelCount (6.17 successor count-gap, possibly needs minority-at-ℓ added); 6.15 hdiff
(⟵ Lemma 6.14 max-exp ⟵ the same clock-front (A)).
ABOVE THE RESIDUALS: 6.15 hdrift (Jensen ✓) + htail (numerical ✓); the entire phase-3 mass induction; the §46-free
repair; the consumption chain; the two decisions — ALL PROVEN + verified. The two deepest residuals (A)(B) are the
foundational probabilistic primitives of the clock + role-split subsystems; full unconditionality = closing them.

=== §73: RESIDUAL (A) RE-TARGETED — the pointwise mAbove strand is OVER-STRONG (2026-06-17) ===
ADJUDICATION (Xiang-proxy, substrate 审稿即科学探索, family ChatGPT verified against Doty §6 + my surface):
Lemma 6.15 does NOT need "no biased Main above −ℓ" / mAbove(h+1)=0. Such agents MAY exist (6.15 proves their
MASS is small). 6.15's Azuma bounded-differences step needs only the WEAKER far-above cutoff
  max biased exponent ≤ −ℓ + q,  q=⌊ln n/3⌋   (Lemma 6.14, whp),
which bounds |Δ ln φ| ≤ 4^{q−1}/(0.002|M|). VERIFIED: my Phase3NumericalTail/Lemma615 already consume this as
`hdiff : |Φ y − Φ x| ≤ c` — NOT mAbove=0. So the pointwise mAbove=0 / MainHourBelow / hNoMainAbove /
ClockNoMainAbove / SnapshotLeaves strand is STRONGER THAN THE PAPER and OFF the 6.15 critical path — an
artifact of the snapshot threading. It stays committed as a sound deterministic readout but is NOT pursued
further (do NOT grind the joint clock-front POINTWISE induction).
CORRECT residual (A), the whp chain (LARGELY BUILT):
  Lemma 6.10 leakage Azuma (Φ=m_{>h}−1.1c_{>h}, m_{>h}≤0.0012 whp) — BUILT: Lemma610Potential (potential +
    bounded increment diff_stopped) + Lemma610StoppedAzuma (Azuma tail), carrying hreg:Regime (synchronous-hour
    window c_{>h}≤1/11 = the clock front-shape, "largely proven").
  → Lemma 6.11 leakage count ≤0.0024|M| whp  → Lemma 6.13 O_ℓ partner floor ≥0.15|M| whp (my carried hyp)
  + Lemma 6.14 max-exp cutoff ≤−ℓ+q whp (1−O(n^{-12})) = my carried hdiff input.
  Union all into the phase-3 mass-above failure budget (matches §46 union-route + the whole proof's whp shape).
TRUE BOTTOM of (A): the Regime/synchronous-hour window (clock front-shape, largely proven) + the 6.10→6.14
max-exp-cutoff derivation. NOT a pointwise joint induction. This is a major course-correction saving the grind.
WHAT MIGHT BE WRONG: family's "6.14 cutoff persists deterministically over the 6.15 interval (splits only
decrease exponent)" needs a line-check; and the 6.10/6.11/6.14 numbering is family's read of Doty (corroborated
by internal consistency + match to my carried hyps, not re-read line-by-line this turn).

=== §74: RESIDUAL (B) — two valid routes, satisfiability audit decides (2026-06-17) ===
family2 (ChatGPT, verified vs Doty §5): Doty's ACTUAL Lemma 5.2 is NOT the MGF/Azuma count-martingale. It is:
 (1) TOP split (Main vs RoleCR): Chernoff via self-correcting imbalance |D|=|M−S| dominated by a symmetric
     ±1 walk (drift always toward 0) → Pr(|D|≥ηn) ≤ 2exp(−η²n/2); M=(n+D)/2, S=(n−D)/2.
 (2) SECOND split (RoleCR U,U→R,C): Janson geometric waiting-time (Doty Thm 4.3/Cor 4.4), NOT a martingale.
     #reactions x: C=x, R=s−x, U=s−2x; drive U≤ρs in O(1) time → C,R ≥ (1−ρ)/2·s. Same-state pair rate
     u(u−1)/(n(n−1)) (NOT the 2|A||B| cross-rectangle).
 (3) FINAL C/R floors: DETERMINISTIC arithmetic from x. With s≈n/2: |C|,|R| ≥ (1−ε)n/4.
CRUCIAL CORRECTION (correctness, not just style): the "milestone = all RoleMCR drained" does NOT guarantee
the Clock/Reserve split — the second split is a SEPARATE O(1)-time process. Stopping at the milestone may leave
RoleCR undecided → too few Clock. Count-window must attach to END of Algorithm 0 (or the milestone chain must
include the second split down to a small residual).
ROUTE CHOICE (Xiang-proxy, do NOT break tie on preference — let science decide): Codex built the MGF/Azuma
route (post_residual_subset_fiveBad → 5-event union, + topSplit_or_rest decomposition + topSplitWindow_whp),
reusing the ALREADY-BUILT axiom-clean per-count drifts (RoleSplitC0MGF). family2 says MGF is asymptotically
valid (exponent n/log n still gives 1/n²) but "less faithful, harder to connect to Doty's constants." DECISION
RULE: when Codex's build lands, run the §3.3 SATISFIABILITY AUDIT on the clockCount/reserveCount window
targets — does the built clockCount_lower_deficit drift genuinely REACH (1−η)n/4 (i.e. capture the second
split), or only a weaker floor? If REACHES → accept MGF route (reuses landed infra). If NOT → redirect to
family2's faithful Chernoff-domination + Janson route (saved: HANDOFF/family2_doty_lemma52_route.md), whose
final C/R is DETERMINISTIC arithmetic (cleaner constants).

=== §75: RESIDUAL (A) DISCHARGE DAG — joint hour-induction reusing BUILT infra (2026-06-17) ===
family A-wire (ChatGPT, verified vs Doty §6) gives the exact per-hour DAG. Both my carried phase-3 hyps
discharge from a single clock-front/Regime input cascading through a JOINT HOUR-INDUCTION:
  Clock-front + Regime_h ⟹ 6.10_h ⟹ 6.11_h ; 6.11_h + 6.16_{h-1} + clock-len ⟹ 6.13_h ;
  6.13_{h-q..h-5} + 6.15_{h-q} + clock-len ⟹ 6.14_h ; 6.13_h+6.14_h+6.15_{h-1}+6.16_{h-1} ⟹ 6.15_h.  (q=⌊ln n/3⌋)
  My O_ℓ floor ≥0.15|M| = 6.13 at h=ℓ (ρ_{ℓ-1}=0.408 → 0.97−2·0.408=0.154→0.15). My hdiff max-exp ≤−ℓ+q = 6.14 at ℓ.
EACH LEMMA'S NATURE + REUSE STATUS:
 · 6.10 (leakage Azuma Φ=m_{>h}−1.1c_{>h}): BUILT — Lemma610Potential + Lemma610StoppedAzuma, carrying Regime
   (c_{>h}≤1/11 = my hyp, the algebraically-sufficient drift condition 1−1.1(1−c_{>h})<0). The HARD probability.
 · 6.11 (leakage count ≤0.0024|M|): DETERMINISTIC doubling on top of 6.10 (each high O splits once → ×2). No new
   concentration. "Lemma611 = Lemma610 + phase3_split_leak_doubling."
 · 6.13 (O_ℓ floor): process-of-elimination ARITHMETIC: from 6.16_{h-1} (μ≤ρ_{h-1}|M|2^{-h+1} → ≤2ρ_{h-1}|M| biased
   ≥−h) + 6.11 leakage → |O|≥(0.9976−2ρ_{h-1})|M|; then Lemma 4.7 epidemic pull (a=0.9c, within 2/c) → |O_h|≥
   (0.97−2ρ_{h-1})|M|. 6.16 ρ-chain BUILT (Lemma616TotalMass). Need: Lemma 4.7 epidemic-pull + the arithmetic.
 · 6.14 (max-exp cutoff): NOT a new Azuma — base-4 potential φ(>−h+q) DRAIN-TO-ZERO. Same split-potential
   contraction E[φ(t+1/n)]≤(1−0.77m/n)φ(t) as 6.15 (REUSE phase3_phiMass_multiplicative_drift), run 51(q-5)n/m
   interactions → E[φ]=O(n^{-12}) → Markov (φ nonneg int) → P[φ>0]=O(n^{-12}). Partner floor 6.13 early-hour
   |O(≥h-q)|≥0.77|M|. REUSE the built 6.15 drift + a Markov-to-zero wrapper.
 · 6.15: BUILT modulo 6.13/6.14 (hdrift Jensen ✓, htail numerical ✓, hdiff = this 6.14).
VERDICT: residual (A) is a JOINT HOUR-INDUCTION over BUILT pieces (6.10 Azuma, 6.16 ρ-chain, 6.15 φ-drift) +
deterministic bridges (6.11 doubling, 6.13 elimination arithmetic, 6.14 Markov-to-zero reusing 6.15 drift) +
Lemma 4.7 epidemic-pull + the induction threading. NOT a hard new probabilistic frontier — the hard probability
(6.10, 6.15) is done. The pointwise mAbove strand (§73) stays parked. Saved: HANDOFF/family_A_dependency_dag.md.

=== §76: hReach = Lemma 4.7 catalytic pull = the SAME Janson engine as (B) CRDrain (2026-06-17) ===
family A-reach (ChatGPT vs Doty §4/§6.13): hReach (the last genuine (A) piece) is a Lemma 4.7 CATALYTIC PULL,
NOT a new martingale, and INDEPENDENT of the 6.10 Regime supermartingale (both under the same broad clock-front
event, but hReach needs only the start_h fact ≥0.9|C| at hour ≥h).
 · Lemma 4.7: catalyst A (≥an), susceptible B (b₁n → b₂n), each A-B interaction forces B to leave. Per-step rate
   p_i ≳ 2a·i/n. Time T = Σ_{i=b₂n+1}^{b₁n} Geom(2ai/n), E[T] ≤ (n/2a)ln(b₁/b₂); parallel (ln b₁−ln b₂)/(2a).
   Completion-to-zero ≤ 5ln n/(2a) w.p. 1−O(1/n²). Sibling of Lemma 4.5 (epidemic i,s→i,i, rate i(n-i)), SAME
   Janson Theorem 4.3/Cor 4.4.
 · 6.13 instantiation: a=0.9c, b₁=(0.9976−2ρ_{h-1})m ≤0.7976m, b₂=0.0276m → E[t]≤1.89/c → pull completes <2/c whp.
   hReach proves |O_{<h}(t)| ≤ 0.0276|M| after the 2/c window; combined with |O_{≤h}|≥(0.9976−2ρ_{h-1})|M| (6.16
   + 6.11) gives |O_h|≥(0.97−2ρ_{h-1})|M| = 0.154|M| at h=ℓ (ρ=0.408) → my 0.15 floor.
 · LEAN: discharge via the tree's geometric-sum Janson — killed_geometric_tail / decreasing_janson_tail (GatedGeo
   metricDrift / HtTractableSlots), with per-step rate 2ai/n. EpidemicTime (Lemma 4.5) alone is NOT the black box;
   the killed_geometric_tail with rate-floor 2ai/n IS Lemma 4.7.
CONVERGENCE: BOTH deepest residuals' remaining genuine pieces are the SAME "Janson catalytic-drain" shape:
 (A) hReach: O_{<h} drained to 0.0276|M| at rate 2ai/n.
 (B-rest) CRDrain: undecided RoleCR drained to δs at rate u(u−1)/(n(n−1)).
Both → killed_geometric_tail. The campaign's "every atom bottoms out at the same death-rectangle/geometric-sum"
finding holds at the very bottom. Saved: HANDOFF/family_A_reach_lemma47.md.

=== §77: SLOT-3 INDUCTION SKELETON (family2 R1, verified vs Doty §6 Thm 6.12) — the keystone ===
The Lean structure for the whole phase-3 joint hour-induction (6.13-6.17):
 · Hour-local predicates H13(h),H14(h),H15(h),H16(h). Core(h) := H13∧H14∧H15∧H16.
 · UPWARD strong induction h=0..ℓ, IH = ∀k<h, Core(k). (NOT downward — all deps go backward: h-1 or h-q.)
   Cleanest Lean: Prefix(H):=∀k≤H,Core(k) via Nat.rec (strong history w/o repeated strong_induction_on).
 · Per-hour step deps (matches §75 DAG): H13(h)⟸H16(h-1)+6.11(h); H14(h)⟸H15(h-q)+H13[h-q,h-5];
   H15(h)⟸H13(h)+H14(h)+H15(h-1)+H16(h-1); H16(h)⟸H15(h)+H16(h-1)+6.11(h)+cancellation(4.6).
 · 6.17 is a SEPARATE later induction over h∈[ℓ-5,ℓ], base h=ℓ-5 from 6.16, step uses H17(h-1)+6.15+6.11+4.6.
 · UNION over O(log n) hours (NOT one global martingale): per-hour fails 6.14:n^{-12}, 6.15:exp(-Θ(n^0.06)) →
   ε₃=Σε_h. Allocate ε_h=1/((L+1)n²) OR use stronger tails + prove (L+1)n^{-12}≤n^{-2} under L=O(log n).
 · Base: h=0 trivial (6.13/6.15), 6.14 vacuous h<q, mass-chain base = 6.16 from Lemma 5.3 (|g|<0.025m,
   start mass ≤0.03|M|, ℓ-5≥0).
 · Lean targets: coreAll : ∀h≤ℓ, Core h ; minorityAll : ∀h∈[ℓ-5,ℓ], H17 h ; → phase-3 exit theorems.
6.11 BRIDGE (family3 R1): Leak_h ≤ 2·m_{>h} where m_{>h} must be the CUMULATIVE "ever-pulled-high" resource
 (NOT current {O.hour>h} count — after a high-O splits its biased descendants stay in the leak set). Charge
 Leak_h ↪ HighPull_h×{0,1}. CHECK: is our Lemma610 m_{>h} cumulative or current?
6.14 BRIDGE (family3 R1): REUSE the 6.15 multiplicative φ-drift with γ=0.77 (NOT 0.15), r=−h+q, run
 N=51(q-5)n/m interactions → E[φ_N]≤(1-0.77m/n)^N·0.001|M|=O(n^{-12}) → integer-Markov P[φ_N>0]≤E[φ_N].
 Abstract reusable: |O_split|≥γ|M| ⟹ E[φ'(>r)]≤(1-γm/n)φ(>r); 6.14 γ=0.77+Markov, 6.15 γ=τ_h≥0.15+Azuma.
Saved: HANDOFF/family_slot3_induction_skeleton.md + family_slot3_611_614_bridges.md.

=== §78: SLOT-3 clock-front discharge — the GoodClock(0..ℓ) bundle + hReach/Regime SPLIT (family R2/R4) ===
hReach and Regime are INDEPENDENT clock-front facts (do NOT conflate):
 · hReach (6.13 O-floor) needs ONLY: clock-start catalyst floor |{C:hour≥h}|≥0.9|C| at start_h + clock-hour
   monotonicity. NOT the 6.10 supermartingale. Via Lemma 4.7 (a=0.9c or 0.899c, b₁=0.7976m, b₂=0.0276m → pull
   completes <2/c whp, exp(-Θ(n))). Discharges from clock start/monotone alone.
 · Regime (6.10 leakage Azuma) needs: c_{>h}≤1/11 (fast-front smallness) over the stopped interval. This is the
   QUANTILE/TAIL fact (NOT width — §, family4 R1). Plus endpoint c_{>h}(end_h)=0.001 + hour-length upper (Azuma
   variance O(1/n)) from Theorem 6.9.
MINIMAL CLOCK DISCHARGE = expose ONE GoodClock(0..ℓ) event with, per hour r≤ℓ:
 (1) c_{>r}(t)≤1/11 for t≤end_r [Regime/6.10]; (2) c_{>r}(end_r)=0.001 [endpoint]; (3) |{C:hour≥r}|≥0.9|C| at
 start_r [hReach/6.13]; (4) hour-length upper end_r−·=O(1) [Azuma var]; (5) hour-length lower end_r−start_r ≥
 [0.45(k-2)-2.2]/c², k=45 [fits 2/c+47/m AND 51(q-5)/m for 6.14]; (6) clock-hour monotonicity/persistence.
 Theorem 6.9 supplies (4)(5); the quantile front-shape supplies (1)(2)(3); monotonicity (6).
ACTION: CHECK whether our proven front-shape (frontShape_step/front_width_at) is a QUANTILE-tail theorem (gives
1-3) or only a WIDTH theorem (does NOT give c_{>h} small — a narrow band could sit entirely above h). If only
width → the quantile/Theorem-6.9 front is a real remaining clock-front leaf. Adapter (trivial): 1000·cAbove ≤
clockCount → 11·cAbove ≤ clockCount. Saved: HANDOFF/family_slot3_goodclock_bundle.md, family_slot3_regime_quantile.md.
NOTE: family R2 hdom answer was re-statement-padded + truncated before the hdom specifics (§2.6 rejected); re-asked tight (R3).

=== §79: hdom CONSTRUCTION (family R3, verified vs Doty Thm 6.2) — closes the dominant-level leaf ===
Doty Thm 6.2: −ℓ = ⌊log₂(g/(0.4|M|))⌋, i.e. ℓ = ⌈log₂(0.4|M|/G)⌉ (G=|g|). Window 0.4|M| ≤ G·2^ℓ < 0.8|M|
("substantial relative gap"); β⁺ ≥ g = g_ℓ·2^{-ℓ} ≥ 0.4|M|·2^{-ℓ} (= our gapMassLower conclusion).
LEAN: ℓ := Nat.find {k : (2/5)|M| ≤ G·2^k}. (2/5)|M| ≤ G·2^ℓ by Nat.find_spec; minimality (ℓ>0) → G·2^{ℓ-1} <
(2/5)|M| → ×2 → G·2^ℓ < (4/5)|M|. Replaces carried hdom with a CONSTRUCTED ℓ.
CRUCIAL: existence holds ONLY under the small-gap entry G < 0.025|M| (Lemma 5.3 output). Large gaps (G≥0.8|M|)
have NO valid ℓ≥0 — Doty handles them earlier (Thm 6.2 is the small-gap case). And ℓ≥5 (G·2^4<0.025|M|·16=0.4|M|)
→ ℓ-5≥0, which 6.17's induction base needs. So hdom = Nat.find construction CARRYING the small-gap Pre (Lemma 5.3).
Saved: HANDOFF/family_slot3_hdom_construction.md.

=== SLOT-3 DESIGN STATUS (after the 猛攻 rolling harvest) ===
DONE (design): §75 DAG · §77 induction skeleton (keystone) · §78 clock-front GoodClock bundle + hReach/Regime split ·
§79 hdom · 6.11/6.14 bridges · hReach=Lemma4.7 · εbalance determinism. BUILT (Lean): 6.10 Azuma, 6.15 hdrift/htail,
6.16 ρ-chain, 6.17 minority, cancellation engine. PENDING design (in flight): assembly (Pre₃/Post₃/ε₃), 6.17
count-gap, Lemma 4.6 (cancellation time), Lemma 5.3 (entry/base). REMAINING IMPL (after design): the Core(h)
predicate defs + Prefix/Nat.rec induction scaffold + wiring built lemmas + the GoodClock quantile front (real leaf:
our front-shape is WIDTH not quantile) + hReach Janson instance + 6.11 cumulative-leak + 6.14 drain instance.

=== §80: SLOT-3 DESIGN COMPLETE — Lemma 5.3 base (family R4) + hdom leaf CLEARED ===
Lemma 5.3 (entry/base, verified vs Doty): |g|≥0.025|M| → stabilizes in Phase 2; |g|<0.025|M| → end of Phase 1
all bias∈{-1,0,+1}, biased count ≤0.03|M| (both 1-O(1/n²)). Phase-3 entry: every biased Main exponent 0 (mass 1)
→ μ_start ≤0.03|M|; unbiased Mains → hour 0. Precondition = phase-1 entry (no RoleMCR, g=Σ Main bias).
BASE = h=0 base of 6.16 (NOT ℓ-5): ρ_0=0.1, μ_start≤0.03|M|≤0.1|M|=ρ_0|M|2^0. ρ chain: 0.1 (h≤ℓ-5), then
0.104/0.13/0.212/0.408/0.808 (ℓ-4..ℓ). [CORRECTION to §76: 0.13 = ρ_{ℓ-3}, not a start value.] Small-gap branch
gives ℓ-5≥0. Saved: HANDOFF/family_slot3_lemma53_base.md.
hdom LEAF CLEARED (mine, verified 90b74141): Phase3DominantLevelConstruct.dominantLevel_exists — Nat.find ell with
0.4M≤g·2^ell<0.8M under small-gap entry. Discharges gapMassLower's carried hdom.

SLOT-3 DESIGN PHASE = DONE. Full Doty §6 phase-3 mapped: DAG(§75) + skeleton(§77) + clock-front(§78) + hdom(§79)
+ base(§80) + 6.11/6.14 bridges + hReach(4.7) + Lemma 4.6 cancel + εbalance + §4 Janson engine. NEXT = IMPLEMENTATION:
(1) Core(h) predicate defs + Prefix/Nat.rec scaffold; (2) per-hour step lemmas wiring built 6.10/6.15/6.16/6.17;
(3) GoodClock quantile front (real leaf — our front-shape is width); (4) hReach/6.11/6.14 Janson instances;
(5) hdom→gapMassLower wiring; (6) Core-all → slot-3 PhaseConvergenceW. Codex on slot-0; slot-3 impl when it frees.

=== §81: SLOT-3 ASSEMBLY Pre₃/Post₃ (family2 R2) + TWO newly-surfaced sub-leaves ===
Post₃ = branch disjunction:
 · Post3_maj (Thm 6.2, 0<|g|<0.025|M|): |M_*|≥0.92|M| (Main opinion i, exponent ∈{-ℓ,-(ℓ+1),-(ℓ+2)}) ∧
   μ_{>-ℓ}≤0.002|M|2^{-ℓ} ∧ β⁻≤0.004|M|2^{-ℓ}. NEEDS Lemma 6.18 cleanup (minority-mass → 92% COUNT).
 · Post3_tie (Thm 6.1, g=0): all biased agents have exponent −L.
Pre₃ = small-gap entry: all phase-3 well-formed, role-count good (5.2 → |M|,|C|,|R| const fractions), |g|<0.025|M|,
 biases∈{-1,0,+1}, biased count ≤0.03|M|, bias-sum=g (all from Lemma 5.3 + phase-2→3 init).
core_all + minority_all → the per-hour union tail → Post3_maj (the deterministic exit profile holds when all
 Core(h)+H17(h) hold). Saved: HANDOFF/family_slot3_assembly_pre_post.md.
NEW SUB-LEAVES (completeness-critic surfaced — were NOT in the prior design):
 (A) Lemma 6.18 — converts the 6.17 minority-mass bound into the |M_*|≥0.92|M| three-level COUNT statement.
 (B) TIE branch (Theorem 6.1, g=0) — separate from the majority hour-induction; all biased → exponent −L.
 Slot 3 needs BOTH branches (Post₃ is the disjunction) unless the pipeline routes ties elsewhere.

=== §82: COMPLETENESS-CRITIC (family4 R3) — slot-3 design was NOT complete; ~9 missing pieces ===
[CORRECTION to §80: "design complete" was PREMATURE. The completeness-critic surfaced these.]
MISSING NAMED NODES:
 1. Theorem 6.12 PACKAGING record (Theorem612Core): owns strong-induction bookkeeping + ρ/τ tables + h=0 base +
    tie convention l:=L+5. Not a comment.
 2. Lemma 6.18 (Lemma618MajorityBand) — BIGGEST miss: (a) whp at end_{l+2} majority count in {−l,−l−1,−l−2} ≥
    0.96|M|; (b) DETERMINISTIC reachable preservation ≥0.92|M| while in phase 3. Uses 6.11+6.17+two 4.7 pulls +
    a reachability invariant. PAPER ARITHMETIC INCONSISTENCY: prose "0.0036|M|" vs line "b₂=0.0056m" — pick a
    consistent strengthened target.
 3. Theorem 6.2 (Theorem62Phase3NonTiePost) — the actual non-tie EXIT consumed by phases 5-8 (not 6.16/6.17).
 4. Theorem 6.1 (Theorem61TiePhase3Post) — tie branch, +16 ln n split tail + c₃=26 no-early-exit. Separate from
    the non-tie l-induction (run Theorem612 through h=L with tie convention, then the extra split).
SILENT DETERMINISTIC INVARIANTS (the probabilistic lemmas assume these):
 5. SIGNED GAP CONSERVATION g = β⁺−β⁻ through cancel/split transitions (deterministic, not probabilistic).
 6. MASS MONOTONICITY: mass_preserved_by_split, mass_decreases_by_cancel, mu_nonincreasing, mu_tail_nonincreasing,
    mass_bound_to_count_bound (μ≤ρ|M|2^{-h+1} ⟹ count(exp≥−h)≤2ρ|M| — used in 6.13 process-of-elimination).
 7. ★CRITICAL VACUITY RISK★: HourWindow (HourCoupling.lean:493) = ∀a∈c, (main∨clock) ∧ phase=3 ∧ (main→unbiased).
    FORCES every agent Main-or-Clock. But real phase-3 has reserveCount ≥ n/5 Reserve agents (HonestWindows). So
    HourWindow is UNSATISFIABLE on real reachable phase-3 configs → the 6.10/HourCoupling chain CANNOT be
    instantiated to discharge slot-3 unless HourWindow is WEAKENED to allow inert Reserve (proven no-op on cAbove/
    mAbove/mass/hour-coupling). §3.3 hidden-vacuity-at-instantiation; #print axioms can't catch. VERIFY the
    instantiation path (is it a projected Main+Clock sub-config?) before concluding; if not projected, weaken
    HourWindow. HIGHEST-VALUE critic find.
 8+. role-count/role-preservation invariants + (family4 R4 in flight to finish).
Saved: HANDOFF/family_slot3_completeness_critic.md. SLOT-3 DESIGN is ~85%, NOT complete — these 7+ pieces remain.

=== §83: SLOT-3 DETERMINISTIC FOUNDATION (family4 critic2, vs Doty Algorithm 3) — design now TRULY complete ===
The deterministic algebra layer the probabilistic 6.10-6.18 chain sits on (many "easily-forgotten"):
ROLE INVARIANTS (8): 8.1 role preservation in Phase 3 (no role changes — phase-3 rules only touch minute/counter/
 hour/opinion/exponent); 8.2 role-count preservation (main/clock/reserveCount constant under phase-3 support);
 8.3 fixed-denominator M,C>0 for 6.10 (entry counts); 8.4 thread role-split bounds c<1/3<m (Lemma 5.2);
 8.5 ★Reserve INERTNESS★ — Reserve no-op on mAbove/cAbove/β±/μ/φ + null partner (THE HourWindow weakening fix).
TRANSITION ALGEBRA (9, deterministic):
 9.1 CANCEL (opposite opinions, equal exp −h → both unbiased O, hour←h): cancel_preserves_signed_gap,
     cancel_decreases_unsigned_mass, cancel β± equally, cancel removes 2·2^{-h}, cancel_produces_O_at_hour_h.
 9.2 SPLIT (unbiased Main hour>|exp| meets biased i → copy opinion, both exp→exp−1; one 2^e → two 2^{e-1}):
     split_preserves_signed_gap, split_preserves_unsigned_mass μ, split_halves, split_requires exp>−hour,
     split_decreases φ(>−h) strictly. [many already in tree: phase3CancelSplit_*]
 9.3 HOUR DRAG (unbiased Main hour←max(hour, ⌊clock.minute/k⌋)): hour_drag_only_unbiased_Main,
     hour_drag_preserves μ/β±/g, hour_drag only-increases-hour, no bias/opinion/exponent change.
SLOT-3 DESIGN = NOW COMPLETE (2 critic rounds). Full = probabilistic chain (§75/§77) + clock-front (§78) +
deterministic foundation (§83) + exit Thm6.1/6.2/Lemma6.18 (§81/§82) + base Lemma5.3 (§80) + hdom (§79 ✅ mine).
Saved: HANDOFF/family_slot3_critic_finish.md.

=== §84: HourWindow/Reserve VACUITY FIX (family R5, vs Doty Algorithm 3) — resolves the critical §82.7 risk ===
WEAKEN HourWindow → HourWindow' (HourCoupling.lean:493):
  def HourWindow' c := ∀ a ∈ c, a.phase.val = 3 ∧ (a.role=.main ∨ .clock ∨ .reserve) ∧ (a.role=.main → a.bias=.zero)
  (Or minimal: drop the role disjunct IF a NoStaleRoles invariant excludes RoleMCR/RoleCR. Prefer explicit form —
   admits Reserve, excludes stale RoleMCR/RoleCR which aren't real post-phase-1.) KEEP phase=3 for ALL agents incl.
   Reserve — else the phase-sync wrapper fires when Reserve meets a different-phase agent (Reserve no longer inert).
RESERVE-NOOP LEMMAS (Phase 3 has ONLY Clock-Clock / unbiased-Main-Clock / Main-Main branches — NO Reserve branch):
  phase3_reserve_pair_noop : u,v phase 3 ∧ (u.role=.reserve ∨ v.role=.reserve) → phase3Step u v = (u,v).
  Derived preservations: reserve_pair_noop_{clockCount,mainCount,reserveCount, cAbove,mAbove, clock_minutes,
  main_hours, mu, betaPlus, betaMinus}.
DRIFT SURVIVES: Φ=mAbove/|M|−1.1cAbove/|C| (|M|,|C| exclude Reserve). Reserve-involving interaction pairs are NULL
steps (Φ unchanged) → they only make E[ΔΦ] more negative or equal, never positive → supermartingale preserved (just
a rate rescale by the non-Reserve-pair fraction). So HourWindow' is SATISFIABLE on real phase-3 AND the 6.10 chain
goes through. THE VACUITY IS RESOLVED (design). Impl = swap HourWindow→HourWindow' in the 6.10 chain + the noops.
Saved: HANDOFF/family_slot3_hourwindow_fix.md.

=== SLOT-3 DESIGN + CRITICAL-FIX = COMPLETE. Implementation is the next campaign (codex, after slot-0). ===

=== §84-addendum: reserve-noop REFINEMENT (verified vs Transition.lean:577) ===
phase3CancelSplit branches on BIAS not role (Transition.lean:579). A Reserve agent has bias=.zero, so:
 · CANCEL branch (pos/neg dyadic): does NOT fire (Reserve is .zero, not dyadic). ✓ inert.
 · SPLIT branch (.zero, .dyadic): FIRES iff the zero-agent's hour.val > the biased exponent i.val. So a Reserve
   (.zero) paired with a biased Main WOULD split IF Reserve.hour > exp — NOT automatically inert!
RESOLUTION: reserve-noop holds CONDITIONAL on Reserve.hour ≤ exp (e.g. Reserve.hour = 0 — Reserve agents don't run
the hour mechanism, so should have hour 0). So HourWindow' must ALSO pin Reserve agents' hour low (or carry
"all Reserve have hour 0"), OR the full-Transition δ dispatch must role-gate Main-Reserve away from phase3CancelSplit.
ACTION for impl: verify the δ dispatch (does it apply phase3CancelSplit to Main-Reserve pairs, or role-gate?) AND/OR
add "Reserve ⟹ hour=0" to HourWindow'. This is a real refinement — family's clean "Reserve no phase-3 branch"
(pseudocode-true) needs the hour condition at our bias-branching implementation. [verify-don't-transcribe catch]
NOTE: family3 countgap (6.17 successor count-gap) failed twice on the bridge — low priority (6.17 minority is BUILT;
count-gap is a successor residual), skipped, not retried a 3rd time.

=== §85: SLOT-0 Stage-1.5 OBSTRUCTION — the last-MCR phase-10 drag (Codex, counterexample-verified) ===
Stage 1.5 (last RoleMCR → roleMCRCount=0) is NOT a simple InvClosed-shell milestone. Codex VERIFIED (axiom-clean
counterexample) that "∀ mcr, phase=0" (mcrPhase0FreeTargetShell) is FALSE under the kernel:
 · c = {phase0 MCR, phase1 Clock(unassigned)}: card=2, all MCR phase 0, freeTargetCount=1.
 · phaseEpidemicUpdate (Transition.lean:1762) syncs the low-phase agent UP + runs runInitsBetween (1488) → phaseInit;
   phase-1 init: role=.mcr → enterPhase10 (phase:=10, role PRESERVED) (Transition.lean:132/31/52).
 · So the phase-0 MCR is dragged to phase 10 (error), still role=.mcr → roleMCRCount stays 1. "all MCR phase 0" broken.
 Also: allPhase0 itself isn't globally InvClosed (Phase-0 clock counter→0 advances phase, Transition:294); only
 preserved under noClockAtZero guard (Phase0Window:1638).
INTERPRETATION: a leftover MCR either CONVERTS (Rule 2, good) or gets phase-epidemic-dragged to phase 10 (the
ERROR/backup branch — Doty's "RoleMCR is an error case"). roleMCRCount=0 (Stage-2 needs it) requires all MCR drain
DURING phase 0, BEFORE clock advancement — a phase-0-internal TIMING race, gated by allPhase0/noClockAtZero, NOT a
global InvClosed. The phase-10 drag is the rare failure → slot-10 backup. Right Stage-1.5 framing = phase-0-window-
gated whp last-MCR conversion (family R6 in flight). [§3.3 satisfiability caught the false invariant — codex rigorous]
SLOT 0 honest: Stage-2 DONE+verified; Stage-1.5 hit this REAL obstruction (not a mirror); needs the phase-0-timing
framing. Slot 0 NOT closed yet.

=== §86: 6.17 count-gap CORRECTED — mainLevelCount≤majorityLevelCount is OVER-STRONG (family3, verified) ===
[ANOTHER over-strong-object catch, like pointwise-mAbove §73 + HourWindow vacuity §82.7.]
The carried mainLevelCount(ℓ)≤majorityLevelCount(ℓ) is over-strong/FALSE: mainLevelCount=|A_ℓ|+|B_ℓ| (both
opinions) ≤ |A_ℓ| iff |B_ℓ|=0. Doty uses NO pointwise domination invariant. CORRECT object = the Lemma-4.6
cancellation-RATE condition 0<d<b<a at the active level, derived from the gap invariant β⁺−β⁻=g + the 6.11
below-tail (0.0012) + 6.15 above-tail (0.002). Recurrence closes at MASS level: β⁻_after ≤ (2ξ_{h-1}−d/m)|M|2^{-h};
final h=ℓ (a=0.412m, b=0.0088m, d=0.008m, E[t]<2.95/m, 6/m window) → β⁻_end_ℓ ≤ 0.004|M|2^{-ℓ} = ξ_ℓ. CAVEAT:
printed ξ's mix rounded/working values; if carrying 0.0056 use d=0.0072m for slack. REPLACE the count-gap residual
with the (a,b,d) cancellation-rate lemma; do NOT require the pointwise count domination. Saved:
HANDOFF/family_slot3_617_countgap.md. [verify: |A|+|B|≤|A| ⟺ |B|=0 — the over-strong catch is algebra-confirmed]

=== §87: SLOT-0 E_noadvance VACUITY — global clock-survival interface carries FALSE hcard/hcap (codex, counterexample) ===
Codex caught a vacuity in its OWN E_noadvance round (§85/E_noadvance): stage15W_of_noAdvanceResidual is axiom-clean
but VACUOUS — the global clock-survival interface (ClockCounterSurvival) carries universally-FALSE inputs:
 · hcard: ∀ c, 2≤c.card → c.card=n — FALSE (stage15_clock_survival_hcard_not_universal, 3-copy config).
 · hcap: ∀ j∈Clocks, ∀ c, c.count(species j) ≤ m — FALSE (stage15_clock_survival_hcap_not_universal, m+1 copies).
 #print axioms clean but the carried hyps are unsatisfiable → wiring closure onto it = fake inputs. Codex REFUSED.
 [§3.3 trap: clean axioms ≠ satisfiable hyps. Codex's counterexample guards are the catch.]
FIX (machinery EXISTS): switch to the REACHABLE/support-local interface ReachableClockTail.lean:
 reachable_cap_is_honest (378) — the cap holds on REACHABLE configs (resolves the false global hcap);
 mgf_depletion_tail_reachable (274), clock_perτ_uniform_reachable (349), reachable_decrement_bound (251).
 On reachable configs from Phase0Initial, hcard/hcap are HONEST. Stage-1/1.5 post supply clock-lower-band/no-zero.
SLOT-0 honest: deep multi-round grind. Stage-2 ✅; Stage-1.5 has gone mirror→false-mcrPhase0→timed→E_noadvance
(vacuous global iface)→ now reachable-iface redo. Each round honestly ruled out a wrong route + caught a vacuity/
false-invariant (the §3.3 discipline working). Not closed; closure = reachable clock-survival + warmup + the genuine
Doty role-count hyps.

=== §88: SLOT-0 reachable closure — 2 producers remain (codex; corrects my reachable_cap_is_honest error) ===
Codex landed the reachable-interface theorems (stage15Gate_hcard_reach, stage15Gate_hcap_reach_card,
stage15NoAdvanceResidual_of_stage15Gate_card_cap_reachable — verified 4388 jobs, axiom-clean). My §87 brief
ERRED: reachable_cap_is_honest (ReachableClockTail:378) does NOT supply a reachable cap — it PROVES the global cap
is FALSE (a marker). Codex caught it (verify-don't-transcribe). The genuine remaining producers to BUILD:
 1. REACHABLE COVER: {c | Reachable c₀ c ∧ ¬WinN 0 n c} ⊆ ⋃ j∈Clocks {c | DepletedCount (species j) N0 R c}
    (the WinN-breach deterministic reduction, but on REACHABLE configs — mirror ClockCounterSurvival Part 1).
 2. SHARP REACHABLE CAP: ∀ j∈Clocks, ∀ c, Reachable c₀ c → c.count(species j) ≤ m (TRUE on reachable: the
    per-clock marker species counts are bounded by the conserved population; build the reachability invariant).
Then wire both into stage15NoAdvanceResidual (the interface is now SATISFIABLE) → close slot 0. SLOT-0 Stage-1.5 =
7 rounds, each converging; the reachable route is right, needs these 2 reachable-fact producers.

=== §89: SLOT-0 cover SHAPE obstruction — per-species cover is FALSE shape; real cover is aggregate (codex) ===
Codex landed the sharp reachable cap (stage15Gate_hcap_reach_card_family: count(species j)≤n via card conservation,
verified) + reachable_hcover_of_global_hcover. But the COVER producer can't be honestly built for the per-species
interface:
 · survival_union_bound (ClockCounterSurvival:168) takes hcover as a HYP; Part 1 only gives one-step breach, NOT
   {¬WinN}⊆⋃DepletedCount.
 · Phase6ClockTailSupport:7 EXPLICITLY marks the global per-species cover {¬WinN}⊆⋃Depleted as FALSE SHAPE,
   replaced by support-local/horizon comparison. [So the per-species E_noadvance route is on a false-shaped cover.]
 · DepletedCount (Phase6ClockTailDepletion:59) = static species count drop (count≤N0−R), NOT the WinN breach's
   counter-zero/phase-window decomposition → RHS shape mismatch.
 · ClockCounterDepthCover:209 has the REAL deterministic cover, but RHS = aggregate DepthDepleted, NOT per-species.
FIX: re-route Stage-1.5 E_noadvance to the PHASE-6-STYLE aggregate/support-local clock-tail (Phase6ClockTailSupport
/ ClockCounterDepthCover — phase 6 ALREADY solved this exact false-cover problem), not the per-species
survival_union_bound. SLOT-0 Stage-1.5 round 9: cap ✅ (sharp reachable); cover needs the aggregate re-route.

=== §90: ★ROOT CAUSE FOUND (火眼金睛 Q2/Q4/Q5 + tree evidence) — stopping-time RACE mis-encoded as STATIC INVARIANT★ ===
Xiang's instinct (9 rounds w/o closing ⟹ real error) was RIGHT. The error is in OUR FORMALIZATION, NOT the paper.
CONVERGED DIAGNOSIS (4 channels + tree):
 · Q2 (paper audit): NO paper gap. Clock decrements ONLY in Clock-Clock (≤2/n per step) → E[dec]≤26 ln n over 13n ln n
   steps vs 50 ln n counter → Chernoff n^{-144/19}, union n^{-125/19}. Margin genuine. roleMCRCount=0 is a whp EVENT,
   not an invariant. Cascade can't advance the FIRST clock early (no higher-phase agent yet) — it's the failure branch.
 · Q4 (over-strong): roleMCRCount=0 is over-strong AS A POINTWISE INVARIANT, correct AS Good₀ (whp event). NOT
   droppable (leftover RoleMCR = ERROR, the mechanism proving g=Σ Main.bias). Post₀ = Good₀ ∨ Backup₀(→Phase10).
 · Q5 (ROOT CAUSE): (b) broadened — a FIRST-PASSAGE/STOPPING-TIME event encoded as a STATIC INVARIANT/COVER. The real
   good event is a RACE τ₀=T_roleMCR_zero < σ₀=T_clock_advance. The 3 false objects (∀c mcrPhase0, ∀c hcard/hcap,
   per-species cover) are EXACTLY what you get proving a race with static universal facts.
 · TREE EVIDENCE (mine): phase-3 consumers destructure RoleSplitGood with roleMCRCount=0 as `_` (UNUSED); it appears
   in ZERO Phase3*/HourCoupling*/CancelClock* files. Only used for the clean conservation identity.
THE FIX (Q5, confirmed): replace the WinN/cover/survival_union_bound interface with a KILLED/STOPPED KERNEL:
  cemetery Bad0 := {clock advanced to phase 1 before roleMCRCount=0} ∪ {seen10}.
  Prove ONLY the scalar stopped statement: Pr[τ₀ ≤ 12.5 ln n ∧ τ₀ < σ₀] ≥ 1 − O(1/n²).
  GoodPhase0(c_T) := roleMCRCount=0 ∧ role-count-good(RoleCR→Reserve normalized) ∧ ¬(clock advanced before MCR=0) ∧ ¬seen10.
  Complement = fast-path FAILURE (NOT repaired in phase 0 — Phase1/Phase10 backup handles total correctness).
  τ₀ tail = Stage-1's mcrCount Janson (have it); σ₀ race = the per-clock decrement Chernoff (Q2; ≤2/n Clock-Clock rate,
  26 ln n vs 50 ln n counter). Machinery: killed_geometric_tail / killK EXISTS (used in Stage-2). NO ∀c, NO cover.
This dissolves the 9-round false-object cascade. Saved: HANDOFF/Q2/Q4/Q5_*.md.

=== §91: §90 VALIDATED — killed-kernel is the RIGHT abstraction; GoodPhase0 = multi-producer assembly (codex r10) ===
Codex r10 confirmed "killed-kernel 本身不是缺口" — the race abstraction (§90) is RIGHT, the 9-round cover cascade
correctly abandoned. It refused a residual wrapper, decomposed GoodPhase0 into genuine sub-producers:
 (1) MCR stopped-race: Φ=mcrCount alone insufficient — last MCR (M=1) has diagonal rate 0, needs the FLOOR
     (a₀≤assignableCount). Floor chain = warmup(fresh→floorGate; assignableCount=0 at fresh start) → floor-tail.
     Floor-tail NOT yet unconditional (Lemma51Discharge.floor_escape_prefix_le carries hqbound/q; only q=1 proven).
 (2) role-count-good = a SEPARATE whp event (RoleSplitWindows via the top-split imbalance martingale; roleSplit
     Windows_whp needs hjump/hdrift/hrest, RoleSplitWindowMartingaleAtom). This is the OTHER HALF of slot 0 — the
     part already mostly built (cosh route, εbalance, stage2CRDrainW). NOT a consequence of the MCR race.
 (3) clock no-advance ≈ DONE: TransitionClockPairBound:104 unconditional entry.
 (4) seen10 / GoodPhase0 need a Config×Bool marked-state API at the slot-0 layer (marked-kernel tech is in
     EarlyDripMarked, not the phase-0 race API). ¬seen10 has no state space yet.
SO: slot 0 = GoodPhase0 = [MCR-race (killed kernel + floor + seen10)] ∧ [role-count-windows (top-split martingale,
mostly built)] ∧ [¬seen10]. A genuine multi-producer assembly. §90 fixed the abstraction (the 9-round blocker);
the producers (floor-tail unconditional, role-count windows discharge, seen10 bridge) are the honest remaining work.
Clock no-advance ≈ done. NOT one missing piece; will take several producer rounds.

=== §92: Q4 FULL (Xiang-pasted) — the sharp Post^fast₀/Post^safe₀ split confirms §90/§91 ===
Q4's complete conclusion (my capture truncated): the 9-round failure = proving "last RoleMCR drains before phase
advance" as a HARD/POINTWISE obligation, when Doty proves it only WHP (fast path) + routes failure to Phase 10.
FORMALIZATION (sharpest): Post^fast₀ := roleMCR=0 ∧ |M|∈(1±ε)n/2 ∧ |C|,|R|≥(1−ε)n/4 ∧ Σ Main.bias=g  [whp 1-O(1/n²)];
Post^safe₀ := Post^fast₀ ∨ ◇Phase10Backup. Phase 1/2/3 consume ONLY Post^fast₀ (whp event); the GLOBAL Thm 3.1
consumes Post^safe₀ (backup branch = Phase 10, Lemma 7.7, O(1/n²) trigger → negligible to expected O(log n)).
ALIGNMENT: codex's killed-race phase0_mcr_race_whp IS Post^fast₀'s roleMCR=0-whp part (not pointwise) — we pivoted
onto Doty's actual structure. The floor-tail (round 12) is the producer for this whp bound. role-count-windows
(RoleSplitWindows) is the rest of Post^fast₀ (mostly built). Backup₀/Phase10 = slot-10 (already ✅). Saved:
HANDOFF/Q4_overstrong_post_FULL.md.

=== §93: Q7 — role-count-windows half audit: SOUND, but shares the stopped-race boundary ===
Q7 verdict: the role-count-windows (|M|/|C|/|R| ∈ window via the top-split imbalance martingale) do NOT hide the
per-species-cover error — genuine count-collapse/balance theorem. BUT they SHARE the stopped-race boundary (real
kernel can leave phase 0 before the role-count process completes). So prove them on the Phase-0-stopped/KILLED
kernel, not the unrestricted real kernel.
CRISP FULL Post^fast₀ INTERFACE (Q7): NoClockAdvanceBefore(T) ∧ RoleSplitGood(ε,n,c_T) ∧ MainBiasSum(c_T)=g.
 · RoleSplitGood (RoleMCR=0 ∧ count-windows, BOTH) → prove in the KILLED kernel (cemetery = clock advanced).
 · NoClockAdvanceBefore(T) → SEPARATE first-passage tail. ClockBad(c):=∃ clock, counter=0 ∧ phase=0. Routes:
   (a) per-clock first-passage (count clock-clock interactions/clock, union over n); (b) aggregate Φ=Σ e^{-s·counter}
   with immigration (clock-at-0 ⟹ Φ≥1, stopped MGF drift). NOT the per-species cover (clock agents FLOW through
   depth species — a flow variable, not a depleted resource → per-species cover false; aggregate true).
 · MainBiasSum=g → the conservation (deterministic).
 Compose by union bound. EXTENDS codex's killed-race to cover the role-windows too (same kernel). Saved:
 HANDOFF/Q7_rolewindows_audit.md.

=== §94: ★FLOOR FALSE OBJECT★ (Q6 proactive audit — caught BEFORE grinding) — wrong floor; use Doty MONOTONE s_f+m_f ===
Q6 caught the floor-tail as a FALSE OBJECT: we chase assignableCount (DROPS under Rule 4 cr,cr→clock,reserve,
assignableCount_pair_rule4_drop), but Doty's floor A := s_f+m_f = #{unassigned non-RoleMCR, INCLUDING concrete
Clock/Reserve/RoleCR} is MONOTONE NONDECREASING ("once s_f+m_f>n/5, never decreases"). assignableCount EXCLUDES the
new Clock/Reserve → appears to drop → false object. FIX:
 · A(c) := #{x : x.assigned=false ∧ x.role ≠ RoleMCR}. Prove A(c')≥A(c) DETERMINISTICALLY every reachable all-phase-0
   step before σ₀ (monotone invariant, NOT a stochastic survival tail).
 · One-time FLOOR-BIRTH near u=2n/3: A>n/5 whp (early prefix).
 · Stopped drain: P[ΔU<0|U=u,A≥a₀] ≥ 2u·a₀/n²; last MCR (u=1) removed by PERMANENT s_f+m_f at 2/(5n) (NOT diagonal
   U,U which is 0 at u=1; Doty p*=2/(5n) "when u=1" is the smoking gun).
NO stochastic floor-survival tail. Explains why floor-tail kept being "not unconditional" — wrong (non-monotone)
floor. Q6 PROACTIVE audit caught it before round 13+. THE LESSON WORKING. Saved: HANDOFF/Q6_floortail_falseobject.md.
ACTION: re-dispatch codex round 12/13 to use monotone A (deterministic invariant), NOT assignableCount survival tail.

=== §95: SLOT-3 BUILD ORDER + PRE-FLAGGED RACE PIECES (Q9 — framing lesson applied FORWARD) ===
BUILD ORDER (lowest framing-risk first): (1) deterministic transition algebra [g-conservation, mass-monotone,
cancel/split/hour-drag exact effects, reserve-noop — per-transition facts, hard to frame wrong] → (2) HourWindow'
+ reserve-noop [domain hygiene] → (3) Pre₃/base (Lemma 5.3 package) → (4) GoodClock/hdom INTERFACES (the bundle
fields: start_h+2/c≤end_h, +41/m, +47/m, end_{h-1}<start_h — k=45 fits) → (5) Core(h)=H13∧H14∧H15∧H16 thin
Nat.rec/Prefix scaffold → (6) bridges 6.11(stopped leakage)/6.13(O-floor)/6.14(far-above cutoff) → (7) plug built
6.15/6.16/6.17 (interface alignment) → (8) 6.18/Post₃ (probabilistic snapshot + DETERMINISTIC reachability closure).
★RACE-SHAPED PIECES (killed-kernel/STOPPED from the start, NOT static invariants — apply §90/§94 lesson upfront):
 · "no Main above the front" (hour-induction) = Doty 6.10 stopped race (clock-drag vs hour-end).
 · Clock-front Regime (start_h/end_h/lengths) = HITTING-TIME facts → GoodClock stopped events.
 · 6.10/6.11 leakage (mAbove, O.hour>h UNTIL end_h) = stopped bounds, NOT ∀-reachable invariants.
 · 6.13 O-front catch-up = race, killed at min(end_h, badLeak, badMass).
 · 6.14 far-above cutoff = hitting-before-deadline (vacuous h<q → NOT a global max-exp invariant).
 · 6.15 = stopped Azuma (only while potential > threshold).
This de-risks slot-3: build order known + all races pre-flagged so we don't repeat slot-0's 9-round mistake.
Saved: HANDOFF/Q9_slot3_buildorder_raceflags.md.

## §96 (2026-06-18) — ε-interface false-object: r13 wrapper demanded POINTWISE clock tails; the c₀-anchored producer is ALREADY PROVEN

Codex r14, dispatched to discharge the r13 MCR-race wrapper's carried ε's, hit the §3.3 trigger (≥2
false-shaped objects) and correctly STOPPED (file kept axiom-clean, no faked close). Honest diagnosis,
VERIFIED by spot-check:

- r13 `phase0_mcr_race_whp_from_fresh_freeFloorBirth_drain` (Phase0StoppedRace:1618) carries POINTWISE
  hyps: `hS : ∀ y ∈ freeFloorGate, ∑τ (K^τ)y Sᶜ ≤ εS` and `hsideDrain : ∀ y ∈ freeFloorGate, (K^T)y
  phase0SideGateᶜ ≤ εsideDrain` — a uniform tail demanded of ARBITRARY post-warmup gate states. FALSE
  SHAPE (the §90 lesson recursing one level: the ε's were themselves encoded static/pointwise, not as
  first-passages from the fixed start).
- The REAL producer is c₀-anchored: `Slot0HtailAssembly.Phase0ClockZeroPrefixTail` (:75) =
  `∀ c₀, Phase0Initial c₀ → ∀ τ∈range t, (K^τ)c₀ {¬noClockAtZero} ≤ phase0ClockZeroBudget L`, and
  `TransitionClockPairBound.phase0ClockZeroPrefixTail_unconditional` PROVES it UNCONDITIONALLY from
  regime numerics (hn, ht ≤ n(L+1), hlog), consumed by `allPhase0_window_whp`. The file comment itself
  prescribes "a stopped or first-exit form; does not pretend allPhase0 is absorbing."

FIX (settled by the proven lemma + §90 + Doty's own comment — no ChatGPT needed): REFRAME the wrapper
to pay the clock-no-advance σ₀ tail from c₀ via `phase0ClockZeroPrefixTail_unconditional` +
`allPhase0_window_whp` (Markov/union decomposition at the fixed Phase0InitialFresh start), NOT pointwise
over freeFloorGate. This DISCHARGES the clock-leg of εphase/εsideDrain/εS unconditionally.

RESIDUE after reframe = ONE genuine producer: εwarm = `WarmupReachBennettAtom` (RoleSplitFloorDischarge:53,
consumer :114; FloorPrefix:684 keeps `hreach` named) — Doty's warmup/Bennett reach-mass concentration,
no constructor yet. That is the single honest remaining obligation of the MCR-race half (a real
probabilistic atom, not a false object).

NOTE on the f26859ac commit: the monotone-floor + killed-kernel + drain-rate STRUCTURE is sound and
verified axiom-clean; only the ε-INTERFACE shape (pointwise vs c₀-anchored) was wrong. The reframe keeps
all the structure, fixes the interface. Honest scoreboard: MCR-race half = structure proven + clock-leg
dischargeable from PROVEN lemma + εwarm the one remaining atom.

## §97 (2026-06-18, Q10 family OK) — GENERALIZE the slot-0 Janson engine → `catalyticPullTail`; reuse boundary for slot 3

Q10 (verify-don't-transcribe; Doty-cited, aligns with the existing slot-3 board) on whether the
just-verified `freeMCRKernelMilestone` Janson catalytic-drain (slot-0 MCR) instantiates the phase-3
Lemma 4.7 catalytic pull:

TRANSFERS (one-sided pulls) — but the reusable engine must take the floor as a STOPPED-WINDOW LOWER
BOUND, not a monotone counter. Generalize to:
  `catalyticPullTail` hyps:  (i) `∀ t < T_stop, |A_t| ≥ a₀`  (floor during window, NOT |A_{t+1}|≥|A_t|);
  (ii) `B_{t+1} ≤ B_t`;  (iii) `B_t = i > b₂ ⟹ Pr[B_{t+1} < B_t | F_t] ≥ 2·a₀·i/(n(n−1))`.
  Conclusion: geometric-sum tail, ~ (ln b₁ − ln b₂)/(2a₀) parallel time, 5 ln n/(2a₀) whp.
Instantiations (one engine, 3 sites):
  · slot-0 MCR : A=freeTargetCount, B=#RoleMCR, a₀=free floor (floor PROVEN by monotonicity — the
    slot-0 instance is the special case where |A_t|≥a₀ comes from monotone freeTargetCount).
  · phase-3 clock-pull (Doty 6.13 via 4.7, a=0.9c): A=#{Clock.hour ≥ h} (NOT =h — exact-hour is not
    permanent; ≥h is the monotone/safe catalyst), B=#{lagging O-agents not yet pulled to hour h}, a₀=0.9|C|.
  · phase-3 final majority cleanup (a=0.19m): A=#{majority Main at exponent −l or −(l+1)}, B=#{remaining
    O_{l+2}}, a₀=0.19|M_Main|. Here the floor is NOT locally monotone (split moves −(l+1)→−(l+2)); Doty
    proves |A_t|≥0.19|M| by a MASS/GAP REACHABILITY invariant over reachable configs, not local monotonicity.

DOES NOT TRANSFER (separate engines, already on the slot-3 board):
  · two-sided cancellation A_h+B_h→O+O = Doty Lemma 4.6, rate 2|A||B|/(n(n−1)), BOTH factors change —
    not a catalytic pull.
  · weighted-potential φ(>−h) decay = Doty 6.15, multiplicative drift → supermartingale/Azuma, NOT a
    geometric coupon tail. (Board: 6.10 leakage Azuma + 6.15 hdrift/htail + CancelClockConcentration BUILT.)

FALSE OBJECTS TO AVOID (the §90 mistake in a new costume): `ClockEq h` as catalyst; "good target count
stays high" as a static invariant; one-sided catalytic pull used for the ± cancellation.

ACTION (deferred until slot-0 closes; 难题单线 — no 2nd codex now): generalize freeMCRKernelMilestone to
`catalyticPullTail` with the floor-during-window hypothesis (slot-0 monotone instance falls out as the
special case), then slot-3 hReach (Lemma 4.7 pulls) instantiate it twice. Saved: this maximizes the
verified slot-0 investment across both deep slots.

## §98 (2026-06-18, Q11 family OK) — εwarm = KILLED warm-up reach (Doty Lemma 5.1 §5), hGate_abs is the §90 mistake a 3rd time

Q11 (verify-don't-transcribe; Doty-cited) on the last slot-0 producer, εwarm = WarmupReachBennettAtom.
VERDICT: relax `hGate_abs` — the absorbing gate containing the initial config is a FALSE OBJECT (same
category error as the static cover/floor). Warm-up reach is a FIRST-EXIT lower-tail concentration.

WHAT DOTY PROVES (Lemma 5.1 §5, first paragraph — not a separately named Bennett lemma): start all-U;
while u = #U ≥ 2n/3, each non-null top-level role-split interaction is the top U,U→S_f,M_f reaction w.p.
≥ 1/2; Chernoff ⟹ freeTargetCount = s_f+m_f ≥ (2/9)(1−ε)n > n/5 by the time u ↓ 2n/3. THEN s_f+m_f is
monotone (= the §94 floor the MCR drain consumes).

THE KILLED OBJECT: window G_warm = allPhase0 ∧ fresh ∧ U>u₀ ∧ A<a₀ ∧ side-conds (u₀=⌈2n/3⌉, a₀≈n/5,
A=freeTargetCount). Stopping times η=inf{A≥a₀}, ρ=inf{U≤u₀}, σ₀=first clock advance. Prove
Pr_{c₀}[ρ<η ∧ ρ<σ₀ ∧ no side-exit before ρ] ≤ e^{−Ω(n)} (or O(1/n²)). Exit via A≥a₀ = success; via
U≤2n/3 before A≥a₀ = rare lower-tail failure; via clock = paid by the already-proven c₀ clock prefix.

BENNETT POTENTIAL: Ψ_q(c)=exp(λ(qN(c)−T(c))), T=#top reactions=A/2, N=(n−U)−T=#non-null top-level
role-split reactions. For q<1/2 the ≥1/2 top-reaction domination gives multiplicative downward drift in
the killed window. Bad boundary deficit linear iff 2q/(1+q)>3/5; Doty's q=1/2−ε ⟹ A ≥ (2q/(1+q))(n−U)
> n/5 at U≈2n/3 — the formal version of "s_f+m_f ≥ (2/9)(1−ε)n > n/5".

GENUINELY ABSORBING (but it's the SUCCESS SET, not the drift gate): A=freeTargetCount monotone, stays once
≥a₀. It does NOT contain c₀ (A=0 there) so cannot be the drift gate. Correct split: reach the monotone
success set by KILLED concentration + use it as invariant afterward (the MCR drain already does the latter).

KILLED CONTRACT (replaces hGate_abs): G(c) ⟹ E[Ψ(X_{t+1})·1_G(X_{t+1})|X_t=c] ≤ r·Ψ(c), plus boundary
accounting Pr[bad U-exit before A≥a₀] ≤ e^{−Ω(n)} and Pr[clock exit] ≤ O(1/n²) from the proven c₀ tail.

ACTION: codex r16 building WarmupReachKilledBennettAtom (Phase0WarmupReachKilled.lean) per this design,
proving the ≥1/2 drift on the CONCRETE NonuniformMajority kernel (not Doty's abstraction), reusing the
killed-kernel WindowConcentration. Closes εwarm ⟹ slot-0 MCR-race half UNCONDITIONAL.

## §99 (2026-06-18) — εwarm needs a MILESTONE: fixed-T₀ consumption is false at small T₀ (the first-passage lesson, 4th instance)

Codex r16, building the §98 killed warm-up atom, hit a real interface flaw and honestly stopped (no fake
construction). VERIFIED: the r15 wrapper consumes warm-up at a FIXED universally-quantified T₀
(`(K^T₀) c₀ freeFloorGateᶜ`, Phase0StoppedRace:1527/2049). But the fresh start is all-`.mcr`
(RoleSplitConcentration:166) and `freeTargetPred = role≠.mcr ∧ ¬assigned` (RoleSplitFreeTargetFloor:35),
so `freeTargetCount c₀ = 0`; at T₀=0, a₀≥1 the fixed-time free-floor failure prob is 1, NOT O(1/n²).
The killed first-exit proves "BadExit (U≤u₀ ∧ A<a₀) before Good (A≥a₀) is rare" but NOT "at arbitrary fixed
T₀ we're in freeFloor" (could still be mid-warm-window U>u₀ ∧ A<a₀).

FIX (the first-passage lesson a 4th time — fixed-time entry where a milestone is needed): require T₀ ≥ Twarm,
Twarm a concrete deterministic horizon, and prove warm-up COMPLETES by Twarm whp =
  (a) killed first-exit (§98): Pr[BadExit before Good] ≤ e^{−Ω(n)};
  (b) hitting-time UPPER bound η ≤ Twarm whp: pick Twarm = Θ(n) interactions; while U≥2n/3 the per-step
      non-null top-reaction prob is ≥ const, so the U-drain to ≤2n/3 concentrates at Θ(n) (Chernoff), exiting G;
  (c) monotone after Good (freeTargetCount nondecreasing, already proven): once A≥a₀ at η≤Twarm, A_{T₀}≥a₀
      for all T₀≥Twarm ⟹ (K^T₀) c₀ {¬Phase0WarmGood} ≤ O(1/n²);
  (d) thread `hTwarm : Twarm ≤ T₀` into the wrapper's εwarm consumption ⟹ wrapper unconditional in εwarm.
Twarm = Θ(n) is well within the phase-0 O(n log n) T₀ the global assembly uses, so the milestone hyp is satisfiable.

codex r17 building this; Q12 de-risking the Twarm value + the U-drain-hitting / A-floor composition (does a
single fixed Θ(n) horizon work, or is it Θ(n log n) / need an intermediate-milestone union bound).
NOTE: the ae7a9fbf r15 commit stays valid (conditional theorem, verified); this refines the εwarm PRODUCER shape.

## §100 (2026-06-18, Q12 family OK) — εwarm milestone constants SETTLED: Twarm=n, p_dec≥2/5, union bound

Q12 (verify-don't-transcribe; Doty Lemma 5.1-cited) closes the εwarm design. The fixed warm-up horizon WORKS:
  Twarm = n interactions (Θ(1) parallel time) — NOT Θ(n log n). The n log n tail begins only AFTER the
  milestone (draining last U's at catalytic 2u/(5n), min Θ(1/n) at u=1; Doty's 12.5 ln n part).
HITTING: ρ = inf{U ≤ u₀=⌈2n/3⌉}. Before ρ, p_dec ≥ U(U−1)/(n(n−1)) ≥ 2/5 (n≥6; asymptotically Doty's (u/n)²≥4/9).
  ρ>n ⟹ <n/3 decrements in n trials each ≥2/5 ⟹ Pr[ρ>n] ≤ Pr[Bin(n,2/5)<n/3] ≤ e^{−n/180}. (q=1/2 rough bound ⟹ Twarm=2n.)
COMPOSITION (union bound, NO independence): {A_{Twarm}<a₀} ⊆ {ρ>Twarm} ∪ {ρ<η} ∪ {σ₀≤Twarm} ∪ {side exit}.
  freeTargetCount monotone ⟹ if U hit u₀ by Twarm and killed bad-exit ρ<η didn't occur, A≥a₀ already happened
  and persists to Twarm. Final atom: Pr_{c₀}[(K^Twarm)c₀{¬WarmGood}] ≤ e^{−n/180} + Pr[ρ<η] + Pr[σ₀≤Twarm] + Pr[side]
  = O(1/n²), with Pr[σ₀≤Twarm] paid by the proven c₀ clock prefix.
ADVERSARIAL POINT (validated): the fixed horizon is valid for REACHING the floor, not draining all MCR — no fat
  tail before U=2n/3 (U,U has constant prob ≥2/5); the fat tail is only after. So a single fixed Θ(n) horizon
  works; no hidden race at this milestone, no intermediate-milestone union needed.
DESIGN NOW COMPLETE (§98 killed first-exit + §99 milestone + §100 constants). codex r18 BUILDING the 4 concrete
pieces (1: U-decrement ≥2/5 on stepDistOrSelf; 2: Ψ_q killed drift; 3: BadExit threshold; 4: Bin Chernoff hitting)
+ union assembly. No further design question — pure construction.

## §101 (2026-06-18) — the last warm-up gap: TYPED first-exit transfer (untyped `none` cemetery overcounts success)

Codex r19, assembling the 4 warm-up pieces (d31e5366), built the CK-chain union machinery + resolved its own
r18 concern (roleMCRCount one-step non-increase, Phase0WarmupReachKilled:372) but stopped honestly at the LAST gap:
the union assembly needs a REAL fixed-time endpoint (K^Twarm)c₀ {freeTargetCount<aWarm} ≤ …, and the existing
killed machinery overcounts.

THE GAP: the killed kernel uses a SINGLE untyped cemetery `none` — killed on ANY window exit (GOOD=floor≥a₀
success, or BAD=U≤u₀ failure → same death token). So `real_le_killed_now` (GatedKillNow:135) /
`kill_now_escape_le_prefix_union` (:260) bound real-bad by killed {none ∪ alive-bad}, CHARGING the GOOD (success,
≈1) mass as failure budget — wrong magnitude, bound useless.

THE FIX (typed first-exit; A=freeTargetCount monotone nondecreasing is the key): at fixed T=Twarm,
  {A_T < a₀} ⊆ {τ_exit > T : still U>u₀} ∪ {BAD first-exit by T} ∪ {σ₀≤T} ∪ {side}.
GOOD-exit mass EXCLUDED by monotonicity (GOOD by τ≤T ⟹ A_T≥a₀ ⟹ ∉{A_T<a₀}). {τ>T} ≤ rho_not_hit_tail_janson
(postTail); {BAD first-exit} ≤ badExitPrefixBudget (:1767, already built); {σ₀≤T} ≤ proven c₀ clock prefix.

codex r20 building the typed transfer — route (a) direct first-exit stopping decomposition (preferred, reuses
CKChainBound/badExitPrefixBudget) OR (b) two-token typed-cemetery killed kernel (GoodDead uncharged / BadDead
charged). Q13 de-risking the cleanest measure-theory formulation + the identity Pr[hit BAD before GOOD within T]
= Σ_{t<T} Pr[alive in G through t, step into BAD at t+1]. Then assemble + wire → MCR-race half UNCONDITIONAL.
NOTE: this is the typed-boundary theme — the killed kernel needed TWO boundaries where it had one.

## §102 (2026-06-18, Q13 family OK) — rigorous typed first-exit spec; the persistence-lemma caveat

Q13 (verify-don't-transcribe) gives the rigorous spec for the §101 typed first-exit transfer codex r20 is building.
CONFIRMS route (a) direct first-exit (route (b) two-token GoodDead/BadDead kernel = equivalent packaging). The
target identity:
  Pr[τ≤T, X_τ∈BAD] = Σ_{t=0}^{T-1} Pr[X_0..X_t∈G, X_{t+1}∈BAD] = Σ_{t<T} ∫_G μ_t^G(dc) K(c,BAD),
  μ_t^G = δ_{c₀}K_G^t (substochastic killed-alive), K_G(c,D)=1_G(c)K(c,D∩G).
So BAD first-exit prob = EXACTLY the killed-alive-prefix last-step BAD budget (= codex's badExitPrefixBudget :1767),
IF indexed Σ_{t<T} Pr[alive through t ∧ X_{t+1}∈BAD].
Fixed-time transfer: K^T c₀ {A<a₀} ≤ Pr[U_T>u₀] + (BAD first-exit) + (side/clock prefix).

TWO PITFALLS (both already handled, but recorded):
 1. OFF-BY-ONE: "alive through t" = X_t∈G; BAD checked at t+1 NOT t ({alive through t ∧ X_t∈BAD} = ∅ since
    G∩BAD=∅). codex's "last-step BadExit budget" naming = correct indexing.
 2. ★PERSISTENCE (the adversarial caveat): A-monotonicity must hold AFTER Good is reached (Good is OUTSIDE G):
    A_t≥a₀ ∧ no-side-exit[t,T] ⟹ A_T≥a₀. If monotonicity were scoped only to the window, Good mass could NOT be
    dropped and the typed kernel proves only a HITTING statement, not K^T{A<a₀}. For freeTargetCount this is the
    intended global monotone floor — and the §94 monotone proof (Phase0StoppedRace:263) is a GLOBAL one-step
    ∀-pair non-decrease, so persistence holds unconditionally. (Watch: if r20 ever scopes monotonicity to in-window,
    that's the false object — it must be global/side-good.)
Needed hyps (clean): c₀∈G; Good/Bad/G pairwise disjoint; side-good A-monotone; U-monotone (for the hitting tail).
GOOD absorption excluded PATHWISE by A-monotonicity — no independence, no optional stopping, no cemetery overapprox.

## §103 (2026-06-18, recovered ChatGPT answer — Xiang-pasted) — SLOT-3 BUILD ORDER (Doty §6), authoritative

Detailed slot-3 (phase-3 cancellation/induction) build order. Ranks the 4 candidate first-pieces (b)→(c)→(a)→(d):

BUILD ORDER:
 1. ★Phase-3 TRANSITION ALGEBRA (b) FIRST — local, non-probabilistic, hardest to mis-frame; the "typeclass of
    truth". Lemmas: P3Step.kind classifier (ClockEpidemic|ClockDrip|HourDrag|Cancel|Split|PhaseCounter|Noop);
    p3_biasSum_step_eq (g=β₊−β₋ conserved), p3_totalMass_step_le (μ=β₊+β₋ nonincrease), p3_totalMass_cancel_eq,
    p3_totalMass_split_eq (split preserves μ, cancel decreases it), p3_massAbove_step_le, p3_phiAbove_split_delta,
    p3_hourDrag_bias_eq/_mass_eq, p3_reserve_noop_for_phase3_measures, p3_reachable_biasSum_eq/_totalMass_le.
    Unblocks 6.13/6.15/6.16/6.17/6.18.
 2. HourWindow′ WEAKENING + reserve-noop (c) — constrain ONLY Clock minute/hour front, Main O.hour, biased Main
    exponent; admit Reserve as INERT for phase-3 measures (Reserve used later for >−l splits, not phase-3 clock-hour).
 3. Pre₃ base package (Lemma 5.3 consequences): small gap, initial mass ≤ 0.03|M|, l−5≥0, role-counts, phase-3 init.
 4. GoodClock/hdom INTERFACES ONLY (not full Regime proof): start h, end h, hdom h + fields start+2/c≤end,
    start+2/c+41/m≤end, start+2/c+47/m≤end, end(h−1)<start h. Constants arranged so 2/c+47/m fits a sync hour at k=45.
 5. Core(h) strong-induction scaffold — THIN: Core h := H13 h ∧ H14 h ∧ H15 h ∧ H16 h, each Hᵢ a STOPPED/hour-local
    event NOT a global prefix invariant. Base from Lemma 5.3; h=0 bases of 6.13/6.15 trivial.
 6. Bridge 6.11 (stopped leakage "until end_h") / 6.13 (O-hour lower bound) / 6.14 (far-above cutoff).
 7. Plug built 6.15(hdrift/htail)/6.16/6.17 into Core — interface alignment.
 8. 6.18/Post₃: SPLIT into probabilistic snapshot + DETERMINISTIC reachability closure (Doty stops reasoning
    probabilistically after 6.17, uses reachability+invariants while still in Phase 3).

RACE-SHAPED (state as STOPPED events in GoodClock, NOT static invariants — the §90 lesson): GoodClock/Regime
(start_h/end_h/hdom = hitting times); 6.10/6.11 leakage (mAbove, O.hour>h "until end_h"); 6.13 O-front catch-up
(kill at min(end_h,badLeak,badMass)); 6.14 far-above cutoff (hitting-before-deadline, VACUOUS for h<q); 6.15
potential drop (stopped Azuma after start+2/c, while potential above threshold); 6.16/6.17 cancellation (race vs
6/m time in sync hour, "by start+2/c+47/m≤end_h" via Lemma 4.6); Phase-3 exit/counter (epidemic, not simultaneous).

VACUITY/OVER-STRONG TRAPS: (1) end_h direction — must be "first time beyond-h front reaches small threshold" so
"before end_h front tiny"; wrong inequality ⟹ Nat.find=0 ⟹ empty hour. (2) l−5≥0 carry 5≤l explicitly (no Nat-sub
floor). (3) tie case: l undefined → Doty sets l=L+5; keep tie/majority variants separate. (4) l+2≤L domain for 6.18
end_{l+2}. (5) strict split-guard off-by-one (split when O.hour STRICTLY > biased exponent magnitude → "reduce mass
above −h" not "at-or-above"). (6) DON'T upgrade 6.15 to zero-upper-tail (it's small mass above −h, not absence;
zero only in 6.14 for >−h+q). (7) O_h NOT monotone (clock-drag ↑, split consumes — 6.13 is process-of-elimination
+ stopped leakage + prev mass, not monotonicity). (8) 6.17 minority via sign(g)/explicit majority param, not WLOG A.
(9) 6.18 closure only for configs reachable while ALL still in Phase 3 (not global postcondition). (10) counts vs
fractions (m=|M|/n etc.): named coercion lemmas, else 6.10–6.17 constants brittle.

Grounded against Doty §6 (the connected repo couldn't resolve the commit, so framed against the slot-3 summary + §6).
DEFER until slot-0 closes (难题单线). The slot-0 catalyticPullTail (§97) instantiates 6.13's O-front pull (a₀=0.9c).

## §104 (2026-06-18) — ★SLOT-0 MCR-RACE HALF CLOSED: phase0_mcr_race_whp UNCONDITIONAL in εwarm (verified)★

codex r21 closed the last mile (committed e367c449); INDEPENDENTLY VERIFIED by me:
 - full ExactMajority closure builds (3824 jobs, EXIT=0);
 - #print axioms phase0_mcr_race_whp_from_fresh_freeFloorBirth_drain = [propext, Classical.choice, Quot.sound];
 - the public wrapper (Phase0StoppedRace:2726) carries NO WarmupReachBennettAtom / εwarm — only hTwarm:Twarm≤T₀
   + Phase0InitialFresh + satisfiable regime side-hyps, with a fully SCALAR bound:
     {roleMCRCount≠0 ∨ seen10} ≤ 4·roleSplitInvSqBudget n + freeMCRJansonBudget + clock-budget terms = O(1/n²).
Last-mile pieces (e367c449): badExitPrefixBound_Twarm_le_inv_sq_of_fresh (scalar 1/n²), clock-prefix-sum scalar
bound, warm-gate-entry total ≤ 4·roleSplitInvSqBudget n, predicate transfer via haWarm:a₀≤aWarm n (NO a₀/aWarm/uMin gap).

THE FULL CHAIN from the 13-round wall is now CLOSED + axiom-clean: §90 stopping-time race + §94 monotone floor
(f26859ac) → §96 c₀-anchored clock-leg (ae7a9fbf) → §98/§99/§100 killed first-exit warm-up + milestone + constants
(2ccadae8/7fd8706a/a8c7ef0e) → §101/§102 typed first-exit transfer (75734547) → scalar bounds + discharge (e367c449).

REMAINING for slot 0 (Lemma 5.2 full): (1) the role-count-windows half (RoleSplitWindows — Main.bias sum = g +
count windows, shares the killed-kernel boundary §93); (2) assembly into Post^fast₀ = NoClockAdvance ∧
killed-kernel(RoleSplitGood) ∧ MainBiasSum=g (union bound §93); (3) Post^safe₀ = Post^fast₀ ∨ ◇Phase10Backup.
PENDING escape audit: the carried side-hyps (hTwarm, haWarm:a₀≤aWarm, htotal, hlog, regime) are satisfiable-by-design
(global assembly supplies them) but the formal satisfiability/escape audit (task #3) is still due.

## §105 (2026-06-18, Q14 recovered — Xiang-pasted) — SLOT-3 deterministic transition algebra: ★β/μ are WEIGHTED, not counts★

The slot-3 piece-(b) exact per-step deltas (Doty §6, verify-don't-transcribe). Notation: level j = biased Main at
exponent −j; w j = 2^{−j}; bias = opinion·2^exponent. ★KEY CORRECTION (resolves the §103 count-vs-weight trap):
β₊=Σ_{op=+1}|bias|, β₋=Σ_{op=−1}|bias|, μ=β₊+β₋ are WEIGHTED dyadic mass, NOT biased-agent counts. g=β₊−β₋ invariant.
Split guard STRICT: level j splits only if O.hour > j (≥ j+1).

(1) g=β₊−β₋ PRESERVED by EVERY phase-3 transition:
  Cancel level j: (+,−j),(−,−j)→O,O: Δβ₊=−w j, Δβ₋=−w j, Δg=0.
  Split sign s level j: (s,−j),O→(s,−(j+1)),(s,−(j+1)): Δβ_s=2w(j+1)−w(j)=0, Δg=0.
  Clock/hour/phase/reserve/noop: all Δ=0.
(2) μ=β₊+β₋ WEIGHTED, NONINCREASING; ONLY cancel decreases:
  Cancel level j: Δμ=−2w j=−2^{1−j}.  Split: Δμ=2w(j+1)−w(j)=0 (preserves).  Others: 0.
  ⟹ `totalMass_noninc` MUST use weighted μ, NOT count. (Biased COUNT B: cancel ΔB=−2, split ΔB=+1 — so count is
     the WRONG object; μ is right.)
(3) Tail above −h — TWO DIFFERENT objects:
  countAbove_h = #{level j<h} — NOT monotone (interior split j+1<h gives Δ=+1; cancel j<h Δ=−2; split j+1=h Δ=−1).
  μAbove_h = μ(>−h) = Σ_{exp>−h}|bias| — NONINCREASING: cancel j<h Δ=−2w j; split j+1<h Δ=0, j+1=h Δ=−w j=−2^{−(h−1)},
    j≥h Δ=0. ★Boundary split j=h−1 is the off-by-one: moves mass −(h−1)→−h, and −h is NOT strictly above −h. So use
    μAbove (weighted), never countAbove, for the monotone-decrease lemmas.
(4) Doty's φ(>−h) potential (Lemma 6.15): level j<h has φ_h(a)=4^{h−1−j}; φ(>−h)=Σ_{level j<h}4^{h−1−j}. Bounds
  countAbove; μ(>−h) ≤ 2^{−h+1}·φ(>−h). Exact deltas:
    Cancel j<h: Δφ_h=−2·4^{h−1−j}; else 0.
    Split: j+1<h: Δφ_h=−(1/2)·4^{h−1−j}; j+1=h: Δφ_h=−4^{h−1−j}(=−1 at j=h−1); j≥h: 0.
  LEAN-SAFE φ lemma: either the exact case split, OR the inequality "split level j, j<h ⟹ φ_h(after) ≤ φ_h(before)
    − (1/2)·4^{h−1−j}" (exact interior, conservative at boundary where true drop is 1).
USE when slot-3 starts (deferred, codex on slot-0): these are the p3_biasSum_step_eq / p3_totalMass_step_le /
p3_massAbove_step_le / p3_phiAbove_split_delta lemma bodies (§103 piece b), with WEIGHTED μ throughout.

## §106 (2026-06-18, Q15 family OK) — role-windows are ABSTRACT-awaiting-constructor (not false); concrete path

Q15 (verify-don't-transcribe; repo-cited) audits the remaining εWin role-windows producers. VERDICT: NOT
false-shaped — abstract atoms instantiable by EXISTING machinery. The ONE false-shape to avoid: a plain
unconditional MilestonePhase/martingale drift over the RAW kernel assuming the floor/gate always present
(false at small mcrCount + assignableCount=0; the repo already documents this). Must be killed/gated.

(a) Main / top-split window (RoleSplitWindowMartingaleAtom, RoleSplitWindowsBennettAtom, topSplitWindow_whp,
roleSplitWindows_whp) — SAME stochastic family as the warm-up top-reaction analysis. Instantiate via the
warm-up killed-monitor/Bennett/cosh machinery (Phase0WarmupReachKilled) with relabel:
  freeTargetCount floor monitor → top-split alive gate / free-target floor
  top U,U or U,freeTarget scheduler rectangle → R1/R2/R3 top-assignment rectangle
  freeTargetCount deviation → Main-count or topCRMass signed deviation
  floor escape → the additive hrest/killed-escape budget.
NOT iid Bernoulli (null interactions, gate exits, concurrent R4 drain matter) — killed/gated monitor + escape.

(b) CRDrainWindow — NOT a catalytic pull; a DIAGONAL self-drain R4: CR,CR→Clock,Reserve, rate
crCount(crCount−1)/(n(n−1)). Missing KernelMilestone constructor input = phase0_crCount_decrease_prob (ALREADY
in repo, Stage-2 theorem). Reframe: freeMCRKernelMilestone → crCount KernelMilestone; progress pᵢ = M(M−1)/(n(n−1))
for current CR threshold M; milestone = crCount ≤ thresholdᵢ; post_sound = enough R4 firings + DETERMINISTIC
ClockReserveBalanced ledger ⟹ Clock ≥ (1−η)n/4 ∧ Reserve ≥ (1−η)n/4. Clock/Reserve balance is deterministic,
NOT a new martingale (matches the §-adjudication-log εbalance-is-deterministic finding). No-MCR shell ABSORBING
for Stage 2 (once roleMCRCount=0 no rule recreates MCR → killed escape mass zero). Drain-to-Θ(n): constant
lower-rate corollary; drain-to-≤1: heterogeneous Janson/KernelMilestone family.

PATH (codex r23): instantiate (a) from Phase0WarmupReachKilled, (b) from phase0_crCount_decrease_prob +
ClockReserveBalanced → discharge roleSplitWindows_whp → concrete phase0_roleSplit_whp (RoleSplitGood whp,
εRole O(1/n²)) → slot-0/Lemma 5.2 CLOSED. No reframe needed; reuse maximizes the verified warm-up investment.

## §107 (2026-06-18) — ★SLOT-0 STRUCTURAL ERROR FOUND (adversarial audit, Xiang-directed): §94 false-floor RESURFACED in stage15Gate★

After r21→r24 kept revealing "one more producer" (the §3.3 fingerprint), Xiang invoked the playbook: STOP grinding,
adversarial-audit. codex (Lean dep trace H1-H4) + ChatGPT family3 (vs Doty §5) CONVERGED:

ROOT CAUSE: `stage15Gate` (the Stage-1.5 interface gate, Phase0RoleSplitDischarge:320) uses the RAW `floorGate`
= `assignableCount` (RoleSplitConcentration:3168) — which is EXACTLY the §94 NON-MONOTONE false-floor object we
killed. The CLOSED MCR-race route uses the MONOTONE `freeFloorGate` (Phase0StoppedRace:180), whose warmup entry is
ALREADY wired (Phase0StoppedRace:2535). So the Stage-1.5 interface is built on the discredited assignableCount floor
⟹ the proof keeps "forever rediscovering" the same raw floor/no-advance producer (hfloorEntry, w15's floor part).

Plus:
 - H1 REDUNDANT producers: hphaseEntry already closed (allPhase0_window_whp_unconditional_from_fresh, :927);
   hentry's role-MCR part already closed (phase0_mcr_race_whp_from_fresh_freeFloorBirth_drain, :2957). The wrapper
   re-demands them as fresh hyps.
 - H3 DOUBLE-COUNT: `_work0_fresh` consumes the closed MCR-race theorem AND `work0` (EndpointWiring:99), whose
   Stage1/1.5 path (RoleSplitConcentration:5868) ALSO drives MCR→0 — so MCR→0 is driven TWICE.
 - family3: Doty's Lemma 5.2 is DIRECT (5.1 top-split + role-split + concentration), NOT a 3-stage CK entry-gate
   cascade. The "correct older spine already exists"; the later assembly proliferated stages (over-decomposition).

FIX (codex's one-step repair): make slot-0 consume the already-closed phase0_mcr_race_whp_from_fresh_freeFloorBirth_drain
+ the concrete windows/Stage-2 tail DIRECTLY; change stage15Gate's gate from raw `floorGate`(assignableCount) to the
stopped-process `freeFloorGate`/`floorOrDoneGate` (monotone); drop the redundant Stage-1.5 entry re-derivation + the
double-counted staged MCR path. This COLLAPSES the entry-tail cascade → slot-0 closes.

LESSON: the §94 false-floor (assignableCount) was killed in the MCR-race route but SURVIVED in the Stage-1.5 gate
definition — a discredited object resurfacing in a sibling interface. When you kill a false object, grep ALL its
uses; a stale gate built on it re-spawns the exact producer forever. (And: grinding "one more producer" 4+ rounds =
STOP + audit, per §3.3 — Xiang had to invoke it; I should have self-triggered.)

## §108 (2026-06-18) — ★★SLOT-0 / LEMMA 5.2 CLOSED — INDEPENDENTLY VERIFIED★★

phase0_roleSplit_whp_closed_mcrRace_concrete_windows_work0_fresh_calibrated (Phase0StoppedRace:4145):
  (kernel^T) c₀ {¬ RoleSplitGood (1/25) n} ≤ O(1/n²) from Phase0InitialFresh,
carrying ONLY satisfiable regime/calibration numerics (hn6/hN/hn2/hn203/ha1/h2a/haWarm/hTwarm/htotal/hlog,
lam/hlam/ht, s/sc/hs/hδn) — NO abstract producer, NO uninstantiated budget. Bound fully concrete:
topSplitCoshPrefix + 4·roleSplitInvSqBudget + freeMCRJanson + crDrainStage2Budget(=1/n²) + clock budget.

INDEPENDENTLY VERIFIED (not codex self-report): full ExactMajority closure Build completed (3824 jobs, EXIT 0);
#print axioms = [propext, Classical.choice, Quot.sound]; zero sorryAx.

THE SAGA RESOLVED: §90 stopping-time race + §94 monotone floor → §96 c₀-anchored clock-leg → §98/99/100 killed
first-exit warm-up + milestone + constants → §101/102 typed first-exit → §104 MCR-race half closed → §106 role-windows
concrete → §107 STRUCTURAL ERROR FOUND (raw-floorGate=assignableCount §94 false-floor resurfaced in stage15Gate;
audit-converged codex+family3) → re-frame collapsed the cascade → §108 Stage-2 budget calibrated to 1/n² → CLOSED.

Slot 0 was one of the TWO deepest residuals. Board now: 10/11 phase-atom cores (slots 0,1,2,4,5,6,7,8,9,10);
slot 3 (phase-3 cancellation) the remaining deep partial. STILL NEEDED for unconditional Thm 3.1: slot 3, the `ra`
constructor (instantiate all 11 + regime wiring), the per-slot escape audit. Slot-0 ✅ is the hardest one done.

## §109 — slot-3 leaf-design synthesis (Q27-Q30 read in full, 06-18)

Four family ChatGPT design drops (HANDOFF/slot3-drops/Q27..Q30) digested. State of the 4 slot-3 probabilistic leaves:
 - 6.13 catalytic (Q27): SAME pattern as closed slot-0 catalytic-pull; generic engine `CatalyticPull.catalyticPullKernelMilestone`
   already in repo (no monotone-floor demand). Only NEW Lean = one deterministic scheduler rectangle `phase3_h13_pull_rect`
   (a₀ clock catalysts × i lagging-O → step-decrease ≥ 2a₀i/(n(n-1))) + stopped-floor plumbing. NO new concentration thm.
 - 6.15 φ-decay (Q29): ALREADY LANDED (`Lemma615MassAbove.massAbove_le_phase3_whp` log-φ Azuma, wrapped by
   `Phase3Engines.h15_muAbove_tail_numerical`). Remaining = stopped-gate transfer + killed-support `hdiff` + const sync (1/1000 vs 1/500).
 - 6.16 mass-halving (Q30): `H16Engine` already has six-stopped-row+cover+union shape; mechanical fill from
   `CancelClockConcentration.stoppedKernel`, reuse `mkH16`/`stoppedTail_sixUnion`. Each row 2·prevρ−2d=ρ.
 - 6.17 minority (Q30): REAL FINDING (implemented 679b979) — leakTotal=0.0032 genuinely fails rows ℓ−3/ℓ−2/ℓ−1
   (repo machine-proves `row_lm3_table_not_closed` etc); need η617≤0.0027, used 0.0024. Carry σ=sign(g), never WLOG A.

TWO GENUINE STRUCTURAL OBSTRUCTIONS — same lesson (interface over-strong on UNCONSTRAINED objects, = the §94/§107 trap):
 A. hdom (Q28 Regime): `BiasedMainIndexLeHour` (index≤own hour) is NOT a step invariant — repo re-exports the
    machine-checked obstruction `biasedMainIndexLeHour_not_phase3_step_invariant` (high-hour zero splits low-hour biased).
    And Lemma 6.10 gives only small-tail 0.0012|M|, NOT the pointwise zero-tail `HDomAt` wants. → MUST refactor `HDomAt`
    to active-band ceiling (`AllBiasedMainBelow` from deterministic top-edge ledger `phase3CancelSplit_preserves_top_edge`)
    + small Main-tail (6.10). ★REGIME BRIEF MUST CARRY THIS: do NOT prove BiasedMainIndexLeHour, it is FALSE as invariant.
 B. 6.11 leakage (Q29/codex §107): `LeakageBridge.tail` demands tail≤0.0027 for ARBITRARY checkpoint starts incl dt=0,
    but drift hyps only hold at alive gated starts → constrain `CoreRunSurface` checkpoint start to leakage-good (codex fixing).
A≡B: an interface quantifying over unconstrained starts/objects is too strong; constrain to reachable/good-gated. Caught at
DESIGN stage (火眼金睛 working) — not after half-grinding.
