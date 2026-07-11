# Doty Thm 3.1 — GLOBAL CHECKLIST (de-vacuum → 0-residual → clean). 2026-06-21

GOAL: a single `doty_theorem_3_1` that is GENUINELY NON-VACUOUS (every carried hyp satisfiable, no
false-blanket-∀, no relocated contradiction), conditional only on DotyRegime + validInitial + card + 2≤n
(+ honest satisfiable named concentration residuals), authoritative-build + axiom clean, dead code removed.

SOUND HEADLINE = `FaithfulCoreDischarge.doty_theorem_3_1_fully_unconditional` (chain-restricted reach;
takes `FaithfulWorkSeamCore` + `hT/ht/hε`). The vacuous variants (minimal/unconditional, false hReach10)
are DEPRECATED-marked. "axiom-clean + sorry-free" is NOT the bar — NON-VACUITY is.

Status key: ✅ done(build+axioms verified) · 🔄 in-flight · ⏳ todo · 🔍 audit-then-repair-if-live

---
## A. DE-VACUUM — make every carried hyp SATISFIABLE (no vacuity). The audits peel these one at a time.
- [✅] A1  ε arithmetic: εepidemic 1/n²→1/(2n²), seamHalfBudget split. (L1, commit 6de7353)
- [✅] A2  overshoot residual domain: SeamPre→SeamEntry (NoOvershoot conjunct excludes overshot). (L2, 915648c)
- [✅] A3  opinion-seed Post: allPhaseEq p ∧ advTriggered(p+1) UNSAT → allPhaseGe p ∧ advTriggered(p+1)
          (= SeedPresencePost; seedPresencePost_satisfiable PROVES ∃c — genuine non-vacuity witness).
          slot4 honestly carries TerminalSeedCarryInputs (not faked). (L3, build 3861 jobs + axioms clean)
- [🔄] A4  hSeamEntryFromWorkPost (Thm31Final:597): round-3 = STRONG SUSPECT (not kernel-level CE'd yet).
          Prove the chain's work-Post genuinely reaches SeamEntry in 1 step, OR strengthen the work Post.
- [N/A] A5-A8  SPINE_MAP §8 (hAtRisk/hdet/Phase6ClockTail.hcap/hcover/hcard/hreset/FloorFailSeedLeg.hPersist):
          round-3 confirmed these are NOT live carried hyps in the 5 live files (de-vacuum/chain-restriction
          already removed them). No action.
- [✅] A10 slot4 hPostToGe UNSAT: FIXED — StableTie4Card (card=n added, Phase4Convergence:95); producer
          derives allPhaseGe 4 internally. (verified, build+axioms)
- [✅] A11 tieResiduals FALSE BLANKETS — the CORE seam-handoff vacuity. Round-3/4 found all 9 slots
          (1/2/3/4/6/7/8/9/10) were false `∀c, allPhaseEq p → SlotKReady` (A11 v1 only renamed consequent —
          still false via identical-agents counterexample). FIXED by CHAIN-RESTRICTION (the hReach10 pattern):
          all 9 now `∀c, Reachable c₀ c → allPhaseEq k → SlotKReady` + proven SlotKReady→work.Pre decompositions.
          grep confirms 0 bare-blanket remain; build 3861 jobs + axioms clean. The 9 are now honest
          reachable-restricted named residuals → A12 classifies each.
- [✅] A12 CLASSIFIED (round-5, bz10009i2): the 9 reachable residuals split as below. Chain-restriction is
          the FINAL form only for slot10-under-branch; the rest need predicate-fix or measure-level.
  - [🔄] A12.3  slot3 STILL-FALSE: Slot3Ready wants c=entry (config identity, NOT phase-3-preserved) →
              weaken to reachable phase-3 shape. (bslyq10qq)
  - [🔄] A12.4  slot4 STILL-FALSE: Slot4Ready wants output=T/noBigBias from allPhaseEq → provide from
              phase-4 Post. (bslyq10qq)
  - [🔄] A12.10 slot10 invariant ONLY under A-majority/tie branch (0≤initialGap) → add gap-sign cond or
              B-majority mirror. (bslyq10qq)
  - [⏳] A12.{1,2,6,7,8,9} GENUINE-CONCENTRATION → B-section (measure-level seam-epidemic, NOT deterministic
              ∀-reachable): slot2/9 informedU≥1 survival; slot1/6/7/8 DrainReady∧mass≤M₀. The deterministic
              ∀-reachable residual is STILL false for these (low-prob reachable CE) — restate measure-level.
- [⏳] A9  CONTINUE the full carried-hyp sweep each round until none suspect. (rounds 1-3 done; A4/A10/A11 open)

## B. GENUINE CONCENTRATIONS TO PROVE — the honest satisfiable bottoms (strategies banked)
- [⏳] B1  overshoot Chernoff tail = TerminalReachableOvershootResidual.hNoOvershoot. n^{1-Ω(c_i)}≤1/(2n²),
          Bin(αn ln n, 2/n) per clock, union over n. TIMED slots {1,5,6,7,8} only. (OVERSHOOT_TAIL_STRATEGY.md)
- [⏳] B2  front recurrence whp = front_recurrence_holds_whp (Doty 6.3/6.5 squaring; ε63=exp(-Ω(n^0.1)),
          early-drip O(n^{-0.85})). (FRONT_RECURRENCE_STRATEGY.md)
- [🔍] B3  §clock tail (per-phase clock-positivity): participation-drain engine landed (clock_real... );
          verify the full ClockRealFaithfulHonest chain (4 side-prefix terms) is genuine, no carried gap.
- [⏳] B4  per-seam first-advance count conditions: A,B both-sign Θ(n) (seam 2/9), H≥1 witness (seam 4),
          clock-front (seam 3). First-advance tails committed; the upstream counts remain.
- [🔍] B5  per-slot work survivals (role-split/escape/epidemic/confinement/C5a): mostly discharged from
          the survival cores — verify each is genuine (not vacuous) on the live chain.

## C. CALIBRATION FITS (the sound headline's hT/ht/hε) — discharge from the witnesses
- [⏳] C1  hε (∀i ε≤1/n²): discharge from seamHalfBudget_double_le_invSq + work-slot budgets (not carry bare).
- [⏳] C2  ht (∀i t≤C0·n·(L+1)): discharge from per-slot time fits.
- [⏳] C3  hT (T=Σt): definitional.

## D. FINAL ASSEMBLY → single 0-residual theorem
- [⏳] D1  Build FaithfulWorkSeamCore from DotyRegime+validInitial (faithfulWorkSeamCore_of_valid needs a
          FaithfulCore — construct it from the regime + the discharged A/B above).
- [⏳] D2  Instantiate doty_theorem_3_1_fully_unconditional → ONE doty_theorem_3_1 (0 residual beyond
          regime+validInitial+honest named concentrations B1-B5).
- [⏳] D3  Final non-vacuity audit (independent) + authoritative build + #print axioms.

## E. DEAD-CODE CLEANUP (only AFTER D — top-down by import closure)
- [✅] E1a mark the 2 known-FALSE variants (minimal/unconditional) DEPRECATED. (done this session)
- [⏳] E1b SPINE_MAP kept as the authoritative live-head + dead-list map.
- [⏳] E2  compute exact transitive import closure of the final doty_theorem_3_1.
- [⏳] E3  trash everything outside the closure in batches (V2-V7 ~5-6k lines, Headline*/Migrated*/Concrete*
          variants, counterDepth* detour, duplicate work-constructor fragments), re-verify build per batch.

---
## Layers peeled so far (the de-vacuum trail — each a real bug #print-axioms can't see)
L1 ε-arithmetic contradiction → L2 overshoot-domain too-broad → L3 opinion-seed Post unsat → (A4/A9 next).
Each found by an INDEPENDENT adversarial audit, verified by hand, committed only after authoritative build.

## Concentration harvest (2026-06-21, parallel codex + family)
- [✅] B1 OvershootChernoffTail.lean — GENUINE (audit), committed 5cc08bc. Residual: Mathlib binomial-Chernoff upper tail.
- [✅] B2 FrontRecurrenceWhp.lean — GENUINE, committed 5cc08bc. Caveat: instantiate on finite minute domain.
- [✅] drain SlotDrainReadyConc.lean — GENUINE (slot6/7/8 from contracting survivals), committed 5cc08bc.
- [🔄] informedU — was VACUOUS (ignored deterministic signed-sum); REDOING via signed-sum conservation (b412m1wua).
- [🔄] slot4 Phase4Post — NOT deterministic (family1): = Phase-3 concentration + Phase-4 gate; joins concentrations.
- [🔄] slot10 B-majority mirror — family2: Phase10Ready := S1 ∨ S0 ∨ Tie1plus (S0 = B-wins mirror, Doty Lemma 7.7 WLOG). Dispatching.
- [✅-ish] B3 §clock — family3: role-pop floor (Lemma 5.2, deterministic given RoleSplitGood, already counted) +
        counter tail (participation drain, ALREADY DONE). Mostly covered; just wire the role floor.

## E-section cleanup method (family2, 2026-06-21)
Module-level import closure FIRST, deletion second. A .lean not in the final theorem module's TRANSITIVE
import closure ⟹ nothing live imports it ⟹ safe to delete. Compute over Lean MODULE IMPORTS (syntactic,
not theorem refs): a Python script parses `import` lines recursively from the root (final theorem module) →
closure set; everything in Ripple/.../ExactMajority NOT in the set = dead. Trash in batches (trash not rm),
rebuild the final theorem after each batch, revert if broken. Module-closure is sufficient (if module M not
in closure, no live module imports it — even one-lemma reuse would show as an import). Do AFTER the final
theorem lands (else discharge files mis-flagged). ~200 dead expected (FinalAssemblyV2-V7, Headline*/Migrated*/
Concrete* variants, counterDepth* detour, vacuous capstones).
