# DOCTRINE — autonomous grind: Thm 6.9 → converges to C-A (front-shape hcap_all)

**Approval:** user "继续啃 Thm 6.9. 自主执行." (2026-06-13). Driving autonomously to milestone/hard-block.

## Finding (Thm 6.9 audit, 2026-06-13)
- ABSTRACT Thm 6.9 (`ClockHourBounds.clock_hour_bounds` / `all_hours_O_log_n` on `clockProto (Minute L₀)`):
  GENUINELY PROVEN, axiom-clean `[propext, Classical.choice, Quot.sound]`, SATISFIABLE preconditions
  (`seedFloorInv` seed floor + ε Chernoff rate bounds). NOT vacuous. ✓ DONE.
- REAL-kernel `ClockRealHours.clock_real_O_log_n`: carries the BARE `habs_mix_all` (∀T c c', Q_mix→support→Q_mix).
  FrontSyncConc established the bare deterministic Q_mix closure is FALSE off FrontSync (at-cap counter=1
  witness `counterPos_one_step_NOT_closed_witness`) ⟹ conditionally vacuous on a false hyp. SUPERSEDED by the
  FrontSync-gated honest `ClockUnconditional.clock_real_unconditional`, which carries `hwin_all`
  (`FrontSyncConc.FrontFeederWindow`) — the C-A front-width residual.
- `ClockFrontWidth` reduced `hwin_all` to the SINGLE terminal residual `hcap_all`:
  `rBeyond (cap−1) c ≤ Bcap` on reachable FrontSync configs (Bcap = O(log log n) doubly-exp envelope cap).
  Everything else PROVEN: per-level squaring `front_breach_le_capSq`/`rBeyond_seed_le_rBeyondSq`, union bound
  `frontSync_union_horizon`, 1/poly budget, `FrontSyncConcentration_remaining` discharge.

**CONVERGENCE:** Thm 6.9 (honest real) AND Lemma 6.10 BOTH reduce to C-A = `hcap_all` = the front-shape
maintenance. This is THE genuine deepest remaining core.

## Goal (one sentence)
Discharge `ClockFrontWidth.hcap_all` (the doubly-exp front-feeder cap on the reachable FrontSync trajectory),
closing the honest real-kernel clock (Thm 6.9) and the FrontSync-gated Q_mix closure.

## Avenues
- (a) **Multi-level downward cascade** (the roadmap structure, ChatGPT-confirmed): maintain the within-envelope
  profile `RWithinEnvelope f₀ i` from the subcritical entry i₀ (where front fraction first ≤ 1/2... actually ≤ n^{−0.4})
  down/up the O(log log n) leading levels via the proven per-level squared seed `front_breach_le_capSq`, with the
  EARLY-DRIP GHOST term (essential — bare recurrence false at tiny tail). Anchor at the subcritical level; the
  doubly-exp envelope collapses below 1/n within `frontWidthBound n = O(log log n)` levels (`rFront_emptied_of_envelope`,
  PROVEN). The genuine residual: `rEnvelope_maintained` (the within-envelope invariant along the trajectory).
- (b) **Couple to the abstract `FrontShapeInduction`** (Config (Minute L₀)) where `front_shape_collapse`/
  `front_emptied_real`/`frontShape_couples_earlyDrip` are PROVEN — transfer the abstract maintenance to the
  real `rFrontFrac`. (The abstract model has the full doubly-exp maintenance; the real-kernel transfer is the gap.)
- (c) **Lean-friendly transfer theorem** (ChatGPT recommendation): `Pr[∀i,t. n^{−0.4} ≤ X_i ≤ 0.1 ⟹ X_{i+1} ≤ p X_i²]
  ≥ 1 − n^{−ω(1)}`, then `frontWidth_loglog` consumes it; one sparse-pioneer/no-long-early-drip lemma for sub-n^{−0.4}.

## Terminal conditions
- SUCCESS: `hcap_all` discharged on the reachable FrontSync domain, axiom-clean. Then clock_real_unconditional
  is unconditional (modulo the satisfiable entry), and Thm 6.9 real is honest.
- HONEST-RESIDUAL: `rEnvelope_maintained` isolated precisely over the reachable domain (refutation-checked,
  not a false universal), with the exact remaining lemma named.

## ⚑ MAJOR SYNTHESIS FINDING (2026-06-13 autonomous audit) — C-A is GENUINELY OPEN

The autonomous Thm 6.9 grind audited the whole §6 clock chain and found: the deep core (C-A front-shape
maintenance) is "discharged" by a CHAIN OF FILES, each REDUCING it to a carried `∀c` hypothesis that is
FALSE (a bunched/at-cap witness), then "deferred to another avenue" — but NEVER honestly proven over the
reachable domain. The false `∀c` hypotheses, all refutable by the SAME pattern:
- **Lemma 6.10** `hour_coupling_v2` : `∀c Regime` — FALSE (empty config, `clockCount 0 ≠ C`).
  REFUTATION VERIFIED IN LEAN: `Lemma610StoppedAzuma.regime_not_universal`. FIXED via stopped kernel.
- **clock_real_O_log_n** : `habs_mix_all` (∀c, Q_mix → support → Q_mix) — FALSE (a phase-3 clock with
  counter 0 at the minute-cap advances to phase 4, breaking `clockPhase3`; at-cap counterPos witness).
- **FrontNarrowConc** `rFrontNarrow_concentration_proven`/`clock_frontSync_via_narrow` : `hfeeder_all`
  (∀c, rBeyond(cap−1)=0 ∧ AllClockP3 ∧ card=n → RWithinEnvelope f₀ (cap−2)) — FALSE: n clocks bunched at
  minute cap−2 satisfy the LHS (rBeyond(cap−1)=0) but rFrontFrac(cap−2)=1 ≫ envelope (e.g. f₀=0 ⟹ env=0).
- **ClockFrontWidth** `rEnvelope_maintained` (∀c) — EXPLICITLY noted FALSE in its own docstring.

ALL follow the `regime_not_universal` pattern (verified-in-Lean exemplar). So C-A is NOT discharged: the
"proven" concentrations are conditionally-vacuous on false `∀c` deferrals.

HONEST TARGET (the genuine deep core, unchanged): the within-envelope maintenance over the REACHABLE
trajectory (NOT `∀c`), with the early-drip GHOST term (Doty Lemma 6.3). This is the multi-session piece
mapped in `CLOCK_FRONTSHAPE_ROADMAP.md` (avenues a/b/c). The fix PATTERN is the same as Lemma 6.10's:
replace the false `∀c` window with a STOPPED/reachable-restricted construction whose maintenance is the
genuine probabilistic concentration. The Lemma 6.10 stopped-kernel fix is the verified template.

## ROUTE PLAN v0 (architecture, PRE-PROOF — to refine with ChatGPT over several rounds)

User directive (2026-06-13): "先规划好路线, 不用贸然上证明" + "多走几轮" — architect first, multi-round ChatGPT.

The honest C-A discharge = prove FrontSync maintained whp over O(log n) steps, conditional on a SATISFIABLE
synchronized-start hypothesis (NOT a false ∀c). Four components:

COMPONENT 1 — the level-split (bulk vs leading).
  rFrontFrac(i) is decreasing in i (≈1 at i=0 → 0 at i=cap). Define the subcritical entry
  i₀ := largest level with rFrontFrac(i) ≥ θ (θ const, ~0.1). BULK (i ≤ i₀): fraction Θ(1), trivially within
  an envelope ≈ 1 — NO concentration. LEADING (i > i₀): fraction < θ subcritical, the doubly-exp squaring
  applies. The within-envelope invariant is non-trivial ONLY on the O(log log n) leading levels.
  OPEN Q (round 1): is i₀ cleanly Lean-definable on the actual config? Does the split give a clean structure?

COMPONENT 2 — the leading-front within-envelope maintenance (THE CORE).
  Union bound over the O(log log n) leading levels × O(log n) steps of the PROVEN squared seed
  (rBeyond_seed_le_rBeyondSq), PLUS the early-drip GHOST (Doty Lemma 6.3) for the bottom-of-leading levels
  where the bare squaring breaks (single lucky drip at tiny tail).
  OPEN Q (round 1): cleanest Lean formalization of the ghost that AVOIDS tracking per-agent provenance
  (e.g. a separate Chernoff over the O(log log n)·H interactions each with prob ≤ p·n^{−0.9})?

COMPONENT 3 — the stopped-kernel wrapper (the VERIFIED Lemma 6.10 template).
  front-shape regime = {leading front within envelope ∧ i₀ well-defined}. K* = piecewise{regime} K id.
  On the regime: per-step breach bounded (front_breach_le_capSq, PROVEN); off: frozen. ⟹ FrontSync-breach
  concentration for K* is HONEST (no false ∀c), conditional on the within-envelope START.
  OPEN Q (round 1): does the stopped-kernel template fit a MULTI-LEVEL invariant, or is a level-indexed
  family of stopped supermartingales cleaner? (Lemma 6.10 was a single supermartingale.)

COMPONENT 4 — the satisfiable entry + the remaining obligation.
  Entry: the synchronized phase-3 seam where the front is within envelope (satisfiable, from role-split/seam).
  Remaining genuine concentration = regime-confinement (trajectory stays within envelope whp) = Components 1-2.

ROUND PLAN: R1 (fired) — level-split + ghost + stopped-structure + minimal hypothesis. R2 — refine i₀ def +
ghost-negligibility Chernoff + exact union budget. R3 — entry hypothesis + wiring. THEN code (per user: no
rushing into proofs). The verified `regime_not_universal` + `Lemma610StoppedAzuma` are the templates.

## ROUTE PLANNING — my own investigation findings (2026-06-13, pre-ChatGPT-round-1)

While ChatGPT reads xiangyazi24/Ripple @0062175 (family: scalar-potential/stopped-fit; family2: avenue-b
coupling), I audited the codebase myself:

FINDING 1 — the within-envelope MAINTENANCE is proven NOWHERE. Every front-shape lemma (abstract
`FrontShapeInduction` AND real `ClockFrontWidth`/`FrontNarrowConc`) ASSUMES `FrontWithinEnvelope`/
`RWithinEnvelope`/`hfeeder_all` as a hypothesis and proves CONSEQUENCES (the count cap, the empty-front,
the early-drip smallness). NO theorem CONCLUDES the maintenance. Grep confirms: no `→ FrontWithinEnvelope`
/ `→ RWithinEnvelope` maintenance theorem exists.

FINDING 2 — AVENUE (b) IS DEAD. The abstract `clockProto (Minute L₀)` model has the SAME gap: its
`frontShape_couples_earlyDrip` (within-envelope → count cap) and `early_drip_small_at` (the ghost bound)
are BOTH conditional on `FrontWithinEnvelope`/`hwin`. So coupling the abstract model to the real kernel
transfers a CONDITIONAL result — no free lunch. The genuine concentration (the probabilistic maintenance)
must be proven directly (avenue a), on the reachable/stopped domain.

FINDING 3 — NO scalar front potential exists in the codebase. So the KEY architecture decision (the family
question): can a SINGLE scalar potential Ψ_front = Σ_i w_i·rFrontFrac(i) (doubly-exp weights) be made a
supermartingale on the within-envelope regime — reducing C-A to ONE stopped Azuma (my verified
Lemma610StoppedAzuma template)? If YES → C-A closes by the exact Lemma 6.10 pattern. If NO → multi-level
union + early-drip-ghost Chernoff (harder). This is THE pivot; await ChatGPT family round 1.

REVISED ROUTE (converging): avenue (a) only [b dead]. The maintenance is the genuine open core, proven
nowhere. The stopped-kernel wrapper (Lemma 6.10 template) eliminates the false ∀c. The OPEN architecture
question = scalar-potential-supermartingale (one stopped Azuma) vs multi-level-union+ghost. Decide via
ChatGPT round 1, THEN code.

## ROUTE PLAN v1 (ChatGPT family round-1 @0062175, 2026-06-13) — the AGREED architecture

PIVOT RESOLVED: NO single scalar potential exists for the front-shape (unlike Lemma 6.10's Φ). So C-A
is NOT one stopped Azuma — it is a LEVEL-INDEXED family + an AUGMENTED GHOST KERNEL + a pathwise first-exit
union bound. The honest target is a PATHWISE stopped/first-exit statement, NOT ∀c.

THE ARCHITECTURE (one line):
  SyncStart ⟹ WindowGood + GhostSmall + SparseNoChain ⟹ CleanTail ⟹ FrontWidthOK.

THREE REGIMES (tail counts X_i := rBeyond(i)/C₀, NOT pointwise; ρ=0.1, ε=n^{−0.45}, ε_clean=n^{−0.4}, η=n^{−0.85}):
  bulk        X_i ≥ 0.1            — DELIBERATELY IGNORED (used only in deterministic front-width, via bulkIdx).
  mesoscopic  n^{−0.4} ≤ X_i ≤ 0.1 — the squaring recurrence X_{i+1} ≤ 0.9p·X_i² + D_{i+1}/C₀ (Lemma 6.3 + ghost).
  sparse      X_i < n^{−0.4}       — the seed-only union bound (where my PROVEN rBeyond_seed_le_rBeyondSq fits).

THE GHOST (essential, NOT "no early drips" — too strong): an AUGMENTED kernel. Either labeled descendant
sets `GhostState = {cfg, ghost : level → Finset AgentId}` or (for the multiset kernel) a DOMINATING
ghost-count `GhostDomState = {cfg, D : level → ℕ}` with one-step domination:
  P[D_i gets early immigrant | F_t] ≤ 1_{X_i<ε}·p·X_i²;  P[D_i grows by epidemic] ≤ 2D_i/n.
The ghost-count need not equal the true set — only dominate under a coupling. GhostSmall: D_i/C₀ ≤ η whp.
Negligible vs X_i² when X_i ≥ n^{−0.4} (X_i² ≥ n^{−0.8} ≫ n^{−0.85}) — THIS is why the clean recurrence uses n^{−0.4}.

STOPPED KERNEL: applied LOCALLY per level (`K63star i z = if Active63 i z then Kaug z else pure z`), NOT as
one global envelope drift. Active63 i = Phase3Window ∧ ε ≤ X_i ≤ ρ ∧ GhostSmall ∧ ParentWindowGood.

FOUR LAYERS:
  A (deterministic tail geometry): bulkIdx, MesoscopicCleanAt → squareEnvelope → FrontWidthOK. Consumes my
    EXISTING frontWidth_loglog / rFront_emptied_of_envelope.
  B (Lemma 6.3 window transfer + ghost): `lemma63_window_transfer` from 3 window ingredients
    (parent_tail_growth: X_i(t−L) ≤ a·X_i(t); drip_immigration ≤ b·p·X_i²·C₀; epidemic_amplification:
    nonGhost(t) ≤ γ(nonGhost(t−L)+imm)), constants γ(0.9a²+b)<0.9 [a≈0.84, b≈0.11, γ≈1.23, window L=0.1n].
    → `lemma65_clean_step_from_ghost` (0.9pX² + n^{−0.85} ≤ pX² for X ≥ n^{−0.4}). THE honest ∀c replacement.
  C (whp concentration): windowGood_all_levels_whp, ghostSmall_all_levels_whp, sparsePioneer_whp (Chernoff/
    Janson, union over levels×steps). My proven seed lemmas → sparsePioneer only.
  D (first-exit transfer): ShapeGoodPath (WindowGood ∧ GhostSmall ∧ NoSparsePioneer all t≤H) → FrontWidthOK
    deterministically; then `front_shape_exit_prob ≤ n^{−A1}+n^{−A2}+n^{−A3}` (pure union bound).

SyncStart HYPOTHESIS (SATISFIABLE — excludes the bunched-at-cap witness, which is NOT a synchronized entry):
  card=n ∧ Phase3ClockConfig ∧ C₀=clockCount ∧ C₀ ≥ κn ∧ InitialClockTail (X_0=1 ∧ ∀i>0 X_i=0, if minutes start at 0)
  ∧ no_ghost (D_0 = 0).

SCOPE: this is a LARGE multi-session build (the augmented ghost kernel is a new state space; the Layer-B
window argument + Layer-C concentrations are substantial). But the architecture is now CONCRETE and agreed.
ROUND 2 (next): refine the GhostDomState domination coupling (Layer B/C) + the augmented-kernel Lean
construction (is Kaug a clean Mathlib kernel?). family2 (avenue-b coupling) pending — my audit already killed it.

## family2 round-1 (avenue-b coupling) — CONFIRMS avenue (b) DEAD (2026-06-13 @0062175)

ChatGPT read the real code and confirms: the clock-minute projection `π(c) = (c.filter role=clock).map minute`
is a LAZY clockProto — `map π (K_real c) = p_clockPair·K_abs(π c) + (1−p_clockPair)·pure(π c)` (non-clock
interactions leave the clock subconfig unchanged), where `p_clockPair = clockCount(clockCount−1)/(card(card−1))`.
The laziness kills EXACT kernel functoriality (intertwining fails: condition "every sampled pair is clock-clock"
fails in the mixed protocol; clockProto sees mC clocks, real samples from n). AND: "the abstract file does NOT
prove a full reachable-trajectory maintenance theorem; it proves per-level squaring, envelope collapse, and a
CONDITIONAL early-drip handoff" — exactly my Finding 1. ⟹ avenue (b) dead (both my audit + ChatGPT-on-real-code).
USEFUL DETAIL retained: the lazy coupling `p_clockPair·K_abs + (1−p)·pure` may help Layer A/B relate the real
per-level squaring to the abstract envelope arithmetic (a lazy embedding), even though it doesn't transfer the theorem.

⟹ ROUTE PLAN v1 (avenue a, augmented ghost kernel, 4 layers) is the CONFIRMED route. Round 2: refine the
augmented-ghost-kernel Lean construction + the domination coupling (the hardest NEW object).

## ROUTE PLAN v2 — round-2 refinements (2026-06-13 @67fedb9)

### family2 R2 (Layer B): Layer B CANNOT be avoided for mesoscopic; write it FORWARD.
- KEY SIMPLIFICATION Q ANSWERED **NO**: the per-step squared seed (`rBeyond_seed_le_rBeyondSq`) only controls
  the FIRST seed into an EMPTY child level — NOT the child tail count once nonempty. Mesoscopic needs three
  things the seed lemma can't see: (1) parent normalization over the window; (2) cumulative drip-immigration
  concentration over L=0.1n steps; (3) epidemic AMPLIFICATION of immigrants. GhostSmall removes only the
  SPARSE early-drip ghost, NOT legitimate mesoscopic immigration/amplification. So: sparse `X_i<n^{−0.4}` →
  my seed lemmas ✓; mesoscopic `n^{−0.4}≤X_i≤0.1` → STILL need Layer B. Only the FORM simplifies.
- FORWARD FORM (do NOT formalize the past): rewrite `X_i(t−L) ≤ a·X_i(t)` as window-start `X_i(s) ≤ a·X_i(s+L)`,
  a `K^L` theorem from the window-start config; aggregate by integrating over the window-start distribution
  `∫ ((Kaug i)^L) z {bad} ∂((Kaug i)^τ c₀)`. No conditional-expectation, no past. Layer D unions over
  window-starts + first-exits. `lemma63_window_transfer_forward (i z) (hActive : Active63 i z) : (Kaug i ^ Lwin) z
  {z' | X(i+1) z' > 0.9 p X(i)²  + D(i+1)/C₀} ≤ ε_window`.
- EPIDEMIC MACHINERY @67fedb9: `ConstantDensityEpidemic.constantDensity_epidemic_O1_parallel` (forward growth
  lower bound, but CONSTANT-density 0.1n→0.9n only, not mesoscopic); `EpidemicTime` (analytic/conditional, not
  ready); `JansonHitting.milestone_hitting_time_bound` (generic milestone wrapper — the CLOSEST reusable, must
  specialize for multiplicative growth x→x/a in the mesoscopic range). The specific mesoscopic parent-growth
  lemma is NOT packaged — must build it (from JansonHitting).

### family R2 (augmented ghost kernel @67fedb9) — RESOLVED. ROUTE PLAN v2-FINAL below.

GHOST KERNEL CONSTRUCTION (resolved):
- INSTRUMENTED kernel `Kevent : Kernel cfg StepEvent` — samples the real interaction but RETAINS a certificate
  `StepEvent = {cfg', i, j, kind : ReactionKind, dripCoin, ...}`, with `map StepEvent.cfg' (Kevent c) = K c`.
- `Kaug z = map (updateAug z) (Kevent z.cfg)`, `updateAug z e = {cfg := e.cfg', D := updateD_from_event z e}`.
- EXACT cfg marginal: `map GhostDomState.cfg (Kaug z) = K z.cfg` (map_map + Kevent_cfg_marginal) ⟹ the augmented
  chain's cfg-projection IS the real protocol chain. `Kernel.map` for deterministic D-update; `Kernel.bind` if D
  needs extra dominating randomness. (A bare `Kernel.comp` is NOT enough — the D-update needs the realized transition.)
- DETERMINISTIC ghost from BARE cfg path = UNSOUND (multiset forgets provenance; worst-case overcharge destroys
  GhostSmall). Sound options: (B) deterministic from the INSTRUMENTED path (StepEvent certificate), or (C) a
  STOCHASTIC dominating count `KD_step` with `P[ΔD_i^imm]≤1_{X_i<ε}pX_i²`, `P[ΔD_i^epi]≤2D_i/n`. C is the v1 line.

GHOSTSMALL CONCENTRATION (resolved — REUSES MY VERIFIED TEMPLATE):
- D_i is NOT a supermartingale (positive drift `E[ΔD_i] ≲ 1_{X_i<ε}pX_i² + 2D_i/n`). So Lemma 6.10's Φ pattern
  does NOT apply to D_i directly. BUT the stopped-kernel WRAPPER applies per level:
  `KghostStar i = Kernel.piecewise {GhostActive i} Kaug Kernel.id` (exactly my Lemma610StoppedAzuma piecewise).
- The POTENTIAL is an EXPONENTIAL supermartingale `Ψ = exp(λ D_i − B_t(λ))` (predictable log-mgf compensator) —
  `∫ Ψ d(KghostStar i z) ≤ Ψ z` unconditionally by the SAME stopped-kernel case split, Chernoff read-off. THIS
  REUSES `AzumaKernel.expSupermartingale_drift` (the exp-MGF kernel drift I already used for Lemma 6.10) + my
  Lemma610StoppedAzuma piecewise wrapper. Or (Option 3, cleanest math) a direct dominating immigration+Yule
  branching Chernoff: D_{t+1} ≤ D_t + Bern(λ_t≤p n^{−0.9}) + Bern(2D_t/n); μ_imm ≤ O(n^{0.1} polylog) ≪ ηC₀=n^{0.15}.
- LOCALIZE: GhostSmall for level i holds ONLY in the LOCAL Doty Lemma-6.3 window (before/around X_i entering the
  mesoscopic band) — NOT the global O(log n) run (a tiny seed could eventually amplify too much over all time).

## ROUTE PLAN v2-FINAL — the Lean lemma chain (both round-2 answers synthesized, ready to code)
```
Kevent                    -- instrument real step; `map cfg' (Kevent c) = K c`  [NEW kernel object]
Kaug                      -- = map(updateAug) Kevent; `map cfg (Kaug z) = K z.cfg` (exact marginal)
K63star i / KghostStar i  -- = piecewise {Active63 i / GhostActive i} Kaug id    [my Lemma610StoppedAzuma piecewise]
ghostSmall_level_whp i    -- exp-supermartingale (AzumaKernel.expSupermartingale_drift) OR branching Chernoff; LOCAL window
ghostSmall_all_levels_whp -- finite union over leading levels
lemma63_window_transfer_forward i  -- FORWARD K^Lwin window-start; consumes GhostSmall; mesoscopic recurrence
                                      X(i+1) ≤ 0.9p X(i)² + D(i+1)/C₀  (parent-growth[JansonHitting] + imm + ampl)
lemma65_clean_step_from_ghost      -- 0.9p X² + n^{−0.85} ≤ p X² for X ≥ n^{−0.4}  [deterministic algebra]
sparsePioneer_whp         -- my proven rBeyond_seed_le_rBeyondSq + sparse-chain union (sparse regime only)
bulkIdx / MesoscopicCleanAt / FrontWidthOK  -- Layer A deterministic geometry; consumes frontWidth_loglog
front_shape_exit_prob     -- Layer D: ShapeGoodPath ⟹ FrontWidthOK (deterministic) + union ≤ n^{−A1}+n^{−A2}+n^{−A3}
```
START hypothesis: `SyncClockStart` (card=n ∧ Phase3 ∧ C₀=clockCount ∧ C₀≥κn ∧ InitialClockTail ∧ D₀=0) — SATISFIABLE,
excludes the bunched-at-cap witness. CODING ORDER: Layer A (low-risk, existing lemmas) → Kevent/Kaug scaffold +
the marginal theorem → K63star + ghostSmall_level (reuse Lemma610StoppedAzuma exp-drift) → Layer B forward → Layer D union.

## ROUND 3 — family2 (Layer-B detail @53066e5, 2026-06-13)

⚠⚠ CONSTANT CHECKPOINT = THE BIGGEST PRE-CODING RISK. The route-plan constants a≈0.84, b≈0.11, γ≈1.23 are
CLOCK-PAIR-PAPER-TIME constants, NOT real mixed-kernel constants. With C₀=κn (κ≈1/4), ρ=0.1, α=2 orientations,
a window of Lwin=0.1n TOTAL interactions forces `log(1/a) ≤ 0.1·ακ(1−ρ)/λ` ⟹ a VERY CLOSE TO 1 (not 0.84) ⟹
γ(0.9a²+b) ≈ 1.24 > 0.9, contraction BREAKS. FIX: measure the window in CLOCK-PAIR time — Lwin in total
interactions = 0.1n/κ² (clock-pair thinning; clock-clock interactions are κ² of all). With κ=1/4, Lwin≈1.6n.
Then a≈0.84 holds. ⟹ MUST re-derive all Layer-B constants for the real mixed kernel (clock-pair time scaling)
and re-verify γ(0.9a²+b)<0.9 BEFORE coding. Keep constants SYMBOLIC in Lean (`hParentMean : λ·meanTime ≤ Lwin`),
don't hard-code a=0.84.

LAYER-B INGREDIENTS (resolved, each pinned):
- parent_growth_forward (X_i(s) ≤ a·X_i(s+L)): `JansonHitting.milestone_hitting_time_bound` with UNIT count
  milestones (NOT geometric — milestones must be one-step-reachable): Y=rBeyond(i), milestone r = x+r+1 ≤ Y,
  p_r ≥ α(x+r)(C₀−yTarget)/(n(n−1)) [epidemic rectangle], meanTime ≲ n/(ακ(1−ρ))·log(1/a). NEW wrapper needed.
- drip_immigration_window: X_i MONOTONE ⟹ q_u ≤ p·X_i(end)² (endpoint dominates all earlier — no a^{−1} needed);
  μ ≤ Lwin·p·X_end²; Bernstein/Bennett for adapted bounded Bernoulli — `Ripple/Probability/BennettLemma.lean`
  (bernstein_optimal) IS on the repo (ChatGPT search missed it; cite the path). inputs: incr≤1, var≤q_u, μ, R=b·p·X_end²·C₀.
- epidemic_amplification_window: CRUDE per-step E[Y'|z] ≤ (1+2/n)Y ⟹ over Lwin: (1+2/n)^Lwin = e^{0.2} ≈ 1.2215 = γ.
  Cleaner than ConstantDensityEpidemic (which is bulk 0.1n→0.9n only). whp via Yule/branching Chernoff or exp-MGF.
- COMPOSITION ALGEBRA (resolved, clean): y0≤0.9pa²x1², imm≤bpx1², ampl γ(y0+imm) ⟹ nonGhost_end/C₀ ≤
  γ(0.9a²+b)·p·x1² ≤ 0.9p·x1² (if γ(0.9a²+b)≤0.9); +ghost ⟹ X(i+1) ≤ 0.9pX² + D(i+1)/C₀. = the Layer-B conclusion.
- CODING ORDER (Layer B): deterministic composition algebra FIRST (cleanest, symbolic constants), then
  parent_growth_forward (JansonHitting unit milestones), then immigration (Bennett) + amplification (crude MGF).

## ROUND 3 — family (Kevent/Kaug @53066e5) — RESOLVED.
DIRECT Kaug (RECOMMENDED first scaffold, shortest): `GhostDomState = {cfg, D : Fin levels → ℕ}`;
`augStep z pair = {cfg := scheduledStep NM z.cfg pair, D := updateD z.cfg z.D pair}`;
`Kaug z = if 2≤z.cfg.card then (PMF.map (augStep z) (interactionPMF z.cfg hc)).toMeasure else dirac z`;
`measurable' := Measurable.of_discrete`. CFG MARGINAL `map cfg (Kaug z) = NM.transitionKernel z.cfg` by map_map
(cfg∘augStep = scheduledStep) — SAME proof pattern as `HourCouplingV2.integral_transitionKernel_eq_sum`
(real kernel = `PMF.map scheduledStep interactionPMF` for card≥2, `PMF.pure c` else). No measurability issues
(discrete space; `MeasurableSpace (StepEvent) := ⊤`). ReactionKind = {drip, epidemicSync, atCapCounter,
nonClockOrNonP3}: drip increments s.minute i→i+1 (child threshold i+1 only); epidemicSync sets both to max
(fast-copies-onto-slow, the amplification event); atCap = stdCounterSubroutine (NO minute change, no ghost mass).
NO dripCoin (drip is DETERMINISTIC at p=1; add only for a future p<1 variant). Two-layer Kevent refactor later if
Layer-B gets cluttered by repeated pair classification.
R3 CODING ORDER: (1) ReactionKind + classify + classify_{drip,sync,atCap}_sound (low-risk deterministic);
(2) GhostDomState + updateD_from_pair + Kaug_direct + Kaug_direct_cfg_marginal (axiom-clean marginal FIRST —
this is the highest-risk new object); (3) optional StepEvent/Kevent refactor.

## ROUND 4 — family2 (Layer-D + SyncClockStart + WIRING @04872bc) — RESOLVED.

LAYER D (resolved): FINITE UNION over (level, window-start) pairs — NOT a level-by-level stopping chain
(painful in Lean: optionals/minimality/overlap). `WindowBadMass i s Lwin z₀ = ∫ (if Active63 i z then
(Kaug i)^Lwin z {bad-window} else 0) ∂((Kaug i)^s z₀)`; `WindowBadMass_le ≤ ε_window`; aggregate
`∑_{i∈leadingLevels} ∑_{s∈range(H+1−Lwin)} WindowBadMass ≤ leadingLevels.card·(H+1−Lwin)·ε_window`; +
deterministic certificate `ShapeGoodPath → FrontWidthOK`; then `front_shape_exit_prob ≤ ε_window_total +
ε_ghost_total + ε_sparse_total`. Matches how ClockUnconditional handles side costs (finite prefix sums).

SyncClockStart SATISFIABLE (confirmed): Phase-3 init resets clock minute←0 (`{a with bias:=.zero,
minute:=zeroFinMin}`) ⟹ X_0=1, X_{i>0}=0 = InitialClockTail. My `clockGE3_entry_of_roleSplitGood`
(ClockCapReachable) gives C₀=clockCount, C₀≥n/5, allPhaseGE3. NEED extra deterministic entry lemmas
(`syncClockStart_of_roleSplitGood_phase3Init` from `Phase3InitPost`) for Phase3ClockConfig, InitialClockTail,
D₀=0, noPhaseAbove3, allClocksCounterPos.

⚑ WIRING — IMPEDANCE MISMATCH RESOLVED (the honest path): the front-shape does NOT plug into the FALSE
`FrontSyncConc.hwin_all`/`ClockFrontWidth.hcap_all` (∀c, deterministic, contain AllClockP3 = too strong for
the mixed protocol). THE RIGHT TARGET is `ClockUnconditional.lean`'s SIDE-PREFIX form, which ALREADY conditions
on `Sgood = QbulkSet ∩ HabsGood`, proves q=0 on Sgood, and leaves prefix sums of `Sgoodᶜ` to discharge.
`ClockUnconditional.sidePrefix_le` decomposes `Sgoodᶜ = QmixFail ∪ FloorFail ∪ SyncFail ∪ PhaseGateFail` with
`(realκ^τ) c₀ Sgoodᶜ ≤ εQ + εfloor + εsync + εphase`. My `front_shape_exit_prob` supplies the SyncFail (and
width-related FloorFail) per-τ bounds → `sidePrefixes_from_front_shape` adapter → sum over (i,τ) →
`clock_real_faithful_O_log_n_unconditional` → honest real-clock theorem.
FRONT-SHAPE IS ONE SIDE-PREFIX TERM — the chain ALSO needs QmixFail/FloorFail/PhaseGateFail bounds +
SyncClockStart (HabsDischarge closes card/clockSize/crossedT/allPhaseGE3 deterministically; clockPhase3/
positive-counters need the FrontSync gate + phase side gates). THE HONEST ROUTE:
  SyncClockStart ⇒ front-shape Layer D ⇒ SyncFail/width FloorFail per-τ ⇒ sidePrefix_le ⇒ all side-prefix sums
  ⇒ clock_real_faithful_O_log_n_unconditional ⇒ honest real-clock theorem.   (NOT ⇒ hwin_all — that's false.)

## ROUND 4 — family (CONSTANT VERDICT @04872bc) — RESOLVED. The checkpoint was REAL; the fix works.

PAPER CONSTANTS FAIL: γ(0.9a²+b) = 1.23·(0.9·0.84²+0.11) = 1.23·0.74504 ≈ 0.9164 > 0.9. Coding (0.84,0.11,1.23)
would BREAK the Layer-B contraction. (The plan-first approach caught a fatal error before coding.)

THE FIX — window in CLOCK-PAIR time: W = w·C₀ clock-clock interactions (NOT 0.1n!). C₀=κn, a total interaction
is clock-clock w.p. ≈κ², so total horizon Lwin = W/κ² = wn/κ. (For κ=1/5, w=0.1 ⟹ W=0.02n clock-pair, Lwin=0.5n.)
With W=w·C₀ the κ CANCELS in ALL THREE ingredients:
- parent growth: meanTime ≲ n/(ακ(1−ρ))·log(1/a); Janson λ·meanTime ≤ Lwin=wn/κ ⟹ **λ·log(1/a) ≤ α(1−ρ)w** (κ cancels).
- immigration: per-total-interaction drip ≤ p(κx)², over Lwin=wn/κ ⟹ μ ≤ w·p·C₀·x² ⟹ coefficient **b = w** (κ cancels).
- amplification: per-step rate is **2κY/n** (one fast clock × any clock = 2YC₀ ordered pairs / n(n−1); NOT 2κ²!),
  over Lwin ⟹ **γ = e^{2w}** (κ cancels). [W=0.1n would give γ=e^1≈2.7, fatal; unthinned 2Y/n gives e^5.]

WORKING CONSTANTS — code the SAFER set (w=0.09, more slack than the razor-thin w=0.1):
  **w=9/100, a=213/250=0.852, b=19/200=0.095, γ=6/5=1.2, λ=101/100** ⟹ γ(0.9a²+b)= (6/5)(0.9·0.852²+0.095) =
  350772/390625 = **0.89798 < 0.9** ✓; parent-growth valid: 1.01·log(250/213) < 2(0.9)(0.09)=0.162 ✓.
  (Near-Doty alt w=0.1: a=837/1000,b=21/200,γ=1223/1000 ⟹ 0.89953<0.9, THIN margin.)
CODE RULE: prove a SYMBOLIC `hcontract : γ·((9/10)·a²+b) ≤ 9/10` lemma, instantiate with w=0.09. NEVER hard-code
the paper triple (0.84,0.11,1.23) — it FAILS. For amplification use rate 2κY/n (not 2κ²Y/n).

## ROUND 5 — family2 (ghost exp-MGF + composition consistency @185fb6d) — RESOLVED.

GHOST EPIDEMIC RATE: clock-thinned `qepi(z) ≤ 2D(C₀−D)/(n(n−1)) ≈ 2κD/n` (NOT 2D/n). Keep exact finite-n form
in Lean. Immigration `qimm(z) ≤ 1_{X_i<ε}·p·(C₀/n)²·X_i²` (the (C₀/n)²=κ² clock-pair factor; absorb into p if route did).

GHOST CONCENTRATION (resolved — NEW lemma, partial reuse): D_i has POSITIVE drift ⟹ `AzumaKernel.expSupermartingale_drift`
does NOT fit directly (it needs ∫Φ≤Φ, gives a weak Hoeffding `t·c²` exponent; GhostSmall needs a Poisson/Chernoff
MEAN-sensitive exponent). REUSE the stopped-kernel piecewise pattern from `Lemma610StoppedAzuma` + the
`AzumaKernel.azuma_exp_tail` geometric-drift-tail STYLE, but prove a NEW predictable-log-MGF drift:
  Ψ(z)=exp(λ·D_i(z) − B(z)); compensator step `bλ(z)=log(1+qimm(e^λ−1))+log(1+qepi(e^λ−1))`, B accumulates as a
  state field; `ghost_exp_drift : ∫ Ψ d(KghostStar i z) ≤ Ψ z` (multiplicative rate 1). λ=(1/100)log n,
  R=ηC₀=κn^{0.15}, μ=O(n^{0.1}polylog) ⟹ tail `exp(−Ω(n^{0.15}log n)) ≤ n^{−A}`. Keep λ symbolic; numeric lemma
  `hcomp : B_H λ ≤ (λ/2)·ηC₀`, discharge with λ=log n/100 later.

GHOST NEGLIGIBILITY (clean): `lemma65_clean_step_from_ghost`: 0.9p·X²+D/C₀ ≤ p·X² ⟺ D/C₀ ≤ 0.1p·X². With η=n^{−0.85},
X≥n^{−0.4}: n^{−0.85} ≤ 0.1p·n^{−0.8} ⟺ n^{−0.05} ≤ p/10 ⟺ **n ≥ (10/p)²⁰** (=10²⁰ for p=1; huge but harmless).

SPARSE-PIONEER (my seed lemma = the one-step; NEW chain wrapper): `sparse_seed_step_bound` (rBeyond_seed_le_rBeyondSq
+ X_i<n^{−0.4} ⟹ K c {seed} ≤ n^{−0.8}) is REUSED. But the BAD EVENT is a CHAIN of sparse pioneer drips of length
r=frontWidthBound n=Θ(log log n): `sparse_chain_whp` — P[one fixed chain] ≤ (n^{−0.8})^r, #choices ≤ H·cap^r·H^r ⟹
total n^{−Ω(log log n)} = n^{−ω(1)}. This chain-length union is NEW Layer-C (not present). [Note clock-pair: rBeyond/n=κX_i,
so the seed bound is κ²n^{−0.8} — cruder n^{−0.8} is safe.]

REGIME THRESHOLDS (complete, no gap; use ≤): bulk ρ≤X, mesoscopic ε_clean≤X≤ρ, sparse X<ε_clean. ρ=0.1,
ε_clean=n^{−0.4}, ε=n^{−0.45} (ghost trigger), η=n^{−0.85}. The band n^{−0.45}≤X<n^{−0.4} = sparse-but-NON-ghost-
triggering (1_{X<ε} off there) — must be EXPLICITLY classified as sparse/SparseNoChain, NOT a gap.

⚠ FrontWidthOK ⇒ FrontSync needs the SHIFTED/CAP-LEVEL form (IMPORTANT): don't state width abstractly. Use
`rBeyond (bulkIdx c + frontWidthBound n) c = 0` AND prove `capMinute ≤ bulkIdx c + frontWidthBound n` (consumes
`rFront_emptied_of_envelope`). Bare frontWidthBound is just a WIDTH, not automatically FrontSync (=rBeyond capMinute=0).

## ROUND 5 — family (ADVERSARIAL RED-TEAM @185fb6d) — VERDICT: directionally right, NOT code-ready.
The audit found 6 REAL holes (the plan-first approach caught them BEFORE coding):

HOLE 1 (BIGGEST) — MIXED vs ALL-CLOCK normalization mismatch. The route uses X_i=rBeyond(i)/C₀ (clock-normalized),
but existing `ClockFrontProfile`/`WidthPrefix`/`ClockFrontSyncFromWidth` use rBeyond/CARD (full-population) AND
assume `AllClockP3 c` (EVERY agent is a phase-3 clock). AllClockP3 is FALSE in the real mixed protocol (Main/Reserve
coexist). `goodFrontWidth_of_windowed_profile_and_climb` even uses AllClockP3 to prove rBeyond 0 = card. ⟹ reusing
those bridges unchanged makes the proof INAPPLICABLE or silently an all-clock theorem (not the real protocol).
FIX (do FIRST, before any Layer-B): mixed `ClockFrac T c = rBeyond T c/C₀`, `ClockP3 c = ∀ a∈c, role=clock→phase=3`
(NOT all agents), `ClockGoodFrontWidth W C₀ c = ∀i, 0<rBeyond i→ C₀≤10·rBeyond(i−W)`; redo the deterministic geometry
clock-normalized. WidthPrefix.goodFrontWidth_whp_at's bad event contains `card=n ∧ AllClockP3` → impossible/inapplicable.

HOLE 2 — Active63 contains a FUTURE event (vacuity). v1 Active63 includes `ParentWindowGood` (= X_i(s)≤a·X_i(s+L), a
window/future-good event). If the stopped kernel's active gate contains a future event, it only runs where the desired
behavior is ALREADY assumed ⟹ vacuous. FIX: Active63 = ONLY state-local gates (Phase3Window ∧ ε≤X_i≤ρ ∧ GhostSmall);
ParentWindowGood is a CONCLUSION of the window theorem, NOT a gate.

HOLE 3 — the ghost: `EarlyDripMarked.markedK` ALREADY EXISTS (faithful labeled marked-agent kernel for Doty's
early-drip set, path-dependent, projects EXACTLY to the real chain). A NEW count-only GhostDomState would need a
nontrivial domination theorem (D_i dominates the true marked descendant set) that can easily fail. LOWER-RISK FIX:
use `EarlyDripMarked.markedK` directly (D_i := marked/tainted count at level i), prove GhostSmall on the marked chain,
transfer via `markedK_pow_erase`. DON'T duplicate the ghost machinery.

HOLE 4 — front-shape is NOT the last open piece. `ClockUnconditional` leaves ALL side-prefixes (QmixFail, FloorFail,
SyncFail, PhaseGateFail) UNBOUNDED in the RHS; `sidePrefix_le` is just the union-bound SHELL (conditional on 4 inputs).
- SyncFail: front-shape supplies (modulo Hole 1).
- FloorFail: MISCLASSIFIED as "width-related" — it's a LOWER-bound/bulk-PROGRESS failure (¬ mC/10 ≤ rBeyond(T+1)),
  belongs to the SEED/BULK side, NOT front-width. Separate adapter.
- QmixFail: needs clockPhase3 synchronization (the hard residual).
- PhaseGateFail (MOST important): includes allClocksCounterPos. HabsDischarge has `ClockPhase3_remaining_synchronization`
  = a NAMED UNPROVED obligation (one-step closure of allClocksCounterPos on Q_mix∧allPhaseGE3∧noPhaseAbove3) =
  "exactly the front-shape synchronization fact." Needs `phaseGates_of_prefix_frontSync`.
⟹ Finishing the front-shape will NOT close the clock theorem unless the 4 side-prefix ADAPTERS are added.

HOLE 5 — CIRCULARITY (FrontSync). FrontSync is BOTH the condition keeping the phase-3 window safe AND the event the
front-shape proves. The front-shape proof CANNOT assume FrontSync as a precondition — must be a FIRST-EXIT result:
`Pr[∃ t≤H, ¬FrontSync(t) ∧ bulk_not_near_cap(t)] ≤ ε` (run real kernel WHILE FrontSync∧gates hold; failure = SyncFail/
PhaseGateFail). DON'T prove `∀ reachable c, FrontSync c → ...` then use it for FrontSync (= the old false-∀c). ALSO:
allClocksCounterPos needs PREFIX FrontSync (not endpoint) ⟹ explicit `phaseGates_of_prefix_frontSync (hstart) (hprefix:
∀t≤τ, FrontSync(path t)) : allPhaseGE3 ∧ noPhaseAbove3 ∧ allClocksCounterPos ∧ (∀c'∈support, noPhaseAbove3)`.

HOLE 6 — STALE constant line. The doctrine still has the OLD incorrect `epidemic_amplification: (1+2/n)Y → e^0.2`
alongside the corrected `2κY/n, γ=e^{2w}`. Dangerous inconsistency. FIX: put final constants in a dedicated Lean
theorem `layerB_constants_ok : γ·((9/10)a²+b) ≤ 9/10`, NEVER refer to the stale (1+2/n)^Lwin line.

## PRE-CODING CHECKLIST (R5 verdict — build these NON-probabilistic adapters/decisions FIRST, before Layer-B):
1. MIXED front geometry (replace AllClockP3/card-normalized): `ClockFrac C₀ T c`, `ClockGoodFrontWidth C₀ W c`,
   `clockGoodFrontWidth_of_windowed_profile_and_climb_mixed`. [Hole 1 — biggest]
2. `phaseGates_of_prefix_frontSync` (prefix FrontSync ⟹ the 4 phase gates). [Holes 4,5]
3. The 4 SIDE-PREFIX ADAPTERS: `SyncFail_prefix_from_front_shape`, `PhaseGateFail_prefix_from_prefix_frontSync`,
   `QmixFail_prefix_from_phase_gates`, `FloorFail_prefix_from_seed_or_bulk_progress`. [Hole 4]
4. DECIDE: use `EarlyDripMarked.markedK` (D_i := marked count) instead of a new count-only ghost. [Hole 3]
5. `layerB_constants_ok` dedicated theorem (w=0.09 set); purge the stale (1+2/n) line. [Hole 6]
6. Active63 = state-local gates ONLY (remove ParentWindowGood). [Hole 2]
7. Phrase the front-shape as FIRST-EXIT, not ∀c. [Hole 5]
THEN code Layer A (mixed geometry) → Kaug/marked-ghost → Layer B (symbolic constants) → side-prefix adapters → assembly.

## ROUND 6 — family2 (EarlyDripMarked + adapters @3c8b59e) — big REUSE, clear scope.

GHOST = `EarlyDripMarked.markedK` (Hole 3 fix CONFIRMED — major reuse, NO new ghost kernel, NO domination proof):
- `taintedCount mc = countP (·.2 = true) mc` IS Doty's `|D_{≥T+1}|` DIRECTLY (the marked early-drip descendant count
  for level T: marks agents crossing above T by drip while c_{≥T}<n^{−0.45}, + epidemic-inherited from marked). So
  D_i := taintedCount in `markedK i θn`. NO separate domination proof (it IS the true descendant count).
- `markedK_pow_erase : (markedK^t) mc₀ (eraseConfig⁻¹' A) = (realK^t)(eraseConfig mc₀) A` — marked chain projects
  EXACTLY to real chain at every horizon. Analyze marked events internally, transfer by erasure.
- `tainted_rise_prob_le : P[taintedCount rises] ≤ (count@T/n)² + 2·taintedCount/n` — the two-term ghost rate
  ALREADY PROVEN (early-drip seed + epidemic inheritance). `aboveCount = taintedCount + cleanAbove`, `MarkInv`.
- CAVEAT (Hole 1 again): `tainted_rise_prob_le` assumes `AllClockP3 (eraseConfig mc)`. NEW: clock-filtered
  `clockTaintedCount T mc = countP (role=clock ∧ T+1≤minute ∧ ·.2) mc` or prove marks-that-matter are clock marks.

phaseGates_of_prefix_frontSync = CLEAN deterministic induction (NOT a prob theorem):
- `ClockFrontShape.counterPos_closed_of_frontSync` ALREADY proves: on Q_mix∧allPhaseGE3∧noPhaseAbove3, FrontSync ⟹
  allClocksCounterPos one-step closed (no clock at cap ⟹ stdCounterSubroutine never fires ⟹ counters don't
  decrement). THE key discharge of the named `ClockPhase3_remaining_synchronization` obligation.
- REUSE `HabsDischarge.allPhaseGE3_closed`. NEW small lemma: `noPhaseAbove3_closed_of_frontSync` (not in files).
- Then `phaseGates_of_prefix_frontSync (hstart)(hprefix:∀t≤τ FrontSync) : allPhaseGE3∧noPhaseAbove3∧
  allClocksCounterPos∧(∀c'∈support, noPhaseAbove3)` by path induction.

THE 4 SIDE-PREFIX ADAPTERS (scope clarified):
- SyncFail (=¬FrontSync): direct from front-shape first-exit, MODULO the bulk-near-cap exception (εB bulk-arrival
  term, cf. ClockFrontSyncFromWidth's εB). Endpoint inclusion: {¬FrontSync at τ} ⊆ {first-exit before τ} ∪ {bulk-near-cap}.
- PhaseGateFail: via phaseGates_of_prefix_frontSync (contrapositive: PhaseGateFail(τ) ⟹ ∃t≤τ ¬FrontSync(t)); first-exit adapter.
- QmixFail: card/clockSize/clockPhase3 from phase gates, BUT `crossedT` is a SEPARATE seed/bulk-PROGRESS invariant.
  QmixFail_prefix ≤ phase-gate fail + crossedT fail + start-structure fail.
- FloorFail (¬ mC/10 ≤ rBeyond(T+1)): NOT front-width — a bulk-arrival/seed-floor LOWER bound. Lives in the
  real-clock SEED/BULK machinery (seed: crossedT⟹floor; bulk: floor⟹crossedT+1), NOT ClockUnconditional/EarlyDripMarked/
  front-shape. A SEPARATE adapter/input.

HONEST ROUTE (confirmed): `EarlyDripMarked + mixed front-shape first-exit ⇒ SyncFail/phase-gate prefix bounds ⇒
sidePrefix_le WITH SEPARATE Qmix(crossedT)/Floor adapters ⇒ clock_real_faithful_O_log_n_unconditional`. Front-shape
alone does NOT close it (supplies SyncFail + width pieces only). Do NOT resurrect hwin_all.

REUSE/NEW (R6 family2): REUSE = markedK/taintedCount/markedK_pow_erase/tainted_rise_prob_le (ghost),
counterPos_closed_of_frontSync, allPhaseGE3_closed. NEW = clock-filtered taint (mixed, Hole 1),
noPhaseAbove3_closed_of_frontSync, phaseGates assembly, QmixFail/crossedT split, FloorFail seed/bulk adapter,
first-exit→endpoint adapters (bulk-near-cap εB). ## ROUND 6 — family (MIXED GEOMETRY @3c8b59e) — Layer A = mixed WRAPPER around REUSED arithmetic (NOT a re-proof).

REUSE vs RE-STATE (clear):
- REUSABLE AS-IS (abstract REAL-SEQUENCE arithmetic, denominator-agnostic): `FrontTail.windowed_doubly_exp`,
  `windowed_floor_crossing`, `frontWidthBound`, `front_emptied_at_width`/`frontWidth_loglog`,
  `HabsDischarge.rBeyond_antitone_threshold`, `frontSync_iff_rBeyond_cap_zero`. They don't care card vs C₀.
- RE-STATE (config-facing wrappers, currently card-normalized + AllClockP3 — Hole 1; MECHANICAL card→C₀ swap):
  `ClockFrontProfile.frac`→`ClockFrac C₀`, `WindowedFrontProfile`→`ClockWindowedFrontProfile C₀`, `ClimbBound`→
  `ClockClimbBound C₀`, `GoodFrontWidth`→`ClockGoodFrontWidth C₀`, `goodFrontWidth_of_windowed_profile_and_climb`,
  `WidthPrefix.goodFrontWidth_whp_at`-endpoint bridge, `ClockFrontWidth.rFront_emptied_of_envelope`.
  ⟹ Layer A is NOT a wholesale re-proof of the doubly-exp math — just a mixed wrapper around the reused sequence lemmas.
- DEFS: `ClockP3 c = ∀a∈c, role=clock→phase=3` (strictly weaker than AllClockP3); `ClockFrac C₀ T c = rBeyond T c/C₀`;
  `ClockGoodFrontWidth C₀ W c = ∀i, 0<rBeyond i c → C₀≤10·rBeyond(i−W)c`. Carry `hC₀: clockCount c = C₀`, `0<C₀`.
  `rBeyond_zero_eq_C₀ (hC₀): rBeyond 0 c = C₀` (no ClockP3 needed — every clock minute ≥ 0).

κ SEPARATION (clean): κ lives in the PROBABILISTIC Layer-B rates, NOT the deterministic Layer-A envelope. Envelope is
on X_T=rBeyond/C₀ with X_{T+1}≤X_T²; the seed bound (rBeyond/card)²=κ²X_T² has its κ² cancel over Lwin=wn/κ in
Layer B. DO NOT absorb κ into the envelope f₀.

⚠ CAP-SAFETY CORRECTED (my earlier note was backwards): need the bulk BELOW the top band, NOT near the cap.
`capMinute ≤ bulkIdx+frontWidthBound` is WRONG (that = hour completing, cap legitimately nonempty). The cap-safety
condition is `bulkIdx C₀ cap c + W < capMinute` OR directly `10·rBeyond(capMinute−W) c < C₀`. Then:
`rBeyond_eq_zero_of_clockGoodWidth_of_bulk_below (hgood)(hbulk: 10·rBeyond(i−W)<C₀): rBeyond i c = 0` (same proof as
existing card-version, card→C₀) → `frontSync_of_clockGoodWidth_of_bulk_below` (via frontSync_iff_rBeyond_cap_zero).
Matches the existing bridge: cap-nonemptiness = width-fail ∪ side-fail ∪ bulk-arrival-near-cap. Prefer the direct
`hbulk` form over `bulkIdx` for side-prefix wiring (avoids findGreatest overhead).

## ════ 6-ROUND PLANNING COMPLETE — CODE-READINESS VERDICT ════
The route is fully planned, red-teamed, constant-verified, reuse/new delineated. CROSS-CUTTING THEME (Hole 1): the
existing §6 clock machinery is written for the ALL-CLOCK abstract model (card-normalized + AllClockP3); the
mixed-protocol adaptation (card→C₀, ClockP3) is needed THROUGHOUT but is MECHANICAL restatement reusing the abstract
arithmetic + the proven per-step facts. The hard NEW probabilistic content is: Layer-B forward window transfer (3
ingredients, w=0.09 constants) + the GhostSmall on EarlyDripMarked.markedK + the sparse-chain union + the first-exit
phrasing. The ghost + counter-positivity + the doubly-exp math are REUSED. CODING ORDER (low→high risk):
1. Mixed Layer-A geometry wrappers (A0-A3, mechanical card→C₀) + `layerB_constants_ok` (w=0.09) + `rBeyond_zero_eq_C₀`.
2. `noPhaseAbove3_closed_of_frontSync` + `phaseGates_of_prefix_frontSync` (clean det. induction, reuses counterPos_closed).
3. Clock-filtered taint on EarlyDripMarked.markedK + GhostSmall (predictable-log-MGF, reuses tainted_rise_prob_le).
4. Layer-B forward window transfer (symbolic constants → w=0.09) + Layer-C concentrations (immigration=Bennett,
   amplification=crude MGF, parent-growth=JansonHitting unit milestones) + sparse-chain union.
5. Layer-D first-exit union + the 4 side-prefix adapters (SyncFail/PhaseGateFail front-shape; QmixFail+crossedT;
   FloorFail=separate seed/bulk) → sidePrefix_le → clock_real_faithful_O_log_n_unconditional → honest clock.

## WAVE-2 — FloorFail (ChatGPT @6bd4f80) — mostly REUSE, thin adapter.
FloorFail = {c | ¬ mC/10 ≤ rBeyond(T+1) c} is SEPARATE from front-width (confirms R5) but the seed-floor
PROBABILISTIC ENGINE is ALREADY PROVEN. Reuse map:
- `ClockRealSeed.lean`: `seedLo mC = mC/10`, `seed_drip_floor`, `rSeedPot_contracts_seed` (seed 0→mC/10 drift).
- `ClockKilledMinute.lean`: `SeedPost n mC T c = seedLo mC ≤ rBeyond(T+1)` (= ¬FloorFail!), `clock_killed_seed_stepW`,
  `clock_real_seed_step_gated` ((realκ^tseed)c₀{¬SeedPost} ≤ εesc+εseed).
- `ClockWeakAssembly.clock_real_seed_leg_avg` (averaged seed-leg prefix — THE key reuse for the side-prefix).
- `ClockRealBulk.lean`: QbulkWin=Q_mix∧floor, `clock_real_advance_bulk`; `ClockRealHours.Q_mix_succ_of_post`.
- `not_FloorFail_of_Q_mix_succ`: Q_mix(T+1) ⟹ ¬FloorFail(T) TRIVIAL (crossedT: 0.9mC ≥ mC/10). But Q_mix(T) ⇏
  ¬FloorFail(T) (the seed step). So FloorFail is the seed-leg obligation between Q_mix(T) and QbulkWin(T).
NEW (thin, deterministic adapter only): `FloorFail_at_seed_end_le` (rewrite FloorFail=¬SeedPost + clock_real_seed_leg_avg),
`FloorFail_during_bulk_le_seedFail_plus_QmixPrefix` (floor persistence via `hmono_mix_discharged`), bundled
`FloorFail_prefix_from_seed_or_bulk_progress` → sidePrefix_le's hfloor input.

## CODING STATUS (live):
WAVE 1 (committed, axiom-clean): ClockFrontMixed (Layer-A geometry+constants), PhaseGatesPrefix (phase gates),
  ClockTaintMixed (ghost rate, ClockTaintedRiseSubset isolated).
WAVE 2: GhostSmallConc (committed, axiom-clean — per-level GhostSmall exp-MGF, carries satisfiable hsub/hincr/hqcap).
  FloorFail (mapped — reuse seed engine + thin adapter). Layer-B forward window transfer (ChatGPT draft pending).
  ClockTaintedRiseSubset discharge (pending — connects PhaseGatesPrefix → ClockTaintMixed's hsub).

## Anti-patterns (the campaign's traps)
NO false ∀-universal (the at-cap habs_mix trap, the ∀c Regime Lemma-6.10 trap); the within-envelope maintenance
must be over the REACHABLE/subcritical domain. Early-drip ghost is ESSENTIAL (bare squaring false at tiny tail).
Refutation-check every carried hypothesis FIRST.
