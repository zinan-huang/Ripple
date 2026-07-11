# Doty Theorem 3.1 — TIME-HALF Scoping Report

Read-only deep scoping pass, 2026-06-06. No edits, no git, no build mutation.
Task: produce the attack plan for the **O(log n) expected/whp stabilization-time**
half of Doty et al. Theorem 3.1 (arXiv:2106.10201v2). The **correctness** half
(`stable_majority_correct`) is reported DONE (0-sorry, faithful). This is the
*separate, currently-unexported* time campaign that `MainTheorem.lean:123–152`
explicitly defers.

---

## 0. HEADLINE FINDINGS (these reframe the campaign)

**F1 — The framework already exists and is the right one.** `PhaseConvergence`
(Probability/PhaseConvergence.lean:63) packages a phase as `(Pre, Post, t : ℕ,
ε : ℝ≥0)` with `convergence : Pre x → (K^t) x {¬Post} ≤ ε`. Here **`t` is
interaction count** (powers of the single-interaction `transitionKernel`), so
**parallel time = t / n**. `compose_n_phases` (PhaseConvergence.lean:142, **0
sorry**) assembles m phases into `(K^(Σtᵢ)) x₀ {¬Post_last} ≤ Σεᵢ` provided the
chaining `Post_i ⇒ Pre_{i+1}` holds. This *is* the union-bound composition the
paper uses, already proven. The time theorem is: **make Σtᵢ = O(n log n)
interactions (= O(log n) parallel time) and Σεᵢ = O(1/n) (or O(1/n²·m)).**

**F2 — The Janson bridge is the correct per-phase engine and is fully built.**
`MilestonePhase` (JansonHitting.lean:40) + `milestone_hitting_time_bound`
(JansonHitting.lean:746, **0 sorry**) gives, for a phase with k milestones each
hit per-step w.p. ≥ pᵢ: `(K^t) c₀ {¬Post} ≤ exp(−pMin·μ·(λ−1−ln λ))` whenever
`t ≥ λ·μ`, where `μ = meanTime = Σ 1/pᵢ`. `MilestonePhase.toPhaseConvergence`
(JansonHitting.lean:826) wraps this into a `PhaseConvergence`. This is the formal
realization of the paper's Theorem 4.3 (Janson) + Corollary 4.4 — the exact tool
§4 says it uses. **This is the per-phase time engine and it is sorry-free.**

**F3 — CRITICAL GAP: the three existing `PhaseConvergence` instances are
O(n log n) PARALLEL time, not O(log n), and are built via the WRONG engine for
the time bound.** All three (`phase3TieConvergence` Phase3Convergence.lean:898,
`phase3LowEpidemicConvergence` Invariants.lean:5620, `phase10EpidemicConvergence`
Invariants.lean:7577) carry `t` with hypothesis
`2·n²·(n−1)·log n < t` — i.e. **t = Θ(n³ log n) interactions ⇒ Θ(n² log n)
parallel time**, with `ε = 1/n²`. They are proven via `measure_potential_ge_one`
(multiplicative drift, GeometricDrift.lean:81), which proves *eventual epidemic
completion* but at a polynomial parallel-time cost. **They are correctness/liveness
witnesses (every laggard eventually advances), NOT the O(log n) time witnesses.**
For the time theorem they must be **replaced or supplemented** by clock-timed
`MilestonePhase` instances whose `t` is `O(n log n)` interactions. This is the
campaign's central technical fact, and it is *not* reflected anywhere in the
current 0-sorry tree (the time theorem was never attempted).

**F4 — Config is variable-size `Multiset Λ`; `n` is `c.card`.** `Config Λ =
Multiset Λ` (Basic/PopulationProtocol.lean:35); `transitionKernel` is the uniform
single-interaction kernel. The faithful regime fixes `L = ⌈log₂ n⌉` and `n`
large. There is **no `expectedHittingTime` defined over ExactMajority's
`Config Λ`** — the SSEM `expectedHittingTime` (SSEM/Probability/ExpectedTime.lean)
is over a *fixed-n vector* `Config Q X n`, a different type. SSEM is a **template,
not a drop-in**.

---

## 1. The exact target theorem statement

The cleanest faithful Lean statement, expressed in the existing framework, is the
**whp form first** (it is what `compose_n_phases` directly yields), then the
**expectation form** as a corollary.

### 1a. whp form (direct output of compose_n_phases)

```
theorem majority_stabilizes_whp (L K n : ℕ) (hL : L = Nat.clog 2 n) (hn : N₀ ≤ n)
    (c₀ : Config (AgentState L K)) (hinit : validInitial c₀) (hcard : c₀.card = n) :
    ∃ C : ℕ,                       -- absolute constant
      ((NonuniformMajority L K).transitionKernel ^ (C * n * (L+1)))
        c₀ {c | ¬ majorityStableEndpoint c₀ c} ≤ (1 / n : ℝ≥0∞)
```

Read: within `C·n·(L+1)` interactions — i.e. **C·(L+1) = O(log n) parallel
time** — the protocol has reached a stable correct endpoint except with
probability ≤ 1/n. (`Σεᵢ`: 11 phases × O(1/n²) + the Phase-10 backup's
1/n²·Θ(n log n)-parallel contribution ⇒ total O(1/n); see §3.)

### 1b. expectation form (the headline "O(log n) expected time")

```
theorem majority_expected_stabilization_time (…same hyps…) :
    ∃ C : ℝ, 0 < C ∧
      expectedParallelStabTime (NonuniformMajority L K) c₀ majorityStableEndpoint
        ≤ C * (L + 1)
```

This needs an `expectedParallelStabTime` definition over `Config Λ` (does NOT yet
exist — see §6). Standard tail-sum form, divided by n. The bound follows from the
whp form plus the Phase-10 tail: `E[S] ≤ (whp-time) + P[reach Phase 10]·(Phase-10
time) ≤ O(n log n) + (1/n²)·Θ(n² log n) = O(n log n)` interactions = O(log n)
parallel time. The Phase-10 absorbing tail is exactly why the paper needs
`ε = O(1/n²)` per phase, not merely `o(1)`.

### What `stabilization_time` "was meant to say"

`MainTheorem.lean:123–137` describes it as: *expected parallel time =
interactions/n is O(log n)=O(L)*, stated abstractly as "∃ C and a schedule-time
random variable S with E[S] ≤ C·(L+1)". The faithful realization is **1b**, with
`t` in `PhaseConvergence` interpreted as interaction count and parallel time =
`t/n`. No `stabilization_time` def is currently exported.

---

## 2. The 11 phases — per-phase PhaseConvergence audit

Paper §3.2 phase taxonomy (lines 591–789), with timing class and the machinery
each needs. **"Exists" below = a 0-sorry `PhaseConvergence` instance present in
the tree. None of the existing three is at O(log n) parallel time.**

| Phase | Paper role | Timing class | PhaseConvergence instance? | Engine needed for O(log n) |
|---|---|---|---|---|
| **0** | Population splitting (Main/Reserve/Clock roles) | Timed Θ(log n) | **MISSING** (only deterministic role-allocation lemmas in DeterministicChain/PhaseProgress) | **Janson `MilestonePhase`**: split reactions r₁,x→r₁,r₂ give per-step p=Θ(1) once Θ(n) of each role exist ⇒ μ=O(n) interactions ⇒ O(1) parallel… but the *count* concentration (#r ≈ n/2 ± √n) is a Chernoff/Janson bound. Engine: `milestone_hitting_time_bound` + `DiscreteChernoff`. |
| **1** | Integer averaging of biases → 3 consecutive values | Timed Θ(log n) | **MISSING** | Averaging-to-3-consecutive is the [45] result; per-step drift on bias spread. Engine: drift (`Supermartingale`/Azuma Thm 4.2) timed by clock counter. |
| **2** | (Untimed) propagate opinion set, detect single opinion → maybe halt | Untimed (epidemic) | **MISSING** | Epidemic spread O(log n) parallel via `epidemicExpectedTime`+`Epidemic.concentration`. Engine: Janson epidemic. |
| **3** | (Fixed-res clock) cancel+split averaging across L hours | Timed Θ(log n) — the clock core | `phase3TieConvergence` + `phase3LowEpidemicConvergence` **EXIST but at Θ(n²log n) parallel time** | **THE hardest.** Need the drip+epidemic minute clock: O(1) parallel time/hour × L hours = O(log n). Engine: clock concentration (Janson back/front tails) — see §4. |
| **4** | (Untimed) tie detection via |g|<1 ⇒ g=0 | Untimed | **MISSING** (deterministic `phase4_tie_callback` exists for correctness) | Epidemic detection O(log n). |
| **5,6** | Reserve agents sample then fuel splits, pull biased ≤ −l | Timed Θ(log n) | **MISSING** | Reserve sampling = epidemic; splitting = drift. Janson + drift. |
| **7** | 2-apart reactions eliminate minority at −l..−(l+2) | Timed Θ(log n) | **MISSING** | Cancel/consume drift, clock-timed. Drift (Thm 4.2). |
| **8** | Consumption reactions eliminate last minority | Timed Θ(log n) | **MISSING** | Consumption epidemic-style; Janson. |
| **9** | (Untimed) = Phase 2 detection | Untimed | **MISSING** | Epidemic detection O(log n). |
| **10** | (Untimed) slow stable backup, Θ(n log n) parallel time | Untimed backup | `phase10EpidemicConvergence` **EXISTS at Θ(n²log n) parallel** | This phase is *allowed* to be slow; reached w.p. O(1/n²). The existing slow instance is **acceptable here** — multiplied by 1/n² it is negligible. **REUSE.** |

**Summary:** of 11 phases, **exactly one (Phase 10) has a reusable instance**
(slow is fine there). Phase 3 has two instances but **at the wrong time scale**
for the fast path. **The other ~9 phases have NO PhaseConvergence instance at
all** for the time theorem. The deterministic machinery in `Analysis/` proves
*correctness reachability*, not *timed* convergence.

This is a substantially larger build than the correctness half. The honest
assessment: **the time theorem is a genuine multi-round campaign**, dominated by
constructing per-phase `MilestonePhase`/drift instances at O(log n) parallel
time, with Phase 3's clock being the keystone.

---

## 3. Composition: how compose_n_phases assembles the bound

`compose_n_phases` (PhaseConvergence.lean:142, 0-sorry) takes `phases : Fin 11 →
PhaseConvergence K`, a chaining hypothesis
`h_chain : ∀ i (hi : i+1 < 11), ∀ x, (phases i).Post x → (phases (i+1)).Pre x`,
and `(phases 0).Pre x₀`, and concludes
`(K^(Σ tᵢ)) x₀ {¬(phases 10).Post} ≤ Σ εᵢ`.

**Chaining obligations to discharge (10 of them):** for each consecutive pair,
`Post_i ⇒ Pre_{i+1}`. These are *deterministic invariant implications* and are
the natural seam where the existing `Analysis/Invariants.lean` phase-invariant
lemmas plug in. The disjunctive halting (Phases 2/4/9 may stabilize early) is a
wrinkle: the clean encoding is to make every phase's `Post` be
`majorityStableEndpoint c₀ ∨ (entered phase i+1 with invariant Iᵢ₊₁)`, so an
early-halt `Post` trivially implies the next `Pre` (already stable, absorbing).
`post_absorbing` for the stable disjunct reuses the correctness-side absorbing
lemmas (e.g. `Phase3TiePost` absorbing at Phase3Convergence.lean:905).

**Arithmetic that Σtᵢ = O(n log n):** with each timed phase `tᵢ = cᵢ·n·(L+1)`
interactions (clock counts `cᵢ ln n` down, O(1) parallel/tick) and untimed phases
`tᵢ = O(n log n)` interactions (epidemic), `Σ over 11 phases = (Σcᵢ)·n·(L+1) =
C·n·(L+1)`. This is a `Finset.sum` over `Fin 11` of `O(n(L+1))` terms = trivial
`omega`/`Finset.sum_le_card_nsmul` once each `tᵢ` is bounded. **The arithmetic is
easy; producing the 11 `tᵢ` bounds is the work.**

**Σεᵢ = O(1/n):** 11 phases × O(1/n²) = O(1/n²); the Phase-10 term contributes
`P[reach 10]·1 = O(1/n²)`. Total `O(1/n²)` ≤ `1/n`. Clean `Finset.sum` bound.

---

## 4. The single hardest genuinely-new piece

**The Phase-3 fixed-resolution clock at O(1) parallel time per hour** (paper
lines 498–530, §6, Theorem 6.9). Everything else is "epidemic O(log n)" or
"drift timed by a counter", both of which the existing Janson/drift machinery
supplies fairly directly. The clock is the keystone because the entire O(log n)
(vs the naive O(log² n)) speedup *is* the clock, and it is the only place where a
genuinely new probabilistic object — the drip+epidemic minute process with its
**exponentially-decaying back tail and doubly-exponentially-decaying front tail**
(paper footnote 9, lines 645–656) — must be formalized.

### Concrete attack using existing machinery

1. **Minute process model.** Define the clock sub-population's minute as a
   `MilestonePhase` where milestone `m` = "max minute ≥ m". Drip
   `Cᵢ,Cᵢ→Cᵢ,Cᵢ₊₁` gives, once Θ(n) clock agents sit at minute m, per-step
   advance probability p = Θ(1) (pairs of `Cₘ` meet). Epidemic
   `Cⱼ,Cᵢ→Cⱼ,Cⱼ (i<j)` propagates the max minute at rate matching
   `epidemicExpectedTime` (Epidemic.lean) — O(1) parallel time per minute.
2. **Per-hour time = O(1) parallel.** k=45 minutes/hour (p=1 case, paper line
   663) ⇒ hour advance = 45 minute-advances = O(1) parallel. Bound the minute
   advance with `milestone_hitting_time_bound`: μ = Σ 1/pₘ = O(k) per hour,
   λ=2 ⇒ failure exp(−Θ(k·n)) ≤ 1/n² ✓. This directly instantiates the existing
   Janson wrapper.
3. **L hours total.** L = ⌈log₂ n⌉ hours × O(1) parallel/hour = O(log n) parallel
   ✓. Compose the L hour-milestones into one `MilestonePhase` with k_total = kL
   minutes, μ = O(kL) = O(log n) — μ·n = O(n log n) interactions. **This is the
   only place where `meanTime` legitimately equals Θ(log n) rather than Θ(1).**
4. **Coupling clock→hour→exponent.** The `C⌊i/k⌋,Oⱼ→C⌊i/k⌋,O⌊i/k⌋` drag rule
   couples Main `hour` to clock `minute`. The "loose synchronization keeps hour
   and bias relatively close" property (paper line 505, §6) is the hard invariant:
   a **two-sided Azuma** (Supermartingale.lean Thm 4.2, already 0-sorry) on the
   spread between fastest and slowest hour. This is the genuinely new
   supermartingale, but `Supermartingale.lean` supplies the abstract Azuma; the
   work is defining the right potential (hour-spread) and verifying bounded
   differences.

**Why this is the hard one and not "epidemic":** the back/front tail asymmetry of
the drip-clock (footnote 9) is *not* a plain epidemic; it is the power-of-two /
junta-driven clock. The honest path is the **p=1 deterministic-transition variant
with k=45** (paper lines 658–664), which avoids the randomized drip probability
and lets the minute advance be analyzed as a near-deterministic counter with
epidemic catch-up — reducing the clock to (drift counter) + (epidemic), both
covered. **Recommend formalizing the p=1, k=45 clock**, exactly as the paper says
its proofs do.

---

## 5. Round estimate & recommended FIRST executable avenue

**Difficulty:** HIGH — genuine multi-round probabilistic campaign (unlike the
correctness half, which was deterministic reachability). ~9 missing per-phase
instances + the clock keystone + the expectation wrapper. Estimate **8–15 focused
rounds**, front-loaded on infrastructure that amortizes across phases.

**Recommended FIRST avenue (smallest, highest-leverage, de-risks everything):**

> **A0 — A clean `epidemicMilestone` → `PhaseConvergence` adapter at O(log n)
> parallel time for one UNTIMED phase (Phase 2 or Phase 9, the opinion-set
> detection).**

Rationale: (i) untimed epidemic phases are the simplest (single epidemic spread,
no clock, no hour coupling); (ii) it exercises the *entire* pipeline end-to-end
— `MilestonePhase` → `milestone_hitting_time_bound` → `toPhaseConvergence` — at
the **correct O(log n) parallel time scale**, proving the framework delivers the
target time (which the existing Θ(n²log n) instances do NOT demonstrate); (iii)
it produces the reusable epidemic adapter that Phases 2,4,9 (and the catch-up part
of 3,5,6,8) all consume. Concretely: define `milestone m = "≥ (1−2^{−m})·n agents
infected"`, `p m = Θ(1)`, `k = ⌈log₂ n⌉`, then `meanTime = O(log n)`,
`t = 2·meanTime·n = O(n log n)` interactions, `ε = exp(−Θ(log n)) ≤ 1/n²`. All
hypotheses of `milestone_to_phase_convergence` (JansonHitting.lean:800) are then
discharged by `Real.log`/`exp` arithmetic already used in Phase3Convergence.

**Second avenue (A1):** the `compose_n_phases` wiring *skeleton* with all 11 `t`
and `ε` left as opaque `O(n(L+1))` / `O(1/n²)` parameters and the 10 chaining
lemmas stubbed to the existing invariants — this validates the composition
arithmetic (Σtᵢ=O(n log n), Σεᵢ=O(1/n)) independently of any single phase, so the
two work fronts (per-phase instances vs. composition) proceed in parallel.

**Third (A2, the keystone):** the p=1, k=45 Phase-3 clock per §4.

---

## 6. Mathlib / Ripple probability primitives: present vs ABSENT

**No measure-theoretic hard-stop. The genuine absence is a missing *definition*,
not a missing *theorem*.**

**PRESENT (Ripple, 0-sorry):**
- Janson geometric tail: `JansonGeometric.lean` (1931 lines), `milestone_hitting_time_bound`, `janson_exponential_tail_from_mgf`, `milestone_to_phase_convergence`, `MilestonePhase.toPhaseConvergence` (JansonHitting.lean). **= paper Thm 4.3 + Cor 4.4.** ✓
- Epidemic expected time + concentration: `epidemicExpectedTime`, `epidemic_concentration_of_tail_bounds` (Epidemic.lean, EpidemicTime.lean). **= paper Lemma 4.5.** ✓
- Multiplicative-drift Azuma supermartingale: `Supermartingale.lean`, `SupermartingaleHitting.lean`, `measure_potential_ge_one` (GeometricDrift.lean). **= paper Thm 4.2.** ✓
- Phase composition union bound: `compose_two_phases`, `compose_n_phases` (PhaseConvergence.lean). ✓
- Discrete Chernoff: `DiscreteChernoff.lean`. **= paper Thm 4.1.** ✓
- Markov kernel + IsMarkovKernel for `transitionKernel`, `(K^t)` powers, Chapman–Kolmogorov (`Kernel.pow_add_apply_eq_lintegral`). ✓
- SSEM `expectedHittingTime` + `expectedHittingTime_le_window_mul_inv` + parallel-time form (SSEM/Probability/ExpectedTime.lean) — **template only** (wrong Config type).

**PRESENT (Mathlib):** `PMF`, `Kernel`, `IsMarkovKernel`, `MeasureTheory.Martingale`, `lintegral`/`tsum` over `ℝ≥0∞`, `ENNReal.tsum_geometric`, `Real.exp`/`log`. ✓

**ABSENT (must be DEFINED, not proven from scratch):**
1. **`expectedParallelStabTime` over `Config Λ = Multiset Λ`** for ExactMajority's
   variable-n protocol. SSEM has the analogue over `Config Q X n` (fixed-n
   vector); it must be **re-defined / re-derived** for the Multiset config (the
   tail-sum-of-`probNotHitBy` construction transports, but the type differs). This
   is the one real piece of *new API*, not a Mathlib gap — ~1 round of definitional
   work mirroring SSEM/Probability/ExpectedTime.lean.
2. **The p=1, k=45 minute-clock `MilestonePhase` object** (the §4 keystone). Not a
   primitive gap — built from present Janson+epidemic+Azuma — but genuinely new
   modelling.
3. **~9 per-phase `MilestonePhase`/drift instances** at O(log n) parallel time.
   Not absent primitives — absent *instances*.

**Bottom line:** every probabilistic *primitive* the paper invokes (Thms 4.1–4.3,
Cor 4.4, Lemma 4.5, Thm 4.2 Azuma) is **present and 0-sorry** in Ripple. The
campaign is **instantiation + one missing expectation definition + the clock
keystone**, not a hunt for missing measure theory. The hard-stop risk is *low*;
the *volume* of per-phase instantiation is the real cost.

---

## TL;DR for the campaign

1. Target = O(log n) parallel stabilization time, expressed as `(K^(C·n·(L+1)))
   c₀ {¬stable} ≤ 1/n` (whp) + an expectation corollary. Framework =
   `PhaseConvergence` + `compose_n_phases` (both present, 0-sorry).
2. Per-phase engine = `MilestonePhase` + `milestone_hitting_time_bound` (Janson,
   present, 0-sorry) for timed/epidemic phases; Azuma drift for averaging phases.
3. **Key gap:** the 3 existing `PhaseConvergence` instances are Θ(n² log n)
   *parallel* time (drift-via-`measure_potential_ge_one`) — correctness/liveness
   witnesses, **NOT** O(log n) time witnesses. Only Phase 10 (allowed slow) is
   reusable as-is. ~9 phases need new O(log n) instances.
4. Hardest piece = the Phase-3 fixed-resolution drip+epidemic clock (O(1)
   parallel/hour × L hours). Formalize the **p=1, k=45 deterministic variant** to
   reduce it to drift-counter + epidemic, both already supplied.
5. **First move:** A0 — one untimed epidemic phase (Phase 2/9) as a
   `MilestonePhase` at O(log n) parallel time, proving the pipeline hits the target
   scale and yielding the reusable epidemic adapter. Parallel-track A1: the
   `compose_n_phases` skeleton with opaque tᵢ/εᵢ to lock the Σ arithmetic.
6. Only true API absence: an `expectedParallelStabTime` definition over
   `Config Λ = Multiset Λ` (mirror SSEM's, ~1 round). No Mathlib hard-stop.
