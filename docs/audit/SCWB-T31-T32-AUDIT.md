# Statement audit of SCWB Theorems 3.1 and 3.2 in Lean (2026-11-09)

Verdicts: scwb_theorem_3_1, scwb_theorem_3_2_ctm, scwb_theorem_3_2_of_Θsum faithful with caveats; scwb_theorem_3_2 faithful with material caveats. Confirmed on review: TmOK/CtmOK/SimOK are safety predicates without progress (findings 1, 2); the repair (completion as part of the success event) is in progress. The attribution of the constant `2746` (finding on the time bound) is corrected in the `scwb_theorem_3_2` docstring of release `r2026.11.3`.

# Hostile statement audit: SCWB Theorems 3.1 and 3.2

## Scope checked

I audited a development commit preceding release `r2026.11.3`, with the same statements. I read the theorem bodies, not only their names, including the definitions of `net`, `ctmOf`, `rawLaw`, `initState`, `TmOK`, `SimOK`, both `expTime` definitions, `law`, `ctmTime`, `tlen`, `tmRun`, `encC`, and `cyc`. I also checked the repaired-network paper proof in `docs/audit/FIX3-SCWB-T32.md`, the register-machine note `docs/audit/FIX3-SCWB.md`, and SCWB etr085v2, especially the stochastic-kinetics definition on p. 3, Theorem 3.1 on p. 6, Fig. 3.2 and Theorem 3.2 on pp. 8–9, and Lemmas A.8–A.9 on pp. 15–16.

The paper itself states only big-O constants. The number `2746` is from Ripple's repaired paper-phase Theorem 3.2′, not from the published theorem verbatim.

## Findings

### 1. ERROR — `TmOK` is a safety predicate and can hold vacuously when the required ticks never occur

**Locations:** `Ripple/sCRNUniversality/ClockedCTM/Assembly.lean:72–75`; `Ripple/sCRNUniversality/ClockedCTM/TMtoCTM.lean:390–396, 416–428`.

`CtmOK` and the first conjunct of `TmOK` have the form

```lean
∀ k, ω (k + 1) = some .tick → ...
```

and the final-decoding conjunct of `TmOK` has the same tick antecedent. Therefore every label sequence containing no `tick` satisfies `TmOK` pointwise, regardless of whether any simulated CTM/TM step completes. More generally, a sequence with fewer than the required number of ticks is not rejected merely for failing to complete.

Thus the formal event bounded by `scwb_theorem_3_2_of_Θsum` and `scwb_theorem_3_2` is “no incorrect observed tick,” not “the computation completes and all observed ticks are correct.” The prose saying that “just before tick `4 N` the state encodes” is not a logical consequence of `TmOK` unless existence of that tick is added.

This may well be a null-event issue for the intended network on correct runs, but no theorem in the audited chain proves

```lean
rawLaw ... {ω | ∃ k, ticks k ω = 4 * ctmTime M Lc c t} = 1
```

or the corresponding almost-sure finite hitting-time statement. The repair is to prove tick liveness and use it in the headline theorem, or strengthen `TmOK` with an existence/completion conjunct.

### 2. ERROR — register-machine `SimOK` has the same progress vacuity

**Locations:** `Ripple/sCRNUniversality/RegisterMachine/Clocked/Theorem.lean:54–58, 285–290, 410–429`.

Here

```lean
SimOK ... :=
  ∀ n, K n ω ≤ t → ∃ x c,
    cfgAt M x₀ (K n ω) = some x ∧ Z ... n ω = enc a (x, c)
```

tracks correctness as a function of the number `K n ω` of machine-reaction labels already seen. A path containing only clock labels has `K n ω = 0` forever and can remain an encoding of the initial configuration, so `SimOK` holds even when a nonhalting machine never performs its first step. The paper's “simulation of the first `t` RM steps” requires either those steps to occur or the RM to halt earlier.

Again, the expected-occupation bound strongly suggests that nonprogress should be null under the intended dynamics, but the headline theorem does not state or prove the required liveness implication. This is a semantic defect in the advertised theorem, not a defect in the prefix-safety proof `simOK_of_not_mem`.

### 3. GAP — `rawLaw` is not the law of a continuous-time CTMC

**Locations:** `Ripple/sCRNUniversality/Stochastic/MassAction/Weights.lean:15–51`; `Ripple/sCRNUniversality/Stochastic/MassAction/Traj.lean:58–96`; `Ripple/sCRNUniversality/RegisterMachine/Clocked/Occupation.lean:119–125`.

`rawLaw` has type

```lean
Measure ((n : Nat) → Option N.I)
```

and is constructed by Ionescu–Tulcea from `massActionPMF`. It is exactly the embedded reaction-label chain: at a nonterminal state the next enabled reaction is selected in proportion to its propensity; at a terminal state the next label is `none` with probability one. It contains no exponential holding-time random variables and no continuous-time sample path.

The paper's stochastic kinetics is a Markov jump process with both the reaction choice and an exponential holding time of rate equal to total propensity. Ripple's `rawLaw` formalizes only the first marginal. The notes correctly explain the missing bridge by conditional means and Tonelli, but the audited Lean headline theorems do not contain a theorem constructing the holding times or identifying the `expTime` functional with an expectation under that continuous-time law.

Consequently the probability inequalities are genuine jump-chain probability theorems, while the phrase “expected time” still relies on an external semantic identification.

### 4. GAP — the Lean result does not formalize the repair note's claim that explosion is counted as failure

**Locations:** `Ripple/sCRNUniversality/ClockedCTM/Assembly.lean:566–574`; `docs/audit/FIX3-SCWB-T32.md:631–656, 691–696`.

The repair note explicitly says that explosion is counted as failure and does not occur before a correct window reaches its target. The Lean sample space has no explosion time. Its time functional is

```lean
∫⁻ ω, ∑' n,
  if ticks n ω < N then
    ((net.totalPropensity (traj ... n ω) : ℝ≥0∞)⁻¹
  else 0
```

on an infinite embedded-chain sequence.

If a path makes infinitely many reactions before the required tick and the inverse-propensity series converges, this functional records the finite accumulation time; it does not assign failure or infinite completion time. Such behavior is precisely why an explosion predicate matters for a non-mass-conserving bimolecular network. The repaired construction is designed so that explosion cannot precede a target on a correct window, but that fact is not packaged into the Lean success event or a continuous-time liveness theorem.

This gap is coupled to Findings 1–3. A complete paper-faithful statement needs an actual CTMC stopping time `τ_N`, an explosion time `ζ`, and a proof that on the success event `τ_N < ζ`, with explosion included in failure.

### 5. MINOR — `expTime` is not vacuous by being automatically zero or by comparing with `∞`

**Locations:** `Ripple/sCRNUniversality/ClockedCTM/Assembly.lean:566–574, 720–746`; `Ripple/sCRNUniversality/RegisterMachine/Clocked/Theorem.lean:285–300`.

The possible degeneracies do **not** occur in the simple way one might fear:

* in `ℝ≥0∞`, the inverse of zero is `∞`, not zero, so a terminal state encountered before the stopping criterion does not make a summand disappear;
* in the CTM the initialized clock has positive counts of `A*` and one clock molecule, and `ClockAt` gives a nonterminal enabled clock reaction;
* the theorem hypotheses `t ≥ 1`, `Lc ≥ 2`, `δ > 0`, `k > 0` make the displayed right-hand sides finite;
* for the register machine, `expTime = 0` when the initial machine state is already halted because `LiveState` is false, which is the intended convention rather than a vacuity.

Thus the proved ENNReal inequalities are nontrivial occupation bounds. The problem is their interpretation as completion time, not an automatic `0 ≤ ∞` proof.

### 6. MINOR — apart from liveness, the correctness predicates do represent cumulative error, and are stronger than final-state correctness

**Locations:** `Ripple/sCRNUniversality/RegisterMachine/Clocked/Theorem.lean:54–58, 72–151`; `Ripple/sCRNUniversality/ClockedCTM/Assembly.lean:72–75, 496–559`; `Ripple/sCRNUniversality/ClockedCTM/TMtoCTM.lean:416–455`.

On paths that do make progress:

* RM `SimOK` requires an exact encoded machine configuration after **every** jump while `K ≤ t`, not merely a correct output at the end. The only positive-probability logical error is the zero-branch reaction firing on a nonzero register; `Err` detects it, and the additional `Null` event has measure zero.
* CTM `SimOK` requires the appropriate target class immediately before every tick among the first `N`. This is the right cumulative notion for the four-window construction: intermediate states inside a window are intentionally noncanonical, and the error is a tick before the target class has been reached.
* `TmOK` adds the decoded TM configuration at the last required microtick.

So the bounded complement is a cumulative-prefix error event, not merely a one-time marginal error. The defect is the missing assertion that the relevant prefix exists.

### 7. MINOR — Theorem 3.1 has the paper's quantifier order

**Location:** `Ripple/sCRNUniversality/RegisterMachine/Clocked/Theorem.lean:404–429`.

The fixed object is `net M 1`, determined solely by `M`. The theorem then quantifies over `δ`, input registers `y₀`, and `t`, and only afterward chooses the initial accuracy count `a`. Neither the reactions nor their rates depend on `δ`, the input, or `t`. This matches SCWB Theorem 3.1.

The restrictions `δ ≤ 1` and `t ≥ 1` omit only trivial edge cases: for `δ > 1` every probability is already at most `δ`, and `t = 0` requires no simulated step.

### 8. MINOR — the CTM/TM network is also fixed before the run parameters

**Locations:** `Ripple/sCRNUniversality/ClockedCTM/Theorem.lean:227–243`; `Ripple/sCRNUniversality/ClockedCTM/TMtoCTM.lean:468–495, 526–552`.

`net (ctmOf M) L` depends only on the TM and the chosen clock length. Although `Lc` is an explicit argument of the wrapper theorem, it does not enter `ctmOf` or `net`. The initial `#A* = f` may depend on `Lc`/the tape size, and `#A = a f` is selected after `δ`, the input configuration, and `t`. That is the same substantive order as the paper and the repaired note: network first, then space-dependent initial clock scale, then the requested error/input/time and the remaining accuracy count.

At the CTM level `scwb_theorem_3_2_ctm` similarly fixes `C`, `L`, and tape parameter `n` before choosing `f`, then handles every `δ`, initial CTM word and step bound.

### 9. GAP — the literal paper parameters `s_tm` and padding `Δ` are not present in the Lean headline

**Locations:** `Ripple/sCRNUniversality/ClockedCTM/TMtoCTM.lean:468–495, 526–552`; `docs/audit/FIX3-SCWB-T32.md:560–578, 598–623`.

SCWB Theorem 3.2 quantifies over a TM space bound `s_tm` and an independent padding amount `Δ`. The repaired paper proof chooses

```text
Lc = max(2, s_tm + ceil(Δ/2)),
s = 2 Lc,
2 s_tm + Δ ≤ s ≤ 2 s_tm + Δ + 2.
```

The Lean theorem instead takes `Lc` directly and assumes the actual run satisfies

```lean
∀ t' ≤ t, tlen (tmRun M c t').tape ≤ Lc.
```

This is enough to derive the paper form, up to the documented `+2` rounding, but that derivation is not a theorem in the audited file. In particular, `scwb_theorem_3_2` exposes only even CTM tape lengths `s = 2 Lc` and does not literally have the paper's `∀ Δ` quantifier.

This is a wrapper gap, not a counterexample to the core bound.

### 10. MINOR — the space premise is faithful for canonical tapes but slightly stronger for arbitrary `TM.Tape` representations

**Locations:** `Ripple/sCRNUniversality/ClockedCTM/TMtoCTM.lean:48–57, 303–383, 468–475`.

`tlen T` is the stored list length `|left| + 1 + |right|`. For the canonical inputs used in the TM-to-CTM reduction, its running maximum is the visited tape interval and is the appropriate space measure. For an arbitrary user-supplied `TM.Cfg`, redundant explicit blank cells in the lists also count. Thus the theorem's premise can be stronger than an extensional “number of nonblank/visited cells” premise on noncanonical tapes.

This does not affect the standard input encoding but should be stated when advertising the theorem for every `TM.Cfg`.

### 11. MINOR — the machine model is a reasonable normalization, but the normalization itself is not formalized

**Locations:** `Ripple/sCRNUniversality/ClockedCTM/TMtoCTM.lean:8–24, 143–169, 303–317`.

The theorem is for a binary `TM.Machine QM Bool`, requires `M.blank = false`, and treats `M.delta q b = none` as halting. SCWB uses a binary TM with a designated halt state. These presentations are equivalent after the usual normalization, and Ripple's partial transition is actually slightly more general because halting may depend on the scanned bit.

What is absent is a theorem converting an arbitrary paper-style machine with a halt state/another blank convention to this exact `TM.Machine` interface. Therefore “for any TM” should be read modulo this explicit normalization.

### 12. MINOR — after halting, `tmRun` stays put but `ctmTime` deliberately keeps charging canonical halting cycles

**Location:** `Ripple/sCRNUniversality/ClockedCTM/TMtoCTM.lean:302–317, 344–382`.

`tmRun` is constant after `step? = none`, while `stepCost` assigns `2 * Lc` CTM steps to a halted configuration. This is consistent with `ctm_step_halt`: the CTM returns to the same canonical encoding after a `2 Lc` cycle. It can overcount runtime when the TM halts before the requested bound `t`, but only in the safe direction. It does not create an incorrect final configuration.

### 13. ERROR — the `2746` sentence is a false attribution, and the Lean theorem does not prove that constant

**Locations:** `Ripple/sCRNUniversality/ClockedCTM/TMtoCTM.lean:504–552`; `docs/audit/FIX3-SCWB-T32.md:598–623, 656–675`.

There are three distinct statements:

1. **Original SCWB Theorem 3.2:** only
   `O(v (s_tm+Δ)^(7/2) t_tm^(5/2) / (k 3^(2s_tm+Δ) δ^(3/2)))`.
2. **Ripple repaired paper theorem:** the improved explicit bound
   `2746 (3/2)^(l-1) v s^3 t_tm^2 / (k 3^s δ)`.
3. **Lean `scwb_theorem_3_2`:**
   `2880 ... s^2 t^2 (1+(s-1)log 3)/(...)`, then
   `3168 ... s^3 t^2/(...)`.

Accordingly, the docstring phrase “the paper's `2746`” is wrong: `2746` is Ripple's repaired analysis, not a literal constant in SCWB. Moreover the Lean theorem is numerically weaker than the repaired analysis because it uses `Θsum_le_pow` with `90` and the final `1.1s` estimate, yielding `3168`, about 15.4% larger than `2746`.

The Lean result is still asymptotically stronger than the original SCWB theorem in its `t` and `δ` exponents. The error is the exact-constant claim, not the asymptotic theorem.

### 14. MINOR — the physical time scaling `v/k` is correct for the networks actually defined

**Locations:** `Ripple/sCRNUniversality/ClockedCTM/Network.lean:100–132, 243–285`; `Ripple/sCRNUniversality/RegisterMachine/Clocked/Network.lean:83–101, 128–149`; `Ripple/sCRNUniversality/ClockedCTM/Assembly.lean:566–574`.

Both constructions use unit-rate bimolecular reactions with two distinct reactant species. `src1_ne_src2` proves distinctness for the repaired CTM network; the RM reactions are likewise built from distinct species. At physical rate constant `k` and volume `v`, every unit propensity is multiplied by `k/v`, so reaction-choice probabilities are unchanged and holding-time means are multiplied by `v/k`. The headline factor

```lean
ENNReal.ofReal (v / k) * expTime ...
```

therefore has the correct units and scaling.

### 15. MINOR — `initState` is a meaningful canonical initial state, not an arbitrary witness hidden behind an existential

**Location:** `Ripple/sCRNUniversality/ClockedCTM/Run.lean:442–476`.

`initState` explicitly sets the state population, base-3 memory value, threshold, cleanup resources, one clock molecule at the top, `#A = a f`, and `#A* = f`. Theorems `initState_clockAt` and `initState_K1` prove that it satisfies the clock invariant and the first canonical simulation class.

There is no need for this state to be reachable from another state: in an SCRN theorem the initial molecular counts are part of the input. It is both concrete and compatible with the schedule proof.

### 16. MINOR — `rawLaw` uses the actual mass-action reaction-choice probabilities on its support

**Locations:** `Ripple/sCRNUniversality/Stochastic/MassAction/Weights.lean:15–51`; `Ripple/sCRNUniversality/Stochastic/MassAction/Traj.lean:23–58, 68–96`.

`stateStep` contains a sanitizer for impossible labels so that it is a total function. This does not corrupt the stochastic law: at a nonterminal state, `massActionPMF` assigns probability zero to `none` and to disabled labels; at a terminal state it assigns probability one to `none`. Hence on every positive-probability finite prefix, `rawLaw` fires an enabled reaction with exactly the Gillespie reaction-selection probability.

For the RM proof, `Null` explicitly collects zero-probability labels and `law_Null = 0`. The CTM proof works directly with the same PMF. The sanitizer affects only null/off-support sequences.

### 17. MINOR — the repaired CTM network is still the paper's construction in spirit, but it is not Fig. 3.2 literally

**Location:** `Ripple/sCRNUniversality/ClockedCTM/Network.lean:8–47, 53–132, 243–285`; `docs/audit/FIX3-SCWB-T32.md` §3.3.

For `|Q| = q` and Lean clock parameter `L` (paper clock length `l = L + 1`), the defined network has

```text
species:  6 q + L + 16  = 6 q + l + 15,
labels:  29 q + 2 L + 4.
```

The `6q` control/gate species are `S_{q,1}`, `S_{q,2}`, `S_{q,3}`, `R_q`, and the two `U_{q,b}`. The added `R/U` gates and modified memory reactions implement repairs F1–F3, so this is not merely a formal transcription of the drawn network.

Nevertheless the structural content is preserved:

* finitely many species/reactions depending only on the finite machine and clock length;
* four clocked microsteps per CTM operation;
* base-3 unary molecular-count tape encoding;
* the same comparison, shift, cleanup and autocatalytic mechanisms;
* exclusively unit-rate bimolecular reactions with distinct reactants.

Thus “the paper's construction in spirit” is fair; “the network of Fig. 3.2” without the word “repaired” would be false.

### 18. GAP — the paper's finite-density/molecular-count corollary does not transfer to the proved parameter choice

**Location:** `docs/audit/FIX3-SCWB-T32.md:656–688`; compare SCWB pp. 9 and 16.

The repair note itself records that its choice can make `#A` exceed the base-3 memory scale `m`, for `l = 2` by a factor of order `t_ct/(δ s)`. Therefore SCWB's accompanying remark that `m` dominates the total molecular count—and the resulting finite-density interpretation of the speedup—does not follow for the repaired/Lean parameters.

This is not part of the literal probability/time inequality in Theorem 3.2, so it does not invalidate the displayed bound for a given volume `v`. It is, however, a genuine aspect of the paper's physical-complexity discussion that is weaker after the repair and is not recovered by the Lean headline.

### 19. MINOR — `scwb_theorem_3_2_ctm` is a faithful repaired CTM theorem, not by itself the paper's TM theorem

**Location:** `Ripple/sCRNUniversality/ClockedCTM/Theorem.lean:227–243`.

The declaration fixes an arbitrary total CTM `C`, a word of length `n+3`, and a number `t` of CTM steps. It proves the schedule error bound and the occupation-time estimate through `Θsum n`. It contains no TM-to-CTM conversion, no TM space premise and no padding parameter. Those enter only in `TMtoCTM.lean`.

Its name is acceptable as an internal theorem, but its precise external reading is “the repaired bounded CTM simulation underlying SCWB Theorem 3.2.”

## Direct answers to the requested degeneracy checks

* **Can `TmOK` hold trivially?** Yes. Any path with no tick labels satisfies both universal tick implications. This is Finding 1.
* **Can RM `SimOK` hold without doing the requested work?** Yes pointwise: a clock-only path can keep `K = 0` and remain a correct encoding. This is Finding 2.
* **Can `expTime` be automatically zero?** Not in the nonhalted, positive-step CTM case. It is zero after an already halted RM by design.
* **Can `expTime` be infinite in a way that makes the theorem automatic?** No. The right-hand side is finite under the theorem hypotheses, so the proved inequality rules out infinite expectation. At zero propensity the summand is `∞`, not zero. The unresolved issue is that a finite inverse-propensity series on an explosive path is not a completion time.
* **Is the initial state meaningful?** Yes; it is explicit and proved to be the initial canonical class with the clock at the top.
* **Is `rawLaw` the actual CTMC law?** No. It is the exact embedded reaction-label chain. A continuous-time holding-time law is not present in these declarations.

## Verdicts per headline theorem

### `Ripple.sCRNUniversality.RegisterMachine.Clocked.scwb_theorem_3_1`

**Verdict: faithful with caveats.**

The network and quantifier order match SCWB Theorem 3.1; the prefix error event is at least as strong as final correctness; the explicit `6 v t²/(kδ)` bound implies the paper's big-O bound. The caveats are material but repairable: `SimOK` does not assert progress/completion, and `expTime` is an embedded-chain occupation functional rather than a formally constructed CTMC stopping time.

### `Ripple.sCRNUniversality.ClockedCTM.scwb_theorem_3_2_ctm`

**Verdict: faithful with caveats.**

It faithfully formalizes the repaired four-window CTM construction and its `Θsum` error/time analysis. It is not a literal formalization of the broken Fig. 3.2, and it inherits the missing tick-liveness and continuous-time/explosion bridge.

### `Ripple.sCRNUniversality.ClockedCTM.scwb_theorem_3_2_of_Θsum`

**Verdict: faithful with caveats.**

The TM-to-CTM tracking, network independence, actual-space premise, final decoding and exact `Θsum` bound are soundly aligned with the repaired proof. The statement still lacks a literal `s_tm, Δ` wrapper and uses the safety-only `TmOK`; its time is the synthetic occupation functional.

### `Ripple.sCRNUniversality.ClockedCTM.scwb_theorem_3_2`

**Verdict: faithful with material caveats.**

It gives the correct repaired architecture, quantifier order, cumulative prefix error and an improved asymptotic time bound. It is not fully faithful as advertised because (i) the paper's explicit padding parameters are not in the type, (ii) completion/liveness and continuous-time semantics are absent, and (iii) the declaration proves `3168`, not the repaired paper note's `2746`; the original SCWB paper states only big-O. The finite-density corollary also does not transfer with the proved accuracy counts.

Overall: the Lean developments are substantive nonvacuous safety-and-occupation theorems for concrete fixed CRNs. They are not yet complete formal statements of SCWB's continuous-time “completes the computation with cumulative error at most `δ` in expected time” claim. The shortest repair is not to change the network proof: add almost-sure progress/non-explosion-through-completion, construct or connect to exponential holding times, and provide the `s_tm, Δ` wrapper; separately correct the `2746` attribution.
