# Statement audit of P_EM_paper_thm4_time (2026-11-09)

Verdict: faithful with caveats. One GAP (the paper's displayed scheduler definition states only uniform one-step marginals; Lean uses the standard i.i.d. uniform ordered-pair scheduler, which is the model the paper's proofs use), 15 MINOR confirmations. Headline: `Ripple/PopulationProtocol/SSEM/UpperBound/Thm4Final.lean`.

# Hostile statement audit of `P_EM_paper_thm4_time`

Audit base: a development commit preceding release `r2026.11.3`, with the same statements. I read the headline and target types, the finite-state simulation, the scheduler and hitting-time definitions, the uniform-window composition, the restart argument, the paper's Theorem 4 and model definitions, and the correction records in `FIX2-BURMAN.md` and `OPEN_PROBLEMS.md` §6.1.

1. **GAP — the Lean scheduler is the standard i.i.d. scheduler, while the paper's displayed scheduler definition states only uniform one-time marginals.**  
   **Locations:** `SSEM/Probability/RandomScheduler.lean:27-72, 348-359`; Kanaya et al., §2, pp. 2–3.  
   Lean's `uniformPair` is uniform on the `n(n-1)` **ordered** pairs `(u,v)` with `u ≠ v`, and `nthStepDist` obtains every next pair by a fresh `PMF.bind` against that same distribution. Thus Lean proves the theorem for the usual i.i.d. uniform random scheduler. The paper says that each `Γ_t` is uniform on the ordered interaction set, but its displayed formal definition does not separately state that the variables `Γ_t` are independent. If this is read literally as allowing arbitrary correlations with uniform marginals, Theorem 4 is false: sample one ordered pair `U` uniformly at time zero and set `Γ_t = U` for every `t`. Every `Γ_t` has the required uniform marginal, yet from many configurations only the two agents in `U` ever change, so silence need not be reached. The paper's geometric, Chernoff, and restart calculations plainly use the standard fresh-pair interpretation, and Lean formalizes that intended interpretation. This is therefore a faithfulness caveat in the paper's model wording, not a defect in the Lean theorem.

2. **MINOR — the headline is exactly the time part, not the whole conjunction called “Theorem 4” in prose.**  
   **Locations:** `SSEM/UpperBound/Thm4Final.lean:27-44`; `SSEM/UpperBound/PaperInstance.lean:129-156`; `OPEN_PROBLEMS.md:220-287`.  
   `P_EM_paper_thm4_time` proves
   ```lean
   KanayaThm4TimeExpected 40 208 32 1608 5215 ∧
   KanayaThm4TimeWhp      40 208 32 1608 4172
   ```
   and nothing about correctness or cardinality appears in this type, as the declaration and file both say “time part.” The silent-SSEM theorem and the `O(n)` state bound are separate declarations (`P_EM_paper_fin_solves_silent_SSEM`, `card_PEMPaperFin_le`). Consequently, citing this one theorem alone as the *entire* paper Theorem 4 would be too strong, but citing it as its time component is faithful.

3. **MINOR — the random-scheduler and time units match the intended paper model exactly.**  
   **Locations:** `SSEM/Probability/RandomScheduler.lean:27-72, 348-359`; `SSEM/Probability/ExpectedTime.lean:4494-4537`; `SSEM/UpperBound/PaperInstance.lean:129-149`.  
   The scheduler support has cardinality `n(n-1)` and distinguishes `(u,v)` from `(v,u)`, so it is the ordered initiator/responder model. One Markov step is one interaction. `parallelTime T n` is `T / n`, and the expected target is the expected sequential first-hitting time divided by `n`. The w.h.p. target is stated in interactions as `c₂ n² ⌈log₂ n⌉`, equivalently `c₂ n ⌈log₂ n⌉` parallel time. There is no hidden use of unordered pairs or “rounds” of `n/2` interactions.

4. **MINOR — the theorem proves silence, not merely output stabilization; this is at least as strong as the paper's time conclusion and matches its proof via `S_em`.**  
   **Locations:** `SSEM/Defs/Config.lean:39-59`; `SSEM/Probability/ExpectedTime.lean:4521-4537`; `SSEM/UpperBound/Thm4Assembly.lean:26-82`.  
   `C.isSilent P` means `C.step P u v = C` for every pair of agents. The extra diagonal cases cause no distortion because `Config.step` makes a self-interaction a no-op. The goal is therefore genuine transition-level silence. The paper calls the protocol silent and its Lemma 14 reaches `S_em`; Lean transfers `IsSilentConsensus` to this exact finite-protocol silence predicate. Since silence implies no later output change, this also supplies the stabilization bound claimed in the abstract and theorem, but the formal target itself is the stronger silence time.

5. **MINOR — `probNotHitBy` is the genuine first-hit tail, not endpoint non-membership and not an automatically small quantity.**  
   **Locations:** `SSEM/Probability/ExpectedTime.lean:853-883, 1900-1980`.  
   The Markov chain is lifted with a Boolean flag initialized by `Goal C₀` and thereafter updated by logical OR with `Goal` at the new configuration. `probNotHitBy ... t` is the mass of false-flag states after `t` interactions, hence `P[T > t]`, while `probHitBy ... t` is `P[T ≤ t]`; the two masses sum to one. A path that hits the goal and later leaves it remains counted as hit. This is the correct primitive for the non-absorbing intermediate sets used in the stage composition and for first time to silence.

6. **MINOR — `expectedParallelTimeToSilent` is the standard tail-sum expectation and can be infinite; the asserted bound is not definitional.**  
   **Locations:** `SSEM/Probability/ExpectedTime.lean:2820-2832, 4494-4537`.  
   Lean defines
   ```lean
   expectedHittingTime = ∑' t : ℕ, probNotHitBy ... t
   expectedParallelTime = expectedHittingTime / n
   ```
   in `ENNReal`. This is the standard formula `E[T] = Σ_t P[T>t]` for a nonnegative integer-valued first hitting time, including the value `∞` when the tail is not summable. `expectedParallelTimeToSilent` merely specializes the goal predicate to `isSilent`; it does not truncate, cap, or assign zero to non-hitting paths.

7. **MINOR — the finite state type is a behaviorally exact quotient of the paper's bounded role-dependent state space, not a restriction to states reachable from a canonical initialization.**  
   **Locations:** `SSEM/Convergence/FiniteStatePEM.lean:190-313, 1008-1060`; `SSEM/UpperBound/PaperInstance.lean:76-94`.  
   `PEMFinState` is a disjoint sum by role. It retains exactly the fields read in that role: nonmedian Settled agents store rank/children/leader/answer, the median also stores the bounded timer, Unsettled stores the bounded error counter, and the two Resetting cases store the relevant reset or delay counter. `embPEM` canonicalizes unused fields, `encPEM_embPEM` is the identity, and `transitionPEM_relPEM` plus `transitionPEM_goodPEM` prove that decode–step–encode simulates the flat transition exactly. Every finite configuration has a decoding satisfying `GoodPEM`; no reachability-from-input hypothesis is imposed. Thus the theorem really is “from every configuration” of the paper-sized protocol.

8. **MINOR — using the finite quotient is necessary; the analogous all-configurations statement for the raw unbounded `AgentState` would be false.**  
   **Locations:** `SSEM/Convergence/FiniteStatePEM.lean:222-313, 1018-1056`; `docs/audit/FIX2-BURMAN.md:25-60`.  
   The raw Lean record stores natural-number counters without a type-level upper bound. An arbitrary raw configuration may therefore put an arbitrarily large timer on the median settled agent. Draining that timer alone takes expected parallel time proportional to its initial value, so no uniform `O(n)` bound over all raw configurations is possible. The paper protocol has finite ranges, in particular timer range `0..7(trank+4)`. The quotient is therefore the faithful object for the paper theorem rather than an artificial weakening.

9. **MINOR — the concrete parameters faithfully instantiate the paper's asymptotic constants, with conservative repairs.**  
   **Locations:** `SSEM/UpperBound/PaperInstance.lean:36-91`; `SSEM/UpperBound/Thm4Final.lean:7-42`; `docs/audit/FIX2-BURMAN.md:180-259`.  
   The instance is
   ```text
   trank = 40,
   timer max = 7(40+4) = 308,
   Rmax = ⌈60 ln n⌉,
   Emax = 208 n,
   Dmax = 32 n.
   ```
   `Rmax` is the concrete Burman constant quoted by the paper. The paper leaves `trank` as a sufficiently large constant and `Emax,Dmax` as sufficiently large linear functions; the correction analysis chooses explicit witnesses and repairs the false or vacuous printed intermediate lemmas. This does not weaken Theorem 4. It replaces hidden asymptotic choices by one verified legal instance.

10. **MINOR — the exact numerical conclusion is no weaker than the paper beyond the explicit threshold `n ≥ 1608`.**  
    **Locations:** `SSEM/UpperBound/Thm4Final.lean:34-44`; `SSEM/UpperBound/PaperInstance.lean:129-149`; `docs/audit/FIX2-BURMAN.md:220-259`.  
    Lean proves expected parallel silence time `≤ 5215 n` and failure probability `≤ 1/n` after `4172 n² ⌈log₂ n⌉` interactions. The paper claims only `O(n)` expected and `O(n log n)` w.h.p., with w.h.p. defined as `1-O(1/n)`. Thus the Lean tail is quantitatively stronger. The reviewed paper arithmetic gives `5212.5 n` (hence an integer constant `5213`); Lean uses the slightly more conservative `1043·5 = 5215`. That loses only a constant against the sharpened audit, not against the printed asymptotic theorem. The threshold `1608` makes “sufficiently large `n`” explicit.

11. **MINOR — the hypotheses of `P_EM_paper_window` are satisfiable and invariant.**  
    **Locations:** `SSEM/UpperBound/Thm4Assembly.lean:26-34`; `SSEM/UpperBound/WindowCompose.lean:30-145`; `SSEM/Convergence/FiniteStatePEM.lean:272-313, 980-1018`.  
    `GoodPEM` is the conjunction of the intended upper bounds on timer, resetcount, errorcount, delaytimer, and children. It is not contradictory: every decoded finite state satisfies it. It is preserved by every flat protocol step. The stage theorem therefore composes over a nonempty, step-closed domain rather than an impossible gate.

12. **MINOR — the flat good-state window really transfers to every finite configuration, including configurations that are not endpoints of any paper initialization.**  
    **Locations:** `SSEM/UpperBound/Thm4Assembly.lean:47-82`; `SSEM/Convergence/FiniteStatePEM.lean:1018-1056`.  
    For arbitrary finite `D`, the proof decodes `D` to `embC D`, proves that decoding good, applies the flat uniform window there, and uses the exact chain simulation together with `encC (embC D)=D`. It then enlarges the transferred target from encoded `S_em` to finite `isSilent`. Therefore “non-good starting configurations” do not form an uncovered case: goodness is a property of the canonical flat representative of every finite state.

13. **MINOR — the six-stage composition uses first-hitting-time composition and does not assume that stage endpoints are absorbing or that stage successes are independent.**  
    **Locations:** `SSEM/UpperBound/WindowCompose.lean:110-175, 214-306`; `SSEM/Probability/ExpectedTime.lean` at `probHitBy_add_ge_mul`.  
    Each stage bound is uniform over every good configuration in its source class. `stage_compose` intersects the intermediate hit with the preserved good invariant and invokes `probHitBy_add_ge_mul`, whose suffix starts from the configuration at the first intermediate hit. Multiplying the lower bounds is therefore a conditional Markov argument, not an unjustified product of independent events. The disjunctive branches are handled by uniform bounds on each branch. The final product is checked to exceed `1/5`, and the summed windows are checked to be at most `1043 n²` for `n ≥ 1608`.

14. **MINOR — the restart argument genuinely applies from every configuration after every failed window.**  
    **Locations:** `SSEM/UpperBound/Thm4Assembly.lean:84-146`; `SSEM/Probability/ExpectedTime.lean:2160-2305, 3880-4015, 4494-4518`.  
    The transferred window is uniform over all finite configurations, not only over the original start or over a special good class. Consequently, conditioned on not yet having hit silence, the chain state at a window boundary again has success probability at least `1/5` during the next `1043 n²` interactions. The public restart lemma gives
    ```text
    P[T > rK] ≤ P[T>0] (1-1/5)^r,
    E[T] ≤ K/(1/5).
    ```
    Taking `K=1043n²` yields `E[T]/n ≤ 5215n`. Taking `r=4⌈log₂ n⌉` gives
    ```text
    (4/5)^(4⌈log₂ n⌉)
      = ((4/5)^4)^⌈log₂ n⌉
      ≤ (1/2)^⌈log₂ n⌉
      ≤ 1/n,
    ```
    at horizon `4·1043 n²⌈log₂ n⌉ = 4172 n²⌈log₂ n⌉`. This covers good, non-good, and already-silent starts; the latter simply have first hitting time zero.

15. **MINOR — the theorem and its quantified domain are demonstrably nonempty and axiom-clean in the repository's sense.**  
    **Locations:** `docs/audit/probes/ProbeKanayaThm4.lean:8-27`; the `#print axioms` output of the build.  
    The probe constructs an explicit configuration at `n=1608` and specializes both halves of the theorem to it. The `#print axioms` output records only `propext`, `Classical.choice`, and `Quot.sound` for `P_EM_paper_window`, `P_EM_paper_thm4_time`, and `kanayaThm4Time`; there is no project axiom, `sorry`, or assumption smuggled into the headline.

16. **MINOR — the existential wrapper `KanayaThm4Time` is intentionally less informative than the explicit headline but is not vacuous.**  
    **Locations:** `SSEM/UpperBound/PaperInstance.lean:151-156`; `SSEM/UpperBound/Thm4Assembly.lean:144-147`.  
    The wrapper asks for some natural constants and only separately requires `d ≥ 1` and finite `c₁`; it does not encode the state-count or correctness components. Naturals have no largest element, so choosing `N₀` cannot make its universal tail empty, and the supplied witness is the explicit tuple `(40,208,32,1608,5215,4172)`. For auditing or citation, `P_EM_paper_thm4_time` is the stronger and preferable declaration.

## Verdict

**Faithful with caveats.** Under the standard intended i.i.d. uniform ordered-pair scheduler, the explicit Lean headline faithfully proves the time component of Kanaya et al. Theorem 4 for a concrete repaired paper instance, from every configuration, with a genuine first-silence stopping time and bounds at least as strong as the paper's asymptotic claims. The finite role-indexed state space is an exact behavioral quotient and is necessary to express the paper's bounded state ranges. The only material faithfulness caveat is that the paper's displayed scheduler definition states uniform marginals without explicitly stating independence; Lean chooses the standard i.i.d. interpretation that the paper's own probability calculations require. No vacuity or invalid restart step was found.
