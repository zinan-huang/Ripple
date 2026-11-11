# Ripple

An open, AI-formalized **Lean 4 framework for the mathematics of computing with chemical reaction networks** — from CRN-computable real numbers and their compilation down to large-population protocols, through the stochastic-to-deterministic bridge (Kurtz's mean-field theorem), to two classical Turing-completeness constructions and four population-protocol majority analyses. Everything builds with **zero `sorry`**, **zero named `axiom` declarations** and **no `native_decide`**: every finite computation is checked by the Lean kernel, and `#print axioms` on every headline theorem reports only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

This README describes release **r2026.11.5** (2026-11-11). The Technical Report (`arXiv:2607.13531v2`, 21 July 2026) is a historical snapshot of an earlier tree, and part of what it says about LPP computability was corrected in release r2026.11; see [Publications](#publications) and the [erratum](paper/ERRATA.md). Changes since the report are in [`CHANGELOG.md`](CHANGELOG.md), [`RELEASE_NOTES.md`](RELEASE_NOTES.md) and the [GitHub Releases](https://github.com/zinan-huang/Ripple/releases).

## Where the name comes from

"Ripple" is a mishearing — by an AI. The author said *repo* (short for *repository*) in a voice message; the speech-recognition model heard *ripple*. The transcription stuck as the name — because the underlying research actually did start small and ripple outward.

It began as a homework exercise in Jack Lutz's class at Iowa State: *can you compute rational numbers with a chemical reaction network?* That grew into algebraic numbers, then transcendentals (e, π, the Euler–Mascheroni constant γ, ln 2), then the shape of the whole real-time class, then weaker population-protocol refinements, then — on the other side — stronger infinite-time analogues. Each layer was a new ripple from the same class exercise.

This repository is the Lean 4 counterpart to that trajectory.

## Scope

**The CRN-computability line** — the repository's spine:

1. Huang, Klinge, Lathrop, Li, Lutz — *Real-time computability of real numbers by chemical reaction networks*, Nat. Comput. 2019.
2. Huang, Klinge, Lathrop — *Real-time equivalence of CRNs and analog computers*, DNA 25 (2019).
3. Huang, Huls — *Computing real numbers with large-population protocols having a continuum of equilibria*, DNA 28 (2022).
4. Chen, Huang — *Bounded analog complexity of real numbers* (submitted, 2026).

**Turing-completeness, one theorem on each side of the model ladder:**

5. Bournez, Graça, Pouly — *Polynomial time corresponds to solutions of polynomial ODEs of polynomial length*, J. ACM 2017 (deterministic GPAC/PIVP side).
6. Soloveichik, Cook, Winfree, Bruck — *Computation with finite stochastic chemical reaction networks*, Nat. Comput. 2008 (stochastic side).

**Population-protocol majority — four analyses and protocols:**

7. Angluin, Aspnes, Eisenstat — *A simple population protocol for fast robust approximate majority*, Distributed Computing 2008.
8. Doty, Eftekhari, Gąsieniec, Severson, Uznański, Viglietta — time- and space-optimal stable exact majority, FOCS 2021.
9. Kanaya, Eguchi, Sasada, Ooshita, Inoue — *Time- and space-optimal silent self-stabilizing exact majority in population protocols*, SSS 2025.
10. Burman, Chen, Chen, Doty, Nowak, Severson, Xu — *Time-optimal self-stabilizing leader election in population protocols*, PODC 2021 (source of the Optimal-Silent-SSR ranking subprotocol that (9) composes with).
11. Condon, Hajiaghayi, Kirkpatrick, Mañuch — *Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*, Natural Computing 2020.

**The probabilistic foundation** — the mean-field limit connecting stochastic CRN dynamics (CTMCs) to their deterministic ODE approximations (GPACs):

12. Kurtz — *Solutions of ordinary differential equations as limits of pure jump Markov processes*, J. Appl. Probab. 1970 (convergence in probability).
13. Kurtz — *The relationship between stochastic and deterministic models for chemical reactions*, J. Chem. Phys. 1972 (Chebyshev deviation bound and CLT).
14. Kurtz — *Strong approximation theorems for density dependent Markov chains*, Stochastic Process. Appl. 1978 (a.s. O(log N/√N) rate).
15. Ethier, Kurtz — *Markov Processes: Characterization and Convergence*, Wiley 1986.

**Classical mathematics in service of the number constructions:** van der Poorten's account (1979) of Apéry's ζ(3) recurrences, formalized via an explicit Zeilberger witness; Cassels' elementary descent (1960) for the Catalan equation; Ramanujan's 1914 modular 1/π series, with the surrounding reduction machine-checked (Clausen, Picard–Fuchs, Chowla–Selberg) and the CM evaluation `j((1+√−163)/2) = −640320³` fully verified through the level-41 modular polynomial Φ₄₁. On that evaluation rests the **Chudnovsky formula** for 1/π, proved without hypotheses (`chudnovsky_one_over_pi`): Milla's proof of the main identity, formalized by Xuanji Li in Lean Pool and ported under `Ripple/Number/Milla/` (see [`NOTICE`](NOTICE)), is evaluated at `τ₁₆₃ = (1+√−163)/2`, where the value `s₂(τ₁₆₃) = 77265280/90856689` is derived from Φ₄₁ by a third-order expansion at its node (`s2_heegnerTau163`; notes in [`docs/audit/CHUD-PAPER.md`](docs/audit/CHUD-PAPER.md)). **Ramanujan's 1914 series** for 1/π is likewise proved without hypotheses (`ramanujan_one_over_pi`): its CM evaluation at level 58 (`ramanujanCM58_evaluation`) comes from the degree-29 modular equation of the `Γ₀(2)+` Hauptmodul, certified by the kernel on `Γ₀(58)`, a second-order expansion at the fixed point `i√58/2`, and a level-2 Kummer identity derived from Milla's `E₄` formula and two hypergeometric transformations (notes in [`docs/audit/CHUD-PAPER.md`](docs/audit/CHUD-PAPER.md) §4).

The goal is to treat all of this as one unified, extensible pipeline: a CRN in its mass-action limit is a polynomial ODE system, a population protocol is its finite-N stochastic shadow, and Kurtz's theorem is the verified bridge between them.

## What is formalized (release r2026.11.5)

A prose tour of the current tree follows. The Technical Report documents the older 21 July snapshot and does not cover the `Tri` library, the faithful computability predicates, the LPP compiler in its current form, or bounded compilation.

### The model ladder

The core is one Lean notion of what it means for a bounded CRN/GPAC to *compute* a real number, `CertifiedBoundedTimeComputable` (`Ripple/Core/BoundedTime.lean`): a PIVP whose vector field is a tuple of polynomials with rational coefficients, with a rational initial value, a bounded trajectory and a time modulus. The class predicates follow the papers: `IsCRNComputable` and `IsPolyTimeComputable` are Definitions 2.1 and 2.3 of the bounded analog complexity paper, and `IsRealTimeComputable` (linear modulus) equals the real-time GPAC class of the DNA 25 paper (`isRealTimeComputable_iff_rtgpac`); the real-time class is closed under the field operations (`realtime_field_add`, `_mul`, `_neg`, `_sub`, `_inv`, `_div`).

Around this notion sits the machinery that moves computations along the ladder of models:

- **Bounded compilation** (bounded analog complexity, Construction 3.1 and Theorems 3.3–4.6): a possibly unbounded ℚ-PIVP whose output converges to `α` becomes a bounded one computing `α` through one time change with the joint clock `1 + Σᵢ yᵢ^N` (`bounded_compilation`, `isGPACComputable_iff_isCRNComputable`); blow-up times are computable (`isCRNComputable_blowupTime`), and polynomial time and length give a polynomial modulus (`bounded_compilation_polyTime`). Poly-length computability in the sense of Bournez, Graça and Pouly, for numbers and for functions on compact sets, gives polynomial time for bounded systems (`isPolyTimeComputable_of_isBGPPolyLengthComputable`, `isPolyTimeComputableOn_of_isBGPPolyLengthComputableOn`).
- **Closure under powers** (bounded analog complexity, Theorem 6.1): `α^β` is computable for computable `α > 0` and `β` (`isCRNComputable_rpow`), and polynomial time is preserved (`isPolyTimeComputable_rpow`), with a repaired construction ([`docs/refactor/BAC2-PAPER.md`](docs/refactor/BAC2-PAPER.md) §6).
- **CRN readout** (bounded analog complexity, Section 7): a bounded ℚ-PIVP computing `α > 0` gives a mass-action CRN with zero initial values whose modulus is at most `max(μ(r + k), 0) + (4/α + 4α) r + C` (`crn_of_certified`); polynomial-time GPAC and CRN computation agree for `α > 0` (`isPolyTimeCRNComputable_iff`).
- **The dual-rail compiler** for polynomial dynamics.
- **Large-population protocols** (DNA 28), with the paper's definitions of deterministic and probabilistic LPPs (`IsLPPComputable`, `IsPLPPComputable`, equal by Theorem 17). The main theorem in the GPAC-to-LPP direction, `bounded_crn_is_lpp_computable`, compiles every `α ∈ [0, 1]` computed by a certified PIVP with a CRN decomposition into a deterministic LPP, and with the CRN readout every `IsCRNComputable` number in `[0, 1]` is LPP-computable (`IsCRNComputable.isLPPComputable`); the converse is `lpp_to_gpac`. Unimolecular protocols compute exactly the rationals (`isLPUPComputable_iff_rat`), LPP numbers are closed under products (`lpp_product`), and every algebraic number in `[0, 1]` is LPP-computable (`algebraic_lpp_computable`).

Adding a new number is a plug-in: supply a ℚ-polynomial PIVP, prove boundedness and a convergence modulus, and the pipeline does the rest.

### Computable numbers

The constants e, π, ln 2 and Euler's γ are real-time computable (`euler_is_realtime`, `pi_is_realtime`, `ln2_is_realtime`, `euler_gamma_is_realtime`), as is Catalan's constant G (`catalan_is_realtime`), each through an explicit ℚ-polynomial IVP with a machine-checked convergence bound. π/4, 1/e, ln 2, G, γ and the Dottie number are LPP-computable (`pi_quarter_is_lpp_computable`, `inv_e_is_lpp_computable`, `ln2_is_lpp_computable`, `catalan_is_lpp_computable`, `euler_gamma_is_lpp_computable`, `exists_dottie_lpp`). **Apéry's constant ζ(3) is real-time computable** (`apery_is_realtime`): the five-variable Fermi–Dirac system `fermiPolyPIVP`, with ℚ-polynomial field and rational initial value, computes it with modulus `2r + 6` (`fermi_certifiedBoundedTimeComputable`). A second, *series-encoding* route through the holonomic generating function is built on a formalized Frobenius theory of regular-singular ODEs, together with a formalization-discovered obstruction that delimits where that route works; its real-time statement remains conditional (`apery_real_time_from_adaptation`).

### The stochastic bridge: CTMCs and Kurtz's mean-field theorem

A continuous-time Markov chain theory built from the ground up (none previously existed in Mathlib), through to **Kurtz's law of large numbers** on `[0, T]` (Kurtz 1970, Theorem 3.1) for canonical density-dependent CTMCs (`kurtz_finite_horizon`), with Doob's L² maximal inequality and the quadratic-variation bound proved, for random initial states whose densities converge in probability to `x(0)` as in Kurtz's theorem; its hypotheses are model conditions and regularity of the limit ODE solution. The law of large numbers also holds with an explicit exponential tail, uniform on `[0, T]` (`kurtz_finite_horizon_exp_tail`), and **Kurtz's central limit theorem** (1971) is proved for finite-dimensional distributions (`kurtz_finite_dimensional_clt`: `√N (X_N(t_j) − x(t_j))_j` converges in law to the Gaussian with the linearized mean and covariance). The process-level CLT and the almost-sure O(log N/√N) strong approximation are not formalized (`OPEN_PROBLEMS.md` §6.5). Supporting probability infrastructure — integral Grönwall, Doob's inequality at a random index, Bennett and discrete Freedman inequalities — is general-purpose and reusable by anyone formalizing stochastic kinetics or mean-field limits, whether or not they care about computable numbers.

### Two Turing-completeness theorems

The Bournez–Graça–Pouly side is machine-checked: `bounded_pivp_turing_complete` gives a single rational polynomial ODE with bounded trajectories that simulates a fixed universal (undecidable) machine, read out eventually by threshold. For Soloveichik–Cook–Winfree–Bruck, Theorem 3.1 is proved with the paper's quantifier order (`scwb_theorem_3_1`): for every register machine a network fixed by the machine, run under the jump chain of mass-action kinetics, makes no wrong step among the first `t` machine steps except with probability at most `δ`, with expected time `O(v t²/(k δ))`, for every `δ`, input and `t`, given enough copies of the accuracy species. Theorem 3.2, for Turing machines, is proved in the same form for a repaired version of the paper's Figure 3.2 network, which fails as drawn (`scwb_theorem_3_2`, expected time `O((3/2)^L v s³ t²/(k 3^s δ))`; notes in [`docs/audit/FIX3-SCWB-T32.md`](docs/audit/FIX3-SCWB-T32.md)). Since r2026.11.4 the success events of both theorems include completion of the run (the statement audit [`docs/audit/SCWB-T31-T32-AUDIT.md`](docs/audit/SCWB-T31-T32-AUDIT.md) had found them safety-only), and both theorems also hold on the continuous-time chain with independent exponential holding times (`scwb_theorem_3_1_timed`, `scwb_theorem_3_2_timed`), whose expected elapsed time is the expected sum of mean holding times used in the jump-chain statements. Theorem 4.2 (coverability is decidable) is proved with computable instances (`Decidability.petriCoverabilityDecidable`); Theorem 4.1, simulation of Turing machines over unboundedly many steps and unbounded space, is proved since r2026.11.5 for an explicit network that depends only on the machine ([`docs/audit/FIX3-SCWB-T41.md`](docs/audit/FIX3-SCWB-T41.md); `scwb_theorem_4_1`): for every space bound `s` and `δ ∈ (0, 1]`, the initial count `i₀ ≤ 2s + 4 + 37/√δ` of the accuracy species makes the run fail to encode every configuration of the machine's run with probability at most `1344/(i₀ − 1)² ≤ δ`, for every input of length at most `s`, with an explicit polynomial bound on the expected physical time per simulated step (`OPEN_PROBLEMS.md` §6.2). Bounded-domain extensions of the BGP construction are in preparation.

### Four majority analyses and protocols

The largest pillar of the repository. For the Angluin–Aspnes–Eisenstat 3-state approximate majority protocol, Ripple formalizes the O(n log n) high-probability consensus time for `n ≥ 16` (`convergence_time_high_probability`), not only stable correctness; convergence to the initial majority under a large initial gap is not formalized. For the Doty et al. exact majority protocol: the deterministic stable-correctness chain (`stable_majority_correct`) and the paper's O(log n) state count, on a compact state type with one live Θ(log n) field per role and phase (`Compact.compact_state_count_clog`: at most `73920 (98 ⌈log₂ n⌉ + 102)` states, with stable correctness transported, `Compact.compact_stable_majority_correct`); the O(log n) time bound is not proved. For the Kanaya et al. silent self-stabilizing exact majority protocol: the impossibility of self-stabilization without knowledge of `n` (`impossibility_without_n`), the space lower bound (`space_lower_bound`, Theorem 2), the time lower bound in expectation and with high probability (`time_lower_bound_omega_n_expected`, `time_lower_bound_whp`, Theorem 3), and the qualitative part of Theorem 4, composed with a formalization of the Burman et al. ranking subprotocol: the protocol `P_EM` is silent self-stabilizing exact majority for every `n ≥ 4` (`P_EM_solves_silent_SSEM_linear`), with O(n) states on a finite role-indexed state type (`P_EM_fin_silent_SSEM_states`, at most `394 n` states), also for the papers' parameters (`P_EM_paper_fin_solves_silent_SSEM`, `card_PEMPaperFin_le`). The time upper bound of Theorem 4 is proved for the paper instance (`P_EM_paper_thm4_time`): for `n ≥ 1608` and every configuration, expected parallel time to silence at most `5215 n`, and silence within `4172 n² ⌈log₂ n⌉` interactions except with probability at most `1/n`; the proof includes Burman et al. Lemmas 3.2–3.4 in corrected form (statement audit [`docs/audit/KANAYA-THM4-AUDIT.md`](docs/audit/KANAYA-THM4-AUDIT.md)).

The separate `Tri` library formalizes Condon et al.'s analysis of tri-molecular approximate-majority CRNs. Its paper-facing capstones include the corrected reached-by-deadline entry clause `Tri.Byzantine.theorem4_entry` and the unconditional corrected multi-species consensus theorem `Tri.Multi.theorem5`. The development also proves `Tri.Byzantine.lemma8` for history-dependent Byzantine strategies and `Tri.Multi.lemma12` for the full printed species range, and states Theorem 1(a) with explicit constants (`theorem1a_explicit`: non-consensus mass at most `n^{−γ/200}` after `258 γ n log₂ n` interactions for `n ≥ 2^420`). It records, with an explicit counterexample, that Theorem 4's additional `n^γ` preservation clause is false as printed; see the [English errata and counterexamples](docs/tri/Errata_and_Counterexamples.pdf).

### Gaps exposed by formalization

Machine-checking surfaced genuine gaps in published proofs — in each case the published *theorem* survives, but a proof step or construction does not:

- **LPP compilation (DNA 28).** The published compilation can transiently leave the unit interval, breaking an unstated assumption; the formalized fix inserts a saturating low-pass filter `y' = (x − y)(U − y)`, and the repaired theorem `bounded_crn_is_lpp_computable` has no in-`[0, 1]` hypothesis. (Until `r2026.11` this theorem concluded a predicate that held for every number in `[0, 1]`; see the [erratum](paper/ERRATA.md).)
- **Bounded compilation (DNA 32).** Some steps of the printed proofs of Proposition 3.2 and Theorem 3.4 do not go through as written; for example, eliminating one variable by a time change can reach the blow-up time of another variable at a finite new time (explicit instance in [`docs/refactor/BC.md`](docs/refactor/BC.md), §1.3.3). None of them changes a theorem: the formalization proves Theorems 3.3, 3.4, 4.5 and 4.6 as stated, using one joint time change over all coordinates instead of the iterated one.
- **Turing-machine simulation (SCWB 2008).** The network of Figure 3.2 fails as drawn, even when every microstep finishes before the next clock tick: in microstep 4 the memory count always ends too large by at least 2, the tick's molecule is captured outside microstep 3 with probability at least 2/11 per simulated step, and the microstep-4 species do not determine the digit to remove or the bit to write for a non-normalised machine. Three local repairs restore it, and Theorem 3.2 is proved for the repaired network ([`docs/audit/FIX3-SCWB-T32.md`](docs/audit/FIX3-SCWB-T32.md)).
- **Algebraic numbers in the urn model.** The arbitrary-degree claim silently rests on Catalan's conjecture (Mihăilescu's theorem). Formalizing Cassels' 1960 descent pinned down exactly what the elementary argument gives (a divisibility conclusion: for `x^p = y^q + 1` with primes `p, q ≥ 5`, `q` divides `x`, `cassels_upper_divisor_nat_elementary`) and what it does not (non-existence) — a dependency on a genuinely deep theorem that the informal presentation hides.

### Formalization insights

- **Approximate majority (AAE 2008).** A naive formalization route — bounding the central-region drift via E[1/f'] ≤ (1-δ)/f — turns out to be false (explicit counterexample at n = 4, due to convexity of 1/x). The original paper avoids this pitfall by working with Taylor-series expansions for sufficiently large n. The Lean proof instead follows the product-form supermartingale of AAE's Lemma 4, which the formalization verifies for all n ≥ 1.

Beyond repairs, formalization also *produced* new mathematics: the zero-init non-collapse theorem (`zero_init_no_collapse` in `Ripple/Core/`) — in a bounded, zero-initialized CRN, any species that ever becomes positive stays above some `c > 0` from some time on, so its liminf is positive and it cannot converge to 0, and 0 is not non-trivially computable from zero initialization (`zero_of_limit_is_trivial`) — was conjectured, stated, and proved inside the framework. And the series-encoding recipe applied to Ramanujan's modular 1/π series surfaces a sharp open problem: the series anchor is a fixed point of the drive, so the natural encoding provably does not converge to π exactly.

## How it was built

Essentially all of the Lean was written by AI agents running *publicly available* models (Anthropic's Claude, OpenAI's GPT), orchestrated by standard agentic coding tools, with the human contribution concentrated on choosing the statements, the proof strategies, and the curation. Every AI-proposed proof is compiled and kernel-checked before acceptance: AI proposes, only the Lean kernel certifies. The workflow is reproducible by anyone with the same public toolchain; the [technical report (v2)](https://arxiv.org/abs/2607.13531v2) documents the method used for its July snapshot.

## Trust footprint

Zero `sorry`, zero named `axiom` declarations, and no `native_decide`. `#print axioms` on every headline result reports only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Every finite computation is checked by the Lean kernel; the large kernel-checked certificates are:

| File | Declaration | What the kernel checks |
|---|---|---|
| `Number/Modular/SturmPackedEval.lean` | `packFinal_eq_zero` | `1728^84` times the first 1766 coefficients of the cleared level-41 Φ₄₁ q-expansion, packed into one integer, vanish (about 20 s and 2.5 GB) |
| `Number/Modular/Phi41SymmCheck.lean` | `phi41SparseTerms_rows_eq_swapped_cols` | the 1766 terms of Φ₄₁ are symmetric under `X ↔ Y` (about 11 s and 1 GB) |
| `Number/Modular/ModularPoly41.lean` | `phi41Diag_root`, `phi41DiagCofactor_ne_zero` | `Φ₄₁(j, j)` vanishes at `j = −640320³` with a nonzero cofactor |
| `Number/Modular/Phi41TaylorData.lean` | `phi41Partial00` … `phi41PartialK6` | the partial derivatives of Φ₄₁ up to order three at `(j₀, j₀)`, `j₀ = −640320³`, used for `s₂(τ₁₆₃)` |
| `Number/Modular/Psi29PackedEval.lean` | `p29Final_eq_zero` | the first 3601 coefficients of the cleared weight-480 `Ψ₂₉` form on `Γ₀(58)`, packed into one integer, vanish; with the weighted-sum coefficient bounds `p29W*_le` that fix the packing widths |
| `Number/Modular/R5Data.lean` | `r5Check_eq_true` | the factorization `Ψ₂₉(a + h, a + h) = (h − b) D(h)` with all coefficients of `D` nonpositive, which makes `T₀ = 256·99⁴ − 104` the only root of `Ψ₂₉(X, X)` above `1.1·10¹⁰` |
| `Number/Modular/Psi29TaylorData.lean` | `psi29Partial00` … `psi29_masser_ratio` | the partial derivatives of `Ψ₂₉` up to order two at `(T₀, T₀)`, used for the level-58 CM relation |
| `Number/Modular/SturmCRTBoundCert.lean` | `phi41RowL1Cert_correct`, `phi41TotalL1Cert_correct` | row and total ℓ¹ norms of the Φ₄₁ coefficient matrix used in the height bound |
| `LPP/ExampleGammaCompiled.lean` | jump-code lemmas | the 32 jumps of the compiled Γ population protocol |

`SturmPacked.lean` proves that the packed integers are the Kronecker images of `1728 E₄³`, `1728 Δ`, their `q ↦ q⁴¹` pullbacks and the cleared expansion, and with the coefficient bound `phi41_final_coeff_bound` obtains `phi41Level41FrickeCoefficientCertificate_proof`, the vanishing of the first 1765 coefficients. Half of the 3529 coefficients that the Sturm bound asks for suffice because of the Fricke involution (`Phi41Fricke.lean`, argument in [`docs/refactor/FRICKE.md`](docs/refactor/FRICKE.md)); `Phi41FrickeSturm.lean` concludes that the form vanishes, and the 3529-coefficient statement `phi41Level41SturmCoefficientCertificate_proof` is a corollary.

## What remains open

`OPEN_PROBLEMS.md` tracks the research frontier: the cited-paper results that are not formalized (§6: the Doty et al. stabilization time, Kurtz's process-level CLT and strong approximation), the 1/π fixed-point obstruction and the second-floor (regular-singular arrival) question for series encodings; the [technical report's](https://arxiv.org/abs/2607.13531v2) open-problem sections state the last two precisely.

## Building

```bash
# Prerequisites: elan + Lake (https://leanprover.github.io/)
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get    # pull Mathlib oleans
lake build
```

The default target checks the `Ripple.lean` import closure (600 modules) and all of `Tri`. The exhaustive target, `lake build Ripple`, compiles all 1124 Ripple modules; it is needed for the modules outside the default closure, among them the kernel-checked Φ₄₁ Sturm certificate and the CM-163 evaluation (`Number/Modular/`), the Turing-completeness developments (`BoundedUniversality/`, `sCRNUniversality/`), and `Number/Euler.lean`, `EulerGamma.lean`, `EulerGammaLPP.lean` and `DottieCertified.lean`. A library user who imports one module builds only its dependencies.

Measured for the refactored tree (all Ripple and `Tri` modules, Mathlib from the cache, one CPU node with a 16 GB memory limit): 49.9 minutes with 8 compile threads and 29.2 minutes with 16, with no module more than 3.87 GiB above its import floor and a largest peak of 7.15 GiB.

## Using Ripple

**To check a claim instead of trusting it.** Every headline result is an ordinary Lean theorem; the kernel will tell you exactly what it rests on:

```lean
import Ripple.Number.AperyFermi

#print axioms apery_fermi_is_crn_computable
-- 'apery_fermi_is_crn_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Three standard axioms, nothing else — that check is the whole point of the repository, and it works the same way for any theorem here.

**To use it as a library.** Ripple builds on Mathlib `v4.30.0` (Lean `v4.30.0`); from a project on the same toolchain, add to your `lakefile.toml`:

```toml
[[require]]
name = "Ripple"
git  = "https://github.com/zinan-huang/Ripple"
rev  = "main"
```

The package exposes `Ripple` for the CRN framework and `Tri` for the
tri-molecular approximate-majority formalization. Release `r2026.11` renames
many declarations and modules; [`docs/refactor/RENAMES.tsv`](docs/refactor/RENAMES.tsv)
maps the `r2026.08` names to the new ones, and
[`docs/refactor/STATEMENT-CHANGES.tsv`](docs/refactor/STATEMENT-CHANGES.tsv)
lists the statements that changed with the computability predicates.

**To add your own computable number.** This is the intended extension path, and it is a plug-in: write down a polynomial IVP with rational coefficients and a rational initial value, prove boundedness and a convergence modulus, and package it as a `CertifiedBoundedTimeComputable` (`Ripple/Core/BoundedTime.lean`), the single definition of "computes α". That gives `IsCRNComputable α` (and `IsRealTimeComputable α` with a linear modulus); if `α ∈ [0, 1]` and the system has a CRN decomposition (`PolyCRNDecomposition`), `bounded_crn_is_lpp_computable` gives large-population-protocol computability. If the system is not bounded but its output converges, `bounded_compilation` makes it bounded. `Ripple/Number/CatalanCertified.lean` (a 4-variable IVP, self-contained) is the model to imitate.

**To take pieces.** The probabilistic layers know nothing about CRNs: `CTMC/`, `Kurtz/`, and `Probability/` are a standalone verified toolkit for anyone formalizing continuous-time Markov chains, mean-field limits, or concentration bounds — the parts of this development that did not previously exist in Mathlib.

**Where to start reading.** `Core/PIVP.lean` (the model) → `Core/BoundedTime.lean` (what "computes" means) → one certified number (`Number/CatalanCertified.lean`) → the LPP main theorem (`LPP/BoundedLPP.lean`) → `Kurtz/MeanField.lean` (the stochastic bridge). The [technical report (v2)](https://arxiv.org/abs/2607.13531v2) gives a guided tour of the July 2026 version of this route.

## Structure

```
Ripple/
├── Core/                  GPAC/PIVP, computability predicates, bounded surrogate compilation,
│                          real-time GPAC class, CRN pipeline, zero-init non-collapse
├── DualRail/              dual-rail encoding of polynomial dynamics
├── LPP/                   large-population protocols: definitions, compiler, main theorem, Thm 17
├── Number/                e, π, ln 2, γ, Dottie, Catalan G, ζ(3) (Fermi–Dirac + Apéry series)
│   ├── Frobenius/         regular-singular Frobenius theory; Apéry conifold
│   ├── Hypergeometric/    Clausen, Picard–Fuchs Wronskian, Chowla–Selberg; Ramanujan reduction
│   └── Modular/           modular forms, Φ₄₁, CM-163, j(τ₁₆₃); Ψ₂₉ and the level-58 CM value
├── CTMC/                  DTMC/CTMC, density process, random-index Doob, absorbing states
├── Kurtz/                 Kurtz law of large numbers on [0, T] (with exponential tail), finite-dimensional CLT
├── Probability/           Bennett exponential-moment lemma, discrete Freedman inequality, lazy steps
├── PopulationProtocol/    majority: approximate (AAE), exact (Doty et al.),
│                          self-stabilizing (Kanaya et al.) + Burman ranking subprotocol
├── sCRNUniversality/      stochastic CRNs (SCWB 2008): Theorems 3.1, 3.2 and 4.1 (register and Turing machines, bounded and unbounded space), coverability decidable
├── BoundedUniversality/   GPAC Turing completeness (BGP 2017); bounded extensions in preparation
├── ODE/                   scalar convergence barriers
└── Analysis/              stable Grönwall lemma
```

`Tri/` is a second top-level Lean library for the Condon–Hajiaghayi–
Kirkpatrick–Mañuch tri-molecular approximate-majority analysis;
`docs/tri/` contains its public errata and counterexamples.

`OPEN_PROBLEMS.md` lists the current research frontier; `docs/refactor/` holds the rename map and the paper notes cited from the source.

## Publications

**Technical Report (historical snapshot).** Ho-Lin Chen and Xiang Huang, *Ripple: An Open, AI-Formalized Lean 4 Framework for Computing with CRNs*, exact version [`arXiv:2607.13531v2`](https://arxiv.org/abs/2607.13531v2), revised 21 July 2026; repository copy [`paper/Ripple-DNA32.pdf`](paper/Ripple-DNA32.pdf). It describes the repository as of July 2026 and is not a guide to the current tree: it predates the `Tri` library (`r2026.08`) and everything in `r2026.11`. Version 2 removes an incorrect claim that the Angluin–Aspnes–Eisenstat (2008) approximate-majority proof contains a gap; see [`AAE_ERRATA_STATEMENT.md`](AAE_ERRATA_STATEMENT.md).

**Erratum.** At the v2 snapshot the Lean predicates `IsCRNComputable`, `IsRealTimeComputable` and `IsPolyTimeComputable` held for every real number, and `IsLPPComputable` for every number in `[0, 1]`, so the report's statements about LPP compilation (§3.3, §3.4, §6.1, §8) were not established by the declarations it cites. The report also overstates Kurtz's theorem, the stochastic simulation of Soloveichik et al., the state count of the Doty et al. protocol and the time and space bounds of the Kanaya et al. protocol. [`paper/ERRATA.md`](paper/ERRATA.md) gives the details, the corrected declarations of `r2026.11`, and which of these claims later releases establish (Kurtz's law of large numbers, the Kanaya et al. space and time lower bounds, O(n) state count and time upper bound, Theorems 3.1, 3.2 and 4.1 of Soloveichik et al., the first two with completion since r2026.11.4) and which remain open.

**Other documentation.** [`docs/refactor/`](docs/refactor/) holds the rename maps and the paper proofs cited from the Lean source, and [`docs/audit/`](docs/audit/) further paper notes cited from the source (the CF'24 readout, the Chudnovsky and Ramanujan CM values, SCWB Theorems 3.1 and 3.2, the Burman and Kanaya time-bound proofs) and the statement audits of the Kanaya Theorem 4 time bound and of SCWB Theorems 3.1 and 3.2; [`docs/tri/`](docs/tri/) holds the tri-molecular paper's formalization notes and [errata](docs/tri/Errata_and_Counterexamples.pdf). `WORK_LOG.md`, `CHECKPOINT.md` and `TODO.md` are historical development logs, last updated in May 2026; they are not maintained and do not record later changes.

## References

The full bibliography is in the [technical report (v2)](https://arxiv.org/abs/2607.13531v2). BibTeX for the repository's spine:

```bibtex
@article{HKLLM18,
  author  = {Huang, Xiang and Klinge, Titus H. and Lathrop, James I. and Li, Xiaoyuan and Lutz, Jack H.},
  title   = {Real-time computability of real numbers by chemical reaction networks},
  journal = {Natural Computing},
  volume  = {18},
  pages   = {63--73},
  year    = {2019},
  doi     = {10.1007/s11047-018-9706-x}
}

@inproceedings{HKL19,
  author    = {Huang, Xiang and Klinge, Titus H. and Lathrop, James I.},
  title     = {Real-time equivalence of chemical reaction networks and analog computers},
  booktitle = {DNA Computing and Molecular Programming (DNA 25)},
  series    = {LNCS},
  volume    = {11648},
  pages     = {37--53},
  year      = {2019},
  doi       = {10.1007/978-3-030-26807-7_3}
}

@inproceedings{HH22,
  author    = {Huang, Xiang and Huls, Rachel},
  title     = {Computing real numbers with large-population protocols having a continuum of equilibria},
  booktitle = {DNA Computing and Molecular Programming (DNA 28)},
  series    = {LNCS},
  volume    = {13467},
  pages     = {55--71},
  year      = {2022},
  doi       = {10.1007/978-3-031-13502-6_4}
}

@unpublished{CH26,
  author = {Chen, Ho-Lin and Huang, Xiang},
  title  = {Bounded analog complexity},
  note   = {To appear, DNA 32; arXiv:2607.12234},
  year   = {2026}
}
```

Mean-field limit (Kurtz theorem):

```bibtex
@article{Kurtz70,
  author  = {Kurtz, Thomas G.},
  title   = {Solutions of ordinary differential equations as limits of pure jump {M}arkov processes},
  journal = {Journal of Applied Probability},
  volume  = {7},
  number  = {1},
  pages   = {49--58},
  year    = {1970},
  doi     = {10.2307/3212147}
}

@article{Kurtz72,
  author  = {Kurtz, Thomas G.},
  title   = {The relationship between stochastic and deterministic models for chemical reactions},
  journal = {The Journal of Chemical Physics},
  volume  = {57},
  number  = {7},
  pages   = {2976--2978},
  year    = {1972}
}

@article{Kurtz78,
  author  = {Kurtz, Thomas G.},
  title   = {Strong approximation theorems for density dependent {M}arkov chains},
  journal = {Stochastic Processes and their Applications},
  volume  = {6},
  number  = {3},
  pages   = {223--240},
  year    = {1978}
}

@book{EthierKurtz86,
  author    = {Ethier, Stewart N. and Kurtz, Thomas G.},
  title     = {Markov Processes: Characterization and Convergence},
  publisher = {Wiley},
  year      = {1986},
  edition   = {2nd ed., 2005},
  doi       = {10.1002/9780470316658}
}
```

## Citing

If this formalization is useful in your work, cite the revised technical report:

> Ho-Lin Chen and Xiang Huang. *Ripple: An Open, AI-Formalized Lean 4 Framework for Computing with CRNs*. [arXiv:2607.13531v2](https://arxiv.org/abs/2607.13531v2), 2026.

Please cite v2 rather than v1, and note its [erratum](paper/ERRATA.md) on LPP computability. For results developed from the papers above, cite the relevant source paper as well. The repository itself is a living artifact: cite a release tag (for example `r2026.11`) or a commit hash alongside the report.

## License

Apache-2.0, matching Mathlib. See `LICENSE`.
