# Ripple Release Notes

This file contains long-form, frozen notes for tagged Ripple releases.
Ongoing public-facing changes belong in [`CHANGELOG.md`](CHANGELOG.md);
Technical Report handling, version namespaces, and the release procedure are
defined in [`MAINTENANCE.md`](MAINTENANCE.md).

## r2026.11 — 2026-11-08 (faithful computability predicates, bounded compilation, kernel-only certificates)

This release changes what Ripple's central definitions mean, so it is a
breaking release for code that imports Ripple. It does four things:

1. it restates the computability predicates to match the source papers and
   re-proves the results built on them, which corrects statements of the
   Technical Report (see [`paper/ERRATA.md`](paper/ERRATA.md));
2. it proves the bounded surrogate compilation theorems of the bounded analog
   complexity paper;
3. it removes every `native_decide`, so every finite computation is checked
   by the Lean kernel; and
4. it renames and reorganizes the library and makes a from-scratch build fit
   in 16 GB of memory.

### Faithful computability predicates

In `r2026.08`, `IsCRNComputable`, `IsRealTimeComputable` and
`IsPolyTimeComputable` were defined over a semantic PIVP record whose vector
field was an arbitrary function and whose initial value was an arbitrary
real, so each held for every real number (`realtime_const` proved
`∀ c : ℝ, IsRealTimeComputable c`). `IsLPPComputable` allowed an arbitrary
vector field on the simplex and held for every number in `[0, 1]`. Theorems
whose conclusion was one of these predicates were therefore weaker than
their names, even when their proofs built a genuine construction. The
structure `CertifiedBoundedTimeComputable`, a PIVP with a ℚ-polynomial field
and a ℚ initial value, was already faithful and is unchanged.

In `r2026.11`:

- `IsCRNComputable α` is `∃ d, Nonempty (CertifiedBoundedTimeComputable d α)`
  (Definitions 2.1 and 2.3 of the bounded analog complexity paper), and
  `IsRealTimeComputable` and `IsPolyTimeComputable` bound the modulus of such
  a witness linearly or polynomially. `IsRealTimeComputable` equals the
  real-time GPAC class of the DNA 25 paper (`isRealTimeComputable_iff_rtgpac`,
  against the paper-literal `IsRTGPACComputable`: zero initial values,
  integer coefficients, error at most `2^{-t}` for `t ≥ 1`).
- `IsLPPComputable` and `IsPLPPComputable` are the deterministic and
  probabilistic clauses of Definition 9 of the large-population protocol
  paper: a protocol (a transition function, or rational transition
  probabilities), its balance equation, a rational initial point of the
  simplex, and a marked set whose mass tends to the target.
- The semantic record is renamed `SemanticBTC` and is used only as
  infrastructure.

Every result stated with the old predicates was restated with the new ones
and re-proved, deleted, or replaced; the complete list, with a reason for
each entry, is [`docs/refactor/STATEMENT-CHANGES.tsv`](docs/refactor/STATEMENT-CHANGES.tsv).
The main results now proved for the faithful predicates are:

- closure of the real-time class under the field operations
  (`realtime_field_add`, `_mul`, `_neg`, `_sub`, `_inv`, `_div`) and of the
  CRN-computable class under sums and products;
- `e`, `π`, `ln 2`, Euler's `γ` and Catalan's constant are real-time
  computable, with certified ℚ-polynomial systems (new for `e` and `γ`);
- the [LPP] Main Theorem in both directions: `bounded_crn_is_lpp_computable`
  (a certified computation of `α ∈ [0, 1]` with a CRN decomposition gives a
  deterministic LPP) and `lpp_to_gpac`;
- [LPP] Theorem 17 (`isLPPComputable_iff_isPLPPComputable`), Lemma 10
  (`isLPUPComputable_iff_rat`), Lemma 11 (`lpp_product`), Corollary 18
  (`algebraic_lpp_computable`) and the Corollary 19 numbers `π/4`, `1/e`,
  `ln 2`, Catalan's constant and the Dottie number; Ehrenfest urns as
  protocols.

The LPP compiler (`Ripple/LPP/Compiler.lean`) follows the four stages of the
paper with rational coefficients throughout: the saturating filter that
keeps the output below 1, quadraticization by v-variables, the λ-trick with
balancing dilation, an upper-triangular half-product lift that is formally
conservative, and the PP-to-PLPP construction, with a two-fold replication
to read the output. The steps the paper does not spell out are written in
[`docs/refactor/S1-LPP-PAPER.md`](docs/refactor/S1-LPP-PAPER.md), and the
proof of Theorem 17 for the continuum-of-equilibria definition in
[`docs/refactor/S1-THM17.md`](docs/refactor/S1-THM17.md).

**Migration.** Code that built a `BoundedTimeComputable` from a function
field must now give a `PolyPIVP` (an `MvPolynomial` field over `ℚ` and a
rational initial value). Code that consumed `∃ _ : IsLPPComputable α, True`
now receives `IsLPPComputable α`, a `Prop`.

### Bounded surrogate compilation

`Ripple/Core/SurrogateCompilation.lean` and its companions prove
Construction 3.1, Proposition 3.2, Theorems 3.3 and 3.4, Lemmas 4.1 and 4.3,
and Theorems 4.5 and 4.6 of the bounded analog complexity paper. Instead of
eliminating unbounded variables one at a time, the Lean proof uses one joint
time change `dt/dτ = 1/P(y)` with `P = 1 + Σᵢ yᵢ^N` (`N` even, at least the
degree of the field) and the surrogates `W_a = y^a/P` for `|a| ≤ N`, which all
lie in `[−1, 1]`. The compiled system is again a ℚ-polynomial PIVP with a
rational initial value, and its solution is explicit, so no existence theorem
for the compiled ODE is needed.

- `bounded_compilation`: a ℚ-PIVP whose output converges to `α` gives
  `IsCRNComputable α`; `isGPACComputable_iff_isCRNComputable` states that
  bounded and unbounded GPACs compute the same reals.
- `bounded_compilation_of_blowup` and `isCRNComputable_blowupTime`: a solution
  that blows up at a finite time keeps its output limit, and the blow-up time
  itself is computable.
- `bounded_compilation_polyTime`: polynomial time and arc length give a
  polynomial modulus; the product clock `Πᵢ (1 + yᵢ^N)` gives compiled
  dimension `1 + d(N + 1)`.
- `SurrogateCompilationExamples.lean` instantiates the theorems on unbounded
  inputs (`arctan`, a Gaussian, the pole of `tan`), so their hypotheses are
  satisfiable.

[`docs/refactor/BC.md`](docs/refactor/BC.md) gives the paper proofs and lists
steps of the printed proofs that do not go through as written; none of them
changes a theorem. The release also notes in docstrings that
`bounded_surrogate_strong` and `bounded_surrogate_compilation` in
`BoundedUniversality` are vacuous; a faithful bounded compilation of the BGP
Turing-machine simulation is not formalized.

### Trust footprint

Ripple contains no `sorry`, no `axiom` declaration and no `native_decide`.
`native_decide` had 66 uses in 37 files. The largest was the level-41 Sturm
certificate behind the CM-163 evaluation `j((1+√−163)/2) = −640320³`. It is now
a Kronecker-packed big-integer identity that the kernel evaluates
(`SturmPackedEval`). The Fricke involution then halved it: with the symmetry
of Φ₄₁ (`Phi41SymmCheck`), the cleared form `F` satisfies a transformation law
under `S` (`Phi41Fricke`), each non-identity factor of its norm decays like
`F(τ/41)`, and the level-one Sturm bound already applies after 1765
coefficients instead of 3529 (`levelGamma0_41_sturm_weight_1008_of_S`,
argument in [`docs/refactor/FRICKE.md`](docs/refactor/FRICKE.md)). The kernel
evaluation takes about 20 seconds and 2.5 GB. The 3529-coefficient statements
keep their types. The 26 `native_decide` checks of the compiled Γ protocol
are structural proofs and small kernel decisions. The CRT reconstruction
over 251 primes, including the bounded-residue evaluation added after
`r2026.08`, and the `SturmCRT` target are removed.

File-level `maxHeartbeats` raises and scoped raises above four times the
default are gone. The remaining scoped raises are at most four times the
default, and each records its measured heartbeat count.

### Names and layout

Names now state what a result is. Names that recorded how or when a result
was produced (step numbers, `_v2`, `_unconditional`, `Discharge`,
`Capstone`, ...) are replaced, and `Aprey` is spelled `Apery`. About 2,400
declarations, 610 modules and 120 namespaces of `r2026.08` are renamed;
[`docs/refactor/RENAMES.tsv`](docs/refactor/RENAMES.tsv) maps each one.
`Ripple/PopulationProtocol/Majority/` is flattened into
`Ripple/PopulationProtocol/`, `Ripple.Frobenius` is `Ripple.Number.Frobenius`,
and `Tri.Lazy` is `Ripple.Probability.LazyStep`. Where a conditional and an
unconditional form shared a stem, the plain name is now the unconditional
statement (`bounded_crn_is_lpp_computable`, `Tri.Multi.lemma12`,
`modular_poly_41_vanishes_on_diagonal_cm163`).

255 forwarding wrappers whose statement equals their target and 39
declarations whose statement was `True` are removed, together with modules
that no stated result uses (superseded proof routes of the tri-molecular and
stochastic-CRN formalizations, the `Number.Apery` placeholder, and scratch
files). Five standalone modules that did not compile at `r2026.08` now compile,
so the exhaustive `Ripple` target completes.

### Build

The default Lake target checks the `Ripple.lean` import closure (549
modules) and all of `Tri`; the exhaustive `Ripple` target compiles all 1028
Ripple modules, including the Sturm certificate, the CM-163 evaluation and
the Turing-completeness developments. Twenty-six `import Mathlib` lines are
narrowed, which lowers the import floor of the affected modules from about
6.4 GiB to 1.9–3.5 GiB. Measured on the refactored tree (all Ripple and
`Tri` modules, Mathlib from the cache, one CPU node, 16 GB memory limit): 49.9
minutes with 8 compile threads and 29.2 minutes with 16, no out-of-memory
kill, every probed module within 3.87 GiB of its import floor, and a largest
peak of 7.15 GiB.

The release tree was built on one NERSC Perlmutter CPU node, with Mathlib
from a prebuilt cache and Ripple and `Tri` compiled from scratch with 64
compile threads: `lake build Ripple RippleDefault Tri` completed successfully
(5480 jobs; 1028 Ripple and 447 `Tri` modules) in about 34 minutes of build
time over two 30-minute jobs, the second resuming incrementally, with no
error and no `sorry`. `#print axioms` on 63 headline declarations named in
the erratum and among the new results reports only `propext`, `Classical.choice`
and `Quot.sound`.

### Technical Report status

The Technical Report remains exactly `arXiv:2607.13531v2` (21 July 2026). It
is a historical snapshot, and the README now lists it under Publications.
Its statements about LPP computability in §3.3, §3.4, §6.1 and §8 cite
declarations whose conclusion was the former `IsLPPComputable`; the erratum
[`paper/ERRATA.md`](paper/ERRATA.md) explains what they established and
names the corrected declarations. The erratum also records claims of the
report that the cited declarations do not establish and that this release
does not change: the almost-sure and CLT versions of Kurtz's theorem are
reductions, the unconditional stochastic bound for Soloveichik et al. uses a
per-step error bound of 1, the Doty et al. state bound is O(log⁴ n), and the
Kanaya et al. time upper bound has an unsatisfiable or carried hypothesis.
The README now states these results as they are. The report PDF is
unchanged.

### Known limitations

- `zero_init_no_collapse` concludes a lower bound at arbitrarily late times,
  which excludes convergence to 0; the stronger eventual lower bound is
  proved in the same file but not stated as the headline.
- `apery_fermi_is_crn_computable` states convergence of an explicit bounded
  ℚ-polynomial system to ζ(3) for the semantic record; it is not yet stated as
  `IsCRNComputable`, and real-time computability of ζ(3) is conditional.
- Closure of `IsCRNComputable` under `exp` and `log` (bounded analog
  complexity, Theorem 6.1) is taken as hypotheses in
  `closure_exponentiation_via_exp_log`.
- Some generated-data facts about Φ₄₁ in `ModularPoly41` are proved by
  `decide +kernel` over the generated tables.

## r2026.08 — 2026-08-05 (tri-molecular approximate majority)

This release adds `Tri`, a second Lean library formalizing Condon,
Hajiaghayi, Kirkpatrick, and Mañuch's analysis of tri-molecular
approximate-majority chemical reaction networks.

### Paper-facing results

The new public capstones include:

- `Tri.Byzantine.theorem4_entry`, the fully proved corrected
  reached-by-deadline entry clause of paper Theorem 4;
- `Tri.Multi.theorem5`, the unconditional corrected multi-species consensus
  theorem;
- `Tri.Byzantine.lemma8`, allowing history-dependent Byzantine strategies;
  and
- `Tri.Multi.lemma12_unconditional`, covering the full printed species range
  without the absorption premise used by the older proof route.

The release does not assert Theorem 4's additional claim that relaxed
consensus remains preserved for the following `n^γ` interactions. That clause
is false as printed. The explicit counterexample, the corrected statements,
and the remaining paper errata are published in
[`docs/tri/Errata_and_Counterexamples.pdf`](docs/tri/Errata_and_Counterexamples.pdf);
each entry cites both the printed Natural Computing page and the one-based
Springer PDF page.

### Public curation

The snapshot contains the 474-module active import closure rooted at
`Tri.lean`. Private work logs, model transcripts, task specifications,
scratch files, generated objects, source-paper copies, and six orphaned
experimental modules are absent.

`lakefile.toml` registers the `Ripple.lean` import closure and all of `Tri` as
the default build. Existing users can continue to `import Ripple`; users of
the new formalization can `import Tri`. The exhaustive `lake build Ripple`
target remains available for recompiling every standalone Ripple module,
including the optional compute-from-scratch Sturm/CRT certificates, but their
recorded 32-core cold-build cost of 342m48.341s is no longer imposed on
ordinary users.

### Trust and verification

The `Tri` source contains no `sorry`, `admit`, `unsafe`, custom axiom
declarations, or `native_decide`. Its emitted `#print axioms` checks report
only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. The
repository's pre-existing, explicitly documented `native_decide` uses in the
modular-forms and compiled-constant threads are unchanged.

### Technical Report status

The Technical Report remains exactly `arXiv:2607.13531v2`, dated 21 July
2026. Because the `Tri` library is a substantial later addition, the report is
now labeled as a historical snapshot rather than a complete description of
the live repository.

## v1.0 — 2026-05-08 (Φ₄₁ → CM-163 chain closed)

**0 sorry, 0 named axiom declarations across all six pillars.** `#print axioms` on every headline theorem reports only Lean's three standard axioms.

### Headline

The long-standing `complex_sturm_bound_valence_formula_phi41Level41Cleared`
chain (`Ripple/Number/Modular/ModularPolynomialQExpansion.lean:2751` —
the last open sorry in the Modular pillar) is closed. As a consequence,
the Heegner-class CM evaluation
`j((1 + √-163) / 2) = -640320³` is fully verified in Lean 4 through the
level-41 modular polynomial Φ₄₁.

### What changed

| Commit | Subject |
|---|---|
| `080c9688` | `atkinLehnerInclusion41` — Atkin-Lehner inclusion at level 41 |
| `254deaf2` | `levelOne_cuspForm_eq_zero_of_low_coeffs_vanish` — generic level-1 Sturm bound for arbitrary even k ≥ 4 |
| `e94431d7` | `Phi41ModularFormAssembly.lean` — bundled `phi41Level41ClearedAsModularForm : ModularForm Γ₀(41) 1008` + qExp bridge |
| `eab0efb5` | `Gamma0_41_SturmBound.lean` — partial norm-trick framework |
| `286d65c0` | `phi41Level41SturmBound : 3528 → 3529` (off-by-one fix; classical level-N Sturm at weight 1008 needs 3529 vanishing coefficients, not 3528) |
| `b89c7616` | `levelGamma0_41_sturm_weight_1008` — main Sturm theorem at level 41 weight 1008, via the q-expansion norm bridge `qExp_norm_coeff_zero_of_qExp_coeff_zero` |
| `ec52333d` | `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` — finite recurrence-array zero check via `native_decide` |
| `6bb32ab0` | Cleanup: HANDOFFs archived, CHECKPOINT/TODO/WORK_LOG refreshed |
| `2af6ba47` | Removed 30+ obsolete `LevelOneCuspWeight*.lean` files (~7080 LoC) — superseded by `LevelOneSturmGeneric.lean` |
| `8d008407` | Stale doc reference refresh + CRT-route HANDOFF for future kernel-only replacement |

### Build

```bash
cd projects/Ripple
PATH="$HOME/.elan/bin:$PATH" lake build       # 3695 jobs, ~30-45 min from scratch
```

### Trust footprint (important)

The project has **no `sorry`** and **no named `axiom` declarations**.
`#print axioms` on every headline result reports only Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The only
trust beyond the Lean kernel is `native_decide`, used in finitely many
places to discharge large decidable claims:

- `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` — first 3529
  entries of the Φ₄₁ cleared q-expansion recurrence array are zero
  (added in this release).
- `phi41Diag_root`, `phi41DiagCofactor_ne_zero` — root and cofactor
  checks for `evalPhi41Diag` at `j(τ₁₆₃)` (pre-existing).
- `(List.range 83).Forall ...` — level-41 difference table vanishes
  (pre-existing).

`native_decide` compiles the decision procedure to native code and
trusts that the result matches what the Lean kernel would compute. The
mathematical content is unchanged; only the verification path differs
from a strict kernel-only proof.

A kernel-only Chinese-Remainder-Theorem replacement is feasible in
principle (see `HANDOFF/crt_route_replace_native_decide.md` for the
plan) but would require either a tighter problem-specific coefficient
bound or a custom reflection evaluator — both research-grade tasks
beyond v1.0 scope. The structural CRT helpers are already in place in
`ModularPolynomialSturmCertificate.lean`.

### Architecture changes

`Ripple/Number/Modular/` shrank from 60 → 25 files:

- **Removed**: `LevelOneCuspWeight{2,4,8,...,70}.lean` (35 files, ~7080
  LoC) and `LevelOneSmallWeights.lean`. These were per-weight cusp-form
  vanishing proofs that have been replaced by the single uniform
  theorem `levelOne_cuspForm_eq_zero_of_low_coeffs_vanish` parametrised
  by `k mod 12 ∈ {0, 2, 4, 6, 8, 10}` (332 lines).
- **Added**: `LevelOneSturmGeneric.lean`, `Phi41Bridge.lean` (extended),
  `Phi41ModularFormAssembly.lean`, `Gamma0_41_SturmBound.lean`,
  `SturmBoundIndex.lean`.

### Non-goals / future work

- **Kernel-only Φ₄₁ certificate** (replacing `native_decide`): see
  `HANDOFF/crt_route_replace_native_decide.md`.
- **Mathlib upstream of `LevelOneSturmGeneric`**: the generic level-1
  Sturm bound for arbitrary even weight could plausibly be contributed
  to Mathlib's `Mathlib.NumberTheory.ModularForms` namespace.
- **`maxHeartbeats 800000` audit**: scattered through the project; some
  could be returned to the 200000 default.
- **CRN library extraction**: split Ripple into reusable
  `CRN.Core` / `CRN.Number` / `CRN.Modular` packages.

### Historical pillars

- `RTCRN1`, `RTCRN2`, `LPP` (DNA28), `BAC` (DNA32) — formalised in the
  Core, ODE, DualRail, and LPP pillars over earlier sessions.
- `Number/Frobenius` — long-term strategic pillar for periods, special
  constants, and holonomic-series-defined numbers (decided 2026-04-21,
  see `STRATEGY.md`).

### Acknowledgements

This release was assembled with extensive collaboration from external
LLM agents (codex, gpt-5.5 high) for matrix algebra grinds and
norm-trick analysis, and a general-purpose subagent for the generic
level-1 Sturm proof. The architectural choices, off-by-one fix,
docstring discipline, and final assembly were directed from the main
Lean session.
