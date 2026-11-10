# Ripple Release Notes

This file contains long-form, frozen notes for tagged Ripple releases.
Ongoing public-facing changes belong in [`CHANGELOG.md`](CHANGELOG.md);
Technical Report handling, version namespaces, and the release procedure are
defined in [`MAINTENANCE.md`](MAINTENANCE.md).

## r2026.11.3 — 2026-11-09 (Ramanujan's 1914 series without hypotheses, the time bound of Kanaya et al. Theorem 4, SCWB Theorem 3.2)

An incremental release on top of r2026.11.2. `CHANGELOG.md` lists every
change and `docs/refactor/STATEMENT-CHANGES.tsv` the restated and renamed
declarations.

### Ramanujan's 1914 series

`Ripple.Number.Ramanujan1914.ramanujan_one_over_pi` now proves

    1/π = (2√2/9801) Σ_{k ≥ 0} (4k)! / (k!)⁴ · (1103 + 26390 k) / 396^{4k}

with no hypothesis. The missing piece was the CM evaluation at level 58,
`1103 F(99⁻⁴)² + 26390·99⁻⁴·(F²)′(99⁻⁴) = 9801/(2√2π)` with
`F = ₂F₁(1/8, 3/8; 1; ·)` (`Modular.ramanujanCM58_evaluation`). Its proof
follows the pattern of the Chudnovsky proof in r2026.11.2, one level down:

- The Hauptmodul `T` of `Γ₀(2)+` satisfies the degree-29 modular equation
  `Ψ₂₉(T(29τ), T(τ)) = 0` (`Modular.psi29_modular_equation`). The kernel
  checks it as the vanishing of a weight-480 form on `Γ₀(58)`: its first
  3601 coefficients are evaluated exactly and a Sturm bound on `Γ₀(N)`
  (`Modular.gamma0_eq_zero_of_coeff`) finishes the argument.
- The point `i√58/2` is fixed by `z ↦ −29/(2z)`, so `T(i√58/2)` is a root
  of `Ψ₂₉(X, X)`; a kernel-checked sign certificate shows it is the only
  root above `1.1·10¹⁰`, which gives `x₂(i√58/2) = 1/99⁴`
  (`Modular.x2_tau58`). The second-order expansion of
  `Ψ₂₉(T(−29/(2z)), T(z)) ≡ 0` at the fixed point gives the CM relation for
  the derivative (`Modular.ramanujan58_cm_relation`).
- The level-2 Kummer identity `2E₂(2τ) − E₂(τ) = F(x₂(τ))²` near `i√58/2`
  (`Modular.Z_sq_eq_gauss`) connects the modular side with the series. It
  is derived from Milla's `E₄ = ₂F₁(1/12, 5/12; 1; 1/J)⁴` (ported in
  r2026.11.2) and two hypergeometric transformations, a quadratic and a
  cubic one, proved by uniqueness of analytic solutions
  (`Hypergeometric.gauss2F1_quadratic`, `gauss2F1_cubic_pow_four`).

The paper notes are in [`docs/audit/CHUD-PAPER.md`](docs/audit/CHUD-PAPER.md)
§4, and the scripts that produced `Ψ₂₉` and its coefficient data in
`docs/audit/evidence/chud/lvl58/`. The former conditional statement is
`ramanujan_one_over_pi_of_cm58`.

### Kanaya et al. Theorem 4: the time upper bound

`P_EM_paper_thm4_time` proves the time part of Theorem 4 of Kanaya et al.
for the paper instance of P_EM (`trank = 40`, `Rmax = ⌈60 ln n⌉`,
`Emax = 208 n`, `Dmax = 32 n`): for `n ≥ 1608` and every configuration of
the finite instance, the expected parallel time to silence is at most
`5215 n`, and the population is silent within `4172 n² ⌈log₂ n⌉`
interactions except with probability at most `1/n`. Together with the
correctness and O(n)-state results of r2026.11.2
(`P_EM_paper_fin_solves_silent_SSEM`, `card_PEMPaperFin_le`), every part
of Theorem 4 is now proved for this instance.

The proof composes one uniform window, `P[silent within 1043 n²] ≥ 1/5`
from every configuration (`P_EM_paper_window`), out of stage bounds for the
two epochs of the paper's analysis: Burman et al. Lemma 3.3 (dormancy,
`P_EM_paper_dormancy_bound`), stage A from every good configuration
(`stageA`), the leader stages (`stageB1`, `stageB2`, `stageB1Z`), tree
ranking, Burman et al. Lemmas 3.3–3.4 in corrected form (`stageB34`), and
the ranked stages (`stageA'`, `stageB56`, `stageC`, `stageE`). The paper
proofs are [`docs/audit/FIX2-BURMAN.md`](docs/audit/FIX2-BURMAN.md),
[`FIX2-P2.md`](docs/audit/FIX2-P2.md) and
[`FIX2-P3.md`](docs/audit/FIX2-P3.md). A statement audit
([`docs/audit/KANAYA-THM4-AUDIT.md`](docs/audit/KANAYA-THM4-AUDIT.md))
compares the Lean statement with the paper's: it is faithful, under the
standard scheduler that picks an ordered pair of distinct agents uniformly
and independently at each step. The finite instances also satisfy
Definition 1 with probability one (`P_EM_paper_fin_kanayaDefinition1`).

### Soloveichik–Cook–Winfree–Bruck Theorem 3.2

The network of the paper's Figure 3.2, which simulates a Turing machine
through a clocked counter machine (CTM), fails as drawn: we found three
defects, each with a proof. With three local repairs it works, and
`ClockedCTM.scwb_theorem_3_2` proves Theorem 3.2 for the repaired network
in the paper's quantifier order: for a binary Turing machine `M` the network
and the count of `A*` are fixed first; then for every `δ ∈ (0, 1]`, input
and step bound `t` within the tape bound there is a count of the accuracy
species `A` with error at most `δ` and expected time at most
`3168 (3/2)^L v s³ t²/(k 3^s δ)`, where `s` is the CTM tape length. For
comparison, SCWB state only `O(v (s+Δ)^{7/2} t^{5/2}/(k 3^{2s+Δ} δ^{3/2}))`,
and the repaired paper analysis gives `2746 (3/2)^{l−1} v s³ t²/(k 3^s δ)`.
A sharper bound in terms of `Θsum` is `scwb_theorem_3_2_of_Θsum`, and
`Θsum_le_log` gives its asymptotics.
Lemma A.9, the simulation of a Turing machine by a CTM, is proved
(`ctm_tracks`). Paper proofs:
[`docs/audit/FIX3-SCWB-T32.md`](docs/audit/FIX3-SCWB-T32.md).

**Caveat for Theorems 3.1 and 3.2.** A statement audit
([`docs/audit/SCWB-T31-T32-AUDIT.md`](docs/audit/SCWB-T31-T32-AUDIT.md))
found that the success events of `scwb_theorem_3_1` (r2026.11.2) and
`scwb_theorem_3_2` are safety predicates: they say that no wrong step
happens before the target step, not that the target step is reached. The
paper's theorems also assert that the computation completes, so the Lean
statements are weaker than the paper's on this point; adding completion to
the success event is in progress. The audit records two further caveats:
probabilities are those of the jump chain of the mass-action process, and
"expected time" is the expected sum of the mean holding times
`1/(total propensity)` along that chain, which is not yet connected in Lean
to a constructed continuous-time process; and `scwb_theorem_3_2` is stated
for the CTM tape length `s`, without the paper's padding parameters.
Theorem 4.1 remains open.

### Build

The default target checks the `Ripple.lean` import closure (600 modules) and
all of `Tri`; the exhaustive `Ripple` target compiles all 1124 Ripple
modules, including the level-58 and SCWB Theorem 3.2 developments. The
release tree was built on one NERSC Perlmutter CPU node, with Mathlib from a
prebuilt cache and Ripple and `Tri` compiled from scratch with 64 compile
threads: `lake build Ripple RippleDefault Tri` completed successfully (5588
jobs) in about 34 minutes of build time over two jobs, the second resuming
incrementally, with no error and no `sorry`. `#print axioms` on 176
headline declarations reports only `propext`, `Classical.choice` and
`Quot.sound`.

## r2026.11.2 — 2026-11-09 (the Chudnovsky formula without hypotheses, SCWB Theorem 3.1, O(n) states for P_EM)

An incremental release on top of r2026.11.1. `CHANGELOG.md` lists every
change and `docs/refactor/STATEMENT-CHANGES.tsv` the restated, renamed and
deleted declarations.

### The Chudnovsky formula

`Ripple.Number.Chudnovsky1989.chudnovsky_one_over_pi` now proves

    640320^{3/2} / (12π) = Σ_{k ≥ 0} (−1)^k (6k)! / ((3k)! (k!)³) · (13591409 + 545140134 k) / 640320^{3k}

with no hypothesis. The proof combines three pieces:

- Milla's proof of the main identity for `Im τ` large enough, which expresses
  the series through `j(τ)` and `s₂(τ) = (E₄/E₆)(E₂ − 3/(π Im τ))`. Xuanji
  Li formalized it in Lean Pool; it is ported under `Ripple/Number/Milla/`
  with its Apache-2.0 headers kept, and `NOTICE` records the origin and the
  changes (`Milla.hauptformel`).
- The CM value `j(τ₁₆₃) = −640320³` at `τ₁₆₃ = (1 + √−163)/2`, already
  verified through the level-41 modular polynomial `Φ₄₁` (the j-evaluation
  chain described in the Technical Report).
- The new value `s₂(τ₁₆₃) = 77265280/90856689` (`Modular.s2_heegnerTau163`).
  `M(z) = 1 − 41/z` fixes `τ₁₆₃`, so `(j(τ₁₆₃), j(τ₁₆₃))` is a node of the
  curve `Φ₄₁(X, Y) = 0`; expanding `Φ₄₁(j(z), j(M z)) ≡ 0` to third order at
  that point determines `s₂(τ₁₆₃)` from finitely many integer partial
  derivatives of `Φ₄₁`, which the kernel checks (`Modular.Phi41TaylorData`).

The paper notes are in [`docs/audit/CHUD-PAPER.md`](docs/audit/CHUD-PAPER.md).
The former conditional statement is `chudnovsky_one_over_pi_of_cm163`.
Ramanujan's 1914 series (`ramanujan_one_over_pi`) stays conditional on a
true level-58 evaluation that is not proved; a false statement about the
Legendre λ value at `i√58/2`, `RamanujanLambda58Statement`, is deleted with
its consumers.

### Soloveichik–Cook–Winfree–Bruck Theorem 3.1

`Clocked.scwb_theorem_3_1` has the paper's quantifier order. For every
register machine `M` the network `net M 1` of the paper's Figure 3.1 is
fixed first; then for every `δ ∈ (0, 1]`, input and step bound `t ≥ 1`
there is an initial count of the accuracy species `A` such that, under the
mass-action jump chain, the first `t` machine steps are simulated correctly
with probability at least `1 − δ`, in expected time at most
`6 v t² / (k δ)`. The clock is analysed in occupation-measure form (a flux
identity and cone invariance by a minimum principle); this also supplies the
"memoryless" step of the paper's Lemma A.4, which its Lemma A.1 proves only
for the clock started at the top. Paper proofs:
[`docs/audit/FIX3-SCWB.md`](docs/audit/FIX3-SCWB.md). Theorems 3.2 and 4.1
(Turing machines) remain open.

### Kanaya et al.: O(n) states, and the first step of the time bound

- `P_EM_fin_silent_SSEM_states`: the Lean P_EM runs on a finite
  role-indexed state type with at most `394 n` states and is silent
  self-stabilizing exact majority for `n ≥ 4`.
- `P_EM_paper_fin_solves_silent_SSEM` and `card_PEMPaperFin_le`: the same
  for the parameters of Kanaya et al. and Burman et al. (constant `trank`,
  `Rmax = ⌈60 ln n⌉`, `Emax = e·n`, `Dmax = d·n`), with O(n) states.
- `P_EM_paper_propagation`, Burman et al. Lemma 3.2: after `⌈4 n ln n⌉`
  interactions from a configuration with a Resetting agent of resetcount at
  least `⌈60 ln n⌉`, the configuration is fully propagating except with
  probability at most `2/n`. The proof replaces the paper's citation by two
  potentials and a product-measure supermartingale lemma
  ([`docs/audit/FIX2-BURMAN.md`](docs/audit/FIX2-BURMAN.md)).

The time upper bound of Theorem 4 is stated for the paper instance
(`KanayaThm4Time`) and remains open.

### Other changes

- `kurtz_finite_horizon` takes the initial condition of Kurtz's theorem: a
  random initial state whose densities converge in probability to `x(0)`;
  `kurtz_finite_horizon_of_close` gives the bound uniformly over
  deterministic initial states near `x(0)`.
- `zero_init_no_collapse` states the eventual lower bound (liminf at least
  `c > 0`); `zero_init_eventually_bounded_below`, which carried that
  statement in r2026.11.1, is removed.

### Build

The default target checks the `Ripple.lean` import closure (568 modules) and
all of `Tri`; the exhaustive `Ripple` target compiles all 1063 Ripple
modules, including the Chudnovsky and SCWB developments. The release tree
was built on one NERSC Perlmutter CPU node, with Mathlib from a prebuilt
cache and Ripple and `Tri` compiled from scratch with 64 compile threads:
`lake build Ripple RippleDefault Tri` completed successfully (5525 jobs) in
about 39 minutes of build time over two jobs, the second resuming
incrementally, with no error and no `sorry`. `#print axioms` on 122 headline
declarations reports only `propext`, `Classical.choice` and `Quot.sound`.

## r2026.11.1 — 2026-11-08 (ζ(3) in real time, bounded analog complexity §§2–7, statements matched to their proofs)

An incremental release on top of r2026.11. It adds results and removes
statements whose names claimed more than their proofs give; it does not
change the computability predicates. `CHANGELOG.md` lists every change and
`docs/refactor/STATEMENT-CHANGES.tsv` the deleted, renamed and restated
declarations.

### Apéry's constant in real time

`Ripple.Number.apery_is_realtime` proves that ζ(3) = ∑ 1/(k+1)³ is
real-time computable for the paper predicate, so it lies in the first floor
of the bounded complexity hierarchy. The witness is a five-variable PIVP
with ℚ-polynomial field and initial value `(1, 0, 0, 1/2, 0)`: ȧ = −a,
ḃ = a − b, ċ = 2b − c, q̇ = a q², Ṡ = (2/3) c q, whose output is
S(t) = (2/3)∫₀ᵗ x²/(1 + eˣ) dx, a Fermi–Dirac integral. Its error is at most
(16/3)e^(−t/2) for t ≥ 0, which gives the modulus μ(r) = 2r + 6
(`fermi_certifiedBoundedTimeComputable`).

### The journal version of the bounded analog complexity paper

Sections 2 to 7 of the journal version of [BAC] are formalized:

- Theorem 4.6 for the definition of Bournez, Graça and Pouly, for numbers
  and for functions on a compact set: poly-length computability gives
  polynomial time for bounded systems, through a shifted-clock compilation
  (`isPolyTimeComputable_of_isBGPPolyLengthComputable`,
  `isPolyTimeComputableOn_of_isBGPPolyLengthComputableOn`).
- Section 5, constructible moduli, with exact moduli: `(r+1)^n − 1`,
  `(r+1) log(r+1)` (through a Lambert function constructed in Lean) and the
  tower `E_{k+1}(r)` (`Constructible.polyFamily_certified`,
  `lambert_certified`, `tower_certified`).
- Theorems 6.1 and 6.4, closure under `α^β` for `α > 0`, with the
  polynomial time classes preserved (`isCRNComputable_rpow`,
  `isPolyTimeComputable_rpow`). The draft's construction assumes that an
  upstream output stays above `−1`, which fails for outputs that are
  negative early, and its modulus `max(μ_α, μ_β) + O(1)` is false; the
  formalized construction drives the filter with the square of the input
  and has modulus `max(max(μ_α(r+C), 0) + r + C, μ_β(r+C))`.
- Section 7, the CRN readout with the modulus relation (`crn_of_certified`):
  a bounded ℚ-PIVP computing `α > 0` gives a mass-action CRN with zero
  initial values and modulus at most `max(μ(r + k), 0) + (4/α + 4α) r + C`,
  by a shift to zero initial values, dual rail and a double-inversion
  readout. Consequences: polynomial-time GPAC and CRN computation agree for
  `α > 0` (`isPolyTimeCRNComputable_iff`), and every `IsCRNComputable`
  number in `[0, 1]` is LPP-computable (`IsCRNComputable.isLPPComputable`),
  for example Euler's γ (`euler_gamma_is_lpp_computable`).

The repaired proofs, with the counterexamples to the draft's steps, are in
[`docs/refactor/BAC2-PAPER.md`](docs/refactor/BAC2-PAPER.md).

### Other new results

- Albenque and Gerin, Theorem 5, in every degree without premises
  (`isEhrenfestComputable_algebraic_of_degree`), using an elementary proof
  of Cassels' divisibility theorem.
- Kanaya et al.: Theorem 2 without the input-oblivious premise
  (`space_lower_bound`), Theorem 3 in expectation and with high probability
  for `n ≥ 2` (`time_lower_bound_omega_n_expected`, `time_lower_bound_whp`),
  and the qualitative part of Theorem 4 (`P_EM_solves_silent_SSEM_linear`).
  The paper's Definition 1 is formalized (`KanayaDefinition1`) and implies
  the reachability forms these theorems use
  (`solvesSSEM_of_kanayaDefinition1`, `silentProtocol_of_almostSure`).
- Kurtz's law of large numbers on `[0, T]` for canonical density-dependent
  chains (`kurtz_finite_horizon`).
- The CF'24 readout limit `(3 − √5)/6` from the canonical initial condition,
  and its λ-trick, r²-trick and NAP-20 lifts (`cf24_readout_canonical`).
- Soloveichik et al. Theorem 4.2 with computable coverability instances.

### Statements removed or renamed

A review of the headline declarations found statements whose names claimed a
paper theorem that their proofs do not give. They are deleted or renamed in
this release, and the paper theorems they named are recorded as open in
`OPEN_PROBLEMS.md` §6:

- Soloveichik–Cook–Winfree–Bruck: 22 reachability wrappers whose conclusion
  holds for every pair of states, 14 wrappers about a network that does not
  depend on the machine, and the two stochastic bounds (one with per-step
  error bound 1, one with a premise that fails for two or more steps).
  Theorems 3.1, 3.2 and 4.1 are open.
- Kanaya et al.: the time upper bound
  `PEM_expected_parallel_time_linear_param`, whose premise is false (the
  timer is unbounded). The time and state bounds of Theorem 4 are open.
- Kurtz: `kurtz_strong_approximation` (premise equals conclusion) and
  `kurtz_clt_second_moment` (fixed `N`, carried bound); two convergence
  statements that assume their key estimate are renamed. The CLT and the
  strong approximation are open.
- CF'24: the readout theorems under the hypothesis `Cf24BasinEntry`, which is
  false (`cf24_basinEntry_false`). The limit from every interior initial
  condition is open.

The erratum `paper/ERRATA.md` now states, for each of the report claims in
its second section, what this release establishes and what remains open.

### Build

The default target checks the `Ripple.lean` import closure (561 modules) and
all of `Tri`; the exhaustive `Ripple` target compiles all 1038 Ripple
modules. The release tree was built on one NERSC Perlmutter CPU node, with
Mathlib from a prebuilt cache and Ripple and `Tri` compiled from scratch with
64 compile threads: `lake build Ripple RippleDefault Tri` completed
successfully (5490 jobs) in about 33 minutes of build time over two 30-minute
jobs, the second resuming incrementally, with no error and no `sorry`.
`#print axioms` on 104 headline declarations reports only `propext`,
`Classical.choice` and `Quot.sound`.

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
