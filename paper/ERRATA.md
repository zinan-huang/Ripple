# Erratum to the Technical Report (arXiv:2607.13531v2)

Report: Ho-Lin Chen and Xiang Huang, *Ripple: An Open, AI-Formalized Lean 4
Framework for Computing with CRNs*, `arXiv:2607.13531v2`, revised 21 July
2026 (the repository copy is [`Ripple-DNA32.pdf`](Ripple-DNA32.pdf)).

This note corrects statements of that report about large-population-protocol
(LPP) computability and about the class-level computability predicates, and
records four further claims (Kurtz's theorem, the stochastic CRN simulation,
and two population-protocol results) that the cited declarations do not
establish, with their status in release `r2026.11.1`. The
report PDF is unchanged. No repository commit was recorded for v2. The
definitions quoted below are identical at the last public commit before the
v2 revision date (`e4f5d796`, 20 July 2026) and at release `r2026.08`.

## What was wrong

At the v2 snapshot, four Lean predicates were weaker than their names and
than the papers they formalize:

- `IsCRNComputable α`, `IsRealTimeComputable α` and `IsPolyTimeComputable α n`
  (`Ripple/Core/BoundedTime.lean`) asked for a `BoundedTimeComputable`
  record over the semantic `PIVP` structure, whose vector field is an
  arbitrary function `(Fin d → ℝ) → (Fin d → ℝ)` and whose initial value is an
  arbitrary real vector. They therefore held for **every real number**: the
  one-variable system `y' = 0`, `y(0) = α` is bounded and computes `α` with
  any modulus. The repository proved exactly this as `realtime_const`
  (`∀ c : ℝ, IsRealTimeComputable c`).
- `IsLPPComputable ν` (`Ripple/LPP/Defs.lean`) asked for a trajectory on the
  probability simplex with a rational initial value, solving an ODE whose
  vector field was an unrestricted function. It therefore held for **every
  `ν ∈ [0, 1]`**: the linear field `x₁' = ν − x₁`, `x₂' = x₁ − ν` from
  `x(0) = (1, 0)` stays on the simplex and has `x₁(t) → ν`. (Values outside
  `[0, 1]` are excluded by the simplex alone.) Definition 9 of the
  large-population protocol paper (Huang and Huls, DNA 28) requires the field
  to be the balance equation of a population protocol.

The structure `CertifiedBoundedTimeComputable`, which §3.2 of the report
names as the single carrier of "computes α", was **not** affected: it
required a `PolyPIVP`, that is a vector field of polynomials with rational
coefficients and a rational initial value. The constructions `catalanCBTC`,
`piCBTC`, `ln2CBTC` and `invECBTC` were certified objects of that type.

## Report statements not established by the cited declarations

Each declaration below concluded `∃ _ : IsLPPComputable α, True`, which at
the snapshot follows from `0 ≤ α ≤ 1` alone. Its proof built a genuine
compilation, but its statement did not record it, so `#print axioms` on it
did not certify what the report says.

- §3.4 (p. 6): "`bounded_crn_is_lpp_computable_unconditional` … verified
  clean: every bounded certified PIVP compiles into an LPP computing the same
  number", and stage (iv) "producing the `IsLPPComputable` witness".
- §3.4 (p. 6): the corollary that every algebraic `α ∈ [0, 1]` is
  LPP-computable (`algebraic_lpp_computable`).
- §6.1 (p. 10): "The formalized compilation theorem (§3.4) … proves the
  compilation unconditionally for every bounded certified PIVP". The gap in
  the published proof that §6.1 describes, and the saturating low-pass
  filter that repairs it, are correct as mathematics; the Lean statement
  cited for the repaired theorem was the one above.
- §3.3 (p. 6): "This is the theorem `catalan_is_lpp_computable` …, verified
  clean". The certified PIVP for Catalan's constant (`catalanCBTC`, with
  `|G(t) − G| ≤ (t + 1) e^{-t}`) was correct; the LPP conclusion was not
  established.
- §8 (p. 19): "`π/4 = arctan 1` is re-formalized axiom-free as
  `pi_quarter_is_lpp_computable`". The same applies; the certified PIVP
  `piCBTC` was correct.

The abstract and §2 describe "a single Lean definition of real-time CRN
computation" and "the class of reals it captures". The class-level
predicate exported under the name `IsRealTimeComputable` contained every
real number. For the elementary constants of §3.3, the declarations
`euler_is_realtime`, `pi_quarter_is_realtime`, `pi_is_realtime`,
`ln2_is_realtime` and `euler_gamma_is_realtime` concluded that predicate; the
certified constructions listed above existed for `π/4`, `ln 2` and `1/e`,
but not for `e` and `γ`, whose systems were given only in the semantic form.

At the snapshot no declaration outside `Ripple/Core`, `Ripple/DualRail`,
`Ripple/LPP` and `Ripple/Number` mentioned these predicates. The CTMC and
Kurtz layers (§3.5), the majority formalizations (§4), the
Turing-completeness theorems (§5), the Cassels descent (§6.2), the Frobenius
and modular-forms work (§§7–8) and the `Tri` library are not affected.

## Other statements of the report that the cited formalization does not establish

A review of the headline declarations for release `r2026.11` found the
following. Each declaration below is the same at the v2 snapshot (under its
former name, given in parentheses) and in `r2026.11`; they are recorded here
so that the report is not read as claiming them. Release `r2026.11.1` deletes
or restates them; the status line of each item says which of the report's
claims are now established and which remain open (details in
[`OPEN_PROBLEMS.md`](../OPEN_PROBLEMS.md) §6).

- **Kurtz's theorem, its three versions** (abstract, §2,
  Figure 1, §3.5: "Three sorry-free versions of the limit are proved"). The
  almost-sure rate `kurtz_strong_approximation` takes as its hypothesis
  `h_as_bound` the eventual almost-sure bound
  `(√N / log N) · sup_{t ≤ T} ‖X̄ᴺ(t) − x(t)‖ ≤ K`, from which its
  conclusion follows. The CLT-scale bound `kurtz_clt_second_moment` fixes `N`
  before its constant `C` and carries the Grönwall-type hypothesis
  `h_gronwall`. Both are reductions, not proofs of the limit theorems.
  The weak version (convergence in probability),
  `kurtz_mean_field_convergence`, assumes the estimate that makes the
  convergence a squeeze.
  *Status in `r2026.11.1`:* the law of large numbers on `[0, T]` (Kurtz 1970,
  Theorem 3.1) is established for canonical density-dependent chains,
  `kurtz_finite_horizon`; the former statement is renamed
  `tendsto_sup_err_of_gronwall_markov`. The almost-sure and CLT versions
  remain open; `kurtz_strong_approximation` and `kurtz_clt_second_moment` are
  deleted.
- **Bounded-error stochastic simulation in
  Soloveichik–Cook–Winfree–Bruck** (§5, layer (ii), "bounds the per-step
  error probability"; "arbitrarily small error probability"). The per-step
  bound used by `scwb_stochastic_bound` (formerly `scwb_stochastic_bound_unconditional`)
  is `statePairTransferEpsilonBound := 1`, so its conclusion bounds an error
  probability by `n · 1`. The version with a small per-step error,
  `scwb_stochastic_bound_of_enabled_of_clock`
  (formerly `scwb_stochastic_bound_conditional`), carries hypotheses that are not
  discharged; one of them cannot hold for two or more steps. Layer (i) is
  also weaker than stated: the `PaperTheorems.exists_*` reachability
  statements hold for every pair of states (through the network `∅ ⇄ X`),
  and the state-pair transfer network of `PaperTheorems.statePairTransfer_*`
  does not depend on the machine, so the four-phase development shows that a
  correct execution exists, not that a network fixed by the machine
  simulates it.
  *Status in `r2026.11.1`:* the error-bounded simulation theorems (SCWB
  Theorems 3.1, 3.2 and 4.1) remain open, and the statements above are
  deleted. SCWB Theorem 4.2 (coverability is decidable) is established, now
  as computable instances (`Decidability.petriCoverabilityDecidable`,
  `networkCoverabilityDecidable`).
- **State count of the Doty et al. exact-majority protocol** (§4, "the
  O(log n) state-count bound"). `state_count_poly_bound` proves
  `|Λ| ≤ C · (K + 1) · (L + 1)^4` with `L = ⌈log₂ n⌉` and `K` fixed, that is
  O(log⁴ n) states, not O(log n).
  *Status in `r2026.11.1`:* unchanged and open, together with the O(log n)
  stabilization time; stable correctness is established
  (`ExactMajority.stable_majority_correct`).
- **Self-stabilizing exact majority of Kanaya et al.** (§4, "Ripple formalizes
  the paper's four theorems: … the space lower bound …, convergence, and the
  time upper bound"). The time upper bound
  `PEM_expected_parallel_time_linear_param` has a hypothesis that no
  configuration satisfies (its source file says so); the variant
  `PEM_expected_parallel_time_from_phase_bounds` carries four phase-time
  hypotheses. The space lower bound `space_lower_bound` assumes that the
  transition function ignores the input opinions (`hIO`). The
  impossibility theorem and the unconditional convergence theorem for
  `n ≥ 4` (`P_EM_solves_SSEM_linear`, formerly `P_EM_solves_SSEM_final`) are
  as the report states.
  *Status in `r2026.11.1`:* the space lower bound is established without
  `hIO` (`space_lower_bound`; premises silence and self-stabilization), the
  time lower bound of Theorem 3 is established in expectation and with high
  probability (`time_lower_bound_omega_n_expected`, `time_lower_bound_whp`),
  and `P_EM` is silent SSEM for `n ≥ 4` (`P_EM_solves_silent_SSEM_linear`).
  The time upper bound and the O(n) state count of Theorem 4 remain open;
  `PEM_expected_parallel_time_linear_param` is deleted.

## Corrected statements

Release `r2026.11` redefines the predicates as in the papers and proves the
statements above for the new definitions:

- `IsCRNComputable α` is `∃ d, Nonempty (CertifiedBoundedTimeComputable d α)`
  (Definitions 2.1 and 2.3 of the bounded analog complexity paper);
  `IsRealTimeComputable` and `IsPolyTimeComputable` add a linear or
  polynomial bound on the modulus of such a witness. `IsRealTimeComputable`
  equals the real-time GPAC class `R_RTGPAC` of Huang, Klinge and Lathrop
  (DNA 25): `isRealTimeComputable_iff_rtgpac`.
- `IsLPPComputable ν` is `Nonempty (LPPComputation ν)`, the deterministic
  clause of Definition 9 (a protocol `δ : Q² → Q²`, its balance equation, a
  rational initial value on the simplex and a marked set whose mass tends to
  `ν`); `IsPLPPComputable` is the probabilistic clause, and the two agree by
  Theorem 17 (`isLPPComputable_iff_isPLPPComputable`).
- `bounded_crn_is_lpp_computable`: for `0 ≤ α ≤ 1`, a
  `CertifiedBoundedTimeComputable d α` with a `PolyCRNDecomposition` gives
  `IsLPPComputable α`. It is the former
  `bounded_crn_is_lpp_computable_unconditional` under the new predicate,
  proved through the compiler `isLPPComputable_of_certified`, which uses the
  saturating filter of §6.1.
- `algebraic_lpp_computable`, `catalan_is_lpp_computable` and
  `pi_quarter_is_lpp_computable` conclude the new `IsLPPComputable`.
- `euler_is_realtime`, `pi_quarter_is_realtime`, `pi_is_realtime`,
  `ln2_is_realtime` and `euler_gamma_is_realtime` conclude the new
  `IsRealTimeComputable`, with certified ℚ-polynomial systems for `e` and
  `γ`.
- `realtime_const` is deleted (it is false for the new predicate); its true
  form is `realtime_rat_const` (`q : ℚ`).

`#print axioms` on each of these reports only `propext`, `Classical.choice`
and `Quot.sound`. The complete list of restated, deleted and added
declarations is [`docs/refactor/STATEMENT-CHANGES.tsv`](../docs/refactor/STATEMENT-CHANGES.tsv);
the release notes for `r2026.11` explain the change.
