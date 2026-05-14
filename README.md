# Ripple

A Lean 4 formalization of **Chemical Reaction Network computable numbers** — the class of real numbers a bounded CRN (equivalently, a polynomial initial value problem / GPAC) can compute in real time, and its refinements down to weaker analog models (large-population protocols, bounded-analog complexity).

## Where the name comes from

"Ripple" is a mishearing. The author meant *repository*, the word came out *ripple*, and the name stuck — because the underlying research actually did start small and ripple outward.

It began as a homework exercise in Jack Lutz's class at Iowa State: *can you compute rational numbers with a chemical reaction network?* That grew into algebraic numbers, then transcendentals (e, π, the Euler–Mascheroni constant γ, ln 2), then the shape of the whole real-time class, then weaker population-protocol refinements, then — on the other side — stronger infinite-time analogues. Each layer was a new ripple from the same class exercise.

This repository is the Lean 4 counterpart to that trajectory.

## Scope

Ripple formalizes the theory developed across these papers:

1. Huang, Klinge, Lathrop, Li, Lutz — *Real-time computability of real numbers by chemical reaction networks*, Nat. Comput. 2018.
2. Huang, Klinge, Lathrop — *Real-time equivalence of CRNs and analog computers*, DNA 25 (2019).
3. Huang, Huls — *Computing real numbers with large-population protocols*, DNA 28 (2022).
4. Chen, Huang — *Bounded analog complexity of real numbers* (submitted, 2026).
5. Kurtz — *Solutions of ordinary differential equations as limits of pure jump Markov processes*, J. Appl. Probab. 7 (1970), 49–58.
6. Ethier, Kurtz — *Markov Processes: Characterization and Convergence*, Wiley, 1986 (2nd ed. 2005).

Papers 1–4 develop the CRN computability hierarchy. Papers 5–6 provide the probabilistic foundation: the mean-field limit theorem that connects stochastic CRN dynamics (CTMCs) to their deterministic ODE approximations (GPACs). The goal is to treat these as one unified pipeline.

## What is formalized (as of 2026-05-14)

### CM-163 — `j((1+√−163)/2) = −640320³`

- **`KleinJCM163Statement_proof`** in `Ripple/Number/Modular/CMEvaluation163.lean`.
  The Heegner-class CM evaluation of the modular `j`-invariant at the
  unique class-number-1 discriminant `−163`, fully verified through the
  level-41 modular polynomial `Φ₄₁`. Closing this required:
  - **`atkinLehnerInclusion41`** — the matrix-algebra identity that the
    conjugate of `Γ₀(41)` by the Atkin-Lehner pullback `[[41,0],[0,1]]`
    sits inside `Γ(1)`.
  - **`levelOne_cuspForm_eq_zero_of_low_coeffs_vanish`** — a uniform
    level-1 Sturm bound for arbitrary even weight `k ≥ 4`: if the first
    `⌊k/12⌋ + 1` `q`-expansion coefficients of a level-1 cusp form
    vanish, the form is zero. Parametric in `(a, b, n)` with
    `a·k = 12·b` and `a·n ≥ b + 1`; dispatches on `k mod 12`.
  - **`phi41Level41ClearedAsModularForm`** — the bundled
    `ModularForm Γ₀(41) 1008` whose `q`-expansion equals
    `phi41Level41ClearedEulerQExpansion`, assembled via the graded ring
    of modular forms over the four building blocks (E₄ and Δ on Γ₀(41),
    plus their Atkin-Lehner pullbacks).
  - **`qExp_norm_coeff_zero_of_qExp_coeff_zero`** — the analytic
    substance of Sturm at level `N`: vanishing of the first M
    `q`-coefficients of `f` propagates to vanishing of the first M
    `q`-coefficients of `norm 𝒮ℒ f`, since each non-trivial coset
    contributes at least 0 to the order at infinity by boundedness at
    cusps.
  - **`levelGamma0_41_sturm_weight_1008`** — the Sturm bound at level
    `Γ₀(41)` weight `1008`: combine the q-expansion bridge with the
    generic level-1 Sturm at weight `1008·42 = 42336` and then
    `ModularForm.norm_eq_zero_iff` to deduce `f = 0`.

### ζ(3) — Apéry's constant

- **F1 (three-term recurrence).** `aperyA_recurrence` and `aperyB_recurrence` for the Apéry sequences aₙ, bₙ, closed via the pointwise vdPoorten (1979, §8) Zeilberger witness. `aperyW_pointwise` handles all three case regimes (k ≤ n−2, k = n−1, k = n) axiom-free.
- **F1′ (harmonic correction recurrence).** `aperyD_recurrence` and the decomposition `bₙ = H₃(n)·aₙ + dₙ`.
- **F2 (formal ODE).** `aperyGFA_satisfies_ode` (homogeneous) and `aperyGFB_satisfies_ode` (inhomogeneous with a single `z⁰` correction of 6, since the A-recurrence closes at n=0 but the B-recurrence does not). This is the Apéry differential operator `p(z)u‴ + q(z)u″ + r(z)u′ + s(z)u`.
- **Fermi–Dirac real-time encoding.** `fermi_integral_eq_zeta3` — the identity `(2/3)·∫₀^∞ x²/(1+eˣ) dx = ζ(3)` — via the geometric-remainder expansion `1/(1+eˣ) = Σ (−1)ᵏ e^(−(k+1)x)`, termwise integration, and the alternating-to-zeta rearrangement. Packaged as a `PIVP.Solution` in `apery_fermi_is_crn_computable`, together with a real-time modulus bound `|S(t) − ζ(3)| ≤ C·(t² + 2t + 2)·e^(−t)`.

### Large-population protocols

- **Main theorem (unconditional).** `bounded_crn_is_lpp_computable_unconditional` — every bounded certified PIVP is LPP-computable. Patches the DNA 28 gap where transient overshoot beyond the unit interval could break compilation, via a saturating surrogate `y' = (x − y)(U − y)` with `U ∈ (α, 1) ∩ ℚ`.
- **Algebraic case.** `algebraic_lpp_computable` — every algebraic number in [0,1] is LPP-computable. Five-pipeline construction: minimum-polynomial encoding → positive-rational shift → zero-init wrapper → Stage 1 quadraticization → Stage 2 bound-to-small-λ closure.
- **Stage-by-stage LPP pipeline.** `stage1_quadraticization`, `stage2_*`, `tpp_to_lpp`, `stage4_to_plpp`, reverse `lpp_to_gpac`.
- **Dual-rail and exp-shift constructions.** `dualRail_semantic_solution`, axiom-free.

### Catalan's constant G

`catalan_is_lpp_computable` in `Ripple/Number/CatalanCertified.lean` — G is LPP-computable via `G = ∫₀^∞ s·exp(−s)/(1 + exp(−2s)) ds`, compiled as a 4-variable bounded polynomial IVP (E, R, W = 1−V, G) with convergence bound `|G(t) − G| ≤ (t+1)·exp(−t)`.

### Foundational

- **e, π, ln 2, γ, ½e⁻¹.** Famous constants packaged as CRN-computable with zero sorries. `EulerGamma` is the most intricate.
- **Non-collapse theorem.** `zero_init_no_collapse` (Xiang's conjecture, fully proved).
- **Real-time foundation.** `algebraic_is_certified_crn`, `minPolyPIVP_certified`, `certified_add_rational_nonneg` — direct minimum-polynomial encoding of an algebraic number as a quadratic PIVP, plus rational shifts.

### Kurtz mean-field limit theorem (CTMC → ODE)

The stochastic-to-deterministic bridge: a density-dependent CTMC with N agents converges to the mean-field ODE as N → ∞. Three versions, all sorry-free:

- **`kurtz_mean_field_convergence`** — weak convergence in probability: for ε > 0, P(sup‖X̄ᴺ − x‖ > ε) → 0 as N → ∞. Uses Markov's inequality + pathwise Gronwall.
- **`kurtz_strong_approximation`** — strong (a.s.) convergence: sup‖X̄ᴺ − x‖ = O(log N / √N) almost surely. Uses Azuma–Hoeffding + Borel–Cantelli + integral Gronwall.
- **`kurtz_clt_second_moment`** — CLT-scale second moment bound: E[sup‖X̄ᴺ − x‖²] ≤ C/N. Uses Doob L² + integral Gronwall.

Supporting infrastructure:

- **`integral_gronwall_core`** (`IntegralGronwall.lean`) — if u(t) ≤ α + ∫₀ᵗ β·u(s) ds then u(t) ≤ α·exp(β·t). Proved via Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le` (derivative-form Gronwall) applied to v(t) = α + ∫₀ᵗ β·u.
- **Shifted martingale resolution** (`RandomIndexDoob.lean`) — resolves the canonical filtration mismatch: jump-count stopping time τ is measurable w.r.t. G_n = F_{n+1}, not the natural filtration F_n. Defines M̃(n) = M(n+1), proves it is a G-martingale, derives Doob L² at random index.
- **`canonicalDensityProcess`** — constructs a `DensityProcess` from any `DensityDepCTMC`, discharging all regularity fields (decomposition, QV bound, integrability).

### CTMC infrastructure

- **`Ripple/CTMC/CTMC.lean`** — continuous-time Markov chain: state space, transition rates, holding times, jump chain.
- **`CTMCProcess.lean`** — path-level CTMC process: state trajectory, jump times, stopped process.
- **`DensityDependent.lean`** — density-dependent CTMCs (rate scales with N), density process X̄ᴺ = X/N.
- **`TwoState.lean`** — two-state CTMC: birth-death chain, exact stationary distribution, ergodic convergence.
- **`CanonicalLaw.lean`** — canonical law of the CTMC: probability distribution of the process.
- **`DTMC.lean`** — discrete-time Markov chain foundations.

## What remains open

The repository has **0 `sorry` and 0 `axiom` declarations** across all
eight pillars (Core, ODE, DualRail, LPP, Number, Number/Modular, Kurtz, CTMC).

- **Kernel-only certificate for the Φ₄₁ Sturm coefficient zero check.**
  `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` is currently
  closed via `native_decide`, which trusts the Lean compiler chain in
  addition to the kernel. The CRT-route helpers in
  `Ripple/Number/Modular/ModularPolynomialSturmCertificate.lean` are
  in place; replacing `native_decide` with a kernel-only Chinese
  Remainder Theorem certificate is feasible in principle but requires
  either a tighter problem-specific coefficient bound (the natural
  a-priori bound is ≈10^8590, demanding ≈468 CRT primes) or a custom
  reflection evaluator. See `RELEASE_NOTES.md` and
  `HANDOFF/crt_route_replace_native_decide.md` (in the working
  workspace) for the concrete plan.

## Trust footprint

There are no `axiom` declarations and no `sorry` in any tactic
position. The only trust beyond the Lean kernel is the `native_decide`
tactic, used in finitely many places to discharge large decidable
claims:

- `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` — first 3529
  entries of the Φ₄₁ cleared `q`-expansion recurrence array vanish.
- `phi41Diag_root` — `evalPhi41Diag(j(τ₁₆₃)) = 0`.
- `phi41DiagCofactor_ne_zero` — the cofactor at the root is nonzero.
- A level-41 difference table check via `(List.range 83).Forall ...`.

`native_decide` compiles the decision procedure to native code and
trusts that the compiled program's result matches what the Lean
kernel would compute. The mathematical content is unchanged; only the
verification path differs from a strict kernel-only proof.

## Building

```bash
# Prerequisites: elan + Lake (https://leanprover.github.io/)
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get    # pull Mathlib oleans
lake build
```

Takes 10–20 minutes on first build (mostly Mathlib).

## Structure

```
Ripple/
├── Core/
│   ├── PIVP.lean          Polynomial initial value problems (GPAC model)
│   ├── BoundedTime.lean   Time modulus, complexity hierarchy
│   ├── Compilation.lean   Bounded surrogate compilation
│   └── CRNPipeline.lean   Dual-rail + readout, complexity preservation
├── CTMC/
│   ├── CTMC.lean          Continuous-time Markov chain definition + transitions
│   ├── CTMCProcess.lean   Path-level process, jump times, stopping
│   ├── DensityDependent.lean  Density-dependent CTMC, X̄ᴺ = X/N
│   ├── RandomIndexDoob.lean   Shifted-filtration Doob L², DensityProcess construction
│   ├── TwoState.lean      Two-state birth-death chain, stationary distribution
│   ├── CanonicalLaw.lean  Probability law of the CTMC process
│   └── DTMC.lean          Discrete-time Markov chain foundations
├── Kurtz/
│   ├── Defs.lean          RateSpec, DensityProcess, MeanFieldSolution structures
│   ├── IntegralGronwall.lean  Integral-form Gronwall inequality
│   ├── MeanField.lean     Weak, strong, CLT Kurtz theorems + pathwise Gronwall
│   └── PopulationProtocol.lean  Population protocol specialization
├── LPP/                   Large-population-protocol compilation + main theorem
├── Number/
│   ├── AperySequences.lean   F1 / F1′ / F2 for the Apéry sequences
│   ├── AperyFermi.lean       Fermi–Dirac real-time encoding of ζ(3)
│   ├── ApreyBounded.lean     Conifold Frobenius witness
│   ├── Apery.lean            Overall ζ(3) theorem wiring
│   ├── Frobenius/            Regular-singular Frobenius theory (long-term pillar)
│   └── Modular/              Modular forms, j-invariant, CM-163, Φ₄₁ Sturm
├── ODE/                   Scalar Picard barriers, generic attractor tools
└── Tactic/                (future) automation for constructing proofs
```

`OPEN_PROBLEMS.md` lists the current research frontier; `WORK_LOG.md` and `CHECKPOINT.md` track session-level progress.

## References

CRN computability:

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
  title     = {Computing real numbers with large-population protocols},
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
  note   = {Submitted},
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

If this formalization is useful in your work, cite the relevant paper above. The repository itself is a living artifact — referencing the commit hash alongside the paper is more informative than the repo alone.

## License

Apache-2.0, matching Mathlib. See `LICENSE`.
