# Ripple

A Lean 4 formalization of **Chemical Reaction Network computable numbers** — the class of real numbers a bounded CRN (equivalently, a polynomial initial value problem / GPAC) can compute in real time, and its refinements down to weaker analog models (large-population protocols, bounded-analog complexity).

## Where the name comes from

"Ripple" is a mishearing. The author meant *repository*, the word came out *ripple*, and the name stuck — because the underlying research actually did start small and ripple outward.

It began as a homework exercise in Jack Lutz's class at Iowa State: *can you compute rational numbers with a chemical reaction network?* That grew into algebraic numbers, then transcendentals (e, π, the Euler–Mascheroni constant γ, ln 2), then the shape of the whole real-time class, then weaker population-protocol refinements, then — on the other side — stronger infinite-time analogues. Each layer was a new ripple from the same class exercise.

This repository is the Lean 4 counterpart to that trajectory.

## Scope

Ripple formalizes the theory developed across four papers:

1. Huang, Klinge, Lathrop, Lutz, Lutz — *Real-time computability of real numbers by chemical reaction networks*, Nat. Comput. 2018.
2. Huang, Klinge, Lathrop — *Real-time equivalence of CRNs and analog computers*, DNA 25 (2019).
3. Huang, Huls — *Computing real numbers with large-population protocols*, DNA 28 (2022).
4. Chen, Huang — *Bounded analog complexity of real numbers* (submitted, 2026).

The goal is to treat these as one unified pipeline rather than four disjoint papers.

## What is formalized (as of 2026-04-21)

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

### Foundational

- **e, π, ln 2, γ, ½e⁻¹.** Famous constants packaged as CRN-computable with zero sorries. `EulerGamma` is the most intricate.
- **Non-collapse theorem.** `zero_init_no_collapse` (Xiang's conjecture, fully proved).
- **Real-time foundation.** `algebraic_is_certified_crn`, `minPolyPIVP_certified`, `certified_add_rational_nonneg` — direct minimum-polynomial encoding of an algebraic number as a quadratic PIVP, plus rational shifts.

## What remains open

- **Conifold Frobenius witness for the Apéry ODE** — `apery_conifold_frobenius_witness` at `Ripple/Number/ApreyBounded.lean:338`. The regular-singular-point Frobenius theory needed to pass from the formal ODE to the analytic exponential-rate convergence is not in Mathlib and is effectively a standalone formalization project. The rest of the Apéry chain is axiom-free modulo this witness.
- **Catalan's constant.** Stated, not yet proved.

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
├── LPP/                   Large-population-protocol compilation + main theorem
├── Number/
│   ├── AperySequences.lean   F1 / F1′ / F2 for the Apéry sequences
│   ├── AperyFermi.lean       Fermi–Dirac real-time encoding of ζ(3)
│   ├── ApreyBounded.lean     Conifold Frobenius witness (open)
│   └── Apery.lean            Overall ζ(3) theorem wiring
├── ODE/                   Scalar Picard barriers, generic attractor tools
└── Tactic/                (future) automation for constructing proofs
```

`OPEN_PROBLEMS.md` lists the current research frontier; `WORK_LOG.md` and `CHECKPOINT.md` track session-level progress.

## Citing

If this formalization is useful in your work, cite the relevant paper above. The repository itself is a living artifact — referencing the commit hash alongside the paper is more informative than the repo alone.

## License

Apache-2.0, matching Mathlib. See `LICENSE`.
