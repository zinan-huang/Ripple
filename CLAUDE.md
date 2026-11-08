# Ripple — Lean 4 Framework for CRN Computable Numbers

## Mandatory Maintenance Policy

Before importing development changes, editing Technical Report links, or
updating `CHANGELOG.md`, `RELEASE_NOTES.md`, tags, or GitHub Releases, read
`MAINTENANCE.md` completely and follow it. This checkout is the curated public
publication lineage; never merge or push private development history into it.

## What This Is

Ripple formalizes the theory of Chemical Reaction Network (CRN) computable
numbers in Lean 4, building on work about real-time CRN computability,
real-time equivalence with analog computers, large-population protocols, and
bounded analog complexity.

## Architecture

```
Ripple/
├── Core/                  — PIVP (GPAC), computability predicates (BoundedTime), bounded surrogate compilation
├── Analysis/, ODE/        — Gronwall-type stability; scalar barriers
├── DualRail/              — Dual-rail encoding of polynomial dynamics
├── LPP/                   — Large-population protocols: definitions, compiler, Theorem 17
├── Number/                — Specific real numbers (e, π, ln 2, γ, Catalan, Dottie, ζ(3), ...)
│   ├── Frobenius/         — Regular-singular Frobenius theory
│   └── Modular/           — Modular forms, Φ₄₁, CM evaluation
├── BoundedUniversality/   — GPAC Turing completeness (Bournez–Graça–Pouly)
├── sCRNUniversality/      — Stochastic CRN universality (Soloveichik–Cook–Winfree–Bruck)
├── PopulationProtocol/    — ExactMajority, SSEM, PopProto, PopProtoCommon
├── CTMC/, Kurtz/          — Continuous-time Markov chains; Kurtz mean-field limits
└── Probability/           — Discrete Freedman and Bennett inequalities, lazy steps
Tri/                       — Tri-molecular approximate majority (second Lean library)
```

Names follow the convention described in `RELEASE_NOTES.md` (r2026.11); the
old-to-new map of that release is `docs/refactor/RENAMES.tsv`.

## The Vision

**Frontend:** An LLM agent takes a target number and searches for integral representations.
**Middle:** Lean 4 formal proof infrastructure — encode integrals as ODEs, verify boundedness, prove convergence rate.
**Backend:** (future) ODE simulator to validate constructions numerically.

## Current Goal

Prove Apéry's constant ζ(3) is CRN-computable in the **first floor** of the bounded complexity hierarchy (real-time, μ(r) = Θ(r)). The existing manual proof is second-floor.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /path/to/Ripple
lake build
```

## Conventions

- All proofs follow the Mathlib style guide
- The tree has no `sorry`, no `axiom` declarations and no `native_decide`; keep it that way
- Use Mathlib's ODE and analysis libraries wherever possible
