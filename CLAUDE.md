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
├── Core/
│   ├── PIVP.lean          -- Polynomial Initial Value Problems (GPAC model)
│   ├── BoundedTime.lean   -- Time modulus, complexity hierarchy
│   ├── Compilation.lean   -- Bounded surrogate compilation
│   └── CRNPipeline.lean   -- Dual-rail + readout, complexity preservation
├── Number/
│   └── Apery.lean         -- ζ(3): first target number
└── Tactic/                -- (future) automation for constructing proofs
```

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
- `sorry` marks genuine open goals; `axiom` marks theorems stated but proof deferred
- Use Mathlib's ODE and analysis libraries wherever possible
