# Task for Gemini: Write DensityDependent.lean

## Context

We are building CTMC infrastructure in Lean 4 (Ripple project).
Phase 1 (DTMC) is done: `Ripple/CTMC/DTMC.lean` builds with 0 sorry.
Phase 2 (CTMC) is in progress: `Ripple/CTMC/CTMC.lean`.

Your task is Phase 3: density-dependent CTMCs and the connection
to our existing `Ripple.Kurtz.DensityProcess`.

## Your Task: Write `Ripple/CTMC/DensityDependent.lean`

Create this file with the following content:

### 1. DensityDepCTMC structure

A density-dependent CTMC is a CTMC on the lattice (1/N)·ℤ^d where
the transition rates depend on the current density x = state/N.

```
structure DensityDepCTMC (d : ℕ) where
  /-- Population size -/
  N : ℕ
  hN : 0 < N
  /-- The rate specification (from Ripple.Kurtz.Defs) -/
  rateSpec : Ripple.Kurtz.RateSpec d
```

### 2. Q-matrix construction

From a DensityDepCTMC, construct a QMatrix on Fin(N+1)^d (or similar
finite type). The rate from state x to state x+ℓ is N · β_ℓ(x/N).

### 3. Martingale decomposition (statement only)

State (with sorry proof) that the density process X̄^N(t) = X^N(t)/N
satisfies:
```
X̄^N(t) = X̄^N(0) + ∫₀ᵗ F(X̄^N(s)) ds + M^N(t)
```
where M^N is a martingale.

### 4. QV bound (statement only)

State (with sorry proof):
```
E[sup_{s≤T} ‖M^N(s)‖²] ≤ C·T/N
```

### 5. Bridge to DensityProcess

Construct a `Ripple.Kurtz.DensityProcess` from a `DensityDepCTMC`.
This is the payoff: every field of DensityProcess gets a (sorry) proof
from the CTMC construction. This outlines what needs to be proved
to make the Kurtz theorem fully constructive.

## Key imports

```lean
import Ripple.CTMC.CTMC
import Ripple.Kurtz.Defs
```

## Build Command

```bash
cd /Users/huangx/.openclaw/workspace/projects/Ripple
~/.elan/bin/lake build Ripple.CTMC.DensityDependent
```

## Rules

- Run `lake build` after every change — it MUST compile
- sorry is OK for proofs, but definitions must be complete
- No `axiom` declarations
- Import from `Ripple.Kurtz.Defs` for `RateSpec`, `DensityProcess`, `MeanFieldSolution`
- When done, write a summary to `Ripple/CTMC/GEMINI_DONE.md`
