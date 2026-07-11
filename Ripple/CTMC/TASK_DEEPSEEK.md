# Task for DeepSeek: Complete CTMC.lean

## Context

We are building CTMC (Continuous-Time Markov Chain) infrastructure in Lean 4
as part of the Ripple project. The file `Ripple/CTMC/CTMC.lean` has a skeleton
with two sorry's that need to be closed.

## Your Tasks

### Task 1: Close `row_sum_zero` sorry

File: `Ripple/CTMC/CTMC.lean`

The lemma says: for a Q-matrix, `∑ t, Q.rate s t = 0`.

The proof strategy is:
- Split the sum into the diagonal term + off-diagonal terms
- The diagonal = -exitRate = -(sum of off-diagonal)
- So diagonal + off-diagonal = 0

The sorry is about showing `Finset.filter (· ≠ s) Finset.univ = Finset.univ.erase s`.
Use `Finset.filter_ne'` or `Finset.filter_ne_eq_erase` if available, or prove directly.

### Task 2: Close `embeddedDTMC` sorry

Construct a `PMF S` from the normalized rates `Q.rate s t / Q.exitRate s`.
You need to show the sum equals 1. Use `PMF.ofFintype` with:
- `f t = ENNReal.ofReal (Q.rate s t / Q.exitRate s)` for t ≠ s, `f s = 0`
- Sum = 1 because ∑_{t≠s} q(s,t) / exitRate(s) = exitRate(s)/exitRate(s) = 1

### Task 3: Add transition semigroup skeleton

After closing the sorry's, add these definitions (with sorry proofs OK for now):

```lean
/-- The transition matrix P(t) = exp(tQ). For finite state spaces,
this is a matrix exponential. -/
noncomputable def QMatrix.transitionMatrix (Q : QMatrix S) (t : ℝ) :
    S → S → ℝ := sorry

/-- Kolmogorov forward equation: P'(t) = P(t)·Q. -/
theorem QMatrix.kolmogorov_forward (Q : QMatrix S) :
    ∀ t ≥ 0, HasDerivAt (fun t => Q.transitionMatrix t)
      (fun s u => ∑ v, Q.transitionMatrix t s v * Q.rate v u) t := sorry
```

## Build Command

```bash
cd /Users/huangx/.openclaw/workspace/projects/Ripple
~/.elan/bin/lake build Ripple.CTMC.CTMC
```

## Rules

- Run `lake build` after every change
- No `axiom` declarations
- `sorry` is OK for hard proofs, but try to close the first two
- Use Mathlib lemmas (search with grep in .lake/packages/mathlib/)
- When done, write a summary to `Ripple/CTMC/DEEPSEEK_DONE.md`
