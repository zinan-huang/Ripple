# DeepSeek CTMC Task — Done

## Summary

All three tasks completed. `lake build Ripple.CTMC.CTMC` succeeds with 0 errors.

## Task 1: `row_sum_zero` ✓

Closed using a 4-line proof:

```lean
rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ s)]
rw [Q.diag_eq_neg_exitRate, exitRate, Finset.filter_ne']
linarith
```

**Key lemma:** `Finset.filter_ne'` (Mathlib/Data/Finset/Basic.lean:418) — `(s.filter fun a => a ≠ b) = s.erase b`. This bridges `filter (· ≠ s)` (used in `exitRate`) to `erase s` (from `Finset.add_sum_erase`), making the terms cancel.

## Task 2: `embeddedDTMC` ✓

Refactored into two parts:

1. **`jumpProb`** — normalized jump probabilities `q(s,t)/exitRate(s)` as `ℝ≥0∞`, zero on diagonal. Uses `ENNReal.ofReal` to convert from ℝ; diagonal vanishes because `ENNReal.ofReal (-1) = 0`.
2. **`jumpProb_sum`** — proves `∑_t jumpProb s t = 1` for non-absorbing states. Uses `ENNReal.ofReal_sum_of_nonneg` to commute the sum with `ofReal`, then the ℝ identity `(∑ q) / exitRate = 1`.
3. **`embeddedDTMC`** — one-liner: `PMF.ofFintype (Q.jumpProb s) (Q.jumpProb_sum s h)`.

**Added import:** `Mathlib.Probability.ProbabilityMassFunction.Constructions` (provides `PMF.ofFintype`).

## Task 3: Transition semigroup skeleton ✓

Added:
- `QMatrix.transitionProb` — `P(t) = exp(tQ)` (matrix exponential, `sorry` body)
- `QMatrix.kolmogorov_forward` — Kolmogorov forward equation `P'(t) = P(t)·Q` (`sorry` proof)

Both marked with `/-! ## Transition Semigroup -/` section header.

## Build

```
$ ~/.elan/bin/lake build Ripple.CTMC.CTMC
Build completed successfully (2710 jobs).
```

Two `sorry` warnings remain in the transition semigroup skeleton (expected, per task spec).
