# DeepSeek CTMC Task 3 — Done

## Summary

Created `Ripple/CTMC/TwoState.lean` — a concrete 2-state CTMC example.

`lake build Ripple.CTMC.TwoState` succeeds with 0 errors.

## File: `Ripple/CTMC/TwoState.lean`

### Definitions
- **`twoStateQ (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : QMatrix (Fin 2)`** — 2-state birth-death Q-matrix with birth rate `a` (0→1) and death rate `b` (1→0). Matrix form: `[[-a, a], [b, -b]]`.
- **`twoStationary (ha : 0 < a) (hb : 0 < b) : Distribution (Fin 2)`** — stationary distribution π(0) = b/(a+b), π(1) = a/(a+b).

### Theorems
- `twoStateQ_exitRate_zero` — exit rate from state 0 equals `a`
- `twoStateQ_exitRate_one` — exit rate from state 1 equals `b`
- `twoStateQ_row_sum_zero` — row sums are zero (specializes generic theorem)
- `twoStateQ_absorbing_zero` / `twoStateQ_absorbing_one` — absorbing iff rate = 0
- `twoState_detailedBalance` — stationary distribution satisfies detailed balance
- `twoState_isStationary` — stationary distribution is stationary

### Proof technique
- `fin_cases` enumerates `Fin 2` (4 state pairs)
- `dec_trivial` handles finite Finset equalities on `Fin 2`
- `positivity` handles nonnegativity of ratios in stationary distribution

## Build

```
$ ~/.elan/bin/lake build Ripple.CTMC.TwoState
Build completed successfully (2716 jobs).
```

Zero errors. Also fixed `CTMC.lean:209` (`HasDerivAt.sum` Finset parameter name: `u := Finset.univ`) and `DTMC.lean` ENNReal import for `mul_pos`.
