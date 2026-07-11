# Task for DeepSeek: TwoState CTMC Example + Backward Kolmogorov

## Context

We have a CTMC module in Lean 4 (Ripple project) with:
- `CTMC.lean` — 0 sorry: Q-matrix, exit rates, embedded DTMC, P(t)=exp(tQ), Kolmogorov forward, P(0)=I, P(s+t)=P(s)·P(t)
- `CTMCProcess.lean` — 0 sorry: CTMCPath, stateAt, stateAt_between
- `DensityDependent.lean` — 2 sorry: pathMap (Ionescu-Tulcea), martingale_qv_bound

## Your Task: Create `Ripple/CTMC/TwoState.lean`

Create a concrete 2-state CTMC example demonstrating the infrastructure works.

### 1. Define a 2-state birth-death Q-matrix

```lean
import Ripple.CTMC.CTMC

namespace Ripple.CTMC

/-- A two-state CTMC with birth rate λ and death rate μ.
State 0 = "off", State 1 = "on".
Transitions: 0 →(λ) 1, 1 →(μ) 0. -/
noncomputable def twoStateQ (λ μ : ℝ) (hλ : 0 ≤ λ) (hμ : 0 ≤ μ) :
    QMatrix (Fin 2) where
  rate := ![![-λ, λ], ![μ, -μ]]
  -- OR define rate as a function:
  -- rate s t := if s = 0 ∧ t = 1 then λ else if s = 1 ∧ t = 0 then μ else ...
  rate_nonneg := by ...
  rate_diag := by ...
```

Use `Fin 2` as the state space. You may use `Matrix.of` or `![]` notation, whichever compiles easier.

### 2. Prove basic properties

```lean
/-- Exit rate from state 0 is λ. -/
theorem twoStateQ_exitRate_zero : (twoStateQ λ μ hλ hμ).exitRate 0 = λ := by ...

/-- Exit rate from state 1 is μ. -/  
theorem twoStateQ_exitRate_one : (twoStateQ λ μ hλ hμ).exitRate 1 = μ := by ...

/-- Row sum is zero. -/
-- This should follow from QMatrix.row_sum_zero, just instantiate
```

### 3. Explicit transition matrix for 2 states

The 2-state transition matrix P(t) has the closed form:
```
P(t) = 1/(λ+μ) * [[μ + λ·e^{-(λ+μ)t}, λ - λ·e^{-(λ+μ)t}],
                     [μ - μ·e^{-(λ+μ)t}, λ + μ·e^{-(λ+μ)t}]]
```

State this as a theorem (proof can use sorry if the matrix exponential computation is hard):
```lean
theorem twoState_transitionProb_explicit (hne : λ + μ ≠ 0) (t : ℝ) :
    (twoStateQ λ μ hλ hμ).transitionProb t 0 0 = 
      (μ + λ * Real.exp (-(λ + μ) * t)) / (λ + μ) := by
  sorry -- matrix exponential computation
```

## Build Command

```bash
cd /Users/huangx/.openclaw/workspace/projects/Ripple
~/.elan/bin/lake build Ripple.CTMC.TwoState
```

## Rules

- Run `lake build` after every change — MUST compile
- No `axiom` declarations
- `sorry` is OK for hard proofs (especially the explicit P(t) formula)
- Keep it simple — definitions and basic properties first
- When done, write summary to `Ripple/CTMC/DEEPSEEK_DONE_3.md`
