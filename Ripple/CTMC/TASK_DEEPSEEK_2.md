# Task for DeepSeek: CTMC Process Construction

## Context

We have built CTMC infrastructure in Lean 4 (Ripple project):
- `DTMC.lean` — 0 sorry, DTMC with PMF, Chapman-Kolmogorov
- `CTMC.lean` — 0 sorry, Q-matrix, embedded DTMC, transition semigroup P(t)=exp(tQ), Kolmogorov forward
- `DensityDependent.lean` — 6 sorry, density-dependent CTMC structure + bridge to Kurtz

## Your Task: Create `CTMCProcess.lean`

Create a new file `Ripple/CTMC/CTMCProcess.lean` with the jump-and-hold CTMC construction.

### 1. CTMC path type

```lean
import Ripple.CTMC.CTMC

namespace Ripple.CTMC

/-- A CTMC path: sequence of (holding time, next state) pairs.
The path starts at state `init` and follows the embedded DTMC
with exponential holding times. -/
structure CTMCPath (S : Type*) where
  init : S
  jumps : ℕ → S     -- state after n-th jump
  times : ℕ → ℝ     -- time of n-th jump (cumulative)
```

### 2. State at time t

```lean
/-- The state of the CTMC at time t: find the last jump before t. -/
noncomputable def CTMCPath.stateAt (path : CTMCPath S) (t : ℝ) : S :=
  -- If t < times 0, state is init
  -- Otherwise, find largest n such that times n ≤ t
  sorry -- use Nat.find or similar
```

### 3. Connect to Q-matrix

```lean
/-- A CTMC path is compatible with a Q-matrix if:
- Holding times are exponential with rate exitRate(current state)
- Jumps follow the embedded DTMC -/
def CTMCPath.IsCompatible (path : CTMCPath S) (Q : QMatrix S) : Prop :=
  -- Jump times are increasing
  (∀ n, path.times n < path.times (n + 1)) ∧
  -- The sequence of states follows the jump chain
  True -- placeholder
```

### 4. Fix DTMC.lean linter warning

In `DTMC.lean`, line 49 has a `show` that should be `change`:
```lean
-- Change this:
    show mc.stepN (m + n + 1) s = _
-- To this:
    change mc.stepN (m + n + 1) s = _
```

## Build Command

```bash
cd /Users/huangx/.openclaw/workspace/projects/Ripple
~/.elan/bin/lake build Ripple.CTMC.CTMCProcess
```

## Rules

- Run `lake build` after every change — MUST compile
- No `axiom` declarations
- `sorry` is OK for hard definitions/proofs
- Keep it simple — definitions are more important than proofs
- When done, write summary to `Ripple/CTMC/DEEPSEEK_DONE_2.md`
