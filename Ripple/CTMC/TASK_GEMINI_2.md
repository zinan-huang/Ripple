# Task for Gemini: Prove kolmogorov_forward in CTMC.lean

## Context

File: `Ripple/CTMC/CTMC.lean`

The `transitionProb` definition is now filled in using matrix exponential:

```lean
attribute [local instance] Matrix.normedAddCommGroup

open NormedSpace in
noncomputable def QMatrix.transitionProb (Q : QMatrix S) (t : ℝ) (s u : S) : ℝ :=
  exp (t • (Matrix.of Q.rate)) s u
```

The remaining sorry is `kolmogorov_forward`:

```lean
theorem QMatrix.kolmogorov_forward (Q : QMatrix S) (s u : S) :
    ∀ t ≥ 0, HasDerivAt (fun t => Q.transitionProb t s u)
      (∑ v, Q.transitionProb t s v * Q.rate v u) t :=
  sorry
```

## Proof Strategy

1. Use `hasDerivAt_exp_smul_const` from `Mathlib.Analysis.SpecialFunctions.Exponential`:
   ```
   HasDerivAt (fun u => exp (u • x)) (exp (t • x) * x) t
   ```
   This gives: d/dt exp(t·Q) = exp(t·Q) · Q as matrices.

2. The entry-wise version (which is our goal) says:
   ```
   d/dt [exp(t·Q)]_{su} = [exp(t·Q) · Q]_{su} = ∑_v [exp(t·Q)]_{sv} · Q_{vu}
   ```

3. Key steps:
   - Need `attribute [local instance] Matrix.normedAddCommGroup` for exp to work
   - Use `HasDerivAt.comp` or `ContinuousLinearMap.hasFDerivAt` to extract the (s,u) entry
   - The entry extraction `(· s u) : Matrix S S ℝ → ℝ` is a continuous linear map
   - Matrix multiplication entry: `(A * B) s u = ∑ v, A s v * B v u`

## Key Mathlib Lemmas

- `hasDerivAt_exp_smul_const` in `Mathlib.Analysis.SpecialFunctions.Exponential` (line 384)
- `Matrix.mul_apply` — entry of matrix product as sum
- `Matrix.of_apply` — `Matrix.of f i j = f i j`
- `ContinuousLinearMap.hasDerivAt` for composing with linear maps
- You may need `HasDerivAt.comp` to extract entries

## Important

- The `transitionProb` is defined inside `section TransitionSemigroup` with `attribute [local instance] Matrix.normedAddCommGroup`
- `open NormedSpace` is used for `exp`
- The proof of `kolmogorov_forward` is also inside this section

## Build Command

```bash
cd /Users/huangx/.openclaw/workspace/projects/Ripple
~/.elan/bin/lake build Ripple.CTMC.CTMC
```

## Rules

- Run `lake build` after every change — MUST compile
- No `axiom` declarations
- Keep the proof inside `section TransitionSemigroup`
- If stuck after 3 attempts, write your best attempt with sorry and a comment explaining the blocker
- When done, write to `Ripple/CTMC/GEMINI_DONE_2.md`
