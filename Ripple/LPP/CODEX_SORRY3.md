# Codex Spec: Fill sorry 3 in gammaCompiled_confinement_norm_le

## Target

File: `Ripple/LPP/ExampleGammaCompiled.lean` (around line 3760)

Replace the SINGLE remaining sorry (the `hA_bound` have-statement) with a complete proof.

The sorry looks like:
```lean
  have hA_bound : ‖M.frozenMartingalePart M.canonicalPathMap s records -
      M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ≤
      484 * (1 + 2 * T ^ 2 + 2 * T) * S := by sorry
```

where `M := DensityDepCTMC.mk N hN gammaCompiledRateSpec` and
`S := Real.sqrt (⨆ (u : ℝ) (_ : 0 ≤ u ∧ u ≤ T), ‖M.frozenGeneratorMartingalePart M.canonicalPathMap u records‖ ^ 2)`.

Available context (already in scope when sorry runs):
- `hT : 0 < T`
- `hN : 0 < N`, `hN484 : 484 < N`
- `x₀ : Fin 21 → Fin (N + 1)`, `hinit : M.InSimplex x₀`
- `hclose : ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - gammaCompiledInit‖ ≤ 1 / ↑N`
- `records : M.canonicalRecordΩ`, `hrec : (records 0).2 = x₀`
- `hsim : ∀ n, M.InSimplex ((M.canonicalPathMap records).stateSeq n)`
- `h19const : ∀ n, (M.canonicalPathMap records).stateSeq n 19 = x₀ 19`
- `s : ℝ`, `hs0 : 0 ≤ s`, `hsT : s ≤ T`
- `hy19 : (1 : ℝ) / 484 ≤ (↑(x₀ 19) : ℝ) / ↑N`
- `hS_nn : 0 ≤ S`
- `hS_bound : ∀ u, 0 ≤ u → u ≤ T → ∀ i, |M.frozenGeneratorMartingalePart M.canonicalPathMap u records i| ≤ S`
- `hG_bdd : BddAbove ...` (BddAbove for the ciSup defining S)

## Proof Strategy

### Overview
Write **helper lemmas ABOVE** the main lemma to break the proof into steps.
The main sorry fills as: apply helpers in sequence.

### Step 1: Almost-BC decomposition

Prove a helper that bounds |genDrift_i(x) - drift_i(y)| on simplex:

```lean
private lemma gammaCompiled_genDrift_sub_drift_le (N : ℕ) (hN : 0 < N)
    (x : Fin 21 → Fin (N + 1))
    (hx : (DensityDepCTMC.mk N hN gammaCompiledRateSpec).InSimplex x) (i : Fin 21) :
    let M := DensityDepCTMC.mk N hN gammaCompiledRateSpec
    |M.generatorDrift x i - gammaCompiledRateSpec.drift (M.scaledState x) i| ≤
    if (x 9 : ℕ) = 0 then gammaCompiledRate 22 (M.scaledState x) else 0
```

Proof approach for this helper:

**Case 1: x 9 ≠ 0 (off boundary).**
At off-boundary states, ALL 32 reactions are either feasible or have zero rate on simplex.
This means the system IS boundary-compatible at this specific state.

Rather than using the global `BoundaryCompatibleOnSimplex` theorem (which requires BC for ALL states),
reproduce the calc chain from `generatorDrift_eq_rateSpec_drift_of_boundaryCompatible` 
(DensityDependent.lean:8037-8083):

```
genDrift_i(x) = ∑_y offDiagRate(x,y)·(scaledState(y)-scaledState(x))_i          -- definition
= ∑_y ∑_{matching ℓ} ℓ_i · rate(ℓ, y)                                           -- by offDiagRate_mul_scaledState_sub_apply_eq_sum_jumps
= ∑_ℓ ∑_y [if match then ℓ_i·rate else 0]                                       -- Finset.sum_comm
= ∑_ℓ [if feasible then ℓ_i·rate else 0]                                        -- by sum_matchingStates_const_eq_ite_exists
= ∑_ℓ ℓ_i·rate  = drift_i                                                       -- BC kills infeasible (this step differs for case 2)
```

For the BC kill step (the last one), for each infeasible ℓ:
- If ℓ = jumpProd j (some k < 16): infeasible iff x₂₀ = 0. Then y₂₀ = x₂₀/N = 0, 
  and `gammaCompiledRate_of_y20_eq_zero` gives rate = 0.
- If ℓ = jumpDegr j (some k ≥ 16): infeasible iff x_j = 0. For j ≠ 9 (k ≠ 22),
  `gammaCompiledRate_degraded_eq_zero_of_ne_22` gives rate = 0.
- For k = 22 (jumpDegr 9): infeasible iff x₉ = 0. But x₉ ≥ 1 in this case. So NOT infeasible.

Therefore genDrift = drift. The RHS (if x₉ ≠ 0 then ... else 0) simplifies to 0. Abs bound is trivial.

**Case 2: x 9 = 0 (on boundary).**
Same calc chain as above, but the last step keeps the reaction 22 term:

genDrift_i = ∑_ℓ [if feasible then ℓ_i·rate else 0]
           = ∑_{ℓ ≠ jump(22)} ℓ_i·rate + [if feasible(22) then jump(22)_i·rate(22) else 0]

Since x₉ = 0: feasible(22) = False. So the last term is 0.
For ℓ ≠ jump(22): same BC argument as case 1 (all infeasible ≠ 22 have zero rate).
So: genDrift_i = ∑_ℓ ℓ_i·rate - jump(22)_i·rate(22) = drift_i - jump(22)_i·rate(22)

Therefore: |genDrift_i - drift_i| = |jump(22,i)·rate(22)| ≤ rate(22) (since |jump(22,i)| ≤ 1 by gammaCompiledJump_22_abs_le_one).

IMPORTANT API for the calc chain:
- `M.offDiagRate_mul_scaledState_sub_apply_eq_sum_jumps x y i` (DensityDependent.lean:1903)
- `Finset.sum_comm` (swap sum order)
- `M.sum_matchingStates_const_eq_ite_exists x ℓ val` (DensityDependent.lean:1657)
- `gammaCompiledRate_of_y20_eq_zero` (same file, ~line 3594)
- `gammaCompiledRate_degraded_eq_zero_of_ne_22` (same file, ~line 3605)
- `gammaCompiledJump_22_abs_le_one` (same file, ~line 3632)

For the "all infeasible except 22 have zero rate" step, you need to case-split on the ℓ value 
(which ℓ in jumps is infeasible and has nonzero rate?). Since jumps = Finset.image gammaCompiledJump univ,
each ℓ corresponds to some k : Fin 32. Case split: k < 16 (jumpProd, use y₂₀=0), 
16 ≤ k < 32 ∧ k ≠ 22 (jumpDegr j≠9, use degraded=0), k = 22 (the special case).

WARNING: DO NOT use `fin_cases` on ℓ or try to enumerate all jump directions.
Instead, work with k : Fin 32 (reaction index). The jumps Finset is the image of gammaCompiledJump.
Sum over ℓ ∈ jumps can be rewritten as sum over k : Fin 32 by `Finset.sum_image` 
(if all gammaCompiledJump values are distinct, which they are for this system).

### Step 2: Integral bound

From Step 1 and `frozenMartingalePart_sub_frozenGeneratorMP`:

(M-M*)_i(s) = ∫₀ˢ genDrift_i du - ∫₀ˢ drift_i du

So: |(M-M*)_i(s)| ≤ ∫₀ˢ |genDrift_i - drift_i| du 
                    ≤ ∫₀ˢ rate_22(y(u)) · 1_{x₉(u)=0} du =: A(s)

And: ‖M-M*‖(s) ≤ A(s) ≤ A(T) (since integrand ≥ 0 and s ≤ T)

### Step 3: Bound A(T) ≤ 484·(1+2T²+2T)·S via boundary integral

On boundary (x₉ = 0):
- rate_22(y) = y₈·y₂₀·y₁₉ (since y₉ = 0)
  Specifically: gammaCompiledRate 22 y = y 9 * y 20 * y 19 + y 8 * y 20 * y 19.
  When y 9 = 0: rate_22 = y 8 * y 20 * y 19
- genDrift₉ on boundary = rate_7(y) = y₂₀·y₁₉² 
  (reaction 7 is the only feasible reaction touching species 9 on boundary)
  Specifically: gammaCompiledRate 7 y = y 9 * y 8 * y 20 + y 20 * y 19 * y 19
  When y 9 = 0: rate_7 = y 20 * y 19 * y 19 = y₂₀·y₁₉²
- Ratio: rate_22 / genDrift₉ = y₈·y₂₀·y₁₉ / (y₂₀·y₁₉²) = y₈/y₁₉
  With y₈ ≤ 1 (on simplex) and y₁₉ ≥ 1/484 (from hy19 + h19const): y₈/y₁₉ ≤ 484
- So rate_22 ≤ 484·genDrift₉ on boundary

Therefore: A(T) ≤ 484 · ∫₀ᵀ genDrift₉·1_{boundary} du

To bound ∫₀ᵀ genDrift₉·1_{boundary}:
Apply `scratch_boundary_bound` (PathwiseBound.lean:137) with:
- g(u) = genDrift₉(x(u))  [where x(u) = (M.canonicalPathMap records).frozenStateAt u]
- B = {u : (frozenStateAt u) 9 = 0}
- T = T
- S_bb = S (at boundary times u: ∫₀ᵘ genDrift₉ = y₉(u) - y₉(0) - M*₉(u) = 0 - y₉(0) - M*₉(u) ≤ |M*₉(u)| ≤ S)
- εs = 2·S·(T+1) (off-boundary lower bound on genDrift₉)
- Cg = 2 (crude bound: |genDrift₉| ≤ rate_7 + rate_22 ≤ 1 + 1 = 2)

To verify εs: Off boundary (x₉ ≥ 1), genDrift₉ = rate_7 - rate_22 = y₂₀·(y₈-y₁₉)·(y₉-y₁₉).
When negative: both y₈-y₁₉ and y₉-y₁₉ have opposite signs.
The worst case is y₈ < y₁₉, y₉ > y₁₉: |genDrift₉| = y₂₀·(y₁₉-y₈)·(y₉-y₁₉) ≤ y₁₉·(y₉-y₁₉).
From pathwise cap on y₉ (see below): y₉ ≤ y₁₉ + 2S(T+1). So y₉-y₁₉ ≤ 2S(T+1).
And y₁₉ ≤ 1. So |genDrift₉| ≤ 2S(T+1).
Other case (y₈ > y₁₉, y₉ < y₁₉): |genDrift₉| ≤ (y₈-y₁₉)·y₁₉ ≤ 2S·1 = 2S ≤ 2S(T+1).

So genDrift₉ ≥ -2S(T+1) = -εs. ✓

Pathwise cap on y₈: Apply `scratch_pathwise_cap` (PathwiseBound.lean:9) with:
- φ(t) = frozenDensityProcess_8(t) = (frozenStateAt t 8 : ℝ)/N
- g(t) = genDrift₈(x(t))
- β = (x₀ 19 : ℝ)/N (= y₁₉, constant from h19const)
- κ = 0
- S_cap = S
- Cg_cap = 2

When φ > β (y₈ > y₁₉): genDrift₈ = rate_6 - rate_21 = y₂₀·y₁₉² - y₈·y₂₀·y₁₉ = y₂₀·y₁₉·(y₁₉-y₈) ≤ 0 = κ. ✓
φ(0) = gammaCompiledInit 8 + O(1/N) ≤ 1/N ≤ 1/484 ≤ y₁₉ = β. ✓
Residual: |φ(t) - φ(0) - ∫₀ᵗ g| = |M*₈(t)| ≤ S. ✓

Result: y₈(t) ≤ y₁₉ + 0·T + 2S = y₁₉ + 2S.

Pathwise cap on y₉ (for εs): Apply `scratch_pathwise_cap` with:
- φ(t) = frozenDensityProcess_9(t)
- g(t) = genDrift₉(x(t))
- β = (x₀ 19 : ℝ)/N = y₁₉
- κ = 2S (from y₈ cap: when y₉ > y₁₉, genDrift₉ = y₂₀·(y₈-y₁₉)·(y₉-y₁₉) ≤ 2S·1 = 2S)
  Wait, more carefully: genDrift₉ = y₂₀·(y₈-y₁₉)·(y₉-y₁₉).
  When y₉ > y₁₉ (φ > β): two cases for y₈:
    y₈ ≤ y₁₉: genDrift₉ = y₂₀·(neg)·(pos) ≤ 0 ≤ κ. ✓
    y₈ > y₁₉: genDrift₉ = y₂₀·(y₈-y₁₉)·(y₉-y₁₉) ≤ 2S·(y₉-y₁₉) ≤ 2S·1 = 2S = κ (since y₉-y₁₉ ≤ y₉ ≤ 1). ✓
- S_cap = S
- Cg_cap = 2

Result: y₉(t) ≤ y₁₉ + 2S·T + 2S = y₁₉ + 2S(T+1).

scratch_boundary_bound result: ∫_{B∩[0,T]} genDrift₉ ≤ S + 2S(T+1)·T = S·(1+2T²+2T).

### Final assembly

A(T) ≤ 484 · ∫_{B∩[0,T]} genDrift₉ ≤ 484 · S · (1+2T²+2T).
‖M-M*‖(s) ≤ A(s) ≤ A(T) ≤ 484 · (1+2T²+2T) · S. ✓

## CRITICAL notes

### frozenDensityProcess vs frozenStateAt

- `M.frozenDensityProcess pathMap t ω i = ((pathMap ω).frozenStateAt t i : ℝ) / M.N`
  This is the DENSITY (in [0,1]).
- `(pathMap ω).frozenStateAt t i` is the discrete COUNT (in Fin (N+1)).
- genDrift operates on discrete states x : Fin d → Fin (N+1).
- drift operates on densities y : Fin d → ℝ.
- scaledState x i = (x i : ℝ) / N = frozenDensityProcess value.

### h19const gives stateSeq, need frozenStateAt

h19const says: `(M.canonicalPathMap records).stateSeq n 19 = x₀ 19`

frozenStateAt is piecewise constant with values from stateSeq:
`(path).frozenStateAt t = (path).stateSeq ((path).stateIndex t)`

So h19const gives: `(frozenStateAt t) 19 = x₀ 19` for all t (via stateIndex).
You may need to establish this connection explicitly.

### Integral subtraction

`frozenMartingalePart_sub_frozenGeneratorMP` gives a COMPONENT-WISE identity:
```
(M_i - M*_i)(s) = ∫₀ˢ genDrift_i du - ∫₀ˢ drift_i du
```

The integral is over `Set.Icc 0 s` (or equivalently `Set.Icc (0:ℝ) s`).

To go from |∫ (f-g)| ≤ ∫ |f-g|, use triangle inequality for integrals:
`norm_integral_le_integral_norm` or similar.

### Measurability of g = genDrift₉(frozenStateAt)

frozenStateAt is piecewise constant → g is piecewise constant → measurable and integrable.
Use `CTMCPath.frozenStateAt_measurable` or similar if available.
If not available, the piecewise constant structure gives measurability directly.

### Rate nonnegativity

`gammaCompiledRate k y ≥ 0` for y in [0,1]^d (all products of nonneg terms).
Use `gammaCompiledRateSpec.rate_nonneg` or prove inline.

### Species 8 and 9 genDrift structure

For species 8 (reactions 6 = jumpProd 8 and 21 = jumpDegr 8):
- gammaCompiledRate 6 y = y 20 * y 19 * y 19 (= y₂₀·y₁₉²)
- gammaCompiledRate 21 y = y 8 * y 20 * y 19
- gammaCompiledJump 6 = jumpProd 8: species 8 +1, species 20 -1
- gammaCompiledJump 21 = jumpDegr 8: species 8 -1, species 20 +1
- On simplex when all reactions feasible: genDrift₈ = rate_6 - rate_21 = y₂₀·y₁₉·(y₁₉-y₈)

For species 9 (reactions 7 = jumpProd 9 and 22 = jumpDegr 9):
- gammaCompiledRate 7 y = y 9 * y 8 * y 20 + y 20 * y 19 * y 19
- gammaCompiledRate 22 y = y 9 * y 20 * y 19 + y 8 * y 20 * y 19
- gammaCompiledJump 7 = jumpProd 9: species 9 +1, species 20 -1
- gammaCompiledJump 22 = jumpDegr 9: species 9 -1, species 20 +1
- On simplex all feasible: genDrift₉ = rate_7 - rate_22 = y₂₀·((y₈-y₁₉)·(y₉-y₁₉))

## PRACTICAL ADVICE

1. **Start with the helper `gammaCompiled_genDrift_sub_drift_le`.** This is the critical piece.
   If you can prove this helper, the rest is integration/arithmetic.

2. **For the calc chain in the helper**: Follow the EXACT structure of 
   `generatorDrift_eq_rateSpec_drift_of_boundaryCompatible` (DensityDependent.lean:8037-8083).
   The first 4 calc steps are IDENTICAL. Only the last step differs.

3. **For the "only reaction 22" step**: After getting 
   `genDrift_i = ∑_ℓ [if feasible then ℓ_i·rate else 0]`,
   subtract drift: `genDrift_i - drift_i = -∑_{infeasible ℓ} ℓ_i·rate`.
   Then show: for each infeasible ℓ with ℓ ≠ jump(22), rate = 0.
   This uses `gammaCompiledRate_of_y20_eq_zero` (for jumpProd) and
   `gammaCompiledRate_degraded_eq_zero_of_ne_22` (for jumpDegr k ≠ 22).

4. **If the full calc chain is too hard**, use a FALLBACK: 
   prove `genDrift = drift` when x₉ ≥ 1 (case split: off-boundary = BC, so genDrift = drift).
   For x₉ = 0: use crude bounds on |genDrift_i| and |drift_i| separately, 
   both ≤ const·max_rate, and show the difference ≤ rate_22.

5. **For scratch_pathwise_cap instantiation**: The hardest hypotheses are:
   - `hφmeas : Measurable φ` — φ is frozenDensityProcess component, piecewise constant
   - `hgint : IntegrableOn g (Set.Icc 0 T)` — g is genDrift component, piecewise constant
   - `hres : ∀ t, |φ t - φ 0 - ∫₀ᵗ g| ≤ S` — this IS |M*_i(t)| ≤ S
   If measurability is hard, you may sorry it and move on.

6. **The integral over boundary B** in scratch_boundary_bound needs:
   - `hBmeas : MeasurableSet B` where B = {u : (frozenStateAt u) 9 = 0}
   - frozenStateAt is piecewise constant → B is a finite union of intervals → measurable
   If this is hard, sorry it.

7. **Priority order**: 
   (a) Prove the helper `gammaCompiled_genDrift_sub_drift_le` (MOST IMPORTANT)
   (b) Wire up the integral bound using the helper
   (c) Instantiate scratch_boundary_bound
   (d) Instantiate scratch_pathwise_cap for y₈ and y₉
   (e) Combine everything

   If any step is too hard, leave it as a sorry in a NAMED intermediate have-statement
   and move to the next step. It's better to have 3 small sorry's than 1 big one.

## Build instructions

- DO NOT run `lake build` locally. Only on remote.
- Push: `cd /Users/huangx/repos/Ripple && git add -A && git commit -m "WIP" && git push`
- Build: `ssh uisai2 "cd ~/repos/Ripple && git pull && export PATH=\$HOME/.elan/bin:\$PATH && lake build 2>&1"`
- Quick: `ssh uisai2 "cd ~/repos/Ripple && git pull && export PATH=\$HOME/.elan/bin:\$PATH && lake env lean Ripple/LPP/ExampleGammaCompiled.lean 2>&1 | tail -40"`

## Hard rules

- **No native_decide** — banned
- **No axiom** — banned
- **sorry is OK for intermediate steps** — but label each sorry clearly
- maxHeartbeats can be increased up to 6400000 if needed
- Lean 4 + Mathlib 4
