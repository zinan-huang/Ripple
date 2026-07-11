# Codex Spec: Fill S3.2-S3.7 and S3.9 in ExampleGammaCompiled.lean

Target file: `Ripple/LPP/ExampleGammaCompiled.lean`
Build: `export PATH=$HOME/.elan/bin:$PATH && lake env lean Ripple/LPP/ExampleGammaCompiled.lean 2>&1`

## Context

S3.1 (almost-BC) is CLOSED (line 3724-4070). All 6 remaining sorry's are in
`gammaCompiled_confinement_norm_le_core` (S3.2-S3.7) and
`gammaCompiled_drift_mismatch_pathwise` (S3.9).

Available hypotheses in `gammaCompiled_confinement_norm_le_core`:
- `hT : 0 < T`, `hN : 0 < N`, `hN484 : 484 < N`
- `x₀ : Fin 21 → Fin (N + 1)`, InSimplex and closeness
- `M := DensityDepCTMC.mk N hN gammaCompiledRateSpec`
- `y : ℝ → Fin 21 → ℝ := fun u => M.frozenDensityProcess M.canonicalPathMap u records`
- `x : ℝ → Fin 21 → Fin (N + 1) := fun u => (M.canonicalPathMap records).frozenStateAt u`
- `boundaryRate : ℝ → ℝ := fun u => if ((x u 9 : ℕ) = 0) then gammaCompiledRate 22 (y u) else 0`
- `h_almost_bc : ∀ u i, |genDrift(x u, i) - drift(y u, i)| ≤ boundaryRate u`
- `hS_bound : ∀ u i, 0 ≤ u → u ≤ T → |M*.frozenGeneratorMartingalePart ... u records i| ≤ S`
- `h_frozen19 : ∀ u, y u 19 = (x₀ 19 : ℝ) / N`
- `hy19 : 1/484 ≤ (x₀ 19 : ℝ) / N`
- `hS_nn : 0 ≤ S`

Key imports already present: PathwiseBound.lean has `scratch_pathwise_cap` and `scratch_boundary_bound`.

## S3.2: h_drift_mismatch_to_boundary (line 4114)

**Goal:**
```lean
‖M.frozenMartingalePart M.canonicalPathMap s records -
  M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ≤
  ∫ u in Set.Icc (0 : ℝ) T, boundaryRate u
```

**Proof route:**
1. Use `frozenMartingalePart_sub_frozenGeneratorMP` (DensityDependentAbsorbing.lean:270):
   `(M - M*)_i(s) = ∫₀ˢ (genDrift_i - drift_i) du`
2. For each component i: `|(M-M*)_i| = |∫₀ˢ (genDrift_i - drift_i) du| ≤ ∫₀ˢ |genDrift_i - drift_i| du`
3. Use `h_almost_bc`: `|genDrift_i - drift_i| ≤ boundaryRate u` (uniform in i)
4. So `|(M-M*)_i| ≤ ∫₀ˢ boundaryRate du ≤ ∫₀ᵀ boundaryRate du` (monotonicity: s ≤ T)
5. Take norm: `‖M-M*‖ ≤ ∫₀ᵀ boundaryRate du`

**Key API:**
- `frozenMartingalePart_sub_frozenGeneratorMP` — gives component-wise integral representation
- `pi_norm_le_iff` or `norm_le_pi_norm` — relate sup norm to components
- `norm_integral_le_integral_norm` — |∫ f| ≤ ∫ |f|
- `setIntegral_mono_set` — monotonicity for nonneg integrands

## S3.4: h_y8_cap (line 4124)

**Goal:** `∀ u, 0 ≤ u → u ≤ T → y u 8 ≤ y u 19 + 2 * S`

**Proof:** Instantiate `scratch_pathwise_cap`:
- `φ := fun u => y u 8`, `g := fun u => M.generatorDrift (x u) 8`
- `β := (x₀ 19 : ℝ) / N` (= y u 19 for all u, by h_frozen19)
- `κ := 0` (drift₈ ≤ 0 when y₈ > y₁₉)
- `S := S`, `Cg` = some bound on |generatorDrift₈| (from bounded rates)
- Result: φ t ≤ β + 0·T + 2S = y₁₉ + 2S ✓

**Key facts for hg:**
When y₈ > y₁₉ and x₉ ≠ 0 (so genDrift₈ = drift₈):
  drift₈ = y₂₀·y₁₉·(y₁₉ - y₈) ≤ 0 since y₁₉ - y₈ < 0.
When x₉ = 0: genDrift₈ = drift₈ + (jump(22)₈) · rate₂₂.
  But jump(22)₈ = 0 (reaction 22 = jumpDegr 9, doesn't touch species 8).
  So genDrift₈ = drift₈ ≤ 0 same argument.

**Key fact for h0:** `y 0 8 ≤ y 0 19`. This follows from `hrec` (records 0).2 = x₀`,
so `y 0 8 = x₀ 8 / N` and `y 0 19 = x₀ 19 / N`. At `gammaCompiledInit`:
  init₈ = 0, init₁₉ = 1/484 > 0. With `‖y₀ - init‖ ≤ 1/N` and N > 484:
  y₀8 ≤ init₈ + 1/N = 1/N < 1/484 ≤ y₀19.

**Key fact for hres:** `|y u 8 - y 0 8 - ∫₀ᵘ genDrift₈| = |M*₈(u)|` ≤ S.
  This is exactly hS_bound applied to component 8.

## S3.5: h_y9_cap (line 4127)

**Goal:** `∀ u, 0 ≤ u → u ≤ T → y u 9 ≤ y u 19 + 2 * S * T + 2 * S`

**Proof:** Same as S3.4 but κ = 2 * S:
- `φ := fun u => y u 9`, `g := fun u => M.generatorDrift (x u) 9`
- `β := (x₀ 19 : ℝ) / N`, `κ := 2 * S`, `S := S`
- hg: when y₉ > y₁₉, we have x₉ ≥ 1 (so x₉ ≠ 0), thus genDrift₉ = drift₉.
  drift₉ = y₂₀·(y₈ - y₁₉)·(y₉ - y₁₉).
  From h_y8_cap: y₈ - y₁₉ ≤ 2S.
  From density ∈ [0,1]: y₉ - y₁₉ ≤ y₉ ≤ 1, and y₂₀ ≤ 1.
  When y₈ ≥ y₁₉: drift₉ ≤ 1 · 2S · 1 = 2S. ✓
  When y₈ < y₁₉: (y₈-y₁₉) < 0 and (y₉-y₁₉) > 0, so drift₉ ≤ 0 ≤ 2S. ✓
- Result: φ t ≤ β + 2S·T + 2S ✓

## S3.6: h_boundary_rate_to_drift9 (line 4134)

**Goal:**
```lean
(∫ u in Set.Icc 0 T, boundaryRate u) ≤
  484 * (∫ u in Set.Icc 0 T ∩ {u | (x u 9 : ℕ) = 0}, M.generatorDrift (x u) 9)
```

**Proof:** Pointwise on the boundary {x₉ = 0}:
- `gammaCompiledRate 22 y = y 9 * y 20 * y 19 + y 8 * y 20 * y 19`
- When x₉ = 0: y₉ = 0, so `rate_22 = y₈·y₂₀·y₁₉`
- boundaryRate u = rate_22(y u) = y₈·y₂₀·y₁₉ (the catalyst term)

For genDrift₉ on boundary x₉=0:
  Reaction 22 is NOT feasible (jumpDegr 9 needs x₉ ≥ 1).
  So genDrift₉ = drift₉ (the h_almost_bc residual is subtracted).
  drift₉ = y₂₀·(y₈-y₁₉)·(y₉-y₁₉) = y₂₀·(y₈-y₁₉)·(-y₁₉) (since y₉=0)

Actually, the spec from DNA paper: on boundary x₉=0:
  genDrift₉ = ∑ feasible reactions involving species 9.
  Species 9 appears in jumpProd for reactions that produce species 9.
  Specifically, reaction 7 (jumpProd 7): rate₇ = y₂₀·y₁₉²

So genDrift₉ = (contribution from jumpProd reactions + jumpDegr) to species 9.
The production reactions give positive genDrift₉, and degradation gives 0 (infeasible).

Key ratio on boundary: boundaryRate / genDrift₉.
With y₁₉ ≥ 1/484 (from hy19):
  rate_22 = y₈·y₂₀·y₁₉
  genDrift₉ ≥ y₂₀·y₁₉² (from reaction 7 contribution alone)
  rate_22 / genDrift₉ ≤ y₈/y₁₉ ≤ 1/(1/484) = 484 (using y₈ ≤ 1)

When y₂₀ = 0 or y₁₉ = 0: both terms are 0.
Off boundary: boundaryRate = 0.

## S3.7: h_boundary_genDrift_bound (line 4141)

If the above analysis is correct (boundaryRate ≡ 0), this is trivial.

## S3.9: drift_mismatch_pathwise (line 4351)

**Goal:**
```lean
∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (hN : 0 < N) ... ,
  (sup ‖M-M*‖²) ≤ K * (sup ‖M*‖²) + K / N²
```

**Proof (Finset.sup' trick — NO new uniform bounds needed):**

1. For N > 484: use `gammaCompiled_confinement_pointwise` to get
   `‖M-M*‖²(s) ≤ C²·sup‖M*‖²` where C = 484²·(1+2T²+2T)².
   Take iSup: `sup ‖M-M*‖² ≤ C²·sup‖M*‖² ≤ K·sup‖M*‖² + K/N²`.

2. For N ≤ 484: extract deterministic bound from existing APIs.
   `exists_frozenMartingalePart_norm_bound` + `exists_frozenGeneratorMP_norm_bound`
   give B(N) with `‖M-M*‖²(s) ≤ B(N)` for all s. B(N) depends on N.
   Take `B_max := max over N ∈ [1,484]` using `Finset.sup'`.
   Then `sup ‖M-M*‖² ≤ B_max`. Since N ≤ 484: `K/N² ≥ K/484² ≥ B_max`
   if K ≥ 484²·B_max. So `sup ‖M-M*‖² ≤ K/N²`.

3. `K := max C² (484²·B_max) + 1`.

**Implementation pattern:**
```lean
-- For each N, get a deterministic bound on ‖M-M*‖²
have hdet : ∀ (N : ℕ) (hN : 0 < N), ∃ B, 0 ≤ B ∧ ∀ records s,
    ‖...‖² ≤ B := by
  intro N hN
  -- use exists_frozenMartingalePart_norm_bound + triangle + sq
  sorry -- fill with the deterministic bound extraction
-- Finite max
set B : ℕ → ℝ := fun n => if hn : 0 < n then (hdet n hn).choose else 0
set B_max := (Finset.Icc 1 484).sup' ⟨1, by simp⟩ B
-- K definition
use max ((484 * (1 + 2 * T ^ 2 + 2 * T))^2) (484^2 * B_max) + 1
-- by_cases 484 < N for the two regimes
```

## Build command
```bash
export PATH=$HOME/.elan/bin:$PATH && lake env lean Ripple/LPP/ExampleGammaCompiled.lean 2>&1
```

## Rules
- No `sorry`, `axiom`, `native_decide` in final proof
- If stuck, deliver what compiles + precise stall report describing the exact tactic that fails
- maxHeartbeats may need increasing: use `set_option maxHeartbeats 6400000 in` prefix
