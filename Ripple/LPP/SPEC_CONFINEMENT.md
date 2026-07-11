# Codex Spec: Fill gammaCompiled_confinement_pointwise sorry

## Target
File: `Ripple/LPP/ExampleGammaCompiled.lean`
Find the lemma `gammaCompiled_confinement_pointwise` (currently has `sorry` on its last line).
Replace the `sorry` with a complete proof.

## The lemma to prove
```lean
set_option maxHeartbeats 800000 in
private lemma gammaCompiled_confinement_pointwise {T : ℝ} (hT : 0 < T)
    (N : ℕ) (hN : 0 < N) (hN484 : 484 < N)
    (x₀ : Fin 21 → Fin (N + 1))
    (hinit : (DensityDepCTMC.mk N hN gammaCompiledRateSpec).InSimplex x₀)
    (hclose : ‖(fun i => (↑(x₀ i) : ℝ) / ↑N) - gammaCompiledInit‖ ≤ 1 / ↑N)
    (records : (DensityDepCTMC.mk N hN gammaCompiledRateSpec).canonicalRecordΩ)
    (hrec : (records 0).2 = x₀)
    (s : ℝ) (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    let M := DensityDepCTMC.mk N hN gammaCompiledRateSpec
    ‖M.frozenMartingalePart M.canonicalPathMap s records -
     M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤
    (484 : ℝ) ^ 2 * (1 + 2 * T ^ 2 + 2 * T) ^ 2 *
      (⨆ (u : ℝ) (_ : 0 ≤ u ∧ u ≤ T),
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap u records‖ ^ 2)
```

**NEW hypothesis `hrec`**: `(records 0).2 = x₀` — the record trajectory starts from x₀.
This is needed because `canonicalPathMap records` has `.init = (records 0).2`, so without this,
the CTMC path could start from any lattice state, breaking the y₁₉ ≥ 1/484 bound.
Under `canonicalRecordMeasure x₀`, this holds a.e. by `canonicalRecordMeasure_record_zero_eq_init_ae`.

**How hrec is used**: The key fact is that species 19 is constant along the path, so
`y₁₉(t) = y₁₉(0) = x₀(19)/N`. With `hrec`, we know `.init = (records 0).2 = x₀`,
so `frozenStateAt 0 = x₀` and `y₁₉(0) = x₀(19)/N`. Combined with `hclose`, this gives
`y₁₉ ≥ 1/484` for N > 484.

## Mathematical proof chain

### Definitions
- M = DensityDepCTMC.mk N hN gammaCompiledRateSpec (a CTMC with 21 species, N particles)
- M.frozenMartingalePart: uses rateSpec.drift (abstract ODE drift)
- M.frozenGeneratorMartingalePart: uses M.generatorDrift (finite-lattice generator drift)
- scaledState x i = (x i : ℝ) / N
- generatorDrift x i = ∑_y offDiagRate(x,y) · (scaledState y - scaledState x)_i

### Key identity (already proved at DensityDependentAbsorbing.lean:270)
```
frozenMartingalePart_sub_frozenGeneratorMP:
  (M - M*)_i(s) = ∫₀ˢ genDrift_i(x(u)) du - ∫₀ˢ drift_i(y(u)) du
```

### The proof has 6 steps:

**Step 1: Almost-BC.**
For all 32 reactions, if the reaction is infeasible at state x on simplex AND the reaction
is NOT reaction 22, then its rate vanishes:
- Reactions 0-15 (jumpProd): all rates contain y₂₀ as factor. Infeasible on simplex ⟹ x₂₀=0 ⟹ y₂₀=0 ⟹ rate=0.
- Reactions 16-21,23-31 (jumpDegr j, j≠9): each rate contains y_j as factor. Infeasible ⟹ x_j=0 ⟹ y_j=0 ⟹ rate=0.
- Reaction 22 (jumpDegr 9): rate = y₉·y₂₀·y₁₉ + y₈·y₂₀·y₁₉. At x₉=0: y₉=0 but y₈ term survives.

Consequence: genDrift(x)_i - drift(y)_i = -jump(22)_i · rate(22,y) · 𝟙_{x₉=0}
where jump(22) = jumpDegr 9 (species 9 gets -1, species 20 gets +1).

So |genDrift_i - drift_i| ≤ rate(22,y) · 𝟙_{x₉=0} for ALL i (since |jump(22)_i| ≤ 1).

**Step 2: ‖M-M*‖ ≤ A(s) where A(s) = ∫₀ˢ rate(22,y(u))·𝟙_{x₉(u)=0} du.**
From step 1 + frozenMartingalePart_sub_frozenGeneratorMP:
  |(M-M*)_i(s)| ≤ ∫₀ˢ |genDrift_i - drift_i| ≤ A(s)
  ‖M-M*‖ = max_i |(M-M*)_i| ≤ A(s)

**Step 3: A(s) ≤ A(T) (monotonicity of integral of nonneg function).**

**Step 4: A(T) ≤ 484·√(⨆G)·(1+2T²+2T) via confinement.**
Define S = √(⨆G) where G(u) = ‖M*(u)‖².

4a. Species 19 is constant: gammaCompiledJump k 19 = 0 for all k (no reaction touches species 19).
    The path starts from `(records 0).2 = x₀` (by `hrec`), so `frozenStateAt 0 = x₀`.
    Thus y₁₉ = x₀(19)/N for all t. For N > 484 with hclose: y₁₉ ≥ 1/242 - 1/N ≥ 1/484.

4b. Cap y₈: genDrift₈ = drift₈ = field₈ on simplex (reactions 6 and 21 are BC).
    field₈ = y₂₀·(y₁₉-y₈)·y₁₉. When y₈ > y₁₉: field₈ ≤ 0 (κ=0).
    Process eq: y₈(t) - y₈(0) - ∫genDrift₈ = M*₈(t). Residual ≤ S.
    y₈(0) ≤ 1/N < y₁₉. By scratch_pathwise_cap: y₈(t) ≤ y₁₉ + 2S.

4c. Cap y₉: genDrift₉ = field₉ at interior (x₉>0, all BC there).
    field₉ = y₂₀·(y₈-y₁₉)·(y₉-y₁₉). When y₉ > y₁₉:
    y₈-y₁₉ ≤ 2S from step 4b, y₂₀ ≤ 1, so genDrift₉ ≤ 2S = κ.
    By scratch_pathwise_cap: y₉(t) ≤ y₁₉ + 2S·T + 2S = y₁₉ + 2S(T+1).

4d. Off-boundary lower bound: at interior, genDrift₉ = field₉ ≥ -2S(T+1) = -εs.

4e. Boundary integral bound: at boundary time u (x₉(u)=0):
    y₉(u) = 0, so ∫₀ᵘ genDrift₉ = -y₉(0) - M*₉(u) ≤ S.
    By scratch_boundary_bound: ∫_B genDrift₉ ≤ S + εs·T = S(1+2T²+2T).

4f. A(T) = ∫_B y₈·y₂₀·y₁₉. At boundary: y₈·y₂₀·y₁₉ = (y₈/y₁₉)·(y₂₀·y₁₉²).
    Since genDrift₉ at boundary = y₂₀·y₁₉², we have y₈·y₂₀·y₁₉ = (y₈/y₁₉)·genDrift₉.
    y₈/y₁₉ ≤ 1/(1/484) = 484 (using y₈≤1, y₁₉≥1/484).
    A(T) ≤ 484·∫_B genDrift₉ ≤ 484·S·(1+2T²+2T).

**Step 5: Square.**
F(s) = ‖M-M*‖² ≤ A(T)² ≤ 484²·S²·(1+2T²+2T)² = 484²·(1+2T²+2T)²·S².
And S² = (√(⨆G))² ≤ ⨆G (since ⨆G ≥ 0 and √x² ≤ x for x ≥ 0; also S² = ⨆G exactly).
So F(s) ≤ 484²·(1+2T²+2T)²·⨆G = c·⨆G. ✓

## Recommended proof structure

Write 3-4 helper lemmas ABOVE gammaCompiled_confinement_pointwise, then use them:

### Helper 1: gammaCompiledRate_of_y20_eq_zero
```lean
private lemma gammaCompiledRate_of_y20_eq_zero (k : Fin 32) (y : Fin 21 → ℝ) (hy20 : y 20 = 0) :
    gammaCompiledRate k y = 0
```
Proof: `fin_cases k <;> simp [gammaCompiledRate, hy20, mul_zero, zero_mul, add_zero]`

### Helper 2: gammaCompiledRate_of_degraded_zero
For jumpDegr reactions k ∈ {16,...,31} \ {22}: if the degraded species has y_j = 0, rate = 0.
```lean
private lemma gammaCompiledRate_of_degraded_zero (k : Fin 32) (hk16 : 16 ≤ k.val)
    (hk22 : k ≠ (22 : Fin 32)) (y : Fin 21 → ℝ)
    (hdeg : ∀ j : Fin 21, gammaCompiledJump k j = -1 → y j = 0) :
    gammaCompiledRate k y = 0
```
Proof: fin_cases k, eliminate k < 16 by omega, eliminate k = 22 by contradiction,
for each remaining case: extract y_j = 0 from hdeg (the degraded species j has jump = -1),
then simp with gammaCompiledRate and the zero hypothesis.

Example for k = 16 (jumpDegr 2):
```lean
· have h := hdeg 2 (by simp [gammaCompiledJump, jumpDegr]; split_ifs <;> omega)
  simp [gammaCompiledRate, h, mul_zero, zero_mul]
```

### Helper 3 (optional): gammaCompiledJump_19_eq_zero
```lean
private lemma gammaCompiledJump_19_eq_zero (k : Fin 32) : gammaCompiledJump k 19 = 0
```
Proof: `fin_cases k <;> simp [gammaCompiledJump, jumpProd, jumpDegr]`
(Or in each case, the if-conditions don't match species 19.)

### Main proof structure
```lean
intro M
-- Set up abbreviations
set y := M.frozenDensityProcess M.canonicalPathMap
set genDrift_at := fun u => M.generatorDrift ((M.canonicalPathMap records).frozenStateAt u)
set drift_at := fun u => M.rateSpec.drift (y u records)
-- S² = ⨆G
set supG := ⨆ (u : ℝ) (_ : 0 ≤ u ∧ u ≤ T), ‖M.frozenGeneratorMartingalePart ...‖ ^ 2
-- Get S = √(supG)
set S := Real.sqrt supG
-- Step 2: bound each component
have step2 : ∀ i, |(M.frozenMartingalePart ... s records - M.frozenGeneratorMartingalePart ... s records) i| ≤
    ∫ u in Set.Icc 0 s, gammaCompiledRate 22 (y u records) * (if ... then 1 else 0) := by
  -- Use frozenMartingalePart_sub_frozenGeneratorMP + almost-BC
  sorry
-- Take sup-norm
have norm_bound : ‖...‖ ≤ ∫ ... := by
  rw [Pi.norm_def]
  exact ciSup_le fun i => step2 i
-- etc.
```

## Key API files to READ (exact signatures)

### DensityDependentAbsorbing.lean
- Line 235: `frozenDensityProcess M pathMap t ω i = ((pathMap ω).frozenStateAt t i : ℝ) / M.N`
- Line 241: `frozenInitialCondition M pathMap ω = M.frozenDensityProcess pathMap 0 ω`
- Line 248: frozenMartingalePart definition
- Line 260: frozenGeneratorMartingalePart definition (y - y₀ - ∫genDrift)
- Line 270: `frozenMartingalePart_sub_frozenGeneratorMP`: (M-M*)_i = ∫genDrift_i - ∫drift_i
- Line 290: `frozenDensityProcess_mem_Icc`: y_i ∈ [0,1]
- Line 356: `exists_frozenMartingalePart_norm_bound`: ‖M(s)‖ ≤ C (N-independent)
- Line 387: `exists_frozenGeneratorMP_norm_bound`: ‖M*(s)‖ ≤ C_star

### DensityDependent.lean
- Line 1953: generatorDrift definition
- Line 1903: `offDiagRate_mul_scaledState_sub_apply_eq_sum_jumps`
- Line 1961: `BoundaryCompatible` / `BoundaryCompatibleOnSimplex` definitions
- Line 8037: `generatorDrift_eq_rateSpec_drift_of_boundaryCompatible` — TEMPLATE for almost-BC proof

### PathwiseBound.lean
- Line 9: `scratch_pathwise_cap` — pathwise upper cap (φ ≤ β + κT + 2S)
- Line 137: `scratch_boundary_bound` — boundary integral (∫_B g ≤ S + εs·T)

### ExampleGammaCompiled.lean
- Line 42: gammaCompiledField definition (the ODE vector field, 21 components)
- Line 68: gammaCompiledInit (initial condition, 21 species)
- Line 146: jumpProd / jumpDegr definitions
- Line 154: gammaCompiledJump (32 reactions → jump directions)
- Line 190: gammaCompiledRate (32 reactions → rate functions)
- Line 227: gammaCompiledRateSpec definition
- Line 557: gammaCompiledRateSpec_drift_eq (drift = gammaCompiledField)
- Line 709: gammaCompiledField_19_eq_zero
- Line 714: gammaCompiledField_8_eq: field 8 = y₂₀·(y₁₉-y₈)·y₁₉
- Line 779: gammaCompiled_y19_const (ODE version; CTMC version needs separate proof)

## Critical facts about the rates (verified exhaustively)

All 16 jumpProd rates (k=0,...,15) contain y₂₀ as a multiplicative factor in EVERY term.
All 15 jumpDegr rates (k=16,...,31, k≠22) contain the degraded species y_j as a factor.
Reaction 22 (jumpDegr 9) rate = y₉·y₂₀·y₁₉ + y₈·y₂₀·y₁₉. The y₈ term survives at x₉=0.

Species 19 is NEVER touched by any reaction: gammaCompiledJump k 19 = 0 for all k.

## Compilation

IMPORTANT: Do NOT use `lake build` locally.
- Push: `cd /Users/huangx/repos/Ripple && git add -A && git commit -m "WIP confinement" && git push`
- Build: `ssh uisai2 "cd ~/repos/Ripple && git pull && export PATH=\$HOME/.elan/bin:\$PATH && lake build 2>&1"`
- Quick single-file check: `ssh uisai2 "cd ~/repos/Ripple && git pull && export PATH=\$HOME/.elan/bin:\$PATH && lake env lean Ripple/LPP/ExampleGammaCompiled.lean 2>&1 | tail -30"`

## Hard rules
- **No sorry** in the final version
- **No axiom, no native_decide**
- Line length ≤ 200 chars
- Use `set_option maxHeartbeats 0` if computation is slow
- Lean 4 + Mathlib 4 idioms
- Useful tactics: simp, ring, linarith, nlinarith, norm_num, positivity, omega, gcongr, field_simp, fin_cases
- If integrand is nonneg, integral monotonicity: `MeasureTheory.setIntegral_mono_on`
- For sup-norm on Pi types: `Pi.norm_def`, `ciSup_le`, `norm_le_pi_norm`

## Stall protocol
If stuck on a specific step after 3+ attempts: deliver what compiles + a precise
stall report (exact Lean goal state, what tactic you tried, why it failed).
Do NOT declare "too complex." Grind until it compiles.
