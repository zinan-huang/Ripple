# Halving the Φ41 Sturm certificate by the Fricke involution

Paper note accompanying Ripple release r2026.11. Section numbers are cited from Lean docstrings.
It concerns the cleared level-41 form `F = Δ(τ)^42 Δ(41τ)^42 Φ41(j(41τ), j(τ))` of weight 1008
on `Γ₀(41)` and shows that vanishing of its first 1765 `q`-expansion coefficients forces `F = 0`,
using the Fricke involution `W = [[0,−1],[41,0]]` and the level-one Sturm bound. Mathlib
conventions: `ModularGroup.S = !![0,−1;1,0]`, `ModularGroup.T = !![1,1;0,1]`.

## 0. Summary

The Fricke constant is `41^504`, `F|S(τ) = 41^(-504) F(τ/41)`, there are 41 non-identity cosets,
and the threshold is `m = 1765` (`2·1765 = 3530 ≥ 3529 = 42336/12 + 1`). The method cannot do
better than 1765: a nonzero Fricke-symmetric `F` may have order 1764 at both cusps (valence total
`1008·42/12 = 3528`).

Three points to note:

1. The `S`-form of the functional equation needs `E₄(−1/z) = z⁴ E₄(z)` as well as the `Δ` law. The
   Lean form is cleared (numerators `E₄³`, denominators `Δ`) and never divides by `Δ`, so the
   S-invariance of `j` is not used. The proof also uses the fact that both clearing exponents are
   42, the degree of Φ41 in each variable.
2. The slash convention never touches `W = [[0,−1],[41,0]]`. The proof below slashes only by
   elements of `SL(2,ℤ)` (determinant 1, no `σ`, no `|det|^(k−1)` factor) and uses Fricke only as
   a pointwise identity of functions. For the record, in Mathlib's normalisation
   `(F ∣[1008] W)(τ) = |41|^1007 (41τ)^(-1008) F(Wτ) = 41^503 F(τ)`. In the classical
   normalisation `det^(k/2)`, `F` is a Fricke eigenform with eigenvalue `+1`.
3. The symmetry of Φ41 (`c(x,y) = c(y,x)` on its 1766 terms) is proved in Lean by a kernel check
   on the term list plus a permutation soundness lemma (§4).

## 1. Objects and conventions

- `F = phi41Level41ClearedAsModularForm : ModularForm Gamma0_41_GL 1008`
  (`Phi41ModularFormAssembly`), defined as the weight-1008 component of
  `evalSparseBivarCleared phi41SparseTerms 42 42 xNum xDen yNum yDen` in the graded ring
  `⨁ k, ModularForm Gamma0_41_GL k`. Here
  `xNum = E4Cubed_pullback41_normalized` (`E₄(41τ)³`), `xDen = delta_pullback41_normalized`
  (`Δ(41τ)`), `yNum = E4Cubed_on_Gamma0_41` (`E₄(τ)³`), `yDen = delta_on_Gamma0_41` (`Δ(τ)`).
  Pointwise:
  `F(τ) = Σ_t c_t P(41τ)^{x_t} Q(41τ)^{42−x_t} P(τ)^{y_t} Q(τ)^{42−y_t}` with `P = E₄³`, `Q = Δ`.
  So `x` is the `j(41τ)` slot and `y` the `j(τ)` slot, and `F = Δ(τ)^42 Δ(41τ)^42 Φ41(j(41τ), j(τ))`.
- `41τ` in Lean is `pullback41GL • τ`, with `pullback41GL = !![41,0;0,1]` (`Gamma0_41_ModularForms`).
  `E4_pullback41_normalized_apply` gives `E4_pullback41_normalized τ = E4 (pullback41GL • τ)`,
  and `delta_pullback41_normalized_apply` the same for `deltaLevelOneMF`, whose coercion is
  `ModularForm.discriminant`.
- Mathlib: `ModularGroup.S = !![0,−1;1,0]` and `ModularGroup.T = !![1,1;0,1]`;
  `UpperHalfPlane.modular_S_smul : S • z = mk (−z)⁻¹ _`;
  `modular_T_zpow_smul : T ^ n • z = (n : ℝ) +ᵥ z`;
  `ModularForm.SL_slash_apply : (f ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (−k)` for `γ : SL(2,ℤ)`.
  The GL slash is `σ g (f (g • τ)) * |det g|^(k−1) * denom g τ ^ (−k)` (`slash_def`).
- `t ↦ τ/41` is the positive-real scalar action. Define
  `fricke41Pos : {x : ℝ // 0 < x} := ⟨41⁻¹, by norm_num⟩`; then
  `coe_pos_real_smul : ↑(r • z) = (r : ℝ) • (z : ℂ)` and `pos_real_im : (r • z).im = r * z.im`.

## 2. The proof on paper

Throughout, `k = 1008`, `N = 41`, `K = 42 k = 42336`, `K/12 + 1 = 3529`.

### 2.1 Fricke functional equation (S-form)

For `v ∈ ℍ` put `u = v/41` (`u = fricke41Pos • v`), so `41u = v`. Then
`41·(S v) = −41/v = −1/u = S u`, and `S v = S(41u)`. From `E₄(S z) = z⁴E₄(z)`
(`E4_S_transform`) and `Δ(S z) = z¹²Δ(z)` (`delta_S_transform`):

- `P(41·Sv) = P(Su) = u¹² P(u)` and `Q(41·Sv) = u¹² Q(u)`;
- `P(Sv) = v¹² P(v) = v¹² P(41u)` and `Q(Sv) = v¹² Q(41u)`.

Hence
```
F(Sv) = Σ_t c_t (u¹²P(u))^x (u¹²Q(u))^{42−x} (v¹²P(41u))^y (v¹²Q(41u))^{42−y}
      = u^504 v^504 · Σ_t c_t P(u)^x Q(u)^{42−x} P(41u)^y Q(41u)^{42−y}       (x, y ≤ 42)
      = u^504 v^504 · Σ_t c_t P(41u)^x Q(41u)^{42−x} P(u)^y Q(u)^{42−y}       (c_{x,y} = c_{y,x})
      = u^504 v^504 · F(u)
      = 41^(−504) · v^1008 · F(v/41).
```
Equivalently `F(−1/(41u)) = 41^504 u^1008 F(u)`, the Fricke form: put `v = 41u` and
`S v = −1/(41u)`; then `41^(−504)(41u)^1008 = 41^504 u^1008`.

### 2.2 The 41 non-identity translates

Let `γ = [[a,b],[c,d]] ∈ SL(2,ℤ)` with `41 ∤ c`, i.e. `γ ∉ Γ₀(41)`. Choose `j ∈ ℤ` with
`cj ≡ d (mod 41)` (`c` is invertible mod 41). Then
`(S T^j)⁻¹ = [[j,1],[−1,0]]` and `h := γ (S T^j)⁻¹ = [[aj−b, a],[cj−d, c]]`,
which has determinant 1 and `41 | cj − d`, so `h ∈ Γ₀(41)` and `γ = h · S T^j`.
(`S T^j = [[0,−1],[1,j]]`; its bottom row is `(1 : j) ∈ P¹(F₄₁)`. Together with `Γ₀(41)`
itself, with bottom row `(0 : 1)`, these are the `42` right cosets.)

For such `γ`, with `w = T^j τ` (`↑w = τ + j`):
```
(F ∣ γ)(τ) = (F ∣ h ∣ S T^j)(τ) = (F ∣ S T^j)(τ)              (F is Γ₀(41)-invariant)
           = F(S w) · (τ + j)^(−1008)                         (denom(S T^j, τ) = τ + j = ↑w)
           = 41^(−504) w^1008 F(w/41) · w^(−1008)              (§2.1)
           = 41^(−504) · F((τ + j)/41).
```
So the constant is `41^(−504)`, and the form "constant times `F(τ/41)`" holds up to the
translation `τ ↦ τ + j`, which does not change `Im`.

### 2.3 Decay

If the first `m` coefficients of the `q`-expansion of `F` vanish, then
`F(τ) = O(exp(−2π m Im τ))` on `atImInfty` (`exp_decay_atImInfty_of_qExpansion_coeff_zero`).
Since `Im((τ+j)/41) = Im τ / 41` and `τ ↦ (τ+j)/41` maps `atImInfty` to `atImInfty`, each
non-identity factor is `O(exp(−2π (m/41) Im τ))`. There are exactly `42 − 1 = 41` of them, so
their product `H` is `O(exp(−2π m Im τ))`. The identity factor is `F` itself, so
`norm F = F · H = O(exp(−2π (2m) Im τ))`.

### 2.4 Conclusion

`norm F : ModularForm 𝒮ℒ 42336` (`gamma0_41_normLevelOne`). With `m = 1765`,
`exp(−2π·3530·y) ≤ exp(−2π·3529·y)` for `y > 0`, so
`norm F = O(exp(−2π (K/12+1) Im τ))`, and `levelOne_modularForm_eq_zero_of_exp_decay` gives
`norm F = 0`. Then `ModularForm.norm_eq_zero_iff` gives `F = 0`.

Sharpness: Γ₀(41) has two elliptic points of order 2 and none of order 3, and
`ord_∞ F + ord_0 F + (rest) = 3528`. With Fricke symmetry `ord_0 = ord_∞`, so 1764 is not
enough in general, and 1765 is the least `m` for which this argument works.

## 3. How this meets Mathlib's norm (arbitrary representatives)

`ModularForm.norm 𝒮ℒ f` has coercion `∏ q : 𝒮ℒ ⧸ Γ.subgroupOf 𝒮ℒ, quotientFunc f q`, and
`quotientFunc f ⟦r⟧ = ⇑f ∣[k] r.val⁻¹` (GL slash, `quotientFunc_mk`). The representative `r`
is arbitrary, which is why §2.2 is stated for every `γ ∉ Γ₀(41)` rather than for chosen
representatives. Steps for `q = ⟦r⟧ ≠ e := QuotientGroup.mk 1`:

1. `r ∉ Gamma0_41_GL.subgroupOf 𝒮ℒ`: otherwise `QuotientGroup.eq` gives `⟦r⟧ = ⟦1⟧`.
2. `r.val ∈ 𝒮ℒ = (mapGL ℝ).range`, so `r.val = mapGL γ₀`. Then `γ₀ ∉ Gamma0 41`, since
   `Gamma0_41_GL = (Gamma0 41).map (mapGL ℝ)`, `Subgroup.mem_subgroupOf`, and
   `Subgroup.mem_map` with `mapGL_injective`. Put `γ = γ₀⁻¹ ∉ Gamma0 41`; then
   `r.val⁻¹ = mapGL γ`.
3. Decompose `γ = h * (S * T^j)` (§2.2). By `SlashAction.slash_mul` and
   `SlashInvariantFormClass.slash_action_eq f (mapGL h) (Subgroup.mem_map_of_mem _ hh)`,
   `⇑f ∣[k] mapGL γ = ⇑f ∣[k] mapGL (S * T^j)`. This is the SL slash (`SL_slash`, `rfl`).
4. The identity coset is `quotientFunc f e = ⇑f` (slash by `1⁻¹`). The existing proof
   `gamma0_41_norm_decay_of_decay` already factors `norm = f · H` with
   `H = ∏ q ∈ univ \ {e}, quotientFunc f q` (its `hfac`); that factorisation is reused verbatim.
5. Count: `(univ \ {e}).card = Fintype.card − 1 = 41`, from `gamma0_41_normQuot_card`
   (`Nat.card … = 42`), `Nat.card_eq_fintype_card`, `Finset.card_univ_diff`. The `Fintype` is
   `Fintype.ofFinite` as in the existing proof. Go through `Nat.card` so that no instance
   mismatch arises.
6. Product bound: `Asymptotics.IsBigO.finsetProd` (Mathlib, the
   lemma `ModularForm.norm` itself uses), then `Finset.prod_const` and
   `← Real.exp_nat_mul` to turn `∏_{41} exp(−2π(m/41)y)` into `exp(−2π m y)`.

This is not a general two-cusp Sturm theorem. It needs only the explicit coset translates of
this one Fricke-symmetric form, together with the existing level-one Sturm theorem.

## 4. Lean

The argument is implemented in the following modules (`Ripple/Number/Modular/`).

- `Phi41SymmCheck` (imports only `ModularPoly41Terms`): the kernel check
  `phi41SparseTerms_rows_eq_swapped_cols` (with `bucketBy`), which says that bucketing the terms of
  Φ41 by `xPow` equals bucketing by `yPow` and swapping, i.e. that the coefficient array is
  symmetric.
- `Phi41ModularFormAssembly`: the form `phi41Level41ClearedAsModularForm` and its pointwise
  formula `phi41Level41ClearedAsModularForm_apply` (via `gradedEvalAt`, `gradedEvalAt_of`), with
  `E4_pullback41_normalized_apply` and `delta_pullback41_normalized_apply`.
- `Phi41Fricke`:
  - symmetry of Φ41 (§2.1): `flatten_bucketBy_perm`, `phi41SparseTerms_perm_swap`,
    `evalSparseBivarCleared_of_perm`, `evalSparseBivarCleared_map_swap`,
    `evalSparseBivarCleared_phi41_symm`, and the two-scalar homogeneity
    `evalSparseBivarCleared_smul_smul`;
  - the Fricke functional equation (§2.1): `fricke41Pos`, `pullback41GL_smul_fricke41Pos`,
    `pullback41GL_smul_S_smul`, `phi41Level41ClearedAsModularForm_S`, using `E4_S_transform` and
    `delta_S_transform` (`KleinJ`);
  - cosets and decay (§2.2, §2.3, §3): `SL2_eq_gamma0_41_mul_S_T_zpow`,
    `slash_S_T_zpow_apply_of_S`, `gamma0_41_quotientFunc_eq_of_ne`, `im_fricke41Pos_T_zpow`,
    `isBigO_comp_fricke41Pos_T_zpow`;
  - the Fricke-Sturm theorem (§2.4): `levelGamma0_41_sturm_weight_1008_of_S`, which takes the
    `S`-form identity with an arbitrary constant `C` and the vanishing of the first 1765
    coefficients, and concludes `f = 0`. It reuses the level-one Sturm theorem
    `levelOne_modularForm_eq_zero_of_exp_decay` (`LevelOneSturmGeneric`), the decay lemma
    `exp_decay_atImInfty_of_qExpansion_coeff_zero` (`HigherOrderDecay`) and the factorisation
    pattern of `gamma0_41_norm_decay_of_decay` (`Gamma0_41_SturmBound`).
- `SturmPacked`: the packed certificate for the first 1765 coefficients,
  `phi41FrickeSturmBound` (`= 1765`) and `phi41Level41FrickeCoefficientCertificate_proof`.
- `Phi41FrickeSturm`: `phi41Level41ClearedAsModularForm_eq_zero`,
  `phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_fricke`, and, as corollaries,
  `phi41Level41SturmCoefficientCertificate_proof` and
  `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` (the 3529-coefficient statements).

The older general theorem `levelGamma0_41_sturm_weight_1008` (bound 3529) remains in
`Gamma0_41_SturmBound`.
