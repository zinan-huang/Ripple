# Paper proofs for the steps of the faithful [LPP] compiler that [LPP] does not give

Paper note accompanying Ripple release r2026.11. Section numbers are cited from Lean docstrings.
Theorem numbers follow [LPP]; page numbers refer to its 28-page version arXiv:2206.06594v1.

Bibliography keys.

- [LPP] X. Huang and R. Huls, *Computing real numbers with large-population protocols having a
  continuum of equilibria* (DNA 28, 2022).
- [BFK] O. Bournez, P. Fraigniaud and X. Koegler, *Computing with large populations using
  interactions* (MFCS 2012), cited in [LPP] for its Lemma 4 (derandomization of probabilistic
  protocols).
- [BAC] H.-L. Chen and X. Huang, *Bounded Analog Complexity* (DNA 32, 2026).

The compiler (`Ripple/LPP/Compiler.lean`) proves: for `α ∈ [0, 1]`, a
`CertifiedBoundedTimeComputable d α` (bounded ℚ-PIVP with modulus) with a `PolyCRNDecomposition`
gives `IsPLPPComputable α` ([LPP] Def 9, PLPP clause), and with Theorem 17 (`S1-THM17.md`)
`IsLPPComputable α`. The stages follow [LPP] §3. This note writes out the steps that are not in
the paper or that differ from it.

Notation: Stage 2 produces `x(t) ∈ ℝ^{n+1}` (coordinate `0` the balancing species, output
`o' = o + 1`), on the simplex and nonnegative for `t ≥ 0`, solving a cubic conservative ODE,
with `x_{o'}(t) → α`.

## 0. The stages, and what is not in the paper

| step | paper | Lean (other modules) | this note |
|---|---|---|---|
| surrogate `x_out ≤ U < 1` | not in paper (needed for Remark 14) | `saturating_surrogate_cbtc` (certified) | — |
| output init `0` | [LPP] Thm 13 assumes `x_i(0) = 0` | `certified_zero_init_wrapper_sharp` (certified) | — |
| Stage 1, Thm 12 | v-variables | `stage1_vvariable_with_output_eq_and_modulus`, real `A, B` | `stage1_vvariable_rat`: the same system with `A, B ∈ ℚ_{≥0}` (§1) |
| Stage 2, Thm 13 + Remark 14 | λ-trick, one-trick, balancing dilation | `stage2_ode_from_room` (analysis, real coefficients) | its field equals a rational transfer tensor (§3) |
| Stage 3, Thm 15 | ordered pairs `z_{ij} = x_i x_j` (not formally conservative) | `symmetricLift` (upper triangle, formally conservative) | sum and readout identities (§4) |
| Stage 4, Construction 1 | `ε`-trick | `SynPPBalance.toPLPPTransitions`, field = `κ ·` lift field | time rescaling `t ↦ κ t` (§5) |
| readout | `Σ_j z_{1j} = x_1` | none (the upper-triangle sum is `x_o(2 − x_o)`) | 2-fold replication (§2) |

## 1. Stage 1 with rational coefficients

[LPP] Theorem 12: for `x' = p − q·x` with `p, q ∈ P⁺` (nonnegative rational coefficients) and
the v-variables `v_β = x^β` (`|β| ≤ D`, including `v_0 = 1`), `v_β' = Σ_k β_k x^{β − e_k} (p_k − q_k x_k)`
is `Σ_{a,b} A_{β a b} v_a v_b − (Σ_a B_{β a} v_a) v_β` with
`A_{β a b} = Σ_{k : β_k > 0, a = β − e_k} β_k · coeff_b(p_k)` and `B_{β a} = Σ_k β_k · coeff_a(q_k)`.
These are sums of products of naturals and coefficients of `p_k, q_k ∈ ℚ[x]`, hence in `ℚ_{≥0}`.
The repository's `vCoeffA`, `vCoeffB` are these numbers cast to `ℝ` (`vCoeffA_eq_cast`). The
output coordinate is `v_{e_o} = x_o` for all `t`, the initial values `x(0)^β` are rational and
nonnegative. Nothing else changes.

## 2. Fractional readout by replication

Claim. Let `x(t)` be a trajectory of the balance equation of a PLPP `α` on `[n]` satisfying the
Definition 9 conditions except the readout, and let `w : [n] → {0, ..., m}` (`m ≥ 1`) with
`Σ_q (w_q / m) x_q(t) → ν`. Then `ν` is PLPP-computable.

Construction. States `[n] × [m]`; probabilities
`α'_{(i,r)(j,s)(k,r')(l,s')} = α_{ijkl} [r' = r][s' = s]` (each agent keeps its copy index).
Row sums: `Σ_{(k,r'),(l,s')} α'… = Σ_{k,l} α_{ijkl} = 1`; entries are rational and `≥ 0`.

Lift `y_{(q, r)} = x_q / m`. Initial values are rational, `Σ y = Σ x`, so the simplex and
nonnegativity conditions transfer. Marked set `M' = {(q, r) : r < w_q}`:
`Σ_{M'} y = Σ_q w_q x_q / m → ν`.

ODE. With `a = (q, c)`: for inputs `(i, r), (j, s)`,
`Σ_{(l,s')} α'_{(i,r)(j,s)(q,c)(l,s')} = [c = r] Σ_l α_{ijql}` and
`Σ_{(k,r')} α'_{(i,r)(j,s)(k,r')(q,c)} = [c = s] Σ_k α_{ijkq}`. So the production term of the
replicated field at `y` is
`Σ_{i,j} Σ_{r,s} (x_i x_j / m²)([c = r] Σ_l α_{ijql} + [c = s] Σ_k α_{ijkq})
 = Σ_{i,j} (x_i x_j / m²) · m (Σ_l α_{ijql} + Σ_k α_{ijkq})`,
and the degradation term is `2 (x_q / m) Σ_{(k,r)} x_k / m = (2/m) x_q Σ_k x_k`. Hence the
replicated field at `y` is `b(x)_q / m = y_{(q,c)}'`. ∎

Lean: `Ripple/LPP/Replication.lean` (`replicate`, `replicate_balanceField_lift`,
`isPLPPComputable_of_fractional_readout`).

## 3. Stage 2 is a rational cubic transfer tensor

Stage 2 ([LPP] Thm 13 with the selective λ-trick of the repository, Remark 14): with
`F_i(y) = Σ_{a,b} A_{iab} y_a y_b − (Σ_a B_{ia} y_a) y_i` (Stage 1, rational), constants
`c ∈ ℚ ∩ (0, 1]`, `ε = 1/c`, scale factors `u_j = 1` for `j = o` and `u_j = c` otherwise,
the selective λ-trick of `ε F` is
`G_i(y) = u_i ε F_i(y_1/u_1, …) = Σ_{a,b} A'_{iab} y_a y_b − (Σ_a B'_{ia} y_a) y_i`,
`A'_{iab} = u_i ε A_{iab} / (u_a u_b)`, `B'_{ia} = ε B_{ia} / u_a` (the `u_i` of the degradation
term cancels). `A', B'` are in `ℚ_{≥0}`. The balancing dilation `x_0' = −(Σ_i G_i(x_{1..n})) x_0`,
`x_{i}' = G_i(x_{1..n}) x_0` is the transfer field with rates `A'_{iab}` for
`0 → i` with context `(a, b)` and `B'_{ia}` for `i → 0` with context `(a, 0)`
(`ofBalancingDilation_toField`). The analysis (simplex, nonnegativity, and
`x_{o'}(t) → α` under the room condition `x_o + c Σ_{j≠o} x_j ≤ 1 − c` with `εc = 1`) is
`stage2_ode_from_room`.

The room constant. With `x_o ≤ U < 1`, `0 ≤ x_j ≤ M` for Stage 1 (`stage1_rest_bound_and_nonneg`)
and `K = nM + 1`, any rational `0 < c < (1 − U)/(2K)` gives `cK ≤ (1 − U)/2`, hence
`c ≤ 1/2`, `c Σ_j x_j(0) ≤ c n M ≤ 1`, and `x_o + c Σ_{j≠o} x_j ≤ U + c n M ≤ U + cK − c ≤ 1 − c`.

## 4. Half-products: total mass and readout

Upper pairs `{i ≤ j}`, `z_{ij} = s_{ij} x_i x_j` with `s_{ii} = 1`, `s_{ij} = 2` (`i < j`)
(`halfProduct`). Each `z_k` is the sum of `x_r x_p` over the ordered pairs `(r, p)` whose
unordered pair is `k` (one pair if `i = j`, two otherwise). Hence

- `Σ_k z_k = Σ_{r,p} x_r x_p = (Σ x)²`, so the lift of a simplex point is on the simplex;
- with weights (out of 2) `w_{oo} = 2`, `w_{oj} = 1` (`j ≠ o`), `0` otherwise:
  `Σ_k (w_k/2) z_k = x_o² + Σ_{j≠o} x_o x_j = x_o Σ_j x_j = x_o` on the simplex.

The weight is written as `w_k = #{p : k = {o, p}} + [k = {o, o}] ≤ 2` (`p ↦ {o, p}` is injective).
`z ≥ 0` and `z(0)` rational follow from `x`. The lifted ODE `z' = L(z)` with `L` the symmetric lift
field holds along `z = halfProduct ∘ x` (`symmetricLift_halfProduct_hasDerivAt`,
formally conservative; this replaces [LPP] Thm 15's ordered-pair field, see S1.md §1.3, reading note 2).

## 5. Stage 4 and time

`SynPPBalance.toPLPPTransitions` of the lift has balance field `κ L` with `κ = 1/(‖coeff‖₁ + 1) ∈ ℚ_{>0}`
(`toPLPPTransitions_balanceField_eq`, `toSynPPBalance_toField`). So
`Z(t) = z(κ t)` solves the PLPP balance equation (chain rule;
`symmetricMeanFieldSolution`), keeps the conditions of §4 for `t ≥ 0`, and
`Σ_k (w_k/2) Z_k(t) = x_{o'}(κ t) → α`. §2 with `m = 2` gives `IsPLPPComputable α` for `α < 1`.
`α = 1` is the idle protocol on two states started at `(1, 0)` (`isLPPComputable_rat`).
