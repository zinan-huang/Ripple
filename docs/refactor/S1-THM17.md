# [LPP] Theorem 17: PLPP with rational probabilities implies deterministic LPP (paper proof)

Paper note accompanying Ripple release r2026.11. Section numbers are cited from Lean docstrings.
Theorem numbers follow [LPP]; page numbers refer to its 28-page version arXiv:2206.06594v1.

Bibliography keys.

- [LPP] X. Huang and R. Huls, *Computing real numbers with large-population protocols having a
  continuum of equilibria* (DNA 28, 2022).
- [BFK] O. Bournez, P. Fraigniaud and X. Koegler, *Computing with large populations using
  interactions* (MFCS 2012), cited in [LPP] for its Lemma 4 (derandomization of probabilistic
  protocols).
- [BAC] H.-L. Chen and X. Huang, *Bounded Analog Complexity* (DNA 32, 2026).

Statement ([LPP] p. 23, citing [BFK] Lemma 4): if a PLPP with rational probabilities computes
`ν ∈ [0, 1]` (Definition 9), then a deterministic LPP computes `ν`.
The paper adds that the [BFK] construction "still correctly encodes the balance equation", so the
theorem holds for the continuum-of-equilibria Definition 9. This note proves exactly that, for the
construction formalised in `Ripple/LPP/Derandomization.lean`.

## Objects

- A PLPP on `Q = [n]`: probabilities `α_{ijkl} ∈ ℚ_{≥0}` with `Σ_{k,l} α_{ijkl} = 1` for every
  ordered input pair `(i, j)` ([LPP] Def 6, with the `≥ 0` reading of S1.md §1.3). Balance field
  ([LPP] Eq. (5)): `b(x)_q = Σ_{i,j} x_i x_j (Σ_l α_{ijql} + Σ_k α_{ijkq}) − 2 x_q Σ_k x_k`.
- A deterministic LPP on `Q'`: a map `δ : Q'² → Q'²` ([LPP] Def 5; the null reaction is
  `δ(q₁, q₂) = (q₁, q₂)`). Its balance field (Eq. (4)) is the PLPP field of the `{0,1}` table
  `α'_{abce} = [δ(a, b) = (c, e)]`.
- A computation of `ν` (Def 9): a trajectory `x(t)`, `t ≥ 0`, of `x' = b(x)` with `x(0)` rational,
  nonnegative, on the simplex, staying nonnegative and on the simplex, and a marked set `M` with
  `Σ_{q ∈ M} x_q(t) → ν`.

## Construction ([BFK] Lemma 4)

Let `m ≥ 1` be a common denominator: `m α_{ijkl} ∈ ℕ` for all indices. For each ordered pair
`(i, j)` partition the slots `[m] = {0, ..., m−1}` into blocks `S_{ij}(k, l)` of sizes
`m α_{ijkl}` (possible since the sizes sum to `m`; only the sizes matter, the Lean `coinSlot`
uses an arbitrary bijection); write `slot_{ij}(u) = (k, l)` for `u ∈ S_{ij}(k, l)`.
So `#{u : slot_{ij}(u) = (k, l)} = m α_{ijkl}`, hence

  (C1) `#{u : slot_{ij}(u)₁ = k} = m Σ_l α_{ijkl}` and (C2) `#{u : slot_{ij}(u)₂ = l} = m Σ_k α_{ijkl}`.

The deterministic protocol has states `Q × [m]` and the rule

  `δ((i, r), (j, s)) = ((k, r + 1), (l, s + 1))` with `(k, l) = slot_{ij}(r + s mod m)`,

all indices mod `m`. It is a function `(Q × [m])² → (Q × [m])²`, i.e. a deterministic LPP.

## Claim

If `x` is a PLPP computation of `ν` with marked set `M`, then `y_{(q, r)}(t) = x_q(t) / m` is a
deterministic LPP computation of `ν` with marked set `M × [m]`.

## Proof

Initial and invariant conditions. `y(0)` is rational (`x_q(0) / m`), nonnegative, and
`Σ_{q, r} y_{(q,r)} = Σ_q x_q`, so `y` stays on the simplex and nonnegative for `t ≥ 0` because
`x` does. The readout is `Σ_{q ∈ M} Σ_r x_q / m = Σ_{q ∈ M} x_q → ν`.

ODE. Fix a state `(q, c)`. Write `B` for the deterministic balance field. Degradation term:
`2 y_{(q,c)} Σ_{(k,r)} y_{(k,r)} = (2/m) x_q Σ_k x_k`.

Production term: `Σ_{(i,r),(j,s)} y_{(i,r)} y_{(j,s)} ([first output = (q, c)] + [second output = (q, c)])`.
Every product is `x_i x_j / m²`.

- First output `(k, r + 1) = (q, c)` means `r = c − 1` and `slot_{ij}(r + s)₁ = q`. With `r` fixed,
  `s ↦ r + s mod m` is a bijection of `[m]`, so by (C1) the number of `s` is `m Σ_l α_{ijql}`.
  Contribution: `Σ_{i,j} (x_i x_j / m²) · m Σ_l α_{ijql} = (1/m) Σ_{i,j} x_i x_j Σ_l α_{ijql}`.
- Second output `(l, s + 1) = (q, c)` means `s = c − 1` and `slot_{ij}(r + s)₂ = q`; now `r` ranges
  over `[m]` and `r ↦ r + s` is a bijection, so by (C2) the count is `m Σ_k α_{ijkq}`.
  Contribution: `(1/m) Σ_{i,j} x_i x_j Σ_k α_{ijkq}`.

Hence `B(y)_{(q,c)} = (1/m) b(x)_q = (x_q / m)' = y_{(q,c)}'`. So `y` solves the deterministic
balance equation. No uniqueness or stability argument is needed: Definition 9 asks for a
trajectory of the ODE, and `y` is one. ∎

Remark. [BFK] uses the cyclic coin `r ↦ r + 1` so that, from an arbitrary initial coin
distribution, the coin marginals converge to uniform (their Lemma 3); with the uniform initial
lift used here the coin part is exactly uniform for all `t`, and the `+1` is not needed for the
claim. It is kept because it is the formalised construction.

## Lean

- Construction and the balance-field computation: `PLPPTransitions.derandomizeTransitions`,
  `derandomize_meanField_uniformLift_eq`, `derandomize_preserves_continuum_computation`
  (`Ripple/LPP/Derandomization.lean`). The count (C1)/(C2) is
  `PLPPTransitions.coinSlot_first_count` and `coinSlot_second_count`; the bijection `r ↦ r + s` is `coinAdd`.
- Identification of the `{0,1}` table as a transition function and the theorem:
  `PLPPTransitions.derandomizeLPP`, `PLPPTransitions.derandomizeLPP_toPLPP`,
  `IsPLPPComputable.isLPPComputable`, `isLPPComputable_iff_isPLPPComputable`
  (`Ripple/LPP/Determinization.lean`).
