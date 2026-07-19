# Ripple Release Notes

## v1.0 — 2026-05-08 (Φ₄₁ → CM-163 chain closed)

**0 sorry / 0 axiom decl across all six pillars.**

### Headline

The long-standing `complex_sturm_bound_valence_formula_phi41Level41Cleared`
chain (`Ripple/Number/Modular/ModularPolynomialQExpansion.lean:2751` —
the last open sorry in the Modular pillar) is closed. As a consequence,
the Heegner-class CM evaluation
`j((1 + √-163) / 2) = -640320³` is fully verified in Lean 4 through the
level-41 modular polynomial Φ₄₁.

### What changed

| Commit | Subject |
|---|---|
| `080c9688` | `atkinLehnerInclusion41` — Atkin-Lehner inclusion at level 41 |
| `254deaf2` | `levelOne_cuspForm_eq_zero_of_low_coeffs_vanish` — generic level-1 Sturm bound for arbitrary even k ≥ 4 |
| `e94431d7` | `Phi41ModularFormAssembly.lean` — bundled `phi41Level41ClearedAsModularForm : ModularForm Γ₀(41) 1008` + qExp bridge |
| `eab0efb5` | `Gamma0_41_SturmBound.lean` — partial norm-trick framework |
| `286d65c0` | `phi41Level41SturmBound : 3528 → 3529` (off-by-one fix; classical level-N Sturm at weight 1008 needs 3529 vanishing coefficients, not 3528) |
| `b89c7616` | `levelGamma0_41_sturm_weight_1008` — main Sturm theorem at level 41 weight 1008, via the q-expansion norm bridge `qExp_norm_coeff_zero_of_qExp_coeff_zero` |
| `ec52333d` | `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` — finite recurrence-array zero check via `native_decide` |
| `6bb32ab0` | Cleanup: HANDOFFs archived, CHECKPOINT/TODO/WORK_LOG refreshed |
| `2af6ba47` | Removed 30+ obsolete `LevelOneCuspWeight*.lean` files (~7080 LoC) — superseded by `LevelOneSturmGeneric.lean` |
| `8d008407` | Stale doc reference refresh + CRT-route HANDOFF for future kernel-only replacement |

### Build

```bash
cd projects/Ripple
PATH="$HOME/.elan/bin:$PATH" lake build       # 3695 jobs, ~30-45 min from scratch
```

### Trust footprint (important)

The project has **no `sorry`** and **no `axiom`**. The only trust beyond
the Lean kernel is `native_decide`, used in finitely many places to
discharge large decidable claims:

- `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` — first 3529
  entries of the Φ₄₁ cleared q-expansion recurrence array are zero
  (added in this release).
- `phi41Diag_root`, `phi41DiagCofactor_ne_zero` — root and cofactor
  checks for `evalPhi41Diag` at `j(τ₁₆₃)` (pre-existing).
- `(List.range 83).Forall ...` — level-41 difference table vanishes
  (pre-existing).

`native_decide` compiles the decision procedure to native code and
trusts that the result matches what the Lean kernel would compute. The
mathematical content is unchanged; only the verification path differs
from a strict kernel-only proof.

A kernel-only Chinese-Remainder-Theorem replacement is feasible in
principle (see `HANDOFF/crt_route_replace_native_decide.md` for the
plan) but would require either a tighter problem-specific coefficient
bound or a custom reflection evaluator — both research-grade tasks
beyond v1.0 scope. The structural CRT helpers are already in place in
`ModularPolynomialSturmCertificate.lean`.

### Architecture changes

`Ripple/Number/Modular/` shrank from 60 → 25 files:

- **Removed**: `LevelOneCuspWeight{2,4,8,...,70}.lean` (35 files, ~7080
  LoC) and `LevelOneSmallWeights.lean`. These were per-weight cusp-form
  vanishing proofs that have been replaced by the single uniform
  theorem `levelOne_cuspForm_eq_zero_of_low_coeffs_vanish` parametrised
  by `k mod 12 ∈ {0, 2, 4, 6, 8, 10}` (332 lines).
- **Added**: `LevelOneSturmGeneric.lean`, `Phi41Bridge.lean` (extended),
  `Phi41ModularFormAssembly.lean`, `Gamma0_41_SturmBound.lean`,
  `SturmBoundIndex.lean`.

### Non-goals / future work

- **Kernel-only Φ₄₁ certificate** (replacing `native_decide`): see
  `HANDOFF/crt_route_replace_native_decide.md`.
- **Mathlib upstream of `LevelOneSturmGeneric`**: the generic level-1
  Sturm bound for arbitrary even weight could plausibly be contributed
  to Mathlib's `Mathlib.NumberTheory.ModularForms` namespace.
- **`maxHeartbeats 800000` audit**: scattered through the project; some
  could be returned to the 200000 default.
- **CRN library extraction**: split Ripple into reusable
  `CRN.Core` / `CRN.Number` / `CRN.Modular` packages.

### Historical pillars

- `RTCRN1`, `RTCRN2`, `LPP` (DNA28), `BAC` (DNA32) — formalised in the
  Core, ODE, DualRail, and LPP pillars over earlier sessions.
- `Number/Frobenius` — long-term strategic pillar for periods, special
  constants, and holonomic-series-defined numbers (decided 2026-04-21,
  see `STRATEGY.md`).

### Acknowledgements

This release was assembled with extensive collaboration from external
LLM agents (codex, gpt-5.5 high) for matrix algebra grinds and
norm-trick analysis, and a general-purpose subagent for the generic
level-1 Sturm proof. The architectural choices, off-by-one fix,
docstring discipline, and final assembly were directed from the main
Lean session.
