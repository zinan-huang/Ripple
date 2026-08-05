# Tri-molecular approximate-majority formalization

`Tri` is the Lean 4 formalization of Condon, Hajiaghayi, Kirkpatrick, and
Mañuch, *Approximate Majority Analyses using Tri-molecular Chemical Reaction
Networks*, Natural Computing 19 (2020), 249–270
([DOI 10.1007/s11047-019-09756-4](https://doi.org/10.1007/s11047-019-09756-4)).

The public library contains the active import closure rooted at
[`Tri.lean`](../../Tri.lean). Its paper-facing results include:

- `Tri.Byzantine.theorem4_entry`, the corrected reached-by-deadline entry
  clause of Theorem 4;
- `Tri.Multi.theorem5`, the unconditional corrected multi-species consensus
  theorem;
- `Tri.Byzantine.lemma8`, for history-dependent Byzantine strategies; and
- `Tri.Multi.lemma12_unconditional`, which repairs the printed proof of the
  full species-range tail bound.

Theorem 4's additional claim that relaxed consensus is preserved for the next
`n^γ` interactions is false as printed. The formalization records the
corrected entry statement and does not assert the false preservation clause.
The supporting publication locations, corrections, and counterexamples are
collected in:

- [Errata and Counterexamples (PDF)](Errata_and_Counterexamples.pdf)
- [LaTeX source](ERRATA.tex)

Each erratum gives the printed Natural Computing page and the one-based
Springer PDF page.

## Verification

From the repository root:

```bash
lake build
python3 scripts/audit_tri.py
```

The audit checks for `sorry`, `admit`, `unsafe`, custom axioms, and
`native_decide`, runs the build, and verifies every emitted `#print axioms`
result against the standard Lean/Mathlib trust footprint.
