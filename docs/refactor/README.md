# Notes for the r2026.11 reorganization

Release `r2026.11` renames and reorganizes the library, restates the
computability predicates to match the source papers, and adds the bounded
surrogate compilation theorems. This directory holds the public records of
those changes. Lean docstrings cite the paper notes by file and section.

| File | Content |
|---|---|
| [`RENAMES.tsv`](RENAMES.tsv) | Old name, new name and kind (`decl`, `module`, `namespace`, `dir`) for every declaration, module, namespace and directory of `r2026.08` that was renamed, followed by the renames of the incremental releases. Apply it before updating code that imports Ripple. |
| [`STATEMENT-CHANGES.tsv`](STATEMENT-CHANGES.tsv) | Declarations whose statement changed, that were deleted, or that were added, when the computability predicates were restated (`predicates`) and when bounded compilation was proved (`compilation`), and in the incremental releases (`r2026.11.1`, `r2026.11.2`), with the reason for each. |
| [`S1.md`](S1.md) | The paper definitions of real-time, bounded-time and LPP computability, and the Lean definitions that now match them. |
| [`S1-LPP-PAPER.md`](S1-LPP-PAPER.md) | Paper proofs of the steps of the LPP compiler that the large-population protocol paper does not spell out. |
| [`S1-THM17.md`](S1-THM17.md) | Paper proof of Theorem 17 of the large-population protocol paper for its continuum-of-equilibria definition. |
| [`BC.md`](BC.md) | Paper proofs of Construction 3.1, Proposition 3.2 and Theorems 3.3, 3.4, 4.5 and 4.6 of the bounded analog complexity paper, with the repairs of the printed proofs. |
| [`FRICKE.md`](FRICKE.md) | The Fricke-involution argument that halves the Φ₄₁ Sturm certificate. |
| [`BAC2-PAPER.md`](BAC2-PAPER.md) | Release `r2026.11.1`: repairs to Sections 5 to 7 of the journal version of the bounded analog complexity paper (power closure, CRN readout, constructible moduli) used by the Lean proofs. |

`RENAMES.tsv` records the rename step only. A few names it lists as targets
were later deleted or reused when the predicates were restated; for example
`bounded_crn_is_lpp_computable` now names the unconditional theorem and its
former conditional form was deleted. `STATEMENT-CHANGES.tsv` is
authoritative for those declarations.
