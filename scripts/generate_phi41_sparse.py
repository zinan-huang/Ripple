#!/usr/bin/env python3
"""Generate Lean data for the sparse bivariate modular polynomial Phi_41.

The script calls PARI/GP's `polmodular(41)`, extracts all nonzero terms, and
prints either a short summary or a Lean `List SparseBivarTerm` declaration.
It is a data generator only; Lean still checks any theorem that consumes the
generated declarations.
"""

from __future__ import annotations

import argparse
import hashlib
import shutil
import subprocess
import tempfile
from pathlib import Path


GP_PROGRAM = r"""
p = polmodular(41);
maxi = poldegree(p, x);
maxj = poldegree(p, y);
print("DEGREES\t", maxi, "\t", maxj);
for(i = 0, maxi, for(j = 0, maxj, c = polcoef(polcoef(p, i, x), j, y); if(c != 0, printf("TERM\t%Ps\t%ld\t%ld\n", c, i, j))));
"""


def run_gp(stack: str) -> list[tuple[int, int, int]]:
    gp = shutil.which("gp")
    if gp is None:
        raise SystemExit("PARI/GP executable `gp` was not found on PATH")

    with tempfile.NamedTemporaryFile("w", suffix=".gp", delete=False) as handle:
        handle.write(GP_PROGRAM)
        gp_file = Path(handle.name)

    try:
        proc = subprocess.run(
            [gp, "-q", "-s", stack, str(gp_file)],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    finally:
        gp_file.unlink(missing_ok=True)

    terms: list[tuple[int, int, int]] = []
    degrees: tuple[int, int] | None = None
    for raw in proc.stdout.splitlines():
        fields = raw.split("\t")
        if not fields:
            continue
        if fields[0] == "DEGREES":
            degrees = (int(fields[1]), int(fields[2]))
        elif fields[0] == "TERM":
            terms.append((int(fields[1]), int(fields[2]), int(fields[3])))

    if degrees != (42, 42):
        raise SystemExit(f"unexpected Phi_41 degrees: {degrees!r}")
    if len(terms) != 1766:
        raise SystemExit(f"unexpected nonzero term count: {len(terms)}")
    return terms


def digest_terms(terms: list[tuple[int, int, int]]) -> str:
    h = hashlib.sha256()
    for coeff, x_pow, y_pow in terms:
        h.update(f"{coeff},{x_pow},{y_pow}\n".encode())
    return h.hexdigest()


def print_summary(terms: list[tuple[int, int, int]]) -> None:
    diag: dict[int, int] = {}
    for coeff, x_pow, y_pow in terms:
        diag[x_pow + y_pow] = diag.get(x_pow + y_pow, 0) + coeff
    nonzero_diag = {k: v for k, v in diag.items() if v != 0}
    print(f"terms: {len(terms)}")
    print(f"degrees: X=42 Y=42 diagonal={max(diag)}")
    print(f"nonzero diagonal coefficients: {len(nonzero_diag)}")
    print(f"sha256: {digest_terms(terms)}")


def print_lean(terms: list[tuple[int, int, int]], declaration: str) -> None:
    print("import Ripple.Number.Modular.ModularPoly41")
    print()
    print("namespace Ripple.Number.Modular")
    print()
    print(f"/-- Sparse bivariate data for PARI/GP `polmodular(41)`. -/")
    print(f"def {declaration} : List SparseBivarTerm := [")
    for idx, (coeff, x_pow, y_pow) in enumerate(terms):
        suffix = "," if idx + 1 < len(terms) else ""
        print(f"  ⟨({coeff} : ℤ), {x_pow}, {y_pow}⟩{suffix}")
    print("]")
    print()
    print("end Ripple.Number.Modular")


def print_diag_lean(terms: list[tuple[int, int, int]], declaration: str) -> None:
    diag: dict[int, int] = {}
    for coeff, x_pow, y_pow in terms:
        diag[x_pow + y_pow] = diag.get(x_pow + y_pow, 0) + coeff
    max_degree = max(diag)

    print("import Ripple.Number.Modular.ModularPoly41")
    print()
    print("namespace Ripple.Number.Modular")
    print()
    print("/-- Ascending coefficients of the diagonal specialization of `polmodular(41)`. -/")
    print(f"def {declaration} : List ℤ := [")
    for degree in range(max_degree + 1):
        suffix = "," if degree < max_degree else ""
        print(f"  ({diag.get(degree, 0)} : ℤ){suffix}")
    print("]")
    print()
    print("end Ripple.Number.Modular")


def print_full_data_lean(
    terms: list[tuple[int, int, int]], sparse_decl: str, diag_decl: str
) -> None:
    diag: dict[int, int] = {}
    for coeff, x_pow, y_pow in terms:
        diag[x_pow + y_pow] = diag.get(x_pow + y_pow, 0) + coeff
    max_degree = max(diag)

    print("import Ripple.Number.Modular.ModularPoly41")
    print()
    print("set_option linter.style.longLine false")
    print()
    print("namespace Ripple.Number.Modular")
    print()
    print("/-- Sparse bivariate data for PARI/GP `polmodular(41)`. -/")
    print(f"def {sparse_decl} : List SparseBivarTerm := [")
    for idx, (coeff, x_pow, y_pow) in enumerate(terms):
        suffix = "," if idx + 1 < len(terms) else ""
        print(f"  ⟨({coeff} : ℤ), {x_pow}, {y_pow}⟩{suffix}")
    print("]")
    print()
    print("/-- Ascending coefficients of the diagonal specialization of `polmodular(41)`. -/")
    print(f"def {diag_decl} : List ℤ := [")
    for degree in range(max_degree + 1):
        suffix = "," if degree < max_degree else ""
        print(f"  ({diag.get(degree, 0)} : ℤ){suffix}")
    print("]")
    print()
    print("set_option maxRecDepth 65536 in")
    print("set_option maxHeartbeats 20000000 in")
    print("-- Generated 1766-term sparse-to-diagonal integer coefficient comparison.")
    print(f"theorem {sparse_decl}_diag_coeffs :")
    print(f"    sparseBivarDiagCoeffList {sparse_decl} = {diag_decl} := by")
    print("  native_decide")
    print()
    print(f"theorem {sparse_decl}_diag_evalCoeffList (z : ℂ) :")
    print(f"    evalSparseBivarDiagC {sparse_decl} z = evalCoeffListC {diag_decl} z := by")
    print(f"  rw [← eval_sparseBivarDiagCoeffList {sparse_decl} z, {sparse_decl}_diag_coeffs]")
    print()
    print("set_option maxRecDepth 65536 in")
    print("set_option maxHeartbeats 20000000 in")
    print("-- Generated 83-term diagonal coefficient comparison with the isolated factorization.")
    print(f"theorem {diag_decl}_append_zero_eq_isolated_coeffs :")
    print(f"    {diag_decl} ++ [0] = phi41DiagIsolatedCoeffList := by")
    print("  native_decide")
    print()
    print(f"theorem {sparse_decl}_diag_eq_evalPhi41DiagIsolatedC (z : ℂ) :")
    print(f"    evalSparseBivarDiagC {sparse_decl} z = evalPhi41DiagIsolatedC z := by")
    print(f"  rw [{sparse_decl}_diag_evalCoeffList, ← evalCoeffListC_append_zero {diag_decl} z,")
    print(f"    {diag_decl}_append_zero_eq_isolated_coeffs, eval_phi41DiagIsolatedCoeffList]")
    print()
    print("end Ripple.Number.Modular")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--stack", default="512M", help="PARI/GP stack size")
    parser.add_argument("--lean", action="store_true", help="print Lean declaration")
    parser.add_argument("--diag-lean", action="store_true", help="print diagonal coefficient list")
    parser.add_argument("--full-data-lean", action="store_true", help="print sparse and diagonal data")
    parser.add_argument("--decl", default="phi41SparseTerms", help="Lean declaration name")
    parser.add_argument("--diag-decl", default="phi41DiagCoeffsAsc", help="diagonal declaration name")
    args = parser.parse_args()

    terms = run_gp(args.stack)
    if args.lean:
        print_lean(terms, args.decl)
    elif args.diag_lean:
        print_diag_lean(terms, args.decl)
    elif args.full_data_lean:
        print_full_data_lean(terms, args.decl, args.diag_decl)
    else:
        print_summary(terms)


if __name__ == "__main__":
    main()
