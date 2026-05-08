#!/usr/bin/env python3
"""Exact PARI/GP check for the level-41 Phi_41 Sturm q-expansion.

This script verifies the computational fact used by the pending Lean
certificate, using the same compressed q -> q^41 split as the Lean checker:

    Phi_41(E4(q^41)^3 / Delta(q^41), E4(q)^3 / Delta(q))
      * Delta(q^41)^42 * Delta(q)^42

has valuation beyond the requested bound.  The arithmetic is exact PARI/GP
power-series arithmetic; this is a reproducible data-source check, not a Lean
kernel proof.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Optional


GP_TEMPLATE = r"""
N = {bound};
EXTRA = {extra};
PREC = N + EXTRA;
M = (PREC + 40) \ 41;
PMOD = {prime};
mk(c) = if(PMOD == 0, c, Mod(c, PMOD));
default(seriesprecision, PREC);
q = 'x + O('x^PREC);
qsmall = 'x + O('x^M);

E4 = mk(1) + mk(240) * sum(n = 1, PREC, mk(sigma(n, 3)) * q^n);
Delta = q * prod(n = 1, PREC, (mk(1) - q^n)^24);
C = E4^3;
E4small = mk(1) + mk(240) * sum(n = 1, M, mk(sigma(n, 3)) * qsmall^n);
Deltasmall = qsmall * prod(n = 1, M, (mk(1) - qsmall^n)^24);
Csmall = E4small^3;

CPow = vector(43); DPow = vector(43); CSmallPow = vector(43); DSmallPow = vector(43);
CPow[1] = 1; DPow[1] = 1; CSmallPow[1] = 1; DSmallPow[1] = 1;
for(i = 2, 43, CPow[i] = CPow[i - 1] * C; DPow[i] = DPow[i - 1] * Delta; CSmallPow[i] = CSmallPow[i - 1] * Csmall; DSmallPow[i] = DSmallPow[i - 1] * Deltasmall);
P = vector(43, i, CSmallPow[i] * DSmallPow[43 - (i - 1)]);
Q = vector(43, j, CPow[j] * DPow[43 - (j - 1)]);

Phi = polmodular(41);
S = mk(0);
for(i = 0, 42, for(j = 0, 42, c = polcoef(polcoef(Phi, i, 'x), j, 'y); if(c != 0, S = S + mk(c) * subst(P[i + 1], 'x, q^41) * Q[j + 1])));

v = valuation(S);
print("BOUND\t", N);
print("PREC\t", PREC);
print("SMALL_PREC\t", M);
print("MOD_PRIME\t", PMOD);
print("VALUATION\t", v);
print("STURM_ZERO\t", if(v >= N, 1, 0));
quit;
"""


def run_gp(bound: int, extra: int, stack: str, timeout: Optional[int], prime: int) -> str:
    gp = shutil.which("gp")
    if gp is None:
        raise SystemExit("PARI/GP executable `gp` was not found on PATH")

    program = GP_TEMPLATE.format(bound=bound, extra=extra, prime=prime)
    with tempfile.NamedTemporaryFile("w", suffix=".gp", delete=False) as handle:
        handle.write(program)
        gp_file = Path(handle.name)

    try:
        try:
            proc = subprocess.run(
                [gp, "-q", "-s", stack, str(gp_file)],
                check=True,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout or ""
            stderr = exc.stderr or ""
            if isinstance(stdout, bytes):
                stdout = stdout.decode()
            if isinstance(stderr, bytes):
                stderr = stderr.decode()
            return stdout + (
                f"TIMEOUT\t{timeout}\n"
                "STATUS\tinterrupted before valuation was produced\n"
            ) + stderr
    finally:
        gp_file.unlink(missing_ok=True)

    if proc.stderr.strip():
        return proc.stdout + "\nSTDERR:\n" + proc.stderr
    return proc.stdout


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=3528)
    parser.add_argument("--extra", type=int, default=128)
    parser.add_argument("--stack", default="2G")
    parser.add_argument("--timeout", type=int, default=None, help="seconds")
    parser.add_argument("--prime", type=int, default=0, help="compute modulo this prime")
    args = parser.parse_args()

    print(run_gp(args.bound, args.extra, args.stack, args.timeout, args.prime), end="")


if __name__ == "__main__":
    main()
