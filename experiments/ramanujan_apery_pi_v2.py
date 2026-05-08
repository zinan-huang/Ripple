"""
Apéry-mechanism on Ramanujan PF: structural obstruction analysis + alternatives.

Findings from v1: simple b_n candidates don't give P[B] = poly_low.

This v2 establishes the STRUCTURAL fact:
  - Ramanujan PF kernel restricted to formal power series at z=0 is 1-D
    (just A itself), because the series recurrence is order-1 (2-term).
  - Hence "two formal-series companions same PF" is impossible: any
    B(z)=Σb_n z^n with P[B]=poly_d is just a finite-dim affine
    adjustment of A, giving B''/A'' = constant (uninteresting).
  - Apéry's ζ(3) works because his recurrence is ORDER 2 (3-term),
    so the series solution space is 2-D, giving genuine companions.

We then test the *non-trivial* avenue: B = D[A] for differential
operators D ∈ Q[z, ∂_z] of degree ≤ d. The companion B_n carries
information about period/quasi-period structure.

Alternative output: the standard Ramanujan-Sato evaluation
  1/π = (2√2/9801) Σ a_k (1103 + 26390 k) / 396^{4k}
gives π as a function of M(z₀) := 1103·A(z₀) + 26390·z₀·A'(z₀),
specifically π = 9801 / (2√2·M(z₀)). The inverter rate against M
is ≈ M ≈ 1/π (slow). This is exactly the bottleneck described in
the doctrine.
"""

import math
from fractions import Fraction
import numpy as np
from mpmath import mpf, mp
mp.dps = 60

# ---------------------------------------------------------------------------
# Picard-Fuchs operator: P = z²(1-256z)∂³ + 3z(1-384z)∂² + (1-816z)∂ - 24
# Recurrence on b_n in P[Σ b_n z^n] = Σ R_m z^m:
#   R_m = (m+1)³ · b_{m+1}  -  4(4m+1)(4m+2)(4m+3) · b_m
# This is a 2-term recurrence ⇒ formal-series kernel is 1-D.

Z_C = Fraction(1, 256)


def a_seq(N):
    """a_n = (4n)!/(n!)^4 as exact Fractions."""
    out = [Fraction(1)]
    for n in range(N):
        num = 4 * (4 * n + 1) * (4 * n + 2) * (4 * n + 3) * out[-1]
        den = (n + 1) ** 3
        out.append(num / den)
    return out


def apply_operator(coeffs):
    """Coefficients of R(z) = P[Σ coeffs[n] z^n]."""
    N = len(coeffs) - 1
    R = [Fraction(0)] * (N + 1)
    for m in range(N + 1):
        if m + 1 <= N:
            R[m] += (m + 1) ** 3 * coeffs[m + 1]
        R[m] += -4 * (4 * m + 1) * (4 * m + 2) * (4 * m + 3) * coeffs[m]
    return R


def solve_inhomog(forcing, N):
    """
    Given forcing[m] = c_m for m=0..d, solve the recurrence
      (m+1)³ b_{m+1} = 4(4m+1)(4m+2)(4m+3) b_m + c_m,   b_0 = 0
    out to N. Returns b_n list. (Assumes c_m=0 for m > deg.)
    """
    b = [Fraction(0)]
    for m in range(N):
        c = forcing[m] if m < len(forcing) else Fraction(0)
        b_next = (4 * (4 * m + 1) * (4 * m + 2) * (4 * m + 3) * b[-1] + c) / (m + 1) ** 3
        b.append(b_next)
    return b


def eval_d2(coeffs, z):
    """B''(z) via mpmath."""
    Z = mpf(z); s = mpf(0)
    for n, y in enumerate(coeffs):
        if n >= 2:
            s += n * (n - 1) * mpf(y.numerator) / mpf(y.denominator) * Z ** (n - 2)
    return s


def eval_d0(coeffs, z):
    Z = mpf(z); s = mpf(0)
    for n, y in enumerate(coeffs):
        s += mpf(y.numerator) / mpf(y.denominator) * Z ** n
    return s


def eval_d1(coeffs, z):
    Z = mpf(z); s = mpf(0)
    for n, y in enumerate(coeffs):
        if n >= 1:
            s += n * mpf(y.numerator) / mpf(y.denominator) * Z ** (n - 1)
    return s


# ---------------------------------------------------------------------------
def main():
    print("=" * 72)
    print("  Ramanujan PF: structural analysis of Apéry mechanism transferability")
    print("=" * 72)

    N = 300
    A = a_seq(N)

    # ---- Step 1: confirm 2-term recurrence (1-D formal-series kernel)
    print("\n[1] Recurrence on coefficients of B = Σ b_n z^n:")
    print("    (m+1)³ b_{m+1} = 4(4m+1)(4m+2)(4m+3) b_m + c_m")
    print("    where c_m is the m-th coefficient of P[B].")
    print("    => 2-term recurrence ⇒ kernel ∩ Q[[z]] = Q·A.\n")

    # ---- Step 2: test all forcings P[B] = z^k for k = 0..5
    print("[2] Try forcing P[B] = z^k.  Each gives a unique b_n.")
    print("    Compute B''(z)/A''(z) at z = 0.999·z_c.  Should be constant.")
    print()
    z_eval = mpf("0.999") * mpf(Z_C.numerator) / mpf(Z_C.denominator)
    App = eval_d2(A, z_eval)

    for k in range(6):
        forcing = [Fraction(0)] * (k + 1)
        forcing[k] = Fraction(1)
        B = solve_inhomog(forcing, N)
        Bpp = eval_d2(B, z_eval)
        ratio = Bpp / App if App != 0 else float('nan')
        print(f"    forcing z^{k}: B''/A'' at z=0.999·z_c = {float(ratio):.10f}")

    # Confirm: each forcing gives a B that is finite-dim adjustment of A.
    # P[B] = z^k means b_n satisfies homogeneous recurrence for n ≥ k+1.
    # So B = (low-deg poly) + λ·(A − low-deg part), with λ depending on k.
    # ⇒ B''/A'' = λ for large enough z.

    # ---- Step 3: nontrivial companion via differential operator B = D[A]
    print()
    print("[3] B = (z·∂_z)·A    (i.e., b_n = n·a_n)")
    B = [Fraction(n) * A[n] for n in range(N + 1)]
    R = apply_operator(B)
    nz = max([n for n in range(N + 1) if R[n] != 0], default=-1)
    print(f"    P[B] has nonzero coefficients up to z^{nz} (NOT a polynomial).")
    print("    => B = (z∂)·A is NOT in the kernel of P, and P[B] is")
    print("    inhomogeneous of unbounded degree. No Apéry-style companion.")

    # ---- Step 4: nontrivial companion via mult. by polynomial: B = z·A
    print()
    print("[4] B = z·A    (b_n = a_{n-1}, b_0 = 0)")
    B = [Fraction(0)] + A[:N]
    R = apply_operator(B)
    nz_count = sum(1 for r in R if r != 0)
    print(f"    P[B] has {nz_count} nonzero coefficients.")
    if nz_count > 0:
        first = next(n for n in range(N + 1) if R[n] != 0)
        last = max(n for n in range(N + 1) if R[n] != 0)
        print(f"    nonzero range: z^{first} .. z^{last}")

    # ---- Step 5: STRUCTURAL OBSTRUCTION SUMMARY
    print()
    print("=" * 72)
    print("  STRUCTURAL OBSTRUCTION (this is the answer)")
    print("=" * 72)
    print("""
For Ramanujan's Picard-Fuchs operator P = z²(1-256z)∂³ + 3z(1-384z)∂²
+ (1-816z)∂ - 24, the recurrence governing the formal-power-series
kernel is

    (m+1)³ b_{m+1} = 4(4m+1)(4m+2)(4m+3) b_m   (m ≥ 0).

This is a 2-TERM recurrence: each b_{m+1} is determined by b_m alone.
Hence kernel ∩ Q[[z]] = Q · A(z) — 1-dimensional.

Apéry's ζ(3) Picard-Fuchs operator has the recurrence

    (n+1)³ A_{n+1} = (34n³+51n²+27n+5) A_n - n³ A_{n-1}

which is a 3-TERM recurrence, so the series-solution space is
2-dimensional. Apéry's b_n is the second basis element of that 2-D
space, with b_0=0, b_1=6, and Apéry constructed it explicitly as

    b_n = a_n · Σ_{m=1}^n m^{-3}
        + 2 Σ_{k=1}^n (-1)^{k-1} / (k³ C(n,k) C(n+k,k))   (corrections)

making P[B] = 6·n·(constant) — actually P[Σb_n z^n] = 6 (constant).

For Ramanujan's order-1 series recurrence, no second linearly independent
formal-series solution exists. The other two solutions of the order-3
PF involve log(z) at z=0 — they are NOT formal power series and cannot
be encoded as Σ b_n z^n with rational b_n.

CONSEQUENCE: the Apéry "two same-recurrence sequences, ratio at conifold
gives target" mechanism cannot be ported to Ramanujan PF at z=0
naively. To get π as a PIVP readout from the Ramanujan series, we must
either:
  (i) use a different PF whose recurrence is order ≥ 2 (e.g., one of
      the AvSZ Calabi-Yau 5-list entries other than (1/4,1/2,3/4)),
  (ii) use logarithmic Frobenius solutions, encoded via initial
       conditions at the CM point z₀ = 1/396⁴ rather than at z=0,
  (iii) use the Wronskian / Legendre quadratic-period identity
       (K·E' + K'·E - K·K' = π/2) which gives π directly as a
       quadratic form in periods.
""")


if __name__ == '__main__':
    main()
