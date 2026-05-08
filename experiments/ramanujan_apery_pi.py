"""
Apéry-style mechanism for π via Ramanujan's Picard-Fuchs ODE.

Adaptation of Xiang's ζ(3) construction (apery-adaptation-zeta3) to the
Ramanujan family. The mechanism:

  1. Ramanujan's hypergeometric g(z) = ₃F₂(1/4,1/2,3/4;1,1;256z) satisfies
     the third-order Picard-Fuchs ODE

        p(z) g''' + q(z) g'' + r(z) g' + s(z) g = 0

     with p(z) = z²(1−256z), q(z) = 3z(1−384z),
          r(z) = 1−816z,     s(z) = −24.

  2. The conifold is at z_c = 1/256. Indicial analysis (computed
     analytically below) gives exponents ρ ∈ {0, 1/2, 1}. The ρ=1/2
     local solution φ₁ has √(1−256z) branch behavior; its second
     derivative φ₁''(z) ~ (1−256z)^{−3/2} blows up at the conifold.

  3. Define A(z) = g(z) = Σ a_n z^n with a_n = (4n)!/(n!)⁴. Both A(z)
     and a hypothetical "companion" B(z) (with a different prescribed
     evaluation of the same operator, P[B] = c · const) carry a φ₁
     component and have second derivatives blowing up at z_c.

  4. The ratio B''(z)/A''(z) → β₁/α₁ as z → z_c, where (α_i, β_i) are
     the conifold-basis components of A and B respectively. By the
     Apéry mechanism, β₁/α₁ is the target arithmetic constant.

This script:
  - verifies the indicial exponents at z_c numerically
  - identifies a candidate companion sequence B(z) (Apéry-style
    harmonic-weighted) whose generating function satisfies P[B] = const
  - computes B''/A'' numerically as z → 1/256 and reports the limit

Run:  python3 ramanujan_apery_pi.py
"""

import math
from fractions import Fraction
import numpy as np
from mpmath import mpf, mp
mp.dps = 50

# ---------------------------------------------------------------------------
# Picard-Fuchs operator coefficients

def p_z(z):
    return z * z * (1 - 256 * z)

def q_z(z):
    return 3 * z * (1 - 384 * z)

def r_z(z):
    return 1 - 816 * z

def s_z(z):
    return -24

Z_C = 1.0 / 256.0  # conifold


# ---------------------------------------------------------------------------
# Verify indicial polynomial at z_c

def indicial_at_conifold():
    """
    Substitute y(z) = (1−256z)^ρ into the ODE p y''' + q y'' + r y' + s y
    and extract the leading coefficient in (1−256z)^(ρ−2).

    Result: −128 ρ (ρ−1) (2ρ − 1).
    """
    print("[indicial] expected exponents from −128 ρ(ρ−1)(2ρ−1) = 0:")
    print("           ρ ∈ {0, 1/2, 1}")
    print("[indicial] φ₁(z) ~ (1−256z)^{1/2}, so φ₁''(z) ~ (1−256z)^{−3/2}.")


# ---------------------------------------------------------------------------
# Sequences

def a_seq(N):
    """a_n = (4n)!/(n!)^4 as exact rationals (= Fraction with den 1)."""
    out = [Fraction(1)]
    for n in range(N):
        # (n+1)^3 a_{n+1} = 4 (4n+1)(4n+2)(4n+3) a_n
        num = 4 * (4 * n + 1) * (4 * n + 2) * (4 * n + 3) * out[-1]
        den = (n + 1) ** 3
        out.append(num / den)
    return out


def harmonic_b_seq(N, weight_power=1):
    """
    Candidate Apéry-style companion: b_n = a_n * H_n^(weight_power)
    where H_n^(p) := Σ_{k=1}^n 1/k^p.

    Try several weight powers; the right one (if it exists) makes the
    Picard-Fuchs operator applied to B(z) = Σ b_n z^n yield a
    polynomial-in-z forcing of low degree.
    """
    A = a_seq(N)
    H = [Fraction(0)]
    for k in range(1, N + 1):
        H.append(H[-1] + Fraction(1, k ** weight_power))
    return [A[n] * H[n] for n in range(N + 1)]


def shifted_b_seq(N):
    """b_n := n · a_n.  Try this as a baseline."""
    A = a_seq(N)
    return [Fraction(n) * A[n] for n in range(N + 1)]


def frobenius_b_seq(N):
    """
    Second Frobenius solution at z=0.  Since the indicial polynomial at
    z=0 is ρ³ (triple root 0), the second solution is
        y_1(z) = log(z) · A(z) + Σ b_n z^n
    where b_n = ∂a_n(ρ)/∂ρ |_{ρ=0}.

    a_n(ρ) = (1/4+ρ)_n (1/2+ρ)_n (3/4+ρ)_n · 4^(3n) / (1+ρ)_n^3.

    So  b_n / a_n = Σ_{k=0}^{n-1} [ψ(k+1/4) + ψ(k+1/2) + ψ(k+3/4)
                                    − 3 ψ(k+1)]   evaluated at ρ=0
                  = Σ_{k=0}^{n-1} [1/(k+1/4) + 1/(k+1/2) + 1/(k+3/4)
                                   − 3/(k+1)]      (telescoping log-derivs).
    """
    A = a_seq(N)
    # accumulator W_n = Σ_{k=0}^{n-1} [1/(k+1/4)+1/(k+1/2)+1/(k+3/4) − 3/(k+1)]
    W = [Fraction(0)]
    for k in range(N):
        term = (Fraction(1, 4 * k + 1) * 4
                + Fraction(1, 2 * k + 1) * 2
                + Fraction(1, 4 * k + 3) * 4
                - Fraction(3, k + 1))
        W.append(W[-1] + term)
    return [A[n] * W[n] for n in range(N + 1)]


def frobenius_c_seq(N):
    """
    Third Frobenius solution coefficient: c_n = (1/2) ∂²a_n/∂ρ² |_{ρ=0}.
    Using log-derivative form,
        c_n / a_n = (1/2) [ W_n^2 + V_n ]
    where  V_n = Σ_{k=0}^{n-1} [−1/(k+1/4)² − 1/(k+1/2)² − 1/(k+3/4)²
                                + 3/(k+1)²].
    """
    A = a_seq(N)
    W = [Fraction(0)]
    V = [Fraction(0)]
    for k in range(N):
        w_term = (Fraction(1, 4 * k + 1) * 4
                  + Fraction(1, 2 * k + 1) * 2
                  + Fraction(1, 4 * k + 3) * 4
                  - Fraction(3, k + 1))
        v_term = (- Fraction(16, (4 * k + 1) ** 2)
                  - Fraction(4, (2 * k + 1) ** 2)
                  - Fraction(16, (4 * k + 3) ** 2)
                  + Fraction(3, (k + 1) ** 2))
        W.append(W[-1] + w_term)
        V.append(V[-1] + v_term)
    return [A[n] * (W[n] * W[n] + V[n]) / 2 for n in range(N + 1)]


# ---------------------------------------------------------------------------
# Apply ODE operator P[y] to a power series Σ y_n z^n

def apply_operator(coeffs):
    """
    Given y_n for n=0..N (coeffs[n]), return the coefficients R_n of
    R(z) = p(z) y''' + q(z) y'' + r(z) y' + s(z) y
         = z²(1−256z) y''' + 3z(1−384z) y'' + (1−816z) y' − 24 y.

    R_n = coefficient of z^n in R(z).

    y' = Σ n y_n z^(n−1)
    y'' = Σ n(n−1) y_n z^(n−2)
    y''' = Σ n(n−1)(n−2) y_n z^(n−3)

    z² y''' has coefficient n(n−1)(n−2) y_n at z^(n−1)
    256 z³ y''' has coefficient n(n−1)(n−2) y_n at z^n
        so z² y''' − 256 z³ y''' coeff at z^m: (m+1)m(m−1) y_{m+1} − 256 m(m−1)(m−2) y_m
    3z y'' has coeff at z^m: 3 m(m−1)(m+1)... wait let me redo carefully.

    Coefficient of z^m in:
      z² y''' = sum over n: n(n−1)(n−2) y_n z^(n+(−3)+2) = n(n−1)(n−2) y_n z^(n−1)
        contributing at m: with n−1=m, so n=m+1: (m+1)m(m−1) y_{m+1}
      −256 z³ y''' = at m: with n=m: n(n−1)(n−2) y_n = m(m−1)(m−2) y_m, multiplied by −256
      3z y'' = 3 sum n(n−1) y_n z^(n−1), at m: 3 (m+1) m y_{m+1}
      −1152 z² y'' = at m: −1152 m(m−1) y_m
      y' = sum n y_n z^(n−1), at m: (m+1) y_{m+1}
      −816 z y' = at m: −816 m y_m
      −24 y = at m: −24 y_m
    """
    N = len(coeffs) - 1
    R = [Fraction(0)] * (N + 1)
    for m in range(N + 1):
        # z² y'''
        if m + 1 <= N:
            R[m] += (m + 1) * m * (m - 1) * coeffs[m + 1]
        # −256 z³ y'''
        R[m] += -256 * m * (m - 1) * (m - 2) * coeffs[m]
        # 3 z y''
        if m + 1 <= N:
            R[m] += 3 * (m + 1) * m * coeffs[m + 1]
        # −1152 z² y''
        R[m] += -1152 * m * (m - 1) * coeffs[m]
        # y'
        if m + 1 <= N:
            R[m] += (m + 1) * coeffs[m + 1]
        # −816 z y'
        R[m] += -816 * m * coeffs[m]
        # −24 y
        R[m] += -24 * coeffs[m]
    return R


# ---------------------------------------------------------------------------
# Numerical evaluation of A, A', A'', B, B', B'' at points near z_c

def eval_series(coeffs, z, derivative=0):
    """Σ n(n−1)...(n−d+1) y_n z^(n−d) for derivative=d.  Uses mpmath."""
    Z = mpf(z)
    s = mpf(0)
    if derivative == 0:
        for n, y in enumerate(coeffs):
            s += mpf(y.numerator) / mpf(y.denominator) * Z ** n
    elif derivative == 1:
        for n, y in enumerate(coeffs):
            if n >= 1:
                s += n * mpf(y.numerator) / mpf(y.denominator) * Z ** (n - 1)
    elif derivative == 2:
        for n, y in enumerate(coeffs):
            if n >= 2:
                s += n * (n - 1) * mpf(y.numerator) / mpf(y.denominator) * Z ** (n - 2)
    return s


# ---------------------------------------------------------------------------
# Main experiment

def main():
    print("=" * 72)
    print("  Apéry-style mechanism for π via Ramanujan's Picard-Fuchs ODE")
    print("=" * 72)

    indicial_at_conifold()
    print()

    # Verify P[A] = 0 (A is a homogeneous solution)
    N = 200
    A = a_seq(N)
    R_A = apply_operator(A)
    nonzero = [(n, R_A[n]) for n in range(N + 1) if R_A[n] != 0]
    print(f"[homog]  P[A] = 0?  number of nonzero coefficients up to z^{N}: {len(nonzero)}")
    if nonzero:
        for n, v in nonzero[:5]:
            print(f"           coeff z^{n}: {v}")

    print()

    # Try several companion sequences and see what P[B] looks like
    print(f"[trial]  computing P[B] for several candidate B(z) = Σ b_n z^n ...")

    candidates = [
        ("b_n = ∂a_n/∂ρ|_0   (second Frobenius)",  frobenius_b_seq(N)),
        ("c_n = ∂²a_n/(2∂ρ²)|_0  (third Frobenius)", frobenius_c_seq(N)),
        ("b_n = n · a_n",                          shifted_b_seq(N)),
        ("b_n = a_n · H_n^(1)  (harmonic, p=1)",   harmonic_b_seq(N, 1)),
        ("b_n = a_n · H_n^(2)  (harmonic, p=2)",   harmonic_b_seq(N, 2)),
        ("b_n = a_n · H_n^(3)  (harmonic, p=3)",   harmonic_b_seq(N, 3)),
    ]

    for name, B in candidates:
        R_B = apply_operator(B)
        # Look at the first few coefficients
        print(f"\n  {name}")
        for n in range(8):
            print(f"      P[B] coeff z^{n} = {R_B[n]}")
        # Check if it's a polynomial of low degree
        nz = [n for n in range(N + 1) if R_B[n] != 0]
        if nz:
            max_nonzero = max(nz)
            print(f"      P[B] has nonzero coeffs up to z^{max_nonzero}")
        else:
            print(f"      P[B] = 0 (B would be a homogeneous solution)")

    print()
    print("=" * 72)
    print("  Numerical: A''(z)/B''(z) for various B candidates as z → z_c")
    print("=" * 72)

    # Evaluate near conifold
    test_zs = [0.5 * Z_C, 0.9 * Z_C, 0.99 * Z_C, 0.999 * Z_C, 0.9999 * Z_C]

    for name, B in candidates:
        print(f"\n  {name}")
        print(f"    z/z_c    A''(z)         B''(z)         B''/A''")
        for z in test_zs:
            App = eval_series(A, z, derivative=2)
            Bpp = eval_series(B, z, derivative=2)
            ratio = Bpp / App if App != 0 else mpf('nan')
            print(f"    {z/Z_C:.4f}  {float(App):14.6e}  {float(Bpp):14.6e}  {float(ratio):18.10f}")
        # Final compare with π, π², 1/π, 2/π, etc.
        z = test_zs[-1]
        ratio = float(eval_series(B, z, derivative=2) / eval_series(A, z, derivative=2))
        comparisons = [
            ("π",       math.pi),
            ("π²",      math.pi ** 2),
            ("π/2",     math.pi / 2),
            ("π²/6",    math.pi ** 2 / 6),
            ("1/π",     1.0 / math.pi),
            ("2/π",     2.0 / math.pi),
            ("π/√2",    math.pi / math.sqrt(2.0)),
            ("π²/8",    math.pi ** 2 / 8),
            ("π·log2",  math.pi * math.log(2.0)),
            ("log2·2",  math.log(2.0) * 2.0),
        ]
        for label, val in comparisons:
            print(f"      ratio / ({label})  =  {ratio / val:.6f}")


if __name__ == '__main__':
    main()
