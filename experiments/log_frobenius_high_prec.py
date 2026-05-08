"""
High-precision check: what is the conifold ratio B''(z)/A''(z) for the
log-Frobenius companion B = ∂_ρ A(z,ρ)|_{ρ=0}?

Earlier (ramanujan_apery_pi.py at N=200, z=0.9999·z_c) gave ~5.538.
8·log(2) = 5.5452 is suspiciously close — verify with higher N and
closer-to-conifold z.
"""
import math
from fractions import Fraction
from mpmath import mpf, mp
mp.dps = 100


def a_seq(N):
    out = [Fraction(1)]
    for n in range(N):
        out.append(4 * (4*n+1) * (4*n+2) * (4*n+3) * out[-1] / Fraction((n+1)**3))
    return out


def frobenius_b_seq(N):
    """b_n = ∂a_n/∂ρ|_{ρ=0}.  Equivalent form:
       b_n = a_n · Σ_{k=0}^{n-1} [4/(4k+1) + 2/(2k+1) + 4/(4k+3) − 3/(k+1)]."""
    A = a_seq(N)
    W = [Fraction(0)]
    for k in range(N):
        W.append(W[-1] + Fraction(4, 4*k+1) + Fraction(2, 2*k+1)
                       + Fraction(4, 4*k+3) - Fraction(3, k+1))
    return [A[n] * W[n] for n in range(N+1)]


def eval_d2(coeffs, z):
    Z = mpf(z); s = mpf(0)
    for n, y in enumerate(coeffs):
        if n >= 2:
            s += n * (n-1) * mpf(y.numerator) / mpf(y.denominator) * Z ** (n-2)
    return s


def main():
    print("High-precision conifold ratio for log-Frobenius companion:")
    print(f"  Hypothesis A:  ratio = 8·log(2) = {8 * mp.log(2)}")
    print(f"  Hypothesis B:  ratio = (something else, π-related)\n")

    Z_C = mpf(1) / 256
    target = 8 * mp.log(2)

    for N in [500, 1000, 1500, 2000]:
        print(f"  N = {N}:")
        A = a_seq(N)
        B = frobenius_b_seq(N)
        for frac_str in ["0.999", "0.9999", "0.99999", "0.999999", "0.9999999"]:
            z = mpf(frac_str) * Z_C
            App = eval_d2(A, z)
            Bpp = eval_d2(B, z)
            r = Bpp / App
            print(f"    z/z_c = {frac_str:10s}  ratio = {r}")
            print(f"                            ratio - 8·log(2) = {float(r - target):+.4e}")
        print()


if __name__ == "__main__":
    main()
