"""
Chudnovsky 1989 series for 1/π — explicit PIVP construction and rate
calculation.

The Chudnovsky identity:
    (640320)^{3/2} / (12 π)  =  Σ_{k≥0}  (-1)^k a_k · (A + B k) / 640320^{3k}
    where  a_k = (6k)! / ((3k)! (k!)^3),
           A = 13591409,
           B = 545140134.

Rate analysis under 化除法为减法 (write π = 640320^{3/2}/(12·M_∞), invert
against M_∞):

    dP/dτ = 640320^{3/2} - 12·M·P,    rate 12·M_∞ at FP.

Correcting my earlier memory entry which claimed M_∞ ≈ 5.36×10^14:
this was WRONG.  The correct value is M_∞ ≈ 1.36×10^7, giving rate
~1.6×10^8 per unit τ, about 5×10^4 times faster than Ramanujan's ~3120.

Still substantial but not 10^11.
"""
from mpmath import mpf, mp, pi, sqrt, log
mp.dps = 80

PI = mp.pi


def chudnovsky_M(N=30):
    """Compute M_∞ via direct series."""
    a = mpf(1)  # a_0 = 1
    A = mpf(13591409)
    B = mpf(545140134)
    s = A  # k=0 term: (+1) * 1 * A / 640320^0 = A
    z = mpf(1) / mpf(640320)**3
    zpow = z  # (-z)^k for k=1: but Chudnovsky has (-1)^k 1/640320^{3k}, so we use (-z)^k
    sign = -1
    for k in range(1, N + 1):
        # a_{k}/a_{k-1} = (6k-5)(6k-4)(6k-3)(6k-2)(6k-1)(6k) / [(3k-2)(3k-1)(3k) · k^3]
        a = a * (6*k-5) * (6*k-4) * (6*k-3) * (6*k-2) * (6*k-1) * (6*k) / (
            (3*k-2) * (3*k-1) * (3*k) * k**3
        )
        s += sign * a * (A + B*k) * zpow
        zpow *= z
        sign = -sign
    return s


def main():
    print("=" * 70)
    print("  Chudnovsky 1989 π-series: rate analysis")
    print("=" * 70)
    print()

    M_inf = chudnovsky_M(40)
    print(f"  M_∞ (N=40)               = {M_inf}")

    target = mpf(640320)**(mpf(3)/2) / (12 * PI)
    print(f"  640320^{{3/2}} / (12·π)    = {target}")
    print(f"  difference                 = {M_inf - target}")
    print()

    rate_chud = 12 * M_inf  # = 640320^{3/2}/π
    rate_naive = 1 / PI
    rate_ramanujan = 9801 / PI

    print(f"  Inverter rate analysis:")
    print(f"    Naive  dP/dτ = 1 - (1/π)·P:           rate = 1/π ≈ {float(rate_naive):.6f}")
    print(f"    Ramanujan dP/dτ = 9801 - 2√2·M·P:     rate = 9801/π ≈ {float(rate_ramanujan):.4f}")
    print(f"    Chudnovsky dP/dτ = 640320^{{3/2}} - 12·M·P:")
    print(f"                                          rate = 12·M_∞ ≈ {float(rate_chud):.4f}")
    print()
    print(f"  Speedup factors:")
    print(f"    Ramanujan / Naive       = 9801                        ≈ {9801}")
    print(f"    Chudnovsky / Naive      = 640320^{{3/2}}                ≈ {float(640320**1.5):.4e}")
    print(f"    Chudnovsky / Ramanujan  = 640320^{{3/2}} / 9801          ≈ {float(640320**1.5 / 9801):.4f}")
    print()

    # Per-term geometric decay
    decay = mpf(640320)**3 / (6 * 5 * 4 * 3 * 2 * 1)  # rough leading-order
    # More precisely a_{k+1}/a_k · (1/640320^3) → ?
    # ratio = (6k)(6k-1)(6k-2)(6k-3)(6k-4)(6k-5) / ((3k)(3k-1)(3k-2)k^3) · 1/640320^3
    # leading k → ∞: 6^6 k^6 / (27 k^3 · k^3) / 640320^3 = 46656/27 / 640320^3 = 1728/640320^3
    asymp_ratio = mpf(1728) / mpf(640320)**3
    print(f"  Per-term decay rate (k → ∞):   1728/640320³ = {asymp_ratio}")
    print(f"  Equivalent digits/term:        {-float(log(asymp_ratio)/log(10)):.4f}")
    print()
    print("  ⇒ Chudnovsky converges ~14.18 digits per term, vs Ramanujan's")
    print("    8 digits/term.  But raw arithmetic per term costs ~6×.")
    print()

    # Memory-correction note
    print("=" * 70)
    print("  Correction note")
    print("=" * 70)
    print("""
  The earlier (2026-04-25 first pass) doctrine §3.5 / memory entry
  claimed the Chudnovsky speedup factor over Ramanujan was ~10^11.
  This was WRONG — it confused 640320^{3/2} (≈ 5.12×10^8) with some
  larger value.

  The correct comparison:
    Ramanujan:   prefactor 9801,             rate ≈ 3120
    Chudnovsky:  prefactor 640320^{3/2},     rate ≈ 1.63×10^8

  So the multiplicative speedup is

    Chudnovsky / Ramanujan  =  640320^{3/2} / 9801  ≈  52,278.

  About 5×10^4, not 10^11.  Still a substantial structural gain
  beyond Ramanujan, but bounded — within the AvSZ family there is no
  clean exponentially better π-PIVP.
""")


if __name__ == '__main__':
    main()
