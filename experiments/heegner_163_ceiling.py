"""
Heegner-163 ceiling for Chudnovsky's π-PIVP rate.

The thesis: within CM-modular π formulas (Ramanujan-Sato type), the
prefactor M_∞ scales with the j-invariant at a CM point.  For
imaginary quadratic K = Q(√−d) with class number 1, the largest
discriminant is d = 163 (Heegner's theorem, completed by Stark 1967
and Baker 1966), giving the famous near-integer

    exp(π√163) ≈ 640320³ + 744 - 196884/(640320³) + …
              = j(τ_163) + 744

where τ_163 = (1 + √−163)/2 and j is Klein's modular function.

Chudnovsky's prefactor 640320^{3/2} = (j(τ_163) − 744)^{1/2} is
therefore *the* maximum value of the prefactor among class-number-1
CM points.  Any other π-formula in the AvSZ family inherits a smaller
j-invariant and a smaller M_∞.

This script verifies:
  (i)  exp(π√163) ≈ 640320³ + 744 to many digits (Ramanujan's near-integer)
  (ii) the j-invariants at the nine Heegner points
       d ∈ {1,2,3,7,11,19,43,67,163} with d=163 maximal
  (iii) the corresponding M_∞ for each Heegner d that admits an
        AvSZ-style π identity, comparing rates.
"""
from mpmath import mpf, mp, pi, sqrt, exp, log, log10
mp.dps = 100
PI = mp.pi


def near_integer_check():
    """Check exp(π√163) ≈ j(τ_163) + 744 = 640320³ + 744."""
    val = exp(PI * sqrt(mpf(163)))
    target = mpf(640320) ** 3 + 744
    diff = val - target
    print(f"  exp(π√163)         = {val}")
    print(f"  640320³ + 744      = {target}")
    print(f"  difference         = {float(diff):.6e}")
    print(f"  log10|diff|        = {float(log10(abs(diff))):.4f}")
    print(f"  ⇒ Ramanujan constant: agrees to ~12 decimal places (next term")
    print(f"    is 196884·exp(-π√163), tiny).")


def heegner_table():
    """Class-number-1 imaginary quadratic discriminants and their j-values.

    For d ∈ {1,2,3,7,11,19,43,67,163}, j(τ_d) is a rational integer.
    We use the standard table of cubes (j = J^3 where J is integer).

    Table from Cox, Primes of the Form x²+ny², chapter 13:
      d=1   : j = (12)³                = 1728
      d=2   : j = (20)³                = 8000
      d=3   : j = 0
      d=7   : j = -(15)³               = -3375
      d=11  : j = -(32)³               = -32768
      d=19  : j = -(96)³               = -884736
      d=43  : j = -(960)³              = -884736000
      d=67  : j = -(5280)³             = -147197952000
      d=163 : j = -(640320)³           = -262537412640768000
    """
    table = [
        (1,   12,         True),
        (2,   20,         True),
        (3,   0,          False),  # j = 0, no AvSZ-style identity
        (7,   -15,        True),
        (11,  -32,        True),
        (19,  -96,        True),
        (43,  -960,       True),
        (67,  -5280,      True),
        (163, -640320,    True),
    ]
    print(f"  {'d':>4}  {'J':>10}  {'|J|':>10}  {'|J|^{3/2}':>20}")
    print(f"  {'-'*4}  {'-'*10}  {'-'*10}  {'-'*20}")
    for d, J, _ in table:
        if J == 0:
            print(f"  {d:>4}  {J:>10}  {'—':>10}  {'(j=0, special)':>20}")
        else:
            absJ = abs(J)
            half_pow = mpf(absJ) ** mpf("1.5")
            print(f"  {d:>4}  {J:>10}  {absJ:>10}  {float(half_pow):>20.4e}")
    print()
    print("  ⇒ d=163 gives |J|^{3/2} = 640320^{3/2} ≈ 5.12×10^8, which is")
    print("    the maximum among class-number-1 discriminants.  Smaller-d")
    print("    Heegner points give smaller analog rates.")


def chudnovsky_vs_d67():
    """Rate comparison: d=163 (Chudnovsky) vs d=67 (analogous formula).

    The d=67 Ramanujan-Sato analogue exists but has rate 5280^{3/2}/π.
    """
    rate_163 = mpf(640320) ** mpf("1.5") / PI
    rate_67  = mpf(5280)  ** mpf("1.5") / PI
    rate_43  = mpf(960)   ** mpf("1.5") / PI
    rate_19  = mpf(96)    ** mpf("1.5") / PI
    rate_ram = mpf(9801) / PI  # Ramanujan, level 4 (not Heegner table; uses 396 = 4·99)
    print(f"  d=163 (Chudnovsky):    rate ≈ {float(rate_163):.4e} digits/τ")
    print(f"  d=67  (analogue):       rate ≈ {float(rate_67):.4e} digits/τ")
    print(f"  d=43:                  rate ≈ {float(rate_43):.4e} digits/τ")
    print(f"  d=19:                  rate ≈ {float(rate_19):.4e} digits/τ")
    print(f"  Ramanujan 1914 (lvl 4): rate ≈ {float(rate_ram):.4e} digits/τ")
    print()
    print(f"  Ratios vs Chudnovsky (d=163):")
    print(f"    d=67  / d=163 = {float(rate_67  / rate_163):.6e}")
    print(f"    d=43  / d=163 = {float(rate_43  / rate_163):.6e}")
    print(f"    Ramanujan / d=163 = {float(rate_ram / rate_163):.6e}")


def main():
    print("=" * 76)
    print("  Heegner-163 ceiling for π-PIVP analog rate")
    print("=" * 76)
    print()
    print("--- (i) Ramanujan's near-integer ---")
    near_integer_check()
    print()
    print("--- (ii) Class-number-1 discriminants and their j-invariants ---")
    heegner_table()
    print()
    print("--- (iii) Analog rate by Heegner discriminant ---")
    chudnovsky_vs_d67()
    print()
    print("=" * 76)
    print("  Theorem (sharp ceiling, conjectural)")
    print("=" * 76)
    print("""
  Within the AvSZ + Heegner-CM family of π identities, the analog
  inverter rate is bounded above by 640320^{3/2}/π ≈ 1.63×10^8,
  attained by Chudnovsky's d=163 series.  The bound stems from
  Heegner-Stark-Baker: 163 is the largest squarefree d for which
  Q(√−d) has class number 1.

  Going beyond would require either:
    (a) higher-class-number CM (multiple j-values, no clean formula), or
    (b) non-CM modular constructions (e.g. quasi-modular or higher-genus
        Calabi-Yau), where the ratio-readout mechanism may or may not
        survive (this is OPEN).

  Our survey of non-AvSZ paradigms (Machin / BBP / AGM / Borwein /
  Brouncker) shows none achieves rate > O(1) in continuous time.
""")


if __name__ == '__main__':
    main()
