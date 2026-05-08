"""
化除法为减法 + 余项 GF + variation：Ramanujan/π without inverting 1/π.

Setup. Ramanujan 1914 says

  1/π = (2√2/9801) · M,    M = Σ_{k≥0} a_k (1103 + 26390 k) / 396^{4k}

so π = 9801 / (2√2 · M), where M ≈ 1102.67 is the *large* limit value.

Two ways to encode π:

(A) NAIVE: encode 1/π directly, then run inverter
        dP/dτ = 1 - (1/π) · P
    Fixed point P = π; linearisation rate = 1/π ≈ 0.318. SLOW.

(B) SUBTRACTION: rewrite π = 9801 / (2√2 · M), invert against M
        dP/dτ = 9801 - 2√2 · M · P
    Fixed point: 2√2 · M · P = 9801 ⇒ P = 9801/(2√2·M) = π.
    Linearisation rate at FP: |∂_P f| = 2√2 · M_∞ = 9801/π ≈ 3120.
    FAST — rate is set by *M*, not by *1/π*.

This is the 'change division to subtraction' trick: don't compute the
small reciprocal, recognise that π is *already* expressed as a scaled
inverse of a large quantity M, and invert the large quantity directly.

Numerical verification follows.
"""

import math
from mpmath import mpf, mp
mp.dps = 50

PI = mp.pi

# ---------------------------------------------------------------------------
# Compute M = Σ a_k (1103 + 26390 k) / 396^{4k} numerically (mpmath).

def ramanujan_M(N=80):
    a = mpf(1)
    s = mpf(1103)
    for k in range(1, N + 1):
        # a_k / a_{k-1} = 4(4k-3)(4k-2)(4k-1)/k^3
        a = a * 4 * (4*k - 3) * (4*k - 2) * (4*k - 1) / mpf(k) ** 3
        s += a * (1103 + 26390 * k) / mpf(396) ** (4 * k)
    return s


def main():
    print("=" * 72)
    print("  化除法为减法: π via the large Ramanujan sum M, not 1/π")
    print("=" * 72)
    M = ramanujan_M(80)
    print(f"\nRamanujan partial sum (N=80):")
    print(f"  M  = {M}")
    print(f"  9801/(2√2·M)         = {9801 / (2 * mp.sqrt(2) * M)}")
    print(f"  π                    = {PI}")
    print(f"  difference            = {9801 / (2 * mp.sqrt(2) * M) - PI}")

    print("\n--- (A) NAIVE inverter against 1/π ---")
    I = 1 / PI
    print(f"  Inverter ODE: dP/dτ = 1 - I·P,  I = 1/π ≈ {float(I):.6f}")
    print(f"  FP: P = 1/I = π ≈ {float(PI):.6f}")
    print(f"  Linearisation rate: |∂_P f| = I = 1/π ≈ {float(I):.6f}")
    # Simulate
    P = mpf(0)
    dt = mpf("0.01")
    for n in range(int(50 / dt)):  # τ up to 50
        P += dt * (1 - I * P)
    print(f"  After τ=50: P = {float(P):.10f},  error |P-π| = {float(abs(P-PI)):.2e}")

    print("\n--- (B) SUBTRACTION: invert against M directly ---")
    print(f"  Inverter ODE: dP/dτ = 9801 - 2√2·M·P")
    print(f"  FP: P = 9801/(2√2·M) = π ≈ {float(PI):.6f}")
    rate_B = 2 * mp.sqrt(2) * M
    print(f"  Linearisation rate: |∂_P f| = 2√2·M ≈ {float(rate_B):.4f}")
    print(f"  Speedup over (A): factor {float(rate_B / I):.4f} ≈ 9801")
    P = mpf(0)
    dt = mpf("0.0001")  # smaller dt because rate ~3120
    for n in range(int(0.05 / dt)):  # τ up to 0.05
        P += dt * (9801 - 2 * mp.sqrt(2) * M * P)
    print(f"  After τ=0.05: P = {float(P):.10f},  error |P-π| = {float(abs(P-PI)):.2e}")

    print("\n--- Reach ε=1e-15 precision: τ comparison ---")
    tau_naive = float(PI * math.log(1e15))   # rate 1/π → τ = π·log(1/ε)
    tau_sub   = float(PI / 9801 * math.log(1e15))  # rate 9801/π → τ = (π/9801)·log(1/ε)
    print(f"  (A) τ_ε = π · log(10^15)         ≈ {tau_naive:.4f}")
    print(f"  (B) τ_ε = (π/9801) · log(10^15)  ≈ {tau_sub:.6f}")
    print(f"  ratio: (B)/(A) = 1/9801 ≈ {tau_sub/tau_naive:.6e}")

    print("\n" + "=" * 72)
    print("  Why this is the 'subtraction' trick, not a τ-rescaling")
    print("=" * 72)
    print("""
The two ODEs are related by the trivial scaling

  9801 - 2√2·M·P  ≡  9801 · [1 - (2√2 M / 9801)·P]
                  ≡  9801 · [1 - (1/π)·P].

So (B) is just (A) multiplied by the constant 9801 — equivalent to
substituting τ' = 9801·τ. The rate per unit τ' is 1/π; the rate per
unit τ is 9801/π.

In *abstract* PIVP this is just a time-rescaling. In *bounded analog
complexity* (Huang–Chen 2026), the time modulus is measured against
the natural τ of the encoding ODE — and (B)'s τ-modulus is smaller by
factor 9801.

The 化除法为减法 move is therefore: (i) write π = 9801/(2√2·M),
making the relevant denominator be the *large* M ≈ 1102 instead of
the *small* 1/π ≈ 0.318; (ii) the natural inverter against M is
amplified by the same scale factor 9801, giving rate 9801/π.

This buys an O(9801)-factor reduction in time modulus 'for free'
(only by absorbing rational constants into the ODE coefficients).

Combined with the rate-k logistic inverter (blog 007), the total rate
becomes k · 9801/π — both speedups stack multiplicatively.
""")


if __name__ == '__main__':
    main()
