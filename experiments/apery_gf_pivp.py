"""
Apéry generating function holonomic ODE → explicit 4-variable PIVP.

Original ODE:
    x²(4−x) f''' + x(10−3x) f'' + (2−x) f' = 1

First-order system. Let (x, y₁, y₂, y₃) = (x, f, f', f'').
Direct form (non-polynomial because of 1/[x²(4−x)]):
    y₁' = y₂
    y₂' = y₃
    y₃' = [1 − x(10−3x)·y₃ − (2−x)·y₂] / [x²(4−x)]

To get polynomial RHS, rescale time: let dτ = dt / [x²(4−x)].
With ẏ = dy/dτ, the system becomes:

    ẋ  = x²(4−x)                            (x-flow, forces x to evolve)
    ẏ₁ = x²(4−x) · y₂                       (y₁ = f)
    ẏ₂ = x²(4−x) · y₃                       (y₂ = f')
    ẏ₃ = 1 − x(10−3x)·y₃ − (2−x)·y₂         (y₃ = f'')

This IS a 4-variable degree-≤4 polynomial autonomous system. PIVP formally.

## The obstruction (not hidden — write it down)

x = 0 is a fixed point of ẋ = x²(4−x). So starting from x₀ = 0 we cannot
evolve. To evaluate f(1), we must start from some x₀ > 0 and integrate
until x reaches 1. The τ-time to traverse (x₀, 1] is:
    T(x₀) = ∫_{x₀}^1 dx / [x²(4−x)]
         = (1/4)·[1/x − (1/4)·log((4−x)/x)] evaluated from x₀ to 1
         = finite for any x₀ > 0, → ∞ as x₀ → 0⁺.

Initial data at x = x₀:
    y₁(0) = f(x₀),  y₂(0) = f'(x₀),  y₃(0) = f''(x₀)
where the series ∑ xⁿ/(n³·C(2n,n)) converges fast enough to get these
to rational precision with ~r terms. So for each rational x₀, the PIVP
needs rational IC from the Frobenius series — it's a *family* of
approximants, one per x₀. This is the zero-IC open problem noted in
FINDINGS.md: is there a single PIVP that starts at fully rational IC
(e.g., all zeros) and still evaluates f(1)? Unknown.

## What this script does

1. Define the 4-variable polynomial RHS explicitly.
2. Integrate numerically from x₀ = 0.01 with Frobenius-series IC.
3. Check that y₁ at τ such that x(τ) = 1 equals f(1) = −(2/5)·ζ(3)
   (for F(x)=f(−x) it's +(2/5)·ζ(3) at x=1; we use F-form below).
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta

# Work with F(x) = Σ (-1)^(n-1) x^n / (n³ C(2n,n)), F(1) = (2/5)·ζ(3).
# ODE for F: x²(4+x) F''' + x(10+3x) F'' + (2+x) F' = 1
# Change sign conventions: let u = x, coefficients
# P3 = u²(4+u), P2 = u(10+3u), P1 = 2+u, RHS=1


def series_ICs(x0, N=200):
    """Partial sum of F(x) = Σ (-1)^(n-1) xⁿ / (n³ C(2n,n)) and derivatives at x0."""
    F = Fp = Fpp = 0.0
    # a_n = (-1)^(n-1) / (n³·C(2n,n))
    from math import comb
    for n in range(1, N+1):
        a = ((-1)**(n-1)) / (n**3 * comb(2*n, n))
        F   += a * x0**n
        Fp  += a * n * x0**(n-1) if n >= 1 else 0.0
        Fpp += a * n * (n-1) * x0**(n-2) if n >= 2 else 0.0
    return F, Fp, Fpp


def rhs(tau, state):
    x, y1, y2, y3 = state
    xscale = x**2 * (4 + x)  # for F-form
    return [
        xscale,                                          # dx/dτ
        xscale * y2,                                     # dy1/dτ
        xscale * y3,                                     # dy2/dτ
        1 - x*(10 + 3*x)*y3 - (2 + x)*y2,                # dy3/dτ
    ]


def target_tau(x0, x1):
    """τ-time to go from x0 to x1 along ẋ = x²(4+x)."""
    # Integrate dx / [x²(4+x)]
    from scipy.integrate import quad
    T, _ = quad(lambda x: 1 / (x**2 * (4 + x)), x0, x1)
    return T


def run(x0=0.01):
    F0, Fp0, Fpp0 = series_ICs(x0, N=400)
    print(f"Start at x0 = {x0}")
    print(f"  F(x0)   ≈ {F0:.12f}")
    print(f"  F'(x0)  ≈ {Fp0:.12f}")
    print(f"  F''(x0) ≈ {Fpp0:.12f}")
    state0 = [x0, F0, Fp0, Fpp0]

    T = target_tau(x0, 1.0)
    print(f"\nτ-time to reach x=1: {T:.6f}")

    # Integrate with τ-events: stop when x = 1
    def hit_one(tau, state):
        return state[0] - 1.0
    hit_one.terminal = True
    hit_one.direction = 1

    sol = solve_ivp(rhs, (0, 2*T), state0, method="DOP853",
                    rtol=1e-13, atol=1e-15, events=hit_one)

    print(f"\nIntegration stopped at τ = {sol.t[-1]:.6f}  (expected {T:.6f})")
    print(f"x at end: {sol.y[0,-1]:.12f}  (expected 1.0)")
    print(f"F(1) computed:  {sol.y[1,-1]:.12f}")
    target = (2/5) * zeta(3)
    print(f"(2/5)·ζ(3):     {target:.12f}")
    print(f"|err|: {abs(sol.y[1,-1] - target):.3e}")


if __name__ == "__main__":
    for x0 in [0.1, 0.01, 0.001]:
        print("=" * 60)
        run(x0=x0)
        print()
