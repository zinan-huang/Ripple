"""
5-variable polynomial PIVP for ζ(3) via Fermi-Dirac integral,
with the rational 2/3 prefactor absorbed directly into Ṡ so that
S(∞) = ζ(3) with no trailing scaling step.

Identity: (2/3) · ∫₀^∞ x² / (1 + eˣ) dx = ζ(3)

State variables (all bounded on [0, ∞)):
    a = e^(-t)         ∈ (0, 1]
    b = t · e^(-t)     ∈ [0, 1/e]
    c = t² · e^(-t)    ∈ [0, 4/e²]
    r = 1 / (1 + eᵗ) = a/(1+a)  ∈ (0, 1/2]
    S = ∫₀ᵗ x²/(1+eˣ) dx, target (3/2)ζ(3) ≈ 1.80308

Polynomial dynamics:
    ȧ = -a
    ḃ = a - b
    ċ = 2b - c
    ṙ = a·r²      [since r = 1/(1+eᵗ), ṙ = -eᵗ/(1+eᵗ)² = -(1-r)(r) = r² - r,
                   but we want purely polynomial; use r = a/(1+a),
                   ṙ = ȧ/(1+a) - a·ȧ/(1+a)² = -a/(1+a) + a²/(1+a)²
                      = -r + r·a/(1+a) · ... — let's rederive.]

Actually the cleanest form: let q = 1/(1+a), so r = a·q. Then q̇ = -ȧ·q² = a·q².
    q̇ = a·q²
    r = a·q, so ṙ = ȧq + aq̇ = -aq + a·aq² = -aq + a²q² = -r + r·(aq) = -r + r·r = r² - r.
So ṙ = r² - r, no need for q.

Actually wait: r = 1/(1+eᵗ), not 1/(1+a). Let me redo.
    r = 1/(1+eᵗ)
    ṙ = -eᵗ/(1+eᵗ)² = -(1-r)·r       (since eᵗ/(1+eᵗ) = 1-r)
    = -r + r²
Polynomial in r alone.

Integrand: x²/(1+eˣ) = t²·r evaluated at x=t. But we want t² expressed polynomially:
    t² appears in c = t²·a = t²·e^(-t), so t² = c/a, NOT polynomial.

Fix: use integrand directly as t²·r, with t² accessible via c only if we divide
by a. To avoid division, we need another variable.

Alternative: let d = t². Then ḋ = 2t, and ṫ = 1 (trivial). So we add:
    t (state), ṫ = 1 — but t is unbounded. Bad.

Better: integrate using c and 1/(1+eᵗ). We have:
    x² / (1+eˣ) = x²·(1-r) / eˣ · ... no.
    x² / (1+eˣ) = x²·e^(-x) / (e^(-x) + 1) · (well, 1/(1+eˣ) = e^(-x)/(1+e^(-x)))
                = x²·e^(-x) / (1 + e^(-x))
                = c / (1+a)
So integrand = c · q where q = 1/(1+a), q̇ = -ȧ·q²·... ȧ = -a, so
    q̇ = -(-a)·q² = a·q² [wait, q = 1/(1+a), dq/dt = -da/dt/(1+a)² = a/(1+a)² = a·q²]
Yes! q̇ = a·q².

Boundedness: a ∈ (0,1], so q = 1/(1+a) ∈ [1/2, 1). All bounded.

Final 5-variable system:
    ȧ = -a              a(0) = 1
    ḃ = a - b           b(0) = 0
    ċ = 2b - c          c(0) = 0
    q̇ = a·q²            q(0) = 1/2
    Ṡ = c·q             S(0) = 0

All polynomial (degree ≤ 2 in RHS). All bounded. S(∞) = (3/2)ζ(3).
"""

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import zeta

TARGET = zeta(3)  # 2/3 absorbed into Ṡ, so S(∞) = ζ(3) directly


def rhs(t, y):
    a, b, c, q, S = y
    return [
        -a,
        a - b,
        2 * b - c,
        a * q * q,
        (2/3) * c * q,
    ]


def run(t_end=40.0, rtol=1e-12, atol=1e-14):
    y0 = [1.0, 0.0, 0.0, 0.5, 0.0]
    sol = solve_ivp(
        rhs, (0.0, t_end), y0,
        method="DOP853", rtol=rtol, atol=atol,
        dense_output=True,
    )
    S_final = sol.y[4, -1]
    err = abs(S_final - TARGET)
    print(f"t_end        = {t_end}")
    print(f"S(t_end)     = {S_final:.15f}")
    print(f"ζ(3)         = {TARGET:.15f}")
    print(f"|S - target| = {err:.3e}")
    # Bounded check
    print(f"\nBoundedness check (should all stay in ranges):")
    print(f"  a ∈ [{sol.y[0].min():.6f}, {sol.y[0].max():.6f}]  expected (0, 1]")
    print(f"  b ∈ [{sol.y[1].min():.6f}, {sol.y[1].max():.6f}]  expected [0, 1/e≈0.3679]")
    print(f"  c ∈ [{sol.y[2].min():.6f}, {sol.y[2].max():.6f}]  expected [0, 4/e²≈0.5413]")
    print(f"  q ∈ [{sol.y[3].min():.6f}, {sol.y[3].max():.6f}]  expected [1/2, 1)")
    return sol, S_final, err


def convergence_rate():
    """Check exponential convergence: |S(t) - target| ~ e^(-t)·poly(t)."""
    print("\nConvergence rate (remaining error vs. t):")
    y0 = [1.0, 0.0, 0.0, 0.5, 0.0]
    sol = solve_ivp(rhs, (0.0, 60.0), y0, method="DOP853",
                    rtol=1e-13, atol=1e-15, dense_output=True)
    for T in [5, 10, 15, 20, 25, 30, 35, 40]:
        S_T = sol.sol(T)[4]
        err = abs(S_T - TARGET)
        expected_tail = T * T * np.exp(-T)  # leading tail ~ t²e^(-t)
        print(f"  t={T:3d}  |err| = {err:.3e}   t²e^(-t) = {expected_tail:.3e}   ratio = {err/expected_tail:.3f}")


if __name__ == "__main__":
    print(f"Target ζ(3) = {TARGET:.15f}\n")
    for t_end in [20.0, 30.0, 50.0]:
        print("=" * 60)
        run(t_end=t_end)
        print()
    convergence_rate()
