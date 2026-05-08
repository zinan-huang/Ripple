"""
DEFUNCT — keeps its output as a record of a failed framing.

Discrete version of the V/U vs z_1 check. Same flaw as
apery_conifold_ode_trajectory.py: v_n/u_n → ζ(3) is a coefficient
limit, but our surrogate z_n = a_{n-1}/a_n misrepresents where the
Frobenius 3/2 bound lives. The observed log-log slope is junk; the
discrete ratio error ~(z_1/z_2)^n is double-exponentially smaller
than |z_1 − z_n|^{3/2}, so the 3/2 bound holds trivially with no
signal about its sharpness.

A correct experiment needs the 8-var PIVP trajectory, whose result
component is the specific linear combination with 3/2 local form.

Below is the original script for record.
--------------------------------------------------------------------

Numerical check of the 3/2-order conifold asymptotic (F5 / STRATEGY Step 5).

The Lean hypothesis `AperyConifoldThreeHalvesBound` claims:

    |sol.trajectory t iR  -  ζ(3)|
      ≤  K32 · |z₁ - z(t)| · sqrt(|z₁ - z(t)|)

with z₁ = 17 - 12 √2 the Apéry conifold. In plain English: once the
scalar z-component is close to the conifold, the ratio error decays
like |z₁ - z|^{3/2}.

This script verifies the 3/2 exponent directly at the generating-function
level (before translating to the 8-var PIVP). We use Apéry's recurrence
to build the integer sequences a_n (= u_n), b_n (= v_n) satisfying

    (n+1)^3 a_{n+1}  =  (34 n^3 + 51 n^2 + 27 n + 5) a_n  -  n^3 a_{n-1}

with a_0 = 1, a_1 = 5 and the analogous b-recurrence with different IC,
and extract the "effective z" variable via

    z_n := a_{n-1} / a_n,      z_n  →  z₁  geometrically.

Then we plot |b_n / a_n - ζ(3)| against |z₁ - z_n| on log-log and fit the
slope. The Frobenius claim predicts slope ≈ 1.5.
"""

import math
from fractions import Fraction

import matplotlib.pyplot as plt
import numpy as np
from mpmath import mp, mpf, sqrt as msqrt

mp.dps = 80

Z1 = mpf(17) - 12 * msqrt(2)            # ≈ 0.029437251522857...
ZETA3 = mp.zeta(3)


def apery_sequences(N):
    """Return (a[0..N], b[0..N]) as mpf sequences.

    a_n : Apéry's 'u_n' = Σ_k C(n,k)^2 C(n+k,k)^2, satisfies the recurrence.
    b_n : the 'v_n' companion with b_0 = 0, b_1 = 6 (matches Apéry's original
          construction so that b_n / a_n → ζ(3)).
    """
    a = [mpf(1), mpf(5)]
    b = [mpf(0), mpf(6)]
    for n in range(1, N):
        coef = 34 * n**3 + 51 * n**2 + 27 * n + 5
        denom = (n + 1) ** 3
        a.append((coef * a[n] - n**3 * a[n - 1]) / denom)
        b.append((coef * b[n] - n**3 * b[n - 1]) / denom)
    return a, b


def main():
    N = 220
    a, b = apery_sequences(N)

    # Use z_n := a_{n-1} / a_n as the "effective z" which tends to Z1.
    z_ns = []
    err_ratio = []
    for n in range(5, N):
        z_n = a[n - 1] / a[n]
        z_ns.append(z_n)
        err_ratio.append(abs(b[n] / a[n] - ZETA3))

    dist = [abs(Z1 - z_n) for z_n in z_ns]

    # Log-log slope: log(err_ratio) = slope · log(dist) + const.
    log_dist = np.array([float(mp.log(d)) for d in dist], dtype=float)
    log_err = np.array(
        [float(mp.log(e)) if e > 0 else -1e9 for e in err_ratio], dtype=float
    )
    # Keep only finite points.
    mask = np.isfinite(log_err) & np.isfinite(log_dist)
    slope_fit, intercept = np.polyfit(log_dist[mask], log_err[mask], 1)
    print(f"Log-log fit: slope = {slope_fit:.4f}, intercept = {intercept:.4f}")
    print(f"Frobenius prediction for 3/2-order bound: slope = 1.5")
    print(f"z_1 (conifold)        = {Z1}")
    print(f"ζ(3)                  = {ZETA3}")
    print(f"Final z_n             = {z_ns[-1]}")
    print(f"Final |z_1 - z_n|     = {dist[-1]}")
    print(f"Final ratio error     = {err_ratio[-1]}")

    fig, ax = plt.subplots(figsize=(8, 5))
    ax.loglog(
        [float(d) for d in dist],
        [float(e) for e in err_ratio],
        "o-",
        markersize=3,
        linewidth=0.8,
        label="|b_n/a_n - ζ(3)|",
    )

    # Reference slopes 1 and 3/2.
    d_np = np.array([float(d) for d in dist])
    e0 = float(err_ratio[0])
    d0 = float(dist[0])
    ax.loglog(d_np, e0 * (d_np / d0) ** 1.0, "--", label="slope 1")
    ax.loglog(d_np, e0 * (d_np / d0) ** 1.5, "--", label="slope 3/2 (Frobenius)")

    ax.set_xlabel(r"|z_1 - z_n|,  z_n = a_{n-1}/a_n")
    ax.set_ylabel(r"|b_n/a_n - ζ(3)|")
    ax.set_title(
        f"Apéry conifold 3/2-order check  (fitted slope = {slope_fit:.3f})"
    )
    ax.legend()
    ax.grid(True, which="both", ls=":")
    fig.tight_layout()
    out_path = "experiments/apery_conifold_three_halves.png"
    fig.savefig(out_path, dpi=140)
    print(f"\nSaved plot to {out_path}")


if __name__ == "__main__":
    main()
