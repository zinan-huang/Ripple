"""
DEFUNCT — keeps its output as a record of a failed framing.

This script plots |V(z)/U(z) − ζ(3)| vs |z_1 − z|. The premise is wrong:
V(z)/U(z) does NOT converge to ζ(3) at z_1.

- u_n ~ c·z_1^{−n}/n^{3/2}, so U(z_1) = Σ c/n^{3/2} CONVERGES (3/2 > 1).
- H(z) := V(z) − ζ(3)U(z) has radius z_2 > z_1 (Apéry), analytic at z_1.
- So V/U − ζ(3) → H(z_1)/U(z_1), a generically nonzero constant.
  Observed plateau at ~0.825 is this constant.

Apéry's v_n/u_n → ζ(3) is a coefficient-ratio limit, not a
generating-function-ratio limit.

The actual AperyConifoldThreeHalvesBound is about the PIVP result
component (a specific linear combination isolating the (z_1−z)^{1/2}
Frobenius branch). V/U does not isolate that branch. A correct
numerical check requires the 8-var PIVP trajectory itself.

Below is the original script and its (now re-interpreted) output.
--------------------------------------------------------------------

Numerical check of the 3/2-order conifold asymptotic (F5), continuous version.

Strategy: evaluate the generating functions U(z) = Σ u_n zⁿ and
V(z) = Σ v_n zⁿ at a sweep of z approaching z_1 = 17 − 12√2, where u_n,
v_n are Apéry's sequences satisfying

    (n+1)³ u_{n+1} = (34n³ + 51n² + 27n + 5) u_n − n³ u_{n−1}
    u_0 = 1, u_1 = 5       (for u_n)
    v_0 = 0, v_1 = 6       (for v_n)

Both series have radius of convergence exactly z_1, so we can evaluate
them via truncation for z ∈ (0, z_1) with enough terms.

Apéry's theorem: v_n / u_n → ζ(3) geometrically. At the level of
generating functions, V(z) / U(z) → ζ(3) as z → z_1⁻, with a local
Frobenius expansion at z_1 controlled by the exponents {0, 1/2, 1}.

This script plots |V(z) / U(z) − ζ(3)| against |z_1 − z| on a log-log
scale and fits the slope. The Frobenius claim (STRATEGY Step 5,
AperyConifoldThreeHalvesBound) predicts that the ratio error decays
like |z_1 − z|^{3/2} (with log-log slope 3/2).
"""

from fractions import Fraction

import matplotlib.pyplot as plt
import numpy as np
from mpmath import mp, mpf, sqrt as msqrt

mp.dps = 40

Z1 = mpf(17) - 12 * msqrt(2)          # ≈ 0.029437251522857
ZETA3 = mp.zeta(3)


def apery_seqs(N):
    """Return u[0..N], v[0..N] as mpf lists."""
    u = [mpf(1), mpf(5)]
    v = [mpf(0), mpf(6)]
    for n in range(1, N):
        coef = 34 * n**3 + 51 * n**2 + 27 * n + 5
        denom = (n + 1) ** 3
        u.append((coef * u[n] - n**3 * u[n - 1]) / denom)
        v.append((coef * v[n] - n**3 * v[n - 1]) / denom)
    return u, v


def eval_series(coeffs, z, N):
    """Σ coeffs[n] · z^n for n = 0..N."""
    s = mpf(0)
    zp = mpf(1)
    for n in range(N + 1):
        s += coeffs[n] * zp
        zp *= z
    return s


def main():
    # Need enough terms so that the z = z_1·(1 − δ) evaluations converge.
    # u_n ~ α_2^n / n^{3/2} where α_2 = 1/z_1 = 17 + 12√2 ≈ 33.97.
    # For |z| = z_1·(1 − δ), tail term ~ (1 − δ)^n / n^{3/2}. Need n big.
    # Tail of U(z) at z = z_1·(1-δ): ~ (1-δ)^N / N^{3/2}.
    # To see |z_1-z|^{3/2} down to δ_min, need (1-δ_min)^N ≪ δ_min^{3/2}·ε.
    # N=60000, δ_min=5e-4: (1-5e-4)^60000 ≈ e^{-30} ≈ 1e-13. Fine.
    N = 60000
    print(f"Building Apéry sequences, N = {N}...")
    u, v = apery_seqs(N)
    print("Sequences built.")

    deltas_py = np.geomspace(5e-4, 0.15, 20)
    dists = []
    errs = []
    for d in deltas_py:
        d_mp = mpf(float(d))
        z = Z1 * (1 - d_mp)
        U = eval_series(u, z, N)
        V = eval_series(v, z, N)
        ratio = V / U
        err = abs(ratio - ZETA3)
        dist = Z1 - z   # positive, = Z1 · δ
        dists.append(float(dist))
        errs.append(float(err))

    dists_np = np.array(dists)
    errs_np = np.array(errs)

    log_d = np.log(dists_np)
    log_e = np.log(errs_np)
    mask = np.isfinite(log_e) & (errs_np > 0)
    slope, intercept = np.polyfit(log_d[mask], log_e[mask], 1)
    print(f"Truncation N        = {N}")
    print(f"log-log slope fit   = {slope:.4f}")
    print(f"Frobenius prediction = 1.5  (3/2-order)")
    print(f"min |z_1 − z| tested = {dists_np.min():.3e}")
    print(f"max |z_1 − z| tested = {dists_np.max():.3e}")
    print(f"ratio error at min d = {errs_np[dists_np.argmin()]:.3e}")

    fig, ax = plt.subplots(figsize=(8, 5))
    ax.loglog(dists_np, errs_np, "o-", markersize=4, label="|V(z)/U(z) − ζ(3)|")
    d_line = np.geomspace(dists_np.min(), dists_np.max(), 100)
    ref0 = errs_np[-1] / dists_np[-1] ** 1.0
    ax.loglog(d_line, ref0 * d_line ** 1.0, "--", label="slope 1", alpha=0.6)
    ref15 = errs_np[-1] / dists_np[-1] ** 1.5
    ax.loglog(d_line, ref15 * d_line ** 1.5, "--",
              label="slope 3/2 (Frobenius)", alpha=0.6)
    ref2 = errs_np[-1] / dists_np[-1] ** 2.0
    ax.loglog(d_line, ref2 * d_line ** 2.0, "--", label="slope 2", alpha=0.4)

    ax.set_xlabel("|z_1 − z|")
    ax.set_ylabel("|V(z)/U(z) − ζ(3)|")
    ax.set_title(
        f"Apéry conifold 3/2-order check (N={N}, fitted slope = {slope:.3f})"
    )
    ax.legend()
    ax.grid(True, which="both", ls=":")
    fig.tight_layout()
    out = "experiments/apery_conifold_ode_trajectory.png"
    fig.savefig(out, dpi=140)
    print(f"\nSaved plot to {out}")


if __name__ == "__main__":
    main()
