"""Experiment 02: Van der Pol (biased by constant c) dual-rail constant-k test.

To make the origin a non-fixed-point (so zero-init GPAC leaves 0), we add
a constant bias `c > 0` to the x2 equation. This keeps the limit cycle
(Poincaré-Bendixson, |c| < 1) and lets us test the dual-rail on a genuine
bounded oscillator.
"""
from __future__ import annotations

import os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))

C_BIAS = 0.5  # constant forcing; FP shifts to (c, 0), still unstable for mu > 0


def original_rhs(mu):
    def rhs(_t, y):
        x1, x2 = y
        return [x2, mu * (1.0 - x1 * x1) * x2 - x1 + C_BIAS]

    return rhs


def dualrail_rhs(k, mu):
    """x_i = u_i - v_i, split monomial-wise by sign.

    p1 = x2               -> p1+ = u2,   p1- = v2
    p2 = mu x2 - mu x1^2 x2 - x1
       = mu(u2 - v2)
         - mu(u1 - v1)^2 (u2 - v2)
         - (u1 - v1)
    Expand x1^2 x2 = (u1^2 - 2 u1 v1 + v1^2)(u2 - v2)
                   = u1^2 u2 - u1^2 v2 - 2 u1 v1 u2 + 2 u1 v1 v2
                     + v1^2 u2 - v1^2 v2.
    So -mu x1^2 x2 = -mu u1^2 u2 + mu u1^2 v2 + 2 mu u1 v1 u2
                     - 2 mu u1 v1 v2 - mu v1^2 u2 + mu v1^2 v2.
    p2+ (positive terms): mu u2 + mu u1^2 v2 + 2 mu u1 v1 u2 + mu v1^2 v2 + v1
    p2- (negative terms): mu v2 + mu u1^2 u2 + 2 mu u1 v1 v2 + mu v1^2 u2 + u1
    """

    def rhs(_t, state):
        u1, v1, u2, v2 = state
        # p1
        p1p = u2
        p1n = v2
        # p2
        p2p = (
            mu * u2
            + mu * u1 * u1 * v2
            + 2.0 * mu * u1 * v1 * u2
            + mu * v1 * v1 * v2
            + v1
            + C_BIAS
        )
        p2n = (
            mu * v2
            + mu * u1 * u1 * u2
            + 2.0 * mu * u1 * v1 * v2
            + mu * v1 * v1 * u2
            + u1
        )
        ann1 = k * u1 * v1
        ann2 = k * u2 * v2
        return [p1p - ann1, p1n - ann1, p2p - ann2, p2n - ann2]

    return rhs


def run_one(mu, T, ks):
    """Simulate for given mu, return (sol_orig, {k: sol_dr})."""
    t_eval = np.linspace(0.0, T, 8000)
    sol_orig = solve_ivp(
        original_rhs(mu),
        (0.0, T),
        [0.0, 0.0],  # zero init, bias makes origin non-stationary
        t_eval=t_eval,
        rtol=1e-9,
        atol=1e-11,
        method="LSODA",
    )
    sols = {}
    for k in ks:
        sols[k] = solve_ivp(
            dualrail_rhs(k, mu),
            (0.0, T),
            [0.0, 0.0, 0.0, 0.0],
            t_eval=t_eval,
            rtol=1e-9,
            atol=1e-11,
            method="LSODA",
        )
    return sol_orig, sols


def plot_original(sol_orig, mu, fname):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4))
    ax1.plot(sol_orig.t, sol_orig.y[0], label="x1")
    ax1.plot(sol_orig.t, sol_orig.y[1], label="x2")
    ax1.set_xlabel("t")
    ax1.set_title(f"Original Van der Pol, mu = {mu}")
    ax1.legend()
    ax2.plot(sol_orig.y[0], sol_orig.y[1])
    ax2.set_xlabel("x1")
    ax2.set_ylabel("x2")
    ax2.set_title("Phase portrait")
    fig.tight_layout()
    fig.savefig(fname, dpi=120)
    plt.close(fig)


def plot_dualrail(sol_orig, sol_dr, k, mu, fname):
    fig, axes = plt.subplots(2, 1, figsize=(10, 6), sharex=True)
    u1, v1, u2, v2 = sol_dr.y
    axes[0].plot(sol_dr.t, u1, label="u1")
    axes[0].plot(sol_dr.t, v1, label="v1")
    axes[0].plot(sol_dr.t, u1 - v1, "--", alpha=0.5, label="u1 - v1")
    axes[0].plot(sol_orig.t, sol_orig.y[0], ":", alpha=0.7, label="x1 (orig)")
    axes[0].set_ylabel("species 1")
    axes[0].legend(loc="upper right")
    axes[0].set_title(f"Van der Pol dual-rail, mu = {mu}, k = {k}")
    axes[1].plot(sol_dr.t, u2, label="u2")
    axes[1].plot(sol_dr.t, v2, label="v2")
    axes[1].plot(sol_dr.t, u2 - v2, "--", alpha=0.5, label="u2 - v2")
    axes[1].plot(sol_orig.t, sol_orig.y[1], ":", alpha=0.7, label="x2 (orig)")
    axes[1].set_xlabel("t")
    axes[1].set_ylabel("species 2")
    axes[1].legend(loc="upper right")
    fig.tight_layout()
    fig.savefig(fname, dpi=120)
    plt.close(fig)


def simulate():
    mus = [1.0, 5.0, 20.0]
    ks = [0.1, 1.0, 10.0, 100.0, 1000.0]

    summary = []
    for mu in mus:
        # Enough time to see multiple cycles: period ~ (3 - 2 ln2) mu for large mu
        T = max(30.0, 5.0 * (3.0 - 2.0 * np.log(2.0)) * mu)
        sol_orig, sols = run_one(mu, T, ks)
        plot_original(sol_orig, mu, os.path.join(HERE, f"original_mu={mu}.png"))
        for k, sol in sols.items():
            plot_dualrail(
                sol_orig, sol, k, mu,
                os.path.join(HERE, f"dualrail_mu={mu}_k={k}.png"),
            )
            u1, v1, u2, v2 = sol.y
            row = dict(
                mu=mu,
                k=k,
                max_u1=float(np.nanmax(u1)),
                max_v1=float(np.nanmax(v1)),
                max_u2=float(np.nanmax(u2)),
                max_v2=float(np.nanmax(v2)),
                max_x1=float(np.nanmax(np.abs(sol_orig.y[0]))),
                max_x2=float(np.nanmax(np.abs(sol_orig.y[1]))),
                T=T,
                status="bounded" if np.all(np.isfinite(sol.y)) else "BLOWUP",
            )
            summary.append(row)
            print(row)

    # Aggregate k-sweep plot for mu = 5 (interesting regime)
    mu_sweep = 5.0
    T = 5.0 * (3.0 - 2.0 * np.log(2.0)) * mu_sweep
    ks_sweep = np.logspace(-1, 4, 30)
    max_u1, max_v1, max_u2, max_v2 = [], [], [], []
    for k in ks_sweep:
        sol = solve_ivp(
            dualrail_rhs(k, mu_sweep),
            (0.0, T),
            [0.0, 0.0, 0.0, 0.0],
            t_eval=np.linspace(0.0, T, 4000),
            rtol=1e-8,
            atol=1e-10,
            method="LSODA",
        )
        u1, v1, u2, v2 = sol.y
        max_u1.append(float(np.nanmax(u1)))
        max_v1.append(float(np.nanmax(v1)))
        max_u2.append(float(np.nanmax(u2)))
        max_v2.append(float(np.nanmax(v2)))

    fig, ax = plt.subplots(figsize=(8, 4))
    ax.semilogx(ks_sweep, max_u1, label="max u1")
    ax.semilogx(ks_sweep, max_v1, label="max v1")
    ax.semilogx(ks_sweep, max_u2, label="max u2")
    ax.semilogx(ks_sweep, max_v2, label="max v2")
    ax.set_xlabel("k (log scale)")
    ax.set_ylabel("peak on [0, T]")
    ax.set_title(f"Van der Pol dual-rail peaks vs k (mu = {mu_sweep})")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "k_sweep_mu=5.png"), dpi=120)
    plt.close(fig)

    # Write summary
    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        for row in summary:
            f.write(str(row) + "\n")


if __name__ == "__main__":
    simulate()
