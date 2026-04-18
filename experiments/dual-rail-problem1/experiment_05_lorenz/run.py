"""Experiment 05: Lorenz attractor dual-rail constant-k test.

x' = sigma*(y-x) + c
y' = x*(rho - z) - y
z' = x*y - beta*z
c = 0.1 (small bias to escape origin).
"""
from __future__ import annotations

import os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))

SIGMA = 10.0
RHO = 28.0
BETA = 8.0 / 3.0
C_BIAS = 0.1


def original_rhs(_t, state):
    x, y, z = state
    return [
        SIGMA * (y - x) + C_BIAS,
        x * (RHO - z) - y,
        x * y - BETA * z,
    ]


def dualrail_rhs(k):
    """Monomial split.

    p1 = sigma*y - sigma*x + c
       = sigma*(u2-v2) - sigma*(u1-v1) + c
    p1p: sigma*u2 + sigma*v1 + c
    p1n: sigma*v2 + sigma*u1

    p2 = rho*x - x*z - y
       = rho*(u1-v1) - (u1-v1)*(u3-v3) - (u2-v2)
       Expand (u1-v1)*(u3-v3) = u1*u3 - u1*v3 - v1*u3 + v1*v3
       So -x*z = -u1*u3 + u1*v3 + v1*u3 - v1*v3
    p2p: rho*u1 + u1*v3 + v1*u3 + v2
    p2n: rho*v1 + u1*u3 + v1*v3 + u2

    p3 = x*y - beta*z
       = (u1-v1)*(u2-v2) - beta*(u3-v3)
       x*y = u1*u2 - u1*v2 - v1*u2 + v1*v2
    p3p: u1*u2 + v1*v2 + beta*v3
    p3n: u1*v2 + v1*u2 + beta*u3
    """

    def rhs(_t, state):
        u1, v1, u2, v2, u3, v3 = state
        p1p = SIGMA * u2 + SIGMA * v1 + C_BIAS
        p1n = SIGMA * v2 + SIGMA * u1

        p2p = RHO * u1 + u1 * v3 + v1 * u3 + v2
        p2n = RHO * v1 + u1 * u3 + v1 * v3 + u2

        p3p = u1 * u2 + v1 * v2 + BETA * v3
        p3n = u1 * v2 + v1 * u2 + BETA * u3

        a1 = k * u1 * v1
        a2 = k * u2 * v2
        a3 = k * u3 * v3

        return [p1p - a1, p1n - a1, p2p - a2, p2n - a2, p3p - a3, p3n - a3]

    return rhs


def run_one(T, ks):
    t_eval = np.linspace(0.0, T, 10000)
    sol_orig = solve_ivp(
        original_rhs,
        (0.0, T),
        [0.0, 0.0, 0.0],
        t_eval=t_eval,
        rtol=1e-10,
        atol=1e-12,
        method="LSODA",
    )
    sols = {}
    for k in ks:
        sols[k] = solve_ivp(
            dualrail_rhs(k),
            (0.0, T),
            [0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
            t_eval=t_eval,
            rtol=1e-10,
            atol=1e-12,
            method="LSODA",
        )
    return sol_orig, sols


def plot_original(sol_orig, fname):
    fig = plt.figure(figsize=(12, 8))
    ax1 = fig.add_subplot(2, 2, 1)
    ax1.plot(sol_orig.t, sol_orig.y[0], label="x")
    ax1.plot(sol_orig.t, sol_orig.y[1], label="y")
    ax1.plot(sol_orig.t, sol_orig.y[2], label="z")
    ax1.set_xlabel("t")
    ax1.set_title("Original Lorenz time series")
    ax1.legend()

    ax2 = fig.add_subplot(2, 2, 2)
    ax2.plot(sol_orig.y[0], sol_orig.y[2], linewidth=0.5)
    ax2.set_xlabel("x")
    ax2.set_ylabel("z")
    ax2.set_title("x-z projection")

    ax3 = fig.add_subplot(2, 2, 3, projection="3d")
    ax3.plot(sol_orig.y[0], sol_orig.y[1], sol_orig.y[2], linewidth=0.3)
    ax3.set_xlabel("x")
    ax3.set_ylabel("y")
    ax3.set_zlabel("z")
    ax3.set_title("3D attractor")

    fig.tight_layout()
    fig.savefig(fname, dpi=120)
    plt.close(fig)


def plot_dualrail(sol_orig, sol_dr, k, fname):
    fig, axes = plt.subplots(3, 1, figsize=(12, 9), sharex=True)
    u1, v1, u2, v2, u3, v3 = sol_dr.y
    labels = ["x", "y", "z"]
    for ax, (u, v), i in zip(axes, [(u1, v1), (u2, v2), (u3, v3)], range(3)):
        ax.plot(sol_dr.t, u, label=f"u_{labels[i]}")
        ax.plot(sol_dr.t, v, label=f"v_{labels[i]}")
        ax.plot(sol_dr.t, u - v, "--", alpha=0.5, label="u - v")
        ax.plot(sol_orig.t, sol_orig.y[i], ":", alpha=0.7, label=f"{labels[i]} (orig)")
        ax.set_ylabel(labels[i])
        ax.legend(loc="upper right", fontsize=7)
    axes[0].set_title(f"Lorenz dual-rail, k = {k}")
    axes[-1].set_xlabel("t")
    fig.tight_layout()
    fig.savefig(fname, dpi=120)
    plt.close(fig)


def simulate():
    T = 25.0
    ks = [0.1, 1.0, 10.0, 100.0, 1000.0, 10000.0]

    sol_orig, sols = run_one(T, ks)
    plot_original(sol_orig, os.path.join(HERE, "original.png"))

    summary = []
    for k, sol in sols.items():
        plot_dualrail(sol_orig, sol, k, os.path.join(HERE, f"dualrail_k={k}.png"))
        u1, v1, u2, v2, u3, v3 = sol.y
        row = dict(
            k=k,
            max_u1=float(np.nanmax(u1)),
            max_v1=float(np.nanmax(v1)),
            max_u2=float(np.nanmax(u2)),
            max_v2=float(np.nanmax(v2)),
            max_u3=float(np.nanmax(u3)),
            max_v3=float(np.nanmax(v3)),
            max_x_orig=float(np.nanmax(np.abs(sol_orig.y[0]))),
            max_y_orig=float(np.nanmax(np.abs(sol_orig.y[1]))),
            max_z_orig=float(np.nanmax(sol_orig.y[2])),
            all_finite=bool(np.all(np.isfinite(sol.y))),
        )
        summary.append(row)
        print(row)

    fig, ax = plt.subplots(figsize=(8, 4))
    ks_arr = np.array([r["k"] for r in summary])
    for key, label in [("max_u1", "max u_x"), ("max_u2", "max u_y"), ("max_u3", "max u_z"),
                        ("max_v1", "max v_x"), ("max_v2", "max v_y"), ("max_v3", "max v_z")]:
        vals = np.array([r[key] for r in summary])
        ax.loglog(ks_arr, vals, "o-", label=label)
    ax.set_xlabel("k")
    ax.set_ylabel("peak")
    ax.set_title("Lorenz dual-rail peak vs k")
    ax.legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "k_sweep.png"), dpi=120)
    plt.close(fig)

    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        for row in summary:
            f.write(str(row) + "\n")


if __name__ == "__main__":
    simulate()
