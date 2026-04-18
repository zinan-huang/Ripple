"""Experiment 04: Brusselator dual-rail constant-k test.

x1' = A + x1^2 x2 - (B+1) x1
x2' = B x1       - x1^2 x2
zero init, A, B > 0, B > 1 + A^2 for limit cycle.
"""
from __future__ import annotations

import os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))


def original_rhs(A, B):
    def rhs(_t, y):
        x1, x2 = y
        return [A + x1 * x1 * x2 - (B + 1.0) * x1, B * x1 - x1 * x1 * x2]

    return rhs


def dualrail_rhs(k, A, B):
    """See system.md for derivation.

    x1^2 x2 = u1^2 u2 - u1^2 v2 - 2 u1 v1 u2 + 2 u1 v1 v2 + v1^2 u2 - v1^2 v2
    """

    def rhs(_t, state):
        u1, v1, u2, v2 = state

        # x1^2 x2 split
        pos_x12x2 = u1 * u1 * u2 + 2.0 * u1 * v1 * v2 + v1 * v1 * u2
        neg_x12x2 = u1 * u1 * v2 + 2.0 * u1 * v1 * u2 + v1 * v1 * v2

        # p1 = A + x1^2 x2 - (B+1) x1
        p1p = A + pos_x12x2 + (B + 1.0) * v1
        p1n = neg_x12x2 + (B + 1.0) * u1

        # p2 = B x1 - x1^2 x2
        p2p = B * u1 + neg_x12x2
        p2n = B * v1 + pos_x12x2

        ann1 = k * u1 * v1
        ann2 = k * u2 * v2
        return [p1p - ann1, p1n - ann1, p2p - ann2, p2n - ann2]

    return rhs


def run_one(A, B, T, ks):
    t_eval = np.linspace(0.0, T, 8000)
    sol_orig = solve_ivp(
        original_rhs(A, B),
        (0.0, T),
        [0.0, 0.0],
        t_eval=t_eval,
        rtol=1e-9,
        atol=1e-11,
        method="LSODA",
    )
    sols = {}
    for k in ks:
        sols[k] = solve_ivp(
            dualrail_rhs(k, A, B),
            (0.0, T),
            [0.0, 0.0, 0.0, 0.0],
            t_eval=t_eval,
            rtol=1e-9,
            atol=1e-11,
            method="LSODA",
        )
    return sol_orig, sols


def plot_original(sol_orig, A, B, fname):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4))
    ax1.plot(sol_orig.t, sol_orig.y[0], label="x1")
    ax1.plot(sol_orig.t, sol_orig.y[1], label="x2")
    ax1.set_xlabel("t")
    ax1.set_title(f"Original Brusselator, A={A}, B={B}")
    ax1.legend()
    ax2.plot(sol_orig.y[0], sol_orig.y[1])
    ax2.set_xlabel("x1")
    ax2.set_ylabel("x2")
    ax2.set_title("Phase portrait")
    fig.tight_layout()
    fig.savefig(fname, dpi=120)
    plt.close(fig)


def plot_dualrail(sol_orig, sol_dr, k, A, B, fname):
    fig, axes = plt.subplots(2, 1, figsize=(10, 6), sharex=True)
    u1, v1, u2, v2 = sol_dr.y
    axes[0].plot(sol_dr.t, u1, label="u1")
    axes[0].plot(sol_dr.t, v1, label="v1")
    axes[0].plot(sol_dr.t, u1 - v1, "--", alpha=0.5, label="u1 - v1")
    axes[0].plot(sol_orig.t, sol_orig.y[0], ":", alpha=0.7, label="x1 (orig)")
    axes[0].set_ylabel("species 1")
    axes[0].legend(loc="upper right")
    axes[0].set_title(f"Brusselator dual-rail, A={A}, B={B}, k={k}")
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
    # Limit-cycle regime: B > 1 + A^2.
    # (A, B) = (1, 3) is the classic textbook choice.
    # Also try (1, 5) for more oscillation, (2, 6) for different amplitude.
    configs = [(1.0, 3.0), (1.0, 5.0), (2.0, 6.0)]
    ks = [0.01, 0.1, 1.0, 10.0, 100.0, 1000.0]

    summary = []
    for A, B in configs:
        T = 40.0
        sol_orig, sols = run_one(A, B, T, ks)
        plot_original(
            sol_orig, A, B, os.path.join(HERE, f"original_A={A}_B={B}.png")
        )
        for k, sol in sols.items():
            plot_dualrail(
                sol_orig, sol, k, A, B,
                os.path.join(HERE, f"dualrail_A={A}_B={B}_k={k}.png"),
            )
            u1, v1, u2, v2 = sol.y
            row = dict(
                A=A,
                B=B,
                k=k,
                max_u1=float(np.nanmax(u1)),
                max_v1=float(np.nanmax(v1)),
                max_u2=float(np.nanmax(u2)),
                max_v2=float(np.nanmax(v2)),
                final_v1=float(v1[-1]) if np.isfinite(v1[-1]) else float("nan"),
                final_v2=float(v2[-1]) if np.isfinite(v2[-1]) else float("nan"),
                max_x1_orig=float(np.nanmax(sol_orig.y[0])),
                max_x2_orig=float(np.nanmax(sol_orig.y[1])),
                all_finite=bool(np.all(np.isfinite(sol.y))),
            )
            summary.append(row)
            print(row)

    # k-sweep peak plot
    fig, ax = plt.subplots(figsize=(8, 4))
    for A, B in configs:
        rows = [r for r in summary if r["A"] == A and r["B"] == B]
        ks_arr = np.array([r["k"] for r in rows])
        peak_u1 = np.array([r["max_u1"] for r in rows])
        peak_v1 = np.array([r["max_v1"] for r in rows])
        peak_u2 = np.array([r["max_u2"] for r in rows])
        peak_v2 = np.array([r["max_v2"] for r in rows])
        ax.loglog(ks_arr, peak_u1, "o-", label=f"max u1 (A={A}, B={B})")
        ax.loglog(ks_arr, peak_v1, "x--", label=f"max v1 (A={A}, B={B})")
    ax.set_xlabel("k")
    ax.set_ylabel("peak")
    ax.set_title("Brusselator dual-rail peak vs k")
    ax.legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "k_sweep.png"), dpi=120)
    plt.close(fig)

    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        for row in summary:
            f.write(str(row) + "\n")


if __name__ == "__main__":
    simulate()
