"""Experiment 01: scalar cubic y' = 1 - y^3 dual-rail constant-k test."""
from __future__ import annotations

import os
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))


def original_rhs(_t, y):
    return [1.0 - y[0] ** 3]


def dualrail_rhs(k):
    def rhs(_t, state):
        u, v = state
        u_dot = 1.0 + 3.0 * u * u * v + v ** 3 - k * u * v
        v_dot = u ** 3 + 3.0 * u * v * v - k * u * v
        return [u_dot, v_dot]

    return rhs


def simulate():
    T = 30.0
    t_eval = np.linspace(0.0, T, 4000)

    # Original
    sol_y = solve_ivp(
        original_rhs, (0.0, T), [0.0], t_eval=t_eval, rtol=1e-10, atol=1e-12
    )

    # Dual-rail at several k
    ks = [0.1, 1.0, 10.0, 100.0, 1000.0]
    sols = {}
    for k in ks:
        sols[k] = solve_ivp(
            dualrail_rhs(k),
            (0.0, T),
            [0.0, 0.0],
            t_eval=t_eval,
            rtol=1e-10,
            atol=1e-12,
            method="LSODA",
        )

    # Plot original
    fig, ax = plt.subplots(figsize=(8, 4))
    ax.plot(sol_y.t, sol_y.y[0], label="y(t)", linewidth=2)
    ax.axhline(1.0, color="gray", linestyle="--", alpha=0.5, label="y = 1")
    ax.set_xlabel("t")
    ax.set_ylabel("y")
    ax.set_title(r"Original GPAC: $y' = 1 - y^3$, $y(0) = 0$")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "original.png"), dpi=120)
    plt.close(fig)

    # Plot u, v for each k
    for k, sol in sols.items():
        fig, ax = plt.subplots(figsize=(8, 4))
        u, v = sol.y
        ax.plot(sol.t, u, label="u(t)", linewidth=2)
        ax.plot(sol.t, v, label="v(t)", linewidth=2)
        ax.plot(sol.t, u - v, "--", label="u - v", alpha=0.7)
        ax.set_xlabel("t")
        ax.set_ylabel("concentration")
        ax.set_title(f"Dual-rail, k = {k}")
        ax.legend()
        fig.tight_layout()
        fig.savefig(os.path.join(HERE, f"dualrail_k={k}.png"), dpi=120)
        plt.close(fig)

    # Sweep: max(u), max(v) vs k
    ks_sweep = np.logspace(-1, 4, 40)
    max_u, max_v, max_s = [], [], []
    for k in ks_sweep:
        sol = solve_ivp(
            dualrail_rhs(k),
            (0.0, T),
            [0.0, 0.0],
            t_eval=t_eval,
            rtol=1e-8,
            atol=1e-10,
            method="LSODA",
        )
        u, v = sol.y
        max_u.append(u.max())
        max_v.append(v.max())
        max_s.append((u + v).max())

    fig, ax = plt.subplots(figsize=(8, 4))
    ax.semilogx(ks_sweep, max_u, label="max u")
    ax.semilogx(ks_sweep, max_v, label="max v")
    ax.semilogx(ks_sweep, max_s, label="max (u + v)")
    ax.set_xlabel("k (log scale)")
    ax.set_ylabel("peak value on [0, T]")
    ax.set_title("Boundedness vs k")
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "k_sweep.png"), dpi=120)
    plt.close(fig)

    print("max|y| =", abs(sol_y.y[0]).max())
    for k, sol in sols.items():
        u, v = sol.y
        print(
            f"k={k:>8}: max u = {u.max():.4f}, max v = {v.max():.4f}, "
            f"max(u+v) = {(u + v).max():.4f}"
        )


if __name__ == "__main__":
    simulate()
