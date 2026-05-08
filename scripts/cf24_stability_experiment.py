"""CF'24 local stability — numerical verification.

Integrates the 3-PP field
    f_0 = -2a^2 + 7ab - 2ac
    f_1 =  2a^2 - 8ab + 16ac - bc
    f_2 =  ab - 14ac + bc

from several simplex-interior initial conditions and verifies:
  (1) convergence to fixed point ((7+3√5)/18, 2/9, (7-3√5)/18),
  (2) V(t) := (b(t)-b*)^2 + (c(t)-c*)^2 decays,
  (3) once |b-b*|+|c-c*| <= 1/16, V̇ <= -(11-4√5)·V holds pointwise,
  (4) readout z_11 + z_01/2 -> (3-√5)/6.
"""

from __future__ import annotations

import math
from typing import List, Tuple

import numpy as np
from scipy.integrate import solve_ivp


SQRT5 = math.sqrt(5.0)
A_STAR = (7.0 + 3.0 * SQRT5) / 18.0
B_STAR = 2.0 / 9.0
C_STAR = (7.0 - 3.0 * SQRT5) / 18.0
READOUT_STAR = (3.0 - SQRT5) / 6.0

SPECTRAL_GAP_Q = 13.0 - 4.0 * SQRT5      # Q-form spectral gap  (≈ 4.056)
RESIDUAL_GAP   = 11.0 - 4.0 * SQRT5      # after cubic absorption (≈ 2.056)
BALL_RADIUS    = 1.0 / 16.0              # |Δb| + |Δc| ≤ 1/16


def field(t: float, x: np.ndarray) -> np.ndarray:
    a, b, c = x
    return np.array([
        -2*a*a + 7*a*b - 2*a*c,
         2*a*a - 8*a*b + 16*a*c - b*c,
               a*b - 14*a*c + b*c,
    ])


def V(b: float, c: float) -> float:
    return (b - B_STAR) ** 2 + (c - C_STAR) ** 2


def Vdot(x: np.ndarray) -> float:
    """Lie derivative of V along the field."""
    _, b, c = x
    f = field(0.0, x)
    return 2.0 * (b - B_STAR) * f[1] + 2.0 * (c - C_STAR) * f[2]


def readout(x: np.ndarray) -> float:
    return x[2] + x[1] / 2.0


def run_trajectory(x0: np.ndarray, t_end: float = 60.0) -> Tuple[np.ndarray, np.ndarray]:
    sol = solve_ivp(field, (0.0, t_end), x0, rtol=1e-10, atol=1e-12,
                    dense_output=True, max_step=0.05)
    return sol.t, sol.y


def main() -> None:
    print(f"Fixed point: a* = {A_STAR:.6f}, b* = {B_STAR:.6f}, c* = {C_STAR:.6f}")
    print(f"Readout target: (3-√5)/6 = {READOUT_STAR:.6f}")
    print(f"Spectral gap (Q):   13-4√5 = {SPECTRAL_GAP_Q:.4f}")
    print(f"Residual gap (small ball): 11-4√5 = {RESIDUAL_GAP:.4f}")
    print(f"Small-ball threshold: |Δb|+|Δc| ≤ {BALL_RADIUS:.4f}")
    print()

    # Simplex-interior initial conditions (a+b+c = 1, all > 0).
    inits: List[np.ndarray] = [
        np.array([A_STAR + 0.02, B_STAR - 0.015, C_STAR - 0.005]),  # tiny perturbation, should enter ball fast
        np.array([A_STAR - 0.05, B_STAR + 0.03, C_STAR + 0.02]),    # moderate perturbation
        np.array([0.50, 0.30, 0.20]),                                # far from fixed point
        np.array([0.90, 0.05, 0.05]),                                # a-heavy
        np.array([0.20, 0.50, 0.30]),                                # b-heavy
    ]

    for idx, x0 in enumerate(inits):
        assert abs(x0.sum() - 1.0) < 1e-12, "Initial condition not on simplex"
        assert np.all(x0 > 0), "Initial condition must be interior"

        t, y = run_trajectory(x0, t_end=60.0)
        a_t, b_t, c_t = y

        err_fp = np.linalg.norm(y[:, -1] - np.array([A_STAR, B_STAR, C_STAR]))
        err_readout = abs(readout(y[:, -1]) - READOUT_STAR)

        # Compute V(t) and check exponential decay envelope once inside the small ball.
        V_t = (b_t - B_STAR) ** 2 + (c_t - C_STAR) ** 2
        L1_t = np.abs(b_t - B_STAR) + np.abs(c_t - C_STAR)

        # Find first time index where trajectory enters the small ball.
        in_ball = np.where(L1_t <= BALL_RADIUS)[0]
        enter_t = t[in_ball[0]] if in_ball.size else None

        # Pointwise check: Vdot <= -(11-4√5) * V inside the ball.
        violations = 0
        worst_ratio = -np.inf
        if enter_t is not None:
            for k in in_ball:
                xk = y[:, k]
                vd = Vdot(xk)
                vk = V(xk[1], xk[2])
                if vk > 1e-14:
                    ratio = vd / vk        # expect <= -(11-4√5)
                    if ratio > -RESIDUAL_GAP + 1e-6:
                        violations += 1
                    worst_ratio = max(worst_ratio, ratio)

        print(f"Trajectory {idx}: x0 = {x0}")
        print(f"  ‖x(60) - fixed point‖ = {err_fp:.3e}")
        print(f"  |readout(60) - (3-√5)/6| = {err_readout:.3e}")
        if enter_t is not None:
            print(f"  entered 1/16-ball at t = {enter_t:.3f}")
            print(f"  pointwise V̇/V  worst ratio in ball = {worst_ratio:.4f}"
                  f"  (expected ≤ -{RESIDUAL_GAP:.4f})")
            print(f"  violations of small-ball estimate: {violations} / {len(in_ball)}")
        else:
            print(f"  did NOT enter 1/16-ball in 60s (min L1 distance: {L1_t.min():.4f})")
        print()


if __name__ == "__main__":
    main()
