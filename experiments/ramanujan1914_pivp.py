"""
Ramanujan 1914 formula for 1/π — GPAC / PIVP simulation.

The series (Ramanujan, Quart. J. Math. 45 (1914), 350–372):

    1/π = (2√2/9801) · Σ_{k=0}^∞ (4k)!/(k!)^4 · (1103 + 26390 k) / 396^(4k).

Let a_k = (4k)!/(k!)^4 and f(z) = Σ a_k z^k. Then f satisfies

    θ^3 f = 256 z (θ + 1/4)(θ + 1/2)(θ + 3/4) f,     θ := z d/dz,

equivalently f(z) = ₃F₂(1/4, 1/2, 3/4; 1, 1; 256 z). Singular points at
z = 0 (MUM, triple indicial root), z = 1/256, z = ∞.

Ramanujan's evaluation point z₀ = 1/396⁴ is deep inside the disk of
convergence. The per-term geometric decay factor is 256 z₀ = 1/99⁴.

To make the GPAC model live on a comfortable domain, we rescale the
argument: let w := z / z₀ ∈ [0, 1] and g(w) := f(z₀ w) = Σ a_k z₀^k w^k.
Then g(1) = f(z₀), g'(1) = z₀ f'(z₀), and g satisfies

    w² (1 − 256 z₀ w) g''' = 3 w (384 z₀ w − 1) g''
                            + (816 z₀ w − 1) g'
                            + 24 z₀ g.

The other regular singular point is now at w = 1/(256 z₀) = 99⁴ ≈ 10⁸,
far outside our target w = 1.

GPAC / polynomial PIVP encoding. With state X = (w, Q, g, g', g'', P) and
Q := 1 / [w² (1 − 256 z₀ w)], and time-rescaling dw/dτ = 1 − w, every RHS
below is polynomial in X:

    dw/dτ   = 1 − w
    dQ/dτ   = −2 w (1 − 384 z₀ w) · Q² · (1 − w)
    dg/dτ   = g' · (1 − w)
    dg'/dτ  = g'' · (1 − w)
    dg''/dτ = Q · [3 w (384 z₀ w − 1) g'' + (816 z₀ w − 1) g' + 24 z₀ g] · (1 − w)
    dP/dτ   = 1 − I(X) · P,     I(X) := (2√2/9801) · (1103 · g + 26390 · g')

Readout: P(τ) → π exponentially as τ → ∞. Indeed w(τ) → 1 at rate 1 so
I(X(τ)) → 1/π at rate 1, and the linear inverter dP/dτ = 1 − I·P has
fixed point P = 1/I with decay rate I(∞) = 1/π ≈ 0.318.

Experiments in this file:
  (1) verify the recurrence (k+1)³ a_{k+1} = 4(4k+1)(4k+2)(4k+3) a_k;
  (2) direct partial-sum convergence of Ramanujan's series;
  (3) integrate the full 6-state polynomial PIVP and check w → 1,
      I → 1/π, P → π, and the exponential rates;
  (4) plot all three convergences.
"""

import math
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

# ---------------------------------------------------------------------------
# Constants

Z0 = 1.0 / (396.0 ** 4)                  # Ramanujan evaluation point
INV_PI = 1.0 / math.pi                   # target value
PREFAC = 2.0 * math.sqrt(2.0) / 9801.0   # (2√2/9801)
DECAY = 256.0 * Z0                       # per-term factor = 1/99⁴

# ---------------------------------------------------------------------------
# Coefficient sequence

def a_coeff(k):
    """a_k = (4k)!/(k!)⁴, using lgamma to stay in float range."""
    log_a = math.lgamma(4 * k + 1) - 4 * math.lgamma(k + 1)
    return math.exp(log_a)


def check_recurrence(kmax=30):
    worst = 0.0
    for k in range(kmax):
        lhs = (k + 1) ** 3 * a_coeff(k + 1)
        rhs = 4 * (4 * k + 1) * (4 * k + 2) * (4 * k + 3) * a_coeff(k)
        rel = abs(lhs - rhs) / max(abs(rhs), 1.0)
        worst = max(worst, rel)
    return worst


# ---------------------------------------------------------------------------
# Direct Ramanujan partial sum

def ramanujan_partial_sum(N):
    S = 0.0
    last_term = 0.0
    for k in range(N):
        t = a_coeff(k) * (1103.0 + 26390.0 * k) * (Z0 ** k)
        S += t
        last_term = t
    return PREFAC * S, last_term


# ---------------------------------------------------------------------------
# Series initial conditions for g(w) at small w₁

def g_series_ic(w1, N=40):
    """Truncated series g(w₁), g'(w₁), g''(w₁) from g(w) = Σ a_k z₀^k w^k."""
    g = 0.0
    gp = 0.0
    gpp = 0.0
    for k in range(N):
        ck = a_coeff(k) * (Z0 ** k)
        g += ck * w1 ** k
        if k >= 1:
            gp += ck * k * w1 ** (k - 1)
        if k >= 2:
            gpp += ck * k * (k - 1) * w1 ** (k - 2)
    return g, gp, gpp


# ---------------------------------------------------------------------------
# Polynomial PIVP in τ-coordinate

def pivp_poly(tau, X):
    w, Q, g, gp, gpp, P = X
    drift = 1.0 - w
    dw = drift
    # d/dw [w² (1 − 256 z₀ w)] = 2w − 3·256 z₀ w² = 2w (1 − 384 z₀ w)
    dQ = -2.0 * w * (1.0 - 384.0 * Z0 * w) * Q * Q * drift
    dg = gp * drift
    dgp = gpp * drift
    Lg = (3.0 * w * (384.0 * Z0 * w - 1.0) * gpp
          + (816.0 * Z0 * w - 1.0) * gp
          + 24.0 * Z0 * g)
    dgpp = Q * Lg * drift
    # Readout 1/π estimate, built polynomially from (g, g').
    I = PREFAC * (1103.0 * g + 26390.0 * gp)
    # Linear Newton–Raphson-free inverter: P → 1/I = π.
    dP = 1.0 - I * P
    return [dw, dQ, dg, dgp, dgpp, dP]


# --- Rational-constant variant: √2 grown in-system by a 1-D PIVP.
# Extra state s with s(0) = 1, ds/dτ = s(1 − s²/2).  Fixed points 0, ±√2;
# only s = √2 is stable with linearization rate 2.  Readout becomes
#     I(X) = (2/9801) · s · (1103 g + 26390 g')
# so every constant in the full PIVP is rational.

def pivp_poly_sqrt2(tau, X):
    w, Q, g, gp, gpp, P, s = X
    drift = 1.0 - w
    dw = drift
    dQ = -2.0 * w * (1.0 - 384.0 * Z0 * w) * Q * Q * drift
    dg = gp * drift
    dgp = gpp * drift
    Lg = (3.0 * w * (384.0 * Z0 * w - 1.0) * gpp
          + (816.0 * Z0 * w - 1.0) * gp
          + 24.0 * Z0 * g)
    dgpp = Q * Lg * drift
    I = (2.0 / 9801.0) * s * (1103.0 * g + 26390.0 * gp)
    dP = 1.0 - I * P
    ds = s * (1.0 - 0.5 * s * s)
    return [dw, dQ, dg, dgp, dgpp, dP, ds]


def run_pivp_sqrt2(w1=1e-3, T_MAX=60.0, n_steps=6000, P0=3.0, s0=1.0):
    g1, gp1, gpp1 = g_series_ic(w1, N=40)
    Q1 = 1.0 / (w1 * w1 * (1.0 - 256.0 * Z0 * w1))
    tau_start = -math.log(1.0 - w1)
    X0 = [w1, Q1, g1, gp1, gpp1, P0, s0]
    t_eval = np.linspace(tau_start, tau_start + T_MAX, n_steps)
    sol = solve_ivp(
        pivp_poly_sqrt2, [tau_start, tau_start + T_MAX], X0,
        t_eval=t_eval, method='DOP853', rtol=1e-12, atol=1e-14,
    )
    return sol, tau_start


# --- IBP / modular-composition variant.
# Move √2 outside the inverter.  Define
#     T(τ) := 1103 g + 26390 g'   →  T_∞ = 9801 / (2√2 π)
#     dL/dτ = 1 − T · L           →  L_∞   = 1 / T_∞ = 2√2 π / 9801
# and run the rational √2-generator s alongside.  The readout is
#     M := (9801/4) · s · L       →  M_∞   = (9801/4) · √2 · 2√2 π / 9801 = π.
# √2 enters only as a final scalar multiplication; the inverter chain
# never sees it.  The s08-hierarchy IBP bound is exactly the modular
# substitution lemma in this configuration: |M − π| ≤ (9801/4) ·
# (|L| · |s − √2| + √2 · |L − L_∞|), so M inherits the slower of the two
# upstream rates and adds no further loss.

def pivp_poly_ibp(tau, X):
    w, Q, g, gp, gpp, L, s = X
    drift = 1.0 - w
    dw = drift
    dQ = -2.0 * w * (1.0 - 384.0 * Z0 * w) * Q * Q * drift
    dg = gp * drift
    dgp = gpp * drift
    Lg = (3.0 * w * (384.0 * Z0 * w - 1.0) * gpp
          + (816.0 * Z0 * w - 1.0) * gp
          + 24.0 * Z0 * g)
    dgpp = Q * Lg * drift
    T = 1103.0 * g + 26390.0 * gp
    dL = 1.0 - T * L
    ds = s * (1.0 - 0.5 * s * s)
    return [dw, dQ, dg, dgp, dgpp, dL, ds]


# --- Rate-k inverter: replace the linear inverter dP/dτ = 1 − I·P
# (rate I = 1/π) by dP/dτ = P(1 − (I·P)^k).  In the rescaled variable
# x = I·P this is the logistic-k ODE dx/dτ = x(1 − x^k), whose stable
# fixed point x* = 1 has linearization δx' = −k δx, so the asymptotic
# rate is exactly k, independent of the value of I.  The asymptotic
# rate, not the order of convergence, is what changes — this is not
# the continuous analogue of Householder's iterative method (which
# trades order, not rate; in the continuous limit Householder still
# linearises at rate 1).

def pivp_poly_ratek(tau, X, k=2):
    w, Q, g, gp, gpp, P = X
    drift = 1.0 - w
    dw = drift
    dQ = -2.0 * w * (1.0 - 384.0 * Z0 * w) * Q * Q * drift
    dg = gp * drift
    dgp = gpp * drift
    Lg = (3.0 * w * (384.0 * Z0 * w - 1.0) * gpp
          + (816.0 * Z0 * w - 1.0) * gp
          + 24.0 * Z0 * g)
    dgpp = Q * Lg * drift
    I = PREFAC * (1103.0 * g + 26390.0 * gp)
    dP = P * (1.0 - (I * P) ** k)
    return [dw, dQ, dg, dgp, dgpp, dP]


def run_pivp_ratek(k=2, w1=1e-3, T_MAX=60.0, n_steps=6000, P0=3.0):
    g1, gp1, gpp1 = g_series_ic(w1, N=40)
    Q1 = 1.0 / (w1 * w1 * (1.0 - 256.0 * Z0 * w1))
    tau_start = -math.log(1.0 - w1)
    X0 = [w1, Q1, g1, gp1, gpp1, P0]
    t_eval = np.linspace(tau_start, tau_start + T_MAX, n_steps)
    sol = solve_ivp(
        lambda t, X: pivp_poly_ratek(t, X, k=k),
        [tau_start, tau_start + T_MAX], X0,
        t_eval=t_eval, method='DOP853', rtol=1e-12, atol=1e-14,
    )
    return sol, tau_start


def run_pivp_ibp(w1=1e-3, T_MAX=60.0, n_steps=6000, L0=0.0, s0=1.0):
    g1, gp1, gpp1 = g_series_ic(w1, N=40)
    Q1 = 1.0 / (w1 * w1 * (1.0 - 256.0 * Z0 * w1))
    tau_start = -math.log(1.0 - w1)
    X0 = [w1, Q1, g1, gp1, gpp1, L0, s0]
    t_eval = np.linspace(tau_start, tau_start + T_MAX, n_steps)
    sol = solve_ivp(
        pivp_poly_ibp, [tau_start, tau_start + T_MAX], X0,
        t_eval=t_eval, method='DOP853', rtol=1e-12, atol=1e-14,
    )
    return sol, tau_start


def run_pivp(w1=1e-3, T_MAX=60.0, n_steps=6000, P0=3.0):
    g1, gp1, gpp1 = g_series_ic(w1, N=40)
    Q1 = 1.0 / (w1 * w1 * (1.0 - 256.0 * Z0 * w1))
    # Re-parameterise time so that w(0) = w1 = 1 - e^{-τ_start}.
    tau_start = -math.log(1.0 - w1)
    X0 = [w1, Q1, g1, gp1, gpp1, P0]
    t_eval = np.linspace(tau_start, tau_start + T_MAX, n_steps)
    sol = solve_ivp(
        pivp_poly, [tau_start, tau_start + T_MAX], X0,
        t_eval=t_eval, method='DOP853', rtol=1e-12, atol=1e-14,
    )
    return sol, tau_start


# ---------------------------------------------------------------------------
# Main experiment

def main():
    print("=" * 72)
    print("  Ramanujan 1914  —  GPAC / polynomial PIVP experiment")
    print("=" * 72)
    print(f"  z₀ = 1/396⁴       = {Z0:.6e}")
    print(f"  256 z₀ (= 1/99⁴)  = {DECAY:.6e}")
    print(f"  target 1/π        = {INV_PI:.15f}")
    print(f"  prefactor 2√2/9801 = {PREFAC:.15f}")
    print()

    # --- (1) recurrence ---
    worst = check_recurrence(30)
    print(f"[1] recurrence  max relative error over k = 0..29 : {worst:.2e}")

    # --- (2) direct partial sum ---
    print()
    print("[2] direct partial-sum convergence of Ramanujan's series")
    Ns = [1, 2, 3, 4, 5, 6, 8, 10, 15, 20]
    for N in Ns:
        est, last = ramanujan_partial_sum(N)
        err = abs(est - INV_PI)
        print(f"    N={N:>3}  last term={last:>14.4e}  est={est:.15f}  err={err:.2e}")

    # --- (3) polynomial PIVP ---
    print()
    print("[3] polynomial PIVP  (state w, Q, g, g', g'', P; dw/dτ = 1 − w)")
    w1 = 1e-3
    sol, tau_start = run_pivp(w1=w1, T_MAX=60.0, n_steps=6000, P0=3.0)
    w_tau  = sol.y[0]; g_tau = sol.y[2]; gp_tau = sol.y[3]; P_tau = sol.y[5]
    est_tau = PREFAC * (1103.0 * g_tau + 26390.0 * gp_tau)
    err_invpi = np.abs(est_tau - INV_PI)
    err_pi    = np.abs(P_tau   - math.pi)
    print(f"    w₁ = {w1} ; τ_start = {tau_start:.3f}")
    print(f"    τ_max = {sol.t[-1]:.2f}   w(τ_max) = {w_tau[-1]:.10f}   "
          f"(1 − w) = {1 - w_tau[-1]:.2e}")
    print(f"    I(τ_max)  = {est_tau[-1]:.15f}   |I − 1/π| = {err_invpi[-1]:.2e}")
    print(f"    P(τ_max)  = {P_tau[-1]:.15f}    |P − π|   = {err_pi[-1]:.2e}")

    for label, errs, expected in [
        ('I → 1/π ', err_invpi, 1.0),
        ('P → π   ', err_pi,    INV_PI),
    ]:
        mask = (errs > 1e-14) & (sol.t > tau_start + 8.0) & (sol.t < sol.t[-1] - 5.0)
        if mask.sum() > 10:
            coeffs = np.polyfit(sol.t[mask], np.log(errs[mask]), 1)
            alpha = -coeffs[0]
            print(f"    {label} fitted exponential rate α ≈ {alpha:.4f}   "
                  f"(expected: {expected:.4f})")

    # --- (3b) rational-constant 7-state PIVP with √2 sub-generator ---
    print()
    print("[3b] 7-state PIVP with √2 sub-generator  (all constants rational)")
    sol2, _ = run_pivp_sqrt2(w1=w1, T_MAX=60.0, n_steps=6000, P0=3.0, s0=1.0)
    s_tau = sol2.y[6]; P_tau2 = sol2.y[5]; g_tau2 = sol2.y[2]; gp_tau2 = sol2.y[3]
    I_tau2 = (2.0 / 9801.0) * s_tau * (1103.0 * g_tau2 + 26390.0 * gp_tau2)
    err_s    = np.abs(s_tau - math.sqrt(2.0))
    err_I2   = np.abs(I_tau2 - INV_PI)
    err_pi2  = np.abs(P_tau2 - math.pi)
    print(f"    s(τ_max)  = {s_tau[-1]:.15f}     |s − √2|  = {err_s[-1]:.2e}")
    print(f"    I(τ_max)  = {I_tau2[-1]:.15f}   |I − 1/π| = {err_I2[-1]:.2e}")
    print(f"    P(τ_max)  = {P_tau2[-1]:.15f}    |P − π|   = {err_pi2[-1]:.2e}")
    # Compare to the 6-state variant (which uses 2√2/9801 as a hard-coded real constant).
    delta = err_pi2[-1] - err_pi[-1]
    print(f"    ΔP(τ_max) = {delta:+.2e}   (7-state minus 6-state — same ballpark means no bias accumulation)")

    for label, errs, expected in [
        ('s → √2 ',  err_s,   2.0),
        ('I → 1/π', err_I2,   1.0),
        ('P → π  ', err_pi2, INV_PI),
    ]:
        mask = (errs > 1e-14) & (sol2.t > tau_start + 8.0) & (sol2.t < sol2.t[-1] - 5.0)
        if mask.sum() > 10:
            coeffs = np.polyfit(sol2.t[mask], np.log(errs[mask]), 1)
            alpha = -coeffs[0]
            print(f"    {label} fitted exponential rate α ≈ {alpha:.4f}   "
                  f"(expected: {expected:.4f})")

    # --- (3d) Rate-k inverters: skip the 1/π low-pass entirely ---
    print()
    print("[3d] Rate-k inverters  dP/dτ = P(1 − (I·P)^k)  →  rate = k at P = 1/I")
    rate_k_results = {}
    for k in (1, 2, 3, 4):
        solk, _ = run_pivp_ratek(k=k, w1=w1, T_MAX=60.0, n_steps=6000, P0=3.0)
        Pk = solk.y[5]
        err_k = np.abs(Pk - math.pi)
        rate_k_results[k] = (solk, err_k)
        print(f"    k={k}  P(τ_max)={Pk[-1]:.15f}  |P − π|={err_k[-1]:.2e}")
        # Fit the exponential rate on the pre-saturation window only.
        # Higher-k variants saturate in just a few τ-units, so pick a
        # narrow window starting once the trajectory has settled.
        floor = 1e-13
        above_floor = err_k > floor
        if above_floor.any():
            t_in = solk.t[above_floor]
            e_in = err_k[above_floor]
            if len(t_in) > 30:
                t_lo = t_in[0] + 0.3 * (t_in[-1] - t_in[0])
                t_hi = t_in[0] + 0.85 * (t_in[-1] - t_in[0])
                mask = (solk.t >= t_lo) & (solk.t <= t_hi) & (err_k > floor)
                if mask.sum() > 8:
                    coeffs = np.polyfit(solk.t[mask], np.log(err_k[mask]), 1)
                    print(f"    k={k}  fitted exponential rate α ≈ {-coeffs[0]:.4f}   "
                          f"(expected: {k:.4f}; window τ∈[{t_lo:.1f},{t_hi:.1f}])")

    # --- (3c) IBP / modular variant: √2 outside the inverter ---
    print()
    print("[3c] IBP / modular PIVP  (√2 multiplied outside; inverter sees no √2)")
    sol3, _ = run_pivp_ibp(w1=w1, T_MAX=60.0, n_steps=6000, L0=0.0, s0=1.0)
    L_tau   = sol3.y[5]
    s_tau3  = sol3.y[6]
    g_tau3  = sol3.y[2]
    gp_tau3 = sol3.y[3]
    T_tau   = 1103.0 * g_tau3 + 26390.0 * gp_tau3
    T_inf   = 9801.0 / (2.0 * math.sqrt(2.0) * math.pi)
    L_inf   = 2.0 * math.sqrt(2.0) * math.pi / 9801.0
    M_tau   = (9801.0 / 4.0) * s_tau3 * L_tau
    err_T   = np.abs(T_tau - T_inf)
    err_L   = np.abs(L_tau - L_inf)
    err_s3  = np.abs(s_tau3 - math.sqrt(2.0))
    err_pi3 = np.abs(M_tau - math.pi)
    print(f"    T_∞ = 9801/(2√2 π) = {T_inf:.6f}")
    print(f"    L_∞ = 2√2 π/9801   = {L_inf:.6e}")
    print(f"    T(τ_max)  = {T_tau[-1]:.10f}    |T − T_∞|  = {err_T[-1]:.2e}")
    print(f"    L(τ_max)  = {L_tau[-1]:.15e}  |L − L_∞|  = {err_L[-1]:.2e}")
    print(f"    s(τ_max)  = {s_tau3[-1]:.15f}     |s − √2|  = {err_s3[-1]:.2e}")
    print(f"    M(τ_max)  = {M_tau[-1]:.15f}    |M − π|   = {err_pi3[-1]:.2e}")

    for label, errs in [
        ('T → T_∞', err_T),
        ('L → L_∞', err_L),
        ('s → √2 ',  err_s3),
        ('M → π  ',  err_pi3),
    ]:
        mask = (errs > 1e-14) & (sol3.t > tau_start + 8.0) & (sol3.t < sol3.t[-1] - 5.0)
        if mask.sum() > 10:
            coeffs = np.polyfit(sol3.t[mask], np.log(errs[mask]), 1)
            alpha = -coeffs[0]
            print(f"    {label} fitted exponential rate α ≈ {alpha:.4f}")

    # --- plot ---
    fig, axes = plt.subplots(1, 2, figsize=(13, 5))

    # Left: three-way comparison of the π-readout errors only.
    # Once a curve reaches the round-off floor it just bounces around;
    # plot the running minimum to show the decay envelope cleanly,
    # and stop the curve once the running minimum has stopped improving
    # for a while (pure numerical noise after that).

    def envelope(t_arr, e_arr, plateau_window=200):
        e_clean = np.maximum(np.array(e_arr, dtype=float), 1e-17)
        run_min = np.minimum.accumulate(e_clean)
        if len(run_min) > plateau_window:
            improvements = run_min[:-plateau_window] - run_min[plateau_window:]
            improving = improvements > run_min[plateau_window:] * 1e-3
            if improving.any():
                last = int(np.where(improving)[0].max()) + plateau_window
                last = min(last + 50, len(run_min))
                return t_arr[:last], run_min[:last]
        return t_arr, run_min

    ax = axes[0]
    # Variants (A) and (B) never reach the noise floor in T_MAX = 60,
    # so plot raw curves; variant (C) saturates around τ ≈ 12, so
    # plot its decay envelope.
    ax.semilogy(sol.t  - tau_start, np.maximum(err_pi,  1e-17), 'C0-',  lw=1.6,
                label=r'(A)  linear inverter, rate $1/\pi$   $|P-\pi|$')
    ax.semilogy(sol2.t - tau_start, np.maximum(err_pi2, 1e-17), 'C2--', lw=1.6,
                label=r'(B)  linear inverter, $\sqrt{2}$ inside   $|P-\pi|$')
    t3, e3 = envelope(sol3.t - tau_start, err_pi3)
    ax.semilogy(t3, e3, 'C3-',  lw=1.8,
                label=r'(C)  IBP / modular, $\sqrt{2}$ outside   $|M-\pi|$')
    sol_k2, err_k2 = rate_k_results[2]
    t4, e4 = envelope(sol_k2.t - tau_start, err_k2)
    ax.semilogy(t4, e4, 'C4-',  lw=1.8,
                label=r'(D)  rate-2 inverter, $P\,(1-(IP)^2)$   $|P-\pi|$')
    # Reference rate lines.
    tau_ref = np.linspace(2, 50, 50)
    ax.semilogy(tau_ref, 0.6 * np.exp(-tau_ref / math.pi),
                'k:', lw=1.0, alpha=0.5, label=r'rate $1/\pi \approx 0.318$')
    ax.semilogy(tau_ref, 1.0 * np.exp(-tau_ref),
                color='0.5', linestyle=':', lw=1.0,
                label=r'rate $1$')
    ax.semilogy(tau_ref, 0.5 * np.exp(-2.0 * tau_ref),
                color='0.3', linestyle=':', lw=1.0,
                label=r'rate $2$')
    ax.set_xlabel(r'$\tau$  (shifted so $\tau=0$ at $w=w_1$)')
    ax.set_ylabel(r'$|\mathrm{output} - \pi|$')
    ax.set_title('Three encodings of π — readout convergence')
    ax.set_ylim(1e-15, 5)
    ax.legend(fontsize=8, loc='upper right'); ax.grid(True, alpha=0.3)

    # Right: anatomy of variant (C) — show why it's faster.
    ax = axes[1]
    tA, eA = envelope(sol3.t - tau_start, err_s3)
    tB, eB = envelope(sol3.t - tau_start, err_L)
    tC, eC = envelope(sol3.t - tau_start, err_pi3)
    ax.semilogy(tA, eA, 'C1-',  lw=1.6, label=r'$|s - \sqrt{2}|$  (rate 2)')
    ax.semilogy(tB, eB, 'C4-',  lw=1.6, label=r'$|L - L_\infty|$  (rate 1)')
    ax.semilogy(tC, eC, 'C3-',  lw=1.8, label=r'$|M - \pi|$  (readout)')
    ax.semilogy(tau_ref, 0.5 * np.exp(-2.0 * tau_ref),
                'k:', lw=1.0, alpha=0.5, label='rate 2')
    ax.semilogy(tau_ref, 1.0 * np.exp(-tau_ref),
                color='0.5', linestyle=':', lw=1.0, label='rate 1')
    ax.set_xlabel(r'$\tau$')
    ax.set_ylabel('abs error')
    ax.set_title('Anatomy of variant (C):  upstream rates → readout')
    ax.set_ylim(1e-15, 5)
    ax.legend(fontsize=9, loc='upper right'); ax.grid(True, alpha=0.3)

    plt.tight_layout()
    out = '/tmp/ramanujan1914_pivp_ibp.png'
    plt.savefig(out, dpi=130)
    print()
    print(f"  plot saved to  {out}")


if __name__ == '__main__':
    main()
