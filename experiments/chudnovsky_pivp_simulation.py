"""
Explicit Chudnovsky π-PIVP: ODE system + numerical simulation.

Parallel to the Ramanujan construction in blog posts 005-007, but for
Chudnovsky's 1989 series.  Goal: verify that the symbolic analog rate
12·M_∞ ≈ 1.63×10^8 matches the simulated transient rate.

Architecture:
  (1) Series-sum PIVP  — produces M(τ) → M_∞
  (2) Inverter PIVP    — produces P(τ) → π via dP/dτ = 640320^{3/2} − 12·M·P

Series-sum PIVP for M = Σ a_k (A + B k) z₀^k where
  a_k = (6k)!/((3k)!(k!)³),  A=13591409, B=545140134, z₀ = 1/640320³.

Recurrence:
  a_{k+1} = a_k · (6k+1)(6k+2)(6k+3)(6k+4)(6k+5)(6k+6) /
                  [(3k+1)(3k+2)(3k+3) · (k+1)³]
       (sign flipped because of the (-1)^k).

In continuous time we replace "k" by a continuous parameter and
introduce "production" of new terms at constant rate.  A clean way:

  - state K(τ): "current term index", grows linearly
  - state α(τ): tracks a_K · z₀^K
  - state M(τ): partial sum

This gives a rational-ODE construction (not strictly polynomial because
of the high-degree factors); to get a *polynomial* PIVP one can either
expand the rational ODE into more states or accept that the construction
is GPAC modulo standard rational-to-polynomial gadgets.

Here we focus on the rate verification, not strict GPAC purity.
"""
from mpmath import mpf, mp, pi, sqrt, log, log10, exp
mp.dps = 60
PI = mp.pi

A = mpf(13591409)
B = mpf(545140134)
ROOT = mpf(640320)


def chudnovsky_M_partial(K=20):
    """Compute the partial sum M_K = Σ_{k=0}^{K-1} (-1)^k a_k (A+Bk)/640320^{3k}."""
    a = mpf(1)
    z = 1 / ROOT**3
    s = A
    sign = -1
    zpow = z
    for k in range(1, K):
        a = a * (6*k-5) * (6*k-4) * (6*k-3) * (6*k-2) * (6*k-1) * (6*k) / (
            (3*k-2) * (3*k-1) * (3*k) * k**3
        )
        s += sign * a * (A + B*k) * zpow
        zpow *= z
        sign = -sign
    return s


def simulate_pivp(M_final, T_max=1e-6, N_steps=10000):
    """Simulate dP/dτ = 640320^{3/2} − 12 M_final · P with P(0) = 0.

    Analytical solution: P(τ) = (640320^{3/2}/(12 M_final)) · (1 − exp(−12 M_final τ)).
    At fixed point P_∞ = 640320^{3/2}/(12 M_final) = π (assuming M_final = M_∞).

    Verify the rate constant 12 M_final matches the linearization eigenvalue."""
    rate = 12 * M_final
    P_inf = ROOT**(mpf(3)/2) / (12 * M_final)

    dt = T_max / N_steps
    P = mpf(0)
    log_errs = []
    times = []
    for n in range(N_steps + 1):
        tau = n * dt
        deriv = ROOT**(mpf(3)/2) - 12 * M_final * P
        if n % (N_steps // 20) == 0:
            err = abs(P_inf - P)
            if err > 0:
                log_errs.append(float(log10(err)))
                times.append(float(tau))
        P += deriv * dt
    return times, log_errs, P_inf, rate


def main():
    print("=" * 76)
    print("  Chudnovsky π-PIVP: explicit construction + rate verification")
    print("=" * 76)
    print()

    print("--- Step 1: M_∞ via partial sum ---")
    M = chudnovsky_M_partial(K=25)
    target = ROOT**(mpf(3)/2) / (12 * PI)
    print(f"  M (K=25)              = {M}")
    print(f"  640320^{{3/2}}/(12·π)  = {target}")
    print(f"  diff                  = {float(M - target):.3e}")
    print()

    print("--- Step 2: inverter PIVP simulation ---")
    print("  ODE:  dP/dτ = 640320^{3/2} − 12·M_∞·P,  P(0) = 0")
    print(f"  Symbolic rate r = 12·M_∞ = {float(12*M):.6e}")
    print(f"  Symbolic P_∞    = {float(ROOT**(mpf(3)/2)/(12*M)):.10f}")
    print(f"  π               = {float(PI):.10f}")
    print()
    times, log_errs, P_inf, rate = simulate_pivp(M, T_max=1e-7, N_steps=20000)
    print(f"  Simulation T_max = 1e-7, N_steps = 20000")
    print(f"  τ          log10|P_inf − P|")
    for t, e in zip(times[::4], log_errs[::4]):
        print(f"    {t:.3e}    {e:.4f}")
    # Linear fit slope of log10|err| vs τ should give -rate/log(10)
    if len(times) > 5:
        slope = (log_errs[-1] - log_errs[1]) / (times[-1] - times[1])
        observed_rate = -slope * float(log(mpf(10)))
        print()
        print(f"  Fitted decay rate (from log slope) = {observed_rate:.4e}")
        print(f"  Symbolic rate                       = {float(rate):.4e}")
        print(f"  Ratio                               = {observed_rate/float(rate):.6f}")
        print()
        digits_per_tau = float(rate) / float(log(mpf(10)))
        print(f"  ⇒ {digits_per_tau:.4e} decimal digits of π per unit τ")
    print()

    print("=" * 76)
    print("  State count for full PIVP (informal)")
    print("=" * 76)
    print("""
  Series-sum module (compute M_∞ from recurrence):
    - K, α, M           = 3 states   (continuous-time term generator)
    - extra rational-to-poly gadgets to handle 6th-degree numerator   ~6 states
    - sign alternation gadget                                          1 state
                                                          ─────────
                                                          ≈ 10 states

  Inverter module (P → π):
    - P                                                                1 state
    - constants A, B, 640320^{3/2}, 12 (system parameters)             —

  Total active states: ≈ 11.

  Compare Ramanujan: ≈ 8 states (because (4k)!/(k!)^4 only has 4-degree
  numerator and 3-degree denominator).  Chudnovsky's 6-fold numerator
  costs a few extra states but buys the 5×10^4 rate factor.
""")


if __name__ == '__main__':
    main()
